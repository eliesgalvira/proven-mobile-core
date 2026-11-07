# docs/spec/tickets/22-e2e.md and 30-e2e-handover.md
{ kernel, edge, eupf, packetrusher }:
let
  ip = { core = "10.33.0.11"; upf = "10.33.0.20"; ran = "10.33.0.30"; gnb2 = "10.33.0.31"; dn = "10.33.0.40"; };
  setup = ../test-vectors/capture/setup;
  rusherSocket = "/run/rusher.sock";

  lan = addresses: { lib, ... }: {
    virtualisation.vlans = [ 1 ];
    virtualisation.memorySize = 512;
    networking.interfaces.eth1.ipv4.addresses = lib.mkForce (map (address: { inherit address; prefixLength = 24; }) addresses);
    networking.firewall.enable = false;
  };
in
{
  name = "speck5g-e2e";

  nodes = {
    core = { lib, pkgs, ... }: {
      imports = [ (lan [ ip.core ]) ];
      # The edge binds the core's address, so it starts once that is configured.
      systemd.services.edge.after = [ "network-online.target" ];
      systemd.services.edge.wants = [ "network-online.target" ];
      systemd.services.edge.serviceConfig.ExecStart =
        let
          config = lib.recursiveUpdate (lib.importTOML ../edge/config.example.toml) {
            kernel.path = "${kernel}/bin/kernel";
            n4.smf = ip.core;
          };
        in
        "${edge}/bin/edge --config ${(pkgs.formats.toml { }).generate "edge.toml" config}";
    };

    upf = {
      imports = [ (lan [ ip.upf ]) ];
      # eUPF's XDP program hands a G-PDU to the kernel when the gNB's MAC is not yet
      # in the neighbour table, already encapsulated from eUPF's own address; without
      # accept_local the kernel drops it as a martian instead of resolving the gNB.
      boot.kernel.sysctl = {
        "net.ipv4.ip_forward" = 1;
        "net.ipv4.conf.all.rp_filter" = 0;
        "net.ipv4.conf.eth1.rp_filter" = 0;
        "net.ipv4.conf.eth1.accept_local" = 1;
      };
      systemd.services.eupf.serviceConfig.ExecStart = "${eupf}/bin/eupf --config ${setup}/eupf/config.yml --iface eth1";
    };

    dn = {
      imports = [ (lan [ ip.dn ]) ];
      networking.interfaces.eth1.ipv4.routes = [ { address = "10.45.0.0"; prefixLength = 16; via = ip.upf; } ];
    };

    # UERANSIM's gNB and UE run the registration case. PacketRusher then runs both
    # gNBs of the handover cases, on 10.33.0.30 and 10.33.0.31, and their UE in one
    # process, since its UE moves between gNBs inside that process.
    ran = { pkgs, ... }: {
      imports = [ (lan [ ip.ran ip.gnb2 ]) ];
      # nr-ue adds its routing table to rt_tables, so it must be a writable copy.
      environment.etc."iproute2/rt_tables" = {
        mode = "0644";
        text = "255\tlocal\n254\tmain\n253\tdefault\n0\tunspec\n";
      };
      # PacketRusher sends and reads every NGAP message on stream 0, so only
      # UERANSIM can check the core's stream ids (docs/spec/tickets/31-edge-sctp-coverage.md).
      systemd.services.gnb.serviceConfig.ExecStart =
        let
          gnb = pkgs.runCommand "gnb.yaml" { } "${pkgs.yq-go}/bin/yq '.ignoreStreamIds = false' ${setup}/ueransim/gnb.yaml > $out";
        in
        "${pkgs.ueransim}/bin/nr-gnb -c ${gnb}";
      systemd.services.ue.serviceConfig.ExecStart = "${pkgs.ueransim}/bin/nr-ue -c ${setup}/ueransim/ue.yaml";
      systemd.services.rusher.serviceConfig.ExecStart = "${packetrusher}/bin/packetrusher --config ${setup}/packetrusher/config.yml --tunnel-backend userspace multi-ue -n 1 --dedicatedGnb --number-of-gnbs 2 --tunnel --tunnel-vrf=false --control-socket ${rusherSocket}";
    };
  };

  testScript = ''
    import json, re

    def step(name, run, *args, **kwargs):
        try:
            return run(*args, **kwargs)
        except Exception as e:
            raise Exception(f"E2E FAIL: {name}") from e

    def control(action, *args):
        return json.loads(ran.succeed(f"${packetrusher}/bin/packetrusher control --socket ${rusherSocket} --ue 1 --timeout 45s --action {action} {' '.join(args)}"))["ues"][0]

    start_all()
    step("start eUPF", upf.wait_until_succeeds, "systemctl start eupf && journalctl -u eupf -q --grep 'Starting PFCP connection'", timeout=120)
    step("start core", core.wait_until_succeeds, "systemctl start edge && journalctl -u edge -q --grep 'association with the UPF up'", timeout=120)
    step("start gnb", ran.wait_until_succeeds, "systemctl start gnb && journalctl -u gnb -q --grep 'NG Setup procedure is successful'", timeout=60)
    # nr-ue drops system information that arrives before it has the gNB's signal, and
    # then waits for the gNB's next broadcast. A UE that has selected no cell after 30 s
    # is restarted once: only cell selection between the two simulators is retried,
    # which involves no core message beyond the NG Setup already checked.
    ran.succeed("systemctl start ue")
    selected = "journalctl -u ue -q --grep 'Selected cell'"
    try:
        ran.wait_until_succeeds(selected, timeout=30)
    except Exception:
        print("E2E RETRY: the UE selected no cell in 30 s; restarting it once")
        ran.succeed("systemctl restart ue")
        step("UE selects a cell", ran.wait_until_succeeds, selected, timeout=30)
    step("register and establish", ran.wait_until_succeeds, "ip -4 -br addr show uesimtun0 | grep -q ' 10[.]45[.]'", timeout=90)
    print(step("ping through eUPF", ran.wait_until_succeeds, "ping -c 4 -i 0.5 -W 2 -I uesimtun0 ${ip.dn}", timeout=30))
    print("E2E PASS: registration")

    step("stop UERANSIM", ran.succeed, "systemctl stop ue gnb")
    step("start PacketRusher", ran.wait_until_succeeds, "systemctl start rusher && test -S ${rusherSocket}", timeout=30)
    step("PacketRusher register and establish", control, "wait")
    ue = step("PacketRusher UE address", lambda: re.findall(r"PDU session 1 address: (\S+)", ran.succeed("journalctl -u rusher -o cat"))[-1])

    def handover(name, action, target):
        ping = f"ping -c 4 -i 0.5 -W 2 -I {ue} ${ip.dn}"
        print(step(f"{name}: ping before", ran.wait_until_succeeds, ping, timeout=30))
        status = step(f"{name}: handover", control, action, "--target", target)
        if status["gnb"] != target:
            raise Exception(f"E2E FAIL: {name}: UE on gNB {status['gnb']}")
        print(step(f"{name}: ping after", ran.wait_until_succeeds, ping, timeout=30))
        print(f"E2E PASS: {name}")

    handover("xn-handover", "xn-handover", "00000002")
    handover("n2-handover", "ng-handover", "00000001")
  '';
}
