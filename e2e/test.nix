# docs/spec/tickets/22-e2e.md
{ kernel, edge, eupf }:
let
  ip = { core = "10.33.0.11"; upf = "10.33.0.20"; ran = "10.33.0.30"; dn = "10.33.0.40"; };

  lan = address: { lib, ... }: {
    virtualisation.vlans = [ 1 ];
    virtualisation.memorySize = 512;
    networking.interfaces.eth1.ipv4.addresses = lib.mkForce [ { inherit address; prefixLength = 24; } ];
    networking.firewall.enable = false;
  };
in
{
  name = "speck5g-e2e";

  nodes = {
    core = { lib, pkgs, ... }: {
      imports = [ (lan ip.core) ];
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
      imports = [ (lan ip.upf) ];
      boot.kernel.sysctl = {
        "net.ipv4.ip_forward" = 1;
        "net.ipv4.conf.all.rp_filter" = 0;
        "net.ipv4.conf.eth1.rp_filter" = 0;
      };
      systemd.services.eupf.serviceConfig.ExecStart = "${eupf}/bin/eupf --config ${../test-vectors/capture/setup/eupf/config.yml} --iface eth1";
    };

    dn = {
      imports = [ (lan ip.dn) ];
      networking.interfaces.eth1.ipv4.routes = [ { address = "10.45.0.0"; prefixLength = 16; via = ip.upf; } ];
    };

    ran = { pkgs, ... }: {
      imports = [ (lan ip.ran) ];
      # nr-ue adds its routing table to rt_tables, so it must be a writable copy.
      environment.etc."iproute2/rt_tables" = {
        mode = "0644";
        text = "255\tlocal\n254\tmain\n253\tdefault\n0\tunspec\n";
      };
      systemd.services.gnb.serviceConfig.ExecStart = "${pkgs.ueransim}/bin/nr-gnb -c ${../test-vectors/capture/setup/ueransim/gnb.yaml}";
      systemd.services.ue.serviceConfig.ExecStart = "${pkgs.ueransim}/bin/nr-ue -c ${../test-vectors/capture/setup/ueransim/ue.yaml}";
    };
  };

  testScript = ''
    def step(name, machine, command, timeout):
        try:
            return machine.wait_until_succeeds(command, timeout=timeout)
        except Exception as e:
            raise Exception(f"E2E FAIL: {name}") from e

    start_all()
    step("start eUPF", upf, "systemctl start eupf && journalctl -u eupf -q --grep 'Starting PFCP connection'", 120)
    step("start core", core, "systemctl start edge && journalctl -u edge -q --grep 'association with the UPF up'", 120)
    step("start gnb", ran, "systemctl start gnb && journalctl -u gnb -q --grep 'NG Setup procedure is successful'", 60)
    step("register and establish", ran, "systemctl start ue && ip -4 -br addr show uesimtun0 | grep -q ' 10[.]45[.]'", 90)
    print(step("ping through eUPF", ran, "ping -c 4 -i 0.5 -W 2 -I uesimtun0 ${ip.dn}", 30))
    print("E2E PASS")
  '';
}
