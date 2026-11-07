#!/usr/bin/env python3
"""Capture NGAP, PFCP and GTP-U against Open5GS and eUPF in Docker, then extract the vectors.

    python3 -I capture.py registration <output dir> [--keep-up]
    python3 -I capture.py handover <output dir> [--keep-up]

registration (milestone 1): a UERANSIM gNB and UE register (SUCI Profile A), open an
IPv4 PDU session on DNN "internet" and ping the data network; then the eUPF probes
(pfcp_probe.py) run into a second capture. Gives registration-pdu.pcapng,
vectors.json, eupf-probes.pcapng and probe.json.

handover (milestone 2): PacketRusher runs two gNBs and the UE: registration and PDU
session on gNB 1, Xn handover to gNB 2 (Path Switch), N2 handover to gNB 1 cancelled
after the Handover Command, N2 handover to gNB 1, a ping before the first handover
and after each one. Gives handover.pcapng and handover.json.

Both build and docker-load the Nix images (flake.nix), bring up MongoDB with the
subscriber, the Open5GS NFs and eUPF, start tcpdump on the bridge before the SMF and
AMF so the PFCP association is captured, run the scenario, save the logs, tear the
stack down (--keep-up leaves it running), filter the capture with tshark and run
extract.py. Needs nix (flakes), docker with compose v2 and the host's sctp kernel module.
"""
import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
COMPOSE = ["docker", "compose", "-f", str(HERE / "docker-compose.yml")]
FILTER = "sctp or udp port 8805 or udp port 2152 or icmp"
NETSHOOT = "nicolaka/netshoot:v0.14@sha256:7f08c4aff13ff61a35d30e30c5c1ea8396eac6ab4ce19fd02d5a4b3b5d0d09a2"
DATA_NETWORK = "10.33.0.40"
SOCKET = "/tmp/pr.sock"
GNB1, GNB2 = "00000001", "00000002"


def run(*args, **kw):
    return subprocess.run(args, **{"check": True, **kw})


def dc(*args, **kw):
    return run(*COMPOSE, *args, **kw)


def ok(*args):
    return dc(*args, check=False, capture_output=True).returncode == 0


def nix_build(attr):
    return run("nix", "build", "--no-link", "--print-out-paths", f"{HERE}#{attr}",
               capture_output=True, text=True).stdout.strip()


def reap(proc):
    """Waits for proc, and kills it if it is still running 10 s later."""
    try:
        proc.wait(timeout=10)
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.wait()


def until(what, test, seconds):
    for _ in range(seconds * 2):
        if test():
            return
        time.sleep(0.5)
    sys.exit(f"capture.py: timed out waiting for {what}")


def core_up(*services):
    """MongoDB with the subscriber, the NRF, then the other NFs, eUPF, the data network,
    the capture helper and the scenario's services; the SMF and AMF wait for the capture."""
    dc("down", "-v", "--remove-orphans", check=False, capture_output=True)
    dc("up", "-d", "--quiet-pull", "mongo")
    until("mongo", lambda: ok("exec", "-T", "mongo", "mongosh", "--quiet", "--eval", "db.runCommand({ping:1}).ok"), 30)
    dc("exec", "-T", "mongo", "mongosh", "--quiet", "open5gs", "/subscriber.js", capture_output=True)
    dc("up", "-d", "nrf")
    time.sleep(2)
    dc("up", "-d", "--quiet-pull", "ausf", "udm", "udr", "pcf", "nssf", "bsf", "eupf", "dn", "capture", *services)
    time.sleep(3)


class Capture:
    """tcpdump on the bridge, streamed to a file the invoking user owns rather than root."""

    def __init__(self, pcap, out):
        self.pcap, self.log = pcap, out / "logs" / "tcpdump.log"

    def __enter__(self):
        with open(self.pcap, "wb") as pcap, open(self.log, "wb") as err:
            self.proc = subprocess.Popen([*COMPOSE, "exec", "-T", "capture", "tcpdump", "-i", "br-5gcap", "-U",
                                          "-s", "0", "-w", "-", FILTER], stdout=pcap, stderr=err)
        time.sleep(2)

    def __exit__(self, *exc):
        time.sleep(2)
        dc("exec", "-T", "capture", "pkill", "-INT", "tcpdump", check=False)
        reap(self.proc)


def save_logs(out, *services):
    print("== logs ==")
    for service in services:
        text = dc("logs", "--no-color", service, capture_output=True, text=True).stdout
        (out / "logs" / f"{service}.log").write_text(re.sub(r"\x1b\[[0-9;]*m", "", text))


def registration(out):
    core_up()
    print("== capture: PFCP association, NG setup, registration, PDU session, ping ==")
    with Capture(out / "raw.pcap", out):
        dc("up", "-d", "smf", "amf")
        time.sleep(8)
        dc("up", "-d", "gnb")
        time.sleep(3)
        dc("up", "-d", "ue")
        until("the UE's PDU session", lambda: "10.45." in dc(
            "exec", "-T", "ue", "ip", "-4", "-br", "addr", "show", "uesimtun0",
            check=False, capture_output=True, text=True).stdout, 40)
        ping = dc("exec", "-T", "ue", "ping", "-c", "4", "-i", "0.5", "-I", "uesimtun0", DATA_NETWORK,
                  check=False, capture_output=True, text=True).stdout
        (out / "logs" / "ping.log").write_text(ping)
        print(ping)

    print("== eUPF probes ==")
    with Capture(out / "probe.pcap", out), open(out / "probe.json", "w") as probe:
        run("docker", "run", "--rm", "--network", "container:speck5g-smf-1",
            "-v", f"{HERE / 'pfcp_probe.py'}:/probe.py:ro", "-v", f"{out / 'raw.pcap'}:/raw.pcap:ro",
            "--entrypoint", "python3", NETSHOOT, "/probe.py", "/raw.pcap", stdout=probe, check=False)
    state = run("docker", "inspect", "-f", "eupf state={{.State.Status}} exit={{.State.ExitCode}}",
                "speck5g-eupf-1", capture_output=True, text=True).stdout
    (out / "logs" / "eupf-state.txt").write_text(state)
    print(state.strip())
    after = dc("exec", "-T", "ue", "ping", "-c", "3", "-W", "1", "-I", "uesimtun0", DATA_NETWORK,
               check=False, capture_output=True, text=True)
    (out / "logs" / "ping-after-probes.log").write_text(after.stdout + after.stderr)
    sessions = dc("exec", "-T", "dn", "curl", "-s", "http://10.33.0.20:8080/api/v1/pfcp_sessions",
                  check=False, capture_output=True, text=True).stdout
    (out / "logs" / "eupf-sessions.json").write_text(sessions)

    save_logs(out, "amf", "smf", "ausf", "udm", "eupf", "gnb", "ue")
    subscriber = dc("exec", "-T", "mongo", "mongosh", "--quiet", "open5gs", "--eval",
                    'printjson(db.subscribers.findOne({imsi:"001010000000001"},{security:1,_id:0}))',
                    capture_output=True, text=True).stdout
    (out / "logs" / "subscriber-after.txt").write_text(subscriber)


def control(action, target=None):
    args = ["packetrusher", "control", "--socket", SOCKET, "--ue", "1", "--action", action, "--timeout", "45s"]
    if target:
        args += ["--target", target]
    status = json.loads(dc("exec", "-T", "ran", *args, capture_output=True, text=True).stdout)["ues"][0]
    print(f"   {action} {target or ''}: {status}")
    return status


def ping_ue(ue_ip, log):
    time.sleep(1)
    result = dc("exec", "-T", "ran", "ping", "-c", "2", "-i", "0.5", "-W", "2", "-I", ue_ip, DATA_NETWORK,
                check=False, capture_output=True, text=True)
    log.write(result.stdout)
    summary = re.search(r"\d+ packets transmitted.*", result.stdout)
    if summary is None:
        sys.exit(f"capture.py: ping from {ue_ip} printed no summary:\n{result.stdout}{result.stderr}")
    print("   " + summary.group(0))


def handover(out):
    """gNB 2 gets 10.33.0.31 in the same container."""
    core_up("ran")
    dc("exec", "-T", "ran", "ip", "addr", "add", "10.33.0.31/24", "dev", "eth0")

    print("== capture: PFCP association, NG setup x2, registration, PDU session, handovers ==")
    pr_log = out / "logs" / "packetrusher.log"
    with Capture(out / "raw.pcap", out):
        dc("up", "-d", "smf", "amf")
        time.sleep(8)
        with open(pr_log, "wb") as log:
            rusher = subprocess.Popen([*COMPOSE, "exec", "-T", "ran", "packetrusher", "--config", "/cfg/config.yml",
                                       "--tunnel-backend", "userspace", "multi-ue", "-n", "1", "--dedicatedGnb",
                                       "--number-of-gnbs", "2", "--tunnel", "--tunnel-vrf=false",
                                       "--control-socket", SOCKET], stdout=log, stderr=subprocess.STDOUT)
        try:
            until("the control socket", lambda: ok("exec", "-T", "ran", "test", "-S", SOCKET), 30)
            with open(out / "logs" / "ping.log", "w") as pings:
                control("wait")
                ue_ip = re.search(r"PDU session 1 address: (\S+)", pr_log.read_text()).group(1)
                ping_ue(ue_ip, pings)
                control("xn-handover", GNB2)
                ping_ue(ue_ip, pings)
                control("ng-handover-cancel", GNB1)
                until("Handover Cancel Acknowledge", lambda: pr_log.read_text().count("Handover Cancel Acknowledge") == 1, 15)
                ping_ue(ue_ip, pings)
                status = control("ng-handover", GNB1)
                ping_ue(ue_ip, pings)
        finally:
            rusher.terminate()
            reap(rusher)
        if status["gnb"] != GNB1:
            sys.exit(f"capture.py: UE ended on gNB {status['gnb']}")
    save_logs(out, "amf", "eupf")


# scenario -> (bring-up and capture, RAN image, compose profiles,
#              (pcap, tshark filter, pcapng) to keep, vectors)
SCENARIOS = {
    "registration": (registration, "ueransim-image", [],
                     [("raw.pcap", "sctp || pfcp || gtp", "registration-pdu.pcapng"),
                      ("probe.pcap", "pfcp || gtp || icmp", "eupf-probes.pcapng")], "vectors.json"),
    "handover": (handover, "packetrusher-image", ["--profile", "handover"],
                 [("raw.pcap", "sctp || pfcp || gtp", "handover.pcapng")], "handover.json"),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("scenario", choices=SCENARIOS)
    parser.add_argument("out", type=Path, help="output directory")
    parser.add_argument("--keep-up", action="store_true", help="leave the stack running")
    args = parser.parse_args()
    scenario, ran_image, profiles, pcaps, vectors = SCENARIOS[args.scenario]
    COMPOSE.extend(profiles)
    out = args.out.resolve()
    (out / "logs").mkdir(parents=True, exist_ok=True)

    print("== build + load Nix images ==")
    for attr in ("open5gs-image", ran_image):
        with open(nix_build(attr), "rb") as image:
            run("docker", "load", stdin=image)
    print("== core up ==")
    try:
        scenario(out)
    finally:
        if not args.keep_up:
            dc("down", "-v", "--remove-orphans")

    print("== filter + extract vectors ==")
    tools = Path(nix_build("extract-tools")) / "bin"
    for pcap, display, pcapng in pcaps:
        run(str(tools / "tshark"), "-r", str(out / pcap), "-Y", display, "-F", "pcapng", "-w", str(out / pcapng))
    run(str(tools / "python3"), "-I", str(HERE / "extract.py"), args.scenario, str(out / pcaps[0][2]),
        str(HERE), str(out / vectors), env={"PATH": str(tools)})
    print(f"== done: {', '.join(str(out / name) for _, _, name in pcaps)}, {out / vectors} ==")


if __name__ == "__main__":
    main()
