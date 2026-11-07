"""Capture one Xn handover and two N2 handovers, the first cancelled, against Open5GS.

    python3 -I handover.py <output dir>

Builds the Open5GS and PacketRusher images (flake.nix) and docker-loads them, starts
the core and eUPF, then records on the Docker bridge: PFCP association, NG Setup of
two gNBs, registration, PDU session, Xn handover gNB 1 -> 2 (Path Switch), N2
handover gNB 2 -> 1 cancelled after the Handover Command, and N2 handover gNB 2 -> 1,
with a ping from the UE before the first handover and after each one. It saves the
logs, tears the stack down and turns the capture into handover.pcapng and
handover.json with extract.py.

Needs nix (flakes), docker with compose v2 and the host's sctp kernel module.
"""
import json
import re
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = Path(sys.argv[1]).resolve()
COMPOSE = ["docker", "compose", "-f", str(HERE / "docker-compose.yml"), "--profile", "handover"]
FILTER = "sctp or udp port 8805 or udp port 2152 or icmp"
SOCKET = "/tmp/pr.sock"
GNB1, GNB2 = "00000001", "00000002"
DATA_NETWORK = "10.33.0.40"


def run(*args, **kw):
    return subprocess.run(args, **{"check": True, **kw})


def dc(*args, **kw):
    return run(*COMPOSE, *args, **kw)


def nix_build(attr):
    return run("nix", "build", "--no-link", "--print-out-paths", f"{HERE}#{attr}",
               capture_output=True, text=True).stdout.strip()


def until(what, test, seconds):
    for _ in range(seconds * 2):
        if test():
            return
        time.sleep(0.5)
    sys.exit(f"handover.py: timed out waiting for {what}")


def control(action, target=None):
    args = ["packetrusher", "control", "--socket", SOCKET, "--ue", "1", "--action", action, "--timeout", "45s"]
    if target:
        args += ["--target", target]
    status = json.loads(dc("exec", "-T", "ran", *args, capture_output=True, text=True).stdout)["ues"][0]
    print(f"   {action} {target or ''}: {status}")
    return status


def ping(ue_ip, log):
    time.sleep(1)
    result = dc("exec", "-T", "ran", "ping", "-c", "2", "-i", "0.5", "-W", "2", "-I", ue_ip, DATA_NETWORK,
                check=False, capture_output=True, text=True)
    log.write(result.stdout)
    print("   " + result.stdout.strip().splitlines()[-2])


def capture_stack():
    dc("up", "-d", "--quiet-pull", "mongo")
    until("mongo", lambda: subprocess.run(
        [*COMPOSE, "exec", "-T", "mongo", "mongosh", "--quiet", "--eval", "db.runCommand({ping:1}).ok"],
        capture_output=True).returncode == 0, 30)
    dc("exec", "-T", "mongo", "mongosh", "--quiet", "open5gs", "/subscriber.js", capture_output=True)
    dc("up", "-d", "nrf")
    time.sleep(2)
    dc("up", "-d", "--quiet-pull", "ausf", "udm", "udr", "pcf", "nssf", "bsf", "eupf", "dn", "capture", "ran")
    dc("exec", "-T", "ran", "ip", "addr", "add", "10.33.0.31/24", "dev", "eth0")
    # eUPF's XDP program sends downlink G-PDUs only to a gNB address its ARP table holds.
    for gnb_ip in ("10.33.0.30", "10.33.0.31"):
        dc("exec", "-T", "ran", "ping", "-c", "1", "-I", gnb_ip, "10.33.0.20", capture_output=True)
    time.sleep(3)

    print("== capture: PFCP association, NG setup x2, registration, PDU session, handovers ==")
    with open(OUT / "raw.pcap", "wb") as pcap, open(OUT / "logs" / "tcpdump.log", "wb") as err:
        capture = subprocess.Popen([*COMPOSE, "exec", "-T", "capture", "tcpdump", "-i", "br-5gcap", "-U",
                                    "-s", "0", "-w", "-", FILTER], stdout=pcap, stderr=err)
    time.sleep(2)
    dc("up", "-d", "smf", "amf")
    time.sleep(8)
    pr_log = OUT / "logs" / "packetrusher.log"
    with open(pr_log, "wb") as log:
        subprocess.Popen([*COMPOSE, "exec", "-T", "ran", "packetrusher", "--config", "/cfg/config.yml",
                          "--tunnel-backend", "userspace", "multi-ue", "-n", "1", "--dedicatedGnb",
                          "--number-of-gnbs", "2", "--tunnel", "--tunnel-vrf=false",
                          "--control-socket", SOCKET], stdout=log, stderr=subprocess.STDOUT)
    until("the control socket", lambda: subprocess.run(
        [*COMPOSE, "exec", "-T", "ran", "test", "-S", SOCKET], capture_output=True).returncode == 0, 30)
    cancel_acks = lambda: pr_log.read_text().count("Handover Cancel Acknowledge")
    with open(OUT / "logs" / "ping.log", "w") as pings:
        control("wait")
        ue_ip = re.search(r"PDU session 1 address: (\S+)", pr_log.read_text()).group(1)
        ping(ue_ip, pings)
        control("xn-handover", GNB2)
        ping(ue_ip, pings)
        control("ng-handover-cancel", GNB1)
        until("Handover Cancel Acknowledge", lambda: cancel_acks() == 1, 15)
        ping(ue_ip, pings)
        status = control("ng-handover", GNB1)
        ping(ue_ip, pings)
    if status["gnb"] != GNB1:
        sys.exit(f"handover.py: UE ended on gNB {status['gnb']}")
    time.sleep(2)
    dc("exec", "-T", "capture", "pkill", "-INT", "tcpdump", check=False)
    capture.wait(timeout=10)

    print("== logs ==")
    for service in ("amf", "eupf"):
        text = dc("logs", "--no-color", service, capture_output=True, text=True).stdout
        (OUT / "logs" / f"{service}.log").write_text(re.sub(r"\x1b\[[0-9;]*m", "", text))


def main():
    (OUT / "logs").mkdir(parents=True, exist_ok=True)
    print("== build + load Nix images ==")
    for attr in ("open5gs-image", "packetrusher-image"):
        with open(nix_build(attr), "rb") as image:
            run("docker", "load", stdin=image)

    print("== core up ==")
    dc("down", "-v", "--remove-orphans", capture_output=True)
    try:
        capture_stack()
    finally:
        dc("down", "-v", "--remove-orphans")

    print("== filter + extract vectors ==")
    tools = Path(nix_build("extract-tools")) / "bin"
    run(str(tools / "tshark"), "-r", str(OUT / "raw.pcap"), "-Y", "sctp || pfcp || gtp", "-F", "pcapng",
        "-w", str(OUT / "handover.pcapng"))
    run(str(tools / "python3"), "-I", str(HERE / "extract.py"), "handover", str(OUT / "handover.pcapng"),
        str(HERE), str(OUT / "handover.json"), env={"PATH": str(tools)})
    print(f"== done: {OUT}/handover.pcapng, {OUT}/handover.json ==")


if __name__ == "__main__":
    main()
