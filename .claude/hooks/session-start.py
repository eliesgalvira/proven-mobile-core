#!/usr/bin/env python3
# Provisions Bend and Lean in cloud sessions from GitHub release assets, which the default
# network level allows. Local machines install their own toolchain.
import hashlib
import os
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request
from pathlib import Path

BEND_VERSION = "2.0.39"
BEND_SHA256 = "6cf462fd8f70b094a4950ebb709a9c4ffd8f1d1189d9cedf1fd63cd5d041c7ab"
LEAN_VERSION = "4.34.0"
LEAN_SHA256 = "caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b"
BEND_HOME = Path("/opt/bend")
LEAN_DIR = Path.home() / ".elan/toolchains" / f"leanprover--lean4---v{LEAN_VERSION}"


def output(*cmd: str) -> str:
    try:
        return subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True).stdout.strip()
    except OSError:
        return ""


def fetch(url: str, dest: Path, sha256: str) -> None:
    for attempt in range(4):
        try:
            with urllib.request.urlopen(url) as r, open(dest, "wb") as f:
                shutil.copyfileobj(r, f)
            break
        except OSError:
            if attempt == 3:
                raise
    if hashlib.sha256(dest.read_bytes()).hexdigest() != sha256:
        sys.exit(f"{dest.name}: checksum mismatch")


def link(target: Path, name: str) -> None:
    path = Path("/usr/local/bin") / name
    path.unlink(missing_ok=True)
    path.symlink_to(target)


def main() -> None:
    if os.environ.get("CLAUDE_CODE_REMOTE") != "true":
        return
    os.environ.update(BEND_HOME=str(BEND_HOME), BEND_NO_TELEMETRY="1")
    with tempfile.TemporaryDirectory() as d:
        tmp = Path(d)
        if BEND_VERSION not in output(str(BEND_HOME / "bin/bend"), "version"):
            name = f"bend-{BEND_VERSION}-linux-x64.tar.gz"
            fetch(f"https://github.com/bendlang/bend/releases/download/v{BEND_VERSION}/{name}", tmp / name, BEND_SHA256)
            with tarfile.open(tmp / name) as t:
                t.extractall(tmp, filter="tar")
            shutil.rmtree(BEND_HOME, ignore_errors=True)
            (BEND_HOME / "bin").mkdir(parents=True)
            for item in ("bend2", "guide"):
                shutil.move(tmp / "bend" / item, BEND_HOME / item)
            shutil.move(tmp / "bend/bin/bend", BEND_HOME / "bin/bend")

        if f"version {LEAN_VERSION}" not in output(str(LEAN_DIR / "bin/lean"), "--version"):
            if shutil.which("zstd") is None:
                subprocess.run(["apt-get", "update", "-qq"], check=True, stdout=subprocess.DEVNULL)
                subprocess.run(["apt-get", "install", "-y", "-qq", "zstd"], check=True, stdout=subprocess.DEVNULL)
            name = f"lean-{LEAN_VERSION}-linux.tar.zst"
            fetch(f"https://github.com/leanprover/lean4/releases/download/v{LEAN_VERSION}/{name}", tmp / name, LEAN_SHA256)
            shutil.rmtree(LEAN_DIR, ignore_errors=True)
            LEAN_DIR.mkdir(parents=True)
            subprocess.run(["tar", "--zstd", "-xf", str(tmp / name), "-C", str(LEAN_DIR), "--strip-components=1"], check=True)

        link(BEND_HOME / "bin/bend", "bend")
        for name in ("lean", "leanc", "lake"):
            link(LEAN_DIR / "bin" / name, name)
        env_file = os.environ.get("CLAUDE_ENV_FILE")
        if env_file:
            with open(env_file, "a") as f:
                f.write(f"export BEND_HOME={BEND_HOME} BEND_NO_TELEMETRY=1\n")

        (tmp / "LAWS.bend").write_text("import Base\n\nlaw warm:\n  {0n == 0n : Nat}\n")
        (tmp / "PROOF.bend").write_text("import Base\nimport ./LAWS.bend as L\n\ndef L.warm():\n  {==}\n")
        warm = subprocess.run(["bend", "PROOF.bend", "--verdict"], cwd=tmp, capture_output=True, text=True)
        print((warm.stdout.splitlines() or [""])[-1])
        if warm.returncode:
            sys.exit(warm.returncode)

    first = lambda s: (s.splitlines() or [""])[0]
    print(f"toolchain: {output('bend', 'version')} | {first(output('lean', '--version'))} | {first(output('clang', '--version'))} | {output('cargo', '--version')}")


main()
