#!/usr/bin/env -S python3 -I
"""Blocks a push that would publish personal or orchestration data.

    scripts/privacy-check.py <remote>     as .githooks/pre-push, ref lines on stdin
    scripts/privacy-check.py --all        every object, message and ref in the repo

It reads what the push adds: new blobs (also inside gzip, bzip2, xz, ZIP and
base64), their paths, commit messages, author and committer, and ref names.
The rules here are generic. Literal private names (machines, users, known ids)
come from a pattern file outside the repo, read when it exists; its path is
$SPECK5G_PRIVACY_PATTERNS or ~/.config/5g-spec-kernel/privacy-patterns.json:

    {"words": [...],     whole tokens, also inside camelCase identifiers
     "phrases": [...],   case-insensitive text
     "except": {"<phrase or word>": ["<path glob>", ...]}}
"""
import base64, bz2, fnmatch, gzip, io, ipaddress, json, lzma, os, re, struct, subprocess, sys, zipfile
from pathlib import Path

ZERO = "0" * 40
IDENTITIES = {"Elies <68759092+eliesgalvira@users.noreply.github.com>", "Claude <noreply@anthropic.com>"}
EMAILS = {"68759092+eliesgalvira@users.noreply.github.com", "noreply@anthropic.com", "verylongusername1@3gpp.com"}
# The first commits the 2026-11-16 history rewrite changed; nothing that contains them goes back up.
OLD_HISTORY = {"ac754fd424d255827ccf5049d2ffe2de4c29a4df", "faa0aa210d454a8cf7a82156f9b0626ac7fdeb23"}
BINARIES = ["test-vectors/capture/*.pcapng"]
CAPTURE_NETS = [ipaddress.ip_network(n) for n in ("10.33.0.0/24", "10.45.0.0/16", "127.0.0.0/8")]
# The test bench's own key material, published with it so the captures can be reproduced (test-vectors/capture/NOTES.md).
KEY_FILES = {"test-vectors/capture/setup/hnet/curve25519-1.key"}
TEST_SECRETS = ["test-vectors/*", "e2e/edge.toml", "edge/config.example.toml"]

I = re.I
# Literals carry a [x] class so that this file passes its own check.
RULES = [
    ("1 personal path", re.compile(r"/home/[a-z_][a-z0-9_.-]*/|/Users/[A-Za-z][^/\s]*/|file:///hom[e]/|[A-Za-z]:\\Users\\|~/(?:Repos|Documents|Sandbox|\.cache|\.agents|\.claude|\.t3)\b")),
    ("3 tailscale", re.compile(r"(?<![\d.])100\.(?:6[4-9]|[7-9]\d|1[01]\d|12[0-7])\.\d{1,3}\.\d{1,3}(?![\d.])|\.ts\.net\b", I)),
    ("4 agent or thread id", re.compile(r"\bmcp:(?:launch:)?[0-9a-f]{8}|t3cod[e]://|t3-threa[d]://|T3 Code threa[d]|Claude-Sessio[n]:|claude\.ai/code/session_", I)),
    ("5 brief or transcript", re.compile(r"Encargo de Elie[s]|Elies, litera[l]|\.cache/coordinado[r]|delegaciones[\w-]*\.json", I)),
    ("7 credential", re.compile(r"\bgh[pousr]_[A-Za-z0-9]{36}|github_pat_\w{22,}|\bsk-ant-[\w-]{20,}|\bsk-(?:proj-)?[A-Za-z0-9]{32,}|\btskey-[\w-]{10,}|\bAKIA[0-9A-Z]{16}\b|\bxox[abprs]-[\w-]{10,}|\bglpat-[\w-]{20}|\bAIza[\w-]{35}")),
    ("9 home or own hardware", re.compile(r"misma cas[a]|mismaCas[a]|mismo ?propietari[o]|same (?:house|owner)\b|sin swa[p]|\b\d+(?:[.,]\d+)?\s*Gi?B\s+(?:de\s+)?(?:RAM|memoria|of RAM|of memory|swap)\b", I)),
]
PRIVATE_KEY = re.compile(r"-----BEGIN (?:[A-Z]+ )?PRIVATE KEY-----")
ASSIGNED_SECRET = re.compile(r"""(?i)(?:api[_-]?key|secret|token|passw(?:or)?d|private[_-]?key|access[_-]?key|bearer|\bkey|\bopc)["']?\s*[:=]\s*["']?([A-Za-z0-9+/_=-]{20,})""")
EMAIL = re.compile(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}")
DNI = re.compile(r"\b(\d{8})([A-Z])\b|\b([XYZ])(\d{7})([A-Z])\b")
IBAN = re.compile(r"\bES\d{2}(?: ?\d{4}){5}\b")
PHONE = re.compile(r"\+34[ -]?[6-9]\d{2}[ -]?\d{3}[ -]?\d{3}(?!\d)")
BASE64 = re.compile(rb"[A-Za-z0-9+/]{40,}={0,2}")
# Splits identifiers into words: fooBar -> foo, Bar; HTTPServer -> HTTP, Server.
CAMEL = re.compile(r"(?<=[^\W\dA-Z_])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][^\W\dA-Z_])|(?<=\d)(?=\D)|(?<=\D)(?=\d)")
BRIEF_PATHS = ["*ENCARGO*", "*.jsonl"]


def git(*args: str, input: bytes | None = None) -> bytes:
    return subprocess.run(["git", *args], input=input, stdout=subprocess.PIPE, check=True).stdout


def private_patterns() -> dict:
    path = Path(os.environ.get("SPECK5G_PRIVACY_PATTERNS") or Path.home() / ".config/5g-spec-kernel/privacy-patterns.json")
    return json.loads(path.read_text()) if path.is_file() else {}


def matches(glob_list, path: str) -> bool:
    return any(fnmatch.fnmatch(path, g) for g in glob_list)


def entropy(s: str) -> float:
    from math import log2
    return -sum(s.count(c) / len(s) * log2(s.count(c) / len(s)) for c in set(s))


class Checker:
    def __init__(self, private: dict):
        self.findings: list[str] = []
        self.words = {w.lower(): w for w in private.get("words", [])}
        self.phrases = [(p, re.compile(re.escape(p), I)) for p in private.get("phrases", [])]
        self.exceptions = private.get("except", {})

    def report(self, rule: str, where: str, text: str, start: int, end: int) -> None:
        line = text[max(0, start - 40):end + 40].replace("\n", " ")
        self.findings.append(f"{where}: rule {rule}: {text[start:end]!r} in …{line}…")

    def allowed(self, literal: str, path: str | None) -> bool:
        return path is not None and matches(self.exceptions.get(literal, []), path)

    def text(self, where: str, text: str, path: str | None = None) -> None:
        """Rules 1-10 on one piece of text; path is the file it came from, if any."""
        for rule, rx in RULES:
            for m in rx.finditer(text):
                self.report(rule, where, text, m.start(), m.end())
        low = text.lower()
        if any(w in low for w in self.words):
            for m in re.finditer(r"[^\W_]+", text):
                for t in CAMEL.sub(" ", m.group()).split():
                    w = self.words.get(t.lower())
                    if w and not self.allowed(w, path):
                        self.report("2 private name", where, text, m.start(), m.end())
        for literal, rx in self.phrases:
            if not self.allowed(literal, path):
                for m in rx.finditer(text):
                    self.report("8 private name", where, text, m.start(), m.end())
        for m in EMAIL.finditer(text):
            if m.group().lower() not in EMAILS:
                self.report("6 email", where, text, m.start(), m.end())
        for m in PRIVATE_KEY.finditer(text):
            if path not in KEY_FILES:
                self.report("7 credential", where, text, m.start(), m.end())
        for m in ASSIGNED_SECRET.finditer(text):
            if entropy(m.group(1)) > 3 and not (path and matches(TEST_SECRETS, path)):
                self.report("7 credential", where, text, m.start(), m.end())
        for m in DNI.finditer(text):
            if m.group(1):
                n, letter = int(m.group(1)), m.group(2)
            else:
                n, letter = int(str("XYZ".index(m.group(3))) + m.group(4)), m.group(5)
            if "TRWAGMYFPDXBNJZSQVHLCKE"[n % 23] == letter:
                self.report("10 DNI or NIE", where, text, m.start(), m.end())
        for m in IBAN.finditer(text):
            digits = m.group().replace(" ", "")
            if int(digits[4:] + "1428" + digits[2:4]) % 97 == 1:
                self.report("10 IBAN", where, text, m.start(), m.end())
        for m in PHONE.finditer(text):
            self.report("10 phone", where, text, m.start(), m.end())

    def blob(self, path: str, data: bytes, where: str) -> None:
        self.text(where + " (path)", path, path)
        if matches(BRIEF_PATHS, path):
            self.findings.append(f"{where}: rule 5 brief or transcript: path {path}")
        binary = b"\0" in data[:8000]
        if binary and not matches(BINARIES, path):
            self.findings.append(f"{where}: rule 11 binary: {path} is not in BINARIES")
        if path.endswith(".pcapng"):
            self.pcapng(where, data)
        for name, buf in self.expand(where, data):
            self.text(name, buf.decode("utf-8", "replace"), path)

    def expand(self, name: str, data: bytes, depth: int = 0):
        yield name, data
        if depth > 3:
            return
        inner = []
        try:
            if data[:2] == b"\x1f\x8b":
                inner.append(("gzip", gzip.decompress(data)))
            elif data[:3] == b"BZh":
                inner.append(("bzip2", bz2.decompress(data)))
            elif data[:6] == b"\xfd7zXZ\0":
                inner.append(("xz", lzma.decompress(data)))
            elif data[:4] == b"PK\x03\x04":
                z = zipfile.ZipFile(io.BytesIO(data))
                inner += [(n, z.read(n)) for n in z.namelist()]
            elif data[:4] in (b"(\xb5/\xfd", b"7z\xbc\xaf"):
                self.findings.append(f"{name}: rule 11 binary: zstd or 7z archive, not inspected")
        except Exception as e:
            self.findings.append(f"{name}: rule 11 binary: unreadable archive ({e})")
        for m in BASE64.finditer(data):
            try:
                dec = base64.b64decode(m.group(), validate=True)
            except ValueError:
                continue
            if dec[:2] == b"\x1f\x8b" or dec[:4] == b"PK\x03\x04" or sum(32 <= b < 127 or b in (9, 10, 13) for b in dec) > 0.9 * len(dec):
                inner.append(("base64", dec))
        for label, buf in inner:
            yield from self.expand(f"{name}!{label}", buf, depth + 1)

    def pcapng(self, where: str, d: bytes) -> None:
        """Rule 11 for captures: no host, OS, app or comment options, and only the test bench's addresses."""
        i, links = 0, []
        while i + 12 <= len(d):
            kind, length = struct.unpack_from("<II", d, i)
            if length < 12 or i + length > len(d):
                self.findings.append(f"{where}: rule 11 capture: malformed block at {i}")
                return
            body = d[i + 8:i + length - 4]
            if kind == 0x0A0D0D0A:
                self.options(where, body[16:], {1: "comment", 2: "hardware", 3: "OS", 4: "application"}, allow={4})
            elif kind == 1:
                links.append(struct.unpack_from("<H", body)[0])
                self.options(where, body[8:], {1: "comment", 2: "interface name", 3: "description", 12: "OS", 15: "hardware"}, allow={2})
            elif kind == 6:
                iface, _, _, captured = struct.unpack_from("<IIII", body)
                pkt = body[20:20 + captured]
                try:
                    self.packet(where, links[iface] if iface < len(links) else -1, pkt)
                except (struct.error, ValueError):
                    self.findings.append(f"{where}: rule 11 capture: truncated packet at {i}")
                self.options(where, body[20 + (captured + 3) // 4 * 4:], {1: "comment"})
            elif kind not in (5,):
                self.findings.append(f"{where}: rule 11 capture: block type {kind:#x} not allowed")
            i += length

    def options(self, where: str, opts: bytes, names: dict, allow: set = frozenset()) -> None:
        j = 0
        while j + 4 <= len(opts):
            code, length = struct.unpack_from("<HH", opts, j)
            if code == 0:
                return
            value = opts[j + 4:j + 4 + length]
            if code in names and code not in allow:
                self.findings.append(f"{where}: rule 11 capture: {names[code]} option {value[:60]!r}")
            elif code in allow:
                self.text(where + f" (capture {names[code]})", value.decode("utf-8", "replace"))
            j += 4 + (length + 3) // 4 * 4

    def packet(self, where: str, link: int, pkt: bytes) -> None:
        if link == 1:
            off, ethertype = 14, struct.unpack_from(">H", pkt, 12)[0]
            while ethertype in (0x8100, 0x88A8):
                ethertype, off = struct.unpack_from(">H", pkt, off + 2)[0], off + 4
        else:
            self.findings.append(f"{where}: rule 11 capture: link type {link} not allowed")
            return
        if ethertype == 0x0806:
            return
        if ethertype != 0x0800:
            self.findings.append(f"{where}: rule 11 capture: ethertype {ethertype:#06x} not allowed")
            return
        for a in (pkt[off + 12:off + 16], pkt[off + 16:off + 20]):
            ip = ipaddress.ip_address(a)
            if not any(ip in n for n in CAPTURE_NETS):
                self.findings.append(f"{where}: rule 11 capture: address {ip} outside the test bench")

    def commit(self, oid: str, author: str, committer: str, message: str) -> None:
        for who in (author, committer):
            if who not in IDENTITIES:
                self.findings.append(f"commit {oid[:10]}: rule 6 identity: {who}")
        self.text(f"commit {oid[:10]} message", message)


def scan(checker: Checker, revs: list[str]) -> None:
    objects = git("rev-list", "--objects", *revs).decode().splitlines()
    paths: dict[str, str] = {}
    for row in objects:
        oid, _, path = row.partition(" ")
        if path:
            paths.setdefault(oid, path)
    batch = git("cat-file", "--batch", input="".join(o + "\n" for o in paths).encode())
    i = 0
    while i < len(batch):
        header_end = batch.index(b"\n", i)
        oid, kind, size = batch[i:header_end].decode().split()
        data = batch[header_end + 1:header_end + 1 + int(size)]
        i = header_end + 2 + int(size)
        if kind == "blob":
            checker.blob(paths[oid], data, f"{paths[oid]} ({oid[:10]})")
    log = git("log", "--format=%H%x00%an <%ae>%x00%cn <%ce>%x00%B%x01", *revs).decode("utf-8", "replace")
    for rec in log.split("\x01"):
        fields = rec.lstrip("\n").split("\x00")
        if len(fields) == 4:
            checker.commit(*fields)


def contains_old_history(tip: str) -> list[str]:
    present = [c for c in OLD_HISTORY if subprocess.run(["git", "cat-file", "-e", c + "^{commit}"], stderr=subprocess.DEVNULL).returncode == 0]
    return [c for c in present if subprocess.run(["git", "merge-base", "--is-ancestor", c, tip]).returncode == 0]


def main() -> int:
    checker = Checker(private_patterns())
    if sys.argv[1:] == ["--all"]:
        scan(checker, ["--all"])
        for ref in git("for-each-ref", "--format=%(refname)").decode().split():
            checker.text(f"ref {ref}", ref)
            for old in contains_old_history(ref):
                checker.findings.append(f"{ref}: rule 12 old history: contains {old[:10]}, from before the history rewrite")
    elif len(sys.argv) >= 2:
        remote = sys.argv[1]
        for line in sys.stdin.read().splitlines():
            _, local, remote_ref, remote_sha = line.split()
            if local == ZERO:
                continue
            checker.text(f"ref {remote_ref}", remote_ref)
            for old in contains_old_history(local):
                checker.findings.append(f"{remote_ref}: rule 12 old history: contains {old[:10]}, from before the history rewrite")
            known = [remote_sha] if remote_sha != ZERO and subprocess.run(["git", "cat-file", "-e", remote_sha], stderr=subprocess.DEVNULL).returncode == 0 else []
            scan(checker, [local, "--not", f"--remotes={remote}", *known])
    else:
        print(__doc__, file=sys.stderr)
        return 2
    for f in dict.fromkeys(checker.findings):
        print(f, file=sys.stderr)
    if checker.findings:
        print(f"\nprivacy-check: {len(set(checker.findings))} findings; nothing was pushed. See AGENTS.md § Publishing.", file=sys.stderr)
        return 1
    return 0


sys.exit(main())
