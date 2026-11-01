#!/usr/bin/env python3
"""Extract the ASN.1 modules of 3GPP TS 38.413 (NGAP) from the 3GPP zip or docx.

Usage: python3 -I extract.py 38413-j40.zip OUT_DIR

The spec marks every ASN.1 block with "-- ASN1START" and "-- ASN1STOP" lines.
Each block is one module and is written to OUT_DIR/<ModuleName>.asn, without the
marker lines. Standard library only; the input is treated as untrusted.
"""
import pathlib
import re
import sys
import xml.etree.ElementTree as ET
import zipfile

W = "{http://schemas.openxmlformats.org/wordprocessingml/2006/main}"
MAX_XML_BYTES = 64 << 20

# Word typography that may leak into code paragraphs, mapped back to ASCII.
ASCII = str.maketrans({
    " ": " ", " ": " ", " ": " ", " ": " ",
    "‐": "-", "‑": "-", "–": "-", "—": "-", "−": "-",
    "‘": "'", "’": "'", "“": '"', "”": '"',
})


def document_xml(path):
    with zipfile.ZipFile(path) as z:
        docx = [n for n in z.namelist() if n.lower().endswith(".docx")]
        if docx:
            if len(docx) != 1:
                sys.exit(f"expected one .docx in {path}, found {docx}")
            with z.open(docx[0]) as inner, zipfile.ZipFile(inner) as d:
                return read_bounded(d, "word/document.xml")
        return read_bounded(z, "word/document.xml")


def read_bounded(z, name):
    if z.getinfo(name).file_size > MAX_XML_BYTES:
        sys.exit(f"{name} is larger than {MAX_XML_BYTES} bytes")
    return z.read(name)


def paragraph_text(p):
    out = []
    for e in p.iter():
        if e.tag == W + "t":
            out.append(e.text or "")
        elif e.tag == W + "tab":
            out.append("\t")
        elif e.tag in (W + "br", W + "cr"):
            out.append("\n")
        elif e.tag == W + "noBreakHyphen":
            out.append("-")
    return "".join(out).translate(ASCII)


def asn1_blocks(xml):
    body = ET.fromstring(xml).find(W + "body")
    block = None
    for p in body.iter(W + "p"):
        for line in paragraph_text(p).split("\n"):
            marker = line.strip()
            if marker == "-- ASN1START":
                if block is not None:
                    sys.exit("ASN1START inside an open block")
                block = []
            elif marker == "-- ASN1STOP":
                if block is None:
                    sys.exit("ASN1STOP without ASN1START")
                yield block
                block = None
            elif block is not None:
                block.append(line.rstrip())
    if block is not None:
        sys.exit("unterminated ASN1START block")


def main(src, out_dir):
    out = pathlib.Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)
    seen = set()
    for lines in asn1_blocks(document_xml(src)):
        text = "\n".join(lines).strip("\n") + "\n"
        m = re.search(r"^\s*([A-Z][A-Za-z0-9-]*)\s*(\{[^}]*\})?\s*DEFINITIONS\b", text, re.M | re.S)
        if not m:
            sys.exit("block without a module header:\n" + text[:300])
        bad = sorted({c for c in text if ord(c) > 126 or (ord(c) < 32 and c not in "\t\n")})
        if bad:
            sys.exit(f"{m.group(1)}: non-ASCII characters left: {bad!r}")
        if m.group(1) in seen:
            sys.exit(f"module {m.group(1)} appears twice")
        seen.add(m.group(1))
        target = out / f"{m.group(1)}.asn"
        target.write_text(text)
        print(f"{target.name}\t{text.count(chr(10))} lines")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    main(sys.argv[1], sys.argv[2])
