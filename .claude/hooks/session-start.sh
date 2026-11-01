#!/usr/bin/env bash
# Provisions Bend and Lean in cloud sessions from GitHub release assets, which the default
# network level allows. Local machines install their own toolchain.
set -euo pipefail
[ "${CLAUDE_CODE_REMOTE:-}" = "true" ] || exit 0

BEND_VERSION=2.0.39
BEND_SHA256=6cf462fd8f70b094a4950ebb709a9c4ffd8f1d1189d9cedf1fd63cd5d041c7ab
LEAN_VERSION=4.34.0
LEAN_SHA256=caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b
export BEND_HOME=/opt/bend BEND_NO_TELEMETRY=1
LEAN_DIR="$HOME/.elan/toolchains/leanprover--lean4---v$LEAN_VERSION"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

fetch() {
  curl -fsSL --retry 3 -o "$tmp/$2" "$1"
  echo "$3  $tmp/$2" | sha256sum -c - >/dev/null
}

if ! "$BEND_HOME/bin/bend" version 2>/dev/null | grep -q "$BEND_VERSION"; then
  name="bend-$BEND_VERSION-linux-x64.tar.gz"
  fetch "https://github.com/bendlang/bend/releases/download/v$BEND_VERSION/$name" "$name" "$BEND_SHA256"
  tar -xzf "$tmp/$name" -C "$tmp"
  rm -rf "$BEND_HOME"
  mkdir -p "$BEND_HOME/bin"
  mv "$tmp/bend/bend2" "$tmp/bend/guide" "$BEND_HOME/"
  mv "$tmp/bend/bin/bend" "$BEND_HOME/bin/bend"
fi

if ! "$LEAN_DIR/bin/lean" --version 2>/dev/null | grep -q "version $LEAN_VERSION"; then
  command -v zstd >/dev/null || { apt-get update -qq && apt-get install -y -qq zstd; } >/dev/null
  name="lean-$LEAN_VERSION-linux.tar.zst"
  fetch "https://github.com/leanprover/lean4/releases/download/v$LEAN_VERSION/$name" "$name" "$LEAN_SHA256"
  rm -rf "$LEAN_DIR"
  mkdir -p "$LEAN_DIR"
  tar --zstd -xf "$tmp/$name" -C "$LEAN_DIR" --strip-components=1
fi

ln -sf "$BEND_HOME/bin/bend" /usr/local/bin/bend
for bin in lean leanc lake; do
  ln -sf "$LEAN_DIR/bin/$bin" "/usr/local/bin/$bin"
done
if [ -n "${CLAUDE_ENV_FILE:-}" ]; then
  printf 'export BEND_HOME=%s BEND_NO_TELEMETRY=1\n' "$BEND_HOME" >> "$CLAUDE_ENV_FILE"
fi

printf 'import Base\n\nlaw warm:\n  {0n == 0n : Nat}\n' > "$tmp/LAWS.bend"
printf 'import Base\nimport ./LAWS.bend as L\n\ndef L.warm():\n  {==}\n' > "$tmp/PROOF.bend"
(cd "$tmp" && bend PROOF.bend --verdict | tail -1)

echo "toolchain: $(bend version 2>&1) | $(lean --version 2>&1 | head -1) | $(clang --version 2>&1 | head -1) | $(cargo --version 2>&1)"
