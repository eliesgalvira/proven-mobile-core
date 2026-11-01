#!/usr/bin/env bash
# Provisions Bend and Lean in cloud sessions. Local machines install their own toolchain.
set -euo pipefail
[ "${CLAUDE_CODE_REMOTE:-}" = "true" ] || exit 0

BEND_VERSION=2.0.39
BEND_SHA256=6cf462fd8f70b094a4950ebb709a9c4ffd8f1d1189d9cedf1fd63cd5d041c7ab
LEAN_TOOLCHAIN=leanprover/lean4:v4.34.0
export BEND_HOME=/opt/bend BEND_NO_TELEMETRY=1
ELAN_BIN="$HOME/.elan/bin"

if ! "$BEND_HOME/bin/bend" version 2>/dev/null | grep -q "$BEND_VERSION"; then
  tmp=$(mktemp -d)
  trap 'rm -rf "$tmp"' EXIT
  name="bend-$BEND_VERSION-linux-x64.tar.gz"
  curl -fsSL -o "$tmp/$name" "https://github.com/bendlang/bend/releases/download/v$BEND_VERSION/$name"
  echo "$BEND_SHA256  $tmp/$name" | sha256sum -c - >/dev/null
  tar -xzf "$tmp/$name" -C "$tmp"
  rm -rf "$BEND_HOME"
  mkdir -p "$BEND_HOME/bin"
  mv "$tmp/bend/bend2" "$tmp/bend/guide" "$BEND_HOME/"
  mv "$tmp/bend/bin/bend" "$BEND_HOME/bin/bend"
fi

if ! "$ELAN_BIN/lean" --version 2>/dev/null | grep -q "4.34.0"; then
  curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --no-modify-path --default-toolchain none >/dev/null
  "$ELAN_BIN/elan" toolchain install "$LEAN_TOOLCHAIN" >/dev/null
  "$ELAN_BIN/elan" default "$LEAN_TOOLCHAIN" >/dev/null
fi

for bin in "$BEND_HOME"/bin/* "$ELAN_BIN"/*; do
  ln -sf "$bin" /usr/local/bin/
done
if [ -n "${CLAUDE_ENV_FILE:-}" ]; then
  printf 'export BEND_HOME=%s BEND_NO_TELEMETRY=1\n' "$BEND_HOME" >> "$CLAUDE_ENV_FILE"
fi

warm=$(mktemp -d)
printf 'import Base\n\nlaw warm:\n  {0n == 0n : Nat}\n' > "$warm/LAWS.bend"
printf 'import Base\nimport ./LAWS.bend as L\n\ndef L.warm():\n  {==}\n' > "$warm/PROOF.bend"
(cd "$warm" && bend PROOF.bend --verdict | tail -1)
rm -rf "$warm"

echo "toolchain: $(bend version 2>&1) | $(lean --version 2>&1 | head -1) | $(clang --version 2>&1 | head -1) | $(cargo --version 2>&1)"
