#!/usr/bin/env nu
# The gate: docs/spec/milestone-1.md § Verification. Any failing command
# stops it.

def step [name: string] {
  print $"\n== ($name)"
}

def main [] {
  cd ($env.FILE_PWD | path dirname)

  step "1. no @unsafe or foreign import outside kernel/main.bend"
  let unsafe = glob --no-dir kernel/**/*.bend
    | each {|f| $f | path relative-to (pwd) }
    | where $it != "kernel/main.bend"
    | each {|f| open --raw $f | lines | enumerate | where {|l| $l.item =~ '@unsafe|^\s*def\s+\S+\?\(|^\s*import\s+"' } | each {|l| $"($f):($l.index + 1):($l.item)" } }
    | flatten
  if ($unsafe | is-not-empty) {
    $unsafe | each {|l| print $l }
    error make {msg: "unsafe or foreign code outside kernel/main.bend"}
  }

  step "2. bend kernel/PROOF.bend"
  ^timeout 1500 bend kernel/PROOF.bend

  step "3. bend kernel/PROOF.bend --verdict"
  ^timeout 1500 bend kernel/PROOF.bend --verdict

  step "4. kernel tests"
  ^nu scripts/test-kernel.sh

  step "5. cargo test (edge)"
  do { cd edge; ^timeout 1500 cargo test --quiet }

  step "6. acceptance list"
  ^python3 -I scripts/acceptance.py

  step "7. ngap: generated code is current and agrees with pycrate on the capture"
  ^python3 -I tools/ngap-gen/test_gen.py
  ^python3 -I tools/ngap-gen/oracle.py

  print "\nCHECK OK"
}
