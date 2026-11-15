#!/usr/bin/env nu
# The gate: docs/spec/milestone-1.md § Verification. Any failing command
# stops it, so the quick checks come first. `--verdict` runs the everyday
# checker before its own kernel, so the spec's step 2 is inside it. With
# --strict, the acceptance list requires every law it names, done ticket or
# not.

def step [name: string] {
  print $"\n== ($name)"
}

def main [--strict] {
  cd ($env.FILE_PWD | path dirname)

  step "no @unsafe or foreign import outside kernel/main.bend"
  let unsafe = glob --no-dir kernel/**/*.bend
    | each {|f| $f | path relative-to (pwd) }
    | where $it != "kernel/main.bend"
    | each {|f| open --raw $f | lines | enumerate | where {|l| $l.item =~ '@unsafe|^\s*def\s+\S+\?\(|^\s*import\s+"' } | each {|l| $"($f):($l.index + 1):($l.item)" } }
    | flatten
  if ($unsafe | is-not-empty) {
    $unsafe | each {|l| print $l }
    error make {msg: "unsafe or foreign code outside kernel/main.bend"}
  }

  step "acceptance list"
  ^python3 -I scripts/acceptance.py ...(if $strict { [--strict] } else { [] })

  step "bend kernel/PROOF.bend --verdict"
  ^timeout 1500 bend kernel/PROOF.bend --verdict

  step "kernel tests"
  ^nu scripts/test-kernel.nu --strict

  step "cargo test (edge)"
  do { cd edge; ^timeout 1500 cargo test --quiet }

  step "ngap: generated code is current and agrees with pycrate on the NGAP vectors"
  ^python3 -I tools/ngap-gen/test_gen.py
  ^python3 -I tools/ngap-gen/oracle.py

  print "\nCHECK OK"
}
