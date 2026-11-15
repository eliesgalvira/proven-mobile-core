#!/usr/bin/env nu
# Runs kernel/tests/*.bend, or only the named ones (`pdu_session` or
# `kernel/tests/pdu_session.bend`), --jobs at a time. Each must exit 0, print
# no FAIL line and print a line starting PASS or SKIP. With --strict, SKIP
# fails too. Tests are compiled to a binary first, into build/kernel-tests:
# `bend file.bend` overflows the machine stack on million-element lists where
# the binary does not (Bend WONTFIX, #798).

def passes [file: string, bin: string, strict: bool]: nothing -> bool {
  let exe = $bin | path join ($file | path parse | get stem)
  let built = do { ^timeout 300 bend $file -o $exe } | complete
  let ran = if $built.exit_code == 0 { do { ^timeout 300 $exe } | complete } else { $built }
  let out = $ran.stdout + $ran.stderr | lines
  let ok = $ran.exit_code == 0 and not ($out | any {|l| $l starts-with FAIL }) and ($out | any {|l| ($l starts-with PASS) or ($l starts-with SKIP) })
  let verdict = if not $ok {
    [$"FAILED \(exit ($ran.exit_code)\)"]
  } else if $strict and ($out | any {|l| $l starts-with SKIP }) {
    ["SKIPPED tests are not allowed with --strict"]
  } else {
    []
  }
  $out ++ $verdict | each {|l| $"($file): ($l)" } | str join "\n" | print
  $verdict | is-empty
}

def main [--strict, --jobs: int = 6, ...tests: string] {
  cd ($env.FILE_PWD | path dirname)
  let bin = "build/kernel-tests"
  mkdir $bin
  let files = if ($tests | is-empty) {
    glob --no-dir kernel/tests/*.bend | each {|f| $f | path relative-to (pwd) }
  } else {
    $tests | each {|t| $"kernel/tests/($t | path parse | get stem).bend" }
  }
  let results = $files | par-each --threads $jobs {|f| passes $f $bin $strict }
  if not ($results | all {|ok| $ok }) { exit 1 }
}
