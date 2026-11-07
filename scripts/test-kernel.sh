#!/usr/bin/env nu
# Runs every kernel/tests/*.bend. Each must exit 0, print no FAIL line and
# print a line starting PASS or SKIP. With --strict, SKIP fails too.
# Tests are compiled to a binary first, into build/kernel-tests: `bend
# file.bend` overflows the machine stack on million-element lists where the
# binary does not (Bend WONTFIX, #798).

def passes [file: string, bin: string, strict: bool]: nothing -> bool {
  let exe = $bin | path join ($file | path parse | get stem)
  let built = do { ^timeout 300 bend $file -o $exe } | complete
  let ran = if $built.exit_code == 0 { do { ^timeout 300 $exe } | complete } else { $built }
  let out = $ran.stdout + $ran.stderr | lines
  $out | each {|l| print $"($file): ($l)" }
  let ok = $ran.exit_code == 0 and not ($out | any {|l| $l starts-with FAIL }) and ($out | any {|l| ($l starts-with PASS) or ($l starts-with SKIP) })
  if not $ok {
    print $"($file): FAILED \(exit ($ran.exit_code)\)"
    false
  } else if $strict and ($out | any {|l| $l starts-with SKIP }) {
    print $"($file): SKIPPED tests are not allowed with --strict"
    false
  } else {
    true
  }
}

def main [--strict] {
  cd ($env.FILE_PWD | path dirname)
  let bin = "build/kernel-tests"
  mkdir $bin
  let results = glob --no-dir kernel/tests/*.bend | sort | each {|f| passes ($f | path relative-to (pwd)) $bin $strict }
  if not ($results | all {|ok| $ok }) { exit 1 }
}
