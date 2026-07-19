#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
oracle="$repo_root/.lake/build/bin/adequacy_oracle"

lake --dir "$repo_root" build adequacy_oracle

assert_exit() {
  local expected=$1
  local fixture=$2
  shift 2

  local output
  local actual
  set +e
  output=$(
    cd "$repo_root"
    "$oracle" "$@" "$fixture" 2>&1
  )
  actual=$?
  set -e

  if [[ $actual -ne $expected ]]; then
    printf 'expected exit %s, got %s for %s\n%s\n' "$expected" "$actual" "$fixture" "$output" >&2
    return 1
  fi

  if [[ $output != *"adequacy check  $fixture"* ]]; then
    printf 'missing neutral adequacy banner for %s\n%s\n' "$fixture" "$output" >&2
    return 1
  fi

  if [[ $output == *"seal adequacy check"* ]]; then
    printf 'found stale seal branding for %s\n%s\n' "$fixture" "$output" >&2
    return 1
  fi

  if [[ $output != *"WARN VACUOUS over observed finite sample"* ]]; then
    printf 'missing vacuous warning for %s\n%s\n' "$fixture" "$output" >&2
    return 1
  fi
}

empty_fixture="$repo_root/Test/fixtures/adequacy-empty.json"
single_label_fixture="$repo_root/Test/fixtures/adequacy-single-label.json"

assert_exit 3 "$empty_fixture"
assert_exit 3 "$single_label_fixture"
assert_exit 0 "$empty_fixture" --allow-vacuous
assert_exit 0 "$single_label_fixture" --allow-vacuous

echo "adequacy CLI regression tests passed"
