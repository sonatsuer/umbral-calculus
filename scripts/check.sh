#!/usr/bin/env bash
# Build the development and fail on any `sorry`.
#
# The check reads Lean's own "declaration uses 'sorry'" warning rather than
# grepping sources, so it cannot be fooled by the word appearing in a comment
# and cannot miss a `sorry` introduced by a tactic. Lake replays warnings from
# cache, so this works on an up-to-date build too.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "==> lake build"
out=$(lake build 2>&1) || { echo "$out"; echo "FAIL: build failed" >&2; exit 1; }
echo "$out"

echo "==> checking for sorry"
if echo "$out" | grep -q "declaration uses 'sorry'"; then
  echo "$out" | grep "declaration uses 'sorry'" >&2
  echo "FAIL: sorry found" >&2
  exit 1
fi
echo "OK: no sorry"

# Every `free_*` theorem must be closed by the abstraction theorem applied to
# nothing but the term. That is what makes its statement *definitionally* the
# logical relation at its type: a weaker statement, or a stronger one, stops
# typechecking. Without the check it is easy to "fix" such a theorem by adding
# a tactic block, which silently turns it back into a consequence.
echo "==> checking free_* theorems are closed by a bare abstraction theorem"
bad=$(awk '
  /^theorem free_/ { inthm = 1; name = $2; line = FNR; next }
  inthm && /:=[[:space:]]*$/ { expect = 1; inthm = 0; next }
  expect {
    if ($0 !~ /^  [po]abstraction_closed .* t$/)
      printf "%s:%d: %s is not closed by a bare abstraction theorem: %s\n", FILENAME, FNR, name, $0
    expect = 0
  }
' $(find FreeThms -name '*.lean'))
if [ -n "$bad" ]; then echo "$bad" >&2; echo "FAIL: see above" >&2; exit 1; fi
count=$(grep -rc "^theorem free_" FreeThms --include='*.lean' | awk -F: '{s+=$2} END {print s}')
echo "OK: $count free_* theorems, each the unfolded logical relation at its type"
