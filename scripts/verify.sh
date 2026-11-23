#!/usr/bin/env bash
set -euo pipefail

PARANOID=0
RUN_COMPARATOR=1
for arg in "$@"; do
  case "$arg" in
    --paranoid) PARANOID=1 ;;
    --no-comparator) RUN_COMPARATOR=0 ;;
    *) echo "Usage: $0 [--paranoid] [--no-comparator]"; exit 2 ;;
  esac
done

echo "=== 1. Fetching Mathlib cache (without lake update) ==="
lake exe cache get || true

echo "=== 2. Building SignedGraphs and Solution ==="
lake build SignedGraphs Solution

echo "=== 3. Static anti-cheat hygiene check ==="
hygiene_hits=$(grep -rnE '\b(sorry|sorryAx|admit|axiom|native_decide|unsafe|unsafeCast|implemented_by|extern|partial|skipKernelTC|local instance)\b' \
  SignedGraphs.lean SignedGraphs/ comparator/ChallengeDefs.lean comparator/Solution.lean \
  | grep -vE '^[^:]+:[0-9]+:[[:space:]]*(--|/[-!]|/-)' \
  | grep -vE 'AuditAxioms\.lean' || true)
if [ -n "$hygiene_hits" ]; then
  echo "HYGIENE CHECK FAILED:"
  echo "$hygiene_hits"
  exit 1
fi
echo "HYGIENE CHECK PASSED (0 forbidden constructs)."

echo "=== 4. Axiom audit (SignedGraphs/AuditAxioms.lean) ==="
lake env lean SignedGraphs/AuditAxioms.lean

if [ "$RUN_COMPARATOR" -eq 1 ]; then
  if [ "$PARANOID" -eq 1 ]; then
    echo "=== 5. Independent kernel replay: lake comparator --paranoid ==="
    lake comparator --paranoid
  else
    echo "=== 5. Comparator verification: lake comparator ==="
    lake comparator
  fi
fi

echo "ALL CHECKS PASSED."
