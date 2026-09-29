#!/usr/bin/env bash
# Axiom gate for the trusted library EBCMCategory (legacy tree; see ../README.md).
#
#   bash scripts/axiom_gate.sh            build the library, then run the checks below
#   bash scripts/axiom_gate.sh --no-build skip `lake build` (CI builds first)
#
# Fails (exit 1) if
#   1. an `axiom` declaration appears in EBCMCategory/ or EBCMCategory.lean (source check);
#   2. scripts/AxiomGate.lean does not import exactly the modules under EBCMCategory/;
#   3. some constant declared in an EBCMCategory.* module is an axiom, or depends on an axiom
#      other than propext, Quot.sound and Classical.choice (this includes sorryAx and
#      Lean.ofReduceBool); this is `#print axioms` for every declaration (scripts/AxiomGate.lean).
# Long commands are wrapped in `perl -e 'alarm N'` (this machine has no `timeout`).
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2
BUILD=1
for arg in "$@"; do
  case "$arg" in
    --no-build) BUILD=0 ;;
    -h|--help) sed -n '2,13p' "$0"; exit 0 ;;
    *) echo "unknown option: $arg" >&2; exit 2 ;;
  esac
done
ALARM=${AXIOM_GATE_ALARM:-1800}
with_alarm() { perl -e 'alarm shift; exec @ARGV' "$ALARM" "$@"; }
status=0

echo "== [1/3] source check: no axiom declarations in EBCMCategory/"
# declaration keyword at the start of a line, optionally after attributes and modifiers
AXIOM_RE='^[[:space:]]*(@\[[^]]*\][[:space:]]*)?((private|protected|noncomputable|unsafe|partial)[[:space:]]+)*axiom[[:space:]]+[^[:space:]]'
if grep -rnE "$AXIOM_RE" EBCMCategory EBCMCategory.lean; then
  echo "FAIL: axiom declaration(s) in the trusted library (listed above)" >&2
  status=1
else
  echo "   none"
fi

echo "== [2/3] scripts/AxiomGate.lean imports every module under EBCMCategory/"
want=$(find EBCMCategory -name '*.lean' | sed 's#\.lean$##; s#/#.#g' | LC_ALL=C sort)
have=$(grep -E '^import EBCMCategory\.' scripts/AxiomGate.lean | sed 's/^import //' | LC_ALL=C sort)
if [ "$want" != "$have" ]; then
  echo "FAIL: the import list of scripts/AxiomGate.lean differs from the modules on disk:" >&2
  diff <(echo "$want") <(echo "$have") >&2
  status=1
else
  echo "   $(echo "$want" | wc -l | tr -d ' ') modules"
fi

if [ "$BUILD" = 1 ]; then
  echo "== building the trusted library (lake build)"
  with_alarm lake build >/dev/null 2>&1 || { echo "FAIL: lake build" >&2; with_alarm lake build 2>&1 | grep -E 'error' | head -20 >&2; exit 1; }
fi

echo "== [3/3] #print axioms for every EBCMCategory declaration"
out=$(lake env perl -e 'alarm shift; exec @ARGV' "$ALARM" lean scripts/AxiomGate.lean 2>&1)
rc=$?
echo "$out" | grep -E "axiom gate|error|depends on|declared as an axiom" | sed 's/^/   /'
if [ $rc -ne 0 ] || ! echo "$out" | grep -q "axiom gate PASSED"; then
  echo "FAIL: axiom gate (exit $rc)" >&2
  status=1
fi

if [ $status -eq 0 ]; then echo "AXIOM GATE PASSED"; else echo "AXIOM GATE FAILED" >&2; fi
exit $status
