#!/usr/bin/env bash
# SA-PASS spec-to-Lean alignment audit for the trusted library EBCMCategory.
#
#   bash scripts/sa_pass.sh                 report mode: Alignment/report/sa_pass_report.{json,md}
#   bash scripts/sa_pass.sh --self-test     the audit must catch every mock; the example must pass
#   bash scripts/sa_pass.sh --strict        exit 1 if a required claim lacks SA-PASS = 1
#   bash scripts/sa_pass.sh --no-build      reuse the last build and audit JSON (re-score only)
#   bash scripts/sa_pass.sh --check-sources also verify every claim text against its cited lines
#
# Steps: merge Alignment/claims/*.yaml -> Alignment/claims.yaml + claims_blind.yaml; build
# Alignment.All and Alignment.Audit; run the Lean audit (scripts/SaPassReport.lean) which writes
# Alignment/report/sa_pass_audit.json; score it with scripts/sa_pass_score.py.
# Long commands are wrapped in `perl -e 'alarm N'` (this machine has no `timeout`), with
# N = $SA_PASS_ALARM seconds (default 1800) per step; a build killed by the alarm is resumed (lake
# keeps finished modules), and the audit's alarm is set in the lean process itself.
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2
ROOT="$(pwd)"
MODE=report
STRICT=""
BUILD=1
CHECK_SOURCES=""
for arg in "$@"; do
  case "$arg" in
    --self-test) MODE=selftest ;;
    --strict) STRICT="--strict" ;;
    --no-build) BUILD=0 ;;
    --check-sources) CHECK_SOURCES="--check-sources" ;;
    -h|--help) sed -n '2,15p' "$0"; exit 0 ;;
    *) echo "unknown option: $arg" >&2; exit 2 ;;
  esac
done

PY="$ROOT/../../.venv/bin/python"
[ -x "$PY" ] || PY="$(command -v python3)"
ALARM=${SA_PASS_ALARM:-1800}
with_alarm() { perl -e 'alarm shift; exec @ARGV' "$ALARM" "$@"; }
mkdir -p Alignment/report
LOG=Alignment/report/build.log

echo "== [1/4] merging claim fragments"
"$PY" scripts/sa_merge_claims.py $CHECK_SOURCES || { echo "claim merge failed" >&2; exit 2; }

if [ "$BUILD" = 1 ]; then
  echo "== [2/4] building Alignment.All and Alignment.Audit (log: $LOG)"
  ok=0
  for attempt in 1 2 3 4 5; do
    with_alarm lake build +Alignment.All +Alignment.Audit >"$LOG" 2>&1
    rc=$?
    if [ $rc -eq 0 ]; then ok=1; break; fi
    if [ $rc -eq 142 ]; then echo "   build attempt $attempt hit the ${ALARM}s alarm; resuming"; continue; fi
    break
  done
  if [ $ok != 1 ]; then
    echo "BUILD FAILED (exit $rc); errors:" >&2
    grep -E "^error|error:" -A6 "$LOG" | head -60 >&2
    exit 2
  fi
  grep -E "^warning: .*(sorry|sa_)" "$LOG" | sed 's/^/   /' | head -20

  echo "== [3/4] running the Lean audit"
  ok=0
  for attempt in 1 2 3; do
    # the alarm is set in the lean process itself (under `lake env`), so that it cannot outlive lake
    lake env perl -e 'alarm shift; exec @ARGV' "$ALARM" lean scripts/SaPassReport.lean \
      >Alignment/report/audit.log 2>&1
    rc=$?
    if [ $rc -eq 0 ]; then ok=1; break; fi
    if [ $rc -eq 142 ]; then echo "   audit attempt $attempt hit the ${ALARM}s alarm; retrying"; continue; fi
    break
  done
  if [ $ok != 1 ]; then
    echo "AUDIT FAILED (exit $rc):" >&2
    head -40 Alignment/report/audit.log >&2
    exit 2
  fi
  tail -1 Alignment/report/audit.log | sed 's/^/   /'
else
  echo "== [2-3/4] --no-build: reusing Alignment/report/sa_pass_audit.json"
fi

echo "== [4/4] scoring ($MODE)"
"$PY" scripts/sa_pass_score.py --mode "$MODE" $STRICT $CHECK_SOURCES
exit $?
