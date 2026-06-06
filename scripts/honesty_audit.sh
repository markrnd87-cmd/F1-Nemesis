#!/usr/bin/env bash
# Mechanized-honesty gate (P4) for the F1-square genuine-proof layer.
#
# The honesty layer is a VERIFIER, not a prohibition (program stance): it does not forbid
# proving anything, it forbids fooling ourselves. This script enforces that the proof layer is
# axiom-clean — no `sorry`, no `native_decide`, no stray `axiom` — via `#print axioms`, which is
# authoritative (textual greps would false-positive on the docstrings that *discuss* sorry).
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== F1 honesty audit =="

# 1. The library must build.
lake build

# 2. Axiom audit over every proof-layer theorem.
out="$(lake env lean scripts/audit_axioms.lean)"
echo "$out"

# 3. No forbidden axioms: sorryAx (sorry), Lean.ofReduceBool (native_decide), trustCompiler.
if echo "$out" | grep -qE 'sorryAx|ofReduceBool|trustCompiler'; then
  echo "FAIL: the proof layer depends on a forbidden axiom (sorry / native_decide)." >&2
  exit 1
fi

# 4. Every theorem that uses axioms must use only the standard trio
#    {propext, Classical.choice, Quot.sound}. Any other named axiom fails.
if echo "$out" | grep -E 'depends on axioms' \
   | grep -vqE '\[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]'; then
  echo "FAIL: a theorem depends on an axiom outside {propext, Classical.choice, Quot.sound}." >&2
  echo "$out" | grep -E 'depends on axioms' \
    | grep -vE '\[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]' >&2
  exit 1
fi

echo "PASS: the proof layer is axiom-clean (no sorry, no native_decide, no stray axioms)."
