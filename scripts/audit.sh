#!/usr/bin/env bash
# Soundness gate. Every headline theorem reported by demos/lean/Audit.lean must depend
# ONLY on the three standard Lean axioms — no `sorry` (sorryAx), no `native_decide`
# (Lean.ofReduceBool), and no custom/extra axioms of any kind. Exits non-zero otherwise.
set -uo pipefail

cd "$(dirname "$0")/../demos/lean" || { echo "audit: cannot find demos/lean"; exit 2; }

ALLOWED='propext|Classical.choice|Quot.sound'
EXPECTED=6   # number of `#print axioms` declarations in Audit.lean

out="$(lake env lean Audit.lean 2>&1)"; rc=$?
echo "$out"

if [ "$rc" -ne 0 ]; then
  echo "VERIFY FAILED: Audit.lean did not typecheck (exit $rc)."; exit 1
fi

n="$(printf '%s\n' "$out" | grep -c 'depends on axioms')"
if [ "$n" -ne "$EXPECTED" ]; then
  echo "VERIFY FAILED: expected $EXPECTED axiom reports, found $n (Audit.lean changed, or a #print axioms failed)."; exit 1
fi

if printf '%s\n' "$out" | grep -qE 'sorryAx|ofReduceBool'; then
  echo "VERIFY FAILED: 'sorry' (sorryAx) or native_decide (Lean.ofReduceBool) detected."; exit 1
fi

# Any axiom token outside the allowed set is a failure.
bad="$(printf '%s\n' "$out" \
  | sed -n 's/.*depends on axioms: \[\(.*\)\]/\1/p' \
  | tr ',' '\n' | sed 's/^[[:space:]]*//; s/[[:space:]]*$//' \
  | grep -vxE "$ALLOWED" || true)"
if [ -n "$bad" ]; then
  echo "VERIFY FAILED: disallowed axiom(s):"; printf '  %s\n' $bad; exit 1
fi

echo "VERIFY OK: all $n headline theorems depend only on [propext, Classical.choice, Quot.sound]."
