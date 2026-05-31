#!/usr/bin/env bash
# Soundness gate. Every headline theorem reported by demos/lean/Audit.lean must depend
# ONLY on the three standard Lean axioms — no `sorry` (sorryAx), no `native_decide`
# (Lean.ofReduceBool), no `bv_decide` native-reflection axioms (`*._native.bv_decide.ax_*`,
# type `verifyBVExpr cert = true` — posited, not kernel-checked), and no custom/extra axioms
# of any kind. Exits non-zero otherwise.
# NOTE: Lean pretty-prints long axiom lists across MULTIPLE lines, so we flatten the output
# to a single line before extracting axiom names (an earlier single-line `sed` silently
# missed a wrapped `_native.bv_decide.ax` name — see the libsignal-nodes-2 gap-fix review).
# SCOPE: this gate audits exactly the headline theorems listed in Audit.lean — a NEW headline
# theorem is only checked once it is registered there (and EXPECTED bumped). Keep both in sync.
set -uo pipefail

cd "$(dirname "$0")/../demos/lean" || { echo "audit: cannot find demos/lean"; exit 2; }

ALLOWED='propext|Classical.choice|Quot.sound'
EXPECTED=85  # number of 'depends on axioms' report lines expected (one per headline theorem)

out="$(lake env lean Audit.lean 2>&1)"; rc=$?
echo "$out"

if [ "$rc" -ne 0 ]; then
  echo "VERIFY FAILED: Audit.lean did not typecheck (exit $rc)."; exit 1
fi

# Flatten to a single line FIRST so multi-line-wrapped axiom lists are contiguous.
flat="$(printf '%s' "$out" | tr '\n' ' ')"

n="$(printf '%s' "$flat" | grep -oE 'depends on axioms:' | grep -c .)"
if [ "$n" -ne "$EXPECTED" ]; then
  echo "VERIFY FAILED: expected $EXPECTED axiom reports, found $n (Audit.lean changed, or a #print axioms failed)."; exit 1
fi

# Primary blocklist (matches regardless of line wrapping): sorry, native_decide, and
# bv_decide's native-reflection axioms / any posited `.ax_N` axiom.
if printf '%s' "$flat" | grep -qE 'sorryAx|ofReduceBool|native_decide|_native|bv_decide\.ax|\.ax_[0-9]'; then
  echo "VERIFY FAILED: 'sorry' / native_decide / bv_decide native-reflection axiom detected."; exit 1
fi

# Any axiom token outside the allowed set is a failure (extracted from the flattened lists).
bad="$(printf '%s' "$flat" \
  | grep -oE 'depends on axioms: \[[^]]*\]' \
  | sed -E 's/.*\[(.*)\]/\1/' \
  | tr ',' '\n' | sed 's/^[[:space:]]*//; s/[[:space:]]*$//' \
  | grep -vE '^$' | grep -vxE "$ALLOWED" || true)"
if [ -n "$bad" ]; then
  echo "VERIFY FAILED: disallowed axiom(s):"; printf '  %s\n' $bad; exit 1
fi

echo "VERIFY OK: all $n headline theorems depend only on [propext, Classical.choice, Quot.sound]."
