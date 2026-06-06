#!/usr/bin/env bash
# Soundness gate. Every headline theorem reported by demos/lean/Audit.lean must depend ONLY on
# the three standard Lean axioms [propext, Classical.choice, Quot.sound] — no `sorry` (sorryAx),
# no `native_decide` (Lean.ofReduceBool), no `bv_decide` native-reflection axioms
# (`*._native.bv_decide.ax_*`, type `verifyBVExpr cert = true` — posited, not kernel-checked),
# and no custom/extra axioms of any kind. Exits non-zero otherwise.
#
# ONE DOCUMENTED EXCEPTION (the cryptographic hardness floor): the PQXDH key-agreement
# orchestration/correctness theorems (`Pqxdh.pqxdh_initiate_total` / `Pqxdh.pqxdh_accept_total` and
# the two correctness headlines `Pqxdh.pqxdh_keys_agree_no_opk` / `Pqxdh.pqxdh_keys_agree_with_opk`)
# extract / reason over the real call sites of the opaque primitives X25519 / ML-KEM / HKDF /
# EC-canonicity, which Aeneas emits as named Lean `axiom`s. Those — and ONLY those five named
# primitive axioms, and ONLY in those four theorems — are additionally permitted. The check below
# ENFORCES that confinement: if any of the five floor axioms appears in any OTHER headline theorem,
# the gate fails. So the strong "only the 3 standard axioms" guarantee still holds for all the other
# theorems, and the floor axioms are exactly the assumed hardness primitives, surfaced explicitly.
#
# NOTE: Lean pretty-prints long axiom lists across MULTIPLE lines, so we flatten the output to a
# single line before extracting axiom names (an earlier single-line `sed` silently missed a
# wrapped `_native.bv_decide.ax` name — see the libsignal-nodes-2 gap-fix review).
# SCOPE: this gate audits exactly the headline theorems listed in Audit.lean — a NEW headline
# theorem is only checked once it is registered there (and EXPECTED bumped). Keep both in sync.
set -uo pipefail

cd "$(dirname "$0")/../demos/lean" || { echo "audit: cannot find demos/lean"; exit 2; }

STANDARD='propext|Classical.choice|Quot.sound'
# The named hardness-floor primitive axioms (extracted from the #[charon::opaque] primitives).
FLOOR='pqxdh\.x25519_agree|pqxdh\.mlkem_encapsulate|pqxdh\.mlkem_decapsulate|pqxdh\.hkdf_sha256_derive|pqxdh\.ec_is_canonical'
# The ONLY theorems permitted to additionally depend on the FLOOR axioms (exact names).
# The four PQXDH orchestration/correctness theorems: the two totality envelopes and the two
# key-agreement correctness headlines (which take the floor properties as hypotheses on the agreed
# legs — those hypotheses mention the opaque primitives, so the floor axioms appear transitively).
FLOOR_OK='Pqxdh\.pqxdh_initiate_total|Pqxdh\.pqxdh_accept_total|Pqxdh\.pqxdh_keys_agree_no_opk|Pqxdh\.pqxdh_keys_agree_with_opk'
EXPECTED=241  # number of 'depends on axioms' report lines expected (one per headline theorem)
# NB: this counts 'depends on axioms:' lines only. TWO registered headlines print 'does not depend on
# any axioms' (the kernel `decide` witnesses `Gf16IrreducibleMirror.noSmallFactor_POLY` and
# `HmacPrf.hmac_pads_distinct`), so they are registered in Audit.lean but do NOT add to this count.
# The VCVio-hybrid floor round adds the generic q-query oracle hybrid (the reusable FCF
# `OracleHybrid.v` analog), the HMAC per-hop localization, the PRF→RF reduction, and the
# Sha256Wire extracted-compression cascade/fold-identity headlines.
# The cascade-perhop round adds 12 headlines (229→241): the per-hop reduction `singleBlockRed`
# CONCRETELY BUILT and BOTH simulation-correctness pins (hreal/hideal) DISCHARGED at the
# single-block (q=1) slice, culminating in `cascadeFixedLen_prfAdvantage_le_one_smul_of_compressionPRF`
# (and its extracted-SHA-256 wiring `sha256_singleBlockCascade_..._of_compressionPRF`) — the q=1
# cascade bound carrying ONLY the compression-PRF advantage `hbound`, no simCorrect hypotheses.

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

# Global blocklist (matches regardless of line wrapping or which theorem): sorry, native_decide,
# and bv_decide's native-reflection axioms / any posited `.ax_N` axiom — NEVER allowed anywhere.
if printf '%s' "$flat" | grep -qE 'sorryAx|ofReduceBool|native_decide|_native|bv_decide\.ax|\.ax_[0-9]'; then
  echo "VERIFY FAILED: 'sorry' / native_decide / bv_decide native-reflection axiom detected."; exit 1
fi

# Per-theorem allowlist: STANDARD for every theorem; STANDARD+FLOOR only for the FLOOR_OK two.
# This both rejects unexpected axioms AND confines the floor axioms to the orchestration theorems.
fail=0; floor_used=0
while IFS= read -r seg; do
  [ -z "$seg" ] && continue
  name="$(printf '%s' "$seg" | sed -E "s/^'([^']+)'.*/\1/")"
  list="$(printf '%s' "$seg" | sed -E 's/.*\[(.*)\]/\1/')"
  if printf '%s' "$name" | grep -qxE "$FLOOR_OK"; then
    allow="$STANDARD|$FLOOR"
  else
    allow="$STANDARD"
  fi
  bad="$(printf '%s' "$list" | tr ',' '\n' | sed 's/^[[:space:]]*//; s/[[:space:]]*$//' \
    | grep -vE '^$' | grep -vxE "$allow" || true)"
  if [ -n "$bad" ]; then
    echo "VERIFY FAILED: theorem '$name' depends on disallowed axiom(s):"; printf '  %s\n' $bad; fail=1
  fi
  if printf '%s' "$list" | grep -qE "$FLOOR"; then floor_used=$((floor_used + 1)); fi
done < <(printf '%s' "$flat" | grep -oE "'[^']+' depends on axioms: \[[^]]*\]")

if [ "$fail" -ne 0 ]; then exit 1; fi

echo "VERIFY OK: all $n headline theorems depend only on [propext, Classical.choice, Quot.sound]"
echo "          (the $floor_used PQXDH orchestration theorem(s) additionally on the named X25519/ML-KEM/HKDF/EC hardness-floor axioms)."
