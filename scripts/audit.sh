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

# Resolve the roster path BEFORE we cd into demos/lean (it lives next to this script).
ROSTER="$(cd "$(dirname "$0")" && pwd)/audit-roster.txt"

cd "$(dirname "$0")/../demos/lean" || { echo "audit: cannot find demos/lean"; exit 2; }

STANDARD='propext|Classical.choice|Quot.sound'
# The named hardness-floor primitive axioms (extracted from the #[charon::opaque] primitives).
FLOOR='pqxdh\.x25519_agree|pqxdh\.mlkem_encapsulate|pqxdh\.mlkem_decapsulate|pqxdh\.hkdf_sha256_derive|pqxdh\.ec_is_canonical'
# The ONLY theorems permitted to additionally depend on the FLOOR axioms (exact names).
# The four PQXDH orchestration/correctness theorems: the two totality envelopes and the two
# key-agreement correctness headlines (which take the floor properties as hypotheses on the agreed
# legs — those hypotheses mention the opaque primitives, so the floor axioms appear transitively).
FLOOR_OK='Pqxdh\.pqxdh_initiate_total|Pqxdh\.pqxdh_accept_total|Pqxdh\.pqxdh_keys_agree_no_opk|Pqxdh\.pqxdh_keys_agree_with_opk'
EXPECTED=289  # number of 'depends on axioms' report lines expected (one per headline theorem)
# NB: this counts 'depends on axioms:' lines only. THREE registered headlines print 'does not depend
# on any axioms' (the kernel `decide` witnesses `Gf16IrreducibleMirror.noSmallFactor_POLY` and
# `HmacPrf.hmac_pads_distinct`, plus the pure structure def `HmacPrf.cascadeKeyedHash`), so they are
# registered in Audit.lean but do NOT add to this count.
# The VCVio-hybrid floor round adds the generic q-query oracle hybrid (the reusable FCF
# `OracleHybrid.v` analog), the HMAC per-hop localization, the PRF→RF reduction, and the
# Sha256Wire extracted-compression cascade/fold-identity headlines.
# The cascade-perhop round adds 12 headlines (229→241): the per-hop reduction `singleBlockRed`
# CONCRETELY BUILT and BOTH simulation-correctness pins (hreal/hideal) DISCHARGED at the
# single-block (q=1) slice, culminating in `cascadeFixedLen_prfAdvantage_le_one_smul_of_compressionPRF`
# (and its extracted-SHA-256 wiring `sha256_singleBlockCascade_..._of_compressionPRF`) — the q=1
# cascade bound carrying ONLY the compression-PRF advantage `hbound`, no simCorrect hypotheses.
# Sub-arc (a) registers 3 headlines but adds only 2 to this count (241→243): `cascadeKeyedHash`
# (the cascade as a VCVio
# `CollisionResistance.KeyedHashFamily` — a pure def, prints 'does not depend on any axioms', so it
# does NOT add to the count), `cascadeCAUAdvantage` (cAU/weak-collision-resistance
# advantage = VCVio's existing `keyedCRAdvantage` on the cascade — FCF cAU.v Adv_WCR, NO bespoke
# game), and the HONEST general-q headline `cascadeFixedLen_prfAdvantage_le_qmul_add_cAU`
# (≤ q•ε + cAU, the GNMAC_PRF.v:29 PRF-term + WCR-term shape). The floor story: general-q needs
# compression-PRF AND cascade-cAU; compression-PRF ALONE is insufficient (length-extension). The
# per-hop pins remain HYPOTHESES (not discharged for q>1) and the cAU term is the named floor.
# Sub-arc (c) adds 12 headlines (243→255): the per-hop PRF SWAP discharged at GENERAL depth `i` (the
# FCF `hF.v` G0_G1 half) UP TO an explicit, carried bad-event slack. `depthIRedHandler`/`depthIRed`
# (concrete depth-`i` reduction, the single challenge KEY plays the depth-`i` chaining value — Bellare
# Lemma 3.1 Claim 3.5), `depthIRealScheme`/`depthIIdealImpl` (the experiments it lands in),
# `depthIRed_prfRealExp`/`depthIRed_prfIdealExp` (pins hreal/hideal DISCHARGED as CLEAN equalities),
# `depthIHop_eq_prfAdvantage` (hop = compression-PRF advantage, hypothesis-free),
# `badSlack` (the EXPLICIT prefix-collision residual, a concretely-defined ℝ carried UNBOUNDED — FCF
# cAU.v:30-39 Adv_WCR), `depthIHop_le_prfAdvantage_add_badSlack` (THE (c) DELIVERABLE: per-hop pin =
# (compression-PRF call) + (carried badSlack), general depth), `badSlack_eq_zero_of_endpoints` /
# `depthIHop_le_prfAdvantage_of_endpoints` (HONEST n=1 recovery — badSlack 0 ONLY under
# endpoint-coincidence, NOT assumed 0 for n>1), `cascadeFixedLen_prfAdvantage_le_sum_upToBad`
# (telescoping headline). The bad-event BOUND is sub-arc (b); cAU→compression-PRF is (d). NEITHER done
# here — the general-q cascade is NOT closed by (c), only the per-hop swap is.

out="$(lake env lean Audit.lean 2>&1)"; rc=$?
echo "$out"

if [ "$rc" -ne 0 ]; then
  echo "VERIFY FAILED: Audit.lean did not typecheck (exit $rc)."; exit 1
fi

# ── ROBUST REPORT PARSING (prime-safe) ───────────────────────────────────────
# Lean prints `'<name>' depends on axioms: [<list>]` (the list may wrap across
# lines) or `'<name>' does not depend on any axioms`. THEOREM NAMES MAY CONTAIN
# SINGLE QUOTES (e.g. `foo'`), so an earlier `'[^']+'` segment regex SILENTLY
# DROPPED prime-named reports from the allowlist loop — a custom axiom in such a
# theorem could then evade the check entirely (gate-audit, CRITICAL). We instead
# split into one-report-per-line on the column-0 opening quote (Lean starts each
# report at column 0; wrapped continuation lines begin with whitespace), then
# strip the wrapping quotes by position — robust to any quote inside the name.
records="$(printf '%s\n' "$out" | awk '
  /^\047/ { if (rec != "") print rec; rec = $0; next }   # \047 = single quote
  { rec = rec " " $0 }
  END { if (rec != "") print rec }
')"

# ── COUNT + ROSTER INTEGRITY ─────────────────────────────────────────────────
# The authoritative roster of what SHOULD be audited is the set of `#print axioms`
# directives in Audit.lean. Cross-check (a) that every directive produced exactly
# one parsed report and vice-versa (so a dropped/garbled segment fails LOUDLY,
# closing the prime-hole symptom even if parsing ever regresses), and (b) that
# the registered set matches the committed external roster scripts/audit-roster.txt
# (so a count-neutral headline SWAP in Audit.lean is a reviewable, gated event,
# not silent — gate-audit, MEDIUM).
# Compare sorted newline-joined strings directly (no temp files / no process
# substitution — portable and sandbox-safe). `comm`-free: exact string equality
# on the sorted-unique sets, with a printed line-diff on mismatch.
# Reports come in two forms: `'name' depends on axioms: [...]` and
# `'name' does not depend on any axioms`. Match BOTH (note: "depend" without the
# trailing 's' in the axiom-free form) so the cross-check covers every directive.
reg_names="$(grep -E '^#print axioms ' Audit.lean | sed -E 's/^#print axioms +//; s/[[:space:]]+$//' | sort -u)"
rep_names="$(printf '%s\n' "$records" | grep -E "' (depends on axioms:|does not depend)" \
  | sed -E "s/^'(.*)' (depends on axioms:|does not depend).*/\1/" | sort -u)"

if [ "$reg_names" != "$rep_names" ]; then
  echo "VERIFY FAILED: the #print axioms directives in Audit.lean do not match the parsed reports."
  echo "  (a report was dropped/garbled, or a name failed to resolve)."
  echo "  Registered-but-not-reported:"; printf '%s\n' "$reg_names" | grep -vxF "$rep_names" 2>/dev/null | sed 's/^/    /'
  echo "  Reported-but-not-registered:"; printf '%s\n' "$rep_names" | grep -vxF "$reg_names" 2>/dev/null | sed 's/^/    /'
  exit 1
fi

if [ -f "$ROSTER" ]; then
  roster_names="$(sort -u "$ROSTER")"
  if [ "$roster_names" != "$reg_names" ]; then
    echo "VERIFY FAILED: Audit.lean headline roster changed vs scripts/audit-roster.txt."
    echo "  A headline was added/removed/renamed. If intended, regenerate the roster:"
    echo "    grep -E '^#print axioms ' demos/lean/Audit.lean | sed -E 's/^#print axioms +//' | sort -u > scripts/audit-roster.txt"
    echo "  Added vs roster:"; printf '%s\n' "$reg_names" | grep -vxF "$roster_names" 2>/dev/null | sed 's/^/    /'
    echo "  Removed vs roster:"; printf '%s\n' "$roster_names" | grep -vxF "$reg_names" 2>/dev/null | sed 's/^/    /'
    exit 1
  fi
else
  echo "VERIFY WARNING: scripts/audit-roster.txt missing — skipping the external-roster swap check."
fi

# Count of reports that actually depend on axioms (the EXPECTED semantic).
n="$(printf '%s\n' "$records" | grep -cF "depends on axioms:")"
if [ "$n" -ne "$EXPECTED" ]; then
  echo "VERIFY FAILED: expected $EXPECTED axiom reports, found $n (Audit.lean changed, or a #print axioms failed)."; exit 1
fi

# Global blocklist (matches regardless of line wrapping or which theorem): sorry, native_decide,
# and bv_decide's native-reflection axioms / any posited `.ax_N` axiom — NEVER allowed anywhere.
flat="$(printf '%s' "$out" | tr '\n' ' ')"
if printf '%s' "$flat" | grep -qE 'sorryAx|ofReduceBool|native_decide|_native|bv_decide\.ax|\.ax_[0-9]'; then
  echo "VERIFY FAILED: 'sorry' / native_decide / bv_decide native-reflection axiom detected."; exit 1
fi

# Per-theorem allowlist: STANDARD for every theorem; STANDARD+FLOOR only for the FLOOR_OK four.
# This both rejects unexpected axioms AND confines the floor axioms to the orchestration theorems.
# `checked` counts segments actually processed; it must equal `n` (defence-in-depth: a segment that
# fails to parse its axiom list would be skipped, so a mismatch fails the gate).
fail=0; floor_used=0; checked=0
while IFS= read -r rec; do
  case "$rec" in
    *" depends on axioms: ["*"]") ;;          # a report with an axiom list
    *) continue ;;                            # 'does not depend...' / blank / non-report line
  esac
  # Strip the wrapping quotes BY POSITION (prime-safe): name = between leading `'`
  # and the literal `' depends on axioms:`; list = between the last `[` and first `]`.
  name="${rec%%\' depends on axioms:*}"; name="${name#\'}"
  list="${rec##*\[}"; list="${list%%\]*}"
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
  checked=$((checked + 1))
done <<EOF
$records
EOF

if [ "$checked" -ne "$n" ]; then
  echo "VERIFY FAILED: parsed $checked axiom-bearing reports but counted $n (a report was dropped — possible parse hole)."; exit 1
fi
if [ "$fail" -ne 0 ]; then exit 1; fi

echo "VERIFY OK: all $n headline theorems depend only on [propext, Classical.choice, Quot.sound]"
echo "          (the $floor_used PQXDH orchestration theorem(s) additionally on the named X25519/ML-KEM/HKDF/EC hardness-floor axioms)."
