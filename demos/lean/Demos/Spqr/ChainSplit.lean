/-
  SPQR symmetric-ratchet step — structural / value adequacy of the output split.

  The SPQR analog of Demo 3's per-step plumbing. The extracted `spqr_chain_next`
  (Crypto/Sha256.lean `spqr_chain_next_total` is the value-adequacy hook) computes

      genr8r = HKDF-Expand(prk, info=(ctr+1)_be ‖ label, 64)   -- a 64-byte block
      (new_next, out_key) = (genr8r[0..32], genr8r[32..64])    -- the output split

  and returns `(ctr+1, new_next, out_key)`. The cryptographic core is the 64-byte
  HKDF-Expand `genr8r`; the **output split** of that 64-byte block into the next
  chain key `new_next` and the emitted output key `out_key` is the deterministic
  per-step plumbing — exactly the length-doubling split `Blk64 ≃ Key × Key` that the
  width-generic ratchet hybrid (`Demos/Ratchet/Generic.lean`) is proven over, and the
  *same* byte-split that Demo 3's extracted `ratchet.ratchet_split` computes.

  This file BANKS that structural adequacy:

  * `spqr_chain_next_loop2_split_spec` — a *value* spec (not just totality) for the
    extracted output-split loop `spqr_chain_next_loop2`: it writes `new_next[i]=genr8r[i]`
    and `out_key[i]=genr8r[32+i]` for all `i < 32`. (The audited `spqr_chain_next_loop2_total`
    only certifies the loop does not fail; this pins *what it computes*.)

  * `spqrSplit` — the pure split function driven by that extracted loop, and
    `spqrSplit_eq_splitPure` — it is *definitionally the same byte-split* as Demo 3's
    `RatchetSecurity.splitPure`. Hence `spqrSplit_bijective` reuses Demo 3's
    `splitPure_bijective` verbatim: the SPQR output split is the length-doubling
    bijection the hybrid consumes.

  SCOPE (honest boundary). This is value/structural adequacy over the extracted
  function — NO security game is defined or discharged here. The full SCKA-style
  pseudorandomness *advantage bound* is NOT reached, because the SPQR chain's per-step
  generator is step-indexed: the running counter `ctr` feeds the HKDF `info`, so the
  effective block generator `G_ctr : Key → Blk64` differs at each hop. The
  `RatchetGeneric` hybrid is stated over a *single, step-invariant* `G`, so SPQR does
  not literally instantiate it without an extra modeling assumption that treats each
  counter-indexed `G_ctr` as one PRG — a security-modeling choice we deliberately do
  not make here. What is unconditionally banked is that the *split half* of the SPQR
  step is precisely the trusted length-doubling bijection. (See TRUST.md, libsignal/SPQR
  node section: these are totality / functional-correctness results, no security.)
-/
import Demos.Crypto.Sha256
import Demos.Ratchet.Chain

open Aeneas Std Result
open List (Vector)

namespace Spqr.ChainSplit

/-! ## Value spec for the extracted output-split loop. -/

/-- The output-split loop computes the byte split on the indices already processed:
`new_next` accumulates `genr8r[0..i]` and `out_key` accumulates `genr8r[32..32+i]`.
This is the value-adequacy invariant (the audited `spqr_chain_next_loop2_total` proves
only non-failure; this proves *what* it computes). -/
theorem spqr_chain_next_loop2_split_loop (genr8r : Array Std.U8 64#usize) :
    ∀ (new_next out_key : Array Std.U8 32#usize) (i : Std.Usize),
      i.val ≤ 32 →
      (∀ j, j < i.val → new_next.val[j]! = genr8r.val[j]!) →
      (∀ j, j < i.val → out_key.val[j]! = genr8r.val[32 + j]!) →
      sha256.spqr_chain_next_loop2 genr8r new_next out_key i
        ⦃ r => (∀ j, j < 32 → r.1.val[j]! = genr8r.val[j]!) ∧
               (∀ j, j < 32 → r.2.val[j]! = genr8r.val[32 + j]!) ⦄ := by
  intro new_next out_key i hi hnn hok
  unfold sha256.spqr_chain_next_loop2
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 32#usize) × (Array Std.U8 32#usize) × Std.Usize =>
      32 - s.2.2.val)
    (inv := fun s : (Array Std.U8 32#usize) × (Array Std.U8 32#usize) × Std.Usize =>
      s.2.2.val ≤ 32 ∧
      (∀ j, j < s.2.2.val → s.1.val[j]! = genr8r.val[j]!) ∧
      (∀ j, j < s.2.2.val → s.2.1.val[j]! = genr8r.val[32 + j]!))
    (post := fun r : (Array Std.U8 32#usize) × (Array Std.U8 32#usize) =>
      (∀ j, j < 32 → r.1.val[j]! = genr8r.val[j]!) ∧
      (∀ j, j < 32 → r.2.val[j]! = genr8r.val[32 + j]!))
  · rintro ⟨nn1, ok1, i1⟩ ⟨hi1, hnn1, hok1⟩
    simp only [sha256.spqr_chain_next_loop2.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨a, ha⟩
      step as ⟨off, hoff⟩
      step as ⟨v3, hv3⟩
      step as ⟨a1, ha1⟩
      step as ⟨i4, hi4⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · scalar_tac
      · intro j hj
        subst ha
        by_cases hje : j = i1.val
        · subst hje; simp_lists [hv1]
        · have hlt2 : j < i1.val := by scalar_tac
          simp_lists; exact hnn1 j hlt2
      · intro j hj
        subst ha1
        by_cases hje : j = i1.val
        · subst hje
          simp_lists [hv3]
          scalar_tac
        · have hlt2 : j < i1.val := by scalar_tac
          simp_lists; exact hok1 j hlt2
      · scalar_tac
    · rename_i hge
      refine ⟨?_, ?_⟩
      · intro j hj; apply hnn1; scalar_tac
      · intro j hj; apply hok1; scalar_tac
  · exact ⟨hi, hnn, hok⟩

/-- **Value adequacy of the output split.** The extracted `spqr_chain_next_loop2`, started
from zeroed accumulators at index 0, splits the 64-byte block: the first 32 bytes are the
new chain key, the next 32 are the emitted output key. -/
theorem spqr_chain_next_loop2_split_spec (genr8r : Array Std.U8 64#usize) :
    sha256.spqr_chain_next_loop2 genr8r
        (Array.repeat 32#usize 0#u8) (Array.repeat 32#usize 0#u8) 0#usize
      ⦃ r => (∀ j, j < 32 → r.1.val[j]! = genr8r.val[j]!) ∧
             (∀ j, j < 32 → r.2.val[j]! = genr8r.val[32 + j]!) ⦄ := by
  apply spqr_chain_next_loop2_split_loop
  · scalar_tac
  · intro j hj; scalar_tac
  · intro j hj; scalar_tac

/-! ## Value specs for the two input loops (pinning the HKDF inputs).

These pin *what* the counter-info loop (`loop0`) and the chain-key copy loop (`loop1`) write,
so that the HKDF inputs `info4`/`ikm1` the chain step feeds into `hkdf_extract`/`hkdf_expand_64`
are tied to the actual `(next, ctr)`, not arbitrary arrays. (The audited
`spqr_chain_next_loop0_total`/`spqr_chain_next_loop1_total` certify only non-failure.) -/

/-- The counter-info loop writes `CHAIN_NEXT_LABEL` into `info[4 .. 4+31)`, leaving every other
index untouched: `info4[4+k] = CHAIN_NEXT_LABEL[k]` for `k < 31`. (The first four bytes — the
big-endian counter — are written before the loop and are not disturbed by it.) -/
theorem spqr_chain_next_loop0_label_loop (lbl : Array Std.U8 31#usize) :
    ∀ (info : Array Std.U8 256#usize) (i : Std.Usize),
      i.val ≤ 31 →
      (∀ k, k < i.val → info.val[4 + k]! = lbl.val[k]!) →
      lbl = sha256.CHAIN_NEXT_LABEL →
      sha256.spqr_chain_next_loop0 info i
        ⦃ r => ∀ k, k < 31 → r.val[4 + k]! = lbl.val[k]! ⦄ := by
  intro info i hi hpre hlbl
  unfold sha256.spqr_chain_next_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 256#usize) × Std.Usize => 31 - s.2.val)
    (inv := fun s : (Array Std.U8 256#usize) × Std.Usize =>
      s.2.val ≤ 31 ∧ (∀ k, k < s.2.val → s.1.val[4 + k]! = lbl.val[k]!))
    (post := fun r : Array Std.U8 256#usize => ∀ k, k < 31 → r.val[4 + k]! = lbl.val[k]!)
  · rintro ⟨o1, i1⟩ ⟨hi1, hpre1⟩
    simp only [sha256.spqr_chain_next_loop0.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨off, hoff⟩
      step as ⟨a, ha⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_⟩
      · scalar_tac
      · intro k hk
        subst ha
        have hoffv : off.val = 4 + i1.val := hoff
        by_cases hke : k = i1.val
        · subst hke
          simp_lists [hoffv, hv1]
          subst hlbl
          rfl
        · have hlt2 : k < i1.val := by scalar_tac
          simp_lists [hoffv]
          exact hpre1 k hlt2
      · scalar_tac
    · rename_i hge
      intro k hk; apply hpre1; scalar_tac
  · exact ⟨hi, hpre⟩

/-- The counter-info loop, run from index 0 over the pre-loop array `info` (whose `[4..35)`
region is still zero), produces `info4` with `info4[4+k] = CHAIN_NEXT_LABEL[k]` for `k < 31`. -/
theorem spqr_chain_next_loop0_label_spec (info : Array Std.U8 256#usize) :
    sha256.spqr_chain_next_loop0 info 0#usize
      ⦃ r => ∀ k, k < 31 → r.val[4 + k]! = sha256.CHAIN_NEXT_LABEL.val[k]! ⦄ := by
  apply spqr_chain_next_loop0_label_loop
  · scalar_tac
  · intro k hk; scalar_tac
  · rfl

/-- The chain-key copy loop writes `next` into `ikm[0 .. 32)`: `ikm1[j] = next[j]` for `j < 32`.
This pins that the HKDF-Extract `ikm` (input keying material) begins with the actual chain key
`next`, so `prk = HKDF-Extract(0³², next ‖ 0…)` is the extract of *this* chain key. -/
theorem spqr_chain_next_loop1_copy_loop (next : Array Std.U8 32#usize) :
    ∀ (ikm : Array Std.U8 1536#usize) (i : Std.Usize),
      i.val ≤ 32 →
      (∀ j, j < i.val → ikm.val[j]! = next.val[j]!) →
      sha256.spqr_chain_next_loop1 next ikm i
        ⦃ r => ∀ j, j < 32 → r.val[j]! = next.val[j]! ⦄ := by
  intro ikm i hi hpre
  unfold sha256.spqr_chain_next_loop1
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 1536#usize) × Std.Usize => 32 - s.2.val)
    (inv := fun s : (Array Std.U8 1536#usize) × Std.Usize =>
      s.2.val ≤ 32 ∧ (∀ j, j < s.2.val → s.1.val[j]! = next.val[j]!))
    (post := fun r : Array Std.U8 1536#usize => ∀ j, j < 32 → r.val[j]! = next.val[j]!)
  · rintro ⟨o1, i1⟩ ⟨hi1, hpre1⟩
    simp only [sha256.spqr_chain_next_loop1.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨a, ha⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_⟩
      · scalar_tac
      · intro j hj
        subst ha
        by_cases hje : j = i1.val
        · subst hje; simp_lists [hv1]
        · have hlt2 : j < i1.val := by scalar_tac
          simp_lists; exact hpre1 j hlt2
      · scalar_tac
    · rename_i hge
      intro j hj; apply hpre1; scalar_tac
  · exact ⟨hi, hpre⟩

/-- The chain-key copy loop run from index 0 over zeroed `ikm` produces `ikm1` with
`ikm1[j] = next[j]` for `j < 32`. -/
theorem spqr_chain_next_loop1_copy_spec (next : Array Std.U8 32#usize)
    (ikm : Array Std.U8 1536#usize) :
    sha256.spqr_chain_next_loop1 next ikm 0#usize
      ⦃ r => ∀ j, j < 32 → r.val[j]! = next.val[j]! ⦄ := by
  apply spqr_chain_next_loop1_copy_loop
  · scalar_tac
  · intro j hj; scalar_tac

/-! ## The SPQR output split as a pure bijection, matching Demo 3's `splitPure`. -/

open RatchetSecurity (Key Blk64 splitPure splitPure_bijective)

/-- The SPQR output split as a pure total function, driven by the extracted loop. The
non-`ok` branch is provably unreachable (the loop is total); a distinguished value lets
totality close it. -/
def spqrSplit (b : Blk64) : Key × Key :=
  match sha256.spqr_chain_next_loop2 b (Array.repeat 32#usize 0#u8) (Array.repeat 32#usize 0#u8) 0#usize with
  | .ok p => p
  | _ => (Array.repeat 32#usize 0#u8, Array.repeat 32#usize 0#u8)

/-- First component (new chain key) = the low 32 bytes of the block. -/
theorem spqrSplit_fst (b : Blk64) (j : ℕ) (hj : j < 32) :
    (spqrSplit b).1.val[j]! = b.val[j]! := by
  obtain ⟨p, hp, h1, _⟩ := WP.spec_imp_exists (spqr_chain_next_loop2_split_spec b)
  simp only [spqrSplit, hp]; exact h1 j hj

/-- Second component (output key) = the high 32 bytes of the block. -/
theorem spqrSplit_snd (b : Blk64) (j : ℕ) (hj : j < 32) :
    (spqrSplit b).2.val[j]! = b.val[32 + j]! := by
  obtain ⟨p, hp, _, h2⟩ := WP.spec_imp_exists (spqr_chain_next_loop2_split_spec b)
  simp only [spqrSplit, hp]; exact h2 j hj

/-- **Structural adequacy: the SPQR output split is the SAME byte-split as Demo 3's
`splitPure`.** Both carve a 64-byte block into its low/high 32-byte halves; proved by
extensional equality of the two halves byte-by-byte. -/
theorem spqrSplit_eq_splitPure : spqrSplit = splitPure := by
  funext b
  apply Prod.ext
  · apply Subtype.ext; apply List.ext_getElem!
    · simp only [Array.length_eq]
    · intro j
      by_cases hj : j < 32
      · rw [spqrSplit_fst b j hj, RatchetSecurity.splitPure_fst b j hj]
      · rw [getElem!_neg, getElem!_neg] <;> (simp only [Array.length_eq]; scalar_tac)
  · apply Subtype.ext; apply List.ext_getElem!
    · simp only [Array.length_eq]
    · intro j
      by_cases hj : j < 32
      · rw [spqrSplit_snd b j hj, RatchetSecurity.splitPure_snd b j hj]
      · rw [getElem!_neg, getElem!_neg] <;> (simp only [Array.length_eq]; scalar_tac)

/-- **The SPQR output split is the length-doubling bijection** `Blk64 ≃ Key × Key` that the
width-generic ratchet hybrid (`RatchetGeneric`) consumes — reusing Demo 3's
`splitPure_bijective` verbatim (no new proof). Splitting a *uniform* 64-byte HKDF block thus
yields an *independent uniform* `(new chain key, output key)` pair: the structural fact a
SCKA-style pseudorandomness argument over this step would rest on. -/
theorem spqrSplit_bijective : Function.Bijective spqrSplit := by
  rw [spqrSplit_eq_splitPure]; exact splitPure_bijective

/-! ## The chain-step split formula on the whole `spqr_chain_next`. -/

/-- **The SPQR chain-step split formula** (functional correctness, no security).
`spqr_chain_next next ctr` advances the counter to `ctr + 1` and emits a `(new_next, out_key)`
pair that is exactly the split of the 64-byte HKDF-Expand block `genr8r`: the new chain key is
its **first** 32 bytes (`new_next[j] = genr8r[j]`) and the emitted output key is its **second**
32 bytes (`out_key[j] = genr8r[32 + j]`). This pins `chain.rs`'s `next_key_internal` output
layout — the counter advance and the `genr8r[0..32] | genr8r[32..64]` split the SCKA `output_key`
production rests on.

The 64-byte block `genr8r` is **not** an arbitrary witness: the statement pins the very `prk`/`info4`
the function computes. Concretely it exhibits the actual `info4`/`ikm1`/`prk` together with the
*sub-step equations* that determine them from `(next, ctr)`:

* `info4` is the result of the extracted counter-info loop `spqr_chain_next_loop0` (so it is the
  function's actual info array), and its label region is pinned byte-for-byte —
  `info4[4+k] = CHAIN_NEXT_LABEL[k]` for `k < 31` (the counter-`be`-prefixed `"Signal PQ Ratchet
  V1 Chain Next"` info string);
* `ikm1` is the result of the extracted chain-key copy loop `spqr_chain_next_loop1`, with its keying
  material pinned to the chain key — `ikm1[j] = next[j]` for `j < 32`;
* `prk = hkdf_extract 0³² ikm1 32` is *literally* the HKDF salt-extract of that `ikm1`; and
* `genr8r = hkdf_expand_64 prk info4 35`.

So `genr8r` is the HKDF-Expand of the PRK extracted from the *actual* chain key `next` under the
*actual* counter-derived info string — the opaque-but-total cryptographic core — and the split below
is the split of that block, not of an unrelated concatenation. -/
theorem spqr_chain_next_split_spec (next : Array Std.U8 32#usize) (ctr : Std.U32)
    (hctr : ctr.val < Std.U32.max) :
    sha256.spqr_chain_next next ctr
      ⦃ r => r.1.val = ctr.val + 1 ∧
             ∃ (info4 : Array Std.U8 256#usize) (ikm1 : Array Std.U8 1536#usize)
               (prk : Array Std.U8 32#usize) (genr8r : Array Std.U8 64#usize),
               -- `info4` is the function's actual counter-info array, with the label pinned:
               (∀ k, k < 31 → info4.val[4 + k]! = sha256.CHAIN_NEXT_LABEL.val[k]!) ∧
               -- `ikm1` is the function's actual keying material, pinned to the chain key `next`:
               (∀ j, j < 32 → ikm1.val[j]! = next.val[j]!) ∧
               -- `prk` is the salt-extract of *that* `ikm1`; `genr8r` the HKDF-Expand of `prk`/`info4`:
               sha256.hkdf_extract (Array.repeat 32#usize 0#u8) ikm1 32#usize = ok prk ∧
               sha256.hkdf_expand_64 prk info4 35#usize = ok genr8r ∧
               (∀ j, j < 32 → r.2.1.val[j]! = genr8r.val[j]!) ∧
               (∀ j, j < 32 → r.2.2.val[j]! = genr8r.val[32 + j]!) ⦄ := by
  unfold sha256.spqr_chain_next
  step as ⟨ctr1, hctr1⟩
  step as ⟨ctrb, _⟩
  step as ⟨i, _⟩
  step as ⟨info1, _⟩
  step as ⟨i1, _⟩
  step as ⟨info2, _⟩
  step as ⟨i2, _⟩
  step as ⟨info3, _⟩
  step as ⟨i3, _⟩
  step as ⟨a, _⟩
  -- Bind the counter-info loop with its *value* spec, capturing the label layout of `info4`.
  apply Aeneas.Std.WP.spec_bind (spqr_chain_next_loop0_label_spec a)
  intro info4 hinfo4
  -- Bind the chain-key copy loop with its *value* spec, capturing the `ikm1 = next` layout.
  apply Aeneas.Std.WP.spec_bind (spqr_chain_next_loop1_copy_spec next (Array.repeat 1536#usize 0#u8))
  intro ikm1 hikm1
  -- Bind the HKDF-Extract of `ikm1`, capturing its defining equation: `prk` is the salt-extract of
  -- the keying material we just pinned to the chain key.
  obtain ⟨prk, hprkeq, -⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Sha256.hkdf_extract_total (Array.repeat 32#usize 0#u8) ikm1 32#usize (by scalar_tac))
  rw [hprkeq]; simp only [bind_tc_ok]
  -- Bind the HKDF-Expand of `prk`/`info4`, capturing its defining equation: the block we split is
  -- the actual HKDF-Expand output, not an arbitrary array.
  obtain ⟨genr8r, hgenr8r, -⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Sha256.hkdf_expand_64_total prk info4 35#usize (by scalar_tac))
  rw [hgenr8r]; simp only [bind_tc_ok]
  -- the output split loop carves the 64-byte block `genr8r` into the two halves.
  apply Aeneas.Std.WP.spec_bind (spqr_chain_next_loop2_split_spec genr8r)
  rintro ⟨nn, ok⟩ ⟨h1, h2⟩
  simp only at h1 h2
  exact ⟨by scalar_tac, info4, ikm1, prk, genr8r, hinfo4, hikm1, hprkeq, hgenr8r, h1, h2⟩

end Spqr.ChainSplit
