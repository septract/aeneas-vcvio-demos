/-
  SPQR symmetric ratchet keystream — pseudorandomness via the STEP-INDEXED hybrid.

  SPQR's symmetric ratchet step `spqr_chain_next next ctr` computes a 64-byte block

      genr8r = HKDF-Expand(HKDF-Extract(0³², next), info = (ctr+1)_be ‖ CHAIN_NEXT_LABEL, 64)

  and splits it `(new_next, out_key) = (genr8r[0..32], genr8r[32..64])`, returning
  `(ctr+1, new_next, out_key)`. The effective block generator is therefore **counter-indexed**:
  the running counter feeds the HKDF `info`, so `G_ctr : Key → Blk64` differs at every hop. The
  single, step-invariant generic hybrid in `Generic.lean` does not literally cover this; the
  step-indexed family hybrid in `GenericIndexed.lean` (`RatchetGenericIndexed`) does.

  This file instantiates that step-indexed hybrid for SPQR:

  * `spqrGen ctr0 : ℕ → Key → Blk64` — the counter-indexed block generator. Hop `i` evaluates
    SPQR's chain core at counter offset `ctr0 + i`, producing the 64-byte HKDF-Expand block
    `genr8r` from chain key `ck`. It is defined PURELY by matching `.ok` of the actual extracted
    pipeline (`spqr_chain_next_loop0`/`loop1`/`hkdf_extract`/`hkdf_expand_64`), totality
    discharging the non-`ok` branch — exactly as `Spqr.ChainSplit.spqrSplit` is driven by the
    extracted `spqr_chain_next_loop2`. So `spqrGen` is the genuine SPQR block, grounded in the
    extracted Aeneas functions, not an abstract placeholder.

  * The output split reuses `Spqr.ChainSplit.spqrSplit` / `spqrSplit_bijective` VERBATIM — already
    banked as Demo 3's length-doubling bijection `Blk64 ≃ Key × Key`.

  * Instantiating `RatchetGenericIndexed.gen_advantage_le_sum` / `gen_secure_asymptotic_idx` at
    `split := spqrSplit`, `hsplit := spqrSplit_bijective`, `G := spqrGen ctr0`, base `t := 0`
    yields the SPQR keystream's `Σε` advantage bound and its asymptotic pseudorandomness.

  HARDNESS ASSUMPTION (a hypothesis, NEVER an axiom, NO new game). "Each counter-indexed block
  generator `G_i = genBlockPRGI (spqrGen ctr0) i` is a secure PRG" is carried as the explicit
  premise `hbound` — a bound on VCVio's existing `PRGScheme.prgAdvantage` of the per-hop reduction,
  structurally identical to how `RatchetSecurity.ratchet_secure_asymptotic` carries its per-step
  block-PRG bound. `genBlockPRGI G i = { gen := G i }` is just VCVio's existing `PRGScheme`; no new
  security definition is introduced. `prgRealExp` / `prgIdealExp` / `negligible` are reused verbatim.

  SCOPE (honest boundary, inherited from `Chain.lean`). The hybrid treats the hop-`i` seed (chain
  key) as uniform, whereas the real chain key is HKDF-EXTRACTED from the previous block. The
  single-`G` `Chain.lean` development has the EXACT same gap — step-indexing inherits it, it does
  not introduce a new one. Reducing the Extract step itself (PRK pseudorandomness) is out of scope.
-/
import Demos.Spqr.ChainSplit
import Demos.Ratchet.GenericIndexed

open Aeneas Std OracleComp ENNReal PRGScheme
open List (Vector)

namespace Spqr.RatchetPrg

open RatchetSecurity (Key Blk64)
open Spqr.ChainSplit (spqrSplit spqrSplit_bijective)
open RatchetGenericIndexed
  (genStepI genKeystreamI genRatchetPRGI genBlockPRGI genReductionI
   gen_advantage_le_sum gen_secure_asymptotic_idx)

/-! ## The counter-indexed SPQR block generator.

`spqr_chain_next next ctr` builds, in order:
* `info4 = spqr_chain_next_loop0 (counter-prefixed array) 0`  — the HKDF info string;
* `ikm1  = spqr_chain_next_loop1 next (zeroed) 0`             — the keying material `= next`;
* `prk   = hkdf_extract 0³² ikm1 32`;
* `genr8r = hkdf_expand_64 prk info4 35`                       — the 64-byte block.

`spqrBlock next ctr` reproduces that pipeline up to `genr8r`, matching `.ok` at each step;
the non-`ok` branches are unreachable (every sub-step is total) and a distinguished value lets
totality close them. This is the SAME discipline `spqrSplit` uses for `spqr_chain_next_loop2`. -/
def spqrBlock (next : Key) (ctr : Std.U32) : Blk64 :=
  match sha256.spqr_chain_next next ctr with
  | .ok r =>
      -- the genuine block is `concat new_next out_key`; recover it from the returned split halves
      -- via the inverse of the split (`spqrSplit (concat a b) = (a, b)`). Since `spqr_chain_next`
      -- sets `(new_next, out_key) = spqrSplit genr8r`, `concat new_next out_key = genr8r`.
      RatchetSecurity.concat r.2.1 r.2.2
  | _ => Array.repeat 64#usize 0#u8

/-- Total, wrapping `ℕ → U32` (the SPQR counter is a `u32`; `core::num::U32::to_be_bytes` truncates
mod `2³²`, so a wrapping map is the faithful index). `U32` is `⟨bv : BitVec 32⟩`; `BitVec.ofNat`
is total and reduces mod `2³²`. -/
def u32OfNat (n : ℕ) : Std.U32 := ⟨BitVec.ofNat _ n⟩

/-- **The counter-indexed SPQR block generator.** Hop `i` (relative to base counter `ctr0`)
evaluates SPQR's chain core at counter `ctr0 + i`, producing the 64-byte HKDF-Expand block from
chain key `ck`. This is the genuine SPQR block (driven by the extracted `spqr_chain_next`), now a
*family* indexed by the hop, because the counter feeds the HKDF `info`. -/
def spqrGen (ctr0 : ℕ) : ℕ → Key → Blk64 :=
  fun i ck => spqrBlock ck (u32OfNat (ctr0 + i))

/-! ## Value-adequacy bridge: `spqrGen`'s block splits to exactly what `spqr_chain_next` returns.

`spqr_chain_next next ctr` returns `(ctr+1, new_next, out_key)`, and `spqrGen` was built so that its
block is `concat new_next out_key`. Since `spqrSplit = splitPure` and `splitPure (concat a b) = (a, b)`
(the split is the inverse of `concat`), splitting `spqrGen`'s block recovers exactly the chain step's
returned `(new_next, out_key)`. So the step-indexed hybrid below is over the genuine SPQR step, not an
unrelated function. -/

theorem spqrSplit_concat (a b : Key) : spqrSplit (RatchetSecurity.concat a b) = (a, b) := by
  rw [Spqr.ChainSplit.spqrSplit_eq_splitPure]
  apply Prod.ext
  · apply Subtype.ext; apply List.ext_getElem!
    · simp only [Array.length_eq]
    · intro j
      by_cases hj : j < 32
      · rw [RatchetSecurity.splitPure_fst _ j hj, RatchetSecurity.concat_lo a b j hj]
      · rw [getElem!_neg, getElem!_neg] <;> (simp only [Array.length_eq]; scalar_tac)
  · apply Subtype.ext; apply List.ext_getElem!
    · simp only [Array.length_eq]
    · intro j
      by_cases hj : j < 32
      · rw [RatchetSecurity.splitPure_snd _ j hj, RatchetSecurity.concat_hi a b j hj]
      · rw [getElem!_neg, getElem!_neg] <;> (simp only [Array.length_eq]; scalar_tac)

/-- **The SPQR ratchet step IS one step-indexed generic step.** For any chain key `next` and counter
offset `i`, `genStepI spqrSplit (spqrGen ctr0) i next` (split of the `i`-th counter-indexed block) is
exactly the `(new_next, out_key)` pair the extracted `spqr_chain_next next (ctr0+i)` returns. This
pins the hybrid's per-step plumbing to the real chain step. -/
theorem spqrGen_step_eq (ctr0 i : ℕ) (next : Key) :
    ∀ r, sha256.spqr_chain_next next (u32OfNat (ctr0 + i)) = .ok r →
      genStepI spqrSplit (spqrGen ctr0) i next = (r.2.1, r.2.2) := by
  intro r hr
  simp only [genStepI, spqrGen, spqrBlock, hr, spqrSplit_concat]

/-! ## The SPQR ratchet keystream as the step-indexed-hybrid instance.

`spqrSplit` (reused verbatim, with `spqrSplit_bijective`) is the length-doubling split; `spqrGen ctr0`
is the counter-indexed generator family; base `t := 0`. These are *defeq aliases* of the
`RatchetGenericIndexed` constructions (a `def := genX spqrSplit (spqrGen ctr0) …`), so the headline
theorems are the generic step-indexed ones instantiated — the hybrid argument is proved once, in
`GenericIndexed.lean`. -/

/-- The SPQR symmetric-ratchet keystream as a PRG (seed = initial chain key, output = the `n`
emitted output keys), from initial counter `ctr0`. -/
def spqrRatchetPRG (ctr0 n : ℕ) : PRGScheme Key (List.Vector Key n) :=
  genRatchetPRGI spqrSplit (spqrGen ctr0) n 0

/-- Hop `i`'s reduction adversary (against the per-hop block PRG `genBlockPRGI (spqrGen ctr0) i`). -/
def spqrReduction (ctr0 n i : ℕ) (A : PRGAdversary (List.Vector Key n)) : PRGAdversary Blk64 :=
  genReductionI spqrSplit (spqrGen ctr0) n 0 i A

/-- **SPQR keystream `Σε` bound.** The pseudorandomness advantage of the SPQR symmetric-ratchet
keystream (from initial counter `ctr0`) is bounded by the sum, over the `n` hops, of the per-hop
counter-indexed block-PRG's advantage against the explicit per-step reduction — the protocol-shaped
`Σε` bound. (The SPQR instance of `RatchetGenericIndexed.gen_advantage_le_sum`, with `spqrSplit_bijective`
supplying the split-of-uniform-block = independent-uniform-keys fact.) -/
theorem spqr_ratchet_advantage_le_sum (ctr0 n : ℕ) (A : PRGAdversary (List.Vector Key n)) :
    (spqrRatchetPRG ctr0 n).prgAdvantage A
      ≤ ∑ i ∈ Finset.range n,
          (genBlockPRGI (spqrGen ctr0) (0 + i)).prgAdvantage (spqrReduction ctr0 n i A) :=
  gen_advantage_le_sum spqrSplit spqrSplit_bijective (spqrGen ctr0) n 0 A

/-- **SPQR keystream asymptotic pseudorandomness (the headline).** If each counter-indexed block
generator `G_i = genBlockPRGI (spqrGen ctr0) i` is a secure PRG — every per-hop reduction's advantage
bounded by one negligible `ε` (the per-step PRG-security HYPOTHESIS, structurally identical to
`RatchetSecurity.ratchet_secure_asymptotic`'s per-step bound; NOT an axiom, NO new game) — and the
chain length is polynomially bounded, then the SPQR symmetric-ratchet keystream family (from initial
counter `0`) is pseudorandom. (The SPQR instance of `RatchetGenericIndexed.gen_secure_asymptotic_idx`.) -/
theorem spqr_ratchet_secure_asymptotic
    (len : ℕ → ℕ)
    (A : ∀ sp, PRGAdversary (List.Vector Key (len sp)))
    (ε : ℕ → ℝ≥0∞) (hε : negligible ε)
    (hbound : ∀ sp, ∀ i < len sp,
      ENNReal.ofReal ((genBlockPRGI (spqrGen 0) i).prgAdvantage
        (spqrReduction 0 (len sp) i (A sp))) ≤ ε sp)
    (hlen : ∃ p : Polynomial ℕ, ∀ sp, len sp ≤ p.eval sp) :
    negligible (fun sp => ENNReal.ofReal ((spqrRatchetPRG 0 (len sp)).prgAdvantage (A sp))) :=
  gen_secure_asymptotic_idx (fun _ => Key) (fun _ => Blk64)
    (fun _ => spqrSplit) (fun _ => spqrSplit_bijective) (fun _ => spqrGen 0) len A ε hε hbound hlen

end Spqr.RatchetPrg
