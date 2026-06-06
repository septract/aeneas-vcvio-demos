/-
  Wire phase — instantiating HmacPrf's abstract compression `f` at the **genuine extracted**
  `sha256.sha256_compress`, and turning the prose "sha256 is `cascade sha256_compress H0`" into a
  real theorem (the extracted multi-block hash IS the Merkle–Damgård cascade of the extracted
  compression).

  INTEGRITY: the pure compression `compressPure` is *defined from* the extracted
  `Demos.Extracted.Sha256.sha256.sha256_compress` via its totality proof
  (`Sha256.sha256_compress_total`); it is NOT a hand-written FIPS round function. The trusted link
  is the closed lemma `compress_eq_ok : sha256_compress st blk = .ok (compressPure st blk)` — so the
  cascade and the PRF instantiation below provably reduce *through* the extracted code. `#print
  axioms` on the wired declarations reports only `[propext, Classical.choice, Quot.sound]` (the
  totality lemmas are theorems, not axioms); the compression-PRF assumption is a HYPOTHESIS, never an
  axiom.

  Status (round 1 of the Wire phase): what is closed here —
  - `compressPure` + `compress_eq_ok` — the totalized pure projection of the extracted compression,
    provably equal to the `Result`-monadic extraction on all inputs (the trusted link);
  - `extractBlockPure` + `extract_block_eq_ok` — the same for the per-block extraction loop;
  - `extractBlocks` — the pure list of the `nblocks` 64-byte message blocks;
  - `sha256_loop2_eq_cascade` — **the fold identity**: the extracted block-absorption loop
    `sha256_loop2 nblocks buf state 0` returns `ok (cascade compressPure state (extractBlocks …))`,
    i.e. the extracted multi-block driver IS `HmacPrf.cascade` of the extracted compression. Proved
    by a `Std.loop.spec_decr_nat` invariant ("state = cascade compressPure H0 (blocks 0..b)");
  - `sha256CompressionPRF` — `HmacPrf.compressionPRF` instantiated at the *extracted* `compressPure`,
    so "SHA-256 compression is a PRF" is exactly `negligible (sha256CompressionPRF.prfAdvantage)`;
  - the SPQR-path floor headline `sha256_cascade_prfAdvantage_le_qmul`: under the compression-PRF
    assumption (a hypothesis), the cascade of the extracted compression has advantage `≤ q · ε`,
    via `HmacPrf.cascadeFixedLen_prfAdvantage_le_qmul_simCorrect`.

  HONEST SCOPE (do NOT overclaim): this wires the HMAC/cascade layer *down to* the
  compression-PRF assumption, over the genuine extracted compression. The remaining bridges are
  unbuilt and documented as such: (i) the per-hop simulation-correctness pins + the ideal-endpoint
  interpolation of the cascade hybrid (the deep, lazy-RO distributional step in `HmacPrf.lean`);
  (ii) HMAC = NMAC ∘ key-derivation (BCK); (iii) HKDF-Extract PRK-pseudorandomness (Krawczyk 2010);
  (iv) the final wiring into the SPQR ratchet's per-hop PRG hypothesis. The compression-PRF
  assumption stays the named atomic floor.
-/
import Demos.Crypto.Sha256
import Demos.Crypto.HmacPrf
import VCVio.CryptoFoundations.Asymptotics.Negligible

open Aeneas Std Result OracleComp OracleSpec ENNReal

namespace Sha256Wire

/-! ## The totalized pure projection of the extracted compression (the trusted link) -/

/-- A canonical inhabitant of the chaining-state type, used only as the (never-reached) default of
the result projection. -/
def stateDefault : Array Std.U32 8#usize := Array.repeat 8#usize 0#u32

/-- **The pure SHA-256 compression**, projected from the extracted `Result`-monadic
`sha256.sha256_compress` via `Option.ofResult`. On every input the extracted code is total
(`Sha256.sha256_compress_total`), so the `Option.getD` default `stateDefault` is *never* reached —
`compress_eq_ok` below proves the projection equals the extracted function on all inputs. This is
the honest adapter the briefing requires: we wire TO the extracted compression, we do not
reimplement it. -/
def compressPure (state : Array Std.U32 8#usize) (block : Array Std.U8 64#usize) :
    Array Std.U32 8#usize :=
  (Option.ofResult (sha256.sha256_compress state block)).getD stateDefault

/-- **The trusted link.** The extracted `Result`-monadic compression equals `ok (compressPure …)` on
*every* input — derived purely from totality, no hand-edit of the extracted def. This is the lemma
the entire wiring rests on: every downstream `cascade` / PRF reduction reduces *through* the
extracted `sha256_compress`. -/
theorem compress_eq_ok (state : Array Std.U32 8#usize) (block : Array Std.U8 64#usize) :
    sha256.sha256_compress state block = .ok (compressPure state block) := by
  have htot := Sha256.sha256_compress_total state block
  -- Totality rules out `fail`/`div`, so the result is `ok v` for some `v`.
  unfold compressPure Option.ofResult
  cases h : sha256.sha256_compress state block with
  | ok v => simp
  | fail e => rw [h] at htot; simp at htot
  | div => rw [h] at htot; simp at htot

/-! ## The pure per-block extraction -/

/-- A canonical inhabitant of the 64-byte block type (the never-reached default). -/
def blockDefault : Array Std.U8 64#usize := Array.repeat 64#usize 0#u8

/-- **The pure block extraction**, projected from the extracted `sha256.extract_block` via its
totality (`Sha256.extract_block_total`, valid when `off + 64 ≤ 2048`). -/
def extractBlockPure (buf : Array Std.U8 2048#usize) (off : Std.Usize) : Array Std.U8 64#usize :=
  (Option.ofResult (sha256.extract_block buf off)).getD blockDefault

/-- The trusted link for block extraction: `extract_block buf off = ok (extractBlockPure …)` when the
block fits (`off + 64 ≤ 2048`). -/
theorem extract_block_eq_ok (buf : Array Std.U8 2048#usize) (off : Std.Usize)
    (hoff : off.val + 64 ≤ 2048) :
    sha256.extract_block buf off = .ok (extractBlockPure buf off) := by
  have htot := Sha256.extract_block_total buf off hoff
  unfold extractBlockPure Option.ofResult
  cases h : sha256.extract_block buf off with
  | ok v => simp
  | fail e => rw [h] at htot; simp at htot
  | div => rw [h] at htot; simp at htot

/-! ## The pure list of message blocks -/

/-- The `Usize` offset of block `b`: `64 · b`, constructed with its in-bounds proof when it fits in
a `Usize` (which it always does for the message-block range `b < nblocks ≤ 32`, where `64·b <
2048`), and defaulting to `0` otherwise — the default is never reached on the in-range slice the
cascade theorem lives on. -/
def blockOffset (b : ℕ) : Std.Usize :=
  if h : 64 * b < 2 ^ System.Platform.numBits then
    UScalar.ofNatCore (ty := UScalarTy.Usize) (64 * b) (by rw [UScalarTy.Usize_numBits_eq]; exact h)
  else 0#usize

/-- The pure list of the `nblocks` 64-byte message blocks of `buf`, in order: block `b` is
`extractBlockPure buf (64·b)`. This is `HmacPrf.cascade`'s input list — the value the extracted
`sha256_loop2` folds the compression over. -/
def extractBlocks (buf : Array Std.U8 2048#usize) (nblocks : ℕ) : List (Array Std.U8 64#usize) :=
  (List.range nblocks).map (fun b => extractBlockPure buf (blockOffset b))

@[simp] theorem extractBlocks_length (buf : Array Std.U8 2048#usize) (nblocks : ℕ) :
    (extractBlocks buf nblocks).length = nblocks := by simp [extractBlocks]

/-- The block at position `b < nblocks` of `extractBlocks` is `extractBlockPure buf (blockOffset b)`. -/
theorem extractBlocks_getElem (buf : Array Std.U8 2048#usize) (nblocks : ℕ) (b : ℕ)
    (hb : b < nblocks) :
    (extractBlocks buf nblocks)[b]'(by simp [hb]) = extractBlockPure buf (blockOffset b) := by
  simp [extractBlocks, List.getElem_map, List.getElem_range]

/-- Dropping `b` blocks (for `b < nblocks`) exposes block `b` at the head, then the rest. -/
theorem extractBlocks_drop (buf : Array Std.U8 2048#usize) (nblocks : ℕ) (b : ℕ)
    (hb : b < nblocks) :
    List.drop b (extractBlocks buf nblocks) =
      extractBlockPure buf (blockOffset b) :: List.drop (b + 1) (extractBlocks buf nblocks) := by
  have hbl : b < (extractBlocks buf nblocks).length := by simp [hb]
  rw [List.drop_eq_getElem_cons hbl, extractBlocks_getElem buf nblocks b hb]

/-! ## The offset computed by the loop matches `blockOffset` -/

/-- The extracted loop computes the block offset as `64#usize * b`. For `b < nblocks ≤ 32` this
checked multiplication succeeds and its value is `64 · b = blockOffset b` — pinning the offset the
pure `extractBlocks` uses to the one the extracted loop actually computes. -/
theorem mul_offset_eq (nblocks : Std.Usize) (b1 : Std.Usize)
    (hnb : nblocks.val ≤ 32) (hlt : b1.val < nblocks.val) :
    (64#usize * b1 : Result Std.Usize) = Result.ok (blockOffset b1.val) := by
  have hb32 : b1.val < 32 := Nat.lt_of_lt_of_le hlt hnb
  have hmax : (64#usize).val * b1.val ≤ Usize.max := by scalar_tac
  have hspec := Std.Usize.mul_spec (x := 64#usize) (y := b1) hmax
  have hbnd : 64 * b1.val < 2 ^ System.Platform.numBits := by
    have hpb : 2 ^ 16 ≤ 2 ^ System.Platform.numBits := by
      apply Nat.pow_le_pow_right (by norm_num)
      cases System.Platform.numBits_eq <;> simp_all
    omega
  -- The product is `ok z` with `z.val = 64 * b1.val`; identify `z` with `blockOffset b1.val`.
  generalize hr : (64#usize * b1) = r at hspec ⊢
  match r, hspec with
  | .ok z, hspec =>
    rw [Std.WP.spec_ok] at hspec
    have hzv : z.val = 64 * b1.val := by
      have h64 : (64#usize).val = 64 := by scalar_tac
      rw [hspec, h64]
    refine congrArg Result.ok ?_
    apply Std.UScalar.eq_of_val_eq
    rw [hzv]
    unfold blockOffset
    rw [dif_pos hbnd]
    rfl
  | .fail e, hspec => exact absurd hspec (by rw [Std.WP.spec_fail]; exact not_false)
  | .div, hspec => exact absurd hspec (by rw [Std.WP.spec_div]; exact not_false)

/-! ## The fold identity: the extracted block-absorption loop IS the cascade -/

/-- **The block-absorption loop is the Merkle–Damgård cascade (value-level spec).** For `nblocks ≤
32` and any starting counter `b ≤ nblocks`, the extracted `sha256_loop2 nblocks buf state b` returns
`ok` of `HmacPrf.cascade compressPure state` applied to the *remaining* blocks `drop b
(extractBlocks buf nblocks)`. Specializing `b = 0` (next theorem) gives the full hash state as the
cascade over all blocks. Proved by a `Std.loop.spec_decr_nat` invariant; each iteration rewrites the
extracted offset/extract/compress steps to their pure projections (`mul_offset_eq`,
`extract_block_eq_ok`, `compress_eq_ok`) and folds one `cascade` step (`extractBlocks_drop`). -/
theorem sha256_loop2_eq_cascade_suffix (nblocks : Std.Usize) (buf : Array Std.U8 2048#usize)
    (hnb : nblocks.val ≤ 32) :
    ∀ (state : Array Std.U32 8#usize) (b : Std.Usize), b.val ≤ nblocks.val →
      sha256.sha256_loop2 nblocks buf state b
        ⦃ r => r = HmacPrf.cascade compressPure state
                  (List.drop b.val (extractBlocks buf nblocks.val)) ⦄ := by
  intro state b hb
  unfold sha256.sha256_loop2
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U32 8#usize) × Std.Usize => nblocks.val - s.2.val)
    (inv := fun s : (Array Std.U32 8#usize) × Std.Usize =>
      s.2.val ≤ nblocks.val ∧
        HmacPrf.cascade compressPure s.1 (List.drop s.2.val (extractBlocks buf nblocks.val)) =
          HmacPrf.cascade compressPure state (List.drop b.val (extractBlocks buf nblocks.val)))
    (post := fun r : Array Std.U32 8#usize =>
      r = HmacPrf.cascade compressPure state (List.drop b.val (extractBlocks buf nblocks.val)))
  · rintro ⟨st1, b1⟩ ⟨hb1, hcasc⟩
    simp only [sha256.sha256_loop2.body]
    split
    · rename_i hlt
      -- b1 < nblocks: one fold step.
      have hb1lt : b1.val < nblocks.val := by scalar_tac
      -- offset
      rw [mul_offset_eq nblocks b1 hnb hb1lt]
      -- extract_block at the pure offset (bound: 64*b1 + 64 ≤ 2048)
      have hoffbd : (blockOffset b1.val).val + 64 ≤ 2048 := by
        have hbv : (blockOffset b1.val).val = 64 * b1.val := by
          unfold blockOffset
          have hbnd : 64 * b1.val < 2 ^ System.Platform.numBits := by
            have hpb : 2 ^ 16 ≤ 2 ^ System.Platform.numBits := by
              apply Nat.pow_le_pow_right (by norm_num)
              cases System.Platform.numBits_eq <;> simp_all
            have : b1.val < 32 := hb1lt.trans_le hnb
            omega
          rw [dif_pos hbnd]; rfl
        have : b1.val < 32 := hb1lt.trans_le hnb
        omega
      simp only [Std.bind_tc_ok]
      rw [extract_block_eq_ok buf (blockOffset b1.val) hoffbd]
      -- compress
      simp only [Std.bind_tc_ok]
      rw [compress_eq_ok]
      simp only [Std.bind_tc_ok]
      -- increment the counter: it succeeds and equals `b1.val + 1`
      have hmaxadd : b1.val + (1#usize).val ≤ Usize.max := by
        have : b1.val < 32 := hb1lt.trans_le hnb
        scalar_tac
      have hspec := Std.Usize.add_spec (x := b1) (y := 1#usize) hmaxadd
      obtain ⟨bsucc, hbsucc, hbsuccval⟩ :
          ∃ z : Std.Usize, (b1 + 1#usize : Result Std.Usize) = Result.ok z ∧ z.val = b1.val + 1 := by
        cases hc : (b1 + 1#usize : Result Std.Usize) with
        | ok z =>
          rw [hc] at hspec; simp only [Std.WP.spec_ok] at hspec
          exact ⟨z, rfl, by scalar_tac⟩
        | fail e => rw [hc] at hspec; simp at hspec
        | div => rw [hc] at hspec; simp at hspec
      rw [hbsucc]
      simp only [Std.bind_tc_ok, Std.WP.spec_ok]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hbsuccval]; scalar_tac
      · -- cascade invariant preserved: one block absorbed
        simp only at hcasc ⊢
        rw [← hcasc]
        have hdrop := extractBlocks_drop buf nblocks.val b1.val hb1lt
        rw [hbsuccval, hdrop, HmacPrf.cascade_cons]
      · rw [hbsuccval]; scalar_tac
    · rename_i hge
      -- b1 ≥ nblocks: loop done, drop b1 = []
      simp only [Std.WP.spec_ok]
      have hb1ge : nblocks.val ≤ b1.val := by scalar_tac
      have hdropnil : List.drop b1.val (extractBlocks buf nblocks.val) = [] := by
        apply List.drop_eq_nil_of_le; simp [hb1ge]
      simp only at hcasc ⊢
      rw [← hcasc, hdropnil, HmacPrf.cascade_nil]
  · exact ⟨hb, rfl⟩

/-- **The extracted SHA-256 state IS the cascade of the extracted compression (headline).** The
extracted multi-block driver `sha256_loop2 nblocks buf H0 0`, started from the SHA-256 initial
vector `H0`, returns exactly `HmacPrf.cascade compressPure H0 (extractBlocks buf nblocks)` — turning
the prose "sha256 is `cascade sha256_compress H0`" into a theorem. The compression folded is the
*extracted* `sha256_compress` (via `compressPure` / `compress_eq_ok`), so this is the genuine
trusted-link identity, not a re-implementation. -/
theorem sha256_loop2_eq_cascade (nblocks : Std.Usize) (buf : Array Std.U8 2048#usize)
    (hnb : nblocks.val ≤ 32) :
    sha256.sha256_loop2 nblocks buf sha256.H0 0#usize =
      Result.ok (HmacPrf.cascade compressPure sha256.H0 (extractBlocks buf nblocks.val)) := by
  have h := sha256_loop2_eq_cascade_suffix nblocks buf hnb sha256.H0 0#usize (by simp)
  -- drop 0 = identity
  have h0 : (0#usize).val = 0 := by scalar_tac
  rw [h0] at h
  simp only [List.drop_zero] at h
  -- h : sha256_loop2 … ⦃ r => r = cascade … ⦄ ; extract the value
  generalize hr : sha256.sha256_loop2 nblocks buf sha256.H0 0#usize = r at h ⊢
  match r, h with
  | .ok z, h => rw [Std.WP.spec_ok] at h; rw [h]
  | .fail e, h => exact absurd h (by rw [Std.WP.spec_fail]; exact not_false)
  | .div, h => exact absurd h (by rw [Std.WP.spec_div]; exact not_false)

/-! ## The compression PRF instantiated at the extracted `sha256_compress`

`HmacPrf.compressionPRF`'s abstract `f : K → Block → K` is now instantiated at the *extracted*
`compressPure` (= the totalized `sha256.sha256_compress`). "SHA-256 compression is a PRF" is exactly
`negligible (fun κ => (sha256CompressionPRF keygen).prfAdvantage (advₖ))` — the named atomic floor,
stated as a hypothesis on the headline below, never an axiom. -/

/-- The chaining-state type of SHA-256 (`K` in `HmacPrf.cascade`): eight 32-bit words. -/
abbrev State := Array Std.U32 8#usize

/-- One SHA-256 input block (`Block` in `HmacPrf.cascade`): 64 bytes. -/
abbrev Block := Array Std.U8 64#usize

/-- **The SHA-256 compression function, as a VCVio `PRFScheme`, wired to the EXTRACTED code.**
The evaluation function is `compressPure`, the totalized projection of the extracted
`sha256.sha256_compress` (`compress_eq_ok` is the trusted link). The compression-PRF assumption is
the statement that *this* scheme has negligible `prfAdvantage`. -/
def sha256CompressionPRF (keygen : ProbComp State) : PRFScheme State Block State :=
  HmacPrf.compressionPRF keygen compressPure

@[simp] theorem sha256CompressionPRF_eval (keygen : ProbComp State) :
    (sha256CompressionPRF keygen).eval = compressPure := rfl

/-- The cascade of `sha256CompressionPRF` evaluates by `HmacPrf.cascade compressPure` — i.e. its
keyed iterated hash IS the Merkle–Damgård fold of the extracted compression (`sha256_loop2_eq_cascade`
connects this to the extracted multi-block driver). -/
theorem cascade_sha256CompressionPRF_eval (keygen : ProbComp State) (k : State) (blocks : List Block) :
    (HmacPrf.cascadePRF (sha256CompressionPRF keygen)).eval k blocks =
      HmacPrf.cascade compressPure k blocks := by
  simp [HmacPrf.cascadePRF, sha256CompressionPRF, HmacPrf.compressionPRF]

/-! ## The SPQR-path floor headline

Under the compression-PRF assumption (the named atomic floor, a HYPOTHESIS), the fixed-length
cascade of the EXTRACTED `sha256_compress` is a PRF up to the standard `q · ε` factor. This wires
`HmacPrf`'s cascade hybrid (`cascadeFixedLen_prfAdvantage_le_qmul_simCorrect`) at the extracted
compression. The per-hop simulation-correctness pins (`hreal`/`hideal`), the endpoint pins
(`hQ`/`h0`), and the uniform per-hop bound (`hbound`) are the cascade hybrid's remaining
obligations — the deep, lazy-RO distributional step left honestly open in `HmacPrf.lean`; this
headline does not discharge them, it *connects them to the extracted compression*.

The `[DecidableEq Block]` / `[SampleableType State]` / `[DecidableEq (List Block)]` instances are
taken as caller-supplied (instance-implicit): we do not fabricate the giant `Fintype` of the 8-word
state here (that would force a `maxRecDepth` smell). The statement is fully general in them — the
honest scope is "the extracted compression's cascade is a PRF *given* these standard structural
instances and the compression-PRF assumption". -/
theorem sha256_cascade_prfAdvantage_le_qmul
    [DecidableEq Block] [SampleableType State] [DecidableEq (List Block)]
    (keygen : ProbComp State) (n : ℕ)
    (adv : PRFScheme.PRFAdversary (List Block) State)
    (q : ℕ) (H : ℕ → ProbComp Bool)
    (hQ : H q = (HmacPrf.cascadeFixedLenPRF (sha256CompressionPRF keygen) n).prfRealExp adv)
    (h0 : H 0 = PRFScheme.prfIdealExp adv)
    (red : ℕ → PRFScheme.PRFAdversary Block State)
    (hreal : ∀ i ∈ Finset.range q,
      H (i + 1) = (sha256CompressionPRF keygen).prfRealExp (red i))
    (hideal : ∀ i ∈ Finset.range q,
      H i = PRFScheme.prfIdealExp (red i))
    (ε : ℝ)
    (hbound : ∀ i ∈ Finset.range q,
      (sha256CompressionPRF keygen).prfAdvantage (red i) ≤ ε) :
    (HmacPrf.cascadeFixedLenPRF (sha256CompressionPRF keygen) n).prfAdvantage adv ≤ q • ε :=
  HmacPrf.cascadeFixedLen_prfAdvantage_le_qmul_simCorrect
    (sha256CompressionPRF keygen) n adv q H hQ h0 red hreal hideal ε hbound

/-- **The compression-PRF assumption, named.** "SHA-256 compression is a PRF" — the atomic floor of
the whole tower, stated over the EXTRACTED `compressPure` via `sha256CompressionPRF`. For a
security-parameter-indexed key generator and adversary family, the distinguishing advantage against
the extracted compression is `negligible` (VCVio's `negligible`, coerced from `ℝ` via
`ENNReal.ofReal`). This is the `Prop` the cascade floor takes as a hypothesis; it is NEVER an axiom
and NEVER discharged here — it is precisely Bellare's standing assumption that the SHA-256
compression function is pseudorandom. -/
def Sha256CompressIsPRF [DecidableEq Block] [SampleableType State]
    (keygen : ℕ → ProbComp State) (advFam : ℕ → PRFScheme.PRFAdversary Block State) : Prop :=
  negligible (fun κ => ENNReal.ofReal
    ((sha256CompressionPRF (keygen κ)).prfAdvantage (advFam κ)))

end Sha256Wire
