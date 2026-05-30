/-
  Demo 3 — a symmetric-key KDF ratchet chain, proven pseudorandom by a HYBRID ARGUMENT.

  This is the first demo with genuine *protocol* shape: state (the chain key) threaded across
  `n` steps, a multi-hop game-walk, and the `Σε` / poly-many-hops soundness side condition.

      ck₀ ──step──▶ ck₁ ──step──▶ ck₂ ...        stepᵢ = ratchet_split (G ckᵢ)
       │            │                            (next chain key, message key) := split(G ck)
       ▼            ▼
      mk₀          mk₁          ...              the protocol output (message keys)

  The per-step *plumbing* — splitting a 64-byte KDF/PRG output block into the next 32-byte
  chain key and a 32-byte message key — is the Aeneas-extracted `ratchet.ratchet_split`, with
  value adequacy from `Demos/Ratchet/Step.lean`. The KDF/PRG `G` itself is abstract; its
  security (`G`'s output is pseudorandom) is the hardness assumption.

  Security: the message-key sequence from a uniform seed is indistinguishable from `n`
  independent uniform keys. We prove the standard hybrid: replace one PRG block at a time with
  uniform; each adjacent hop is a single reduction to `G`'s PRG security; the advantages
  telescope to `Σ_{i<n} prgAdvantage G (reduction i)`. Asymptotically, for a *polynomial* chain
  length the total advantage stays negligible — the "sound iff n = poly" side condition, made
  a literal Lean step (`negligible_polynomial_mul`).

  We deliberately use a length-doubling **PRG** hybrid (each hop a clean reduction to PRG
  security), not the PRF→stream-PRG path (whose collision argument is unfinished upstream).

  Scope (see README "What is deliberately not formalized"): this is Signal's *symmetric* KDF
  chain only — not the full Double Ratchet. `prgAdvantage` is over *all* adversaries: the
  reductions' efficiency ("calls `A` once") is an informal observation, not a formalized
  cost/poly-time bound (the cost-adequacy open item).
-/
import Demos.Ratchet.Step
import Demos.StreamCipher.ByteArray
import VCVio.CryptoFoundations.PRG
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.CryptoFoundations.Asymptotics.Negligible
import Mathlib.Data.Fintype.Vector

open Aeneas Std OracleComp ENNReal PRGScheme
open List (Vector)

namespace RatchetSecurity

/-! ## Types: chain/message keys (`Key`) and the PRG output block (`Blk64`). -/

/-- A 32-byte key (chain key or message key): the native Aeneas array, defeq `List.Vector U8 32`.
This is the same type as `StreamByteSecurity.Block`, so it reuses those `Fintype`/`SampleableType`
instances (and the underlying `Std.U8` instances). -/
abbrev Key := Std.Array Std.U8 32#usize

/-- A 64-byte KDF/PRG output block, defeq `List.Vector U8 64`. `ratchet_split` carves it into a
`(next chain key, message key)` pair. -/
abbrev Blk64 := Std.Array Std.U8 64#usize

instance : Fintype Blk64 := inferInstanceAs (Fintype (List.Vector Std.U8 64))
instance : SampleableType Blk64 := inferInstanceAs (SampleableType (List.Vector Std.U8 64))
instance : Inhabited Key := ⟨Array.repeat 32#usize 0#u8⟩
instance : Inhabited Blk64 := ⟨Array.repeat 64#usize 0#u8⟩

/-! ## The extracted per-step split, and that it is a bijection `Blk64 ≃ Key × Key`. -/

/-- The deterministic ratchet-step glue as a pure total function, driven by the Aeneas-extracted
`ratchet_split`. The non-`ok` branch is provably unreachable (`ratchet_split` is total, by
`ratchet.ratchet_split_spec`); it uses a distinguished value so totality does the work. -/
def splitPure (b : Blk64) : Key × Key :=
  match ratchet.ratchet_split b with
  | .ok p => p
  | _ => (Array.repeat 32#usize 0#u8, Array.repeat 32#usize 0#u8) -- unreachable (totality)

/-- **Value adequacy, collapsed.** The extracted `ratchet_split` is total and returns `splitPure`. -/
theorem ratchet_split_eq (b : Blk64) : ratchet.ratchet_split b = .ok (splitPure b) := by
  obtain ⟨p, hp, _⟩ := WP.spec_imp_exists (ratchet.ratchet_split_spec b)
  simp only [splitPure, hp]

/-- First component (next chain key) = the low half of the block. -/
theorem splitPure_fst (b : Blk64) (j : ℕ) (hj : j < 32) :
    (splitPure b).1.val[j]! = b.val[j]! := by
  obtain ⟨p, hp, h1, _⟩ := WP.spec_imp_exists (ratchet.ratchet_split_spec b)
  simp only [splitPure, hp]; exact h1 j hj

/-- Second component (message key) = the high half of the block. -/
theorem splitPure_snd (b : Blk64) (j : ℕ) (hj : j < 32) :
    (splitPure b).2.val[j]! = b.val[32 + j]! := by
  obtain ⟨p, hp, _, h2⟩ := WP.spec_imp_exists (ratchet.ratchet_split_spec b)
  simp only [splitPure, hp]; exact h2 j hj

/-- `splitPure` is injective: the two halves determine all 64 bytes. -/
theorem splitPure_injective : Function.Injective splitPure := by
  intro b b' h
  apply Subtype.ext
  apply List.ext_getElem!
  · simp only [Array.length_eq]
  · intro k
    by_cases hk : k < 64
    · by_cases hk32 : k < 32
      · have e1 : (splitPure b).1.val[k]! = (splitPure b').1.val[k]! := by rw [h]
        rw [← splitPure_fst b k hk32, ← splitPure_fst b' k hk32]; exact e1
      · -- k ∈ [32, 64): write k = 32 + (k - 32) with k - 32 < 32
        have hlt : k - 32 < 32 := by omega
        have hkeq : 32 + (k - 32) = k := by omega
        have e2 : (splitPure b).2.val[k - 32]! = (splitPure b').2.val[k - 32]! := by rw [h]
        have lb := splitPure_snd b (k - 32) hlt
        have lb' := splitPure_snd b' (k - 32) hlt
        rw [hkeq] at lb lb'
        rw [← lb, ← lb']; exact e2
    · rw [getElem!_neg, getElem!_neg] <;> (simp only [Array.length_eq]; scalar_tac)

/-- The explicit inverse of `splitPure`: concatenate the low (chain) and high (message) halves
back into one 64-byte block. (`Std.Array` is a length-indexed subtype of `List`.) -/
def concat (k m : Key) : Blk64 :=
  ⟨k.val ++ m.val, by rw [List.length_append, Array.length_eq, Array.length_eq]; scalar_tac⟩

theorem concat_lo (k m : Key) (j : ℕ) (hj : j < 32) : (concat k m).val[j]! = k.val[j]! := by
  have hk : j < k.val.length := by rw [Array.length_eq]; scalar_tac
  simp only [concat]; simp_lists

theorem concat_hi (k m : Key) (j : ℕ) (hj : j < 32) :
    (concat k m).val[32 + j]! = m.val[j]! := by
  simp only [concat]; simp_lists; congr 1; scalar_tac

/-- `splitPure` is surjective: every `(chain key, message key)` pair is `split (concat k m)`. -/
theorem splitPure_surjective : Function.Surjective splitPure := by
  rintro ⟨k, m⟩
  refine ⟨concat k m, Prod.ext ?_ ?_⟩
  · apply Subtype.ext; apply List.ext_getElem!
    · simp only [Array.length_eq]
    · intro j
      by_cases hj : j < 32
      · rw [splitPure_fst (concat k m) j hj, concat_lo k m j hj]
      · rw [getElem!_neg, getElem!_neg] <;> (simp only [Array.length_eq]; scalar_tac)
  · apply Subtype.ext; apply List.ext_getElem!
    · simp only [Array.length_eq]
    · intro j
      by_cases hj : j < 32
      · rw [splitPure_snd (concat k m) j hj, concat_hi k m j hj]
      · rw [getElem!_neg, getElem!_neg] <;> (simp only [Array.length_eq]; scalar_tac)

/-- **The split is a bijection** `Blk64 ≃ Key × Key`. Hence splitting a *uniform* 64-byte block
yields an *independent uniform* `(chain key, message key)` pair — the fact that powers the
adjacent hybrid hop. -/
theorem splitPure_bijective : Function.Bijective splitPure :=
  ⟨splitPure_injective, splitPure_surjective⟩

/-! ## The ratchet chain and its view as a PRG.

`G : Key → Blk64` is the abstract KDF/PRG block generator (its pseudorandomness is the
hardness assumption). One `step` derives `(next chain key, message key)` from a chain key by
splitting `G ck` with the extracted `ratchet_split`. The `keystream` iterates `step`. -/

/-- One ratchet step: split the abstract PRG's 64-byte block into `(next chain key, message key)`,
where the split is the Aeneas-extracted `ratchet_split`. -/
def step (G : Key → Blk64) (ck : Key) : Key × Key := splitPure (G ck)

/-- The message-key stream: iterate `step` from a seed chain key, collecting the `n` message
keys. The chain key is the state threaded across steps. -/
def keystream (G : Key → Blk64) : (n : ℕ) → Key → List.Vector Key n
  | 0, _ => .nil
  | _ + 1, ck => (step G ck).2 ::ᵥ keystream G _ (step G ck).1

/-- The ratchet as a PRG: seed = initial chain key, output = the `n` message keys. -/
def ratchetPRG (G : Key → Blk64) (n : ℕ) : PRGScheme Key (List.Vector Key n) where
  gen ck := keystream G n ck

/-- The abstract block generator as a `PRGScheme` (the hardness assumption is on *this*: its
64-byte output is pseudorandom). -/
def blockPRG (G : Key → Blk64) : PRGScheme Key Blk64 where gen := G

/-! ## The hybrid reduction.

`redStream G b n i` builds the full `n`-key vector for hybrid hop `i`: the first `i` keys are
*uniform* (sampled), the challenge block `b` is split in at depth `i` (its message-key half is
emitted, its chain-key half seeds the real chain), and the remaining keys are *real*. It
recurses on the length, so it lands in `List.Vector Key n` with no length casts. -/
def redStream (G : Key → Blk64) (b : Blk64) :
    (n : ℕ) → (i : ℕ) → ProbComp (List.Vector Key n)
  | 0, _ => pure .nil
  | _ + 1, 0 => pure ((splitPure b).2 ::ᵥ keystream G _ (splitPure b).1)
  | _ + 1, i + 1 => do
      let k ← $ᵗ Key
      let rest ← redStream G b _ i
      pure (k ::ᵥ rest)

/-- The reduction adversary for hop `i`: feed the assembled vector to the cipher distinguisher. -/
def reduction (G : Key → Blk64) (n i : ℕ) (A : PRGAdversary (List.Vector Key n)) :
    PRGAdversary Blk64 := fun b => redStream G b n i >>= A

/-- With the challenge block instantiated to a *real* PRG block `G s` and idealizing nothing
(`i = 0`), the reduction stream is exactly the real `keystream` from seed `s`. -/
theorem redStream_real_zero (G : Key → Blk64) (s : Key) (n : ℕ) :
    redStream G (G s) n 0 = pure (keystream G n s) := by
  cases n with
  | zero => rfl
  | succ n => simp only [redStream, keystream, step]

/-- **Endpoint (real).** Hop-`0`'s real experiment is the ratchet's real experiment. -/
theorem real_start (G : Key → Blk64) (n : ℕ) (A : PRGAdversary (List.Vector Key n)) :
    prgRealExp (blockPRG G) (reduction G n 0 A) = prgRealExp (ratchetPRG G n) A := by
  simp only [PRGScheme.prgRealExp, reduction, blockPRG, ratchetPRG]
  refine bind_congr fun s => ?_
  rw [redStream_real_zero, pure_bind]

/-- Sampling a pair uniformly is two independent uniform draws. -/
theorem prod_uniform_bind {α β γ : Type} [Fintype α] [Inhabited α] [SampleableType α]
    [Fintype β] [Inhabited β] [SampleableType β] (g : α × β → ProbComp γ) :
    (($ᵗ (α × β)) >>= g) = (do let a ← $ᵗ α; let b ← $ᵗ β; g (a, b)) := by
  show (((·, ·) <$> ($ᵗ α) <*> ($ᵗ β)) >>= g) = _
  simp [monad_norm]

/-- **The hybrid hop (the crux).** Splitting a *uniform* block yields an *independent uniform*
`(chain key, message key)`, so idealizing hop `i` (challenge block uniform) gives the same output
distribution as hop `i+1`'s real experiment (the real chain reseeded from a fresh uniform key).
By induction on the length, threading an arbitrary continuation `A`; the base case is the split
bijection (`splitPure_bijective`), the step commutes the two independent draws. -/
theorem glue (G : Key → Blk64) : ∀ (n i : ℕ) (A : List.Vector Key n → ProbComp Bool),
    Pr[= true | (do let b ← $ᵗ Blk64; redStream G b n i >>= A)]
      = Pr[= true | (do let s ← $ᵗ Key; redStream G (G s) n (i + 1) >>= A)] := by
  intro n
  induction n with
  | zero =>
    intro i A
    simp only [redStream, pure_bind]
    rw [probOutput_bind_const, probOutput_bind_const]
    simp
  | succ m ih =>
    intro i A
    cases i with
    | zero =>
      have hL : (do let b ← $ᵗ Blk64; redStream G b (m + 1) 0 >>= A)
          = (($ᵗ Blk64) >>= fun b =>
              (fun p : Key × Key => A (p.2 ::ᵥ keystream G m p.1)) (splitPure b)) := by
        simp only [redStream, pure_bind]
      have hR : (do let s ← $ᵗ Key; redStream G (G s) (m + 1) 1 >>= A)
          = (do let s ← $ᵗ Key; let k ← $ᵗ Key; A (k ::ᵥ keystream G m s)) := by
        simp only [redStream, redStream_real_zero, pure_bind, bind_assoc]
      rw [hL, hR,
        probOutput_bind_bijective_uniform_cross (α := Blk64) splitPure splitPure_bijective
          (fun p : Key × Key => A (p.2 ::ᵥ keystream G m p.1)) true,
        prod_uniform_bind]
    | succ j =>
      rw [show (do let b ← $ᵗ Blk64; redStream G b (m + 1) (j + 1) >>= A)
            = ($ᵗ Blk64) >>= fun b => ($ᵗ Key) >>= fun k =>
                redStream G b m j >>= fun rest => A (k ::ᵥ rest) from by
          simp only [redStream, bind_assoc, pure_bind]]
      rw [probOutput_bind_bind_swap ($ᵗ Blk64) ($ᵗ Key)
            (fun b k => redStream G b m j >>= fun rest => A (k ::ᵥ rest)) true]
      rw [probOutput_bind_congr' ($ᵗ Key) true (fun k => ih j (fun rest => A (k ::ᵥ rest)))]
      rw [show (do let s ← $ᵗ Key; redStream G (G s) (m + 1) (j + 2) >>= A)
            = ($ᵗ Key) >>= fun s => ($ᵗ Key) >>= fun k =>
                redStream G (G s) m (j + 1) >>= fun rest => A (k ::ᵥ rest) from by
          simp only [redStream, bind_assoc, pure_bind]]
      rw [probOutput_bind_bind_swap ($ᵗ Key) ($ᵗ Key)
            (fun s k => redStream G (G s) m (j + 1) >>= fun rest => A (k ::ᵥ rest)) true]

/-! ## The ideal endpoint: `n` independent uniform keys. -/

/-- `n` independent uniform keys, assembled as a vector. -/
def uniformVec : (n : ℕ) → ProbComp (List.Vector Key n)
  | 0 => pure .nil
  | _ + 1 => do let k ← $ᵗ Key; let rest ← uniformVec _; pure (k ::ᵥ rest)

/-- Once the idealized prefix covers the whole length (`n ≤ i`), the challenge block is never
used and the reduction stream is just `n` independent uniform keys. -/
theorem redStream_ideal (G : Key → Blk64) (b : Blk64) :
    ∀ (n i : ℕ), n ≤ i → redStream G b n i = uniformVec n := by
  intro n
  induction n with
  | zero => intro i _; rfl
  | succ m ih =>
    intro i hi
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    simp only [redStream, uniformVec]
    rw [ih i' (by omega)]

/-- Consing is a bijection `Key × List.Vector Key m ≃ List.Vector Key (m+1)`. -/
theorem cons_bijective (m : ℕ) :
    Function.Bijective (fun p : Key × List.Vector Key m => p.1 ::ᵥ p.2) := by
  constructor
  · rintro ⟨k, v⟩ ⟨k', v'⟩ h
    obtain ⟨rfl, rfl⟩ := Vector.injective2_cons h
    rfl
  · intro w
    exact ⟨(w.head, w.tail), Vector.cons_head_tail w⟩

/-- **Independent uniform keys = a uniform vector.** `n` i.i.d. uniform keys have the same output
distribution as one uniform draw from `List.Vector Key n`. By induction via the cons bijection. -/
theorem uniformVec_eq (n : ℕ) (A : List.Vector Key n → ProbComp Bool) :
    Pr[= true | uniformVec n >>= A] = Pr[= true | ($ᵗ (List.Vector Key n)) >>= A] := by
  induction n with
  | zero =>
    simp only [uniformVec, pure_bind]
    rw [probOutput_bind_eq_tsum]
    rw [tsum_eq_single Vector.nil (by intro v hv; exact absurd (Subsingleton.elim v _) hv)]
    simp
  | succ m ih =>
    rw [← probOutput_bind_bijective_uniform_cross (α := Key × List.Vector Key m)
          (fun p => p.1 ::ᵥ p.2) (cons_bijective m) A true]
    rw [prod_uniform_bind]
    simp only [uniformVec, bind_assoc, pure_bind]
    refine probOutput_bind_congr' ($ᵗ Key) true (fun k => ?_)
    exact ih (fun v => A (k ::ᵥ v))

/-- **Endpoint (ideal).** Hop-`n`'s real experiment is the ratchet's ideal experiment (`n`
independent uniform message keys). -/
theorem ideal_end (G : Key → Blk64) (n : ℕ) (A : PRGAdversary (List.Vector Key n)) :
    Pr[= true | prgRealExp (blockPRG G) (reduction G n n A)]
      = Pr[= true | (prgIdealExp A : ProbComp Bool)] := by
  simp only [PRGScheme.prgRealExp, PRGScheme.prgIdealExp, reduction, blockPRG]
  have hcomp : ($ᵗ Key >>= fun s => redStream G (G s) n n >>= A)
      = ($ᵗ Key >>= fun _ => uniformVec n >>= A) := by
    refine bind_congr fun s => ?_
    rw [redStream_ideal G (G s) n n le_rfl]
  rw [hcomp, probOutput_bind_const ($ᵗ Key) (uniformVec n >>= A) true, uniformVec_eq]
  simp

/-- **Consecutive hybrids glue.** Hop `i`'s *ideal* experiment is hop `i+1`'s *real*
experiment — this is `glue` read through the PRG experiment definitions. -/
theorem ideal_eq_next (G : Key → Blk64) (n i : ℕ) (A : PRGAdversary (List.Vector Key n)) :
    Pr[= true | (prgIdealExp (reduction G n i A) : ProbComp Bool)]
      = Pr[= true | prgRealExp (blockPRG G) (reduction G n (i + 1) A)] := by
  simp only [PRGScheme.prgIdealExp, PRGScheme.prgRealExp, reduction, blockPRG]
  exact glue G n i A

/-! ## The telescoping hybrid bound. -/

/-- Hop `i`'s real-experiment winning probability (the hybrid sequence). -/
noncomputable def hyb (G : Key → Blk64) (n : ℕ) (A : PRGAdversary (List.Vector Key n)) (i : ℕ) :
    ℝ := (Pr[= true | prgRealExp (blockPRG G) (reduction G n i A)]).toReal

/-- **Main theorem (concrete hybrid bound).** The ratchet keystream's pseudorandomness advantage
is bounded by the sum, over the `n` steps, of the underlying block-PRG's advantage against the
explicit per-step reductions. Each summand is one game hop; the bound is the telescoping
triangle inequality `|hyb 0 − hyb n| ≤ Σ |hyb i − hyb (i+1)|`, with every hop equal to a PRG
advantage (`glue`). This is the protocol-shaped result: the total advantage is `Σε` over the
chain, not a single `ε`. -/
theorem ratchet_advantage_le_sum (G : Key → Blk64) (n : ℕ)
    (A : PRGAdversary (List.Vector Key n)) :
    (ratchetPRG G n).prgAdvantage A
      ≤ ∑ i ∈ Finset.range n, (blockPRG G).prgAdvantage (reduction G n i A) := by
  have hhop : ∀ i, (blockPRG G).prgAdvantage (reduction G n i A)
      = |hyb G n A i - hyb G n A (i + 1)| := by
    intro i
    unfold PRGScheme.prgAdvantage hyb
    rw [ideal_eq_next G n i A]
  have hstart : (ratchetPRG G n).prgAdvantage A = |hyb G n A 0 - hyb G n A n| := by
    unfold PRGScheme.prgAdvantage hyb
    rw [← real_start G n A, ← ideal_end G n A]
  rw [hstart]
  simp_rw [hhop]
  calc |hyb G n A 0 - hyb G n A n|
      = |∑ i ∈ Finset.range n, (hyb G n A i - hyb G n A (i + 1))| := by
        rw [Finset.sum_range_sub' (hyb G n A) n]
    _ ≤ ∑ i ∈ Finset.range n, |hyb G n A i - hyb G n A (i + 1)| :=
        Finset.abs_sum_le_sum_abs _ _

/-! ## Asymptotic security: the poly-many-hops side condition. -/

/-- **Asymptotic security (the headline).** Index the block PRG, the distinguisher, and the
*chain length* `len` by a security parameter `sp`. If the block PRG family is secure — each of
the per-step reductions has advantage bounded by one negligible `ε` — **and the chain length is
polynomially bounded**, then the ratchet keystream family is pseudorandom (negligible advantage).

The polynomial bound on `len` is *essential and used*: the proof bounds the advantage by
`len sp · ε sp` and discharges negligibility through `negligible_polynomial_mul`. Drop the
polynomial hypothesis and the proof does not close — this is the theory note's "`Σε` is
negligible iff the number of hops is polynomial" side condition, made a literal Lean step. -/
theorem ratchet_secure_asymptotic
    (G : ℕ → Key → Blk64) (len : ℕ → ℕ)
    (A : ∀ sp, PRGAdversary (List.Vector Key (len sp)))
    (ε : ℕ → ℝ≥0∞) (hε : negligible ε)
    (hbound : ∀ sp, ∀ i < len sp,
      ENNReal.ofReal ((blockPRG (G sp)).prgAdvantage (reduction (G sp) (len sp) i (A sp))) ≤ ε sp)
    (hlen : ∃ p : Polynomial ℕ, ∀ sp, len sp ≤ p.eval sp) :
    negligible (fun sp =>
      ENNReal.ofReal ((ratchetPRG (G sp) (len sp)).prgAdvantage (A sp))) := by
  obtain ⟨p, hp⟩ := hlen
  refine negligible_of_le (fun sp => ?_) (negligible_polynomial_mul hε p)
  calc ENNReal.ofReal ((ratchetPRG (G sp) (len sp)).prgAdvantage (A sp))
      ≤ ENNReal.ofReal (∑ i ∈ Finset.range (len sp),
          (blockPRG (G sp)).prgAdvantage (reduction (G sp) (len sp) i (A sp))) :=
        ENNReal.ofReal_le_ofReal (ratchet_advantage_le_sum (G sp) (len sp) (A sp))
    _ = ∑ i ∈ Finset.range (len sp),
          ENNReal.ofReal ((blockPRG (G sp)).prgAdvantage (reduction (G sp) (len sp) i (A sp))) :=
        ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)
    _ ≤ ∑ _i ∈ Finset.range (len sp), ε sp :=
        Finset.sum_le_sum (fun i hi => hbound sp i (Finset.mem_range.mp hi))
    _ = (len sp : ℝ≥0∞) * ε sp := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (↑(p.eval sp) : ℝ≥0∞) * ε sp := by
        gcongr
        exact_mod_cast hp sp

end RatchetSecurity
