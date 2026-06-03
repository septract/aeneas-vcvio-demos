/-
  Demo 2b (security bridge) — the **meaty** 32-byte combiner, used as a stream cipher,
  proven pseudorandom by reduction to PRG security.

  The cipher's keystream/message/ciphertext type is the *native* Aeneas array `Array U8 32`
  (definitionally `List.Vector U8 32`, so it inherits `Fintype`/`SampleableType`). Encryption
  is the Aeneas-extracted `combine` (the `while`-loop over byte arrays). Using the
  loop-invariant value-adequacy `stream.combine_spec`, we show the per-message map is a
  permutation, and conclude — exactly as in `StreamSecurity` for `BitVec 64` — that the
  cipher's pseudorandomness advantage equals the underlying PRG's, via the reduction
  `r ↦ A (combine r msg)`.
-/
import Demos.StreamCipher.LoopCorrectness
import VCVio.CryptoFoundations.PRG
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.CryptoFoundations.Asymptotics.Negligible
import VCVio.OracleComp.QueryTracking.QueryBound
import Mathlib.Data.Fintype.Vector

open Aeneas Std OracleComp ENNReal PRGScheme

namespace StreamByteSecurity

/-- A 32-byte block: the native Aeneas array type, definitionally `List.Vector U8 32`. -/
abbrev Block := Std.Array Std.U8 32#usize

/-- `U8` is in bijection with `BitVec 8` (it wraps one). -/
def u8Equiv : Std.U8 ≃ BitVec 8 where
  toFun x := x.bv
  invFun b := ⟨b⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Std.U8 := Fintype.ofEquiv _ u8Equiv.symm
instance : SampleableType Std.U8 := SampleableType.ofEquiv u8Equiv.symm
instance : Fintype Block := inferInstanceAs (Fintype (List.Vector Std.U8 32))
instance : SampleableType Block := inferInstanceAs (SampleableType (List.Vector Std.U8 32))

/-! ## Generic base lemma: uniform is invariant under any permutation. -/

theorem uniform_perm_invariant {R : Type} [SampleableType R] [Fintype R]
    (A : R → ProbComp Bool) (e : R ≃ R) :
    Pr[= true | (do let r ← $ᵗ R; A r)]
      = Pr[= true | (do let r ← $ᵗ R; A (e r))] := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  simp only [probOutput_uniformSample]
  exact (Equiv.tsum_eq e (fun r => (Fintype.card R : ℝ≥0∞)⁻¹ * Pr[= true | A r])).symm

/-! ## The extracted cipher and its value adequacy. -/

/-- Encryption = the Aeneas-extracted `combine`. The non-`ok` branch is provably
unreachable (`combine` is total, by `stream.combine_spec`). -/
def enc (ks m : Block) : Block :=
  match stream.combine ks m with
  | .ok c => c
  | _ => ks

/-- **Value adequacy** of the extracted loop at the block level: pointwise XOR. -/
theorem enc_spec (ks m : Block) (j : ℕ) (hj : j < 32) :
    (enc ks m).val[j]! = ks.val[j]! ^^^ m.val[j]! := by
  obtain ⟨r, hr, hpost⟩ := WP.spec_imp_exists (stream.combine_spec ks m)
  simp only [enc, hr]
  exact hpost j hj

/-- XOR-with-the-same-byte twice is the identity. -/
theorem u8_xor_cancel (a b : Std.U8) : a ^^^ b ^^^ b = a := by
  rw [U8.eq_equiv_bv_eq]
  simp only [UScalar.bv_xor, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Encrypting with a fixed message is an involution, hence a permutation of the key space. -/
theorem enc_enc (ks m : Block) : enc (enc ks m) m = ks := by
  apply Subtype.ext
  apply List.ext_getElem!
  · simp only [Array.length_eq]
  · intro n
    by_cases hn : n < 32
    · rw [enc_spec (enc ks m) m n hn, enc_spec ks m n hn]
      exact u8_xor_cancel _ _
    · rw [getElem!_neg, getElem!_neg] <;> (simp only [Array.length_eq]; scalar_tac)

/-- XOR-with-a-fixed-message as a permutation of the (byte-array) key space. -/
def encEquiv (m : Block) : Block ≃ Block where
  toFun ks := enc ks m
  invFun ks := enc ks m
  left_inv ks := enc_enc ks m
  right_inv ks := enc_enc ks m

/-! ## The stream cipher and its pseudorandomness reduction. -/

/-- The PRG-based stream cipher over 32-byte blocks, for a fixed message, as a `PRGScheme`:
its output is `combine (G seed) msg` — the Aeneas-extracted byte-array XOR. -/
def streamGen {S : Type} (prg : PRGScheme S Block) (m : Block) : PRGScheme S Block where
  gen s := enc (prg.gen s) m

/-- **Main reduction (byte-array version).** The 32-byte stream cipher's pseudorandomness
advantage equals the underlying PRG's advantage against the reduction `r ↦ A (combine r msg)`.
The encryption is the meaty Aeneas-extracted loop `combine`; its value adequacy
(`enc_spec`/`stream.combine_spec`) makes the per-message map a permutation. -/
theorem streamGen_advantage {S : Type} [SampleableType S]
    (prg : PRGScheme S Block) (m : Block) (A : PRGAdversary Block) :
    (streamGen prg m).prgAdvantage A = prg.prgAdvantage (fun r => A (enc r m)) := by
  have hreal : Pr[= true | (streamGen prg m).prgRealExp A]
      = Pr[= true | prg.prgRealExp (fun r => A (enc r m))] := by
    simp only [PRGScheme.prgRealExp, streamGen]
  have hideal : Pr[= true | (prgIdealExp A : ProbComp Bool)]
      = Pr[= true | (prgIdealExp (fun r => A (enc r m)) : ProbComp Bool)] := by
    simp only [PRGScheme.prgIdealExp]
    exact uniform_perm_invariant A (encEquiv m)
  unfold PRGScheme.prgAdvantage
  rw [hreal, hideal]

/-- The explicit reduction adversary: distinguish the PRG's output by first running the
extracted `combine` with the fixed message. Structurally it calls `A` once after one `combine`;
this efficiency observation is *informal* — we do not formalize a cost/poly-time bound (see the
README scope notes). -/
def reduction (m : Block) (A : PRGAdversary Block) : PRGAdversary Block :=
  fun r => A (enc r m)

/-- **Security (concrete).** The 32-byte stream cipher whose encryption is the meaty
Aeneas-extracted loop `combine` is at least as secure as the underlying PRG. -/
theorem streamGen_secure {S : Type} [SampleableType S]
    (prg : PRGScheme S Block) (m : Block) (A : PRGAdversary Block) :
    (streamGen prg m).prgAdvantage A ≤ prg.prgAdvantage (reduction m A) :=
  _root_.le_of_eq (streamGen_advantage prg m A)

/-- **Security (asymptotic).** Indexing the PRG and distinguisher by a security parameter
(the cipher reuses the same fixed 32-byte extracted `combine` block at every `sp`): if the
PRG family is secure (negligible advantage against the `reduction`), the cipher family is
secure (negligible distinguishing advantage). The honest end-to-end statement that the
extracted Rust loop, used as a stream cipher, is pseudorandom assuming `G` is a PRG. -/
theorem streamGen_secure_asymptotic {S : ℕ → Type} [∀ sp, SampleableType (S sp)]
    (G : ∀ sp, PRGScheme (S sp) Block) (m : ℕ → Block) (A : ∀ _sp, PRGAdversary Block)
    (hG : negligible fun sp => ENNReal.ofReal ((G sp).prgAdvantage (reduction (m sp) (A sp)))) :
    negligible fun sp => ENNReal.ofReal ((streamGen (G sp) (m sp)).prgAdvantage (A sp)) := by
  have heq : (fun sp => ENNReal.ofReal ((streamGen (G sp) (m sp)).prgAdvantage (A sp)))
      = (fun sp => ENNReal.ofReal ((G sp).prgAdvantage (reduction (m sp) (A sp)))) := by
    funext sp
    exact congrArg ENNReal.ofReal (streamGen_advantage (G sp) (m sp) (A sp))
  rw [heq]; exact hG

/-- The reduction adds **no** oracle queries: `reduction m A = fun r => A (enc r m)` runs only the
total extracted `combine` loop (a pure value computation, zero uniform-sampling queries) before
calling `A`. So it makes exactly as many queries as `A`, staying inside any query-bound class `A`
is in — efficiency preservation over the *meaty* extracted loop. -/
theorem reduction_queryBound (m : Block) (A : PRGAdversary Block) (q : ℕ)
    (hA : ∀ x, IsTotalQueryBound (A x) q) (r : Block) :
    IsTotalQueryBound (reduction m A r) q := hA (enc r m)

/-- **Security against the query-bounded adversary class (closing the "all adversaries" gap),
over the meaty extracted loop.** As in `Word.lean`, the PRG hardness assumption `hPRG` is made
relative to the query-bounded class (the satisfiable form of "`G` is a secure PRG"), and the
reduction is *proved* to stay in that class (`reduction_queryBound`), so the 32-byte
`combine`-based cipher is secure against the same class. The query-count caveat of `Word.lean`
applies (query-bounded ⊋ PPT). -/
theorem streamGen_secure_against_queryBounded {S : ℕ → Type} [∀ sp, SampleableType (S sp)]
    (G : ∀ sp, PRGScheme (S sp) Block) (m : ℕ → Block) (A : ∀ _sp, PRGAdversary Block)
    (q : ℕ → ℕ) (hA : ∀ sp x, IsTotalQueryBound (A sp x) (q sp))
    (ε : ℕ → ℝ≥0∞) (hε : negligible ε)
    (hPRG : ∀ sp (D : PRGAdversary Block),
              (∀ x, IsTotalQueryBound (D x) (q sp)) →
              ENNReal.ofReal ((G sp).prgAdvantage D) ≤ ε sp) :
    negligible fun sp => ENNReal.ofReal ((streamGen (G sp) (m sp)).prgAdvantage (A sp)) := by
  refine negligible_of_le (fun sp => ?_) hε
  rw [streamGen_advantage (G sp) (m sp) (A sp)]
  exact hPRG sp (reduction (m sp) (A sp))
    (fun r => reduction_queryBound (m sp) (A sp) (q sp) (hA sp) r)

end StreamByteSecurity
