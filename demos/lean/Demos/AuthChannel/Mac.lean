/-
  Demo 4 (message authentication) — part 1: the extracted MAC verify and its value adequacy,
  the canonical PRF-based MAC instantiated against VCVio's `MacAlg`, and perfect completeness.

  The MAC is the libsignal HMAC shape: a *deterministic canonical* MAC `tag(k,m) = F_k(m)`,
  `verify(k,m,t) = (F_k(m) == t)`, where `F` is a PRF (HMAC-SHA256 in libsignal), modeled
  abstractly here as a `PRFScheme`. The tag-comparison `verify` is the **Aeneas-extracted Rust**
  (`demos/rust/mac.rs`): a constant-length, all-bytes equality check. Its value adequacy
  (`verify_spec_pointwise`) is the ε=0 node link; the PRF assumption is the tower edge that
  Demo 6 (HMAC-is-a-PRF) would discharge down to the SHA-256 compression function.
-/
import Demos.Extracted.Mac
import VCVio.CryptoFoundations.MacAlg
import VCVio.CryptoFoundations.PRF

open Aeneas Std Result

namespace AuthMac

/-- The MAC tag space: the native 32-byte Aeneas array (HMAC-SHA256 output / SPQR `MAC_SIZE`). -/
abbrev Tag := Std.Array Std.U8 32#usize

/-! ## Value adequacy of the extracted `verify` loop -/

/-- Loop invariant for `mac.verify_loop`: the threaded flag `ok` records whether every byte
processed so far has matched. -/
theorem verify_loop_spec (a b : Tag) (i0 : Std.Usize) (ok0 : Bool)
    (hi0 : i0.val ≤ 32)
    (hok0 : ok0 = true ↔ ∀ j, j < i0.val → a.val[j]! = b.val[j]!) :
    mac.verify_loop a b i0 ok0 ⦃ r => r = true ↔ ∀ j, j < 32 → a.val[j]! = b.val[j]! ⦄ := by
  unfold mac.verify_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : Std.Usize × Bool => 32 - s.1.val)
    (inv := fun s : Std.Usize × Bool => s.1.val ≤ 32 ∧
      (s.2 = true ↔ ∀ j, j < s.1.val → a.val[j]! = b.val[j]!))
    (post := fun r : Bool => r = true ↔ ∀ j, j < 32 → a.val[j]! = b.val[j]!)
  · rintro ⟨i1, ok1⟩ ⟨hi1, hok1⟩
    simp only [mac.verify_loop.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨v2, hv2⟩
      split
      · -- bytes differ at index i1: the flag becomes `false`
        rename_i hne
        step as ⟨i3, hi3⟩
        refine ⟨?_, ?_, ?_⟩
        · scalar_tac
        · simp only [Bool.false_eq_true, false_iff]
          intro hall
          have hi : a.val[i1.val]! = b.val[i1.val]! := hall i1.val (by scalar_tac)
          grind
        · scalar_tac
      · -- bytes match at index i1: the flag carries `ok1` forward
        rename_i heq
        step as ⟨i3, hi3⟩
        have hi : a.val[i1.val]! = b.val[i1.val]! := by grind
        refine ⟨?_, ?_, ?_⟩
        · scalar_tac
        · rw [hok1]
          constructor
          · intro h j hj
            by_cases hje : j = i1.val
            · subst hje; exact hi
            · exact h j (by scalar_tac)
          · intro h j hj; exact h j (by scalar_tac)
        · scalar_tac
    · rename_i hge
      have h32 : i1.val = 32 := by scalar_tac
      show ok1 = true ↔ ∀ j, j < 32 → a.val[j]! = b.val[j]!
      constructor
      · intro htrue j hj; exact (hok1.mp htrue) j (h32.symm ▸ hj)
      · intro hall; exact hok1.mpr (fun j hj => hall j (h32 ▸ hj))
  · exact ⟨hi0, hok0⟩

/-- **Value adequacy.** The extracted `verify` is total and accepts iff the two tags agree on
every byte. -/
theorem verify_spec_pointwise (a b : Tag) :
    mac.verify a b ⦃ r => r = true ↔ ∀ j, j < 32 → a.val[j]! = b.val[j]! ⦄ := by
  unfold mac.verify
  apply verify_loop_spec
  · scalar_tac
  · simp

/-- Byte-array equality reduces to pointwise equality of all 32 entries. -/
theorem tag_eq_iff (a b : Tag) : a = b ↔ ∀ j, j < 32 → a.val[j]! = b.val[j]! := by
  constructor
  · rintro rfl _ _; rfl
  · intro h
    apply Subtype.ext
    apply List.ext_getElem!
    · simp only [Array.length_eq]
    · intro n
      by_cases hn : n < 32
      · exact h n hn
      · rw [getElem!_neg, getElem!_neg] <;> (simp only [Array.length_eq]; scalar_tac)

/-- The tag space has decidable equality (it is a 32-element list under the hood). -/
instance : DecidableEq Tag :=
  fun a b => decidable_of_iff _ (tag_eq_iff a b).symm

/-! ## The canonical PRF-based MAC, instantiated against VCVio's `MacAlg` -/

variable {K M : Type}

/-- Total Boolean view of the extracted verify (the non-`ok` branch is unreachable). -/
def verifyB (a t : Tag) : Bool :=
  match mac.verify a t with
  | .ok b => b
  | _ => false

/-- **The Boolean verify decides tag equality** (from `verify_spec_pointwise`). -/
@[simp] theorem verifyB_eq_true_iff (a t : Tag) : verifyB a t = true ↔ a = t := by
  obtain ⟨r, hr, hpost⟩ := WP.spec_imp_exists (verify_spec_pointwise a t)
  simp only [verifyB, hr]
  rw [hpost, ← tag_eq_iff]

/-- The **canonical deterministic MAC** built from a PRF `F`: `tag k m = F_k(m)`, and
`verify` runs the extracted byte-comparison on the recomputed tag. Computations live in
`ProbComp = OracleComp unifSpec` (so `keygen` is the PRF's key generation directly). -/
def macAlg (prf : PRFScheme K M Tag) : MacAlg ProbComp M K Tag where
  keygen := prf.keygen
  tag k m := pure (prf.eval k m)
  verify k m t := pure (verifyB (prf.eval k m) t)

@[simp] theorem macAlg_keygen (prf : PRFScheme K M Tag) :
    (macAlg prf).keygen = prf.keygen := rfl

@[simp] theorem macAlg_tag (prf : PRFScheme K M Tag) (k : K) (m : M) :
    (macAlg prf).tag k m = pure (prf.eval k m) := rfl

@[simp] theorem macAlg_verify (prf : PRFScheme K M Tag) (k : K) (m : M) (t : Tag) :
    (macAlg prf).verify k m t = pure (verifyB (prf.eval k m) t) := rfl

/-- **Perfect completeness.** Honestly generated tags always verify — because the extracted
`verify` decides equality and `F_k(m) = F_k(m)`. Stated for uniform-key PRFs (the standard
case; makes `keygen` total). -/
theorem macAlg_perfectlyComplete [SampleableType K] (prf : PRFScheme K M Tag)
    (hkey : prf.UniformKey) :
    (macAlg prf).PerfectlyComplete ProbCompRuntime.probComp := by
  intro msg
  have hv : ∀ k : K, verifyB (prf.eval k msg) (prf.eval k msg) = true :=
    fun k => (verifyB_eq_true_iff _ _).mpr rfl
  rw [PRFScheme.UniformKey] at hkey
  -- The canonical `ProbComp` runtime's `evalDist` is the ambient SPMF semantics, so
  -- `Pr[= true | probComp.evalDist X]` is just `Pr[= true | X]` (definitional).
  have hbridge : ∀ X : ProbComp Bool,
      Pr[= true | ProbCompRuntime.probComp.evalDist X] = Pr[= true | X] := fun _ => rfl
  simp only [hbridge, macAlg, pure_bind, hv, hkey]
  rw [probOutput_bind_const, probFailure_uniformSample]
  simp

end AuthMac
