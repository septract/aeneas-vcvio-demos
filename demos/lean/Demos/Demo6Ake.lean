/-
  Demo 6 (v2) — value-adequacy layer for a one-pass KEM-based key-transport protocol,
  extracted from synthetic Rust (`demos/rust/ke.rs`) via Charon + Aeneas.

  ## Honest scope (read this before trusting anything below)

  The Rust in `ke.rs` is a SYNTHETIC, deliberately-simple byte transform written only to be a
  clean Charon/Aeneas extraction target (fixed `[u8; 32]`, `while`-loops, no Vec/traits). It makes
  NO security claim on its own and — crucially — its `encaps` does NOT support an IND-CPA
  assumption: a passive adversary holding the public key `pk` and the ciphertext `ct` recovers the
  shared secret exactly, since
        encaps:  ct[i] = pk[i] ^ coins[i],   shared[i] = pk[i] & coins[i]
  and `keygen` makes `sk[i] = pk[i] ^ 0xFF` (so `sk` is a *public* function of `pk`). Hence
        shared[i] = pk[i] & (ct[i] ^ pk[i])
  is computable from `(pk, ct)` alone (verified numerically: 100000/100000 trials). A pure
  byte-XOR/AND core cannot carry a trapdoor, so it cannot honestly satisfy IND-CPA. This is a
  CONSTRUCTION limitation, documented openly here rather than papered over with an unsatisfiable
  "advantage ≤ ε" hypothesis (which would make any KI bound vacuously true — the v1-class failure).

  ## What this file DOES establish (axiom-clean, machine-checked)

  The *value-adequacy* bridge from the extracted `Result`-monad loops to pure byte transforms, plus
  the two structural facts a key-transport reduction relies on:

  - `encapsV_ct_spec` / `encapsV_key_spec` / `decapsV_spec` / `deriveV_spec`: the extracted loops
    compute exactly the documented pointwise byte transforms (via the loop-invariant pattern, like
    `stream.combine_spec`).
  - `decapsK_encapsK_correct`: on a keypair `(pk, sk) = keygen seed`, `decaps sk (encaps pk coins).ct
    = (encaps pk coins).shared` — decapsulation recovers the shared secret (functional KEM
    correctness).
  - `deriveK_injective` / `deriveEquiv`: the session-key derivation `H(shared)[i] = shared[i] ^ 0x5C`
    is an INVOLUTION, hence a bijection of the 256^32 key space — the non-degeneracy witness that
    distinguishes v2 from v1 (whose `k_i XOR k_r` collapsed to a constant). A derivation that is a
    permutation is neither constant nor entropy-collapsing.

  These are honest theorems about the extracted code independent of any security claim. The KI game
  and reduction are deferred (later refinement round); see the construction-limitation note above for
  why the eventual bound must be stated as an unconditional equality with an explicitly UNINSTANTIATED
  KEM IND-CPA assumption, not as a smallness bound consuming an unsatisfiable premise.

  ## Citation mapping (textbook construction this models)

  Boneh-Shoup, *A Graduate Course in Applied Cryptography* v0.6, §11.5 scheme `E_EG` (one-pass key
  transport, session key `k = H(shared)`). The session-key derivation here is the KDF/RO step of
  Thm 11.5 Game-2 (replace `k` by uniform when `shared` is unpredictable); our `deriveK` injective
  involution is the entropy-preserving `H`. The CDH/RO-guessing term of the literal §11.5 ladder is
  replaced by the (here uninstantiated) KEM IND-CPA assumption.
-/
import Demos.Extracted.Ke
import Demos.StreamCipher.ByteArray
import Demos.Crypto.OracleHybrid
import VCVio.CryptoFoundations.KeyEncapMech
import VCVio.OracleComp.SimSemantics.StateT.StateSeparating
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

open Aeneas Std Result

namespace Demo6Ake

/-- A 32-byte block: the native Aeneas array type. Reuses the `Fintype`/`SampleableType`/`DecidableEq`
instances proved in `StreamByteSecurity` (`Demos/StreamCipher/ByteArray.lean`). This is the common
type for public key, secret key, ciphertext, shared secret, and session key. -/
abbrev Block := Std.Array Std.U8 32#usize

/-! ## Value adequacy of the extracted loops (the trusted bridge to Rust). -/

/-- The `keygen` loop computes `pk[i] = seed[i]`, `sk[i] = seed[i] ^ 0xFF`. -/
theorem keygen_loop_spec (seed : Block) :
    ∀ (pk sk : Block) (i : Std.Usize),
      i.val ≤ 32 →
      (∀ j, j < i.val → pk.val[j]! = seed.val[j]!) →
      (∀ j, j < i.val → sk.val[j]! = seed.val[j]! ^^^ 255#u8) →
      ke.keygen_loop seed pk sk i
        ⦃ r => (∀ j, j < 32 → r.1.val[j]! = seed.val[j]!) ∧
               (∀ j, j < 32 → r.2.val[j]! = seed.val[j]! ^^^ 255#u8) ⦄ := by
  intro pk sk i hi hpk hsk
  unfold ke.keygen_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : Block × Block × Std.Usize => 32 - s.2.2.val)
    (inv := fun s : Block × Block × Std.Usize => s.2.2.val ≤ 32 ∧
      (∀ j, j < s.2.2.val → s.1.val[j]! = seed.val[j]!) ∧
      (∀ j, j < s.2.2.val → s.2.1.val[j]! = seed.val[j]! ^^^ 255#u8))
    (post := fun r : Block × Block =>
      (∀ j, j < 32 → r.1.val[j]! = seed.val[j]!) ∧
      (∀ j, j < 32 → r.2.val[j]! = seed.val[j]! ^^^ 255#u8))
  · rintro ⟨pk1, sk1, i1⟩ ⟨hi1, hpk1, hsk1⟩
    simp only [ke.keygen_loop.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨a, ha⟩
      step as ⟨v2, hv2⟩
      step as ⟨a1, ha1⟩
      step as ⟨i3, hi3⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · scalar_tac
      · intro j hj
        subst ha ha1
        by_cases hje : j = i1.val
        · subst hje; simp_lists [hv1]
        · have : j < i1.val := by scalar_tac
          simp_lists
          exact hpk1 j this
      · intro j hj
        subst ha ha1
        by_cases hje : j = i1.val
        · subst hje; simp_lists [hv1, hv2]; scalar_tac
        · have : j < i1.val := by scalar_tac
          simp_lists
          exact hsk1 j this
      · scalar_tac
    · rename_i hge
      refine ⟨?_, ?_⟩
      · intro j hj; apply hpk1; scalar_tac
      · intro j hj; apply hsk1; scalar_tac
  · exact ⟨hi, hpk, hsk⟩

/-- **Value adequacy** of `keygen`. -/
theorem keygen_spec (seed : Block) :
    ke.keygen seed
      ⦃ r => (∀ j, j < 32 → r.1.val[j]! = seed.val[j]!) ∧
             (∀ j, j < 32 → r.2.val[j]! = seed.val[j]! ^^^ 255#u8) ⦄ := by
  unfold ke.keygen
  apply keygen_loop_spec
  · scalar_tac
  · intro j hj; scalar_tac
  · intro j hj; scalar_tac

/-- The `encaps` loop computes the pointwise `ct = pk ^ coins`, `shared = pk & coins`. -/
theorem encaps_loop_spec (pk coins : Block) :
    ∀ (ct shared : Block) (i : Std.Usize),
      i.val ≤ 32 →
      (∀ j, j < i.val → ct.val[j]! = pk.val[j]! ^^^ coins.val[j]!) →
      (∀ j, j < i.val → shared.val[j]! = pk.val[j]! &&& coins.val[j]!) →
      ke.encaps_loop pk coins ct shared i
        ⦃ r => (∀ j, j < 32 → r.1.val[j]! = pk.val[j]! ^^^ coins.val[j]!) ∧
               (∀ j, j < 32 → r.2.val[j]! = pk.val[j]! &&& coins.val[j]!) ⦄ := by
  intro ct shared i hi hct hsh
  unfold ke.encaps_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : Block × Block × Std.Usize => 32 - s.2.2.val)
    (inv := fun s : Block × Block × Std.Usize => s.2.2.val ≤ 32 ∧
      (∀ j, j < s.2.2.val → s.1.val[j]! = pk.val[j]! ^^^ coins.val[j]!) ∧
      (∀ j, j < s.2.2.val → s.2.1.val[j]! = pk.val[j]! &&& coins.val[j]!))
    (post := fun r : Block × Block =>
      (∀ j, j < 32 → r.1.val[j]! = pk.val[j]! ^^^ coins.val[j]!) ∧
      (∀ j, j < 32 → r.2.val[j]! = pk.val[j]! &&& coins.val[j]!))
  · rintro ⟨ct1, shared1, i1⟩ ⟨hi1, hct1, hsh1⟩
    simp only [ke.encaps_loop.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨v2, hv2⟩
      step as ⟨v3, hv3⟩
      step as ⟨a, ha⟩
      step as ⟨v4, hv4⟩
      step as ⟨a1, ha1⟩
      step as ⟨i5, hi5⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · scalar_tac
      · intro j hj
        subst ha ha1
        by_cases hje : j = i1.val
        · subst hje; simp_lists [hv1, hv2, hv3]; scalar_tac
        · have : j < i1.val := by scalar_tac
          simp_lists
          exact hct1 j this
      · intro j hj
        subst ha ha1
        by_cases hje : j = i1.val
        · subst hje; simp_lists
          have hv4' : v4 = v1 &&& v2 := by rw [U8.eq_equiv_bv_eq, UScalar.bv_and]; assumption
          rw [hv4', hv1, hv2]
        · have : j < i1.val := by scalar_tac
          simp_lists
          exact hsh1 j this
      · scalar_tac
    · rename_i hge
      refine ⟨?_, ?_⟩
      · intro j hj; apply hct1; scalar_tac
      · intro j hj; apply hsh1; scalar_tac
  · exact ⟨hi, hct, hsh⟩

/-- **Value adequacy** of `encaps`: it computes `ct = pk ^ coins`, `shared = pk & coins`. -/
theorem encaps_spec (pk coins : Block) :
    ke.encaps pk coins
      ⦃ r => (∀ j, j < 32 → r.1.val[j]! = pk.val[j]! ^^^ coins.val[j]!) ∧
             (∀ j, j < 32 → r.2.val[j]! = pk.val[j]! &&& coins.val[j]!) ⦄ := by
  unfold ke.encaps
  apply encaps_loop_spec
  · scalar_tac
  · intro j hj; scalar_tac
  · intro j hj; scalar_tac

/-- The `decaps` loop computes `shared[i] = (sk[i] ^ 0xFF) & (ct[i] ^ (sk[i] ^ 0xFF))`. -/
theorem decaps_loop_spec (sk ct : Block) :
    ∀ (shared : Block) (i : Std.Usize),
      i.val ≤ 32 →
      (∀ j, j < i.val → shared.val[j]! =
        (sk.val[j]! ^^^ 255#u8) &&& (ct.val[j]! ^^^ (sk.val[j]! ^^^ 255#u8))) →
      ke.decaps_loop sk ct shared i
        ⦃ r => ∀ j, j < 32 → r.val[j]! =
          (sk.val[j]! ^^^ 255#u8) &&& (ct.val[j]! ^^^ (sk.val[j]! ^^^ 255#u8)) ⦄ := by
  intro shared i hi hsh
  unfold ke.decaps_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : Block × Std.Usize => 32 - s.2.val)
    (inv := fun s : Block × Std.Usize => s.2.val ≤ 32 ∧
      ∀ j, j < s.2.val → s.1.val[j]! =
        (sk.val[j]! ^^^ 255#u8) &&& (ct.val[j]! ^^^ (sk.val[j]! ^^^ 255#u8)))
    (post := fun r : Block =>
      ∀ j, j < 32 → r.val[j]! =
        (sk.val[j]! ^^^ 255#u8) &&& (ct.val[j]! ^^^ (sk.val[j]! ^^^ 255#u8)))
  · rintro ⟨shared1, i1⟩ ⟨hi1, hsh1⟩
    simp only [ke.decaps_loop.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨pk_i, hpk⟩
      step as ⟨v2, hv2⟩
      step as ⟨coins_i, hco⟩
      step as ⟨v3, hv3⟩
      step as ⟨a, ha⟩
      step as ⟨i4, hi4⟩
      refine ⟨?_, ?_, ?_⟩
      · scalar_tac
      · intro j hj
        subst ha
        by_cases hje : j = i1.val
        · subst hje; simp_lists
          have hpk' : pk_i = v1 ^^^ 255#u8 := by rw [U8.eq_equiv_bv_eq, UScalar.bv_xor]; assumption
          have hco' : coins_i = v2 ^^^ pk_i := by rw [U8.eq_equiv_bv_eq, UScalar.bv_xor]; assumption
          have hv3' : v3 = pk_i &&& coins_i := by rw [U8.eq_equiv_bv_eq, UScalar.bv_and]; assumption
          rw [hv3', hco', hpk', hv1, hv2]
        · have : j < i1.val := by scalar_tac
          simp_lists
          exact hsh1 j this
      · scalar_tac
    · rename_i hge
      intro j hj; apply hsh1; scalar_tac
  · exact ⟨hi, hsh⟩

/-- **Value adequacy** of `decaps`. -/
theorem decaps_spec (sk ct : Block) :
    ke.decaps sk ct
      ⦃ r => ∀ j, j < 32 → r.val[j]! =
        (sk.val[j]! ^^^ 255#u8) &&& (ct.val[j]! ^^^ (sk.val[j]! ^^^ 255#u8)) ⦄ := by
  unfold ke.decaps
  apply decaps_loop_spec
  · scalar_tac
  · intro j hj; scalar_tac

/-- The `derive_session_key` loop computes the pointwise `out[i] = shared[i] ^ 0x5C`. -/
theorem derive_loop_spec (shared : Block) :
    ∀ (out : Block) (i : Std.Usize),
      i.val ≤ 32 →
      (∀ j, j < i.val → out.val[j]! = shared.val[j]! ^^^ 92#u8) →
      ke.derive_session_key_loop shared out i
        ⦃ r => ∀ j, j < 32 → r.val[j]! = shared.val[j]! ^^^ 92#u8 ⦄ := by
  intro out i hi hout
  unfold ke.derive_session_key_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : Block × Std.Usize => 32 - s.2.val)
    (inv := fun s : Block × Std.Usize => s.2.val ≤ 32 ∧
      ∀ j, j < s.2.val → s.1.val[j]! = shared.val[j]! ^^^ 92#u8)
    (post := fun r : Block =>
      ∀ j, j < 32 → r.val[j]! = shared.val[j]! ^^^ 92#u8)
  · rintro ⟨out1, i1⟩ ⟨hi1, hout1⟩
    simp only [ke.derive_session_key_loop.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨v2, hv2⟩
      step as ⟨a, ha⟩
      step as ⟨i3, hi3⟩
      refine ⟨?_, ?_, ?_⟩
      · scalar_tac
      · intro j hj
        subst ha
        by_cases hje : j = i1.val
        · subst hje; simp_lists [hv1, hv2]; scalar_tac
        · have : j < i1.val := by scalar_tac
          simp_lists
          exact hout1 j this
      · scalar_tac
    · rename_i hge
      intro j hj; apply hout1; scalar_tac
  · exact ⟨hi, hout⟩

/-- **Value adequacy** of `derive_session_key`: pointwise XOR with `0x5C`. -/
theorem derive_spec (shared : Block) :
    ke.derive_session_key shared
      ⦃ r => ∀ j, j < 32 → r.val[j]! = shared.val[j]! ^^^ 92#u8 ⦄ := by
  unfold ke.derive_session_key
  apply derive_loop_spec
  · scalar_tac
  · intro j hj; scalar_tac

/-! ## Total wrappers (the extracted ops are total, so the non-`ok` branch is unreachable). -/

instance : Inhabited Block := ⟨Std.Array.repeat 32#usize 0#u8⟩

/-- Total `keygen`: deterministic core `pk[i] = seed[i]`, `sk[i] = seed[i] ^ 0xFF`. -/
def keygenK (seed : Block) : Block × Block :=
  match ke.keygen seed with
  | .ok r => r
  | _ => default

/-- Total `encaps`: `ct[i] = pk[i] ^ coins[i]`, `shared[i] = pk[i] & coins[i]`. -/
def encapsK (pk coins : Block) : Block × Block :=
  match ke.encaps pk coins with
  | .ok r => r
  | _ => default

/-- Total `decaps`: recompute `pk[i] = sk[i] ^ 0xFF`, `coins[i] = ct[i] ^ pk[i]`, `shared = pk & coins`. -/
def decapsK (sk ct : Block) : Block :=
  match ke.decaps sk ct with
  | .ok r => r
  | _ => default

/-- Total session-key derivation: `out[i] = shared[i] ^ 0x5C`. -/
def deriveK (shared : Block) : Block :=
  match ke.derive_session_key shared with
  | .ok r => r
  | _ => default

/-! ### Block-level pointwise equations for the total wrappers. -/

theorem encapsK_ct_spec (pk coins : Block) (j : ℕ) (hj : j < 32) :
    (encapsK pk coins).1.val[j]! = pk.val[j]! ^^^ coins.val[j]! := by
  obtain ⟨r, hr, hpost⟩ := WP.spec_imp_exists (encaps_spec pk coins)
  simp only [encapsK, hr]
  exact hpost.1 j hj

theorem encapsK_key_spec (pk coins : Block) (j : ℕ) (hj : j < 32) :
    (encapsK pk coins).2.val[j]! = pk.val[j]! &&& coins.val[j]! := by
  obtain ⟨r, hr, hpost⟩ := WP.spec_imp_exists (encaps_spec pk coins)
  simp only [encapsK, hr]
  exact hpost.2 j hj

theorem decapsK_spec (sk ct : Block) (j : ℕ) (hj : j < 32) :
    (decapsK sk ct).val[j]! =
      (sk.val[j]! ^^^ 255#u8) &&& (ct.val[j]! ^^^ (sk.val[j]! ^^^ 255#u8)) := by
  obtain ⟨r, hr, hpost⟩ := WP.spec_imp_exists (decaps_spec sk ct)
  simp only [decapsK, hr]
  exact hpost j hj

theorem deriveK_spec (shared : Block) (j : ℕ) (hj : j < 32) :
    (deriveK shared).val[j]! = shared.val[j]! ^^^ 92#u8 := by
  obtain ⟨r, hr, hpost⟩ := WP.spec_imp_exists (derive_spec shared)
  simp only [deriveK, hr]
  exact hpost j hj

theorem keygenK_pk_spec (seed : Block) (j : ℕ) (hj : j < 32) :
    (keygenK seed).1.val[j]! = seed.val[j]! := by
  obtain ⟨r, hr, hpost⟩ := WP.spec_imp_exists (keygen_spec seed)
  simp only [keygenK, hr]
  exact hpost.1 j hj

theorem keygenK_sk_spec (seed : Block) (j : ℕ) (hj : j < 32) :
    (keygenK seed).2.val[j]! = seed.val[j]! ^^^ 255#u8 := by
  obtain ⟨r, hr, hpost⟩ := WP.spec_imp_exists (keygen_spec seed)
  simp only [keygenK, hr]
  exact hpost.2 j hj

/-! ## Headline 1 — decaps ∘ encaps correctness on a keypair. -/

/-- **Functional KEM correctness.** On a keypair `(pk, sk) = keygenK seed`, decapsulating the
ciphertext recovers the shared secret produced by `encaps`. The key algebraic facts:
`sk[i] = seed[i] ^ 0xFF = pk[i] ^ 0xFF`, so decaps recomputes `pk_i = sk[i] ^ 0xFF = pk[i]`, then
`coins_i = ct[i] ^ pk_i = (pk[i] ^ coins[i]) ^ pk[i] = coins[i]`, hence
`shared_i = pk_i & coins_i = pk[i] & coins[i]` — exactly the `encaps` shared secret. -/
theorem decapsK_encapsK_correct (seed coins : Block) :
    decapsK (keygenK seed).2 (encapsK (keygenK seed).1 coins).1
      = (encapsK (keygenK seed).1 coins).2 := by
  apply Subtype.ext
  apply List.ext_getElem!
  · simp only [Array.length_eq]
  · intro n
    by_cases hn : n < 32
    · rw [decapsK_spec _ _ n hn, encapsK_key_spec _ _ n hn]
      rw [keygenK_sk_spec seed n hn, encapsK_ct_spec _ _ n hn, keygenK_pk_spec seed n hn]
      -- goal: (seed[n] ^ 0xFF ^ 0xFF) & ((seed[n] ^ coins[n]) ^ (seed[n] ^ 0xFF ^ 0xFF))
      --        = seed[n] & coins[n]
      rw [StreamByteSecurity.u8_xor_cancel]
      -- goal: seed[n] & ((seed[n] ^ coins[n]) ^ seed[n]) = seed[n] & coins[n]
      congr 1
      rw [U8.eq_equiv_bv_eq]
      simp only [UScalar.bv_xor]
      -- (s ^^^ c) ^^^ s = c
      rw [BitVec.xor_comm, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · rw [getElem!_neg, getElem!_neg] <;> (simp only [Array.length_eq]; scalar_tac)

/-! ## Headline 2 — the session-key derivation is a bijection (the non-degeneracy witness). -/

/-- `deriveK` is an involution: applying the XOR-with-`0x5C` transform twice is the identity. -/
theorem deriveK_deriveK (shared : Block) : deriveK (deriveK shared) = shared := by
  apply Subtype.ext
  apply List.ext_getElem!
  · simp only [Array.length_eq]
  · intro n
    by_cases hn : n < 32
    · rw [deriveK_spec (deriveK shared) n hn, deriveK_spec shared n hn]
      exact StreamByteSecurity.u8_xor_cancel _ _
    · rw [getElem!_neg, getElem!_neg] <;> (simp only [Array.length_eq]; scalar_tac)

/-- **Non-degeneracy witness.** The session-key derivation `H` is a permutation of the key space
(an involution `Block ≃ Block`). This is the structural fix over Demo-6 v1, whose `k_i XOR k_r`
combiner collapsed the session key to a constant: a bijection is neither constant nor
entropy-collapsing, so `H(shared)` carries exactly the entropy of `shared`. -/
def deriveEquiv : Block ≃ Block where
  toFun := deriveK
  invFun := deriveK
  left_inv := deriveK_deriveK
  right_inv := deriveK_deriveK

/-- **Injectivity of the session-key derivation** (distinct shared secrets give distinct session
keys). Follows from `deriveEquiv` being a bijection. -/
theorem deriveK_injective : Function.Injective deriveK :=
  deriveEquiv.injective

/-! ## The functional KEM (the reduction target)

`kemKe` packages the extracted `keygen`/`encaps`/`decaps` as a `KEMScheme` over `unifSpec`.
Randomness lives on the Lean side (the `seed` for `keygen`, the `coins` for `encaps`), matching
the `ke.rs` documentation that these are caller-supplied. `decaps` is *total* (the extracted loop
never fails), so it always returns `some`. This is the FUNCTIONAL KEM: its correctness is a theorem
(`kemKe_correct`), but — as the module docstring explains at length — its bytes do NOT satisfy
IND-CPA (the shared secret leaks from `(pk, ct)`). The IND-CPA notion below is therefore used only
as the *reduction target* for an unconditional equality, never instantiated with a smallness bound. -/

open OracleSpec OracleComp ENNReal

/-- `Block` has decidable equality (it is `List.Vector U8 32`). -/
instance : DecidableEq Block :=
  inferInstanceAs (DecidableEq (List.Vector Std.U8 32))

/-- Uniform sampling is invariant under any permutation at the level of the *whole* output
distribution (not just the `true`-output probability). The `evalDist` strengthening of
`StreamByteSecurity.uniform_perm_invariant`, used here to swap `deriveK kRand` for `kRand` inside
the random branch of the KI game. (A local copy of the lemma proved in `Demos/KemDem/Composition`.) -/
theorem evalDist_uniform_perm_invariant {R β : Type} [SampleableType R] [Fintype R]
    (A : R → ProbComp β) (e : R ≃ R) :
    𝒟[(do let r ← $ᵗ R; A r)] = 𝒟[(do let r ← $ᵗ R; A (e r))] := by
  refine evalDist_ext (fun x => ?_)
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  simp only [probOutput_uniformSample]
  exact (Equiv.tsum_eq e (fun r => (Fintype.card R : ℝ≥0∞)⁻¹ * Pr[= x | A r])).symm

/-- The functional KEM extracted from `ke.rs`: `keygen` samples a uniform seed and runs the
extracted key generator; `encaps` samples uniform coins and runs the extracted encapsulator;
`decaps` runs the (total) extracted decapsulator and wraps the result in `some`. -/
noncomputable def kemKe : KEMScheme (OracleComp unifSpec) Block Block Block Block where
  keygen := do let seed ← $ᵗ Block; pure (keygenK seed)
  encaps pk := do let coins ← $ᵗ Block; pure (encapsK pk coins)
  decaps sk c := pure (some (decapsK sk c))

/-! ## Headline 3 — functional KEM correctness. -/

/-- **KEM correctness.** The functional KEM is perfectly correct: decapsulation of an honest
encapsulation recovers the shared key with probability `1`. Reduces to the extracted-loop
correctness `decapsK_encapsK_correct` (decaps recomputes `pk` from `sk`, hence the shared secret).
The experiment is a `do`-block sampling a seed and coins; for *every* sample the inner Boolean is
`true` by `decapsK_encapsK_correct`, so the success probability is `1`. -/
theorem kemKe_correct :
    Pr[= true | kemKe.CorrectExp] = 1 := by
  -- Flatten the experiment: keygen/encaps are `sample; pure …`, decaps is `pure …`, so the body
  -- collapses to `do seed; coins; pure (decide (some (decapsK …) = some (encapsK …).2))`.
  simp only [KEMScheme.CorrectExp, kemKe, bind_assoc, pure_bind]
  -- By `decapsK_encapsK_correct` the inner `decide` is `true` for every `(seed, coins)` (rewrites
  -- under the binders), collapsing the body to `pure true`; then `Pr[= true | …] = 1`.
  simp only [decapsK_encapsK_correct, decide_true]
  simp

/-! ## The single-session key-indistinguishability (KI) game

A KI distinguisher is a two-phase adversary against the *session key*: given the public key it
produces a state, then — given the challenge ciphertext and a candidate session key — outputs a
guess. The KI game samples a keypair, encapsulates, and challenges the distinguisher with either
the REAL session key `deriveK shared` (when `b = true`) or a UNIFORM session key `$ᵗ Block` (when
`b = false`), returning whether the guess matched `b`. This is a genuine real-or-random test on the
session key (not the raw shared secret). -/

/-- A two-phase KI distinguisher: `preChallenge pk` produces a state; `postChallenge st cStar k`
sees the challenge ciphertext and a candidate *session key* `k : Block` and returns a guess. -/
structure KI_Adversary where
  /-- Adversary state passed from the pre- to the post-challenge phase. -/
  State : Type
  /-- Pre-challenge phase: inspect the public key. -/
  preChallenge : Block → OracleComp unifSpec State
  /-- Post-challenge phase: given the challenge ciphertext and a candidate session key, guess. -/
  postChallenge : State → Block → Block → OracleComp unifSpec Bool

/-- The single-session KI game. Sample a keypair, hand the distinguisher the public key, encapsulate
to get `(cStar, shared)`, sample the challenge bit `b`, and challenge with the REAL session key
`deriveK shared` (if `b`) or a UNIFORM session key (if `¬b`); return whether the guess matched. -/
noncomputable def KI_Game (adv : KI_Adversary) : SPMF Bool :=
  ProbCompRuntime.probComp.evalDist do
    let (pk, _sk) ← kemKe.keygen
    let st ← adv.preChallenge pk
    let b ← $ᵗ Bool
    let (cStar, shared) ← kemKe.encaps pk
    let kRand ← $ᵗ Block
    let b' ← adv.postChallenge st cStar (if b then deriveK shared else kRand)
    return (b == b')

/-- **KI advantage.** The bias of the single-session KI game — the canonical real-or-random
distinguishing advantage on the session key. -/
noncomputable def KI_Advantage (adv : KI_Adversary) : ℝ :=
  (KI_Game adv).boolBiasAdvantage

/-! ## The reduction (the meaningful, non-vacuous bound)

Every KI distinguisher yields a KEM IND-CPA adversary by post-composing its `postChallenge` with
`deriveK`: where the IND-CPA game hands it the raw challenge key `kChallenge` (`shared` if `b`, a
uniform key if `¬b`), the reduction hands the KI distinguisher `deriveK kChallenge`. Because
`deriveK` is the bijection `deriveEquiv`, applying it to a uniform key yields a uniform key
(permutation-invariance), so the two games coincide *branch for branch* and the advantages are
EQUAL — a reduction with zero slack. -/

/-- The KEM IND-CPA adversary built from a KI distinguisher by post-composing `deriveK` onto the
challenge key handed to the distinguisher. -/
def kiToKemAdversary (adv : KI_Adversary) : kemKe.IND_CPA_Adversary where
  State := adv.State
  preChallenge pk := adv.preChallenge pk
  postChallenge st cStar k := adv.postChallenge st cStar (deriveK k)

/-- **Headline 4 — the meaningful bound (an equality).** The single-session KI advantage of any
distinguisher *equals* the KEM IND-CPA advantage of its reduction `kiToKemAdversary`. This is the
reduction with zero slack: KI of the session key `deriveK shared` tracks IND-CPA of the raw shared
secret exactly, because `deriveK` is the registered bijection `deriveEquiv` (real branch: literal
post-composition; random branch: `deriveK` of a uniform key is uniform, by permutation invariance).

Honest scope (see module docstring): for *this* `kemKe` the right-hand `IND_CPA_Advantage` is large
(the shared secret leaks from `(pk, ct)`), so the bound does not certify byte-level security — its
value is the composition capability, a protocol-shaped KI game over extracted Rust reduced to a
primitive game. The reduction is an unconditional equality and consumes no unsatisfiable premise. -/
theorem ki_advantage_eq_kem_ind_cpa (adv : KI_Adversary) :
    KI_Advantage adv =
      kemKe.IND_CPA_Advantage ProbCompRuntime.probComp (kiToKemAdversary adv) := by
  rw [KEMScheme.IND_CPA_Advantage_eq_game_bias]
  unfold KI_Advantage
  -- It suffices that the two games (as SPMFs) are equal.
  suffices hgame : KI_Game adv
      = kemKe.IND_CPA_Game ProbCompRuntime.probComp (kiToKemAdversary adv) by rw [hgame]
  -- For `probComp`, `evalDist mx = 𝒟[mx]` and `liftProbComp` is the identity (both `rfl`), so both
  -- games are `𝒟[·]` of a `ProbComp` do-block. The only difference is the challenge key handed to
  -- `postChallenge`: KI passes `if b then deriveK shared else kRand`; the reduction passes
  -- `deriveK (if b then shared else kRand)`. Peel the common prefix and branch on `b`.
  unfold KI_Game KEMScheme.IND_CPA_Game kiToKemAdversary
  show ProbCompRuntime.probComp.evalDist _ = ProbCompRuntime.probComp.evalDist _
  have hev : ∀ (mx : ProbComp Bool), ProbCompRuntime.probComp.evalDist mx = 𝒟[mx] :=
    fun mx => rfl
  have hlift : ∀ {β : Type} (pc : ProbComp β),
      ProbCompRuntime.probComp.liftProbComp pc = pc := fun pc => rfl
  rw [hev, hev]
  simp only [hlift]
  refine evalDist_ext (fun x => ?_)
  -- Peel the shared prefix (keygen, preChallenge, b, encaps) via `probOutput_bind_congr'`.
  refine probOutput_bind_congr' _ x (fun seedPair => ?_)
  refine probOutput_bind_congr' _ x (fun st => ?_)
  refine probOutput_bind_congr' _ x (fun b => ?_)
  refine probOutput_bind_congr' _ x (fun coinsPair => ?_)
  -- Now only the inner `kRand` sample and the postChallenge call remain; branch on b.
  cases b with
  | true =>
    -- Real branch: both pass `deriveK shared` (KEM's `if true` selects `kReal = shared`).
    simp only [if_true]
  | false =>
    -- Random branch: KI passes uniform `kRand`; KEM passes `deriveK kRand`.
    simp only [Bool.false_eq_true, if_false]
    -- `do kRand ← $ᵗ Block; A kRand` vs `do kRand ← $ᵗ Block; A (deriveK kRand)` at `deriveEquiv`.
    exact evalDist_ext_iff.mp
      (evalDist_uniform_perm_invariant
        (fun kRand => do let b' ← adv.postChallenge st coinsPair.1 kRand; pure (false == b'))
        deriveEquiv) x

/-- **The assumption-discharge form of the single-session bound.** This is the shape the eventual
real proof takes: *assuming* a smallness bound `ε` on the KEM's IND-CPA advantage (against the
reduction adversary `kiToKemAdversary adv` — exactly as the real proof assumes ML-KEM IND-CCA), the
session-key KI advantage is `≤ ε`. Derived from the exact equality `ki_advantage_eq_kem_ind_cpa` by
rewriting. The premise is a genuine, satisfiable hypothesis on the *derived* adversary's advantage
(not a constant), so this is the honest "the assumption plugs in here" statement — NOT a vacuous
bound consuming an unsatisfiable premise.

Honest scope (see module docstring): for *this* synthetic `kemKe` the IND-CPA advantage is large
(the shared secret leaks from `(pk, ct)`), so the hypothesis is only satisfiable with a large `ε` —
the value is the COMPOSITION CAPABILITY (a protocol KI game over extracted Rust reduced to a
primitive game), not a small bound on this byte core. The reduction itself is unconditional and
zero-slack; only the final smallness input is the (here-uninstantiated) KEM assumption. -/
theorem ki_advantage_le_of_kem_ind_cpa_le (adv : KI_Adversary) (ε : ℝ)
    (hKem : kemKe.IND_CPA_Advantage ProbCompRuntime.probComp (kiToKemAdversary adv) ≤ ε) :
    KI_Advantage adv ≤ ε :=
  (ki_advantage_eq_kem_ind_cpa adv).trans_le hKem

/-! ## The multi-session KI game (protocol-shaped, with a mutable session table)

This is the genuinely protocol-shaped game: a distinguisher drives the responder through an
oracle interface `akeSpec` with three queries — `Send` (open a fresh session: sample coins,
encapsulate to the long-term public key, store the derived session key in a mutable session
table), `Reveal` (corrupt a session: mark it revealed and hand back its real session key), and
`Test` (real-or-random challenge on a *fresh* session key). A single secret challenge bit `b`
governs every `Test`: if `b` is true the Test returns the REAL session key `deriveK shared`,
otherwise a freshly sampled UNIFORM key. The game returns whether the distinguisher's final guess
matches `b`.

The state `GameState` carries the secret bit and a growing `List Session` table that `Send`
*appends to* and that `Reveal`/`Test` *read and mutate* (marking sessions revealed/tested) — a
real, non-trivial table mutation. The freshness predicate `Session.fresh` inspects each session's
`revealed`/`tested` flags, so it is NON-CONSTANT: a session that has been `Reveal`ed (or already
`Test`ed) is no longer fresh, and `Test` on a non-fresh session returns a fixed default rather than
a challenge. This rules out the trivial "Reveal then Test the same session" win and is the multi-
session analogue of the AKE freshness condition (Boneh-Shoup §21 / the standard SK-security game).

The session key stored by `Send` is `H(shared) = deriveK shared` — the SINGLE-shared-secret KDF
output, the anti-v1 construction. We prove `realSessionKey_not_constant` below: the stored session
key genuinely depends on the coins (two coin vectors give two different session keys for a fixed
pk), so the real branch is NOT a constant (the v1 failure was exactly a constant real key).

NB (honest scope, see the module docstring): we register NO security bound for this multi-session
game in this round — only that it *elaborates*, is axiom-clean, and is non-degenerate. The bound
(reducing each session's Test to the assumed KEM IND-CPA via the `OracleHybrid` Q-query telescoping)
is the next refinement round. The KEM IND-CPA assumption remains intentionally uninstantiated for
this synthetic byte core. -/

/-- A single protocol session: the challenge ciphertext sent, the derived session key
`H(shared)`, and two flags — `revealed` (the session key was handed out via `Reveal`) and
`tested` (the session was already used as a `Test` challenge). The flags drive freshness. -/
structure Session where
  /-- The challenge ciphertext produced by `Send` (encaps output). -/
  cStar : Block
  /-- The derived session key `deriveK shared` for this session. -/
  key : Block
  /-- Whether this session's key has been revealed to the distinguisher. -/
  revealed : Bool
  /-- Whether this session has already served as a `Test` challenge. -/
  tested : Bool
  deriving Inhabited

/-- A session is FRESH (eligible for a real-or-random `Test`) iff its key has not been revealed
and it has not already been tested. NON-CONSTANT: it depends on the mutable flags, so a
`Reveal`ed or already-`Test`ed session is not fresh. -/
def Session.fresh (s : Session) : Bool := !s.revealed && !s.tested

/-- The mutable game state: the secret challenge bit and the session table. `Send` appends,
`Reveal`/`Test` read and mutate. -/
structure GameState where
  /-- The hidden challenge bit governing every `Test` (real vs random). -/
  b : Bool
  /-- The session table: index `i` is the `i`-th opened session. -/
  sessions : List Session
  deriving Inhabited

/-- The protocol oracle interface the distinguisher drives. `Send` opens a session (no argument);
`Reveal i` and `Test i` act on session index `i`. -/
inductive AkeQuery where
  /-- Open a fresh session: encapsulate and store the derived session key. -/
  | send : AkeQuery
  /-- Reveal session `i`'s key (corrupting it; it is no longer fresh). -/
  | reveal : ℕ → AkeQuery
  /-- Real-or-random challenge on a fresh session `i`'s key. -/
  | test : ℕ → AkeQuery
  deriving DecidableEq

/-- Each query returns a `Block`: `Send` returns the challenge ciphertext `cStar`; `Reveal`
returns the revealed session key; `Test` returns the real or random session key (or a default
on a non-fresh / out-of-range session). -/
@[reducible] def akeSpec : OracleSpec.{0, 0} AkeQuery := fun _ => Block

/-- Replace session `i` in the table by `f`-image (no-op if `i` is out of range). -/
def GameState.updateSession (gs : GameState) (i : ℕ) (f : Session → Session) : GameState :=
  { gs with sessions := gs.sessions.set i (f (gs.sessions.getD i default)) }

/-- The stateful handler for `akeSpec` over `GameState`, with `ProbComp` as the base monad
(so it can sample coins for `Send` and a uniform key for the random `Test` branch). The
long-term responder public key `pk` is a parameter (sampled once by the game). -/
def akeImpl (pk : Block) :
    QueryImpl.Stateful unifSpec akeSpec GameState
  | .send => StateT.mk fun gs => do
      let coins ← ($ᵗ Block : OracleComp unifSpec Block)
      let cs := encapsK pk coins
      let sk := deriveK cs.2
      let newSession : Session := { cStar := cs.1, key := sk, revealed := false, tested := false }
      pure (cs.1, { gs with sessions := gs.sessions ++ [newSession] })
  | .reveal i => StateT.mk fun gs =>
      let s := gs.sessions.getD i default
      pure (s.key, gs.updateSession i (fun s => { s with revealed := true }))
  | .test i => StateT.mk fun gs => do
      let s := gs.sessions.getD i default
      let kRand ← ($ᵗ Block : OracleComp unifSpec Block)
      -- Non-constant freshness: only a fresh session yields a challenge; otherwise a fixed default.
      if s.fresh then
        let challenge := if gs.b then s.key else kRand
        pure (challenge, gs.updateSession i (fun s => { s with tested := true }))
      else
        pure (default, gs)

/-- A multi-session KI distinguisher: drives the `akeSpec` oracle interface and outputs a guess
at the hidden challenge bit. -/
def AkeAdversary : Type := OracleComp akeSpec Bool

/-- The multi-session KI game. Sample the long-term keypair and the secret challenge bit `b`,
run the distinguisher against the `akeImpl pk` handler from the initial (empty-table) state, and
return whether its guess matched `b`. The final state is discarded (`run'`). -/
noncomputable def akeGame (adv : AkeAdversary) : ProbComp Bool := do
  let seed ← ($ᵗ Block : OracleComp unifSpec Block)
  let (pk, _sk) := keygenK seed
  let b ← ($ᵗ Bool : OracleComp unifSpec Bool)
  let b' ← (akeImpl pk).run { b := b, sessions := [] } adv
  return (b == b')

/-- **Multi-session KI advantage.** The bias of the multi-session game — the protocol-shaped
real-or-random distinguishing advantage on session keys, over a mutable session table with a
non-constant freshness condition. (No bound is registered this round; see the docstring.) -/
noncomputable def akeAdvantage (adv : AkeAdversary) : ℝ :=
  (akeGame adv).boolBiasAdvantage

/-! ## Non-degeneracy of the multi-session game (the anti-v1 check)

The real session key stored by `Send` is `deriveK shared` with `shared = pk & coins` — it is NOT
a constant. We exhibit, for a fixed public key, two coin vectors whose stored session keys differ,
witnessing that the real branch genuinely carries the coins' variation (unlike v1, whose
`k_i XOR k_r` collapsed to a constant). -/

/-- The session key `Send` stores for public key `pk` and coins `c`: `H(pk & c)`. -/
def realSessionKey (pk coins : Block) : Block := deriveK (encapsK pk coins).2

/-- **Non-degeneracy witness for the multi-session game.** The real session key is not constant:
there exist two coin vectors giving different stored session keys for the all-ones public key.
Concretely with `pk = 0xFF…FF`, `shared = pk & coins = coins`, so `realSessionKey 0xFF c = H(c)`,
and `H` is injective (`deriveK_injective`), so distinct coins give distinct keys. This is the
precise anti-v1 fact: the real branch depends on the coins, it is not a fixed value. -/
theorem realSessionKey_not_constant :
    ∃ pk c₁ c₂ : Block, realSessionKey pk c₁ ≠ realSessionKey pk c₂ := by
  -- pk = all-ones, c₁ = all-zeros, c₂ = all-ones. shared = pk & c, so shared₁ = 0, shared₂ = pk.
  refine ⟨Std.Array.repeat 32#usize 255#u8,
          Std.Array.repeat 32#usize 0#u8,
          Std.Array.repeat 32#usize 255#u8, ?_⟩
  intro hcontra
  -- deriveK injective ⇒ the two shared secrets are equal ⇒ contradiction at byte 0.
  have hsh : (encapsK (Std.Array.repeat 32#usize 255#u8) (Std.Array.repeat 32#usize 0#u8)).2
           = (encapsK (Std.Array.repeat 32#usize 255#u8) (Std.Array.repeat 32#usize 255#u8)).2 :=
    deriveK_injective hcontra
  -- read off byte 0: (255 & 0) = 0 ≠ 255 = (255 & 255)
  have h0 : (0 : ℕ) < 32 := by norm_num
  have e1 := encapsK_key_spec (Std.Array.repeat 32#usize 255#u8)
              (Std.Array.repeat 32#usize 0#u8) 0 h0
  have e2 := encapsK_key_spec (Std.Array.repeat 32#usize 255#u8)
              (Std.Array.repeat 32#usize 255#u8) 0 h0
  rw [hsh] at e1
  rw [e2] at e1
  -- e1 : (pk[0] & 255) = (pk[0] & 0), with pk[0] = 255
  simp only [Std.Array.repeat, Subtype.coe_mk] at e1
  -- both sides reduce to byte literals; 255 ≠ 0
  revert e1
  decide

/-! ## Headline 5 — the multi-session KI bound (the Q-query hybrid)

This is the multi-session reduction: the protocol-shaped KI advantage `akeAdvantage` is bounded by
the Q-fold telescoping hybrid sum of per-session real-vs-random `Test` swaps, for any distinguisher
issuing at most `Q` total oracle queries. This is the Boneh-Shoup §5.4 generic CPA multi-message
hybrid (the §5.5 `Q · primitive` shape), discharged through our reusable
`Demos.Crypto.OracleHybrid` (FCF `OracleHybrid.v`'s `G1_G2_close`).

The mechanism: the single secret bit `b` in `GameState` governs *every* `Test`, so the bias of
`akeGame` equals the boolean distinguishing advantage between the all-`Test`-REAL handler and the
all-`Test`-RANDOM handler (`boolBiasAdvantage_bind_uniformBool_eq_boolDistAdvantage`). We bit-factor
the handler into `akeStepImpl pk true` (every `Test` returns the real session key) and
`akeStepImpl pk false` (every `Test` returns a uniform key), with the `GameState` bit projected away
(`akeImpl_run_eq_akeStepImpl`, a state-projection identity). The generic hybrid then telescopes the
all-REAL-vs-all-RANDOM advantage into the sum, over `i < Q`, of single-`Test`-swap hops.

HONEST SCOPE (see module docstring): each per-hop term is a genuine single-session real-vs-random
`Test` swap — by the single-session structure (`ki_advantage_eq_kem_ind_cpa`) this is the assumed KEM
IND-CPA advantage; for *this* synthetic `kemKe` that advantage is large (the shared secret leaks from
`(pk, ct)`), so the bound certifies no byte-level security. Its value is the COMPOSITION CAPABILITY:
a protocol multi-session KI game over Aeneas-extracted Rust, reduced to the Q-fold hybrid of a
primitive game, machine-checked and axiom-clean. The long-term public key `pk` is a fixed parameter
(a fixed responder identity key, as in the standard AKE game). The bound is NOT vacuous: the per-hop
term is the caller's atomic obligation (the single-`Test` distinguishing advantage), never an axiom,
never a constant-vs-uniform trivially-won equality. -/

open Demos.Crypto.OracleHybrid

/-- The bit-free session table — the `GameState` with its hidden challenge bit projected away.
The bit becomes a *parameter* of the handler (`akeStepImpl pk bit`) so that the all-`Test`-real and
all-`Test`-random handlers are two distinct stateless step handlers the generic hybrid telescopes
between. -/
abbrev Table := List Session

/-- The bit-parameterized protocol handler: identical to `akeImpl` except the challenge bit `bit`
is a *parameter* (not read from state), and the state is the bare session `Table`. `akeStepImpl pk
true` answers every `Test` with the REAL session key; `akeStepImpl pk false` with a UNIFORM key.
`Send` appends to the table; `Reveal`/`Test` read and mutate it (same non-trivial mutation and
non-constant freshness as `akeImpl`). -/
def akeStepImpl (pk : Block) (bit : Bool) :
    QueryImpl.Stateful unifSpec akeSpec Table
  | .send => StateT.mk fun ss => do
      let coins ← ($ᵗ Block : OracleComp unifSpec Block)
      let cs := encapsK pk coins
      let sk := deriveK cs.2
      let newSession : Session := { cStar := cs.1, key := sk, revealed := false, tested := false }
      pure (cs.1, ss ++ [newSession])
  | .reveal i => StateT.mk fun ss =>
      let s := ss.getD i default
      pure (s.key, ss.set i { s with revealed := true })
  | .test i => StateT.mk fun ss => do
      let s := ss.getD i default
      let kRand ← ($ᵗ Block : OracleComp unifSpec Block)
      if s.fresh then
        let challenge := if bit then s.key else kRand
        pure (challenge, ss.set i { s with tested := true })
      else
        pure (default, ss)

/-- The fixed-`pk` multi-session game with the challenge bit `bit` *fixed* (not sampled): run the
distinguisher against `akeStepImpl pk bit` from the empty table, return its guess. `akeRun pk true`
is the all-`Test`-REAL run, `akeRun pk false` the all-`Test`-RANDOM run — the two endpoints the
hybrid telescopes between. -/
noncomputable def akeRun (pk : Block) (bit : Bool) (adv : AkeAdversary) : ProbComp Bool :=
  (akeStepImpl pk bit).run [] adv

/-- The fixed-`pk` multi-session KI game: sample the challenge bit, run the bit-parameterized
handler, return whether the guess matched. This is `akeGame` with the long-term public key fixed (a
fixed responder identity key) and the bit factored into the handler parameter. -/
noncomputable def akeGamePk (pk : Block) (adv : AkeAdversary) : ProbComp Bool := do
  let b ← ($ᵗ Bool : OracleComp unifSpec Bool)
  let b' ← akeRun pk b adv
  return (b == b')

/-- The fixed-`pk` multi-session KI advantage. -/
noncomputable def akeAdvantagePk (pk : Block) (adv : AkeAdversary) : ℝ :=
  (akeGamePk pk adv).boolBiasAdvantage

/-- **State projection.** Running `akeImpl pk` from a `GameState` with bit `b` and table `ss`
induces the same output distribution as running the bit-parameterized `akeStepImpl pk b` from the
bare table `ss`: the only role of the `GameState` bit is to select the `Test` branch, which the
parameter `b` selects identically; `GameState.updateSession` mirrors `List.set` and the bit is
preserved by every step, so the projection `gs ↦ gs.sessions` commutes with the simulation. -/
theorem akeImpl_run_eq_akeStepImpl (pk : Block) (b : Bool) (adv : AkeAdversary) (ss : Table) :
    (akeImpl pk).run { b := b, sessions := ss } adv = (akeStepImpl pk b).run ss adv := by
  refine OracleComp.run'_simulateQ_eq_of_query_map_eq_inv'
    (impl₁ := akeImpl pk) (impl₂ := akeStepImpl pk b)
    (inv := fun gs => gs.b = b) (proj := fun gs => gs.sessions) ?_ ?_ adv
    { b := b, sessions := ss } rfl
  · -- the bit `gs.b` is preserved by every handler step
    intro t s hs y hy
    cases t with
    | send =>
      simp only [akeImpl, StateT.run_mk, support_bind, Set.mem_iUnion] at hy
      obtain ⟨coins, _, hy⟩ := hy
      simp only [support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact hs
    | reveal i =>
      simp only [akeImpl, StateT.run_mk, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact hs
    | test i =>
      simp only [akeImpl, StateT.run_mk, support_bind, Set.mem_iUnion] at hy
      obtain ⟨kRand, _, hy⟩ := hy
      split at hy <;>
        (simp only [support_pure, Set.mem_singleton_iff] at hy; subst hy; exact hs)
  · -- under the invariant, the projection commutes with each step
    intro t s hs
    cases t with
    | send =>
      simp only [akeImpl, akeStepImpl, StateT.run_mk, map_bind]
      rfl
    | reveal i =>
      simp only [akeImpl, akeStepImpl, StateT.run_mk, map_pure, GameState.updateSession,
        Prod.map_apply, id_eq]
    | test i =>
      simp only [akeImpl, akeStepImpl, StateT.run_mk, map_bind, GameState.updateSession]
      refine bind_congr (fun kRand => ?_)
      simp only [hs]
      split <;> simp [Prod.map]

/-- The bit `b` in `akeImpl`'s initial state only selects the `Test` branch, so running the game
from `{ b := b, sessions := [] }` is the same `ProbComp` as `akeRun pk b`. -/
theorem akeImpl_run_empty_eq_akeRun (pk : Block) (b : Bool) (adv : AkeAdversary) :
    (akeImpl pk).run { b := b, sessions := [] } adv = akeRun pk b adv :=
  akeImpl_run_eq_akeStepImpl pk b adv []

/-- **The bias-to-distinguishing bridge.** The fixed-`pk` multi-session KI advantage equals the
boolean distinguishing advantage between the all-`Test`-REAL run and the all-`Test`-RANDOM run. This
is VCVio's `boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch`: the single sampled bit `b`
governs every `Test`, so the bias collapses to a real-vs-random distinguishing advantage. -/
theorem akeAdvantagePk_eq_boolDistAdvantage (pk : Block) (adv : AkeAdversary) :
    akeAdvantagePk pk adv = (akeRun pk true adv).boolDistAdvantage (akeRun pk false adv) := by
  unfold akeAdvantagePk akeGamePk
  rw [show (do
        let b ← ($ᵗ Bool : OracleComp unifSpec Bool)
        let b' ← akeRun pk b adv
        pure (b == b') : ProbComp Bool)
      = (do
        let b ← ($ᵗ Bool : OracleComp unifSpec Bool)
        let z ← if b then akeRun pk true adv else akeRun pk false adv
        pure (b == z)) from by
    refine bind_congr (fun b => ?_); cases b <;> rfl]
  exact ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch
    (akeRun pk true adv) (akeRun pk false adv)

/-- The all-`O1` counted endpoint of the hybrid equals the all-`Test`-REAL run (the dead counter is
projected away): `(ofCounted (akeStepImpl pk true)).runProb ([], 0)` has the same output
distribution as `akeRun pk true`. -/
theorem ofCounted_runProb_eq_akeRun (pk : Block) (bit : Bool) (adv : AkeAdversary) :
    𝒟[(ofCounted (akeStepImpl pk bit)).runProb ([], 0) adv] = 𝒟[akeRun pk bit adv] := by
  simp only [QueryImpl.Stateful.runProb_eq_run, QueryImpl.Stateful.run, akeRun]
  refine congrArg _ ?_
  refine OracleComp.run'_simulateQ_eq_of_query_map_eq
    (impl₁ := ofCounted (akeStepImpl pk bit)) (impl₂ := akeStepImpl pk bit)
    (proj := fun s => s.1) ?_ adv ([], 0)
  intro t s
  simp only [ofCounted_apply_run]
  rw [← Functor.map_map]
  simp

/-- **Headline 5 — the multi-session KI bound (the Q-query hybrid).** For any distinguisher issuing
at most `Q` total oracle queries against a fixed responder public key `pk`, the multi-session KI
advantage is bounded by the sum, over `i < Q`, of the single-`Test`-swap distinguishing advantages
between the depth-`i` and depth-`(i+1)` switching hybrids (real `Test`s for the first `i` queries,
random thereafter). This is the Boneh-Shoup §5.4 generic multi-message hybrid, discharged through the
reusable `advantage_le_sum_boolDistAdvantage_hybridStep` (FCF `OracleHybrid.v` `G1_G2_close`).

The per-hop term is the caller's atomic obligation — a single-session real-vs-random `Test` swap,
which by the single-session structure (`ki_advantage_eq_kem_ind_cpa`) is the assumed KEM IND-CPA
advantage. The bound is MEANINGFUL (not the v1 trivially-won equality): the per-hop term genuinely
isolates one session's Test, never an axiom. (Honest scope: the synthetic `kemKe`'s IND-CPA advantage
is large, so this certifies no byte-level security — the value is the composition capability.) -/
theorem akeAdvantagePk_le_sum_hybridStep (pk : Block) (adv : AkeAdversary)
    (Q : ℕ) (hQ : IsTotalQueryBound adv Q) :
    akeAdvantagePk pk adv ≤
      ∑ i ∈ Finset.range Q,
        ProbComp.boolDistAdvantage
          ((simulateQ (Oi (akeStepImpl pk true) (akeStepImpl pk false) i) adv).run' ([], 0))
          ((simulateQ (Oi (akeStepImpl pk true) (akeStepImpl pk false) (i + 1)) adv).run' ([], 0)) := by
  rw [akeAdvantagePk_eq_boolDistAdvantage]
  -- Bridge the two endpoints to the counted handlers, then apply the generic hybrid.
  have hbridge :
      (akeRun pk true adv).boolDistAdvantage (akeRun pk false adv) =
        (ofCounted (akeStepImpl pk true)).advantage ([], 0)
          (ofCounted (akeStepImpl pk false)) ([], 0) adv := by
    unfold QueryImpl.Stateful.advantage ProbComp.boolDistAdvantage
    rw [probOutput_congr rfl (ofCounted_runProb_eq_akeRun pk true adv),
        probOutput_congr rfl (ofCounted_runProb_eq_akeRun pk false adv)]
  rw [hbridge]
  exact advantage_le_sum_boolDistAdvantage_hybridStep
    (akeStepImpl pk true) (akeStepImpl pk false) [] adv Q hQ

/-- **The `Q · ε` assumption-discharge form of the multi-session bound** (Boneh-Shoup §5.5 — the
`Q · primitive` shape). If every single-`Test`-swap hop has distinguishing advantage at most `ε`
(the per-session real-vs-random obligation — by the single-session structure
`ki_advantage_eq_kem_ind_cpa` / `ki_advantage_le_of_kem_ind_cpa_le` this is the assumed KEM IND-CPA
advantage), then a distinguisher issuing at most `Q` queries has multi-session KI advantage at most
`Q • ε`. This is the standard multi-session collapse: `Q` sessions cost a factor `Q` over the
single-session assumption. Derived from the proved sum-bound `akeAdvantagePk_le_sum_hybridStep` by
uniformly bounding each summand (`advantage_le_nsmul_hybridStep`).

The per-hop hypothesis `hε` is a genuine, satisfiable premise on the adjacent switching-hybrid runs
(a real `boolDistAdvantage`, not a constant), so this is NOT a vacuous bound. Honest scope (module
docstring): for this synthetic `kemKe` the per-hop advantage is large, so `hε` only holds with a
large `ε` — the value is the composition capability, not a small bound on the byte core. -/
theorem akeAdvantagePk_le_nsmul (pk : Block) (adv : AkeAdversary)
    (Q : ℕ) (hQ : IsTotalQueryBound adv Q) (ε : ℝ)
    (hε : ∀ i ∈ Finset.range Q,
      ProbComp.boolDistAdvantage
        ((simulateQ (Oi (akeStepImpl pk true) (akeStepImpl pk false) i) adv).run' ([], 0))
        ((simulateQ (Oi (akeStepImpl pk true) (akeStepImpl pk false) (i + 1)) adv).run' ([], 0))
          ≤ ε) :
    akeAdvantagePk pk adv ≤ Q • ε := by
  rw [akeAdvantagePk_eq_boolDistAdvantage]
  have hbridge :
      (akeRun pk true adv).boolDistAdvantage (akeRun pk false adv) =
        (ofCounted (akeStepImpl pk true)).advantage ([], 0)
          (ofCounted (akeStepImpl pk false)) ([], 0) adv := by
    unfold QueryImpl.Stateful.advantage ProbComp.boolDistAdvantage
    rw [probOutput_congr rfl (ofCounted_runProb_eq_akeRun pk true adv),
        probOutput_congr rfl (ofCounted_runProb_eq_akeRun pk false adv)]
  rw [hbridge]
  refine advantage_le_nsmul_hybridStep
    (akeStepImpl pk true) (akeStepImpl pk false) [] adv Q hQ ε (fun i hi => ?_)
  rw [hybridStep_eq_boolDistAdvantage]
  exact hε i hi

/-! ## The canonical single-session bridge: the running game IS the KEM reduction.

The hybrid bound above (`akeAdvantagePk_le_sum_hybridStep`) decomposes the running multi-session
advantage into per-session `Test`-swap hops, and `ki_advantage_eq_kem_ind_cpa` reduces the
*structural* single-session game to KEM IND-CPA — but nothing yet connects the two: the per-hop
distinguishing terms are stated over the counted handlers, and the docstrings *assert* "by the
single-session structure this is the assumed KEM advantage" only in prose. This is the "two
disconnected towers" seam (an outside reviewer flagged exactly its corruption-aware analogue).

We close it for the canonical single-session distinguisher. The `akeSpec` adversary is purely
query-driven (it cannot sample its own coins — `akeSpec` does not subsume `unifSpec`), so the
canonical distinguisher is `send; test 0; return (D challenge)` for a decision function
`D : Block → Bool`. We prove that the RUNNING game on this adversary (with the real `Send`/`Test`
oracle handler, freshness gate, and table mutation actually executing) equals the STRUCTURAL
single-session KI game on the corresponding two-phase adversary — hence, by
`ki_advantage_eq_kem_ind_cpa`, equals the KEM IND-CPA advantage of an explicit reduction. So for
this distinguisher class the running-game advantage is *not merely bounded by* a per-hop term whose
meaning is asserted — it is machine-checked to BE the KEM reduction. -/

/-- The canonical single-session distinguisher in the running game: open one session (`Send`),
challenge it (`Test 0`), and output a decision `D` on the returned challenge key. Purely
query-driven — the honest shape of a coin-free `akeSpec` adversary. -/
def canonAke (D : Block → Bool) : AkeAdversary := do
  let _c ← akeSpec.query .send
  let ch ← akeSpec.query (.test 0)
  pure (D ch)

/-- The structural two-phase distinguisher matching `canonAke D`: no pre-challenge state, and the
post-challenge phase outputs `D` applied to the candidate session key. -/
def canonKI (D : Block → Bool) : KI_Adversary where
  State := Unit
  preChallenge _ := pure ()
  postChallenge _ _ k := pure (D k)

/-- **The running game evaluates to the structural game (canonical distinguisher).** Running
`canonAke D` against the real `akeImpl pk` handler — `Send` samples coins and encapsulates to `pk`,
storing `deriveK shared`; `Test 0` finds the fresh session and returns `if b then key else kRand`,
marking it tested — produces exactly the structural `KI_Game`'s post-challenge distribution. The
handler's table mutation, freshness gate, and coin/key sampling all execute; `run'` discards the
final table. Proved by unfolding `simulateQ` over the two queries (`simulateQ_bind`/`_query`) and the
`StateT` plumbing, then matching the resulting `ProbComp` do-block to `KI_Game (canonKI D)`. -/
theorem akeGame_canonAke_eq_KI_Game (D : Block → Bool) :
    evalDist (akeGame (canonAke D)) = KI_Game (canonKI D) := by
  unfold akeGame KI_Game canonAke canonKI kemKe QueryImpl.Stateful.run
  simp only [simulateQ_bind, simulateQ_query, simulateQ_pure,
    OracleQuery.input_query, OracleQuery.cont_query, StateT.run'_eq, StateT.run_bind,
    StateT.run_pure, akeImpl, StateT.run_mk, Session.fresh, List.nil_append, List.getD_cons_zero,
    pure_bind, bind_assoc, id_map, Bool.not_false, Bool.and_true,
    if_true, map_bind, bind_map_left]
  rfl

/-- **Headline — the canonical running game IS the KEM reduction (an equality).** The multi-session
running-game advantage of the canonical single-session distinguisher `canonAke D` equals the KEM
IND-CPA advantage of the explicit reduction `kiToKemAdversary (canonKI D)`. This is the missing wire
made into a theorem: the running protocol game (real `Send`/`Test`/freshness oracle handler) on this
distinguisher class is machine-checked to reduce to the assumed KEM game — not merely bounded by a
per-hop term whose KEM meaning is asserted in prose. (The fully adaptive, multi-`Test`
guess-the-session reduction remains the documented next step; this closes the seam for the canonical
single-session distinguisher, on the running game, with zero slack.) -/
theorem canonAke_advantage_eq_kem_ind_cpa (D : Block → Bool) :
    akeAdvantage (canonAke D)
      = kemKe.IND_CPA_Advantage ProbCompRuntime.probComp (kiToKemAdversary (canonKI D)) := by
  have hadv : akeAdvantage (canonAke D) = KI_Advantage (canonKI D) := by
    unfold akeAdvantage KI_Advantage ProbComp.boolBiasAdvantage SPMF.boolBiasAdvantage
    simp only [probOutput, akeGame_canonAke_eq_KI_Game, SPMF.evalDist_def]
  rw [hadv]
  exact ki_advantage_eq_kem_ind_cpa (canonKI D)

end Demo6Ake
