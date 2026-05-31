/-
  SPQR node — value adequacy and functional correctness of the extracted
  Ratcheted-Authenticator glue.

  `authenticator.rs` is the Aeneas extraction of the non-cryptographic core of
  SPQR's authenticator (`src/authenticator.rs`, `src/util.rs`): the big-endian
  epoch encoding, the domain-separation string assembly, the `root_key`/`mac_key`
  update split, and the constant-time MAC comparison. The HMAC/HKDF themselves are
  external crates outside the fragment (constructions above the hardness floor —
  extracted+reduced in `crypto/sha256.rs`); this file is the byte plumbing.

  We prove **value adequacy** (totality) of every entry point, plus functional
  correctness of the security-relevant pieces: the KDF-output split is exactly the
  two 32-byte halves, the update IKM is `root_key ‖ k` (the documented salt/IKM
  swap vs. the spec prose), and the constant-time comparator returns `0` on equal
  MACs (so `verify_*` accepts a genuine tag).
-/
import Demos.Extracted.Authenticator

open Aeneas Std Result

namespace Spqr.Auth

/-! ### Big-endian epoch encoding -/

/-- `epoch_to_be_bytes` is total: each iteration shifts `ep` right by `56 - 8·i`
(`i < 8`, so the shift is `< 64`) and truncates to a byte. -/
@[step]
theorem epoch_to_be_bytes_total (ep : Std.U64) :
    authenticator.epoch_to_be_bytes ep ⦃ fun _ => True ⦄ := by
  unfold authenticator.epoch_to_be_bytes authenticator.epoch_to_be_bytes_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 8#usize) × Std.Usize => 8 - s.2.val)
    (inv := fun s : (Array Std.U8 8#usize) × Std.Usize => s.2.val ≤ 8)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [authenticator.epoch_to_be_bytes_loop.body]
    split
    · rename_i hlt
      repeat' step*
    · trivial
  · scalar_tac

/-! ### The root_key/mac_key update split -/

/-- The `update_split` loop computes the two 32-byte halves of the 64-byte
`KDF_AUTH` output on indices processed so far. -/
theorem update_split_loop_spec (kdf : Array Std.U8 64#usize) :
    ∀ (rk mk : Array Std.U8 32#usize) (i : Std.Usize),
      i.val ≤ 32 →
      (∀ j, j < i.val → rk.val[j]! = kdf.val[j]!) →
      (∀ j, j < i.val → mk.val[j]! = kdf.val[32 + j]!) →
      authenticator.update_split_loop kdf rk mk i
        ⦃ r => (∀ j, j < 32 → r.1.val[j]! = kdf.val[j]!) ∧
               (∀ j, j < 32 → r.2.val[j]! = kdf.val[32 + j]!) ⦄ := by
  intro rk mk i hi hrk hmk
  unfold authenticator.update_split_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 32#usize) × (Array Std.U8 32#usize) × Std.Usize =>
      32 - s.2.2.val)
    (inv := fun s : (Array Std.U8 32#usize) × (Array Std.U8 32#usize) × Std.Usize =>
      s.2.2.val ≤ 32 ∧
      (∀ j, j < s.2.2.val → s.1.val[j]! = kdf.val[j]!) ∧
      (∀ j, j < s.2.2.val → s.2.1.val[j]! = kdf.val[32 + j]!))
    (post := fun r : (Array Std.U8 32#usize) × (Array Std.U8 32#usize) =>
      (∀ j, j < 32 → r.1.val[j]! = kdf.val[j]!) ∧
      (∀ j, j < 32 → r.2.val[j]! = kdf.val[32 + j]!))
  · rintro ⟨rk1, mk1, i1⟩ ⟨hi1, hrk1, hmk1⟩
    simp only [authenticator.update_split_loop.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨a, ha⟩
      step as ⟨o32, ho32⟩
      step as ⟨v2, hv2⟩
      step as ⟨a1, ha1⟩
      step as ⟨i4, hi4⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · scalar_tac
      · intro j hj
        subst ha
        by_cases hje : j = i1.val
        · subst hje; simp_lists [hv1]
        · have : j < i1.val := by scalar_tac
          simp_lists; exact hrk1 j this
      · intro j hj
        subst ha1
        by_cases hje : j = i1.val
        · subst hje; simp_lists [hv2]; scalar_tac
        · have : j < i1.val := by scalar_tac
          simp_lists; exact hmk1 j this
      · scalar_tac
    · rename_i hge
      refine ⟨?_, ?_⟩
      · intro j hj; apply hrk1; scalar_tac
      · intro j hj; apply hmk1; scalar_tac
  · exact ⟨hi, hrk, hmk⟩

/-- **Functional correctness of the update split.** `update_split` yields exactly
`(kdf_out[0..32], kdf_out[32..64])` — the `root_key`/`mac_key` reassignment in
`Authenticator::update`. -/
theorem update_split_spec (kdf : Array Std.U8 64#usize) :
    authenticator.update_split kdf
      ⦃ r => (∀ j, j < 32 → r.1.val[j]! = kdf.val[j]!) ∧
             (∀ j, j < 32 → r.2.val[j]! = kdf.val[32 + j]!) ⦄ := by
  unfold authenticator.update_split
  apply update_split_loop_spec <;> scalar_tac

/-! ### The update IKM (`root_key ‖ k`) -/

/-- The `auth_update_ikm` loop writes `root_key` to bytes `0..32` and `k` to bytes
`32..64` on indices processed so far. -/
theorem auth_update_ikm_loop_spec (rk k : Array Std.U8 32#usize) :
    ∀ (out : Array Std.U8 64#usize) (i : Std.Usize),
      i.val ≤ 32 →
      (∀ j, j < i.val → out.val[j]! = rk.val[j]!) →
      (∀ j, j < i.val → out.val[32 + j]! = k.val[j]!) →
      authenticator.auth_update_ikm_loop rk k out i
        ⦃ r => (∀ j, j < 32 → r.val[j]! = rk.val[j]!) ∧
               (∀ j, j < 32 → r.val[32 + j]! = k.val[j]!) ⦄ := by
  intro out i hi hrk hk
  unfold authenticator.auth_update_ikm_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 64#usize) × Std.Usize => 32 - s.2.val)
    (inv := fun s : (Array Std.U8 64#usize) × Std.Usize =>
      s.2.val ≤ 32 ∧
      (∀ j, j < s.2.val → s.1.val[j]! = rk.val[j]!) ∧
      (∀ j, j < s.2.val → s.1.val[32 + j]! = k.val[j]!))
    (post := fun r : Array Std.U8 64#usize =>
      (∀ j, j < 32 → r.val[j]! = rk.val[j]!) ∧
      (∀ j, j < 32 → r.val[32 + j]! = k.val[j]!))
  · rintro ⟨o1, i1⟩ ⟨hi1, hrk1, hk1⟩
    simp only [authenticator.auth_update_ikm_loop.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨o2, ho2⟩
      step as ⟨v2, hv2⟩
      step as ⟨o32, ho32⟩
      step as ⟨a, ha⟩
      step as ⟨i4, hi4⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · scalar_tac
      · intro j hj
        subst ha; subst ho2
        by_cases hje : j = i1.val
        · subst hje; simp_lists [hv1]
        · have : j < i1.val := by scalar_tac
          simp_lists; exact hrk1 j this
      · intro j hj
        subst ha; subst ho2
        by_cases hje : j = i1.val
        · subst hje; simp_lists [hv2]
        · have hlt2 : j < i1.val := by scalar_tac
          simp_lists; exact hk1 j hlt2
      · scalar_tac
    · rename_i hge
      refine ⟨?_, ?_⟩
      · intro j hj; apply hrk1; scalar_tac
      · intro j hj; apply hk1; scalar_tac
  · exact ⟨hi, hrk, hk⟩

/-- **Functional correctness of the update IKM.** `auth_update_ikm` is `root_key ‖
k`: the HKDF input keying material in `Authenticator::update`
(`[self.root_key, k].concat()`) — the documented salt/IKM swap relative to the
ML-KEM-Braid spec prose, here pinned to the code. -/
theorem auth_update_ikm_spec (rk k : Array Std.U8 32#usize) :
    authenticator.auth_update_ikm rk k
      ⦃ r => (∀ j, j < 32 → r.val[j]! = rk.val[j]!) ∧
             (∀ j, j < 32 → r.val[32 + j]! = k.val[j]!) ⦄ := by
  unfold authenticator.auth_update_ikm
  apply auth_update_ikm_loop_spec <;> scalar_tac

/-! ### Constant-time MAC comparison -/

/-- On equal inputs the comparison accumulator never changes: `r |= a[i] ^ a[i]`
adds nothing. So the loop returns its initial accumulator. -/
theorem compare_loop_refl (a : Array Std.U8 32#usize) :
    ∀ (r : Std.U8) (i : Std.Usize), i.val ≤ 32 →
      authenticator.compare_loop a a r i ⦃ res => res = r ⦄ := by
  intro r i hi
  unfold authenticator.compare_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : Std.U8 × Std.Usize => 32 - s.2.val)
    (inv := fun s : Std.U8 × Std.Usize => s.2.val ≤ 32 ∧ s.1 = r)
    (post := fun res : Std.U8 => res = r)
  · rintro ⟨r1, i1⟩ ⟨hi1, hr1⟩
    simp only [authenticator.compare_loop.body, authenticator.MACSIZE]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨v2, hv2⟩
      step as ⟨i3, hi3⟩
      step as ⟨r2, hr2⟩
      step as ⟨i4, hi4⟩
      refine ⟨?_, ?_, ?_⟩
      · scalar_tac
      · -- r2 = r1 |||(a[i] ^ a[i]) = r1 ||| 0 = r1 = r
        have hvv : v1 = v2 := by rw [hv1, hv2]
        have hr1' : r1 = r := hr1
        apply UScalar.eq_of_val_eq
        have hi30 : i3.val = 0 := by rw [hi3, hvv]; simp [UScalar.val_xor, Nat.xor_self]
        rw [hr2, hr1']; simp [UScalar.val_or, hi30]
      · scalar_tac
    · rename_i hge
      exact hr1
  · exact ⟨hi, rfl⟩

-- `compare_loop_refl` shows the accumulator is unchanged on equal inputs (accept); `inz_spec`
-- evaluates the constant-time bit-twiddle (`inz 0 = 0` accept, `inz v = 1` for `v ≠ 0` reject);
-- and `compare_reject` proves the security direction — `compare` returns nonzero on any byte
-- difference, i.e. a forged/altered tag is rejected (the SCKA unforgeability direction).

/-- The constant-time `inz` bit-twiddle on the 8-bit input, as a closed `BitVec` identity
(including the final narrowing cast to 8 bits) — discharged by KERNEL `decide` (256-case
enumeration), so no SAT solver and no native-reflection axiom. `((v | -v) >> 8) & 1 = 0` iff
`v = 0`. -/
theorem inz_bit : ∀ b : BitVec 8,
    ((((b.setWidth 16) ||| (~~~(b.setWidth 16) + 1)) >>> 8 &&& 1#16).setWidth 8)
      = (if b = 0#8 then 0#8 else 1#8) := by
  decide

/-- **Evaluation of the constant-time `inz`.** `inz v = 0` when `v = 0` (accept) and `= 1`
when `v ≠ 0` (reject) — the bit-twiddle `((v | -v) >> 8) & 1`, via the kernel-decided `inz_bit`
(so the headline proof carries no native/reflection axiom). -/
theorem inz_spec (v : Std.U8) :
    authenticator.inz v ⦃ res => res.bv = if v.bv = 0#8 then 0#8 else 1#8 ⦄ := by
  unfold authenticator.inz
  step*
  simp only [Aeneas.Std.UScalar.cast_bv_eq, result_post2, i3_post2, i2_post2, i1_post, i_post,
    value1_post, Aeneas.Std.UScalar.wrapping_add_bv_eq, Aeneas.Std.UScalar.bv_not,
    Aeneas.Std.UScalarTy.numBits]
  exact inz_bit v.bv

/-- XOR of two differing bytes is nonzero (via `Nat.xor_eq_zero`, kernel-checked). -/
theorem u8_xor_ne_zero (a b : Std.U8) (h : a ≠ b) : a ^^^ b ≠ 0#u8 := by
  intro hc; apply h; apply Aeneas.Std.UScalar.eq_of_val_eq
  have hv : (a ^^^ b).val = 0 := by rw [hc]; rfl
  rw [Aeneas.Std.UScalar.val_xor] at hv
  exact Nat.xor_eq_zero_iff.mp hv

/-- OR with a nonzero right operand is nonzero (via `BitVec.or_eq_zero_iff`, kernel-checked). -/
theorem u8_or_ne_zero_right (a c : Std.U8) (h : c ≠ 0#u8) : a ||| c ≠ 0#u8 := by
  intro hc; apply h
  have e : (a ||| c).bv = 0#8 := by rw [hc]; decide
  rw [Aeneas.Std.UScalar.bv_or] at e
  have hc0 : c.bv = 0#8 := (BitVec.or_eq_zero_iff.mp e).2
  apply Aeneas.Std.UScalar.eq_of_val_eq
  show c.bv.toNat = (0#u8).bv.toNat; rw [hc0]; decide

/-- OR with a nonzero left operand is nonzero. -/
theorem u8_or_ne_zero_left (a c : Std.U8) (h : a ≠ 0#u8) : a ||| c ≠ 0#u8 := by
  intro hc; apply h
  have e : (a ||| c).bv = 0#8 := by rw [hc]; decide
  rw [Aeneas.Std.UScalar.bv_or] at e
  have ha0 : a.bv = 0#8 := (BitVec.or_eq_zero_iff.mp e).1
  apply Aeneas.Std.UScalar.eq_of_val_eq
  show a.bv.toNat = (0#u8).bv.toNat; rw [ha0]; decide

/-- **The comparison loop rejects on a difference.** If `lhs` and `rhs` differ at some index
`k < 32`, the OR-accumulator is nonzero at the end: once the differing byte's XOR is OR-ed in,
no later OR can clear it. Invariant: `r ≠ 0 ∨ i ≤ k` (either we already differ, or we have not
yet reached `k`). -/
theorem compare_loop_reject (lhs rhs : Array Std.U8 32#usize) (k : Nat)
    (hk : k < 32) (hdiff : lhs.val[k]! ≠ rhs.val[k]!) :
    ∀ (r : Std.U8) (i : Std.Usize), i.val ≤ 32 → (r ≠ 0#u8 ∨ i.val ≤ k) →
      authenticator.compare_loop lhs rhs r i ⦃ res => res ≠ 0#u8 ⦄ := by
  intro r i hi hinv0
  unfold authenticator.compare_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : Std.U8 × Std.Usize => 32 - s.2.val)
    (inv := fun s : Std.U8 × Std.Usize => s.2.val ≤ 32 ∧ (s.1 ≠ 0#u8 ∨ s.2.val ≤ k))
    (post := fun res : Std.U8 => res ≠ 0#u8)
  · rintro ⟨r1, i1⟩ ⟨hi1, hor⟩
    simp only [authenticator.compare_loop.body, authenticator.MACSIZE]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨v2, hv2⟩
      step as ⟨i3, hi3⟩
      step as ⟨r2, hr2⟩
      step as ⟨i4, hi4⟩
      refine ⟨?_, ?_, ?_⟩
      · scalar_tac
      · have hi3' : i3 = v1 ^^^ v2 := Aeneas.Std.UScalar.eq_of_val_eq hi3
        have hr2' : r2 = r1 ||| i3 := Aeneas.Std.UScalar.eq_of_val_eq hr2
        by_cases hik : i1.val = k
        · -- at the differing index: the XOR term is nonzero, so the accumulator is nonzero
          left
          have hne : v1 ≠ v2 := by rw [hv1, hv2, hik]; exact hdiff
          rw [hr2', hi3']
          exact u8_or_ne_zero_right r1 (v1 ^^^ v2) (u8_xor_ne_zero v1 v2 hne)
        · cases hor with
          | inl hr1 => left; rw [hr2']; exact u8_or_ne_zero_left r1 i3 hr1
          | inr hle => right; have hle' : i1.val ≤ k := hle; scalar_tac
      · scalar_tac
    · rename_i hge
      cases hor with
      | inl hr1 => exact hr1
      | inr hle => exfalso; scalar_tac
  · exact ⟨hi, hinv0⟩

/-- **The MAC comparator rejects forged tags.** If the offered tag `rhs` differs from the
expected `lhs` at any byte, `compare` returns a nonzero value (reject) — the unforgeability
direction the SCKA authentication argument needs. `compare = inz(OR-fold)`; the fold is nonzero
(`compare_loop_reject`) and `inz` of a nonzero value is `1` (`inz_spec`). -/
theorem compare_reject (lhs rhs : Array Std.U8 32#usize) (k : Nat)
    (hk : k < 32) (hdiff : lhs.val[k]! ≠ rhs.val[k]!) :
    authenticator.compare lhs rhs ⦃ res => res ≠ 0#u8 ⦄ := by
  unfold authenticator.compare
  apply Aeneas.Std.WP.spec_bind
    (compare_loop_reject lhs rhs k hk hdiff 0#u8 0#usize (by scalar_tac) (Or.inr (by scalar_tac)))
  intro r hr
  -- `inz r ≠ 0` because `r ≠ 0`: weaken `inz_spec` (kernel-clean) to the rejection.
  apply Aeneas.Std.WP.spec_mono (inz_spec r)
  intro res hres
  have hrbv : r.bv ≠ 0#8 := by
    intro h0; apply hr; apply Aeneas.Std.UScalar.eq_of_val_eq
    show r.bv.toNat = (0#u8).bv.toNat; rw [h0]; decide
  rw [if_neg hrbv] at hres
  intro hc0; rw [hc0] at hres; exact absurd hres (by decide)

/-! ### Domain-separation string / MAC-data builders (value adequacy) -/

@[step]
theorem auth_update_info_loop0_ok :
    ∀ (out : Array Std.U8 53#usize) (i : Std.Usize), i.val ≤ 45 →
      authenticator.auth_update_info_loop0 out i ⦃ fun _ => True ⦄ := by
  intro out i hi
  unfold authenticator.auth_update_info_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 53#usize) × Std.Usize => 45 - s.2.val)
    (inv := fun s : (Array Std.U8 53#usize) × Std.Usize => s.2.val ≤ 45)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [authenticator.auth_update_info_loop0.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

@[step]
theorem auth_update_info_loop1_ok (eb : Array Std.U8 8#usize) :
    ∀ (out : Array Std.U8 53#usize) (j : Std.Usize), j.val ≤ 8 →
      authenticator.auth_update_info_loop1 eb out j ⦃ fun _ => True ⦄ := by
  intro out j hj
  unfold authenticator.auth_update_info_loop1
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 53#usize) × Std.Usize => 8 - s.2.val)
    (inv := fun s : (Array Std.U8 53#usize) × Std.Usize => s.2.val ≤ 8)
    (post := fun _ => True)
  · rintro ⟨o1, j1⟩ hinv
    simp only [authenticator.auth_update_info_loop1.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hj

/-- `auth_update_info` (HKDF info = label ‖ `ToBytes(epoch)`) is total. -/
theorem auth_update_info_total (ep : Std.U64) :
    authenticator.auth_update_info ep ⦃ fun _ => True ⦄ := by
  unfold authenticator.auth_update_info
  repeat' step*

@[step]
theorem mac_hdr_data_loop0_ok :
    ∀ (out : Array Std.U8 105#usize) (i : Std.Usize), i.val ≤ 33 →
      authenticator.mac_hdr_data_loop0 out i ⦃ fun _ => True ⦄ := by
  intro out i hi
  unfold authenticator.mac_hdr_data_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 105#usize) × Std.Usize => 33 - s.2.val)
    (inv := fun s : (Array Std.U8 105#usize) × Std.Usize => s.2.val ≤ 33)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [authenticator.mac_hdr_data_loop0.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

@[step]
theorem mac_hdr_data_loop1_ok (eb : Array Std.U8 8#usize) :
    ∀ (out : Array Std.U8 105#usize) (j : Std.Usize), j.val ≤ 8 →
      authenticator.mac_hdr_data_loop1 eb out j ⦃ fun _ => True ⦄ := by
  intro out j hj
  unfold authenticator.mac_hdr_data_loop1
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 105#usize) × Std.Usize => 8 - s.2.val)
    (inv := fun s : (Array Std.U8 105#usize) × Std.Usize => s.2.val ≤ 8)
    (post := fun _ => True)
  · rintro ⟨o1, j1⟩ hinv
    simp only [authenticator.mac_hdr_data_loop1.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hj

@[step]
theorem mac_hdr_data_loop2_ok (hdr : Array Std.U8 64#usize) :
    ∀ (out : Array Std.U8 105#usize) (m : Std.Usize), m.val ≤ 64 →
      authenticator.mac_hdr_data_loop2 hdr out m ⦃ fun _ => True ⦄ := by
  intro out m hm
  unfold authenticator.mac_hdr_data_loop2
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 105#usize) × Std.Usize => 64 - s.2.val)
    (inv := fun s : (Array Std.U8 105#usize) × Std.Usize => s.2.val ≤ 64)
    (post := fun _ => True)
  · rintro ⟨o1, m1⟩ hinv
    simp only [authenticator.mac_hdr_data_loop2.body, authenticator.HEADER_SIZE]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hm

/-- **Value adequacy of the header MAC input** `label ‖ ToBytes(epoch) ‖ hdr` (the
64-byte ML-KEM-768 header), as in `Authenticator::mac_hdr`. -/
theorem mac_hdr_data_total (ep : Std.U64) (hdr : Array Std.U8 64#usize) :
    authenticator.mac_hdr_data ep hdr ⦃ fun _ => True ⦄ := by
  unfold authenticator.mac_hdr_data
  repeat' step*

@[step]
theorem mac_ct_data_loop0_ok :
    ∀ (out : Array Std.U8 1131#usize) (i : Std.Usize), i.val ≤ 35 →
      authenticator.mac_ct_data_loop0 out i ⦃ fun _ => True ⦄ := by
  intro out i hi
  unfold authenticator.mac_ct_data_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 1131#usize) × Std.Usize => 35 - s.2.val)
    (inv := fun s : (Array Std.U8 1131#usize) × Std.Usize => s.2.val ≤ 35)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [authenticator.mac_ct_data_loop0.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

@[step]
theorem mac_ct_data_loop1_ok (eb : Array Std.U8 8#usize) :
    ∀ (out : Array Std.U8 1131#usize) (j : Std.Usize), j.val ≤ 8 →
      authenticator.mac_ct_data_loop1 eb out j ⦃ fun _ => True ⦄ := by
  intro out j hj
  unfold authenticator.mac_ct_data_loop1
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 1131#usize) × Std.Usize => 8 - s.2.val)
    (inv := fun s : (Array Std.U8 1131#usize) × Std.Usize => s.2.val ≤ 8)
    (post := fun _ => True)
  · rintro ⟨o1, j1⟩ hinv
    simp only [authenticator.mac_ct_data_loop1.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hj

@[step]
theorem mac_ct_data_loop2_ok (ct : Array Std.U8 1088#usize) :
    ∀ (out : Array Std.U8 1131#usize) (m : Std.Usize), m.val ≤ 1088 →
      authenticator.mac_ct_data_loop2 ct out m ⦃ fun _ => True ⦄ := by
  intro out m hm
  unfold authenticator.mac_ct_data_loop2
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 1131#usize) × Std.Usize => 1088 - s.2.val)
    (inv := fun s : (Array Std.U8 1131#usize) × Std.Usize => s.2.val ≤ 1088)
    (post := fun _ => True)
  · rintro ⟨o1, m1⟩ hinv
    simp only [authenticator.mac_ct_data_loop2.body, authenticator.CIPHERTEXT_SIZE]
    repeat' step*
  · exact hm

/-- **Value adequacy of the ciphertext MAC input** `label ‖ ToBytes(epoch) ‖ (ct1‖ct2)`
(the 1088-byte ML-KEM-768 ciphertext the authenticator actually covers), as in
`Authenticator::mac_ct`/`verify_ct`. -/
theorem mac_ct_data_total (ep : Std.U64) (ct : Array Std.U8 1088#usize) :
    authenticator.mac_ct_data ep ct ⦃ fun _ => True ⦄ := by
  unfold authenticator.mac_ct_data
  repeat' step*

end Spqr.Auth
