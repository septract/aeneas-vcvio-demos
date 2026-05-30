/-
  PQXDH node — value adequacy and functional correctness of the extracted
  key-schedule glue.

  `pqxdh.rs` is the Aeneas extraction of the deterministic byte plumbing of
  Signal's PQXDH handshake (`rust/protocol/src/pqxdh.rs`, with the EC wire codec
  from `rust/core/src/curve.rs`): assembling the HKDF secret input
  (`[0xFF;32] ‖ DH1 ‖ DH2 ‖ DH3 [‖ DH4] ‖ SS`), splitting the 96-byte HKDF output
  into `(root_key, chain_key, pqr_key)`, and the `EncodeEC`/`DecodeEC` codec.
  The DH / KEM / HKDF primitives are external; this is the glue around them — the
  error-dense layer the Bhargavan et al. (USENIX'24) re-encapsulation attack lived
  in.

  We prove functional correctness of the security-relevant byte layouts:
  the discontinuity prefix is all-`0xFF`, the HKDF-output split is exactly the
  three 32-byte slices (`HandshakeKeys::derive_with_label`'s `derive_arrays`), and
  `DecodeEC ∘ EncodeEC = id` (the inverse law the spec §2.1 mandates and the AD
  construction relies on). These subsume value adequacy (a `spec`-triple obligation
  rules out `fail`/`div`). The full `pqxdh_secret_input` assembly threads `&mut`
  slices through `put32`; its mechanized spec is left as future work (noted at the
  prefix lemma), but its per-segment shape is exactly the prefix + `put32` copies.
-/
import Demos.Extracted.Pqxdh

open Aeneas Std Result

namespace Pqxdh

/-! ### The discontinuity prefix -/

/-- The discontinuity-prefix loop fills bytes `0..32` of the secret buffer with
`0xFF` (X3DH/PQXDH "discontinuity bytes"), leaving it total. This is the leading
block of `pqxdh_secret_input`; the remaining `put32` copies (which thread `&mut`
slices) are value-adequate by the same shape but their slice spec is future work. -/
theorem secret_prefix_loop_spec :
    ∀ (out : Array Std.U8 160#usize) (i : Std.Usize), i.val ≤ 32 →
      (∀ j, j < i.val → out.val[j]! = 255#u8) →
      pqxdh.pqxdh_secret_input_loop out i
        ⦃ r => ∀ j, j < 32 → r.val[j]! = 255#u8 ⦄ := by
  intro out i hi hpre
  unfold pqxdh.pqxdh_secret_input_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 160#usize) × Std.Usize => 32 - s.2.val)
    (inv := fun s : (Array Std.U8 160#usize) × Std.Usize =>
      s.2.val ≤ 32 ∧ (∀ j, j < s.2.val → s.1.val[j]! = 255#u8))
    (post := fun r : Array Std.U8 160#usize => ∀ j, j < 32 → r.val[j]! = 255#u8)
  · rintro ⟨o1, i1⟩ ⟨hi1, hpre1⟩
    simp only [pqxdh.pqxdh_secret_input_loop.body, pqxdh.DH_LEN]
    split
    · rename_i hlt
      step as ⟨a, ha⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_⟩
      · scalar_tac
      · intro j hj
        subst ha
        by_cases hje : j = i1.val
        · subst hje; simp_lists
        · have : j < i1.val := by scalar_tac
          simp_lists; exact hpre1 j this
      · scalar_tac
    · rename_i hge
      intro j hj; apply hpre1; scalar_tac
  · exact ⟨hi, hpre⟩

/-! ### The HKDF-output split -/

/-- The `derive_split` loop computes, on indices processed so far, the three
32-byte slices of the HKDF output. -/
theorem derive_split_loop_spec (okm : Array Std.U8 96#usize) :
    ∀ (rk ck pq : Array Std.U8 32#usize) (i : Std.Usize),
      i.val ≤ 32 →
      (∀ j, j < i.val → rk.val[j]! = okm.val[j]!) →
      (∀ j, j < i.val → ck.val[j]! = okm.val[32 + j]!) →
      (∀ j, j < i.val → pq.val[j]! = okm.val[64 + j]!) →
      pqxdh.derive_split_loop okm rk ck pq i
        ⦃ r => (∀ j, j < 32 → r.1.val[j]! = okm.val[j]!) ∧
               (∀ j, j < 32 → r.2.1.val[j]! = okm.val[32 + j]!) ∧
               (∀ j, j < 32 → r.2.2.val[j]! = okm.val[64 + j]!) ⦄ := by
  intro rk ck pq i hi hrk hck hpq
  unfold pqxdh.derive_split_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 32#usize) × (Array Std.U8 32#usize) ×
      (Array Std.U8 32#usize) × Std.Usize => 32 - s.2.2.2.val)
    (inv := fun s : (Array Std.U8 32#usize) × (Array Std.U8 32#usize) ×
      (Array Std.U8 32#usize) × Std.Usize =>
      s.2.2.2.val ≤ 32 ∧
      (∀ j, j < s.2.2.2.val → s.1.val[j]! = okm.val[j]!) ∧
      (∀ j, j < s.2.2.2.val → s.2.1.val[j]! = okm.val[32 + j]!) ∧
      (∀ j, j < s.2.2.2.val → s.2.2.1.val[j]! = okm.val[64 + j]!))
    (post := fun r : (Array Std.U8 32#usize) × (Array Std.U8 32#usize) ×
      (Array Std.U8 32#usize) =>
      (∀ j, j < 32 → r.1.val[j]! = okm.val[j]!) ∧
      (∀ j, j < 32 → r.2.1.val[j]! = okm.val[32 + j]!) ∧
      (∀ j, j < 32 → r.2.2.val[j]! = okm.val[64 + j]!))
  · rintro ⟨rk1, ck1, pq1, i1⟩ ⟨hi1, hrk1, hck1, hpq1⟩
    simp only [pqxdh.derive_split_loop.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨a, ha⟩
      step as ⟨o32, ho32⟩
      step as ⟨v2, hv2⟩
      step as ⟨a1, ha1⟩
      step as ⟨o64, ho64⟩
      step as ⟨v3, hv3⟩
      step as ⟨a2, ha2⟩
      step as ⟨i6, hi6⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
          simp_lists; exact hck1 j this
      · intro j hj
        subst ha2
        by_cases hje : j = i1.val
        · subst hje; simp_lists [hv3]; scalar_tac
        · have : j < i1.val := by scalar_tac
          simp_lists; exact hpq1 j this
      · scalar_tac
    · rename_i hge
      refine ⟨?_, ?_, ?_⟩
      · intro j hj; apply hrk1; scalar_tac
      · intro j hj; apply hck1; scalar_tac
      · intro j hj; apply hpq1; scalar_tac
  · exact ⟨hi, hrk, hck, hpq⟩

/-- **Functional correctness of the HKDF-output split.** `derive_split` is total
and yields exactly `(okm[0..32], okm[32..64], okm[64..96])` — the `root_key`,
`chain_key`, `pqr_key` deserialization that `HandshakeKeys::derive_with_label`
performs via `derive_arrays`. -/
theorem derive_split_spec (okm : Array Std.U8 96#usize) :
    pqxdh.derive_split okm
      ⦃ r => (∀ j, j < 32 → r.1.val[j]! = okm.val[j]!) ∧
             (∀ j, j < 32 → r.2.1.val[j]! = okm.val[32 + j]!) ∧
             (∀ j, j < 32 → r.2.2.val[j]! = okm.val[64 + j]!) ⦄ := by
  unfold pqxdh.derive_split
  apply derive_split_loop_spec <;> scalar_tac

/-! ### The EncodeEC / DecodeEC codec -/

/-- The `encode_ec` body loop copies `key[0..32]` into `out[1..33]` and leaves the
tag byte `out[0]` untouched (it only writes indices `1 + i`). -/
theorem encode_ec_loop_spec (key : Array Std.U8 32#usize) (c : Std.U8) :
    ∀ (out : Array Std.U8 33#usize) (i : Std.Usize),
      i.val ≤ 32 → out.val[0]! = c →
      (∀ j, j < i.val → out.val[1 + j]! = key.val[j]!) →
      pqxdh.encode_ec_loop key out i
        ⦃ r => r.val[0]! = c ∧ (∀ j, j < 32 → r.val[1 + j]! = key.val[j]!) ⦄ := by
  intro out i hi h0 hout
  unfold pqxdh.encode_ec_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 33#usize) × Std.Usize => 32 - s.2.val)
    (inv := fun s : (Array Std.U8 33#usize) × Std.Usize =>
      s.2.val ≤ 32 ∧ s.1.val[0]! = c ∧ (∀ j, j < s.2.val → s.1.val[1 + j]! = key.val[j]!))
    (post := fun r : Array Std.U8 33#usize =>
      r.val[0]! = c ∧ (∀ j, j < 32 → r.val[1 + j]! = key.val[j]!))
  · rintro ⟨o1, i1⟩ ⟨hi1, h01, hout1⟩
    simp only [pqxdh.encode_ec_loop.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨o2, ho2⟩
      step as ⟨a, ha⟩
      step as ⟨i3, hi3⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · scalar_tac
      · subst ha; simp_lists [h01]
      · intro j hj
        subst ha
        by_cases hje : j = i1.val
        · subst hje; simp_lists [hv1]
        · have : j < i1.val := by scalar_tac
          simp_lists; exact hout1 j this
      · scalar_tac
    · rename_i hge
      exact ⟨h01, fun j hj => hout1 j (by scalar_tac)⟩
  · exact ⟨hi, h0, hout⟩

/-- **Functional correctness of `EncodeEC`.** `encode_ec` is total and produces a
33-byte wire key whose tag byte is `0x05` (`KeyType::Djb`) and whose remaining 32
bytes are the input u-coordinate — `PublicKey::serialize`. -/
theorem encode_ec_spec (key : Array Std.U8 32#usize) :
    pqxdh.encode_ec key
      ⦃ r => r.val[0]! = pqxdh.KEY_TYPE_DJB ∧
             (∀ j, j < 32 → r.val[1 + j]! = key.val[j]!) ⦄ := by
  unfold pqxdh.encode_ec
  step as ⟨a, ha⟩
  apply encode_ec_loop_spec key pqxdh.KEY_TYPE_DJB a 0#usize (by scalar_tac)
  · subst ha; simp_lists
  · intro j hj; scalar_tac

/-- The `decode_ec` body loop copies `bytes[1..33]` into `key[0..32]`. -/
theorem decode_ec_loop_spec (bytes : Array Std.U8 33#usize) :
    ∀ (key : Array Std.U8 32#usize) (i : Std.Usize),
      i.val ≤ 32 →
      (∀ j, j < i.val → key.val[j]! = bytes.val[1 + j]!) →
      pqxdh.decode_ec_loop bytes key i
        ⦃ r => ∀ j, j < 32 → r.val[j]! = bytes.val[1 + j]! ⦄ := by
  intro key i hi hkey
  unfold pqxdh.decode_ec_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 32#usize) × Std.Usize => 32 - s.2.val)
    (inv := fun s : (Array Std.U8 32#usize) × Std.Usize =>
      s.2.val ≤ 32 ∧ (∀ j, j < s.2.val → s.1.val[j]! = bytes.val[1 + j]!))
    (post := fun r : Array Std.U8 32#usize => ∀ j, j < 32 → r.val[j]! = bytes.val[1 + j]!)
  · rintro ⟨k1, i1⟩ ⟨hi1, hkey1⟩
    simp only [pqxdh.decode_ec_loop.body]
    split
    · rename_i hlt
      step as ⟨i2, hi2⟩
      step as ⟨v1, hv1⟩
      step as ⟨a, ha⟩
      step as ⟨i3, hi3⟩
      refine ⟨?_, ?_, ?_⟩
      · scalar_tac
      · intro j hj
        subst ha
        by_cases hje : j = i1.val
        · subst hje; simp_lists [hv1, hi2]
        · have : j < i1.val := by scalar_tac
          simp_lists; exact hkey1 j this
      · scalar_tac
    · rename_i hge
      intro j hj; apply hkey1; scalar_tac
  · exact ⟨hi, hkey⟩

/-- **`DecodeEC ∘ EncodeEC = id` (spec §2.1).** Decoding a freshly-encoded
Curve25519 key returns `some key'` whose 32 bytes agree with the original — the
inverse law the PQXDH spec mandates and the AD construction relies on. (The DJB
tag check passes because `encode_ec` writes `0x05` at byte 0.) -/
theorem decode_encode_roundtrip (key : Array Std.U8 32#usize) :
    (do let e ← pqxdh.encode_ec key; pqxdh.decode_ec e)
      ⦃ r => ∃ k, r = some k ∧ (∀ j, j < 32 → k.val[j]! = key.val[j]!) ⦄ := by
  apply Aeneas.Std.WP.spec_bind (encode_ec_spec key)
  rintro e ⟨h0, htail⟩
  unfold pqxdh.decode_ec
  step as ⟨tag, htag⟩
  have htagv : tag = pqxdh.KEY_TYPE_DJB := by simp_all
  split
  · -- the DJB tag check cannot fail: `tag = 0x05`.
    rename_i hne; simp [htagv] at hne
  · -- decode the 32-byte u-coordinate and conclude it agrees with `key`.
    apply Aeneas.Std.WP.spec_bind
      (decode_ec_loop_spec e (Array.repeat 32#usize 0#u8) 0#usize
        (by scalar_tac) (by intro j hj; scalar_tac))
    rintro k hk
    exact ⟨k, rfl, fun j hj => by rw [hk j hj]; exact htail j hj⟩

end Pqxdh
