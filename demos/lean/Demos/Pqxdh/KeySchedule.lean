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
  the discontinuity prefix is all-`0xFF`, the **full secret-input assembly** is exactly
  `[0xFF;32] ‖ DH1 ‖ DH2 ‖ DH3 [‖ DH4] ‖ SS` (both the no-OPK and one-time-prekey paths —
  `pqxdh_secret_input_spec` / `pqxdh_secret_input_with_opk_spec`, via a reusable `put32`
  segment-copy spec that sets its window and preserves the rest), the HKDF-output split is
  exactly the three 32-byte slices (`HandshakeKeys::derive_with_label`'s `derive_arrays`), and
  `DecodeEC ∘ EncodeEC = id` (the inverse law the spec §2.1 mandates and the AD construction
  relies on). These subsume value adequacy (a `spec`-triple obligation rules out `fail`/`div`).
  The secret-input layout is the KDF-input premise the AKE proof rests on, and its segment
  ordering is the part the Bhargavan et al. re-encapsulation attack turned on.
-/
import Demos.Extracted.Pqxdh

open Aeneas Std Result

namespace Pqxdh

/-- `(to_slice a).val = a.val` definitionally — used to collapse the `to_slice`/`from_slice`
round-trips without unfolding `to_slice`'s proof term (which balloons on nested slices). -/
theorem to_slice_val {n : Std.Usize} (a : Array Std.U8 n) :
    (Aeneas.Std.Array.to_slice a).val = a.val := rfl

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

/-! ### `put32`: copy a 32-byte segment into the secret buffer -/

/-- `put32`'s loop copies `src[0..32]` into `out[off .. off+32]` and leaves every byte
outside that window unchanged, tracked relative to the entry slice `out0`. -/
theorem put32_loop_spec (off : Std.Usize) (src : Array Std.U8 32#usize) (out0 : Aeneas.Std.Slice Std.U8)
    (hlen : off.val + 32 ≤ out0.length) :
    ∀ (out : Aeneas.Std.Slice Std.U8) (i : Std.Usize),
      i.val ≤ 32 → out.length = out0.length →
      (∀ k, k < off.val → out.val[k]! = out0.val[k]!) →
      (∀ j, j < i.val → out.val[off.val + j]! = src.val[j]!) →
      (∀ k, off.val + 32 ≤ k → k < out0.length → out.val[k]! = out0.val[k]!) →
      pqxdh.put32_loop out off src i
        ⦃ r => r.length = out0.length ∧
               (∀ k, k < off.val → r.val[k]! = out0.val[k]!) ∧
               (∀ j, j < 32 → r.val[off.val + j]! = src.val[j]!) ∧
               (∀ k, off.val + 32 ≤ k → k < out0.length → r.val[k]! = out0.val[k]!) ⦄ := by
  intro out i hi hl hbelow hwin habove
  unfold pqxdh.put32_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Aeneas.Std.Slice Std.U8) × Std.Usize => 32 - s.2.val)
    (inv := fun s : (Aeneas.Std.Slice Std.U8) × Std.Usize =>
      s.2.val ≤ 32 ∧ s.1.length = out0.length ∧
      (∀ k, k < off.val → s.1.val[k]! = out0.val[k]!) ∧
      (∀ j, j < s.2.val → s.1.val[off.val + j]! = src.val[j]!) ∧
      (∀ k, off.val + 32 ≤ k → k < out0.length → s.1.val[k]! = out0.val[k]!))
    (post := fun r : Aeneas.Std.Slice Std.U8 =>
      r.length = out0.length ∧
      (∀ k, k < off.val → r.val[k]! = out0.val[k]!) ∧
      (∀ j, j < 32 → r.val[off.val + j]! = src.val[j]!) ∧
      (∀ k, off.val + 32 ≤ k → k < out0.length → r.val[k]! = out0.val[k]!))
  · rintro ⟨o1, i1⟩ ⟨hi1, hl1, hb1, hw1, ha1⟩
    simp only [pqxdh.put32_loop.body, pqxdh.DH_LEN]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨i2, hi2⟩
      step as ⟨s, hs⟩
      step as ⟨i3, hi3⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · subst hs; rw [Aeneas.Std.Slice.set_length]; exact hl1
      · intro k hk
        subst hs
        have : k ≠ i2.val := by scalar_tac
        simp_lists; exact hb1 k hk
      · intro j hj
        subst hs
        by_cases hje : j = i1.val
        · subst hje; simp_lists [hi2, hv1]
        · have hjlt : j < i1.val := by scalar_tac
          have : off.val + j ≠ i2.val := by scalar_tac
          simp_lists; exact hw1 j hjlt
      · intro k hk hk2
        subst hs
        have : k ≠ i2.val := by scalar_tac
        simp_lists; exact ha1 k hk hk2
      · scalar_tac
    · rename_i hge
      refine ⟨hl1, hb1, ?_, ha1⟩
      intro j hj; exact hw1 j (by scalar_tac)
  · exact ⟨hi, hl, hbelow, hwin, habove⟩

/-- `put32 out off src` copies `src[0..32]` into `out[off .. off+32]`, preserving the rest. -/
@[step]
theorem put32_spec (off : Std.Usize) (src : Array Std.U8 32#usize) (out : Aeneas.Std.Slice Std.U8)
    (hlen : off.val + 32 ≤ out.length) :
    pqxdh.put32 out off src
      ⦃ r => r.length = out.length ∧
             (∀ k, k < off.val → r.val[k]! = out.val[k]!) ∧
             (∀ j, j < 32 → r.val[off.val + j]! = src.val[j]!) ∧
             (∀ k, off.val + 32 ≤ k → k < out.length → r.val[k]! = out.val[k]!) ⦄ := by
  unfold pqxdh.put32
  apply put32_loop_spec off src out hlen out 0#usize (by scalar_tac) rfl
    (fun k hk => rfl) (fun j hj => by scalar_tac) (fun k hk hk2 => rfl)

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

/-- **Functional correctness of the PQXDH secret input (no one-time prekey).** The 160-byte
HKDF secret input is exactly `[0xFF;32] ‖ DH1 ‖ DH2 ‖ DH3 ‖ SS` — the discontinuity prefix
followed by the four 32-byte DH/KEM segments at their offsets. This is the KDF-input layout the
AKE proof's key-derivation premise rests on (the segment ordering is the BJKS-attack-relevant
part). -/
theorem pqxdh_secret_input_spec (dh1 dh2 dh3 ss : Array Std.U8 32#usize) :
    pqxdh.pqxdh_secret_input dh1 dh2 dh3 ss
      ⦃ r => (∀ j, j < 32 → r.val[j]! = 255#u8) ∧
             (∀ j, j < 32 → r.val[32 + j]! = dh1.val[j]!) ∧
             (∀ j, j < 32 → r.val[64 + j]! = dh2.val[j]!) ∧
             (∀ j, j < 32 → r.val[96 + j]! = dh3.val[j]!) ∧
             (∀ j, j < 32 → r.val[128 + j]! = ss.val[j]!) ⦄ := by
  unfold pqxdh.pqxdh_secret_input
  apply Aeneas.Std.WP.spec_bind
    (secret_prefix_loop_spec (Array.repeat 160#usize 0#u8) 0#usize (by scalar_tac)
      (by intro j hj; scalar_tac))
  intro out1 hpre
  simp only [Aeneas.Std.Array.to_slice_mut, Aeneas.Std.lift]
  step*
  -- Every intermediate slice has length 160, so the `to_slice`/`from_slice` round-trips just
  -- shuffle `.val`; collapse them to the four `put32` results `s1, s3, s5, s7`.
  have L0 : out1.to_slice.length = 160 := by simp [Aeneas.Std.Array.to_slice]
  have L1 : s1.length = 160 := by rw [s1_post1]; exact L0
  have V1 : (out1.from_slice s1).val = s1.val := by
    apply Aeneas.Std.Array.from_slice_val; scalar_tac
  have L1' : (out1.from_slice s1).to_slice.length = 160 := by
    simp only [Aeneas.Std.Array.to_slice, V1]; scalar_tac
  have L3 : s3.length = 160 := by rw [s3_post1]; exact L1'
  have V3 : ((out1.from_slice s1).from_slice s3).val = s3.val := by
    apply Aeneas.Std.Array.from_slice_val; scalar_tac
  have L3' : ((out1.from_slice s1).from_slice s3).to_slice.length = 160 := by
    simp only [Aeneas.Std.Array.to_slice, V3]; scalar_tac
  have L5 : s5.length = 160 := by rw [s5_post1]; exact L3'
  have V5 : (((out1.from_slice s1).from_slice s3).from_slice s5).val = s5.val := by
    apply Aeneas.Std.Array.from_slice_val; scalar_tac
  have L5' : (((out1.from_slice s1).from_slice s3).from_slice s5).to_slice.length = 160 := by
    simp only [Aeneas.Std.Array.to_slice, V5]; scalar_tac
  have L7 : s7.length = 160 := by rw [s7_post1]; exact L5'
  have V7 : ((((out1.from_slice s1).from_slice s3).from_slice s5).from_slice s7).val = s7.val := by
    apply Aeneas.Std.Array.from_slice_val; scalar_tac
  simp only [Aeneas.Std.Array.to_slice, V1, V3, V5, V7] at s1_post2 s1_post3 s3_post2 s3_post3 s5_post2 s5_post3 s7_post2 s7_post3 ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [s7_post2 j (by scalar_tac), s5_post2 j (by scalar_tac), s3_post2 j (by scalar_tac),
      s1_post2 j (by scalar_tac)]
    exact hpre j hj
  · intro j hj
    rw [s7_post2 (32 + j) (by scalar_tac), s5_post2 (32 + j) (by scalar_tac),
      s3_post2 (32 + j) (by scalar_tac)]
    exact s1_post3 j hj
  · intro j hj
    rw [s7_post2 (64 + j) (by scalar_tac), s5_post2 (64 + j) (by scalar_tac)]
    exact s3_post3 j hj
  · intro j hj
    rw [s7_post2 (96 + j) (by scalar_tac)]
    exact s5_post3 j hj
  · intro j hj
    exact s7_post3 j hj

/-- The discontinuity-prefix loop for the one-time-prekey path (192-byte buffer). -/
theorem secret_prefix_with_opk_loop_spec :
    ∀ (out : Array Std.U8 192#usize) (i : Std.Usize), i.val ≤ 32 →
      (∀ j, j < i.val → out.val[j]! = 255#u8) →
      pqxdh.pqxdh_secret_input_with_opk_loop out i
        ⦃ r => ∀ j, j < 32 → r.val[j]! = 255#u8 ⦄ := by
  intro out i hi hpre
  unfold pqxdh.pqxdh_secret_input_with_opk_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 192#usize) × Std.Usize => 32 - s.2.val)
    (inv := fun s : (Array Std.U8 192#usize) × Std.Usize =>
      s.2.val ≤ 32 ∧ (∀ j, j < s.2.val → s.1.val[j]! = 255#u8))
    (post := fun r : Array Std.U8 192#usize => ∀ j, j < 32 → r.val[j]! = 255#u8)
  · rintro ⟨o1, i1⟩ ⟨hi1, hpre1⟩
    simp only [pqxdh.pqxdh_secret_input_with_opk_loop.body, pqxdh.DH_LEN]
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

/-- **Functional correctness of the PQXDH secret input with a one-time prekey.** The 192-byte
HKDF secret input is exactly `[0xFF;32] ‖ DH1 ‖ DH2 ‖ DH3 ‖ DH4 ‖ SS` — the discontinuity
prefix and the five 32-byte DH/KEM segments at their offsets. -/
theorem pqxdh_secret_input_with_opk_spec (dh1 dh2 dh3 dh4 ss : Array Std.U8 32#usize) :
    pqxdh.pqxdh_secret_input_with_opk dh1 dh2 dh3 dh4 ss
      ⦃ r => (∀ j, j < 32 → r.val[j]! = 255#u8) ∧
             (∀ j, j < 32 → r.val[32 + j]! = dh1.val[j]!) ∧
             (∀ j, j < 32 → r.val[64 + j]! = dh2.val[j]!) ∧
             (∀ j, j < 32 → r.val[96 + j]! = dh3.val[j]!) ∧
             (∀ j, j < 32 → r.val[128 + j]! = dh4.val[j]!) ∧
             (∀ j, j < 32 → r.val[160 + j]! = ss.val[j]!) ⦄ := by
  unfold pqxdh.pqxdh_secret_input_with_opk
  apply Aeneas.Std.WP.spec_bind
    (secret_prefix_with_opk_loop_spec (Array.repeat 192#usize 0#u8) 0#usize (by scalar_tac)
      (by intro j hj; scalar_tac))
  intro out1 hpre
  simp only [Aeneas.Std.Array.to_slice_mut, Aeneas.Std.lift]
  step*
  have L0 : out1.to_slice.length = 192 := by simp [Aeneas.Std.Array.to_slice]
  have L1 : s1.length = 192 := by rw [s1_post1]; exact L0
  have V1 : (out1.from_slice s1).val = s1.val := by
    apply Aeneas.Std.Array.from_slice_val; scalar_tac
  have L1' : (out1.from_slice s1).to_slice.length = 192 := by
    simp only [Aeneas.Std.Array.to_slice, V1]; scalar_tac
  have L3 : s3.length = 192 := by rw [s3_post1]; exact L1'
  have V3 : ((out1.from_slice s1).from_slice s3).val = s3.val := by
    apply Aeneas.Std.Array.from_slice_val; scalar_tac
  have L3' : ((out1.from_slice s1).from_slice s3).to_slice.length = 192 := by
    simp only [Aeneas.Std.Array.to_slice, V3]; scalar_tac
  have L5 : s5.length = 192 := by rw [s5_post1]; exact L3'
  have V5 : (((out1.from_slice s1).from_slice s3).from_slice s5).val = s5.val := by
    apply Aeneas.Std.Array.from_slice_val; scalar_tac
  have L5' : (((out1.from_slice s1).from_slice s3).from_slice s5).to_slice.length = 192 := by
    simp only [Aeneas.Std.Array.to_slice, V5]; scalar_tac
  have L7 : s7.length = 192 := by rw [s7_post1]; exact L5'
  have V7 : ((((out1.from_slice s1).from_slice s3).from_slice s5).from_slice s7).val = s7.val := by
    apply Aeneas.Std.Array.from_slice_val; scalar_tac
  have L7' : ((((out1.from_slice s1).from_slice s3).from_slice s5).from_slice s7).to_slice.length = 192 := by
    simp only [Aeneas.Std.Array.to_slice, V7]; scalar_tac
  have L9 : s9.length = 192 := by rw [s9_post1]; exact L7'
  have V9 : (((((out1.from_slice s1).from_slice s3).from_slice s5).from_slice s7).from_slice s9).val = s9.val := by
    apply Aeneas.Std.Array.from_slice_val; scalar_tac
  simp only [to_slice_val] at s1_post2 s1_post3
  simp only [to_slice_val, V1] at s3_post2 s3_post3
  simp only [to_slice_val, V3] at s5_post2 s5_post3
  simp only [to_slice_val, V5] at s7_post2 s7_post3
  simp only [to_slice_val, V7] at s9_post2 s9_post3
  simp only [V9]
  -- Drop the large nested-slice hypotheses so the clause chains run in a small context.
  clear V1 V3 V5 V7 V9 L0 L1 L1' L3 L3' L5 L5' L7 L7' L9
    s1_post1 s1_post4 s3_post1 s3_post4 s5_post1 s5_post4 s7_post1 s7_post4 s9_post1 s9_post4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [s9_post2 j (by scalar_tac), s7_post2 j (by scalar_tac), s5_post2 j (by scalar_tac),
      s3_post2 j (by scalar_tac), s1_post2 j (by scalar_tac)]
    exact hpre j hj
  · intro j hj
    rw [s9_post2 (32 + j) (by scalar_tac), s7_post2 (32 + j) (by scalar_tac),
      s5_post2 (32 + j) (by scalar_tac), s3_post2 (32 + j) (by scalar_tac)]
    exact s1_post3 j hj
  · intro j hj
    rw [s9_post2 (64 + j) (by scalar_tac), s7_post2 (64 + j) (by scalar_tac),
      s5_post2 (64 + j) (by scalar_tac)]
    exact s3_post3 j hj
  · intro j hj
    rw [s9_post2 (96 + j) (by scalar_tac), s7_post2 (96 + j) (by scalar_tac)]
    exact s5_post3 j hj
  · intro j hj
    rw [s9_post2 (128 + j) (by scalar_tac)]
    exact s7_post3 j hj
  · intro j hj
    exact s9_post3 j hj

/-! ### The associated data `AD = EncodeEC(IK_A) ‖ EncodeEC(IK_B)` -/

/-- The `associated_data` copy loop writes `a` to bytes `0..33` and `b` to bytes `33..66`. -/
theorem associated_data_loop_spec (a b : Array Std.U8 33#usize) :
    ∀ (out : Array Std.U8 66#usize) (i : Std.Usize), i.val ≤ 33 →
      (∀ j, j < i.val → out.val[j]! = a.val[j]!) →
      (∀ j, j < i.val → out.val[33 + j]! = b.val[j]!) →
      pqxdh.associated_data_loop a b out i
        ⦃ r => (∀ j, j < 33 → r.val[j]! = a.val[j]!) ∧
               (∀ j, j < 33 → r.val[33 + j]! = b.val[j]!) ⦄ := by
  intro out i hi ha hb
  unfold pqxdh.associated_data_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 66#usize) × Std.Usize => 33 - s.2.val)
    (inv := fun s : (Array Std.U8 66#usize) × Std.Usize =>
      s.2.val ≤ 33 ∧
      (∀ j, j < s.2.val → s.1.val[j]! = a.val[j]!) ∧
      (∀ j, j < s.2.val → s.1.val[33 + j]! = b.val[j]!))
    (post := fun r : Array Std.U8 66#usize =>
      (∀ j, j < 33 → r.val[j]! = a.val[j]!) ∧
      (∀ j, j < 33 → r.val[33 + j]! = b.val[j]!))
  · rintro ⟨o1, i1⟩ ⟨hi1, ha1, hb1⟩
    simp only [pqxdh.associated_data_loop.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨o2, ho2⟩
      step as ⟨v2, hv2⟩
      step as ⟨i3, hi3⟩
      step as ⟨a2, ha2⟩
      step as ⟨i4, hi4⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · scalar_tac
      · intro j hj
        subst ha2; subst ho2
        by_cases hje : j = i1.val
        · subst hje; simp_lists [hv1]
        · have : j < i1.val := by scalar_tac
          simp_lists; exact ha1 j this
      · intro j hj
        subst ha2; subst ho2
        by_cases hje : j = i1.val
        · subst hje; simp_lists [hv2]
        · have hlt2 : j < i1.val := by scalar_tac
          simp_lists; exact hb1 j hlt2
      · scalar_tac
    · rename_i hge
      refine ⟨?_, ?_⟩
      · intro j hj; apply ha1; scalar_tac
      · intro j hj; apply hb1; scalar_tac
  · exact ⟨hi, ha, hb⟩

/-- **Functional correctness of the associated data.** `associated_data` is exactly
`EncodeEC(IK_A) ‖ EncodeEC(IK_B)` — two 33-byte wire keys (each tagged `0x05`) concatenated:
byte 0 = `0x05`, bytes `1..33` = `IK_A`, byte 33 = `0x05`, bytes `34..66` = `IK_B`. This is the
identity-binding `AD` the PQXDH transcript MACs, and the exact construction the Bhargavan et al.
re-encapsulation attack targeted. -/
theorem associated_data_spec (ika ikb : Array Std.U8 32#usize) :
    pqxdh.associated_data ika ikb
      ⦃ r => r.val[0]! = pqxdh.KEY_TYPE_DJB ∧
             (∀ j, j < 32 → r.val[1 + j]! = ika.val[j]!) ∧
             r.val[33]! = pqxdh.KEY_TYPE_DJB ∧
             (∀ j, j < 32 → r.val[34 + j]! = ikb.val[j]!) ⦄ := by
  unfold pqxdh.associated_data
  apply Aeneas.Std.WP.spec_bind (encode_ec_spec ika)
  rintro a ⟨ha0, hatail⟩
  apply Aeneas.Std.WP.spec_bind (encode_ec_spec ikb)
  rintro b ⟨hb0, hbtail⟩
  apply Aeneas.Std.WP.spec_mono
    (associated_data_loop_spec a b (Array.repeat 66#usize 0#u8) 0#usize (by scalar_tac)
      (by intro j hj; scalar_tac) (by intro j hj; scalar_tac))
  rintro r ⟨hra, hrb⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hra 0 (by scalar_tac)]; exact ha0
  · intro j hj; rw [hra (1 + j) (by scalar_tac)]; exact hatail j hj
  · have h := hrb 0 (by scalar_tac); simp only [Nat.add_zero] at h; rw [h]; exact hb0
  · intro j hj
    have h := hrb (1 + j) (by scalar_tac)
    have he : 33 + (1 + j) = 34 + j := by omega
    rw [he] at h; rw [h]; exact hbtail j hj

end Pqxdh
