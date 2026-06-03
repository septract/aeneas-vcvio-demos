/-
  Crypto node — RFC 5869 functional specs for the extracted HKDF (extract / expand).

  These are **functional-correctness** results (no security game): they pin *what* the
  Aeneas-extracted `hkdf_extract` / `hkdf_expand_{64,96}` compute, in terms of the extracted
  `hmac_sha256_var`, matching RFC 5869:

  * **HKDF-Extract** (§2.2): `PRK = HMAC(salt, ikm)`.
  * **HKDF-Expand** (§2.3): `T(i) = HMAC(prk, T(i-1) ‖ info ‖ i)` with `T(0)` empty, and the
    output `OKM = T(1) ‖ T(2) [‖ T(3)]` truncated to the requested length.

  The message-builder helpers (`hkdf_t1_msg`, `hkdf_tn_msg`) assemble the per-block HMAC inputs;
  their byte-layout value specs below show the `T(i)` input buffer is exactly
  `[ prev ‖ ] info ‖ ctr` over its live prefix, and the expand specs then read the result as the
  concatenation of the chained HMAC blocks. Totality is already in `Demos/Crypto/Sha256.lean`
  (`hkdf_extract_total`, `hkdf_expand_64_total`, `hkdf_expand_96_total`); this file is the value
  layer on top of it. No security game; SHA-256-compression-as-PRF/RO remains the named floor.
-/
import Demos.Crypto.Sha256

open Aeneas Std Result

namespace Sha256

/-! ### HKDF-Extract (RFC 5869 §2.2): `PRK = HMAC(salt, ikm)` -/

/-- **HKDF-Extract functional spec.** The extracted `hkdf_extract salt ikm ikmlen` is *definitionally*
RFC 5869's `PRK = HMAC(salt, ikm)` over the variable-length HMAC: salt is the HMAC key, ikm the
message. (Upstream uses an all-zero salt by default; here salt is an explicit 32-byte argument.) -/
theorem hkdf_extract_eq (salt : Array Std.U8 32#usize) (ikm : Array Std.U8 1536#usize)
    (ikmlen : Std.Usize) :
    sha256.hkdf_extract salt ikm ikmlen = sha256.hmac_sha256_var salt ikm ikmlen := rfl

/-! ### The HKDF-Expand message builders (RFC 5869 §2.3 `T(i)` inputs) -/

/-- `hkdf_t1_msg_loop` copies `info[0..infolen]` into `m[0..infolen]`, leaving the rest unchanged. -/
theorem hkdf_t1_msg_loop_spec (info : Array Std.U8 256#usize) (infolen : Std.Usize)
    (hil : infolen.val ≤ 256) :
    ∀ (m : Array Std.U8 1536#usize) (i : Std.Usize), i.val ≤ infolen.val →
      (∀ j, j < i.val → m.val[j]! = info.val[j]!) →
      sha256.hkdf_t1_msg_loop info infolen m i
        ⦃ r => (∀ j, j < infolen.val → r.val[j]! = info.val[j]!) ∧
               (∀ k, infolen.val ≤ k → r.val[k]! = m.val[k]!) ⦄ := by
  intro m i hi hpre
  unfold sha256.hkdf_t1_msg_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 1536#usize) × Std.Usize => infolen.val - s.2.val)
    (inv := fun s : (Array Std.U8 1536#usize) × Std.Usize =>
      s.2.val ≤ infolen.val ∧
      (∀ j, j < s.2.val → s.1.val[j]! = info.val[j]!) ∧
      (∀ k, infolen.val ≤ k → s.1.val[k]! = m.val[k]!))
    (post := fun r : Array Std.U8 1536#usize =>
      (∀ j, j < infolen.val → r.val[j]! = info.val[j]!) ∧
      (∀ k, infolen.val ≤ k → r.val[k]! = m.val[k]!))
  · rintro ⟨o1, i1⟩ ⟨hi1, hpre1, hrest1⟩
    simp only [sha256.hkdf_t1_msg_loop.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨a, ha⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · scalar_tac
      · intro j hj
        subst ha
        by_cases hje : j = i1.val
        · subst hje; simp_lists [hv1]
        · have : j < i1.val := by scalar_tac
          simp_lists; exact hpre1 j this
      · intro k hk
        subst ha
        have : k ≠ i1.val := by scalar_tac
        simp_lists; exact hrest1 k hk
      · scalar_tac
    · rename_i hge
      exact ⟨fun j hj => hpre1 j (by scalar_tac), hrest1⟩
  · exact ⟨hi, hpre, fun k hk => rfl⟩

/-- **HKDF-Expand `T(1)` input layout.** `hkdf_t1_msg info infolen ctr` builds the 1536-byte
scratch buffer whose live prefix is `info[0..infolen] ‖ ctr`: byte `j < infolen` is `info[j]`,
and byte `infolen` is the counter `ctr`. This is RFC 5869's `T(1) = HMAC(PRK, info ‖ 0x01)`
input (with `T(0)` empty), the HMAC message length being `infolen + 1`. -/
theorem hkdf_t1_msg_spec (info : Array Std.U8 256#usize) (infolen : Std.Usize) (ctr : Std.U8)
    (hil : infolen.val ≤ 256) :
    sha256.hkdf_t1_msg info infolen ctr
      ⦃ r => (∀ j, j < infolen.val → r.val[j]! = info.val[j]!) ∧
             r.val[infolen.val]! = ctr ⦄ := by
  unfold sha256.hkdf_t1_msg
  apply Aeneas.Std.WP.spec_bind
    (hkdf_t1_msg_loop_spec info infolen hil (Array.repeat 1536#usize 0#u8) 0#usize
      (by scalar_tac) (by intro j hj; scalar_tac))
  rintro m1 ⟨hlo, hhi⟩
  step as ⟨a, ha⟩
  subst ha
  refine ⟨?_, ?_⟩
  · intro j hj
    have : j ≠ infolen.val := by scalar_tac
    simp_lists; exact hlo j hj
  · simp_lists

/-- `hkdf_tn_msg_loop0` copies `prev[0..32]` into `m[0..32]`, leaving the rest unchanged. -/
theorem hkdf_tn_msg_loop0_spec (prev : Array Std.U8 32#usize) :
    ∀ (m : Array Std.U8 1536#usize) (i : Std.Usize), i.val ≤ 32 →
      (∀ j, j < i.val → m.val[j]! = prev.val[j]!) →
      sha256.hkdf_tn_msg_loop0 prev m i
        ⦃ r => (∀ j, j < 32 → r.val[j]! = prev.val[j]!) ∧
               (∀ k, 32 ≤ k → r.val[k]! = m.val[k]!) ⦄ := by
  intro m i hi hpre
  unfold sha256.hkdf_tn_msg_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 1536#usize) × Std.Usize => 32 - s.2.val)
    (inv := fun s : (Array Std.U8 1536#usize) × Std.Usize =>
      s.2.val ≤ 32 ∧
      (∀ j, j < s.2.val → s.1.val[j]! = prev.val[j]!) ∧
      (∀ k, 32 ≤ k → s.1.val[k]! = m.val[k]!))
    (post := fun r : Array Std.U8 1536#usize =>
      (∀ j, j < 32 → r.val[j]! = prev.val[j]!) ∧
      (∀ k, 32 ≤ k → r.val[k]! = m.val[k]!))
  · rintro ⟨o1, i1⟩ ⟨hi1, hpre1, hrest1⟩
    simp only [sha256.hkdf_tn_msg_loop0.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨a, ha⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · scalar_tac
      · intro j hj
        subst ha
        by_cases hje : j = i1.val
        · subst hje; simp_lists [hv1]
        · have : j < i1.val := by scalar_tac
          simp_lists; exact hpre1 j this
      · intro k hk
        subst ha
        have : k ≠ i1.val := by scalar_tac
        simp_lists; exact hrest1 k hk
      · scalar_tac
    · rename_i hge
      exact ⟨fun j hj => hpre1 j (by scalar_tac), hrest1⟩
  · exact ⟨hi, hpre, fun k hk => rfl⟩

/-- `hkdf_tn_msg_loop1` copies `info[0..infolen]` into `m[32 .. 32+infolen]`, preserving the
first 32 bytes and `m[32+infolen ..]`. -/
theorem hkdf_tn_msg_loop1_spec (info : Array Std.U8 256#usize) (infolen : Std.Usize)
    (hil : infolen.val ≤ 256) :
    ∀ (m : Array Std.U8 1536#usize) (i : Std.Usize), i.val ≤ infolen.val →
      (∀ j, j < i.val → m.val[32 + j]! = info.val[j]!) →
      sha256.hkdf_tn_msg_loop1 info infolen m i
        ⦃ r => (∀ k, k < 32 → r.val[k]! = m.val[k]!) ∧
               (∀ j, j < infolen.val → r.val[32 + j]! = info.val[j]!) ∧
               (∀ k, 32 + infolen.val ≤ k → r.val[k]! = m.val[k]!) ⦄ := by
  intro m i hi hpre
  unfold sha256.hkdf_tn_msg_loop1
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 1536#usize) × Std.Usize => infolen.val - s.2.val)
    (inv := fun s : (Array Std.U8 1536#usize) × Std.Usize =>
      s.2.val ≤ infolen.val ∧
      (∀ k, k < 32 → s.1.val[k]! = m.val[k]!) ∧
      (∀ j, j < s.2.val → s.1.val[32 + j]! = info.val[j]!) ∧
      (∀ k, 32 + infolen.val ≤ k → s.1.val[k]! = m.val[k]!))
    (post := fun r : Array Std.U8 1536#usize =>
      (∀ k, k < 32 → r.val[k]! = m.val[k]!) ∧
      (∀ j, j < infolen.val → r.val[32 + j]! = info.val[j]!) ∧
      (∀ k, 32 + infolen.val ≤ k → r.val[k]! = m.val[k]!))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlo1, hmid1, hhi1⟩
    simp only [sha256.hkdf_tn_msg_loop1.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨off, hoff⟩
      step as ⟨a, ha⟩
      step as ⟨i3, hi3⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · intro k hk
        subst ha
        have : k ≠ off.val := by scalar_tac
        simp_lists; exact hlo1 k hk
      · intro j hj
        subst ha
        by_cases hje : j = i1.val
        · subst hje; simp_lists [hv1, hoff]
        · have : j < i1.val := by scalar_tac
          have : 32 + j ≠ off.val := by scalar_tac
          simp_lists; exact hmid1 j (by scalar_tac)
      · intro k hk
        subst ha
        have : k ≠ off.val := by scalar_tac
        simp_lists; exact hhi1 k hk
      · scalar_tac
    · rename_i hge
      exact ⟨hlo1, fun j hj => hmid1 j (by scalar_tac), hhi1⟩
  · exact ⟨hi, fun k hk => rfl, hpre, fun k hk => rfl⟩

/-- **HKDF-Expand `T(i)` input layout** (`i ≥ 2`). `hkdf_tn_msg prev info infolen ctr` builds the
1536-byte scratch buffer whose live prefix is `prev[0..32] ‖ info[0..infolen] ‖ ctr`: byte `j < 32`
is the previous block `prev[j]`, byte `32 + j` (`j < infolen`) is `info[j]`, and byte `32 + infolen`
is the counter `ctr`. This is RFC 5869's `T(i) = HMAC(PRK, T(i-1) ‖ info ‖ i)` input — the
HMAC message length being `32 + infolen + 1`. -/
theorem hkdf_tn_msg_spec (prev : Array Std.U8 32#usize) (info : Array Std.U8 256#usize)
    (infolen : Std.Usize) (ctr : Std.U8) (hil : infolen.val ≤ 256) :
    sha256.hkdf_tn_msg prev info infolen ctr
      ⦃ r => (∀ j, j < 32 → r.val[j]! = prev.val[j]!) ∧
             (∀ j, j < infolen.val → r.val[32 + j]! = info.val[j]!) ∧
             r.val[32 + infolen.val]! = ctr ⦄ := by
  unfold sha256.hkdf_tn_msg
  apply Aeneas.Std.WP.spec_bind
    (hkdf_tn_msg_loop0_spec prev (Array.repeat 1536#usize 0#u8) 0#usize
      (by scalar_tac) (by intro j hj; scalar_tac))
  rintro m1 ⟨hlo0, hhi0⟩
  apply Aeneas.Std.WP.spec_bind
    (hkdf_tn_msg_loop1_spec info infolen hil m1 0#usize (by scalar_tac) (by intro j hj; scalar_tac))
  rintro m2 ⟨hlo1, hmid1, hhi1⟩
  step as ⟨off, hoff⟩
  step as ⟨a, ha⟩
  subst ha
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have : j ≠ off.val := by scalar_tac
    simp_lists
    rw [hlo1 j (by scalar_tac), hlo0 j hj]
  · intro j hj
    have : 32 + j ≠ off.val := by scalar_tac
    simp_lists
    exact hmid1 j hj
  · have : off.val = 32 + infolen.val := by scalar_tac
    simp_lists [hoff]

/-! ### HKDF-Expand (RFC 5869 §2.3): `OKM = T(1) ‖ T(2) [‖ T(3)]` -/

/-- `hkdf_expand_64_loop` interleaves `t1`/`t2` into `okm[0..32]`/`okm[32..64]`. -/
theorem hkdf_expand_64_loop_spec (t1 t2 : Array Std.U8 32#usize) :
    ∀ (okm : Array Std.U8 64#usize) (i : Std.Usize), i.val ≤ 32 →
      (∀ j, j < i.val → okm.val[j]! = t1.val[j]!) →
      (∀ j, j < i.val → okm.val[32 + j]! = t2.val[j]!) →
      sha256.hkdf_expand_64_loop t1 t2 okm i
        ⦃ r => (∀ j, j < 32 → r.val[j]! = t1.val[j]!) ∧
               (∀ j, j < 32 → r.val[32 + j]! = t2.val[j]!) ⦄ := by
  intro okm i hi hp1 hp2
  unfold sha256.hkdf_expand_64_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 64#usize) × Std.Usize => 32 - s.2.val)
    (inv := fun s : (Array Std.U8 64#usize) × Std.Usize =>
      s.2.val ≤ 32 ∧
      (∀ j, j < s.2.val → s.1.val[j]! = t1.val[j]!) ∧
      (∀ j, j < s.2.val → s.1.val[32 + j]! = t2.val[j]!))
    (post := fun r : Array Std.U8 64#usize =>
      (∀ j, j < 32 → r.val[j]! = t1.val[j]!) ∧
      (∀ j, j < 32 → r.val[32 + j]! = t2.val[j]!))
  · rintro ⟨o1, i1⟩ ⟨hi1, hpa, hpb⟩
    simp only [sha256.hkdf_expand_64_loop.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨okm1, ho1⟩
      step as ⟨v2, hv2⟩
      step as ⟨off, hoff⟩
      step as ⟨a, ha⟩
      step as ⟨i4, hi4⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · scalar_tac
      · intro j hj
        subst ha ho1
        by_cases hje : j = i1.val
        · subst hje
          have : i1.val ≠ off.val := by scalar_tac
          simp_lists [hv1]
        · have hlt' : j < i1.val := by scalar_tac
          have : j ≠ off.val := by scalar_tac
          have : j ≠ i1.val := by scalar_tac
          simp_lists; exact hpa j hlt'
      · intro j hj
        subst ha ho1
        by_cases hje : j = i1.val
        · subst hje; simp_lists [hv2, hoff]
        · have hlt' : j < i1.val := by scalar_tac
          have : 32 + j ≠ off.val := by scalar_tac
          have : 32 + j ≠ i1.val := by scalar_tac
          simp_lists; exact hpb j hlt'
      · scalar_tac
    · rename_i hge
      exact ⟨fun j hj => hpa j (by scalar_tac), fun j hj => hpb j (by scalar_tac)⟩
  · exact ⟨hi, hp1, hp2⟩

/-- **HKDF-Expand (64-byte) functional spec — RFC 5869 §2.3.** For `infolen ≤ 256`,
`hkdf_expand_64 prk info infolen` produces `OKM = T(1) ‖ T(2)` where each `T(i)` is the
HMAC of `prk` over the `hkdf_{t1,tn}_msg` input buffer for that block. Concretely there exist
message buffers `m1, m2` and blocks `t1, t2` such that:

* `m1` is the `T(1)` input `info ‖ 0x01` (so `m1[j]=info[j]` for `j<infolen`, `m1[infolen]=1`);
* `t1 = HMAC(prk, m1, infolen+1)`;
* `m2` is the `T(2)` input `t1 ‖ info ‖ 0x02`;
* `t2 = HMAC(prk, m2, 32+infolen+1)`;
* the output is `okm[0..32] = t1`, `okm[32..64] = t2`.

This pins the extracted code as exactly the RFC 5869 `T(i) = HMAC(prk, T(i-1)‖info‖i)` chaining
truncated to 64 bytes — the `KDF_AUTH` block the SPQR chain step consumes. No security game. -/
theorem hkdf_expand_64_spec (prk : Array Std.U8 32#usize) (info : Array Std.U8 256#usize)
    (infolen : Std.Usize) (hil : infolen.val ≤ 256) :
    sha256.hkdf_expand_64 prk info infolen
      ⦃ r => ∃ (m1 m2 : Array Std.U8 1536#usize) (t1 t2 : Array Std.U8 32#usize)
               (len1 len2 : Std.Usize),
          len1.val = infolen.val + 1 ∧
          (∀ j, j < infolen.val → m1.val[j]! = info.val[j]!) ∧
          m1.val[infolen.val]! = 1#u8 ∧
          sha256.hmac_sha256_var prk m1 len1 = ok t1 ∧
          len2.val = 32 + infolen.val + 1 ∧
          (∀ j, j < 32 → m2.val[j]! = t1.val[j]!) ∧
          (∀ j, j < infolen.val → m2.val[32 + j]! = info.val[j]!) ∧
          m2.val[32 + infolen.val]! = 2#u8 ∧
          sha256.hmac_sha256_var prk m2 len2 = ok t2 ∧
          (∀ j, j < 32 → r.val[j]! = t1.val[j]!) ∧
          (∀ j, j < 32 → r.val[32 + j]! = t2.val[j]!) ⦄ := by
  unfold sha256.hkdf_expand_64
  -- m1 = T(1) input
  apply Aeneas.Std.WP.spec_bind (hkdf_t1_msg_spec info infolen 1#u8 hil)
  rintro m1 ⟨hm1_lo, hm1_ctr⟩
  step as ⟨len1, hlen1⟩
  -- t1 = HMAC(prk, m1, len1)
  have hlen1le : len1.val ≤ 1536 := by scalar_tac
  obtain ⟨t1w, ht1w, -⟩ := Aeneas.Std.WP.spec_imp_exists (hmac_sha256_var_total prk m1 len1 hlen1le)
  apply Aeneas.Std.WP.spec_bind
    (Aeneas.Std.WP.exists_imp_spec (m := sha256.hmac_sha256_var prk m1 len1)
      (P := fun t1' => sha256.hmac_sha256_var prk m1 len1 = ok t1') ⟨t1w, ht1w, ht1w⟩)
  rintro t1 ht1_eq
  -- m2 = T(2) input
  apply Aeneas.Std.WP.spec_bind (hkdf_tn_msg_spec t1 info infolen 2#u8 hil)
  rintro m2 ⟨hm2_lo, hm2_mid, hm2_ctr⟩
  step as ⟨off, hoff⟩
  step as ⟨len2, hlen2⟩
  -- t2 = HMAC(prk, m2, len2)
  have hlen2le : len2.val ≤ 1536 := by scalar_tac
  obtain ⟨t2w, ht2w, -⟩ := Aeneas.Std.WP.spec_imp_exists (hmac_sha256_var_total prk m2 len2 hlen2le)
  apply Aeneas.Std.WP.spec_bind
    (Aeneas.Std.WP.exists_imp_spec (m := sha256.hmac_sha256_var prk m2 len2)
      (P := fun t2' => sha256.hmac_sha256_var prk m2 len2 = ok t2') ⟨t2w, ht2w, ht2w⟩)
  rintro t2 ht2_eq
  -- the interleave loop
  apply Aeneas.Std.WP.spec_mono
    (hkdf_expand_64_loop_spec t1 t2 (Array.repeat 64#usize 0#u8) 0#usize (by scalar_tac)
      (by intro j hj; scalar_tac) (by intro j hj; scalar_tac))
  rintro okm ⟨hok1, hok2⟩
  exact ⟨m1, m2, t1, t2, len1, len2, hlen1, hm1_lo, hm1_ctr, ht1_eq, by scalar_tac,
    hm2_lo, hm2_mid, hm2_ctr, ht2_eq, hok1, hok2⟩

/-- `hkdf_expand_96_loop` interleaves `t1`/`t2`/`t3` into the three 32-byte segments. -/
theorem hkdf_expand_96_loop_spec (t1 t2 t3 : Array Std.U8 32#usize) :
    ∀ (okm : Array Std.U8 96#usize) (i : Std.Usize), i.val ≤ 32 →
      (∀ j, j < i.val → okm.val[j]! = t1.val[j]!) →
      (∀ j, j < i.val → okm.val[32 + j]! = t2.val[j]!) →
      (∀ j, j < i.val → okm.val[64 + j]! = t3.val[j]!) →
      sha256.hkdf_expand_96_loop t1 t2 t3 okm i
        ⦃ r => (∀ j, j < 32 → r.val[j]! = t1.val[j]!) ∧
               (∀ j, j < 32 → r.val[32 + j]! = t2.val[j]!) ∧
               (∀ j, j < 32 → r.val[64 + j]! = t3.val[j]!) ⦄ := by
  intro okm i hi hp1 hp2 hp3
  unfold sha256.hkdf_expand_96_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 96#usize) × Std.Usize => 32 - s.2.val)
    (inv := fun s : (Array Std.U8 96#usize) × Std.Usize =>
      s.2.val ≤ 32 ∧
      (∀ j, j < s.2.val → s.1.val[j]! = t1.val[j]!) ∧
      (∀ j, j < s.2.val → s.1.val[32 + j]! = t2.val[j]!) ∧
      (∀ j, j < s.2.val → s.1.val[64 + j]! = t3.val[j]!))
    (post := fun r : Array Std.U8 96#usize =>
      (∀ j, j < 32 → r.val[j]! = t1.val[j]!) ∧
      (∀ j, j < 32 → r.val[32 + j]! = t2.val[j]!) ∧
      (∀ j, j < 32 → r.val[64 + j]! = t3.val[j]!))
  · rintro ⟨o1, i1⟩ ⟨hi1, hpa, hpb, hpc⟩
    simp only [sha256.hkdf_expand_96_loop.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨okm1, ho1⟩
      step as ⟨v2, hv2⟩
      step as ⟨off2, hoff2⟩
      step as ⟨okm2, ho2⟩
      step as ⟨v3, hv3⟩
      step as ⟨off3, hoff3⟩
      step as ⟨a, ha⟩
      step as ⟨i6, hi6⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · intro j hj
        subst ha ho2 ho1
        by_cases hje : j = i1.val
        · subst hje
          have : i1.val ≠ off3.val := by scalar_tac
          have : i1.val ≠ off2.val := by scalar_tac
          simp_lists [hv1]
        · have hlt' : j < i1.val := by scalar_tac
          have : j ≠ off3.val := by scalar_tac
          have : j ≠ off2.val := by scalar_tac
          have : j ≠ i1.val := by scalar_tac
          simp_lists; exact hpa j hlt'
      · intro j hj
        subst ha ho2 ho1
        by_cases hje : j = i1.val
        · subst hje
          have : 32 + i1.val ≠ off3.val := by scalar_tac
          simp_lists [hv2, hoff2]
        · have hlt' : j < i1.val := by scalar_tac
          have : 32 + j ≠ off3.val := by scalar_tac
          have : 32 + j ≠ off2.val := by scalar_tac
          have : 32 + j ≠ i1.val := by scalar_tac
          simp_lists; exact hpb j hlt'
      · intro j hj
        subst ha ho2 ho1
        by_cases hje : j = i1.val
        · subst hje; simp_lists [hv3, hoff3]
        · have hlt' : j < i1.val := by scalar_tac
          have : 64 + j ≠ off3.val := by scalar_tac
          have : 64 + j ≠ off2.val := by scalar_tac
          have : 64 + j ≠ i1.val := by scalar_tac
          simp_lists; exact hpc j hlt'
      · scalar_tac
    · rename_i hge
      exact ⟨fun j hj => hpa j (by scalar_tac), fun j hj => hpb j (by scalar_tac),
        fun j hj => hpc j (by scalar_tac)⟩
  · exact ⟨hi, hp1, hp2, hp3⟩

/-- **HKDF-Expand (96-byte) functional spec — RFC 5869 §2.3.** For `infolen ≤ 256`,
`hkdf_expand_96 prk info infolen` produces `OKM = T(1) ‖ T(2) ‖ T(3)` where each `T(i)` is the
HMAC of `prk` over the `hkdf_{t1,tn}_msg` input buffer for that block:

* `m1` is `info ‖ 0x01`, `t1 = HMAC(prk, m1, infolen+1)`;
* `m2` is `t1 ‖ info ‖ 0x02`, `t2 = HMAC(prk, m2, 32+infolen+1)`;
* `m3` is `t2 ‖ info ‖ 0x03`, `t3 = HMAC(prk, m3, 32+infolen+1)`;
* the output is `okm[0..32]=t1`, `okm[32..64]=t2`, `okm[64..96]=t3`.

This pins the extracted code as exactly RFC 5869's `T(i) = HMAC(prk, T(i-1)‖info‖i)` chaining
truncated to 96 bytes — the block PQXDH's `derive` (root‖chain‖pqr) consumes. No security game. -/
theorem hkdf_expand_96_spec (prk : Array Std.U8 32#usize) (info : Array Std.U8 256#usize)
    (infolen : Std.Usize) (hil : infolen.val ≤ 256) :
    sha256.hkdf_expand_96 prk info infolen
      ⦃ r => ∃ (m1 m2 m3 : Array Std.U8 1536#usize) (t1 t2 t3 : Array Std.U8 32#usize)
               (len1 len2 len3 : Std.Usize),
          len1.val = infolen.val + 1 ∧
          (∀ j, j < infolen.val → m1.val[j]! = info.val[j]!) ∧
          m1.val[infolen.val]! = 1#u8 ∧
          sha256.hmac_sha256_var prk m1 len1 = ok t1 ∧
          len2.val = 32 + infolen.val + 1 ∧
          (∀ j, j < 32 → m2.val[j]! = t1.val[j]!) ∧
          (∀ j, j < infolen.val → m2.val[32 + j]! = info.val[j]!) ∧
          m2.val[32 + infolen.val]! = 2#u8 ∧
          sha256.hmac_sha256_var prk m2 len2 = ok t2 ∧
          len3.val = 32 + infolen.val + 1 ∧
          (∀ j, j < 32 → m3.val[j]! = t2.val[j]!) ∧
          (∀ j, j < infolen.val → m3.val[32 + j]! = info.val[j]!) ∧
          m3.val[32 + infolen.val]! = 3#u8 ∧
          sha256.hmac_sha256_var prk m3 len3 = ok t3 ∧
          (∀ j, j < 32 → r.val[j]! = t1.val[j]!) ∧
          (∀ j, j < 32 → r.val[32 + j]! = t2.val[j]!) ∧
          (∀ j, j < 32 → r.val[64 + j]! = t3.val[j]!) ⦄ := by
  unfold sha256.hkdf_expand_96
  -- m1 = T(1) input
  apply Aeneas.Std.WP.spec_bind (hkdf_t1_msg_spec info infolen 1#u8 hil)
  rintro m1 ⟨hm1_lo, hm1_ctr⟩
  step as ⟨len1, hlen1⟩
  have hlen1le : len1.val ≤ 1536 := by scalar_tac
  obtain ⟨t1w, ht1w, -⟩ := Aeneas.Std.WP.spec_imp_exists (hmac_sha256_var_total prk m1 len1 hlen1le)
  apply Aeneas.Std.WP.spec_bind
    (Aeneas.Std.WP.exists_imp_spec (m := sha256.hmac_sha256_var prk m1 len1)
      (P := fun t1' => sha256.hmac_sha256_var prk m1 len1 = ok t1') ⟨t1w, ht1w, ht1w⟩)
  rintro t1 ht1_eq
  -- m2 = T(2) input
  apply Aeneas.Std.WP.spec_bind (hkdf_tn_msg_spec t1 info infolen 2#u8 hil)
  rintro m2 ⟨hm2_lo, hm2_mid, hm2_ctr⟩
  step as ⟨off2, hoff2⟩
  step as ⟨len2, hlen2⟩
  have hlen2le : len2.val ≤ 1536 := by scalar_tac
  obtain ⟨t2w, ht2w, -⟩ := Aeneas.Std.WP.spec_imp_exists (hmac_sha256_var_total prk m2 len2 hlen2le)
  apply Aeneas.Std.WP.spec_bind
    (Aeneas.Std.WP.exists_imp_spec (m := sha256.hmac_sha256_var prk m2 len2)
      (P := fun t2' => sha256.hmac_sha256_var prk m2 len2 = ok t2') ⟨t2w, ht2w, ht2w⟩)
  rintro t2 ht2_eq
  -- m3 = T(3) input
  apply Aeneas.Std.WP.spec_bind (hkdf_tn_msg_spec t2 info infolen 3#u8 hil)
  rintro m3 ⟨hm3_lo, hm3_mid, hm3_ctr⟩
  step as ⟨off3, hoff3⟩
  -- t3 = HMAC(prk, m3, len3) where len3 = i1+1 = 32+infolen+1
  have hlen3le : off3.val ≤ 1536 := by scalar_tac
  obtain ⟨t3w, ht3w, -⟩ := Aeneas.Std.WP.spec_imp_exists (hmac_sha256_var_total prk m3 off3 hlen3le)
  apply Aeneas.Std.WP.spec_bind
    (Aeneas.Std.WP.exists_imp_spec (m := sha256.hmac_sha256_var prk m3 off3)
      (P := fun t3' => sha256.hmac_sha256_var prk m3 off3 = ok t3') ⟨t3w, ht3w, ht3w⟩)
  rintro t3 ht3_eq
  -- the interleave loop
  apply Aeneas.Std.WP.spec_mono
    (hkdf_expand_96_loop_spec t1 t2 t3 (Array.repeat 96#usize 0#u8) 0#usize (by scalar_tac)
      (by intro j hj; scalar_tac) (by intro j hj; scalar_tac) (by intro j hj; scalar_tac))
  rintro okm ⟨hok1, hok2, hok3⟩
  exact ⟨m1, m2, m3, t1, t2, t3, len1, len2, off3, hlen1, hm1_lo, hm1_ctr, ht1_eq,
    by scalar_tac, hm2_lo, hm2_mid, hm2_ctr, ht2_eq, by scalar_tac,
    hm3_lo, hm3_mid, hm3_ctr, ht3_eq, hok1, hok2, hok3⟩

end Sha256
