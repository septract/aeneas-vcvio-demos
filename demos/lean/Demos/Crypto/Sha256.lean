/-
  Crypto node — value adequacy of the extracted SHA-256 compression / variable-length hash.

  `sha256.rs` is the Aeneas extraction of a faithful FIPS 180-4 SHA-256: the
  message-schedule expansion, the 64 ARX rounds, and the Davies–Meyer feed-forward.
  It is the hash primitive under libsignal's HMAC-SHA256 / HKDF (`crypto.rs` uses
  `sha2::Sha256`). Like the ratchet demo's ChaCha20 node, the content is genuine
  cryptographic arithmetic, so the value-adequacy obligation is **totality**: the
  extracted code never panics (every schedule index `w[t-15]`/`w[t-2]` and round
  index `K[t]`/`w[t]` is in bounds) or overflows, hence it denotes a total pure
  function. Its compression function being a PRF / random oracle is the standard
  named assumption; HMAC and HKDF are built structurally on top (`Hmac.lean`).
-/
import Demos.Extracted.Sha256

open Aeneas Std Result

namespace Sha256

/-- Loading a big-endian word from four bytes never fails (shifts by 8/16/24 < 32). -/
@[step]
theorem load_be_total (b0 b1 b2 b3 : Std.U8) :
    sha256.load_be b0 b1 b2 b3 ⦃ fun _ => True ⦄ := by
  unfold sha256.load_be
  step*

/-- The message-schedule copy loop (`W[0..16] = block words`) never fails: it reads
`block[4t .. 4t+3]` for `t < 16` (so `4t+3 ≤ 63 < 64`) and writes `W[t]`. -/
@[step]
theorem compress_loop0_ok (block : Array Std.U8 64#usize) :
    ∀ (w : Array Std.U32 64#usize) (t : Std.Usize), t.val ≤ 16 →
      sha256.sha256_compress_loop0 block w t ⦃ fun _ => True ⦄ := by
  intro w t ht
  unfold sha256.sha256_compress_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U32 64#usize) × Std.Usize => 16 - s.2.val)
    (inv := fun s : (Array Std.U32 64#usize) × Std.Usize => s.2.val ≤ 16)
    (post := fun _ => True)
  · rintro ⟨w1, t1⟩ hinv
    simp only [sha256.sha256_compress_loop0.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact ht

/-- The message-schedule expansion loop (`W[16..64]`) never fails: for `16 ≤ t < 64`
the reads `W[t-15]`, `W[t-2]`, `W[t-7]`, `W[t-16]` are all in `[0,64)` (no underflow,
in bounds), the rotates/shifts are by constants `< 32`, and the writes hit `W[t]`. -/
@[step]
theorem compress_loop1_ok :
    ∀ (w : Array Std.U32 64#usize) (t : Std.Usize), 16 ≤ t.val → t.val ≤ 64 →
      sha256.sha256_compress_loop1 w t ⦃ fun _ => True ⦄ := by
  intro w t ht0 ht1
  unfold sha256.sha256_compress_loop1
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U32 64#usize) × Std.Usize => 64 - s.2.val)
    (inv := fun s : (Array Std.U32 64#usize) × Std.Usize => 16 ≤ s.2.val ∧ s.2.val ≤ 64)
    (post := fun _ => True)
  · rintro ⟨w1, t1⟩ ⟨hlo, hhi⟩
    simp only [sha256.sha256_compress_loop1.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact ⟨ht0, ht1⟩

/-- The 64 compression rounds never fail: each reads `K[t]`/`W[t]` for `t < 64` and
does only rotates/shifts/`wrapping_add`/bitwise ops over the eight working words. -/
@[step]
theorem compress_loop2_ok (w : Array Std.U32 64#usize) :
    ∀ (a b c d e f g h : Std.U32) (t : Std.Usize), t.val ≤ 64 →
      sha256.sha256_compress_loop2 w a b c d e f g h t ⦃ fun _ => True ⦄ := by
  intro a b c d e f g h t ht
  unfold sha256.sha256_compress_loop2
  apply Std.loop.spec_decr_nat
    (measure := fun s : Std.U32 × Std.U32 × Std.U32 × Std.U32 × Std.U32 × Std.U32 ×
      Std.U32 × Std.U32 × Std.Usize => 64 - s.2.2.2.2.2.2.2.2.val)
    (inv := fun s : Std.U32 × Std.U32 × Std.U32 × Std.U32 × Std.U32 × Std.U32 ×
      Std.U32 × Std.U32 × Std.Usize => s.2.2.2.2.2.2.2.2.val ≤ 64)
    (post := fun _ => True)
  · rintro ⟨a1, b1, c1, d1, e1, f1, g1, h1, t1⟩ hinv
    simp only [sha256.sha256_compress_loop2.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact ht

/-- The feed-forward loop (`out[i] = state[i] + work[i]`, `i < 8`) never fails. -/
@[step]
theorem compress_loop3_ok (state work_final : Array Std.U32 8#usize) :
    ∀ (out : Array Std.U32 8#usize) (i : Std.Usize), i.val ≤ 8 →
      sha256.sha256_compress_loop3 state work_final out i ⦃ fun _ => True ⦄ := by
  intro out i hi
  unfold sha256.sha256_compress_loop3
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U32 8#usize) × Std.Usize => 8 - s.2.val)
    (inv := fun s : (Array Std.U32 8#usize) × Std.Usize => s.2.val ≤ 8)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [sha256.sha256_compress_loop3.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

/-- **Value adequacy of the compression function.** `sha256_compress` is total —
the headline ε = 0 lifting obligation for the SHA-256 node. We step through the four
proved-total loops and the scalar `a..h` working-variable extraction of the standard
FIPS presentation, destructuring the round loop's 8-tuple result before the
feed-forward loop. -/
@[step]
theorem sha256_compress_total (state : Array Std.U32 8#usize) (block : Array Std.U8 64#usize) :
    sha256.sha256_compress state block ⦃ fun _ => True ⦄ := by
  unfold sha256.sha256_compress
  step as ⟨w1, _⟩
  step as ⟨w2, _⟩
  step as ⟨a, _⟩
  step as ⟨b, _⟩
  step as ⟨c, _⟩
  step as ⟨d, _⟩
  step as ⟨e, _⟩
  step as ⟨ff, _⟩
  step as ⟨gg, _⟩
  step as ⟨hh, _⟩
  step as ⟨tup, _⟩
  obtain ⟨a1, b1, c1, d1, e1, f1, g1, h1⟩ := tup
  step*

/-- Serializing the state to a 32-byte digest never fails. -/
@[step]
theorem state_to_bytes_total (state : Array Std.U32 8#usize) :
    sha256.state_to_bytes state ⦃ fun _ => True ⦄ := by
  unfold sha256.state_to_bytes sha256.state_to_bytes_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 32#usize) × Std.Usize => 8 - s.2.val)
    (inv := fun s : (Array Std.U8 32#usize) × Std.Usize => s.2.val ≤ 8)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [sha256.state_to_bytes_loop.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · scalar_tac

/-! ### HMAC-SHA256 (two-pass) -/

/-- The `K0 ⊕ pad` block builder never fails (writes `out[0..32]`). -/
@[step]
theorem key_pad_block_loop_ok (key : Array Std.U8 32#usize) (pad : Std.U8) :
    ∀ (out : Array Std.U8 64#usize) (i : Std.Usize), i.val ≤ 32 →
      sha256.key_pad_block_loop key pad out i ⦃ fun _ => True ⦄ := by
  intro out i hi
  unfold sha256.key_pad_block_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 64#usize) × Std.Usize => 32 - s.2.val)
    (inv := fun s : (Array Std.U8 64#usize) × Std.Usize => s.2.val ≤ 32)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [sha256.key_pad_block_loop.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

@[step]
theorem key_pad_block_total (key : Array Std.U8 32#usize) (pad : Std.U8) :
    sha256.key_pad_block key pad ⦃ fun _ => True ⦄ := by
  unfold sha256.key_pad_block
  apply key_pad_block_loop_ok; scalar_tac

/-! ### HMAC byte layout: `key_pad_block` writes `(key ⊕ pad) ‖ pad^32`

The `K0 ⊕ pad` block builder writes `out[i] = key[i] ⊕ pad` for `i < 32` and leaves
`out[i] = pad` for `32 ≤ i < 64` (the buffer is initialised to `pad`, since the 32-byte
key is zero-padded to the 64-byte block size before the XOR — RFC 2104 / FIPS 198 `K0`).
This is the byte shape the HMAC two-pass equation `H((K0⊕opad)‖H((K0⊕ipad)‖m))` rests on. -/
theorem key_pad_block_loop_spec (key : Array Std.U8 32#usize) (pad : Std.U8) :
    ∀ (out : Array Std.U8 64#usize) (i : Std.Usize), i.val ≤ 32 →
      (∀ j, j < i.val → out.val[j]! = key.val[j]! ^^^ pad) →
      (∀ k, 32 ≤ k → k < 64 → out.val[k]! = pad) →
      sha256.key_pad_block_loop key pad out i
        ⦃ r => (∀ j, j < 32 → r.val[j]! = key.val[j]! ^^^ pad) ∧
               (∀ k, 32 ≤ k → k < 64 → r.val[k]! = pad) ⦄ := by
  intro out i hi hlo hhi
  unfold sha256.key_pad_block_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 64#usize) × Std.Usize => 32 - s.2.val)
    (inv := fun s : (Array Std.U8 64#usize) × Std.Usize =>
      s.2.val ≤ 32 ∧
      (∀ j, j < s.2.val → s.1.val[j]! = key.val[j]! ^^^ pad) ∧
      (∀ k, 32 ≤ k → k < 64 → s.1.val[k]! = pad))
    (post := fun r : Array Std.U8 64#usize =>
      (∀ j, j < 32 → r.val[j]! = key.val[j]! ^^^ pad) ∧
      (∀ k, 32 ≤ k → k < 64 → r.val[k]! = pad))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlo1, hhi1⟩
    simp only [sha256.key_pad_block_loop.body]
    split
    · rename_i hlt
      step as ⟨v1, hv1⟩
      step as ⟨v2, hv2⟩
      step as ⟨a, ha⟩
      step as ⟨i3, hi3⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · scalar_tac
      · intro j hj
        subst ha
        by_cases hje : j = i1.val
        · subst hje; simp_lists; rw [← hv1]; scalar_tac
        · have : j < i1.val := by scalar_tac
          simp_lists; exact hlo1 j this
      · intro k hk hk2
        subst ha
        have : k ≠ i1.val := by scalar_tac
        simp_lists; exact hhi1 k hk hk2
      · scalar_tac
    · rename_i hge
      exact ⟨fun j hj => hlo1 j (by scalar_tac), hhi1⟩
  · exact ⟨hi, hlo, hhi⟩

/-- **HMAC byte layout — the padded-key block `K0 ⊕ pad`.** `key_pad_block key pad` produces
the 64-byte block whose first 32 bytes are `key[i] ⊕ pad` and whose trailing 32 bytes are `pad`
(the 32-byte key zero-padded to the 64-byte block, then XORed with `pad`). With `pad = 0x36`
this is `K0 ⊕ ipad`; with `pad = 0x5c` it is `K0 ⊕ opad` — the two operands of HMAC's two passes. -/
theorem key_pad_block_spec (key : Array Std.U8 32#usize) (pad : Std.U8) :
    sha256.key_pad_block key pad
      ⦃ r => (∀ j, j < 32 → r.val[j]! = key.val[j]! ^^^ pad) ∧
             (∀ k, 32 ≤ k → k < 64 → r.val[k]! = pad) ⦄ := by
  unfold sha256.key_pad_block
  apply key_pad_block_loop_spec key pad (Array.repeat 64#usize pad) 0#usize (by scalar_tac)
  · intro j hj; scalar_tac
  · intro k hk hk2
    have hrep : (Array.repeat 64#usize pad).val = List.replicate 64 pad := rfl
    rw [hrep, List.getElem!_replicate]; exact hk2

/-! ### Variable-length (bounded) SHA-256 — the multi-block Merkle–Damgård hash -/

/-- Copying a 64-byte block out of the scratch buffer never fails, given the block
fits: `off + 64 ≤ 2048`. -/
@[step]
theorem extract_block_total (buf : Array Std.U8 2048#usize) (off : Std.Usize) :
    off.val + 64 ≤ 2048 → sha256.extract_block buf off ⦃ fun _ => True ⦄ := by
  intro hoff
  unfold sha256.extract_block sha256.extract_block_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 64#usize) × Std.Usize => 64 - s.2.val)
    (inv := fun s : (Array Std.U8 64#usize) × Std.Usize => s.2.val ≤ 64)
    (post := fun _ => True)
  · rintro ⟨bl, j⟩ hinv
    simp only [sha256.extract_block_loop.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · scalar_tac

/-- The data-copy loop (`buf[0..len] = data[0..len]`) never fails for `len ≤ 2048`. -/
@[step]
theorem sha256_loop0_total (data : Array Std.U8 2048#usize) (len : Std.Usize) :
    len.val ≤ 2048 →
    ∀ (buf : Array Std.U8 2048#usize) (i : Std.Usize), i.val ≤ len.val →
      sha256.sha256_loop0 data len buf i ⦃ fun _ => True ⦄ := by
  intro hlen buf i hi
  unfold sha256.sha256_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 2048#usize) × Std.Usize => len.val - s.2.val)
    (inv := fun s : (Array Std.U8 2048#usize) × Std.Usize => s.2.val ≤ len.val)
    (post := fun _ => True)
  · rintro ⟨b1, i1⟩ hinv
    simp only [sha256.sha256_loop0.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

/-- The length-field write loop never fails when `8 ≤ total ≤ 2048` (writes
`buf[total-8 .. total]`, shifts by `56 - 8k < 64`). -/
@[step]
theorem sha256_loop1_total (total : Std.Usize) (bitlen : Std.U64) :
    8 ≤ total.val → total.val ≤ 2048 →
    ∀ (buf : Array Std.U8 2048#usize) (k : Std.Usize), k.val ≤ 8 →
      sha256.sha256_loop1 total buf bitlen k ⦃ fun _ => True ⦄ := by
  intro htlo hthi buf k hk
  unfold sha256.sha256_loop1
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 2048#usize) × Std.Usize => 8 - s.2.val)
    (inv := fun s : (Array Std.U8 2048#usize) × Std.Usize => s.2.val ≤ 8)
    (post := fun _ => True)
  · rintro ⟨b1, k1⟩ hinv
    simp only [sha256.sha256_loop1.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hk

/-- The block-absorption loop never fails for `nblocks ≤ 32`: each iteration
extracts block `b < nblocks` (so `64·(b+1) ≤ 2048`) and runs the total compression. -/
@[step]
theorem sha256_loop2_total (nblocks : Std.Usize) (buf : Array Std.U8 2048#usize) :
    nblocks.val ≤ 32 →
    ∀ (state : Array Std.U32 8#usize) (b : Std.Usize), b.val ≤ nblocks.val →
      sha256.sha256_loop2 nblocks buf state b ⦃ fun _ => True ⦄ := by
  intro hnb state b hb
  unfold sha256.sha256_loop2
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U32 8#usize) × Std.Usize => nblocks.val - s.2.val)
    (inv := fun s : (Array Std.U32 8#usize) × Std.Usize => s.2.val ≤ nblocks.val)
    (post := fun _ => True)
  · rintro ⟨st1, b1⟩ hinv
    simp only [sha256.sha256_loop2.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hb

/-- **Value adequacy of variable-length SHA-256.** `sha256 data len` is total for
`len + 9 ≤ 2048` — the multi-block hash that makes HMAC/HKDF/AEAD functionally
identical to upstream over the bounded domain (rather than 32-byte-only). -/
@[step]
theorem sha256_total (data : Array Std.U8 2048#usize) (len : Std.Usize) :
    len.val + 9 ≤ 2048 → sha256.sha256 data len ⦃ fun _ => True ⦄ := by
  intro hlen
  unfold sha256.sha256
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨nblocks, hnb⟩
  have hnb32 : nblocks.val ≤ 32 := by scalar_tac
  have hnb1 : 1 ≤ nblocks.val := by scalar_tac
  step as ⟨total, htot⟩
  have htot_hi : total.val ≤ 2048 := by scalar_tac
  have htot_lo : 8 ≤ total.val := by scalar_tac
  have hlen2048 : len.val ≤ 2048 := by scalar_tac
  step*

/-! ### Variable-length HMAC-SHA256 over the multi-block hash -/

@[step]
theorem hmac_var_loop0_total (kb_i : Array Std.U8 64#usize) :
    ∀ (inner : Array Std.U8 2048#usize) (i : Std.Usize), i.val ≤ 64 →
      sha256.hmac_sha256_var_loop0 kb_i inner i ⦃ fun _ => True ⦄ := by
  intro inner i hi
  unfold sha256.hmac_sha256_var_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 2048#usize) × Std.Usize => 64 - s.2.val)
    (inv := fun s : (Array Std.U8 2048#usize) × Std.Usize => s.2.val ≤ 64)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [sha256.hmac_sha256_var_loop0.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

@[step]
theorem hmac_var_loop1_total (msg : Array Std.U8 1536#usize) (msglen : Std.Usize) :
    msglen.val ≤ 1536 →
    ∀ (inner : Array Std.U8 2048#usize) (i : Std.Usize), i.val ≤ msglen.val →
      sha256.hmac_sha256_var_loop1 msg msglen inner i ⦃ fun _ => True ⦄ := by
  intro hml inner i hi
  unfold sha256.hmac_sha256_var_loop1
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 2048#usize) × Std.Usize => msglen.val - s.2.val)
    (inv := fun s : (Array Std.U8 2048#usize) × Std.Usize => s.2.val ≤ msglen.val)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [sha256.hmac_sha256_var_loop1.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

@[step]
theorem hmac_var_loop2_total (kb_o : Array Std.U8 64#usize) :
    ∀ (outer : Array Std.U8 2048#usize) (i : Std.Usize), i.val ≤ 64 →
      sha256.hmac_sha256_var_loop2 kb_o outer i ⦃ fun _ => True ⦄ := by
  intro outer i hi
  unfold sha256.hmac_sha256_var_loop2
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 2048#usize) × Std.Usize => 64 - s.2.val)
    (inv := fun s : (Array Std.U8 2048#usize) × Std.Usize => s.2.val ≤ 64)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [sha256.hmac_sha256_var_loop2.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

@[step]
theorem hmac_var_loop3_total (id : Array Std.U8 32#usize) :
    ∀ (outer : Array Std.U8 2048#usize) (i : Std.Usize), i.val ≤ 32 →
      sha256.hmac_sha256_var_loop3 id outer i ⦃ fun _ => True ⦄ := by
  intro outer i hi
  unfold sha256.hmac_sha256_var_loop3
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 2048#usize) × Std.Usize => 32 - s.2.val)
    (inv := fun s : (Array Std.U8 2048#usize) × Std.Usize => s.2.val ≤ 32)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [sha256.hmac_sha256_var_loop3.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

/-- **Value adequacy of variable-length HMAC-SHA256.** Total for `msglen ≤ 1536`
(so the inner hash `64 + msglen ≤ 1600` is within `HASH_CAP`). The full two-pass
HMAC over the variable hash — functionally identical to upstream `hmac_sha256` for
any (bounded) message under a 32-byte key. -/
@[step]
theorem hmac_sha256_var_total (key : Array Std.U8 32#usize) (msg : Array Std.U8 1536#usize)
    (msglen : Std.Usize) :
    msglen.val ≤ 1536 → sha256.hmac_sha256_var key msg msglen ⦃ fun _ => True ⦄ := by
  intro hml
  unfold sha256.hmac_sha256_var
  step*

/-! ### HMAC byte-layout value specs for the four assembly loops

These pin *what* each assembly loop writes (the audited `hmac_var_loop{0,1,2,3}_total` certify
only non-failure). Together they give the HMAC two-pass byte equation `hmac_sha256_var` =
`H((K0⊕opad) ‖ H((K0⊕ipad) ‖ msg))` over the extracted code: `loop0`/`loop1` assemble the inner
buffer `(K0⊕ipad) ‖ msg`, `loop2`/`loop3` assemble the outer buffer `(K0⊕opad) ‖ inner_digest`. -/

/-- `loop0` copies the padded-key block `kb_i` into `inner[0..64]`, leaving the rest unchanged. -/
theorem hmac_var_loop0_spec (kb_i : Array Std.U8 64#usize) :
    ∀ (inner : Array Std.U8 2048#usize) (i : Std.Usize), i.val ≤ 64 →
      (∀ j, j < i.val → inner.val[j]! = kb_i.val[j]!) →
      sha256.hmac_sha256_var_loop0 kb_i inner i
        ⦃ r => (∀ j, j < 64 → r.val[j]! = kb_i.val[j]!) ∧
               (∀ k, 64 ≤ k → r.val[k]! = inner.val[k]!) ⦄ := by
  intro inner i hi hpre
  unfold sha256.hmac_sha256_var_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 2048#usize) × Std.Usize => 64 - s.2.val)
    (inv := fun s : (Array Std.U8 2048#usize) × Std.Usize =>
      s.2.val ≤ 64 ∧
      (∀ j, j < s.2.val → s.1.val[j]! = kb_i.val[j]!) ∧
      (∀ k, 64 ≤ k → s.1.val[k]! = inner.val[k]!))
    (post := fun r : Array Std.U8 2048#usize =>
      (∀ j, j < 64 → r.val[j]! = kb_i.val[j]!) ∧
      (∀ k, 64 ≤ k → r.val[k]! = inner.val[k]!))
  · rintro ⟨o1, i1⟩ ⟨hi1, hpre1, hrest1⟩
    simp only [sha256.hmac_sha256_var_loop0.body]
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

/-- `loop1` copies `msg[0..msglen]` into `inner[64 .. 64+msglen]`, preserving `inner[0..64]` and
`inner[64+msglen ..]`. -/
theorem hmac_var_loop1_spec (msg : Array Std.U8 1536#usize) (msglen : Std.Usize)
    (hml : msglen.val ≤ 1536) :
    ∀ (inner : Array Std.U8 2048#usize) (i : Std.Usize), i.val ≤ msglen.val →
      (∀ j, j < i.val → inner.val[64 + j]! = msg.val[j]!) →
      sha256.hmac_sha256_var_loop1 msg msglen inner i
        ⦃ r => (∀ k, k < 64 → r.val[k]! = inner.val[k]!) ∧
               (∀ j, j < msglen.val → r.val[64 + j]! = msg.val[j]!) ∧
               (∀ k, 64 + msglen.val ≤ k → r.val[k]! = inner.val[k]!) ⦄ := by
  intro inner i hi hpre
  unfold sha256.hmac_sha256_var_loop1
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 2048#usize) × Std.Usize => msglen.val - s.2.val)
    (inv := fun s : (Array Std.U8 2048#usize) × Std.Usize =>
      s.2.val ≤ msglen.val ∧
      (∀ k, k < 64 → s.1.val[k]! = inner.val[k]!) ∧
      (∀ j, j < s.2.val → s.1.val[64 + j]! = msg.val[j]!) ∧
      (∀ k, 64 + msglen.val ≤ k → s.1.val[k]! = inner.val[k]!))
    (post := fun r : Array Std.U8 2048#usize =>
      (∀ k, k < 64 → r.val[k]! = inner.val[k]!) ∧
      (∀ j, j < msglen.val → r.val[64 + j]! = msg.val[j]!) ∧
      (∀ k, 64 + msglen.val ≤ k → r.val[k]! = inner.val[k]!))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlo1, hmid1, hhi1⟩
    simp only [sha256.hmac_sha256_var_loop1.body]
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
          have : 64 + j ≠ off.val := by scalar_tac
          simp_lists; exact hmid1 j (by scalar_tac)
      · intro k hk
        subst ha
        have : k ≠ off.val := by scalar_tac
        simp_lists; exact hhi1 k hk
      · scalar_tac
    · rename_i hge
      exact ⟨hlo1, fun j hj => hmid1 j (by scalar_tac), hhi1⟩
  · exact ⟨hi, fun k hk => rfl, hpre, fun k hk => rfl⟩

/-- `loop2` copies the outer padded-key block `kb_o` into `outer[0..64]`. -/
theorem hmac_var_loop2_spec (kb_o : Array Std.U8 64#usize) :
    ∀ (outer : Array Std.U8 2048#usize) (i : Std.Usize), i.val ≤ 64 →
      (∀ j, j < i.val → outer.val[j]! = kb_o.val[j]!) →
      sha256.hmac_sha256_var_loop2 kb_o outer i
        ⦃ r => (∀ j, j < 64 → r.val[j]! = kb_o.val[j]!) ∧
               (∀ k, 64 ≤ k → r.val[k]! = outer.val[k]!) ⦄ := by
  intro outer i hi hpre
  unfold sha256.hmac_sha256_var_loop2
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 2048#usize) × Std.Usize => 64 - s.2.val)
    (inv := fun s : (Array Std.U8 2048#usize) × Std.Usize =>
      s.2.val ≤ 64 ∧
      (∀ j, j < s.2.val → s.1.val[j]! = kb_o.val[j]!) ∧
      (∀ k, 64 ≤ k → s.1.val[k]! = outer.val[k]!))
    (post := fun r : Array Std.U8 2048#usize =>
      (∀ j, j < 64 → r.val[j]! = kb_o.val[j]!) ∧
      (∀ k, 64 ≤ k → r.val[k]! = outer.val[k]!))
  · rintro ⟨o1, i1⟩ ⟨hi1, hpre1, hrest1⟩
    simp only [sha256.hmac_sha256_var_loop2.body]
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

/-- `loop3` copies the 32-byte inner digest `id` into `outer[64..96]`. -/
theorem hmac_var_loop3_spec (id : Array Std.U8 32#usize) :
    ∀ (outer : Array Std.U8 2048#usize) (i : Std.Usize), i.val ≤ 32 →
      (∀ j, j < i.val → outer.val[64 + j]! = id.val[j]!) →
      sha256.hmac_sha256_var_loop3 id outer i
        ⦃ r => (∀ k, k < 64 → r.val[k]! = outer.val[k]!) ∧
               (∀ j, j < 32 → r.val[64 + j]! = id.val[j]!) ∧
               (∀ k, 96 ≤ k → r.val[k]! = outer.val[k]!) ⦄ := by
  intro outer i hi hpre
  unfold sha256.hmac_sha256_var_loop3
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 2048#usize) × Std.Usize => 32 - s.2.val)
    (inv := fun s : (Array Std.U8 2048#usize) × Std.Usize =>
      s.2.val ≤ 32 ∧
      (∀ k, k < 64 → s.1.val[k]! = outer.val[k]!) ∧
      (∀ j, j < s.2.val → s.1.val[64 + j]! = id.val[j]!) ∧
      (∀ k, 96 ≤ k → s.1.val[k]! = outer.val[k]!))
    (post := fun r : Array Std.U8 2048#usize =>
      (∀ k, k < 64 → r.val[k]! = outer.val[k]!) ∧
      (∀ j, j < 32 → r.val[64 + j]! = id.val[j]!) ∧
      (∀ k, 96 ≤ k → r.val[k]! = outer.val[k]!))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlo1, hmid1, hhi1⟩
    simp only [sha256.hmac_sha256_var_loop3.body]
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
          have : 64 + j ≠ off.val := by scalar_tac
          simp_lists; exact hmid1 j (by scalar_tac)
      · intro k hk
        subst ha
        have : k ≠ off.val := by scalar_tac
        simp_lists; exact hhi1 k hk
      · scalar_tac
    · rename_i hge
      exact ⟨hlo1, fun j hj => hmid1 j (by scalar_tac), hhi1⟩
  · exact ⟨hi, fun k hk => rfl, hpre, fun k hk => rfl⟩

/-- **HMAC two-pass byte equation** (functional correctness, no security). For `msglen ≤ 1536`,
the extracted `hmac_sha256_var key msg msglen` is exactly RFC 2104's
`H((K0 ⊕ opad) ‖ H((K0 ⊕ ipad) ‖ msg))`: there are an inner buffer `inner2`, an inner digest `id`,
and an outer buffer `outer2` such that

* `inner2[0..32] = key ⊕ 0x36`, `inner2[32..64] = 0x36`, `inner2[64..64+msglen] = msg`
  (the `K0 ⊕ ipad` prefix followed by the message), and `id = SHA256(inner2, 64 + msglen)`;
* `outer2[0..32] = key ⊕ 0x5c`, `outer2[32..64] = 0x5c`, `outer2[64..96] = id`
  (the `K0 ⊕ opad` prefix followed by the inner digest);
* the result is `SHA256(outer2, 96)`.

This pins the byte-level shape the HMAC-is-a-PRF reduction lifts (`Demos/Crypto/HmacPrf.lean`'s
`hmacSpec`), now over the genuine extracted two-pass code rather than asserted abstractly. The
two pads `0x36 = 54` (ipad) and `0x5c = 92` (opad) are distinct, exactly as RFC 2104 requires. -/
theorem hmac_sha256_var_byte_eq (key : Array Std.U8 32#usize) (msg : Array Std.U8 1536#usize)
    (msglen : Std.Usize) (hml : msglen.val ≤ 1536) :
    sha256.hmac_sha256_var key msg msglen
      ⦃ r => ∃ (inner2 outer2 : Array Std.U8 2048#usize) (id : Array Std.U8 32#usize)
               (leni : Std.Usize),
          leni.val = 64 + msglen.val ∧
          (∀ j, j < 32 → inner2.val[j]! = key.val[j]! ^^^ 54#u8) ∧
          (∀ k, 32 ≤ k → k < 64 → inner2.val[k]! = 54#u8) ∧
          (∀ j, j < msglen.val → inner2.val[64 + j]! = msg.val[j]!) ∧
          sha256.sha256 inner2 leni = ok id ∧
          (∀ j, j < 32 → outer2.val[j]! = key.val[j]! ^^^ 92#u8) ∧
          (∀ k, 32 ≤ k → k < 64 → outer2.val[k]! = 92#u8) ∧
          (∀ j, j < 32 → outer2.val[64 + j]! = id.val[j]!) ∧
          sha256.sha256 outer2 96#usize = ok r ⦄ := by
  unfold sha256.hmac_sha256_var
  -- kb_i = K0 ⊕ ipad
  apply Aeneas.Std.WP.spec_bind (key_pad_block_spec key 54#u8)
  rintro kb_i ⟨hki_lo, hki_hi⟩
  -- inner1 = kb_i ‖ (zeros)
  apply Aeneas.Std.WP.spec_bind
    (hmac_var_loop0_spec kb_i (Array.repeat 2048#usize 0#u8) 0#usize (by scalar_tac)
      (by intro j hj; scalar_tac))
  rintro inner1 ⟨hin1_lo, hin1_hi⟩
  -- inner2 = kb_i ‖ msg
  apply Aeneas.Std.WP.spec_bind
    (hmac_var_loop1_spec msg msglen hml inner1 0#usize (by scalar_tac)
      (by intro j hj; scalar_tac))
  rintro inner2 ⟨hin2_lo, hin2_mid, hin2_hi⟩
  -- i = 64 + msglen
  step as ⟨i, hi⟩
  have hile : i.val + 9 ≤ 2048 := by scalar_tac
  -- id = SHA256(inner2, i): bind with a value spec capturing the defining equation.
  obtain ⟨idw, hidw, -⟩ := Aeneas.Std.WP.spec_imp_exists (sha256_total inner2 i hile)
  apply Aeneas.Std.WP.spec_bind
    (Aeneas.Std.WP.exists_imp_spec (m := sha256.sha256 inner2 i)
      (P := fun id' => sha256.sha256 inner2 i = ok id') ⟨idw, hidw, hidw⟩)
  rintro id hid_eq
  -- kb_o = K0 ⊕ opad
  apply Aeneas.Std.WP.spec_bind (key_pad_block_spec key 92#u8)
  rintro kb_o ⟨hko_lo, hko_hi⟩
  -- outer1 = kb_o ‖ (zeros)
  apply Aeneas.Std.WP.spec_bind
    (hmac_var_loop2_spec kb_o (Array.repeat 2048#usize 0#u8) 0#usize (by scalar_tac)
      (by intro j hj; scalar_tac))
  rintro outer1 ⟨hou1_lo, hou1_hi⟩
  -- outer2 = kb_o ‖ id
  apply Aeneas.Std.WP.spec_bind
    (hmac_var_loop3_spec id outer1 0#usize (by scalar_tac) (by intro j hj; scalar_tac))
  rintro outer2 ⟨hou2_lo, hou2_mid, hou2_hi⟩
  -- the final SHA256(outer2, 96): expose its result digest as the existential witness.
  obtain ⟨r, hr_eq, -⟩ := Aeneas.Std.WP.spec_imp_exists (sha256_total outer2 96#usize (by scalar_tac))
  apply Aeneas.Std.WP.exists_imp_spec (m := sha256.sha256 outer2 96#usize)
  refine ⟨r, hr_eq, inner2, outer2, id, i, hi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- inner2[0..32] = key ⊕ ipad
    intro j hj
    rw [hin2_lo j (by scalar_tac), hin1_lo j (by scalar_tac), hki_lo j hj]
  · -- inner2[32..64] = ipad
    intro k hk hk2
    rw [hin2_lo k (by scalar_tac), hin1_lo k (by scalar_tac), hki_hi k hk hk2]
  · -- inner2[64..64+msglen] = msg
    exact hin2_mid
  · -- inner digest equation
    exact hid_eq
  · -- outer2[0..32] = key ⊕ opad
    intro j hj
    rw [hou2_lo j (by scalar_tac), hou1_lo j (by scalar_tac), hko_lo j hj]
  · -- outer2[32..64] = opad
    intro k hk hk2
    rw [hou2_lo k (by scalar_tac), hou1_lo k (by scalar_tac), hko_hi k hk hk2]
  · -- outer2[64..96] = inner digest
    exact hou2_mid
  · -- result = SHA256(outer2, 96)
    exact hr_eq

/-! ### HKDF-SHA256 over the variable-length HMAC -/

/-- **HKDF-Extract is total** (`PRK = HMAC(salt, ikm)`), for `ikmlen ≤ 1536`. -/
@[step]
theorem hkdf_extract_total (salt : Array Std.U8 32#usize) (ikm : Array Std.U8 1536#usize)
    (ikmlen : Std.Usize) :
    ikmlen.val ≤ 1536 → sha256.hkdf_extract salt ikm ikmlen ⦃ fun _ => True ⦄ := by
  intro h
  unfold sha256.hkdf_extract
  exact hmac_sha256_var_total salt ikm ikmlen h

@[step]
theorem hkdf_t1_msg_loop_total (info : Array Std.U8 256#usize) (infolen : Std.Usize) :
    infolen.val ≤ 256 →
    ∀ (m : Array Std.U8 1536#usize) (i : Std.Usize), i.val ≤ infolen.val →
      sha256.hkdf_t1_msg_loop info infolen m i ⦃ fun _ => True ⦄ := by
  intro hil m i hi
  unfold sha256.hkdf_t1_msg_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 1536#usize) × Std.Usize => infolen.val - s.2.val)
    (inv := fun s : (Array Std.U8 1536#usize) × Std.Usize => s.2.val ≤ infolen.val)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [sha256.hkdf_t1_msg_loop.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

@[step]
theorem hkdf_t1_msg_total (info : Array Std.U8 256#usize) (infolen : Std.Usize) (ctr : Std.U8) :
    infolen.val ≤ 256 → sha256.hkdf_t1_msg info infolen ctr ⦃ fun _ => True ⦄ := by
  intro hil
  unfold sha256.hkdf_t1_msg
  step*

@[step]
theorem hkdf_tn_msg_loop0_total (prev : Array Std.U8 32#usize) :
    ∀ (m : Array Std.U8 1536#usize) (i : Std.Usize), i.val ≤ 32 →
      sha256.hkdf_tn_msg_loop0 prev m i ⦃ fun _ => True ⦄ := by
  intro m i hi
  unfold sha256.hkdf_tn_msg_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 1536#usize) × Std.Usize => 32 - s.2.val)
    (inv := fun s : (Array Std.U8 1536#usize) × Std.Usize => s.2.val ≤ 32)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [sha256.hkdf_tn_msg_loop0.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

@[step]
theorem hkdf_tn_msg_loop1_total (info : Array Std.U8 256#usize) (infolen : Std.Usize) :
    infolen.val ≤ 256 →
    ∀ (m : Array Std.U8 1536#usize) (i : Std.Usize), i.val ≤ infolen.val →
      sha256.hkdf_tn_msg_loop1 info infolen m i ⦃ fun _ => True ⦄ := by
  intro hil m i hi
  unfold sha256.hkdf_tn_msg_loop1
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 1536#usize) × Std.Usize => infolen.val - s.2.val)
    (inv := fun s : (Array Std.U8 1536#usize) × Std.Usize => s.2.val ≤ infolen.val)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [sha256.hkdf_tn_msg_loop1.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

@[step]
theorem hkdf_tn_msg_total (prev : Array Std.U8 32#usize) (info : Array Std.U8 256#usize)
    (infolen : Std.Usize) (ctr : Std.U8) :
    infolen.val ≤ 256 → sha256.hkdf_tn_msg prev info infolen ctr ⦃ fun _ => True ⦄ := by
  intro hil
  unfold sha256.hkdf_tn_msg
  step*

@[step]
theorem hkdf_expand_96_loop_total (t1 t2 t3 : Array Std.U8 32#usize) :
    ∀ (okm : Array Std.U8 96#usize) (i : Std.Usize), i.val ≤ 32 →
      sha256.hkdf_expand_96_loop t1 t2 t3 okm i ⦃ fun _ => True ⦄ := by
  intro okm i hi
  unfold sha256.hkdf_expand_96_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 96#usize) × Std.Usize => 32 - s.2.val)
    (inv := fun s : (Array Std.U8 96#usize) × Std.Usize => s.2.val ≤ 32)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [sha256.hkdf_expand_96_loop.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

/-- **Value adequacy of HKDF-Expand (96 bytes).** Total for `infolen ≤ 256`:
`T1 ‖ T2 ‖ T3` with the RFC 5869 T-chaining over the variable-length HMAC. -/
theorem hkdf_expand_96_total (prk : Array Std.U8 32#usize) (info : Array Std.U8 256#usize)
    (infolen : Std.Usize) :
    infolen.val ≤ 256 → sha256.hkdf_expand_96 prk info infolen ⦃ fun _ => True ⦄ := by
  intro hil
  unfold sha256.hkdf_expand_96
  step*

@[step]
theorem hkdf_expand_64_loop_total (t1 t2 : Array Std.U8 32#usize) :
    ∀ (okm : Array Std.U8 64#usize) (i : Std.Usize), i.val ≤ 32 →
      sha256.hkdf_expand_64_loop t1 t2 okm i ⦃ fun _ => True ⦄ := by
  intro okm i hi
  unfold sha256.hkdf_expand_64_loop
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 64#usize) × Std.Usize => 32 - s.2.val)
    (inv := fun s : (Array Std.U8 64#usize) × Std.Usize => s.2.val ≤ 32)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [sha256.hkdf_expand_64_loop.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

/-- **Value adequacy of HKDF-Expand (64 bytes).** Total for `infolen ≤ 256`: `T1 ‖ T2`
with the same RFC 5869 T-chaining; the 64-byte block the SPQR chain step consumes. -/
@[step]
theorem hkdf_expand_64_total (prk : Array Std.U8 32#usize) (info : Array Std.U8 256#usize)
    (infolen : Std.Usize) :
    infolen.val ≤ 256 → sha256.hkdf_expand_64 prk info infolen ⦃ fun _ => True ⦄ := by
  intro hil
  unfold sha256.hkdf_expand_64
  step*

/-! ### SPQR symmetric ratchet step (chain.rs `next_key_internal`) -/

/-- The label-copy loop never fails: writes `info[4+i]` for `i < 31` (`4+i < 256`). -/
@[step]
theorem spqr_chain_next_loop0_total :
    ∀ (info : Array Std.U8 256#usize) (i : Std.Usize), i.val ≤ 31 →
      sha256.spqr_chain_next_loop0 info i ⦃ fun _ => True ⦄ := by
  intro info i hi
  unfold sha256.spqr_chain_next_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 256#usize) × Std.Usize => 31 - s.2.val)
    (inv := fun s : (Array Std.U8 256#usize) × Std.Usize => s.2.val ≤ 31)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [sha256.spqr_chain_next_loop0.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

/-- The chain-key copy loop never fails: `ikm[i] = next[i]` for `i < 32`. -/
@[step]
theorem spqr_chain_next_loop1_total (next : Array Std.U8 32#usize) :
    ∀ (ikm : Array Std.U8 1536#usize) (i : Std.Usize), i.val ≤ 32 →
      sha256.spqr_chain_next_loop1 next ikm i ⦃ fun _ => True ⦄ := by
  intro ikm i hi
  unfold sha256.spqr_chain_next_loop1
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 1536#usize) × Std.Usize => 32 - s.2.val)
    (inv := fun s : (Array Std.U8 1536#usize) × Std.Usize => s.2.val ≤ 32)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [sha256.spqr_chain_next_loop1.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

/-- The output split loop never fails: `new_next[i] = genr8r[i]`, `out_key[i] = genr8r[32+i]`,
`i < 32` (`32+i < 64`). -/
@[step]
theorem spqr_chain_next_loop2_total (genr8r : Array Std.U8 64#usize) :
    ∀ (new_next out_key : Array Std.U8 32#usize) (i : Std.Usize), i.val ≤ 32 →
      sha256.spqr_chain_next_loop2 genr8r new_next out_key i ⦃ fun _ => True ⦄ := by
  intro new_next out_key i hi
  unfold sha256.spqr_chain_next_loop2
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 32#usize) × (Array Std.U8 32#usize) × Std.Usize =>
      32 - s.2.2.val)
    (inv := fun s : (Array Std.U8 32#usize) × (Array Std.U8 32#usize) × Std.Usize =>
      s.2.2.val ≤ 32)
    (post := fun _ => True)
  · rintro ⟨o1, o2, i1⟩ hinv
    simp only [sha256.spqr_chain_next_loop2.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

/-- `step` spec for `u32::to_be_bytes`: Aeneas ships the `to_le_bytes` step spec but not the
big-endian one, so `step*` stalls on it. Totality suffices — the result is a length-4 array,
so the subsequent constant indices `0..3` are in bounds regardless of value. -/
@[step]
theorem u32_to_be_bytes_step (x : Std.U32) :
    lift (core.num.U32.to_be_bytes x) ⦃ fun _ => True ⦄ := by
  simp only [lift, WP.spec_ok]

/-- **Value adequacy of the SPQR chain step.** `spqr_chain_next` is total for `ctr < u32::MAX`
(so `ctr+1` doesn't overflow): build the `info`, extract+expand 64 bytes via HKDF, split into the
new chain key and the emitted output key. This is the symmetric ratchet producing the SCKA
`output_key`s. -/
theorem spqr_chain_next_total (next : Array Std.U8 32#usize) (ctr : Std.U32) :
    ctr.val < Std.U32.max → sha256.spqr_chain_next next ctr ⦃ fun _ => True ⦄ := by
  intro hctr
  unfold sha256.spqr_chain_next
  step*
  trivial

/-! ### Variable-length AEAD (encrypt-then-MAC) -/

@[step]
theorem etm_enc_var_loop0_total (keystream msg : Array Std.U8 1536#usize) (len : Std.Usize) :
    len.val ≤ 1536 →
    ∀ (c : Array Std.U8 1536#usize) (i : Std.Usize), i.val ≤ len.val →
      sha256.etm_encrypt_var_loop0 keystream msg len c i ⦃ fun _ => True ⦄ := by
  intro hl c i hi
  unfold sha256.etm_encrypt_var_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 1536#usize) × Std.Usize => len.val - s.2.val)
    (inv := fun s : (Array Std.U8 1536#usize) × Std.Usize => s.2.val ≤ len.val)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [sha256.etm_encrypt_var_loop0.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

@[step]
theorem etm_enc_var_loop1_total (mac : Array Std.U8 32#usize) :
    ∀ (tag : Array Std.U8 10#usize) (j : Std.Usize), j.val ≤ 10 →
      sha256.etm_encrypt_var_loop1 mac tag j ⦃ fun _ => True ⦄ := by
  intro tag j hj
  unfold sha256.etm_encrypt_var_loop1
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 10#usize) × Std.Usize => 10 - s.2.val)
    (inv := fun s : (Array Std.U8 10#usize) × Std.Usize => s.2.val ≤ 10)
    (post := fun _ => True)
  · rintro ⟨o1, j1⟩ hinv
    simp only [sha256.etm_encrypt_var_loop1.body, sha256.TAG_LEN]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hj

/-- **Value adequacy of variable-length AEAD encryption.** Total for `len ≤ 1536`. -/
theorem etm_encrypt_var_total (keystream msg : Array Std.U8 1536#usize) (len : Std.Usize)
    (mac_key : Array Std.U8 32#usize) :
    len.val ≤ 1536 → sha256.etm_encrypt_var keystream msg len mac_key ⦃ fun _ => True ⦄ := by
  intro hl
  unfold sha256.etm_encrypt_var
  step*

@[step]
theorem etm_dec_var_loop0_total (tag : Array Std.U8 10#usize) (mac : Array Std.U8 32#usize) :
    ∀ (r : Std.U8) (k : Std.Usize), k.val ≤ 10 →
      sha256.etm_decrypt_var_loop0 tag mac r k ⦃ fun _ => True ⦄ := by
  intro r k hk
  unfold sha256.etm_decrypt_var_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : Std.U8 × Std.Usize => 10 - s.2.val)
    (inv := fun s : Std.U8 × Std.Usize => s.2.val ≤ 10)
    (post := fun _ => True)
  · rintro ⟨r1, k1⟩ hinv
    simp only [sha256.etm_decrypt_var_loop0.body, sha256.TAG_LEN]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hk

@[step]
theorem etm_dec_var_loop1_total (c keystream : Array Std.U8 1536#usize) (len : Std.Usize) :
    len.val ≤ 1536 →
    ∀ (m : Array Std.U8 1536#usize) (i : Std.Usize), i.val ≤ len.val →
      sha256.etm_decrypt_var_loop1 c len keystream m i ⦃ fun _ => True ⦄ := by
  intro hl m i hi
  unfold sha256.etm_decrypt_var_loop1
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 1536#usize) × Std.Usize => len.val - s.2.val)
    (inv := fun s : (Array Std.U8 1536#usize) × Std.Usize => s.2.val ≤ len.val)
    (post := fun _ => True)
  · rintro ⟨o1, i1⟩ hinv
    simp only [sha256.etm_decrypt_var_loop1.body]
    split
    · rename_i hlt; repeat' step*
    · trivial
  · exact hi

/-- **Value adequacy of variable-length AEAD decryption.** Total for `len ≤ 1536`:
recompute the MAC, constant-time compare, and on success XOR back — `none` on mismatch. -/
theorem etm_decrypt_var_total (c : Array Std.U8 1536#usize) (len : Std.Usize)
    (tag : Array Std.U8 10#usize) (keystream : Array Std.U8 1536#usize)
    (mac_key : Array Std.U8 32#usize) :
    len.val ≤ 1536 → sha256.etm_decrypt_var c len tag keystream mac_key ⦃ fun _ => True ⦄ := by
  intro hl
  unfold sha256.etm_decrypt_var
  step as ⟨mac, hmac⟩
  step as ⟨r, hr⟩
  split
  · trivial
  · repeat' step*

end Sha256
