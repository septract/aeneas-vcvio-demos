/-
  Demo 3 (meaty node) — the ratchet's block generator is the **real, Aeneas-extracted
  ChaCha20 block function**, not abstract.

  `Chain.lean` proves the ratchet secure for *any* block generator `G : Key → Blk64`
  (the hybrid reduction is generic). Here we discharge the value-adequacy obligation for a
  concrete `G`: the extracted `chacha.chacha20_block` is **total** (never panics/overflows),
  so it defines a genuine pure function `chachaPure`, and instantiating the generic theorems
  at `G := chachaPure` gives security for the ratchet whose steps run real ARX Rust — under
  the standard, named assumption that ChaCha20 (keyed by the chain key) is a PRG.
-/
import Demos.Ratchet.Chain
import Demos.Extracted.Chacha

open Aeneas Std Result OracleComp ENNReal PRGScheme RatchetSecurity

namespace RatchetChacha


/-- The quarter-round never fails (pure wrapping-add / xor / rotate). The 4-binder
postcondition matches the tuple arity, so `step*` can advance through a `quarter` *call*
(introducing the four result words) without unfolding it. -/
@[step]
theorem quarter_total (a b c d : Std.U32) :
    chacha.quarter a b c d ⦃ _ _ _ _ => True ⦄ := by
  unfold chacha.quarter
  step*

/-- One double round never fails: 8 quarter-rounds plus in-bounds reads/writes of a 16-word
state. `step*` advances through each quarter-round via its registered spec (no unfolding) and
the array index/update specs (literal bounds). -/
@[step]
theorem double_round_total (s : Array Std.U32 16#usize) :
    chacha.double_round s ⦃ fun _ => True ⦄ := by
  unfold chacha.double_round
  repeat' step*

/-- Loading a little-endian word from four bytes never fails (shifts by 8/16/24 < 32). -/
@[step]
theorem load_le_total (b0 b1 b2 b3 : Std.U8) :
    chacha.load_le b0 b1 b2 b3 ⦃ fun _ => True ⦄ := by
  unfold chacha.load_le
  step*

/-- Loop 0 (load the 8 key words into the state) never fails. -/
@[step]
theorem chacha20_block_loop0_total (key : Array Std.U8 32#usize) :
    ∀ (state : Array Std.U32 16#usize) (i : Std.Usize), i.val ≤ 8 →
      chacha.chacha20_block_loop0 key state i ⦃ fun _ => True ⦄ := by
  intro state i hi
  unfold chacha.chacha20_block_loop0
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U32 16#usize) × Std.Usize => 8 - s.2.val)
    (inv := fun s : (Array Std.U32 16#usize) × Std.Usize => s.2.val ≤ 8)
    (post := fun _ => True)
  · rintro ⟨st1, i1⟩ hinv
    simp only [chacha.chacha20_block_loop0.body]
    split
    · rename_i hlt
      repeat' step*
    · trivial
  · exact hi

/-- Loop 1 (the 10 double rounds) never fails. -/
@[step]
theorem chacha20_block_loop1_total :
    ∀ (work : Array Std.U32 16#usize) (r : Std.Usize), r.val ≤ 10 →
      chacha.chacha20_block_loop1 work r ⦃ fun _ => True ⦄ := by
  intro work r hr
  unfold chacha.chacha20_block_loop1
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U32 16#usize) × Std.Usize => 10 - s.2.val)
    (inv := fun s : (Array Std.U32 16#usize) × Std.Usize => s.2.val ≤ 10)
    (post := fun _ => True)
  · rintro ⟨w1, r1⟩ hinv
    simp only [chacha.chacha20_block_loop1.body]
    split
    · rename_i hlt
      repeat' step*
    · trivial
  · exact hr

/-- Loop 2 (add the original state and serialize to 64 bytes) never fails. -/
@[step]
theorem chacha20_block_loop2_total (state work : Array Std.U32 16#usize) :
    ∀ (out : Array Std.U8 64#usize) (j : Std.Usize), j.val ≤ 16 →
      chacha.chacha20_block_loop2 state work out j ⦃ fun _ => True ⦄ := by
  intro out j hj
  unfold chacha.chacha20_block_loop2
  apply Std.loop.spec_decr_nat
    (measure := fun s : (Array Std.U8 64#usize) × Std.Usize => 16 - s.2.val)
    (inv := fun s : (Array Std.U8 64#usize) × Std.Usize => s.2.val ≤ 16)
    (post := fun _ => True)
  · rintro ⟨o1, j1⟩ hinv
    simp only [chacha.chacha20_block_loop2.body]
    split
    · rename_i hlt
      repeat' step*
    · trivial
  · exact hj

/-- **Value adequacy.** The Aeneas-extracted ChaCha20 block function is **total** — it never
panics or overflows — for every 32-byte key. -/
theorem chacha20_block_total (key : Array Std.U8 32#usize) :
    chacha.chacha20_block key ⦃ fun _ => True ⦄ := by
  unfold chacha.chacha20_block
  repeat' step*

/-- The pure block function realized by the (total) extracted ChaCha20. The non-`ok` branch is
provably unreachable (`chacha20_block_total`), so this faithfully *is* the extracted function —
no failure can be masked by the fallback. -/
def chachaPure (k : Key) : Blk64 :=
  match chacha.chacha20_block k with
  | .ok o => o
  | _ => default

/-- `chachaPure` is exactly what the extracted Rust computes (stated in `Result`, certifying
totality). -/
theorem chachaPure_spec (k : Key) : chacha.chacha20_block k = .ok (chachaPure k) := by
  obtain ⟨o, ho, _⟩ := WP.spec_imp_exists (chacha20_block_total k)
  simp only [chachaPure, ho]

/-! ## Concrete security: the ratchet over the real extracted ChaCha20.

Instantiate the generic ratchet theorems (`Chain.lean`, proved for any block generator
`G : Key → Blk64`) at `G := chachaPure`. The keystream is now produced by iterating genuine
extracted ARX Rust; security holds under the standard, named assumption that ChaCha20 (keyed by
the chain key) is a PRG. -/

/-- **Concrete hybrid bound.** The ChaCha-based ratchet's pseudorandomness advantage is bounded
by the sum, over the `n` steps, of ChaCha20's PRG advantage against the per-step reductions. -/
theorem chacha_ratchet_advantage_le_sum (n : ℕ) (A : PRGAdversary (List.Vector Key n)) :
    (ratchetPRG chachaPure n).prgAdvantage A
      ≤ ∑ i ∈ Finset.range n,
          (blockPRG chachaPure).prgAdvantage (reduction chachaPure n i A) :=
  ratchet_advantage_le_sum chachaPure n A

/-- **Concrete asymptotic security.** If ChaCha20 (keyed by the chain key) is a secure PRG —
each per-step reduction's advantage bounded by one negligible `ε` — and the chain length is
polynomial, then the ChaCha-based ratchet's message-key stream is pseudorandom. The extracted
ARX node is real arithmetic; PRG hardness and poly length are the named premises. -/
theorem chacha_ratchet_secure_asymptotic (len : ℕ → ℕ)
    (A : ∀ sp, PRGAdversary (List.Vector Key (len sp)))
    (ε : ℕ → ℝ≥0∞) (hε : negligible ε)
    (hbound : ∀ sp, ∀ i < len sp,
      ENNReal.ofReal ((blockPRG chachaPure).prgAdvantage
        (reduction chachaPure (len sp) i (A sp))) ≤ ε sp)
    (hlen : ∃ p : Polynomial ℕ, ∀ sp, len sp ≤ p.eval sp) :
    negligible (fun sp =>
      ENNReal.ofReal ((ratchetPRG chachaPure (len sp)).prgAdvantage (A sp))) :=
  ratchet_secure_asymptotic (fun _ => chachaPure) len A ε hε hbound hlen

end RatchetChacha
