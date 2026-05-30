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
  independent uniform keys. The hybrid argument itself lives once, generically, in
  `Demos/Ratchet/Generic.lean` (over any key/block types and a length-doubling split bijection);
  this file is the **fixed-width instance** at `K := Key`, `B := Blk64`, `split := splitPure`.
  So the concrete `step`/`keystream`/…/`ratchet_advantage_le_sum` below are defeq aliases of the
  generic constructions and theorems — no duplicated proof.

  We deliberately use a length-doubling **PRG** hybrid (each hop a clean reduction to PRG
  security), not the PRF→stream-PRG path (whose collision argument is unfinished upstream).

  Scope (see README "What is deliberately not formalized"): this is Signal's *symmetric* KDF
  chain only — not the full Double Ratchet. `prgAdvantage` is over *all* adversaries here; the
  reductions' efficiency ("calls `A` once") is made a query-count theorem and security is
  restated against the poly-query adversary class in `Demos/Ratchet/Cost.lean`.
-/
import Demos.Ratchet.Step
import Demos.StreamCipher.ByteArray
import Demos.Ratchet.Generic

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

/-! ## The ratchet chain as the fixed-width instance of the generic hybrid (`Generic.lean`).

`step`/`keystream`/`ratchetPRG`/`blockPRG`/`redStream`/`reduction`/`uniformVec` are the
`RatchetGeneric` constructions specialized to `K := Key`, `B := Blk64`, `split := splitPure`;
they are *defeq aliases* (a `def := genX splitPure …`), so any downstream proof that unfolds one
also unfolds the corresponding `RatchetGeneric.genX`. The headline theorems are the generic ones
instantiated — the hybrid argument is proved once, in `Generic.lean`. -/

/-- One ratchet step: split `G ck` into `(next chain key, message key)` via the extracted split. -/
def step (G : Key → Blk64) (ck : Key) : Key × Key := RatchetGeneric.genStep splitPure G ck

/-- The message-key stream: iterate `step` from a seed chain key, collecting the `n` message keys. -/
def keystream (G : Key → Blk64) (n : ℕ) (ck : Key) : List.Vector Key n :=
  RatchetGeneric.genKeystream splitPure G n ck

/-- The ratchet as a PRG: seed = initial chain key, output = the `n` message keys. -/
def ratchetPRG (G : Key → Blk64) (n : ℕ) : PRGScheme Key (List.Vector Key n) :=
  RatchetGeneric.genRatchetPRG splitPure G n

/-- The abstract block generator as a `PRGScheme` (the hardness assumption is on *this*).
Kept concrete (defeq to `RatchetGeneric.genBlockPRG`) so `(blockPRG G).gen` reduces cleanly. -/
def blockPRG (G : Key → Blk64) : PRGScheme Key Blk64 where gen := G

/-- The hybrid reduction stream: `i` leading uniform keys, the challenge block `b` split in at
depth `i`, the remaining keys real. -/
def redStream (G : Key → Blk64) (b : Blk64) (n i : ℕ) : ProbComp (List.Vector Key n) :=
  RatchetGeneric.genRedStream splitPure G b n i

/-- The reduction adversary for hop `i`: feed the assembled vector to the cipher distinguisher. -/
def reduction (G : Key → Blk64) (n i : ℕ) (A : PRGAdversary (List.Vector Key n)) :
    PRGAdversary Blk64 := RatchetGeneric.genReduction splitPure G n i A

/-- `n` independent uniform keys, assembled as a vector. -/
def uniformVec (n : ℕ) : ProbComp (List.Vector Key n) := RatchetGeneric.genUniformVec Key n

/-- **Independent uniform keys = a uniform vector** (instance of `gen_uniformVec_eq`). -/
theorem uniformVec_eq (n : ℕ) (A : List.Vector Key n → ProbComp Bool) :
    Pr[= true | uniformVec n >>= A] = Pr[= true | ($ᵗ (List.Vector Key n)) >>= A] :=
  RatchetGeneric.gen_uniformVec_eq n A

/-- **Main theorem (concrete hybrid bound).** The ratchet keystream's pseudorandomness advantage
is bounded by the sum, over the `n` steps, of the underlying block-PRG's advantage against the
explicit per-step reductions — the protocol-shaped `Σε` bound. (The fixed-width instance of
`RatchetGeneric.gen_advantage_le_sum`.) -/
theorem ratchet_advantage_le_sum (G : Key → Blk64) (n : ℕ)
    (A : PRGAdversary (List.Vector Key n)) :
    (ratchetPRG G n).prgAdvantage A
      ≤ ∑ i ∈ Finset.range n, (blockPRG G).prgAdvantage (reduction G n i A) :=
  RatchetGeneric.gen_advantage_le_sum splitPure splitPure_bijective G n A

/-- **Asymptotic security (the headline).** If the block PRG family is secure (each per-step
reduction's advantage bounded by one negligible `ε`) **and the chain length is polynomially
bounded**, then the ratchet keystream family is pseudorandom. The polynomial bound is essential
and used (`negligible_polynomial_mul`) — the "`Σε` is negligible iff the number of hops is
polynomial" side condition. (The fixed-width instance of `RatchetGeneric.gen_secure_asymptotic_width`.) -/
theorem ratchet_secure_asymptotic
    (G : ℕ → Key → Blk64) (len : ℕ → ℕ)
    (A : ∀ sp, PRGAdversary (List.Vector Key (len sp)))
    (ε : ℕ → ℝ≥0∞) (hε : negligible ε)
    (hbound : ∀ sp, ∀ i < len sp,
      ENNReal.ofReal ((blockPRG (G sp)).prgAdvantage (reduction (G sp) (len sp) i (A sp))) ≤ ε sp)
    (hlen : ∃ p : Polynomial ℕ, ∀ sp, len sp ≤ p.eval sp) :
    negligible (fun sp =>
      ENNReal.ofReal ((ratchetPRG (G sp) (len sp)).prgAdvantage (A sp))) :=
  RatchetGeneric.gen_secure_asymptotic_width (fun _ => Key) (fun _ => Blk64)
    (fun _ => splitPure) (fun _ => splitPure_bijective) G len A ε hε hbound hlen

end RatchetSecurity
