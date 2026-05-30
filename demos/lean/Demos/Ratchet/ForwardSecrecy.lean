/-
  Demo 3 (forward secrecy) — compromising a later chain key does not reveal earlier message keys.

  This is the property that *justifies* a ratchet over a flat key schedule. We prove the strong
  joint form: the message-key prefix together with the surviving chain key,
  `(keystream G j ck₀, ck_j)`, is indistinguishable from uniform. In particular, given `ck_j`
  (the "compromised" current chain key), the earlier message keys `mk₀ … mk_{j-1}` are
  pseudorandom — they look like independent uniform keys even to an adversary holding `ck_j`.

  This is *stronger* than the plain keystream pseudorandomness of `Chain.lean`: projecting away
  the final key (`Prod.fst`) recovers it. The proof is the same `n`-step hybrid, with the final
  chain key carried along as an extra output; each hop reduces to PRG security of the block
  generator `G`, via the same split-bijection `glue`. We reuse Chain.lean's helpers
  (`splitPure_bijective`, `prod_uniform_bind`, `uniformVec_eq`).
-/
import Demos.Ratchet.Chain
import Demos.Ratchet.Chacha

open Aeneas Std OracleComp ENNReal PRGScheme RatchetSecurity

namespace RatchetFS

/-- The chain key after `n` ratchet steps from `ck`. -/
def finalKey (G : Key → Blk64) : ℕ → Key → Key
  | 0, ck => ck
  | n + 1, ck => finalKey G n (step G ck).1

/-- The forward-secrecy view of the ratchet as a PRG: from a seed chain key, output **both** the
`j` message keys *and* the surviving chain key `ck_j`. Pseudorandomness of this is forward
secrecy: the message keys stay uniform-looking even given the final chain key. -/
def fsGen (G : Key → Blk64) (j : ℕ) : PRGScheme Key (List.Vector Key j × Key) where
  gen ck := (keystream G j ck, finalKey G j ck)

/-- The hybrid reduction stream for forward secrecy: like `redStream`, but it also outputs the
final chain key. For the leading uniform front it samples keys; at the challenge depth it splits
`b` (message-key half emitted, chain-key half seeds the real suffix, which determines `ck_j`);
when the front covers the whole length the final key is a fresh uniform reseed. -/
def fsRedStream (G : Key → Blk64) (b : Blk64) :
    (J : ℕ) → (i : ℕ) → ProbComp (List.Vector Key J × Key)
  | 0, _ => do let fin ← $ᵗ Key; pure (.nil, fin)
  | n + 1, 0 =>
      pure ((splitPure b).2 ::ᵥ keystream G n (splitPure b).1, finalKey G n (splitPure b).1)
  | n + 1, i + 1 => do
      let k ← $ᵗ Key
      let r ← fsRedStream G b n i
      pure (k ::ᵥ r.1, r.2)

/-- The forward-secrecy reduction adversary for hop `i`. -/
def fsReduction (G : Key → Blk64) (J i : ℕ)
    (A : PRGAdversary (List.Vector Key J × Key)) : PRGAdversary Blk64 :=
  fun b => fsRedStream G b J i >>= A

/-- With the challenge block a real `G s` and nothing idealized, the reduction stream is exactly
the forward-secrecy output (message keys + final key) of the real chain from `s`. -/
theorem fsRedStream_real_zero (G : Key → Blk64) (s : Key) (J : ℕ) :
    fsRedStream G (G s) (J + 1) 0 = pure (keystream G (J + 1) s, finalKey G (J + 1) s) := by
  simp only [fsRedStream, keystream, finalKey, step]

/-- **The forward-secrecy hybrid hop.** Idealizing hop `i` (challenge block uniform) gives the
same output distribution as hop `i+1`'s real experiment. Mirrors `RatchetSecurity.glue`, with
the surviving chain key carried along; the `n = 1` boundary needs an extra independent-draw swap
because there the final key is a fresh reseed rather than chain-derived. -/
theorem fsGlue (G : Key → Blk64) :
    ∀ (n i : ℕ) (A : (List.Vector Key n × Key) → ProbComp Bool),
      Pr[= true | (do let b ← $ᵗ Blk64; fsRedStream G b n i >>= A)]
        = Pr[= true | (do let s ← $ᵗ Key; fsRedStream G (G s) n (i + 1) >>= A)] := by
  intro n
  induction n with
  | zero =>
    intro i A
    simp only [fsRedStream, bind_assoc, pure_bind]
    rw [probOutput_bind_const ($ᵗ Blk64) (do let fin ← $ᵗ Key; A (.nil, fin)) true,
        probOutput_bind_const ($ᵗ Key) (do let fin ← $ᵗ Key; A (.nil, fin)) true]
    simp
  | succ m ih =>
    intro i A
    cases i with
    | zero =>
      rw [show (do let b ← $ᵗ Blk64; fsRedStream G b (m + 1) 0 >>= A)
            = ($ᵗ Blk64) >>= fun b =>
                (fun p : Key × Key => A (p.2 ::ᵥ keystream G m p.1, finalKey G m p.1))
                  (splitPure b) from by simp only [fsRedStream, pure_bind]]
      rw [probOutput_bind_bijective_uniform_cross (α := Blk64) splitPure splitPure_bijective
            (fun p : Key × Key => A (p.2 ::ᵥ keystream G m p.1, finalKey G m p.1)) true,
          prod_uniform_bind]
      cases m with
      | zero =>
        simp only [keystream, finalKey]
        rw [probOutput_bind_bind_swap ($ᵗ Key) ($ᵗ Key) (fun a b => A (b ::ᵥ .nil, a)) true]
        rw [show (do let s ← $ᵗ Key; fsRedStream G (G s) 1 1 >>= A)
              = ($ᵗ Key) >>= fun _ => (do let k ← $ᵗ Key; let fin ← $ᵗ Key; A (k ::ᵥ .nil, fin))
                from by simp only [fsRedStream, bind_assoc, pure_bind]]
        rw [probOutput_bind_const ($ᵗ Key)
              (do let k ← $ᵗ Key; let fin ← $ᵗ Key; A (k ::ᵥ .nil, fin)) true]
        simp
      | succ m' =>
        rw [show (do let s ← $ᵗ Key; fsRedStream G (G s) (m' + 2) 1 >>= A)
              = ($ᵗ Key) >>= fun s => ($ᵗ Key) >>= fun k =>
                  A (k ::ᵥ keystream G (m' + 1) s, finalKey G (m' + 1) s) from by
              simp only [fsRedStream, keystream, finalKey, step, pure_bind, bind_assoc]]
    | succ j =>
      rw [show (do let b ← $ᵗ Blk64; fsRedStream G b (m + 1) (j + 1) >>= A)
            = ($ᵗ Blk64) >>= fun b => ($ᵗ Key) >>= fun k =>
                fsRedStream G b m j >>= fun r => A (k ::ᵥ r.1, r.2) from by
          simp only [fsRedStream, bind_assoc, pure_bind]]
      rw [probOutput_bind_bind_swap ($ᵗ Blk64) ($ᵗ Key)
            (fun b k => fsRedStream G b m j >>= fun r => A (k ::ᵥ r.1, r.2)) true]
      rw [probOutput_bind_congr' ($ᵗ Key) true (fun k => ih j (fun r => A (k ::ᵥ r.1, r.2)))]
      rw [show (do let s ← $ᵗ Key; fsRedStream G (G s) (m + 1) (j + 2) >>= A)
            = ($ᵗ Key) >>= fun s => ($ᵗ Key) >>= fun k =>
                fsRedStream G (G s) m (j + 1) >>= fun r => A (k ::ᵥ r.1, r.2) from by
          simp only [fsRedStream, bind_assoc, pure_bind]]
      rw [probOutput_bind_bind_swap ($ᵗ Key) ($ᵗ Key)
            (fun s k => fsRedStream G (G s) m (j + 1) >>= fun r => A (k ::ᵥ r.1, r.2)) true]

/-- **Endpoint (real).** Hop-`0`'s real experiment is the forward-secrecy real experiment. -/
theorem fs_real_start (G : Key → Blk64) (n : ℕ) (A : PRGAdversary (List.Vector Key n × Key)) :
    Pr[= true | prgRealExp (blockPRG G) (fsReduction G n 0 A)]
      = Pr[= true | prgRealExp (fsGen G n) A] := by
  cases n with
  | zero =>
    simp only [PRGScheme.prgRealExp, fsReduction, fsGen, fsRedStream, finalKey,
      bind_assoc, pure_bind]
    rw [probOutput_bind_const ($ᵗ Key) (do let fin ← $ᵗ Key; A (.nil, fin)) true]
    simp
  | succ J =>
    have h : prgRealExp (blockPRG G) (fsReduction G (J + 1) 0 A)
        = prgRealExp (fsGen G (J + 1)) A := by
      simp only [PRGScheme.prgRealExp, fsReduction, blockPRG, fsGen]
      refine bind_congr fun s => ?_
      rw [fsRedStream_real_zero, pure_bind]
    rw [h]

/-- The all-idealized reduction stream is `n` independent uniform message keys plus an
independent uniform final key. -/
theorem fsRedStream_diag (G : Key → Blk64) (b : Blk64) :
    ∀ n, fsRedStream G b n n
      = (do let v ← uniformVec n; let fin ← $ᵗ Key; pure (v, fin)) := by
  intro n
  induction n with
  | zero => simp only [fsRedStream, uniformVec, pure_bind]
  | succ n ih => simp only [fsRedStream, uniformVec, ih, bind_assoc, pure_bind]

/-- **Endpoint (ideal).** Hop-`n`'s real experiment is the ideal experiment: `n` uniform message
keys together with a uniform final chain key (uniform over `List.Vector Key n × Key`). -/
theorem fs_ideal_end (G : Key → Blk64) (n : ℕ) (A : PRGAdversary (List.Vector Key n × Key)) :
    Pr[= true | prgRealExp (blockPRG G) (fsReduction G n n A)]
      = Pr[= true | (prgIdealExp A : ProbComp Bool)] := by
  simp only [PRGScheme.prgRealExp, PRGScheme.prgIdealExp, fsReduction, blockPRG]
  have hcomp : ($ᵗ Key >>= fun s => fsRedStream G (G s) n n >>= A)
      = ($ᵗ Key >>= fun _ => (do let v ← uniformVec n; let fin ← $ᵗ Key; A (v, fin))) := by
    refine bind_congr fun s => ?_
    rw [fsRedStream_diag]; simp only [bind_assoc, pure_bind]
  rw [hcomp, probOutput_bind_const ($ᵗ Key)
      (do let v ← uniformVec n; let fin ← $ᵗ Key; A (v, fin)) true,
    prod_uniform_bind, uniformVec_eq n (fun v => do let fin ← $ᵗ Key; A (v, fin))]
  simp

/-- **Consecutive hybrids glue.** Hop `i`'s ideal experiment is hop `i+1`'s real experiment. -/
theorem fs_ideal_eq_next (G : Key → Blk64) (n i : ℕ)
    (A : PRGAdversary (List.Vector Key n × Key)) :
    Pr[= true | (prgIdealExp (fsReduction G n i A) : ProbComp Bool)]
      = Pr[= true | prgRealExp (blockPRG G) (fsReduction G n (i + 1) A)] := by
  simp only [PRGScheme.prgIdealExp, PRGScheme.prgRealExp, fsReduction, blockPRG]
  exact fsGlue G n i A

/-- Hop `i`'s real-experiment winning probability (the forward-secrecy hybrid sequence). -/
noncomputable def fsHyb (G : Key → Blk64) (n : ℕ)
    (A : PRGAdversary (List.Vector Key n × Key)) (i : ℕ) : ℝ :=
  (Pr[= true | prgRealExp (blockPRG G) (fsReduction G n i A)]).toReal

/-- **Forward secrecy (concrete hybrid bound).** The joint pseudorandomness advantage of the
message-key prefix together with the surviving chain key is bounded by the sum, over the `n`
steps, of the block PRG's advantage against the per-step reductions. Hence compromising `ck_n`
leaves the earlier message keys pseudorandom. -/
theorem fs_advantage_le_sum (G : Key → Blk64) (n : ℕ)
    (A : PRGAdversary (List.Vector Key n × Key)) :
    (fsGen G n).prgAdvantage A
      ≤ ∑ i ∈ Finset.range n, (blockPRG G).prgAdvantage (fsReduction G n i A) := by
  have hhop : ∀ i, (blockPRG G).prgAdvantage (fsReduction G n i A)
      = |fsHyb G n A i - fsHyb G n A (i + 1)| := by
    intro i
    unfold PRGScheme.prgAdvantage fsHyb
    rw [fs_ideal_eq_next G n i A]
  have hstart : (fsGen G n).prgAdvantage A = |fsHyb G n A 0 - fsHyb G n A n| := by
    unfold PRGScheme.prgAdvantage fsHyb
    rw [← fs_real_start G n A, ← fs_ideal_end G n A]
  rw [hstart]
  simp_rw [hhop]
  calc |fsHyb G n A 0 - fsHyb G n A n|
      = |∑ i ∈ Finset.range n, (fsHyb G n A i - fsHyb G n A (i + 1))| := by
        rw [Finset.sum_range_sub' (fsHyb G n A) n]
    _ ≤ ∑ i ∈ Finset.range n, |fsHyb G n A i - fsHyb G n A (i + 1)| :=
        Finset.abs_sum_le_sum_abs _ _

/-- **Forward secrecy (asymptotic).** If the block PRG family is secure (negligible advantage
against each per-step reduction) and the number of steps is polynomial, the joint
(message-key prefix, surviving chain key) is pseudorandom — forward secrecy holds. -/
theorem fs_secure_asymptotic
    (G : ℕ → Key → Blk64) (len : ℕ → ℕ)
    (A : ∀ sp, PRGAdversary (List.Vector Key (len sp) × Key))
    (ε : ℕ → ℝ≥0∞) (hε : negligible ε)
    (hbound : ∀ sp, ∀ i < len sp,
      ENNReal.ofReal ((blockPRG (G sp)).prgAdvantage (fsReduction (G sp) (len sp) i (A sp))) ≤ ε sp)
    (hlen : ∃ p : Polynomial ℕ, ∀ sp, len sp ≤ p.eval sp) :
    negligible (fun sp =>
      ENNReal.ofReal ((fsGen (G sp) (len sp)).prgAdvantage (A sp))) := by
  obtain ⟨p, hp⟩ := hlen
  refine negligible_of_le (fun sp => ?_) (negligible_polynomial_mul hε p)
  calc ENNReal.ofReal ((fsGen (G sp) (len sp)).prgAdvantage (A sp))
      ≤ ENNReal.ofReal (∑ i ∈ Finset.range (len sp),
          (blockPRG (G sp)).prgAdvantage (fsReduction (G sp) (len sp) i (A sp))) :=
        ENNReal.ofReal_le_ofReal (fs_advantage_le_sum (G sp) (len sp) (A sp))
    _ = ∑ i ∈ Finset.range (len sp),
          ENNReal.ofReal ((blockPRG (G sp)).prgAdvantage (fsReduction (G sp) (len sp) i (A sp))) :=
        ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)
    _ ≤ ∑ _i ∈ Finset.range (len sp), ε sp :=
        Finset.sum_le_sum (fun i hi => hbound sp i (Finset.mem_range.mp hi))
    _ = (len sp : ℝ≥0∞) * ε sp := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (↑(p.eval sp) : ℝ≥0∞) * ε sp := by gcongr; exact_mod_cast hp sp

/-! ## Forward secrecy of the ratchet over the real extracted ChaCha20. -/

/-- **Forward secrecy for the ChaCha ratchet (concrete bound).** Instantiate at the extracted
ChaCha20 block function: compromising the chain key `ck_n` leaves the earlier message keys
pseudorandom, with advantage bounded by the sum of ChaCha20's per-step PRG advantages. -/
theorem chacha_forward_secrecy_le_sum (n : ℕ)
    (A : PRGAdversary (List.Vector Key n × Key)) :
    (fsGen RatchetChacha.chachaPure n).prgAdvantage A
      ≤ ∑ i ∈ Finset.range n,
          (blockPRG RatchetChacha.chachaPure).prgAdvantage
            (fsReduction RatchetChacha.chachaPure n i A) :=
  fs_advantage_le_sum RatchetChacha.chachaPure n A

/-- **Forward secrecy for the ChaCha ratchet (asymptotic).** If ChaCha20 is a secure PRG and the
chain length is polynomial, the message-key prefix is pseudorandom even given the surviving
chain key. -/
theorem chacha_forward_secrecy_asymptotic (len : ℕ → ℕ)
    (A : ∀ sp, PRGAdversary (List.Vector Key (len sp) × Key))
    (ε : ℕ → ℝ≥0∞) (hε : negligible ε)
    (hbound : ∀ sp, ∀ i < len sp,
      ENNReal.ofReal ((blockPRG RatchetChacha.chachaPure).prgAdvantage
        (fsReduction RatchetChacha.chachaPure (len sp) i (A sp))) ≤ ε sp)
    (hlen : ∃ p : Polynomial ℕ, ∀ sp, len sp ≤ p.eval sp) :
    negligible (fun sp =>
      ENNReal.ofReal ((fsGen RatchetChacha.chachaPure (len sp)).prgAdvantage (A sp))) :=
  fs_secure_asymptotic (fun _ => RatchetChacha.chachaPure) len A ε hε hbound hlen

end RatchetFS
