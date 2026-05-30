/-
  Demo 3 (cost adequacy) — the hybrid reduction is efficient relative to the adversary, in the
  **query-count** cost measure (queries to the uniform-sampling oracle, `IsTotalQueryBound`).
  This is the cost notion native to the pure `ProbComp` model — *not* a wall-clock/circuit-time
  bound; read every "efficient" below as "in uniform-sampling query count".

  The audit's strongest point was that `prgAdvantage` quantifies over *all* adversaries and the
  "reduction is no heavier than `A`" remark was informal. This file makes it a theorem.

  The reduction is `fun b => redStream G b n i >>= A`: it runs `A` once after sampling `i`
  fresh keys and running a deterministic chain. So its query count is `A`'s plus the cost of `i`
  key-samples. We prove exactly that: writing `keyCost` for the query cost of one `$ᵗ Key`, the
  reduction makes at most `i·keyCost + qA` queries when `A` makes at most `qA`. With a polynomial
  chain length the overhead `i·keyCost` is polynomial, so the reduction maps poly-query
  adversaries to poly-query adversaries — efficiency preservation. We then restate ratchet
  security against the **poly-query adversary class**, with the PRG assumption made relative to
  that same class (closing the "all adversaries" gap), the per-hop bound now *derived* from
  PRG-security-against-poly-query rather than assumed for each specific reduction.

  `keyCost` is a **finite constant proved to exist** by `exists_totalQueryBound` (every
  finite-range computation has a finite query bound); its exact *value* is left abstract, since
  computing it would fight VCVio's `SampleableType` instance internals and is irrelevant to the
  argument, which is *relative* to `A`. (The general lemmas `redStream_queryBound` /
  `reduction_queryBound` are stated for an arbitrary such bound `qKey`; the concrete `keyCost`
  instantiates them.)
-/
import Demos.Ratchet.Chain
import VCVio.OracleComp.QueryTracking.QueryBound

open Aeneas Std OracleComp ENNReal PRGScheme RatchetSecurity

namespace RatchetCost

/-- **Every finite-range computation makes finitely many queries.** An `OracleComp` is a finite
term, so it has *some* total query bound; in the `queryBind` case we take the `max` over the
finite oracle range of the continuations' bounds. This discharges the existence of a finite
per-sample query cost (`qKey`) without computing it from the `SampleableType` internals. -/
theorem exists_totalQueryBound {ι : Type} {spec : OracleSpec ι} [spec.Fintype] {α : Type}
    (oa : OracleComp spec α) : ∃ n, IsTotalQueryBound oa n := by
  classical
  induction oa with
  | pure x => exact ⟨0, trivial⟩
  | queryBind t k ih =>
    refine ⟨(Finset.univ.sup fun u => (ih u).choose) + 1,
      isTotalQueryBound_query_bind_iff.mpr ⟨Nat.succ_pos _, fun u => ?_⟩⟩
    have hle : (ih u).choose ≤ (Finset.univ.sup fun u => (ih u).choose) :=
      Finset.le_sup (f := fun u => (ih u).choose) (Finset.mem_univ u)
    exact ((ih u).choose_spec).mono (by omega)

/-- **Reduction overhead.** `redStream` samples `i` keys and runs a deterministic chain, so it
makes at most `i · qKey` uniform-oracle queries, where `qKey` bounds one `$ᵗ Key`. (The base
cases are `pure`, which makes no queries; each recursive step adds one key-sample via
`isTotalQueryBound_bind`.) -/
theorem redStream_queryBound (G : Key → Blk64) (qKey : ℕ)
    (hqKey : IsTotalQueryBound ($ᵗ Key) qKey) (b : Blk64) :
    ∀ (n i : ℕ), IsTotalQueryBound (redStream G b n i) (i * qKey) := by
  intro n
  induction n with
  | zero => intro i; exact trivial
  | succ m ih =>
    intro i
    cases i with
    | zero => exact trivial
    | succ j =>
      have hb : IsTotalQueryBound (redStream G b (m + 1) (j + 1)) (qKey + j * qKey) := by
        simp only [redStream]
        refine isTotalQueryBound_bind (n₂ := j * qKey) hqKey (fun k => ?_)
        refine isTotalQueryBound_bind (n₂ := 0) (ih j) (fun rest => ?_)
        exact (show IsTotalQueryBound (pure (k ::ᵥ rest)) 0 from trivial)
      have he : (j + 1) * qKey = qKey + j * qKey := by ring
      rw [he]; exact hb

/-- **The reduction is no heavier than `A` (a theorem).** For any input block, the reduction
`fun b => redStream G b n i >>= A` makes at most `i · qKey + qA` uniform-oracle queries, where
`qA` bounds `A`. I.e. it runs `A` once plus a bounded, `A`-independent overhead. -/
theorem reduction_queryBound (G : Key → Blk64) (qKey : ℕ)
    (hqKey : IsTotalQueryBound ($ᵗ Key) qKey) (n i : ℕ)
    (A : PRGAdversary (List.Vector Key n)) (qA : ℕ)
    (hA : ∀ v, IsTotalQueryBound (A v) qA) (b : Blk64) :
    IsTotalQueryBound (reduction G n i A b) (i * qKey + qA) := by
  simp only [reduction]
  exact isTotalQueryBound_bind (redStream_queryBound G qKey hqKey b n i) hA

/-! ## The per-key-sample cost is a finite constant. -/

/-- The query cost of sampling one key: a finite constant, by `exists_totalQueryBound`
(we never need its exact value). -/
noncomputable def keyCost : ℕ := (exists_totalQueryBound ($ᵗ Key)).choose

theorem keyCost_spec : IsTotalQueryBound ($ᵗ Key) keyCost :=
  (exists_totalQueryBound ($ᵗ Key)).choose_spec

/-! ## Cost-aware ratchet security: secure against the poly-query adversary class.

This closes the audit's two cost caveats. The PRG hardness assumption (`hPRG`) is now made
**relative to an efficiency class** — distinguishers making at most `(pLen·keyCost + pA)`
queries — rather than all adversaries; and the reductions are **proved** to stay inside that
class (efficiency preservation), via `reduction_queryBound` and `keyCost_spec`. The per-hop
advantage bound (`hbound` of `ratchet_secure_asymptotic`) is then *derived*, not assumed. -/

/-- **Cost-aware asymptotic security.** Let `A` be a distinguisher family making at most
`pA(sp)` queries, and `len` a polynomially-bounded chain length (`len sp ≤ pLen(sp)`). If the
block PRG `G` is `ε`-secure against distinguishers making at most `(pLen·keyCost + pA)(sp)`
queries — for a negligible `ε` — then the ratchet's message-key stream is pseudorandom
(negligible advantage). (Generic over the block generator `G`; instantiate at the extracted
ChaCha20 from `Demos/Ratchet/Chacha.lean`.) Each per-step reduction calls `A` once plus `i ≤ len sp`
key-samples, so it makes `≤ i·keyCost + pA(sp) ≤ (pLen·keyCost + pA)(sp)` queries — inside the
class `hPRG` covers; that fact is proved here, not assumed. -/
theorem ratchet_secure_against_polyQuery
    (G : ℕ → Key → Blk64) (len : ℕ → ℕ)
    (A : ∀ sp, PRGAdversary (List.Vector Key (len sp)))
    (pA : Polynomial ℕ) (hA : ∀ sp v, IsTotalQueryBound (A sp v) (pA.eval sp))
    (pLen : Polynomial ℕ) (hlen : ∀ sp, len sp ≤ pLen.eval sp)
    (ε : ℕ → ℝ≥0∞) (hε : negligible ε)
    (hPRG : ∀ sp (D : PRGAdversary Blk64),
              (∀ x, IsTotalQueryBound (D x) ((pLen * Polynomial.C keyCost + pA).eval sp)) →
              ENNReal.ofReal ((blockPRG (G sp)).prgAdvantage D) ≤ ε sp) :
    negligible (fun sp =>
      ENNReal.ofReal ((ratchetPRG (G sp) (len sp)).prgAdvantage (A sp))) := by
  refine ratchet_secure_asymptotic G len A ε hε ?_ ⟨pLen, hlen⟩
  intro sp i hi
  refine hPRG sp _ (fun b =>
    (reduction_queryBound (G sp) keyCost keyCost_spec (len sp) i (A sp) (pA.eval sp)
      (hA sp) b).mono ?_)
  have hi' : i ≤ pLen.eval sp := hi.le.trans (hlen sp)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  gcongr

end RatchetCost
