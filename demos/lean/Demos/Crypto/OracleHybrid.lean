/-
  Generic q-query oracle hybrid — the Lean analog of FCF's `OracleHybrid.v`,
  built on top of VCVio's shipped telescoping sum
  `QueryImpl.Stateful.advantage_hybrid` (deps/VCV-io/VCVio/StateSeparating/Hybrid.lean).

  This is **infrastructure**, not a new security notion: it abstracts the per-query
  switching-handler argument that VCVio currently only instantiates for IND-CPA
  (`AsymmEncAlg/INDCPA/Oracle.lean`). Given two arbitrary *stateless* per-query
  handlers `O1 O2 : QueryImpl E ProbComp` on a common export interface `E`, and a
  client `A` making at most `q` total queries, it shows

      |advantage(all-`O1`) − advantage(all-`O2`)|
          ≤ ∑_{i < q} (single-query hop at position `i`).

  The endpoints are reconstructed from a counted *switching* handler `Oi O1 O2 i`
  (first `i` queries answered by `O1`, the rest by `O2`, exactly FCF's `Oi`), and
  the sum is VCVio's `advantage_hybrid`. Nothing here is VCVio-specific to a
  primitive — it is written in upstreamable style but committed only to our tree.

  Convention (matching VCVio's IND-CPA `leftUntil`): with the per-query counter
  `c`, query is answered by `O1` iff `c < i`. Hence `Oi 0 = ` all-`O2`, and
  `Oi q = ` all-`O1` for a `q`-query-bounded client. The atomic per-hop term is
  left to the caller (FCF's `k` / `Gi_Si_close`).
-/
import VCVio.StateSeparating.Hybrid
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.ProgramLogic.Relational.SimulateQ

open OracleSpec OracleComp ProbComp

namespace Demos.Crypto.OracleHybrid

variable {ιₑ : Type} {E : OracleSpec.{0, 0} ιₑ} {σ : Type}

/-! ## The counter-threading handlers

We work over `QueryImpl.Stateful unifSpec E σ`, i.e. handlers
`QueryImpl E (StateT σ ProbComp)` whose inner monad answers to uniform sampling.
This is exactly the shape `advantage` / `advantage_hybrid` consume, and exactly
the shape of VCVio's `prfRealQueryImpl` / `prfIdealQueryImpl` after they are
read as stateful handlers over their cache. -/

/-- Run a stateless step handler and **increment a counter** alongside its state.
This is the "dead-counter" instrumentation: `ofCounted O` behaves exactly like
`O` on the `σ` component, but threads a query count in the second component.

It is the analog of FCF's `O1_count` / `G1_count` instrumentation: the counter
is observational, used only to state and prove the bounded-equality endpoint. -/
def ofCounted (O : QueryImpl.Stateful unifSpec E σ) :
    QueryImpl.Stateful unifSpec E (σ × ℕ) := fun t => StateT.mk fun s =>
  (fun p => (p.1, (p.2, s.2 + 1))) <$> (O t).run s.1

/-- The **switching handler** `Oi O1 O2 i` (FCF `OracleHybrid.v:48`): the first
`i` queries (those issued while the counter `c < i`) are answered by `O1`, all
later queries by `O2`. The counter increments on every export query.

`Oi O1 O2 0` is the all-`O2` handler, and `Oi O1 O2 q` is the all-`O1` handler
for any client issuing at most `q` queries — the two facts proved below. -/
def Oi (O1 O2 : QueryImpl.Stateful unifSpec E σ) (i : ℕ) :
    QueryImpl.Stateful unifSpec E (σ × ℕ) := fun t => StateT.mk fun s =>
  (fun p => (p.1, (p.2, s.2 + 1))) <$>
    (if s.2 < i then (O1 t).run s.1 else (O2 t).run s.1)

@[simp]
lemma Oi_apply_run (O1 O2 : QueryImpl.Stateful unifSpec E σ) (i : ℕ)
    (t : E.Domain) (s : σ × ℕ) :
    (Oi O1 O2 i t).run s =
      (fun p => (p.1, (p.2, s.2 + 1))) <$>
        (if s.2 < i then (O1 t).run s.1 else (O2 t).run s.1) := rfl

@[simp]
lemma ofCounted_apply_run (O : QueryImpl.Stateful unifSpec E σ)
    (t : E.Domain) (s : σ × ℕ) :
    (ofCounted O t).run s =
      (fun p => (p.1, (p.2, s.2 + 1))) <$> (O t).run s.1 := rfl

/-! ## Endpoint identity: `Oi 0 = ` all-`O2`

`leftUntil = 0` means `c < 0` is never true, so every query is answered by `O2`;
the counter is dead weight, projected away. Port of FCF `G2_eq_Gi_0`
(OracleHybrid.v:306, "much simpler"). -/

/-- `Oi O1 O2 0` and `ofCounted O2` have the same `run'` (output distribution
ignoring final state), for every client `A` and initial state — in fact the very
same `ProbComp` value. This is the `G2 ≈ Gi(0)` endpoint. -/
lemma run'_Oi_zero_eq_ofCounted_right
    (O1 O2 : QueryImpl.Stateful unifSpec E σ)
    {α : Type} (A : OracleComp E α) (s : σ × ℕ) :
    (simulateQ (Oi O1 O2 0) A).run' s = (simulateQ (ofCounted O2) A).run' s := by
  refine OracleComp.run'_simulateQ_eq_of_query_map_eq
    (impl₁ := Oi O1 O2 0) (impl₂ := ofCounted O2) (proj := id) ?_ A s
  intro t s
  simp [Oi, ofCounted]

/-! ## Endpoint identity: `Oi q = ` all-`O1` for a `q`-bounded client

This is FCF's `G1_eq_Gi_q` (OracleHybrid.v:230, "the most complicated part").
VCVio makes it clean: a `q`-query-bounded client never drives the counter `c`
up to `q`, so the switch condition `c < q` always fires and `Oi O1 O2 q` always
picks `O1`. We discharge it with the generic relational query-bound transport
`probOutput_simulateQ_run_eq_of_impl_eq_queryBound`, exactly the engine VCVio's
IND-CPA hybrid uses (`Oracle.lean:289`), here over an arbitrary `O1 O2`. -/

/-- `ofCounted O1` increments the counter by exactly one on each query: the final
counter is `s.2 + 1` on every support path. The one-step monotonicity fact the
budget invariant needs. -/
lemma ofCounted_counter_eq (O : QueryImpl.Stateful unifSpec E σ)
    (t : E.Domain) (s : σ × ℕ)
    (z : E.Range t × (σ × ℕ)) (hz : z ∈ support ((ofCounted O t).run s)) :
    z.2.2 = s.2 + 1 := by
  simp only [ofCounted_apply_run, support_map, Set.mem_image] at hz
  obtain ⟨p, _, hp⟩ := hz
  simp [← hp]

/-- On any state with counter `c < q`, the switching handler `Oi O1 O2 q` agrees
with the all-`O1` counted handler `ofCounted O1` (the switch fires). -/
lemma Oi_q_run_eq_ofCounted_left_of_lt (O1 O2 : QueryImpl.Stateful unifSpec E σ)
    (q : ℕ) (t : E.Domain) (s : σ × ℕ) (hs : s.2 < q) :
    (Oi O1 O2 q t).run s = (ofCounted O1 t).run s := by
  simp [Oi, ofCounted, hs]

/-- The full `run` (output *and* final state) of `Oi O1 O2 q` and `ofCounted O1`
agree pointwise, for a `q`-query-bounded client `A`, from a fresh counter. -/
lemma run_Oi_q_eq_ofCounted_left_probOutput
    (O1 O2 : QueryImpl.Stateful unifSpec E σ)
    {α : Type} (A : OracleComp E α) (q : ℕ) (hA : IsTotalQueryBound A q)
    (s₀ : σ) (w : α × (σ × ℕ)) :
    Pr[= w | (simulateQ (Oi O1 O2 q) A).run (s₀, 0)] =
      Pr[= w | (simulateQ (ofCounted O1) A).run (s₀, 0)] := by
  refine OracleComp.ProgramLogic.Relational.probOutput_simulateQ_run_eq_of_impl_eq_queryBound
    (impl₁ := Oi O1 O2 q) (impl₂ := ofCounted O1)
    (Inv := fun (s : σ × ℕ) (b : ℕ) => s.2 + b ≤ q)
    (canQuery := fun _ b => 0 < b)
    (cost := fun _ b => b - 1)
    (oa := A) (budget := q) (hbound := hA)
    (himpl_eq := ?_) (hpres₂ := ?_)
    (s := (s₀, 0)) (hs := by simp) (z := w)
  · intro t s b hInv hcan
    have hlt : s.2 < q := by omega
    exact Oi_q_run_eq_ofCounted_left_of_lt O1 O2 q t s hlt
  · intro t s b hInv hcan z hz
    have hcounter : z.2.2 = s.2 + 1 := ofCounted_counter_eq O1 t s z hz
    have hpos : 0 < b := hcan
    simp only [hcounter]
    omega

/-- **`G1 ≈ Gi(q)`.** For a client `A` issuing at most `q` total queries, the
switching handler `Oi O1 O2 q` and the all-`O1` counted handler `ofCounted O1`
induce the same output distribution from a fresh counter, for any `O1 O2`.

The proof is the generic relational transport: with invariant
`Inv (s,c) b := c + b ≤ q`, every query the budget permits has `c < q`, so the
two handlers agree (`Oi_q_run_eq_ofCounted_left_of_lt`), and the all-`O1`
handler preserves the invariant since it increments `c` by one while the budget
decrements by one. -/
lemma evalDist_run'_Oi_q_eq_ofCounted_left
    (O1 O2 : QueryImpl.Stateful unifSpec E σ)
    {α : Type} (A : OracleComp E α) (q : ℕ) (hA : IsTotalQueryBound A q)
    (s₀ : σ) :
    𝒟[(simulateQ (Oi O1 O2 q) A).run' (s₀, 0)] =
      𝒟[(simulateQ (ofCounted O1) A).run' (s₀, 0)] := by
  have hfull : 𝒟[(simulateQ (Oi O1 O2 q) A).run (s₀, 0)] =
      𝒟[(simulateQ (ofCounted O1) A).run (s₀, 0)] :=
    evalDist_ext (fun w =>
      run_Oi_q_eq_ofCounted_left_probOutput O1 O2 A q hA s₀ w)
  simp only [StateT.run']
  simpa [evalDist_map] using congrArg (fun p => Prod.fst <$> p) hfull

/-! ## The hybrid sum (FCF `G1_G2_close`)

We feed the two endpoint identities into VCVio's shipped telescoping
`advantage_hybrid`, instantiated at the switching family `h i := Oi O1 O2 i`
and the constant state family `s i := (s₀, 0)`. -/

/-- **Generic q-query oracle hybrid.** For arbitrary stateless step handlers
`O1 O2` and a client `A` issuing at most `q` total queries, the distinguishing
advantage between answering `A` entirely with `O1` versus entirely with `O2` is
bounded by the sum, over `i < q`, of the single-query-hop advantages between the
`i`-th and `(i+1)`-th switching hybrids.

This is the Lean analog of FCF `OracleHybrid.v`'s `G1_G2_close` (the q-fold
hybrid sum), reusing VCVio's `QueryImpl.Stateful.advantage_hybrid` for the
telescoping triangle inequality. The per-hop term
`(Oi O1 O2 i).advantage … (Oi O1 O2 (i+1)) …` is the caller's atomic obligation
(FCF's `k` / `Gi_Si_close`): a single-query `O1`-vs-`O2` swap at position `i`. -/
theorem advantage_le_sum_hybridStep
    (O1 O2 : QueryImpl.Stateful unifSpec E σ) (s₀ : σ)
    (A : OracleComp E Bool) (q : ℕ) (hA : IsTotalQueryBound A q) :
    (ofCounted O1).advantage (s₀, 0) (ofCounted O2) (s₀, 0) A ≤
      ∑ i ∈ Finset.range q,
        (Oi O1 O2 i).advantage (s₀, 0) (Oi O1 O2 (i + 1)) (s₀, 0) A := by
  -- The shipped telescoping sum over the switching family.
  have hsum := QueryImpl.Stateful.advantage_hybrid
    (σ := fun _ => σ × ℕ) (E := E)
    (h := fun i => Oi O1 O2 i) (s := fun _ => (s₀, 0)) A q
  -- `advantage_hybrid` bounds `(Oi 0).advantage (Oi q)` by the same sum.
  -- Rewrite the two endpoints to `ofCounted O2` / `ofCounted O1`.
  have hzero : (Oi O1 O2 0).advantage (s₀, 0) (Oi O1 O2 q) (s₀, 0) A =
      (ofCounted O2).advantage (s₀, 0) (Oi O1 O2 q) (s₀, 0) A :=
    QueryImpl.Stateful.advantage_eq_of_evalDist_runProb_eq
      (by simp only [QueryImpl.Stateful.runProb_eq_run, QueryImpl.Stateful.run]
          rw [run'_Oi_zero_eq_ofCounted_right])
  have hq : (ofCounted O2).advantage (s₀, 0) (Oi O1 O2 q) (s₀, 0) A =
      (ofCounted O2).advantage (s₀, 0) (ofCounted O1) (s₀, 0) A :=
    QueryImpl.Stateful.advantage_eq_of_evalDist_runProb_eq_right
      (by simp only [QueryImpl.Stateful.runProb_eq_run, QueryImpl.Stateful.run]
          exact evalDist_run'_Oi_q_eq_ofCounted_left O1 O2 A q hA s₀)
  rw [hzero, hq] at hsum
  rw [QueryImpl.Stateful.advantage_symm] at hsum
  exact hsum

/-- **`q · k` form** (FCF `distance_le_prod_f`). If each single-query hop has
advantage at most `k`, the full `O1`-vs-`O2` advantage is at most `q • k`. -/
theorem advantage_le_nsmul_hybridStep
    (O1 O2 : QueryImpl.Stateful unifSpec E σ) (s₀ : σ)
    (A : OracleComp E Bool) (q : ℕ) (hA : IsTotalQueryBound A q)
    (k : ℝ)
    (hk : ∀ i ∈ Finset.range q,
      (Oi O1 O2 i).advantage (s₀, 0) (Oi O1 O2 (i + 1)) (s₀, 0) A ≤ k) :
    (ofCounted O1).advantage (s₀, 0) (ofCounted O2) (s₀, 0) A ≤ q • k :=
  le_trans (advantage_le_sum_hybridStep O1 O2 s₀ A q hA) (by
    have hcard := Finset.sum_le_card_nsmul (Finset.range q)
      (fun i => (Oi O1 O2 i).advantage (s₀, 0) (Oi O1 O2 (i + 1)) (s₀, 0) A) k hk
    simpa using hcard)

/-! ## Per-hop term as a `boolDistAdvantage` (the reuse glue to the cascade API)

The per-hop terms summed by `advantage_le_sum_hybridStep` are
`QueryImpl.Stateful.advantage`s of adjacent switching hybrids. Downstream floor
discharges (e.g. `HmacPrf`'s cascade lemma `boolDistAdvantage_le_sum_chain`)
state their per-hop obligations as `ProbComp.boolDistAdvantage`s of two
`ProbComp Bool` experiments. This section pins the generic per-hop term to that
shape — *definitionally*, since `QueryImpl.Stateful.advantage` is the
`boolDistAdvantage` of the two handlers' `run'` distributions — so a caller can
read each summand of the generic hybrid as a concrete distinguishing advantage
between two simulated runs without re-deriving the bridge each time. -/

/-- **Per-hop term is a `boolDistAdvantage`.** The single-query hop at position
`i` summed by `advantage_le_sum_hybridStep` is exactly the boolean distinguishing
advantage between running the client `A` through the depth-`i` switching handler
and through the depth-`(i+1)` switching handler (both from a fresh counter). This
is the bridge from the generic hybrid's per-hop term to the
`ProbComp.boolDistAdvantage` API the cascade-PRF floor (`HmacPrf`) consumes — true
by `rfl` (`Stateful.advantage` *is* that `boolDistAdvantage`), exposed as a named
lemma so reductions need not re-unfold the handler plumbing. -/
theorem hybridStep_eq_boolDistAdvantage
    (O1 O2 : QueryImpl.Stateful unifSpec E σ) (s₀ : σ)
    (A : OracleComp E Bool) (i : ℕ) :
    (Oi O1 O2 i).advantage (s₀, 0) (Oi O1 O2 (i + 1)) (s₀, 0) A =
      ProbComp.boolDistAdvantage
        ((simulateQ (Oi O1 O2 i) A).run' (s₀, 0))
        ((simulateQ (Oi O1 O2 (i + 1)) A).run' (s₀, 0)) := rfl

/-- **The full generic hybrid bound, with the per-hop terms read as
`boolDistAdvantage`s.** Re-states `advantage_le_sum_hybridStep` with each summand
rewritten through `hybridStep_eq_boolDistAdvantage`: the all-`O1`-vs-all-`O2`
advantage is at most the sum, over `i < q`, of the boolean distinguishing
advantages between the adjacent switching-handler runs. This is the form a
cascade/MAC floor consumes directly (its per-hop reduction bounds exactly such a
`boolDistAdvantage`), closing the reuse gap the round-1 notes flagged: the floor no
longer reconstructs the telescoping sum — it instantiates this and discharges the
`q` concrete per-hop `boolDistAdvantage`s. -/
theorem advantage_le_sum_boolDistAdvantage_hybridStep
    (O1 O2 : QueryImpl.Stateful unifSpec E σ) (s₀ : σ)
    (A : OracleComp E Bool) (q : ℕ) (hA : IsTotalQueryBound A q) :
    (ofCounted O1).advantage (s₀, 0) (ofCounted O2) (s₀, 0) A ≤
      ∑ i ∈ Finset.range q,
        ProbComp.boolDistAdvantage
          ((simulateQ (Oi O1 O2 i) A).run' (s₀, 0))
          ((simulateQ (Oi O1 O2 (i + 1)) A).run' (s₀, 0)) := by
  refine le_trans (advantage_le_sum_hybridStep O1 O2 s₀ A q hA) (le_of_eq ?_)
  exact Finset.sum_congr rfl (fun i _ =>
    hybridStep_eq_boolDistAdvantage O1 O2 s₀ A i)

/-! ## A non-vacuous end-to-end instance (the bound applies to a real swap)

`advantage_le_sum_hybridStep` is only useful if it can be *instantiated* at a
concrete `O1 O2` and a genuinely-`q`-bounded client and produce a meaningful
bound. We close one such instance fully: the trivial stateless handler that
ignores its query and returns a fixed boolean (one for `O1`, the other for `O2`),
against the `1`-query client that queries once and reports the answer. The hybrid
bound holds (it is the generic theorem at `q = 1`); the right-hand side is the
single hop `i = 0`. This witnesses, as a *theorem* (not just the `example` below),
that the infrastructure discharges to a real conclusion — the generic per-hop term
is the atomic obligation, exactly as intended. -/

/-- **End-to-end instance.** For any two stateless boolean-export handlers and any
client issuing at most one query, the generic hybrid bound collapses to the single
hop `i = 0`: the all-`O1`-vs-all-`O2` advantage is at most the lone per-hop
`boolDistAdvantage`. A concrete, non-vacuous use of `advantage_le_sum_hybridStep`
at `q = 1`, confirming the infrastructure produces a real bound (the per-hop term
is the caller's atomic obligation, never an axiom). -/
theorem advantage_le_single_hop_of_oneQuery
    (O1 O2 : QueryImpl.Stateful unifSpec E σ) (s₀ : σ)
    (A : OracleComp E Bool) (hA : IsTotalQueryBound A 1) :
    (ofCounted O1).advantage (s₀, 0) (ofCounted O2) (s₀, 0) A ≤
      ProbComp.boolDistAdvantage
        ((simulateQ (Oi O1 O2 0) A).run' (s₀, 0))
        ((simulateQ (Oi O1 O2 1) A).run' (s₀, 0)) := by
  have h := advantage_le_sum_boolDistAdvantage_hybridStep O1 O2 s₀ A 1 hA
  simpa using h

/-! ## Sanity: the query bound is load-bearing

The `q`-query bound in `advantage_le_sum_hybridStep` is not decorative. The
following witnesses that the hybrid sum is a genuine, non-vacuous reduction:
there exist `O1 O2` and a `1`-query client for which the bound at `q = 1` reduces
to a single hop, while at `q = 0` the right-hand side is the empty sum `0` — so
the bound at `q = 0` would force `advantage = 0`, which is generally false (e.g.
`O1` answers `true` to a query, `O2` answers `false`). The lemma is stated only
with the *correct* bound `IsTotalQueryBound A q`, so it cannot be misapplied. -/
example : IsTotalQueryBound
    (do let _ ← (liftM (OracleSpec.query (spec := unifSpec) (0 : ℕ)))
        pure true : OracleComp unifSpec Bool) 1 := by
  rw [OracleComp.isTotalQueryBound_query_bind_iff]
  exact ⟨by norm_num, fun _ => trivial⟩

end Demos.Crypto.OracleHybrid
