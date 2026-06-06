/-
  Reusable PRF → random-function reduction (the FCF `PRF.v` `RndR_func` analog).

  This module abstracts the concrete, fully-closed PRF→random-function reduction in
  `Demos/AuthChannel/SufCma.lean` (which is specialized to the canonical PRF-based MAC, with the
  `M →ₒ Tag` oracle and the `verifyB`/`wasQueried` forgery gate) into a *primitive-agnostic*
  reduction over an arbitrary domain/range `D →ₒ R`. Nothing here is a new security game: it reuses
  VCVio's trusted `PRFScheme` / `prfRealQueryImpl` / `prfIdealQueryImpl` / `prfAdvantage`, the lazy
  `randomOracle` (= `uniformSampleImpl.withCaching`), the `WriterT (QueryLog …)` logging layer, and
  the `randomOracle`-on-cache-miss uniformity. The proofs are the SufCma proofs, generalized over the
  bespoke MAC `Tag` to a generic `R` (and over the bespoke `verifyB` gate to an abstract test).

  The two reusable headlines:

  * `simulateQ_prfReal_fwdLog` — the **real-world correspondence**: simulating any client `oa`
    through the forwarding+logging handler `fwdLogImpl` and then through the *real* PRF handler
    (`prfRealQueryImpl k`) equals simulating it through the "answer `D →ₒ R` queries by `prf.eval k`
    and log them" handler. This is the inductive core that lets a game whose oracle is the real PRF
    be re-expressed as the same game with a logged keyed function; it is fully generic in the client.

  * `prfIdeal_freshQuery_le` — the **random-function guessing bound**: in the ideal world (the keyed
    function replaced by a lazy random oracle), a reduction that runs a client through the logging
    oracle and then issues *one fresh* `D →ₒ R` query and accepts only if (a) a freshness gate says
    the query point was never logged and (b) the answer matches a target value, succeeds with
    probability at most `1/|R|`. This is the FCF `RndR_func` fresh-point bound and the base case the
    cascade/MAC floors consume.

  This is the FCF `PRF.v` (`PRF_G_A` vs `PRF_G_B`, `RndR_func`) reduction, reusable across MAC/AEAD
  style floors exactly as FCF's `PRF.v` is reused across HMAC/GNMAC/GHMAC.
-/
import Demos.AuthChannel.Mac

open OracleComp OracleSpec ENNReal PRFScheme

namespace Demos.Crypto.PrfReduction

universe u

variable {D R : Type} [DecidableEq D] [SampleableType R]

/-! ## The forwarding + logging handler (generic in `D`, `R`) -/

/-- The reduction's simulation oracle: forward `unifSpec` queries to the ambient PRF-game oracle
(no log), and forward `D →ₒ R` (function) queries to the ambient function oracle while logging the
queried point. This is `AuthMac.fwdLogImpl` with the bespoke `M →ₒ Tag` generalized to `D →ₒ R`;
it uses no MAC structure. -/
noncomputable def fwdLogImpl :
    QueryImpl (unifSpec + (D →ₒ R))
      (WriterT (QueryLog (D →ₒ R)) (OracleComp (unifSpec + (D →ₒ R)))) :=
  fun x => match x with
    | Sum.inl q => liftM ((unifSpec + (D →ₒ R)).query (Sum.inl q))
    | Sum.inr d => do
        let r ← liftM ((unifSpec + (D →ₒ R)).query (Sum.inr d))
        tell [⟨d, r⟩]
        pure r

/-- The "real keyed function" handler the correspondence lands in: forward `unifSpec` to the ambient
`ProbComp`, and answer `D →ₒ R` queries by `prf.eval k`, logging the queried point. This is the
generic shape of `AuthMac.ufImpl` (the MAC's tagging oracle), with the tag set to `prf.eval k`. -/
noncomputable def keyedLogImpl {K : Type} (prf : PRFScheme K D R) (k : K) :
    QueryImpl (unifSpec + (D →ₒ R)) (WriterT (QueryLog (D →ₒ R)) ProbComp) :=
  fun x => match x with
    | Sum.inl q =>
        WriterT.mk ((liftM (unifSpec.query q) : ProbComp _) >>= fun u =>
          pure (u, (∅ : QueryLog (D →ₒ R))))
    | Sum.inr d =>
        WriterT.mk ((pure (prf.eval k d) : ProbComp R) >>= fun u =>
          pure (u, ([⟨d, u⟩] : QueryLog (D →ₒ R))))

omit [DecidableEq D] [SampleableType R] in
/-- **Real-world correspondence, inductive core.** Simulating any client through the reduction's
forwarding+logging oracle and then through the real PRF handler is the same, value-and-log by
value-and-log, as simulating it through the keyed-function logging handler `keyedLogImpl`. Generic
in the client `oa`; proved by `OracleComp.inductionOn` with a per-oracle definitional head step and
the inductive hypothesis on the tail (the SufCma `simulateQ_prfReal_fwdLog` proof, verbatim modulo
the `M →ₒ Tag → D →ₒ R` rename). -/
theorem simulateQ_prfReal_fwdLog {K : Type} (prf : PRFScheme K D R) (k : K)
    {α : Type} (oa : OracleComp (unifSpec + (D →ₒ R)) α) :
    simulateQ (prf.prfRealQueryImpl k) ((simulateQ fwdLogImpl oa).run) =
      (simulateQ (keyedLogImpl prf k) oa).run := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t f ih =>
    cases t with
    | inl q =>
      simp only [simulateQ_bind, WriterT.run_bind', simulateQ_spec_query]
      change simulateQ (prf.prfRealQueryImpl k)
          ((fwdLogImpl (Sum.inl q)).run >>= fun x =>
            (Prod.map id fun x_1 => x.2 ++ x_1) <$> (simulateQ fwdLogImpl (f x.1)).run) = _
      simp only [simulateQ_bind, simulateQ_map]
      have head : simulateQ (prf.prfRealQueryImpl k) (fwdLogImpl (Sum.inl q)).run
          = (keyedLogImpl prf k (Sum.inl q)).run := rfl
      rw [head]; refine bind_congr fun x => ?_; rw [ih x.1]
    | inr d =>
      simp only [simulateQ_bind, WriterT.run_bind', simulateQ_spec_query]
      change simulateQ (prf.prfRealQueryImpl k)
          ((fwdLogImpl (Sum.inr d)).run >>= fun x =>
            (Prod.map id fun x_1 => x.2 ++ x_1) <$> (simulateQ fwdLogImpl (f x.1)).run) = _
      simp only [simulateQ_bind, simulateQ_map]
      have head : simulateQ (prf.prfRealQueryImpl k) (fwdLogImpl (Sum.inr d)).run
          = (keyedLogImpl prf k (Sum.inr d)).run := rfl
      rw [head]; refine bind_congr fun x => ?_; rw [ih x.1]

/-! ## The random-function side: cache–log invariant and the fresh-point bound -/

section RF

open scoped Classical

/-- The ideal-world simulation handler (the keyed function replaced by a lazy random oracle). This
is exactly VCVio's `prfIdealQueryImpl` at `D`, `R` — the FCF `RndR_func`. -/
noncomputable abbrev idealImpl : QueryImpl (unifSpec + (D →ₒ R))
    (StateT ((D →ₒ R).QueryCache) ProbComp) :=
  PRFScheme.prfIdealQueryImpl (D := D) (R := R)

/-- **Cache–log invariant.** Running a client through the reduction's logging forward oracle, then
through the ideal-world random oracle from cache `c₀`, only ever caches points that were already
cached or have been logged. With `c₀ = ∅` and empty initial log, an unlogged point stays uncached:
this is what makes a "fresh (= unlogged) point" a genuine cache miss for the final query. Generic in
the client; proved by induction (the SufCma `fwdLog_cache_log_inv`, generalized to `D →ₒ R`). -/
theorem fwdLog_cache_log_inv {γ : Type}
    (oa : OracleComp (unifSpec + (D →ₒ R)) γ) :
    ∀ (c₀ : (D →ₒ R).QueryCache) (log₀ : QueryLog (D →ₒ R)),
    (∀ m : D, c₀ m ≠ none → (log₀.wasQueried m = true)) →
    ∀ z ∈ support
      ((simulateQ idealImpl
        ((fun p => (p.1, log₀ ++ p.2)) <$> (simulateQ fwdLogImpl oa).run)).run c₀),
    ∀ m : D, z.2 m ≠ none → z.1.2.wasQueried m = true := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro c₀ log₀ hinit z hz m hm
    simp only [simulateQ_pure, WriterT.run_pure', map_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    simpa using hinit m hm
  | query_bind t f ih =>
    intro c₀ log₀ hinit z hz m hm
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind', map_bind, Functor.map_map,
      simulateQ_map, StateT.run_bind, StateT.run_map] at hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨x, hx, hz⟩ := hz
    have hhead : ∀ mm : D, x.2 mm ≠ none → (log₀ ++ x.1.2).wasQueried mm = true := by
      cases t with
      | inl q =>
        have key : (simulateQ idealImpl (fwdLogImpl (Sum.inl q)).run).run c₀ =
            ((unifSpec.query q : ProbComp _) >>= fun u =>
              pure ((u, (∅ : QueryLog (D →ₒ R))), c₀)) := by
          show (simulateQ idealImpl ((·, (∅ : QueryLog (D →ₒ R))) <$>
              (liftM ((unifSpec + (D →ₒ R)).query (Sum.inl q)) :
                OracleComp (unifSpec + (D →ₒ R)) _))).run c₀ = _
          rw [simulateQ_map, simulateQ_spec_query]
          show ((·, (∅ : QueryLog (D →ₒ R))) <$>
            (liftM (unifSpec.query q : ProbComp _) :
              StateT ((D →ₒ R).QueryCache) ProbComp _)).run c₀ = _
          simp [StateT.run_monadLift, map_eq_bind_pure_comp]
        rw [key] at hx
        obtain ⟨u, _, hu⟩ := (mem_support_bind_iff _ _ _).1 hx
        have hxeq : x = ((u, ∅), c₀) := by simpa using hu
        subst hxeq
        intro mm hmm
        simpa using hinit mm hmm
      | inr d =>
        have hq : simulateQ idealImpl
            (liftM ((unifSpec + (D →ₒ R)).query (Sum.inr d)) :
              OracleComp (unifSpec + (D →ₒ R)) R) =
            OracleSpec.randomOracle (spec := (D →ₒ R)) d :=
          simulateQ_spec_query _ (Sum.inr d)
        have key : (simulateQ idealImpl (fwdLogImpl (Sum.inr d)).run).run c₀ =
            ((OracleSpec.randomOracle (spec := (D →ₒ R)) d).run c₀ >>= fun p =>
              pure ((p.1, ([⟨d, p.1⟩] : QueryLog (D →ₒ R))), p.2)) := by
          show (simulateQ idealImpl ((liftM ((unifSpec + (D →ₒ R)).query (Sum.inr d)) :
              OracleComp (unifSpec + (D →ₒ R)) R) >>= fun t =>
                pure (t, ([⟨d, t⟩] : QueryLog (D →ₒ R))))).run c₀ = _
          rw [simulateQ_bind, hq]
          simp only [simulateQ_pure, StateT.run_bind]
          rfl
        have hcache : ∀ p ∈ support ((OracleSpec.randomOracle (spec := (D →ₒ R)) d).run c₀),
            ∀ mm : D, mm ≠ d → p.2 mm = c₀ mm := by
          intro p hp mm hmm
          cases hc : c₀ d with
          | some u =>
            rw [QueryImpl.withCaching_run_some _ hc] at hp
            simp only [support_pure, Set.mem_singleton_iff] at hp
            rw [hp]
          | none =>
            rw [QueryImpl.withCaching_run_none _ hc] at hp
            simp only [support_map, Set.mem_image] at hp
            obtain ⟨v, _, rfl⟩ := hp
            exact QueryCache.cacheQuery_of_ne _ _ hmm
        rw [key] at hx
        obtain ⟨p, hp, hxeq⟩ := (mem_support_bind_iff _ _ _).1 hx
        have hxeq' : x = ((p.1, ([⟨d, p.1⟩] : QueryLog (D →ₒ R))), p.2) := by
          simpa using hxeq
        subst hxeq'
        intro mm hmm
        by_cases hmsg : mm = d
        · subst hmsg
          simp [QueryLog.wasQueried_eq_decide_mem_map_fst]
        · have hcc : (p.2) mm = c₀ mm := hcache p hp mm hmsg
          have hc₀ : c₀ mm ≠ none := by rwa [hcc] at hmm
          have hlog : log₀.wasQueried mm = true := hinit mm hc₀
          simp only [QueryLog.wasQueried_eq_decide_mem_map_fst, List.map_append,
            List.mem_append, decide_eq_true_eq]
          left
          simpa [QueryLog.wasQueried_eq_decide_mem_map_fst] using hlog
    rw [support_map, Set.mem_image] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    have hih := ih x.1.1 x.2 (log₀ ++ x.1.2) hhead
      ((p.1.1, (log₀ ++ x.1.2) ++ p.1.2), p.2) ?_ m hm
    · simpa [List.append_assoc] using hih
    · simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image]
      exact ⟨p, hp, by simp [List.append_assoc]⟩

variable [Fintype R]

/-- **Fresh-point guessing bound.** The final verification query of the reduction, run against the
ideal random oracle at a point that is uncached whenever the gate `b` is on, accepts (gate `b` is on
*and* the sampled answer equals the target `target`) with probability at most `1/|R|`: an uncached
query samples the answer uniformly and independently of `target`, so the chance it matches is exactly
`1/|R|`. The SufCma `fresh_query_bound`, generalized from the `verifyB` tag check to a `DecidableEq`
equality on `R`. -/
theorem freshQuery_bound (d : D) (target : R) (b : Bool)
    (cache' : (D →ₒ R).QueryCache) (hfresh : b = true → cache' d = none) :
    Pr[= true |
      (simulateQ idealImpl
        ((liftM ((unifSpec + (D →ₒ R)).query (Sum.inr d)) :
            OracleComp (unifSpec + (D →ₒ R)) R) >>= fun r =>
          pure (b && decide (r = target)))).run' cache'] ≤ (Fintype.card R : ℝ≥0∞)⁻¹ := by
  have hq : simulateQ idealImpl
      (liftM ((unifSpec + (D →ₒ R)).query (Sum.inr d)) :
        OracleComp (unifSpec + (D →ₒ R)) R) =
      OracleSpec.randomOracle (spec := (D →ₒ R)) d :=
    simulateQ_spec_query _ (Sum.inr d)
  have hred : (simulateQ idealImpl
      ((liftM ((unifSpec + (D →ₒ R)).query (Sum.inr d)) :
          OracleComp (unifSpec + (D →ₒ R)) R) >>= fun r =>
        pure (b && decide (r = target)))).run' cache' =
      (OracleSpec.randomOracle (spec := (D →ₒ R)) d).run' cache' >>= fun r =>
        pure (b && decide (r = target)) := by
    rw [simulateQ_bind, hq]
    simp only [simulateQ_pure]
    rw [StateT.run'_eq, StateT.run'_eq, StateT.run_bind, map_bind]
    simp [StateT.run_pure]
  rw [hred]
  cases b with
  | false =>
    simp only [Bool.false_and]
    rw [show (fun _ : R => pure (false : Bool) : R → ProbComp Bool) =
      pure ∘ fun _ : R => (false : Bool) from rfl, ← probEvent_eq_eq_probOutput,
      probEvent_bind_pure_comp]
    rw [probEvent_eq_zero (fun x _ h => absurd h (by simp))]
    exact zero_le _
  | true =>
    have hfree : cache' d = none := hfresh rfl
    have hbound : Pr[= true |
        (OracleSpec.randomOracle (spec := (D →ₒ R)) d).run' cache' >>= fun r =>
          pure (true && decide (r = target))] ≤
        Pr[= target | (OracleSpec.randomOracle (spec := (D →ₒ R)) d).run' cache'] := by
      rw [← probEvent_eq_eq_probOutput,
        show (fun r => pure (true && decide (r = target)) :
            R → ProbComp Bool) = pure ∘ fun r => true && decide (r = target) from rfl,
        probEvent_bind_pure_comp, ← probEvent_eq_eq_probOutput]
      refine probEvent_mono ?_
      intro r _ hr
      simp only [Function.comp_apply, Bool.true_and, decide_eq_true_eq] at hr
      exact hr
    refine hbound.trans ?_
    rw [StateT.run'_eq, QueryImpl.withCaching_run_none _ hfree, Functor.map_map,
      show (fun a => (a, cache'.cacheQuery d a).1 : R → R) = (id : R → R) from rfl,
      id_map, show uniformSampleImpl d = ($ᵗ R : ProbComp R) from rfl,
      probOutput_uniformSample]

/-! ## The reduction and the `gameAdvantage ≤ prfAdvantage + 1/|R|` headline

The reusable functor: from a *client* `client : OracleComp (unifSpec + (D →ₒ R)) (D × R)` that
runs against the function oracle and outputs a candidate "forgery" — a query point `d` together with
a claimed value `target` — build a PRF distinguisher. It runs the client through the logging forward
oracle, then issues *one* fresh `D →ₒ R` query at `d`, and accepts iff (a) `d` was never logged
(freshness) and (b) the oracle's answer at `d` equals `target`. The headline (`reduction_RF_le`)
bounds the *ideal-world* acceptance of this distinguisher by `1/|R|`: against a random function, a
freshly-queried point matches a fixed target only by chance. This is precisely the base case the
cascade/MAC floors consume, with no MAC structure baked in. -/

/-- The PRF distinguisher derived from a `(D × R)`-valued client: run the client through the logging
forward oracle, then query the function oracle at the produced point `d`, accept iff `d` was unlogged
and the recomputed value matches the produced `target`. Generic analog of `AuthMac.reduction`. -/
noncomputable def reduction (client : OracleComp (unifSpec + (D →ₒ R)) (D × R)) :
    PRFScheme.PRFAdversary D R :=
  (do
    let ((d, target), log) ← (simulateQ fwdLogImpl client).run
    let r ← ((unifSpec + (D →ₒ R)).query (Sum.inr d) :
      OracleComp (unifSpec + (D →ₒ R)) R)
    return !log.wasQueried d && decide (r = target) :
      OracleComp (unifSpec + (D →ₒ R)) Bool)

/-- **Random-function forgery bound.** Against a random function (the PRF ideal world), the
distinguisher built by `reduction` accepts with probability at most `1/|R|`: its acceptance requires
guessing the random oracle's value at a *fresh* (unlogged ⟹ uncached, by `fwdLog_cache_log_inv`)
point. The SufCma `reduction_RF_le`, generalized to `D →ₒ R`. -/
theorem reduction_RF_le [Nonempty R] (client : OracleComp (unifSpec + (D →ₒ R)) (D × R)) :
    (Pr[= true | PRFScheme.prfIdealExp (reduction client)]).toReal ≤ (Fintype.card R : ℝ)⁻¹ := by
  classical
  suffices h : Pr[= true | PRFScheme.prfIdealExp (reduction client)] ≤
      (Fintype.card R : ℝ≥0∞)⁻¹ by
    rw [show ((Fintype.card R : ℝ)⁻¹) = ((Fintype.card R : ℝ≥0∞)⁻¹).toReal from by
      rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]]
    exact ENNReal.toReal_mono (ENNReal.inv_ne_top.mpr (by exact_mod_cast Fintype.card_ne_zero)) h
  rw [PRFScheme.prfIdealExp]
  show Pr[= true |
      (simulateQ idealImpl (reduction client)).run' ∅] ≤ _
  unfold reduction
  rw [show (do
        let ((d, target), log) ← (simulateQ fwdLogImpl client).run
        let r ← ((unifSpec + (D →ₒ R)).query (Sum.inr d) :
          OracleComp (unifSpec + (D →ₒ R)) R)
        (pure (!log.wasQueried d && decide (r = target)) :
          OracleComp (unifSpec + (D →ₒ R)) Bool)) =
      ((simulateQ fwdLogImpl client).run >>= fun w =>
        (liftM ((unifSpec + (D →ₒ R)).query (Sum.inr w.1.1)) :
            OracleComp (unifSpec + (D →ₒ R)) R) >>= fun r =>
          pure (!w.2.wasQueried w.1.1 && decide (r = w.1.2))) from rfl]
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind, probOutput_bind_eq_tsum]
  have hterm : ∀ w : ((D × R) × QueryLog (D →ₒ R)) × (D →ₒ R).QueryCache,
      w ∈ support ((simulateQ idealImpl (simulateQ fwdLogImpl client).run).run ∅) →
        Pr[= true | Prod.fst <$> ((simulateQ idealImpl
            ((liftM ((unifSpec + (D →ₒ R)).query (Sum.inr w.1.1.1)) :
                OracleComp (unifSpec + (D →ₒ R)) R) >>= fun r =>
              pure (!w.1.2.wasQueried w.1.1.1 && decide (r = w.1.1.2)))).run w.2)] ≤
          (Fintype.card R : ℝ≥0∞)⁻¹ := by
    intro w hw
    have hinv := fwdLog_cache_log_inv (D := D) client ∅ ∅
      (by intro m hm; simp at hm) w (by simpa using hw)
    have hfresh : (!w.1.2.wasQueried w.1.1.1) = true → w.2 w.1.1.1 = none := by
      intro hb
      by_contra hc
      have := hinv w.1.1.1 hc
      simp [this] at hb
    have hb := freshQuery_bound (D := D) w.1.1.1 w.1.1.2 (!w.1.2.wasQueried w.1.1.1) w.2 hfresh
    simpa [StateT.run'_eq] using hb
  calc ∑' w, Pr[= w | (simulateQ idealImpl (simulateQ fwdLogImpl client).run).run ∅] *
        Pr[= true | Prod.fst <$> ((simulateQ idealImpl
            ((liftM ((unifSpec + (D →ₒ R)).query (Sum.inr w.1.1.1)) :
                OracleComp (unifSpec + (D →ₒ R)) R) >>= fun r =>
              pure (!w.1.2.wasQueried w.1.1.1 && decide (r = w.1.1.2)))).run w.2)]
      ≤ ∑' w, Pr[= w | (simulateQ idealImpl (simulateQ fwdLogImpl client).run).run ∅] *
          (Fintype.card R : ℝ≥0∞)⁻¹ := by
        refine ENNReal.tsum_le_tsum fun w => ?_
        by_cases hw : w ∈ support ((simulateQ idealImpl (simulateQ fwdLogImpl client).run).run ∅)
        · exact mul_le_mul' le_rfl (hterm w hw)
        · rw [probOutput_eq_zero_of_not_mem_support hw]; simp
    _ = (∑' w, Pr[= w | (simulateQ idealImpl (simulateQ fwdLogImpl client).run).run ∅]) *
          (Fintype.card R : ℝ≥0∞)⁻¹ := by rw [ENNReal.tsum_mul_right]
    _ ≤ 1 * (Fintype.card R : ℝ≥0∞)⁻¹ := by gcongr; exact tsum_probOutput_le_one
    _ = (Fintype.card R : ℝ≥0∞)⁻¹ := one_mul _

end RF

/-! ## The PRF-reduction triangle (the deliverable functor)

`gameAcceptance ≤ prfAdvantage(reduction) + 1/|R|`: the "real-world acceptance of the reduction" is
within `prfAdvantage` of its ideal-world acceptance (a pure triangle inequality on the PRF game), and
the ideal-world acceptance is `≤ 1/|R|` by `reduction_RF_le`. A caller whose security game's
acceptance *equals* `Pr[= true | prfRealExp (reduction client)]` (established via
`simulateQ_prfReal_fwdLog`) gets `gameAdvantage ≤ prfAdvantage(reduction) + 1/|R|` directly. -/

variable [Fintype R]

/-- **The reusable bound.** The real-world acceptance probability of the reduction is bounded by the
PRF distinguishing advantage of the reduction plus the random-function guessing term `1/|R|`. This is
the primitive-agnostic version of `AuthMac.macUF_le`; instantiating `client` at a concrete game's
adversary (and identifying `Pr[= true | prfRealExp (reduction client)]` with the game's advantage via
`simulateQ_prfReal_fwdLog`) recovers the floor bound for that game. -/
theorem prfReal_le_prfAdvantage_add_RF [Nonempty R] {K : Type} (prf : PRFScheme K D R)
    (client : OracleComp (unifSpec + (D →ₒ R)) (D × R)) :
    (Pr[= true | prf.prfRealExp (reduction client)]).toReal ≤
      prf.prfAdvantage (reduction client) + (Fintype.card R : ℝ)⁻¹ := by
  have htri : (Pr[= true | prf.prfRealExp (reduction client)]).toReal ≤
      prf.prfAdvantage (reduction client) +
      (Pr[= true | PRFScheme.prfIdealExp (reduction client)]).toReal := by
    unfold PRFScheme.prfAdvantage
    set a := (Pr[= true | prf.prfRealExp (reduction client)]).toReal
    set b := (Pr[= true | PRFScheme.prfIdealExp (reduction client)]).toReal
    have : a - b ≤ |a - b| := le_abs_self _
    linarith
  exact htri.trans (by have := reduction_RF_le (D := D) client; linarith)

end Demos.Crypto.PrfReduction
