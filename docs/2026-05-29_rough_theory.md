# Provable correctness (PL / FV)  <->  game-based security

How the standard PL/formal-verification notion of provable correctness lines up
with game-based cryptographic security, and how a stack of proofs from real code
up to a security game fits one framework.

(updated 2026-05-29)

## 0. Thesis

ONE relation runs through the whole stack:

  ~[eps]   -- "no PPT adversary distinguishes the two sides with advantage > eps"

with two special cases:
  ~[0]  = exact behavioral / observational equivalence   (the PL `equiv`)
  ~c    = ~[negl]                                         (computational indist.)

ONE notion, ADEQUACY ("this boundary preserves security"), recurs at three
boundaries:
  (i)   program-equivalence boundary   -- exact rewrite preserves security
  (ii)  game-hop boundary              -- each hop perturbs advantage by <= eps
  (iii) language / code boundary       -- the translation reflects adversaries

A security proof is then a PATH

  P_concrete  ~[eps_0]  G_0  ~[eps_1]  G_1  ...  ~[eps_n]  IDEAL

and the theorem is the SUM of the edge labels:

  Adv(A ; P_concrete)  <=  eps_0 + eps_1 + ... + eps_n  +  base(IDEAL)

sound iff the path is short (poly-many hops) and Sum eps is negligible.

The rest of the note develops each piece.

================================================================================

## 1. PL notion of correctness

  P \in Program
  Trace      : Seq(Event)
  semantics  : Program -> P(Trace)        -- a program denotes a SET of traces

  equiv P1 P2  =  semantics(P1) = semantics(P2)        -- exact equality

  adequacy:  equiv P1 P2  =>  security P1 = security P2
             (security is a property of the denotation, not of syntax)

The two-way version of adequacy is FULL ABSTRACTION. The universal "for all
contexts C[.]" of contextual equivalence is the quantifier to watch: crypto
keeps it but bounds it.

(Reads as a simulation-based notion of correctness -- see sec. 4.)

================================================================================

## 2. Game-based notions of security

Three substitutions turn PL `equiv` into crypto `equiv`:

  P(Trace)       ->  Dist(Trace)       nondeterminism      -> probability
  =              ->  ~c                exact equality       -> comput. indist.
  context C[.]   ->  PPT Adversary     all contexts         -> bounded context

So:
  semantics : Program -> Dist(Trace)
  P1 ~c P2  =  forall PPT D. | Pr[D(semantics P1)=1] - Pr[D(semantics P2)=1] | <= negl

  Adv      \in Adversary       -- PPT; the bounded "context" C[.]
  Game[Adv] \in Program        -- challenger composed with the adversary

Two shapes of game:

(1) Indistinguishability games (decisional): SECURITY IS AN EQUIV.
      secure  =  Game_0 ~c Game_1
      e.g. IND-CPA: Game_b encrypts m_b.
      -> exactly the PL `equiv` line, `=` weakened to `~c`, the two programs
         being two challenger configs.

(2) Search / forgery games: SECURITY IS A TRACE PREDICATE (bounded safety).
      W \subseteq Trace                              -- "win" / "bad" set
      secure  =  forall PPT Adv. Pr[ trace(Game[Adv]) \in W ] <= trivial + negl
      e.g. EUF-CMA: W = "Adv emitted a fresh valid forgery".
      -> a quantitative, resource-bounded probabilistic safety property
         (hyperproperty).

================================================================================

## 3. Adequacy, re-read = the game-hopping lemma

  PL:     equiv P1 P2   =>   security P1  =  security P2
  crypto: P1 ~c P2      =>   | security P1 - security P2 | <= negl

`security` is Lipschitz / continuous w.r.t. the `~c` pseudometric. So a proof is
a chain  Game_0 ~c Game_1 ~c ... ~c Game_n , and adequacy transports the
advantage along each hop with negligible loss.

  (Shoup, "Sequences of Games"; Bellare-Rogaway code-based games;
   mechanized as pRHL in EasyCrypt.)

================================================================================

## 4. Simulation-based  <->  game-based

  simulation-based (ideal/real, UC):
    real(pi) ~c ideal(F)
      = forall env Z, forall real Adv. exists Sim. Z can't distinguish
      = contextual equiv / refinement of spec F,
        Sim = the forward-simulation witness (Abadi-Lamport refinement map).

  simulation-based  =>    game-based      ideal world makes W impossible; ~c
                                          carries negl to the real world.
  game-based        =/=>  simulation-based  one property < full refinement.

  UC extra: ~c is a CONGRUENCE (closed under composition) -> composition thm.
  Bare game-based need not compose.
  Crypto analogue of full-abstraction / congruence  vs.  proving one property.

================================================================================

## 5. One framework for the stack

Goal:  P_concrete == G_0 == G_1 == ... == IDEAL  in a single theory.

The trap: `==` is OVERLOADED. The links are not one relation:
  - exact (PL refinement / observational eq):                       cost 0
      inlining, dead code, eager<->lazy sampling, reorder indep samples
  - statistical ("up to bad", Fundamental Lemma):                   cost <= Pr[bad]
  - computational (reduction to assumption):                        cost eps_assump(B)
  - terminal step to IDEAL: NOT a program eq; it EVALUATES Adv on the
      final game (= 0 or trivial by inspection).

Forcing all into one `==` breaks:
  (a) collapse to exact dist. equality -> reduction steps don't typecheck
      (~c is assumption-contingent, holds only vs bounded A); or
  (b) keep `==` = ~c throughout         -> ~c is not transitive for an
      unbounded number of hops (see side-condition below).

Fix: don't use an equivalence. Use the advantage-GRADED relation (a pseudometric):

  P ~[eps] Q   "no PPT A distinguishes P,Q with advantage > eps"

Two laws make the chain compose:
  exact:     P ~[0] Q                                  subsumes every PL-exact step
  triangle:  P ~[eps] Q,  Q ~[eps'] R  =>  P ~[eps+eps'] R     compose = ADD

Theorem = the sum:
  Adv(A ; P_concrete)  <=  eps_0 + eps_1 + ... + eps_n  +  base(IDEAL)
  each eps_i \in { 0 | statistical-distance | reduction-term }.

Glue to the PL half: the sec.-1 `adequacy` line IS the eps=0 link.
  P_concrete  ~[0]  G_0  ~[eps_1]  G_1  ...  ~[eps_n]  IDEAL
  (vertical implementation-correctness refinement, then horizontal game hops.)

SOUNDNESS SIDE-CONDITION (what a single `==` hides):
  ~[eps] / ~c is transitive only for a POLY number of hops.
  Must check Sum eps_i is negligible. If the chain length depends on a parameter
  (e.g. n sessions / ratchet steps in Signal) you get n*eps -- sound iff n = poly.
  A naive `==`-chain conceals this; the graded relation forces you to discharge it.

Established realizations of exactly this framework:
  - code-based games + Fundamental Lemma         (Bellare-Rogaway)
  - pRHL / apRHL ((eps,delta), composes by +)    (EasyCrypt)        <- canonical
  - State-Separating Proofs                       (Brzuska et al.)   <- modular,
      packages/oracles, monoidal composition, functorial reductions; fits Signal
  - categorical: morphisms in a category enriched over the advantage
      quantale ([0,1], <=, +); the chain is composition.

================================================================================

## 6. The code boundary (tool-agnostic): an adequate translation

Reaching real code = crossing a LANGUAGE boundary via a translation
  T : L_impl -> Model        (Rust -> proof-assistant term is one instance)
Bottom node = T(P_concrete). To slot into the ~[eps] chain, T must be a
SEMANTICS-PRESERVING translation -- this IS the sec.-1 `adequacy` line, now
applied to T. It is a meta-theorem about the tool, not a hop in the chain.

"Fits the framework" requires, in INCREASING strength:

  1. value adequacy        [[P]] = [[T(P)]] on outputs.
       what functional-correctness tools give. necessary, NOT sufficient.
  2. cost adequacy         PPT-in-Model  <=>  PPT-against-code  (poly-related).
       needed so the eps_i (advantages vs BOUNDED A) transfer across the
       boundary. translating to a PURE function erases the cost/timing
       accounting the whole ~[eps] framework quantifies over.
  3. observation adequacy  Model leakage fn over-approximates what the REAL
       adversary sees. anything unmodeled (timing, faults, memory) = an
       explicit TRUSTED assumption, OUTSIDE eps. (side channels live here.)

Direction that makes security flow DOWN to real code:
  want        G_0 secure (model)  =>  P_concrete secure (real)
  contrapos:  real attack  =>  model attack
  => T must REFLECT adversaries (every concrete A maps to a model A, adv up to negl).
  This is exactly a COMPUTATIONAL-SOUNDNESS theorem (Abadi-Rogaway;
  Backes-Pfitzmann-Waidner): abstract security => concrete security, provided the
  abstraction reflects all concrete adversaries.
  (reflecting = soundness, what you need. preserving / no-false-attacks = full
   abstraction; a bonus, not required for the implication.)

Enriched-category view: T is a FUNCTOR between two ~[eps]-enriched categories;
soundness = T is non-expansive ( d(TP,TQ) >= d(P,Q) ). A functional-correctness-
only tool is a functor on the UNDERLYING discrete categories -- it forgets the
metric enrichment. Requirement: T must be an ENRICHED functor.

Net: the code link contributes an ~[eps_T] edge (eps_T = 0 iff T is exactly
adequate at all three levels) that REFLECTS adversaries; model-security then
transfers to code under the SAME Sum-eps / poly-hops side-condition that governs
the rest of the stack -- end to end.

================================================================================

## 7. Instance: Aeneas (Rust -> Lean)

Direction: Aeneas LIFTS Rust -> a pure functional model in a proof assistant
  (Rust --Charon--> LLBC --Aeneas--> Lean/F*/Coq).
It is NOT extraction (PA -> code); it is the reverse. Real libsignal Rust is the
SOURCE; the Lean model is derived. (So "T" of sec. 6 = Charon+Aeneas.)

Output shape:  f_rust : Input -> Output    -- PURE, TOTAL, deterministic.
Aeneas eliminates borrows/state into pure functions, but crypto games are
PROBABILISTIC + STATEFUL (sampling, oracles, adaptive A). Impedance mismatch.

Reconcile: randomness/state become EXPLICIT INPUTS; the game layer binds them.
  OsRng  ->  explicit  coins : Bytes  parameter of f_rust
  G_0 A  =  do { coins <- sample; ... f_rust coins ... }   -- PMF monad binds coins

So the bottom link  P_concrete ~[0] G_0  SPLITS into two obligations:
  (a) functional    f_rust = f_spec       -- Aeneas proves this, eps=0, in Lean
  (b) idealization  G_0 from f_spec faithfully models protocol execution
                                           -- a modeling assumption, definitional
Aeneas discharges (a); the crypto framework does the hops; (b) is the glue
(modeling bugs hide here).

Assembled stack (Lean):
  real Rust (libsignal core)
     | Charon + Aeneas        (rng -> explicit coins)
     v
  f_rust : Coins -> State -> Output        [pure, Lean]
     | (a)  f_rust = f_spec                 eps = 0
     v
  f_spec
     | wrap: PMF monad binds coins; expose oracles to A
     v
  G_0 : Adversary -> PMF Bool
     | ~[eps_1] G_1 ~ ... ~[eps_n]  IDEAL   game hops, Sum eps
     v
  secure

Trust boundary / what is axiomatic:
  - Aeneas translation soundness (trusted toolchain; has metatheory) = sec.-6 T.
  - Rust subset coverage: traits/generics ok-ish; unsafe / FFI / I/O NOT
      -> carve a verifiable CORE (KDF, AEAD, ratchet update); rest = trusted bdy.
  - probabilistic-relational layer must EXIST in Lean:
      build ~[eps] on Mathlib PMF; Fundamental Lemma + reductions on top.
      (Lean has less off-the-shelf than EasyCrypt/SSProve -- you build it.)
  - hardness assumptions -> the reduction eps_i terms.

Alternative one-PA path (Coq): hax (Rust -> SSProve); SSProve already IS
code-based games in Coq -> the whole stack in one Coq dev. Trade-off: SSProve's
functional-correctness reasoning over stateful Rust is less ergonomic than
Aeneas; hax prefers hacspec-style code.

================================================================================

## 8. Open: cost adequacy is the hinge

Highest-value formalization target. Most "verified crypto down to real code"
efforts are vague exactly at sec.-6 obligation (2): pin down the cost model on
each side and the polynomial relation between them. Without it the `forall PPT A.
adv <= eps` quantifiers never actually reach the real program, and (3) -- the
side-channel gap -- silently widens from "explicit assumption" to "unsound".

================================================================================

## Appendix: adequacy at three boundaries (the unification)

  boundary              relation        what adequacy says            cost
  --------------------  --------------  ----------------------------  -----------
  program equivalence   ~[0]            exact rewrite keeps security  0
  game hop              ~[eps_i]        hop perturbs advantage <= eps eps_i
  language / code (T)   ~[eps_T]        translation reflects attacks  eps_T (0 if
                                                                      exact)

Same relation (~[eps]), same notion (adequacy), three boundaries. Security is
the path; the theorem is Sum eps; soundness is poly-many hops with Sum eps negl.
