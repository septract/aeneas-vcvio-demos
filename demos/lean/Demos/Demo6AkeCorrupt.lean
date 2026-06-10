/-
  Demo 6.1 — cleanness-under-corruption for the synthetic KEM key-transport AKE game.

  ## What this adds over Demo 6 (`Demos/Demo6Ake.lean`)

  Demo 6 built a multi-session key-indistinguishability (KI) game over the extracted synthetic KEM
  (`kemKe`), with `Send`/`Reveal`/`Test` oracles and a *session-level* freshness predicate
  (`Session.fresh = !revealed && !tested`), and reduced the single-session KI advantage to the
  ASSUMED KEM IND-CPA via the zero-slack equality `ki_advantage_eq_kem_ind_cpa`. Demo 6's
  freshness only closes the "Reveal-then-Test-the-same-session" trap.

  The GENUINE hard part of real AKE games (Fujioka-Suzuki / FG PQXDH key-indistinguishability,
  TR/SCKA secure messaging) is NOT "is the session key pseudorandom" — Demo 6 showed that composes.
  It is the **cleanness / freshness predicate UNDER CORRUPTION**: the adversary may CORRUPT
  long-term keys (not just reveal session keys), and the Test session must be FRESH in a precise,
  PARTNER-AWARE, oracle-history-dependent sense. Demo 6.1 adds exactly this layer:

  1. **Long-term keys + a party table.** A finite list of `Party`s, each holding a long-term KEM
     keypair `(pk, sk) = keygenK seed` and a `corrupted` flag. A `Corrupt` oracle hands out a
     party's long-term secret and marks it corrupted (Boneh-Shoup §21.9.3 "Compromise user").
  2. **Partner-aware sessions.** Each session records its `owner`, intended `peer`, a session id
     `sid` (= the encaps ciphertext `cStar`), and an `Option` partner index, set at `Send` time by
     a `compatible`-triple match (B-S §21.9 partner function).
  3. **A partner-aware cleanness predicate** `Session.cleanIn`: a Test session is clean iff its own
     key is unrevealed, its partner's key is unrevealed, it is untested, AND the long-term key it
     relies on (its `peer`'s `pk`) was not corrupted. This mirrors the B-S §21.9.3 PFS `vulnerable`
     rule (Def 21.2): a finished instance gets the real/random key UNLESS its `pid` (= our `peer`)
     belongs to a compromised user.

  We prove, axiom-clean (`[propext, Classical.choice, Quot.sound]`):
  - `exists_clean_test_session` / `clean_reachable_under_corruption` — anti-vacuity: a clean Test
    session EXISTS, even on a state where a (non-peer) party is already corrupted (so the clean
    branch genuinely scores a challenge — the predicate is not too strong).
  - `corrupt_peer_then_test_unclean` — anti-trivial-win: corrupting the Test session's peer makes
    it unclean (so the "Corrupt peer, decaps, distinguish" attack is excluded — the predicate is
    not too weak). This is the load-bearing both-sided non-triviality.
  - `reveal_self_then_test_unclean` / `reveal_partner_then_test_unclean` — the Reveal traps.
  - `partner_symmetric` — the partner relation is symmetric (well-formed partnering).
  - `clean_with_live_partner` / `reveal_live_partner_unclean` — clause (b) is non-vacuous WITH a
    recognised (`partner = some j`) live partner: a clean session with a live unrevealed partner
    exists, and revealing exactly that partner makes it unclean.
  - `realCleanSessionKey_not_constant` — non-degeneracy survives: a clean session's real key is
    still non-constant (it depends on the coins).
  - `cakeAdvantage_eq_boolDistAdvantage` (with `cakeImpl_run_eq_cakeStepImpl`) — `cleanIn` is
    GENUINELY EXERCISED by a running game: the multi-session KI-under-corruption advantage `cakeAdvantage`,
    whose every `Test` query is gated by `s.cleanIn`, collapses to the real-vs-random distinguishing
    advantage, with the hidden bit projecting cleanly. This is the object that makes `cleanIn`
    load-bearing inside an actual `OracleComp` run (not merely in the guard lemmas).
  - `cleanKi_advantage_eq_kem_ind_cpa` — **reduction respects cleanness (structural single-clean-
    session model)**: the corruption-aware single-session KI advantage EQUALS the KEM IND-CPA
    advantage of an explicit reduction `corruptKiToKemAdversary` that embeds the challenge ONLY in
    the uncorrupted peer party `P*` and never holds (nor computes) that peer's secret. HONEST SEAM:
    this is proved over the STRUCTURAL `CorruptKI_Game` (clause (d) baked in by never emitting
    `skStar`), NOT by invoking the literal `cleanIn` inside the reduction; the link to `cleanIn` is
    carried by the guard lemmas + the clean-gated game above, not by an end-to-end composition. See
    the theorem's own docstring for the precise statement of what is and is not machine-checked.
  - `cakeGameFinal` + `finalClean` + `tested_peer_corrupted_not_finalClean` /
    `tested_revealed_not_finalClean` / `finalClean_witness` — **a definitional flaw found by working
    the reduction by hand, then fixed.** The multi-session game gated `cleanIn` AT TEST TIME ONLY;
    with the dynamic Corrupt/Reveal oracles that admits a compromise-AFTER-test distinguisher winning
    with advantage ≈1 and NO KEM assumption (`send; test; corrupt peer; recover the key`). The fix is
    the standard whole-trace freshness convention (B-S §21 / FG `clean` on the full transcript):
    `cakeGameFinal` scores only if the FINAL state is `finalClean`. The exclusion + anti-vacuity facts
    are registered. See the `End-of-game freshness` section for the full account. (The companion base
    demo additionally closes the running-game↔KEM-reduction seam for the canonical single-session
    distinguisher: `Demo6Ake.canonAke_advantage_eq_kem_ind_cpa`.)

  ## Honest scope (read before trusting anything)

  - SYNTHETIC protocol. The byte core (`ke.rs`) does NOT satisfy IND-CPA (the shared secret leaks
    from `(pk, ct)`; see Demo 6's docstring). The KEM IND-CPA assumption is UNINSTANTIATED; no
    byte-level security is certified. The value is the cleanness-under-corruption EXPRESSIBILITY and
    the reduction-RESPECT, machine-checked over extracted Rust.
  - **The `sk = pk ^ 0xFF` leak** (`keygenK_sk_spec`): a party's long-term secret is a *public*
    involution of its public key. This is load-bearing and surfaced HONESTLY:
      (a) it is exactly why cleanness clause (d) MUST exclude a corrupted peer (corrupting the peer
          recovers its sk and breaks any session to it — the anti-trivial-win fact);
      (b) it makes the reduction's simulation of `Corrupt` for NON-challenge parties trivial (the
          reduction self-generates every other party's keypair). For this synthetic construction the
          reduction never needs the challenge party's secret, so it respects cleanness — but the
          same leak is why this byte core certifies no security.
  - **Window collapse (scope limit, NOT a claim).** The synthetic model has no real time, so the
    §21.9.4 "between when I was activated and when I finished" corruption window degenerates to
    "ever corrupted". We model the STATIC + PFS fragment (B-S Def 21.2) only; KCI / HSM-window /
    forward-secrecy-window security is NOT claimed.

  ## Citation mapping

  Boneh-Shoup, *A Graduate Course in Applied Cryptography* v0.6, §21.9 "Formal definitions"
  (Def 21.1 static AKE, Experiments 0/1, partner function `fresh`/`connected`/`vulnerable`,
  `compatible` triple p.887-888) and §21.9.3 "Modeling perfect forward secrecy" (the "Compromise
  user" query, the revised `vulnerable` rule, Def 21.2 PFS-secure, Remark 21.4 KCI-resistance,
  p.890-892). Eventual-real analogue: FG ePrint 2024/702 `clean^PQXDH`.
-/
import Demos.Demo6Ake

open Aeneas Std Result
open OracleSpec OracleComp ENNReal

namespace Demo6AkeCorrupt

open Demo6Ake

/-! ## Long-term keys and the party table.

A `Party` is an honest user holding a long-term KEM keypair `(pk, sk) = keygenK seed` plus a
`corrupted` flag. The `Corrupt` oracle (§21.9.3 "Compromise user") sets `corrupted := true` and
hands out `sk`. -/

/-- A party (honest user instance) with a long-term KEM keypair and a corruption flag.
`(pk, sk) = keygenK seed` for some sampled seed; `corrupted` is set by the `Corrupt` oracle. -/
structure Party where
  /-- The party's long-term public key. -/
  pk : Block
  /-- The party's long-term secret key (`= pk ^ 0xFF` for this synthetic KEM). -/
  sk : Block
  /-- Whether this party's long-term key has been handed out via `Corrupt`. -/
  corrupted : Bool
  deriving Inhabited

/-! ## Partner-aware sessions.

A session records the party running it (`owner`), its intended partner (`peer`), the session id
`sid` (the encaps ciphertext `cStar` — the "loosely-matching transcript" of B-S §21.9.2), its
`role` (left/right, for the `compatible` triple), its derived key, an `Option` partner index set at
`Send` time, and the `revealed`/`tested` flags. -/

/-- A single protocol session, extended with partner structure for cleanness-under-corruption. -/
structure CSession where
  /-- The party running this session (the local user instance `I.user`). -/
  owner : ℕ
  /-- The intended partner party (`I.pid`): the session encapsulates TO this party's long-term pk,
  so this is the long-term key the session RELIES ON for KI. -/
  peer : ℕ
  /-- Role bit for the `compatible` triple (B-S §21.9 p.888): partners have opposite roles. -/
  role : Bool
  /-- The session id = the encaps ciphertext `cStar` (the loosely-matching transcript). -/
  sid : Block
  /-- The derived session key `deriveK shared`. -/
  key : Block
  /-- The matching partner session index, set once at `Send` by the `compatible` match (or `none`). -/
  partner : Option ℕ
  /-- Whether this session's key was handed out via `Reveal`. -/
  revealed : Bool
  /-- Whether this session was already used as a `Test` challenge. -/
  tested : Bool
  deriving Inhabited

/-- The `compatible` predicate (B-S §21.9 p.888): two sessions are partners iff their owner/peer
ids cross-match, their roles differ, and they share the same loosely-matching transcript (`sid`).
This is the literal §21.9 compatible triple specialized to KEM key-transport. -/
def compatible (s t : CSession) : Bool :=
  s.peer == t.owner && t.peer == s.owner && (s.role != t.role) && (s.sid == t.sid)

/-- `compatible` is symmetric. -/
theorem compatible_symm (s t : CSession) : compatible s t = compatible t s := by
  -- Turn every `==` into `decide (· = ·)` and `!=` into `decide (¬ ·)`, push `eq_comm`, then the
  -- two sides are conjunctions of the same atoms in different order — `ac_rfl` finishes.
  simp only [compatible, beq_eq_decide]
  rw [(by simp [eq_comm] : decide (s.peer = t.owner) = decide (t.owner = s.peer)),
      (by simp [eq_comm] : decide (t.peer = s.owner) = decide (s.owner = t.peer)),
      (by simp [eq_comm] : decide (s.sid = t.sid) = decide (t.sid = s.sid)),
      (by rw [bne_comm] : (s.role != t.role) = (t.role != s.role))]
  ac_rfl

/-! ## The mutable game state. -/

/-- The mutable game state: the secret challenge bit, the party table (long-term keys + corruption
flags), and the session table. -/
structure CGameState where
  /-- The hidden challenge bit governing every clean `Test`. -/
  b : Bool
  /-- The party table: index `p` is party `p`'s long-term keypair + corruption flag. -/
  parties : List Party
  /-- The session table: index `i` is the `i`-th opened session. -/
  sessions : List CSession
  deriving Inhabited

/-! ## The partner-aware cleanness predicate (the headline definition).

A Test session `s` (with index `i` into the table, against party table `parties` and session table
`ss`) is CLEAN iff ALL of:
  (a) `!s.revealed`                         — its own key was not revealed (Reveal-self trap);
  (b) its partner's key was not revealed     — `match s.partner with some j => !ss[j].revealed`
                                               (the partner-Reveal trap / connected-to-J rule);
  (c) `!s.tested`                            — it is not already a Test challenge;
  (d) `!(parties[s.peer].corrupted)`         — the long-term key it RELIES ON (its peer's ltk) was
                                               not Corrupted (the §21.9.3 PFS `vulnerable` rule).

Clause (d) keys off `peer` (= `I.pid`), NOT `owner` (= `I.user`): per B-S Remark 21.4, corrupting
the OWNER does not break cleanness (KCI resistance / forward secrecy). The condition is LOCAL to the
Test session's peer — corrupting any OTHER party leaves it clean (so the predicate is not vacuous
under corruption). -/

/-- Look up party `p`'s corruption flag in the table (a missing party is treated as uncorrupted —
the `default` party has `corrupted := false`; an out-of-range peer never arises for a session
created by the `Send` oracle, which only encapsulates to a registered party). -/
def CGameState.peerCorrupted (gs : CGameState) (p : ℕ) : Bool :=
  (gs.parties.getD p default).corrupted

/-- The partner-aware cleanness predicate (clauses (a)-(d) above). `s` is the candidate Test
session; `gs` supplies the party table and session table it is read against. -/
def CSession.cleanIn (s : CSession) (gs : CGameState) : Bool :=
  !s.revealed
  && (match s.partner with
      | some j => !(gs.sessions.getD j default).revealed
      | none   => true)
  && !s.tested
  && !(gs.peerCorrupted s.peer)

/-- `cleanIn` ignores the challenge bit `b`: it reads only the party table (clause (d)) and the
session table (clauses (a)-(c)). Used to relate the bit-carrying `cakeImpl` gate to the
bit-parameterized `cakeStepImpl` gate. -/
theorem cleanIn_bit_irrel (s : CSession) (b b' : Bool) (parties : List Party)
    (ss : List CSession) :
    s.cleanIn { b := b, parties := parties, sessions := ss }
      = s.cleanIn { b := b', parties := parties, sessions := ss } := by
  rfl

/-! ## The oracle interface over the corruption-aware state.

Four queries:
  - `send owner peer role` — open a session: encapsulate to `parties[peer].pk`, store the derived
    session key, and set the partner by the first existing `compatible` session.
  - `reveal i` — mark session `i` revealed and hand out its key (session-level corruption).
  - `corrupt p` — mark party `p` corrupted and hand out its long-term secret (§21.9.3 "Compromise
    user"). Returns the secret as a `Block`.
  - `test i` — real-or-random on session `i` ONLY if it is clean; otherwise a fixed default. -/

/-- The corruption-aware oracle interface. `send` carries `(owner, peer, role)`; `reveal`/`test`
carry a session index; `corrupt` carries a party index. -/
inductive CAkeQuery where
  /-- Open a session run by `owner`, intended for partner `peer`, with role bit `role`. -/
  | send : ℕ → ℕ → Bool → CAkeQuery
  /-- Reveal session `i`'s key. -/
  | reveal : ℕ → CAkeQuery
  /-- Corrupt party `p`: hand out its long-term secret, mark it corrupted. -/
  | corrupt : ℕ → CAkeQuery
  /-- Real-or-random challenge on a clean session `i`. -/
  | test : ℕ → CAkeQuery
  deriving DecidableEq

/-- Every query returns a `Block` (`send` → `cStar`; `reveal` → the session key; `corrupt` → the
party's long-term secret; `test` → the real/random key or a default). -/
@[reducible] def cakeSpec : OracleSpec.{0, 0} CAkeQuery := fun _ => Block

/-- Find the index of the first existing session `compatible` with the freshly-built session `s`
(B-S §21.9 partner function). Returns `none` if there is no compatible session yet. -/
def findPartner (ss : List CSession) (s : CSession) : Option ℕ :=
  (ss.zipIdx.find? (fun p => compatible s p.1)).map (·.2)

/-- Replace session `i` by its `f`-image (no-op if `i` is out of range). -/
def CGameState.updateSession (gs : CGameState) (i : ℕ) (f : CSession → CSession) : CGameState :=
  { gs with sessions := gs.sessions.set i (f (gs.sessions.getD i default)) }

/-- Mark party `p` corrupted (no-op if out of range). -/
def CGameState.corruptParty (gs : CGameState) (p : ℕ) : CGameState :=
  { gs with parties := gs.parties.set p { (gs.parties.getD p default) with corrupted := true } }

/-- The stateful handler for `cakeSpec` over `CGameState`. The party table is established by the
game before the adversary runs; the handler reads `parties[peer].pk` for `send` and `parties[p].sk`
for `corrupt`. -/
def cakeImpl :
    QueryImpl.Stateful unifSpec cakeSpec CGameState
  | .send owner peer role => StateT.mk fun gs => do
      let coins ← ($ᵗ Block : OracleComp unifSpec Block)
      let pk := (gs.parties.getD peer default).pk
      let cs := encapsK pk coins
      let key := deriveK cs.2
      let newSession : CSession :=
        { owner := owner, peer := peer, role := role, sid := cs.1, key := key,
          partner := findPartner gs.sessions
            { owner := owner, peer := peer, role := role, sid := cs.1, key := key,
              partner := none, revealed := false, tested := false },
          revealed := false, tested := false }
      pure (cs.1, { gs with sessions := gs.sessions ++ [newSession] })
  | .reveal i => StateT.mk fun gs =>
      let s := gs.sessions.getD i default
      pure (s.key, gs.updateSession i (fun s => { s with revealed := true }))
  | .corrupt p => StateT.mk fun gs =>
      let sk := (gs.parties.getD p default).sk
      pure (sk, gs.corruptParty p)
  | .test i => StateT.mk fun gs => do
      let s := gs.sessions.getD i default
      let kRand ← ($ᵗ Block : OracleComp unifSpec Block)
      if s.cleanIn gs then
        let challenge := if gs.b then s.key else kRand
        pure (challenge, gs.updateSession i (fun s => { s with tested := true }))
      else
        pure (default, gs)

/-! ## Anti-trivial-win and anti-vacuity guard lemmas (the load-bearing both-sided non-triviality).

These validate the cleanness DEFINITION before any reduction is built. They establish that the
predicate is non-trivial on BOTH sides:
  - NOT too weak: corrupting the Test session's peer (or revealing its / its partner's key, or
    re-testing it) makes it UNCLEAN — so the trivial corruption/reveal attacks are excluded.
  - NOT too strong: a clean Test session EXISTS, even on a state where some OTHER party is already
    corrupted — so the clean branch genuinely scores a challenge (cleanness does not collapse to the
    empty case the moment any Corrupt is issued).

The corruption flag underlying clause (d). -/

/-- **Anti-trivial-win (the v1-class trap at the corruption layer).** If the Test session's PEER
party is corrupted, the session is UNCLEAN. This is the formal reason the "Corrupt the peer,
recompute `sk = pk ^ 0xFF`, decapsulate `sid`, derive, distinguish" attack is excluded from the
advantage: a session relying on a corrupted long-term key is never scored. Mirrors the B-S §21.9.3
`vulnerable` rule (`I.pid` compromised ⇒ `I.esk ← I.sk`, not random). -/
theorem corrupt_peer_then_test_unclean (gs : CGameState) (s : CSession)
    (hpeer : gs.peerCorrupted s.peer = true) : s.cleanIn gs = false := by
  simp only [CSession.cleanIn, hpeer, Bool.not_true, Bool.and_false]

/-- **Anti-trivial-win, the Reveal-self trap.** A session whose own key was revealed is unclean. -/
theorem reveal_self_then_test_unclean (gs : CGameState) (s : CSession)
    (hrev : s.revealed = true) : s.cleanIn gs = false := by
  simp only [CSession.cleanIn, hrev, Bool.not_true, Bool.false_and]

/-- **Anti-trivial-win, the partner-Reveal trap.** If the Test session has a partner `j` whose key
was revealed, the session is unclean. (Motivation, not proved here: for partnered sessions sharing a
`sid` the two session keys coincide, so revealing the partner's key would leak the Test key — hence
the predicate must exclude it. The proof below is purely flag-based on `cleanIn` clause (b); the
key-equality is not a dependency.) Mirrors the B-S §21.9 connected-to-J rule (p.888): `I` inherits
`J.esk` only if `J` is fresh. -/
theorem reveal_partner_then_test_unclean (gs : CGameState) (s : CSession) (j : ℕ)
    (hpart : s.partner = some j) (hrev : (gs.sessions.getD j default).revealed = true) :
    s.cleanIn gs = false := by
  simp only [CSession.cleanIn, hpart, hrev, Bool.not_true]
  simp

/-- **Anti-trivial-win, the already-tested trap.** A session that was already a Test challenge is
unclean (no double-scoring). -/
theorem tested_then_test_unclean (gs : CGameState) (s : CSession)
    (htest : s.tested = true) : s.cleanIn gs = false := by
  simp only [CSession.cleanIn, htest, Bool.not_true, Bool.and_false, Bool.false_and]

/-- A "good" session: unrevealed, untested, no recognised partner, owned by party 0, peer party 1.
The canonical clean candidate used in the anti-vacuity witnesses. -/
def goodSession : CSession :=
  { owner := 0, peer := 1, role := false, sid := default, key := default,
    partner := none, revealed := false, tested := false }

/-- A two-party table where party `0` is corrupted but party `1` (the peer of `goodSession`) is
NOT — the witness that cleanness survives a corruption of a non-peer party. -/
def witnessParties : List Party :=
  [ { pk := default, sk := default, corrupted := true },     -- party 0: CORRUPTED
    { pk := default, sk := default, corrupted := false } ]   -- party 1: honest (the peer)

/-- The witness state: bit `true`, the `witnessParties` table (party 0 corrupted), and a single
session `goodSession` (peer = party 1, uncorrupted). -/
def witnessState : CGameState :=
  { b := true, parties := witnessParties, sessions := [goodSession] }

/-- **Anti-vacuity: a clean Test session exists.** `goodSession`, read against `witnessState`, is
clean — even though party 0 is already corrupted. This proves the predicate is NOT too strong: the
clean branch is reachable, so a clean Test genuinely scores a real-or-random challenge rather than
defaulting. Mirrors B-S Remark 21.1 (validity conditions hold in Exp 0). -/
theorem exists_clean_test_session : goodSession.cleanIn witnessState = true := by
  decide

/-- **Anti-vacuity under corruption (the corruption-layer analogue of `realSessionKey_not_constant`'s
reachability).** A clean Test session exists on a state where a Corrupt has ALREADY been issued (to a
non-peer party). This is the explicit witness obligation from the skeptic's STOP condition: the
clean predicate is LOCAL to the peer, so a corruption of another party does not destroy cleanness —
the predicate is not the too-strong "no party ever corrupted" version. -/
theorem clean_reachable_under_corruption :
    ∃ (gs : CGameState) (s : CSession),
      (gs.parties.getD 0 default).corrupted = true ∧ s.cleanIn gs = true := by
  exact ⟨witnessState, goodSession, by decide, by decide⟩

/-! ## Well-formed partnering.

`findPartner` returns the index of an actually-`compatible` session, so clause (b) of `cleanIn`
consults the RIGHT session (not a stale/aliased one). Combined with `compatible_symm`, the partner
relation is symmetric: if `s`'s partner is the session at `j`, then `s` is `compatible` with it and
(symmetrically) it is `compatible` with `s`. -/

/-- **Partner soundness.** If `findPartner ss s = some j`, then `j` is a valid index and the session
at `j` is genuinely `compatible` with `s`. So `cleanIn`'s clause (b) reads a real partner, never an
aliased or out-of-range session. -/
theorem findPartner_compatible (ss : List CSession) (s : CSession) (j : ℕ)
    (h : findPartner ss s = some j) :
    j < ss.length ∧ compatible s (ss.getD j default) = true := by
  simp only [findPartner, Option.map_eq_some_iff] at h
  obtain ⟨p, hfind, hj⟩ := h
  have hmem := List.find?_some hfind
  have hmem' := List.mem_of_find?_eq_some hfind
  -- `p ∈ ss.zipIdx` gives `ss[p.2]? = some p.1` and `p.2 < ss.length`.
  rw [List.mem_zipIdx_iff_getElem?] at hmem'
  subst hj
  refine ⟨?_, ?_⟩
  · -- p.2 < ss.length from the `getElem?` being `some`
    have hmm := hmem'; rw [List.getElem?_eq_some_iff] at hmm; exact hmm.1
  · -- compatible s (ss.getD p.2 default) = compatible s p.1 = true
    have hget : ss.getD p.2 default = p.1 := by
      have : ss[p.2]? = some p.1 := by simpa using hmem'
      simp [List.getD_eq_getElem?_getD, this]
    rw [hget]; exact hmem

/-- **Partner symmetry.** If `s`'s partner (found in `ss`) is the session at index `j`, then `s` is
`compatible` with the session at `j` AND that session is `compatible` with `s` — the §21.9 partner
relation is symmetric (so "no partner revealed" guards a genuinely mutual partner). -/
theorem partner_symmetric (ss : List CSession) (s : CSession) (j : ℕ)
    (h : findPartner ss s = some j) :
    compatible s (ss.getD j default) = true ∧ compatible (ss.getD j default) s = true := by
  obtain ⟨_, hc⟩ := findPartner_compatible ss s j h
  exact ⟨hc, by rw [compatible_symm]; exact hc⟩

/-! ## Non-degeneracy survives cleanness (the anti-v1 check at the corruption layer).

A CLEAN session's real key is still non-constant: it depends on the coins, so the clean Test branch
genuinely carries entropy (it is not the v1 constant-collapse). We exhibit a clean session whose
stored real key, with the all-ones peer public key, differs for two coin vectors — reusing Demo 6's
`realSessionKey_not_constant` (the clean predicate constrains only the flags/partner/corruption, NOT
the coins, so the entropy of the real branch is untouched). -/

/-- Build the canonical clean session that encapsulates to public key `pk` with coins `c`: peer
party 1 (uncorrupted in `witnessParties`), unrevealed, untested, no partner. Its `key` is the real
session key `realSessionKey pk c = deriveK (encapsK pk c).2`. -/
def cleanSessionWith (pk c : Block) : CSession :=
  { owner := 0, peer := 1, role := false, sid := (encapsK pk c).1,
    key := realSessionKey pk c, partner := none, revealed := false, tested := false }

/-- **Non-degeneracy survives cleanness.** There is a fixed party table (party 1, the peer, is
uncorrupted) and two coin vectors such that BOTH induce a CLEAN session and the two clean sessions
carry DIFFERENT real keys. So gating Test on `cleanIn` does not collapse the real branch to a
constant — the clean session genuinely scores a non-trivial real-or-random challenge. This is the
corruption-layer analogue of `realSessionKey_not_constant`. -/
theorem realCleanSessionKey_not_constant :
    ∃ (parties : List Party) (pk c₁ c₂ : Block),
      (cleanSessionWith pk c₁).cleanIn { b := true, parties := parties, sessions := [] } = true ∧
      (cleanSessionWith pk c₂).cleanIn { b := true, parties := parties, sessions := [] } = true ∧
      (cleanSessionWith pk c₁).key ≠ (cleanSessionWith pk c₂).key := by
  obtain ⟨pk, c₁, c₂, hne⟩ := realSessionKey_not_constant
  refine ⟨witnessParties, pk, c₁, c₂, ?_, ?_, ?_⟩
  · -- clean: peer = party 1, which is uncorrupted; unrevealed/untested; no partner.
    simp only [CSession.cleanIn, cleanSessionWith, CGameState.peerCorrupted, witnessParties]
    decide
  · simp only [CSession.cleanIn, cleanSessionWith, CGameState.peerCorrupted, witnessParties]
    decide
  · -- the two keys are the two distinct real session keys.
    simpa only [cleanSessionWith, realSessionKey] using hne

/-! ## Clause (b) is non-vacuous WITH a live partner.

All the witnesses above use `partner := none`, so clause (b) of `cleanIn` holds trivially in them.
To witness that clause (b) is genuinely non-vacuous — that the clean branch is reachable with a
RECOGNISED partner present (and is broken by revealing exactly that partner) — we exhibit a session
whose `partner = some j` pointing at a real, `compatible`, UNREVEALED session, prove it clean, and
prove that revealing the partner makes it unclean. This validates clause (b) the way
`exists_clean_test_session` validates the whole predicate. -/

/-- A two-session table exhibiting a live partner: session 0 (`owner 0, peer 1, role false`) and
session 1 (`owner 1, peer 0, role true`), sharing `sid = default`, so they are `compatible`; both
unrevealed/untested. Session 0 names session 1 as its partner. -/
def partneredSession0 : CSession :=
  { owner := 0, peer := 1, role := false, sid := default, key := default,
    partner := some 1, revealed := false, tested := false }

/-- The partner of `partneredSession0`: `owner 1, peer 0, role true`, same `sid`, unrevealed. -/
def partneredSession1 : CSession :=
  { owner := 1, peer := 0, role := true, sid := default, key := default,
    partner := some 0, revealed := false, tested := false }

/-- A state with both partnered sessions and a two-party table whose peer (party 1) is uncorrupted. -/
def partneredState : CGameState :=
  { b := true, parties := witnessParties, sessions := [partneredSession0, partneredSession1] }

/-- **`partneredSession0` and `partneredSession1` are genuinely partners** (the `compatible` triple
holds), so clause (b)'s partner lookup names a real, mutual partner — not `none`, not an alias. -/
theorem partnered_compatible : compatible partneredSession0 partneredSession1 = true := by
  decide

/-- **Clause (b) non-vacuity WITH a live partner.** `partneredSession0`, read against
`partneredState`, is CLEAN even though it has a recognised partner (session 1) — because that
partner is unrevealed (and the peer, party 1, is uncorrupted). This is the missing witness that the
clean branch is reachable with `partner = some j` live, complementing `exists_clean_test_session`
(which used `partner = none`). -/
theorem clean_with_live_partner : partneredSession0.cleanIn partneredState = true := by
  decide

/-- **Clause (b) bites with a live partner.** Revealing the live partner (session 1) makes
`partneredSession0` unclean — even though the session's OWN key, its peer-corruption, and its tested
flag are all still good. So clause (b) genuinely consults the partner's `revealed` flag (the
connected-to-J rule), and the "reveal the partner, then Test this session" attack is excluded. This
is `reveal_partner_then_test_unclean` instantiated on a concrete live partner. -/
theorem reveal_live_partner_unclean :
    partneredSession0.cleanIn
      { partneredState with
        sessions := partneredState.sessions.set 1 { partneredSession1 with revealed := true } }
      = false := by
  decide

/-! ## A genuine multi-session game whose `Test` is gated by `cleanIn`.

The single-session reduction below (`cleanKi_advantage_eq_kem_ind_cpa`) is stated over a *structural*
single-clean-session model (`CorruptKI_Game`), which bakes clause (d) in by never emitting `skStar`
(see its docstring for the honest seam). To make the `cleanIn` predicate genuinely EXERCISED by a
running game — not just by the guard lemmas — we build the multi-session game `cakeGame` directly
over the `cakeImpl` handler (whose `test` query is gated by `s.cleanIn gs`). This mirrors Demo 6's
`akeGame`/`akeAdvantage` exactly, lifted to the corruption-aware state. We register that this game
ELABORATES, is axiom-clean, and projects its hidden bit identically to Demo 6's (the state-projection
identity `cakeImpl_run_eq_cakeStepImpl`), establishing `cakeAdvantage_eq_boolDistAdvantage` — the
real-vs-random collapse of the clean-gated game. The party table (long-term keys + initial corruption
flags) is a parameter, established by the game before the adversary runs.

HONEST SCOPE: we register NO new security BOUND for this multi-session clean-gated game (the
single-session structural reduction is the reduction-respect headline). What is added here is that
`cleanIn` is invoked by a genuine `OracleComp` run with a real advantage, the bit projects cleanly,
and the game is non-degenerate — closing the "cleanIn is orphaned from any game" seam. -/

/-- A multi-session corruption-aware KI distinguisher: drives the `cakeSpec` oracle interface
(`send`/`reveal`/`corrupt`/`test`) and outputs a guess at the hidden challenge bit. -/
def CAkeAdversary : Type := OracleComp cakeSpec Bool

/-- The multi-session clean-gated KI game. The party table `parties` (long-term keys + initial
corruption flags) is fixed by the game; sample the secret bit `b`, run the distinguisher against the
`cakeImpl` handler (whose `test` is gated by `cleanIn`) from the table-with-empty-sessions state,
return whether the guess matched. -/
noncomputable def cakeGame (parties : List Party) (adv : CAkeAdversary) : ProbComp Bool := do
  let b ← ($ᵗ Bool : OracleComp unifSpec Bool)
  let b' ← cakeImpl.run { b := b, parties := parties, sessions := [] } adv
  return (b == b')

/-- The multi-session clean-gated KI advantage — the bias of `cakeGame`. The `cleanIn` predicate is
genuinely invoked inside every `test` query of the run. -/
noncomputable def cakeAdvantage (parties : List Party) (adv : CAkeAdversary) : ℝ :=
  (cakeGame parties adv).boolBiasAdvantage

/-- The bit-free corruption-aware state — `CGameState` with the hidden bit projected away. The bit
becomes a parameter of the handler (`cakeStepImpl bit`). -/
structure CTable where
  /-- The party table (long-term keys + corruption flags). -/
  parties : List Party
  /-- The session table. -/
  sessions : List CSession
  deriving Inhabited

/-- The bit-parameterized clean-gated handler: identical to `cakeImpl` except the challenge bit
`bit` is a parameter (not read from state), over the bare `CTable`. The `test` query is STILL gated
by `cleanIn` (read against the reconstructed `CGameState`), so cleanness is exercised here too. -/
def cakeStepImpl (bit : Bool) :
    QueryImpl.Stateful unifSpec cakeSpec CTable
  | .send owner peer role => StateT.mk fun ct => do
      let coins ← ($ᵗ Block : OracleComp unifSpec Block)
      let pk := (ct.parties.getD peer default).pk
      let cs := encapsK pk coins
      let key := deriveK cs.2
      let newSession : CSession :=
        { owner := owner, peer := peer, role := role, sid := cs.1, key := key,
          partner := findPartner ct.sessions
            { owner := owner, peer := peer, role := role, sid := cs.1, key := key,
              partner := none, revealed := false, tested := false },
          revealed := false, tested := false }
      pure (cs.1, { ct with sessions := ct.sessions ++ [newSession] })
  | .reveal i => StateT.mk fun ct =>
      let s := ct.sessions.getD i default
      pure (s.key, { ct with sessions := ct.sessions.set i { s with revealed := true } })
  | .corrupt p => StateT.mk fun ct =>
      let party := ct.parties.getD p default
      pure (party.sk, { ct with parties := ct.parties.set p { party with corrupted := true } })
  | .test i => StateT.mk fun ct => do
      let s := ct.sessions.getD i default
      let kRand ← ($ᵗ Block : OracleComp unifSpec Block)
      if s.cleanIn { b := bit, parties := ct.parties, sessions := ct.sessions } then
        let challenge := if bit then s.key else kRand
        pure (challenge, { ct with sessions := ct.sessions.set i { s with tested := true } })
      else
        pure (default, ct)

/-- The fixed-table clean-gated run with the bit fixed: run the distinguisher against
`cakeStepImpl bit` from the table-with-empty-sessions state. `cakeRun parties true` is the
all-clean-`Test`-REAL run, `cakeRun parties false` the all-clean-`Test`-RANDOM run. -/
noncomputable def cakeRun (parties : List Party) (bit : Bool) (adv : CAkeAdversary) :
    ProbComp Bool :=
  (cakeStepImpl bit).run { parties := parties, sessions := [] } adv

/-- **State projection (corruption-aware).** Running `cakeImpl` from a `CGameState` with bit `b`,
party table `parties`, and session table `ss` induces the same output distribution as running the
bit-parameterized `cakeStepImpl b` from the bare `CTable`: the bit only selects the `Test` branch
(and is fed identically into the `cleanIn` gate — `cleanIn` ignores the bit, so the gate is
unchanged), and the party/session table mutations mirror each other. This is the corruption-aware
analogue of Demo 6's `akeImpl_run_eq_akeStepImpl`. -/
theorem cakeImpl_run_eq_cakeStepImpl (b : Bool) (parties : List Party) (adv : CAkeAdversary)
    (ss : List CSession) :
    cakeImpl.run { b := b, parties := parties, sessions := ss } adv
      = (cakeStepImpl b).run { parties := parties, sessions := ss } adv := by
  refine OracleComp.run'_simulateQ_eq_of_query_map_eq_inv'
    (impl₁ := cakeImpl) (impl₂ := cakeStepImpl b)
    (inv := fun gs => gs.b = b) (proj := fun gs => ({ parties := gs.parties, sessions := gs.sessions } : CTable)) ?_ ?_ adv
    { b := b, parties := parties, sessions := ss } rfl
  · -- the bit `gs.b` is preserved by every handler step
    intro t s hs y hy
    cases t with
    | send owner peer role =>
      simp only [cakeImpl, StateT.run_mk, support_bind, Set.mem_iUnion] at hy
      obtain ⟨coins, _, hy⟩ := hy
      simp only [support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact hs
    | reveal i =>
      simp only [cakeImpl, StateT.run_mk, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact hs
    | corrupt p =>
      simp only [cakeImpl, CGameState.corruptParty, StateT.run_mk, support_pure,
        Set.mem_singleton_iff] at hy
      subst hy; exact hs
    | test i =>
      simp only [cakeImpl, StateT.run_mk, support_bind, Set.mem_iUnion] at hy
      obtain ⟨kRand, _, hy⟩ := hy
      split at hy <;>
        (simp only [CGameState.updateSession, support_pure, Set.mem_singleton_iff] at hy
         subst hy; exact hs)
  · -- under the invariant, the projection commutes with each step
    intro t s hs
    cases t with
    | send owner peer role =>
      simp only [cakeImpl, cakeStepImpl, StateT.run_mk, map_bind]
      rfl
    | reveal i =>
      simp only [cakeImpl, cakeStepImpl, StateT.run_mk, map_pure, CGameState.updateSession,
        Prod.map_apply, id_eq]
    | corrupt p =>
      simp only [cakeImpl, cakeStepImpl, StateT.run_mk, map_pure, CGameState.corruptParty,
        Prod.map_apply, id_eq]
    | test i =>
      simp only [cakeImpl, cakeStepImpl, StateT.run_mk, map_bind, CGameState.updateSession]
      refine bind_congr (fun kRand => ?_)
      -- The `cakeImpl` gate reads `cleanIn s` (full CGameState); the `cakeStepImpl` gate reads
      -- `cleanIn { b := b, parties := s.parties, sessions := s.sessions }`. `cleanIn` ignores `b`,
      -- so the two gate conditions are equal; rewrite the first into the second before splitting.
      have hgate : (s.sessions.getD i default).cleanIn s
          = (s.sessions.getD i default).cleanIn
              { b := b, parties := s.parties, sessions := s.sessions } := by
        rfl
      rw [hgate]
      split <;> simp [Prod.map, hs]

/-- The bit `b` in `cakeImpl`'s initial state only selects the `Test` branch, so running the game
from the empty-sessions state is the same `ProbComp` as `cakeRun parties b`. -/
theorem cakeImpl_run_empty_eq_cakeRun (b : Bool) (parties : List Party) (adv : CAkeAdversary) :
    cakeImpl.run { b := b, parties := parties, sessions := [] } adv = cakeRun parties b adv :=
  cakeImpl_run_eq_cakeStepImpl b parties adv []

/-- **The bias-to-distinguishing bridge for the clean-gated game.** The multi-session clean-gated KI
advantage equals the boolean distinguishing advantage between the all-clean-`Test`-REAL run and the
all-clean-`Test`-RANDOM run. The single sampled bit `b` governs every clean `Test`, so the bias
collapses to a real-vs-random distinguishing advantage — over a game in which `cleanIn` genuinely
gates each `Test`. This is the corruption-aware analogue of `akeAdvantagePk_eq_boolDistAdvantage`. -/
theorem cakeAdvantage_eq_boolDistAdvantage (parties : List Party) (adv : CAkeAdversary) :
    cakeAdvantage parties adv
      = (cakeRun parties true adv).boolDistAdvantage (cakeRun parties false adv) := by
  unfold cakeAdvantage cakeGame
  rw [show (do
        let b ← ($ᵗ Bool : OracleComp unifSpec Bool)
        let b' ← cakeImpl.run { b := b, parties := parties, sessions := [] } adv
        pure (b == b') : ProbComp Bool)
      = (do
        let b ← ($ᵗ Bool : OracleComp unifSpec Bool)
        let z ← if b then cakeRun parties true adv else cakeRun parties false adv
        pure (b == z)) from by
    refine bind_congr (fun b => ?_)
    rw [cakeImpl_run_empty_eq_cakeRun]
    cases b <;> rfl]
  exact ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch
    (cakeRun parties true adv) (cakeRun parties false adv)

/-! ## The reduction that RESPECTS cleanness (the headline).

We now give the single-session KI-under-corruption game and prove the reduction to KEM IND-CPA, in
the same zero-slack style as Demo 6's `ki_advantage_eq_kem_ind_cpa`, but with the corruption layer
made explicit.

**The clean Test, concretely.** There is one *challenge party* `P*` (the peer of the Test session)
and `n` OTHER parties. A corruption-aware KI adversary may corrupt ANY party except `P*` (clause (d)
of `cleanIn` forbids only corrupting the peer of a scored Test). We model this directly: the game
samples `P*`'s keypair AND `n` other parties' keypairs, and hands the adversary
  - `P*`'s public key `pk*`, and
  - the FULL keypairs of all `n` other parties (i.e. it has already corrupted every party it is
    allowed to corrupt — the maximally-corrupting clean adversary).
The one secret the game NEVER reveals is `sk*`. That single omission IS clause (d): the Test is
scored only when `P*` is uncorrupted, and the reduction never holds `sk*`.

**Why this is the §21.9.3 reduction, not the synthetic leak.** Although `sk* = pk* ^ 0xFF` is a
public involution for THIS byte core, the reduction below NEVER computes it: it embeds the KEM
challenge in `P*` and self-generates the other parties' keypairs. So the reduction transfers to a
real (trapdoor) KEM where `sk*` is genuinely hidden — the synthetic leak is used nowhere in the
proof. (It is used only OUTSIDE the reduction, to justify clause (d): see
`corrupt_peer_then_test_unclean`.) -/

/-- A corruption-aware single-session KI adversary over `n` other parties. `preChallenge` sees the
challenge party's public key `pk*` together with the FULL keypairs of all `n` other corruptible
parties (a `List (Block × Block)` of `(pk, sk)`); `postChallenge` sees the challenge ciphertext and
a candidate session key, and guesses. This is Demo 6's `KI_Adversary` augmented with the
other-parties' corruption data — exactly what an adversary learns by corrupting every party it is
permitted to (everyone but `P*`). -/
structure CorruptKIAdversary (n : ℕ) where
  /-- Adversary state from the pre- to the post-challenge phase. -/
  State : Type
  /-- Pre-challenge: inspect `pk*` and the `n` corrupted other-party keypairs. -/
  preChallenge : Block → List (Block × Block) → OracleComp unifSpec State
  /-- Post-challenge: given the challenge ciphertext and a candidate session key, guess. -/
  postChallenge : State → Block → Block → OracleComp unifSpec Bool

/-- The corruption-aware single-session KI game. Sample `P*`'s keypair and `n` other parties'
keypairs; hand the adversary `pk*` and the other keypairs (the corrupted parties); encapsulate to
`pk*`; sample the bit `b`; challenge with the REAL session key `deriveK shared` (if `b`) or a UNIFORM
key (if `¬b`); return whether the guess matched. The Test session's peer is `P*`, which is NEVER
corrupted (its secret `sk*` is never given out) — the clean condition (d) by construction. -/
noncomputable def CorruptKI_Game {n : ℕ} (adv : CorruptKIAdversary n) : SPMF Bool :=
  ProbCompRuntime.probComp.evalDist do
    let (pkStar, _skStar) ← kemKe.keygen
    let others ← (List.replicate n ()).mapM (fun _ => do
      let (pk, sk) ← kemKe.keygen; pure (pk, sk))
    let st ← adv.preChallenge pkStar others
    let b ← $ᵗ Bool
    let (cStar, shared) ← kemKe.encaps pkStar
    let kRand ← $ᵗ Block
    let b' ← adv.postChallenge st cStar (if b then deriveK shared else kRand)
    return (b == b')

/-- **Corruption-aware KI advantage** (Test gated to the clean session whose peer `P*` is
uncorrupted). -/
noncomputable def CorruptKIAdvantage {n : ℕ} (adv : CorruptKIAdversary n) : ℝ :=
  (CorruptKI_Game adv).boolBiasAdvantage

/-- **The reduction that respects cleanness.** From a corruption-aware KI adversary build a KEM
IND-CPA adversary: in the pre-challenge phase, SELF-GENERATE the `n` other parties' keypairs (the
simulation of `Corrupt` for every party except `P*` — sound because per-party long-term keys are
independent), pass them plus `pk*` to the KI adversary; in the post-challenge phase, post-compose
`deriveK` onto the challenge key (exactly Demo 6's `kiToKemAdversary`). The KEM challenge `pk*` is
embedded as `P*`'s long-term key; the reduction NEVER computes `sk*` — it respects clause (d). -/
noncomputable def corruptKiToKemAdversary {n : ℕ} (adv : CorruptKIAdversary n) :
    kemKe.IND_CPA_Adversary where
  State := adv.State
  preChallenge pkStar := do
    let others ← (List.replicate n ()).mapM (fun _ => do
      let (pk, sk) ← kemKe.keygen; pure (pk, sk))
    adv.preChallenge pkStar others
  postChallenge st cStar k := adv.postChallenge st cStar (deriveK k)

/-- **Headline — the reduction respects cleanness (an equality), over the STRUCTURAL single-clean-
session model.** The corruption-aware single-session KI advantage `CorruptKIAdvantage` EQUALS the
KEM IND-CPA advantage of the reduction `corruptKiToKemAdversary`. Zero slack: the other-parties'
keypairs are sampled identically on both sides (so the pre-challenge phases coincide); the real
branch is literal `deriveK` post-composition; the random branch is `deriveK` of a uniform key =
uniform, by the registered bijection `deriveEquiv` (permutation invariance). The reduction embeds
the challenge ONLY in the uncorrupted peer `P*` and simulates `Corrupt` for every other party itself
— the standard B-S §21.9.3 reduction structure, here proved.

HOW THIS RELATES TO `cleanIn` (the honest seam — read this).** This equality is stated over
`CorruptKI_Game`, which models cleanness STRUCTURALLY, NOT by invoking the `cleanIn` predicate: the
peer `P*` is the one party whose secret `skStar` is never handed to the adversary (the omission of
`skStar` IS clause (d) — `P*` uncorrupted), while all `n` other parties' keypairs are handed over
(the maximally-corrupting clean adversary). The link between this structural model and the literal
`cleanIn` predicate is NOT a single end-to-end equality; it is carried by:
  - the guard lemmas (`corrupt_peer_then_test_unclean`, `reveal_self/partner/tested_then_test_unclean`,
    `clean_with_live_partner`, `reveal_live_partner_unclean`), which pin that `cleanIn` rejects
    exactly the trivial attacks and admits clean sessions (both sides non-trivial);
  - the genuine clean-gated multi-session game (`cakeGame` / `cakeAdvantage`), in which `cleanIn`
    actually gates each `Test` query of a running `OracleComp`, with its bit projecting cleanly
    (`cakeImpl_run_eq_cakeStepImpl`, `cakeAdvantage_eq_boolDistAdvantage`).
So "the reduction respects cleanness" is proved at the level of the structural maximally-corrupting
single-clean-session model; the connection to the literal `cleanIn` predicate is established by the
guard lemmas + the clean-gated game, NOT by a machine-checked composition that runs the reduction
inside `cakeImpl`. That composition (a multi-session clean-gated reduction telescoped through
`OracleHybrid`) is the next refinement; it is NOT claimed here. This headline is the static-corruption
+ single-clean-session fragment.

Honest scope (module docstring): for this synthetic `kemKe` the right-hand `IND_CPA_Advantage` is
large (`shared` leaks from `(pk, ct)`), so the bound certifies no byte-level security; the KEM
IND-CPA assumption stays UNINSTANTIATED. The value is the cleanness-under-corruption EXPRESSIBILITY
and reduction-RESPECT, machine-checked over extracted Rust. The reduction is an unconditional
equality consuming no unsatisfiable premise. -/
theorem cleanKi_advantage_eq_kem_ind_cpa {n : ℕ} (adv : CorruptKIAdversary n) :
    CorruptKIAdvantage adv =
      kemKe.IND_CPA_Advantage ProbCompRuntime.probComp (corruptKiToKemAdversary adv) := by
  rw [KEMScheme.IND_CPA_Advantage_eq_game_bias]
  unfold CorruptKIAdvantage
  suffices hgame : CorruptKI_Game adv
      = kemKe.IND_CPA_Game ProbCompRuntime.probComp (corruptKiToKemAdversary adv) by rw [hgame]
  unfold CorruptKI_Game KEMScheme.IND_CPA_Game corruptKiToKemAdversary
  show ProbCompRuntime.probComp.evalDist _ = ProbCompRuntime.probComp.evalDist _
  have hev : ∀ (mx : ProbComp Bool), ProbCompRuntime.probComp.evalDist mx = 𝒟[mx] :=
    fun mx => rfl
  have hlift : ∀ {β : Type} (pc : ProbComp β),
      ProbCompRuntime.probComp.liftProbComp pc = pc := fun pc => rfl
  rw [hev, hev]
  simp only [hlift]
  -- Flatten both sides to the same left-nested bind form: the RHS's `preChallenge` begins with the
  -- SAME `others` sampling, so after `bind_assoc` both sides are
  --   keygen; others; preChallenge; b; encaps; kRand; postChallenge
  -- with the only difference being the challenge key handed to `postChallenge`.
  simp only [bind_assoc]
  refine evalDist_ext (fun x => ?_)
  refine probOutput_bind_congr' _ x (fun pkStarPair => ?_)
  refine probOutput_bind_congr' _ x (fun others => ?_)
  refine probOutput_bind_congr' _ x (fun st => ?_)
  refine probOutput_bind_congr' _ x (fun b => ?_)
  refine probOutput_bind_congr' _ x (fun coinsPair => ?_)
  cases b with
  | true =>
    simp only [if_true]
  | false =>
    simp only [Bool.false_eq_true, if_false]
    exact evalDist_ext_iff.mp
      (evalDist_uniform_perm_invariant
        (fun kRand => do let b' ← adv.postChallenge st coinsPair.1 kRand; pure (false == b'))
        deriveEquiv) x

/-! ## End-of-game freshness: the Test-time-check seam, found and fixed.

WORKING THE ADAPTIVE-GAME REDUCTION BY HAND SURFACED A DEFINITIONAL FLAW in `cakeGame` (kept
above, unchanged, as the record of the discovery): its `cleanIn` gate is evaluated AT TEST TIME
ONLY. With the DYNAMIC `corrupt`/`reveal` oracles this admits compromise-AFTER-test distinguishers
that need no KEM assumption at all. The simplest:

    send 0 1 false   ↦ ct       -- open a session to peer 1; sid = ct is returned
    test 0           ↦ ch       -- clean AT THIS MOMENT ⇒ the challenge is handed out
    corrupt 1        ↦ sk₁      -- NOW corrupt the peer
    output (ch == deriveK (decapsK sk₁ ct))    -- decaps correctness recovers the REAL key

If `b = true` the comparison always succeeds; if `b = false` it succeeds only on a `2⁻²⁵⁶` `kRand`
collision. So this adversary's `cakeAdvantage` is ≈ 1 independent of any hardness assumption, and
NO bound of the form `cakeAdvantage ≤ f(KEM advantage)` is provable for the at-Test-time game.
(An even simpler variant uses `reveal 0` after `test 0`.) The formal ingredients are already
registered: `decapsK_encapsK_correct` is the recovery step, and `corrupt_peer_then_test_unclean`
shows the PREDICATE would reject the session — the bug is WHEN it is consulted, not what it says.

THE FIX (the standard convention): real AKE definitions evaluate freshness over the WHOLE TRACE,
not at Test time — B-S §21 requires the test session to (still) be fresh when the adversary halts,
and FG's `clean` predicates are conditions on the complete experiment transcript. `cakeGameFinal`
below scores `b == b'` only if every tested session is fresh IN THE FINAL STATE; otherwise it
outputs a fresh coin, so unclean traces contribute exactly zero bias (the "penalize-to-coin"
convention, compatible with `boolBiasAdvantage`).

This is precisely the multi-trap cleanness-predicate subtlety the FG-transcription assessment
flagged as the open risk (the `clean^PQXDH` trap class), here surfaced CONCRETELY by the synthetic
rehearsal — the derisking this demo exists to do. The lesson for the real transcription: the
freshness predicate's EVALUATION POINT is as load-bearing as its clauses. -/

/-- End-of-game freshness for a (tested) session: clauses (a)/(b)/(d) of `cleanIn`, read against
the FINAL state. Clause (c) (`!tested`) is deliberately ABSENT: at game end every scored session
has `tested := true` by construction; (c) was only the no-double-Test gate at query time. -/
def CSession.freshAtEnd (s : CSession) (gs : CGameState) : Bool :=
  !s.revealed
  && (match s.partner with
      | some j => !(gs.sessions.getD j default).revealed
      | none   => true)
  && !(gs.peerCorrupted s.peer)

/-- `cleanIn` is exactly end-of-game freshness PLUS the not-yet-tested query gate: the Test-time
predicate and the end-of-game predicate differ ONLY in clause (c). This pins that `cakeGameFinal`
strengthens (not changes) the cleanness notion: the same (a)/(b)/(d) conditions, re-checked at the
right time. -/
theorem cleanIn_eq_freshAtEnd_and_not_tested (s : CSession) (gs : CGameState) :
    s.cleanIn gs = (s.freshAtEnd gs && !s.tested) := by
  unfold CSession.cleanIn CSession.freshAtEnd
  ac_rfl

/-- Whole-trace cleanness: every session that was scored as a Test challenge (`tested = true`) is
fresh in the final state. Untested sessions impose no condition. -/
def CGameState.finalClean (gs : CGameState) : Bool :=
  gs.sessions.all (fun s => !s.tested || s.freshAtEnd gs)

/-- **The CORRECTED multi-session clean-gated KI game** — `cakeGame` with the standard whole-trace
freshness convention: run the adversary against the same `cakeImpl` handler (Test still gated by
`cleanIn` at query time, so double-testing and testing-while-unclean still default), then score
`b == b'` ONLY if the final state is `finalClean`; otherwise output a fresh coin. The
compromise-after-test traces that break the at-Test-time game are thereby scored as coins (zero
bias) instead of wins. -/
noncomputable def cakeGameFinal (parties : List Party) (adv : CAkeAdversary) : ProbComp Bool := do
  let b ← ($ᵗ Bool : OracleComp unifSpec Bool)
  let (b', gsF) ← cakeImpl.runState { b := b, parties := parties, sessions := [] } adv
  if gsF.finalClean then pure (b == b') else ($ᵗ Bool : OracleComp unifSpec Bool)

/-- The corrected multi-session clean-gated KI advantage — the bias of `cakeGameFinal`. -/
noncomputable def cakeAdvantageFinal (parties : List Party) (adv : CAkeAdversary) : ℝ :=
  (cakeGameFinal parties adv).boolBiasAdvantage

/-- **The corrupt-after-test attack is EXCLUDED (generic).** Any final state containing a tested
session whose peer ends corrupted fails `finalClean` — so under the corrected convention every
corrupt-the-peer-after-test trace is scored as a coin (zero bias), never a win. This is the formal
exclusion the at-Test-time game lacks. -/
theorem tested_peer_corrupted_not_finalClean (gs : CGameState) (s : CSession)
    (hmem : s ∈ gs.sessions) (htested : s.tested = true)
    (hcorr : gs.peerCorrupted s.peer = true) :
    gs.finalClean = false := by
  apply Bool.eq_false_iff.mpr
  intro hall
  rw [CGameState.finalClean, List.all_eq_true] at hall
  have h := hall s hmem
  simp [htested, CSession.freshAtEnd, hcorr] at h

/-- **The reveal-after-test attack is EXCLUDED (generic).** Any final state containing a tested
session whose own key ends revealed fails `finalClean` — the simplest compromise-after-test trace
(`test i; reveal i; compare`) is likewise scored as a coin. -/
theorem tested_revealed_not_finalClean (gs : CGameState) (s : CSession)
    (hmem : s ∈ gs.sessions) (htested : s.tested = true)
    (hrev : s.revealed = true) :
    gs.finalClean = false := by
  apply Bool.eq_false_iff.mpr
  intro hall
  rw [CGameState.finalClean, List.all_eq_true] at hall
  have h := hall s hmem
  simp [htested, CSession.freshAtEnd, hrev] at h

/-- The state shape the corrupt-after-test trace ends in: the session TESTED, its peer (party 1)
now CORRUPTED. (`goodSession` with `tested := true`; both parties' corruption flags set.) -/
def corruptAfterTestState : CGameState :=
  { b := true,
    parties := [ { pk := default, sk := default, corrupted := true },
                 { pk := default, sk := default, corrupted := true } ],
    sessions := [ { goodSession with tested := true } ] }

/-- **Concrete instance:** the corrupt-after-test final state fails `finalClean`. -/
theorem corruptAfterTest_not_finalClean : corruptAfterTestState.finalClean = false := by
  decide

/-- The clean-trace final state: `goodSession` TESTED, its peer (party 1) still honest. -/
def cleanFinalState : CGameState :=
  { b := true, parties := witnessParties,
    sessions := [ { goodSession with tested := true } ] }

/-- **Anti-vacuity for the corrected convention:** a tested-and-still-fresh final state PASSES
`finalClean` — clean traces still score `b == b'`, so the corrected game is not vacuous (the coin
branch does not swallow honest runs). Together with `tested_peer_corrupted_not_finalClean` /
`tested_revealed_not_finalClean` this is the both-sided non-triviality of the END-OF-GAME
convention, mirroring the Test-time pair (`exists_clean_test_session` + the `*_unclean` guards). -/
theorem finalClean_witness : cleanFinalState.finalClean = true := by
  decide

end Demo6AkeCorrupt
