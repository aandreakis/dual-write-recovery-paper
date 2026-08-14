(*  Title:       Dual_Write_Effect_Observation_Law.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE NAME SLICE (reference-object program, Phase 2; owner decisions
    D-095/D-097) --- an additive post-freeze sibling under the freeze's
    own protocol: no landed statement, proof, definition, name, import,
    or session-DAG change to the frozen corpus.  ZERO new theorems:
    this theory only NAMES the corpus's organizing law and re-exports
    the landed facts under the law's canonical fact names (alias
    bindings; no new proof obligation enters the trusted base).

    THE OBSERVATION BOUND --- the organizing law of the dual-write
    corpus, already proved as observation_measured_dilemma
    (Dual_Write_Effect_Observation_Bound.thy, ladder section 31): on
    the designed witness pair --- equal durable cores, equal epochs,
    divergent emission ledgers, both effect-safe and genuinely
    emitting --- ANY recovery-metadata channel, of ANY result type,
    that agrees on the pair defeats every recovery policy factoring
    through it: the policy's own re-drive heals every scoped store
    mismatch at the pinned coordinate, yet the run is effect-unsafe on
    one member or loses a committed effect on the other.

    The practitioner reading (the lesson, stated at its honest
    strength): "recovery can only restore what it can observe."  A
    recovery process whose metadata cannot DISTINGUISH two histories
    cannot repair their difference, no matter how that metadata is
    encoded --- an external cursor, a generation counter, a dedup
    digest, any recovery metadata whatsoever.  The mechanism that
    survives is reading the sink itself: an accurate delivered-suffix
    observation separates the designed pair
    (ledger_length_separates_pair), so it lies outside every defeated
    class here; paired with fencing against concurrent and zombie
    interference it is the landed positive lane --- the "Sink-and-
    Fence" mechanism (the sink-reading escape and the fenced re-drive
    of the landed corpus; see the effect tier's fencing lane and the
    unified tier's discipline lane).

    HONESTY FENCES (they travel with this theory and bind every
    quotation of the law):
    - Exists-machine polarity: the law says "there IS a designed
      dual-write machine/pair on which EVERY agreeing observation
      channel is defeated" --- never a for-every-system claim, never
      "exactly-once is impossible" as a pure negative, and no new
      impossibility class: the lift only re-packages the landed
      kernel's own derivation (see the section-31 provenance).
    - For-all-observations scope: the inner quantifier ranges over
      observation channels obs :: (nat, nat) dwe_state => 'r with 'r
      FREE --- the law's strength is the type-generic channel, not a
      universal machine claim.
    - The edge is disclosed in both directions: an ACCURATE
      delivery-count cursor persisted outside the store separates the
      pair, so nothing here defeats it --- and nothing here claims it
      EARNS the escape's guarantees either (that is proved only for
      the landed sink_delta policy); conversely a ledger-READING
      observation that happens to agree on the pair is still defeated
      (reading the sink is necessary for survival, not sufficient:
      the channel must resolve the delivered suffix the members
      actually differ in).
    - Statement-vs-pin: the slogan is the READING of the law; the
      binding object is the exact landed statement aliased below.
      Wherever slogan and statement could diverge, the statement wins.

    Handle pairing (owner decision D-097 L8): the mechanism handle
    (read authoritative sink acceptance, then fence it) leads
    practitioner surfaces; the
    information-boundary principle ("the boundary is information, not
    storage") is stated here as the lesson and is promoted to a
    headline only on discharged for-all-interface evidence --- which
    does not exist today and is not claimed.

    Provenance: reference-object program Phase-2 NAME slice
    (roads/program/, owner decisions D-095, D-097 L8/L14), gate
    P3_EGate40.  In-source ML oracle gates are STRIPPED at landing per
    house rule; oracle-freedom is certified by the scratch-side gate
    session with confirmed-biting negative controls
    (roads/program/phase2_gates/egate40/).
*)

theory Dual_Write_Effect_Observation_Law
  imports Dual_Write_Effect_Observation_Bound
begin

section \<open>The Observation Bound: the corpus's organizing law, named\<close>

text \<open>
  THE OBSERVATION BOUND.  The landed statement, in words (the binding
  object is @{thm [source] observation_measured_dilemma}, aliased
  verbatim below): there exist two reachable states of the designed
  witness machine with equal durable cores, equal epochs, divergent
  emission ledgers, both effect-safe and genuinely emitting, such that
  for EVERY observation @{text "obs :: (nat, nat) dwe_state \<Rightarrow> 'r"}
  (result type free) agreeing on the pair and every policy @{text P}
  factoring through it (@{text "\<forall>t. P t = g (obs t)"}), there are
  re-drive outcomes on both members that heal every scoped store
  mismatch at the pinned coordinate, while the run is effect-unsafe on
  one member or loses the committed effect on the other.

  Reading: recovery can only restore what it can observe.  A recovery
  channel that cannot tell two histories apart cannot repair their
  difference --- and "channel" is any recovery metadata of any type.
  The slogan is exactly as strong as the statement above --- an
  exists-pair, for-all-channels fact on the designed machine --- and
  no stronger.
\<close>

lemmas observation_bound = observation_measured_dilemma

text \<open>
  The lift behind the law, at the designed pair: any agreeing
  observation channel defeats every policy factoring through it.
\<close>

lemmas observation_bound_lift = pair_agreeing_observation_defeated

text \<open>
  The law's disclosed edge, separation direction: an accurate
  delivered-count observation distinguishes the pair (the emission
  ledgers have lengths 2 and 1), so it fails the agreement premise of
  every theorem above and lies outside every class this law defeats.
\<close>

lemmas observation_bound_separating_edge = ledger_length_separates_pair

text \<open>
  The law's disclosed edge, insufficiency direction: reading the sink
  is necessary for survival, not sufficient --- a ledger-reading
  observation that still agrees on the pair is still defeated; the
  channel must resolve what the members actually differ in.
\<close>

lemmas observation_bound_reading_insufficient =
  ledger_reading_observation_still_defeated

end
