(*  Title:       Dual_Write_Effect_Compensation.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Compensable sinks: is irreversibility load-bearing for the landed
    recovery-information dilemma?  (Theory-backlog items F and G, the
    extension wave's F+G slice) --- an additive post-freeze slice under
    the freeze's own protocol: no landed statement, proof, definition,
    name, import, or session-DAG change to the frozen corpus.  A
    CONTROL/SECTION-grade addition on the landed law's boundary, never a
    headline: the landed T2.10 dilemma, its T2.11 exactly-once reading,
    and the Dichotomy remain the results of record, exactly as scoped.

    THE ONE-QUESTION ANSWER, at theorem level: irreversibility is
    load-bearing exactly as CANCELLATIVITY of the sink's observable, and
    not as absence of compensating actions.  The refined slogan, fence-
    checked: "compensating actions do not escape the dilemma; absorbing
    sinks do" --- where "absorbing" means the MATCHED semantics below
    (order-aware cancel, unmatched compensations absorbed as no-ops),
    never the signed or truncated ones.  Both branches are theorems:

    ESCAPE BRANCH (matched/absorbing semantics): the store-measured
    policy compensate-everything-then-redo-everything achieves
    per-obligation matched-view count one at its own frontier, on every
    payload-duplicate-free crashed state of the pinned type with a
    strictly ascending, forward-only committed source
    (matched_view_escape_general; the design-pinned six-premise form
    matched_view_escape follows by weakening), with the policy provably
    store-measured (compensate_redo_store_measured) and the SAME batch
    succeeding on BOTH members of the landed dilemma pair
    (matched_view_escape_inhabited) --- the designed pair no longer
    separates at the matched observable.  Over-compensation of
    never-delivered effects is absorbed by the semantics
    (over_compensation_absorbed), and compensations need no guard: a
    backward payload never increases any matched-view count
    (compensation_appends_guard_free) --- the compensable analogue of
    Resume-guard-freedom in the landed discipline (item G's honest
    positive; the general saga DISCIPLINE over interleaved partial
    compensations is recorded future work, not claimed).

    NO-ESCAPE BRANCH (cancellative semantics): if the observable is
    signed (group-like net counts: every compensation permanently shifts
    state, e.g. a balance counter) or even aggregate-truncated
    (floor-at-zero counters, nat monus), the landed designed pair's gap
    of one survives EVERY shared appended batch --- compensate-then-redo
    included --- so every store-measured and every (core, epoch)-measured
    policy still fails (signed_view_batch_agreement_dilemma,
    signed_view_recovery_dilemma, signed_view_epoch_measured_dilemma,
    truncated_view_no_escape_control).  These rows are presented as the
    landed batch-agreement argument re-run at the signed/truncated view,
    in the T2.11 manner --- a reading of the same designed pair, never a
    new impossibility class; exists-system polarity throughout, and the
    impossibility rows consume NO ordering premise (right polarity,
    unchanged from the landed corpus).  The truncated row is the
    load-bearing control killing the floor-at-zero middle position: the
    compensate-redo batch itself lands the LOSS member at truncated view
    0, not 1 (trunc_compensate_redo_loss_zero) --- order-blind absorption
    at the aggregate is not enough; ORDER-AWARE matching (a per-entry
    stateful lookup in the sink) is the load-bearing ingredient.

    RAW-VS-MATCHED PARTING CONTROL (mandatory; what keeps the landed
    corpus untouched-and-honest): the escape's own redrive at the landed
    safe-side witness is premature AND duplicate in the landed RAW
    taxonomy --- effect_unsafe fires, exactly_once_at fails --- AT THE
    SAME STATE where the matched view is exact
    (matched_escape_raw_hazard_control).  The two observables provably
    part ways at one state: the landed dichotomy is about the raw
    observable of irreversible sinks and remains exhaustive there.

    COMPLETER: the idempotent cell's store-measured escape becomes a
    named theorem (dedup_view_bulk_redrive_escape): the drop-0 bulk
    policy --- literally the m = 0 instance of the landed
    cursor_policy_store_measured --- heals and leaves per-obligation
    dedup-view count one, via the landed T2.11 layer-1 iff.  The
    effect-class picture, four rows, each cell theorem-backed:
    irreversible (raw view): impossible, the landed T2.10/T2.11/
    Dichotomy; idempotent (dedup view): possible store-measured (the
    completer); compensable-matched: possible store-measured (the
    escape); compensable-cancellative (signed, truncated): impossible
    (the new rows).  Every "possible" cell works by the sink inspecting
    its own state at apply time --- the landed sentence "exactly-once
    effect recovery exists and requires reading the sink" keeps its full
    strength for the raw observable, and the new rows say precisely
    where the read can live instead, never that it can be eliminated.

    VOCABULARY FENCES (binding, from the freeze documents): the bare
    phrase "exactly-once" is never used unqualified and no new name
    contains it --- the matched notion is "per-obligation matched-view
    count one at the redrive's own frontier", stated as inline count
    forms mirroring T2.11's layer-1 left-hand side, which is likewise
    nameless.  The count-one conjunct subsumes delivery and therefore
    INHERITS the terminal-state liveness stand-in status of the landed
    lost_effect / at_least_once_at boundary (through the landed
    at_least_once_iff_not_lost bridge) --- a state-level reading at the
    redrive's own frontier, not a temporal eventually.  The escape is
    parametric over any state of the pinned type (exactly the landed
    B1 posture, boundary row 5); the dilemma rows are exists-system.
    The forward_only_source premise is disclosed at every consumption
    site and witnessed load-bearing
    (matched_escape_forward_premise_load_bearing); the ascending premise
    is consumed by the escape exactly where the landed B1 consumes it
    and is witnessed load-bearing at the landed equal-coordinate posture
    (matched_escape_asc_load_bearing); the impossibility rows consume
    neither.  Efficiency honesty: the escape fires 2*|R| writes per
    recovery and its RAW ledger footprint grows by that much per crash
    cycle --- a possibility-boundary theorem, not an engineering
    recommendation (the landed sink-reading delta stays the
    practitioner's policy).

    MODELING DELTA: definitions only, over the existing ledger.  Every
    new observable is a pure function (a projection) of the landed
    emission ledger; remove1 happens inside the projection mview, never
    on dwe_emitted; compensating emissions are ordinary appends through
    the LANDED policy_redrive.  No new machine, no new record, no new
    rule; boundary row 3 (the append-only two-store boundary) is
    byte-untouched.  The landed sink_dedup_view is the in-corpus
    precedent for observable-as-projection.  Compensation entries are
    unjustified in the landed taxonomy by design (their payloads are not
    committed source events), so raw premature fires on them --- the
    compensable world gets its own count-form conclusions and never
    touches effect_unsafe's definition.  The concrete scheme comp0/fwd0
    (a mod-20 coordinate flip lifted through the src_coord bijection) is
    an identifier-space convention standing in for "every effect has a
    distinguished compensating counterpart"; the theorems are parametric
    in any compensation_scheme.

    IMPORTS: the single cyclic-lane sibling Dual_Write_Effect_
    Exactly_Once (through it Dilemma / Discipline / Cyclic), consumed
    for the T2.11 layer-1 iff, the exactly-once vocabulary of the raw
    control, ascending_obligations_distinct, and
    count_list_distinct_mem.  The terminal branch is deliberately NOT
    imported (namespace rule).  The section-18 equal-coordinate control
    posture (psl_w) is re-declared locally as cpsl_w because
    Dual_Write_Effect_Sink_Delta_Idempotence is not in this import cone
    (the Decider precedent for out-of-cone re-declaration); the
    cross-reference is @{text psl_w}-prose only.

    PROVENANCE: paper/dual_write/theory_backlog/FG_COMPENSATION_DESIGN.md
    (the binding spec; extension-wave F+G spike, 2026-07-06) and the
    banked probe paper/dual_write/theory_backlog/fg_probe/
    FG_Compensation_Probe.thy (GREEN x2 clean-db, quick_and_dirty=false,
    md5 4cc7d5d510be678300433c2a93c3ab13): the probe machine-checks both
    branch cruxes at the list level; this theory ports its content
    against the landed definitions.  Probe-to-landed statement
    adaptations are recorded in the slice report.  Local counting
    helpers are deduped against HOL2025-2 (count_list_append,
    count_list_0_iff, count_list_remove1 are stock) and against the
    landed count_list_distinct_mem --- cited, not restated.

    In-source ML oracle gates are STRIPPED at landing: oracle-freedom
    is certified by scratch-side per-slice gate sessions with
    confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Compensation
  imports Dual_Write_Effect_Exactly_Once
begin

section \<open>The compensation scheme and the three observables\<close>

text \<open>
  A compensation scheme is a total involution @{term cmp} on payloads
  together with an orientation predicate @{term fwd} that the involution
  flips: the compensation of a forward payload is backward and vice
  versa (which also yields fixpoint-freedom).  Totality is cheaply
  inhabitable (the concrete scheme below) and avoids option-plumbing;
  the orientation flip is what lets the matched view treat any backward
  payload as a canceller of its forward counterpart with no ambiguity
  about "compensating a compensation" (@{term "cmp"} of a backward
  payload is forward and appends again --- coherent by the involution).
\<close>

definition compensation_scheme :: "('p \<Rightarrow> 'p) \<Rightarrow> ('p \<Rightarrow> bool) \<Rightarrow> bool" where
  "compensation_scheme cmp fwd \<longleftrightarrow>
     (\<forall>p. cmp (cmp p) = p) \<and> (\<forall>p. fwd (cmp p) \<longleftrightarrow> \<not> fwd p)"

text \<open>The disclosed source premise of the escape branch: every committed
  source payload is forward --- real WALs commit business facts, not
  compensation records.  Named, disclosed at every consumption site,
  and witnessed load-bearing below; the impossibility rows never
  consume it.\<close>

definition forward_only_source :: "('p \<Rightarrow> bool) \<Rightarrow> 'p list \<Rightarrow> bool" where
  "forward_only_source fwd H \<longleftrightarrow> (\<forall>p \<in> set H. fwd p)"

text \<open>
  THE MATCHED (absorbing) OBSERVABLE.  One apply step: a forward payload
  appends; a backward payload removes ONE occurrence of its forward
  counterpart if present and is a no-op otherwise
  (@{const remove1}-if-present-else-noop) --- a stateful per-entry
  lookup the SINK performs at apply time, precisely the move the landed
  dedup sink makes at T2.11.  The view is a pure projection of the
  payload stream; the ledger itself stays append-only (boundary row 3
  untouched), exactly the @{const sink_dedup_view} precedent.
\<close>

definition mstep :: "('p \<Rightarrow> bool) \<Rightarrow> ('p \<Rightarrow> 'p) \<Rightarrow> 'p list \<Rightarrow> 'p \<Rightarrow> 'p list" where
  "mstep fwd cmp os p = (if fwd p then os @ [p] else remove1 (cmp p) os)"

definition mview :: "('p \<Rightarrow> bool) \<Rightarrow> ('p \<Rightarrow> 'p) \<Rightarrow> 'p list \<Rightarrow> 'p list" where
  "mview fwd cmp ps = foldl (mstep fwd cmp) [] ps"

definition comp_matched_view
  :: "((src_coord \<times> ('k, 'v) source_event) \<Rightarrow> bool)
      \<Rightarrow> ((src_coord \<times> ('k, 'v) source_event)
           \<Rightarrow> (src_coord \<times> ('k, 'v) source_event))
      \<Rightarrow> ('k, 'v) dwe_state
      \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list"
where
  "comp_matched_view fwd cmp t = mview fwd cmp (map e_payload (dwe_emitted t))"

text \<open>
  THE SIGNED (cancellative) OBSERVABLE: the integer net count --- forward
  occurrences minus backward occurrences.  Every compensation permanently
  shifts the value (a balance counter: a refund for a payment that never
  executed is itself money moving).  And its TRUNCATED weakening: the
  same difference at nat monus (a floor-at-zero counter).
\<close>

definition net_count :: "('p \<Rightarrow> 'p) \<Rightarrow> 'p list \<Rightarrow> 'p \<Rightarrow> int" where
  "net_count cmp ps p = int (count_list ps p) - int (count_list ps (cmp p))"

definition net_view_exact_at
  :: "((src_coord \<times> ('k, 'v) source_event)
        \<Rightarrow> (src_coord \<times> ('k, 'v) source_event))
      \<Rightarrow> frontier \<Rightarrow> ('k, 'v) dwe_state \<Rightarrow> bool"
where
  "net_view_exact_at cmp f t \<longleftrightarrow>
     (\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                   (exec_scope (dwe_core t)) f).
        net_count cmp (map e_payload (dwe_emitted t)) p = 1)"

definition trunc_count :: "('p \<Rightarrow> 'p) \<Rightarrow> 'p list \<Rightarrow> 'p \<Rightarrow> nat" where
  "trunc_count cmp ps p = count_list ps p - count_list ps (cmp p)"

text \<open>
  THE STORE-MEASURED RECOVERY POLICY under test: compensate everything
  the replay could owe, then redo all of it --- the batch
  @{term "map cmp R @ R"} over the frontier-bounded scoped replay
  @{term R}.  A policy CAN enumerate this compensating superset without
  reading the sink (the replay is core-derivable); the match-check does
  not disappear --- it migrates into the sink's apply-time semantics.
  Its emissions go through the LANDED @{const policy_redrive} unchanged.
\<close>

definition compensate_redo_policy
  :: "((src_coord \<times> (nat, nat) source_event)
        \<Rightarrow> (src_coord \<times> (nat, nat) source_event))
      \<Rightarrow> frontier \<Rightarrow> redrive_policy"
where
  "compensate_redo_policy cmp f t =
     (let R = replay_down_hist (exec_src_hist (dwe_core t))
                (exec_scope (dwe_core t)) f
      in map cmp R @ R)"

theorem compensate_redo_store_measured:
  "store_measured (compensate_redo_policy cmp f)"
  unfolding store_measured_def
  by (intro exI[of _ "\<lambda>c. (let R = replay_down_hist (exec_src_hist c)
                                     (exec_scope c) f
                           in map cmp R @ R)"])
     (simp add: compensate_redo_policy_def Let_def)


section \<open>The matched-cancellation toolbox (probe M-layer, ported)\<close>

text \<open>A block of forward payloads appends verbatim (probe M1).\<close>

lemma mview_forward_block:
  assumes "\<forall>p \<in> set ps. fwd p"
  shows "foldl (mstep fwd cmp) os ps = os @ ps"
  using assms by (induction ps arbitrary: os) (simp_all add: mstep_def)

text \<open>A block of compensations folds to @{const remove1} (probe M2).\<close>

lemma mview_compensation_block:
  assumes invol: "\<And>p. cmp (cmp p) = p"
      and bk: "\<forall>p \<in> set R. \<not> fwd (cmp p)"
  shows "foldl (mstep fwd cmp) os (map cmp R) = fold remove1 R os"
  using bk
  by (induction R arbitrary: os) (simp_all add: mstep_def invol)

text \<open>On a distinct list, @{const remove1} is a filter --- the content of
  HOL's @{thm [source] distinct_remove1_removeAll} composed with
  @{thm [source] removeAll_filter_not_eq}, re-oriented.\<close>

lemma remove1_distinct_filter:
  assumes "distinct xs"
  shows "remove1 x xs = filter (\<lambda>y. y \<noteq> x) xs"
proof -
  have "remove1 x xs = removeAll x xs"
    by (rule distinct_remove1_removeAll[OF assms])
  also have "\<dots> = filter (\<lambda>y. x \<noteq> y) xs"
    by (simp add: removeAll_filter_not_eq)
  also have "\<dots> = filter (\<lambda>y. y \<noteq> x) xs"
    by (rule filter_cong) auto
  finally show ?thesis .
qed

text \<open>Folding @{const remove1} over a distinct accumulator is one filter
  (probe M3).\<close>

lemma fold_remove1_distinct_filter:
  assumes "distinct os"
  shows "fold remove1 R os = filter (\<lambda>x. x \<notin> set R) os"
  using assms
proof (induction R arbitrary: os)
  case Nil
  then show ?case by (simp add: filter_id_conv)
next
  case (Cons r R')
  have step: "remove1 r os = filter (\<lambda>y. y \<noteq> r) os"
    by (rule remove1_distinct_filter[OF Cons.prems])
  have d: "distinct (filter (\<lambda>y. y \<noteq> r) os)"
    using Cons.prems by simp
  have "fold remove1 (r # R') os
      = fold remove1 R' (filter (\<lambda>y. y \<noteq> r) os)"
    by (simp add: step)
  also have "\<dots> = filter (\<lambda>x. x \<notin> set R') (filter (\<lambda>y. y \<noteq> r) os)"
    by (rule Cons.IH[OF d])
  also have "\<dots> = filter (\<lambda>x. x \<notin> set (r # R')) os"
    by (rule filter_filter[THEN trans]) (rule filter_cong; auto)
  finally show ?case .
qed

text \<open>THE ABSORPTION MECHANISM, named (probe M5): an unmatched backward
  payload is a no-op --- over-compensation of a never-delivered effect
  costs nothing at the matched observable.  Under the signed and
  truncated observables it is NOT absorbed; that asymmetry is the whole
  result of this theory.\<close>

theorem over_compensation_absorbed:
  assumes "\<not> fwd p" and "cmp p \<notin> set os"
  shows "mstep fwd cmp os p = os"
  using assms by (simp add: mstep_def remove1_idem)

text \<open>
  ITEM G's HONEST POSITIVE: compensations need NO guard --- one apply
  step of ANY backward payload never increases any matched-view count
  (HOL's @{thm [source] count_list_remove1}).  The T2.8 discipline's
  compensable analogue adds zero new guard classes, exactly as Resume
  is guard-free in the landed discipline.  The general saga DISCIPLINE
  (interleaved partial compensations, multi-round crash-interrupted
  compensate-redo convergence, a named weaker safety notion for signed
  sinks) is recorded future work; nothing below claims it.
\<close>

theorem compensation_appends_guard_free:
  assumes "\<not> fwd p"
  shows "count_list (mstep fwd cmp os p) q \<le> count_list os q"
  using assms by (simp add: mstep_def)

text \<open>The accumulator facts the state-level escape needs: every element
  of a matched view is forward (backward payloads only ever remove),
  and the view of a distinct stream is distinct.\<close>

lemma mview_acc_forward:
  assumes "\<forall>q \<in> set os. fwd q"
  shows "\<forall>q \<in> set (foldl (mstep fwd cmp) os ps). fwd q"
  using assms
proof (induction ps arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases "fwd p")
    case True
    have base: "\<forall>q \<in> set (os @ [p]). fwd q"
      using Cons.prems True by auto
    show ?thesis
      using Cons.IH[OF base] True by (simp add: mstep_def)
  next
    case False
    have base: "\<forall>q \<in> set (remove1 (cmp p) os). fwd q"
      using Cons.prems set_remove1_subset by fastforce
    show ?thesis
      using Cons.IH[OF base] False by (simp add: mstep_def)
  qed
qed

lemma mview_forward_elements:
  "\<forall>q \<in> set (mview fwd cmp ps). fwd q"
  unfolding mview_def by (rule mview_acc_forward) simp

lemma mview_acc_distinct:
  assumes "distinct os" and "distinct ps" and "set os \<inter> set ps = {}"
  shows "distinct (foldl (mstep fwd cmp) os ps)"
  using assms
proof (induction ps arbitrary: os)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases "fwd p")
    case True
    have notin: "p \<notin> set os"
      using Cons.prems(3) by auto
    have d1: "distinct (os @ [p])"
      using Cons.prems(1) notin by simp
    have disj: "set (os @ [p]) \<inter> set ps = {}"
      using Cons.prems(2,3) by auto
    show ?thesis
      using Cons.IH[OF d1 _ disj] Cons.prems(2) True
      by (simp add: mstep_def)
  next
    case False
    have d1: "distinct (remove1 (cmp p) os)"
      using Cons.prems(1) by simp
    have disj: "set (remove1 (cmp p) os) \<inter> set ps = {}"
      using Cons.prems(3) set_remove1_subset by fastforce
    show ?thesis
      using Cons.IH[OF d1 _ disj] Cons.prems(2) False
      by (simp add: mstep_def)
  qed
qed

lemma mview_distinct:
  assumes "distinct ps"
  shows "distinct (mview fwd cmp ps)"
  unfolding mview_def using assms
  by (intro mview_acc_distinct) simp_all


section \<open>The concrete scheme: a mod-20 coordinate flip (probe C1, lifted)\<close>

text \<open>
  The witness scheme on the pinned payload type: flip the coordinate's
  representing nat across a mod-20 band (residues 0..9 are forward,
  10..19 backward), leave the business event untouched.  The witness
  coordinates @{term "coord_of_nat 1"} / @{term "coord_of_nat 2"} (the
  landed @{const ec1} / @{const ec2}) are forward; their compensations
  live at coordinates 11 and 12 --- a reserved identifier range disjoint
  from every committed coordinate of the landed witnesses and strictly
  beyond the witness frontier, so compensations never enter any replay
  (@{const replay_down_hist} filters at the frontier).  Honest reading:
  an identifier-space convention standing in for "every effect has a
  distinguished compensating counterpart"; every general theorem above
  and below is parametric in ANY @{const compensation_scheme}.
\<close>

definition tcmp :: "nat \<Rightarrow> nat" where
  "tcmp c = (if c mod 20 < 10 then c + 10 else c - 10)"

definition tfwd :: "nat \<Rightarrow> bool" where
  "tfwd c \<longleftrightarrow> c mod 20 < 10"

lemma mod20_shift_up:
  fixes c :: nat
  assumes "c mod 20 < 10"
  shows "(c + 10) mod 20 = c mod 20 + 10"
proof -
  have "(c + 10) mod 20 = (c mod 20 + 10) mod 20"
    by (simp add: mod_add_left_eq)
  also have "\<dots> = c mod 20 + 10"
    using assms by (intro mod_less) simp
  finally show ?thesis .
qed

lemma mod20_shift_down:
  fixes c :: nat
  assumes ge: "10 \<le> c mod 20"
  shows "(c - 10) mod 20 = c mod 20 - 10"
proof -
  have le_c: "10 \<le> c"
    using ge mod_less_eq_dividend[of c 20] by linarith
  have c_split: "c = 20 * (c div 20) + c mod 20"
    by simp
  have "c - 10 = 20 * (c div 20) + (c mod 20 - 10)"
    using ge c_split by linarith
  then have "(c - 10) mod 20 = (20 * (c div 20) + (c mod 20 - 10)) mod 20"
    by simp
  also have "\<dots> = (c mod 20 - 10) mod 20"
    by (simp add: mod_mult_self3)
  also have "\<dots> = c mod 20 - 10"
    by (intro mod_less) simp
  finally show ?thesis .
qed

lemma tcmp_invol: "tcmp (tcmp c) = c"
proof (cases "c mod 20 < 10")
  case True
  then have up: "(c + 10) mod 20 = c mod 20 + 10"
    by (rule mod20_shift_up)
  then show ?thesis
    using True by (simp add: tcmp_def)
next
  case False
  then have ge: "10 \<le> c mod 20" by simp
  have le_c: "10 \<le> c"
    using ge mod_less_eq_dividend[of c 20] by linarith
  have down: "(c - 10) mod 20 = c mod 20 - 10"
    by (rule mod20_shift_down[OF ge])
  have lt: "(c - 10) mod 20 < 10"
    using down ge by simp
  show ?thesis
    using False lt le_c by (simp add: tcmp_def)
qed

lemma tfwd_flip: "tfwd (tcmp c) \<longleftrightarrow> \<not> tfwd c"
proof (cases "c mod 20 < 10")
  case True
  then show ?thesis
    by (simp add: tcmp_def tfwd_def mod20_shift_up)
next
  case False
  then have ge: "10 \<le> c mod 20" by simp
  show ?thesis
    using False by (simp add: tcmp_def tfwd_def mod20_shift_down[OF ge])
qed

lemma tcmp_fixpoint_free: "tcmp c \<noteq> c"
proof (cases "c mod 20 < 10")
  case True
  then show ?thesis by (simp add: tcmp_def)
next
  case False
  then have "10 \<le> c"
    using mod_less_eq_dividend[of c 20] by linarith
  then have "c - 10 < c" by linarith
  then show ?thesis
    using False by (simp add: tcmp_def)
qed

text \<open>The lift through the landed @{type src_coord} bijection (both
  round-trips are landed simp rules in the layer-0 theory).\<close>

definition comp0
  :: "src_coord \<times> (nat, nat) source_event
      \<Rightarrow> src_coord \<times> (nat, nat) source_event"
where
  "comp0 p = (coord_of_nat (tcmp (Rep_src_coord (fst p))), snd p)"

definition fwd0 :: "src_coord \<times> (nat, nat) source_event \<Rightarrow> bool" where
  "fwd0 p \<longleftrightarrow> tfwd (Rep_src_coord (fst p))"

lemma comp0_invol: "comp0 (comp0 p) = p"
  by (simp add: comp0_def tcmp_invol)

lemma fwd0_flip: "fwd0 (comp0 p) \<longleftrightarrow> \<not> fwd0 p"
  by (simp add: comp0_def fwd0_def tfwd_flip)

theorem comp0_scheme: "compensation_scheme comp0 fwd0"
  unfolding compensation_scheme_def
  by (simp add: comp0_invol fwd0_flip)

text \<open>The reserved range, computed at the landed witness payloads.\<close>

lemma comp0_witness_coords:
  "comp0 (ec1, e1) = (coord_of_nat 11, e1)
 \<and> comp0 (ec2, e2) = (coord_of_nat 12, e2)
 \<and> fwd0 (ec1, e1) \<and> fwd0 (ec2, e2)
 \<and> \<not> fwd0 (coord_of_nat 11, e1) \<and> \<not> fwd0 (coord_of_nat 12, e2)"
  by (simp add: comp0_def fwd0_def tcmp_def tfwd_def ec_defs)

lemma fos_pair: "forward_only_source fwd0 [(ec1, e1), (ec2, e2)]"
  by (simp add: forward_only_source_def fwd0_def tfwd_def ec_defs)


section \<open>THE ESCAPE BRANCH: compensate-then-redo on matched semantics\<close>

text \<open>
  The general form.  From every payload-duplicate-free crashed state of
  the pinned type whose committed source is strictly ascending and
  forward-only, the compensate-redo policy's OWN redrive heals every
  scoped store mismatch, leaves per-obligation matched-view count one
  at the redrive's own frontier, and leaves no backward residue in the
  view.  Premise disclosure, exact: @{const strictly_ascending_source}
  is consumed for distinctness of the redo block (exactly the landed B1
  site); @{const forward_only_source} is consumed to orient the replay
  (twice: the compensation block folds to @{const remove1} only over
  forward obligations, and the redo block appends only forward
  payloads); \<open>\<not> duplicate\<close> is consumed for distinctness of the ledger
  view.  The design-pinned six-premise statement follows by weakening
  below --- its \<^emph>\<open>premature\<close>-half is proof-unnecessary (the recorded
  premise audit, resolved): the matched view NORMALIZES any
  duplicate-free ledger through the accumulator lemmas above, so
  unjustified forward entries are simply cancelled or kept like any
  others, and backward ledger entries can only cancel entries preceding
  them in the ledger, never the redo block.
\<close>

theorem matched_view_escape_general:
  assumes scheme: "compensation_scheme cmp fwd"
      and ndup: "\<not> duplicate t"
      and crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and fin: "f \<le> exec_finish (dwe_core t)"
      and asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
      and fwdS: "forward_only_source fwd (exec_src_hist (dwe_core t))"
  shows "(\<exists>t'. policy_redrive (compensate_redo_policy cmp f) t f t')
       \<and> (\<forall>t'. policy_redrive (compensate_redo_policy cmp f) t f t' \<longrightarrow>
            (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k)
          \<and> (\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t'))
                         (exec_scope (dwe_core t')) f).
               count_list (comp_matched_view fwd cmp t') p = 1)
          \<and> (\<forall>q \<in> set (comp_matched_view fwd cmp t'). fwd q))"
proof (rule conjI)
  show "\<exists>t'. policy_redrive (compensate_redo_policy cmp f) t f t'"
    using policy_redriveI[OF crashed fin] by blast
next
  show "\<forall>t'. policy_redrive (compensate_redo_policy cmp f) t f t' \<longrightarrow>
          (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k)
        \<and> (\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t'))
                       (exec_scope (dwe_core t')) f).
             count_list (comp_matched_view fwd cmp t') p = 1)
        \<and> (\<forall>q \<in> set (comp_matched_view fwd cmp t'). fwd q)"
  proof (intro allI impI)
    fix t'
    assume pr: "policy_redrive (compensate_redo_policy cmp f) t f t'"
    define S where "S = exec_src_hist (dwe_core t)"
    define K where "K = exec_scope (dwe_core t)"
    define R where "R = replay_down_hist S K f"
    define L where "L = map e_payload (dwe_emitted t)"
    define W where "W = mview fwd cmp L"

    have invol: "\<And>p. cmp (cmp p) = p"
      and flip: "\<And>p. fwd (cmp p) \<longleftrightarrow> \<not> fwd p"
      using scheme by (auto simp: compensation_scheme_def)

    have batch: "compensate_redo_policy cmp f t = map cmp R @ R"
      by (simp add: compensate_redo_policy_def Let_def R_def S_def K_def)
    have em': "dwe_emitted t' = dwe_emitted t
        @ map (\<lambda>(c, e). (length S, dwe_epoch t, c, e)) (map cmp R @ R)"
      using policy_redrive_emitted[OF pr] by (simp add: S_def batch)
    have pay': "map e_payload (dwe_emitted t') = L @ map cmp R @ R"
      by (simp add: em' L_def)
    have src': "exec_src_hist (dwe_core t') = S"
      using policy_redrive_src_same[OF pr] by (simp add: S_def)
    have scope': "exec_scope (dwe_core t') = K"
      using policy_redrive_scope_same[OF pr] by (simp add: K_def)

    \<comment> \<open>ledger-view facts: distinct (from \<open>\<not> duplicate\<close>) and all-forward\<close>
    have dL: "distinct L"
      using ndup by (simp add: duplicate_def L_def)
    have dW: "distinct W"
      unfolding W_def by (rule mview_distinct[OF dL])
    have fwdW: "\<forall>q \<in> set W. fwd q"
      unfolding W_def by (rule mview_forward_elements)

    \<comment> \<open>replay facts: distinct (the ascending premise, landed B1 site)
        and forward (the forward-only source premise, both sites)\<close>
    have dR: "distinct R"
      unfolding R_def S_def K_def
      by (rule ascending_obligations_distinct[OF asc])
    have fwdR: "\<forall>p \<in> set R. fwd p"
      using replay_down_hist_subset[of S K f] fwdS
      by (auto simp: forward_only_source_def R_def S_def)
    have backR: "\<forall>p \<in> set R. \<not> fwd (cmp p)"
      using fwdR by (simp add: flip)

    \<comment> \<open>the normal form of the post-redrive matched view\<close>
    have view': "comp_matched_view fwd cmp t'
        = filter (\<lambda>x. x \<notin> set R) W @ R"
    proof -
      have "comp_matched_view fwd cmp t'
          = mview fwd cmp (L @ map cmp R @ R)"
        by (simp add: comp_matched_view_def pay')
      also have "\<dots> = foldl (mstep fwd cmp)
                        (foldl (mstep fwd cmp) W (map cmp R)) R"
        by (simp add: mview_def W_def)
      also have "\<dots> = foldl (mstep fwd cmp) (fold remove1 R W) R"
        by (simp add: mview_compensation_block[OF invol backR])
      also have "\<dots> = foldl (mstep fwd cmp)
                        (filter (\<lambda>x. x \<notin> set R) W) R"
        by (simp add: fold_remove1_distinct_filter[OF dW])
      also have "\<dots> = filter (\<lambda>x. x \<notin> set R) W @ R"
        by (rule mview_forward_block[OF fwdR])
      finally show ?thesis .
    qed

    have count1: "\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t'))
                              (exec_scope (dwe_core t')) f).
                    count_list (comp_matched_view fwd cmp t') p = 1"
    proof
      fix p
      assume "p \<in> set (replay_down_hist (exec_src_hist (dwe_core t'))
                         (exec_scope (dwe_core t')) f)"
      then have pR: "p \<in> set R"
        by (simp add: src' scope' R_def)
      have c0: "count_list (filter (\<lambda>x. x \<notin> set R) W) p = 0"
        using pR by (simp add: count_list_0_iff)
      have c1: "count_list R p = 1"
        using dR pR by (simp add: count_list_distinct_mem)
      show "count_list (comp_matched_view fwd cmp t') p = 1"
        by (simp add: view' c0 c1)
    qed

    have residue: "\<forall>q \<in> set (comp_matched_view fwd cmp t'). fwd q"
    proof -
      have "set (comp_matched_view fwd cmp t') \<subseteq> set W \<union> set R"
        by (auto simp: view')
      then show ?thesis using fwdW fwdR by blast
    qed

    show "(\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k)
        \<and> (\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t'))
                       (exec_scope (dwe_core t')) f).
             count_list (comp_matched_view fwd cmp t') p = 1)
        \<and> (\<forall>q \<in> set (comp_matched_view fwd cmp t'). fwd q)"
      using policy_redrive_heals[OF pr] count1 residue by blast
  qed
qed

text \<open>The design-pinned statement, verbatim (a weakening of the general
  form: \<open>\<not> effect_unsafe\<close> supplies \<open>\<not> duplicate\<close>; its \<open>premature\<close> half
  is deliberately unused --- the recorded premise audit, disclosed
  exactly as the landed B1 discloses its unused reachability premise).\<close>

theorem matched_view_escape:
  assumes scheme: "compensation_scheme cmp fwd"
      and safe: "\<not> effect_unsafe t"
      and crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and fin: "f \<le> exec_finish (dwe_core t)"
      and asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
      and fwdS: "forward_only_source fwd (exec_src_hist (dwe_core t))"
  shows "(\<exists>t'. policy_redrive (compensate_redo_policy cmp f) t f t')
       \<and> (\<forall>t'. policy_redrive (compensate_redo_policy cmp f) t f t' \<longrightarrow>
            (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k)
          \<and> (\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t'))
                         (exec_scope (dwe_core t')) f).
               count_list (comp_matched_view fwd cmp t') p = 1)
          \<and> (\<forall>q \<in> set (comp_matched_view fwd cmp t'). fwd q))"
proof -
  have ndup: "\<not> duplicate t"
    using safe by (simp add: effect_unsafe_def)
  show ?thesis
    by (rule matched_view_escape_general[OF scheme ndup crashed fin asc fwdS])
qed

subsection \<open>Inhabitation at the landed dilemma pair: the pair no longer
  separates\<close>

text \<open>The concrete batch at the pair (equal cores compute equal
  batches): compensate both obligations, then redo both.\<close>

lemma cr_batch_eval:
  "compensate_redo_policy comp0 ec2 d1_w
     = [(coord_of_nat 11, e1), (coord_of_nat 12, e2), (ec1, e1), (ec2, e2)]"
  by (simp add: compensate_redo_policy_def Let_def d1_w_def mkT_def mkC_def
                replay_down_hist_def comp0_def tcmp_def e1_def e2_def ec_defs)

lemma cr_same_batch:
  "compensate_redo_policy comp0 ec2 d1_w
     = compensate_redo_policy comp0 ec2 d2_w"
  by (simp add: compensate_redo_policy_def Let_def d1_w_def d2_w_def mkT_def mkC_def)

text \<open>The post-redrive matched views, computed: on the SAFE member the
  two compensations cancel the two delivered effects and the redo block
  rebuilds them; on the LOSS member the second compensation is absorbed
  as a no-op (over-compensation of the never-delivered effect) and the
  redo block delivers both.  Both members end at the same exact view.\<close>

lemma cr_d1_view:
  "comp_matched_view fwd0 comp0
     (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2)
   = [(ec1, e1), (ec2, e2)]"
  by (simp add: comp_matched_view_def mview_def mstep_def redrive_result_def
                compensate_redo_policy_def Let_def d1_w_def mkT_def mkC_def
                replay_down_hist_def comp0_def fwd0_def tcmp_def tfwd_def
                e1_def e2_def ec_defs)

lemma cr_d2_view:
  "comp_matched_view fwd0 comp0
     (redrive_result (compensate_redo_policy comp0 ec2) d2_w ec2)
   = [(ec1, e1), (ec2, e2)]"
  by (simp add: comp_matched_view_def mview_def mstep_def redrive_result_def
                compensate_redo_policy_def Let_def d2_w_def mkT_def mkC_def
                replay_down_hist_def comp0_def fwd0_def tcmp_def tfwd_def
                e1_def e2_def ec_defs)

theorem matched_view_escape_inhabited:
  "compensate_redo_policy comp0 ec2 d1_w
     = compensate_redo_policy comp0 ec2 d2_w
 \<and> count_list (comp_matched_view fwd0 comp0
     (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2))
     (ec1, e1) = 1
 \<and> count_list (comp_matched_view fwd0 comp0
     (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2))
     (ec2, e2) = 1
 \<and> count_list (comp_matched_view fwd0 comp0
     (redrive_result (compensate_redo_policy comp0 ec2) d2_w ec2))
     (ec1, e1) = 1
 \<and> count_list (comp_matched_view fwd0 comp0
     (redrive_result (compensate_redo_policy comp0 ec2) d2_w ec2))
     (ec2, e2) = 1"
proof (intro conjI)
  show "compensate_redo_policy comp0 ec2 d1_w
          = compensate_redo_policy comp0 ec2 d2_w"
    by (rule cr_same_batch)
  show "count_list (comp_matched_view fwd0 comp0
          (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2))
          (ec1, e1) = 1"
    unfolding cr_d1_view by (simp add: e1_def e2_def ec_defs)
  show "count_list (comp_matched_view fwd0 comp0
          (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2))
          (ec2, e2) = 1"
    unfolding cr_d1_view by (simp add: e1_def e2_def ec_defs)
  show "count_list (comp_matched_view fwd0 comp0
          (redrive_result (compensate_redo_policy comp0 ec2) d2_w ec2))
          (ec1, e1) = 1"
    unfolding cr_d2_view by (simp add: e1_def e2_def ec_defs)
  show "count_list (comp_matched_view fwd0 comp0
          (redrive_result (compensate_redo_policy comp0 ec2) d2_w ec2))
          (ec2, e2) = 1"
    unfolding cr_d2_view by (simp add: e1_def e2_def ec_defs)
qed


section \<open>THE PARTING CONTROL: raw and matched observables diverge at one
  state\<close>

text \<open>
  MANDATORY HONESTY CONTROL.  The escape's own redrive at the landed
  safe-side member @{const d1_w} is PREMATURE (its compensation entries'
  payloads are not committed source events --- unjustified in the landed
  taxonomy by design) and DUPLICATE (both obligations re-fired over a
  ledger that already carried them) --- so @{const effect_unsafe} fires
  and @{const exactly_once_at} fails --- AT THE SAME STATE where the
  matched view is exact at both obligations.  The two observables
  provably part ways at one reachable-rooted redrive result: the landed
  T2.10 / T2.11 / Dichotomy statements are about the RAW observable of
  irreversible sinks and remain exactly as scoped; nothing here weakens
  them, and no reader can take the escape as contradicting them.
\<close>

lemma cr_d1_result_emitted:
  "dwe_emitted (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2)
     = [(1, 0, ec1, e1), (2, 0, ec2, e2),
        (2, 1, coord_of_nat 11, e1), (2, 1, coord_of_nat 12, e2),
        (2, 1, ec1, e1), (2, 1, ec2, e2)]"
  unfolding redrive_result_def cr_batch_eval
  by (simp add: d1_w_def mkT_def mkC_def eval_nat_numeral)

lemma cr_d1_result_src:
  "exec_src_hist (dwe_core
      (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2))
     = [(ec1, e1), (ec2, e2)]"
  by (simp add: redrive_result_def d1_w_def mkT_def mkC_def)

lemma cr_d1_result_premature:
  "premature (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2)"
  unfolding premature_def cr_d1_result_emitted cr_d1_result_src
  by (simp add: justified_at_def e1_def e2_def ec_defs eval_nat_numeral)

lemma cr_d1_result_duplicate:
  "duplicate (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2)"
  unfolding duplicate_def cr_d1_result_emitted
  by (simp add: e1_def e2_def ec_defs)

theorem matched_escape_raw_hazard_control:
  "premature (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2)
 \<and> duplicate (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2)
 \<and> effect_unsafe (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2)
 \<and> \<not> exactly_once_at ec2
     (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2)
 \<and> count_list (comp_matched_view fwd0 comp0
     (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2))
     (ec1, e1) = 1
 \<and> count_list (comp_matched_view fwd0 comp0
     (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2))
     (ec2, e2) = 1"
proof (intro conjI)
  show "premature (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2)"
    by (rule cr_d1_result_premature)
  show "duplicate (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2)"
    by (rule cr_d1_result_duplicate)
  show "effect_unsafe (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2)"
    using cr_d1_result_duplicate by (simp add: effect_unsafe_def)
  show "\<not> exactly_once_at ec2
          (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2)"
    using cr_d1_result_duplicate
    by (simp add: exactly_once_at_def effect_unsafe_def)
  show "count_list (comp_matched_view fwd0 comp0
          (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2))
          (ec1, e1) = 1"
    unfolding cr_d1_view by (simp add: e1_def e2_def ec_defs)
  show "count_list (comp_matched_view fwd0 comp0
          (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2))
          (ec2, e2) = 1"
    unfolding cr_d1_view by (simp add: e1_def e2_def ec_defs)
qed

text \<open>The companion direction: the bulk redo WITHOUT the compensation
  block (the landed drop-0 cursor policy) leaves matched-view count 2
  at the already-delivered obligation on the safe member ---
  compensate-first is load-bearing on matched sinks.\<close>

theorem bulk_redo_needs_compensation_control:
  "count_list (comp_matched_view fwd0 comp0
      (redrive_result
         (\<lambda>s. drop 0 (replay_down_hist (exec_src_hist (dwe_core s))
                        (exec_scope (dwe_core s)) ec2))
         d1_w ec2)) (ec1, e1) = 2"
  by (simp add: comp_matched_view_def mview_def mstep_def redrive_result_def
                d1_w_def mkT_def mkC_def replay_down_hist_def fwd0_def
                tfwd_def e1_def e2_def ec_defs)


section \<open>Load-bearing controls: both escape premises bite\<close>

text \<open>
  CONTROL (ascending premise; the landed aliasing axis).  At the landed
  section-18 equal-coordinate posture --- re-declared locally as
  @{text cpsl_w} below because that theory is not in this import cone;
  the landed constant is @{text psl_w} --- one business payload is
  committed twice (WF-H1-legal: the locked core's wellformedness is
  non-strict), the source is forward-only, but NOT strictly ascending.
  The compensate-redo ledger footprint (stamped exactly as the landed
  redrive rule stamps) leaves matched-view count 2 at the duplicated
  obligation: both compensations fire against an empty ledger and are
  absorbed, then BOTH redo copies land.  The escape consumes the
  ascending premise exactly as the landed B1 does --- same premise
  philosophy, same control genre.  The state is a state of the type,
  not claimed reachable, matching the theorem's own premise set.
\<close>

definition cpsl_w :: "(nat, nat) dwe_state" where
  "cpsl_w = mkT (mkC [(ec1, e1), (ec1, e1)] [] [] {} Running) [] 0"

lemma cpsl_wf: "wellformed_src_history (exec_src_hist (dwe_core cpsl_w))"
proof -
  have "exec_src_hist (dwe_core cpsl_w) = [(ec1, e1), (ec1, e1)]"
    by (simp add: cpsl_w_def mkT_def mkC_def)
  moreover have "wellformed_src_history [(ec1, e1), (ec1, e1)]"
    by (rule wf_hist_pair) (simp_all add: ec_defs)
  ultimately show ?thesis by simp
qed

lemma cpsl_not_asc:
  "\<not> strictly_ascending_source (exec_src_hist (dwe_core cpsl_w))"
  by (simp add: strictly_ascending_source_def cpsl_w_def mkT_def mkC_def
                ec_defs)

lemma cpsl_forward_only:
  "forward_only_source fwd0 (exec_src_hist (dwe_core cpsl_w))"
  by (simp add: forward_only_source_def fwd0_def tfwd_def cpsl_w_def
                mkT_def mkC_def ec_defs)

lemma cpsl_obligation:
  "(ec1, e1) \<in> set (replay_down_hist (exec_src_hist (dwe_core cpsl_w))
                      (exec_scope (dwe_core cpsl_w)) ec1)"
  by (simp add: cpsl_w_def mkT_def mkC_def replay_down_hist_def e1_def
                ec_defs)

lemma cpsl_view_eval:
  "comp_matched_view fwd0 comp0
     (cpsl_w\<lparr>dwe_emitted := dwe_emitted cpsl_w
        @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core cpsl_w)),
                         dwe_epoch cpsl_w, c, e))
            (compensate_redo_policy comp0 ec1 cpsl_w)\<rparr>)
   = [(ec1, e1), (ec1, e1)]"
  by (simp add: comp_matched_view_def mview_def mstep_def cpsl_w_def
                mkT_def mkC_def compensate_redo_policy_def Let_def
                replay_down_hist_def comp0_def fwd0_def tcmp_def tfwd_def
                e1_def ec_defs)

theorem matched_escape_asc_load_bearing:
  "\<exists>(t :: (nat, nat) dwe_state) f p.
     wellformed_src_history (exec_src_hist (dwe_core t))
   \<and> forward_only_source fwd0 (exec_src_hist (dwe_core t))
   \<and> \<not> strictly_ascending_source (exec_src_hist (dwe_core t))
   \<and> p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                (exec_scope (dwe_core t)) f)
   \<and> count_list (comp_matched_view fwd0 comp0
        (t\<lparr>dwe_emitted := dwe_emitted t
             @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                              dwe_epoch t, c, e))
                 (compensate_redo_policy comp0 f t)\<rparr>)) p \<noteq> 1"
proof -
  have ne: "count_list (comp_matched_view fwd0 comp0
        (cpsl_w\<lparr>dwe_emitted := dwe_emitted cpsl_w
             @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core cpsl_w)),
                              dwe_epoch cpsl_w, c, e))
                 (compensate_redo_policy comp0 ec1 cpsl_w)\<rparr>)) (ec1, e1) \<noteq> 1"
    unfolding cpsl_view_eval by (simp add: e1_def ec_defs)
  show ?thesis
    using cpsl_wf cpsl_forward_only cpsl_not_asc cpsl_obligation ne by blast
qed

text \<open>
  CONTROL (forward-only premise; the recorded premise audit's witness).
  The audit asked whether @{const forward_only_source} could be dropped
  alongside the \<open>premature\<close> half: it cannot --- it orients the REPLAY,
  not the ledger.  At a state whose committed source contains a
  BACKWARD payload (strictly ascending, so the ascending premise cannot
  rescue), the redo block's copy of that obligation acts as a
  canceller instead of an append: the compensate-redo footprint leaves
  matched-view count 0, not 1, at the backward obligation.
\<close>

definition cbk_w :: "(nat, nat) dwe_state" where
  "cbk_w = mkT (mkC [(coord_of_nat 11, e1)] [] [] {} Running) [] 0"

lemma cbk_wf: "wellformed_src_history (exec_src_hist (dwe_core cbk_w))"
proof -
  have "exec_src_hist (dwe_core cbk_w) = [(coord_of_nat 11, e1)]"
    by (simp add: cbk_w_def mkT_def mkC_def)
  moreover have "wellformed_src_history [(coord_of_nat 11, e1)]"
    by (rule wf_hist_single) simp
  ultimately show ?thesis by simp
qed

lemma cbk_asc:
  "strictly_ascending_source (exec_src_hist (dwe_core cbk_w))"
  by (simp add: strictly_ascending_source_def cbk_w_def mkT_def mkC_def)

lemma cbk_not_forward_only:
  "\<not> forward_only_source fwd0 (exec_src_hist (dwe_core cbk_w))"
  by (simp add: forward_only_source_def fwd0_def tfwd_def cbk_w_def
                mkT_def mkC_def)

lemma cbk_obligation:
  "(coord_of_nat 11, e1) \<in> set (replay_down_hist
      (exec_src_hist (dwe_core cbk_w)) (exec_scope (dwe_core cbk_w))
      (coord_of_nat 11))"
  by (simp add: cbk_w_def mkT_def mkC_def replay_down_hist_def e1_def)

lemma cbk_view_eval:
  "comp_matched_view fwd0 comp0
     (cbk_w\<lparr>dwe_emitted := dwe_emitted cbk_w
        @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core cbk_w)),
                         dwe_epoch cbk_w, c, e))
            (compensate_redo_policy comp0 (coord_of_nat 11) cbk_w)\<rparr>)
   = []"
  by (simp add: comp_matched_view_def mview_def mstep_def cbk_w_def
                mkT_def mkC_def compensate_redo_policy_def Let_def
                replay_down_hist_def comp0_def fwd0_def tcmp_def tfwd_def
                e1_def)

theorem matched_escape_forward_premise_load_bearing:
  "\<exists>(t :: (nat, nat) dwe_state) f p.
     wellformed_src_history (exec_src_hist (dwe_core t))
   \<and> strictly_ascending_source (exec_src_hist (dwe_core t))
   \<and> \<not> forward_only_source fwd0 (exec_src_hist (dwe_core t))
   \<and> p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                (exec_scope (dwe_core t)) f)
   \<and> count_list (comp_matched_view fwd0 comp0
        (t\<lparr>dwe_emitted := dwe_emitted t
             @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                              dwe_epoch t, c, e))
                 (compensate_redo_policy comp0 f t)\<rparr>)) p \<noteq> 1"
proof -
  have ne: "count_list (comp_matched_view fwd0 comp0
        (cbk_w\<lparr>dwe_emitted := dwe_emitted cbk_w
             @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core cbk_w)),
                              dwe_epoch cbk_w, c, e))
                 (compensate_redo_policy comp0 (coord_of_nat 11) cbk_w)\<rparr>))
        (coord_of_nat 11, e1) \<noteq> 1"
    unfolding cbk_view_eval by simp
  show ?thesis
    using cbk_wf cbk_asc cbk_not_forward_only cbk_obligation ne by blast
qed


section \<open>THE NO-ESCAPE BRANCH: signed cancellation (probe S-layer, ported)\<close>

text \<open>The net count is additive under append (probe S1) --- the entire
  signed branch is this one equation.\<close>

lemma net_count_append:
  "net_count cmp (xs @ ys) p = net_count cmp xs p + net_count cmp ys p"
  by (simp add: net_count_def)

text \<open>THE SIGNED KERNEL (probe S2): a shared appended batch shifts both
  members' net counts by the same amount, so a gap of one survives
  EVERY batch --- they cannot both end at net one.  One line, no
  ordering premise, no state: pure counting.\<close>

theorem net_agreement_kernel:
  assumes "net_count cmp L1 q = net_count cmp L2 q + 1"
  shows "\<not> (net_count cmp (L1 @ B) q = 1 \<and> net_count cmp (L2 @ B) q = 1)"
  using assms by (simp add: net_count_append)

text \<open>The gap premise is inhabited whenever one ledger carries the
  obligation once, the other not at all, and neither carries the
  backward payload (probe S3).\<close>

lemma pair_net_gap:
  assumes "count_list L1 q = 1" and "count_list L2 q = 0"
      and "cmp q \<notin> set L1" and "cmp q \<notin> set L2"
  shows "net_count cmp L1 q = net_count cmp L2 q + 1"
  using assms by (simp add: net_count_def count_list_0_iff)

text \<open>
  THE SIGNED DILEMMA: the landed designed pair, re-read at the signed
  observable --- exists-system polarity, the same certificate conjuncts,
  the same healing conjuncts (the store still heals; healing still
  cannot arbitrate), with the horn now: not both members reach
  per-obligation net count one at the frontier.  Presented in the
  T2.11 manner: a READING of the landed batch-agreement argument at a
  new observable, never a new impossibility class.  The three-case
  analysis of the landed kernel collapses to one inequality; NO
  ordering premise is consumed (the landed impossibility polarity,
  preserved).  Compensate-then-redo is covered like every other policy
  --- and computed failing below.
\<close>

theorem signed_view_batch_agreement_dilemma:
  "\<exists>t1 t2.
     dwe_reachable t1 \<and> dwe_reachable t2
   \<and> dwe_core t1 = dwe_core t2 \<and> dwe_epoch t1 = dwe_epoch t2
   \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
   \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
   \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
   \<and> (\<forall>P. P t1 = P t2 \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> \<not> (net_view_exact_at comp0 ec2 t1'
            \<and> net_view_exact_at comp0 ec2 t2')))"
proof -
  have inner: "\<forall>P. P d1_w = P d2_w \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> \<not> (net_view_exact_at comp0 ec2 t1'
            \<and> net_view_exact_at comp0 ec2 t2'))"
  proof (intro allI impI)
    fix P :: redrive_policy
    assume PB: "P d1_w = P d2_w"
    have grd1: "\<exists>c. exec_status (dwe_core d1_w) = Crashed c"
      by (simp add: d1_fields)
    have grd2: "\<exists>c. exec_status (dwe_core d2_w) = Crashed c"
      by (simp add: d2_fields)
    have fin1: "ec2 \<le> exec_finish (dwe_core d1_w)"
      by (simp add: d1_fields)
    have fin2: "ec2 \<le> exec_finish (dwe_core d2_w)"
      by (simp add: d2_fields)
    define t1' where "t1' = redrive_result P d1_w ec2"
    define t2' where "t2' = redrive_result P d2_w ec2"
    have pr1: "policy_redrive P d1_w ec2 t1'"
      unfolding t1'_def by (rule policy_redriveI[OF grd1 fin1])
    have pr2: "policy_redrive P d2_w ec2 t2'"
      unfolding t2'_def by (rule policy_redriveI[OF grd2 fin2])

    have em1: "dwe_emitted t1'
        = [(1, 0, ec1, e1), (2, 0, ec2, e2)]
          @ map (\<lambda>(c, e). (2, 1, c, e)) (P d1_w)"
      unfolding t1'_def redrive_result_def
      by (simp add: d1_w_def mkT_def mkC_def eval_nat_numeral)
    have em2: "dwe_emitted t2'
        = [(1, 0, ec1, e1)] @ map (\<lambda>(c, e). (2, 1, c, e)) (P d2_w)"
      unfolding t2'_def redrive_result_def
      by (simp add: d2_w_def mkT_def mkC_def eval_nat_numeral)
    have pay1: "map e_payload (dwe_emitted t1')
        = [(ec1, e1), (ec2, e2)] @ P d1_w"
      by (simp add: em1)
    have pay2: "map e_payload (dwe_emitted t2')
        = [(ec1, e1)] @ P d1_w"
      by (simp add: em2 PB[symmetric])

    have gap: "net_count comp0 [(ec1, e1), (ec2, e2)] (ec2, e2)
        = net_count comp0 [(ec1, e1)] (ec2, e2) + 1"
      by (simp add: net_count_def comp0_def tcmp_def e1_def e2_def ec_defs)
    have nboth: "\<not> (net_count comp0 (map e_payload (dwe_emitted t1'))
                      (ec2, e2) = 1
                  \<and> net_count comp0 (map e_payload (dwe_emitted t2'))
                      (ec2, e2) = 1)"
      using net_agreement_kernel[OF gap, of "P d1_w"]
      by (simp add: pay1 pay2)

    have mem1: "(ec2, e2) \<in> set (replay_down_hist
        (exec_src_hist (dwe_core t1')) (exec_scope (dwe_core t1')) ec2)"
      unfolding t1'_def redrive_result_def
      by (simp add: d1_w_def mkT_def mkC_def replay_down_hist_def
                    e1_def e2_def ec_defs eval_nat_numeral)
    have mem2: "(ec2, e2) \<in> set (replay_down_hist
        (exec_src_hist (dwe_core t2')) (exec_scope (dwe_core t2')) ec2)"
      unfolding t2'_def redrive_result_def
      by (simp add: d2_w_def mkT_def mkC_def replay_down_hist_def
                    e1_def e2_def ec_defs eval_nat_numeral)
    have nexact: "\<not> (net_view_exact_at comp0 ec2 t1'
                   \<and> net_view_exact_at comp0 ec2 t2')"
      using nboth mem1 mem2 by (auto simp: net_view_exact_at_def)

    have heal1: "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k"
      by (rule policy_redrive_heals[OF pr1])
    have heal2: "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k"
      by (rule policy_redrive_heals[OF pr2])

    show "\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> \<not> (net_view_exact_at comp0 ec2 t1'
            \<and> net_view_exact_at comp0 ec2 t2')"
      using pr1 pr2 heal1 heal2 nexact by blast
  qed
  have epochs: "dwe_epoch d1_w = dwe_epoch d2_w"
    by (simp add: d1_fields d2_fields)
  have all:
    "dwe_reachable d1_w \<and> dwe_reachable d2_w
   \<and> dwe_core d1_w = dwe_core d2_w \<and> dwe_epoch d1_w = dwe_epoch d2_w
   \<and> dwe_emitted d1_w \<noteq> dwe_emitted d2_w
   \<and> \<not> effect_unsafe d1_w \<and> \<not> effect_unsafe d2_w
   \<and> genuinely_emitting d1_w \<and> genuinely_emitting d2_w
   \<and> (\<forall>P. P d1_w = P d2_w \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> \<not> (net_view_exact_at comp0 ec2 t1'
            \<and> net_view_exact_at comp0 ec2 t2')))"
    using reach_d1 reach_d2 d_cores_eq epochs d_emitted_neq d1_not_unsafe
          d2_not_unsafe d1_emitting d2_emitting inner
    by blast
  then show ?thesis by blast
qed

text \<open>The store-measured and (core, epoch)-measured faces --- the landed
  quantifier plumbing, unchanged: the classes enter only through "its
  policies cannot distinguish the pair".\<close>

corollary signed_view_recovery_dilemma:
  "\<forall>P. store_measured P \<longrightarrow>
     (\<exists>t1 t2 t1' t2'.
        dwe_reachable t1 \<and> dwe_reachable t2
      \<and> dwe_core t1 = dwe_core t2
      \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
      \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
      \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
      \<and> policy_redrive P t1 ec2 t1'
      \<and> policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
      \<and> \<not> (net_view_exact_at comp0 ec2 t1'
         \<and> net_view_exact_at comp0 ec2 t2'))"
proof (intro allI impI)
  fix P :: redrive_policy
  assume sm: "store_measured P"
  obtain t1 t2 where
    base: "dwe_reachable t1" "dwe_reachable t2"
          "dwe_core t1 = dwe_core t2" "dwe_epoch t1 = dwe_epoch t2"
          "dwe_emitted t1 \<noteq> dwe_emitted t2"
          "\<not> effect_unsafe t1" "\<not> effect_unsafe t2"
          "genuinely_emitting t1" "genuinely_emitting t2"
    and agree: "\<forall>P. P t1 = P t2 \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> \<not> (net_view_exact_at comp0 ec2 t1'
            \<and> net_view_exact_at comp0 ec2 t2'))"
    using signed_view_batch_agreement_dilemma by blast
  from sm obtain g where g: "\<forall>t. P t = g (dwe_core t)"
    unfolding store_measured_def by blast
  have "P t1 = P t2"
    using g base(3) by metis
  then obtain t1' t2' where
    prim: "policy_redrive P t1 ec2 t1'" "policy_redrive P t2 ec2 t2'"
          "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k"
          "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k"
          "\<not> (net_view_exact_at comp0 ec2 t1'
            \<and> net_view_exact_at comp0 ec2 t2')"
    using agree by blast
  show "\<exists>t1 t2 t1' t2'.
        dwe_reachable t1 \<and> dwe_reachable t2
      \<and> dwe_core t1 = dwe_core t2
      \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
      \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
      \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
      \<and> policy_redrive P t1 ec2 t1'
      \<and> policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
      \<and> \<not> (net_view_exact_at comp0 ec2 t1'
         \<and> net_view_exact_at comp0 ec2 t2')"
    using base(1,2,3,5,6,7,8,9) prim by blast
qed

corollary signed_view_epoch_measured_dilemma:
  "\<forall>P. store_epoch_measured P \<longrightarrow>
     (\<exists>t1 t2 t1' t2'.
        dwe_reachable t1 \<and> dwe_reachable t2
      \<and> dwe_core t1 = dwe_core t2
      \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
      \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
      \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
      \<and> policy_redrive P t1 ec2 t1'
      \<and> policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
      \<and> \<not> (net_view_exact_at comp0 ec2 t1'
         \<and> net_view_exact_at comp0 ec2 t2'))"
proof (intro allI impI)
  fix P :: redrive_policy
  assume sem: "store_epoch_measured P"
  obtain t1 t2 where
    base: "dwe_reachable t1" "dwe_reachable t2"
          "dwe_core t1 = dwe_core t2" "dwe_epoch t1 = dwe_epoch t2"
          "dwe_emitted t1 \<noteq> dwe_emitted t2"
          "\<not> effect_unsafe t1" "\<not> effect_unsafe t2"
          "genuinely_emitting t1" "genuinely_emitting t2"
    and agree: "\<forall>P. P t1 = P t2 \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> \<not> (net_view_exact_at comp0 ec2 t1'
            \<and> net_view_exact_at comp0 ec2 t2'))"
    using signed_view_batch_agreement_dilemma by blast
  from sem obtain g where g: "\<forall>t. P t = g (dwe_core t) (dwe_epoch t)"
    unfolding store_epoch_measured_def by blast
  have "P t1 = P t2"
    using g base(3) base(4) by metis
  then obtain t1' t2' where
    prim: "policy_redrive P t1 ec2 t1'" "policy_redrive P t2 ec2 t2'"
          "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k"
          "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k"
          "\<not> (net_view_exact_at comp0 ec2 t1'
            \<and> net_view_exact_at comp0 ec2 t2')"
    using agree by blast
  show "\<exists>t1 t2 t1' t2'.
        dwe_reachable t1 \<and> dwe_reachable t2
      \<and> dwe_core t1 = dwe_core t2
      \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
      \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
      \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
      \<and> policy_redrive P t1 ec2 t1'
      \<and> policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
      \<and> \<not> (net_view_exact_at comp0 ec2 t1'
         \<and> net_view_exact_at comp0 ec2 t2')"
    using base(1,2,3,5,6,7,8,9) prim by blast
qed

text \<open>The escape policy itself, computed at the signed view: it is
  store-measured, so it must fall to the signed dilemma --- and does,
  concretely: the LOSS member's unmatched compensation permanently
  shifts the net to 0 while the safe member ends at 1.  Blind bulk
  compensation corrupts the loss-side member of a signed sink.\<close>

lemma signed_compensate_redo_loss_zero:
  "net_count comp0 (map e_payload (dwe_emitted
      (redrive_result (compensate_redo_policy comp0 ec2) d2_w ec2)))
      (ec2, e2) = 0"
  by (simp add: net_count_def redrive_result_def compensate_redo_policy_def Let_def
                d2_w_def mkT_def mkC_def replay_down_hist_def comp0_def
                tcmp_def e1_def e2_def ec_defs)

lemma signed_compensate_redo_safe_one:
  "net_count comp0 (map e_payload (dwe_emitted
      (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2)))
      (ec2, e2) = 1"
  by (simp add: net_count_def redrive_result_def compensate_redo_policy_def Let_def
                d1_w_def mkT_def mkC_def replay_down_hist_def comp0_def
                tcmp_def e1_def e2_def ec_defs)


section \<open>The truncated control: floor-at-zero counters do not escape\<close>

text \<open>
  THE MIDDLE-POSITION KILLER.  A tempting reading of the escape is
  "order-aware matching is overkill; a floor-at-zero counter (nat
  monus) already absorbs over-compensation at the aggregate".  FALSE,
  and this is the control that shows it: the designed pair's truncated
  gap also survives every shared batch (the whole arithmetic: a
  truncated count of one forces the plain count one above the backward
  count, so one extra forward occurrence lands at two, not one),
  so the pair still defeats every policy that cannot distinguish its
  members --- and the compensate-redo batch itself lands the LOSS
  member at truncated view 0, not 1 (the unmatched compensation EATS
  the subsequent redo at the aggregate).  Order-aware matching --- a
  per-entry stateful lookup in the sink --- is the load-bearing
  ingredient of the escape, not absorption at the aggregate.  No
  ordering premise; exists-system polarity; hand-checked monus
  arithmetic (the one row not probe-checked, disclosed in the slice
  record).
\<close>

theorem truncated_view_no_escape_control:
  "\<exists>t1 t2.
     dwe_reachable t1 \<and> dwe_reachable t2
   \<and> dwe_core t1 = dwe_core t2 \<and> dwe_epoch t1 = dwe_epoch t2
   \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
   \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
   \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
   \<and> (\<forall>P. P t1 = P t2 \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> \<not> (trunc_count comp0 (map e_payload (dwe_emitted t1'))
                (ec2, e2) = 1
            \<and> trunc_count comp0 (map e_payload (dwe_emitted t2'))
                (ec2, e2) = 1)))"
proof -
  have inner: "\<forall>P. P d1_w = P d2_w \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> \<not> (trunc_count comp0 (map e_payload (dwe_emitted t1'))
                (ec2, e2) = 1
            \<and> trunc_count comp0 (map e_payload (dwe_emitted t2'))
                (ec2, e2) = 1))"
  proof (intro allI impI)
    fix P :: redrive_policy
    assume PB: "P d1_w = P d2_w"
    have grd1: "\<exists>c. exec_status (dwe_core d1_w) = Crashed c"
      by (simp add: d1_fields)
    have grd2: "\<exists>c. exec_status (dwe_core d2_w) = Crashed c"
      by (simp add: d2_fields)
    have fin1: "ec2 \<le> exec_finish (dwe_core d1_w)"
      by (simp add: d1_fields)
    have fin2: "ec2 \<le> exec_finish (dwe_core d2_w)"
      by (simp add: d2_fields)
    define t1' where "t1' = redrive_result P d1_w ec2"
    define t2' where "t2' = redrive_result P d2_w ec2"
    have pr1: "policy_redrive P d1_w ec2 t1'"
      unfolding t1'_def by (rule policy_redriveI[OF grd1 fin1])
    have pr2: "policy_redrive P d2_w ec2 t2'"
      unfolding t2'_def by (rule policy_redriveI[OF grd2 fin2])

    have em1: "dwe_emitted t1'
        = [(1, 0, ec1, e1), (2, 0, ec2, e2)]
          @ map (\<lambda>(c, e). (2, 1, c, e)) (P d1_w)"
      unfolding t1'_def redrive_result_def
      by (simp add: d1_w_def mkT_def mkC_def eval_nat_numeral)
    have em2: "dwe_emitted t2'
        = [(1, 0, ec1, e1)] @ map (\<lambda>(c, e). (2, 1, c, e)) (P d2_w)"
      unfolding t2'_def redrive_result_def
      by (simp add: d2_w_def mkT_def mkC_def eval_nat_numeral)
    have pay1: "map e_payload (dwe_emitted t1')
        = [(ec1, e1), (ec2, e2)] @ P d1_w"
      by (simp add: em1)
    have pay2: "map e_payload (dwe_emitted t2')
        = [(ec1, e1)] @ P d1_w"
      by (simp add: em2 PB[symmetric])

    have t1eq: "trunc_count comp0 (map e_payload (dwe_emitted t1'))
                  (ec2, e2)
        = 1 + count_list (P d1_w) (ec2, e2)
          - count_list (P d1_w) (comp0 (ec2, e2))"
      by (simp add: trunc_count_def pay1 comp0_def tcmp_def
                    e1_def e2_def ec_defs)
    have t2eq: "trunc_count comp0 (map e_payload (dwe_emitted t2'))
                  (ec2, e2)
        = count_list (P d1_w) (ec2, e2)
          - count_list (P d1_w) (comp0 (ec2, e2))"
      by (simp add: trunc_count_def pay2 comp0_def tcmp_def
                    e1_def e2_def ec_defs)
    have nboth: "\<not> (trunc_count comp0 (map e_payload (dwe_emitted t1'))
                      (ec2, e2) = 1
                  \<and> trunc_count comp0 (map e_payload (dwe_emitted t2'))
                      (ec2, e2) = 1)"
    proof
      assume both:
        "trunc_count comp0 (map e_payload (dwe_emitted t1')) (ec2, e2) = 1
       \<and> trunc_count comp0 (map e_payload (dwe_emitted t2')) (ec2, e2) = 1"
      have e1': "1 + count_list (P d1_w) (ec2, e2)
                   - count_list (P d1_w) (comp0 (ec2, e2)) = 1"
        using both by (simp add: t1eq)
      have e2': "count_list (P d1_w) (ec2, e2)
                   - count_list (P d1_w) (comp0 (ec2, e2)) = 1"
        using both by (simp add: t2eq)
      show False using e1' e2' by arith
    qed

    have heal1: "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k"
      by (rule policy_redrive_heals[OF pr1])
    have heal2: "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k"
      by (rule policy_redrive_heals[OF pr2])

    show "\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> \<not> (trunc_count comp0 (map e_payload (dwe_emitted t1'))
                (ec2, e2) = 1
            \<and> trunc_count comp0 (map e_payload (dwe_emitted t2'))
                (ec2, e2) = 1)"
      using pr1 pr2 heal1 heal2 nboth by blast
  qed
  have epochs: "dwe_epoch d1_w = dwe_epoch d2_w"
    by (simp add: d1_fields d2_fields)
  have all:
    "dwe_reachable d1_w \<and> dwe_reachable d2_w
   \<and> dwe_core d1_w = dwe_core d2_w \<and> dwe_epoch d1_w = dwe_epoch d2_w
   \<and> dwe_emitted d1_w \<noteq> dwe_emitted d2_w
   \<and> \<not> effect_unsafe d1_w \<and> \<not> effect_unsafe d2_w
   \<and> genuinely_emitting d1_w \<and> genuinely_emitting d2_w
   \<and> (\<forall>P. P d1_w = P d2_w \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> \<not> (trunc_count comp0 (map e_payload (dwe_emitted t1'))
                (ec2, e2) = 1
            \<and> trunc_count comp0 (map e_payload (dwe_emitted t2'))
                (ec2, e2) = 1)))"
    using reach_d1 reach_d2 d_cores_eq epochs d_emitted_neq d1_not_unsafe
          d2_not_unsafe d1_emitting d2_emitting inner
    by blast
  then show ?thesis by blast
qed

text \<open>The computed bite: the escape batch itself, read at the truncated
  aggregate, starves the loss member (view 0 --- the unmatched
  compensation eats the redo) while the safe member reads 1.\<close>

lemma trunc_compensate_redo_loss_zero:
  "trunc_count comp0 (map e_payload (dwe_emitted
      (redrive_result (compensate_redo_policy comp0 ec2) d2_w ec2)))
      (ec2, e2) = 0"
  by (simp add: trunc_count_def redrive_result_def compensate_redo_policy_def Let_def
                d2_w_def mkT_def mkC_def replay_down_hist_def comp0_def
                tcmp_def e1_def e2_def ec_defs)

lemma trunc_compensate_redo_safe_one:
  "trunc_count comp0 (map e_payload (dwe_emitted
      (redrive_result (compensate_redo_policy comp0 ec2) d1_w ec2)))
      (ec2, e2) = 1"
  by (simp add: trunc_count_def redrive_result_def compensate_redo_policy_def Let_def
                d1_w_def mkT_def mkC_def replay_down_hist_def comp0_def
                tcmp_def e1_def e2_def ec_defs)


section \<open>The completer: the idempotent cell's escape, named (T2.11 tie)\<close>

text \<open>
  RESTATEMENT-GRADE, disclosed as such: the landed T2.11 layer-1 iff
  plus the post-redrive ledger image, made a named theorem so the
  effect-class table's idempotent cell is a citation instead of a
  two-step folklore inference.  The drop-0 bulk policy --- literally the
  m = 0 instance of the landed @{thm [source] cursor_policy_store_measured}
  --- heals and leaves per-obligation dedup-view count one at its own
  frontier, from EVERY crashed state of the pinned type (no safety, no
  ordering premise: the dedup view absorbs repeats by construction).
  The count-one form mirrors T2.11's layer-1 left-hand side and carries
  its disclosed liveness stand-in status through the same bridge;
  nothing here strengthens or re-scopes T2.11.
\<close>

theorem dedup_view_bulk_redrive_escape:
  assumes crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and fin: "f \<le> exec_finish (dwe_core t)"
  shows "store_measured
           (\<lambda>s. drop 0 (replay_down_hist (exec_src_hist (dwe_core s))
                          (exec_scope (dwe_core s)) f))
       \<and> (\<exists>t'. policy_redrive
                 (\<lambda>s. drop 0 (replay_down_hist (exec_src_hist (dwe_core s))
                                (exec_scope (dwe_core s)) f)) t f t')
       \<and> (\<forall>t'. policy_redrive
                 (\<lambda>s. drop 0 (replay_down_hist (exec_src_hist (dwe_core s))
                                (exec_scope (dwe_core s)) f)) t f t' \<longrightarrow>
            (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k)
          \<and> (\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t'))
                         (exec_scope (dwe_core t')) f).
               count_list (sink_dedup_view t') p = 1))"
proof (intro conjI)
  show "store_measured
          (\<lambda>s. drop 0 (replay_down_hist (exec_src_hist (dwe_core s))
                         (exec_scope (dwe_core s)) f))"
    by (rule cursor_policy_store_measured)
next
  show "\<exists>t'. policy_redrive
               (\<lambda>s. drop 0 (replay_down_hist (exec_src_hist (dwe_core s))
                              (exec_scope (dwe_core s)) f)) t f t'"
    using policy_redriveI[OF crashed fin] by blast
next
  show "\<forall>t'. policy_redrive
               (\<lambda>s. drop 0 (replay_down_hist (exec_src_hist (dwe_core s))
                              (exec_scope (dwe_core s)) f)) t f t' \<longrightarrow>
          (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k)
        \<and> (\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t'))
                       (exec_scope (dwe_core t')) f).
             count_list (sink_dedup_view t') p = 1)"
  proof (intro allI impI)
    fix t'
    assume pr: "policy_redrive
                  (\<lambda>s. drop 0 (replay_down_hist (exec_src_hist (dwe_core s))
                                 (exec_scope (dwe_core s)) f)) t f t'"
    define R where "R = replay_down_hist (exec_src_hist (dwe_core t))
                          (exec_scope (dwe_core t)) f"
    have em': "dwe_emitted t' = dwe_emitted t
        @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                         dwe_epoch t, c, e)) R"
      using policy_redrive_emitted[OF pr] by (simp add: R_def)
    have img': "e_payload ` set (dwe_emitted t')
        = e_payload ` set (dwe_emitted t) \<union> set R"
      by (simp add: em' image_Un image_image)
    have src': "exec_src_hist (dwe_core t') = exec_src_hist (dwe_core t)"
      by (rule policy_redrive_src_same[OF pr])
    have scope': "exec_scope (dwe_core t') = exec_scope (dwe_core t)"
      by (rule policy_redrive_scope_same[OF pr])
    have alo: "at_least_once_at f t'"
      unfolding at_least_once_at_def
      by (simp add: src' scope' img' R_def[symmetric])
    have cnt: "\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t'))
                           (exec_scope (dwe_core t')) f).
                 count_list (sink_dedup_view t') p = 1"
      by (rule dedup_sink_exactly_once_iff_at_least_once[THEN iffD2, OF alo])
    show "(\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k)
        \<and> (\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t'))
                       (exec_scope (dwe_core t')) f).
             count_list (sink_dedup_view t') p = 1)"
      using policy_redrive_heals[OF pr] cnt by blast
  qed
qed


end
