(*  Title:       Dual_Write_Effect_Retention_Control.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE PRESENCE-DESTROYING RETENTION CONTROL (roadmap Wave 2, slice W2a)
    --- the missing biting witness for the landed presence bound's
    retention proviso, an additive post-freeze slice under the freeze's
    own protocol: no landed statement, proof, definition, name, import,
    or session-DAG change to the frozen corpus.

    The landed Dual_Write_Effect_Presence_Bound pins the sink-reading
    escape from above: sink_delta reads the emission ledger only through
    the presence set of delivered payloads, and is invariant under every
    presence-PRESERVING ledger rewrite (reorder, duplicate collapse,
    stamp/epoch loss, keep-latest compaction).  Its retention reading ---
    only the recovery window's presence bits matter, so retention may
    forget everything OUTSIDE the window --- carries a proviso: delivered-
    payload presence WITHIN the recovery window must survive.  The
    2026-07-07 gap-hunt (the sink-retention lens redo + the solo hunter;
    fleet register ranks 16/21, flagged in the orchestrator's verdict as
    the one under-covered axis) found that proviso had NO biting witness
    for the presence-DESTROYING case: the single most common CDC outage
    pattern --- sink retention shorter than crash-to-recovery downtime
    (a 7-day Kafka topic, a 9-day outage) --- deletes delivered payloads
    before recovery reads them, the sink-read under-reports, and the
    escape re-emits every one: duplicates on exactly the events it was
    designed to protect, produced by the escape itself.  This theory
    makes that failure mode, and its exact boundary, a theorem set.

    THE ADDITIVITY DISCIPLINE (binding).  Boundary row 3 stands: no
    machine transition removes a ledger entry, and none is added here.
    The control is FUNCTION-LEVEL: retention_view n truncates the n
    oldest entries of the ledger AS AN OBSERVATION --- the sink's
    readable index after retention expiry, i.e. what a recovery
    procedure can still READ --- never a machine rule.  The ledger
    itself remains the external world's true record (a webhook already
    fired does not un-fire when a topic segment expires), which is
    exactly why the verdicts below are honest: every hazard is evaluated
    at the TRUE ledger, where the world really did receive the payload
    twice even though the recovery could no longer see the first copy.

    Content: (i) the retained view and the retention-read escape
    (retention_delta = the landed sink_delta filter computed against the
    retained view; near-definitionally the landed escape run on the
    rewritten ledger, and literally the landed escape at expiry depth 0);
    (ii) window_presence_destroyed, the proviso's exact boundary: the
    retention read EQUALS the true read IFF no delivered-in-window
    presence was destroyed --- so the landed escape guarantees transfer
    verbatim exactly up to that line --- plus the premise-free no-loss
    theorem (a retention read can only ever OVER-emit: at-least-once is
    never at risk, exactly-once is); (iii) THE BITING CONTROL at the
    landed dilemma pair's own members: at d2_w the true read is the
    landed exactly-once-restoring redrive (cited, never re-proved) while
    the depth-1 retention read re-emits the already-delivered payload
    and its redrive result is duplicate / effect-unsafe at the true
    ledger --- and machine-REACHABLE, because the retention batch there
    coincides with the cold m = 0 cursor re-drive (the stale-cursor
    amplification this tier warns about, now produced by the escape's
    own read); at d1_w the same view fabricates a duplicate from a state
    that owed nothing; (iv) THE CALIBRATION TWIN: a reachable state
    where the same depth-1 retention genuinely destroys delivered
    presence --- but outside the scoped recovery window --- and the
    retention read collapses to the true read and stays exactly-once:
    the control bites on WINDOW presence destruction specifically, never
    on the view plumbing; (v) the class contrast: the retention read is
    not presence-measured (truncation reads arrival order, which the
    landed presence class erases), and it DISTINGUISHES the dilemma pair
    --- its defeat here is a new axis (observation destroyed), not the
    landed batch-agreement ceiling (observation missing).

    PROVENANCE: paper/dual_write/theory_backlog/THEORY_IMPROVEMENT_ROADMAP.md
    Wave 2 slice W2a; paper/dual_write/prose_phase/framing_exploration/
    gap_hunt_2026-07-07/GAP_HUNT_FLEET_CAPTURE.md section A2 (presence-
    destroying witness control, merged from the banked sink-retention
    redo LENS_REDO_sink_retention_opus_max.json and the solo hunter's
    appendix-E note); register ranks 16/21 axis.

    In-source ML oracle gates are STRIPPED at landing: oracle-freedom is
    certified by scratch-side per-slice gate sessions with
    confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Retention_Control
  imports Dual_Write_Effect_Exactly_Once Dual_Write_Effect_Presence_Bound
begin

section \<open>Scope: the retention proviso gets its biting witness\<close>

text \<open>
  The landed record proves the sink-reading escape robust to the BENIGN
  sink rewrites (@{thm [source] sink_delta_payload_presence_invariant},
  @{thm [source] sink_delta_log_compaction}): every presence-preserving
  re-encoding of the ledger is invisible to @{const sink_delta}.  What a
  real sink additionally does is FORGET on a retention clock --- and
  forgetting is presence-DESTROYING, the case the landed invariance
  family deliberately does not cover and the landed corpus never
  witnesses.  This theory closes that axis at the function level:

  \<^item> the retained view @{text retention_view} models the sink's readable
    index after retention expiry (the @{term n} OLDEST entries gone ---
    the delete-retention discipline of production log stores, applied to
    the arrival-ordered, append-only ledger);

  \<^item> the retention-read escape @{text retention_delta} is the landed
    escape's own filter fed the retained view in place of the true
    ledger --- the recovery procedure of the landed positive side, run
    against a sink that has already expired part of its history;

  \<^item> hazards stay evaluated at the TRUE ledger throughout: the machine,
    its rules, and boundary row 3 (no rule removes a ledger entry) are
    untouched, and no reachability claim is made for any truncated
    ledger AS a machine state.  Retention truncates the recovery's
    observation channel, not the world.

  The payoff is the exact boundary of the landed retention proviso: the
  retention read computes the landed batch IFF no delivered payload of
  the current scoped, frontier-bounded replay was expired
  (@{text retention_read_faithful_iff_window_intact} below), the landed
  escape guarantees transfer verbatim on the intact side (calibration,
  at a reachable state with genuine out-of-window destruction), and on
  the destroyed side the escape's OWN redrive duplicates at both members
  of the landed dilemma pair --- with the loss-side result reachable by
  the machine itself.
\<close>

section \<open>The retained view and the retention-read escape\<close>

text \<open>
  @{term "retention_view n L"} is the ledger with its @{term n} oldest
  entries expired.  The ledger is append-only in arrival order, so
  dropping a prefix is exactly oldest-first retention expiry; a
  keep-the-most-recent-@{term w} window is the instance
  @{term "n = length L - w"}.  An observation function on the pinned
  emission type --- never a machine rule.
\<close>

definition retention_view
  :: "nat \<Rightarrow> ('k, 'v) emission list \<Rightarrow> ('k, 'v) emission list"
where
  "retention_view n L = drop n L"

text \<open>
  The retention-read escape: the landed @{const sink_delta} filter with
  the presence test taken against the retained view.  Pinned at
  @{typ "(nat, nat) dwe_state"} like the landed policy classes, so
  @{term "retention_delta n f"} IS a @{typ redrive_policy}.
\<close>

definition retention_delta
  :: "nat \<Rightarrow> frontier \<Rightarrow> (nat, nat) dwe_state \<Rightarrow>
      (src_coord \<times> (nat, nat) source_event) list"
where
  "retention_delta n f t =
     filter (\<lambda>p. p \<notin> e_payload ` set (retention_view n (dwe_emitted t)))
       (replay_down_hist (exec_src_hist (dwe_core t))
          (exec_scope (dwe_core t)) f)"

text \<open>
  The near-definitional bridge to the landed vocabulary: the
  retention-read escape IS the landed escape evaluated on the rewritten
  ledger --- the exact rewrite form the landed invariance family
  (@{thm [source] sink_delta_compaction_invariant}) quantifies over.
  Everything below is therefore a statement about which ledger rewrites
  the landed escape tolerates.
\<close>

lemma retention_delta_is_sink_delta_on_view:
  "retention_delta n f t
     = sink_delta f (t\<lparr>dwe_emitted := retention_view n (dwe_emitted t)\<rparr>)"
  by (simp add: retention_delta_def sink_delta_def)

text \<open>Expiry depth 0 is literally the landed escape: the view plumbing
  adds nothing of its own.\<close>

lemma retention_zero_is_true_read:
  "retention_delta 0 f t = sink_delta f t"
  by (simp add: retention_delta_def sink_delta_def retention_view_def)

text \<open>Retention only ever under-reports presence:\<close>

lemma retention_view_presence_subset:
  "e_payload ` set (retention_view n L) \<subseteq> e_payload ` set L"
  unfolding retention_view_def by (rule image_mono[OF set_drop_subset])

text \<open>So the retention read only ever OVER-emits: its batch contains
  the true batch.  The failure mode this slice witnesses is duplication,
  never a new loss --- made precise by the no-loss theorem below.\<close>

lemma sink_delta_subset_retention_delta:
  "set (sink_delta f t) \<subseteq> set (retention_delta n f t)"
proof
  fix p
  assume "p \<in> set (sink_delta f t)"
  then have pR: "p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                            (exec_scope (dwe_core t)) f)"
        and pout: "p \<notin> e_payload ` set (dwe_emitted t)"
    by (auto simp: sink_delta_def)
  have "p \<notin> e_payload ` set (retention_view n (dwe_emitted t))"
    using pout retention_view_presence_subset[of n "dwe_emitted t"] by auto
  with pR show "p \<in> set (retention_delta n f t)"
    by (simp add: retention_delta_def)
qed

section \<open>Window presence destruction: the proviso's exact boundary\<close>

text \<open>
  The landed proviso names its own boundary: delivered-payload presence
  WITHIN the recovery window must survive.  Formally: some payload of
  the current scoped, frontier-bounded replay was delivered (it is in
  the true ledger's presence set) and expired (it is not in the
  retained view's presence set).  Destruction OUTSIDE the window ---
  payloads the current recovery could not re-drive anyway --- is
  deliberately not counted, and the calibration twin below shows it is
  rightly not counted.
\<close>

definition window_presence_destroyed
  :: "nat \<Rightarrow> frontier \<Rightarrow> (nat, nat) dwe_state \<Rightarrow> bool"
where
  "window_presence_destroyed n f t \<longleftrightarrow>
     (\<exists>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                   (exec_scope (dwe_core t)) f).
        p \<in> e_payload ` set (dwe_emitted t)
      \<and> p \<notin> e_payload ` set (retention_view n (dwe_emitted t)))"

text \<open>
  THE INVISIBILITY DIRECTION: if retention destroyed no delivered-in-
  window presence, the retention read computes the landed batch --- the
  membership test is only ever applied to replay members, the same
  observation as the landed
  @{thm [source] sink_delta_needs_only_scoped_presence}.  Premise-free
  beyond the window condition; pure filter algebra.
\<close>

lemma retention_window_intact_invisible:
  assumes intact: "\<not> window_presence_destroyed n f t"
  shows "retention_delta n f t = sink_delta f t"
  unfolding retention_delta_def sink_delta_def
proof (rule filter_cong[OF refl])
  fix p
  assume p: "p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                        (exec_scope (dwe_core t)) f)"
  have fwd: "p \<in> e_payload ` set (dwe_emitted t)
               \<Longrightarrow> p \<in> e_payload ` set (retention_view n (dwe_emitted t))"
    using intact p unfolding window_presence_destroyed_def by blast
  have bwd: "p \<in> e_payload ` set (retention_view n (dwe_emitted t))
               \<Longrightarrow> p \<in> e_payload ` set (dwe_emitted t)"
    using retention_view_presence_subset[of n "dwe_emitted t"] by auto
  show "(p \<notin> e_payload ` set (retention_view n (dwe_emitted t)))
          = (p \<notin> e_payload ` set (dwe_emitted t))"
    using fwd bwd by blast
qed

text \<open>THE BITING DIRECTION: any destroyed delivered-in-window payload is
  kept by the retention filter and dropped by the true filter, so the
  two batches differ.  Together: an IFF --- the proviso's boundary is
  exactly window presence survival, with nothing to spare.\<close>

lemma window_destroyed_delta_differs:
  assumes "window_presence_destroyed n f t"
  shows "retention_delta n f t \<noteq> sink_delta f t"
proof -
  from assms obtain p
    where pR: "p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                          (exec_scope (dwe_core t)) f)"
      and pF: "p \<in> e_payload ` set (dwe_emitted t)"
      and pV: "p \<notin> e_payload ` set (retention_view n (dwe_emitted t))"
    unfolding window_presence_destroyed_def by blast
  have "p \<in> set (retention_delta n f t)"
    using pR pV by (simp add: retention_delta_def)
  moreover have "p \<notin> set (sink_delta f t)"
    using pF by (simp add: sink_delta_def)
  ultimately show ?thesis by metis
qed

theorem retention_read_faithful_iff_window_intact:
  "retention_delta n f t = sink_delta f t
     \<longleftrightarrow> \<not> window_presence_destroyed n f t"
  using retention_window_intact_invisible window_destroyed_delta_differs
  by blast

text \<open>A policy redrive consumes its policy only at the redriven state,
  so equal batches there give the same redrive relation --- the
  transfer vehicle for the intact side.\<close>

lemma policy_redrive_batch_cong:
  assumes "P t = Q t"
  shows "policy_redrive P t f t' \<longleftrightarrow> policy_redrive Q t f t'"
  using assms by (simp add: policy_redrive_def)

text \<open>
  THE INTACT-SIDE TRANSFER: under the landed B1 premises, if retention
  destroyed no delivered-in-window presence then the retention-read
  redrive heals every scoped mismatch at its own frontier and lands
  exactly-once there --- by CITATION of the landed
  @{thm [source] sink_delta_achieves_exactly_once}, through the iff
  above.  The landed escape guarantees survive retention exactly up to
  the proviso's line.
\<close>

theorem retention_window_intact_exactly_once:
  assumes intact: "\<not> window_presence_destroyed n f t"
      and safe: "\<not> effect_unsafe t"
      and crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and fin: "f \<le> exec_finish (dwe_core t)"
      and asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "(\<exists>t'. policy_redrive (retention_delta n f) t f t')
       \<and> (\<forall>t'. policy_redrive (retention_delta n f) t f t' \<longrightarrow>
            (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k)
          \<and> exactly_once_at f t')"
proof -
  have eq: "retention_delta n f t = sink_delta f t"
    by (rule retention_window_intact_invisible[OF intact])
  have pr_eq: "\<And>t'. policy_redrive (retention_delta n f) t f t'
                 = policy_redrive (sink_delta f) t f t'"
    by (simp add: policy_redrive_def eq)
  show ?thesis
    unfolding pr_eq
    by (rule sink_delta_achieves_exactly_once[OF safe crashed fin asc])
qed

section \<open>What retention cannot cost: no loss, ever\<close>

text \<open>
  Premise-free (not even the ascending premise, matching the landed
  premise-free posture of @{thm [source] sink_reading_escape_general}'s
  general form): because the retained presence set only shrinks, every
  replay payload is either still visibly delivered or re-emitted by the
  retention batch --- so a retention-read redrive is ALWAYS
  at-least-once at its frontier.  Retention attacks exactly-once
  through the DUPLICATE horn alone; the loss horn of the landed dilemma
  never fires for a retention read.  (This is why the practitioner
  symptom of retention-shorter-than-downtime is a duplicate storm,
  never silent skips.)
\<close>

theorem retention_escape_never_loses:
  assumes pr: "policy_redrive (retention_delta n f) t f t'"
  shows "at_least_once_at f t' \<and> \<not> lost_effect f t'"
proof -
  have em': "dwe_emitted t'
      = dwe_emitted t
        @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                         dwe_epoch t, c, e))
            (retention_delta n f t)"
    by (rule policy_redrive_emitted[OF pr])
  have src': "exec_src_hist (dwe_core t') = exec_src_hist (dwe_core t)"
    by (rule policy_redrive_src_same[OF pr])
  have scope': "exec_scope (dwe_core t') = exec_scope (dwe_core t)"
    by (rule policy_redrive_scope_same[OF pr])
  have img': "e_payload ` set (dwe_emitted t')
      = e_payload ` set (dwe_emitted t) \<union> set (retention_delta n f t)"
    by (simp add: em' image_Un image_image)
  have alo: "at_least_once_at f t'"
    unfolding at_least_once_at_def src' scope'
  proof
    fix p
    assume p: "p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                          (exec_scope (dwe_core t)) f)"
    show "p \<in> e_payload ` set (dwe_emitted t')"
    proof (cases "p \<in> e_payload ` set (dwe_emitted t)")
      case True
      then show ?thesis by (simp add: img')
    next
      case False
      then have "p \<notin> e_payload ` set (retention_view n (dwe_emitted t))"
        using retention_view_presence_subset[of n "dwe_emitted t"] by auto
      then have "p \<in> set (retention_delta n f t)"
        using p by (simp add: retention_delta_def)
      then show ?thesis by (simp add: img')
    qed
  qed
  then show ?thesis
    by (simp add: at_least_once_iff_not_lost)
qed

section \<open>The bridge to the landed presence-preserving family\<close>

text \<open>
  Presence-PRESERVING retention is invisible --- a direct instance of
  the landed @{thm [source] sink_delta_compaction_invariant} through the
  near-definitional bridge, i.e. exactly the landed invariance family
  doing its work on a retained view that happens to destroy nothing.
  Contrast the landed keep-latest compaction, whose presence
  preservation is a THEOREM (@{thm [source] payload_compact_presence}):
  a retention view carries no such theorem, and the witness below shows
  a landed reachable state where it genuinely fails --- the destroying
  view is exactly what the landed preserving hypothesis excludes, and
  there the invariance CONCLUSION fails too, so the landed family is
  tight at its own hypothesis.
\<close>

theorem retention_presence_preserving_invisible:
  assumes "e_payload ` set (retention_view n (dwe_emitted t))
             = e_payload ` set (dwe_emitted t)"
  shows "retention_delta n f t = sink_delta f t"
  unfolding retention_delta_is_sink_delta_on_view
  by (rule sink_delta_compaction_invariant[OF assms])

text \<open>Ledger evaluations at the landed dilemma pair (the pair's fields
  are the landed @{thm [source] d1_fields} / @{thm [source] d2_fields}).\<close>

lemma d1_retention_view:
  "retention_view 1 (dwe_emitted d1_w) = [(2, 0, ec2, e2)]"
  by (simp add: retention_view_def d1_fields eval_nat_numeral)

lemma d2_retention_view:
  "retention_view 1 (dwe_emitted d2_w) = []"
  by (simp add: retention_view_def d2_fields eval_nat_numeral)

lemma d1_retention_delta:
  "retention_delta 1 ec2 d1_w = [(ec1, e1)]"
  by (simp add: retention_delta_def retention_view_def replay_down_hist_def
                d1_w_def mkT_def mkC_def e1_def e2_def ec_defs
                eval_nat_numeral)

lemma d2_retention_delta:
  "retention_delta 1 ec2 d2_w = [(ec1, e1), (ec2, e2)]"
  by (simp add: retention_delta_def retention_view_def replay_down_hist_def
                d2_w_def mkT_def mkC_def e1_def e2_def ec_defs
                eval_nat_numeral)

lemma d1_sink_delta: "sink_delta ec2 d1_w = []"
  by (simp add: sink_delta_def d1_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs)

lemma d2_sink_delta: "sink_delta ec2 d2_w = [(ec2, e2)]"
  by (simp add: sink_delta_def d2_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs)

text \<open>The destroying witness, at the landed loss-side member: depth-1
  retention there is NOT presence-preserving --- and the invariance
  conclusion fails with it.\<close>

theorem retention_outside_presence_preserving_family:
  "e_payload ` set (retention_view 1 (dwe_emitted d2_w))
     \<noteq> e_payload ` set (dwe_emitted d2_w)
 \<and> retention_delta 1 ec2 d2_w \<noteq> sink_delta ec2 d2_w"
proof
  show "e_payload ` set (retention_view 1 (dwe_emitted d2_w))
          \<noteq> e_payload ` set (dwe_emitted d2_w)"
    by (simp add: retention_view_def d2_w_def mkT_def eval_nat_numeral)
next
  show "retention_delta 1 ec2 d2_w \<noteq> sink_delta ec2 d2_w"
    by (simp add: retention_delta_def retention_view_def sink_delta_def
                  replay_down_hist_def d2_w_def mkT_def mkC_def
                  e1_def e2_def ec_defs eval_nat_numeral)
qed

section \<open>THE BITING CONTROL: the loss-side member re-duplicated\<close>

definition d2_ret_w :: "(nat, nat) dwe_state" where
  "d2_ret_w = redrive_result (retention_delta 1 ec2) d2_w ec2"

text \<open>
  The scenario, at the landed dilemma pair's own loss-side member
  @{const d2_w} (reachable, effect-safe, crashed; ledger
  @{term "[(1, 0, ec1, e1)]"} --- one payload delivered, one committed
  effect genuinely owed):

  \<^item> THE TRUE READ (the landed positive side, cited): the landed
    @{thm [source] sink_delta_restores_exactly_once_at_d2} --- the
    escape's batch is the m = 1 cursor suffix, its redrive is a machine
    reconcile, the result is reachable and exactly-once at the
    frontier.  Nothing is re-proved here.

  \<^item> THE RETENTION READ at expiry depth 1: the sink's whole readable
    window expired during the outage (@{term "retention_view 1"} of a
    one-entry ledger is empty).  The delivered payload
    @{term "(ec1, e1)"} is reported ABSENT, the recovery window's
    presence is destroyed, and the retention batch is the FULL replay
    --- literally the cold m = 0 cursor batch: retention that outlives
    the readable window degenerates the sink-reading escape into the
    stale-cursor re-drive this tier's amplification witnesses warn
    about.  The redrive result @{const d2_ret_w} still heals every
    scoped store mismatch, is still at-least-once (the no-loss theorem
    biting), and is DUPLICATE, hence effect-unsafe, at the true ledger
    --- exactly-once is forfeit.  It is moreover machine-REACHABLE: the
    retention batch coincides with the cold-cursor reconcile at this
    state, so the machine itself realizes the damage.

  Window presence destruction is thereby witnessed load-bearing for the
  escape's guarantee: the landed B1 premises all HOLD at @{const d2_w}
  --- only the proviso is violated, and only the verdict flips.
\<close>

lemma pr_d2_ret:
  "policy_redrive (retention_delta 1 ec2) d2_w ec2 d2_ret_w"
  unfolding d2_ret_w_def by (rule policy_redriveI[OF d2_crashed d2_fin])

lemma d2_ret_unique:
  assumes "policy_redrive (retention_delta 1 ec2) d2_w ec2 t'"
  shows "t' = d2_ret_w"
  unfolding d2_ret_w_def by (rule policy_redrive_result[OF assms])

lemma d2_ret_emitted:
  "dwe_emitted d2_ret_w
     = [(1, 0, ec1, e1), (2, 1, ec1, e1), (2, 1, ec2, e2)]"
  by (simp add: d2_ret_w_def redrive_result_def retention_delta_def
                retention_view_def replay_down_hist_def d2_w_def mkT_def
                mkC_def e1_def e2_def ec_defs eval_nat_numeral)

lemma d2_ret_duplicate: "duplicate d2_ret_w"
  by (simp add: duplicate_def d2_ret_emitted)

lemma d2_ret_unsafe: "effect_unsafe d2_ret_w"
  by (simp add: effect_unsafe_def d2_ret_duplicate)

lemma d2_ret_not_exactly_once: "\<not> exactly_once_at ec2 d2_ret_w"
  by (simp add: exactly_once_at_def d2_ret_unsafe)

lemma d2_window_destroyed: "window_presence_destroyed 1 ec2 d2_w"
  by (simp add: window_presence_destroyed_def retention_view_def
                replay_down_hist_def d2_w_def mkT_def mkC_def
                e1_def e2_def ec_defs eval_nat_numeral)

text \<open>The retention batch at @{const d2_w} is the whole scoped replay
  --- the cold-cursor degeneration, and the reachability vehicle.\<close>

lemma d2_retention_delta_is_cold_replay:
  "retention_delta 1 ec2 d2_w
     = replay_down_hist (exec_src_hist (dwe_core d2_w))
         (exec_scope (dwe_core d2_w)) ec2"
  by (simp add: retention_delta_def retention_view_def replay_down_hist_def
                d2_w_def mkT_def mkC_def e1_def e2_def ec_defs
                eval_nat_numeral)

lemma rec_d2_ret: "emitting_reconcile 0 d2_w ec2 d2_ret_w"
  by (simp add: emitting_reconcile_def d2_ret_w_def redrive_result_def
                retention_delta_def retention_view_def d2_w_def mkT_def
                mkC_def replay_down_hist_def e1_def e2_def ec_defs
                eval_nat_numeral)

lemma reach_d2_ret: "dwe_reachable d2_ret_w"
  by (rule dwe_reachable_reconcile_ext[OF reach_d2 rec_d2_ret])

theorem retention_biting_control:
  "dwe_reachable d2_w \<and> \<not> effect_unsafe d2_w
 \<and> exactly_once_at ec2 (redrive_result (sink_delta ec2) d2_w ec2)
 \<and> (ec1, e1) \<in> e_payload ` set (dwe_emitted d2_w)
 \<and> (ec1, e1) \<notin> e_payload ` set (retention_view 1 (dwe_emitted d2_w))
 \<and> (ec1, e1) \<in> set (retention_delta 1 ec2 d2_w)
 \<and> window_presence_destroyed 1 ec2 d2_w
 \<and> policy_redrive (retention_delta 1 ec2) d2_w ec2 d2_ret_w
 \<and> (\<forall>t'. policy_redrive (retention_delta 1 ec2) d2_w ec2 t'
       \<longrightarrow> t' = d2_ret_w)
 \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core d2_ret_w) ec2) ec2 k)
 \<and> at_least_once_at ec2 d2_ret_w
 \<and> duplicate d2_ret_w
 \<and> effect_unsafe d2_ret_w
 \<and> \<not> exactly_once_at ec2 d2_ret_w
 \<and> dwe_reachable d2_ret_w"
proof -
  have true_read: "exactly_once_at ec2 (redrive_result (sink_delta ec2) d2_w ec2)"
    using sink_delta_restores_exactly_once_at_d2 by blast
  have delivered: "(ec1, e1) \<in> e_payload ` set (dwe_emitted d2_w)"
    by (simp add: d2_fields)
  have absent: "(ec1, e1) \<notin> e_payload ` set (retention_view 1 (dwe_emitted d2_w))"
    by (simp add: retention_view_def d2_w_def mkT_def eval_nat_numeral)
  have reemitted: "(ec1, e1) \<in> set (retention_delta 1 ec2 d2_w)"
    by (simp add: retention_delta_def retention_view_def
                  replay_down_hist_def d2_w_def mkT_def mkC_def
                  e1_def e2_def ec_defs eval_nat_numeral)
  have uniq: "\<forall>t'. policy_redrive (retention_delta 1 ec2) d2_w ec2 t'
                 \<longrightarrow> t' = d2_ret_w"
    using d2_ret_unique by blast
  have heal: "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core d2_ret_w) ec2) ec2 k"
    by (rule policy_redrive_heals[OF pr_d2_ret])
  have alo: "at_least_once_at ec2 d2_ret_w"
    using retention_escape_never_loses[OF pr_d2_ret] by blast
  show ?thesis
    by (intro conjI reach_d2 d2_not_unsafe true_read delivered absent
          reemitted d2_window_destroyed pr_d2_ret uniq heal alo
          d2_ret_duplicate d2_ret_unsafe d2_ret_not_exactly_once
          reach_d2_ret)
qed

section \<open>The safe member: a fabricated duplicate from a state that owed nothing\<close>

text \<open>
  The same depth-1 view at the pair's SAFE member @{const d1_w}
  (reachable, both payloads delivered, ledger
  @{term "[(1, 0, ec1, e1), (2, 0, ec2, e2)]"}).  The state is already
  exactly-once at the frontier (the landed
  @{thm [source] d1_exactly_once}); the true read owes NOTHING (its
  batch is empty) and the landed positive theorem keeps the redrive
  exactly-once.  Depth-1 retention expires exactly the oldest delivered
  entry, reports @{term "(ec1, e1)"} absent, and the retention read
  FABRICATES a re-emission from a state that owed nothing --- the
  redrive result is duplicate / effect-unsafe at the true ledger.
  (At this member the retention batch @{term "[(ec1, e1)]"} is not a
  @{term "drop m"} suffix of the replay, so no machine reconcile
  realizes it; the redrive-relation posture here is the landed
  dilemma's own, and the loss-side member above already supplies the
  machine-reachable damage.)
\<close>

definition d1_ret_w :: "(nat, nat) dwe_state" where
  "d1_ret_w = redrive_result (retention_delta 1 ec2) d1_w ec2"

lemma d1_crashed: "\<exists>c. exec_status (dwe_core d1_w) = Crashed c"
  by (simp add: d1_fields)

lemma d1_fin: "ec2 \<le> exec_finish (dwe_core d1_w)"
  by (simp add: d1_fields)

lemma d1_asc: "strictly_ascending_source (exec_src_hist (dwe_core d1_w))"
  using d2_asc by (simp add: d_cores_eq)

lemma pr_d1_ret:
  "policy_redrive (retention_delta 1 ec2) d1_w ec2 d1_ret_w"
  unfolding d1_ret_w_def by (rule policy_redriveI[OF d1_crashed d1_fin])

lemma d1_ret_unique:
  assumes "policy_redrive (retention_delta 1 ec2) d1_w ec2 t'"
  shows "t' = d1_ret_w"
  unfolding d1_ret_w_def by (rule policy_redrive_result[OF assms])

lemma d1_ret_emitted:
  "dwe_emitted d1_ret_w
     = [(1, 0, ec1, e1), (2, 0, ec2, e2), (2, 1, ec1, e1)]"
  by (simp add: d1_ret_w_def redrive_result_def retention_delta_def
                retention_view_def replay_down_hist_def d1_w_def mkT_def
                mkC_def e1_def e2_def ec_defs eval_nat_numeral)

lemma d1_ret_duplicate: "duplicate d1_ret_w"
  by (simp add: duplicate_def d1_ret_emitted)

lemma d1_ret_unsafe: "effect_unsafe d1_ret_w"
  by (simp add: effect_unsafe_def d1_ret_duplicate)

lemma d1_ret_not_exactly_once: "\<not> exactly_once_at ec2 d1_ret_w"
  by (simp add: exactly_once_at_def d1_ret_unsafe)

lemma d1_window_destroyed: "window_presence_destroyed 1 ec2 d1_w"
  by (simp add: window_presence_destroyed_def retention_view_def
                replay_down_hist_def d1_w_def mkT_def mkC_def
                e1_def e2_def ec_defs eval_nat_numeral)

theorem retention_biting_control_safe_member:
  "dwe_reachable d1_w
 \<and> exactly_once_at ec2 d1_w
 \<and> sink_delta ec2 d1_w = []
 \<and> (\<forall>t'. policy_redrive (sink_delta ec2) d1_w ec2 t'
       \<longrightarrow> exactly_once_at ec2 t')
 \<and> retention_delta 1 ec2 d1_w = [(ec1, e1)]
 \<and> (ec1, e1) \<in> e_payload ` set (dwe_emitted d1_w)
 \<and> (ec1, e1) \<notin> e_payload ` set (retention_view 1 (dwe_emitted d1_w))
 \<and> window_presence_destroyed 1 ec2 d1_w
 \<and> policy_redrive (retention_delta 1 ec2) d1_w ec2 d1_ret_w
 \<and> (\<forall>t'. policy_redrive (retention_delta 1 ec2) d1_w ec2 t'
       \<longrightarrow> t' = d1_ret_w)
 \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core d1_ret_w) ec2) ec2 k)
 \<and> at_least_once_at ec2 d1_ret_w
 \<and> duplicate d1_ret_w
 \<and> effect_unsafe d1_ret_w
 \<and> \<not> exactly_once_at ec2 d1_ret_w"
proof -
  have true_read: "\<forall>t'. policy_redrive (sink_delta ec2) d1_w ec2 t'
                      \<longrightarrow> exactly_once_at ec2 t'"
    using sink_delta_achieves_exactly_once
            [OF d1_not_unsafe d1_crashed d1_fin d1_asc] by blast
  have delivered: "(ec1, e1) \<in> e_payload ` set (dwe_emitted d1_w)"
    by (simp add: d1_fields)
  have absent: "(ec1, e1) \<notin> e_payload ` set (retention_view 1 (dwe_emitted d1_w))"
    by (simp add: retention_view_def d1_w_def mkT_def e1_def e2_def ec_defs
                  eval_nat_numeral)
  have uniq: "\<forall>t'. policy_redrive (retention_delta 1 ec2) d1_w ec2 t'
                 \<longrightarrow> t' = d1_ret_w"
    using d1_ret_unique by blast
  have heal: "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core d1_ret_w) ec2) ec2 k"
    by (rule policy_redrive_heals[OF pr_d1_ret])
  have alo: "at_least_once_at ec2 d1_ret_w"
    using retention_escape_never_loses[OF pr_d1_ret] by blast
  show ?thesis
    by (intro conjI reach_d1 d1_exactly_once d1_sink_delta true_read
          d1_retention_delta delivered absent d1_window_destroyed
          pr_d1_ret uniq heal alo d1_ret_duplicate d1_ret_unsafe
          d1_ret_not_exactly_once)
qed

section \<open>THE CALIBRATION TWIN: destruction outside the window is harmless\<close>

text \<open>
  The control must bite on WINDOW presence destruction specifically,
  not on the view plumbing --- so the twin runs the SAME depth-1
  retention view at a reachable crashed state where retention genuinely
  destroyed delivered presence, but only OUTSIDE the scoped recovery
  window.  The witness chain delivers the landed third business event
  @{const e3} (the Discipline theory's @{term "Insert 2 3"}, whose key
  2 lies outside the pinned contract scope @{term "{0, 1}"}) first, then
  the in-scope @{const e2}: the ledger's OLDEST entry is the
  out-of-scope delivery, so depth-1 expiry removes presence the current
  scoped, frontier-bounded replay never asks about.  The retention read
  collapses to the true read (through the iff, whose intact side is
  evaluated, not assumed), and the landed escape guarantees hold
  verbatim: heal plus exactly-once at the frontier.

  Both witnesses run the same @{term "retention_view 1"}: at
  @{const d2_w} / @{const d1_w} the destroyed presence is in-window and
  exactly-once is forfeit; here it is out-of-window and exactly-once
  survives.  The landed retention reading --- retention may forget
  everything outside the window --- is thereby calibrated exactly.
\<close>

definition rc1_w :: "(nat, nat) dwe_state" where
  "rc1_w = mkT (mkC [(ec1, e3)] [] [] {} Running) [] 0"

definition rc2_w :: "(nat, nat) dwe_state" where
  "rc2_w = mkT (mkC [(ec1, e3)] [] [(ec1, e3)] {(ec1, e3)} Running) [] 0"

definition rc3_w :: "(nat, nat) dwe_state" where
  "rc3_w = mkT (mkC [(ec1, e3)] [(ec1, e3)] [(ec1, e3)] {} Running)
               [(1, 0, ec1, e3)] 0"

definition rc4_w :: "(nat, nat) dwe_state" where
  "rc4_w = mkT (mkC [(ec1, e3), (ec2, e2)] [(ec1, e3)] [(ec1, e3)] {}
                  Running)
               [(1, 0, ec1, e3)] 0"

definition rc5_w :: "(nat, nat) dwe_state" where
  "rc5_w = mkT (mkC [(ec1, e3), (ec2, e2)] [(ec1, e3)]
                  [(ec1, e3), (ec2, e2)] {(ec2, e2)} Running)
               [(1, 0, ec1, e3)] 0"

definition rc6_w :: "(nat, nat) dwe_state" where
  "rc6_w = mkT (mkC [(ec1, e3), (ec2, e2)] [(ec1, e3), (ec2, e2)]
                  [(ec1, e3), (ec2, e2)] {} Running)
               [(1, 0, ec1, e3), (2, 0, ec2, e2)] 0"

definition cal_w :: "(nat, nat) dwe_state" where
  "cal_w = mkT (mkC [(ec1, e3), (ec2, e2)] [(ec1, e3), (ec2, e2)]
                  [(ec1, e3), (ec2, e2)] {} (Crashed ec2))
               [(1, 0, ec1, e3), (2, 0, ec2, e2)] 0"

subsection \<open>Wellformedness and admissibility along the chain\<close>

lemma wfh_e3c1: "wellformed_src_history [(ec1, e3)]"
  by (rule wf_hist_single) (simp add: ec_defs)

lemma wfh_e3_pair: "wellformed_src_history [(ec1, e3), (ec2, e2)]"
  by (rule wf_hist_pair) (simp_all add: ec_defs)

lemma wf_rc1: "wellformed_exec_state (dwe_core rc1_w)"
  by (simp add: rc1_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e3c1)

lemma wf_rc2: "wellformed_exec_state (dwe_core rc2_w)"
  by (simp add: rc2_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e3c1)

lemma wf_rc3: "wellformed_exec_state (dwe_core rc3_w)"
  by (simp add: rc3_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e3c1)

lemma wf_rc4: "wellformed_exec_state (dwe_core rc4_w)"
  by (simp add: rc4_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e3c1
                wfh_e3_pair)

lemma wf_rc5: "wellformed_exec_state (dwe_core rc5_w)"
  by (simp add: rc5_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e3c1
                wfh_e3_pair)

lemma wf_rc6: "wellformed_exec_state (dwe_core rc6_w)"
  by (simp add: rc6_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e3_pair)

lemma g_W0_src_e3:
  "exec_label_preserves_history_wf (dwe_core W0) (DoSource ec1 e3)"
  by (simp add: W0_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_rc1_enq_e3:
  "exec_label_preserves_history_wf (dwe_core rc1_w)
     (EnqueueDownstream ec1 e3)"
  by (simp add: rc1_w_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_rc2_down_e3:
  "exec_label_preserves_history_wf (dwe_core rc2_w) (DoDownstream ec1 e3)"
  by (simp add: rc2_w_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_rc3_src2:
  "exec_label_preserves_history_wf (dwe_core rc3_w) (DoSource ec2 e2)"
  by (simp add: rc3_w_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_rc4_enq2:
  "exec_label_preserves_history_wf (dwe_core rc4_w)
     (EnqueueDownstream ec2 e2)"
  by (simp add: rc4_w_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_rc5_down2:
  "exec_label_preserves_history_wf (dwe_core rc5_w) (DoDownstream ec2 e2)"
  by (simp add: rc5_w_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_rc6_crash:
  "exec_label_preserves_history_wf (dwe_core rc6_w) (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

subsection \<open>The witness steps and reachability\<close>

lemma rcs1: "dwe_step W0 (DoSource ec1 e3) rc1_w"
proof -
  have c: "dw_exec_step (dwe_core W0) (DoSource ec1 e3) (dwe_core rc1_w)"
    by (rule do_sourceI) (simp_all add: W0_def rc1_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: W0_def rc1_w_def mkT_def)
qed

lemma rcs2: "dwe_step rc1_w (EnqueueDownstream ec1 e3) rc2_w"
proof -
  have c: "dw_exec_step (dwe_core rc1_w) (EnqueueDownstream ec1 e3)
             (dwe_core rc2_w)"
    by (rule enqueue_downstreamI)
       (simp_all add: rc1_w_def rc2_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c])
       (simp_all add: rc1_w_def rc2_w_def mkT_def)
qed

lemma rcs3: "dwe_step rc2_w (DoDownstream ec1 e3) rc3_w"
proof -
  have c: "dw_exec_step (dwe_core rc2_w) (DoDownstream ec1 e3)
             (dwe_core rc3_w)"
    by (rule do_downstreamI) (simp_all add: rc2_w_def rc3_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_publish_emitI[OF c])
       (simp add: rc2_w_def rc3_w_def mkT_def mkC_def eval_nat_numeral)
qed

lemma rcs4: "dwe_step rc3_w (DoSource ec2 e2) rc4_w"
proof -
  have c: "dw_exec_step (dwe_core rc3_w) (DoSource ec2 e2) (dwe_core rc4_w)"
    by (rule do_sourceI) (simp_all add: rc3_w_def rc4_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c])
       (simp_all add: rc3_w_def rc4_w_def mkT_def)
qed

lemma rcs5: "dwe_step rc4_w (EnqueueDownstream ec2 e2) rc5_w"
proof -
  have c: "dw_exec_step (dwe_core rc4_w) (EnqueueDownstream ec2 e2)
             (dwe_core rc5_w)"
    by (rule enqueue_downstreamI)
       (simp_all add: rc4_w_def rc5_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c])
       (simp_all add: rc4_w_def rc5_w_def mkT_def)
qed

lemma rcs6: "dwe_step rc5_w (DoDownstream ec2 e2) rc6_w"
proof -
  have c: "dw_exec_step (dwe_core rc5_w) (DoDownstream ec2 e2)
             (dwe_core rc6_w)"
    by (rule do_downstreamI) (simp_all add: rc5_w_def rc6_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_publish_emitI[OF c])
       (simp add: rc5_w_def rc6_w_def mkT_def mkC_def eval_nat_numeral)
qed

lemma rcs7: "dwe_step rc6_w (Crash ec2) cal_w"
proof -
  have c: "dw_exec_step (dwe_core rc6_w) (Crash ec2) (dwe_core cal_w)"
    by (rule crashI) (simp_all add: rc6_w_def cal_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c])
       (simp_all add: rc6_w_def cal_w_def mkT_def)
qed

lemma reach_rc1: "dwe_reachable rc1_w"
  by (rule dwe_reachable_label_ext[OF reach_W0 wf_W0 g_W0_src_e3 rcs1])

lemma reach_rc2: "dwe_reachable rc2_w"
  by (rule dwe_reachable_label_ext[OF reach_rc1 wf_rc1 g_rc1_enq_e3 rcs2])

lemma reach_rc3: "dwe_reachable rc3_w"
  by (rule dwe_reachable_label_ext[OF reach_rc2 wf_rc2 g_rc2_down_e3 rcs3])

lemma reach_rc4: "dwe_reachable rc4_w"
  by (rule dwe_reachable_label_ext[OF reach_rc3 wf_rc3 g_rc3_src2 rcs4])

lemma reach_rc5: "dwe_reachable rc5_w"
  by (rule dwe_reachable_label_ext[OF reach_rc4 wf_rc4 g_rc4_enq2 rcs5])

lemma reach_rc6: "dwe_reachable rc6_w"
  by (rule dwe_reachable_label_ext[OF reach_rc5 wf_rc5 g_rc5_down2 rcs6])

lemma reach_cal: "dwe_reachable cal_w"
  by (rule dwe_reachable_label_ext[OF reach_rc6 wf_rc6 g_rc6_crash rcs7])

subsection \<open>Evaluations at the calibration state\<close>

lemma cal_replay:
  "replay_down_hist [(ec1, e3), (ec2, e2)] {0, 1} ec2 = [(ec2, e2)]"
  by (simp add: replay_down_hist_def e2_def e3_def ec_defs)

lemma cal_not_unsafe: "\<not> effect_unsafe cal_w"
  by (simp add: effect_unsafe_def premature_def duplicate_def
                justified_at_def cal_w_def mkT_def mkC_def e2_def e3_def
                ec_defs eval_nat_numeral)

lemma cal_crashed: "\<exists>c. exec_status (dwe_core cal_w) = Crashed c"
  by (simp add: cal_w_def mkT_def mkC_def)

lemma cal_fin: "ec2 \<le> exec_finish (dwe_core cal_w)"
  by (simp add: cal_w_def mkT_def mkC_def)

lemma cal_asc: "strictly_ascending_source (exec_src_hist (dwe_core cal_w))"
  by (simp add: strictly_ascending_source_def cal_w_def mkT_def mkC_def
                ec_defs)

lemma cal_retention_view:
  "retention_view 1 (dwe_emitted cal_w) = [(2, 0, ec2, e2)]"
  by (simp add: retention_view_def cal_w_def mkT_def eval_nat_numeral)

text \<open>Retention genuinely destroyed DELIVERED presence at the twin:\<close>

lemma cal_presence_destroyed_globally:
  "(ec1, e3) \<in> e_payload ` set (dwe_emitted cal_w)
 \<and> (ec1, e3) \<notin> e_payload ` set (retention_view 1 (dwe_emitted cal_w))
 \<and> e_payload ` set (retention_view 1 (dwe_emitted cal_w))
     \<noteq> e_payload ` set (dwe_emitted cal_w)"
  by (auto simp: retention_view_def cal_w_def mkT_def e2_def e3_def ec_defs
                 eval_nat_numeral)

text \<open>But no delivered-IN-WINDOW presence was destroyed: the expired
  payload's key lies outside the contract scope, so the scoped replay
  never asks about it.\<close>

lemma cal_window_intact: "\<not> window_presence_destroyed 1 ec2 cal_w"
  by (simp add: window_presence_destroyed_def retention_view_def
                replay_down_hist_def cal_w_def mkT_def mkC_def
                e2_def e3_def ec_defs eval_nat_numeral)

lemma cal_retention_eq_sink:
  "retention_delta 1 ec2 cal_w = sink_delta ec2 cal_w"
  by (rule retention_window_intact_invisible[OF cal_window_intact])

lemma cal_sink_delta: "sink_delta ec2 cal_w = []"
  by (simp add: sink_delta_def replay_down_hist_def cal_w_def mkT_def
                mkC_def e2_def e3_def ec_defs)

theorem retention_calibration_out_of_window:
  "dwe_reachable cal_w
 \<and> \<not> effect_unsafe cal_w
 \<and> (ec1, e3) \<in> e_payload ` set (dwe_emitted cal_w)
 \<and> (ec1, e3) \<notin> e_payload ` set (retention_view 1 (dwe_emitted cal_w))
 \<and> e_payload ` set (retention_view 1 (dwe_emitted cal_w))
     \<noteq> e_payload ` set (dwe_emitted cal_w)
 \<and> \<not> window_presence_destroyed 1 ec2 cal_w
 \<and> retention_delta 1 ec2 cal_w = sink_delta ec2 cal_w
 \<and> (\<exists>t'. policy_redrive (retention_delta 1 ec2) cal_w ec2 t')
 \<and> (\<forall>t'. policy_redrive (retention_delta 1 ec2) cal_w ec2 t' \<longrightarrow>
      (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') ec2) ec2 k)
    \<and> exactly_once_at ec2 t')"
proof -
  have pos: "(\<exists>t'. policy_redrive (retention_delta 1 ec2) cal_w ec2 t')
       \<and> (\<forall>t'. policy_redrive (retention_delta 1 ec2) cal_w ec2 t' \<longrightarrow>
            (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') ec2) ec2 k)
          \<and> exactly_once_at ec2 t')"
    by (rule retention_window_intact_exactly_once
          [OF cal_window_intact cal_not_unsafe cal_crashed cal_fin cal_asc])
  show ?thesis
    using pos cal_presence_destroyed_globally
    by (intro conjI reach_cal cal_not_unsafe cal_window_intact
          cal_retention_eq_sink) blast+
qed

section \<open>Class contrast: what the retention read is, and is not\<close>

text \<open>
  The landed escape is presence-measured
  (@{thm [source] sink_delta_presence_measured}): it factors through
  (core, delivered-payload presence), which is exactly why every
  presence-preserving rewrite is invisible to it.  The retention read is
  NOT presence-measured: WHICH entries expire is a fact about arrival
  order, and the landed presence class erases order.  The control pair
  is the landed safe member @{const d1_w} against its ledger-permuted
  twin --- equal cores, equal presence, the two arrival orders --- on
  which depth-1 retention expires DIFFERENT payloads and the retention
  read computes different batches.  A designed state pair of the pinned
  type in the house control posture (the landed @{const sp0_w}
  precedent): reachability neither claimed nor needed, since the class
  quantifies over all states.
\<close>

definition d1_perm_w :: "(nat, nat) dwe_state" where
  "d1_perm_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)]
                      [(ec1, e1), (ec2, e2)] {} (Crashed ec2))
                   [(2, 0, ec2, e2), (1, 0, ec1, e1)] 1"

lemma d1_perm_cores: "dwe_core d1_perm_w = dwe_core d1_w"
  by (simp add: d1_perm_w_def d1_w_def mkT_def)

lemma d1_perm_presence:
  "e_payload ` set (dwe_emitted d1_perm_w)
     = e_payload ` set (dwe_emitted d1_w)"
  by (auto simp: d1_perm_w_def d1_w_def mkT_def)

lemma d1_perm_retention_delta:
  "retention_delta 1 ec2 d1_perm_w = [(ec2, e2)]"
  by (simp add: retention_delta_def retention_view_def replay_down_hist_def
                d1_perm_w_def mkT_def mkC_def e1_def e2_def ec_defs
                eval_nat_numeral)

theorem retention_read_not_presence_measured:
  "\<not> presence_measured (retention_delta 1 ec2)"
proof
  assume "presence_measured (retention_delta 1 ec2)"
  then obtain g where g: "\<forall>t. retention_delta 1 ec2 t
      = g (dwe_core t) (e_payload ` set (dwe_emitted t))"
    unfolding presence_measured_def by blast
  have "retention_delta 1 ec2 d1_perm_w = retention_delta 1 ec2 d1_w"
    using g d1_perm_cores d1_perm_presence by metis
  then show False
    by (simp add: retention_delta_def retention_view_def
                  replay_down_hist_def d1_perm_w_def d1_w_def mkT_def
                  mkC_def e1_def e2_def ec_defs eval_nat_numeral)
qed

text \<open>
  And the retention read DISTINGUISHES the landed dilemma pair --- the
  members differ precisely in the ledger component the view truncates
  --- so it is not a pair-agreeing policy and the landed batch-agreement
  kernel (@{thm [source] batch_agreement_dilemma}) does not defeat it.
  Its defeat above is therefore a genuinely NEW axis: the landed
  dilemma defeats policies whose observation is MISSING (they cannot
  see the ledger); retention defeats a policy whose observation is
  DESTROYED (the ledger's readable index no longer carries the window's
  presence).  Reading the sink remains necessary --- and reading a
  retention-truncated sink is not sufficient.  The landed defeat
  theorems keep their exists-system polarity untouched; no new policy
  impossibility is claimed.
\<close>

theorem retention_read_distinguishes_dilemma_pair:
  "retention_delta 1 ec2 d1_w \<noteq> retention_delta 1 ec2 d2_w"
  by (simp add: retention_delta_def retention_view_def
                replay_down_hist_def d1_w_def d2_w_def mkT_def mkC_def
                e1_def e2_def ec_defs eval_nat_numeral)

end
