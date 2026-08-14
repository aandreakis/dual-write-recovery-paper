(*  Title:       DWU_Journal_Grade.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Purpose: The journal-graded reading of the unified exactly-once verdict.

    An external review round (R10) machine-confirmed a two-surface divergence
    in the unified machine's grading: u_exactly_once_at measures delivery
    against retained_hist (the source history above dwu_floor), while
    u_lost_journal grades against the full commit journal.  Because URetain is
    guard-free BY DESIGN (retention is an environment action here; the
    truncation/retention axis is DWU_Truncation's subject, and the
    fenced-discipline grammar deliberately admits URetain unguarded), a
    disciplined completed-claim run can retain away a committed,
    never-delivered obligation: the headline u_exactly_once_at_completed_claim
    then certifies the endpoint exactly-once while u_lost_journal holds at the
    very same endpoint.

    This theory makes the journal-grade story explicit, in four moves:
      (1) u_exactly_once_journal_at --- the journal-graded verdict (same
          safety conjunct, coverage measured against dwu_journal);
      (2) permanent_source_journal_coincidence and its headline corollary
          u_exactly_once_at_completed_claim_journal --- on the
          permanent-source fragment (floor 0, journal = source) the two
          verdicts coincide, so the landed headline IS journal-graded there;
      (3) retention_sound_bridge + disciplined_journal_is_source +
          disciplined_retention_sound_journal_grade --- if the endpoint's
          dropped prefix is already accepted (retained_prefix_covered) and
          the journal equals the source history, retained-grade exactness
          upgrades to journal grade; u_retention_sound_steps is a
          sufficient run-level discipline establishing that premise;
      (4) the review's divergence run, banked verbatim as the in-corpus
          control journal_grade_divergence_control, plus the trace-level
          carrier u_retention_sound_steps whose retain-guarded runs deliver
          the bridge's coverage premise at every frontier within finish, with
          a positive publish-then-retain control closing the loop.

    Honesty regime: quick_and_dirty = false (ROOT-pinned), ZERO sorry, ZERO
    oops, no axiomatization, no consts, no oracles.  Every statement is PROVED.
*)

theory DWU_Journal_Grade
  imports DWU_Claim_Witness
begin

section \<open>1. The journal-graded verdict\<close>

text \<open>Same shape as @{const u_exactly_once_at}, with the at-least-once carrier
  switched from @{const retained_hist} to the full @{const dwu_journal}: the
  safety conjunct @{text "\<not> u_effect_unsafe"} is unchanged, and coverage is
  demanded for every in-scope journal obligation at the frontier.\<close>

definition u_exactly_once_journal_at :: "frontier \<Rightarrow> ('k, 'v) dwu_state \<Rightarrow> bool" where
  "u_exactly_once_journal_at f t \<longleftrightarrow>
     \<not> u_effect_unsafe t
   \<and> set (replay_down_hist (dwu_journal t) (exec_scope (dwu_store t)) f)
       \<subseteq> set (log_payloads (dwu_accepted t))"

text \<open>The coverage conjunct is exactly the negation of the landed journal-graded
  loss predicate, so the verdict reads: safe and no journal-graded loss.\<close>

lemma u_exactly_once_journal_at_alt:
  "u_exactly_once_journal_at f t \<longleftrightarrow> \<not> u_effect_unsafe t \<and> \<not> u_lost_journal f t"
  by (auto simp: u_exactly_once_journal_at_def u_lost_journal_def)


section \<open>2. Coincidence on the permanent-source fragment\<close>

text \<open>Under @{const u_permanent_source} (floor 0 and journal = source history)
  the retained suffix IS the journal, so the two verdicts are one.\<close>

lemma permanent_source_journal_coincidence:
  assumes "u_permanent_source t"
  shows "u_exactly_once_journal_at f t \<longleftrightarrow> u_exactly_once_at f t"
proof -
  from assms have "retained_hist t = dwu_journal t"
    by (simp add: u_permanent_source_def retained_hist_def)
  then show ?thesis
    by (simp add: u_exactly_once_journal_at_def u_exactly_once_at_def
                  u_at_least_once_at_def)
qed

text \<open>The headline @{text u_exactly_once_at_completed_claim} upgraded to the
  journal grade under the added permanent-source premise at the post-fire
  state: the six landed premises are untouched.\<close>

theorem u_exactly_once_at_completed_claim_journal:
  assumes "u_disciplined_trace (dwu_init b K fin) acts t"
      and "u_claim_of acts i j g f"
      and "u_window_fresh acts i j f"
      and "dwu_temporal_trace (dwu_init b K fin) (take j acts) tj"
      and "dwu_fence tj \<le> g"
      and "dwu_temporal_trace (dwu_init b K fin) (take (Suc j) acts) tj'"
      and "u_permanent_source tj'"
  shows "u_exactly_once_journal_at f tj'"
  using u_exactly_once_at_completed_claim[OF assms(1) assms(2) assms(3)
          assms(4) assms(5) assms(6)]
  by (simp add: permanent_source_journal_coincidence[OF assms(7)])


section \<open>3. The retention-sound bridge\<close>

text \<open>@{const dwu_floor} splits the source history into the dropped prefix and
  @{const retained_hist}.  @{text retained_prefix_covered} says the obligations
  the floor has dropped are already accepted; together with the retained-graded
  verdict and journal = source, the journal grade follows by set algebra.\<close>

definition retained_prefix_covered :: "frontier \<Rightarrow> ('k, 'v) dwu_state \<Rightarrow> bool" where
  "retained_prefix_covered f t \<longleftrightarrow>
     set (replay_down_hist (take (dwu_floor t) (exec_src_hist (dwu_store t)))
            (exec_scope (dwu_store t)) f)
       \<subseteq> set (log_payloads (dwu_accepted t))"

text \<open>@{const replay_down_hist} is a filter, so it distributes over append.\<close>

lemma replay_down_hist_append:
  "replay_down_hist (H1 @ H2) K f = replay_down_hist H1 K f @ replay_down_hist H2 K f"
  by (simp add: replay_down_hist_def)

theorem retention_sound_bridge:
  assumes eo: "u_exactly_once_at f t"
      and cov: "retained_prefix_covered f t"
      and js: "dwu_journal t = exec_src_hist (dwu_store t)"
  shows "u_exactly_once_journal_at f t"
proof -
  have split: "dwu_journal t
             = take (dwu_floor t) (exec_src_hist (dwu_store t)) @ retained_hist t"
    unfolding retained_hist_def js by (rule append_take_drop_id[symmetric])
  have pfx: "set (replay_down_hist (take (dwu_floor t) (exec_src_hist (dwu_store t)))
                   (exec_scope (dwu_store t)) f)
               \<subseteq> set (log_payloads (dwu_accepted t))"
    using cov by (simp add: retained_prefix_covered_def)
  have sfx: "set (replay_down_hist (retained_hist t) (exec_scope (dwu_store t)) f)
               \<subseteq> set (log_payloads (dwu_accepted t))"
    using eo by (simp add: u_exactly_once_at_def u_at_least_once_at_def)
  have safe: "\<not> u_effect_unsafe t"
    using eo by (simp add: u_exactly_once_at_def)
  show ?thesis
    unfolding u_exactly_once_journal_at_def
    by (subst split) (use safe pfx sfx in \<open>auto simp: replay_down_hist_append\<close>)
qed


section \<open>4. Disciplined journals are the source history\<close>

text \<open>The discipline's safety invariant already carries journal = source as its
  C3 conjunct (@{text u_disc_inv}, no truncation inside a disciplined trace);
  harvest it through the landed preservation induction.\<close>

lemma disciplined_journal_is_source:
  assumes "u_disciplined_trace (dwu_init b K fin) acts t"
  shows "dwu_journal t = exec_src_hist (dwu_store t)"
  using u_disc_inv_pres[OF assms u_disc_inv_init] by (rule u_disc_invD(3))

corollary disciplined_retention_sound_journal_grade:
  assumes "u_disciplined_trace (dwu_init b K fin) acts t"
      and "u_exactly_once_at f t"
      and "retained_prefix_covered f t"
  shows "u_exactly_once_journal_at f t"
  by (rule retention_sound_bridge[OF assms(2) assms(3)
        disciplined_journal_is_source[OF assms(1)]])


section \<open>5. The divergence control (the banked external-review run)\<close>

text \<open>The external review's counterexample, banked as a permanent in-corpus
  control pricing the disclosure: a five-action disciplined run --- commit
  @{text "(ec1, e1)"}; @{const URetain} 1; crash; empty claim; fire --- whose
  endpoint the headline certifies @{const u_exactly_once_at} while
  @{const u_lost_journal} holds (and the retained-surface @{const u_lost} does
  not).  The retention dropped the committed journal obligation before the
  claim read the state, so the armed batch is empty and nothing is accepted.\<close>

definition jg_acts :: "(nat, nat) dwu_action list" where
  "jg_acts = [ULift 0 (DoSource ec1 e1), URetain (Suc 0), ULift 0 (Crash ec2),
              UArmF 0 ec2, UFire 0]"

definition jg2 :: "(nat, nat) dwu_state" where
  "jg2 = uW1\<lparr>dwu_floor := Suc 0\<rparr>"

definition jg3 :: "(nat, nat) dwu_state" where
  "jg3 = cw2\<lparr>dwu_floor := Suc 0\<rparr>"

definition jg4 :: "(nat, nat) dwu_state" where
  "jg4 = jg3\<lparr>dwu_fence := 0,
             dwu_gens := (dwu_gens jg3)(0 \<mapsto> UArmed [])\<rparr>"

subsection \<open>5.1 Machine steps\<close>

lemma jg_step_retain: "dwu_step uW1 (URetain (Suc 0)) jg2"
proof -
  have "dwu_step uW1 (URetain (Suc 0)) (uW1\<lparr>dwu_floor := Suc 0\<rparr>)"
    by (rule dwu_step.uretain) (simp_all add: uW1_def mkU_def mkC_def)
  then show ?thesis by (simp add: jg2_def)
qed

lemma jg2_store: "dwu_store jg2 = dwu_store uW1"
  by (simp add: jg2_def)

lemma jg_wf2: "wellformed_exec_state (dwu_store jg2)"
  by (simp add: jg2_store rf_wf1)

lemma jg_g_crash: "exec_label_preserves_history_wf (dwu_store jg2) (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma jg_step_crash: "dwu_step jg2 (ULift 0 (Crash ec2)) jg3"
proof -
  have c: "dw_exec_step (dwu_store jg2) (Crash ec2)
             (mkC [(ec1, e1)] [] [] {} (Crashed ec2))"
    by (rule crashI) (simp_all add: jg2_def uW1_def mkU_def mkC_def)
  have "dwu_step jg2 (ULift 0 (Crash ec2))
          (jg2\<lparr>dwu_store := mkC [(ec1, e1)] [] [] {} (Crashed ec2)\<rparr>)"
    by (rule dwu_step.ulift_nonprod[OF _ _ c])
       (simp_all add: jg2_def uW1_def mkU_def)
  also have "jg2\<lparr>dwu_store := mkC [(ec1, e1)] [] [] {} (Crashed ec2)\<rparr> = jg3"
    by (simp add: jg2_def jg3_def uW1_def cw2_def mkU_def)
  finally show ?thesis .
qed

text \<open>The retained suffix at the crashed state is empty, so the armed sink
  delta is empty --- the committed journal obligation has been retained away.\<close>

lemma jg3_retained: "retained_hist jg3 = []"
  by (simp add: retained_hist_def jg3_def cw2_def mkU_def mkC_def)

lemma jg3_delta: "u_sink_delta ec2 jg3 = []"
  by (simp add: u_sink_delta_def jg3_retained replay_down_hist_def)

lemma jg3_journal: "dwu_journal jg3 = [(ec1, e1)]"
  by (simp add: jg3_def cw2_def mkU_def)

lemma jg3_batch:
  "stamped_at (length (dwu_journal jg3)) 0 (u_sink_delta ec2 jg3) = []"
  by (simp add: jg3_delta stamped_at_def)

lemma jg_step_arm: "dwu_step jg3 (UArmF 0 ec2) jg4"
proof -
  have dom0: "0 \<in> dom (dwu_gens jg3)" by (simp add: jg3_def cw2_def mkU_def)
  have crashed: "\<exists>c. exec_status (dwu_store jg3) = Crashed c"
    by (rule exI[of _ ec2]) (simp add: jg3_def cw2_def mkU_def mkC_def)
  have fin: "ec2 \<le> exec_finish (dwu_store jg3)"
    by (simp add: jg3_def cw2_def mkU_def mkC_def)
  have fence: "dwu_fence jg3 \<le> 0" by (simp add: jg3_def cw2_def mkU_def)
  have "dwu_step jg3 (UArmF 0 ec2)
          (jg3\<lparr>dwu_fence := 0,
               dwu_gens := (dwu_gens jg3)
                 (0 \<mapsto> UArmed (stamped_at (length (dwu_journal jg3)) 0
                                 (u_sink_delta ec2 jg3)))\<rparr>)"
    by (rule dwu_step.uarmf[OF dom0 crashed fin fence])
  then show ?thesis by (simp only: jg3_batch jg4_def)
qed

lemma jg_step_fire: "dwu_step jg4 (UFire 0) jg3"
proof -
  have g: "dwu_gens jg4 0 = Some (UArmed [])"
    by (simp add: jg4_def)
  have "dwu_step jg4 (UFire 0)
          (jg4\<lparr>dwu_sent := dwu_sent jg4 @ [],
               dwu_accepted := dwu_accepted jg4
                 @ (if dwu_fence jg4 \<le> 0 then [] else []),
               dwu_gens := (dwu_gens jg4)(0 \<mapsto> UProd)\<rparr>)"
    by (rule dwu_step.ufire[OF g])
  also have "jg4\<lparr>dwu_sent := dwu_sent jg4 @ [],
               dwu_accepted := dwu_accepted jg4
                 @ (if dwu_fence jg4 \<le> 0 then [] else []),
               dwu_gens := (dwu_gens jg4)(0 \<mapsto> UProd)\<rparr> = jg3"
    by (simp add: jg4_def jg3_def cw2_def mkU_def fun_upd_upd)
  finally show ?thesis .
qed

subsection \<open>5.2 The disciplined trace\<close>

lemma jg_disciplined: "u_disciplined_trace uW0 jg_acts jg3"
  unfolding jg_acts_def
proof -
  have d5: "u_disciplined_trace jg3 [] jg3"
    by (rule u_disciplined_trace.ud_refl)
  have d4: "u_disciplined_trace jg4 [UFire 0] jg3"
    by (rule u_disciplined_trace.ud_fire[OF jg_step_fire d5])
  have guard: "distinct (log_payloads
                 (stamped_at (length (dwu_journal jg3)) 0 (u_sink_delta ec2 jg3)))"
    by (simp add: jg3_batch log_payloads_def map_filter_simps)
  have d3: "u_disciplined_trace jg3 [UArmF 0 ec2, UFire 0] jg3"
    by (rule u_disciplined_trace.ud_claim[OF guard jg_step_arm d4])
  have d2: "u_disciplined_trace jg2 [ULift 0 (Crash ec2), UArmF 0 ec2, UFire 0] jg3"
    by (rule u_disciplined_trace.ud_nonpub[OF jg_wf2 jg_g_crash _ jg_step_crash d3])
       simp
  have d1: "u_disciplined_trace uW1
              [URetain (Suc 0), ULift 0 (Crash ec2), UArmF 0 ec2, UFire 0] jg3"
    by (rule u_disciplined_trace.ud_retain[OF jg_step_retain d2])
  show "u_disciplined_trace uW0
          [ULift 0 (DoSource ec1 e1), URetain (Suc 0), ULift 0 (Crash ec2),
           UArmF 0 ec2, UFire 0] jg3"
    by (rule u_disciplined_trace.ud_nonpub[OF rf_wf0 rf_g0 _ rf_step0 d1]) simp
qed

lemma jg_disciplined_init:
  "u_disciplined_trace (dwu_init Map.empty {0, 1} ec2) jg_acts jg3"
  using jg_disciplined unfolding rf_uW0_init .

subsection \<open>5.3 The temporal prefixes, the claim window, and the fence premise\<close>

lemma jg_temporal_pre: "dwu_temporal_trace uW0 (take 4 jg_acts) jg4"
proof -
  have t4: "dwu_temporal_trace jg4 [] jg4" by (rule dwu_temporal_trace.dwu_refl)
  have t3: "dwu_temporal_trace jg3 [UArmF 0 ec2] jg4"
    by (rule dwu_temporal_trace.dwu_other_step[OF _ _ jg_step_arm t4]) simp_all
  have t2: "dwu_temporal_trace jg2 [ULift 0 (Crash ec2), UArmF 0 ec2] jg4"
    by (rule dwu_temporal_trace.dwu_lift_step[OF jg_wf2 jg_g_crash jg_step_crash t3])
  have t1: "dwu_temporal_trace uW1
              [URetain (Suc 0), ULift 0 (Crash ec2), UArmF 0 ec2] jg4"
    by (rule dwu_temporal_trace.dwu_other_step[OF _ _ jg_step_retain t2]) simp_all
  show ?thesis
    unfolding jg_acts_def
    by simp (rule dwu_temporal_trace.dwu_lift_step[OF rf_wf0 rf_g0 rf_step0 t1])
qed

lemma jg_temporal_post: "dwu_temporal_trace uW0 (take (Suc 4) jg_acts) jg3"
proof -
  have t5: "dwu_temporal_trace jg3 [] jg3" by (rule dwu_temporal_trace.dwu_refl)
  have t4: "dwu_temporal_trace jg4 [UFire 0] jg3"
    by (rule dwu_temporal_trace.dwu_other_step[OF _ _ jg_step_fire t5]) simp_all
  have t3: "dwu_temporal_trace jg3 [UArmF 0 ec2, UFire 0] jg3"
    by (rule dwu_temporal_trace.dwu_other_step[OF _ _ jg_step_arm t4]) simp_all
  have t2: "dwu_temporal_trace jg2
              [ULift 0 (Crash ec2), UArmF 0 ec2, UFire 0] jg3"
    by (rule dwu_temporal_trace.dwu_lift_step[OF jg_wf2 jg_g_crash jg_step_crash t3])
  have t1: "dwu_temporal_trace uW1
              [URetain (Suc 0), ULift 0 (Crash ec2), UArmF 0 ec2, UFire 0] jg3"
    by (rule dwu_temporal_trace.dwu_other_step[OF _ _ jg_step_retain t2]) simp_all
  show ?thesis
    unfolding jg_acts_def
    by simp (rule dwu_temporal_trace.dwu_lift_step[OF rf_wf0 rf_g0 rf_step0 t1])
qed

lemma jg_temporal_pre_init:
  "dwu_temporal_trace (dwu_init Map.empty {0, 1} ec2) (take 4 jg_acts) jg4"
  using jg_temporal_pre unfolding rf_uW0_init .

lemma jg_temporal_post_init:
  "dwu_temporal_trace (dwu_init Map.empty {0, 1} ec2) (take (Suc 4) jg_acts) jg3"
  using jg_temporal_post unfolding rf_uW0_init .

lemma jg_claim: "u_claim_of jg_acts 3 4 0 ec2"
proof -
  have len: "length jg_acts = 5" by (simp add: jg_acts_def)
  have n3: "jg_acts ! 3 = UArmF 0 ec2" by (simp add: jg_acts_def)
  have n4: "jg_acts ! 4 = UFire 0" by (simp add: jg_acts_def)
  have mid: "\<forall>n. 3 < n \<and> n < 4 \<longrightarrow>
        jg_acts ! n \<noteq> UFire 0 \<and> (\<forall>f'. jg_acts ! n \<noteq> UArmF 0 f')"
    by (intro allI impI) linarith
  show ?thesis using len n3 n4 mid by (simp add: u_claim_of_def)
qed

lemma jg_fresh: "u_window_fresh jg_acts 3 4 ec2"
  unfolding u_window_fresh_def by (intro allI impI) linarith

lemma jg_fence_pre: "dwu_fence jg4 \<le> 0"
  by (simp add: jg4_def jg3_def cw2_def mkU_def)

subsection \<open>5.4 The banked verdicts\<close>

text \<open>1. The headline theorem applies to the retention run and certifies
  exactly-once at the endpoint.\<close>

theorem jg_headline_applies: "u_exactly_once_at ec2 jg3"
  by (rule u_exactly_once_at_completed_claim[OF jg_disciplined_init jg_claim
        jg_fresh jg_temporal_pre_init jg_fence_pre jg_temporal_post_init])

text \<open>2. Cross-check by direct evaluation: nothing was accepted, and the
  retained owed set is empty.\<close>

lemma jg_direct_eval: "u_exactly_once_at ec2 jg3"
  by (simp add: u_exactly_once_at_def u_effect_unsafe_def u_premature_def
                u_duplicate_def u_at_least_once_at_def retained_hist_def
                replay_down_hist_def log_payloads_def map_filter_simps
                jg3_def cw2_def mkU_def mkC_def)

text \<open>3. The journal-graded loss predicate holds at the same endpoint: the
  committed obligation @{text "(ec1, e1)"} is replayed by the full journal and
  is not among the accepted log payloads.\<close>

lemma jg_lost_journal: "u_lost_journal ec2 jg3"
  by (simp add: u_lost_journal_def jg3_def cw2_def mkU_def mkC_def
                replay_down_hist_def log_payloads_def map_filter_simps
                e1_def ec_defs)

text \<open>4. The retained-surface loss predicate does NOT hold --- the divergence
  between the two loss surfaces is exactly the retention.\<close>

lemma jg_not_lost_retained: "\<not> u_lost ec2 jg3"
  by (simp add: u_lost_def jg3_retained replay_down_hist_def)

text \<open>5. Nothing was ever accepted: the certified claim is empty.\<close>

lemma jg_accepted_empty: "dwu_accepted jg3 = []"
  by (simp add: jg3_def cw2_def mkU_def)

text \<open>6. Priced in this theory's own vocabulary: the endpoint fails the
  journal-graded verdict, and it fails the bridge's coverage premise --- the
  floor dropped an obligation that was never accepted.\<close>

lemma jg_not_journal_grade: "\<not> u_exactly_once_journal_at ec2 jg3"
  using jg_lost_journal by (simp add: u_exactly_once_journal_at_alt)

lemma jg_retained_prefix_not_covered: "\<not> retained_prefix_covered ec2 jg3"
  by (simp add: retained_prefix_covered_def jg3_def cw2_def mkU_def mkC_def
                replay_down_hist_def log_payloads_def map_filter_simps
                e1_def ec_defs)

text \<open>THE BANKED BUNDLE: one disciplined completed-claim run whose endpoint the
  headline certifies exactly-once while the development's own journal-graded
  loss predicate reports a lost committed obligation.\<close>

theorem journal_grade_divergence_control:
  "u_disciplined_trace (dwu_init Map.empty {0, 1} ec2) jg_acts jg3
 \<and> u_exactly_once_at ec2 jg3
 \<and> u_lost_journal ec2 jg3
 \<and> \<not> u_lost ec2 jg3
 \<and> dwu_accepted jg3 = []"
  by (intro conjI jg_disciplined_init jg_headline_applies jg_lost_journal
        jg_not_lost_retained jg_accepted_empty)


section \<open>6. The trace-level retention-soundness carrier\<close>

text \<open>A run-level predicate isolating WHEN retention keeps the journal grade:
  every @{const URetain} step may only drop obligations that are already
  accepted at that step, at every frontier within finish (the finish is
  trace-constant by @{text u_exec_finish_const}).  @{const UTruncCrash} is
  excluded exactly as the discipline grammar excludes it; every other action
  is admitted unguarded.  Such runs deliver @{const retained_prefix_covered}
  at the endpoint, which is the retention-sound bridge's coverage premise.\<close>

inductive u_retention_sound_steps
  :: "('k, 'v) dwu_state \<Rightarrow> ('k, 'v) dwu_action list \<Rightarrow> ('k, 'v) dwu_state \<Rightarrow> bool"
where
  urs_refl:
    "u_retention_sound_steps t [] t"
| urs_step:
    "\<lbrakk>\<forall>d c. \<alpha> \<noteq> UTruncCrash d c; \<forall>n. \<alpha> \<noteq> URetain n;
      dwu_step t \<alpha> t';
      u_retention_sound_steps t' as t''\<rbrakk> \<Longrightarrow>
     u_retention_sound_steps t (\<alpha> # as) t''"
| urs_retain:
    "\<lbrakk>\<forall>f. f \<le> exec_finish (dwu_store t) \<longrightarrow>
        set (replay_down_hist (drop (dwu_floor t) (take n (exec_src_hist (dwu_store t))))
               (exec_scope (dwu_store t)) f)
          \<subseteq> set (log_payloads (dwu_accepted t));
      dwu_step t (URetain n) t';
      u_retention_sound_steps t' as t''\<rbrakk> \<Longrightarrow>
     u_retention_sound_steps t (URetain n # as) t''"

text \<open>The retain-step inversion beyond the landed frame: the floor lands at
  @{text n}, bounded by the old floor and the source-history length.\<close>

lemma dwu_step_retain_bounds:
  assumes "dwu_step t (URetain n) t'"
  shows "dwu_floor t \<le> n \<and> n \<le> length (exec_src_hist (dwu_store t))
       \<and> dwu_floor t' = n"
  using assms by (cases rule: dwu_step.cases) auto

text \<open>The covering induction: the floor prefix is frozen by every non-retain
  step (no truncation, so the source history only grows above it), the
  accepted ledger only grows, and a guarded retain extends the covered prefix
  by exactly its guarded segment.\<close>

lemma u_retention_sound_steps_covered:
  "u_retention_sound_steps s acts t \<Longrightarrow>
   dwu_floor s \<le> length (exec_src_hist (dwu_store s)) \<Longrightarrow>
   f \<le> exec_finish (dwu_store s) \<Longrightarrow>
   retained_prefix_covered f s \<Longrightarrow>
   retained_prefix_covered f t"
proof (induction rule: u_retention_sound_steps.induct)
  case (urs_refl t)
  then show ?case by blast
next
  case (urs_step \<alpha> t t' as t'')
  have sc: "exec_scope (dwu_store t') = exec_scope (dwu_store t)"
    by (rule u_exec_scope_const[OF urs_step.hyps(3)])
  have fin: "exec_finish (dwu_store t') = exec_finish (dwu_store t)"
    by (rule u_exec_finish_const[OF urs_step.hyps(3)])
  have acc: "set (log_payloads (dwu_accepted t)) \<subseteq> set (log_payloads (dwu_accepted t'))"
    by (rule u_step_accepted_set_mono[OF urs_step.hyps(3)])
  from u_step_owed_ingredients[OF urs_step.hyps(3)] urs_step.hyps(1,2)
  have shape:
    "(exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t)
        \<and> dwu_floor t' = dwu_floor t)
   \<or> (\<exists>c e. exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t) @ [(c, e)]
        \<and> dwu_floor t' = dwu_floor t)"
    by blast
  have pfx_len: "take (dwu_floor t') (exec_src_hist (dwu_store t'))
               = take (dwu_floor t) (exec_src_hist (dwu_store t))
             \<and> dwu_floor t' \<le> length (exec_src_hist (dwu_store t'))"
    using shape
  proof (elim disjE)
    assume "exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t)
          \<and> dwu_floor t' = dwu_floor t"
    with urs_step.prems(1) show ?thesis by simp
  next
    assume "\<exists>c e. exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t) @ [(c, e)]
          \<and> dwu_floor t' = dwu_floor t"
    then obtain c e where
      A: "exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t) @ [(c, e)]"
      and B: "dwu_floor t' = dwu_floor t" by blast
    have z: "dwu_floor t - length (exec_src_hist (dwu_store t)) = 0"
      using urs_step.prems(1) by linarith
    have p1: "take (dwu_floor t') (exec_src_hist (dwu_store t'))
            = take (dwu_floor t) (exec_src_hist (dwu_store t))"
      by (simp add: A B z)
    have p2: "dwu_floor t' \<le> length (exec_src_hist (dwu_store t'))"
    proof -
      have "length (exec_src_hist (dwu_store t'))
          = Suc (length (exec_src_hist (dwu_store t)))"
        by (simp add: A)
      then show ?thesis using urs_step.prems(1) B by linarith
    qed
    show ?thesis by (rule conjI[OF p1 p2])
  qed
  have cov': "retained_prefix_covered f t'"
  proof -
    have "set (replay_down_hist (take (dwu_floor t') (exec_src_hist (dwu_store t')))
                (exec_scope (dwu_store t')) f)
        = set (replay_down_hist (take (dwu_floor t) (exec_src_hist (dwu_store t)))
                (exec_scope (dwu_store t)) f)"
      by (simp add: pfx_len[THEN conjunct1] sc)
    also have "\<dots> \<subseteq> set (log_payloads (dwu_accepted t))"
      using urs_step.prems(3) by (simp add: retained_prefix_covered_def)
    also have "\<dots> \<subseteq> set (log_payloads (dwu_accepted t'))" by (rule acc)
    finally show ?thesis by (simp add: retained_prefix_covered_def)
  qed
  have fin': "f \<le> exec_finish (dwu_store t')"
    using urs_step.prems(2) fin by simp
  show ?case
    by (rule urs_step.IH[OF pfx_len[THEN conjunct2] fin' cov'])
next
  case (urs_retain t n t' as t'')
  note frame = dwu_step_retain_full[OF urs_retain.hyps(2)]
  note bnds = dwu_step_retain_bounds[OF urs_retain.hyps(2)]
  let ?H = "exec_src_hist (dwu_store t)"
  have splitH: "take n ?H
              = take (dwu_floor t) ?H @ drop (dwu_floor t) (take n ?H)"
  proof -
    have "take (dwu_floor t) (take n ?H) @ drop (dwu_floor t) (take n ?H) = take n ?H"
      by (rule append_take_drop_id)
    moreover have "take (dwu_floor t) (take n ?H) = take (dwu_floor t) ?H"
      using bnds by (simp add: min.absorb1)
    ultimately show ?thesis by simp
  qed
  have pre: "set (replay_down_hist (take (dwu_floor t) ?H) (exec_scope (dwu_store t)) f)
               \<subseteq> set (log_payloads (dwu_accepted t))"
    using urs_retain.prems(3) by (simp add: retained_prefix_covered_def)
  have seg: "set (replay_down_hist (drop (dwu_floor t) (take n ?H))
                    (exec_scope (dwu_store t)) f)
               \<subseteq> set (log_payloads (dwu_accepted t))"
    using urs_retain.hyps(1)[rule_format, OF urs_retain.prems(2)] .
  have cov': "retained_prefix_covered f t'"
  proof -
    have "set (replay_down_hist (take (dwu_floor t') (exec_src_hist (dwu_store t')))
                (exec_scope (dwu_store t')) f)
        = set (replay_down_hist (take n ?H) (exec_scope (dwu_store t)) f)"
      by (simp add: frame bnds)
    also have "\<dots> = set (replay_down_hist (take (dwu_floor t) ?H)
                          (exec_scope (dwu_store t)) f)
                  \<union> set (replay_down_hist (drop (dwu_floor t) (take n ?H))
                          (exec_scope (dwu_store t)) f)"
      by (subst splitH) (simp add: replay_down_hist_append)
    also have "\<dots> \<subseteq> set (log_payloads (dwu_accepted t))"
      using pre seg by blast
    finally have "set (replay_down_hist
                        (take (dwu_floor t') (exec_src_hist (dwu_store t')))
                        (exec_scope (dwu_store t')) f)
                    \<subseteq> set (log_payloads (dwu_accepted t))" .
    then show ?thesis by (simp add: retained_prefix_covered_def frame)
  qed
  have len': "dwu_floor t' \<le> length (exec_src_hist (dwu_store t'))"
    by (simp add: frame bnds)
  have fin': "f \<le> exec_finish (dwu_store t')"
    using urs_retain.prems(2) by (simp add: frame)
  show ?case
    by (rule urs_retain.IH[OF len' fin' cov'])
qed

text \<open>From the pinned init the side conditions are free: floor 0, empty source
  history, and the store's finish is the init parameter.\<close>

theorem u_retention_sound_run_covered:
  assumes "u_retention_sound_steps (dwu_init b K fin) acts t"
      and "f \<le> fin"
  shows "retained_prefix_covered f t"
proof (rule u_retention_sound_steps_covered[OF assms(1)])
  show "dwu_floor (dwu_init b K fin)
          \<le> length (exec_src_hist (dwu_store (dwu_init b K fin)))"
    by (simp add: dwu_init_def initial_exec_state_def)
  show "f \<le> exec_finish (dwu_store (dwu_init b K fin))"
    using assms(2) by (simp add: dwu_init_def initial_exec_state_def)
  show "retained_prefix_covered f (dwu_init b K fin)"
    by (simp add: retained_prefix_covered_def dwu_init_def initial_exec_state_def
                  replay_down_hist_def)
qed

corollary retention_sound_run_journal_grade:
  assumes "u_disciplined_trace (dwu_init b K fin) acts t"
      and "u_retention_sound_steps (dwu_init b K fin) acts t"
      and "f \<le> fin"
      and "u_exactly_once_at f t"
  shows "u_exactly_once_journal_at f t"
  by (rule disciplined_retention_sound_journal_grade[OF assms(1) assms(4)
        u_retention_sound_run_covered[OF assms(2) assms(3)]])

subsection \<open>6.1 The positive control: publish, then retain, keeps the journal grade\<close>

text \<open>The same retention action as the divergence run, taken AFTER the
  committed obligation was delivered: commit @{text "(ec1, e1)"}; enqueue;
  publish (accepted); @{const URetain} 1.  The run is disciplined AND
  retention-sound, so the capstone corollary certifies the journal grade at
  the endpoint --- the carrier is exactly the discriminator between this run
  and the banked divergence run.\<close>

definition jr_acts :: "(nat, nat) dwu_action list" where
  "jr_acts = [ULift 0 (DoSource ec1 e1), ULift 0 (EnqueueDownstream ec1 e1),
              ULift 0 (DoDownstream ec1 e1), URetain (Suc 0)]"

definition jr4 :: "(nat, nat) dwu_state" where
  "jr4 = uW3\<lparr>dwu_floor := Suc 0\<rparr>"

lemma jr_step_retain: "dwu_step uW3 (URetain (Suc 0)) jr4"
proof -
  have "dwu_step uW3 (URetain (Suc 0)) (uW3\<lparr>dwu_floor := Suc 0\<rparr>)"
    by (rule dwu_step.uretain) (simp_all add: uW3_def mkU_def mkC_def)
  then show ?thesis by (simp add: jr4_def)
qed

lemma jr_retain_guard:
  "\<forall>f. f \<le> exec_finish (dwu_store uW3) \<longrightarrow>
     set (replay_down_hist
            (drop (dwu_floor uW3) (take (Suc 0) (exec_src_hist (dwu_store uW3))))
            (exec_scope (dwu_store uW3)) f)
       \<subseteq> set (log_payloads (dwu_accepted uW3))"
proof (intro allI impI)
  fix f :: frontier
  have seg: "drop (dwu_floor uW3) (take (Suc 0) (exec_src_hist (dwu_store uW3)))
           = [(ec1, e1)]"
    by (simp add: uW3_def mkU_def mkC_def)
  have acc: "set (log_payloads (dwu_accepted uW3)) = {(ec1, e1)}"
    by (simp add: uW3_def mkU_def rf_x1_def log_payloads_def map_filter_simps)
  have "set (replay_down_hist [(ec1, e1)] (exec_scope (dwu_store uW3)) f)
          \<subseteq> {(ec1, e1)}"
    using replay_subset[of "[(ec1, e1)]" "exec_scope (dwu_store uW3)" f] by simp
  then show "set (replay_down_hist
                   (drop (dwu_floor uW3) (take (Suc 0) (exec_src_hist (dwu_store uW3))))
                   (exec_scope (dwu_store uW3)) f)
               \<subseteq> set (log_payloads (dwu_accepted uW3))"
    by (simp add: seg acc)
qed

lemma jr_retention_sound: "u_retention_sound_steps uW0 jr_acts jr4"
  unfolding jr_acts_def
proof -
  have d4: "u_retention_sound_steps jr4 [] jr4"
    by (rule u_retention_sound_steps.urs_refl)
  have d3: "u_retention_sound_steps uW3 [URetain (Suc 0)] jr4"
    by (rule u_retention_sound_steps.urs_retain[OF jr_retain_guard jr_step_retain d4])
  have d2: "u_retention_sound_steps uW2
              [ULift 0 (DoDownstream ec1 e1), URetain (Suc 0)] jr4"
    by (rule u_retention_sound_steps.urs_step[OF _ _ rf_step2 d3]) simp_all
  have d1: "u_retention_sound_steps uW1
              [ULift 0 (EnqueueDownstream ec1 e1), ULift 0 (DoDownstream ec1 e1),
               URetain (Suc 0)] jr4"
    by (rule u_retention_sound_steps.urs_step[OF _ _ rf_step1 d2]) simp_all
  show "u_retention_sound_steps uW0
          [ULift 0 (DoSource ec1 e1), ULift 0 (EnqueueDownstream ec1 e1),
           ULift 0 (DoDownstream ec1 e1), URetain (Suc 0)] jr4"
    by (rule u_retention_sound_steps.urs_step[OF _ _ rf_step0 d1]) simp_all
qed

lemma jr_disciplined: "u_disciplined_trace uW0 jr_acts jr4"
  unfolding jr_acts_def
proof -
  have d4: "u_disciplined_trace jr4 [] jr4"
    by (rule u_disciplined_trace.ud_refl)
  have d3: "u_disciplined_trace uW3 [URetain (Suc 0)] jr4"
    by (rule u_disciplined_trace.ud_retain[OF jr_step_retain d4])
  have d2: "u_disciplined_trace uW2
              [ULift 0 (DoDownstream ec1 e1), URetain (Suc 0)] jr4"
    by (rule u_disciplined_trace.ud_publish[OF rf_wf2 rf_g2 _ _ _ rf_step2 d3])
       (simp_all add: uW2_def mkU_def mkC_def log_payloads_def map_filter_simps)
  have d1: "u_disciplined_trace uW1
              [ULift 0 (EnqueueDownstream ec1 e1), ULift 0 (DoDownstream ec1 e1),
               URetain (Suc 0)] jr4"
    by (rule u_disciplined_trace.ud_nonpub[OF rf_wf1 rf_g1 _ rf_step1 d2]) simp
  show "u_disciplined_trace uW0
          [ULift 0 (DoSource ec1 e1), ULift 0 (EnqueueDownstream ec1 e1),
           ULift 0 (DoDownstream ec1 e1), URetain (Suc 0)] jr4"
    by (rule u_disciplined_trace.ud_nonpub[OF rf_wf0 rf_g0 _ rf_step0 d1]) simp
qed

lemma jr_retention_sound_init:
  "u_retention_sound_steps (dwu_init Map.empty {0, 1} ec2) jr_acts jr4"
  using jr_retention_sound unfolding rf_uW0_init .

lemma jr_disciplined_init:
  "u_disciplined_trace (dwu_init Map.empty {0, 1} ec2) jr_acts jr4"
  using jr_disciplined unfolding rf_uW0_init .

text \<open>The endpoint verdicts: coverage BY the carrier theorem, cross-checked by
  direct evaluation; the retained-graded verdict by direct evaluation; and the
  journal grade BY the capstone corollary, cross-checked by direct evaluation.
  The journal replay at the endpoint is nonempty, so the journal-grade
  conjunct is load-bearing, not vacuous.\<close>

lemma jr_prefix_covered: "retained_prefix_covered ec2 jr4"
  by (rule u_retention_sound_run_covered[OF jr_retention_sound_init]) simp

lemma jr_prefix_covered_direct: "retained_prefix_covered ec2 jr4"
  by (simp add: retained_prefix_covered_def jr4_def uW3_def mkU_def mkC_def
                replay_down_hist_def log_payloads_def map_filter_simps
                rf_x1_def e1_def ec_defs)

lemma jr_exactly_once: "u_exactly_once_at ec2 jr4"
  by (simp add: u_exactly_once_at_def u_effect_unsafe_def u_premature_def
                u_duplicate_def u_justified_def u_at_least_once_at_def
                retained_hist_def replay_down_hist_def log_payloads_def
                map_filter_simps jr4_def uW3_def mkU_def mkC_def
                rf_x1_def e1_def ec_defs)

theorem jr_journal_grade: "u_exactly_once_journal_at ec2 jr4"
  by (rule retention_sound_run_journal_grade[OF jr_disciplined_init
        jr_retention_sound_init _ jr_exactly_once]) simp

lemma jr_journal_grade_direct: "u_exactly_once_journal_at ec2 jr4"
  by (simp add: u_exactly_once_journal_at_def u_effect_unsafe_def u_premature_def
                u_duplicate_def u_justified_def replay_down_hist_def
                log_payloads_def map_filter_simps jr4_def uW3_def mkU_def
                mkC_def rf_x1_def e1_def ec_defs)


section \<open>7. The endpoint exchange rate and the nonempty journal-grade control\<close>

text \<open>Two review-accepted strengthenings close the theory.

  First, under journal = source the sufficiency bridge is half of an
  equivalence: the theorem below states the journal/retained EXCHANGE RATE at
  the endpoint --- @{const u_exactly_once_journal_at} holds iff the
  retained-graded @{const u_exactly_once_at} and
  @{const retained_prefix_covered} both hold.  @{text retention_sound_bridge}
  is exactly the backward direction; the forward direction splits the journal
  replay at @{const dwu_floor} via @{text replay_down_hist_append} (the
  journal is the floor prefix followed by @{const retained_hist}), so journal
  coverage yields the floor-prefix and retained-suffix coverages, and the
  safety conjunct is shared verbatim.

  Second, the journal-graded headline
  @{text u_exactly_once_at_completed_claim_journal} is exercised on the
  NONEMPTY banked claim witness of @{text DWU_Claim_Witness}: the six landed
  completed-claim premises are consumed unchanged, and the added
  @{const u_permanent_source} premise evaluates away at the endpoint (journal
  @{text "[(ec1, e1)]"} = source history, floor 0).  This is the positive
  regression control at NONZERO payload --- complementing the
  retention-carrier control of section 6.1, whose journal grade rests on the
  carrier rather than on the headline.\<close>

theorem journal_grade_iff_retained_grade_and_prefix_covered:
  assumes js: "dwu_journal t = exec_src_hist (dwu_store t)"
  shows "u_exactly_once_journal_at f t
           \<longleftrightarrow> (u_exactly_once_at f t \<and> retained_prefix_covered f t)"
proof
  assume jg: "u_exactly_once_journal_at f t"
  have split: "dwu_journal t
             = take (dwu_floor t) (exec_src_hist (dwu_store t)) @ retained_hist t"
    unfolding retained_hist_def js by (rule append_take_drop_id[symmetric])
  have safe: "\<not> u_effect_unsafe t"
    using jg by (simp add: u_exactly_once_journal_at_def)
  have jcov: "set (replay_down_hist (dwu_journal t) (exec_scope (dwu_store t)) f)
                \<subseteq> set (log_payloads (dwu_accepted t))"
    using jg by (simp add: u_exactly_once_journal_at_def)
  have both: "set (replay_down_hist (take (dwu_floor t) (exec_src_hist (dwu_store t)))
                    (exec_scope (dwu_store t)) f)
                \<subseteq> set (log_payloads (dwu_accepted t))
            \<and> set (replay_down_hist (retained_hist t) (exec_scope (dwu_store t)) f)
                \<subseteq> set (log_payloads (dwu_accepted t))"
    using jcov by (simp add: split replay_down_hist_append)
  show "u_exactly_once_at f t \<and> retained_prefix_covered f t"
    using safe both
    by (auto simp: u_exactly_once_at_def u_at_least_once_at_def
                   retained_prefix_covered_def)
next
  assume rc: "u_exactly_once_at f t \<and> retained_prefix_covered f t"
  show "u_exactly_once_journal_at f t"
    by (rule retention_sound_bridge[OF rc[THEN conjunct1] rc[THEN conjunct2] js])
qed

text \<open>The added premise of the journal headline, evaluated at the banked
  claim-witness endpoint.\<close>

lemma cw4_permanent_source: "u_permanent_source cw4"
  by (simp add: u_permanent_source_def cw4_def mkU_def mkC_def)

text \<open>The journal-graded verdict on the nonempty claim witness, BY the journal
  headline: the six landed premises of @{text DWU_Claim_Witness} plus the
  evaluated permanent-source premise.\<close>

theorem cw4_completed_claim_journal_grade: "u_exactly_once_journal_at ec2 cw4"
  by (rule u_exactly_once_at_completed_claim_journal[OF cw_disciplined_init
        cw_claim cw_fresh cw_temporal_pre_init cw_fence_pre
        cw_temporal_post_init cw4_permanent_source])

text \<open>Cross-check by direct evaluation of the closed end-state.\<close>

lemma cw4_completed_claim_journal_grade_direct:
  "u_exactly_once_journal_at ec2 cw4"
  by (simp add: u_exactly_once_journal_at_def u_effect_unsafe_def u_premature_def
                u_duplicate_def u_justified_def replay_down_hist_def
                log_payloads_def map_filter_simps cw4_def mkU_def mkC_def
                rf_x1_def e1_def ec_defs)

end
