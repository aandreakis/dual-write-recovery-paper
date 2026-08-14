(*  Title:       Dual_Write_Characterization.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Capability/exclusion packaging for the source-first crash window.  This
    theory names the exact decomposed capabilities that make the source-first
    bad-crash theorem apply, and records negative controls for tempting
    overclaims such as treating an already-completed downstream write as part of
    the vulnerable class.
*)

theory Dual_Write_Characterization
  imports Dual_Write_Replay_Safety
begin

section \<open>Source-first bad-crash capability class\<close>

definition source_first_crash_capability_window
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) implementation_source_first_gap_witness \<Rightarrow> bool"
where
  "source_first_crash_capability_window I W \<longleftrightarrow>
     dwi_refines_exec I
   \<and> implementation_has_source_first_window I W
   \<and> running_labels (implementation_gap_precrash_labels W)
   \<and> non_atomic_source_effect_window I W
   \<and> isfg_crash_at W < isfg_down_at W
   \<and> source_ack_after_commit W
   \<and> pending_downstream_intent_at_crash I W
   \<and> no_later_source_overwrite_before_crash W
   \<and> no_visible_downstream_effect_at_crash I W"

definition source_first_crash_capability_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "source_first_crash_capability_implementation I \<longleftrightarrow>
     (\<exists>W. source_first_crash_capability_window I W)"

definition source_first_crash_capability_crash_admissible_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "source_first_crash_capability_crash_admissible_implementation I \<longleftrightarrow>
     (\<exists>W.
        source_first_crash_capability_window I W
      \<and> implementation_crash_enabled_for_gap I W)"

definition source_first_crash_capability_crash_closed_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "source_first_crash_capability_crash_closed_implementation I \<longleftrightarrow>
     crash_closed_implementation I
   \<and> (\<exists>W. source_first_crash_capability_window I W)"

text \<open>Definitional bridge, not a mathematical theorem: the two window
  predicates @{const source_first_crash_capability_window} (this theory) and
  @{const adversarial_pending_intent_source_first_window}
  (@{text Dual_Write_Execution}) unfold to the same nine conjuncts, so the
  biconditional below equates two names for one notion.  It is recorded as a
  bridge lemma because three later proofs rewrite with it; it is not an
  equivalence of independently defined notions.\<close>

lemma source_first_crash_capability_window_iff_adversarial_pending_intent:
  "source_first_crash_capability_window I W \<longleftrightarrow>
   adversarial_pending_intent_source_first_window I W"
  by (simp add: source_first_crash_capability_window_def
                adversarial_pending_intent_source_first_window_def)

lemma source_first_crash_capability_window_imp_no_shared_commit_window:
  assumes "source_first_crash_capability_window I W"
  shows "non_atomic_no_shared_commit_source_first_window I W"
  using assms
  by (simp add: source_first_crash_capability_window_iff_adversarial_pending_intent
                adversarial_pending_intent_source_first_window_imp_no_shared_commit_source_first_window)

lemma source_first_crash_capability_window_imp_source_first_gap:
  assumes "source_first_crash_capability_window I W"
  shows "implementation_admits_source_first_gap I W"
  using
    non_atomic_no_shared_commit_source_first_window_imp_implementation_admits_source_first_gap
      [OF source_first_crash_capability_window_imp_no_shared_commit_window
        [OF assms]]
  .

theorem source_first_crash_capability_window_has_abstract_bad_crash_execution:
  assumes window: "source_first_crash_capability_window I W"
  shows "\<exists>s. bad_crash_execution_for_gap
    (operational_gap_of_implementation_gap I W) s"
  using window
  by (simp add: source_first_crash_capability_window_iff_adversarial_pending_intent
                adversarial_pending_intent_source_first_window_has_abstract_bad_crash_execution)

theorem source_first_crash_capability_implementation_has_abstract_bad_crash_execution:
  assumes impl: "source_first_crash_capability_implementation I"
  shows "\<exists>W s.
      source_first_crash_capability_window I W
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I W) s"
proof -
  from impl obtain W where window: "source_first_crash_capability_window I W"
    by (auto simp: source_first_crash_capability_implementation_def)
  from source_first_crash_capability_window_has_abstract_bad_crash_execution
        [OF window]
  obtain s where bad:
    "bad_crash_execution_for_gap (operational_gap_of_implementation_gap I W) s"
    by blast
  from window bad show ?thesis by blast
qed

theorem source_first_crash_capability_crash_admissible_implementation_has_concrete_bad_crash_execution:
  assumes impl: "source_first_crash_capability_crash_admissible_implementation I"
  shows "\<exists>W s.
      source_first_crash_capability_window I W
    \<and> implementation_crash_enabled_for_gap I W
    \<and> dwi_trace I (dwi_initial I) (implementation_gap_crash_labels W) s
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I W) (dwi_state I s)"
proof -
  from impl obtain W where window: "source_first_crash_capability_window I W"
      and crash: "implementation_crash_enabled_for_gap I W"
    by (auto simp:
        source_first_crash_capability_crash_admissible_implementation_def)
  have gap: "implementation_admits_source_first_gap I W"
    by (rule source_first_crash_capability_window_imp_source_first_gap[OF window])
  from implementation_admits_source_first_gap_with_crash_has_concrete_bad_crash_execution
        [OF gap crash]
  obtain s where trace:
      "dwi_trace I (dwi_initial I) (implementation_gap_crash_labels W) s"
      and bad:
        "bad_crash_execution_for_gap
          (operational_gap_of_implementation_gap I W) (dwi_state I s)"
    by blast
  from window crash trace bad show ?thesis by blast
qed

theorem source_first_crash_capability_window_crash_closed_has_concrete_bad_crash_execution:
  assumes window: "source_first_crash_capability_window I W"
      and closed: "crash_closed_implementation I"
  shows "\<exists>s.
      dwi_trace I (dwi_initial I) (implementation_gap_crash_labels W) s
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I W) (dwi_state I s)"
proof -
  have gap: "implementation_admits_source_first_gap I W"
    by (rule source_first_crash_capability_window_imp_source_first_gap[OF window])
  have crash: "implementation_crash_enabled_for_gap I W"
    by (rule crash_closed_imp_implementation_crash_enabled_for_gap
        [OF closed gap])
  from implementation_admits_source_first_gap_with_crash_has_concrete_bad_crash_execution
        [OF gap crash]
  obtain s where trace:
      "dwi_trace I (dwi_initial I) (implementation_gap_crash_labels W) s"
      and bad:
        "bad_crash_execution_for_gap
          (operational_gap_of_implementation_gap I W) (dwi_state I s)"
    by blast
  from trace bad show ?thesis by blast
qed

theorem source_first_crash_capability_crash_closed_implementation_has_concrete_bad_crash_execution:
  assumes impl: "source_first_crash_capability_crash_closed_implementation I"
  shows "\<exists>W s.
      source_first_crash_capability_window I W
    \<and> dwi_trace I (dwi_initial I) (implementation_gap_crash_labels W) s
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I W) (dwi_state I s)"
proof -
  from impl obtain W where closed: "crash_closed_implementation I"
      and window: "source_first_crash_capability_window I W"
    by (auto simp:
        source_first_crash_capability_crash_closed_implementation_def)
  from source_first_crash_capability_window_crash_closed_has_concrete_bad_crash_execution
        [OF window closed]
  obtain s where trace:
      "dwi_trace I (dwi_initial I) (implementation_gap_crash_labels W) s"
      and bad:
        "bad_crash_execution_for_gap
          (operational_gap_of_implementation_gap I W) (dwi_state I s)"
    by blast
  from window trace bad show ?thesis by blast
qed


section \<open>Shared atomic macro-commit contrast\<close>

record ('k, 'v) shared_atomic_commit_witness =
  sac_pre   :: "('k, 'v) dw_exec_label list"
  sac_key   :: "'k"
  sac_at    :: src_coord
  sac_event :: "('k, 'v) source_event"

definition shared_atomic_commit_state
  :: "('k, 'v) dw_exec_state \<Rightarrow> src_coord \<Rightarrow>
      ('k, 'v) source_event \<Rightarrow> ('k, 'v) dw_exec_state"
where
  "shared_atomic_commit_state s c e =
     s\<lparr> exec_src_hist := exec_src_hist s @ [(c, e)],
       exec_down_hist := exec_down_hist s @ [(c, e)],
       exec_enqueued := exec_enqueued s @ [(c, e)],
       exec_acked := exec_acked s @ [(c, e)],
       exec_pending := exec_pending s - {(c, e)} \<rparr>"

definition source_downstream_history_aligned
  :: "('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  "source_downstream_history_aligned s \<longleftrightarrow>
     exec_src_hist s = exec_down_hist s"

lemma source_downstream_history_aligned_no_mismatch_at:
  assumes aligned: "source_downstream_history_aligned s"
  shows "\<not> mismatch_at (proto_of_exec_at s f) f k"
  using aligned
  by (auto simp: source_downstream_history_aligned_def
                 mismatch_at_def proto_of_exec_at_def
                 store2_of_exec_def log_image_def restrict_def)

lemma source_downstream_history_aligned_no_observable_mismatch:
  assumes aligned: "source_downstream_history_aligned s"
  shows "\<not> observable_mismatch s f k"
  using source_downstream_history_aligned_no_mismatch_at[OF aligned]
  by (simp add: observable_mismatch_def)

lemma source_downstream_history_aligned_no_divergence:
  assumes aligned: "source_downstream_history_aligned s"
  shows "\<not> diverges (proto_of_exec_at s f) f"
  using source_downstream_history_aligned_no_mismatch_at[OF aligned]
  by (auto simp: diverges_iff_mismatch_at)

definition shared_atomic_source_downstream_commit
  :: "('k, 'v) dw_exec_state \<Rightarrow> 'k \<Rightarrow> src_coord \<Rightarrow>
      ('k, 'v) source_event \<Rightarrow> ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  "shared_atomic_source_downstream_commit s k c e s' \<longleftrightarrow>
     exec_status s = Running
   \<and> c \<le> exec_finish s
   \<and> key_of e = k
   \<and> effective_source_effect (exec_base s) e k
   \<and> k \<in> exec_scope s
   \<and> s' = shared_atomic_commit_state s c e"

datatype ('k, 'v) shared_atomic_commit_label =
    SharedSourceDownstreamCommit src_coord "('k, 'v) source_event"
  | SharedCommitCrash frontier
  | SharedCommitObserve frontier

inductive shared_atomic_commit_step
  :: "('k, 'v) dw_exec_state \<Rightarrow>
      ('k, 'v) shared_atomic_commit_label \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  shared_commit:
    "shared_atomic_source_downstream_commit s (key_of e) c e s' \<Longrightarrow>
     shared_atomic_commit_step s (SharedSourceDownstreamCommit c e) s'"
| shared_crash:
    "exec_status s = Running \<Longrightarrow>
     shared_atomic_commit_step s (SharedCommitCrash c)
       (s\<lparr>exec_status := Crashed c\<rparr>)"
| shared_observe:
    "shared_atomic_commit_step s (SharedCommitObserve f) s"

inductive shared_atomic_commit_trace
  :: "('k, 'v) dw_exec_state \<Rightarrow>
      ('k, 'v) shared_atomic_commit_label list \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  shared_trace_refl:
    "shared_atomic_commit_trace s [] s"
| shared_trace_step:
    "\<lbrakk>shared_atomic_commit_step s a s';
      shared_atomic_commit_trace s' as s''\<rbrakk> \<Longrightarrow>
     shared_atomic_commit_trace s (a # as) s''"

definition shared_atomic_commit_only_execution
  :: "('k, 'v) dw_exec_state \<Rightarrow>
      ('k, 'v) shared_atomic_commit_label list \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  "shared_atomic_commit_only_execution s xs s' \<longleftrightarrow>
     source_downstream_history_aligned s
   \<and> shared_atomic_commit_trace s xs s'"

definition source_first_gap_of_shared_atomic_commit
  :: "('k, 'v) shared_atomic_commit_witness \<Rightarrow>
      ('k, 'v) implementation_source_first_gap_witness"
where
  "source_first_gap_of_shared_atomic_commit A =
     \<lparr> isfg_pre = sac_pre A,
       isfg_gap =
         [Ack (sac_at A) (sac_event A),
          EnqueueDownstream (sac_at A) (sac_event A),
          DoDownstream (sac_at A) (sac_event A)],
       isfg_key = sac_key A,
       isfg_source_at = sac_at A,
       isfg_event = sac_event A,
       isfg_down_at = sac_at A,
       isfg_down_event = sac_event A,
       isfg_crash_at = sac_at A \<rparr>"

lemma shared_atomic_commit_step_no_mismatch_at_commit:
  assumes atomic: "shared_atomic_source_downstream_commit s k c e s'"
  shows "\<not> mismatch_at (proto_of_exec_at s' c) c k"
proof -
  from atomic have key: "key_of e = k"
      and scope: "k \<in> exec_scope s"
      and post: "s' = shared_atomic_commit_state s c e"
    by (auto simp: shared_atomic_source_downstream_commit_def)
  have src:
    "Src (exec_base s') (exec_src_hist s') c k = event_result e"
    using key post
    by (simp add: shared_atomic_commit_state_def Src_snoc_event_at_key)
  have down:
    "Src (exec_base s') (exec_down_hist s') c k = event_result e"
    using key post
    by (simp add: shared_atomic_commit_state_def Src_snoc_event_at_key)
  from scope post src down show ?thesis
    by (simp add: shared_atomic_commit_state_def mismatch_at_def
                  proto_of_exec_at_def store2_of_exec_def log_image_def
                  restrict_def)
qed

lemma shared_atomic_commit_step_crash_after_commit_no_observable_mismatch:
  assumes atomic: "shared_atomic_source_downstream_commit s k c e s'"
  shows "\<not> observable_mismatch
      (s'\<lparr>exec_status := Crashed c\<rparr>) c k"
  using shared_atomic_commit_step_no_mismatch_at_commit[OF atomic]
  by (simp add: observable_mismatch_def)

lemma shared_atomic_commit_step_advances_both_histories:
  assumes step:
    "shared_atomic_commit_step s (SharedSourceDownstreamCommit c e) s'"
  shows
    "exec_src_hist s' = exec_src_hist s @ [(c, e)]
   \<and> exec_down_hist s' = exec_down_hist s @ [(c, e)]
   \<and> exec_enqueued s' = exec_enqueued s @ [(c, e)]
   \<and> exec_acked s' = exec_acked s @ [(c, e)]"
  using step
  by cases
     (auto simp: shared_atomic_source_downstream_commit_def
                 shared_atomic_commit_state_def)

lemma shared_atomic_commit_step_leaves_no_pending_downstream_intent:
  assumes step:
    "shared_atomic_commit_step s (SharedSourceDownstreamCommit c e) s'"
  shows "exec_pending s' = exec_pending s - {(c, e)}"
  using step
  by cases
     (auto simp: shared_atomic_source_downstream_commit_def
                 shared_atomic_commit_state_def)

lemma shared_atomic_commit_step_same_intent_not_pending:
  assumes step:
    "shared_atomic_commit_step s (SharedSourceDownstreamCommit c e) s'"
  shows "(c, e) \<notin> exec_pending s'"
  using shared_atomic_commit_step_leaves_no_pending_downstream_intent[OF step]
  by simp

lemma shared_atomic_commit_step_preserves_history_alignment:
  assumes step: "shared_atomic_commit_step s a s'"
      and aligned: "source_downstream_history_aligned s"
  shows "source_downstream_history_aligned s'"
  using step aligned
  by cases
     (auto simp: source_downstream_history_aligned_def
                 shared_atomic_source_downstream_commit_def
                 shared_atomic_commit_state_def)

lemma shared_atomic_commit_trace_preserves_history_alignment:
  assumes trace: "shared_atomic_commit_trace s xs s'"
      and aligned: "source_downstream_history_aligned s"
  shows "source_downstream_history_aligned s'"
  using trace aligned
proof (induction rule: shared_atomic_commit_trace.induct)
  case (shared_trace_refl s)
  show ?case by (rule shared_trace_refl.prems)
next
  case (shared_trace_step s a s' xs s'')
  have aligned': "source_downstream_history_aligned s'"
    by (rule shared_atomic_commit_step_preserves_history_alignment
        [OF shared_trace_step.hyps(1) shared_trace_step.prems])
  show ?case by (rule shared_trace_step.IH[OF aligned'])
qed

theorem shared_atomic_commit_only_execution_no_observable_mismatch:
  assumes exec: "shared_atomic_commit_only_execution s xs s'"
  shows "\<not> observable_mismatch s' f k"
proof -
  from exec have aligned0: "source_downstream_history_aligned s"
      and trace: "shared_atomic_commit_trace s xs s'"
    by (auto simp: shared_atomic_commit_only_execution_def)
  have aligned': "source_downstream_history_aligned s'"
    by (rule shared_atomic_commit_trace_preserves_history_alignment
        [OF trace aligned0])
  show ?thesis
    by (rule source_downstream_history_aligned_no_observable_mismatch
        [OF aligned'])
qed

theorem shared_atomic_commit_only_execution_no_divergence:
  assumes exec: "shared_atomic_commit_only_execution s xs s'"
  shows "\<not> diverges (proto_of_exec_at s' f) f"
proof -
  from exec have aligned0: "source_downstream_history_aligned s"
      and trace: "shared_atomic_commit_trace s xs s'"
    by (auto simp: shared_atomic_commit_only_execution_def)
  have aligned': "source_downstream_history_aligned s'"
    by (rule shared_atomic_commit_trace_preserves_history_alignment
        [OF trace aligned0])
  show ?thesis
    by (rule source_downstream_history_aligned_no_divergence[OF aligned'])
qed

lemma shared_atomic_commit_gap_completed_downstream:
  "completed_downstream_before_crash_gap
    (source_first_gap_of_shared_atomic_commit A)"
  by (simp add: completed_downstream_before_crash_gap_def
                source_first_gap_of_shared_atomic_commit_def)

lemma shared_atomic_commit_gap_not_source_first_crash_capability_window:
  "\<not> source_first_crash_capability_window I
    (source_first_gap_of_shared_atomic_commit A)"
  by (simp add: source_first_crash_capability_window_def
                source_first_gap_of_shared_atomic_commit_def)

lemma shared_atomic_commit_gap_not_non_atomic_no_shared_commit_window:
  "\<not> non_atomic_no_shared_commit_source_first_window I
    (source_first_gap_of_shared_atomic_commit A)"
  by (simp add: non_atomic_no_shared_commit_source_first_window_def
                non_atomic_source_effect_window_def
                source_first_gap_of_shared_atomic_commit_def)

theorem shared_atomic_commit_class_disjoint_from_source_first_capability:
  shows "\<not> source_first_crash_capability_window I
    (source_first_gap_of_shared_atomic_commit A)"
  by (rule shared_atomic_commit_gap_not_source_first_crash_capability_window)

theorem shared_atomic_commit_class_disjoint_from_non_atomic_no_shared_commit:
  shows "\<not> non_atomic_no_shared_commit_source_first_window I
    (source_first_gap_of_shared_atomic_commit A)"
  by (rule shared_atomic_commit_gap_not_non_atomic_no_shared_commit_window)

definition shared_atomic_stale_update_initial :: "(nat, nat) dw_exec_state"
where
  "shared_atomic_stale_update_initial =
     initial_exec_state [0 \<mapsto> 1] {0} ec3"

definition shared_atomic_stale_update_commit
  :: "(nat, nat) shared_atomic_commit_witness"
where
  "shared_atomic_stale_update_commit =
     \<lparr> sac_pre = [],
       sac_key = 0,
       sac_at = ec1,
       sac_event = Update 0 2 \<rparr>"

definition shared_atomic_stale_update_post :: "(nat, nat) dw_exec_state"
where
  "shared_atomic_stale_update_post =
     shared_atomic_commit_state
       shared_atomic_stale_update_initial ec1 (Update 0 2)"

definition shared_atomic_stale_update_crashed :: "(nat, nat) dw_exec_state"
where
  "shared_atomic_stale_update_crashed =
     shared_atomic_stale_update_post\<lparr>exec_status := Crashed ec1\<rparr>"

definition shared_atomic_stale_update_labels
  :: "(nat, nat) shared_atomic_commit_label list"
where
  "shared_atomic_stale_update_labels =
     [SharedSourceDownstreamCommit ec1 (Update 0 2),
      SharedCommitCrash ec1]"

lemma shared_atomic_stale_update_macro_step:
  "shared_atomic_source_downstream_commit
    shared_atomic_stale_update_initial 0 ec1 (Update 0 2)
    shared_atomic_stale_update_post"
  by (simp add: shared_atomic_source_downstream_commit_def
                shared_atomic_stale_update_initial_def
                shared_atomic_stale_update_post_def
                initial_exec_state_def effective_source_effect_def ec_defs)

lemma shared_atomic_stale_update_commit_step:
  "shared_atomic_commit_step
    shared_atomic_stale_update_initial
    (SharedSourceDownstreamCommit ec1 (Update 0 2))
    shared_atomic_stale_update_post"
  by (rule shared_atomic_commit_step.shared_commit)
     (simp add: shared_atomic_stale_update_macro_step)

lemma shared_atomic_stale_update_crash_step:
  "shared_atomic_commit_step
    shared_atomic_stale_update_post
    (SharedCommitCrash ec1)
    shared_atomic_stale_update_crashed"
  unfolding shared_atomic_stale_update_crashed_def
  by (rule shared_atomic_commit_step.shared_crash)
     (simp add: shared_atomic_stale_update_post_def
                shared_atomic_stale_update_initial_def
                shared_atomic_commit_state_def initial_exec_state_def)

lemma shared_atomic_stale_update_trace:
  "shared_atomic_commit_trace
    shared_atomic_stale_update_initial
    shared_atomic_stale_update_labels
    shared_atomic_stale_update_crashed"
  unfolding shared_atomic_stale_update_labels_def
  by (rule shared_atomic_commit_trace.shared_trace_step
        [OF shared_atomic_stale_update_commit_step])
     (rule shared_atomic_commit_trace.shared_trace_step
        [OF shared_atomic_stale_update_crash_step
          shared_atomic_commit_trace.shared_trace_refl])

lemma shared_atomic_stale_update_initial_aligned:
  "source_downstream_history_aligned shared_atomic_stale_update_initial"
  by (simp add: source_downstream_history_aligned_def
                shared_atomic_stale_update_initial_def initial_exec_state_def)

lemma shared_atomic_stale_update_only_execution:
  "shared_atomic_commit_only_execution
    shared_atomic_stale_update_initial
    shared_atomic_stale_update_labels
    shared_atomic_stale_update_crashed"
  by (simp add: shared_atomic_commit_only_execution_def
                shared_atomic_stale_update_initial_aligned
                shared_atomic_stale_update_trace)

corollary shared_atomic_commit_class_nonempty:
  "\<exists>(s0 :: (nat, nat) dw_exec_state)
      (xs :: (nat, nat) shared_atomic_commit_label list)
      (s :: (nat, nat) dw_exec_state).
      shared_atomic_commit_only_execution s0 xs s
    \<and> exec_status s = Crashed ec1
    \<and> \<not> observable_mismatch s ec1 0
    \<and> \<not> diverges (proto_of_exec_at s ec1) ec1"
proof -
  have no_obs:
    "\<not> observable_mismatch shared_atomic_stale_update_crashed ec1 0"
    by (rule shared_atomic_commit_only_execution_no_observable_mismatch
        [OF shared_atomic_stale_update_only_execution])
  have no_div:
    "\<not> diverges
      (proto_of_exec_at shared_atomic_stale_update_crashed ec1) ec1"
    by (rule shared_atomic_commit_only_execution_no_divergence
        [OF shared_atomic_stale_update_only_execution])
  have status: "exec_status shared_atomic_stale_update_crashed = Crashed ec1"
    by (simp add: shared_atomic_stale_update_crashed_def)
  show ?thesis
    apply (rule exI[where x = shared_atomic_stale_update_initial])
    apply (rule exI[where x = shared_atomic_stale_update_labels])
    apply (rule exI[where x = shared_atomic_stale_update_crashed])
    using shared_atomic_stale_update_only_execution status no_obs no_div
    apply simp
    done
qed

lemma shared_atomic_stale_update_no_mismatch_at_commit:
  "\<not> mismatch_at (proto_of_exec_at shared_atomic_stale_update_post ec1) ec1 0"
  by (rule shared_atomic_commit_step_no_mismatch_at_commit
      [OF shared_atomic_stale_update_macro_step])

lemma shared_atomic_stale_update_crash_after_commit_no_observable_mismatch:
  "\<not> observable_mismatch
    (shared_atomic_stale_update_post\<lparr>exec_status := Crashed ec1\<rparr>)
    ec1 0"
  by (rule shared_atomic_commit_step_crash_after_commit_no_observable_mismatch
      [OF shared_atomic_stale_update_macro_step])

lemma shared_atomic_stale_update_no_divergence_at_commit:
  "\<not> diverges (proto_of_exec_at shared_atomic_stale_update_post ec1) ec1"
proof -
  have aligned:
    "source_downstream_history_aligned shared_atomic_stale_update_post"
    by (rule shared_atomic_commit_step_preserves_history_alignment
        [OF shared_atomic_stale_update_commit_step
          shared_atomic_stale_update_initial_aligned])
  show ?thesis
    by (rule source_downstream_history_aligned_no_divergence[OF aligned])
qed

lemma shared_atomic_stale_update_outside_source_first_capability:
  "\<not> source_first_crash_capability_window
    (canonical_dw_implementation shared_atomic_stale_update_initial)
    (source_first_gap_of_shared_atomic_commit
      shared_atomic_stale_update_commit)"
  by (rule shared_atomic_commit_gap_not_source_first_crash_capability_window)

lemma shared_atomic_stale_update_outside_non_atomic_no_shared_commit:
  "\<not> non_atomic_no_shared_commit_source_first_window
    (canonical_dw_implementation shared_atomic_stale_update_initial)
    (source_first_gap_of_shared_atomic_commit
      shared_atomic_stale_update_commit)"
  by (rule shared_atomic_commit_gap_not_non_atomic_no_shared_commit_window)


section \<open>Conditional bad-crash characterization\<close>

definition reachable_observable_bad_crash
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) dw_exec_label list \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> 's \<Rightarrow> bool"
where
  "reachable_observable_bad_crash I xs c k s \<longleftrightarrow>
     dwi_trace I (dwi_initial I) xs s
   \<and> observable_mismatch (dwi_state I s) c k
   \<and> diverges (proto_of_exec_at (dwi_state I s) c) c"

definition implementation_has_reachable_observable_bad_crash
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "implementation_has_reachable_observable_bad_crash I \<longleftrightarrow>
     (\<exists>xs c k s. reachable_observable_bad_crash I xs c k s)"

definition bad_crash_reconstructs_separated_completion
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) dw_exec_label list \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> bool"
where
  "bad_crash_reconstructs_separated_completion I xs c k \<longleftrightarrow>
     (\<exists>C side.
        separated_completion_first_side I C side
      \<and> xs = separated_completion_bad_crash_labels side C
      \<and> c = separated_completion_crash_frontier side C
      \<and> k = sdwc_key C)"

definition implementation_has_reconstructable_bad_crash
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "implementation_has_reconstructable_bad_crash I \<longleftrightarrow>
     (\<exists>xs c k s.
        reachable_observable_bad_crash I xs c k s
      \<and> bad_crash_reconstructs_separated_completion I xs c k)"

definition reachable_bad_crashes_reconstruct_separated_completion
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "reachable_bad_crashes_reconstruct_separated_completion I \<longleftrightarrow>
     (\<forall>xs c k s.
        reachable_observable_bad_crash I xs c k s
        \<longrightarrow> bad_crash_reconstructs_separated_completion I xs c k)"

text \<open>
  The converse below is deliberately conditional. A reachable observable
  mismatch alone does not identify a separated dual-write completion; the trace
  must reconstruct the separated completion that explains the crash frontier.
\<close>

lemma separated_completion_concrete_bad_imp_reachable_observable_bad_crash:
  assumes bad: "separated_completion_concrete_bad_crash_execution I C side s"
  shows "reachable_observable_bad_crash I
    (separated_completion_bad_crash_labels side C)
    (separated_completion_crash_frontier side C) (sdwc_key C) s"
  using bad
  by (simp add: reachable_observable_bad_crash_def
                separated_completion_concrete_bad_crash_execution_def)

lemma separated_completion_bad_crash_reconstructs:
  assumes side: "separated_completion_first_side I C side"
  shows "bad_crash_reconstructs_separated_completion I
    (separated_completion_bad_crash_labels side C)
    (separated_completion_crash_frontier side C) (sdwc_key C)"
  using side
  by (auto simp: bad_crash_reconstructs_separated_completion_def)

theorem separable_non_atomic_crash_closed_imp_reconstructable_bad_crash:
  assumes impl: "separable_non_atomic_crash_closed_dual_write_implementation I"
  shows "implementation_has_reconstructable_bad_crash I"
proof -
  from separable_non_atomic_crash_closed_dual_write_implementation_has_concrete_bad_crash_execution
        [OF impl]
  obtain C side s where side: "separated_completion_first_side I C side"
      and bad: "separated_completion_concrete_bad_crash_execution I C side s"
    by blast
  have reachable:
    "reachable_observable_bad_crash I
      (separated_completion_bad_crash_labels side C)
      (separated_completion_crash_frontier side C) (sdwc_key C) s"
    by (rule separated_completion_concrete_bad_imp_reachable_observable_bad_crash
        [OF bad])
  have reconstructs:
    "bad_crash_reconstructs_separated_completion I
      (separated_completion_bad_crash_labels side C)
      (separated_completion_crash_frontier side C) (sdwc_key C)"
    by (rule separated_completion_bad_crash_reconstructs[OF side])
  from reachable reconstructs show ?thesis
    by (auto simp: implementation_has_reconstructable_bad_crash_def)
qed

theorem reconstructable_bad_crash_imp_separable_non_atomic_crash_closed:
  assumes closed: "crash_closed_implementation I"
      and bad: "implementation_has_reconstructable_bad_crash I"
  shows "separable_non_atomic_crash_closed_dual_write_implementation I"
proof -
  from bad obtain xs c k s C side where
      side: "separated_completion_first_side I C side"
    by (auto simp: implementation_has_reconstructable_bad_crash_def
                   bad_crash_reconstructs_separated_completion_def)
  have completion: "separable_non_atomic_dual_write_completion I C"
    using side by (auto simp: separable_non_atomic_dual_write_completion_def)
  have impl: "separable_non_atomic_dual_write_implementation I"
    using completion by (auto simp: separable_non_atomic_dual_write_implementation_def)
  from closed impl show ?thesis
    by (simp add: separable_non_atomic_crash_closed_dual_write_implementation_def)
qed

theorem conditional_separable_bad_crash_characterization:
  "separable_non_atomic_crash_closed_dual_write_implementation I
   \<longleftrightarrow>
   crash_closed_implementation I
   \<and> implementation_has_reconstructable_bad_crash I"
proof
  assume impl: "separable_non_atomic_crash_closed_dual_write_implementation I"
  hence closed: "crash_closed_implementation I"
    by (simp add: separable_non_atomic_crash_closed_dual_write_implementation_def)
  have bad: "implementation_has_reconstructable_bad_crash I"
    by (rule separable_non_atomic_crash_closed_imp_reconstructable_bad_crash
        [OF impl])
  from closed bad show
    "crash_closed_implementation I
     \<and> implementation_has_reconstructable_bad_crash I"
    by simp
next
  assume rhs:
    "crash_closed_implementation I
     \<and> implementation_has_reconstructable_bad_crash I"
  thus "separable_non_atomic_crash_closed_dual_write_implementation I"
    by (auto intro: reconstructable_bad_crash_imp_separable_non_atomic_crash_closed)
qed

theorem crash_closed_separable_iff_reachable_bad_under_reconstruction:
  assumes recon: "reachable_bad_crashes_reconstruct_separated_completion I"
  shows
    "separable_non_atomic_crash_closed_dual_write_implementation I
     \<longleftrightarrow>
     crash_closed_implementation I
     \<and> implementation_has_reachable_observable_bad_crash I"
proof
  assume impl: "separable_non_atomic_crash_closed_dual_write_implementation I"
  hence closed: "crash_closed_implementation I"
    by (simp add: separable_non_atomic_crash_closed_dual_write_implementation_def)
  from separable_non_atomic_crash_closed_imp_reconstructable_bad_crash[OF impl]
  have bad: "implementation_has_reachable_observable_bad_crash I"
    by (auto simp: implementation_has_reconstructable_bad_crash_def
                   implementation_has_reachable_observable_bad_crash_def)
  from closed bad show
    "crash_closed_implementation I
     \<and> implementation_has_reachable_observable_bad_crash I"
    by simp
next
  assume rhs:
    "crash_closed_implementation I
     \<and> implementation_has_reachable_observable_bad_crash I"
  then obtain xs c k s where closed: "crash_closed_implementation I"
      and reachable: "reachable_observable_bad_crash I xs c k s"
    by (auto simp: implementation_has_reachable_observable_bad_crash_def)
  have reconstructs:
    "bad_crash_reconstructs_separated_completion I xs c k"
    using recon reachable
    unfolding reachable_bad_crashes_reconstruct_separated_completion_def
    by blast
  have reconstructable: "implementation_has_reconstructable_bad_crash I"
    using reachable reconstructs
    by (auto simp: implementation_has_reconstructable_bad_crash_def)
  show "separable_non_atomic_crash_closed_dual_write_implementation I"
    by (rule reconstructable_bad_crash_imp_separable_non_atomic_crash_closed
        [OF closed reconstructable])
qed

lemma separated_completion_first_side_non_atomic_frontiers:
  assumes side: "separated_completion_first_side I C side"
  shows "sdwc_source_at C \<noteq> sdwc_down_at C"
  using separated_completion_first_side_coordinate_sanity[OF side]
  by (cases side) auto

corollary non_atomic_separated_boundary_admits_reconstructable_bad_crash:
  assumes closed: "crash_closed_implementation I"
      and side: "separated_completion_first_side I C side"
  shows "sdwc_source_at C \<noteq> sdwc_down_at C
   \<and> implementation_has_reconstructable_bad_crash I"
proof -
  have completion: "separable_non_atomic_dual_write_completion I C"
    using side by (auto simp: separable_non_atomic_dual_write_completion_def)
  have impl: "separable_non_atomic_crash_closed_dual_write_implementation I"
    using closed completion
    by (auto simp: separable_non_atomic_crash_closed_dual_write_implementation_def
                   separable_non_atomic_dual_write_implementation_def)
  have distinct: "sdwc_source_at C \<noteq> sdwc_down_at C"
    by (rule separated_completion_first_side_non_atomic_frontiers[OF side])
  have bad: "implementation_has_reconstructable_bad_crash I"
    by (rule separable_non_atomic_crash_closed_imp_reconstructable_bad_crash
        [OF impl])
  from distinct bad show ?thesis by simp
qed

definition crash_only_initial_mismatch_state :: "(nat, nat) dw_exec_state"
where
  "crash_only_initial_mismatch_state =
     (initial_exec_state [0 \<mapsto> 1] {0} ec1)
       \<lparr> exec_src_hist := [(ec1, Update 0 2)],
         exec_status := Crashed ec1 \<rparr>"

lemma crash_only_initial_mismatch_observable:
  "observable_mismatch crash_only_initial_mismatch_state ec1 (0::nat)"
  by (rule observable_mismatchI)
     (simp_all add: crash_only_initial_mismatch_state_def
                    initial_exec_state_def Src_def latest_src_event_def
                    src_le_eq_less_eq Let_def ec_defs)

lemma crash_only_initial_mismatch_reachable_bad_crash:
  "reachable_observable_bad_crash
    (canonical_dw_implementation crash_only_initial_mismatch_state)
    [] ec1 (0::nat) crash_only_initial_mismatch_state"
proof -
  have trace0:
    "dwi_trace
      (canonical_dw_implementation crash_only_initial_mismatch_state)
      crash_only_initial_mismatch_state []
      crash_only_initial_mismatch_state"
    by (rule dwi_trace.dwi_trace_refl)
  have trace:
    "dwi_trace
      (canonical_dw_implementation crash_only_initial_mismatch_state)
      (dwi_initial
        (canonical_dw_implementation crash_only_initial_mismatch_state))
      [] crash_only_initial_mismatch_state"
    using trace0 by (simp add: canonical_dw_implementation_def)
  have obs:
    "observable_mismatch crash_only_initial_mismatch_state ec1 (0::nat)"
    by (rule crash_only_initial_mismatch_observable)
  have div:
    "diverges (proto_of_exec_at crash_only_initial_mismatch_state ec1) ec1"
    by (rule observable_mismatch_imp_diverges[OF obs])
  from trace obs div show ?thesis
    by (simp add: reachable_observable_bad_crash_def
                  canonical_dw_implementation_def)
qed

lemma crash_only_initial_mismatch_has_reachable_bad_crash:
  "implementation_has_reachable_observable_bad_crash
    (canonical_dw_implementation crash_only_initial_mismatch_state)"
  using crash_only_initial_mismatch_reachable_bad_crash
  by (auto simp: implementation_has_reachable_observable_bad_crash_def)

lemma crash_only_initial_mismatch_not_separable:
  "\<not> separable_non_atomic_dual_write_implementation
      (canonical_dw_implementation crash_only_initial_mismatch_state)"
proof
  let ?I = "canonical_dw_implementation crash_only_initial_mismatch_state"
  assume sep: "separable_non_atomic_dual_write_implementation ?I"
  then obtain C side where side: "separated_completion_first_side ?I C side"
    by (auto simp: separable_non_atomic_dual_write_implementation_def
                   separable_non_atomic_dual_write_completion_def)
  have running:
    "exec_status (dwi_state ?I (dwi_initial ?I)) = Running"
    by (rule separated_completion_first_side_start_running[OF side])
  thus False
    by (simp add: canonical_dw_implementation_def
                  crash_only_initial_mismatch_state_def
                  initial_exec_state_def)
qed

theorem crash_only_initial_mismatch_refutes_premise_free_characterization:
  "\<exists>I :: ((nat, nat) dw_exec_state, nat, nat) dual_write_implementation.
      crash_closed_implementation I
    \<and> implementation_has_reachable_observable_bad_crash I
    \<and> \<not> separable_non_atomic_crash_closed_dual_write_implementation I"
proof -
  let ?I = "canonical_dw_implementation crash_only_initial_mismatch_state"
  have closed: "crash_closed_implementation ?I"
    by (rule canonical_dw_implementation_crash_closed)
  have bad: "implementation_has_reachable_observable_bad_crash ?I"
    by (rule crash_only_initial_mismatch_has_reachable_bad_crash)
  have not_sep: "\<not> separable_non_atomic_dual_write_implementation ?I"
    by (rule crash_only_initial_mismatch_not_separable)
  have not_closed_sep:
    "\<not> separable_non_atomic_crash_closed_dual_write_implementation ?I"
    using not_sep
    by (simp add: separable_non_atomic_crash_closed_dual_write_implementation_def)
  from closed bad not_closed_sep show ?thesis by blast
qed


section \<open>Negative controls for load-bearing capabilities\<close>

lemma no_source_first_window_not_source_first_crash_capability_window:
  assumes "\<not> implementation_has_source_first_window I W"
  shows "\<not> source_first_crash_capability_window I W"
  using assms by (simp add: source_first_crash_capability_window_def)

lemma non_atomic_source_effect_window_required:
  assumes "\<not> non_atomic_source_effect_window I W"
  shows "\<not> source_first_crash_capability_window I W"
  using assms by (simp add: source_first_crash_capability_window_def)

lemma source_ack_after_commit_required:
  assumes "\<not> source_ack_after_commit W"
  shows "\<not> source_first_crash_capability_window I W"
  using assms by (simp add: source_first_crash_capability_window_def)

lemma pending_downstream_intent_at_crash_required:
  assumes "\<not> pending_downstream_intent_at_crash I W"
  shows "\<not> source_first_crash_capability_window I W"
  using assms by (simp add: source_first_crash_capability_window_def)

lemma no_later_source_overwrite_before_crash_required:
  assumes "\<not> no_later_source_overwrite_before_crash W"
  shows "\<not> source_first_crash_capability_window I W"
  using assms by (simp add: source_first_crash_capability_window_def)

lemma no_visible_downstream_effect_at_crash_required:
  assumes "\<not> no_visible_downstream_effect_at_crash I W"
  shows "\<not> source_first_crash_capability_window I W"
  using assms by (simp add: source_first_crash_capability_window_def)

lemma completed_downstream_before_crash_gap_not_source_first_crash_capability_window:
  assumes completed: "completed_downstream_before_crash_gap W"
  shows "\<not> source_first_crash_capability_window I W"
proof -
  have no_pending: "\<not> pending_downstream_intent_at_crash I W"
    by (rule completed_downstream_before_crash_gap_not_pending_intent[OF completed])
  show ?thesis
    by (rule pending_downstream_intent_at_crash_required[OF no_pending])
qed

lemma shared_atomic_source_downstream_commit_gap_outside_source_first_crash_capability:
  assumes atomic: "shared_atomic_source_downstream_commit_gap W"
  shows "\<not> source_first_crash_capability_window I W"
  using atomic
  by (simp add: shared_atomic_source_downstream_commit_gap_def
                completed_downstream_before_crash_gap_not_source_first_crash_capability_window)

lemma acknowledged_source_window_required_for_no_shared_commit_window:
  assumes "\<not> acknowledged_source_window I W"
  shows "\<not> non_atomic_no_shared_commit_source_first_window I W"
  using assms by (simp add: non_atomic_no_shared_commit_source_first_window_def)

lemma downstream_intent_without_completion_required_for_no_shared_commit_window:
  assumes "\<not> downstream_intent_without_completion I W"
  shows "\<not> non_atomic_no_shared_commit_source_first_window I W"
  using assms by (simp add: non_atomic_no_shared_commit_source_first_window_def)


section \<open>Replay-protected exclusion of source-first crash windows\<close>

definition implementation_replay_derived_crash_window
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) implementation_source_first_gap_witness \<Rightarrow> bool"
where
  "implementation_replay_derived_crash_window I W \<longleftrightarrow>
     (\<forall>s. dwi_trace I (dwi_initial I) (implementation_gap_crash_labels W) s
       \<longrightarrow> (\<exists>\<sigma>. execution_replay_derived_at
          (dwi_state I s) \<sigma> (isfg_crash_at W)))"

lemma observable_mismatch_excludes_execution_replay_derived_at:
  assumes obs: "observable_mismatch s f k"
  shows "\<not> execution_replay_derived_at s \<sigma> f"
proof
  assume derived: "execution_replay_derived_at s \<sigma> f"
  have no_mismatch:
    "\<forall>k. \<not> mismatch_at (proto_of_exec_at s f) f k"
    using replay_derived_at_no_mismatch[of "proto_of_exec_at s f" \<sigma> f]
      derived
    by (simp add: execution_replay_derived_at_def)
  from obs have "mismatch_at (proto_of_exec_at s f) f k"
    by (simp add: observable_mismatch_def)
  with no_mismatch show False by blast
qed

theorem separated_completion_concrete_bad_crash_excludes_replay_derived_at:
  assumes bad:
    "separated_completion_concrete_bad_crash_execution I C side s"
  shows "\<not> execution_replay_derived_at (dwi_state I s) \<sigma>
           (separated_completion_crash_frontier side C)"
proof -
  from bad have obs:
    "observable_mismatch (dwi_state I s)
      (separated_completion_crash_frontier side C) (sdwc_key C)"
    by (simp add: separated_completion_concrete_bad_crash_execution_def)
  show ?thesis
    by (rule observable_mismatch_excludes_execution_replay_derived_at[OF obs])
qed

theorem separable_non_atomic_crash_closed_selects_non_replay_derived_bad_prefix:
  assumes impl:
    "separable_non_atomic_crash_closed_dual_write_implementation I"
  shows "\<exists>C side s.
      separable_non_atomic_dual_write_completion I C
    \<and> separated_completion_first_side I C side
    \<and> separated_completion_concrete_bad_crash_execution I C side s
    \<and> (\<forall>\<sigma>. \<not> execution_replay_derived_at (dwi_state I s) \<sigma>
          (separated_completion_crash_frontier side C))"
proof -
  from separable_non_atomic_crash_closed_dual_write_implementation_has_concrete_bad_crash_execution
        [OF impl]
  obtain C side s where completion:
      "separable_non_atomic_dual_write_completion I C"
      and side: "separated_completion_first_side I C side"
      and bad:
        "separated_completion_concrete_bad_crash_execution I C side s"
    by blast
  have no_replay:
    "\<forall>\<sigma>. \<not> execution_replay_derived_at (dwi_state I s) \<sigma>
      (separated_completion_crash_frontier side C)"
    using separated_completion_concrete_bad_crash_excludes_replay_derived_at
      [OF bad]
    by blast
  from completion side bad no_replay show ?thesis by blast
qed

lemma bad_crash_execution_for_gap_excludes_execution_replay_derived_at:
  assumes bad: "bad_crash_execution_for_gap G s"
  shows "\<not> execution_replay_derived_at s \<sigma> (osg_crash_at G)"
proof -
  from bad have obs: "observable_mismatch s (osg_crash_at G) (osg_key G)"
    by (simp add: bad_crash_execution_for_gap_def)
  show ?thesis
    by (rule observable_mismatch_excludes_execution_replay_derived_at[OF obs])
qed

theorem non_atomic_no_shared_commit_window_excludes_replay_derived_crash_window:
  assumes window: "non_atomic_no_shared_commit_source_first_window I W"
      and crash: "implementation_crash_enabled_for_gap I W"
  shows "\<not> implementation_replay_derived_crash_window I W"
proof
  assume replay: "implementation_replay_derived_crash_window I W"
  have gap: "implementation_admits_source_first_gap I W"
    by (rule
        non_atomic_no_shared_commit_source_first_window_imp_implementation_admits_source_first_gap
        [OF window])
  from implementation_admits_source_first_gap_with_crash_has_concrete_bad_crash_execution
        [OF gap crash]
  obtain s where trace:
      "dwi_trace I (dwi_initial I) (implementation_gap_crash_labels W) s"
      and bad:
        "bad_crash_execution_for_gap
          (operational_gap_of_implementation_gap I W) (dwi_state I s)"
    by blast
  from replay trace obtain \<sigma> where derived:
    "execution_replay_derived_at (dwi_state I s) \<sigma> (isfg_crash_at W)"
    by (auto simp: implementation_replay_derived_crash_window_def)
  have no_derived:
    "\<not> execution_replay_derived_at
      (dwi_state I s) \<sigma> (isfg_crash_at W)"
    using
      bad_crash_execution_for_gap_excludes_execution_replay_derived_at
        [OF bad, of \<sigma>]
    by (simp add: operational_gap_of_implementation_gap_def)
  with derived show False by simp
qed

definition replay_protected_admitted_source_first_crashes
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "replay_protected_admitted_source_first_crashes I \<longleftrightarrow>
     (\<forall>W. implementation_admits_source_first_gap I W
       \<longrightarrow> implementation_crash_enabled_for_gap I W
       \<longrightarrow> implementation_replay_derived_crash_window I W)"

theorem replay_protected_excludes_non_atomic_no_shared_commit_crash_admissible:
  assumes protected: "replay_protected_admitted_source_first_crashes I"
  shows "\<not> non_atomic_no_shared_commit_crash_admissible_implementation I"
proof
  assume impl: "non_atomic_no_shared_commit_crash_admissible_implementation I"
  from impl obtain W where window:
      "non_atomic_no_shared_commit_source_first_window I W"
      and crash: "implementation_crash_enabled_for_gap I W"
    by (auto simp: non_atomic_no_shared_commit_crash_admissible_implementation_def)
  have gap: "implementation_admits_source_first_gap I W"
    by (rule
        non_atomic_no_shared_commit_source_first_window_imp_implementation_admits_source_first_gap
        [OF window])
  from protected gap crash have replay:
    "implementation_replay_derived_crash_window I W"
    by (simp add: replay_protected_admitted_source_first_crashes_def)
  have "\<not> implementation_replay_derived_crash_window I W"
    by (rule
        non_atomic_no_shared_commit_window_excludes_replay_derived_crash_window
        [OF window crash])
  with replay show False by simp
qed

theorem source_first_crash_capability_crash_admissible_excludes_replay_protected:
  assumes impl: "source_first_crash_capability_crash_admissible_implementation I"
  shows "\<not> replay_protected_admitted_source_first_crashes I"
proof
  assume protected: "replay_protected_admitted_source_first_crashes I"
  from impl obtain W where window: "source_first_crash_capability_window I W"
      and crash: "implementation_crash_enabled_for_gap I W"
    by (auto simp:
        source_first_crash_capability_crash_admissible_implementation_def)
  have no_shared: "non_atomic_no_shared_commit_source_first_window I W"
    by (rule source_first_crash_capability_window_imp_no_shared_commit_window
        [OF window])
  have gap: "implementation_admits_source_first_gap I W"
    by (rule source_first_crash_capability_window_imp_source_first_gap[OF window])
  from protected gap crash have replay:
    "implementation_replay_derived_crash_window I W"
    by (simp add: replay_protected_admitted_source_first_crashes_def)
  have "\<not> implementation_replay_derived_crash_window I W"
    by (rule
        non_atomic_no_shared_commit_window_excludes_replay_derived_crash_window
        [OF no_shared crash])
  with replay show False by simp
qed


section \<open>Closed capability witness\<close>

definition stale_update_capability_implementation
  :: "((nat, nat) dw_exec_state, nat, nat) dual_write_implementation"
where
  "stale_update_capability_implementation =
     canonical_dw_implementation
      (initial_exec_state
        (plan_base stale_update_plan)
        (plan_scope stale_update_plan)
        (plan_finish stale_update_plan))"

definition stale_update_capability_window
  :: "(nat, nat) implementation_source_first_gap_witness"
where
  "stale_update_capability_window =
     implementation_gap_of_operational_gap
      (operational_gap_of_plan stale_update_plan)"

lemma stale_update_capability_window_source_ack_completion_gap:
  "source_ack_enqueue_downstream_completion_gap
    stale_update_capability_implementation stale_update_capability_window"
proof -
  let ?s0 =
    "initial_exec_state
      (plan_base stale_update_plan)
      (plan_scope stale_update_plan)
      (plan_finish stale_update_plan)"
  let ?src = "plan_after_source_state stale_update_plan"
  let ?ack = "plan_after_ack_state stale_update_plan"
  let ?enq = "plan_after_enqueue_state stale_update_plan"
  let ?down =
    "?enq\<lparr>exec_down_hist := exec_down_hist ?enq @ [(ec3, Update 0 2)],
          exec_pending := exec_pending ?enq - {(ec3, Update 0 2)}\<rparr>"
  have source:
    "dwi_step stale_update_capability_implementation ?s0
      (DoSource ec1 (Update 0 2)) ?src"
  proof -
    have raw:
      "dw_exec_step ?s0 (DoSource ec1 (Update 0 2))
        (?s0\<lparr>exec_src_hist :=
          exec_src_hist ?s0 @ [(ec1, Update 0 2)]\<rparr>)"
      by (rule dw_exec_step.do_source)
         (simp add: stale_update_plan_def initial_exec_state_def)
    thus ?thesis
      by (simp add: stale_update_capability_implementation_def
                    canonical_dw_implementation_def
                    plan_after_source_state_def stale_update_plan_def
                    plan_prefix_state_def initial_exec_state_def)
  qed
  have ack:
    "dwi_step stale_update_capability_implementation ?src
      (Ack ec1 (Update 0 2)) ?ack"
  proof -
    have raw:
      "dw_exec_step ?src (Ack ec1 (Update 0 2))
        (?src\<lparr>exec_acked :=
          exec_acked ?src @ [(ec1, Update 0 2)]\<rparr>)"
      by (rule dw_exec_step.ack)
         (simp_all add: plan_after_source_state_def stale_update_plan_def
                        plan_prefix_state_def initial_exec_state_def)
    thus ?thesis
      by (simp add: stale_update_capability_implementation_def
                    canonical_dw_implementation_def
                    plan_after_ack_state_def plan_after_source_state_def
                    plan_prefix_state_def stale_update_plan_def
                    initial_exec_state_def)
  qed
  have enqueue:
    "dwi_step stale_update_capability_implementation ?ack
      (EnqueueDownstream ec3 (Update 0 2)) ?enq"
  proof -
    have raw:
      "dw_exec_step ?ack (EnqueueDownstream ec3 (Update 0 2))
        (?ack\<lparr>exec_enqueued :=
             exec_enqueued ?ack @ [(ec3, Update 0 2)],
           exec_pending :=
             insert (ec3, Update 0 2) (exec_pending ?ack)\<rparr>)"
      by (rule dw_exec_step.enqueue_downstream)
         (simp add: plan_after_ack_state_def plan_after_source_state_def
                    plan_prefix_state_def stale_update_plan_def
                    initial_exec_state_def)
    thus ?thesis
      by (simp add: stale_update_capability_implementation_def
                    canonical_dw_implementation_def
                    plan_after_enqueue_state_def plan_after_ack_state_def
                    plan_after_source_state_def plan_prefix_state_def
                    stale_update_plan_def
                    initial_exec_state_def)
  qed
  have downstream:
    "dwi_step stale_update_capability_implementation ?enq
      (DoDownstream ec3 (Update 0 2)) ?down"
  proof -
    have raw:
      "dw_exec_step ?enq (DoDownstream ec3 (Update 0 2)) ?down"
      by (rule dw_exec_step.do_downstream)
         (simp_all add: plan_after_enqueue_state_def plan_after_ack_state_def
                        plan_after_source_state_def plan_prefix_state_def
                        stale_update_plan_def
                        initial_exec_state_def)
    thus ?thesis
      by (simp add: stale_update_capability_implementation_def
                    canonical_dw_implementation_def)
  qed
  have pre:
    "dwi_trace stale_update_capability_implementation
      (dwi_initial stale_update_capability_implementation)
      (isfg_pre stale_update_capability_window) ?s0"
    unfolding stale_update_capability_implementation_def
      stale_update_capability_window_def canonical_dw_implementation_def
      operational_gap_of_plan_def implementation_gap_of_operational_gap_def
      stale_update_plan_def
    by (simp add: dwi_trace.dwi_trace_refl)
  have gap_eq:
    "isfg_gap stale_update_capability_window =
      [Ack (isfg_source_at stale_update_capability_window)
        (isfg_event stale_update_capability_window),
       EnqueueDownstream (isfg_down_at stale_update_capability_window)
        (isfg_down_event stale_update_capability_window)]"
    by (simp add: stale_update_capability_window_def
                  operational_gap_of_plan_def
                  implementation_gap_of_operational_gap_def
                  stale_update_plan_def)
  show ?thesis
    unfolding source_ack_enqueue_downstream_completion_gap_def
  proof (intro conjI)
    show
      "isfg_gap stale_update_capability_window =
       [Ack (isfg_source_at stale_update_capability_window)
          (isfg_event stale_update_capability_window),
        EnqueueDownstream (isfg_down_at stale_update_capability_window)
          (isfg_down_event stale_update_capability_window)]"
      by (rule gap_eq)
  next
    show "\<exists>s_pre s_src s_ack s_enq s_down.
        dwi_trace stale_update_capability_implementation
          (dwi_initial stale_update_capability_implementation)
          (isfg_pre stale_update_capability_window) s_pre \<and>
        dwi_step stale_update_capability_implementation s_pre
          (DoSource (isfg_source_at stale_update_capability_window)
            (isfg_event stale_update_capability_window)) s_src \<and>
        dwi_step stale_update_capability_implementation s_src
          (Ack (isfg_source_at stale_update_capability_window)
            (isfg_event stale_update_capability_window)) s_ack \<and>
        dwi_step stale_update_capability_implementation s_ack
          (EnqueueDownstream (isfg_down_at stale_update_capability_window)
            (isfg_down_event stale_update_capability_window)) s_enq \<and>
        dwi_step stale_update_capability_implementation s_enq
          (DoDownstream (isfg_down_at stale_update_capability_window)
            (isfg_down_event stale_update_capability_window)) s_down"
      using pre source ack enqueue downstream
      by (intro exI[where x = ?s0] exI[where x = ?src]
          exI[where x = ?ack] exI[where x = ?enq] exI[where x = ?down])
         (simp add: stale_update_capability_window_def
                    operational_gap_of_plan_def
                    implementation_gap_of_operational_gap_def
                    stale_update_plan_def)
  qed
qed

lemma stale_update_capability_window_semantic_prefix:
  "semantic_prefix_crash_source_first_window
    stale_update_capability_implementation stale_update_capability_window"
proof -
  have schedule:
    "source_ack_enqueue_downstream_completion_gap
      stale_update_capability_implementation stale_update_capability_window"
    by (rule stale_update_capability_window_source_ack_completion_gap)
  have refines:
    "dwi_refines_exec stale_update_capability_implementation"
    by (simp add: stale_update_capability_implementation_def)
  have running:
    "running_labels (isfg_pre stale_update_capability_window)"
    by (simp add: stale_update_capability_window_def
                  running_labels_def operational_gap_of_plan_def
                  implementation_gap_of_operational_gap_def
                  stale_update_plan_def)
  have non_atomic:
    "non_atomic_source_effect_window
      stale_update_capability_implementation stale_update_capability_window"
    by (simp add: stale_update_capability_implementation_def
                  stale_update_capability_window_def
                  canonical_dw_implementation_def
                  operational_gap_of_plan_def
                  implementation_gap_of_operational_gap_def
                  stale_update_plan_def
                  initial_exec_state_def
                  non_atomic_source_effect_window_def
                  effective_source_effect_def
                  ec_defs)
  have same:
    "same_downstream_effect
      (isfg_event stale_update_capability_window)
      (isfg_down_event stale_update_capability_window)
      (isfg_key stale_update_capability_window)"
    by (simp add: stale_update_capability_window_def
                  operational_gap_of_plan_def
                  implementation_gap_of_operational_gap_def
                  stale_update_plan_def
                  same_downstream_effect_def)
  have before_down:
    "isfg_crash_at stale_update_capability_window <
     isfg_down_at stale_update_capability_window"
    by (simp add: stale_update_capability_window_def
                  operational_gap_of_plan_def
                  implementation_gap_of_operational_gap_def
                  stale_update_plan_def ec_defs)
  have no_prior:
    "no_prior_downstream_effect_at_crash
      stale_update_capability_implementation stale_update_capability_window"
    by (simp add: stale_update_capability_implementation_def
                  stale_update_capability_window_def
                  canonical_dw_implementation_def
                  operational_gap_of_plan_def
                  implementation_gap_of_operational_gap_def
                  stale_update_plan_def
                  initial_exec_state_def
                  no_prior_downstream_effect_at_crash_def
                  no_visible_key_events_def)
  show ?thesis
    using refines schedule running non_atomic same before_down no_prior
    by (simp add: semantic_prefix_crash_source_first_window_def)
qed

lemma stale_update_capability_window_inhabits_capability:
  "source_first_crash_capability_window
    stale_update_capability_implementation stale_update_capability_window"
  using
    semantic_prefix_crash_source_first_window_imp_adversarial_pending_intent
      [OF stale_update_capability_window_semantic_prefix]
  by (simp add: source_first_crash_capability_window_iff_adversarial_pending_intent)

corollary source_first_crash_capability_class_nonempty:
  "\<exists>(I :: ((nat, nat) dw_exec_state, nat, nat) dual_write_implementation)
      (W :: (nat, nat) implementation_source_first_gap_witness).
      source_first_crash_capability_window I W"
proof -
  have "source_first_crash_capability_window
    stale_update_capability_implementation stale_update_capability_window"
    by (rule stale_update_capability_window_inhabits_capability)
  thus ?thesis by blast
qed

corollary stale_update_capability_implementation_has_concrete_bad_crash_execution:
  "\<exists>s.
      dwi_trace stale_update_capability_implementation
        (dwi_initial stale_update_capability_implementation)
        (implementation_gap_crash_labels stale_update_capability_window) s
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap stale_update_capability_implementation
          stale_update_capability_window)
        (dwi_state stale_update_capability_implementation s)"
proof -
  have closed:
    "crash_closed_implementation stale_update_capability_implementation"
    unfolding stale_update_capability_implementation_def
    by (rule canonical_dw_implementation_crash_closed)
  show ?thesis
    by (rule source_first_crash_capability_window_crash_closed_has_concrete_bad_crash_execution
        [OF stale_update_capability_window_inhabits_capability closed])
qed

end
