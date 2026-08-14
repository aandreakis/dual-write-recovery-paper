(*  Title:       Dual_Write_Delivery_Realism.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Delivery-channel realism for the dual-write execution semantics.  This
    theory keeps the original set-valued pending model as an exactly-once
    projection, while adding an explicit queue/list channel that can duplicate,
    reorder, drop, and partition-delay in-flight downstream work.
*)

theory Dual_Write_Delivery_Realism
  imports Dual_Write_Recovery "HOL-Library.Multiset"
begin

section \<open>Queue delivery state and labels\<close>

type_synonym ('k, 'v) delivery_msg =
  "src_coord \<times> ('k, 'v) source_event"

record ('k, 'v) dw_delivery_state =
  del_exec :: "('k, 'v) dw_exec_state"
  del_pending :: "('k, 'v) delivery_msg list"
  del_partitioned :: bool

datatype ('k, 'v) dw_delivery_label =
    DelSource src_coord "('k, 'v) source_event"
  | DelAck src_coord "('k, 'v) source_event"
  | DelEnqueue src_coord "('k, 'v) source_event"
  | DelDeliver src_coord "('k, 'v) source_event"
  | DelDuplicate src_coord "('k, 'v) source_event"
  | DelDrop src_coord "('k, 'v) source_event"
  | DelReorder "('k, 'v) delivery_msg list"
  | DelPartitionOn
  | DelPartitionOff
  | DelCrash frontier
  | DelRecover
  | DelObserve frontier

definition delivery_set_view_consistent
  :: "('k, 'v) dw_delivery_state \<Rightarrow> bool"
where
  "delivery_set_view_consistent S \<longleftrightarrow>
     exec_pending (del_exec S) = set (del_pending S)"

definition delivery_exactly_once_state
  :: "('k, 'v) dw_delivery_state \<Rightarrow> bool"
where
  "delivery_exactly_once_state S \<longleftrightarrow>
     delivery_set_view_consistent S \<and> distinct (del_pending S)"

fun delivery_to_exec_label
  :: "('k, 'v) dw_delivery_label \<Rightarrow> ('k, 'v) dw_exec_label option"
where
  "delivery_to_exec_label (DelSource c e) = Some (DoSource c e)"
| "delivery_to_exec_label (DelAck c e) = Some (Ack c e)"
| "delivery_to_exec_label (DelEnqueue c e) = Some (EnqueueDownstream c e)"
| "delivery_to_exec_label (DelDeliver c e) = Some (DoDownstream c e)"
| "delivery_to_exec_label (DelDuplicate c e) = None"
| "delivery_to_exec_label (DelDrop c e) = None"
| "delivery_to_exec_label (DelReorder q) = None"
| "delivery_to_exec_label DelPartitionOn = None"
| "delivery_to_exec_label DelPartitionOff = None"
| "delivery_to_exec_label (DelCrash c) = Some (Crash c)"
| "delivery_to_exec_label DelRecover = Some Recover"
| "delivery_to_exec_label (DelObserve f) = Some (Observe f)"

fun delivery_exec_labels
  :: "('k, 'v) dw_delivery_label list \<Rightarrow> ('k, 'v) dw_exec_label list"
where
  "delivery_exec_labels [] = []"
| "delivery_exec_labels (a # xs) =
     (case delivery_to_exec_label a of
        None \<Rightarrow> delivery_exec_labels xs
      | Some b \<Rightarrow> b # delivery_exec_labels xs)"

fun exact_delivery_label :: "('k, 'v) dw_delivery_label \<Rightarrow> bool" where
  "exact_delivery_label (DelSource c e) = True"
| "exact_delivery_label (DelAck c e) = True"
| "exact_delivery_label (DelEnqueue c e) = True"
| "exact_delivery_label (DelDeliver c e) = True"
| "exact_delivery_label (DelDuplicate c e) = False"
| "exact_delivery_label (DelDrop c e) = False"
| "exact_delivery_label (DelReorder q) = False"
| "exact_delivery_label DelPartitionOn = False"
| "exact_delivery_label DelPartitionOff = False"
| "exact_delivery_label (DelCrash c) = True"
| "exact_delivery_label DelRecover = True"
| "exact_delivery_label (DelObserve f) = True"

fun delivery_fault_label :: "('k, 'v) dw_delivery_label \<Rightarrow> bool" where
  "delivery_fault_label (DelDuplicate c e) = True"
| "delivery_fault_label (DelDrop c e) = True"
| "delivery_fault_label (DelReorder q) = True"
| "delivery_fault_label DelPartitionOn = True"
| "delivery_fault_label DelPartitionOff = True"
| "delivery_fault_label (DelObserve f) = True"
| "delivery_fault_label (DelSource c e) = False"
| "delivery_fault_label (DelAck c e) = False"
| "delivery_fault_label (DelEnqueue c e) = False"
| "delivery_fault_label (DelDeliver c e) = False"
| "delivery_fault_label (DelCrash c) = False"
| "delivery_fault_label DelRecover = False"

inductive delivery_step
  :: "('k, 'v) dw_delivery_state \<Rightarrow> ('k, 'v) dw_delivery_label \<Rightarrow>
      ('k, 'v) dw_delivery_state \<Rightarrow> bool"
where
  del_source:
    "exec_status (del_exec S) = Running \<Longrightarrow>
     delivery_step S (DelSource c e)
       (S\<lparr>del_exec :=
          (del_exec S)\<lparr>exec_src_hist :=
            exec_src_hist (del_exec S) @ [(c, e)]\<rparr>\<rparr>)"
| del_ack:
    "\<lbrakk>exec_status (del_exec S) = Running;
      (c, e) \<in> set (exec_src_hist (del_exec S))\<rbrakk> \<Longrightarrow>
     delivery_step S (DelAck c e)
       (S\<lparr>del_exec :=
          (del_exec S)\<lparr>exec_acked :=
            exec_acked (del_exec S) @ [(c, e)]\<rparr>\<rparr>)"
| del_enqueue:
    "exec_status (del_exec S) = Running \<Longrightarrow>
     delivery_step S (DelEnqueue c e)
       (S\<lparr>del_exec :=
          (del_exec S)\<lparr>exec_enqueued :=
              exec_enqueued (del_exec S) @ [(c, e)],
            exec_pending := insert (c, e) (exec_pending (del_exec S))\<rparr>,
          del_pending := del_pending S @ [(c, e)]\<rparr>)"
| del_deliver:
    "\<lbrakk>exec_status (del_exec S) = Running;
      \<not> del_partitioned S;
      del_pending S = (c, e) # q\<rbrakk> \<Longrightarrow>
     delivery_step S (DelDeliver c e)
       (S\<lparr>del_exec :=
          (del_exec S)\<lparr>exec_down_hist :=
              exec_down_hist (del_exec S) @ [(c, e)],
            exec_pending := set q\<rparr>,
          del_pending := q\<rparr>)"
| del_duplicate:
    "(c, e) \<in> set (del_pending S) \<Longrightarrow>
     delivery_step S (DelDuplicate c e)
       (S\<lparr>del_exec :=
          (del_exec S)\<lparr>exec_pending :=
            set (del_pending S @ [(c, e)])\<rparr>,
          del_pending := del_pending S @ [(c, e)]\<rparr>)"
| del_drop:
    "(c, e) \<in> set (del_pending S) \<Longrightarrow>
     delivery_step S (DelDrop c e)
       (S\<lparr>del_exec :=
          (del_exec S)\<lparr>exec_pending :=
            set (remove1 (c, e) (del_pending S))\<rparr>,
          del_pending := remove1 (c, e) (del_pending S)\<rparr>)"
| del_reorder:
    "mset q' = mset (del_pending S) \<Longrightarrow>
     delivery_step S (DelReorder q')
       (S\<lparr>del_exec :=
          (del_exec S)\<lparr>exec_pending := set q'\<rparr>,
          del_pending := q'\<rparr>)"
| del_partition_on:
    "delivery_step S DelPartitionOn (S\<lparr>del_partitioned := True\<rparr>)"
| del_partition_off:
    "delivery_step S DelPartitionOff (S\<lparr>del_partitioned := False\<rparr>)"
| del_crash:
    "exec_status (del_exec S) = Running \<Longrightarrow>
     delivery_step S (DelCrash c)
       (S\<lparr>del_exec := (del_exec S)\<lparr>exec_status := Crashed c\<rparr>\<rparr>)"
| del_recover:
    "exec_status (del_exec S) = Crashed c \<Longrightarrow>
     delivery_step S DelRecover
       (S\<lparr>del_exec := (del_exec S)\<lparr>exec_status := Recovered\<rparr>\<rparr>)"
| del_observe:
    "delivery_step S (DelObserve f) S"

inductive delivery_trace
  :: "('k, 'v) dw_delivery_state \<Rightarrow> ('k, 'v) dw_delivery_label list \<Rightarrow>
      ('k, 'v) dw_delivery_state \<Rightarrow> bool"
where
  delivery_trace_refl:
    "delivery_trace S [] S"
| delivery_trace_step:
    "\<lbrakk>delivery_step S a S'; delivery_trace S' as S''\<rbrakk> \<Longrightarrow>
     delivery_trace S (a # as) S''"

lemma delivery_trace_append:
  assumes "delivery_trace S xs S'"
      and "delivery_trace S' ys S''"
  shows "delivery_trace S (xs @ ys) S''"
  using assms
  by (induction arbitrary: ys S'' rule: delivery_trace.induct)
     (auto intro: delivery_trace.intros)

lemma delivery_step_preserves_set_view:
  assumes step: "delivery_step S a S'"
      and consistent: "delivery_set_view_consistent S"
  shows "delivery_set_view_consistent S'"
  using step consistent
  by (cases rule: delivery_step.cases)
     (auto simp: delivery_set_view_consistent_def)


section \<open>The original set model as the exactly-once specialization\<close>

inductive exactly_once_delivery_trace
  :: "('k, 'v) dw_delivery_state \<Rightarrow> ('k, 'v) dw_delivery_label list \<Rightarrow>
      ('k, 'v) dw_delivery_state \<Rightarrow> bool"
where
  exactly_once_refl:
    "delivery_exactly_once_state S \<Longrightarrow>
     exactly_once_delivery_trace S [] S"
| exactly_once_step:
    "\<lbrakk>delivery_exactly_once_state S;
      delivery_step S a S';
      exact_delivery_label a;
      delivery_exactly_once_state S';
      exactly_once_delivery_trace S' xs S''\<rbrakk> \<Longrightarrow>
     exactly_once_delivery_trace S (a # xs) S''"

lemma exactly_once_delivery_trace_imp_delivery_trace:
  assumes "exactly_once_delivery_trace S xs S'"
  shows "delivery_trace S xs S'"
  using assms
  by (induction rule: exactly_once_delivery_trace.induct)
     (auto intro: delivery_trace.intros)

lemma distinct_cons_set_tail:
  assumes "distinct (x # xs)"
  shows "set xs = set (x # xs) - {x}"
  using assms by auto

lemma exact_delivery_step_refines_dw_exec_step:
  assumes step: "delivery_step S a S'"
      and exact: "exact_delivery_label a"
      and state: "delivery_exactly_once_state S"
      and state': "delivery_exactly_once_state S'"
  shows "\<exists>b.
      delivery_to_exec_label a = Some b
    \<and> dw_exec_step (del_exec S) b (del_exec S')"
  using step exact state state'
proof (induction rule: delivery_step.induct)
  case (del_source S c e)
  have step': "dw_exec_step (del_exec S) (DoSource c e)
      ((del_exec S)\<lparr>exec_src_hist :=
        exec_src_hist (del_exec S) @ [(c, e)]\<rparr>)"
    by (rule dw_exec_step.do_source[OF del_source.hyps])
  show ?case using step' by auto
next
  case (del_ack S c e)
  have step': "dw_exec_step (del_exec S) (Ack c e)
      ((del_exec S)\<lparr>exec_acked :=
        exec_acked (del_exec S) @ [(c, e)]\<rparr>)"
    by (rule dw_exec_step.ack[OF del_ack.hyps])
  show ?case using step' by auto
next
  case (del_enqueue S c e)
  have step': "dw_exec_step (del_exec S) (EnqueueDownstream c e)
      ((del_exec S)\<lparr>exec_enqueued :=
          exec_enqueued (del_exec S) @ [(c, e)],
        exec_pending := insert (c, e) (exec_pending (del_exec S))\<rparr>)"
    by (rule dw_exec_step.enqueue_downstream[OF del_enqueue.hyps])
  show ?case using step' by auto
next
  case (del_deliver S c e q)
  have pending: "(c, e) \<in> exec_pending (del_exec S)"
    using del_deliver.hyps del_deliver.prems
    by (simp add: delivery_exactly_once_state_def
                  delivery_set_view_consistent_def)
  have q_pending:
    "set q = exec_pending (del_exec S) - {(c, e)}"
    using del_deliver.hyps del_deliver.prems
    by (auto simp: delivery_exactly_once_state_def
                   delivery_set_view_consistent_def)
  have step': "dw_exec_step (del_exec S) (DoDownstream c e)
      ((del_exec S)\<lparr>exec_down_hist :=
          exec_down_hist (del_exec S) @ [(c, e)],
        exec_pending := exec_pending (del_exec S) - {(c, e)}\<rparr>)"
    by (rule dw_exec_step.do_downstream[OF del_deliver.hyps(1) pending])
  have final:
    "((del_exec S)\<lparr>exec_down_hist :=
          exec_down_hist (del_exec S) @ [(c, e)],
        exec_pending := exec_pending (del_exec S) - {(c, e)}\<rparr>) =
     ((del_exec S)\<lparr>exec_down_hist :=
          exec_down_hist (del_exec S) @ [(c, e)],
        exec_pending := set q\<rparr>)"
    by (simp add: q_pending)
  show ?case using step' final by auto
next
  case (del_duplicate c e S)
  thus ?case by simp
next
  case (del_drop c e S)
  thus ?case by simp
next
  case (del_reorder q' S)
  thus ?case by simp
next
  case (del_partition_on S)
  thus ?case by simp
next
  case (del_partition_off S)
  thus ?case by simp
next
  case (del_crash S c)
  have step': "dw_exec_step (del_exec S) (Crash c)
      ((del_exec S)\<lparr>exec_status := Crashed c\<rparr>)"
    by (rule dw_exec_step.crash[OF del_crash.hyps])
  show ?case using step' by auto
next
  case (del_recover S c)
  have step': "dw_exec_step (del_exec S) Recover
      ((del_exec S)\<lparr>exec_status := Recovered\<rparr>)"
    by (rule dw_exec_step.recover[OF del_recover.hyps])
  show ?case using step' by auto
next
  case (del_observe S f)
  have step': "dw_exec_step (del_exec S) (Observe f) (del_exec S)"
    by (rule dw_exec_step.observe)
  show ?case using step' by auto
qed

theorem exactly_once_delivery_refines_dw_exec_trace:
  assumes trace: "exactly_once_delivery_trace S xs S'"
  shows
    "dw_exec_trace (del_exec S) (delivery_exec_labels xs) (del_exec S')"
  using trace
proof (induction rule: exactly_once_delivery_trace.induct)
  case (exactly_once_refl S)
  show ?case by (simp add: dw_exec_trace.trace_refl)
next
  case (exactly_once_step S a S' xs S'')
  obtain b where b:
      "delivery_to_exec_label a = Some b"
      and step: "dw_exec_step (del_exec S) b (del_exec S')"
    using exact_delivery_step_refines_dw_exec_step
      [OF exactly_once_step.hyps(2) exactly_once_step.hyps(3)
          exactly_once_step.hyps(1) exactly_once_step.hyps(4)]
    by blast
  have tail:
    "dw_exec_trace (del_exec S') (delivery_exec_labels xs) (del_exec S'')"
    by (rule exactly_once_step.IH)
  show ?case
    using dw_exec_trace.trace_step[OF step tail] b by simp
qed


section \<open>Fault schedules preserve bad-crash opportunity\<close>

lemma delivery_fault_step_preserves_proto:
  assumes step: "delivery_step S a S'"
      and fault: "delivery_fault_label a"
  shows
    "proto_of_exec_at (del_exec S') c = proto_of_exec_at (del_exec S) c"
  using step fault
  by (induction rule: delivery_step.induct)
     (simp_all add: proto_of_exec_at_def store2_of_exec_def fun_eq_iff)

lemma delivery_fault_step_preserves_status:
  assumes step: "delivery_step S a S'"
      and fault: "delivery_fault_label a"
  shows "exec_status (del_exec S') = exec_status (del_exec S)"
  using step fault
  by (induction rule: delivery_step.induct) auto

lemma delivery_fault_step_preserves_finish:
  assumes step: "delivery_step S a S'"
      and fault: "delivery_fault_label a"
  shows "exec_finish (del_exec S') = exec_finish (del_exec S)"
  using step fault
  by (induction rule: delivery_step.induct) auto

lemma delivery_fault_trace_preserves_proto:
  assumes trace: "delivery_trace S xs S'"
      and faults: "list_all delivery_fault_label xs"
  shows
    "proto_of_exec_at (del_exec S') c = proto_of_exec_at (del_exec S) c"
  using trace faults
proof (induction rule: delivery_trace.induct)
  case (delivery_trace_refl S)
  show ?case by simp
next
  case (delivery_trace_step S a S' xs S'')
  have fault_a: "delivery_fault_label a"
    using delivery_trace_step.prems by simp
  have faults_xs: "list_all delivery_fault_label xs"
    using delivery_trace_step.prems by simp
  have step_proto:
    "proto_of_exec_at (del_exec S') c = proto_of_exec_at (del_exec S) c"
    by (rule delivery_fault_step_preserves_proto
        [OF delivery_trace_step.hyps(1) fault_a])
  have tail_proto:
    "proto_of_exec_at (del_exec S'') c = proto_of_exec_at (del_exec S') c"
    by (rule delivery_trace_step.IH[OF faults_xs])
  from tail_proto step_proto show ?case by simp
qed

lemma delivery_fault_trace_preserves_status:
  assumes trace: "delivery_trace S xs S'"
      and faults: "list_all delivery_fault_label xs"
  shows "exec_status (del_exec S') = exec_status (del_exec S)"
  using trace faults
proof (induction rule: delivery_trace.induct)
  case (delivery_trace_refl S)
  show ?case by simp
next
  case (delivery_trace_step S a S' xs S'')
  have fault_a: "delivery_fault_label a"
    using delivery_trace_step.prems by simp
  have faults_xs: "list_all delivery_fault_label xs"
    using delivery_trace_step.prems by simp
  have step_status:
    "exec_status (del_exec S') = exec_status (del_exec S)"
    by (rule delivery_fault_step_preserves_status
        [OF delivery_trace_step.hyps(1) fault_a])
  have tail_status:
    "exec_status (del_exec S'') = exec_status (del_exec S')"
    by (rule delivery_trace_step.IH[OF faults_xs])
  from tail_status step_status show ?case by simp
qed

lemma delivery_fault_trace_preserves_finish:
  assumes trace: "delivery_trace S xs S'"
      and faults: "list_all delivery_fault_label xs"
  shows "exec_finish (del_exec S') = exec_finish (del_exec S)"
  using trace faults
proof (induction rule: delivery_trace.induct)
  case (delivery_trace_refl S)
  show ?case by simp
next
  case (delivery_trace_step S a S' xs S'')
  have fault_a: "delivery_fault_label a"
    using delivery_trace_step.prems by simp
  have faults_xs: "list_all delivery_fault_label xs"
    using delivery_trace_step.prems by simp
  have step_finish:
    "exec_finish (del_exec S') = exec_finish (del_exec S)"
    by (rule delivery_fault_step_preserves_finish
        [OF delivery_trace_step.hyps(1) fault_a])
  have tail_finish:
    "exec_finish (del_exec S'') = exec_finish (del_exec S')"
    by (rule delivery_trace_step.IH[OF faults_xs])
  from tail_finish step_finish show ?case by simp
qed

theorem delivery_faults_preserve_bad_crash_enabled:
  assumes enabled: "bad_crash_enabled (del_exec S) c k"
      and trace: "delivery_trace S xs S'"
      and faults: "list_all delivery_fault_label xs"
  shows "bad_crash_enabled (del_exec S') c k"
proof -
  have proto:
    "proto_of_exec_at (del_exec S') c = proto_of_exec_at (del_exec S) c"
    by (rule delivery_fault_trace_preserves_proto[OF trace faults])
  have status:
    "exec_status (del_exec S') = exec_status (del_exec S)"
    by (rule delivery_fault_trace_preserves_status[OF trace faults])
  have finish:
    "exec_finish (del_exec S') = exec_finish (del_exec S)"
    by (rule delivery_fault_trace_preserves_finish[OF trace faults])
  from enabled proto status finish show ?thesis
    by (auto simp: bad_crash_enabled_def)
qed

theorem delivery_faults_have_bad_crash_extension:
  assumes enabled: "bad_crash_enabled (del_exec S) c k"
      and trace: "delivery_trace S xs S'"
      and faults: "list_all delivery_fault_label xs"
  shows "\<exists>S''.
      delivery_trace S (xs @ [DelCrash c]) S''
    \<and> observable_mismatch (del_exec S'') c k
    \<and> diverges (proto_of_exec_at (del_exec S'') c) c"
proof -
  have enabled':
    "bad_crash_enabled (del_exec S') c k"
    by (rule delivery_faults_preserve_bad_crash_enabled[OF assms])
  let ?S'' =
    "S'\<lparr>del_exec :=
       (del_exec S')\<lparr>exec_status := Crashed c\<rparr>\<rparr>"
  have crash_step: "delivery_step S' (DelCrash c) ?S''"
    using enabled'
    by (auto simp: bad_crash_enabled_def intro: delivery_step.del_crash)
  have crash_trace: "delivery_trace S' [DelCrash c] ?S''"
    by (rule delivery_trace.delivery_trace_step
        [OF crash_step delivery_trace.delivery_trace_refl])
  have total_trace:
    "delivery_trace S (xs @ [DelCrash c]) ?S''"
    by (rule delivery_trace_append[OF trace crash_trace])
  have obs: "observable_mismatch (del_exec ?S'') c k"
    using enabled'
    by (simp add: bad_crash_enabled_def observable_mismatch_def)
  have div: "diverges (proto_of_exec_at (del_exec ?S'') c) c"
    by (rule observable_mismatch_imp_diverges[OF obs])
  from total_trace obs div show ?thesis by blast
qed


section \<open>Positive replay premises over the generalized channel\<close>

definition delivery_deduplicating_apply
  :: "('k, 'v) dw_delivery_state \<Rightarrow> bool"
where
  "delivery_deduplicating_apply S \<longleftrightarrow>
     mset (exec_down_hist (del_exec S))
       \<subseteq># mset (exec_enqueued (del_exec S))"

definition delivery_source_ordered_apply
  :: "('k, 'v) dw_delivery_state \<Rightarrow> bool"
where
  "delivery_source_ordered_apply S \<longleftrightarrow>
     (\<exists>q. exec_enqueued (del_exec S)
          = exec_down_hist (del_exec S) @ q)"

definition delivery_eventual_redelivery
  :: "('k, 'v) dw_delivery_state \<Rightarrow> frontier \<Rightarrow> bool"
where
  "delivery_eventual_redelivery S f \<longleftrightarrow>
     no_permanent_recovery_loss (del_exec S) f"

definition delivery_positive_replay_premises
  :: "('k, 'v) dw_delivery_state \<Rightarrow> frontier \<Rightarrow> bool"
where
  "delivery_positive_replay_premises S f \<longleftrightarrow>
     delivery_deduplicating_apply S
   \<and> delivery_source_ordered_apply S
   \<and> delivery_eventual_redelivery S f"

inductive delivery_reconcile_step
  :: "('k, 'v) dw_delivery_state \<Rightarrow> frontier \<Rightarrow>
      ('k, 'v) dw_delivery_state \<Rightarrow> bool"
where
  delivery_reconcile:
    "recovery_reconcile_step (del_exec S) f s' \<Longrightarrow>
     delivery_reconcile_step S f
       (S\<lparr>del_exec := s', del_pending := []\<rparr>)"

lemma delivery_reconcile_redelivers:
  assumes step: "delivery_reconcile_step S f S'"
  shows "recovery_redelivers_source_history (del_exec S) (del_exec S')"
  using step
  by (cases rule: delivery_reconcile_step.cases)
     (auto intro: recovery_reconcile_step_redelivers)

lemma delivery_reconcile_clears_pending:
  assumes step: "delivery_reconcile_step S f S'"
  shows "del_pending S' = [] \<and> exec_pending (del_exec S') = {}"
  using step
proof (cases rule: delivery_reconcile_step.cases)
  case (delivery_reconcile s')
  then have redelivery:
    "recovery_redelivers_source_history (del_exec S) s'"
    by (auto intro: recovery_reconcile_step_redelivers)
  from delivery_reconcile redelivery show ?thesis
    by (auto simp: recovery_redelivers_source_history_def)
qed

theorem delivery_reconcile_no_divergence:
  assumes step: "delivery_reconcile_step S f S'"
  shows "\<not> diverges (proto_of_exec_at (del_exec S') f) f"
  by (rule recovery_redelivery_no_divergence
      [OF delivery_reconcile_redelivers[OF step]])

theorem delivery_positive_premises_temporal_convergence:
  assumes pos: "delivery_positive_replay_premises S f"
  shows "\<exists>wait s_wait s_repaired.
      list_all recovery_observation_label wait
    \<and> dw_exec_trace (del_exec S) wait s_wait
    \<and> recovery_reconcile_step s_wait f s_repaired
    \<and> recovery_temporal_trace (del_exec S)
        (map Recovery_Label wait @ [Recovery_Reconcile f]) s_repaired
    \<and> exec_status s_repaired = Recovered
    \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at s_repaired f) f k)
    \<and> \<not> diverges (proto_of_exec_at s_repaired f) f"
  using no_permanent_recovery_loss_temporal_convergence
    [of "del_exec S" f] pos
  by (auto simp: delivery_positive_replay_premises_def
                 delivery_eventual_redelivery_def)

lemma recovery_observation_trace_from_running_status:
  assumes trace: "dw_exec_trace s xs s'"
      and labels: "list_all recovery_observation_label xs"
      and status: "exec_status s = Running"
  shows "exec_status s' = Running"
  using trace labels status
proof (induction rule: dw_exec_trace.induct)
  case (trace_refl s)
  show ?case using trace_refl.prems by simp
next
  case (trace_step s a s' xs s'')
  have label_a: "recovery_observation_label a"
    using trace_step.prems by simp
  have labels_xs: "list_all recovery_observation_label xs"
    using trace_step.prems by simp
  have status_mid: "exec_status s' = Running"
    using trace_step.hyps(1) label_a trace_step.prems
    by (cases rule: dw_exec_step.cases) auto
  show ?case
    by (rule trace_step.IH[OF labels_xs status_mid])
qed

lemma running_state_no_permanent_recovery_loss:
  assumes status: "exec_status s = Running"
  shows "\<not> no_permanent_recovery_loss s f"
proof
  assume no_loss: "no_permanent_recovery_loss s f"
  then obtain wait s_wait s_repaired where labels:
      "list_all recovery_observation_label wait"
      and trace: "dw_exec_trace s wait s_wait"
      and reconcile: "recovery_reconcile_step s_wait f s_repaired"
    by (auto simp: no_permanent_recovery_loss_def)
  have running: "exec_status s_wait = Running"
    by (rule recovery_observation_trace_from_running_status
        [OF trace labels status])
  with reconcile show False
    by (cases rule: recovery_reconcile_step.cases) auto
qed


section \<open>Closed witnesses for delivery realism\<close>

definition delivery_msg0 :: "(nat, nat) delivery_msg" where
  "delivery_msg0 = (ec1, Insert (0::nat) (2::nat))"

definition delivery_msg1 :: "(nat, nat) delivery_msg" where
  "delivery_msg1 = (ec2, Insert (1::nat) (7::nat))"

definition duplicate_reorder_loss_delivery_start
  :: "(nat, nat) dw_delivery_state"
where
  "duplicate_reorder_loss_delivery_start =
     \<lparr>del_exec =
        initial_exec_state (\<lambda>(_::nat). None) {0::nat} ec2,
      del_pending = [],
      del_partitioned = False\<rparr>"

definition duplicate_reorder_loss_bad_crash_labels
  :: "(nat, nat) dw_delivery_label list"
where
  "duplicate_reorder_loss_bad_crash_labels =
     [DelSource ec1 (Insert (0::nat) (2::nat)),
      DelAck ec1 (Insert (0::nat) (2::nat)),
      DelEnqueue ec1 (Insert (0::nat) (2::nat)),
      DelEnqueue ec2 (Insert (1::nat) (7::nat)),
      DelDuplicate ec1 (Insert (0::nat) (2::nat)),
      DelReorder [delivery_msg1, delivery_msg0, delivery_msg0],
      DelDrop ec1 (Insert (0::nat) (2::nat)),
      DelPartitionOn,
      DelCrash ec1]"

definition duplicate_reorder_loss_bad_crash_final
  :: "(nat, nat) dw_delivery_state"
where
  "duplicate_reorder_loss_bad_crash_final =
     \<lparr>del_exec =
        (initial_exec_state (\<lambda>(_::nat). None) {0::nat} ec2)
          \<lparr>exec_src_hist := [delivery_msg0],
            exec_enqueued := [delivery_msg0, delivery_msg1],
            exec_pending := set [delivery_msg1, delivery_msg0],
            exec_acked := [delivery_msg0],
            exec_status := Crashed ec1\<rparr>,
      del_pending = [delivery_msg1, delivery_msg0],
      del_partitioned = True\<rparr>"

lemma duplicate_reorder_loss_delivery_trace:
  "delivery_trace duplicate_reorder_loss_delivery_start
     duplicate_reorder_loss_bad_crash_labels
     duplicate_reorder_loss_bad_crash_final"
  unfolding duplicate_reorder_loss_delivery_start_def
    duplicate_reorder_loss_bad_crash_labels_def
    duplicate_reorder_loss_bad_crash_final_def
    delivery_msg0_def delivery_msg1_def
  apply (rule delivery_trace.delivery_trace_step)
   apply (rule delivery_step.del_source)
   apply (simp add: initial_exec_state_def)
  apply (rule delivery_trace.delivery_trace_step)
   apply (rule delivery_step.del_ack)
    apply (simp add: initial_exec_state_def)
   apply simp
  apply (rule delivery_trace.delivery_trace_step)
   apply (rule delivery_step.del_enqueue)
   apply (simp add: initial_exec_state_def)
  apply (rule delivery_trace.delivery_trace_step)
   apply (rule delivery_step.del_enqueue)
   apply (simp add: initial_exec_state_def)
  apply (rule delivery_trace.delivery_trace_step)
   apply (rule delivery_step.del_duplicate)
   apply simp
  apply (rule delivery_trace.delivery_trace_step)
   apply (rule delivery_step.del_reorder)
   apply simp
  apply (rule delivery_trace.delivery_trace_step)
   apply (rule delivery_step.del_drop)
   apply (simp add: ec_defs)
  apply (rule delivery_trace.delivery_trace_step)
   apply (rule delivery_step.del_partition_on)
  apply (rule delivery_trace.delivery_trace_step)
   apply (rule delivery_step.del_crash)
   apply (simp add: initial_exec_state_def)
  apply (simp add: delivery_trace.delivery_trace_refl
                   initial_exec_state_def ec_defs)
  done

lemma duplicate_reorder_loss_bad_crash_observable:
  "observable_mismatch
    (del_exec duplicate_reorder_loss_bad_crash_final) ec1 (0::nat)"
  by (rule observable_mismatchI)
     (simp_all add: duplicate_reorder_loss_bad_crash_final_def
                    delivery_msg0_def delivery_msg1_def initial_exec_state_def
                    store2_of_exec_def Src_single_event_at_key
                    Src_def latest_src_event_def Let_def ec_defs)

corollary duplicate_reorder_loss_delivery_bad_crash_witness:
  "\<exists>S.
      delivery_trace duplicate_reorder_loss_delivery_start
        duplicate_reorder_loss_bad_crash_labels S
    \<and> observable_mismatch (del_exec S) ec1 (0::nat)
    \<and> diverges (proto_of_exec_at (del_exec S) ec1) ec1"
proof -
  have div:
    "diverges
      (proto_of_exec_at
        (del_exec duplicate_reorder_loss_bad_crash_final) ec1) ec1"
    by (rule observable_mismatch_imp_diverges
        [OF duplicate_reorder_loss_bad_crash_observable])
  from duplicate_reorder_loss_delivery_trace
    duplicate_reorder_loss_bad_crash_observable div show ?thesis
    by blast
qed

definition delivery_running_mismatch_no_redelivery_state
  :: "(nat, nat) dw_delivery_state"
where
  "delivery_running_mismatch_no_redelivery_state =
     \<lparr>del_exec =
        recovery_source_first_empty_recovered\<lparr>exec_status := Running\<rparr>,
      del_pending = [],
      del_partitioned = False\<rparr>"

lemma delivery_running_mismatch_no_redelivery_diverges:
  "diverges
    (proto_of_exec_at
      (del_exec delivery_running_mismatch_no_redelivery_state) ec1) ec1"
proof -
  have mismatch:
    "mismatch_at
      (proto_of_exec_at
        (del_exec delivery_running_mismatch_no_redelivery_state) ec1)
      ec1 (0::nat)"
    using recovery_source_first_empty_recovered_has_mismatch
    by (simp add: delivery_running_mismatch_no_redelivery_state_def)
  have le_fin:
    "ec1 \<le>
      pfin
        (proto_of_exec_at
          (del_exec delivery_running_mismatch_no_redelivery_state) ec1)"
    by (simp add: delivery_running_mismatch_no_redelivery_state_def
                  proto_of_exec_at_def recovery_source_first_empty_recovered_def
                  recovery_source_first_empty_crashed_def source_crashed_state_def
                  after_source_ack_state_def after_source_state_def
                  initial_exec_state_def)
  from le_fin mismatch show ?thesis
    by (auto simp: diverges_iff_mismatch_at)
qed

corollary delivery_no_permanent_loss_premise_load_bearing_witness:
  "\<exists>S :: (nat, nat) dw_delivery_state.
      delivery_deduplicating_apply S
    \<and> delivery_source_ordered_apply S
    \<and> diverges (proto_of_exec_at (del_exec S) ec1) ec1
    \<and> \<not> delivery_eventual_redelivery S ec1"
proof -
  let ?S = delivery_running_mismatch_no_redelivery_state
  have dedup: "delivery_deduplicating_apply ?S"
    by (simp add: delivery_deduplicating_apply_def
                  delivery_running_mismatch_no_redelivery_state_def
                  recovery_source_first_empty_recovered_def
                  recovery_source_first_empty_crashed_def
                  source_crashed_state_def after_source_ack_state_def
                  after_source_state_def initial_exec_state_def)
  have ordered: "delivery_source_ordered_apply ?S"
    by (simp add: delivery_source_ordered_apply_def
                  delivery_running_mismatch_no_redelivery_state_def
                  recovery_source_first_empty_recovered_def
                  recovery_source_first_empty_crashed_def
                  source_crashed_state_def after_source_ack_state_def
                  after_source_state_def initial_exec_state_def)
  have div:
    "diverges (proto_of_exec_at (del_exec ?S) ec1) ec1"
    by (rule delivery_running_mismatch_no_redelivery_diverges)
  have no_redelivery: "\<not> delivery_eventual_redelivery ?S ec1"
    by (simp add: delivery_eventual_redelivery_def
                  delivery_running_mismatch_no_redelivery_state_def
                  running_state_no_permanent_recovery_loss)
  have packed:
    "delivery_deduplicating_apply ?S
   \<and> delivery_source_ordered_apply ?S
   \<and> diverges (proto_of_exec_at (del_exec ?S) ec1) ec1
   \<and> \<not> delivery_eventual_redelivery ?S ec1"
    using dedup ordered div no_redelivery by blast
  show ?thesis
    apply (rule exI[where x = delivery_running_mismatch_no_redelivery_state])
    using packed
    apply simp
    done
qed


subsection \<open>Positive witness: both apply premises at a NONEMPTY applied channel\<close>

text \<open>The load-bearing witness above satisfies the two positive apply premises
  with an entirely EMPTY channel.  The reachable state below closes that
  witness-adequacy gap: one source commit is enqueued and then actually
  applied, so the applied history is nonempty and both premises hold
  non-vacuously.\<close>

definition delivery_nonempty_apply_labels
  :: "(nat, nat) dw_delivery_label list"
where
  "delivery_nonempty_apply_labels =
     [DelSource ec1 (Insert (0::nat) (2::nat)),
      DelEnqueue ec1 (Insert (0::nat) (2::nat)),
      DelDeliver ec1 (Insert (0::nat) (2::nat))]"

definition delivery_nonempty_apply_state
  :: "(nat, nat) dw_delivery_state"
where
  "delivery_nonempty_apply_state =
     \<lparr>del_exec =
        (initial_exec_state (\<lambda>(_::nat). None) {0::nat} ec2)
          \<lparr>exec_src_hist := [delivery_msg0],
            exec_enqueued := [delivery_msg0],
            exec_down_hist := [delivery_msg0]\<rparr>,
      del_pending = [],
      del_partitioned = False\<rparr>"

lemma delivery_nonempty_apply_trace:
  "delivery_trace duplicate_reorder_loss_delivery_start
     delivery_nonempty_apply_labels
     delivery_nonempty_apply_state"
  unfolding duplicate_reorder_loss_delivery_start_def
    delivery_nonempty_apply_labels_def
    delivery_nonempty_apply_state_def delivery_msg0_def
  apply (rule delivery_trace.delivery_trace_step)
   apply (rule delivery_step.del_source)
   apply (simp add: initial_exec_state_def)
  apply (rule delivery_trace.delivery_trace_step)
   apply (rule delivery_step.del_enqueue)
   apply (simp add: initial_exec_state_def)
  apply (rule delivery_trace.delivery_trace_step)
   apply (rule delivery_step.del_deliver)
     apply (simp add: initial_exec_state_def)
    apply simp
   apply simp
  apply (simp add: delivery_trace.delivery_trace_refl
                   initial_exec_state_def ec_defs)
  done

lemma delivery_nonempty_apply_deduplicating:
  "delivery_deduplicating_apply delivery_nonempty_apply_state"
  by (simp add: delivery_deduplicating_apply_def
                delivery_nonempty_apply_state_def)

lemma delivery_nonempty_apply_source_ordered:
  "delivery_source_ordered_apply delivery_nonempty_apply_state"
  unfolding delivery_source_ordered_apply_def
  by (intro exI[where x = "[]"])
     (simp add: delivery_nonempty_apply_state_def)

corollary delivery_positive_apply_premises_nonempty_witness:
  "\<exists>S :: (nat, nat) dw_delivery_state.
      delivery_trace duplicate_reorder_loss_delivery_start
        delivery_nonempty_apply_labels S
    \<and> exec_down_hist (del_exec S) \<noteq> []
    \<and> delivery_deduplicating_apply S
    \<and> delivery_source_ordered_apply S"
proof -
  have nonempty: "exec_down_hist (del_exec delivery_nonempty_apply_state) \<noteq> []"
    by (simp add: delivery_nonempty_apply_state_def)
  from delivery_nonempty_apply_trace nonempty
       delivery_nonempty_apply_deduplicating
       delivery_nonempty_apply_source_ordered
  show ?thesis by blast
qed

end
