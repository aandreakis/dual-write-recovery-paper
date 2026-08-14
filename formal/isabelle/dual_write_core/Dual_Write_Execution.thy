(*  Title:       Dual_Write_Execution.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Main execution-theorem layer for uncoordinated dual writes. States carry
    durable source/downstream histories, enqueued and pending downstream work,
    acknowledgement history, and crash status. The theory packages the raw
    small-step relation with an admissible wellformed trace wrapper, proves the
    observation/crash bridge, selects bad prefixes for side-parametric
    separable non-atomic completions, and lifts them to concrete bad-crash
    traces under crash closure.  Crash closure (crash_closed_implementation)
    is stated on the trace-reachable fragment: the Crash-enabledness
    obligation binds reachable Running in-range states only.
*)

theory Dual_Write_Execution
  imports Dual_Write_Core
begin

section \<open>Small-step executions and separable bad-crash completions\<close>

datatype dw_run_status =
    Running
  | Crashed frontier
  | Recovered

datatype ('k, 'v) dw_exec_label =
    DoSource src_coord "('k, 'v) source_event"
  | EnqueueDownstream src_coord "('k, 'v) source_event"
  | DoDownstream src_coord "('k, 'v) source_event"
  | Ack src_coord "('k, 'v) source_event"
  | Crash frontier
  | Recover
  | Observe frontier

datatype dual_write_effect_side =
    Source_Effect
  | Downstream_Effect

fun source_exec_labels :: "('k, 'v) src_history \<Rightarrow> ('k, 'v) dw_exec_label list" where
  "source_exec_labels [] = []"
| "source_exec_labels ((c, e) # xs) = DoSource c e # source_exec_labels xs"

fun downstream_exec_labels :: "('k, 'v) src_history \<Rightarrow> ('k, 'v) dw_exec_label list" where
  "downstream_exec_labels [] = []"
| "downstream_exec_labels ((c, e) # xs) =
     EnqueueDownstream c e # DoDownstream c e # downstream_exec_labels xs"

fun src_hist_of_labels :: "('k, 'v) dw_exec_label list \<Rightarrow> ('k, 'v) src_history" where
  "src_hist_of_labels [] = []"
| "src_hist_of_labels (DoSource c e # xs) = (c, e) # src_hist_of_labels xs"
| "src_hist_of_labels (EnqueueDownstream c e # xs) = src_hist_of_labels xs"
| "src_hist_of_labels (DoDownstream c e # xs) = src_hist_of_labels xs"
| "src_hist_of_labels (Ack c e # xs) = src_hist_of_labels xs"
| "src_hist_of_labels (Crash c # xs) = src_hist_of_labels xs"
| "src_hist_of_labels (Recover # xs) = src_hist_of_labels xs"
| "src_hist_of_labels (Observe f # xs) = src_hist_of_labels xs"

fun down_hist_of_labels :: "('k, 'v) dw_exec_label list \<Rightarrow> ('k, 'v) src_history" where
  "down_hist_of_labels [] = []"
| "down_hist_of_labels (DoSource c e # xs) = down_hist_of_labels xs"
| "down_hist_of_labels (EnqueueDownstream c e # xs) = down_hist_of_labels xs"
| "down_hist_of_labels (DoDownstream c e # xs) = (c, e) # down_hist_of_labels xs"
| "down_hist_of_labels (Ack c e # xs) = down_hist_of_labels xs"
| "down_hist_of_labels (Crash c # xs) = down_hist_of_labels xs"
| "down_hist_of_labels (Recover # xs) = down_hist_of_labels xs"
| "down_hist_of_labels (Observe f # xs) = down_hist_of_labels xs"

fun enqueued_hist_of_labels :: "('k, 'v) dw_exec_label list \<Rightarrow> ('k, 'v) src_history" where
  "enqueued_hist_of_labels [] = []"
| "enqueued_hist_of_labels (DoSource c e # xs) = enqueued_hist_of_labels xs"
| "enqueued_hist_of_labels (EnqueueDownstream c e # xs) =
     (c, e) # enqueued_hist_of_labels xs"
| "enqueued_hist_of_labels (DoDownstream c e # xs) = enqueued_hist_of_labels xs"
| "enqueued_hist_of_labels (Ack c e # xs) = enqueued_hist_of_labels xs"
| "enqueued_hist_of_labels (Crash c # xs) = enqueued_hist_of_labels xs"
| "enqueued_hist_of_labels (Recover # xs) = enqueued_hist_of_labels xs"
| "enqueued_hist_of_labels (Observe f # xs) = enqueued_hist_of_labels xs"

fun pending_after_labels
  :: "('k, 'v) dw_exec_label list \<Rightarrow>
      (src_coord \<times> ('k, 'v) source_event) set \<Rightarrow>
      (src_coord \<times> ('k, 'v) source_event) set"
where
  "pending_after_labels [] Q = Q"
| "pending_after_labels (DoSource c e # xs) Q =
     pending_after_labels xs Q"
| "pending_after_labels (EnqueueDownstream c e # xs) Q =
     pending_after_labels xs (insert (c, e) Q)"
| "pending_after_labels (DoDownstream c e # xs) Q =
     pending_after_labels xs (Q - {(c, e)})"
| "pending_after_labels (Ack c e # xs) Q =
     pending_after_labels xs Q"
| "pending_after_labels (Crash c # xs) Q =
     pending_after_labels xs Q"
| "pending_after_labels (Recover # xs) Q =
     pending_after_labels xs Q"
| "pending_after_labels (Observe f # xs) Q =
     pending_after_labels xs Q"

fun acked_hist_of_labels :: "('k, 'v) dw_exec_label list \<Rightarrow> ('k, 'v) src_history" where
  "acked_hist_of_labels [] = []"
| "acked_hist_of_labels (DoSource c e # xs) = acked_hist_of_labels xs"
| "acked_hist_of_labels (EnqueueDownstream c e # xs) = acked_hist_of_labels xs"
| "acked_hist_of_labels (DoDownstream c e # xs) = acked_hist_of_labels xs"
| "acked_hist_of_labels (Ack c e # xs) = (c, e) # acked_hist_of_labels xs"
| "acked_hist_of_labels (Crash c # xs) = acked_hist_of_labels xs"
| "acked_hist_of_labels (Recover # xs) = acked_hist_of_labels xs"
| "acked_hist_of_labels (Observe f # xs) = acked_hist_of_labels xs"

definition running_label :: "('k, 'v) dw_exec_label \<Rightarrow> bool" where
  "running_label a \<longleftrightarrow>
     (case a of Crash _ \<Rightarrow> False | Recover \<Rightarrow> False | _ \<Rightarrow> True)"

definition running_labels :: "('k, 'v) dw_exec_label list \<Rightarrow> bool" where
  "running_labels xs \<longleftrightarrow> list_all running_label xs"

lemma src_hist_of_labels_append [simp]:
  "src_hist_of_labels (xs @ ys) =
   src_hist_of_labels xs @ src_hist_of_labels ys"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  thus ?case by (cases a; simp)
qed

lemma down_hist_of_labels_append [simp]:
  "down_hist_of_labels (xs @ ys) =
   down_hist_of_labels xs @ down_hist_of_labels ys"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  thus ?case by (cases a; simp)
qed

lemma enqueued_hist_of_labels_append [simp]:
  "enqueued_hist_of_labels (xs @ ys) =
   enqueued_hist_of_labels xs @ enqueued_hist_of_labels ys"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  thus ?case by (cases a; simp)
qed

lemma pending_after_labels_append [simp]:
  "pending_after_labels (xs @ ys) Q =
   pending_after_labels ys (pending_after_labels xs Q)"
proof (induction xs arbitrary: Q)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  thus ?case by (cases a; simp)
qed

lemma Diff_singleton_insert:
  "A - {x} - B = A - insert x B"
  by auto

lemma acked_hist_of_labels_append [simp]:
  "acked_hist_of_labels (xs @ ys) =
   acked_hist_of_labels xs @ acked_hist_of_labels ys"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  thus ?case by (cases a; simp)
qed

lemma src_hist_of_labels_single_cons [simp]:
  "src_hist_of_labels [a] @ src_hist_of_labels xs =
   src_hist_of_labels (a # xs)"
  by (cases a; simp)

lemma down_hist_of_labels_single_cons [simp]:
  "down_hist_of_labels [a] @ down_hist_of_labels xs =
   down_hist_of_labels (a # xs)"
  by (cases a; simp)

lemma enqueued_hist_of_labels_single_cons [simp]:
  "enqueued_hist_of_labels [a] @ enqueued_hist_of_labels xs =
   enqueued_hist_of_labels (a # xs)"
  by (cases a; simp)

lemma acked_hist_of_labels_single_cons [simp]:
  "acked_hist_of_labels [a] @ acked_hist_of_labels xs =
   acked_hist_of_labels (a # xs)"
  by (cases a; simp)

lemma running_labels_append [simp]:
  "running_labels (xs @ ys) \<longleftrightarrow> running_labels xs \<and> running_labels ys"
  by (simp add: running_labels_def list_all_append)

lemma src_hist_of_source_exec_labels [simp]:
  "src_hist_of_labels (source_exec_labels H) = H"
  by (induction H) (auto split: prod.splits)

lemma down_hist_of_source_exec_labels [simp]:
  "down_hist_of_labels (source_exec_labels H) = []"
  by (induction H) (auto split: prod.splits)

lemma enqueued_hist_of_source_exec_labels [simp]:
  "enqueued_hist_of_labels (source_exec_labels H) = []"
  by (induction H) (auto split: prod.splits)

lemma pending_after_source_exec_labels [simp]:
  "pending_after_labels (source_exec_labels H) Q = Q"
  by (induction H arbitrary: Q) (auto split: prod.splits)

lemma acked_hist_of_source_exec_labels [simp]:
  "acked_hist_of_labels (source_exec_labels H) = []"
  by (induction H) (auto split: prod.splits)

lemma running_labels_source_exec_labels [simp]:
  "running_labels (source_exec_labels H)"
  by (induction H) (auto simp: running_labels_def running_label_def split: prod.splits)

lemma list_all_running_source_exec_labels [simp]:
  "list_all running_label (source_exec_labels H)"
  using running_labels_source_exec_labels[where H = H]
  by (simp add: running_labels_def)

lemma src_hist_of_downstream_exec_labels [simp]:
  "src_hist_of_labels (downstream_exec_labels H) = []"
  by (induction H) (auto split: prod.splits)

lemma down_hist_of_downstream_exec_labels [simp]:
  "down_hist_of_labels (downstream_exec_labels H) = H"
  by (induction H) (auto split: prod.splits)

lemma enqueued_hist_of_downstream_exec_labels [simp]:
  "enqueued_hist_of_labels (downstream_exec_labels H) = H"
  by (induction H) (auto split: prod.splits)

lemma pending_after_downstream_exec_labels [simp]:
  "pending_after_labels (downstream_exec_labels H) Q = Q - set H"
  by (induction H arbitrary: Q) (auto split: prod.splits)

lemma acked_hist_of_downstream_exec_labels [simp]:
  "acked_hist_of_labels (downstream_exec_labels H) = []"
  by (induction H) (auto split: prod.splits)

lemma running_labels_downstream_exec_labels [simp]:
  "running_labels (downstream_exec_labels H)"
  by (induction H) (auto simp: running_labels_def running_label_def split: prod.splits)

lemma list_all_running_downstream_exec_labels [simp]:
  "list_all running_label (downstream_exec_labels H)"
  using running_labels_downstream_exec_labels[where H = H]
  by (simp add: running_labels_def)

record ('k, 'v) dw_exec_state =
  exec_base      :: "'k \<rightharpoonup> 'v"
  exec_src_hist  :: "('k, 'v) src_history"
  exec_down_hist :: "('k, 'v) src_history"
  exec_enqueued  :: "('k, 'v) src_history"
  exec_pending   :: "(src_coord \<times> ('k, 'v) source_event) set"
  exec_scope     :: "'k set"
  exec_finish    :: frontier
  exec_status    :: dw_run_status
  exec_acked     :: "('k, 'v) src_history"

record ('k, 'v) source_first_impl =
  impl_base       :: "'k \<rightharpoonup> 'v"
  impl_scope      :: "'k set"
  impl_finish     :: frontier
  impl_key        :: "'k"
  impl_event      :: "('k, 'v) source_event"
  impl_source_at  :: src_coord
  impl_down_at    :: src_coord

record ('k, 'v) source_first_plan =
  plan_base        :: "'k \<rightharpoonup> 'v"
  plan_scope       :: "'k set"
  plan_finish      :: frontier
  plan_src_prefix  :: "('k, 'v) src_history"
  plan_down_prefix :: "('k, 'v) src_history"
  plan_key         :: "'k"
  plan_event       :: "('k, 'v) source_event"
  plan_down_event  :: "('k, 'v) source_event"
  plan_source_at   :: src_coord
  plan_down_at     :: src_coord

record ('k, 'v) operational_source_first_gap_witness =
  osg_start      :: "('k, 'v) dw_exec_state"
  osg_pre        :: "('k, 'v) dw_exec_label list"
  osg_gap        :: "('k, 'v) dw_exec_label list"
  osg_key        :: "'k"
  osg_source_at  :: src_coord
  osg_event      :: "('k, 'v) source_event"
  osg_down_at    :: src_coord
  osg_down_event :: "('k, 'v) source_event"
  osg_crash_at   :: frontier

record ('s, 'k, 'v) dual_write_implementation =
  dwi_initial :: "'s"
  dwi_step    :: "'s \<Rightarrow> ('k, 'v) dw_exec_label \<Rightarrow> 's \<Rightarrow> bool"
  dwi_state   :: "'s \<Rightarrow> ('k, 'v) dw_exec_state"

record ('k, 'v) implementation_source_first_gap_witness =
  isfg_pre        :: "('k, 'v) dw_exec_label list"
  isfg_gap        :: "('k, 'v) dw_exec_label list"
  isfg_key        :: "'k"
  isfg_source_at  :: src_coord
  isfg_event      :: "('k, 'v) source_event"
  isfg_down_at    :: src_coord
  isfg_down_event :: "('k, 'v) source_event"
  isfg_crash_at   :: frontier

record ('k, 'v) source_first_no_shared_commit_window =
  sfnc_pre        :: "('k, 'v) dw_exec_label list"
  sfnc_key        :: "'k"
  sfnc_source_at  :: src_coord
  sfnc_event      :: "('k, 'v) source_event"
  sfnc_down_at    :: src_coord
  sfnc_down_event :: "('k, 'v) source_event"
  sfnc_crash_at   :: frontier

record ('k, 'v) source_first_separated_completion =
  sfsc_pre        :: "('k, 'v) dw_exec_label list"
  sfsc_key        :: "'k"
  sfsc_source_at  :: src_coord
  sfsc_event      :: "('k, 'v) source_event"
  sfsc_down_at    :: src_coord
  sfsc_down_event :: "('k, 'v) source_event"

record ('k, 'v) separated_dual_write_completion =
  sdwc_pre        :: "('k, 'v) dw_exec_label list"
  sdwc_key        :: "'k"
  sdwc_source_at  :: src_coord
  sdwc_event      :: "('k, 'v) source_event"
  sdwc_down_at    :: src_coord
  sdwc_down_event :: "('k, 'v) source_event"

definition non_atomic_uncoordinated_source_first
  :: "('k, 'v) source_first_impl \<Rightarrow> bool"
where
  "non_atomic_uncoordinated_source_first A \<longleftrightarrow>
     key_of (impl_event A) = impl_key A
   \<and> event_result (impl_event A) \<noteq> impl_base A (impl_key A)
   \<and> impl_key A \<in> impl_scope A
   \<and> impl_source_at A < impl_down_at A
   \<and> impl_down_at A \<le> impl_finish A"

definition unprotected_source_first_dual_write_plan
  :: "('k, 'v) source_first_plan \<Rightarrow> bool"
where
  "unprotected_source_first_dual_write_plan W \<longleftrightarrow>
     same_downstream_effect (plan_event W) (plan_down_event W) (plan_key W)
   \<and> Src (plan_base W) (plan_down_prefix W) (plan_source_at W) (plan_key W)
       \<noteq> event_result (plan_event W)
   \<and> plan_key W \<in> plan_scope W
   \<and> plan_source_at W < plan_down_at W
   \<and> plan_down_at W \<le> plan_finish W"

definition initial_exec_state
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'k set \<Rightarrow> frontier \<Rightarrow> ('k, 'v) dw_exec_state"
where
  "initial_exec_state b K fin =
     \<lparr> exec_base = b,
       exec_src_hist = [],
       exec_down_hist = [],
       exec_enqueued = [],
       exec_pending = {},
       exec_scope = K,
       exec_finish = fin,
       exec_status = Running,
       exec_acked = [] \<rparr>"

definition after_source_state
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'k set \<Rightarrow> frontier \<Rightarrow> src_coord \<Rightarrow>
      ('k, 'v) source_event \<Rightarrow> ('k, 'v) dw_exec_state"
where
  "after_source_state b K fin c e =
     (initial_exec_state b K fin)\<lparr>exec_src_hist := [(c, e)]\<rparr>"

definition after_source_ack_state
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'k set \<Rightarrow> frontier \<Rightarrow> src_coord \<Rightarrow>
      ('k, 'v) source_event \<Rightarrow> ('k, 'v) dw_exec_state"
where
  "after_source_ack_state b K fin c e =
     (after_source_state b K fin c e)\<lparr>exec_acked := [(c, e)]\<rparr>"

definition source_crashed_state
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'k set \<Rightarrow> frontier \<Rightarrow> src_coord \<Rightarrow>
      ('k, 'v) source_event \<Rightarrow> ('k, 'v) dw_exec_state"
where
  "source_crashed_state b K fin c e =
     (after_source_ack_state b K fin c e)\<lparr>exec_status := Crashed c\<rparr>"

definition plan_prefix_state
  :: "('k, 'v) source_first_plan \<Rightarrow> ('k, 'v) dw_exec_state"
where
  "plan_prefix_state W =
     (initial_exec_state (plan_base W) (plan_scope W) (plan_finish W))
       \<lparr> exec_src_hist := plan_src_prefix W,
         exec_down_hist := plan_down_prefix W,
         exec_enqueued := plan_down_prefix W,
         exec_pending := {} \<rparr>"

definition plan_after_source_state
  :: "('k, 'v) source_first_plan \<Rightarrow> ('k, 'v) dw_exec_state"
where
  "plan_after_source_state W =
     (plan_prefix_state W)
       \<lparr> exec_src_hist :=
           plan_src_prefix W @ [(plan_source_at W, plan_event W)] \<rparr>"

definition plan_after_ack_state
  :: "('k, 'v) source_first_plan \<Rightarrow> ('k, 'v) dw_exec_state"
where
  "plan_after_ack_state W =
     (plan_after_source_state W)
       \<lparr>exec_acked := [(plan_source_at W, plan_event W)]\<rparr>"

definition plan_after_enqueue_state
  :: "('k, 'v) source_first_plan \<Rightarrow> ('k, 'v) dw_exec_state"
where
  "plan_after_enqueue_state W =
     (plan_after_ack_state W)
       \<lparr>exec_enqueued :=
          exec_enqueued (plan_after_ack_state W)
          @ [(plan_down_at W, plan_down_event W)],
        exec_pending :=
          insert (plan_down_at W, plan_down_event W)
            (exec_pending (plan_after_ack_state W))\<rparr>"

definition plan_crashed_state
  :: "('k, 'v) source_first_plan \<Rightarrow> ('k, 'v) dw_exec_state"
where
  "plan_crashed_state W =
     (plan_after_enqueue_state W)\<lparr>exec_status := Crashed (plan_source_at W)\<rparr>"

definition source_first_plan_bad_crash_trace
  :: "('k, 'v) source_first_plan \<Rightarrow> ('k, 'v) dw_exec_label list"
where
  "source_first_plan_bad_crash_trace W =
     source_exec_labels (plan_src_prefix W)
   @ downstream_exec_labels (plan_down_prefix W)
   @ [DoSource (plan_source_at W) (plan_event W),
      Ack (plan_source_at W) (plan_event W),
      EnqueueDownstream (plan_down_at W) (plan_down_event W),
      Crash (plan_source_at W)]"

inductive dw_exec_step
  :: "('k, 'v) dw_exec_state \<Rightarrow> ('k, 'v) dw_exec_label \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  do_source:
    "exec_status s = Running \<Longrightarrow>
     dw_exec_step s (DoSource c e)
       (s\<lparr>exec_src_hist := exec_src_hist s @ [(c, e)]\<rparr>)"
| enqueue_downstream:
    "exec_status s = Running \<Longrightarrow>
     dw_exec_step s (EnqueueDownstream c e)
       (s\<lparr>exec_enqueued := exec_enqueued s @ [(c, e)],
          exec_pending := insert (c, e) (exec_pending s)\<rparr>)"
| do_downstream:
    "exec_status s = Running \<Longrightarrow>
     (c, e) \<in> exec_pending s \<Longrightarrow>
     dw_exec_step s (DoDownstream c e)
       (s\<lparr>exec_down_hist := exec_down_hist s @ [(c, e)],
          exec_pending := exec_pending s - {(c, e)}\<rparr>)"
| ack:
    "exec_status s = Running \<Longrightarrow>
     (c, e) \<in> set (exec_src_hist s) \<Longrightarrow>
     dw_exec_step s (Ack c e)
       (s\<lparr>exec_acked := exec_acked s @ [(c, e)]\<rparr>)"
| crash:
    "exec_status s = Running \<Longrightarrow>
     dw_exec_step s (Crash c) (s\<lparr>exec_status := Crashed c\<rparr>)"
| recover:
    "exec_status s = Crashed c \<Longrightarrow>
     dw_exec_step s Recover (s\<lparr>exec_status := Recovered\<rparr>)"
| observe:
    "dw_exec_step s (Observe f) s"

inductive dw_exec_trace
  :: "('k, 'v) dw_exec_state \<Rightarrow> ('k, 'v) dw_exec_label list \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  trace_refl:
    "dw_exec_trace s [] s"
| trace_step:
    "\<lbrakk>dw_exec_step s a s'; dw_exec_trace s' as s''\<rbrakk> \<Longrightarrow>
     dw_exec_trace s (a # as) s''"

inductive dwi_trace
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> 's \<Rightarrow>
      ('k, 'v) dw_exec_label list \<Rightarrow> 's \<Rightarrow> bool"
where
  dwi_trace_refl:
    "dwi_trace I s [] s"
| dwi_trace_step:
    "\<lbrakk>dwi_step I s a s'; dwi_trace I s' as s''\<rbrakk> \<Longrightarrow>
     dwi_trace I s (a # as) s''"

definition dwi_refines_exec
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "dwi_refines_exec I \<longleftrightarrow>
     (\<forall>s a s'.
        dwi_step I s a s'
        \<longrightarrow> dw_exec_step (dwi_state I s) a (dwi_state I s'))"

definition canonical_dw_implementation
  :: "('k, 'v) dw_exec_state \<Rightarrow>
      (('k, 'v) dw_exec_state, 'k, 'v) dual_write_implementation"
where
  "canonical_dw_implementation s =
     \<lparr> dwi_initial = s,
       dwi_step = dw_exec_step,
       dwi_state = (\<lambda>s. s) \<rparr>"

lemma canonical_dw_implementation_refines_exec [simp]:
  "dwi_refines_exec (canonical_dw_implementation s)"
  by (simp add: dwi_refines_exec_def canonical_dw_implementation_def)

lemma dwi_trace_refines_exec:
  assumes refines: "dwi_refines_exec I"
      and trace: "dwi_trace I s xs s'"
  shows "dw_exec_trace (dwi_state I s) xs (dwi_state I s')"
  using trace refines
proof (induction rule: dwi_trace.induct)
  case (dwi_trace_refl I s)
  show ?case by (rule dw_exec_trace.trace_refl)
next
  case (dwi_trace_step I s a s' as s'')
  have step:
    "dw_exec_step (dwi_state I s) a (dwi_state I s')"
    using dwi_trace_step.prems dwi_trace_step.hyps(1)
    by (auto simp: dwi_refines_exec_def)
  have tail:
    "dw_exec_trace (dwi_state I s') as (dwi_state I s'')"
    by (rule dwi_trace_step.IH[OF dwi_trace_step.prems])
  show ?case
    by (rule dw_exec_trace.trace_step[OF step tail])
qed

lemma dw_exec_trace_imp_canonical_dwi_trace:
  assumes trace: "dw_exec_trace s xs s'"
  shows "dwi_trace (canonical_dw_implementation s0) s xs s'"
  using trace
proof (induction arbitrary: s0 rule: dw_exec_trace.induct)
  case (trace_refl s)
  show ?case by (rule dwi_trace.dwi_trace_refl)
next
  case (trace_step s a s' as s'')
  have step:
    "dwi_step (canonical_dw_implementation s0) s a s'"
    using trace_step.hyps(1)
    by (simp add: canonical_dw_implementation_def)
  show ?case
    by (rule dwi_trace.dwi_trace_step[OF step trace_step.IH])
qed

lemma dwi_trace_append:
  assumes "dwi_trace I s as s'"
      and "dwi_trace I s' bs s''"
  shows "dwi_trace I s (as @ bs) s''"
  using assms
  by (induction arbitrary: bs s'' rule: dwi_trace.induct)
     (auto intro: dwi_trace.intros)

lemma dw_exec_trace_append:
  assumes "dw_exec_trace s as s'"
      and "dw_exec_trace s' bs s''"
  shows "dw_exec_trace s (as @ bs) s''"
  using assms
  by (induction arbitrary: bs s'' rule: dw_exec_trace.induct)
     (auto intro: dw_exec_trace.intros)

lemma dw_exec_trace_NilD:
  assumes "dw_exec_trace s [] s'"
  shows "s' = s"
  using assms
  by cases auto

lemma dw_exec_step_deterministic:
  assumes "dw_exec_step s a s1"
      and "dw_exec_step s a t2"
  shows "s1 = t2"
  using assms
  by (induction arbitrary: t2 rule: dw_exec_step.induct)
     (auto elim: dw_exec_step.cases)

lemma dw_exec_trace_deterministic:
  assumes t1: "dw_exec_trace s xs s1"
      and t2: "dw_exec_trace s xs t2"
  shows "s1 = t2"
  using t1 t2
proof (induction arbitrary: t2 rule: dw_exec_trace.induct)
  case (trace_refl s)
  have "t2 = s"
    by (rule dw_exec_trace_NilD[OF trace_refl.prems])
  thus ?case by simp
next
  case (trace_step s a s' xs s'')
  from trace_step.prems obtain t where
      step2: "dw_exec_step s a t"
      and tail2: "dw_exec_trace t xs t2"
    by cases auto
  have "t = s'"
    using dw_exec_step_deterministic[OF step2 trace_step.hyps(1)] by simp
  with tail2 show ?case
    by (simp add: trace_step.IH)
qed

lemma dw_exec_trace_do_sources:
  assumes "exec_status s = Running"
  shows
    "dw_exec_trace s (source_exec_labels H)
       (s\<lparr>exec_src_hist := exec_src_hist s @ H\<rparr>)"
  using assms
proof (induction H arbitrary: s)
  case Nil
  show ?case by (simp add: dw_exec_trace.trace_refl)
next
  case (Cons x H)
  then obtain c e where x_def: "x = (c, e)"
    by (cases x) blast
  let ?s1 = "s\<lparr>exec_src_hist := exec_src_hist s @ [(c, e)]\<rparr>"
  have step: "dw_exec_step s (DoSource c e) ?s1"
    by (rule dw_exec_step.do_source) (rule Cons.prems)
  have tail:
    "dw_exec_trace ?s1 (source_exec_labels H)
       (?s1\<lparr>exec_src_hist := exec_src_hist ?s1 @ H\<rparr>)"
    by (rule Cons.IH) (simp add: Cons.prems)
  have "?s1\<lparr>exec_src_hist := exec_src_hist ?s1 @ H\<rparr> =
        s\<lparr>exec_src_hist := exec_src_hist s @ (x # H)\<rparr>"
    by (simp add: x_def append_assoc)
  with step tail show ?case
    by (simp add: x_def dw_exec_trace.trace_step)
qed

lemma dw_exec_trace_do_downstreams:
  assumes "exec_status s = Running"
  shows
    "dw_exec_trace s (downstream_exec_labels H)
       (s\<lparr>exec_down_hist := exec_down_hist s @ H,
          exec_enqueued := exec_enqueued s @ H,
          exec_pending := exec_pending s - set H\<rparr>)"
  using assms
proof (induction H arbitrary: s)
  case Nil
  show ?case by (simp add: dw_exec_trace.trace_refl)
next
  case (Cons x H)
  then obtain c e where x_def: "x = (c, e)"
    by (cases x) blast
  let ?s1 =
    "s\<lparr>exec_enqueued := exec_enqueued s @ [(c, e)],
        exec_pending := insert (c, e) (exec_pending s)\<rparr>"
  let ?s2 =
    "?s1\<lparr>exec_down_hist := exec_down_hist ?s1 @ [(c, e)],
          exec_pending := exec_pending ?s1 - {(c, e)}\<rparr>"
  have step1: "dw_exec_step s (EnqueueDownstream c e) ?s1"
    by (rule dw_exec_step.enqueue_downstream) (rule Cons.prems)
  have step2: "dw_exec_step ?s1 (DoDownstream c e) ?s2"
    by (rule dw_exec_step.do_downstream) (simp add: Cons.prems, simp)
  have tail:
    "dw_exec_trace ?s2 (downstream_exec_labels H)
       (?s2\<lparr>exec_down_hist := exec_down_hist ?s2 @ H,
           exec_enqueued := exec_enqueued ?s2 @ H,
           exec_pending := exec_pending ?s2 - set H\<rparr>)"
    by (rule Cons.IH) (simp add: Cons.prems)
  have final:
    "?s2\<lparr>exec_down_hist := exec_down_hist ?s2 @ H,
          exec_enqueued := exec_enqueued ?s2 @ H,
          exec_pending := exec_pending ?s2 - set H\<rparr> =
     s\<lparr>exec_down_hist := exec_down_hist s @ (x # H),
        exec_enqueued := exec_enqueued s @ (x # H),
        exec_pending := exec_pending s - set (x # H)\<rparr>"
    by (simp add: x_def append_assoc Diff_singleton_insert)
  have tail2:
    "dw_exec_trace ?s1 (DoDownstream c e # downstream_exec_labels H)
       (s\<lparr>exec_down_hist := exec_down_hist s @ (x # H),
          exec_enqueued := exec_enqueued s @ (x # H),
          exec_pending := exec_pending s - set (x # H)\<rparr>)"
    using dw_exec_trace.trace_step[OF step2 tail] final by simp
  show ?case
    using dw_exec_trace.trace_step[OF step1 tail2]
    by (simp add: x_def)
qed

lemma dw_exec_trace_prefix_histories:
  assumes "exec_status s = Running"
  shows
    "dw_exec_trace s (source_exec_labels Hs @ downstream_exec_labels Hd)
       (s\<lparr>exec_src_hist := exec_src_hist s @ Hs,
          exec_down_hist := exec_down_hist s @ Hd,
          exec_enqueued := exec_enqueued s @ Hd,
          exec_pending := exec_pending s - set Hd\<rparr>)"
proof -
  let ?s1 = "s\<lparr>exec_src_hist := exec_src_hist s @ Hs\<rparr>"
  have src:
    "dw_exec_trace s (source_exec_labels Hs) ?s1"
    by (rule dw_exec_trace_do_sources[OF assms])
  have down:
    "dw_exec_trace ?s1 (downstream_exec_labels Hd)
       (?s1\<lparr>exec_down_hist := exec_down_hist ?s1 @ Hd,
            exec_enqueued := exec_enqueued ?s1 @ Hd,
            exec_pending := exec_pending ?s1 - set Hd\<rparr>)"
    by (rule dw_exec_trace_do_downstreams) (simp add: assms)
  have final:
    "?s1\<lparr>exec_down_hist := exec_down_hist ?s1 @ Hd,
           exec_enqueued := exec_enqueued ?s1 @ Hd,
           exec_pending := exec_pending ?s1 - set Hd\<rparr> =
     s\<lparr>exec_src_hist := exec_src_hist s @ Hs,
        exec_down_hist := exec_down_hist s @ Hd,
        exec_enqueued := exec_enqueued s @ Hd,
        exec_pending := exec_pending s - set Hd\<rparr>"
    by simp
  show ?thesis
    using dw_exec_trace_append[OF src down] final by simp
qed

lemma dw_exec_step_src_hist:
  assumes "dw_exec_step s a s'"
  shows "exec_src_hist s' = exec_src_hist s @ src_hist_of_labels [a]"
  using assms by cases simp_all

lemma dw_exec_step_down_hist:
  assumes "dw_exec_step s a s'"
  shows "exec_down_hist s' = exec_down_hist s @ down_hist_of_labels [a]"
  using assms by cases simp_all

lemma dw_exec_step_enqueued:
  assumes "dw_exec_step s a s'"
  shows "exec_enqueued s' = exec_enqueued s @ enqueued_hist_of_labels [a]"
  using assms by cases simp_all

lemma dw_exec_step_pending:
  assumes "dw_exec_step s a s'"
  shows "exec_pending s' = pending_after_labels [a] (exec_pending s)"
  using assms by cases simp_all

lemma dw_exec_step_acked:
  assumes "dw_exec_step s a s'"
  shows "exec_acked s' = exec_acked s @ acked_hist_of_labels [a]"
  using assms by cases simp_all

lemma dw_exec_step_base:
  assumes "dw_exec_step s a s'"
  shows "exec_base s' = exec_base s"
  using assms by cases simp_all

lemma dw_exec_step_scope:
  assumes "dw_exec_step s a s'"
  shows "exec_scope s' = exec_scope s"
  using assms by cases simp_all

lemma dw_exec_step_finish:
  assumes "dw_exec_step s a s'"
  shows "exec_finish s' = exec_finish s"
  using assms by cases simp_all

lemma dw_exec_step_running_status:
  assumes step: "dw_exec_step s a s'"
      and running: "running_label a"
      and status: "exec_status s = Running"
  shows "exec_status s' = Running"
  using step running status
  by cases (auto simp: running_label_def split: dw_exec_label.splits)

lemma dw_exec_trace_src_hist:
  assumes "dw_exec_trace s xs s'"
  shows "exec_src_hist s' = exec_src_hist s @ src_hist_of_labels xs"
  using assms
proof (induction rule: dw_exec_trace.induct)
  case (trace_refl s)
  show ?case by simp
next
  case (trace_step s a s' xs s'')
  have "exec_src_hist s'' =
        exec_src_hist s' @ src_hist_of_labels xs"
    by (rule trace_step.IH)
  also have "\<dots> =
        (exec_src_hist s @ src_hist_of_labels [a]) @ src_hist_of_labels xs"
    using dw_exec_step_src_hist[OF trace_step.hyps(1)] by simp
  also have "\<dots> = exec_src_hist s @ src_hist_of_labels (a # xs)"
    by simp
  finally show ?case .
qed

lemma dw_exec_trace_down_hist:
  assumes "dw_exec_trace s xs s'"
  shows "exec_down_hist s' = exec_down_hist s @ down_hist_of_labels xs"
  using assms
proof (induction rule: dw_exec_trace.induct)
  case (trace_refl s)
  show ?case by simp
next
  case (trace_step s a s' xs s'')
  have "exec_down_hist s'' =
        exec_down_hist s' @ down_hist_of_labels xs"
    by (rule trace_step.IH)
  also have "\<dots> =
        (exec_down_hist s @ down_hist_of_labels [a]) @ down_hist_of_labels xs"
    using dw_exec_step_down_hist[OF trace_step.hyps(1)] by simp
  also have "\<dots> = exec_down_hist s @ down_hist_of_labels (a # xs)"
    by simp
  finally show ?case .
qed

lemma dw_exec_trace_enqueued:
  assumes "dw_exec_trace s xs s'"
  shows "exec_enqueued s' = exec_enqueued s @ enqueued_hist_of_labels xs"
  using assms
proof (induction rule: dw_exec_trace.induct)
  case (trace_refl s)
  show ?case by simp
next
  case (trace_step s a s' xs s'')
  have "exec_enqueued s'' =
        exec_enqueued s' @ enqueued_hist_of_labels xs"
    by (rule trace_step.IH)
  also have "\<dots> =
        (exec_enqueued s @ enqueued_hist_of_labels [a]) @ enqueued_hist_of_labels xs"
    using dw_exec_step_enqueued[OF trace_step.hyps(1)] by simp
  also have "\<dots> = exec_enqueued s @ enqueued_hist_of_labels (a # xs)"
    by simp
  finally show ?case .
qed

lemma dw_exec_trace_pending:
  assumes "dw_exec_trace s xs s'"
  shows "exec_pending s' = pending_after_labels xs (exec_pending s)"
  using assms
proof (induction rule: dw_exec_trace.induct)
  case (trace_refl s)
  show ?case by simp
next
  case (trace_step s a s' xs s'')
  have "exec_pending s'' =
        pending_after_labels xs (exec_pending s')"
    by (rule trace_step.IH)
  also have "\<dots> =
        pending_after_labels xs (pending_after_labels [a] (exec_pending s))"
    using dw_exec_step_pending[OF trace_step.hyps(1)] by simp
  also have "\<dots> = pending_after_labels (a # xs) (exec_pending s)"
    by (cases a; simp)
  finally show ?case .
qed

lemma dw_exec_trace_acked:
  assumes "dw_exec_trace s xs s'"
  shows "exec_acked s' = exec_acked s @ acked_hist_of_labels xs"
  using assms
proof (induction rule: dw_exec_trace.induct)
  case (trace_refl s)
  show ?case by simp
next
  case (trace_step s a s' xs s'')
  have "exec_acked s'' =
        exec_acked s' @ acked_hist_of_labels xs"
    by (rule trace_step.IH)
  also have "\<dots> =
        (exec_acked s @ acked_hist_of_labels [a]) @ acked_hist_of_labels xs"
    using dw_exec_step_acked[OF trace_step.hyps(1)] by simp
  also have "\<dots> = exec_acked s @ acked_hist_of_labels (a # xs)"
    by simp
  finally show ?case .
qed

definition history_can_append
  :: "('k, 'v) src_history \<Rightarrow> src_coord \<times> ('k, 'v) source_event \<Rightarrow> bool"
where
  "history_can_append H x \<longleftrightarrow>
     hist_coord x \<noteq> c0
   \<and> (\<forall>y \<in> set H. hist_coord y \<le> hist_coord x)"

lemma wellformed_src_history_append_one:
  assumes wf: "wellformed_src_history H"
      and can: "history_can_append H x"
  shows "wellformed_src_history (H @ [x])"
proof -
  have h1:
    "\<forall>i. Suc i < length (H @ [x])
      \<longrightarrow> src_le (hist_coord ((H @ [x]) ! i))
          (hist_coord ((H @ [x]) ! Suc i))"
  proof (intro allI impI)
    fix i
    assume i: "Suc i < length (H @ [x])"
    show "src_le (hist_coord ((H @ [x]) ! i))
          (hist_coord ((H @ [x]) ! Suc i))"
    proof (cases "Suc i < length H")
      case True
      have i_lt: "i < length H"
        using True by simp
      have src_le:
        "src_le (hist_coord (H ! i)) (hist_coord (H ! Suc i))"
        using wf True by (simp add: wellformed_src_history_def)
      from True i_lt src_le show ?thesis
        by (simp add: nth_append)
    next
      case False
      with i have i_lt: "i < length H"
          and suc_eq: "Suc i = length H"
        by auto
      have "H ! i \<in> set H"
        using i_lt by simp
      with can have "hist_coord (H ! i) \<le> hist_coord x"
        by (auto simp: history_can_append_def)
      with i_lt suc_eq show ?thesis
        by (simp add: nth_append src_le_eq_less_eq)
    qed
  qed
  have h2:
    "\<forall>i. i < length (H @ [x])
      \<longrightarrow> hist_coord ((H @ [x]) ! i) \<noteq> c0"
  proof (intro allI impI)
    fix i
    assume i: "i < length (H @ [x])"
    show "hist_coord ((H @ [x]) ! i) \<noteq> c0"
    proof (cases "i < length H")
      case True
      with wf show ?thesis
        by (simp add: wellformed_src_history_def nth_append)
    next
      case False
      with i have "i = length H" by simp
      with can show ?thesis
        by (simp add: history_can_append_def)
    qed
  qed
  have h3:
    "\<forall>i j. i < length (H @ [x]) \<and> j < length (H @ [x]) \<and> i \<noteq> j
      \<longrightarrow> source_pos_order (H @ [x]) i j
        \<or> source_pos_order (H @ [x]) j i"
  proof (intro allI impI)
    fix i j
    assume ij:
      "i < length (H @ [x]) \<and> j < length (H @ [x]) \<and> i \<noteq> j"
    show "source_pos_order (H @ [x]) i j
        \<or> source_pos_order (H @ [x]) j i"
    proof (cases "i < length H \<and> j < length H")
      case True
      hence i_lt: "i < length H" and j_lt: "j < length H"
        by simp_all
      from wf i_lt j_lt ij have old:
        "source_pos_order H i j \<or> source_pos_order H j i"
        by (auto simp: wellformed_src_history_def)
      have ij_same:
        "source_pos_order (H @ [x]) i j = source_pos_order H i j"
        using i_lt j_lt by (simp add: source_pos_order_def nth_append)
      have ji_same:
        "source_pos_order (H @ [x]) j i = source_pos_order H j i"
        using i_lt j_lt by (simp add: source_pos_order_def nth_append)
      from old ij_same ji_same show ?thesis by simp
    next
      case False
      note not_both_old = False
      from ij have i_len: "i \<le> length H" and j_len: "j \<le> length H"
        by auto
      with False ij show ?thesis
      proof (cases "i = length H")
        case True
        then have j_lt: "j < length H"
          using ij by auto
        have "H ! j \<in> set H"
          using j_lt by simp
        with can have le: "hist_coord (H ! j) \<le> hist_coord x"
          by (auto simp: history_can_append_def)
        show ?thesis
        proof (cases "hist_coord (H ! j) = hist_coord x")
          case True
          with \<open>i = length H\<close> j_lt show ?thesis
            by (auto simp: source_pos_order_def nth_append)
        next
          case False
          with le \<open>i = length H\<close> j_lt show ?thesis
            by (auto simp: source_pos_order_def src_lt_eq_less nth_append)
        qed
      next
        case False
        with i_len have i_lt: "i < length H" by simp
        from ij False have j_eq: "j = length H"
          using i_lt j_len not_both_old by auto
        have "H ! i \<in> set H"
          using i_lt by simp
        with can have le: "hist_coord (H ! i) \<le> hist_coord x"
          by (auto simp: history_can_append_def)
        show ?thesis
        proof (cases "hist_coord (H ! i) = hist_coord x")
          case True
          with j_eq i_lt show ?thesis
            by (auto simp: source_pos_order_def nth_append)
        next
          case False
          with le j_eq i_lt show ?thesis
            by (auto simp: source_pos_order_def src_lt_eq_less nth_append)
        qed
      qed
    qed
  qed
  from h1 h2 h3 show ?thesis
    by (simp add: wellformed_src_history_def)
qed

definition exec_histories_wellformed
  :: "('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  "exec_histories_wellformed s \<longleftrightarrow>
     wellformed_src_history (exec_src_hist s)
   \<and> wellformed_src_history (exec_down_hist s)
   \<and> wellformed_src_history (exec_enqueued s)
   \<and> wellformed_src_history (exec_acked s)"

definition exec_label_preserves_history_wf
  :: "('k, 'v) dw_exec_state \<Rightarrow> ('k, 'v) dw_exec_label \<Rightarrow> bool"
where
  "exec_label_preserves_history_wf s a \<longleftrightarrow>
     (case a of
        DoSource c e \<Rightarrow> history_can_append (exec_src_hist s) (c, e)
      | EnqueueDownstream c e \<Rightarrow> history_can_append (exec_enqueued s) (c, e)
      | DoDownstream c e \<Rightarrow> history_can_append (exec_down_hist s) (c, e)
      | Ack c e \<Rightarrow> history_can_append (exec_acked s) (c, e)
      | Crash _ \<Rightarrow> True
      | Recover \<Rightarrow> True
      | Observe _ \<Rightarrow> True)"

lemma dw_exec_step_exec_histories_wellformed:
  assumes step: "dw_exec_step s a s'"
      and wf: "exec_histories_wellformed s"
      and admissible: "exec_label_preserves_history_wf s a"
  shows "exec_histories_wellformed s'"
  using step wf admissible
  by cases
     (auto simp: exec_histories_wellformed_def
                 exec_label_preserves_history_wf_def
          intro: wellformed_src_history_append_one)

definition pending_enqueued_consistent
  :: "('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  "pending_enqueued_consistent s \<longleftrightarrow>
     exec_pending s \<subseteq> set (exec_enqueued s)"

lemma dw_exec_step_pending_enqueued_consistent:
  assumes step: "dw_exec_step s a s'"
      and consistent: "pending_enqueued_consistent s"
  shows "pending_enqueued_consistent s'"
  using step consistent
  by cases (auto simp: pending_enqueued_consistent_def)

lemma dw_exec_trace_pending_enqueued_consistent:
  assumes trace: "dw_exec_trace s xs s'"
      and consistent: "pending_enqueued_consistent s"
  shows "pending_enqueued_consistent s'"
  using trace consistent
proof (induction rule: dw_exec_trace.induct)
  case (trace_refl s)
  show ?case by (rule trace_refl.prems)
next
  case (trace_step s a s' xs s'')
  have "pending_enqueued_consistent s'"
    by (rule dw_exec_step_pending_enqueued_consistent
        [OF trace_step.hyps(1) trace_step.prems])
  thus ?case
    by (rule trace_step.IH)
qed

definition acked_source_consistent
  :: "('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  "acked_source_consistent s \<longleftrightarrow>
     set (exec_acked s) \<subseteq> set (exec_src_hist s)"

lemma dw_exec_step_acked_source_consistent:
  assumes step: "dw_exec_step s a s'"
      and consistent: "acked_source_consistent s"
  shows "acked_source_consistent s'"
  using step consistent
  by cases (auto simp: acked_source_consistent_def)

lemma dw_exec_trace_acked_source_consistent:
  assumes trace: "dw_exec_trace s xs s'"
      and consistent: "acked_source_consistent s"
  shows "acked_source_consistent s'"
  using trace consistent
proof (induction rule: dw_exec_trace.induct)
  case (trace_refl s)
  show ?case by (rule trace_refl.prems)
next
  case (trace_step s a s' xs s'')
  have "acked_source_consistent s'"
    by (rule dw_exec_step_acked_source_consistent
        [OF trace_step.hyps(1) trace_step.prems])
  thus ?case
    by (rule trace_step.IH)
qed

definition wellformed_exec_state
  :: "('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  "wellformed_exec_state s \<longleftrightarrow>
     exec_histories_wellformed s
   \<and> pending_enqueued_consistent s
   \<and> acked_source_consistent s"

lemma initial_exec_state_wellformed [simp]:
  "wellformed_exec_state (initial_exec_state b K fin)"
  by (simp add: wellformed_exec_state_def exec_histories_wellformed_def
                pending_enqueued_consistent_def acked_source_consistent_def
                initial_exec_state_def wellformed_src_history_def)

lemma dw_exec_step_wellformed_exec_state:
  assumes step: "dw_exec_step s a s'"
      and wf: "wellformed_exec_state s"
      and preserves: "exec_label_preserves_history_wf s a"
  shows "wellformed_exec_state s'"
proof -
  have histories: "exec_histories_wellformed s'"
    by (rule dw_exec_step_exec_histories_wellformed)
       (use step wf preserves in
          \<open>auto simp: wellformed_exec_state_def\<close>)
  have pending: "pending_enqueued_consistent s'"
    by (rule dw_exec_step_pending_enqueued_consistent)
       (use step wf in \<open>auto simp: wellformed_exec_state_def\<close>)
  have acked: "acked_source_consistent s'"
    by (rule dw_exec_step_acked_source_consistent)
       (use step wf in \<open>auto simp: wellformed_exec_state_def\<close>)
  from histories pending acked show ?thesis
    by (simp add: wellformed_exec_state_def)
qed

inductive admissible_dw_exec_trace
  :: "('k, 'v) dw_exec_state \<Rightarrow> ('k, 'v) dw_exec_label list \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  admissible_trace_refl:
    "wellformed_exec_state s \<Longrightarrow> admissible_dw_exec_trace s [] s"
| admissible_trace_step:
    "\<lbrakk>dw_exec_step s a s'; wellformed_exec_state s;
      exec_label_preserves_history_wf s a;
      admissible_dw_exec_trace s' as s''\<rbrakk> \<Longrightarrow>
     admissible_dw_exec_trace s (a # as) s''"

lemma admissible_dw_exec_trace_imp_dw_exec_trace:
  assumes "admissible_dw_exec_trace s xs s'"
  shows "dw_exec_trace s xs s'"
  using assms
  by (induction rule: admissible_dw_exec_trace.induct)
     (auto intro: dw_exec_trace.intros)

lemma admissible_dw_exec_trace_start_wellformed:
  assumes "admissible_dw_exec_trace s xs s'"
  shows "wellformed_exec_state s"
  using assms
  by (induction rule: admissible_dw_exec_trace.induct) simp_all

lemma admissible_dw_exec_trace_final_wellformed:
  assumes "admissible_dw_exec_trace s xs s'"
  shows "wellformed_exec_state s'"
  using assms
  by (induction rule: admissible_dw_exec_trace.induct) simp_all

lemma admissible_dw_exec_trace_single:
  assumes step: "dw_exec_step s a s'"
      and wf: "wellformed_exec_state s"
      and preserves: "exec_label_preserves_history_wf s a"
  shows "admissible_dw_exec_trace s [a] s'"
proof -
  have wf': "wellformed_exec_state s'"
    by (rule dw_exec_step_wellformed_exec_state[OF step wf preserves])
  show ?thesis
    by (rule admissible_dw_exec_trace.admissible_trace_step
        [OF step wf preserves
            admissible_dw_exec_trace.admissible_trace_refl[OF wf']])
qed

lemma admissible_dw_exec_trace_append:
  assumes left: "admissible_dw_exec_trace s xs s'"
      and right: "admissible_dw_exec_trace s' ys s''"
  shows "admissible_dw_exec_trace s (xs @ ys) s''"
  using left right
proof (induction arbitrary: ys s'' rule: admissible_dw_exec_trace.induct)
  case (admissible_trace_refl s)
  show ?case using admissible_trace_refl.prems by simp
next
  case (admissible_trace_step s a s' xs s_mid)
  have tail: "admissible_dw_exec_trace s' (xs @ ys) s''"
    by (rule admissible_trace_step.IH[OF admissible_trace_step.prems])
  have "admissible_dw_exec_trace s (a # (xs @ ys)) s''"
    by (rule admissible_dw_exec_trace.admissible_trace_step
        [OF admissible_trace_step.hyps(1) admissible_trace_step.hyps(2)
            admissible_trace_step.hyps(3) tail])
  thus ?case by simp
qed

lemma admissible_dw_exec_trace_src_hist:
  assumes trace: "admissible_dw_exec_trace s xs s'"
  shows "exec_src_hist s' = exec_src_hist s @ src_hist_of_labels xs"
  by (rule dw_exec_trace_src_hist
      [OF admissible_dw_exec_trace_imp_dw_exec_trace[OF trace]])

lemma admissible_dw_exec_trace_down_hist:
  assumes trace: "admissible_dw_exec_trace s xs s'"
  shows "exec_down_hist s' = exec_down_hist s @ down_hist_of_labels xs"
  by (rule dw_exec_trace_down_hist
      [OF admissible_dw_exec_trace_imp_dw_exec_trace[OF trace]])

lemma admissible_dw_exec_trace_enqueued:
  assumes trace: "admissible_dw_exec_trace s xs s'"
  shows "exec_enqueued s' = exec_enqueued s @ enqueued_hist_of_labels xs"
  by (rule dw_exec_trace_enqueued
      [OF admissible_dw_exec_trace_imp_dw_exec_trace[OF trace]])

lemma admissible_dw_exec_trace_pending:
  assumes trace: "admissible_dw_exec_trace s xs s'"
  shows "exec_pending s' = pending_after_labels xs (exec_pending s)"
  by (rule dw_exec_trace_pending
      [OF admissible_dw_exec_trace_imp_dw_exec_trace[OF trace]])

lemma admissible_dw_exec_trace_acked:
  assumes trace: "admissible_dw_exec_trace s xs s'"
  shows "exec_acked s' = exec_acked s @ acked_hist_of_labels xs"
  by (rule dw_exec_trace_acked
      [OF admissible_dw_exec_trace_imp_dw_exec_trace[OF trace]])

definition running_prefix :: "('k, 'v) dw_exec_label list \<Rightarrow> bool" where
  "running_prefix xs \<longleftrightarrow> running_labels xs"

lemma enqueued_label_in_enqueued_after_trace:
  assumes trace: "dw_exec_trace s xs s'"
      and enq: "(c, e) \<in> set (enqueued_hist_of_labels xs)"
  shows "(c, e) \<in> set (exec_enqueued s')"
  using dw_exec_trace_enqueued[OF trace] enq by auto

lemma downstream_step_consumes_pending:
  assumes "exec_status s = Running"
      and pending: "(c, e) \<in> exec_pending s"
  shows "\<exists>s'.
      dw_exec_trace s [DoDownstream c e] s'
    \<and> (c, e) \<notin> exec_pending s'
    \<and> (c, e) \<in> set (exec_down_hist s')"
proof -
  let ?s' =
    "s\<lparr>exec_down_hist := exec_down_hist s @ [(c, e)],
        exec_pending := exec_pending s - {(c, e)}\<rparr>"
  have step: "dw_exec_step s (DoDownstream c e) ?s'"
    by (rule dw_exec_step.do_downstream[OF assms])
  have trace:
    "dw_exec_trace s [DoDownstream c e] ?s'"
    by (rule dw_exec_trace.trace_step[OF step dw_exec_trace.trace_refl])
  show ?thesis
    using trace by auto
qed

lemma completed_downstream_is_enqueued_but_not_pending:
  assumes "exec_status s = Running"
  shows "\<exists>s'.
      dw_exec_trace s [EnqueueDownstream c e, DoDownstream c e] s'
    \<and> (c, e) \<in> set (exec_enqueued s')
    \<and> (c, e) \<notin> exec_pending s'
    \<and> (c, e) \<in> set (exec_down_hist s')"
proof -
  let ?s1 =
    "s\<lparr>exec_enqueued := exec_enqueued s @ [(c, e)],
        exec_pending := insert (c, e) (exec_pending s)\<rparr>"
  let ?s2 =
    "?s1\<lparr>exec_down_hist := exec_down_hist ?s1 @ [(c, e)],
          exec_pending := exec_pending ?s1 - {(c, e)}\<rparr>"
  have step1: "dw_exec_step s (EnqueueDownstream c e) ?s1"
    by (rule dw_exec_step.enqueue_downstream[OF assms])
  have step2: "dw_exec_step ?s1 (DoDownstream c e) ?s2"
    by (rule dw_exec_step.do_downstream) (simp add: assms, simp)
  have trace:
    "dw_exec_trace s [EnqueueDownstream c e, DoDownstream c e] ?s2"
    by (rule dw_exec_trace.trace_step
        [OF step1 dw_exec_trace.trace_step[OF step2 dw_exec_trace.trace_refl]])
  show ?thesis
    using trace by auto
qed

lemma dw_exec_trace_base:
  assumes "dw_exec_trace s xs s'"
  shows "exec_base s' = exec_base s"
  using assms
  by (induction rule: dw_exec_trace.induct)
     (auto dest: dw_exec_step_base)

lemma dw_exec_trace_scope:
  assumes "dw_exec_trace s xs s'"
  shows "exec_scope s' = exec_scope s"
  using assms
  by (induction rule: dw_exec_trace.induct)
     (auto dest: dw_exec_step_scope)

lemma dw_exec_trace_finish:
  assumes "dw_exec_trace s xs s'"
  shows "exec_finish s' = exec_finish s"
  using assms
  by (induction rule: dw_exec_trace.induct)
     (auto dest: dw_exec_step_finish)

lemma dw_exec_trace_running_status:
  assumes trace: "dw_exec_trace s xs s'"
      and labels: "running_labels xs"
      and status: "exec_status s = Running"
  shows "exec_status s' = Running"
  using labels status trace
proof (induction xs arbitrary: s s')
  case Nil
  have "s' = s"
    by (rule dw_exec_trace_NilD[OF Nil.prems(3)])
  with Nil.prems show ?case by simp
next
  case (Cons a xs)
  from Cons.prems(3) obtain t where
      step: "dw_exec_step s a t"
      and tail: "dw_exec_trace t xs s'"
    by cases auto
  from Cons.prems(1) have a_running: "running_label a"
      and xs_running: "running_labels xs"
    by (simp_all add: running_labels_def)
  have t_running: "exec_status t = Running"
    by (rule dw_exec_step_running_status
        [OF step a_running Cons.prems(2)])
  show ?case
    by (rule Cons.IH[OF xs_running t_running tail])
qed

lemma running_prefix_trace_stays_running:
  assumes trace: "dw_exec_trace s xs s'"
      and prefix: "running_prefix xs"
      and status: "exec_status s = Running"
  shows "exec_status s' = Running"
  using assms
  by (simp add: running_prefix_def dw_exec_trace_running_status)

lemma admissible_dw_exec_trace_base:
  assumes trace: "admissible_dw_exec_trace s xs s'"
  shows "exec_base s' = exec_base s"
  by (rule dw_exec_trace_base
      [OF admissible_dw_exec_trace_imp_dw_exec_trace[OF trace]])

lemma admissible_dw_exec_trace_scope:
  assumes trace: "admissible_dw_exec_trace s xs s'"
  shows "exec_scope s' = exec_scope s"
  by (rule dw_exec_trace_scope
      [OF admissible_dw_exec_trace_imp_dw_exec_trace[OF trace]])

lemma admissible_dw_exec_trace_finish:
  assumes trace: "admissible_dw_exec_trace s xs s'"
  shows "exec_finish s' = exec_finish s"
  by (rule dw_exec_trace_finish
      [OF admissible_dw_exec_trace_imp_dw_exec_trace[OF trace]])

lemma admissible_dw_exec_trace_running_status:
  assumes trace: "admissible_dw_exec_trace s xs s'"
      and labels: "running_labels xs"
      and status: "exec_status s = Running"
  shows "exec_status s' = Running"
  by (rule dw_exec_trace_running_status
      [OF admissible_dw_exec_trace_imp_dw_exec_trace[OF trace] labels status])

definition store2_of_exec
  :: "('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow> ('k \<rightharpoonup> 'v)"
where
  "store2_of_exec s f = Src (exec_base s) (exec_down_hist s) f"

definition proto_of_exec_at
  :: "('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow> ('k, 'v) proto"
where
  "proto_of_exec_at s c =
     \<lparr> pbase = exec_base s,
       psrc = exec_src_hist s,
       pscope = exec_scope s,
       pcrash = c,
       pfin = exec_finish s,
       store2 = store2_of_exec s \<rparr>"

lemma proto_of_exec_at_status_update [simp]:
  "proto_of_exec_at (s\<lparr>exec_status := st\<rparr>) c = proto_of_exec_at s c"
  by (simp add: proto_of_exec_at_def store2_of_exec_def fun_eq_iff)

definition observable_mismatch
  :: "('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> bool"
where
  "observable_mismatch s c k \<longleftrightarrow>
     exec_status s = Crashed c
   \<and> c \<le> exec_finish s
   \<and> mismatch_at (proto_of_exec_at s c) c k"

definition acked_source_effect_at
  :: "('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> bool"
where
  "acked_source_effect_at s c k \<longleftrightarrow>
     (\<exists>c_src e.
        (c_src, e) \<in> set (exec_acked s)
      \<and> c_src \<le> c
      \<and> key_of e = k
      \<and> Src (exec_base s) (exec_src_hist s) c k = event_result e)"

definition acked_observable_mismatch
  :: "('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> bool"
where
  "acked_observable_mismatch s c k \<longleftrightarrow>
     observable_mismatch s c k \<and> acked_source_effect_at s c k"

definition bad_crash_enabled
  :: "('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> bool"
where
  "bad_crash_enabled s c k \<longleftrightarrow>
     exec_status s = Running
   \<and> c \<le> exec_finish s
   \<and> mismatch_at (proto_of_exec_at s c) c k"

definition acked_bad_crash_enabled
  :: "('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> bool"
where
  "acked_bad_crash_enabled s c k \<longleftrightarrow>
     bad_crash_enabled s c k \<and> acked_source_effect_at s c k"

lemma observable_mismatchI:
  assumes "exec_status s = Crashed c"
      and "c \<le> exec_finish s"
      and "k \<in> exec_scope s"
      and "Src (exec_base s) (exec_down_hist s) c k
           \<noteq> Src (exec_base s) (exec_src_hist s) c k"
  shows "observable_mismatch s c k"
  using assms
  by (simp add: observable_mismatch_def mismatch_at_def proto_of_exec_at_def
                store2_of_exec_def log_image_def restrict_def)

lemma observable_mismatch_imp_diverges:
  assumes "observable_mismatch s c k"
  shows "diverges (proto_of_exec_at s c) c"
  using assms
  by (auto simp: observable_mismatch_def diverges_iff_mismatch_at
                 proto_of_exec_at_def)

lemma acked_observable_mismatch_imp_observable_mismatch:
  assumes "acked_observable_mismatch s c k"
  shows "observable_mismatch s c k"
  using assms by (simp add: acked_observable_mismatch_def)

lemma acked_observable_mismatch_imp_diverges:
  assumes "acked_observable_mismatch s c k"
  shows "diverges (proto_of_exec_at s c) c"
  by (rule observable_mismatch_imp_diverges
      [OF acked_observable_mismatch_imp_observable_mismatch[OF assms]])

theorem bad_crash_enabled_extend:
  assumes "bad_crash_enabled s c k"
  shows "\<exists>s'.
      dw_exec_trace s [Crash c] s'
    \<and> observable_mismatch s' c k
    \<and> diverges (proto_of_exec_at s' c) c"
proof -
  let ?s' = "s\<lparr>exec_status := Crashed c\<rparr>"
  from assms have running: "exec_status s = Running"
      and le_fin: "c \<le> exec_finish s"
      and mismatch: "mismatch_at (proto_of_exec_at s c) c k"
    by (auto simp: bad_crash_enabled_def)
  have step: "dw_exec_step s (Crash c) ?s'"
    by (rule dw_exec_step.crash[OF running])
  have trace: "dw_exec_trace s [Crash c] ?s'"
    by (rule dw_exec_trace.trace_step[OF step dw_exec_trace.trace_refl])
  have obs: "observable_mismatch ?s' c k"
    using le_fin mismatch
    by (simp add: observable_mismatch_def)
  hence div: "diverges (proto_of_exec_at ?s' c) c"
    by (rule observable_mismatch_imp_diverges)
  from trace obs div show ?thesis by blast
qed

theorem acked_bad_crash_enabled_extend:
  assumes "acked_bad_crash_enabled s c k"
  shows "\<exists>s'.
      dw_exec_trace s [Crash c] s'
    \<and> acked_observable_mismatch s' c k
    \<and> diverges (proto_of_exec_at s' c) c"
proof -
  let ?s' = "s\<lparr>exec_status := Crashed c\<rparr>"
  from assms have enabled: "bad_crash_enabled s c k"
      and ack: "acked_source_effect_at s c k"
    by (auto simp: acked_bad_crash_enabled_def)
  then have running: "exec_status s = Running"
      and le_fin: "c \<le> exec_finish s"
      and mismatch: "mismatch_at (proto_of_exec_at s c) c k"
    by (auto simp: bad_crash_enabled_def)
  have step: "dw_exec_step s (Crash c) ?s'"
    by (rule dw_exec_step.crash[OF running])
  have trace: "dw_exec_trace s [Crash c] ?s'"
    by (rule dw_exec_trace.trace_step[OF step dw_exec_trace.trace_refl])
  have obs: "observable_mismatch ?s' c k"
    using le_fin mismatch
    by (simp add: observable_mismatch_def)
  hence acked: "acked_observable_mismatch ?s' c k"
    using ack by (simp add: acked_observable_mismatch_def
                        acked_source_effect_at_def)
  hence div: "diverges (proto_of_exec_at ?s' c) c"
    by (rule acked_observable_mismatch_imp_diverges)
  from trace acked div show ?thesis by blast
qed

lemma latest_src_event_snoc_at_key:
  assumes "key_of e = k"
      and "c \<le> f"
  shows "latest_src_event (H @ [(c, e)]) f k = Some (length H)"
  using assms
  by (simp add: latest_src_event_def Let_def nth_append src_le_eq_less_eq)

lemma Src_snoc_event_at_key:
  assumes "key_of e = k"
      and "c \<le> f"
  shows "Src b (H @ [(c, e)]) f k = event_result e"
  using assms
  by (cases e; simp add: Src_def latest_src_event_snoc_at_key)

definition visible_src_event_at
  :: "frontier \<Rightarrow> 'k \<Rightarrow> src_coord \<times> ('k, 'v) source_event \<Rightarrow> bool"
where
  "visible_src_event_at f k x \<longleftrightarrow>
     fst x \<le> f \<and> key_of (snd x) = k"

definition no_visible_key_events
  :: "('k, 'v) src_history \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> bool"
where
  "no_visible_key_events H f k \<longleftrightarrow>
     (\<forall>x \<in> set H. \<not> visible_src_event_at f k x)"

lemma latest_src_event_some_less:
  assumes "latest_src_event H f k = Some i"
  shows "i < length H"
  using assms
  unfolding latest_src_event_def Let_def
  by (auto split: if_splits dest: last_in_set)

lemma latest_src_event_snoc_invisible:
  assumes inv: "\<not> visible_src_event_at f k x"
  shows "latest_src_event (H @ [x]) f k = latest_src_event H f k"
proof -
  obtain c e where x_def: "x = (c, e)" by (cases x)
  let ?P = "\<lambda>i. src_le (hist_coord (H ! i)) f
                  \<and> key_of (hist_event (H ! i)) = k"
  let ?P' = "\<lambda>i. src_le (hist_coord ((H @ [x]) ! i)) f
                   \<and> key_of (hist_event ((H @ [x]) ! i)) = k"

  have range: "[0..<length (H @ [x])] = [0..<length H] @ [length H]"
    by simp
  have old: "filter ?P' [0..<length H] = filter ?P [0..<length H]"
    by (rule filter_cong) (simp_all add: nth_append)
  have tail: "filter ?P' [length H] = []"
    using inv by (simp add: visible_src_event_at_def x_def src_le_eq_less_eq)

  have cand_eq:
    "filter ?P' [0..<length (H @ [x])] = filter ?P [0..<length H]"
  proof -
    have "filter ?P' [0..<length (H @ [x])] =
          filter ?P' ([0..<length H] @ [length H])"
      by (simp only: range)
    also have "\<dots> = filter ?P' [0..<length H] @ filter ?P' [length H]"
      by simp
    also have "\<dots> = filter ?P [0..<length H] @ []"
      by (simp only: old tail)
    finally show ?thesis by simp
  qed

  have "(if filter ?P' [0..<length (H @ [x])] = [] then None
         else Some (last (filter ?P' [0..<length (H @ [x])]))) =
        (if filter ?P [0..<length H] = [] then None
         else Some (last (filter ?P [0..<length H])))"
    by (simp only: cand_eq)
  thus ?thesis
    unfolding latest_src_event_def Let_def .
qed

lemma Src_snoc_invisible:
  assumes "\<not> visible_src_event_at f k x"
  shows "Src b (H @ [x]) f k = Src b H f k"
proof -
  have latest: "latest_src_event (H @ [x]) f k = latest_src_event H f k"
    by (rule latest_src_event_snoc_invisible[OF assms])
  show ?thesis
  proof (cases "latest_src_event H f k")
    case None
    with latest show ?thesis by (simp add: src_characterized_by_latest_event)
  next
    case (Some i)
    hence "i < length H" by (rule latest_src_event_some_less)
    with Some latest show ?thesis
      by (simp add: src_characterized_by_latest_event nth_append)
  qed
qed

lemma latest_src_event_append_no_visible_key_events:
  assumes "\<forall>x \<in> set X. \<not> visible_src_event_at f k x"
  shows "latest_src_event (H @ X) f k = latest_src_event H f k"
  using assms
proof (induction X rule: rev_induct)
  case Nil
  show ?case by simp
next
  case (snoc x X)
  have X_no_vis: "\<forall>x \<in> set X. \<not> visible_src_event_at f k x"
    using snoc.prems by simp
  have x_no_vis: "\<not> visible_src_event_at f k x"
    using snoc.prems by simp
  have "latest_src_event (H @ (X @ [x])) f k =
        latest_src_event ((H @ X) @ [x]) f k"
    by simp
  also have "\<dots> = latest_src_event (H @ X) f k"
    by (rule latest_src_event_snoc_invisible[OF x_no_vis])
  also have "\<dots> = latest_src_event H f k"
    by (rule snoc.IH[OF X_no_vis])
  finally show ?case .
qed

lemma Src_append_no_visible_key_events:
  assumes no_vis: "\<forall>x \<in> set X. \<not> visible_src_event_at f k x"
  shows "Src b (H @ X) f k = Src b H f k"
proof -
  have latest: "latest_src_event (H @ X) f k = latest_src_event H f k"
    by (rule latest_src_event_append_no_visible_key_events[OF no_vis])
  show ?thesis
  proof (cases "latest_src_event H f k")
    case None
    with latest show ?thesis by (simp add: src_characterized_by_latest_event)
  next
    case (Some i)
    hence "i < length H" by (rule latest_src_event_some_less)
    with Some latest show ?thesis
      by (simp add: src_characterized_by_latest_event nth_append)
  qed
qed

lemma no_visible_key_events_appendD2:
  assumes "no_visible_key_events (H1 @ H2) f k"
  shows "no_visible_key_events H2 f k"
  using assms by (auto simp: no_visible_key_events_def)

lemma Src_append_no_visible_key:
  assumes "no_visible_key_events H2 f k"
  shows "Src b (H1 @ H2) f k = Src b H1 f k"
proof -
  from assms have "\<forall>x \<in> set H2. \<not> visible_src_event_at f k x"
    by (simp add: no_visible_key_events_def)
  thus ?thesis
    by (rule Src_append_no_visible_key_events)
qed

lemma Src_no_visible_key_events_eq_base:
  assumes "no_visible_key_events H f k"
  shows "Src b H f k = b k"
proof -
  have "Src b ([] @ H) f k = Src b [] f k"
    by (rule Src_append_no_visible_key[OF assms])
  thus ?thesis by simp
qed

lemma effective_source_no_visible_downstream_imp_stale:
  assumes effect: "effective_source_effect b e k"
      and no_visible: "no_visible_key_events H f k"
  shows "Src b H f k \<noteq> event_result e"
  using assms Src_no_visible_key_events_eq_base[OF no_visible, where b = b]
  by (auto simp: effective_source_effect_def)

definition effective_source_first_dual_write_plan
  :: "('k, 'v) source_first_plan \<Rightarrow> bool"
where
  "effective_source_first_dual_write_plan W \<longleftrightarrow>
     same_downstream_effect (plan_event W) (plan_down_event W) (plan_key W)
   \<and> effective_source_effect (plan_base W) (plan_event W) (plan_key W)
   \<and> no_visible_key_events
        (plan_down_prefix W) (plan_source_at W) (plan_key W)
   \<and> plan_key W \<in> plan_scope W
   \<and> plan_source_at W < plan_down_at W
   \<and> plan_down_at W \<le> plan_finish W"

lemma effective_source_first_dual_write_plan_imp_unprotected:
  assumes "effective_source_first_dual_write_plan W"
  shows "unprotected_source_first_dual_write_plan W"
proof -
  from assms have same:
      "same_downstream_effect (plan_event W) (plan_down_event W) (plan_key W)"
      and effect:
        "effective_source_effect (plan_base W) (plan_event W) (plan_key W)"
      and no_visible:
        "no_visible_key_events
          (plan_down_prefix W) (plan_source_at W) (plan_key W)"
      and scoped: "plan_key W \<in> plan_scope W"
      and source_first: "plan_source_at W < plan_down_at W"
      and finish: "plan_down_at W \<le> plan_finish W"
    by (auto simp: effective_source_first_dual_write_plan_def)
  have stale:
    "Src (plan_base W) (plan_down_prefix W)
       (plan_source_at W) (plan_key W)
     \<noteq> event_result (plan_event W)"
    by (rule effective_source_no_visible_downstream_imp_stale[OF effect no_visible])
  show ?thesis
    using same stale scoped source_first finish
    by (simp add: unprotected_source_first_dual_write_plan_def)
qed

lemma latest_src_event_source_first_window:
  assumes key: "key_of e = k"
      and vis: "c \<le> f"
      and no_vis: "\<forall>x \<in> set R. \<not> visible_src_event_at f k x"
  shows "latest_src_event (L @ [(c, e)] @ R) f k = Some (length L)"
proof -
  have "latest_src_event (L @ [(c, e)] @ R) f k =
        latest_src_event ((L @ [(c, e)]) @ R) f k"
    by simp
  also have "\<dots> = latest_src_event (L @ [(c, e)]) f k"
    by (rule latest_src_event_append_no_visible_key_events
        [where H = "L @ [(c, e)]" and X = R, OF no_vis])
  also have "\<dots> = Some (length L)"
    using key vis by (rule latest_src_event_snoc_at_key)
  finally show ?thesis .
qed

lemma Src_source_first_window:
  assumes key: "key_of e = k"
      and vis: "c \<le> f"
      and no_vis: "\<forall>x \<in> set R. \<not> visible_src_event_at f k x"
  shows "Src b (L @ [(c, e)] @ R) f k = event_result e"
proof -
  have latest: "latest_src_event (L @ [(c, e)] @ R) f k = Some (length L)"
    by (rule latest_src_event_source_first_window[OF key vis no_vis])
  have nth: "(L @ [(c, e)] @ R) ! length L = (c, e)"
    by simp
  show ?thesis
    using latest nth key
    by (cases e; simp add: src_characterized_by_latest_event)
qed

theorem executable_source_window_bad_crash_extension:
  assumes prefix:
    "dw_exec_trace s (pre @ [DoSource c_src e] @ gap) sp"
      and running: "running_labels (pre @ [DoSource c_src e] @ gap)"
      and start: "exec_status s = Running"
      and key: "key_of e = k"
      and scoped: "k \<in> exec_scope s"
      and src_le_crash: "c_src \<le> c_crash"
      and crash_le_fin: "c_crash \<le> exec_finish s"
      and no_later:
        "no_visible_key_events (src_hist_of_labels gap) c_crash k"
      and downstream_stale:
        "Src (exec_base s)
          (exec_down_hist s @ down_hist_of_labels pre @ down_hist_of_labels gap)
          c_crash k \<noteq> event_result e"
  shows "\<exists>s'.
      dw_exec_trace s (pre @ [DoSource c_src e] @ gap @ [Crash c_crash]) s'
    \<and> observable_mismatch s' c_crash k
    \<and> diverges (proto_of_exec_at s' c_crash) c_crash"
proof -
  let ?mid = "pre @ [DoSource c_src e] @ gap"
  let ?s' = "sp\<lparr>exec_status := Crashed c_crash\<rparr>"

  have sp_running: "exec_status sp = Running"
    by (rule dw_exec_trace_running_status[OF prefix running start])
  have crash_step: "dw_exec_step sp (Crash c_crash) ?s'"
    by (rule dw_exec_step.crash[OF sp_running])
  have crash_trace: "dw_exec_trace sp [Crash c_crash] ?s'"
    by (rule dw_exec_trace.trace_step[OF crash_step dw_exec_trace.trace_refl])
  have trace:
    "dw_exec_trace s (pre @ [DoSource c_src e] @ gap @ [Crash c_crash]) ?s'"
    using dw_exec_trace_append[OF prefix crash_trace]
    by simp

  have src_hist_sp:
    "exec_src_hist sp =
      exec_src_hist s @ src_hist_of_labels pre
        @ [(c_src, e)] @ src_hist_of_labels gap"
    using dw_exec_trace_src_hist[OF prefix]
    by (simp add: append_assoc)
  have down_hist_sp:
    "exec_down_hist sp =
      exec_down_hist s @ down_hist_of_labels pre @ down_hist_of_labels gap"
    using dw_exec_trace_down_hist[OF prefix]
    by (simp add: append_assoc)
  have base_sp: "exec_base sp = exec_base s"
    by (rule dw_exec_trace_base[OF prefix])
  have scope_sp: "exec_scope sp = exec_scope s"
    by (rule dw_exec_trace_scope[OF prefix])
  have finish_sp: "exec_finish sp = exec_finish s"
    by (rule dw_exec_trace_finish[OF prefix])

  have no_later_set:
    "\<forall>x \<in> set (src_hist_of_labels gap).
       \<not> visible_src_event_at c_crash k x"
    using no_later by (simp add: no_visible_key_events_def)
  have source_value:
    "Src (exec_base s)
      (exec_src_hist s @ src_hist_of_labels pre
        @ [(c_src, e)] @ src_hist_of_labels gap)
      c_crash k = event_result e"
  proof -
    have "Src (exec_base s)
        ((exec_src_hist s @ src_hist_of_labels pre)
          @ [(c_src, e)] @ src_hist_of_labels gap)
        c_crash k = event_result e"
      by (rule Src_source_first_window[OF key src_le_crash no_later_set])
    thus ?thesis by (simp add: append_assoc)
  qed
  have source_value_sp:
    "Src (exec_base ?s') (exec_src_hist ?s') c_crash k = event_result e"
    using source_value src_hist_sp base_sp by simp
  have downstream_value_sp:
    "Src (exec_base ?s') (exec_down_hist ?s') c_crash k \<noteq> event_result e"
    using downstream_stale down_hist_sp base_sp by simp
  have obs: "observable_mismatch ?s' c_crash k"
  proof (rule observable_mismatchI)
    show "exec_status ?s' = Crashed c_crash" by simp
  next
    show "c_crash \<le> exec_finish ?s'"
      using crash_le_fin finish_sp by simp
  next
    show "k \<in> exec_scope ?s'"
      using scoped scope_sp by simp
  next
    show "Src (exec_base ?s') (exec_down_hist ?s') c_crash k
          \<noteq> Src (exec_base ?s') (exec_src_hist ?s') c_crash k"
      using source_value_sp downstream_value_sp by simp
  qed
  hence div: "diverges (proto_of_exec_at ?s' c_crash) c_crash"
    by (rule observable_mismatch_imp_diverges)

  from trace obs div show ?thesis by blast
qed

theorem executable_source_window_acked_bad_crash_extension:
  assumes prefix:
    "dw_exec_trace s (pre @ [DoSource c_src e] @ gap) sp"
      and running: "running_labels (pre @ [DoSource c_src e] @ gap)"
      and start: "exec_status s = Running"
      and key: "key_of e = k"
      and scoped: "k \<in> exec_scope s"
      and src_le_crash: "c_src \<le> c_crash"
      and crash_le_fin: "c_crash \<le> exec_finish s"
      and no_later:
        "no_visible_key_events (src_hist_of_labels gap) c_crash k"
      and downstream_stale:
        "Src (exec_base s)
          (exec_down_hist s @ down_hist_of_labels pre @ down_hist_of_labels gap)
          c_crash k \<noteq> event_result e"
      and acked:
        "(c_src, e) \<in>
          set (exec_acked s @ acked_hist_of_labels
            (pre @ [DoSource c_src e] @ gap))"
  shows "\<exists>s'.
      dw_exec_trace s (pre @ [DoSource c_src e] @ gap @ [Crash c_crash]) s'
    \<and> observable_mismatch s' c_crash k
    \<and> acked_observable_mismatch s' c_crash k
    \<and> diverges (proto_of_exec_at s' c_crash) c_crash"
proof -
  from executable_source_window_bad_crash_extension
        [OF prefix running start key scoped src_le_crash crash_le_fin
            no_later downstream_stale]
  obtain s' where
      trace:
        "dw_exec_trace s (pre @ [DoSource c_src e] @ gap @ [Crash c_crash]) s'"
      and obs: "observable_mismatch s' c_crash k"
      and div: "diverges (proto_of_exec_at s' c_crash) c_crash"
    by blast
  have ack_s': "(c_src, e) \<in> set (exec_acked s')"
    using dw_exec_trace_acked[OF trace] acked by simp
  have src_hist_s':
    "exec_src_hist s' =
      exec_src_hist s @ src_hist_of_labels pre
        @ [(c_src, e)] @ src_hist_of_labels gap"
    using dw_exec_trace_src_hist[OF trace]
    by (simp add: append_assoc)
  have base_s': "exec_base s' = exec_base s"
    by (rule dw_exec_trace_base[OF trace])
  have no_later_set:
    "\<forall>x \<in> set (src_hist_of_labels gap).
       \<not> visible_src_event_at c_crash k x"
    using no_later by (simp add: no_visible_key_events_def)
  have source_value:
    "Src (exec_base s)
      (exec_src_hist s @ src_hist_of_labels pre
        @ [(c_src, e)] @ src_hist_of_labels gap)
      c_crash k = event_result e"
  proof -
    have "Src (exec_base s)
        ((exec_src_hist s @ src_hist_of_labels pre)
          @ [(c_src, e)] @ src_hist_of_labels gap)
        c_crash k = event_result e"
      by (rule Src_source_first_window[OF key src_le_crash no_later_set])
    thus ?thesis by (simp add: append_assoc)
  qed
  have source_value_s':
    "Src (exec_base s') (exec_src_hist s') c_crash k = event_result e"
    using source_value src_hist_s' base_s' by simp
  have ack_effect: "acked_source_effect_at s' c_crash k"
    using ack_s' src_le_crash key source_value_s'
    by (auto simp: acked_source_effect_at_def)
  have ack_obs: "acked_observable_mismatch s' c_crash k"
    using obs ack_effect by (simp add: acked_observable_mismatch_def)
  from trace obs ack_obs div show ?thesis by blast
qed

theorem executable_downstream_window_bad_crash_extension:
  assumes prefix:
    "dw_exec_trace s
      (pre @ [EnqueueDownstream c_down e_down,
              DoDownstream c_down e_down] @ gap) sp"
      and running:
        "running_labels
          (pre @ [EnqueueDownstream c_down e_down,
                  DoDownstream c_down e_down] @ gap)"
      and start: "exec_status s = Running"
      and key: "key_of e_down = k"
      and scoped: "k \<in> exec_scope s"
      and down_le_crash: "c_down \<le> c_crash"
      and crash_le_fin: "c_crash \<le> exec_finish s"
      and no_later:
        "no_visible_key_events (down_hist_of_labels gap) c_crash k"
      and source_stale:
        "Src (exec_base s)
          (exec_src_hist s @ src_hist_of_labels pre @ src_hist_of_labels gap)
          c_crash k \<noteq> event_result e_down"
  shows "\<exists>s'.
      dw_exec_trace s
        (pre @ [EnqueueDownstream c_down e_down,
                DoDownstream c_down e_down] @ gap @ [Crash c_crash]) s'
    \<and> observable_mismatch s' c_crash k
    \<and> diverges (proto_of_exec_at s' c_crash) c_crash"
proof -
  let ?mid =
    "pre @ [EnqueueDownstream c_down e_down,
            DoDownstream c_down e_down] @ gap"
  let ?s' = "sp\<lparr>exec_status := Crashed c_crash\<rparr>"

  have sp_running: "exec_status sp = Running"
    by (rule dw_exec_trace_running_status[OF prefix running start])
  have crash_step: "dw_exec_step sp (Crash c_crash) ?s'"
    by (rule dw_exec_step.crash[OF sp_running])
  have crash_trace: "dw_exec_trace sp [Crash c_crash] ?s'"
    by (rule dw_exec_trace.trace_step[OF crash_step dw_exec_trace.trace_refl])
  have trace:
    "dw_exec_trace s (?mid @ [Crash c_crash]) ?s'"
    using dw_exec_trace_append[OF prefix crash_trace]
    by simp

  have src_hist_sp:
    "exec_src_hist sp =
      exec_src_hist s @ src_hist_of_labels pre @ src_hist_of_labels gap"
    using dw_exec_trace_src_hist[OF prefix]
    by (simp add: append_assoc)
  have down_hist_sp:
    "exec_down_hist sp =
      exec_down_hist s @ down_hist_of_labels pre
        @ [(c_down, e_down)] @ down_hist_of_labels gap"
    using dw_exec_trace_down_hist[OF prefix]
    by (simp add: append_assoc)
  have base_sp: "exec_base sp = exec_base s"
    by (rule dw_exec_trace_base[OF prefix])
  have scope_sp: "exec_scope sp = exec_scope s"
    by (rule dw_exec_trace_scope[OF prefix])
  have finish_sp: "exec_finish sp = exec_finish s"
    by (rule dw_exec_trace_finish[OF prefix])

  have no_later_set:
    "\<forall>x \<in> set (down_hist_of_labels gap).
       \<not> visible_src_event_at c_crash k x"
    using no_later by (simp add: no_visible_key_events_def)
  have downstream_value:
    "Src (exec_base s)
      (exec_down_hist s @ down_hist_of_labels pre
        @ [(c_down, e_down)] @ down_hist_of_labels gap)
      c_crash k = event_result e_down"
  proof -
    have "Src (exec_base s)
        ((exec_down_hist s @ down_hist_of_labels pre)
          @ [(c_down, e_down)] @ down_hist_of_labels gap)
        c_crash k = event_result e_down"
      by (rule Src_source_first_window[OF key down_le_crash no_later_set])
    thus ?thesis by (simp add: append_assoc)
  qed
  have downstream_value_sp:
    "Src (exec_base ?s') (exec_down_hist ?s') c_crash k =
      event_result e_down"
    using downstream_value down_hist_sp base_sp by simp
  have source_stale_sp:
    "Src (exec_base ?s') (exec_src_hist ?s') c_crash k
      \<noteq> event_result e_down"
    using source_stale src_hist_sp base_sp by simp
  have obs: "observable_mismatch ?s' c_crash k"
  proof (rule observable_mismatchI)
    show "exec_status ?s' = Crashed c_crash" by simp
  next
    show "c_crash \<le> exec_finish ?s'"
      using crash_le_fin finish_sp by simp
  next
    show "k \<in> exec_scope ?s'"
      using scoped scope_sp by simp
  next
    show "Src (exec_base ?s') (exec_down_hist ?s') c_crash k
          \<noteq> Src (exec_base ?s') (exec_src_hist ?s') c_crash k"
      using downstream_value_sp source_stale_sp by simp
  qed
  hence div: "diverges (proto_of_exec_at ?s' c_crash) c_crash"
    by (rule observable_mismatch_imp_diverges)

  from trace obs div show ?thesis
    by (auto simp: append_assoc)
qed

subsection \<open>Operational source-first gaps\<close>

definition operational_gap_precrash_labels
  :: "('k, 'v) operational_source_first_gap_witness \<Rightarrow>
      ('k, 'v) dw_exec_label list"
where
  "operational_gap_precrash_labels G =
     osg_pre G @ [DoSource (osg_source_at G) (osg_event G)] @ osg_gap G"

definition operational_gap_crash_labels
  :: "('k, 'v) operational_source_first_gap_witness \<Rightarrow>
      ('k, 'v) dw_exec_label list"
where
  "operational_gap_crash_labels G =
     operational_gap_precrash_labels G @ [Crash (osg_crash_at G)]"

definition operational_source_first_gap
  :: "('k, 'v) operational_source_first_gap_witness \<Rightarrow> bool"
where
  "operational_source_first_gap G \<longleftrightarrow>
     (\<exists>sp.
        dw_exec_trace (osg_start G) (operational_gap_precrash_labels G) sp)
   \<and> running_labels (operational_gap_precrash_labels G)
   \<and> exec_status (osg_start G) = Running
   \<and> key_of (osg_event G) = osg_key G
   \<and> effective_source_effect
        (exec_base (osg_start G)) (osg_event G) (osg_key G)
   \<and> same_downstream_effect (osg_event G) (osg_down_event G) (osg_key G)
   \<and> osg_key G \<in> exec_scope (osg_start G)
   \<and> osg_source_at G < osg_down_at G
   \<and> osg_down_at G \<le> exec_finish (osg_start G)
   \<and> osg_source_at G \<le> osg_crash_at G
   \<and> osg_crash_at G \<le> exec_finish (osg_start G)
   \<and> no_visible_key_events (src_hist_of_labels (osg_gap G))
        (osg_crash_at G) (osg_key G)
   \<and> no_visible_key_events
        (exec_down_hist (osg_start G)
          @ down_hist_of_labels (osg_pre G)
          @ down_hist_of_labels (osg_gap G))
        (osg_crash_at G) (osg_key G)
   \<and> (osg_source_at G, osg_event G) \<in>
        set (exec_acked (osg_start G)
          @ acked_hist_of_labels (operational_gap_precrash_labels G))
   \<and> (osg_down_at G, osg_down_event G) \<in>
        set (enqueued_hist_of_labels (osg_gap G))
   \<and> (osg_down_at G, osg_down_event G) \<in>
        pending_after_labels (operational_gap_precrash_labels G)
          (exec_pending (osg_start G))"

theorem operational_source_first_gap_has_bad_crash_execution:
  assumes gap: "operational_source_first_gap G"
  shows "\<exists>s.
      dw_exec_trace (osg_start G) (operational_gap_crash_labels G) s
    \<and> (osg_down_at G, osg_down_event G) \<in> set (exec_enqueued s)
    \<and> (osg_down_at G, osg_down_event G) \<in> exec_pending s
    \<and> observable_mismatch s (osg_crash_at G) (osg_key G)
    \<and> acked_observable_mismatch s (osg_crash_at G) (osg_key G)
    \<and> diverges (proto_of_exec_at s (osg_crash_at G)) (osg_crash_at G)"
proof -
  from gap obtain sp where prefix:
    "dw_exec_trace (osg_start G) (operational_gap_precrash_labels G) sp"
    by (auto simp: operational_source_first_gap_def)
  from gap have running:
      "running_labels (operational_gap_precrash_labels G)"
      and start: "exec_status (osg_start G) = Running"
      and key: "key_of (osg_event G) = osg_key G"
      and effect:
        "effective_source_effect
          (exec_base (osg_start G)) (osg_event G) (osg_key G)"
      and scoped: "osg_key G \<in> exec_scope (osg_start G)"
      and src_le_crash: "osg_source_at G \<le> osg_crash_at G"
      and crash_le_fin: "osg_crash_at G \<le> exec_finish (osg_start G)"
      and no_later:
        "no_visible_key_events (src_hist_of_labels (osg_gap G))
          (osg_crash_at G) (osg_key G)"
      and down_no_visible:
        "no_visible_key_events
          (exec_down_hist (osg_start G)
            @ down_hist_of_labels (osg_pre G)
            @ down_hist_of_labels (osg_gap G))
          (osg_crash_at G) (osg_key G)"
      and acked:
        "(osg_source_at G, osg_event G) \<in>
          set (exec_acked (osg_start G)
            @ acked_hist_of_labels (operational_gap_precrash_labels G))"
      and enqueued_intent:
        "(osg_down_at G, osg_down_event G) \<in>
          set (enqueued_hist_of_labels (osg_gap G))"
      and pending_intent:
        "(osg_down_at G, osg_down_event G) \<in>
          pending_after_labels (operational_gap_precrash_labels G)
            (exec_pending (osg_start G))"
    by (auto simp: operational_source_first_gap_def)

  have prefix':
    "dw_exec_trace (osg_start G)
      (osg_pre G @ [DoSource (osg_source_at G) (osg_event G)] @ osg_gap G)
      sp"
    using prefix by (simp add: operational_gap_precrash_labels_def)
  have running':
    "running_labels
      (osg_pre G @ [DoSource (osg_source_at G) (osg_event G)] @ osg_gap G)"
    using running by (simp add: operational_gap_precrash_labels_def)
  have acked':
    "(osg_source_at G, osg_event G) \<in>
      set (exec_acked (osg_start G)
        @ acked_hist_of_labels
            (osg_pre G @ [DoSource (osg_source_at G) (osg_event G)]
              @ osg_gap G))"
    using acked by (simp add: operational_gap_precrash_labels_def)
  have downstream_stale:
    "Src (exec_base (osg_start G))
      (exec_down_hist (osg_start G)
        @ down_hist_of_labels (osg_pre G)
        @ down_hist_of_labels (osg_gap G))
      (osg_crash_at G) (osg_key G)
      \<noteq> event_result (osg_event G)"
    by (rule effective_source_no_visible_downstream_imp_stale
        [OF effect down_no_visible])

  from executable_source_window_acked_bad_crash_extension
        [OF prefix' running' start key scoped src_le_crash crash_le_fin
            no_later downstream_stale acked']
  obtain s where
      trace':
        "dw_exec_trace (osg_start G)
          (osg_pre G @ [DoSource (osg_source_at G) (osg_event G)]
            @ osg_gap G @ [Crash (osg_crash_at G)]) s"
      and obs: "observable_mismatch s (osg_crash_at G) (osg_key G)"
      and ack_obs:
        "acked_observable_mismatch s (osg_crash_at G) (osg_key G)"
      and div:
        "diverges (proto_of_exec_at s (osg_crash_at G)) (osg_crash_at G)"
    by blast
  have trace:
    "dw_exec_trace (osg_start G) (operational_gap_crash_labels G) s"
    using trace'
    by (simp add: operational_gap_crash_labels_def
                  operational_gap_precrash_labels_def)
  have enqueued:
    "(osg_down_at G, osg_down_event G) \<in> set (exec_enqueued s)"
    using dw_exec_trace_enqueued[OF trace] enqueued_intent
    by (auto simp: operational_gap_crash_labels_def
                   operational_gap_precrash_labels_def)
  have pending:
    "(osg_down_at G, osg_down_event G) \<in> exec_pending s"
    using dw_exec_trace_pending[OF trace] pending_intent
    by (simp add: operational_gap_crash_labels_def)
  from trace enqueued pending obs ack_obs div show ?thesis by blast
qed

definition bad_crash_execution_for_gap
  :: "('k, 'v) operational_source_first_gap_witness \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  "bad_crash_execution_for_gap G s \<longleftrightarrow>
     dw_exec_trace (osg_start G) (operational_gap_crash_labels G) s
   \<and> (osg_down_at G, osg_down_event G) \<in> set (exec_enqueued s)
   \<and> (osg_down_at G, osg_down_event G) \<in> exec_pending s
   \<and> observable_mismatch s (osg_crash_at G) (osg_key G)
   \<and> acked_observable_mismatch s (osg_crash_at G) (osg_key G)
   \<and> diverges (proto_of_exec_at s (osg_crash_at G)) (osg_crash_at G)"

corollary operational_source_first_gap_obtains_bad_crash_execution:
  assumes "operational_source_first_gap G"
  shows "\<exists>s. bad_crash_execution_for_gap G s"
  using operational_source_first_gap_has_bad_crash_execution[OF assms]
  by (auto simp: bad_crash_execution_for_gap_def)

subsection \<open>Implementation admissibility\<close>

definition implementation_gap_precrash_labels
  :: "('k, 'v) implementation_source_first_gap_witness \<Rightarrow>
      ('k, 'v) dw_exec_label list"
where
  "implementation_gap_precrash_labels W =
     isfg_pre W @ [DoSource (isfg_source_at W) (isfg_event W)] @ isfg_gap W"

definition implementation_gap_crash_labels
  :: "('k, 'v) implementation_source_first_gap_witness \<Rightarrow>
      ('k, 'v) dw_exec_label list"
where
  "implementation_gap_crash_labels W =
     implementation_gap_precrash_labels W @ [Crash (isfg_crash_at W)]"

definition operational_gap_of_implementation_gap
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) implementation_source_first_gap_witness \<Rightarrow>
      ('k, 'v) operational_source_first_gap_witness"
where
  "operational_gap_of_implementation_gap I W =
     \<lparr> osg_start = dwi_state I (dwi_initial I),
       osg_pre = isfg_pre W,
       osg_gap = isfg_gap W,
       osg_key = isfg_key W,
       osg_source_at = isfg_source_at W,
       osg_event = isfg_event W,
       osg_down_at = isfg_down_at W,
       osg_down_event = isfg_down_event W,
       osg_crash_at = isfg_crash_at W \<rparr>"

definition implementation_gap_of_operational_gap
  :: "('k, 'v) operational_source_first_gap_witness \<Rightarrow>
      ('k, 'v) implementation_source_first_gap_witness"
where
  "implementation_gap_of_operational_gap G =
     \<lparr> isfg_pre = osg_pre G,
       isfg_gap = osg_gap G,
       isfg_key = osg_key G,
       isfg_source_at = osg_source_at G,
       isfg_event = osg_event G,
       isfg_down_at = osg_down_at G,
       isfg_down_event = osg_down_event G,
       isfg_crash_at = osg_crash_at G \<rparr>"

definition implementation_admits_source_first_gap
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) implementation_source_first_gap_witness \<Rightarrow> bool"
where
  "implementation_admits_source_first_gap I W \<longleftrightarrow>
     dwi_refines_exec I
   \<and> (\<exists>s.
        dwi_trace I (dwi_initial I) (implementation_gap_precrash_labels W) s)
   \<and> running_labels (implementation_gap_precrash_labels W)
   \<and> exec_status (dwi_state I (dwi_initial I)) = Running
   \<and> key_of (isfg_event W) = isfg_key W
   \<and> effective_source_effect
        (exec_base (dwi_state I (dwi_initial I)))
        (isfg_event W) (isfg_key W)
   \<and> same_downstream_effect (isfg_event W) (isfg_down_event W) (isfg_key W)
   \<and> isfg_key W \<in> exec_scope (dwi_state I (dwi_initial I))
   \<and> isfg_source_at W < isfg_down_at W
   \<and> isfg_down_at W \<le> exec_finish (dwi_state I (dwi_initial I))
   \<and> isfg_source_at W \<le> isfg_crash_at W
   \<and> isfg_crash_at W \<le> exec_finish (dwi_state I (dwi_initial I))
   \<and> no_visible_key_events (src_hist_of_labels (isfg_gap W))
        (isfg_crash_at W) (isfg_key W)
   \<and> no_visible_key_events
        (exec_down_hist (dwi_state I (dwi_initial I))
          @ down_hist_of_labels (isfg_pre W)
          @ down_hist_of_labels (isfg_gap W))
        (isfg_crash_at W) (isfg_key W)
   \<and> (isfg_source_at W, isfg_event W) \<in>
        set (exec_acked (dwi_state I (dwi_initial I))
          @ acked_hist_of_labels (implementation_gap_precrash_labels W))
   \<and> (isfg_down_at W, isfg_down_event W) \<in>
        set (enqueued_hist_of_labels (isfg_gap W))
   \<and> (isfg_down_at W, isfg_down_event W) \<in>
        pending_after_labels (implementation_gap_precrash_labels W)
          (exec_pending (dwi_state I (dwi_initial I)))"

definition source_first_gap_admissible_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "source_first_gap_admissible_implementation I \<longleftrightarrow>
     (\<exists>W. implementation_admits_source_first_gap I W)"

lemma implementation_admits_source_first_gap_imp_operational_source_first_gap:
  assumes impl_gap: "implementation_admits_source_first_gap I W"
  shows "operational_source_first_gap (operational_gap_of_implementation_gap I W)"
proof -
  from impl_gap obtain s where trace:
    "dwi_trace I (dwi_initial I) (implementation_gap_precrash_labels W) s"
    by (auto simp: implementation_admits_source_first_gap_def)
  from impl_gap have refines: "dwi_refines_exec I"
    by (simp add: implementation_admits_source_first_gap_def)
  have exec_trace:
    "dw_exec_trace (dwi_state I (dwi_initial I))
      (implementation_gap_precrash_labels W) (dwi_state I s)"
    by (rule dwi_trace_refines_exec[OF refines trace])
  show ?thesis
    using impl_gap exec_trace
    by (auto simp: implementation_admits_source_first_gap_def
                   operational_source_first_gap_def
                   operational_gap_of_implementation_gap_def
                   implementation_gap_precrash_labels_def
                   operational_gap_precrash_labels_def)
qed

theorem implementation_admits_source_first_gap_has_abstract_bad_crash_execution:
  assumes impl: "implementation_admits_source_first_gap I W"
  shows "\<exists>s. bad_crash_execution_for_gap
    (operational_gap_of_implementation_gap I W) s"
proof -
  have gap: "operational_source_first_gap (operational_gap_of_implementation_gap I W)"
    by (rule implementation_admits_source_first_gap_imp_operational_source_first_gap
        [OF impl])
  show ?thesis
    by (rule operational_source_first_gap_obtains_bad_crash_execution[OF gap])
qed

theorem source_first_gap_admissible_implementation_has_abstract_bad_crash_execution:
  assumes impl: "source_first_gap_admissible_implementation I"
  shows "\<exists>W s.
      implementation_admits_source_first_gap I W
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I W) s"
proof -
  from impl obtain W where W: "implementation_admits_source_first_gap I W"
    by (auto simp: source_first_gap_admissible_implementation_def)
  from implementation_admits_source_first_gap_has_abstract_bad_crash_execution
        [OF W]
  obtain s where
    "bad_crash_execution_for_gap (operational_gap_of_implementation_gap I W) s"
    by blast
  with W show ?thesis by blast
qed

corollary all_source_first_gap_admissible_implementations_have_abstract_bad_crash_execution:
  "\<forall>I. source_first_gap_admissible_implementation I
    \<longrightarrow> (\<exists>W s.
        implementation_admits_source_first_gap I W
      \<and> bad_crash_execution_for_gap
          (operational_gap_of_implementation_gap I W) s)"
  using source_first_gap_admissible_implementation_has_abstract_bad_crash_execution
  by blast

definition implementation_crash_enabled_for_gap
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) implementation_source_first_gap_witness \<Rightarrow> bool"
where
  "implementation_crash_enabled_for_gap I W \<longleftrightarrow>
     (\<forall>s. dwi_trace I (dwi_initial I) (implementation_gap_precrash_labels W) s
       \<longrightarrow> (\<exists>s'. dwi_step I s (Crash (isfg_crash_at W)) s'))"

text \<open>Crash-closure quantifies over the TRACE-REACHABLE fragment: the
  Crash-enabledness obligation binds exactly the states an execution of the
  implementation can reach, matching the trace quantification of the sibling
  trace predicates, and every consuming proof applies it at a reached state.
  Concrete implementations typically discharge the stronger all-states
  obligation; the bridge lemma below converts it.\<close>

definition crash_closed_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "crash_closed_implementation I \<longleftrightarrow>
     (\<forall>s c. (\<exists>xs. dwi_trace I (dwi_initial I) xs s)
       \<and> exec_status (dwi_state I s) = Running
       \<and> c \<le> exec_finish (dwi_state I s)
       \<longrightarrow> (\<exists>s'. dwi_step I s (Crash c) s'))"

lemma all_states_crash_closure_imp_crash_closed_implementation:
  assumes "\<And>s c. \<lbrakk>exec_status (dwi_state I s) = Running;
                  c \<le> exec_finish (dwi_state I s)\<rbrakk>
           \<Longrightarrow> \<exists>s'. dwi_step I s (Crash c) s'"
  shows "crash_closed_implementation I"
  using assms by (auto simp: crash_closed_implementation_def)

lemma crash_closed_imp_implementation_crash_enabled_for_gap:
  assumes closed: "crash_closed_implementation I"
      and gap: "implementation_admits_source_first_gap I W"
  shows "implementation_crash_enabled_for_gap I W"
proof -
  from gap have refines: "dwi_refines_exec I"
      and running: "running_labels (implementation_gap_precrash_labels W)"
      and start: "exec_status (dwi_state I (dwi_initial I)) = Running"
      and crash_le_fin:
        "isfg_crash_at W \<le> exec_finish (dwi_state I (dwi_initial I))"
    by (auto simp: implementation_admits_source_first_gap_def)
  show ?thesis
  proof (auto simp: implementation_crash_enabled_for_gap_def)
    fix s
    assume trace:
      "dwi_trace I (dwi_initial I) (implementation_gap_precrash_labels W) s"
    have exec_trace:
      "dw_exec_trace (dwi_state I (dwi_initial I))
        (implementation_gap_precrash_labels W) (dwi_state I s)"
      by (rule dwi_trace_refines_exec[OF refines trace])
    have status: "exec_status (dwi_state I s) = Running"
      by (rule dw_exec_trace_running_status[OF exec_trace running start])
    have finish:
      "exec_finish (dwi_state I s) =
       exec_finish (dwi_state I (dwi_initial I))"
      by (rule dw_exec_trace_finish[OF exec_trace])
    have le_s: "isfg_crash_at W \<le> exec_finish (dwi_state I s)"
      using crash_le_fin finish by simp
    from closed trace status le_s show
      "\<exists>s'. dwi_step I s (Crash (isfg_crash_at W)) s'"
      unfolding crash_closed_implementation_def by blast
  qed
qed

definition source_first_gap_crash_admissible_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "source_first_gap_crash_admissible_implementation I \<longleftrightarrow>
     (\<exists>W.
        implementation_admits_source_first_gap I W
      \<and> implementation_crash_enabled_for_gap I W)"

theorem implementation_admits_source_first_gap_with_crash_has_concrete_bad_crash_execution:
  assumes gap: "implementation_admits_source_first_gap I W"
      and crash_enabled: "implementation_crash_enabled_for_gap I W"
  shows "\<exists>s.
      dwi_trace I (dwi_initial I) (implementation_gap_crash_labels W) s
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I W) (dwi_state I s)"
proof -
  from gap obtain sp where pre_trace:
    "dwi_trace I (dwi_initial I) (implementation_gap_precrash_labels W) sp"
    by (auto simp: implementation_admits_source_first_gap_def)
  from crash_enabled pre_trace obtain s where crash_step:
    "dwi_step I sp (Crash (isfg_crash_at W)) s"
    by (auto simp: implementation_crash_enabled_for_gap_def)
  have crash_trace:
    "dwi_trace I sp [Crash (isfg_crash_at W)] s"
    by (rule dwi_trace.dwi_trace_step
        [OF crash_step dwi_trace.dwi_trace_refl])
  have full_trace:
    "dwi_trace I (dwi_initial I) (implementation_gap_crash_labels W) s"
    using dwi_trace_append[OF pre_trace crash_trace]
    by (simp add: implementation_gap_crash_labels_def)

  from gap have refines: "dwi_refines_exec I"
    by (simp add: implementation_admits_source_first_gap_def)
  have exec_full:
    "dw_exec_trace (dwi_state I (dwi_initial I))
      (implementation_gap_crash_labels W) (dwi_state I s)"
    by (rule dwi_trace_refines_exec[OF refines full_trace])

  have op_gap:
    "operational_source_first_gap (operational_gap_of_implementation_gap I W)"
    by (rule implementation_admits_source_first_gap_imp_operational_source_first_gap
        [OF gap])
  from operational_source_first_gap_obtains_bad_crash_execution[OF op_gap]
  obtain s_abs where bad_abs:
    "bad_crash_execution_for_gap (operational_gap_of_implementation_gap I W) s_abs"
    by blast
  have exec_abs:
    "dw_exec_trace (dwi_state I (dwi_initial I))
      (implementation_gap_crash_labels W) s_abs"
    using bad_abs
    by (simp add: bad_crash_execution_for_gap_def
                  operational_gap_of_implementation_gap_def
                  operational_gap_crash_labels_def
                  operational_gap_precrash_labels_def
                  implementation_gap_crash_labels_def
                  implementation_gap_precrash_labels_def)
  have same_state: "dwi_state I s = s_abs"
    by (rule dw_exec_trace_deterministic[OF exec_full exec_abs])
  hence bad_concrete:
    "bad_crash_execution_for_gap
      (operational_gap_of_implementation_gap I W) (dwi_state I s)"
    using bad_abs by simp
  from full_trace bad_concrete show ?thesis by blast
qed

theorem source_first_gap_crash_admissible_implementation_has_concrete_bad_crash_execution:
  assumes impl: "source_first_gap_crash_admissible_implementation I"
  shows "\<exists>W s.
      implementation_admits_source_first_gap I W
    \<and> implementation_crash_enabled_for_gap I W
    \<and> dwi_trace I (dwi_initial I) (implementation_gap_crash_labels W) s
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I W) (dwi_state I s)"
proof -
  from impl obtain W where gap: "implementation_admits_source_first_gap I W"
      and crash: "implementation_crash_enabled_for_gap I W"
    by (auto simp: source_first_gap_crash_admissible_implementation_def)
  from implementation_admits_source_first_gap_with_crash_has_concrete_bad_crash_execution
        [OF gap crash]
  obtain s where trace:
      "dwi_trace I (dwi_initial I) (implementation_gap_crash_labels W) s"
      and bad:
        "bad_crash_execution_for_gap
          (operational_gap_of_implementation_gap I W) (dwi_state I s)"
    by blast
  from gap crash trace bad show ?thesis by blast
qed

corollary all_source_first_gap_crash_admissible_implementations_have_concrete_bad_crash_execution:
  "\<forall>I. source_first_gap_crash_admissible_implementation I
    \<longrightarrow> (\<exists>W s.
        implementation_admits_source_first_gap I W
      \<and> implementation_crash_enabled_for_gap I W
      \<and> dwi_trace I (dwi_initial I) (implementation_gap_crash_labels W) s
      \<and> bad_crash_execution_for_gap
          (operational_gap_of_implementation_gap I W) (dwi_state I s))"
  using source_first_gap_crash_admissible_implementation_has_concrete_bad_crash_execution
  by blast

subsection \<open>Non-atomic source-first implementations without a shared commit\<close>

definition source_first_no_shared_commit_gap_labels
  :: "('k, 'v) source_first_no_shared_commit_window \<Rightarrow>
      ('k, 'v) dw_exec_label list"
where
  "source_first_no_shared_commit_gap_labels W =
     [Ack (sfnc_source_at W) (sfnc_event W),
      EnqueueDownstream (sfnc_down_at W) (sfnc_down_event W)]"

definition source_first_no_shared_commit_precrash_labels
  :: "('k, 'v) source_first_no_shared_commit_window \<Rightarrow>
      ('k, 'v) dw_exec_label list"
where
  "source_first_no_shared_commit_precrash_labels W =
     sfnc_pre W @ [DoSource (sfnc_source_at W) (sfnc_event W)]
       @ source_first_no_shared_commit_gap_labels W"

definition implementation_gap_of_no_shared_commit_window
  :: "('k, 'v) source_first_no_shared_commit_window \<Rightarrow>
      ('k, 'v) implementation_source_first_gap_witness"
where
  "implementation_gap_of_no_shared_commit_window W =
     \<lparr> isfg_pre = sfnc_pre W,
       isfg_gap = source_first_no_shared_commit_gap_labels W,
       isfg_key = sfnc_key W,
       isfg_source_at = sfnc_source_at W,
       isfg_event = sfnc_event W,
       isfg_down_at = sfnc_down_at W,
       isfg_down_event = sfnc_down_event W,
       isfg_crash_at = sfnc_crash_at W \<rparr>"

definition implementation_admits_no_shared_commit_source_first_window
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) source_first_no_shared_commit_window \<Rightarrow> bool"
where
  "implementation_admits_no_shared_commit_source_first_window I W \<longleftrightarrow>
     dwi_refines_exec I
   \<and> (\<exists>s. dwi_trace I (dwi_initial I)
        (source_first_no_shared_commit_precrash_labels W) s)
   \<and> running_labels (sfnc_pre W)
   \<and> exec_status (dwi_state I (dwi_initial I)) = Running
   \<and> key_of (sfnc_event W) = sfnc_key W
   \<and> effective_source_effect
        (exec_base (dwi_state I (dwi_initial I)))
        (sfnc_event W) (sfnc_key W)
   \<and> same_downstream_effect (sfnc_event W) (sfnc_down_event W) (sfnc_key W)
   \<and> sfnc_key W \<in> exec_scope (dwi_state I (dwi_initial I))
   \<and> sfnc_source_at W \<le> sfnc_crash_at W
   \<and> sfnc_crash_at W < sfnc_down_at W
   \<and> sfnc_down_at W \<le> exec_finish (dwi_state I (dwi_initial I))
   \<and> no_visible_key_events
        (exec_down_hist (dwi_state I (dwi_initial I))
          @ down_hist_of_labels (sfnc_pre W))
        (sfnc_crash_at W) (sfnc_key W)"

definition no_shared_commit_source_first_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "no_shared_commit_source_first_implementation I \<longleftrightarrow>
     (\<exists>W. implementation_admits_no_shared_commit_source_first_window I W)"

definition no_shared_commit_source_first_crash_admissible_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "no_shared_commit_source_first_crash_admissible_implementation I \<longleftrightarrow>
     (\<exists>W.
        implementation_admits_no_shared_commit_source_first_window I W
      \<and> implementation_crash_enabled_for_gap I
          (implementation_gap_of_no_shared_commit_window W))"

lemma implementation_admits_no_shared_commit_source_first_window_imp_implementation_admits_source_first_gap:
  assumes window: "implementation_admits_no_shared_commit_source_first_window I W"
  shows "implementation_admits_source_first_gap
    I (implementation_gap_of_no_shared_commit_window W)"
proof -
  from window obtain s where trace:
    "dwi_trace I (dwi_initial I)
      (source_first_no_shared_commit_precrash_labels W) s"
    by (auto simp: implementation_admits_no_shared_commit_source_first_window_def)
  from window have crash_le_fin:
    "sfnc_crash_at W \<le> exec_finish (dwi_state I (dwi_initial I))"
    by (meson implementation_admits_no_shared_commit_source_first_window_def
        less_imp_le order_trans)
  from window show ?thesis
    using trace crash_le_fin
    by (auto simp:
        implementation_admits_source_first_gap_def
        implementation_admits_no_shared_commit_source_first_window_def
        implementation_gap_of_no_shared_commit_window_def
        implementation_gap_precrash_labels_def
        source_first_no_shared_commit_precrash_labels_def
        source_first_no_shared_commit_gap_labels_def
        running_labels_def running_label_def
        no_visible_key_events_def
        order_less_imp_le)
qed

theorem no_shared_commit_source_first_implementation_has_abstract_bad_crash_execution:
  assumes impl: "no_shared_commit_source_first_implementation I"
  shows "\<exists>W s.
      implementation_admits_no_shared_commit_source_first_window I W
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I
          (implementation_gap_of_no_shared_commit_window W)) s"
proof -
  from impl obtain W where window:
    "implementation_admits_no_shared_commit_source_first_window I W"
    by (auto simp: no_shared_commit_source_first_implementation_def)
  have gap: "implementation_admits_source_first_gap
      I (implementation_gap_of_no_shared_commit_window W)"
    by (rule
        implementation_admits_no_shared_commit_source_first_window_imp_implementation_admits_source_first_gap
        [OF window])
  from implementation_admits_source_first_gap_has_abstract_bad_crash_execution
        [OF gap]
  obtain s where bad:
    "bad_crash_execution_for_gap
      (operational_gap_of_implementation_gap I
        (implementation_gap_of_no_shared_commit_window W)) s"
    by blast
  from window bad show ?thesis by blast
qed

theorem no_shared_commit_source_first_crash_admissible_implementation_has_concrete_bad_crash_execution:
  assumes impl: "no_shared_commit_source_first_crash_admissible_implementation I"
  shows "\<exists>W s.
      implementation_admits_no_shared_commit_source_first_window I W
    \<and> implementation_crash_enabled_for_gap I
        (implementation_gap_of_no_shared_commit_window W)
    \<and> dwi_trace I (dwi_initial I)
        (implementation_gap_crash_labels
          (implementation_gap_of_no_shared_commit_window W)) s
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I
          (implementation_gap_of_no_shared_commit_window W))
        (dwi_state I s)"
proof -
  from impl obtain W where window:
      "implementation_admits_no_shared_commit_source_first_window I W"
      and crash:
        "implementation_crash_enabled_for_gap I
          (implementation_gap_of_no_shared_commit_window W)"
    by (auto simp: no_shared_commit_source_first_crash_admissible_implementation_def)
  have gap: "implementation_admits_source_first_gap
      I (implementation_gap_of_no_shared_commit_window W)"
    by (rule
        implementation_admits_no_shared_commit_source_first_window_imp_implementation_admits_source_first_gap
        [OF window])
  from implementation_admits_source_first_gap_with_crash_has_concrete_bad_crash_execution
        [OF gap crash]
  obtain s where trace:
      "dwi_trace I (dwi_initial I)
        (implementation_gap_crash_labels
          (implementation_gap_of_no_shared_commit_window W)) s"
      and bad:
        "bad_crash_execution_for_gap
          (operational_gap_of_implementation_gap I
            (implementation_gap_of_no_shared_commit_window W))
          (dwi_state I s)"
    by blast
  from window crash trace bad show ?thesis by blast
qed

subsection \<open>Prefix-crash schedules and pending-intent windows\<close>

definition source_ack_enqueue_downstream_completion_schedule
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) source_first_no_shared_commit_window \<Rightarrow> bool"
where
  "source_ack_enqueue_downstream_completion_schedule I W \<longleftrightarrow>
     (\<exists>s_pre s_src s_ack s_enq s_down.
        dwi_trace I (dwi_initial I) (sfnc_pre W) s_pre
      \<and> dwi_step I s_pre
          (DoSource (sfnc_source_at W) (sfnc_event W)) s_src
      \<and> dwi_step I s_src
          (Ack (sfnc_source_at W) (sfnc_event W)) s_ack
      \<and> dwi_step I s_ack
          (EnqueueDownstream (sfnc_down_at W) (sfnc_down_event W)) s_enq
      \<and> dwi_step I s_enq
          (DoDownstream (sfnc_down_at W) (sfnc_down_event W)) s_down)"

definition prefix_crash_no_shared_commit_source_first_window
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) source_first_no_shared_commit_window \<Rightarrow> bool"
where
  "prefix_crash_no_shared_commit_source_first_window I W \<longleftrightarrow>
     dwi_refines_exec I
   \<and> source_ack_enqueue_downstream_completion_schedule I W
   \<and> running_labels (sfnc_pre W)
   \<and> exec_status (dwi_state I (dwi_initial I)) = Running
   \<and> key_of (sfnc_event W) = sfnc_key W
   \<and> effective_source_effect
        (exec_base (dwi_state I (dwi_initial I)))
        (sfnc_event W) (sfnc_key W)
   \<and> same_downstream_effect (sfnc_event W) (sfnc_down_event W) (sfnc_key W)
   \<and> sfnc_key W \<in> exec_scope (dwi_state I (dwi_initial I))
   \<and> sfnc_source_at W \<le> sfnc_crash_at W
   \<and> sfnc_crash_at W < sfnc_down_at W
   \<and> sfnc_down_at W \<le> exec_finish (dwi_state I (dwi_initial I))
   \<and> no_visible_key_events
        (exec_down_hist (dwi_state I (dwi_initial I))
          @ down_hist_of_labels (sfnc_pre W))
        (sfnc_crash_at W) (sfnc_key W)"

definition prefix_crash_no_shared_commit_source_first_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "prefix_crash_no_shared_commit_source_first_implementation I \<longleftrightarrow>
     (\<exists>W. prefix_crash_no_shared_commit_source_first_window I W)"

definition prefix_crash_no_shared_commit_crash_admissible_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "prefix_crash_no_shared_commit_crash_admissible_implementation I \<longleftrightarrow>
     (\<exists>W.
        prefix_crash_no_shared_commit_source_first_window I W
      \<and> implementation_crash_enabled_for_gap I
          (implementation_gap_of_no_shared_commit_window W))"

lemma source_ack_enqueue_downstream_completion_schedule_imp_adversarial_precrash_trace:
  assumes schedule: "source_ack_enqueue_downstream_completion_schedule I W"
  shows "\<exists>s.
    dwi_trace I (dwi_initial I)
      (source_first_no_shared_commit_precrash_labels W) s"
proof -
  from schedule obtain s_pre s_src s_ack s_enq s_down where
      pre: "dwi_trace I (dwi_initial I) (sfnc_pre W) s_pre"
      and source:
        "dwi_step I s_pre
          (DoSource (sfnc_source_at W) (sfnc_event W)) s_src"
      and ack:
        "dwi_step I s_src
          (Ack (sfnc_source_at W) (sfnc_event W)) s_ack"
      and enqueue:
        "dwi_step I s_ack
          (EnqueueDownstream (sfnc_down_at W) (sfnc_down_event W)) s_enq"
    by (auto simp: source_ack_enqueue_downstream_completion_schedule_def)
  have source_trace:
    "dwi_trace I s_pre [DoSource (sfnc_source_at W) (sfnc_event W)] s_src"
    by (rule dwi_trace.dwi_trace_step[OF source dwi_trace.dwi_trace_refl])
  have ack_trace:
    "dwi_trace I s_src [Ack (sfnc_source_at W) (sfnc_event W)] s_ack"
    by (rule dwi_trace.dwi_trace_step[OF ack dwi_trace.dwi_trace_refl])
  have enqueue_trace:
    "dwi_trace I s_ack
      [EnqueueDownstream (sfnc_down_at W) (sfnc_down_event W)] s_enq"
    by (rule dwi_trace.dwi_trace_step[OF enqueue dwi_trace.dwi_trace_refl])
  have pre_source:
    "dwi_trace I (dwi_initial I)
      (sfnc_pre W @ [DoSource (sfnc_source_at W) (sfnc_event W)]) s_src"
    by (rule dwi_trace_append[OF pre source_trace])
  have pre_ack:
    "dwi_trace I (dwi_initial I)
      (sfnc_pre W @ [DoSource (sfnc_source_at W) (sfnc_event W)]
        @ [Ack (sfnc_source_at W) (sfnc_event W)]) s_ack"
    using dwi_trace_append[OF pre_source ack_trace]
    by simp
  have pre_enqueue:
    "dwi_trace I (dwi_initial I)
      (sfnc_pre W @ [DoSource (sfnc_source_at W) (sfnc_event W)]
        @ [Ack (sfnc_source_at W) (sfnc_event W),
           EnqueueDownstream (sfnc_down_at W) (sfnc_down_event W)]) s_enq"
    using dwi_trace_append[OF pre_ack enqueue_trace]
    by simp
  thus ?thesis
    by (auto simp: source_first_no_shared_commit_precrash_labels_def
                   source_first_no_shared_commit_gap_labels_def)
qed

lemma prefix_crash_no_shared_commit_source_first_window_imp_no_shared_commit_source_first_window:
  assumes window: "prefix_crash_no_shared_commit_source_first_window I W"
  shows "implementation_admits_no_shared_commit_source_first_window I W"
proof -
  from window have trace:
    "\<exists>s. dwi_trace I (dwi_initial I)
      (source_first_no_shared_commit_precrash_labels W) s"
    by (auto simp: prefix_crash_no_shared_commit_source_first_window_def
        dest: source_ack_enqueue_downstream_completion_schedule_imp_adversarial_precrash_trace)
  from window show ?thesis
    using trace
    by (auto simp:
        prefix_crash_no_shared_commit_source_first_window_def
        implementation_admits_no_shared_commit_source_first_window_def)
qed

corollary prefix_crash_no_shared_commit_source_first_window_imp_source_first_gap_admissible:
  assumes "prefix_crash_no_shared_commit_source_first_window I W"
  shows "source_first_gap_admissible_implementation I"
  using
    implementation_admits_no_shared_commit_source_first_window_imp_implementation_admits_source_first_gap
      [OF prefix_crash_no_shared_commit_source_first_window_imp_no_shared_commit_source_first_window
        [OF assms]]
  by (auto simp: source_first_gap_admissible_implementation_def)

theorem prefix_crash_no_shared_commit_source_first_implementation_has_abstract_bad_crash_execution:
  assumes impl: "prefix_crash_no_shared_commit_source_first_implementation I"
  shows "\<exists>W s.
      prefix_crash_no_shared_commit_source_first_window I W
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I
          (implementation_gap_of_no_shared_commit_window W)) s"
proof -
  from impl obtain W where window:
    "prefix_crash_no_shared_commit_source_first_window I W"
    by (auto simp: prefix_crash_no_shared_commit_source_first_implementation_def)
  have no_shared:
    "implementation_admits_no_shared_commit_source_first_window I W"
    by (rule
        prefix_crash_no_shared_commit_source_first_window_imp_no_shared_commit_source_first_window
        [OF window])
  have gap:
    "implementation_admits_source_first_gap
      I (implementation_gap_of_no_shared_commit_window W)"
    by (rule
        implementation_admits_no_shared_commit_source_first_window_imp_implementation_admits_source_first_gap
        [OF no_shared])
  from implementation_admits_source_first_gap_has_abstract_bad_crash_execution
        [OF gap]
  obtain s where bad:
    "bad_crash_execution_for_gap
      (operational_gap_of_implementation_gap I
        (implementation_gap_of_no_shared_commit_window W)) s"
    by blast
  from window bad show ?thesis by blast
qed

theorem prefix_crash_no_shared_commit_crash_admissible_implementation_has_concrete_bad_crash_execution:
  assumes impl: "prefix_crash_no_shared_commit_crash_admissible_implementation I"
  shows "\<exists>W s.
      prefix_crash_no_shared_commit_source_first_window I W
    \<and> implementation_crash_enabled_for_gap I
        (implementation_gap_of_no_shared_commit_window W)
    \<and> dwi_trace I (dwi_initial I)
        (implementation_gap_crash_labels
          (implementation_gap_of_no_shared_commit_window W)) s
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I
          (implementation_gap_of_no_shared_commit_window W))
        (dwi_state I s)"
proof -
  from impl obtain W where window:
      "prefix_crash_no_shared_commit_source_first_window I W"
      and crash:
        "implementation_crash_enabled_for_gap I
          (implementation_gap_of_no_shared_commit_window W)"
    by (auto simp: prefix_crash_no_shared_commit_crash_admissible_implementation_def)
  have no_shared:
    "implementation_admits_no_shared_commit_source_first_window I W"
    by (rule
        prefix_crash_no_shared_commit_source_first_window_imp_no_shared_commit_source_first_window
        [OF window])
  have gap:
    "implementation_admits_source_first_gap
      I (implementation_gap_of_no_shared_commit_window W)"
    by (rule
        implementation_admits_no_shared_commit_source_first_window_imp_implementation_admits_source_first_gap
        [OF no_shared])
  from implementation_admits_source_first_gap_with_crash_has_concrete_bad_crash_execution
        [OF gap crash]
  obtain s where trace:
      "dwi_trace I (dwi_initial I)
        (implementation_gap_crash_labels
          (implementation_gap_of_no_shared_commit_window W)) s"
      and bad:
        "bad_crash_execution_for_gap
          (operational_gap_of_implementation_gap I
            (implementation_gap_of_no_shared_commit_window W))
          (dwi_state I s)"
    by blast
  from window crash trace bad show ?thesis by blast
qed

definition implementation_has_source_first_window
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) implementation_source_first_gap_witness \<Rightarrow> bool"
where
  "implementation_has_source_first_window I W \<longleftrightarrow>
     (\<exists>s_pre s_src s_gap.
        dwi_trace I (dwi_initial I) (isfg_pre W) s_pre
      \<and> dwi_step I s_pre (DoSource (isfg_source_at W) (isfg_event W)) s_src
      \<and> dwi_trace I s_src (isfg_gap W) s_gap)"

definition non_atomic_source_effect_window
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) implementation_source_first_gap_witness \<Rightarrow> bool"
where
  "non_atomic_source_effect_window I W \<longleftrightarrow>
     exec_status (dwi_state I (dwi_initial I)) = Running
   \<and> key_of (isfg_event W) = isfg_key W
   \<and> effective_source_effect
        (exec_base (dwi_state I (dwi_initial I)))
        (isfg_event W) (isfg_key W)
   \<and> isfg_key W \<in> exec_scope (dwi_state I (dwi_initial I))
   \<and> isfg_source_at W < isfg_down_at W
   \<and> isfg_down_at W \<le> exec_finish (dwi_state I (dwi_initial I))
   \<and> isfg_source_at W \<le> isfg_crash_at W
   \<and> isfg_crash_at W \<le> exec_finish (dwi_state I (dwi_initial I))"

definition acknowledged_source_window
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) implementation_source_first_gap_witness \<Rightarrow> bool"
where
  "acknowledged_source_window I W \<longleftrightarrow>
     (isfg_source_at W, isfg_event W) \<in>
      set (exec_acked (dwi_state I (dwi_initial I))
        @ acked_hist_of_labels (implementation_gap_precrash_labels W))"

definition downstream_intent_without_completion
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) implementation_source_first_gap_witness \<Rightarrow> bool"
where
  "downstream_intent_without_completion I W \<longleftrightarrow>
     same_downstream_effect (isfg_event W) (isfg_down_event W) (isfg_key W)
   \<and> (isfg_down_at W, isfg_down_event W) \<in>
        set (enqueued_hist_of_labels (isfg_gap W))
   \<and> (isfg_down_at W, isfg_down_event W) \<in>
        pending_after_labels (implementation_gap_precrash_labels W)
          (exec_pending (dwi_state I (dwi_initial I)))"

definition no_later_source_overwrite_before_crash
  :: "('k, 'v) implementation_source_first_gap_witness \<Rightarrow> bool"
where
  "no_later_source_overwrite_before_crash W \<longleftrightarrow>
     no_visible_key_events (src_hist_of_labels (isfg_gap W))
       (isfg_crash_at W) (isfg_key W)"

definition no_visible_downstream_effect_at_crash
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) implementation_source_first_gap_witness \<Rightarrow> bool"
where
  "no_visible_downstream_effect_at_crash I W \<longleftrightarrow>
     no_visible_key_events
       (exec_down_hist (dwi_state I (dwi_initial I))
         @ down_hist_of_labels (isfg_pre W)
         @ down_hist_of_labels (isfg_gap W))
       (isfg_crash_at W) (isfg_key W)"

definition source_ack_after_commit
  :: "('k, 'v) implementation_source_first_gap_witness \<Rightarrow> bool"
where
  "source_ack_after_commit W \<longleftrightarrow>
     (isfg_source_at W, isfg_event W) \<in>
       set (acked_hist_of_labels (isfg_gap W))"

definition pending_downstream_intent_at_crash
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) implementation_source_first_gap_witness \<Rightarrow> bool"
where
  "pending_downstream_intent_at_crash I W \<longleftrightarrow>
     same_downstream_effect (isfg_event W) (isfg_down_event W) (isfg_key W)
   \<and> (isfg_down_at W, isfg_down_event W) \<in>
        set (enqueued_hist_of_labels (isfg_gap W))
   \<and> (isfg_down_at W, isfg_down_event W) \<in>
        pending_after_labels (implementation_gap_precrash_labels W)
          (exec_pending (dwi_state I (dwi_initial I)))"

lemma source_ack_after_commit_imp_acknowledged_source_window:
  assumes "source_ack_after_commit W"
  shows "acknowledged_source_window I W"
  using assms
  by (auto simp: source_ack_after_commit_def acknowledged_source_window_def
                 implementation_gap_precrash_labels_def)

lemma pending_downstream_intent_at_crash_imp_downstream_intent_without_completion:
  assumes "pending_downstream_intent_at_crash I W"
  shows "downstream_intent_without_completion I W"
  using assms
  by (simp add: pending_downstream_intent_at_crash_def
                downstream_intent_without_completion_def)

definition no_prior_downstream_effect_at_crash
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) implementation_source_first_gap_witness \<Rightarrow> bool"
where
  "no_prior_downstream_effect_at_crash I W \<longleftrightarrow>
     no_visible_key_events
       (exec_down_hist (dwi_state I (dwi_initial I))
         @ down_hist_of_labels (isfg_pre W))
       (isfg_crash_at W) (isfg_key W)"

definition source_ack_enqueue_downstream_completion_gap
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) implementation_source_first_gap_witness \<Rightarrow> bool"
where
  "source_ack_enqueue_downstream_completion_gap I W \<longleftrightarrow>
     isfg_gap W =
       [Ack (isfg_source_at W) (isfg_event W),
        EnqueueDownstream (isfg_down_at W) (isfg_down_event W)]
   \<and> (\<exists>s_pre s_src s_ack s_enq s_down.
        dwi_trace I (dwi_initial I) (isfg_pre W) s_pre
      \<and> dwi_step I s_pre
          (DoSource (isfg_source_at W) (isfg_event W)) s_src
      \<and> dwi_step I s_src
          (Ack (isfg_source_at W) (isfg_event W)) s_ack
      \<and> dwi_step I s_ack
          (EnqueueDownstream (isfg_down_at W) (isfg_down_event W)) s_enq
      \<and> dwi_step I s_enq
          (DoDownstream (isfg_down_at W) (isfg_down_event W)) s_down)"

definition semantic_prefix_crash_source_first_window
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) implementation_source_first_gap_witness \<Rightarrow> bool"
where
  "semantic_prefix_crash_source_first_window I W \<longleftrightarrow>
     dwi_refines_exec I
   \<and> source_ack_enqueue_downstream_completion_gap I W
   \<and> running_labels (isfg_pre W)
   \<and> non_atomic_source_effect_window I W
   \<and> same_downstream_effect (isfg_event W) (isfg_down_event W) (isfg_key W)
   \<and> isfg_crash_at W < isfg_down_at W
   \<and> no_prior_downstream_effect_at_crash I W"

definition semantic_prefix_crash_source_first_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "semantic_prefix_crash_source_first_implementation I \<longleftrightarrow>
     (\<exists>W. semantic_prefix_crash_source_first_window I W)"

definition semantic_prefix_crash_closed_source_first_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "semantic_prefix_crash_closed_source_first_implementation I \<longleftrightarrow>
     crash_closed_implementation I
   \<and> (\<exists>W. semantic_prefix_crash_source_first_window I W)"

lemma source_ack_enqueue_downstream_completion_gap_imp_implementation_has_source_first_window:
  assumes schedule: "source_ack_enqueue_downstream_completion_gap I W"
  shows "implementation_has_source_first_window I W"
proof -
  from schedule obtain s_pre s_src s_ack s_enq s_down where
      gap_eq:
        "isfg_gap W =
          [Ack (isfg_source_at W) (isfg_event W),
           EnqueueDownstream (isfg_down_at W) (isfg_down_event W)]"
      and pre: "dwi_trace I (dwi_initial I) (isfg_pre W) s_pre"
      and source:
        "dwi_step I s_pre
          (DoSource (isfg_source_at W) (isfg_event W)) s_src"
      and ack:
        "dwi_step I s_src
          (Ack (isfg_source_at W) (isfg_event W)) s_ack"
      and enqueue:
        "dwi_step I s_ack
          (EnqueueDownstream (isfg_down_at W) (isfg_down_event W)) s_enq"
    by (auto simp: source_ack_enqueue_downstream_completion_gap_def)
  have ack_trace:
    "dwi_trace I s_src [Ack (isfg_source_at W) (isfg_event W)] s_ack"
    by (rule dwi_trace.dwi_trace_step[OF ack dwi_trace.dwi_trace_refl])
  have enqueue_trace:
    "dwi_trace I s_ack
      [EnqueueDownstream (isfg_down_at W) (isfg_down_event W)] s_enq"
    by (rule dwi_trace.dwi_trace_step[OF enqueue dwi_trace.dwi_trace_refl])
  have gap_trace:
    "dwi_trace I s_src (isfg_gap W) s_enq"
    using dwi_trace_append[OF ack_trace enqueue_trace] gap_eq
    by simp
  from pre source gap_trace show ?thesis
    by (auto simp: implementation_has_source_first_window_def)
qed

definition adversarial_pending_intent_source_first_window
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) implementation_source_first_gap_witness \<Rightarrow> bool"
where
  "adversarial_pending_intent_source_first_window I W \<longleftrightarrow>
     dwi_refines_exec I
   \<and> implementation_has_source_first_window I W
   \<and> running_labels (implementation_gap_precrash_labels W)
   \<and> non_atomic_source_effect_window I W
   \<and> isfg_crash_at W < isfg_down_at W
   \<and> source_ack_after_commit W
   \<and> pending_downstream_intent_at_crash I W
   \<and> no_later_source_overwrite_before_crash W
   \<and> no_visible_downstream_effect_at_crash I W"

definition adversarial_pending_intent_source_first_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "adversarial_pending_intent_source_first_implementation I \<longleftrightarrow>
     (\<exists>W. adversarial_pending_intent_source_first_window I W)"

definition adversarial_pending_intent_crash_admissible_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "adversarial_pending_intent_crash_admissible_implementation I \<longleftrightarrow>
     (\<exists>W.
        adversarial_pending_intent_source_first_window I W
      \<and> implementation_crash_enabled_for_gap I W)"

definition non_atomic_no_shared_commit_source_first_window
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) implementation_source_first_gap_witness \<Rightarrow> bool"
where
  "non_atomic_no_shared_commit_source_first_window I W \<longleftrightarrow>
     dwi_refines_exec I
   \<and> implementation_has_source_first_window I W
   \<and> running_labels (implementation_gap_precrash_labels W)
   \<and> non_atomic_source_effect_window I W
   \<and> acknowledged_source_window I W
   \<and> downstream_intent_without_completion I W
   \<and> no_later_source_overwrite_before_crash W
   \<and> no_visible_downstream_effect_at_crash I W"

definition non_atomic_no_shared_commit_source_first_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "non_atomic_no_shared_commit_source_first_implementation I \<longleftrightarrow>
     (\<exists>W. non_atomic_no_shared_commit_source_first_window I W)"

definition non_atomic_no_shared_commit_crash_admissible_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "non_atomic_no_shared_commit_crash_admissible_implementation I \<longleftrightarrow>
     (\<exists>W.
        non_atomic_no_shared_commit_source_first_window I W
      \<and> implementation_crash_enabled_for_gap I W)"

lemma implementation_has_source_first_window_imp_precrash_trace:
  assumes window: "implementation_has_source_first_window I W"
  shows "\<exists>s.
    dwi_trace I (dwi_initial I) (implementation_gap_precrash_labels W) s"
proof -
  from window obtain s_pre s_src s_gap where
      pre: "dwi_trace I (dwi_initial I) (isfg_pre W) s_pre"
      and source:
        "dwi_step I s_pre (DoSource (isfg_source_at W) (isfg_event W)) s_src"
      and gap: "dwi_trace I s_src (isfg_gap W) s_gap"
    by (auto simp: implementation_has_source_first_window_def)
  have source_trace:
    "dwi_trace I s_pre [DoSource (isfg_source_at W) (isfg_event W)] s_src"
    by (rule dwi_trace.dwi_trace_step[OF source dwi_trace.dwi_trace_refl])
  have pre_source:
    "dwi_trace I (dwi_initial I)
      (isfg_pre W @ [DoSource (isfg_source_at W) (isfg_event W)]) s_src"
    by (rule dwi_trace_append[OF pre source_trace])
  have full:
    "dwi_trace I (dwi_initial I)
      (isfg_pre W @ [DoSource (isfg_source_at W) (isfg_event W)]
        @ isfg_gap W) s_gap"
    using dwi_trace_append[OF pre_source gap]
    by simp
  thus ?thesis
    by (auto simp: implementation_gap_precrash_labels_def)
qed

lemma non_atomic_no_shared_commit_source_first_window_imp_implementation_admits_source_first_gap:
  assumes window: "non_atomic_no_shared_commit_source_first_window I W"
  shows "implementation_admits_source_first_gap I W"
proof -
  from window have trace:
    "\<exists>s. dwi_trace I (dwi_initial I) (implementation_gap_precrash_labels W) s"
    by (auto simp: non_atomic_no_shared_commit_source_first_window_def
        dest: implementation_has_source_first_window_imp_precrash_trace)
  from window show ?thesis
    using trace
    by (auto simp: non_atomic_no_shared_commit_source_first_window_def
                   implementation_admits_source_first_gap_def
                   non_atomic_source_effect_window_def
                   acknowledged_source_window_def
                   downstream_intent_without_completion_def
                   no_later_source_overwrite_before_crash_def
                   no_visible_downstream_effect_at_crash_def)
qed

corollary non_atomic_no_shared_commit_source_first_window_imp_source_first_gap_admissible:
  assumes "non_atomic_no_shared_commit_source_first_window I W"
  shows "source_first_gap_admissible_implementation I"
  using
    non_atomic_no_shared_commit_source_first_window_imp_implementation_admits_source_first_gap
      [OF assms]
  by (auto simp: source_first_gap_admissible_implementation_def)

corollary non_atomic_no_shared_commit_source_first_implementation_imp_source_first_gap_admissible:
  assumes "non_atomic_no_shared_commit_source_first_implementation I"
  shows "source_first_gap_admissible_implementation I"
  using assms
    non_atomic_no_shared_commit_source_first_window_imp_source_first_gap_admissible
  by (auto simp: non_atomic_no_shared_commit_source_first_implementation_def)

theorem non_atomic_no_shared_commit_source_first_implementation_has_abstract_bad_crash_execution:
  assumes impl: "non_atomic_no_shared_commit_source_first_implementation I"
  shows "\<exists>W s.
      non_atomic_no_shared_commit_source_first_window I W
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I W) s"
proof -
  from impl obtain W where window:
    "non_atomic_no_shared_commit_source_first_window I W"
    by (auto simp: non_atomic_no_shared_commit_source_first_implementation_def)
  hence gap: "implementation_admits_source_first_gap I W"
    by (rule
        non_atomic_no_shared_commit_source_first_window_imp_implementation_admits_source_first_gap)
  from implementation_admits_source_first_gap_has_abstract_bad_crash_execution
        [OF gap]
  obtain s where bad:
    "bad_crash_execution_for_gap (operational_gap_of_implementation_gap I W) s"
    by blast
  from window bad show ?thesis by blast
qed

theorem non_atomic_no_shared_commit_crash_admissible_implementation_has_concrete_bad_crash_execution:
  assumes impl: "non_atomic_no_shared_commit_crash_admissible_implementation I"
  shows "\<exists>W s.
      non_atomic_no_shared_commit_source_first_window I W
    \<and> implementation_crash_enabled_for_gap I W
    \<and> dwi_trace I (dwi_initial I) (implementation_gap_crash_labels W) s
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I W) (dwi_state I s)"
proof -
  from impl obtain W where window:
      "non_atomic_no_shared_commit_source_first_window I W"
      and crash: "implementation_crash_enabled_for_gap I W"
    by (auto simp: non_atomic_no_shared_commit_crash_admissible_implementation_def)
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
  from window crash trace bad show ?thesis by blast
qed

lemma adversarial_pending_intent_source_first_window_imp_no_shared_commit_source_first_window:
  assumes window: "adversarial_pending_intent_source_first_window I W"
  shows "non_atomic_no_shared_commit_source_first_window I W"
  using window
    source_ack_after_commit_imp_acknowledged_source_window
    pending_downstream_intent_at_crash_imp_downstream_intent_without_completion
  by (auto simp: adversarial_pending_intent_source_first_window_def
                 non_atomic_no_shared_commit_source_first_window_def)

theorem adversarial_pending_intent_source_first_window_has_abstract_bad_crash_execution:
  assumes window: "adversarial_pending_intent_source_first_window I W"
  shows "\<exists>s. bad_crash_execution_for_gap
    (operational_gap_of_implementation_gap I W) s"
proof -
  have gap: "implementation_admits_source_first_gap I W"
    by (rule
        non_atomic_no_shared_commit_source_first_window_imp_implementation_admits_source_first_gap
        [OF adversarial_pending_intent_source_first_window_imp_no_shared_commit_source_first_window
          [OF window]])
  show ?thesis
    by (rule implementation_admits_source_first_gap_has_abstract_bad_crash_execution
        [OF gap])
qed

theorem adversarial_pending_intent_source_first_implementation_has_abstract_bad_crash_execution:
  assumes impl: "adversarial_pending_intent_source_first_implementation I"
  shows "\<exists>W s.
      adversarial_pending_intent_source_first_window I W
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I W) s"
proof -
  from impl obtain W where window:
    "adversarial_pending_intent_source_first_window I W"
    by (auto simp: adversarial_pending_intent_source_first_implementation_def)
  from adversarial_pending_intent_source_first_window_has_abstract_bad_crash_execution
        [OF window]
  obtain s where bad:
    "bad_crash_execution_for_gap (operational_gap_of_implementation_gap I W) s"
    by blast
  from window bad show ?thesis by blast
qed

theorem adversarial_pending_intent_crash_admissible_implementation_has_concrete_bad_crash_execution:
  assumes impl: "adversarial_pending_intent_crash_admissible_implementation I"
  shows "\<exists>W s.
      adversarial_pending_intent_source_first_window I W
    \<and> implementation_crash_enabled_for_gap I W
    \<and> dwi_trace I (dwi_initial I) (implementation_gap_crash_labels W) s
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I W) (dwi_state I s)"
proof -
  from impl obtain W where window:
      "adversarial_pending_intent_source_first_window I W"
      and crash: "implementation_crash_enabled_for_gap I W"
    by (auto simp: adversarial_pending_intent_crash_admissible_implementation_def)
  have gap: "implementation_admits_source_first_gap I W"
    by (rule
        non_atomic_no_shared_commit_source_first_window_imp_implementation_admits_source_first_gap
        [OF adversarial_pending_intent_source_first_window_imp_no_shared_commit_source_first_window
          [OF window]])
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

lemma semantic_prefix_crash_source_first_window_imp_adversarial_pending_intent:
  assumes window: "semantic_prefix_crash_source_first_window I W"
  shows "adversarial_pending_intent_source_first_window I W"
proof -
  from window have schedule:
      "source_ack_enqueue_downstream_completion_gap I W"
      and refines: "dwi_refines_exec I"
      and pre_running: "running_labels (isfg_pre W)"
      and non_atomic: "non_atomic_source_effect_window I W"
      and same:
        "same_downstream_effect (isfg_event W) (isfg_down_event W) (isfg_key W)"
      and crash_before_down: "isfg_crash_at W < isfg_down_at W"
      and no_prior: "no_prior_downstream_effect_at_crash I W"
    by (auto simp: semantic_prefix_crash_source_first_window_def)
  from schedule have gap_eq:
    "isfg_gap W =
      [Ack (isfg_source_at W) (isfg_event W),
       EnqueueDownstream (isfg_down_at W) (isfg_down_event W)]"
    by (simp add: source_ack_enqueue_downstream_completion_gap_def)
  have has_window: "implementation_has_source_first_window I W"
    by (rule
        source_ack_enqueue_downstream_completion_gap_imp_implementation_has_source_first_window
        [OF schedule])
  have running: "running_labels (implementation_gap_precrash_labels W)"
    using pre_running gap_eq
    by (simp add: implementation_gap_precrash_labels_def
                  running_labels_def running_label_def)
  have acked: "source_ack_after_commit W"
    using gap_eq by (simp add: source_ack_after_commit_def)
  have pending: "pending_downstream_intent_at_crash I W"
    using gap_eq same
    by (simp add: pending_downstream_intent_at_crash_def
                  implementation_gap_precrash_labels_def)
  have no_later: "no_later_source_overwrite_before_crash W"
    using gap_eq
    by (simp add: no_later_source_overwrite_before_crash_def
                  no_visible_key_events_def)
  have no_down: "no_visible_downstream_effect_at_crash I W"
    using no_prior gap_eq
    by (simp add: no_prior_downstream_effect_at_crash_def
                  no_visible_downstream_effect_at_crash_def)
  from refines has_window running non_atomic crash_before_down acked pending
    no_later no_down show ?thesis
    by (simp add: adversarial_pending_intent_source_first_window_def)
qed

theorem semantic_prefix_crash_source_first_window_has_abstract_bad_crash_execution:
  assumes window: "semantic_prefix_crash_source_first_window I W"
  shows "\<exists>s. bad_crash_execution_for_gap
    (operational_gap_of_implementation_gap I W) s"
  by (rule adversarial_pending_intent_source_first_window_has_abstract_bad_crash_execution
      [OF semantic_prefix_crash_source_first_window_imp_adversarial_pending_intent
        [OF window]])

theorem semantic_prefix_crash_source_first_implementation_has_abstract_bad_crash_execution:
  assumes impl: "semantic_prefix_crash_source_first_implementation I"
  shows "\<exists>W s.
      semantic_prefix_crash_source_first_window I W
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I W) s"
proof -
  from impl obtain W where window:
    "semantic_prefix_crash_source_first_window I W"
    by (auto simp: semantic_prefix_crash_source_first_implementation_def)
  from semantic_prefix_crash_source_first_window_has_abstract_bad_crash_execution
        [OF window]
  obtain s where bad:
    "bad_crash_execution_for_gap (operational_gap_of_implementation_gap I W) s"
    by blast
  from window bad show ?thesis by blast
qed

theorem semantic_prefix_crash_source_first_window_crash_closed_has_concrete_bad_crash_execution:
  assumes window: "semantic_prefix_crash_source_first_window I W"
      and closed: "crash_closed_implementation I"
  shows "\<exists>s.
      dwi_trace I (dwi_initial I) (implementation_gap_crash_labels W) s
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I W) (dwi_state I s)"
proof -
  have pending_window: "adversarial_pending_intent_source_first_window I W"
    by (rule
        semantic_prefix_crash_source_first_window_imp_adversarial_pending_intent
        [OF window])
  have no_shared: "non_atomic_no_shared_commit_source_first_window I W"
    by (rule
        adversarial_pending_intent_source_first_window_imp_no_shared_commit_source_first_window
        [OF pending_window])
  have gap: "implementation_admits_source_first_gap I W"
    by (rule
        non_atomic_no_shared_commit_source_first_window_imp_implementation_admits_source_first_gap
        [OF no_shared])
  have crash_enabled: "implementation_crash_enabled_for_gap I W"
    by (rule crash_closed_imp_implementation_crash_enabled_for_gap
        [OF closed gap])
  show ?thesis
    by (rule
        implementation_admits_source_first_gap_with_crash_has_concrete_bad_crash_execution
        [OF gap crash_enabled])
qed

theorem semantic_prefix_crash_closed_source_first_implementation_has_concrete_bad_crash_execution:
  assumes impl: "semantic_prefix_crash_closed_source_first_implementation I"
  shows "\<exists>W s.
      semantic_prefix_crash_source_first_window I W
    \<and> dwi_trace I (dwi_initial I) (implementation_gap_crash_labels W) s
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I W) (dwi_state I s)"
proof -
  from impl obtain W where closed: "crash_closed_implementation I"
      and window: "semantic_prefix_crash_source_first_window I W"
    by (auto simp: semantic_prefix_crash_closed_source_first_implementation_def)
  from semantic_prefix_crash_source_first_window_crash_closed_has_concrete_bad_crash_execution
        [OF window closed]
  obtain s where trace:
      "dwi_trace I (dwi_initial I) (implementation_gap_crash_labels W) s"
      and bad:
        "bad_crash_execution_for_gap
          (operational_gap_of_implementation_gap I W) (dwi_state I s)"
    by blast
  from window trace bad show ?thesis by blast
qed

lemma prefix_crash_no_shared_commit_window_imp_semantic_prefix_crash_source_first_window:
  assumes window: "prefix_crash_no_shared_commit_source_first_window I W"
  shows "semantic_prefix_crash_source_first_window
    I (implementation_gap_of_no_shared_commit_window W)"
proof -
  from window have crash_lt_down: "sfnc_crash_at W < sfnc_down_at W"
      and down_le_fin:
        "sfnc_down_at W \<le> exec_finish (dwi_state I (dwi_initial I))"
    by (auto simp: prefix_crash_no_shared_commit_source_first_window_def)
  have crash_le_down: "sfnc_crash_at W \<le> sfnc_down_at W"
    using crash_lt_down by (rule order_less_imp_le)
  have crash_le_fin:
    "sfnc_crash_at W \<le> exec_finish (dwi_state I (dwi_initial I))"
    by (rule order_trans[OF crash_le_down down_le_fin])
  from window show ?thesis
    using crash_le_fin
    by (auto simp:
        semantic_prefix_crash_source_first_window_def
        prefix_crash_no_shared_commit_source_first_window_def
        source_ack_enqueue_downstream_completion_gap_def
        source_ack_enqueue_downstream_completion_schedule_def
        implementation_gap_of_no_shared_commit_window_def
        source_first_no_shared_commit_gap_labels_def
        non_atomic_source_effect_window_def
        no_prior_downstream_effect_at_crash_def
        order_less_imp_le)
qed

theorem separated_completion_prefix_selects_semantic_bad_crash_window:
  assumes window: "prefix_crash_no_shared_commit_source_first_window I W"
  shows "\<exists>G s.
      G = implementation_gap_of_no_shared_commit_window W
    \<and> semantic_prefix_crash_source_first_window I G
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I G) s"
proof -
  let ?G = "implementation_gap_of_no_shared_commit_window W"
  have semantic: "semantic_prefix_crash_source_first_window I ?G"
    by (rule
        prefix_crash_no_shared_commit_window_imp_semantic_prefix_crash_source_first_window
        [OF window])
  from semantic_prefix_crash_source_first_window_has_abstract_bad_crash_execution
        [OF semantic]
  obtain s where bad:
    "bad_crash_execution_for_gap (operational_gap_of_implementation_gap I ?G) s"
    by blast
  from semantic bad show ?thesis by blast
qed

theorem prefix_crash_no_shared_commit_source_first_implementation_selects_semantic_bad_prefix:
  assumes impl: "prefix_crash_no_shared_commit_source_first_implementation I"
  shows "\<exists>G s.
      semantic_prefix_crash_source_first_window I G
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I G) s"
proof -
  from impl obtain W where window:
    "prefix_crash_no_shared_commit_source_first_window I W"
    by (auto simp: prefix_crash_no_shared_commit_source_first_implementation_def)
  from separated_completion_prefix_selects_semantic_bad_crash_window[OF window]
  show ?thesis by blast
qed

theorem separated_completion_prefix_crash_closed_selects_concrete_bad_prefix:
  assumes window: "prefix_crash_no_shared_commit_source_first_window I W"
      and closed: "crash_closed_implementation I"
  shows "\<exists>G s.
      G = implementation_gap_of_no_shared_commit_window W
    \<and> semantic_prefix_crash_source_first_window I G
    \<and> dwi_trace I (dwi_initial I) (implementation_gap_crash_labels G) s
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I G) (dwi_state I s)"
proof -
  let ?G = "implementation_gap_of_no_shared_commit_window W"
  have semantic: "semantic_prefix_crash_source_first_window I ?G"
    by (rule
        prefix_crash_no_shared_commit_window_imp_semantic_prefix_crash_source_first_window
        [OF window])
  from semantic_prefix_crash_source_first_window_crash_closed_has_concrete_bad_crash_execution
        [OF semantic closed]
  obtain s where trace:
      "dwi_trace I (dwi_initial I) (implementation_gap_crash_labels ?G) s"
      and bad:
        "bad_crash_execution_for_gap
          (operational_gap_of_implementation_gap I ?G) (dwi_state I s)"
    by blast
  from semantic trace bad show ?thesis by blast
qed

definition no_shared_commit_window_of_completion
  :: "('k, 'v) source_first_separated_completion \<Rightarrow>
      ('k, 'v) source_first_no_shared_commit_window"
where
  "no_shared_commit_window_of_completion C =
     \<lparr> sfnc_pre = sfsc_pre C,
       sfnc_key = sfsc_key C,
       sfnc_source_at = sfsc_source_at C,
       sfnc_event = sfsc_event C,
       sfnc_down_at = sfsc_down_at C,
       sfnc_down_event = sfsc_down_event C,
       sfnc_crash_at = sfsc_source_at C \<rparr>"

definition source_first_separated_completion_run
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) source_first_separated_completion \<Rightarrow> bool"
where
  "source_first_separated_completion_run I C \<longleftrightarrow>
     dwi_refines_exec I
   \<and> source_ack_enqueue_downstream_completion_schedule I
        (no_shared_commit_window_of_completion C)
   \<and> running_labels (sfsc_pre C)
   \<and> exec_status (dwi_state I (dwi_initial I)) = Running
   \<and> key_of (sfsc_event C) = sfsc_key C
   \<and> effective_source_effect
        (exec_base (dwi_state I (dwi_initial I)))
        (sfsc_event C) (sfsc_key C)
   \<and> same_downstream_effect (sfsc_event C) (sfsc_down_event C) (sfsc_key C)
   \<and> sfsc_key C \<in> exec_scope (dwi_state I (dwi_initial I))
   \<and> sfsc_source_at C < sfsc_down_at C
   \<and> sfsc_down_at C \<le> exec_finish (dwi_state I (dwi_initial I))
   \<and> no_visible_key_events
        (exec_down_hist (dwi_state I (dwi_initial I))
          @ down_hist_of_labels (sfsc_pre C))
        (sfsc_source_at C) (sfsc_key C)"

definition source_first_separated_completion_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "source_first_separated_completion_implementation I \<longleftrightarrow>
     (\<exists>C. source_first_separated_completion_run I C)"

definition source_first_separated_completion_crash_closed_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "source_first_separated_completion_crash_closed_implementation I \<longleftrightarrow>
     crash_closed_implementation I
   \<and> source_first_separated_completion_implementation I"

lemma source_first_separated_completion_run_imp_prefix_crash_no_shared_commit_window:
  assumes run: "source_first_separated_completion_run I C"
  shows "prefix_crash_no_shared_commit_source_first_window I
    (no_shared_commit_window_of_completion C)"
  using run
  by (auto simp: source_first_separated_completion_run_def
                 prefix_crash_no_shared_commit_source_first_window_def
                 no_shared_commit_window_of_completion_def)

theorem source_first_separated_completion_run_selects_bad_prefix:
  assumes run: "source_first_separated_completion_run I C"
  shows "\<exists>W G s.
      W = no_shared_commit_window_of_completion C
    \<and> G = implementation_gap_of_no_shared_commit_window W
    \<and> semantic_prefix_crash_source_first_window I G
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I G) s"
proof -
  let ?W = "no_shared_commit_window_of_completion C"
  have window: "prefix_crash_no_shared_commit_source_first_window I ?W"
    by (rule
        source_first_separated_completion_run_imp_prefix_crash_no_shared_commit_window
        [OF run])
  from separated_completion_prefix_selects_semantic_bad_crash_window[OF window]
  show ?thesis by blast
qed

theorem source_first_separated_completion_implementation_has_abstract_bad_crash_execution:
  assumes impl: "source_first_separated_completion_implementation I"
  shows "\<exists>C G s.
      source_first_separated_completion_run I C
    \<and> semantic_prefix_crash_source_first_window I G
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I G) s"
proof -
  from impl obtain C where run: "source_first_separated_completion_run I C"
    by (auto simp: source_first_separated_completion_implementation_def)
  from source_first_separated_completion_run_selects_bad_prefix[OF run]
  obtain G s where semantic: "semantic_prefix_crash_source_first_window I G"
      and bad:
        "bad_crash_execution_for_gap
          (operational_gap_of_implementation_gap I G) s"
    by blast
  from run semantic bad show ?thesis by blast
qed

theorem source_first_separated_completion_run_crash_closed_selects_concrete_bad_prefix:
  assumes run: "source_first_separated_completion_run I C"
      and closed: "crash_closed_implementation I"
  shows "\<exists>W G s.
      W = no_shared_commit_window_of_completion C
    \<and> G = implementation_gap_of_no_shared_commit_window W
    \<and> semantic_prefix_crash_source_first_window I G
    \<and> dwi_trace I (dwi_initial I) (implementation_gap_crash_labels G) s
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I G) (dwi_state I s)"
proof -
  let ?W = "no_shared_commit_window_of_completion C"
  have window: "prefix_crash_no_shared_commit_source_first_window I ?W"
    by (rule
        source_first_separated_completion_run_imp_prefix_crash_no_shared_commit_window
        [OF run])
  from separated_completion_prefix_crash_closed_selects_concrete_bad_prefix
        [OF window closed]
  show ?thesis by blast
qed

theorem source_first_separated_completion_crash_closed_implementation_has_concrete_bad_crash_execution:
  assumes impl: "source_first_separated_completion_crash_closed_implementation I"
  shows "\<exists>C G s.
      source_first_separated_completion_run I C
    \<and> semantic_prefix_crash_source_first_window I G
    \<and> dwi_trace I (dwi_initial I) (implementation_gap_crash_labels G) s
    \<and> bad_crash_execution_for_gap
        (operational_gap_of_implementation_gap I G) (dwi_state I s)"
proof -
  from impl obtain C where
      closed: "crash_closed_implementation I"
      and run: "source_first_separated_completion_run I C"
    by (auto simp: source_first_separated_completion_crash_closed_implementation_def
                   source_first_separated_completion_implementation_def)
  from source_first_separated_completion_run_crash_closed_selects_concrete_bad_prefix
        [OF run closed]
  obtain G s where semantic: "semantic_prefix_crash_source_first_window I G"
      and trace:
        "dwi_trace I (dwi_initial I) (implementation_gap_crash_labels G) s"
      and bad:
        "bad_crash_execution_for_gap
          (operational_gap_of_implementation_gap I G) (dwi_state I s)"
    by blast
  from run semantic trace bad show ?thesis by blast
qed

subsection \<open>Side-parametric separated dual-write completions\<close>

definition separated_completion_bad_precrash_labels
  :: "dual_write_effect_side \<Rightarrow>
      ('k, 'v) separated_dual_write_completion \<Rightarrow>
      ('k, 'v) dw_exec_label list"
where
  "separated_completion_bad_precrash_labels side C =
     (case side of
        Source_Effect \<Rightarrow>
          sdwc_pre C @ [DoSource (sdwc_source_at C) (sdwc_event C)]
      | Downstream_Effect \<Rightarrow>
          sdwc_pre C
          @ [EnqueueDownstream (sdwc_down_at C) (sdwc_down_event C),
             DoDownstream (sdwc_down_at C) (sdwc_down_event C)])"

definition separated_completion_crash_frontier
  :: "dual_write_effect_side \<Rightarrow>
      ('k, 'v) separated_dual_write_completion \<Rightarrow> frontier"
where
  "separated_completion_crash_frontier side C =
     (case side of
        Source_Effect \<Rightarrow> sdwc_source_at C
      | Downstream_Effect \<Rightarrow> sdwc_down_at C)"

definition separated_completion_bad_crash_labels
  :: "dual_write_effect_side \<Rightarrow>
      ('k, 'v) separated_dual_write_completion \<Rightarrow>
      ('k, 'v) dw_exec_label list"
where
  "separated_completion_bad_crash_labels side C =
     separated_completion_bad_precrash_labels side C
     @ [Crash (separated_completion_crash_frontier side C)]"

definition source_first_separated_dual_write_schedule
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) separated_dual_write_completion \<Rightarrow> bool"
where
  "source_first_separated_dual_write_schedule I C \<longleftrightarrow>
     (\<exists>s_pre s_src s_ack s_enq s_down.
        dwi_trace I (dwi_initial I) (sdwc_pre C) s_pre
      \<and> dwi_step I s_pre
          (DoSource (sdwc_source_at C) (sdwc_event C)) s_src
      \<and> dwi_step I s_src
          (Ack (sdwc_source_at C) (sdwc_event C)) s_ack
      \<and> dwi_step I s_ack
          (EnqueueDownstream (sdwc_down_at C) (sdwc_down_event C)) s_enq
      \<and> dwi_step I s_enq
          (DoDownstream (sdwc_down_at C) (sdwc_down_event C)) s_down)"

definition downstream_first_separated_dual_write_schedule
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) separated_dual_write_completion \<Rightarrow> bool"
where
  "downstream_first_separated_dual_write_schedule I C \<longleftrightarrow>
     (\<exists>s_pre s_enq s_down s_src s_ack.
        dwi_trace I (dwi_initial I) (sdwc_pre C) s_pre
      \<and> dwi_step I s_pre
          (EnqueueDownstream (sdwc_down_at C) (sdwc_down_event C)) s_enq
      \<and> dwi_step I s_enq
          (DoDownstream (sdwc_down_at C) (sdwc_down_event C)) s_down
      \<and> dwi_step I s_down
          (DoSource (sdwc_source_at C) (sdwc_event C)) s_src
      \<and> dwi_step I s_src
          (Ack (sdwc_source_at C) (sdwc_event C)) s_ack)"

definition source_first_separable_completion
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) separated_dual_write_completion \<Rightarrow> bool"
where
  "source_first_separable_completion I C \<longleftrightarrow>
     dwi_refines_exec I
   \<and> source_first_separated_dual_write_schedule I C
   \<and> running_labels (sdwc_pre C)
   \<and> exec_status (dwi_state I (dwi_initial I)) = Running
   \<and> key_of (sdwc_event C) = sdwc_key C
   \<and> effective_source_effect
        (exec_base (dwi_state I (dwi_initial I)))
        (sdwc_event C) (sdwc_key C)
   \<and> same_downstream_effect (sdwc_event C) (sdwc_down_event C) (sdwc_key C)
   \<and> sdwc_key C \<in> exec_scope (dwi_state I (dwi_initial I))
   \<and> sdwc_source_at C < sdwc_down_at C
   \<and> sdwc_source_at C \<le> exec_finish (dwi_state I (dwi_initial I))
   \<and> sdwc_down_at C \<le> exec_finish (dwi_state I (dwi_initial I))
   \<and> no_visible_key_events
        (exec_down_hist (dwi_state I (dwi_initial I))
          @ down_hist_of_labels (sdwc_pre C))
        (sdwc_source_at C) (sdwc_key C)"

definition downstream_first_separable_completion
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) separated_dual_write_completion \<Rightarrow> bool"
where
  "downstream_first_separable_completion I C \<longleftrightarrow>
     dwi_refines_exec I
   \<and> downstream_first_separated_dual_write_schedule I C
   \<and> running_labels (sdwc_pre C)
   \<and> exec_status (dwi_state I (dwi_initial I)) = Running
   \<and> key_of (sdwc_event C) = sdwc_key C
   \<and> effective_source_effect
        (exec_base (dwi_state I (dwi_initial I)))
        (sdwc_event C) (sdwc_key C)
   \<and> same_downstream_effect (sdwc_event C) (sdwc_down_event C) (sdwc_key C)
   \<and> sdwc_key C \<in> exec_scope (dwi_state I (dwi_initial I))
   \<and> sdwc_down_at C < sdwc_source_at C
   \<and> sdwc_source_at C \<le> exec_finish (dwi_state I (dwi_initial I))
   \<and> sdwc_down_at C \<le> exec_finish (dwi_state I (dwi_initial I))
   \<and> no_visible_key_events
        (exec_src_hist (dwi_state I (dwi_initial I))
          @ src_hist_of_labels (sdwc_pre C))
        (sdwc_down_at C) (sdwc_key C)"

definition separated_completion_first_side
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) separated_dual_write_completion \<Rightarrow>
      dual_write_effect_side \<Rightarrow> bool"
where
  "separated_completion_first_side I C side \<longleftrightarrow>
     (case side of
        Source_Effect \<Rightarrow> source_first_separable_completion I C
      | Downstream_Effect \<Rightarrow> downstream_first_separable_completion I C)"

definition separable_non_atomic_dual_write_completion
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) separated_dual_write_completion \<Rightarrow> bool"
where
  "separable_non_atomic_dual_write_completion I C \<longleftrightarrow>
     (\<exists>side. separated_completion_first_side I C side)"

definition separable_non_atomic_dual_write_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "separable_non_atomic_dual_write_implementation I \<longleftrightarrow>
     (\<exists>C. separable_non_atomic_dual_write_completion I C)"

definition separated_completion_abstract_bad_crash_execution
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) separated_dual_write_completion \<Rightarrow>
      dual_write_effect_side \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  "separated_completion_abstract_bad_crash_execution I C side s \<longleftrightarrow>
     dw_exec_trace (dwi_state I (dwi_initial I))
       (separated_completion_bad_crash_labels side C) s
   \<and> observable_mismatch s
        (separated_completion_crash_frontier side C) (sdwc_key C)
   \<and> diverges
        (proto_of_exec_at s (separated_completion_crash_frontier side C))
        (separated_completion_crash_frontier side C)"

definition separated_completion_concrete_bad_crash_execution
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) separated_dual_write_completion \<Rightarrow>
      dual_write_effect_side \<Rightarrow> 's \<Rightarrow> bool"
where
  "separated_completion_concrete_bad_crash_execution I C side s \<longleftrightarrow>
     dwi_trace I (dwi_initial I)
       (separated_completion_bad_crash_labels side C) s
   \<and> observable_mismatch (dwi_state I s)
        (separated_completion_crash_frontier side C) (sdwc_key C)
   \<and> diverges
        (proto_of_exec_at (dwi_state I s)
          (separated_completion_crash_frontier side C))
        (separated_completion_crash_frontier side C)"

definition admissible_separated_completion_abstract_bad_crash_execution
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) separated_dual_write_completion \<Rightarrow>
      dual_write_effect_side \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  "admissible_separated_completion_abstract_bad_crash_execution I C side s
   \<longleftrightarrow>
     separated_completion_abstract_bad_crash_execution I C side s
   \<and> admissible_dw_exec_trace (dwi_state I (dwi_initial I))
        (separated_completion_bad_crash_labels side C) s"

definition admissible_separable_non_atomic_dual_write_completion
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) separated_dual_write_completion \<Rightarrow> bool"
where
  "admissible_separable_non_atomic_dual_write_completion I C \<longleftrightarrow>
     separable_non_atomic_dual_write_completion I C
   \<and> (\<forall>side. separated_completion_first_side I C side
        \<longrightarrow> (\<exists>s. admissible_dw_exec_trace
              (dwi_state I (dwi_initial I))
              (separated_completion_bad_crash_labels side C) s))"

definition admissible_separable_non_atomic_dual_write_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "admissible_separable_non_atomic_dual_write_implementation I \<longleftrightarrow>
     (\<exists>C. admissible_separable_non_atomic_dual_write_completion I C)"

definition admissible_separable_non_atomic_crash_closed_dual_write_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "admissible_separable_non_atomic_crash_closed_dual_write_implementation I
   \<longleftrightarrow>
     crash_closed_implementation I
   \<and> admissible_separable_non_atomic_dual_write_implementation I"

lemma source_first_separable_completion_source_before_downstream:
  assumes "source_first_separable_completion I C"
  shows "sdwc_source_at C < sdwc_down_at C"
  using assms by (simp add: source_first_separable_completion_def)

lemma downstream_first_separable_completion_downstream_before_source:
  assumes "downstream_first_separable_completion I C"
  shows "sdwc_down_at C < sdwc_source_at C"
  using assms by (simp add: downstream_first_separable_completion_def)

lemma separated_completion_first_side_coordinate_sanity:
  assumes "separated_completion_first_side I C side"
  shows
    "(case side of
       Source_Effect \<Rightarrow> sdwc_source_at C < sdwc_down_at C
     | Downstream_Effect \<Rightarrow> sdwc_down_at C < sdwc_source_at C)"
  using assms
  by (cases side)
     (simp_all add: separated_completion_first_side_def
                    source_first_separable_completion_source_before_downstream
                    downstream_first_separable_completion_downstream_before_source)

lemma source_first_separated_dual_write_schedule_imp_prefix_trace:
  assumes schedule: "source_first_separated_dual_write_schedule I C"
  shows "\<exists>s.
    dwi_trace I (dwi_initial I)
      (separated_completion_bad_precrash_labels Source_Effect C) s"
proof -
  from schedule obtain s_pre s_src where
      pre: "dwi_trace I (dwi_initial I) (sdwc_pre C) s_pre"
      and source:
        "dwi_step I s_pre
          (DoSource (sdwc_source_at C) (sdwc_event C)) s_src"
    by (auto simp: source_first_separated_dual_write_schedule_def)
  have source_trace:
    "dwi_trace I s_pre
      [DoSource (sdwc_source_at C) (sdwc_event C)] s_src"
    by (rule dwi_trace.dwi_trace_step[OF source dwi_trace.dwi_trace_refl])
  have full:
    "dwi_trace I (dwi_initial I)
      (sdwc_pre C @ [DoSource (sdwc_source_at C) (sdwc_event C)]) s_src"
    by (rule dwi_trace_append[OF pre source_trace])
  thus ?thesis
    by (auto simp: separated_completion_bad_precrash_labels_def)
qed

lemma downstream_first_separated_dual_write_schedule_imp_prefix_trace:
  assumes schedule: "downstream_first_separated_dual_write_schedule I C"
  shows "\<exists>s.
    dwi_trace I (dwi_initial I)
      (separated_completion_bad_precrash_labels Downstream_Effect C) s"
proof -
  from schedule obtain s_pre s_enq s_down where
      pre: "dwi_trace I (dwi_initial I) (sdwc_pre C) s_pre"
      and enqueue:
        "dwi_step I s_pre
          (EnqueueDownstream (sdwc_down_at C) (sdwc_down_event C)) s_enq"
      and downstream:
        "dwi_step I s_enq
          (DoDownstream (sdwc_down_at C) (sdwc_down_event C)) s_down"
    by (auto simp: downstream_first_separated_dual_write_schedule_def)
  have enqueue_trace:
    "dwi_trace I s_pre
      [EnqueueDownstream (sdwc_down_at C) (sdwc_down_event C)] s_enq"
    by (rule dwi_trace.dwi_trace_step[OF enqueue dwi_trace.dwi_trace_refl])
  have downstream_trace:
    "dwi_trace I s_enq
      [DoDownstream (sdwc_down_at C) (sdwc_down_event C)] s_down"
    by (rule dwi_trace.dwi_trace_step[OF downstream dwi_trace.dwi_trace_refl])
  have first_effect_trace:
    "dwi_trace I s_pre
      [EnqueueDownstream (sdwc_down_at C) (sdwc_down_event C),
       DoDownstream (sdwc_down_at C) (sdwc_down_event C)] s_down"
    using dwi_trace_append[OF enqueue_trace downstream_trace] by simp
  have full:
    "dwi_trace I (dwi_initial I)
      (sdwc_pre C
       @ [EnqueueDownstream (sdwc_down_at C) (sdwc_down_event C),
          DoDownstream (sdwc_down_at C) (sdwc_down_event C)]) s_down"
    by (rule dwi_trace_append[OF pre first_effect_trace])
  thus ?thesis
    by (auto simp: separated_completion_bad_precrash_labels_def)
qed

theorem source_first_separable_completion_has_abstract_bad_crash_execution:
  assumes first: "source_first_separable_completion I C"
  shows "\<exists>s.
    separated_completion_abstract_bad_crash_execution I C Source_Effect s"
proof -
  from first have refines: "dwi_refines_exec I"
      and schedule: "source_first_separated_dual_write_schedule I C"
      and pre_running: "running_labels (sdwc_pre C)"
      and start:
        "exec_status (dwi_state I (dwi_initial I)) = Running"
      and key: "key_of (sdwc_event C) = sdwc_key C"
      and effect:
        "effective_source_effect
          (exec_base (dwi_state I (dwi_initial I)))
          (sdwc_event C) (sdwc_key C)"
      and scoped:
        "sdwc_key C \<in> exec_scope (dwi_state I (dwi_initial I))"
      and crash_le_fin:
        "sdwc_source_at C \<le> exec_finish (dwi_state I (dwi_initial I))"
      and no_down:
        "no_visible_key_events
          (exec_down_hist (dwi_state I (dwi_initial I))
            @ down_hist_of_labels (sdwc_pre C))
          (sdwc_source_at C) (sdwc_key C)"
    by (auto simp: source_first_separable_completion_def)
  from source_first_separated_dual_write_schedule_imp_prefix_trace[OF schedule]
  obtain sp where dwi_prefix:
    "dwi_trace I (dwi_initial I)
      (separated_completion_bad_precrash_labels Source_Effect C) sp"
    by blast
  have exec_prefix:
    "dw_exec_trace (dwi_state I (dwi_initial I))
      (sdwc_pre C @ [DoSource (sdwc_source_at C) (sdwc_event C)])
      (dwi_state I sp)"
    using dwi_trace_refines_exec[OF refines dwi_prefix]
    by (simp add: separated_completion_bad_precrash_labels_def)
  have exec_prefix_empty_gap:
    "dw_exec_trace (dwi_state I (dwi_initial I))
      (sdwc_pre C @ [DoSource (sdwc_source_at C) (sdwc_event C)] @ [])
      (dwi_state I sp)"
    using exec_prefix by simp
  have running:
    "running_labels
      (sdwc_pre C @ [DoSource (sdwc_source_at C) (sdwc_event C)] @ [])"
    using pre_running by (simp add: running_labels_def running_label_def)
  have downstream_stale:
    "Src (exec_base (dwi_state I (dwi_initial I)))
      (exec_down_hist (dwi_state I (dwi_initial I))
        @ down_hist_of_labels (sdwc_pre C) @ down_hist_of_labels [])
      (sdwc_source_at C) (sdwc_key C)
      \<noteq> event_result (sdwc_event C)"
    using effective_source_no_visible_downstream_imp_stale[OF effect no_down]
    by simp
  have no_later_empty:
    "no_visible_key_events (src_hist_of_labels [])
      (sdwc_source_at C) (sdwc_key C)"
    by (simp add: no_visible_key_events_def)
  from executable_source_window_bad_crash_extension
        [OF exec_prefix_empty_gap running start key scoped order_refl
            crash_le_fin no_later_empty downstream_stale]
  obtain s where trace:
      "dw_exec_trace (dwi_state I (dwi_initial I))
        (sdwc_pre C @ [DoSource (sdwc_source_at C) (sdwc_event C)]
          @ [] @ [Crash (sdwc_source_at C)]) s"
      and obs: "observable_mismatch s (sdwc_source_at C) (sdwc_key C)"
      and div:
        "diverges (proto_of_exec_at s (sdwc_source_at C)) (sdwc_source_at C)"
    by blast
  from trace obs div show ?thesis
    by (auto simp: separated_completion_abstract_bad_crash_execution_def
                   separated_completion_bad_crash_labels_def
                   separated_completion_bad_precrash_labels_def
                   separated_completion_crash_frontier_def)
qed

theorem downstream_first_separable_completion_has_abstract_bad_crash_execution:
  assumes first: "downstream_first_separable_completion I C"
  shows "\<exists>s.
    separated_completion_abstract_bad_crash_execution I C Downstream_Effect s"
proof -
  from first have refines: "dwi_refines_exec I"
      and schedule: "downstream_first_separated_dual_write_schedule I C"
      and pre_running: "running_labels (sdwc_pre C)"
      and start:
        "exec_status (dwi_state I (dwi_initial I)) = Running"
      and effect:
        "effective_source_effect
          (exec_base (dwi_state I (dwi_initial I)))
          (sdwc_event C) (sdwc_key C)"
      and same:
        "same_downstream_effect
          (sdwc_event C) (sdwc_down_event C) (sdwc_key C)"
      and scoped:
        "sdwc_key C \<in> exec_scope (dwi_state I (dwi_initial I))"
      and crash_le_fin:
        "sdwc_down_at C \<le> exec_finish (dwi_state I (dwi_initial I))"
      and no_source:
        "no_visible_key_events
          (exec_src_hist (dwi_state I (dwi_initial I))
            @ src_hist_of_labels (sdwc_pre C))
          (sdwc_down_at C) (sdwc_key C)"
    by (auto simp: downstream_first_separable_completion_def)
  from same have down_key: "key_of (sdwc_down_event C) = sdwc_key C"
      and result_eq:
        "event_result (sdwc_down_event C) = event_result (sdwc_event C)"
    by (auto simp: same_downstream_effect_def)
  from downstream_first_separated_dual_write_schedule_imp_prefix_trace[OF schedule]
  obtain sp where dwi_prefix:
    "dwi_trace I (dwi_initial I)
      (separated_completion_bad_precrash_labels Downstream_Effect C) sp"
    by blast
  have exec_prefix:
    "dw_exec_trace (dwi_state I (dwi_initial I))
      (sdwc_pre C
       @ [EnqueueDownstream (sdwc_down_at C) (sdwc_down_event C),
          DoDownstream (sdwc_down_at C) (sdwc_down_event C)])
      (dwi_state I sp)"
    using dwi_trace_refines_exec[OF refines dwi_prefix]
    by (simp add: separated_completion_bad_precrash_labels_def)
  have exec_prefix_empty_gap:
    "dw_exec_trace (dwi_state I (dwi_initial I))
      (sdwc_pre C
       @ [EnqueueDownstream (sdwc_down_at C) (sdwc_down_event C),
          DoDownstream (sdwc_down_at C) (sdwc_down_event C)] @ [])
      (dwi_state I sp)"
    using exec_prefix by simp
  have running:
    "running_labels
      (sdwc_pre C
       @ [EnqueueDownstream (sdwc_down_at C) (sdwc_down_event C),
          DoDownstream (sdwc_down_at C) (sdwc_down_event C)] @ [])"
    using pre_running by (simp add: running_labels_def running_label_def)
  have source_stale:
    "Src (exec_base (dwi_state I (dwi_initial I)))
      (exec_src_hist (dwi_state I (dwi_initial I))
        @ src_hist_of_labels (sdwc_pre C) @ src_hist_of_labels [])
      (sdwc_down_at C) (sdwc_key C)
      \<noteq> event_result (sdwc_down_event C)"
    using effective_source_no_visible_downstream_imp_stale[OF effect no_source]
      result_eq
    by simp
  have no_later_empty:
    "no_visible_key_events (down_hist_of_labels [])
      (sdwc_down_at C) (sdwc_key C)"
    by (simp add: no_visible_key_events_def)
  from executable_downstream_window_bad_crash_extension
        [OF exec_prefix_empty_gap running start down_key scoped order_refl
            crash_le_fin no_later_empty source_stale]
  obtain s where trace:
      "dw_exec_trace (dwi_state I (dwi_initial I))
        (sdwc_pre C
         @ [EnqueueDownstream (sdwc_down_at C) (sdwc_down_event C),
            DoDownstream (sdwc_down_at C) (sdwc_down_event C)]
         @ [] @ [Crash (sdwc_down_at C)]) s"
      and obs: "observable_mismatch s (sdwc_down_at C) (sdwc_key C)"
      and div:
        "diverges (proto_of_exec_at s (sdwc_down_at C)) (sdwc_down_at C)"
    by blast
  from trace obs div show ?thesis
    by (auto simp: separated_completion_abstract_bad_crash_execution_def
                   separated_completion_bad_crash_labels_def
                   separated_completion_bad_precrash_labels_def
                   separated_completion_crash_frontier_def)
qed

theorem separable_non_atomic_dual_write_completion_selects_bad_prefix:
  assumes completion: "separable_non_atomic_dual_write_completion I C"
  shows "\<exists>side s.
      separated_completion_first_side I C side
    \<and> separated_completion_abstract_bad_crash_execution I C side s"
proof -
  from completion obtain side where side:
    "separated_completion_first_side I C side"
    by (auto simp: separable_non_atomic_dual_write_completion_def)
  show ?thesis
  proof (cases side)
    case Source_Effect
    with side have first: "source_first_separable_completion I C"
      by (simp add: separated_completion_first_side_def)
    from source_first_separable_completion_has_abstract_bad_crash_execution
          [OF first]
    obtain s where
      bad:
        "separated_completion_abstract_bad_crash_execution I C Source_Effect s"
      by blast
    show ?thesis
      by (intro exI[where x = Source_Effect] exI[where x = s])
         (simp add: separated_completion_first_side_def first bad)
  next
    case Downstream_Effect
    with side have first: "downstream_first_separable_completion I C"
      by (simp add: separated_completion_first_side_def)
    from downstream_first_separable_completion_has_abstract_bad_crash_execution
          [OF first]
    obtain s where
      bad:
        "separated_completion_abstract_bad_crash_execution I C
          Downstream_Effect s"
      by blast
    show ?thesis
      by (intro exI[where x = Downstream_Effect] exI[where x = s])
         (simp add: separated_completion_first_side_def first bad)
  qed
qed

theorem admissible_separable_non_atomic_dual_write_completion_selects_bad_prefix:
  assumes completion:
    "admissible_separable_non_atomic_dual_write_completion I C"
  shows "\<exists>side s.
      separated_completion_first_side I C side
    \<and> admissible_separated_completion_abstract_bad_crash_execution
        I C side s"
proof -
  from completion have sep:
    "separable_non_atomic_dual_write_completion I C"
    by (simp add: admissible_separable_non_atomic_dual_write_completion_def)
  from separable_non_atomic_dual_write_completion_selects_bad_prefix[OF sep]
  obtain side s_bad where side: "separated_completion_first_side I C side"
      and bad:
        "separated_completion_abstract_bad_crash_execution I C side s_bad"
    by blast
  from completion side obtain s_adm where adm:
    "admissible_dw_exec_trace (dwi_state I (dwi_initial I))
      (separated_completion_bad_crash_labels side C) s_adm"
    by (auto simp: admissible_separable_non_atomic_dual_write_completion_def)
  have raw_adm:
    "dw_exec_trace (dwi_state I (dwi_initial I))
      (separated_completion_bad_crash_labels side C) s_adm"
    by (rule admissible_dw_exec_trace_imp_dw_exec_trace[OF adm])
  from bad have raw_bad:
    "dw_exec_trace (dwi_state I (dwi_initial I))
      (separated_completion_bad_crash_labels side C) s_bad"
    by (simp add: separated_completion_abstract_bad_crash_execution_def)
  have same: "s_adm = s_bad"
    by (rule dw_exec_trace_deterministic[OF raw_adm raw_bad])
  have adm_bad:
    "admissible_separated_completion_abstract_bad_crash_execution
      I C side s_adm"
    using bad adm same
    by (simp add: admissible_separated_completion_abstract_bad_crash_execution_def)
  from side adm_bad show ?thesis by blast
qed

theorem separable_non_atomic_dual_write_implementation_has_abstract_bad_crash_execution:
  assumes impl: "separable_non_atomic_dual_write_implementation I"
  shows "\<exists>C side s.
      separable_non_atomic_dual_write_completion I C
    \<and> separated_completion_first_side I C side
    \<and> separated_completion_abstract_bad_crash_execution I C side s"
proof -
  from impl obtain C where completion:
    "separable_non_atomic_dual_write_completion I C"
    by (auto simp: separable_non_atomic_dual_write_implementation_def)
  from separable_non_atomic_dual_write_completion_selects_bad_prefix
        [OF completion]
  obtain side s where side:
      "separated_completion_first_side I C side"
      and bad:
        "separated_completion_abstract_bad_crash_execution I C side s"
    by blast
  from completion side bad show ?thesis by blast
qed

theorem admissible_separable_non_atomic_dual_write_implementation_has_abstract_bad_crash_execution:
  assumes impl: "admissible_separable_non_atomic_dual_write_implementation I"
  shows "\<exists>C side s.
      admissible_separable_non_atomic_dual_write_completion I C
    \<and> separated_completion_first_side I C side
    \<and> admissible_separated_completion_abstract_bad_crash_execution
        I C side s"
proof -
  from impl obtain C where completion:
    "admissible_separable_non_atomic_dual_write_completion I C"
    by (auto simp:
        admissible_separable_non_atomic_dual_write_implementation_def)
  from admissible_separable_non_atomic_dual_write_completion_selects_bad_prefix
        [OF completion]
  obtain side s where side:
      "separated_completion_first_side I C side"
      and bad:
        "admissible_separated_completion_abstract_bad_crash_execution
          I C side s"
    by blast
  from completion side bad show ?thesis by blast
qed

definition separable_non_atomic_crash_closed_dual_write_implementation
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "separable_non_atomic_crash_closed_dual_write_implementation I \<longleftrightarrow>
     crash_closed_implementation I
   \<and> separable_non_atomic_dual_write_implementation I"

lemma crash_closed_extend_dwi_trace:
  assumes closed: "crash_closed_implementation I"
      and refines: "dwi_refines_exec I"
      and trace: "dwi_trace I (dwi_initial I) xs s"
      and running: "running_labels xs"
      and start: "exec_status (dwi_state I (dwi_initial I)) = Running"
      and crash_le_fin:
        "c \<le> exec_finish (dwi_state I (dwi_initial I))"
  shows "\<exists>s'. dwi_trace I (dwi_initial I) (xs @ [Crash c]) s'"
proof -
  have exec_trace:
    "dw_exec_trace (dwi_state I (dwi_initial I)) xs (dwi_state I s)"
    by (rule dwi_trace_refines_exec[OF refines trace])
  have status: "exec_status (dwi_state I s) = Running"
    by (rule dw_exec_trace_running_status[OF exec_trace running start])
  have finish:
    "exec_finish (dwi_state I s) =
     exec_finish (dwi_state I (dwi_initial I))"
    by (rule dw_exec_trace_finish[OF exec_trace])
  have le_s: "c \<le> exec_finish (dwi_state I s)"
    using crash_le_fin finish by simp
  have crash_exists: "\<exists>s'. dwi_step I s (Crash c) s'"
    using closed trace status le_s
    unfolding crash_closed_implementation_def by blast
  then obtain s' where crash: "dwi_step I s (Crash c) s'"
    by blast
  have crash_trace: "dwi_trace I s [Crash c] s'"
    by (rule dwi_trace.dwi_trace_step[OF crash dwi_trace.dwi_trace_refl])
  have full: "dwi_trace I (dwi_initial I) (xs @ [Crash c]) s'"
    by (rule dwi_trace_append[OF trace crash_trace])
  thus ?thesis by blast
qed

lemma separated_completion_first_side_refines:
  assumes "separated_completion_first_side I C side"
  shows "dwi_refines_exec I"
  using assms
  by (cases side;
      auto simp: separated_completion_first_side_def
                 source_first_separable_completion_def
                 downstream_first_separable_completion_def)

lemma separated_completion_first_side_start_running:
  assumes "separated_completion_first_side I C side"
  shows "exec_status (dwi_state I (dwi_initial I)) = Running"
  using assms
  by (cases side;
      auto simp: separated_completion_first_side_def
                 source_first_separable_completion_def
                 downstream_first_separable_completion_def)

lemma separated_completion_first_side_prefix_trace:
  assumes side: "separated_completion_first_side I C side"
  shows "\<exists>s.
    dwi_trace I (dwi_initial I)
      (separated_completion_bad_precrash_labels side C) s"
proof (cases side)
  case Source_Effect
  with side have first: "source_first_separable_completion I C"
    by (simp add: separated_completion_first_side_def)
  from first have schedule: "source_first_separated_dual_write_schedule I C"
    by (simp add: source_first_separable_completion_def)
  show ?thesis
    using Source_Effect
      source_first_separated_dual_write_schedule_imp_prefix_trace[OF schedule]
    by simp
next
  case Downstream_Effect
  with side have first: "downstream_first_separable_completion I C"
    by (simp add: separated_completion_first_side_def)
  from first have schedule:
    "downstream_first_separated_dual_write_schedule I C"
    by (simp add: downstream_first_separable_completion_def)
  show ?thesis
    using Downstream_Effect
      downstream_first_separated_dual_write_schedule_imp_prefix_trace[OF schedule]
    by simp
qed

lemma separated_completion_first_side_running_precrash:
  assumes "separated_completion_first_side I C side"
  shows "running_labels (separated_completion_bad_precrash_labels side C)"
  using assms
  by (cases side;
      auto simp: separated_completion_first_side_def
                 source_first_separable_completion_def
                 downstream_first_separable_completion_def
                 separated_completion_bad_precrash_labels_def
                 running_labels_def running_label_def)

lemma separated_completion_first_side_crash_le_finish:
  assumes "separated_completion_first_side I C side"
  shows "separated_completion_crash_frontier side C
      \<le> exec_finish (dwi_state I (dwi_initial I))"
  using assms
  by (cases side;
      auto simp: separated_completion_first_side_def
                 source_first_separable_completion_def
                 downstream_first_separable_completion_def
                 separated_completion_crash_frontier_def)

lemma separated_completion_crash_closed_lifts_abstract_bad_execution:
  assumes closed: "crash_closed_implementation I"
      and side: "separated_completion_first_side I C side"
      and bad_abs:
        "separated_completion_abstract_bad_crash_execution I C side s_abs"
  shows "\<exists>s.
    separated_completion_concrete_bad_crash_execution I C side s"
proof -
  obtain sp where prefix:
    "dwi_trace I (dwi_initial I)
      (separated_completion_bad_precrash_labels side C) sp"
    using separated_completion_first_side_prefix_trace[OF side] by blast
  have refines: "dwi_refines_exec I"
    by (rule separated_completion_first_side_refines[OF side])
  have running: "running_labels (separated_completion_bad_precrash_labels side C)"
    by (rule separated_completion_first_side_running_precrash[OF side])
  have start: "exec_status (dwi_state I (dwi_initial I)) = Running"
    by (rule separated_completion_first_side_start_running[OF side])
  have crash_le_fin:
    "separated_completion_crash_frontier side C
      \<le> exec_finish (dwi_state I (dwi_initial I))"
    by (rule separated_completion_first_side_crash_le_finish[OF side])
  from crash_closed_extend_dwi_trace
        [OF closed refines prefix running start crash_le_fin]
  obtain s where concrete_trace:
    "dwi_trace I (dwi_initial I)
      (separated_completion_bad_precrash_labels side C
       @ [Crash (separated_completion_crash_frontier side C)]) s"
    by blast
  have concrete_trace':
    "dwi_trace I (dwi_initial I)
      (separated_completion_bad_crash_labels side C) s"
    using concrete_trace
    by (simp add: separated_completion_bad_crash_labels_def)
  from bad_abs have abs_trace:
      "dw_exec_trace (dwi_state I (dwi_initial I))
        (separated_completion_bad_crash_labels side C) s_abs"
      and obs_abs:
        "observable_mismatch s_abs
          (separated_completion_crash_frontier side C) (sdwc_key C)"
      and div_abs:
        "diverges
          (proto_of_exec_at s_abs
            (separated_completion_crash_frontier side C))
          (separated_completion_crash_frontier side C)"
    by (auto simp: separated_completion_abstract_bad_crash_execution_def)
  have concrete_exec:
    "dw_exec_trace (dwi_state I (dwi_initial I))
      (separated_completion_bad_crash_labels side C) (dwi_state I s)"
    by (rule dwi_trace_refines_exec[OF refines concrete_trace'])
  have same_state: "dwi_state I s = s_abs"
    by (rule dw_exec_trace_deterministic[OF concrete_exec abs_trace])
  show ?thesis
    using concrete_trace' obs_abs div_abs same_state
    by (auto simp: separated_completion_concrete_bad_crash_execution_def)
qed

theorem separable_non_atomic_dual_write_completion_crash_closed_selects_concrete_bad_prefix:
  assumes completion: "separable_non_atomic_dual_write_completion I C"
      and closed: "crash_closed_implementation I"
  shows "\<exists>side s.
      separated_completion_first_side I C side
    \<and> separated_completion_concrete_bad_crash_execution I C side s"
proof -
  from separable_non_atomic_dual_write_completion_selects_bad_prefix
        [OF completion]
  obtain side s_abs where side:
      "separated_completion_first_side I C side"
      and bad_abs:
        "separated_completion_abstract_bad_crash_execution I C side s_abs"
    by blast
  from separated_completion_crash_closed_lifts_abstract_bad_execution
        [OF closed side bad_abs]
  obtain s where bad:
    "separated_completion_concrete_bad_crash_execution I C side s"
    by blast
  from side bad show ?thesis by blast
qed

theorem separable_non_atomic_crash_closed_dual_write_implementation_has_concrete_bad_crash_execution:
  assumes impl: "separable_non_atomic_crash_closed_dual_write_implementation I"
  shows "\<exists>C side s.
      separable_non_atomic_dual_write_completion I C
    \<and> separated_completion_first_side I C side
    \<and> separated_completion_concrete_bad_crash_execution I C side s"
proof -
  from impl obtain C where closed: "crash_closed_implementation I"
      and completion: "separable_non_atomic_dual_write_completion I C"
    by (auto simp: separable_non_atomic_crash_closed_dual_write_implementation_def
                   separable_non_atomic_dual_write_implementation_def)
  from separable_non_atomic_dual_write_completion_crash_closed_selects_concrete_bad_prefix
        [OF completion closed]
  obtain side s where side:
      "separated_completion_first_side I C side"
      and bad:
        "separated_completion_concrete_bad_crash_execution I C side s"
    by blast
  from completion side bad show ?thesis by blast
qed

corollary dual_write_concrete_bad_crash_execution:
  assumes "separable_non_atomic_crash_closed_dual_write_implementation I"
  shows "\<exists>C side s.
      separable_non_atomic_dual_write_completion I C
    \<and> separated_completion_first_side I C side
    \<and> separated_completion_concrete_bad_crash_execution I C side s"
  by (rule
      separable_non_atomic_crash_closed_dual_write_implementation_has_concrete_bad_crash_execution
      [OF assms])

theorem admissible_separable_non_atomic_crash_closed_dual_write_implementation_has_concrete_bad_crash_execution:
  assumes impl:
    "admissible_separable_non_atomic_crash_closed_dual_write_implementation I"
  shows "\<exists>C side s s_adm.
      admissible_separable_non_atomic_dual_write_completion I C
    \<and> separated_completion_first_side I C side
    \<and> separated_completion_concrete_bad_crash_execution I C side s
    \<and> admissible_dw_exec_trace (dwi_state I (dwi_initial I))
        (separated_completion_bad_crash_labels side C) s_adm
    \<and> dwi_state I s = s_adm"
proof -
  from impl obtain C where closed: "crash_closed_implementation I"
      and completion:
        "admissible_separable_non_atomic_dual_write_completion I C"
    by (auto simp:
        admissible_separable_non_atomic_crash_closed_dual_write_implementation_def
        admissible_separable_non_atomic_dual_write_implementation_def)
  from completion have sep:
    "separable_non_atomic_dual_write_completion I C"
    by (simp add: admissible_separable_non_atomic_dual_write_completion_def)
  from separable_non_atomic_dual_write_completion_crash_closed_selects_concrete_bad_prefix
        [OF sep closed]
  obtain side s where side:
      "separated_completion_first_side I C side"
      and concrete:
        "separated_completion_concrete_bad_crash_execution I C side s"
    by blast
  from completion side obtain s_adm where adm:
    "admissible_dw_exec_trace (dwi_state I (dwi_initial I))
      (separated_completion_bad_crash_labels side C) s_adm"
    by (auto simp: admissible_separable_non_atomic_dual_write_completion_def)
  have raw_adm:
    "dw_exec_trace (dwi_state I (dwi_initial I))
      (separated_completion_bad_crash_labels side C) s_adm"
    by (rule admissible_dw_exec_trace_imp_dw_exec_trace[OF adm])
  have refines: "dwi_refines_exec I"
    by (rule separated_completion_first_side_refines[OF side])
  from concrete have concrete_trace:
    "dwi_trace I (dwi_initial I)
      (separated_completion_bad_crash_labels side C) s"
    by (simp add: separated_completion_concrete_bad_crash_execution_def)
  have raw_concrete:
    "dw_exec_trace (dwi_state I (dwi_initial I))
      (separated_completion_bad_crash_labels side C) (dwi_state I s)"
    by (rule dwi_trace_refines_exec[OF refines concrete_trace])
  have same: "dwi_state I s = s_adm"
    by (rule dw_exec_trace_deterministic[OF raw_concrete raw_adm])
  from completion side concrete adm same show ?thesis by blast
qed

corollary dual_write_admissible_concrete_bad_crash_execution:
  assumes "admissible_separable_non_atomic_crash_closed_dual_write_implementation I"
  shows "\<exists>C side s s_adm.
      admissible_separable_non_atomic_dual_write_completion I C
    \<and> separated_completion_first_side I C side
    \<and> separated_completion_concrete_bad_crash_execution I C side s
    \<and> admissible_dw_exec_trace (dwi_state I (dwi_initial I))
        (separated_completion_bad_crash_labels side C) s_adm
    \<and> dwi_state I s = s_adm"
  by (rule
      admissible_separable_non_atomic_crash_closed_dual_write_implementation_has_concrete_bad_crash_execution
      [OF assms])

definition separated_completion_of_source_first
  :: "('k, 'v) source_first_separated_completion \<Rightarrow>
      ('k, 'v) separated_dual_write_completion"
where
  "separated_completion_of_source_first C =
     \<lparr> sdwc_pre = sfsc_pre C,
       sdwc_key = sfsc_key C,
       sdwc_source_at = sfsc_source_at C,
       sdwc_event = sfsc_event C,
       sdwc_down_at = sfsc_down_at C,
       sdwc_down_event = sfsc_down_event C \<rparr>"

lemma source_first_separated_completion_run_imp_source_first_separable_completion:
  assumes run: "source_first_separated_completion_run I C"
  shows "source_first_separable_completion I
    (separated_completion_of_source_first C)"
proof -
  from run have source_le_finish:
    "sfsc_source_at C \<le> exec_finish (dwi_state I (dwi_initial I))"
    by (auto simp: source_first_separated_completion_run_def
        intro: order_trans[OF order_less_imp_le])
  from run source_le_finish show ?thesis
    by (auto simp: source_first_separable_completion_def
                   source_first_separated_completion_run_def
                   source_first_separated_dual_write_schedule_def
                   source_ack_enqueue_downstream_completion_schedule_def
                   no_shared_commit_window_of_completion_def
                   separated_completion_of_source_first_def)
qed

corollary source_first_separated_completion_run_imp_separable_non_atomic_dual_write_completion:
  assumes run: "source_first_separated_completion_run I C"
  shows "separable_non_atomic_dual_write_completion I
    (separated_completion_of_source_first C)"
proof -
  have first: "source_first_separable_completion I
      (separated_completion_of_source_first C)"
    by (rule
        source_first_separated_completion_run_imp_source_first_separable_completion
        [OF run])
  show ?thesis
    unfolding separable_non_atomic_dual_write_completion_def
    by (intro exI[where x = Source_Effect])
       (simp add: separated_completion_first_side_def first)
qed

corollary source_first_separated_completion_implementation_imp_separable_non_atomic_dual_write_implementation:
  assumes impl: "source_first_separated_completion_implementation I"
  shows "separable_non_atomic_dual_write_implementation I"
proof -
  from impl obtain C where run: "source_first_separated_completion_run I C"
    by (auto simp: source_first_separated_completion_implementation_def)
  have completion:
    "separable_non_atomic_dual_write_completion I
      (separated_completion_of_source_first C)"
    by (rule
        source_first_separated_completion_run_imp_separable_non_atomic_dual_write_completion
        [OF run])
  thus ?thesis
    by (auto simp: separable_non_atomic_dual_write_implementation_def)
qed

subsection \<open>Semantic-prefix negative controls\<close>

definition completed_downstream_before_crash_gap
  :: "('k, 'v) implementation_source_first_gap_witness \<Rightarrow> bool"
where
  "completed_downstream_before_crash_gap W \<longleftrightarrow>
     isfg_gap W =
       [Ack (isfg_source_at W) (isfg_event W),
        EnqueueDownstream (isfg_down_at W) (isfg_down_event W),
        DoDownstream (isfg_down_at W) (isfg_down_event W)]"

lemma completed_downstream_before_crash_gap_not_pending_intent:
  assumes completed: "completed_downstream_before_crash_gap W"
  shows "\<not> pending_downstream_intent_at_crash I W"
  using completed
  by (simp add: completed_downstream_before_crash_gap_def
                pending_downstream_intent_at_crash_def
                implementation_gap_precrash_labels_def)

lemma completed_downstream_before_crash_gap_not_semantic_prefix:
  assumes completed: "completed_downstream_before_crash_gap W"
  shows "\<not> semantic_prefix_crash_source_first_window I W"
  using completed
  by (auto simp: completed_downstream_before_crash_gap_def
                 semantic_prefix_crash_source_first_window_def
                 source_ack_enqueue_downstream_completion_gap_def)

lemma no_source_ack_after_commit_not_adversarial_pending_intent:
  assumes no_ack: "\<not> source_ack_after_commit W"
  shows "\<not> adversarial_pending_intent_source_first_window I W"
  using no_ack
  by (simp add: adversarial_pending_intent_source_first_window_def)

lemma no_acked_source_effect_at_no_acked_observable_mismatch:
  assumes no_ack: "\<not> acked_source_effect_at s c k"
  shows "\<not> acked_observable_mismatch s c k"
  using no_ack by (simp add: acked_observable_mismatch_def)

definition prior_visible_downstream_effect_at_crash
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow>
      ('k, 'v) implementation_source_first_gap_witness \<Rightarrow> bool"
where
  "prior_visible_downstream_effect_at_crash I W \<longleftrightarrow>
     (\<exists>x \<in> set
        (exec_down_hist (dwi_state I (dwi_initial I))
          @ down_hist_of_labels (isfg_pre W)).
        visible_src_event_at (isfg_crash_at W) (isfg_key W) x)"

lemma prior_visible_downstream_effect_at_crash_not_semantic_prefix:
  assumes prior: "prior_visible_downstream_effect_at_crash I W"
  shows "\<not> semantic_prefix_crash_source_first_window I W"
  using prior
  by (auto simp: prior_visible_downstream_effect_at_crash_def
                 semantic_prefix_crash_source_first_window_def
                 no_prior_downstream_effect_at_crash_def
                 no_visible_key_events_def)

text \<open>
  Pattern-name alias: this names the gap SHAPE a shared atomic
  source+downstream commit would leave at the crash --- both writes
  completed before it --- as a sequential three-label completion.  It is
  NOT itself an indivisible macro-transition; the capability lemmas use
  it to place even this completed pattern outside the source-first
  crash-window classes.
\<close>

definition shared_atomic_source_downstream_commit_gap
  :: "('k, 'v) implementation_source_first_gap_witness \<Rightarrow> bool"
where
  "shared_atomic_source_downstream_commit_gap W \<longleftrightarrow>
     completed_downstream_before_crash_gap W"

lemma shared_atomic_source_downstream_commit_gap_outside_semantic_prefix:
  assumes atomic: "shared_atomic_source_downstream_commit_gap W"
  shows "\<not> semantic_prefix_crash_source_first_window I W"
  using atomic
  by (simp add: shared_atomic_source_downstream_commit_gap_def
                completed_downstream_before_crash_gap_not_semantic_prefix)

lemma operational_source_first_gap_imp_canonical_implementation_admits_source_first_gap:
  assumes gap: "operational_source_first_gap G"
  shows "implementation_admits_source_first_gap
    (canonical_dw_implementation (osg_start G))
    (implementation_gap_of_operational_gap G)"
proof -
  from gap obtain sp where trace:
    "dw_exec_trace (osg_start G) (operational_gap_precrash_labels G) sp"
    by (auto simp: operational_source_first_gap_def)
  have impl_trace:
    "dwi_trace (canonical_dw_implementation (osg_start G)) (osg_start G)
      (operational_gap_precrash_labels G) sp"
    by (rule dw_exec_trace_imp_canonical_dwi_trace[OF trace])
  show ?thesis
    using gap impl_trace
    by (auto simp: implementation_admits_source_first_gap_def
                   operational_source_first_gap_def
                   implementation_gap_of_operational_gap_def
                   implementation_gap_precrash_labels_def
                   operational_gap_precrash_labels_def
                   dwi_refines_exec_def
                   canonical_dw_implementation_def)
qed

lemma operational_source_first_gap_imp_canonical_implementation_crash_enabled:
  assumes gap: "operational_source_first_gap G"
  shows "implementation_crash_enabled_for_gap
    (canonical_dw_implementation (osg_start G))
    (implementation_gap_of_operational_gap G)"
proof -
  from gap have running:
      "running_labels (operational_gap_precrash_labels G)"
      and start: "exec_status (osg_start G) = Running"
    by (auto simp: operational_source_first_gap_def)
  show ?thesis
    unfolding implementation_crash_enabled_for_gap_def
  proof (intro allI impI)
    fix s
    assume trace:
      "dwi_trace (canonical_dw_implementation (osg_start G))
        (dwi_initial (canonical_dw_implementation (osg_start G)))
        (implementation_gap_precrash_labels
          (implementation_gap_of_operational_gap G)) s"
    have exec_trace:
      "dw_exec_trace (osg_start G) (operational_gap_precrash_labels G) s"
      using dwi_trace_refines_exec
        [OF canonical_dw_implementation_refines_exec[where s = "osg_start G"]
            trace]
      by (simp add: canonical_dw_implementation_def
                    implementation_gap_of_operational_gap_def
                    implementation_gap_precrash_labels_def
                    operational_gap_precrash_labels_def)
    have status: "exec_status s = Running"
      by (rule dw_exec_trace_running_status[OF exec_trace running start])
    have step:
      "dwi_step (canonical_dw_implementation (osg_start G))
        s (Crash (isfg_crash_at (implementation_gap_of_operational_gap G)))
        (s\<lparr>exec_status := Crashed
          (isfg_crash_at (implementation_gap_of_operational_gap G))\<rparr>)"
      using dw_exec_step.crash[OF status]
      by (simp add: canonical_dw_implementation_def)
    thus "\<exists>s'.
      dwi_step (canonical_dw_implementation (osg_start G))
        s (Crash (isfg_crash_at (implementation_gap_of_operational_gap G))) s'"
      by blast
  qed
qed

corollary operational_source_first_gap_imp_source_first_gap_admissible_implementation:
  assumes "operational_source_first_gap G"
  shows "source_first_gap_admissible_implementation
    (canonical_dw_implementation (osg_start G))"
  using operational_source_first_gap_imp_canonical_implementation_admits_source_first_gap
    [OF assms]
  by (auto simp: source_first_gap_admissible_implementation_def)

corollary operational_source_first_gap_imp_source_first_gap_crash_admissible_implementation:
  assumes "operational_source_first_gap G"
  shows "source_first_gap_crash_admissible_implementation
    (canonical_dw_implementation (osg_start G))"
  using
    operational_source_first_gap_imp_canonical_implementation_admits_source_first_gap
      [OF assms]
    operational_source_first_gap_imp_canonical_implementation_crash_enabled
      [OF assms]
  by (auto simp: source_first_gap_crash_admissible_implementation_def)


theorem source_first_crash_trace_has_observable_mismatch:
  assumes key: "key_of e = k"
      and changes_value: "event_result e \<noteq> b k"
      and scoped: "k \<in> K"
      and le_fin: "c \<le> fin"
  shows "\<exists>s.
      dw_exec_trace (initial_exec_state b K fin)
        [DoSource c e, Ack c e, Crash c] s
    \<and> observable_mismatch s c k
    \<and> acked_observable_mismatch s c k
    \<and> diverges (proto_of_exec_at s c) c"
proof -
  let ?s0 = "initial_exec_state b K fin"
  let ?s1 = "after_source_state b K fin c e"
  let ?s2 = "after_source_ack_state b K fin c e"
  let ?s3 = "source_crashed_state b K fin c e"

  have step1: "dw_exec_step ?s0 (DoSource c e) ?s1"
  proof -
    have "dw_exec_step ?s0 (DoSource c e)
            (?s0\<lparr>exec_src_hist := exec_src_hist ?s0 @ [(c, e)]\<rparr>)"
      by (rule dw_exec_step.do_source) (simp add: initial_exec_state_def)
    thus ?thesis
      by (simp add: after_source_state_def initial_exec_state_def)
  qed
  have step2: "dw_exec_step ?s1 (Ack c e) ?s2"
  proof -
    have "dw_exec_step ?s1 (Ack c e)
            (?s1\<lparr>exec_acked := exec_acked ?s1 @ [(c, e)]\<rparr>)"
      by (rule dw_exec_step.ack;
          simp add: after_source_state_def initial_exec_state_def)
    thus ?thesis
      by (simp add: after_source_ack_state_def after_source_state_def
                    initial_exec_state_def)
  qed
  have step3: "dw_exec_step ?s2 (Crash c) ?s3"
  proof -
    have "dw_exec_step ?s2 (Crash c) (?s2\<lparr>exec_status := Crashed c\<rparr>)"
      by (rule dw_exec_step.crash)
         (simp add: after_source_ack_state_def after_source_state_def
                    initial_exec_state_def)
    thus ?thesis
      by (simp add: source_crashed_state_def)
  qed

  have trace_tail:
    "dw_exec_trace ?s2 [Crash c] ?s3"
    by (rule dw_exec_trace.trace_step[OF step3 dw_exec_trace.trace_refl])
  have trace_mid:
    "dw_exec_trace ?s1 [Ack c e, Crash c] ?s3"
    by (rule dw_exec_trace.trace_step[OF step2 trace_tail])
  have trace:
    "dw_exec_trace ?s0 [DoSource c e, Ack c e, Crash c] ?s3"
    by (rule dw_exec_trace.trace_step[OF step1 trace_mid])

  have mismatch: "mismatch_at (proto_of_exec_at ?s3 c) c k"
    using key changes_value scoped
    by (simp add: mismatch_at_def proto_of_exec_at_def store2_of_exec_def
                  log_image_def
                  source_crashed_state_def after_source_ack_state_def
                  after_source_state_def initial_exec_state_def
                  Src_single_event_at_key restrict_def)
  hence obs: "observable_mismatch ?s3 c k"
    using le_fin
    by (simp add: observable_mismatch_def source_crashed_state_def
                  after_source_ack_state_def after_source_state_def
                  initial_exec_state_def proto_of_exec_at_def)
  hence acked_obs: "acked_observable_mismatch ?s3 c k"
    using key
    by (simp add: acked_observable_mismatch_def acked_source_effect_at_def
                  Src_single_event_at_key
                  source_crashed_state_def
                  after_source_ack_state_def after_source_state_def
                  initial_exec_state_def)
  hence div: "diverges (proto_of_exec_at ?s3 c) c"
    by (rule acked_observable_mismatch_imp_diverges)

  from trace obs acked_obs div show ?thesis by blast
qed

theorem non_atomic_uncoordinated_source_first_has_bad_crash_execution:
  assumes "non_atomic_uncoordinated_source_first A"
  shows "\<exists>s c k.
      c = impl_source_at A
    \<and> k = impl_key A
    \<and> c < impl_down_at A
    \<and> dw_exec_trace
          (initial_exec_state (impl_base A) (impl_scope A) (impl_finish A))
          [DoSource c (impl_event A), Ack c (impl_event A), Crash c] s
    \<and> observable_mismatch s c k
    \<and> diverges (proto_of_exec_at s c) c"
proof -
  from assms have key: "key_of (impl_event A) = impl_key A"
      and changes: "event_result (impl_event A) \<noteq> impl_base A (impl_key A)"
      and scoped: "impl_key A \<in> impl_scope A"
      and src_lt_down: "impl_source_at A < impl_down_at A"
      and down_le_fin: "impl_down_at A \<le> impl_finish A"
    by (auto simp: non_atomic_uncoordinated_source_first_def)
  have src_le_fin: "impl_source_at A \<le> impl_finish A"
    using src_lt_down down_le_fin by (meson order_less_imp_le order_trans)
  from source_first_crash_trace_has_observable_mismatch
        [where e = "impl_event A"
           and k = "impl_key A"
           and b = "impl_base A"
           and K = "impl_scope A"
           and c = "impl_source_at A"
           and fin = "impl_finish A",
         OF key changes scoped src_le_fin]
  obtain s where
      trace:
        "dw_exec_trace
          (initial_exec_state (impl_base A) (impl_scope A) (impl_finish A))
          [DoSource (impl_source_at A) (impl_event A),
           Ack (impl_source_at A) (impl_event A),
           Crash (impl_source_at A)] s"
      and obs: "observable_mismatch s (impl_source_at A) (impl_key A)"
      and div: "diverges (proto_of_exec_at s (impl_source_at A)) (impl_source_at A)"
    by blast
  with src_lt_down show ?thesis
    by blast
qed


subsection \<open>Finite source-first plans\<close>

lemma source_first_plan_precrash_trace:
  "dw_exec_trace
      (initial_exec_state (plan_base W) (plan_scope W) (plan_finish W))
      (source_exec_labels (plan_src_prefix W)
       @ downstream_exec_labels (plan_down_prefix W)
       @ [DoSource (plan_source_at W) (plan_event W),
          Ack (plan_source_at W) (plan_event W),
          EnqueueDownstream (plan_down_at W) (plan_down_event W)])
      (plan_after_enqueue_state W)"
proof -
  let ?s0 = "initial_exec_state (plan_base W) (plan_scope W) (plan_finish W)"
  let ?sp = "plan_prefix_state W"
  let ?ss = "plan_after_source_state W"
  let ?sa = "plan_after_ack_state W"
  let ?se = "plan_after_enqueue_state W"

  have prefix:
    "dw_exec_trace ?s0
       (source_exec_labels (plan_src_prefix W)
        @ downstream_exec_labels (plan_down_prefix W))
       ?sp"
  proof -
    have "dw_exec_trace ?s0
       (source_exec_labels (plan_src_prefix W)
        @ downstream_exec_labels (plan_down_prefix W))
       (?s0\<lparr>exec_src_hist := exec_src_hist ?s0 @ plan_src_prefix W,
             exec_down_hist := exec_down_hist ?s0 @ plan_down_prefix W,
             exec_enqueued := exec_enqueued ?s0 @ plan_down_prefix W,
             exec_pending := exec_pending ?s0 - set (plan_down_prefix W)\<rparr>)"
      by (rule dw_exec_trace_prefix_histories)
         (simp add: initial_exec_state_def)
    thus ?thesis
      by (simp add: plan_prefix_state_def initial_exec_state_def)
  qed

  have step_source:
    "dw_exec_step ?sp (DoSource (plan_source_at W) (plan_event W)) ?ss"
  proof -
    have "dw_exec_step ?sp (DoSource (plan_source_at W) (plan_event W))
            (?sp\<lparr>exec_src_hist :=
                 exec_src_hist ?sp @ [(plan_source_at W, plan_event W)]\<rparr>)"
      by (rule dw_exec_step.do_source)
         (simp add: plan_prefix_state_def initial_exec_state_def)
    thus ?thesis
      by (simp add: plan_after_source_state_def plan_prefix_state_def)
  qed
  have step_ack:
    "dw_exec_step ?ss (Ack (plan_source_at W) (plan_event W)) ?sa"
  proof -
    have "dw_exec_step ?ss (Ack (plan_source_at W) (plan_event W))
            (?ss\<lparr>exec_acked :=
                 exec_acked ?ss @ [(plan_source_at W, plan_event W)]\<rparr>)"
      by (rule dw_exec_step.ack;
          simp add: plan_after_source_state_def plan_prefix_state_def
                    initial_exec_state_def)
    thus ?thesis
      by (simp add: plan_after_ack_state_def plan_after_source_state_def
                    plan_prefix_state_def initial_exec_state_def)
  qed
  have step_enqueue:
    "dw_exec_step ?sa
       (EnqueueDownstream (plan_down_at W) (plan_down_event W)) ?se"
  proof -
    have "dw_exec_step ?sa
            (EnqueueDownstream (plan_down_at W) (plan_down_event W))
            (?sa\<lparr>exec_enqueued :=
                 exec_enqueued ?sa @ [(plan_down_at W, plan_down_event W)],
                  exec_pending :=
                 insert (plan_down_at W, plan_down_event W) (exec_pending ?sa)\<rparr>)"
      by (rule dw_exec_step.enqueue_downstream)
         (simp add: plan_after_ack_state_def plan_after_source_state_def
                    plan_prefix_state_def initial_exec_state_def)
    thus ?thesis by (simp add: plan_after_enqueue_state_def)
  qed
  have tail_enqueue:
    "dw_exec_trace ?sa
       [EnqueueDownstream (plan_down_at W) (plan_down_event W)] ?se"
    by (rule dw_exec_trace.trace_step[OF step_enqueue dw_exec_trace.trace_refl])
  have tail_ack:
    "dw_exec_trace ?ss
       [Ack (plan_source_at W) (plan_event W),
        EnqueueDownstream (plan_down_at W) (plan_down_event W)] ?se"
    by (rule dw_exec_trace.trace_step[OF step_ack tail_enqueue])
  have tail:
    "dw_exec_trace ?sp
       [DoSource (plan_source_at W) (plan_event W),
        Ack (plan_source_at W) (plan_event W),
        EnqueueDownstream (plan_down_at W) (plan_down_event W)] ?se"
    by (rule dw_exec_trace.trace_step[OF step_source tail_ack])
  show ?thesis
    using dw_exec_trace_append[OF prefix tail]
    by (simp add: append_assoc)
qed

definition no_shared_commit_window_of_plan
  :: "('k, 'v) source_first_plan \<Rightarrow>
      ('k, 'v) source_first_no_shared_commit_window"
where
  "no_shared_commit_window_of_plan W =
     \<lparr> sfnc_pre =
          source_exec_labels (plan_src_prefix W)
          @ downstream_exec_labels (plan_down_prefix W),
       sfnc_key = plan_key W,
       sfnc_source_at = plan_source_at W,
       sfnc_event = plan_event W,
       sfnc_down_at = plan_down_at W,
       sfnc_down_event = plan_down_event W,
       sfnc_crash_at = plan_source_at W \<rparr>"

lemma effective_source_first_dual_write_plan_imp_no_shared_commit_source_first_window:
  assumes plan: "effective_source_first_dual_write_plan W"
  shows "implementation_admits_no_shared_commit_source_first_window
    (canonical_dw_implementation
      (initial_exec_state (plan_base W) (plan_scope W) (plan_finish W)))
    (no_shared_commit_window_of_plan W)"
proof -
  let ?s0 = "initial_exec_state (plan_base W) (plan_scope W) (plan_finish W)"
  have trace:
    "dwi_trace (canonical_dw_implementation ?s0) ?s0
      (source_first_no_shared_commit_precrash_labels
        (no_shared_commit_window_of_plan W))
      (plan_after_enqueue_state W)"
    using dw_exec_trace_imp_canonical_dwi_trace
      [OF source_first_plan_precrash_trace[where W = W]]
    by (simp add: no_shared_commit_window_of_plan_def
                  source_first_no_shared_commit_precrash_labels_def
                  source_first_no_shared_commit_gap_labels_def append_assoc)
  from plan have source_le_finish:
      "plan_source_at W \<le> plan_finish W"
    by (auto simp: effective_source_first_dual_write_plan_def
             intro: order_trans[OF order_less_imp_le])
  show ?thesis
    unfolding implementation_admits_no_shared_commit_source_first_window_def
  proof (intro conjI)
    show "dwi_refines_exec (canonical_dw_implementation ?s0)"
      by simp
  next
    show "\<exists>s. dwi_trace (canonical_dw_implementation ?s0)
        (dwi_initial (canonical_dw_implementation ?s0))
        (source_first_no_shared_commit_precrash_labels
          (no_shared_commit_window_of_plan W)) s"
      using trace by (auto simp: canonical_dw_implementation_def)
  next
    show "running_labels (sfnc_pre (no_shared_commit_window_of_plan W))"
      by (simp add: no_shared_commit_window_of_plan_def)
  next
    show "exec_status
      (dwi_state (canonical_dw_implementation ?s0)
        (dwi_initial (canonical_dw_implementation ?s0))) = Running"
      by (simp add: canonical_dw_implementation_def initial_exec_state_def)
  next
    show "key_of (sfnc_event (no_shared_commit_window_of_plan W)) =
      sfnc_key (no_shared_commit_window_of_plan W)"
      using plan
      by (auto simp: effective_source_first_dual_write_plan_def
                     same_downstream_effect_def
                     no_shared_commit_window_of_plan_def)
  next
    show "effective_source_effect
      (exec_base
        (dwi_state (canonical_dw_implementation ?s0)
          (dwi_initial (canonical_dw_implementation ?s0))))
      (sfnc_event (no_shared_commit_window_of_plan W))
      (sfnc_key (no_shared_commit_window_of_plan W))"
      using plan
      by (simp add: effective_source_first_dual_write_plan_def
                    no_shared_commit_window_of_plan_def
                    canonical_dw_implementation_def initial_exec_state_def)
  next
    show "same_downstream_effect
      (sfnc_event (no_shared_commit_window_of_plan W))
      (sfnc_down_event (no_shared_commit_window_of_plan W))
      (sfnc_key (no_shared_commit_window_of_plan W))"
      using plan
      by (simp add: effective_source_first_dual_write_plan_def
                    no_shared_commit_window_of_plan_def)
  next
    show "sfnc_key (no_shared_commit_window_of_plan W) \<in>
      exec_scope
        (dwi_state (canonical_dw_implementation ?s0)
          (dwi_initial (canonical_dw_implementation ?s0)))"
      using plan
      by (simp add: effective_source_first_dual_write_plan_def
                    no_shared_commit_window_of_plan_def
                    canonical_dw_implementation_def initial_exec_state_def)
  next
    show "sfnc_source_at (no_shared_commit_window_of_plan W) \<le>
      sfnc_crash_at (no_shared_commit_window_of_plan W)"
      by (simp add: no_shared_commit_window_of_plan_def)
  next
    show "sfnc_crash_at (no_shared_commit_window_of_plan W) <
      sfnc_down_at (no_shared_commit_window_of_plan W)"
      using plan
      by (simp add: effective_source_first_dual_write_plan_def
                    no_shared_commit_window_of_plan_def)
  next
    show "sfnc_down_at (no_shared_commit_window_of_plan W) \<le>
      exec_finish
        (dwi_state (canonical_dw_implementation ?s0)
          (dwi_initial (canonical_dw_implementation ?s0)))"
      using plan
      by (simp add: effective_source_first_dual_write_plan_def
                    no_shared_commit_window_of_plan_def
                    canonical_dw_implementation_def initial_exec_state_def)
  next
    show "no_visible_key_events
      (exec_down_hist
        (dwi_state (canonical_dw_implementation ?s0)
          (dwi_initial (canonical_dw_implementation ?s0))) @
       down_hist_of_labels (sfnc_pre (no_shared_commit_window_of_plan W)))
      (sfnc_crash_at (no_shared_commit_window_of_plan W))
      (sfnc_key (no_shared_commit_window_of_plan W))"
      using plan
      by (simp add: effective_source_first_dual_write_plan_def
                    no_shared_commit_window_of_plan_def
                    canonical_dw_implementation_def initial_exec_state_def)
  qed
qed

corollary effective_source_first_dual_write_plan_imp_no_shared_commit_source_first_implementation:
  assumes "effective_source_first_dual_write_plan W"
  shows "no_shared_commit_source_first_implementation
    (canonical_dw_implementation
      (initial_exec_state (plan_base W) (plan_scope W) (plan_finish W)))"
  using
    effective_source_first_dual_write_plan_imp_no_shared_commit_source_first_window
      [OF assms]
  by (auto simp: no_shared_commit_source_first_implementation_def)

definition operational_gap_of_plan
  :: "('k, 'v) source_first_plan \<Rightarrow>
      ('k, 'v) operational_source_first_gap_witness"
where
  "operational_gap_of_plan W =
     \<lparr> osg_start =
          initial_exec_state (plan_base W) (plan_scope W) (plan_finish W),
       osg_pre =
          source_exec_labels (plan_src_prefix W)
          @ downstream_exec_labels (plan_down_prefix W),
       osg_gap =
          [Ack (plan_source_at W) (plan_event W),
           EnqueueDownstream (plan_down_at W) (plan_down_event W)],
       osg_key = plan_key W,
       osg_source_at = plan_source_at W,
       osg_event = plan_event W,
       osg_down_at = plan_down_at W,
       osg_down_event = plan_down_event W,
       osg_crash_at = plan_source_at W \<rparr>"

lemma effective_source_first_dual_write_plan_imp_operational_gap:
  assumes plan: "effective_source_first_dual_write_plan W"
  shows "operational_source_first_gap (operational_gap_of_plan W)"
proof -
  have trace:
    "dw_exec_trace
      (osg_start (operational_gap_of_plan W))
      (operational_gap_precrash_labels (operational_gap_of_plan W))
      (plan_after_enqueue_state W)"
    using source_first_plan_precrash_trace[where W = W]
    by (simp add: operational_gap_of_plan_def
                  operational_gap_precrash_labels_def append_assoc)
  from plan have src_le_fin: "plan_source_at W \<le> plan_finish W"
    by (auto simp: effective_source_first_dual_write_plan_def
             intro: order_trans[OF order_less_imp_le])
  show ?thesis
    unfolding operational_source_first_gap_def
    apply (intro conjI)
                     apply (rule exI[where x = "plan_after_enqueue_state W"])
                     apply (rule trace)
                    apply (simp_all add:
                       operational_gap_of_plan_def
                       operational_gap_precrash_labels_def
                       effective_source_first_dual_write_plan_def
                       initial_exec_state_def
                       running_labels_def running_label_def
                       no_visible_key_events_def)
    using plan src_le_fin
    by (auto simp: effective_source_first_dual_write_plan_def
                   same_downstream_effect_def
                   effective_source_effect_def
                   no_visible_key_events_def)
qed

theorem unprotected_source_first_dual_write_plan_instantiates_executable_window:
  assumes plan: "unprotected_source_first_dual_write_plan W"
  defines "pre \<equiv>
     source_exec_labels (plan_src_prefix W)
     @ downstream_exec_labels (plan_down_prefix W)"
  defines "gap \<equiv>
     [Ack (plan_source_at W) (plan_event W),
      EnqueueDownstream (plan_down_at W) (plan_down_event W)]"
  defines "c \<equiv> plan_source_at W"
  defines "k \<equiv> plan_key W"
  shows "\<exists>s.
      dw_exec_trace
        (initial_exec_state (plan_base W) (plan_scope W) (plan_finish W))
        (pre @ [DoSource c (plan_event W)] @ gap @ [Crash c]) s
    \<and> (plan_down_at W, plan_down_event W) \<in> set (exec_enqueued s)
    \<and> (plan_down_at W, plan_down_event W) \<in> exec_pending s
    \<and> observable_mismatch s c k
    \<and> acked_observable_mismatch s c k
    \<and> diverges (proto_of_exec_at s c) c"
proof -
  from plan have key: "key_of (plan_event W) = plan_key W"
      and stale:
        "Src (plan_base W) (plan_down_prefix W) (plan_source_at W) (plan_key W)
         \<noteq> event_result (plan_event W)"
      and scoped: "plan_key W \<in> plan_scope W"
      and src_lt_down: "plan_source_at W < plan_down_at W"
      and down_le_fin: "plan_down_at W \<le> plan_finish W"
    by (auto simp: unprotected_source_first_dual_write_plan_def
                   same_downstream_effect_def)
  have src_le_fin: "c \<le> plan_finish W"
    using src_lt_down down_le_fin by (simp add: c_def order_less_imp_le order_trans)

  let ?s0 = "initial_exec_state (plan_base W) (plan_scope W) (plan_finish W)"
  let ?sp = "plan_after_enqueue_state W"
  have prefix:
    "dw_exec_trace ?s0 (pre @ [DoSource c (plan_event W)] @ gap) ?sp"
    using source_first_plan_precrash_trace[where W = W]
    by (simp add: pre_def gap_def c_def append_assoc)
  have running: "running_labels (pre @ [DoSource c (plan_event W)] @ gap)"
    by (simp add: pre_def gap_def c_def running_labels_def running_label_def)
  have no_later: "no_visible_key_events (src_hist_of_labels gap) c k"
    by (simp add: gap_def no_visible_key_events_def)
  have downstream_stale:
    "Src (exec_base ?s0)
      (exec_down_hist ?s0 @ down_hist_of_labels pre @ down_hist_of_labels gap)
      c k \<noteq> event_result (plan_event W)"
    using stale by (simp add: initial_exec_state_def pre_def gap_def c_def k_def)
  have acked:
    "(c, plan_event W) \<in>
      set (exec_acked ?s0 @ acked_hist_of_labels
        (pre @ [DoSource c (plan_event W)] @ gap))"
    by (simp add: initial_exec_state_def pre_def gap_def c_def)

  have start0: "exec_status ?s0 = Running"
    by (simp add: initial_exec_state_def)
  have key_c: "key_of (plan_event W) = k"
    using key by (simp add: k_def)
  have scoped0: "k \<in> exec_scope ?s0"
    using scoped by (simp add: initial_exec_state_def k_def)
  have src_le_crash: "c \<le> c"
    by simp
  have crash_le_fin0: "c \<le> exec_finish ?s0"
    using src_le_fin by (simp add: initial_exec_state_def)

  from executable_source_window_acked_bad_crash_extension
        [OF prefix running start0 key_c scoped0 src_le_crash crash_le_fin0
            no_later downstream_stale acked]
  obtain s where
      trace:
        "dw_exec_trace ?s0
          (pre @ [DoSource c (plan_event W)] @ gap @ [Crash c]) s"
      and obs: "observable_mismatch s c k"
      and ack_obs: "acked_observable_mismatch s c k"
      and div: "diverges (proto_of_exec_at s c) c"
    by blast
  have pending:
    "(plan_down_at W, plan_down_event W) \<in> exec_pending s"
    using dw_exec_trace_pending[OF trace]
    by (simp add: initial_exec_state_def pre_def gap_def)
  have enqueued:
    "(plan_down_at W, plan_down_event W) \<in> set (exec_enqueued s)"
    using dw_exec_trace_enqueued[OF trace]
    by (simp add: initial_exec_state_def pre_def gap_def)
  from trace enqueued pending obs ack_obs div show ?thesis by blast
qed

theorem unprotected_source_first_dual_write_plan_has_bad_crash_execution:
  assumes plan: "unprotected_source_first_dual_write_plan W"
  shows "\<exists>s c k tr.
      c = plan_source_at W
    \<and> k = plan_key W
    \<and> tr = source_first_plan_bad_crash_trace W
    \<and> c < plan_down_at W
    \<and> dw_exec_trace
          (initial_exec_state (plan_base W) (plan_scope W) (plan_finish W))
          tr s
    \<and> (plan_down_at W, plan_down_event W) \<in> set (exec_enqueued s)
    \<and> (plan_down_at W, plan_down_event W) \<in> exec_pending s
    \<and> observable_mismatch s c k
    \<and> acked_observable_mismatch s c k
    \<and> diverges (proto_of_exec_at s c) c"
proof -
  let ?pre =
    "source_exec_labels (plan_src_prefix W)
     @ downstream_exec_labels (plan_down_prefix W)"
  let ?gap =
    "[Ack (plan_source_at W) (plan_event W),
      EnqueueDownstream (plan_down_at W) (plan_down_event W)]"
  from plan have src_lt_down: "plan_source_at W < plan_down_at W"
    by (auto simp: unprotected_source_first_dual_write_plan_def
                   same_downstream_effect_def)
  from unprotected_source_first_dual_write_plan_instantiates_executable_window
        [OF plan]
  obtain s where
      trace:
        "dw_exec_trace
          (initial_exec_state (plan_base W) (plan_scope W) (plan_finish W))
          (?pre @ [DoSource (plan_source_at W) (plan_event W)] @ ?gap
            @ [Crash (plan_source_at W)]) s"
      and enqueued:
        "(plan_down_at W, plan_down_event W) \<in> set (exec_enqueued s)"
      and pending:
        "(plan_down_at W, plan_down_event W) \<in> exec_pending s"
      and obs: "observable_mismatch s (plan_source_at W) (plan_key W)"
      and acked_obs: "acked_observable_mismatch s (plan_source_at W) (plan_key W)"
      and div:
        "diverges (proto_of_exec_at s (plan_source_at W)) (plan_source_at W)"
    by blast
  have trace':
    "dw_exec_trace
      (initial_exec_state (plan_base W) (plan_scope W) (plan_finish W))
      (source_first_plan_bad_crash_trace W) s"
    using trace by (simp add: source_first_plan_bad_crash_trace_def append_assoc)
  from src_lt_down trace' enqueued pending obs acked_obs div show ?thesis
    by blast
qed

theorem effective_source_first_dual_write_plan_has_bad_crash_execution:
  assumes plan: "effective_source_first_dual_write_plan W"
  shows "\<exists>s c k tr.
      c = plan_source_at W
    \<and> k = plan_key W
    \<and> tr = source_first_plan_bad_crash_trace W
    \<and> c < plan_down_at W
    \<and> dw_exec_trace
          (initial_exec_state (plan_base W) (plan_scope W) (plan_finish W))
          tr s
    \<and> (plan_down_at W, plan_down_event W) \<in> set (exec_enqueued s)
    \<and> (plan_down_at W, plan_down_event W) \<in> exec_pending s
    \<and> observable_mismatch s c k
    \<and> acked_observable_mismatch s c k
    \<and> diverges (proto_of_exec_at s c) c"
proof -
  have gap: "operational_source_first_gap (operational_gap_of_plan W)"
    by (rule effective_source_first_dual_write_plan_imp_operational_gap[OF plan])
  from operational_source_first_gap_has_bad_crash_execution[OF gap]
  obtain s where
      trace:
        "dw_exec_trace
          (osg_start (operational_gap_of_plan W))
          (operational_gap_crash_labels (operational_gap_of_plan W)) s"
      and enqueued:
        "(osg_down_at (operational_gap_of_plan W),
          osg_down_event (operational_gap_of_plan W)) \<in> set (exec_enqueued s)"
      and pending:
        "(osg_down_at (operational_gap_of_plan W),
          osg_down_event (operational_gap_of_plan W)) \<in> exec_pending s"
      and obs:
        "observable_mismatch s
          (osg_crash_at (operational_gap_of_plan W))
          (osg_key (operational_gap_of_plan W))"
      and ack_obs:
        "acked_observable_mismatch s
          (osg_crash_at (operational_gap_of_plan W))
          (osg_key (operational_gap_of_plan W))"
      and div:
        "diverges
          (proto_of_exec_at s (osg_crash_at (operational_gap_of_plan W)))
          (osg_crash_at (operational_gap_of_plan W))"
    by blast
  from plan have src_lt_down: "plan_source_at W < plan_down_at W"
    by (auto simp: effective_source_first_dual_write_plan_def)
  have trace':
    "dw_exec_trace
      (initial_exec_state (plan_base W) (plan_scope W) (plan_finish W))
      (source_first_plan_bad_crash_trace W) s"
    using trace
    by (simp add: operational_gap_of_plan_def
                  operational_gap_crash_labels_def
                  operational_gap_precrash_labels_def
                  source_first_plan_bad_crash_trace_def append_assoc)
  have enqueued':
    "(plan_down_at W, plan_down_event W) \<in> set (exec_enqueued s)"
    using enqueued by (simp add: operational_gap_of_plan_def)
  have pending':
    "(plan_down_at W, plan_down_event W) \<in> exec_pending s"
    using pending by (simp add: operational_gap_of_plan_def)
  have obs':
    "observable_mismatch s (plan_source_at W) (plan_key W)"
    using obs by (simp add: operational_gap_of_plan_def)
  have ack_obs':
    "acked_observable_mismatch s (plan_source_at W) (plan_key W)"
    using ack_obs by (simp add: operational_gap_of_plan_def)
  have div':
    "diverges (proto_of_exec_at s (plan_source_at W)) (plan_source_at W)"
    using div by (simp add: operational_gap_of_plan_def)
  from src_lt_down trace' enqueued' pending' obs' ack_obs' div' show ?thesis
    by blast
qed


subsection \<open>Closed non-vacuity witness\<close>

definition stale_update_impl :: "(nat, nat) source_first_impl" where
  "stale_update_impl =
     \<lparr> impl_base = [0 \<mapsto> 1],
       impl_scope = {0},
       impl_finish = ec3,
       impl_key = 0,
       impl_event = Update 0 2,
       impl_source_at = ec1,
       impl_down_at = ec3 \<rparr>"

lemma stale_update_impl_non_atomic_uncoordinated_source_first:
  "non_atomic_uncoordinated_source_first stale_update_impl"
  by (simp add: non_atomic_uncoordinated_source_first_def
                stale_update_impl_def ec_defs)

corollary stale_update_impl_has_bad_crash_execution:
  "\<exists>s c k.
      c = impl_source_at stale_update_impl
    \<and> k = impl_key stale_update_impl
    \<and> c < impl_down_at stale_update_impl
    \<and> dw_exec_trace
          (initial_exec_state
            (impl_base stale_update_impl)
            (impl_scope stale_update_impl)
            (impl_finish stale_update_impl))
          [DoSource c (impl_event stale_update_impl),
           Ack c (impl_event stale_update_impl), Crash c] s
    \<and> observable_mismatch s c k
    \<and> diverges (proto_of_exec_at s c) c"
  by (rule non_atomic_uncoordinated_source_first_has_bad_crash_execution
      [OF stale_update_impl_non_atomic_uncoordinated_source_first])


subsection \<open>Closed finite-plan witnesses\<close>

definition stale_update_plan :: "(nat, nat) source_first_plan" where
  "stale_update_plan =
     \<lparr> plan_base = [0 \<mapsto> 1],
       plan_scope = {0},
       plan_finish = ec3,
       plan_src_prefix = [],
       plan_down_prefix = [],
       plan_key = 0,
       plan_event = Update 0 2,
       plan_down_event = Update 0 2,
       plan_source_at = ec1,
       plan_down_at = ec3 \<rparr>"

lemma stale_update_plan_unprotected_source_first:
  "unprotected_source_first_dual_write_plan stale_update_plan"
  by (simp add: unprotected_source_first_dual_write_plan_def
                same_downstream_effect_def stale_update_plan_def ec_defs)

lemma stale_update_plan_effective_source_first:
  "effective_source_first_dual_write_plan stale_update_plan"
  by (simp add: effective_source_first_dual_write_plan_def
                effective_source_effect_def same_downstream_effect_def
                no_visible_key_events_def stale_update_plan_def ec_defs)

corollary stale_update_plan_has_bad_crash_execution:
  "\<exists>s c k tr.
      c = plan_source_at stale_update_plan
    \<and> k = plan_key stale_update_plan
    \<and> tr = source_first_plan_bad_crash_trace stale_update_plan
    \<and> c < plan_down_at stale_update_plan
    \<and> dw_exec_trace
          (initial_exec_state
            (plan_base stale_update_plan)
            (plan_scope stale_update_plan)
            (plan_finish stale_update_plan))
          tr s
    \<and> (plan_down_at stale_update_plan, plan_down_event stale_update_plan)
        \<in> set (exec_enqueued s)
    \<and> (plan_down_at stale_update_plan, plan_down_event stale_update_plan)
        \<in> exec_pending s
    \<and> observable_mismatch s c k
    \<and> acked_observable_mismatch s c k
    \<and> diverges (proto_of_exec_at s c) c"
  by (rule effective_source_first_dual_write_plan_has_bad_crash_execution
      [OF stale_update_plan_effective_source_first])

definition downstream_first_stale_update_initial :: "(nat, nat) dw_exec_state" where
  "downstream_first_stale_update_initial =
     initial_exec_state [0 \<mapsto> 1] {0} ec3"

definition downstream_first_stale_update_completion
  :: "(nat, nat) separated_dual_write_completion"
where
  "downstream_first_stale_update_completion =
     \<lparr> sdwc_pre = [],
       sdwc_key = 0,
       sdwc_source_at = ec3,
       sdwc_event = Update 0 2,
       sdwc_down_at = ec1,
       sdwc_down_event = Update 0 2 \<rparr>"

definition downstream_first_stale_update_enqueued :: "(nat, nat) dw_exec_state" where
  "downstream_first_stale_update_enqueued =
     downstream_first_stale_update_initial
       \<lparr> exec_enqueued :=
           exec_enqueued downstream_first_stale_update_initial
           @ [(ec1, Update 0 2)],
         exec_pending :=
           insert (ec1, Update 0 2)
             (exec_pending downstream_first_stale_update_initial) \<rparr>"

definition downstream_first_stale_update_down_done :: "(nat, nat) dw_exec_state" where
  "downstream_first_stale_update_down_done =
     downstream_first_stale_update_enqueued
       \<lparr> exec_down_hist :=
           exec_down_hist downstream_first_stale_update_enqueued
           @ [(ec1, Update 0 2)],
         exec_pending :=
           exec_pending downstream_first_stale_update_enqueued
           - {(ec1, Update 0 2)} \<rparr>"

definition downstream_first_stale_update_source_done :: "(nat, nat) dw_exec_state" where
  "downstream_first_stale_update_source_done =
     downstream_first_stale_update_down_done
       \<lparr> exec_src_hist :=
           exec_src_hist downstream_first_stale_update_down_done
           @ [(ec3, Update 0 2)] \<rparr>"

definition downstream_first_stale_update_acked :: "(nat, nat) dw_exec_state" where
  "downstream_first_stale_update_acked =
     downstream_first_stale_update_source_done
       \<lparr> exec_acked :=
           exec_acked downstream_first_stale_update_source_done
           @ [(ec3, Update 0 2)] \<rparr>"

lemma downstream_first_stale_update_completion_schedule:
  "downstream_first_separated_dual_write_schedule
    (canonical_dw_implementation downstream_first_stale_update_initial)
    downstream_first_stale_update_completion"
proof -
  let ?I = "canonical_dw_implementation downstream_first_stale_update_initial"
  have pre: "dwi_trace ?I (dwi_initial ?I)
      (sdwc_pre downstream_first_stale_update_completion)
      downstream_first_stale_update_initial"
    unfolding downstream_first_stale_update_completion_def
      downstream_first_stale_update_initial_def
      canonical_dw_implementation_def
    by (simp, rule dwi_trace.dwi_trace_refl)
  have enqueue_exec: "dw_exec_step downstream_first_stale_update_initial
      (EnqueueDownstream ec1 (Update 0 2))
      downstream_first_stale_update_enqueued"
    unfolding downstream_first_stale_update_enqueued_def
    by (rule dw_exec_step.enqueue_downstream)
       (simp add: downstream_first_stale_update_initial_def
                  initial_exec_state_def)
  from enqueue_exec have enqueue: "dwi_step ?I
      downstream_first_stale_update_initial
      (EnqueueDownstream (sdwc_down_at downstream_first_stale_update_completion)
        (sdwc_down_event downstream_first_stale_update_completion))
      downstream_first_stale_update_enqueued"
    by (simp add: downstream_first_stale_update_completion_def
                  canonical_dw_implementation_def)
  have downstream_exec: "dw_exec_step downstream_first_stale_update_enqueued
      (DoDownstream ec1 (Update 0 2))
      downstream_first_stale_update_down_done"
    unfolding downstream_first_stale_update_down_done_def
    by (rule dw_exec_step.do_downstream)
       (simp_all add: downstream_first_stale_update_initial_def
                      downstream_first_stale_update_enqueued_def
                      initial_exec_state_def)
  from downstream_exec have downstream: "dwi_step ?I
      downstream_first_stale_update_enqueued
      (DoDownstream (sdwc_down_at downstream_first_stale_update_completion)
        (sdwc_down_event downstream_first_stale_update_completion))
      downstream_first_stale_update_down_done"
    by (simp add: downstream_first_stale_update_completion_def
                  canonical_dw_implementation_def)
  have source_exec: "dw_exec_step downstream_first_stale_update_down_done
      (DoSource ec3 (Update 0 2))
      downstream_first_stale_update_source_done"
    unfolding downstream_first_stale_update_source_done_def
    by (rule dw_exec_step.do_source)
       (simp add: downstream_first_stale_update_initial_def
                  downstream_first_stale_update_enqueued_def
                  downstream_first_stale_update_down_done_def
                  initial_exec_state_def)
  from source_exec have source: "dwi_step ?I
      downstream_first_stale_update_down_done
      (DoSource (sdwc_source_at downstream_first_stale_update_completion)
        (sdwc_event downstream_first_stale_update_completion))
      downstream_first_stale_update_source_done"
    by (simp add: downstream_first_stale_update_completion_def
                  canonical_dw_implementation_def)
  have ack_exec: "dw_exec_step downstream_first_stale_update_source_done
      (Ack ec3 (Update 0 2))
      downstream_first_stale_update_acked"
    unfolding downstream_first_stale_update_acked_def
    by (rule dw_exec_step.ack)
       (simp_all add: downstream_first_stale_update_initial_def
                      downstream_first_stale_update_enqueued_def
                      downstream_first_stale_update_down_done_def
                      downstream_first_stale_update_source_done_def
                      initial_exec_state_def)
  from ack_exec have ack: "dwi_step ?I
      downstream_first_stale_update_source_done
      (Ack (sdwc_source_at downstream_first_stale_update_completion)
        (sdwc_event downstream_first_stale_update_completion))
      downstream_first_stale_update_acked"
    by (simp add: downstream_first_stale_update_completion_def
                  canonical_dw_implementation_def)
  from pre enqueue downstream source ack show ?thesis
    unfolding downstream_first_separated_dual_write_schedule_def
    by blast
qed

lemma downstream_first_stale_update_completion_admissible_trace:
  "admissible_dw_exec_trace downstream_first_stale_update_initial
    [EnqueueDownstream ec1 (Update 0 2),
     DoDownstream ec1 (Update 0 2),
     DoSource ec3 (Update 0 2),
     Ack ec3 (Update 0 2)]
    downstream_first_stale_update_acked"
proof -
  have enqueue_exec: "dw_exec_step downstream_first_stale_update_initial
      (EnqueueDownstream ec1 (Update 0 2))
      downstream_first_stale_update_enqueued"
    unfolding downstream_first_stale_update_enqueued_def
    by (rule dw_exec_step.enqueue_downstream)
       (simp add: downstream_first_stale_update_initial_def
                  initial_exec_state_def)
  have enqueue_preserves:
    "exec_label_preserves_history_wf downstream_first_stale_update_initial
      (EnqueueDownstream ec1 (Update 0 2))"
    by (simp add: exec_label_preserves_history_wf_def
                  downstream_first_stale_update_initial_def
                  initial_exec_state_def history_can_append_def ec_defs)
  have wf0: "wellformed_exec_state downstream_first_stale_update_initial"
    by (simp add: downstream_first_stale_update_initial_def)
  have wf1: "wellformed_exec_state downstream_first_stale_update_enqueued"
    by (rule dw_exec_step_wellformed_exec_state
        [OF enqueue_exec wf0 enqueue_preserves])

  have downstream_exec: "dw_exec_step downstream_first_stale_update_enqueued
      (DoDownstream ec1 (Update 0 2))
      downstream_first_stale_update_down_done"
    unfolding downstream_first_stale_update_down_done_def
    by (rule dw_exec_step.do_downstream)
       (simp_all add: downstream_first_stale_update_initial_def
                      downstream_first_stale_update_enqueued_def
                      initial_exec_state_def)
  have downstream_preserves:
    "exec_label_preserves_history_wf downstream_first_stale_update_enqueued
      (DoDownstream ec1 (Update 0 2))"
    by (simp add: exec_label_preserves_history_wf_def
                  downstream_first_stale_update_initial_def
                  downstream_first_stale_update_enqueued_def
                  initial_exec_state_def history_can_append_def ec_defs)
  have wf2: "wellformed_exec_state downstream_first_stale_update_down_done"
    by (rule dw_exec_step_wellformed_exec_state
        [OF downstream_exec wf1 downstream_preserves])

  have source_exec: "dw_exec_step downstream_first_stale_update_down_done
      (DoSource ec3 (Update 0 2))
      downstream_first_stale_update_source_done"
    unfolding downstream_first_stale_update_source_done_def
    by (rule dw_exec_step.do_source)
       (simp add: downstream_first_stale_update_initial_def
                  downstream_first_stale_update_enqueued_def
                  downstream_first_stale_update_down_done_def
                  initial_exec_state_def)
  have source_preserves:
    "exec_label_preserves_history_wf downstream_first_stale_update_down_done
      (DoSource ec3 (Update 0 2))"
    by (simp add: exec_label_preserves_history_wf_def
                  downstream_first_stale_update_initial_def
                  downstream_first_stale_update_enqueued_def
                  downstream_first_stale_update_down_done_def
                  initial_exec_state_def history_can_append_def ec_defs)
  have wf3: "wellformed_exec_state downstream_first_stale_update_source_done"
    by (rule dw_exec_step_wellformed_exec_state
        [OF source_exec wf2 source_preserves])

  have ack_exec: "dw_exec_step downstream_first_stale_update_source_done
      (Ack ec3 (Update 0 2))
      downstream_first_stale_update_acked"
    unfolding downstream_first_stale_update_acked_def
    by (rule dw_exec_step.ack)
       (simp_all add: downstream_first_stale_update_initial_def
                      downstream_first_stale_update_enqueued_def
                      downstream_first_stale_update_down_done_def
                      downstream_first_stale_update_source_done_def
                      initial_exec_state_def)
  have ack_preserves:
    "exec_label_preserves_history_wf downstream_first_stale_update_source_done
      (Ack ec3 (Update 0 2))"
    by (simp add: exec_label_preserves_history_wf_def
                  downstream_first_stale_update_initial_def
                  downstream_first_stale_update_enqueued_def
                  downstream_first_stale_update_down_done_def
                  downstream_first_stale_update_source_done_def
                  initial_exec_state_def history_can_append_def ec_defs)
  have wf4: "wellformed_exec_state downstream_first_stale_update_acked"
    by (rule dw_exec_step_wellformed_exec_state
        [OF ack_exec wf3 ack_preserves])

  show ?thesis
    by (rule admissible_dw_exec_trace.admissible_trace_step
        [OF enqueue_exec wf0 enqueue_preserves],
        rule admissible_dw_exec_trace.admissible_trace_step
        [OF downstream_exec wf1 downstream_preserves],
        rule admissible_dw_exec_trace.admissible_trace_step
        [OF source_exec wf2 source_preserves],
        rule admissible_dw_exec_trace.admissible_trace_step
        [OF ack_exec wf3 ack_preserves],
        rule admissible_dw_exec_trace.admissible_trace_refl[OF wf4])
qed

lemma downstream_first_stale_update_bad_crash_admissible_trace:
  "admissible_dw_exec_trace downstream_first_stale_update_initial
    (separated_completion_bad_crash_labels Downstream_Effect
      downstream_first_stale_update_completion)
    (downstream_first_stale_update_down_done
      \<lparr>exec_status := Crashed ec1\<rparr>)"
proof -
  have enqueue_exec: "dw_exec_step downstream_first_stale_update_initial
      (EnqueueDownstream ec1 (Update 0 2))
      downstream_first_stale_update_enqueued"
    unfolding downstream_first_stale_update_enqueued_def
    by (rule dw_exec_step.enqueue_downstream)
       (simp add: downstream_first_stale_update_initial_def
                  initial_exec_state_def)
  have enqueue_preserves:
    "exec_label_preserves_history_wf downstream_first_stale_update_initial
      (EnqueueDownstream ec1 (Update 0 2))"
    by (simp add: exec_label_preserves_history_wf_def
                  downstream_first_stale_update_initial_def
                  initial_exec_state_def history_can_append_def ec_defs)
  have wf0: "wellformed_exec_state downstream_first_stale_update_initial"
    by (simp add: downstream_first_stale_update_initial_def)
  have wf1: "wellformed_exec_state downstream_first_stale_update_enqueued"
    by (rule dw_exec_step_wellformed_exec_state
        [OF enqueue_exec wf0 enqueue_preserves])

  have downstream_exec: "dw_exec_step downstream_first_stale_update_enqueued
      (DoDownstream ec1 (Update 0 2))
      downstream_first_stale_update_down_done"
    unfolding downstream_first_stale_update_down_done_def
    by (rule dw_exec_step.do_downstream)
       (simp_all add: downstream_first_stale_update_initial_def
                      downstream_first_stale_update_enqueued_def
                      initial_exec_state_def)
  have downstream_preserves:
    "exec_label_preserves_history_wf downstream_first_stale_update_enqueued
      (DoDownstream ec1 (Update 0 2))"
    by (simp add: exec_label_preserves_history_wf_def
                  downstream_first_stale_update_initial_def
                  downstream_first_stale_update_enqueued_def
                  initial_exec_state_def history_can_append_def ec_defs)
  have wf2: "wellformed_exec_state downstream_first_stale_update_down_done"
    by (rule dw_exec_step_wellformed_exec_state
        [OF downstream_exec wf1 downstream_preserves])

  have crash_exec: "dw_exec_step downstream_first_stale_update_down_done
      (Crash ec1)
      (downstream_first_stale_update_down_done
        \<lparr>exec_status := Crashed ec1\<rparr>)"
    by (rule dw_exec_step.crash)
       (simp add: downstream_first_stale_update_initial_def
                  downstream_first_stale_update_enqueued_def
                  downstream_first_stale_update_down_done_def
                  initial_exec_state_def)
  have crash_preserves:
    "exec_label_preserves_history_wf downstream_first_stale_update_down_done
      (Crash ec1)"
    by (simp add: exec_label_preserves_history_wf_def)
  have wf3:
    "wellformed_exec_state
      (downstream_first_stale_update_down_done
        \<lparr>exec_status := Crashed ec1\<rparr>)"
    by (rule dw_exec_step_wellformed_exec_state
        [OF crash_exec wf2 crash_preserves])

  have labels:
    "separated_completion_bad_crash_labels Downstream_Effect
      downstream_first_stale_update_completion =
     [EnqueueDownstream ec1 (Update 0 2),
      DoDownstream ec1 (Update 0 2),
      Crash ec1]"
    by (simp add: separated_completion_bad_crash_labels_def
                  separated_completion_bad_precrash_labels_def
                  separated_completion_crash_frontier_def
                  downstream_first_stale_update_completion_def)
  show ?thesis
    unfolding labels
    by (rule admissible_dw_exec_trace.admissible_trace_step
        [OF enqueue_exec wf0 enqueue_preserves],
        rule admissible_dw_exec_trace.admissible_trace_step
        [OF downstream_exec wf1 downstream_preserves],
        rule admissible_dw_exec_trace.admissible_trace_step
        [OF crash_exec wf2 crash_preserves],
        rule admissible_dw_exec_trace.admissible_trace_refl[OF wf3])
qed

lemma downstream_first_stale_update_completion_is_downstream_first:
  "downstream_first_separable_completion
    (canonical_dw_implementation downstream_first_stale_update_initial)
    downstream_first_stale_update_completion"
  using downstream_first_stale_update_completion_schedule
  by (simp add: downstream_first_separable_completion_def
                downstream_first_stale_update_initial_def
                downstream_first_stale_update_completion_def
                canonical_dw_implementation_def dwi_refines_exec_def
                initial_exec_state_def running_labels_def running_label_def
                effective_source_effect_def same_downstream_effect_def
                no_visible_key_events_def ec_defs)

corollary downstream_first_stale_update_completion_inhabits_separable_non_atomic:
  "separable_non_atomic_dual_write_completion
    (canonical_dw_implementation downstream_first_stale_update_initial)
    downstream_first_stale_update_completion"
  unfolding separable_non_atomic_dual_write_completion_def
  by (intro exI[where x = Downstream_Effect])
     (simp add: separated_completion_first_side_def
                downstream_first_stale_update_completion_is_downstream_first)

lemma downstream_first_stale_update_completion_admissible_separable_non_atomic:
  "admissible_separable_non_atomic_dual_write_completion
    (canonical_dw_implementation downstream_first_stale_update_initial)
    downstream_first_stale_update_completion"
proof -
  let ?I = "canonical_dw_implementation downstream_first_stale_update_initial"
  have sep:
    "separable_non_atomic_dual_write_completion ?I
      downstream_first_stale_update_completion"
    by (rule downstream_first_stale_update_completion_inhabits_separable_non_atomic)
  show ?thesis
    unfolding admissible_separable_non_atomic_dual_write_completion_def
  proof (intro conjI allI impI)
    show "separable_non_atomic_dual_write_completion ?I
      downstream_first_stale_update_completion"
      by (rule sep)
  next
    fix side
    assume side:
      "separated_completion_first_side ?I
        downstream_first_stale_update_completion side"
    show "\<exists>s. admissible_dw_exec_trace
        (dwi_state ?I (dwi_initial ?I))
        (separated_completion_bad_crash_labels side
          downstream_first_stale_update_completion) s"
    proof (cases side)
      case Source_Effect
      with side have False
        by (simp add: separated_completion_first_side_def
                      source_first_separable_completion_def
                      downstream_first_stale_update_initial_def
                      downstream_first_stale_update_completion_def
                      canonical_dw_implementation_def ec_defs)
      thus ?thesis by blast
    next
      case Downstream_Effect
      show ?thesis
        by (intro exI[
            where x =
              "downstream_first_stale_update_down_done
                \<lparr>exec_status := Crashed ec1\<rparr>"])
           (use downstream_first_stale_update_bad_crash_admissible_trace in
              \<open>simp add: Downstream_Effect canonical_dw_implementation_def\<close>)
    qed
  qed
qed

lemma canonical_dw_implementation_crash_closed:
  "crash_closed_implementation (canonical_dw_implementation s0)"
  by (auto simp: crash_closed_implementation_def
                 canonical_dw_implementation_def
           intro: dw_exec_step.crash)

corollary downstream_first_stale_update_admissible_crash_closed_implementation:
  "admissible_separable_non_atomic_crash_closed_dual_write_implementation
    (canonical_dw_implementation downstream_first_stale_update_initial)"
  using canonical_dw_implementation_crash_closed
    downstream_first_stale_update_completion_admissible_separable_non_atomic
  by (auto simp:
      admissible_separable_non_atomic_crash_closed_dual_write_implementation_def
      admissible_separable_non_atomic_dual_write_implementation_def)

corollary downstream_first_stale_update_completion_has_abstract_bad_crash_execution:
  "\<exists>s.
    separated_completion_abstract_bad_crash_execution
      (canonical_dw_implementation downstream_first_stale_update_initial)
      downstream_first_stale_update_completion Downstream_Effect s"
  by (rule downstream_first_separable_completion_has_abstract_bad_crash_execution
      [OF downstream_first_stale_update_completion_is_downstream_first])

definition stale_delete_plan :: "(nat, nat) source_first_plan" where
  "stale_delete_plan =
     \<lparr> plan_base = [0 \<mapsto> 1],
       plan_scope = {0},
       plan_finish = ec3,
       plan_src_prefix = [],
       plan_down_prefix = [],
       plan_key = 0,
       plan_event = Delete 0,
       plan_down_event = Delete 0,
       plan_source_at = ec1,
       plan_down_at = ec3 \<rparr>"

lemma stale_delete_plan_unprotected_source_first:
  "unprotected_source_first_dual_write_plan stale_delete_plan"
  by (simp add: unprotected_source_first_dual_write_plan_def
                same_downstream_effect_def stale_delete_plan_def ec_defs)

lemma stale_delete_plan_effective_source_first:
  "effective_source_first_dual_write_plan stale_delete_plan"
  by (simp add: effective_source_first_dual_write_plan_def
                effective_source_effect_def same_downstream_effect_def
                no_visible_key_events_def stale_delete_plan_def ec_defs)

corollary stale_delete_plan_has_bad_crash_execution:
  "\<exists>s c k tr.
      c = plan_source_at stale_delete_plan
    \<and> k = plan_key stale_delete_plan
    \<and> tr = source_first_plan_bad_crash_trace stale_delete_plan
    \<and> c < plan_down_at stale_delete_plan
    \<and> dw_exec_trace
          (initial_exec_state
            (plan_base stale_delete_plan)
            (plan_scope stale_delete_plan)
            (plan_finish stale_delete_plan))
          tr s
    \<and> (plan_down_at stale_delete_plan, plan_down_event stale_delete_plan)
        \<in> set (exec_enqueued s)
    \<and> (plan_down_at stale_delete_plan, plan_down_event stale_delete_plan)
        \<in> exec_pending s
    \<and> observable_mismatch s c k
    \<and> acked_observable_mismatch s c k
    \<and> diverges (proto_of_exec_at s c) c"
  by (rule effective_source_first_dual_write_plan_has_bad_crash_execution
      [OF stale_delete_plan_effective_source_first])

end
