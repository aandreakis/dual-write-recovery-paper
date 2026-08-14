(*  Title:       Dual_Write_Decider.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    A certified, executable point decider for the bad-crash status of a
    concrete dual-write schedule at a given crash frontier and key --- the
    "Programs" companion to the partition theory.

    The relational small-step semantics dw_exec_trace is deterministic and its
    data fields are folds of the label list.  This theory packages that into an
    executable executor state_of_labels and proves it AGREES with the relation
    (on every field observable_mismatch reads), so a concrete schedule's
    bad-crash status at a given frontier c and key k is computed by a total
    function, schedule_bad_crash_at,
    proved correct against the relational observable_mismatch and tied to
    divergence.  Everything is code-exported to Standard ML and exercised on a
    concrete unsafe schedule (a source update crashed before downstream
    catch-up) and a safe one (no crash), proved by kernel evaluation
    (code_simp), so the decider is oracle-free as well as runnable.

    Additive and DBLog-free: imports the existing development and proves new
    facts only; no existing theory is modified.  The only fold without an
    existing lemma is the run-status fold, supplied here.
*)

theory Dual_Write_Decider
  imports Dual_Write_Partition
begin

section \<open>The run-status fold (the one field lacking an existing fold)\<close>

text \<open>The history, pending, scope, base and finish fields of a reached state are
  already characterised as folds/invariants of the label list
  (\<open>dw_exec_trace_src_hist\<close> and friends, \<open>dw_exec_trace_base/scope/finish\<close>).
  Only the run status lacks such a lemma; it advances to \<open>Crashed c\<close> on a crash
  and to \<open>Recovered\<close> on a recover, and is otherwise unchanged.\<close>

fun status_after_labels :: "dw_run_status \<Rightarrow> ('k, 'v) dw_exec_label list \<Rightarrow> dw_run_status" where
  "status_after_labels st [] = st"
| "status_after_labels st (DoSource c e # xs) = status_after_labels st xs"
| "status_after_labels st (EnqueueDownstream c e # xs) = status_after_labels st xs"
| "status_after_labels st (DoDownstream c e # xs) = status_after_labels st xs"
| "status_after_labels st (Ack c e # xs) = status_after_labels st xs"
| "status_after_labels st (Crash c # xs) = status_after_labels (Crashed c) xs"
| "status_after_labels st (Recover # xs) = status_after_labels Recovered xs"
| "status_after_labels st (Observe f # xs) = status_after_labels st xs"

lemma status_after_labels_append:
  "status_after_labels st (xs @ ys) = status_after_labels (status_after_labels st xs) ys"
  by (induction st xs rule: status_after_labels.induct) auto

lemma dw_exec_step_status:
  assumes "dw_exec_step s a s'"
  shows "exec_status s' = status_after_labels (exec_status s) [a]"
  using assms by (cases rule: dw_exec_step.cases) auto

lemma dw_exec_trace_status:
  assumes "dw_exec_trace s xs s'"
  shows "exec_status s' = status_after_labels (exec_status s) xs"
  using assms
proof (induction rule: dw_exec_trace.induct)
  case (trace_refl s) show ?case by simp
next
  case (trace_step s a s' xs s'')
  have "exec_status s'' = status_after_labels (exec_status s') xs"
    by (rule trace_step.IH)
  also have "\<dots> = status_after_labels (status_after_labels (exec_status s) [a]) xs"
    using dw_exec_step_status[OF trace_step.hyps(1)] by simp
  also have "\<dots> = status_after_labels (exec_status s) (a # xs)"
    using status_after_labels_append[of "exec_status s" "[a]" xs] by simp
  finally show ?case .
qed

section \<open>The executable executor and its agreement with the relation\<close>

definition state_of_labels
  :: "('k, 'v) dw_exec_state \<Rightarrow> ('k, 'v) dw_exec_label list \<Rightarrow> ('k, 'v) dw_exec_state"
where
  "state_of_labels s xs =
     s\<lparr> exec_src_hist  := exec_src_hist s @ src_hist_of_labels xs,
        exec_down_hist := exec_down_hist s @ down_hist_of_labels xs,
        exec_enqueued  := exec_enqueued s @ enqueued_hist_of_labels xs,
        exec_pending   := pending_after_labels xs (exec_pending s),
        exec_acked     := exec_acked s @ acked_hist_of_labels xs,
        exec_status    := status_after_labels (exec_status s) xs \<rparr>"

text \<open>\<open>observable_mismatch\<close> reads only the status, finish, base, source history,
  scope and downstream history --- all of which agree between the relationally
  reached state and the executor's output.\<close>

lemma observable_mismatch_state_of_labels:
  assumes tr: "dw_exec_trace s xs s'"
  shows "observable_mismatch s' c k = observable_mismatch (state_of_labels s xs) c k"
proof -
  have st: "exec_status s' = exec_status (state_of_labels s xs)"
    using dw_exec_trace_status[OF tr] by (simp add: state_of_labels_def)
  have fin: "exec_finish s' = exec_finish (state_of_labels s xs)"
    using Dual_Write_Execution.dw_exec_trace_finish[OF tr] by (simp add: state_of_labels_def)
  have base: "exec_base s' = exec_base (state_of_labels s xs)"
    using Dual_Write_Execution.dw_exec_trace_base[OF tr] by (simp add: state_of_labels_def)
  have scope: "exec_scope s' = exec_scope (state_of_labels s xs)"
    using Dual_Write_Execution.dw_exec_trace_scope[OF tr] by (simp add: state_of_labels_def)
  have src: "exec_src_hist s' = exec_src_hist (state_of_labels s xs)"
    using Dual_Write_Execution.dw_exec_trace_src_hist[OF tr] by (simp add: state_of_labels_def)
  have down: "exec_down_hist s' = exec_down_hist (state_of_labels s xs)"
    using Dual_Write_Execution.dw_exec_trace_down_hist[OF tr] by (simp add: state_of_labels_def)
  have store2: "store2_of_exec s' = store2_of_exec (state_of_labels s xs)"
    by (simp add: store2_of_exec_def base down fun_eq_iff)
  have proto: "proto_of_exec_at s' c = proto_of_exec_at (state_of_labels s xs) c"
    by (simp add: proto_of_exec_at_def base scope src fin store2)
  show ?thesis
    by (simp add: observable_mismatch_def st fin proto)
qed

section \<open>The certified decider\<close>

definition schedule_bad_crash_at
  :: "('k, 'v) dw_exec_state \<Rightarrow> ('k, 'v) dw_exec_label list \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> bool"
where
  "schedule_bad_crash_at s0 xs c k = observable_mismatch (state_of_labels s0 xs) c k"

text \<open>Correctness: on any schedule that forms a valid trace, the executable
  verdict matches the relational \<open>observable_mismatch\<close> at the reached state.\<close>

theorem schedule_bad_crash_at_correct:
  assumes "dw_exec_trace s0 xs s'"
  shows "schedule_bad_crash_at s0 xs c k = observable_mismatch s' c k"
  using observable_mismatch_state_of_labels[OF assms]
  by (simp add: schedule_bad_crash_at_def)

text \<open>Soundness: a positive verdict on a valid trace is a genuine observable bad
  crash that diverges at the crash frontier.\<close>

theorem schedule_bad_crash_at_sound:
  assumes tr: "dw_exec_trace s0 xs s'"
      and verdict: "schedule_bad_crash_at s0 xs c k"
  shows "observable_mismatch s' c k
       \<and> diverges (proto_of_exec_at s' c) c"
proof -
  have obs: "observable_mismatch s' c k"
    using schedule_bad_crash_at_correct[OF tr] verdict by simp
  show ?thesis
    using obs observable_mismatch_imp_diverges[OF obs] by simp
qed

section \<open>Code setup for the source-coordinate type\<close>

text \<open>\<open>src_coord\<close> is a typedef copy of the naturals.  We give it a code
  presentation through its sole abstraction \<open>coord_of_nat\<close>, making \<open>Rep\<close>,
  \<open>src_le\<close>, the linorder and equality computable, so the decider exports.\<close>

instantiation src_coord :: equal
begin
definition equal_src_coord :: "src_coord \<Rightarrow> src_coord \<Rightarrow> bool" where
  "equal_src_coord x y \<longleftrightarrow> x = y"
instance by intro_classes (simp add: equal_src_coord_def)
end

code_datatype coord_of_nat

declare Rep_coord_of_nat [code]

lemma src_le_code [code]:
  "src_le (coord_of_nat m) (coord_of_nat n) \<longleftrightarrow> (m \<le> n)"
  by (simp add: src_le_def)

lemma less_eq_src_coord_code [code]:
  "(coord_of_nat m \<le> coord_of_nat n) \<longleftrightarrow> (m \<le> n)"
  by (simp add: less_eq_src_coord_def src_le_def)

lemma equal_src_coord_code [code]:
  "equal_class.equal (coord_of_nat m) (coord_of_nat n) \<longleftrightarrow> (m = n)"
  by (simp add: equal_src_coord_def coord_of_nat_def Abs_src_coord_inject[OF UNIV_I UNIV_I])

declare c0_eq_coord_of_nat_0 [code]

section \<open>Worked examples and Standard ML export\<close>

text \<open>A two-key-free start state: scope \<open>{0}\<close>, the authority maps key \<open>0\<close> to \<open>1\<close>,
  the modelled interval ends at \<open>ec3\<close>.\<close>

definition s0_ex :: "(nat, nat) dw_exec_state" where
  "s0_ex = initial_exec_state [0 \<mapsto> 1] {0} ec3"

text \<open>Unsafe: the source updates key \<open>0\<close> to \<open>2\<close> at \<open>ec1\<close>, then crashes before the
  downstream catches up --- a non-atomic source-first window frozen by the crash.\<close>
definition unsafe_sched :: "(nat, nat) dw_exec_label list" where
  "unsafe_sched = [DoSource ec1 (Update 0 2), Crash ec1]"

text \<open>Safe on this schedule: the same source update with no crash, so the run is
  still \<open>Running\<close> and no crash is observable.\<close>
definition safe_sched :: "(nat, nat) dw_exec_label list" where
  "safe_sched = [DoSource ec1 (Update 0 2)]"

text \<open>The verdicts are computed by kernel evaluation (\<open>code_simp\<close>), so these are
  oracle-free theorems, not merely evaluations.\<close>

lemma unsafe_example: "schedule_bad_crash_at s0_ex unsafe_sched ec1 0"
  by code_simp

lemma safe_example: "\<not> schedule_bad_crash_at s0_ex safe_sched ec1 0"
  by code_simp

text \<open>The decider, the executor and the status fold all generate and type-check
  as Standard ML.\<close>

export_code schedule_bad_crash_at state_of_labels status_after_labels
  initial_exec_state coord_of_nat checking SML

end
