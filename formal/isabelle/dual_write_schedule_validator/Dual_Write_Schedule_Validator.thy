(*  Title:       Dual_Write_Schedule_Validator.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    A certified executable schedule VALIDATOR: the totality/rejection
    companion to the landed point decider (external review finding F2).

    The landed decider is correct ON valid traces: its executor
    state_of_labels evaluates blind label folds, so schedule_bad_crash_at
    returns a verdict on ANY label list, including lists that form no valid
    trace at all (from s0_ex, the list [Crash ec1, DoSource ec1 (Update 0 2)]
    --- the reverse of unsafe_sched --- admits no dw_exec_trace, because the
    do_source rule fires only from a Running status and the crash comes
    first; yet the blind fold answers True on it).  The landed correctness
    theorems are honest --- they quantify over valid traces --- but the
    landed session offers no certified way to CHECK that a given label list
    is one.  This theory supplies that check without touching the locked
    core: a total step function exec_step_fun proved equivalent to the
    inductive dw_exec_step, its Kleisli fold run_labels proved equivalent to
    dw_exec_trace, and a three-valued verdict schedule_verdict
    (Invalid / Safe / Bad) that rejects exactly the trace-less label lists
    and agrees with the landed decider on valid ones.

    Valid means: the label list forms a dw_exec_trace --- the relation the
    landed decider's correctness theorems
    (schedule_bad_crash_at_correct/sound) quantify over.  It does NOT mean
    admissible_dw_exec_trace (the wellformedness-restricted wrapper); a
    Valid schedule may still commit non-wellformed histories.

    Additive companion session: it imports the locked development and proves
    new facts only; the AFP-locked core stays byte-untouched.
*)

theory Dual_Write_Schedule_Validator
  imports Dual_Write_Core.Dual_Write_Decider
begin

section \<open>A total step function, equivalent to the inductive small step\<close>

text \<open>One equation per label constructor of @{type dw_exec_label}, mirroring
  the guards and post-states of the seven @{const dw_exec_step} rules
  verbatim; \<open>None\<close> exactly when the rule's guards fail.  Note the crash
  frontier is arbitrary from the label (not tied to \<open>exec_finish\<close>), recovery
  needs a \<open>Crashed\<close> status but ignores its frontier, and observation is a
  guard-free identity.\<close>

fun exec_step_fun
  :: "('k, 'v) dw_exec_state \<Rightarrow> ('k, 'v) dw_exec_label
      \<Rightarrow> ('k, 'v) dw_exec_state option"
where
  "exec_step_fun s (DoSource c e) =
     (if exec_status s = Running
      then Some (s\<lparr>exec_src_hist := exec_src_hist s @ [(c, e)]\<rparr>)
      else None)"
| "exec_step_fun s (EnqueueDownstream c e) =
     (if exec_status s = Running
      then Some (s\<lparr>exec_enqueued := exec_enqueued s @ [(c, e)],
                   exec_pending := insert (c, e) (exec_pending s)\<rparr>)
      else None)"
| "exec_step_fun s (DoDownstream c e) =
     (if exec_status s = Running \<and> (c, e) \<in> exec_pending s
      then Some (s\<lparr>exec_down_hist := exec_down_hist s @ [(c, e)],
                   exec_pending := exec_pending s - {(c, e)}\<rparr>)
      else None)"
| "exec_step_fun s (Ack c e) =
     (if exec_status s = Running \<and> (c, e) \<in> set (exec_src_hist s)
      then Some (s\<lparr>exec_acked := exec_acked s @ [(c, e)]\<rparr>)
      else None)"
| "exec_step_fun s (Crash c) =
     (if exec_status s = Running
      then Some (s\<lparr>exec_status := Crashed c\<rparr>)
      else None)"
| "exec_step_fun s Recover =
     (case exec_status s of
        Crashed c \<Rightarrow> Some (s\<lparr>exec_status := Recovered\<rparr>)
      | _ \<Rightarrow> None)"
| "exec_step_fun s (Observe f) = Some s"

lemma exec_step_fun_Some_iff:
  "exec_step_fun s a = Some s' \<longleftrightarrow> dw_exec_step s a s'"
proof
  assume "exec_step_fun s a = Some s'"
  then show "dw_exec_step s a s'"
    by (cases a)
       (auto intro: dw_exec_step.intros split: if_splits dw_run_status.splits)
next
  assume "dw_exec_step s a s'"
  then show "exec_step_fun s a = Some s'"
    by (cases rule: dw_exec_step.cases) auto
qed

section \<open>Running a whole schedule: the Kleisli fold\<close>

fun run_labels
  :: "('k, 'v) dw_exec_state \<Rightarrow> ('k, 'v) dw_exec_label list
      \<Rightarrow> ('k, 'v) dw_exec_state option"
where
  "run_labels s [] = Some s"
| "run_labels s (a # xs) =
     (case exec_step_fun s a of
        None \<Rightarrow> None
      | Some s' \<Rightarrow> run_labels s' xs)"

text \<open>\<open>run_labels\<close> succeeds exactly on the label lists that form a
  \<open>dw_exec_trace\<close>, and then returns exactly the relationally reached state.
  Determinism of the relation is a corollary of this functional
  characterisation, so the landed determinism lemmas are not even needed.\<close>

lemma run_labels_Some_iff:
  "run_labels s xs = Some s' \<longleftrightarrow> dw_exec_trace s xs s'"
proof (induction xs arbitrary: s)
  case Nil
  show ?case
    by (auto intro: dw_exec_trace.trace_refl dest: dw_exec_trace_NilD)
next
  case (Cons a xs)
  show ?case
  proof
    assume "run_labels s (a # xs) = Some s'"
    then obtain t where step: "exec_step_fun s a = Some t"
      and rest: "run_labels t xs = Some s'"
      by (auto split: option.splits)
    have "dw_exec_step s a t"
      using step by (simp add: exec_step_fun_Some_iff)
    moreover have "dw_exec_trace t xs s'"
      using rest by (simp add: Cons.IH)
    ultimately show "dw_exec_trace s (a # xs) s'"
      by (rule dw_exec_trace.trace_step)
  next
    assume "dw_exec_trace s (a # xs) s'"
    then obtain t where step: "dw_exec_step s a t"
      and rest: "dw_exec_trace t xs s'"
      by cases auto
    have "exec_step_fun s a = Some t"
      using step by (simp add: exec_step_fun_Some_iff)
    with rest show "run_labels s (a # xs) = Some s'"
      by (simp add: Cons.IH)
  qed
qed

section \<open>The three-valued schedule verdict\<close>

datatype dw_schedule_verdict = Invalid | Safe | Bad

definition schedule_verdict
  :: "('k, 'v) dw_exec_state \<Rightarrow> ('k, 'v) dw_exec_label list
      \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> dw_schedule_verdict"
where
  "schedule_verdict s xs c k =
     (case run_labels s xs of
        None \<Rightarrow> Invalid
      | Some s' \<Rightarrow> if observable_mismatch s' c k then Bad else Safe)"

theorem schedule_verdict_Invalid_iff:
  "schedule_verdict s xs c k = Invalid \<longleftrightarrow> (\<nexists>s'. dw_exec_trace s xs s')"
proof (cases "run_labels s xs")
  case None
  then show ?thesis
    by (auto simp: schedule_verdict_def run_labels_Some_iff[symmetric])
next
  case (Some t)
  then have "dw_exec_trace s xs t"
    by (simp add: run_labels_Some_iff)
  with Some show ?thesis
    by (auto simp: schedule_verdict_def split: if_splits)
qed

theorem schedule_verdict_Bad_iff:
  "schedule_verdict s xs c k = Bad \<longleftrightarrow>
     (\<exists>s'. dw_exec_trace s xs s' \<and> observable_mismatch s' c k)"
proof (cases "run_labels s xs")
  case None
  then show ?thesis
    by (auto simp: schedule_verdict_def run_labels_Some_iff[symmetric])
next
  case (Some t)
  then have tr: "dw_exec_trace s xs t"
    by (simp add: run_labels_Some_iff)
  have uniq: "s' = t" if "dw_exec_trace s xs s'" for s'
    using Some that by (auto simp: run_labels_Some_iff[symmetric])
  show ?thesis
  proof (cases "observable_mismatch t c k")
    case True
    then have "schedule_verdict s xs c k = Bad"
      using Some by (simp add: schedule_verdict_def)
    with True tr show ?thesis by auto
  next
    case False
    then have lhs: "schedule_verdict s xs c k = Safe"
      using Some by (simp add: schedule_verdict_def)
    have "\<not> (\<exists>s'. dw_exec_trace s xs s' \<and> observable_mismatch s' c k)"
      using uniq False by auto
    with lhs show ?thesis by simp
  qed
qed

theorem schedule_verdict_Safe_iff:
  "schedule_verdict s xs c k = Safe \<longleftrightarrow>
     (\<exists>s'. dw_exec_trace s xs s' \<and> \<not> observable_mismatch s' c k)"
proof (cases "run_labels s xs")
  case None
  then show ?thesis
    by (auto simp: schedule_verdict_def run_labels_Some_iff[symmetric])
next
  case (Some t)
  then have tr: "dw_exec_trace s xs t"
    by (simp add: run_labels_Some_iff)
  have uniq: "s' = t" if "dw_exec_trace s xs s'" for s'
    using Some that by (auto simp: run_labels_Some_iff[symmetric])
  show ?thesis
  proof (cases "observable_mismatch t c k")
    case True
    then have lhs: "schedule_verdict s xs c k = Bad"
      using Some by (simp add: schedule_verdict_def)
    have "\<not> (\<exists>s'. dw_exec_trace s xs s' \<and> \<not> observable_mismatch s' c k)"
      using uniq True by auto
    with lhs show ?thesis by simp
  next
    case False
    then have "schedule_verdict s xs c k = Safe"
      using Some by (simp add: schedule_verdict_def)
    with False tr show ?thesis by auto
  qed
qed

subsection \<open>Tie-back to the landed decider\<close>

text \<open>On any label list the validator does not reject, its Bad verdict is
  exactly the landed decider's verdict: the validator refines
  @{const schedule_bad_crash_at} with an explicit validity certificate.\<close>

theorem schedule_verdict_Bad_iff_landed:
  "schedule_verdict s xs c k = Bad \<longleftrightarrow>
     (\<exists>s'. dw_exec_trace s xs s') \<and> schedule_bad_crash_at s xs c k"
proof
  assume "schedule_verdict s xs c k = Bad"
  then obtain s' where tr: "dw_exec_trace s xs s'"
    and obs: "observable_mismatch s' c k"
    by (auto simp: schedule_verdict_Bad_iff)
  have "schedule_bad_crash_at s xs c k"
    using schedule_bad_crash_at_correct[OF tr] obs by simp
  with tr show "(\<exists>s'. dw_exec_trace s xs s') \<and> schedule_bad_crash_at s xs c k"
    by auto
next
  assume "(\<exists>s'. dw_exec_trace s xs s') \<and> schedule_bad_crash_at s xs c k"
  then obtain s' where tr: "dw_exec_trace s xs s'"
    and verdict: "schedule_bad_crash_at s xs c k"
    by auto
  have "observable_mismatch s' c k"
    using schedule_bad_crash_at_correct[OF tr] verdict by simp
  with tr show "schedule_verdict s xs c k = Bad"
    by (auto simp: schedule_verdict_Bad_iff)
qed

section \<open>Worked examples: the validator rejects what the blind fold misjudges\<close>

text \<open>Kernel-evaluated (\<open>code_simp\<close>), oracle-free.  The first pair is the
  honesty gap on display: the reverse of @{const unsafe_sched} forms no
  trace --- the \<open>do_source\<close> rule fires only from \<open>Running\<close>, but the crash
  comes first --- so the validator answers \<open>Invalid\<close>, while the blind fold
  @{const schedule_bad_crash_at} answers \<open>True\<close> on the very same list.\<close>

lemma validator_invalid_example:
  "schedule_verdict s0_ex [Crash ec1, DoSource ec1 (Update 0 2)] ec1 0 = Invalid"
  by code_simp

lemma raw_evaluator_disagrees_on_invalid:
  "schedule_bad_crash_at s0_ex [Crash ec1, DoSource ec1 (Update 0 2)] ec1 0
   \<and> schedule_verdict s0_ex [Crash ec1, DoSource ec1 (Update 0 2)] ec1 0 = Invalid"
  by code_simp

lemma validator_unsafe_example:
  "schedule_verdict s0_ex unsafe_sched ec1 0 = Bad"
  by code_simp

lemma validator_safe_example:
  "schedule_verdict s0_ex safe_sched ec1 0 = Safe"
  by code_simp

text \<open>Wrong-point control: the same unsafe schedule judged at an unaffected
  key.  Key \<open>1\<close> is outside the scope \<open>{0}\<close> of @{const s0_ex} and no event
  touches it, so the schedule is valid but carries no observable mismatch at
  that point: \<open>Safe\<close>, not \<open>Bad\<close> --- the verdict is point-sensitive, not a
  constant.\<close>

lemma validator_wrong_key_control:
  "schedule_verdict s0_ex unsafe_sched ec1 1 = Safe"
  by code_simp

section \<open>Standard ML export\<close>

text \<open>The validator, the Kleisli fold and the step function all generate and
  type-check as Standard ML.  The \<open>src_coord\<close> code setup is imported from the
  landed decider and reused, not redeclared.\<close>

export_code
  schedule_verdict run_labels exec_step_fun
  initial_exec_state coord_of_nat
  checking SML

end
