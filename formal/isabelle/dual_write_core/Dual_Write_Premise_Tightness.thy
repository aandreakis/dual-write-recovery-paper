(*  Title:       Dual_Write_Premise_Tightness.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Premise tightness for the image-level crash-safety characterization
    safe_iff_running_image_faithful (Dual_Write_Converse.thy).  That
    biconditional carries three hypotheses:

      (1) crash_closed_implementation I,
      (2) dwi_refines_exec I               (refinement),
      (3) Running-start.

    This additive theory contributes the crash-closure witness and a
    non-falsifying refinement control; across the development the tightness
    triptych is counterexample-witnessed 3-of-3 (the Running-start pole in
    Dual_Write_Converse by running_start_is_load_bearing, the refinement pole
    in both directions in the sibling theory Dual_Write_Refinement_Tightness).

    Witness one (crash-closure).  A refining, Running-start, NON-crash-closed
    implementation I_relay_labels_open that reaches a genuine reachable Running scoped
    mismatch at the loaded frontier ec3 (key 0, scope {0}) yet is SAFE (no
    reachable observable bad crash).  It runs the loaded relay
    w0 -> w_src2 -> w_enq2 -> w_down2 -> w_src3 with the Crash step WITHHELD, so
    no reachable state is ever Crashed and observable_mismatch (which requires a
    Crashed status) is unsatisfiable on reachable states.  Safety is therefore
    earned by the ABSENCE of a crash at the mismatched Running frontier, NOT by
    the absence of Running states (the vacuity kill-test).  Hence the FORWARD
    direction safe ==> running_image_faithful FAILS once crash-closure is
    dropped: crash-closure is load-bearing.

    Witness two (refinement).  Refinement IS counterexample-witnessable, in
    both directions; the witnesses live in the sibling theory
    Dual_Write_Refinement_Tightness.  There, crash-closed, Running-start,
    non-refining implementations falsify the forward direction (safe yet not
    image-faithful: refinement_drop_falsifies_forward, repeated at the landed
    record state type as refinement_drop_falsifies_forward_exec_type) and the
    backward direction (image-faithful yet unsafe:
    refinement_drop_falsifies_backward).  Refinement is also proof-essential:
    both sides of the biconditional evaluate on any implementation (no
    refinement hypothesis is needed to type them), and the two proof engines
    case-analyse dw_exec_step, reachable only through dwi_refines_exec.  This
    theory retains the landed non-refining control
    sf_non_refining_implementation (crash_closed + Running-start + NOT
    refining) as ONE non-falsifying instance: BOTH sides of the biconditional
    are genuinely, non-vacuously false on it, so the biconditional still holds
    on it.  Dropping refinement therefore does not falsify the statement on
    EVERY implementation --- the non-refining class contains both falsifying
    and non-falsifying members.

    Every reused fact was verified against the landed development.  This theory
    adds no axiom, sorry, or oracle; its headline facts are certified
    oracle-free by a separate build gate kept out of the locked source.
*)

theory Dual_Write_Premise_Tightness
  imports
    Dual_Write_Converse
    Dual_Write_Partition
    Dual_Write_Operational_Definition_Audit
begin

section \<open>Premise tightness for the crash-safety characterization\<close>

subsection \<open>Witness one: the implementation with the crash withheld\<close>

text \<open>
  The witness runs the landed loaded relay states and steps
  (@{const w0}, @{const w_src2}, @{const w_enq2}, @{const w_down2},
  @{const w_src3}), each step packaging a genuine @{const dw_exec_step} inside
  the matching relay lemma, but never offers a @{const Crash} successor.  The
  abstraction map is the identity, so refinement reduces exactly to ``every
  admitted transition is a @{const dw_exec_step}''.
\<close>

definition I_relay_labels_open
  :: "((nat, nat) dw_exec_state, nat, nat) dual_write_implementation"
where
  "I_relay_labels_open =
     \<lparr> dwi_initial = w0,
       dwi_step =
         (\<lambda>s a s'.
              (s = w0     \<and> a = DoSource ec2 (Insert 0 7)         \<and> s' = w_src2)
            \<or> (s = w_src2 \<and> a = EnqueueDownstream ec2 (Insert 0 7) \<and> s' = w_enq2)
            \<or> (s = w_enq2 \<and> a = DoDownstream ec2 (Insert 0 7)      \<and> s' = w_down2)
            \<or> (s = w_down2 \<and> a = DoSource ec3 (Insert 0 9)         \<and> s' = w_src3)),
       dwi_state = (\<lambda>s. s) \<rparr>"

lemma I_relay_labels_open_state [simp]: "dwi_state I_relay_labels_open s = s"
  by (simp add: I_relay_labels_open_def)

lemma I_relay_labels_open_initial [simp]: "dwi_initial I_relay_labels_open = w0"
  by (simp add: I_relay_labels_open_def)

lemma I_relay_labels_open_step_iff:
  "dwi_step I_relay_labels_open s a s' \<longleftrightarrow>
     (s = w0 \<and> a = DoSource ec2 (Insert 0 7) \<and> s' = w_src2)
   \<or> (s = w_src2 \<and> a = EnqueueDownstream ec2 (Insert 0 7) \<and> s' = w_enq2)
   \<or> (s = w_enq2 \<and> a = DoDownstream ec2 (Insert 0 7) \<and> s' = w_down2)
   \<or> (s = w_down2 \<and> a = DoSource ec3 (Insert 0 9) \<and> s' = w_src3)"
  by (simp add: I_relay_labels_open_def)

text \<open>Refinement: each admitted step is precisely the underlying
  @{const dw_exec_step} packaged inside the matching relay lemma, extracted via
  @{thm relay_step_def} (@{const relay_step} is @{const dw_exec_step} together
  with @{const relay_admits}).\<close>

lemma I_relay_labels_open_refines_exec: "dwi_refines_exec I_relay_labels_open"
  unfolding dwi_refines_exec_def
proof (intro allI impI)
  fix s a s'
  assume "dwi_step I_relay_labels_open s a s'"
  then consider
      (a) "s = w0 \<and> a = DoSource ec2 (Insert 0 7) \<and> s' = w_src2"
    | (b) "s = w_src2 \<and> a = EnqueueDownstream ec2 (Insert 0 7) \<and> s' = w_enq2"
    | (c) "s = w_enq2 \<and> a = DoDownstream ec2 (Insert 0 7) \<and> s' = w_down2"
    | (d) "s = w_down2 \<and> a = DoSource ec3 (Insert 0 9) \<and> s' = w_src3"
    by (auto simp: I_relay_labels_open_step_iff)
  then show "dw_exec_step (dwi_state I_relay_labels_open s) a (dwi_state I_relay_labels_open s')"
  proof cases
    case a
    then show ?thesis
      using w_step_src2 by (simp add: relay_step_def)
  next
    case b
    then show ?thesis
      using w_step_enq2 by (simp add: relay_step_def)
  next
    case c
    then show ?thesis
      using w_step_down2 by (simp add: relay_step_def)
  next
    case d
    then show ?thesis
      using w_step_src3 by (simp add: relay_step_def)
  qed
qed

lemma I_relay_labels_open_start_running:
  "exec_status (dwi_state I_relay_labels_open (dwi_initial I_relay_labels_open)) = Running"
  by (simp add: w0_def initial_exec_state_def)

text \<open>Not crash-closed: at the reachable Running in-range state @{const w_src3}
  (reached by the loaded run below) the step relation offers no
  @{term "Crash c"} successor, so the crash-closure obligation
  @{thm crash_closed_implementation_def} fails.\<close>

lemma I_relay_labels_open_no_crash_step_at_w_src3:
  "\<not> (\<exists>s'. dwi_step I_relay_labels_open w_src3 (Crash ec3) s')"
  by (auto simp: I_relay_labels_open_step_iff
                 w_src3_def w_down2_def w_enq2_def w_src2_def w0_def
                 initial_exec_state_def)

text \<open>Kill-test, positive half: a genuine reachable Running scoped mismatch.
  The loaded run reaches @{const w_src3} --- Running, in-range at @{const ec3},
  scope @{term "{0::nat}"} (non-empty), with a genuine scoped mismatch at key 0.
  This is the loaded frontier @{const ec3}, the opposite of a state with no
  reachable Running frontier.\<close>

lemma I_relay_labels_open_reaches_w_src3:
  "dwi_trace I_relay_labels_open (dwi_initial I_relay_labels_open)
     [DoSource ec2 (Insert 0 7), EnqueueDownstream ec2 (Insert 0 7),
      DoDownstream ec2 (Insert 0 7), DoSource ec3 (Insert 0 9)]
     w_src3"
proof -
  have s1: "dwi_step I_relay_labels_open w0 (DoSource ec2 (Insert 0 7)) w_src2"
    by (simp add: I_relay_labels_open_step_iff)
  have s2: "dwi_step I_relay_labels_open w_src2 (EnqueueDownstream ec2 (Insert 0 7)) w_enq2"
    by (simp add: I_relay_labels_open_step_iff)
  have s3: "dwi_step I_relay_labels_open w_enq2 (DoDownstream ec2 (Insert 0 7)) w_down2"
    by (simp add: I_relay_labels_open_step_iff)
  have s4: "dwi_step I_relay_labels_open w_down2 (DoSource ec3 (Insert 0 9)) w_src3"
    by (simp add: I_relay_labels_open_step_iff)
  have "dwi_trace I_relay_labels_open w0
          [DoSource ec2 (Insert 0 7), EnqueueDownstream ec2 (Insert 0 7),
           DoDownstream ec2 (Insert 0 7), DoSource ec3 (Insert 0 9)]
          w_src3"
    by (rule dwi_trace.dwi_trace_step[OF s1],
        rule dwi_trace.dwi_trace_step[OF s2],
        rule dwi_trace.dwi_trace_step[OF s3],
        rule dwi_trace.dwi_trace_step[OF s4],
        rule dwi_trace.dwi_trace_refl)
  then show ?thesis by simp
qed

lemma I_relay_labels_open_not_crash_closed:
  "\<not> crash_closed_implementation I_relay_labels_open"
proof
  assume "crash_closed_implementation I_relay_labels_open"
  moreover have "dwi_trace I_relay_labels_open (dwi_initial I_relay_labels_open)
     [DoSource ec2 (Insert 0 7), EnqueueDownstream ec2 (Insert 0 7),
      DoDownstream ec2 (Insert 0 7), DoSource ec3 (Insert 0 9)]
     w_src3"
    by (rule I_relay_labels_open_reaches_w_src3)
  moreover have "exec_status (dwi_state I_relay_labels_open w_src3) = Running"
    by (simp add: w_src3_running)
  moreover have "ec3 \<le> exec_finish (dwi_state I_relay_labels_open w_src3)"
    by (simp add: w_src3_fields src_le_refl src_le_eq_less_eq)
  ultimately obtain s' where "dwi_step I_relay_labels_open w_src3 (Crash ec3) s'"
    unfolding crash_closed_implementation_def by blast
  with I_relay_labels_open_no_crash_step_at_w_src3 show False by blast
qed

lemma I_relay_labels_open_not_running_image_faithful:
  "\<not> running_image_faithful I_relay_labels_open"
proof
  assume rif: "running_image_faithful I_relay_labels_open"
  have run: "exec_status (dwi_state I_relay_labels_open w_src3) = Running"
    by (simp add: w_src3_running)
  have le: "ec3 \<le> exec_finish (dwi_state I_relay_labels_open w_src3)"
    by (simp add: w_src3_fields src_le_refl src_le_eq_less_eq)
  from rif I_relay_labels_open_reaches_w_src3 run le
  have "\<not> mismatch_at (proto_of_exec_at (dwi_state I_relay_labels_open w_src3) ec3) ec3 0"
    by (simp add: running_image_faithful_def)
  moreover have
    "mismatch_at (proto_of_exec_at (dwi_state I_relay_labels_open w_src3) ec3) ec3 0"
    by (simp add: w_src3_mismatch_ec3)
  ultimately show False by simp
qed

text \<open>Kill-test, negative half: safe by a genuine no-observable-bad-crash
  argument.  Every reachable state is @{term Running} (the initial state is
  Running and every admitted step lands in one of the four Running literals), so
  @{const observable_mismatch} --- which demands @{term "Crashed c"} --- is
  unsatisfiable on reachable states.  Safety is earned by the absence of a
  crash, not by the absence of Running states.\<close>

lemma I_relay_labels_open_step_target_running:
  assumes "dwi_step I_relay_labels_open s a s'"
  shows "exec_status s' = Running"
  using assms
  by (auto simp: I_relay_labels_open_step_iff
                 w_src2_def w_enq2_def w_down2_def w_src3_def
                 w0_def initial_exec_state_def)

lemma I_relay_labels_open_reachable_running_gen:
  assumes "dwi_trace I t xs u"
  shows "I = I_relay_labels_open \<longrightarrow> exec_status t = Running \<longrightarrow> exec_status u = Running"
  using assms
proof (induction rule: dwi_trace.induct)
  case (dwi_trace_refl I s)
  show ?case by simp
next
  case (dwi_trace_step I s a s' as s'')
  show ?case
  proof (intro impI)
    assume Ieq: "I = I_relay_labels_open" and run_s: "exec_status s = Running"
    from dwi_trace_step.hyps(1) Ieq
    have "dwi_step I_relay_labels_open s a s'" by simp
    then have run_s': "exec_status s' = Running"
      by (rule I_relay_labels_open_step_target_running)
    from dwi_trace_step.IH Ieq run_s'
    show "exec_status s'' = Running" by blast
  qed
qed

lemma I_relay_labels_open_reachable_running:
  assumes "dwi_trace I_relay_labels_open (dwi_initial I_relay_labels_open) xs s"
  shows "exec_status s = Running"
proof -
  have "exec_status (dwi_initial I_relay_labels_open) = Running"
    by (simp add: w0_def initial_exec_state_def)
  with I_relay_labels_open_reachable_running_gen[OF assms]
  show ?thesis by simp
qed

lemma I_relay_labels_open_safe:
  "\<not> implementation_has_reachable_observable_bad_crash I_relay_labels_open"
proof
  assume "implementation_has_reachable_observable_bad_crash I_relay_labels_open"
  then obtain xs c k s where
    roc: "reachable_observable_bad_crash I_relay_labels_open xs c k s"
    by (auto simp: implementation_has_reachable_observable_bad_crash_def)
  from roc have tr: "dwi_trace I_relay_labels_open (dwi_initial I_relay_labels_open) xs s"
      and obs: "observable_mismatch (dwi_state I_relay_labels_open s) c k"
    by (auto simp: reachable_observable_bad_crash_def)
  have run: "exec_status s = Running"
    by (rule I_relay_labels_open_reachable_running[OF tr])
  from obs have "exec_status s = Crashed c"
    by (simp add: observable_mismatch_def)
  with run show False by simp
qed

text \<open>Headline: crash-closure is load-bearing.  With crash-closure dropped, the
  forward implication of @{thm safe_iff_running_image_faithful} fails ---
  non-vacuously, at a genuine reachable Running scoped mismatch at the loaded
  frontier @{const ec3}.\<close>

theorem crash_closed_is_load_bearing:
  "dwi_refines_exec I_relay_labels_open
 \<and> exec_status (dwi_state I_relay_labels_open (dwi_initial I_relay_labels_open)) = Running
 \<and> \<not> crash_closed_implementation I_relay_labels_open
 \<and> \<not> implementation_has_reachable_observable_bad_crash I_relay_labels_open
 \<and> \<not> running_image_faithful I_relay_labels_open"
  by (intro conjI)
     (rule I_relay_labels_open_refines_exec,
      rule I_relay_labels_open_start_running,
      rule I_relay_labels_open_not_crash_closed,
      rule I_relay_labels_open_safe,
      rule I_relay_labels_open_not_running_image_faithful)

text \<open>Corollary in the pearl's phrasing: on the safe side of
  @{thm safe_iff_running_image_faithful}, dropping crash-closure admits a
  witness that is safe yet not faithful, so the forward direction is not
  derivable from refinement and Running-start alone.\<close>

corollary crash_closed_drop_breaks_forward:
  "\<not> (\<forall>I :: ((nat,nat) dw_exec_state, nat, nat) dual_write_implementation.
        dwi_refines_exec I
      \<and> exec_status (dwi_state I (dwi_initial I)) = Running
      \<and> \<not> implementation_has_reachable_observable_bad_crash I
      \<longrightarrow> running_image_faithful I)"
  using crash_closed_is_load_bearing by blast


subsection \<open>Witness two: refinement is structurally required\<close>

text \<open>We reuse the landed non-refining negative control verbatim:
  @{const sf_audit_initial} is @{term "initial_exec_state [0 \<mapsto> 1] {0} ec3"}
  (Running, base @{term "[0 \<mapsto> 1]"}, scope @{term "{0::nat}"}, finish
  @{const ec3}); @{const sf_non_refining_implementation} has identity state map
  and step relation @{const dw_exec_step} plus the single extra self-loop
  @{term "(sf_audit_initial, Recover, sf_audit_initial)"} (which breaks
  refinement, since @{const Recover} needs a Crashed state); and
  @{const audit_update} is @{term "Update 0 2"}.\<close>

definition sf_non_refining_run_state :: "(nat, nat) dw_exec_state"
where
  "sf_non_refining_run_state = sf_audit_initial\<lparr>exec_src_hist := [(ec1, audit_update)]\<rparr>"

definition sf_non_refining_crash_state :: "(nat, nat) dw_exec_state"
where
  "sf_non_refining_crash_state = sf_non_refining_run_state\<lparr>exec_status := Crashed ec1\<rparr>"

lemma sf_non_refining_run_state_fields [simp]:
  "exec_status sf_non_refining_run_state = Running"
  "exec_base sf_non_refining_run_state = [0 \<mapsto> 1]"
  "exec_scope sf_non_refining_run_state = {0}"
  "exec_finish sf_non_refining_run_state = ec3"
  "exec_src_hist sf_non_refining_run_state = [(ec1, audit_update)]"
  "exec_down_hist sf_non_refining_run_state = []"
  by (simp_all add: sf_non_refining_run_state_def sf_audit_initial_def initial_exec_state_def)

lemma sf_non_refining_crash_state_fields [simp]:
  "exec_status sf_non_refining_crash_state = Crashed ec1"
  "exec_base sf_non_refining_crash_state = [0 \<mapsto> 1]"
  "exec_scope sf_non_refining_crash_state = {0}"
  "exec_finish sf_non_refining_crash_state = ec3"
  "exec_src_hist sf_non_refining_crash_state = [(ec1, audit_update)]"
  "exec_down_hist sf_non_refining_crash_state = []"
  by (simp_all add: sf_non_refining_crash_state_def sf_non_refining_run_state_def
                    sf_audit_initial_def initial_exec_state_def)

text \<open>The scoped mismatch at @{const ec1}, shared by the running and crashed
  states (@{const proto_of_exec_at} ignores the status field, so both states
  share their proto at @{const ec1}).\<close>

lemma sf_non_refining_run_mismatch_ec1:
  "mismatch_at (proto_of_exec_at sf_non_refining_run_state ec1) ec1 0"
  by (simp add: sf_non_refining_run_state_def sf_audit_initial_def audit_update_def
                mismatch_at_def proto_of_exec_at_def store2_of_exec_def
                log_image_def restrict_def initial_exec_state_def
                Src_single_event_at_key ec_defs)

lemma sf_non_refining_crash_proto_eq_run_proto:
  "proto_of_exec_at sf_non_refining_crash_state ec1 = proto_of_exec_at sf_non_refining_run_state ec1"
  by (simp add: sf_non_refining_crash_state_def proto_of_exec_at_status_update)

lemma sf_non_refining_crash_mismatch_ec1:
  "mismatch_at (proto_of_exec_at sf_non_refining_crash_state ec1) ec1 0"
  using sf_non_refining_run_mismatch_ec1 by (simp add: sf_non_refining_crash_proto_eq_run_proto)

text \<open>Reachability of the two states under the non-refining control: both
  admitted steps are ordinary @{const dw_exec_step} transitions inhabiting the
  left disjunct of the control's step relation; the @{const Recover} self-loop
  is never used.\<close>

lemma sf_non_refining_step_do_source:
  "dwi_step sf_non_refining_implementation sf_audit_initial
     (DoSource ec1 audit_update) sf_non_refining_run_state"
proof -
  have "dw_exec_step sf_audit_initial (DoSource ec1 audit_update)
          (sf_audit_initial\<lparr>exec_src_hist
             := exec_src_hist sf_audit_initial @ [(ec1, audit_update)]\<rparr>)"
    by (rule dw_exec_step.do_source)
       (simp add: sf_audit_initial_def initial_exec_state_def)
  moreover have
    "sf_audit_initial\<lparr>exec_src_hist
        := exec_src_hist sf_audit_initial @ [(ec1, audit_update)]\<rparr>
     = sf_non_refining_run_state"
    by (simp add: sf_non_refining_run_state_def sf_audit_initial_def initial_exec_state_def)
  ultimately show ?thesis
    by (simp add: sf_non_refining_implementation_def)
qed

lemma sf_non_refining_step_crash:
  "dwi_step sf_non_refining_implementation sf_non_refining_run_state
     (Crash ec1) sf_non_refining_crash_state"
proof -
  have "dw_exec_step sf_non_refining_run_state (Crash ec1)
          (sf_non_refining_run_state\<lparr>exec_status := Crashed ec1\<rparr>)"
    by (rule dw_exec_step.crash) simp
  thus ?thesis
    by (simp add: sf_non_refining_implementation_def sf_non_refining_crash_state_def)
qed

lemma sf_non_refining_run_reachable:
  "dwi_trace sf_non_refining_implementation
     (dwi_initial sf_non_refining_implementation)
     [DoSource ec1 audit_update] sf_non_refining_run_state"
proof -
  have init: "dwi_initial sf_non_refining_implementation = sf_audit_initial"
    by (simp add: sf_non_refining_implementation_def)
  show ?thesis
    unfolding init
    by (rule dwi_trace.dwi_trace_step[OF sf_non_refining_step_do_source],
        rule dwi_trace.dwi_trace_refl)
qed

lemma sf_non_refining_crash_reachable:
  "dwi_trace sf_non_refining_implementation
     (dwi_initial sf_non_refining_implementation)
     [DoSource ec1 audit_update, Crash ec1] sf_non_refining_crash_state"
proof -
  have init: "dwi_initial sf_non_refining_implementation = sf_audit_initial"
    by (simp add: sf_non_refining_implementation_def)
  show ?thesis
    unfolding init
    by (rule dwi_trace.dwi_trace_step[OF sf_non_refining_step_do_source],
        rule dwi_trace.dwi_trace_step[OF sf_non_refining_step_crash],
        rule dwi_trace.dwi_trace_refl)
qed

text \<open>The control is genuinely non-refining, re-exported from the landed
  negative control through the definitional alias @{thm sf_refines_def}.\<close>

lemma sf_non_refining_not_refines:
  "\<not> dwi_refines_exec sf_non_refining_implementation"
  using source_first_refinement_clause_negative_control
  by (simp add: sf_refines_def)

text \<open>The control satisfies the other two premises, isolating refinement as the
  sole violated hypothesis of the converse domain.\<close>

lemma sf_non_refining_crash_closed:
  "crash_closed_implementation sf_non_refining_implementation"
  by (auto simp: crash_closed_implementation_def
                 sf_non_refining_implementation_def
           intro: dw_exec_step.crash)

lemma sf_non_refining_start_running:
  "exec_status (dwi_state sf_non_refining_implementation
                  (dwi_initial sf_non_refining_implementation)) = Running"
  by (simp add: sf_non_refining_implementation_def
                sf_audit_initial_def initial_exec_state_def)

text \<open>Both sides of the biconditional are false on the control.  Unsafe: the
  crash trace reaches @{const sf_non_refining_crash_state}, an observable bad crash at
  @{term "(ec1, 0)"} (the divergence conjunct follows from
  @{thm observable_mismatch_imp_diverges}).\<close>

lemma ec1_le_ec3': "ec1 \<le> ec3"
  using ec1_le_ec3 by (simp add: src_le_eq_less_eq)

lemma sf_non_refining_observable_mismatch:
  "observable_mismatch sf_non_refining_crash_state ec1 0"
  by (simp add: observable_mismatch_def sf_non_refining_crash_state_fields
                sf_non_refining_crash_mismatch_ec1 ec1_le_ec3')

lemma sf_non_refining_unsafe:
  "implementation_has_reachable_observable_bad_crash sf_non_refining_implementation"
proof -
  have obs: "observable_mismatch
               (dwi_state sf_non_refining_implementation sf_non_refining_crash_state) ec1 0"
    by (simp add: sf_non_refining_implementation_def sf_non_refining_observable_mismatch)
  have div: "diverges (proto_of_exec_at
               (dwi_state sf_non_refining_implementation sf_non_refining_crash_state) ec1) ec1"
    by (rule observable_mismatch_imp_diverges[OF obs])
  have "reachable_observable_bad_crash sf_non_refining_implementation
          [DoSource ec1 audit_update, Crash ec1] ec1 0 sf_non_refining_crash_state"
    unfolding reachable_observable_bad_crash_def
    using sf_non_refining_crash_reachable obs div by blast
  thus ?thesis
    by (auto simp: implementation_has_reachable_observable_bad_crash_def)
qed

text \<open>Not faithful: the crash-free prefix reaches the Running state
  @{const sf_non_refining_run_state}, in range at @{const ec1}, carrying the same scoped
  mismatch.\<close>

lemma sf_non_refining_not_faithful:
  "\<not> running_image_faithful sf_non_refining_implementation"
proof
  assume rif: "running_image_faithful sf_non_refining_implementation"
  have run: "exec_status
               (dwi_state sf_non_refining_implementation sf_non_refining_run_state) = Running"
    by (simp add: sf_non_refining_implementation_def)
  have le: "ec1 \<le> exec_finish
               (dwi_state sf_non_refining_implementation sf_non_refining_run_state)"
    by (simp add: sf_non_refining_implementation_def ec1_le_ec3')
  from rif sf_non_refining_run_reachable run le
  have "\<not> mismatch_at (proto_of_exec_at
           (dwi_state sf_non_refining_implementation sf_non_refining_run_state) ec1) ec1 0"
    by (simp add: running_image_faithful_def)
  moreover have
    "mismatch_at (proto_of_exec_at
        (dwi_state sf_non_refining_implementation sf_non_refining_run_state) ec1) ec1 0"
    using sf_non_refining_run_mismatch_ec1
    by (simp add: sf_non_refining_implementation_def)
  ultimately show False by simp
qed

text \<open>The biconditional holds on the control: both sides are false, so it is
  truth-functionally true.  This genuinely diverging non-refining control does
  not falsify @{thm safe_iff_running_image_faithful}; the sibling theory
  @{text Dual_Write_Refinement_Tightness} exhibits non-refining
  implementations that do.\<close>

theorem sf_non_refining_biconditional_holds:
  "(\<not> implementation_has_reachable_observable_bad_crash sf_non_refining_implementation)
     \<longleftrightarrow> running_image_faithful sf_non_refining_implementation"
  using sf_non_refining_unsafe sf_non_refining_not_faithful by blast

text \<open>Headline: the non-refining class contains a non-falsifying member.  Here
  is a crash-closed, Running-start, non-refining implementation isolating
  refinement as the sole violated premise; the biconditional still holds on
  it, truth-functionally, because both sides are false.  So dropping
  refinement does not falsify the statement on EVERY implementation.  This is
  not a non-witnessability claim: the sibling theory
  @{text Dual_Write_Refinement_Tightness} exhibits non-refining
  implementations that DO falsify the biconditional, in both directions
  (@{text refinement_drop_falsifies_forward}: safe yet not image-faithful;
  @{text refinement_drop_falsifies_backward}: image-faithful yet unsafe).
  Refinement is therefore load-bearing for the statement itself, not merely
  for the proof; the theorem below,
  @{text refining_structurally_required_in_converse}, records the
  non-falsifying control.\<close>

theorem refining_structurally_required_in_converse:
  "\<not> dwi_refines_exec sf_non_refining_implementation
 \<and> crash_closed_implementation sf_non_refining_implementation
 \<and> exec_status (dwi_state sf_non_refining_implementation
                 (dwi_initial sf_non_refining_implementation)) = Running
 \<and> ((\<not> implementation_has_reachable_observable_bad_crash sf_non_refining_implementation)
      \<longleftrightarrow> running_image_faithful sf_non_refining_implementation)"
  using sf_non_refining_not_refines sf_non_refining_crash_closed
        sf_non_refining_start_running sf_non_refining_biconditional_holds
  by blast

text \<open>Companion strengthening: the failure of both sides is real (non-vacuous).
  The control reaches an actual reachable Running scoped mismatch at the loaded
  frontier @{const ec1} (so it is genuinely not faithful) and an actual
  reachable observable bad crash (so it is genuinely not safe).\<close>

theorem sf_non_refining_both_sides_genuinely_false:
  "implementation_has_reachable_observable_bad_crash sf_non_refining_implementation
 \<and> \<not> running_image_faithful sf_non_refining_implementation
 \<and> dwi_trace sf_non_refining_implementation
     (dwi_initial sf_non_refining_implementation)
     [DoSource ec1 audit_update] sf_non_refining_run_state
 \<and> exec_status (dwi_state sf_non_refining_implementation sf_non_refining_run_state) = Running
 \<and> mismatch_at (proto_of_exec_at
     (dwi_state sf_non_refining_implementation sf_non_refining_run_state) ec1) ec1 0"
  using sf_non_refining_unsafe sf_non_refining_not_faithful sf_non_refining_run_reachable
        sf_non_refining_run_mismatch_ec1
  by (simp add: sf_non_refining_implementation_def)

end
