(*  Title:       Dual_Write_Refinement_Tightness.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Refinement-premise tightness for the image-level crash-safety
    characterization safe_iff_running_image_faithful (Dual_Write_Converse.thy).
    This additive theory witnesses the refinement premise dwi_refines_exec in
    BOTH directions --- forward (safe yet unfaithful) and backward (faithful
    yet unsafe) --- so each of the three premises of the characterization now
    carries a falsifying counterexample: crash-closure in
    Dual_Write_Premise_Tightness (crash_closed_is_load_bearing), Running-start
    in Dual_Write_Converse (running_start_is_load_bearing), and refinement
    here.  Premise tightness is thereby witnessed 3-of-3.

    Forward witness (safe yet unfaithful).  The unit-state implementation
    I_unit_crash maps its only state () to the loaded Running-mismatch state
    w_src3 (Dual_Write_Relay.thy) and admits exactly the Crash-labelled
    self-loops.  crash_closed_implementation asks only for the EXISTENCE of a
    Crash-labelled successor (Dual_Write_Execution.thy), never that the mapped
    successor be Crashed, so the label-level obligation is met by a
    state-no-op.  Without refinement the crash labels carry no semantics:
    every state (reachable or not) maps to the Running state w_src3, so
    observable_mismatch (which requires a Crashed status) is unsatisfiable
    and I_unit_crash is SAFE; yet w_src3 carries the loaded scoped mismatch
    at frontier ec3, so running_image_faithful FAILS already at the empty
    trace.  Hence with refinement the SOLE dropped premise, the forward
    direction of safe_iff_running_image_faithful is falsified.  The witness is
    repeated as I_exec_crash at the exact record instance of the corollary
    crash_closed_drop_breaks_forward (Dual_Write_Premise_Tightness.thy) to
    close any type-level escape.

    Backward witness (faithful yet unsafe).  The two-state implementation
    I_bool_crash starts at the pristine Running state w0 and jumps, by one
    Crash-labelled step that is not a dw_exec_step, to the loaded crashed
    state w_crash: running_image_faithful holds non-vacuously, yet the
    reachable image w_crash is an observable bad crash at frontier ec3.  So
    the BACKWARD direction is falsified with refinement the sole dropped
    premise as well.

    The Crash-labelled self-loop idiom is the entry's own: it mirrors the
    landed Recover self-loop control sf_non_refining_implementation in
    Dual_Write_Operational_Definition_Audit.thy.

    Every reused fact is landed in this development.  This theory adds no
    axiom, sorry, or oracle.
*)

theory Dual_Write_Refinement_Tightness
  imports Dual_Write_Converse
begin

section \<open>The unit-state crash-label witness\<close>

definition I_unit_crash :: "(unit, nat, nat) dual_write_implementation" where
  "I_unit_crash =
     \<lparr> dwi_initial = (),
       dwi_step = (\<lambda>s a s'. \<exists>c. a = Crash c),
       dwi_state = (\<lambda>_. w_src3) \<rparr>"

lemma I_unit_crash_state [simp]: "dwi_state I_unit_crash s = w_src3"
  by (simp add: I_unit_crash_def)

lemma I_unit_crash_initial [simp]: "dwi_initial I_unit_crash = ()"
  by (simp add: I_unit_crash_def)

lemma I_unit_crash_step_iff:
  "dwi_step I_unit_crash s a s' \<longleftrightarrow> (\<exists>c. a = Crash c)"
  by (simp add: I_unit_crash_def)

subsection \<open>(a) Crash-closed: the label-level obligation is met by self-loops\<close>

lemma I_unit_crash_crash_closed: "crash_closed_implementation I_unit_crash"
  unfolding crash_closed_implementation_def
  by (auto simp: I_unit_crash_step_iff)

subsection \<open>(b) Running-start\<close>

lemma I_unit_crash_start_running:
  "exec_status (dwi_state I_unit_crash (dwi_initial I_unit_crash)) = Running"
  by (simp add: w_src3_running)

subsection \<open>(c) Not refining: the Crash-labelled self-loop maps to no
  execution step\<close>

lemma exec_crash_label_status:
  assumes "dw_exec_step s (Crash c) s'"
  shows "exec_status s' = Crashed c"
  using assms by (cases rule: dw_exec_step.cases) auto

lemma no_exec_crash_self_loop: "\<not> dw_exec_step w_src3 (Crash ec3) w_src3"
proof
  assume "dw_exec_step w_src3 (Crash ec3) w_src3"
  then have "exec_status w_src3 = Crashed ec3"
    by (rule exec_crash_label_status)
  with w_src3_running show False by simp
qed

lemma I_unit_crash_crash_step: "dwi_step I_unit_crash () (Crash ec3) ()"
  by (simp add: I_unit_crash_step_iff)

lemma I_unit_crash_not_refines: "\<not> dwi_refines_exec I_unit_crash"
proof
  assume "dwi_refines_exec I_unit_crash"
  then have "dw_exec_step (dwi_state I_unit_crash ()) (Crash ec3)
               (dwi_state I_unit_crash ())"
    using I_unit_crash_crash_step by (auto simp: dwi_refines_exec_def)
  then have "dw_exec_step w_src3 (Crash ec3) w_src3" by simp
  with no_exec_crash_self_loop show False by simp
qed

subsection \<open>(d) Safe: every state maps to the same Running state, so an
  observable bad crash is unsatisfiable on any state, reachable or not\<close>

lemma I_unit_crash_no_observable_mismatch:
  "\<not> observable_mismatch (dwi_state I_unit_crash s) c k"
proof
  assume "observable_mismatch (dwi_state I_unit_crash s) c k"
  then have "exec_status w_src3 = Crashed c"
    by (simp add: observable_mismatch_def)
  with w_src3_running show False by simp
qed

lemma I_unit_crash_safe:
  "\<not> implementation_has_reachable_observable_bad_crash I_unit_crash"
proof
  assume "implementation_has_reachable_observable_bad_crash I_unit_crash"
  then obtain xs c k s where
    "reachable_observable_bad_crash I_unit_crash xs c k s"
    by (auto simp: implementation_has_reachable_observable_bad_crash_def)
  then have "observable_mismatch (dwi_state I_unit_crash s) c k"
    by (simp add: reachable_observable_bad_crash_def)
  with I_unit_crash_no_observable_mismatch show False by blast
qed

subsection \<open>(e) Not running-image-faithful: the empty trace already sits at
  the loaded Running scoped mismatch at the loaded frontier\<close>

lemma I_unit_crash_not_faithful: "\<not> running_image_faithful I_unit_crash"
proof
  assume rif: "running_image_faithful I_unit_crash"
  have tr: "dwi_trace I_unit_crash (dwi_initial I_unit_crash) []
              (dwi_initial I_unit_crash)"
    by (rule dwi_trace.dwi_trace_refl)
  have run: "exec_status (dwi_state I_unit_crash (dwi_initial I_unit_crash))
               = Running"
    by (simp add: w_src3_running)
  have le: "ec3 \<le> exec_finish (dwi_state I_unit_crash (dwi_initial I_unit_crash))"
    by (simp add: w_src3_fields src_le_refl src_le_eq_less_eq)
  from rif tr run le
  have "\<not> mismatch_at
          (proto_of_exec_at (dwi_state I_unit_crash (dwi_initial I_unit_crash)) ec3)
          ec3 0"
    by (simp add: running_image_faithful_def)
  moreover have
    "mismatch_at
       (proto_of_exec_at (dwi_state I_unit_crash (dwi_initial I_unit_crash)) ec3)
       ec3 0"
    by (simp add: w_src3_mismatch_ec3)
  ultimately show False by simp
qed

section \<open>Headline: refinement IS counterexample-witnessable\<close>

text \<open>The safe-yet-unfaithful cell with refinement the sole violated premise
  is inhabited: the forward direction of @{thm safe_iff_running_image_faithful}
  fails with only the refinement hypothesis dropped.  Refinement is therefore
  counterexample-witnessable, not merely proof-essential.\<close>

theorem refinement_drop_falsifies_forward:
  "crash_closed_implementation I_unit_crash
 \<and> exec_status (dwi_state I_unit_crash (dwi_initial I_unit_crash)) = Running
 \<and> \<not> dwi_refines_exec I_unit_crash
 \<and> \<not> implementation_has_reachable_observable_bad_crash I_unit_crash
 \<and> \<not> running_image_faithful I_unit_crash"
  by (intro conjI)
     (rule I_unit_crash_crash_closed,
      rule I_unit_crash_start_running,
      rule I_unit_crash_not_refines,
      rule I_unit_crash_safe,
      rule I_unit_crash_not_faithful)

corollary refinement_drop_breaks_forward:
  "\<not> (\<forall>I :: (unit, nat, nat) dual_write_implementation.
        crash_closed_implementation I
      \<and> exec_status (dwi_state I (dwi_initial I)) = Running
      \<and> \<not> implementation_has_reachable_observable_bad_crash I
      \<longrightarrow> running_image_faithful I)"
  using refinement_drop_falsifies_forward by blast

corollary refinement_drop_falsifies_biconditional:
  "\<not> ((\<not> implementation_has_reachable_observable_bad_crash I_unit_crash)
        \<longleftrightarrow> running_image_faithful I_unit_crash)"
  using refinement_drop_falsifies_forward by blast

section \<open>The same witness at the landed corollary's state type\<close>

text \<open>The landed corollary \<open>crash_closed_drop_breaks_forward\<close>
  (\<open>Dual_Write_Premise_Tightness\<close>) is stated at state type
  @{typ "(nat, nat) dw_exec_state"}.  To close any type-level escape, the same
  crash-label witness is repeated at exactly that record instance: the
  abstraction map is constantly @{const w_src3} and the step relation again
  admits exactly the Crash labels.\<close>

definition I_exec_crash
  :: "((nat, nat) dw_exec_state, nat, nat) dual_write_implementation"
where
  "I_exec_crash =
     \<lparr> dwi_initial = w_src3,
       dwi_step = (\<lambda>s a s'. \<exists>c. a = Crash c),
       dwi_state = (\<lambda>_. w_src3) \<rparr>"

lemma I_exec_crash_state [simp]: "dwi_state I_exec_crash s = w_src3"
  by (simp add: I_exec_crash_def)

lemma I_exec_crash_initial [simp]: "dwi_initial I_exec_crash = w_src3"
  by (simp add: I_exec_crash_def)

lemma I_exec_crash_step_iff:
  "dwi_step I_exec_crash s a s' \<longleftrightarrow> (\<exists>c. a = Crash c)"
  by (simp add: I_exec_crash_def)

lemma I_exec_crash_crash_closed: "crash_closed_implementation I_exec_crash"
  unfolding crash_closed_implementation_def
  by (auto simp: I_exec_crash_step_iff)

lemma I_exec_crash_start_running:
  "exec_status (dwi_state I_exec_crash (dwi_initial I_exec_crash)) = Running"
  by (simp add: w_src3_running)

lemma I_exec_crash_not_refines: "\<not> dwi_refines_exec I_exec_crash"
proof
  assume "dwi_refines_exec I_exec_crash"
  moreover have "dwi_step I_exec_crash w_src3 (Crash ec3) w_src3"
    by (simp add: I_exec_crash_step_iff)
  ultimately have "dw_exec_step w_src3 (Crash ec3) w_src3"
    by (auto simp: dwi_refines_exec_def)
  with no_exec_crash_self_loop show False by simp
qed

lemma I_exec_crash_safe:
  "\<not> implementation_has_reachable_observable_bad_crash I_exec_crash"
proof
  assume "implementation_has_reachable_observable_bad_crash I_exec_crash"
  then obtain xs c k s where
    "reachable_observable_bad_crash I_exec_crash xs c k s"
    by (auto simp: implementation_has_reachable_observable_bad_crash_def)
  then have "observable_mismatch (dwi_state I_exec_crash s) c k"
    by (simp add: reachable_observable_bad_crash_def)
  then have "exec_status w_src3 = Crashed c"
    by (simp add: observable_mismatch_def)
  with w_src3_running show False by simp
qed

lemma I_exec_crash_not_faithful: "\<not> running_image_faithful I_exec_crash"
proof
  assume rif: "running_image_faithful I_exec_crash"
  have tr: "dwi_trace I_exec_crash (dwi_initial I_exec_crash) []
              (dwi_initial I_exec_crash)"
    by (rule dwi_trace.dwi_trace_refl)
  have run: "exec_status (dwi_state I_exec_crash (dwi_initial I_exec_crash))
               = Running"
    by (simp add: w_src3_running)
  have le: "ec3 \<le> exec_finish (dwi_state I_exec_crash (dwi_initial I_exec_crash))"
    by (simp add: w_src3_fields src_le_refl src_le_eq_less_eq)
  from rif tr run le
  have "\<not> mismatch_at
          (proto_of_exec_at (dwi_state I_exec_crash (dwi_initial I_exec_crash)) ec3)
          ec3 0"
    by (simp add: running_image_faithful_def)
  moreover have
    "mismatch_at
       (proto_of_exec_at (dwi_state I_exec_crash (dwi_initial I_exec_crash)) ec3)
       ec3 0"
    by (simp add: w_src3_mismatch_ec3)
  ultimately show False by simp
qed

theorem refinement_drop_falsifies_forward_exec_type:
  "crash_closed_implementation I_exec_crash
 \<and> exec_status (dwi_state I_exec_crash (dwi_initial I_exec_crash)) = Running
 \<and> \<not> dwi_refines_exec I_exec_crash
 \<and> \<not> implementation_has_reachable_observable_bad_crash I_exec_crash
 \<and> \<not> running_image_faithful I_exec_crash"
  by (intro conjI)
     (rule I_exec_crash_crash_closed,
      rule I_exec_crash_start_running,
      rule I_exec_crash_not_refines,
      rule I_exec_crash_safe,
      rule I_exec_crash_not_faithful)

text \<open>Type-for-type negation counterpart of the landed corollary
  \<open>crash_closed_drop_breaks_forward\<close>: at the identical record instance,
  retaining crash-closure and Running-start while dropping only refinement
  no longer entails image-faithfulness.\<close>

corollary refinement_drop_breaks_forward_exec_type:
  "\<not> (\<forall>I :: ((nat, nat) dw_exec_state, nat, nat) dual_write_implementation.
        crash_closed_implementation I
      \<and> exec_status (dwi_state I (dwi_initial I)) = Running
      \<and> \<not> implementation_has_reachable_observable_bad_crash I
      \<longrightarrow> running_image_faithful I)"
  using refinement_drop_falsifies_forward_exec_type by blast

section \<open>The backward direction falls too: faithful yet unsafe\<close>

text \<open>A two-state witness at state type @{typ bool}: the initial state maps to
  the pristine Running state @{const w0} (whose source and downstream histories
  are both empty over the same base, so NO frontier carries a scoped mismatch),
  and the sole step --- again a Crash-labelled transition that is not a
  @{const dw_exec_step}, since @{const w_crash} differs from @{const w0} in its
  histories, not just its status --- jumps to the loaded crashed state
  @{const w_crash}.  Crash-closure holds (the only Running-imaged state offers
  the Crash-labelled step), Running-start holds, refinement fails, and:
  running-image-faithfulness HOLDS non-vacuously (a reachable Running state is
  interrogated at every frontier and never mismatches) while the
  implementation is UNSAFE (the reachable image @{const w_crash} is an
  observable bad crash at the loaded frontier @{const ec3}).  So the BACKWARD
  direction of @{thm safe_iff_running_image_faithful} is also falsified with
  refinement the sole dropped premise.\<close>

definition I_bool_crash :: "(bool, nat, nat) dual_write_implementation" where
  "I_bool_crash =
     \<lparr> dwi_initial = False,
       dwi_step = (\<lambda>s a s'. s' = True \<and> (\<exists>c. a = Crash c)),
       dwi_state = (\<lambda>s. if s then w_crash else w0) \<rparr>"

lemma I_bool_crash_state [simp]:
  "dwi_state I_bool_crash s = (if s then w_crash else w0)"
  by (simp add: I_bool_crash_def)

lemma I_bool_crash_initial [simp]: "dwi_initial I_bool_crash = False"
  by (simp add: I_bool_crash_def)

lemma I_bool_crash_step_iff:
  "dwi_step I_bool_crash s a s' \<longleftrightarrow> s' = True \<and> (\<exists>c. a = Crash c)"
  by (simp add: I_bool_crash_def)

lemma I_bool_crash_crash_closed: "crash_closed_implementation I_bool_crash"
  unfolding crash_closed_implementation_def
  by (auto simp: I_bool_crash_step_iff)

lemma I_bool_crash_start_running:
  "exec_status (dwi_state I_bool_crash (dwi_initial I_bool_crash)) = Running"
  by (simp add: w0_def initial_exec_state_def)

text \<open>Not refining: the admitted @{term "Crash ec3"} step from the pristine
  state jumps to @{const w_crash}, which rewrites the HISTORIES, while the
  @{const dw_exec_step} crash rule only rewrites the status field.\<close>

lemma exec_crash_label_src_hist:
  assumes "dw_exec_step s (Crash c) s'"
  shows "exec_src_hist s' = exec_src_hist s"
  using assms by (cases rule: dw_exec_step.cases) auto

lemma I_bool_crash_not_refines: "\<not> dwi_refines_exec I_bool_crash"
proof
  assume ref: "dwi_refines_exec I_bool_crash"
  have step: "dwi_step I_bool_crash False (Crash ec3) True"
    by (simp add: I_bool_crash_step_iff)
  from ref step
  have "dw_exec_step (dwi_state I_bool_crash False) (Crash ec3)
          (dwi_state I_bool_crash True)"
    unfolding dwi_refines_exec_def by blast
  then have "dw_exec_step w0 (Crash ec3) w_crash"
    by simp
  then have "exec_src_hist w_crash = exec_src_hist w0"
    by (rule exec_crash_label_src_hist)
  then show False
    by (simp add: w_crash_fields w0_def initial_exec_state_def)
qed

text \<open>Faithful, non-vacuously: the only Running-imaged state is the pristine
  @{const w0}, whose two histories are both empty over the same base, so
  @{const store2_of_exec} and @{const log_image} agree at every frontier.\<close>

lemma w0_no_mismatch: "\<not> mismatch_at (proto_of_exec_at w0 c) c k"
  by (simp add: mismatch_at_def proto_of_exec_at_def log_image_def
                store2_of_exec_def restrict_def w0_def initial_exec_state_def)

lemma I_bool_crash_faithful: "running_image_faithful I_bool_crash"
  unfolding running_image_faithful_def
proof (intro allI impI, elim conjE)
  fix xs s c k
  assume "exec_status (dwi_state I_bool_crash s) = Running"
  then have "dwi_state I_bool_crash s = w0"
    by (cases s) (simp_all add: w_crash_fields)
  then show "\<not> mismatch_at (proto_of_exec_at (dwi_state I_bool_crash s) c) c k"
    by (simp add: w0_no_mismatch)
qed

text \<open>Unsafe, non-vacuously: one Crash-labelled step reaches the state imaged
  at @{const w_crash}, the landed observable bad crash at frontier
  @{const ec3}.\<close>

lemma I_bool_crash_true_reachable:
  "dwi_trace I_bool_crash (dwi_initial I_bool_crash) [Crash ec3] True"
proof -
  have "dwi_step I_bool_crash False (Crash ec3) True"
    by (simp add: I_bool_crash_step_iff)
  then show ?thesis
    by (auto intro: dwi_trace.dwi_trace_step dwi_trace.dwi_trace_refl)
qed

lemma I_bool_crash_unsafe:
  "implementation_has_reachable_observable_bad_crash I_bool_crash"
proof -
  have obs: "observable_mismatch (dwi_state I_bool_crash True) ec3 0"
    by (simp add: w_crash_observable_mismatch_at_ec3)
  have div: "diverges (proto_of_exec_at (dwi_state I_bool_crash True) ec3) ec3"
    by (rule observable_mismatch_imp_diverges[OF obs])
  have "reachable_observable_bad_crash I_bool_crash [Crash ec3] ec3 0 True"
    unfolding reachable_observable_bad_crash_def
    using I_bool_crash_true_reachable obs div by blast
  then show ?thesis
    by (auto simp: implementation_has_reachable_observable_bad_crash_def)
qed

theorem refinement_drop_falsifies_backward:
  "crash_closed_implementation I_bool_crash
 \<and> exec_status (dwi_state I_bool_crash (dwi_initial I_bool_crash)) = Running
 \<and> \<not> dwi_refines_exec I_bool_crash
 \<and> running_image_faithful I_bool_crash
 \<and> implementation_has_reachable_observable_bad_crash I_bool_crash"
  by (intro conjI)
     (rule I_bool_crash_crash_closed,
      rule I_bool_crash_start_running,
      rule I_bool_crash_not_refines,
      rule I_bool_crash_faithful,
      rule I_bool_crash_unsafe)

text \<open>Summary: with refinement the SOLE dropped premise, BOTH directions of
  @{thm safe_iff_running_image_faithful} admit falsifying witnesses --- the
  forward direction by @{thm refinement_drop_falsifies_forward} (safe yet
  unfaithful) and the backward direction by
  @{thm refinement_drop_falsifies_backward} (faithful yet unsafe).  The
  refinement premise is therefore counterexample-witnessable in the strongest
  sense, and the premise-tightness triptych is witnessed 3-of-3.\<close>

end
