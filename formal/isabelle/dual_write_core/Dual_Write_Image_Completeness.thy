(*  Title:       Dual_Write_Image_Completeness.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Image completeness for crash-safety: the durability axis.

    The image-level characterization safe_iff_running_image_faithful
    (Dual_Write_Converse) settles crash-safety through the scoped source-log
    image alone.  A natural question is whether a STREAM-level notion --- one
    that inspects the delivered CDC stream as a list, its order, its
    acknowledgement state, or its visibility frontier --- carries a second,
    genuinely stronger crash-safety characterization.  It does not: crash-safety
    depends only on the scoped image.

    The general reason is structural and is recorded here as
    observable_mismatch_depends_only_on_down_image: observable_mismatch reads the
    delivered history exclusively through store2_of_exec = Src (exec_down_hist),
    so two states with the same scoped image (at fixed base, source history,
    scope, finish, and status) receive the SAME observable verdict, however their
    delivered lists differ.

    This theory instantiates that principle on the DURABILITY axis --- the
    sharpest case, because acknowledgement reads exec_acked, a field the image
    (Src) never touches, yet the notion still collapses.  "Acknowledged data is
    never wrong'' (implementation_acked_durable: no reachable
    acked_observable_mismatch) is (i) implied by image crash-safety, (ii)
    strictly weaker than it and vacuously satisfiable by never acknowledging,
    (iii) violated only where the image is already unsafe, and (iv) blind to the
    list/stream seam of history_level_converse_false.  No two-sided law beyond
    the image survives.

    The ORDER axis is treated in the companion theory
    Dual_Write_Order_Completeness.  Adds no axiom, sorry, or oracle; headline
    facts are certified oracle-free by a separate build gate.
*)

theory Dual_Write_Image_Completeness
  imports Dual_Write_Converse
begin

section \<open>Crash-safety depends only on the scoped image\<close>

text \<open>The general completeness principle.  @{const observable_mismatch} enters
  the delivered history only through @{const store2_of_exec}, which is
  @{const Src} of @{const exec_down_hist}.  Hence two states that agree on the
  scoped image (and on base, source history, scope, finish, status) agree on
  every @{const observable_mismatch}: any change to the delivered stream that
  preserves the scoped image --- reordering, a different list, extra
  out-of-scope events --- is invisible to crash-safety.\<close>

lemma observable_mismatch_depends_only_on_down_image:
  assumes eq_img:
      "\<And>f. Src (exec_base s) (exec_down_hist s) f
          = Src (exec_base s') (exec_down_hist s') f"
    and eq_base:   "exec_base s'    = exec_base s"
    and eq_src:    "exec_src_hist s'  = exec_src_hist s"
    and eq_scope:  "exec_scope s'   = exec_scope s"
    and eq_fin:    "exec_finish s'   = exec_finish s"
    and eq_status: "exec_status s'   = exec_status s"
  shows "observable_mismatch s' c k \<longleftrightarrow> observable_mismatch s c k"
proof -
  have proto: "proto_of_exec_at s' c = proto_of_exec_at s c"
    by (simp add: proto_of_exec_at_def store2_of_exec_def
                  eq_base eq_src eq_scope eq_fin eq_img fun_eq_iff)
  show ?thesis
    by (simp add: observable_mismatch_def proto eq_status eq_fin)
qed


section \<open>Acknowledged-durability as an implementation-level safety notion\<close>

text \<open>``Acknowledged data is never wrong'': no reachable state exhibits an
  @{const acked_observable_mismatch}.  This lifts the state predicate
  @{const acked_observable_mismatch} to a whole-implementation property, in the
  shape of @{const implementation_has_reachable_observable_bad_crash}.\<close>

definition implementation_acked_durable
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "implementation_acked_durable I \<longleftrightarrow>
     (\<not> (\<exists>xs c k s.
            dwi_trace I (dwi_initial I) xs s
          \<and> acked_observable_mismatch (dwi_state I s) c k))"

text \<open>
  The strictness witness below uses an implementation-level no-ack relay, not
  a single unacknowledged state of the ack-capable relay.  Its transition
  relation is the ordinary relay label relation with @{const Ack} excluded.
\<close>

definition relay_no_ack_step
  :: "('k, 'v) dw_exec_state \<Rightarrow> ('k, 'v) dw_exec_label \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  "relay_no_ack_step s a s' \<longleftrightarrow>
     relay_step s a s' \<and> (\<forall>c e. a \<noteq> Ack c e)"

definition I_relay_no_ack
  :: "('k, 'v) dw_exec_state \<Rightarrow>
      (('k, 'v) dw_exec_state, 'k, 'v) dual_write_implementation"
where
  "I_relay_no_ack s0 =
     \<lparr>dwi_initial = s0,
      dwi_step = relay_no_ack_step,
      dwi_state = (\<lambda>s. s)\<rparr>"

lemma relay_no_ack_step_preserves_acked:
  assumes "relay_no_ack_step s a s'"
  shows "exec_acked s' = exec_acked s"
  using assms
  by (auto simp: relay_no_ack_step_def relay_step_def
           elim: dw_exec_step.cases)

lemma relay_no_ack_trace_preserves_acked:
  assumes trace: "dwi_trace I s xs s'"
      and Ieq: "I = I_relay_no_ack s0"
  shows "exec_acked s' = exec_acked s"
  using trace Ieq
proof (induction rule: dwi_trace.induct)
  case (dwi_trace_refl I s)
  show ?case by simp
next
  case (dwi_trace_step I s a s' as s'')
  have step: "relay_no_ack_step s a s'"
    using dwi_trace_step.hyps(1) dwi_trace_step.prems
    by (simp add: I_relay_no_ack_def)
  have one: "exec_acked s' = exec_acked s"
    by (rule relay_no_ack_step_preserves_acked[OF step])
  have tail: "exec_acked s'' = exec_acked s'"
    by (rule dwi_trace_step.IH[OF dwi_trace_step.prems])
  show ?case using tail one by simp
qed

theorem I_relay_no_ack_acked_durable:
  assumes empty: "exec_acked s0 = []"
  shows "implementation_acked_durable (I_relay_no_ack s0)"
  unfolding implementation_acked_durable_def
proof (intro notI)
  assume "\<exists>xs c k s.
      dwi_trace (I_relay_no_ack s0) (dwi_initial (I_relay_no_ack s0)) xs s
    \<and> acked_observable_mismatch (dwi_state (I_relay_no_ack s0) s) c k"
  then obtain xs c k s where
      tr: "dwi_trace (I_relay_no_ack s0)
             (dwi_initial (I_relay_no_ack s0)) xs s"
      and bad:
        "acked_observable_mismatch (dwi_state (I_relay_no_ack s0) s) c k"
    by blast
  have init: "dwi_initial (I_relay_no_ack s0) = s0"
    by (simp add: I_relay_no_ack_def)
  have acked_empty: "exec_acked s = []"
    using relay_no_ack_trace_preserves_acked[OF tr refl] empty
    by (simp add: init)
  from bad show False
    by (simp add: I_relay_no_ack_def acked_observable_mismatch_def
                  acked_source_effect_at_def acked_empty)
qed


section \<open>Image crash-safety implies acknowledged-durability\<close>

text \<open>A reachable @{const acked_observable_mismatch} is a reachable
  @{const observable_mismatch} that @{const diverges}, i.e. a reachable
  observable bad crash.  Contrapositively, image crash-safety forces
  acknowledged-durability: the notion is a weakening of the proven image
  characterization, adding nothing on top.\<close>

lemma acked_observable_mismatch_imp_reachable_observable_bad_crash:
  assumes tr:  "dwi_trace I (dwi_initial I) xs s"
      and acked: "acked_observable_mismatch (dwi_state I s) c k"
  shows "reachable_observable_bad_crash I xs c k s"
  unfolding reachable_observable_bad_crash_def
  using tr
        acked_observable_mismatch_imp_observable_mismatch[OF acked]
        acked_observable_mismatch_imp_diverges[OF acked]
  by blast

theorem acked_durable_implied_by_image_safety:
  assumes safe: "\<not> implementation_has_reachable_observable_bad_crash I"
  shows "implementation_acked_durable I"
  unfolding implementation_acked_durable_def
proof (intro notI)
  assume "\<exists>xs c k s.
            dwi_trace I (dwi_initial I) xs s
          \<and> acked_observable_mismatch (dwi_state I s) c k"
  then obtain xs c k s where
      tr:    "dwi_trace I (dwi_initial I) xs s"
      and ac: "acked_observable_mismatch (dwi_state I s) c k"
    by blast
  have "reachable_observable_bad_crash I xs c k s"
    by (rule acked_observable_mismatch_imp_reachable_observable_bad_crash[OF tr ac])
  hence "implementation_has_reachable_observable_bad_crash I"
    unfolding implementation_has_reachable_observable_bad_crash_def by blast
  with safe show False ..
qed


section \<open>Strict weakness via a no-ack implementation\<close>

text \<open>The crash state @{const w_crash} never acknowledges, so its
  @{const exec_acked} is empty and @{term "\<not> acked_observable_mismatch w_crash ec3 0"}
  holds pointwise while @{const w_crash} is image-unsafe.  The state alone is
  not a strictness witness.  The lemmas following it prove that the complete
  reachable state space of @{const I_relay_no_ack} is acknowledgement-free and
  that this same implementation reaches the unsafe state.\<close>

lemma w_crash_exec_acked_empty: "exec_acked w_crash = []"
  by (simp add: w_crash_def w_src3_def w_down2_def w_enq2_def
                w_src2_def w0_def initial_exec_state_def)

lemma w_crash_no_acked_source_effect: "\<not> acked_source_effect_at w_crash ec3 0"
  by (simp add: acked_source_effect_at_def w_crash_exec_acked_empty)

theorem acked_durable_holds_at_w_crash: "\<not> acked_observable_mismatch w_crash ec3 0"
  by (rule no_acked_source_effect_at_no_acked_observable_mismatch
      [OF w_crash_no_acked_source_effect])

lemma relay_no_ack_dwi_stepI:
  assumes step: "relay_step s a s'"
      and no_ack: "\<forall>c e. a \<noteq> Ack c e"
  shows "dwi_step (I_relay_no_ack s0) s a s'"
  using step no_ack
  by (simp add: I_relay_no_ack_def relay_no_ack_step_def)

lemma w_src3_reachable_no_ack:
  "dwi_trace (I_relay_no_ack w0) (dwi_initial (I_relay_no_ack w0))
     [DoSource ec2 (Insert 0 7), EnqueueDownstream ec2 (Insert 0 7),
      DoDownstream ec2 (Insert 0 7), DoSource ec3 (Insert 0 9)]
     w_src3"
proof -
  have init: "dwi_initial (I_relay_no_ack w0) = w0"
    by (simp add: I_relay_no_ack_def)
  show ?thesis
    unfolding init
    by (rule dwi_trace.dwi_trace_step[
          OF relay_no_ack_dwi_stepI[OF w_step_src2]],
        simp,
        rule dwi_trace.dwi_trace_step[
          OF relay_no_ack_dwi_stepI[OF w_step_enq2]],
        simp,
        rule dwi_trace.dwi_trace_step[
          OF relay_no_ack_dwi_stepI[OF w_step_down2]],
        simp,
        rule dwi_trace.dwi_trace_step[
          OF relay_no_ack_dwi_stepI[OF w_step_src3]],
        simp,
        rule dwi_trace.dwi_trace_refl)
qed

lemma w_crash_reachable_no_ack:
  "dwi_trace (I_relay_no_ack w0) (dwi_initial (I_relay_no_ack w0))
     [DoSource ec2 (Insert 0 7), EnqueueDownstream ec2 (Insert 0 7),
      DoDownstream ec2 (Insert 0 7), DoSource ec3 (Insert 0 9), Crash ec3]
     w_crash"
proof -
  have init: "dwi_initial (I_relay_no_ack w0) = w0"
    by (simp add: I_relay_no_ack_def)
  show ?thesis
    unfolding init
    by (rule dwi_trace.dwi_trace_step[
          OF relay_no_ack_dwi_stepI[OF w_step_src2]],
        simp,
        rule dwi_trace.dwi_trace_step[
          OF relay_no_ack_dwi_stepI[OF w_step_enq2]],
        simp,
        rule dwi_trace.dwi_trace_step[
          OF relay_no_ack_dwi_stepI[OF w_step_down2]],
        simp,
        rule dwi_trace.dwi_trace_step[
          OF relay_no_ack_dwi_stepI[OF w_step_src3]],
        simp,
        rule dwi_trace.dwi_trace_step[
          OF relay_no_ack_dwi_stepI[OF w_step_crash]],
        simp,
        rule dwi_trace.dwi_trace_refl)
qed

lemma I_relay_no_ack_w0_acked_durable:
  "implementation_acked_durable (I_relay_no_ack w0)"
  by (rule I_relay_no_ack_acked_durable)
     (simp add: w0_def initial_exec_state_def)

lemma I_relay_no_ack_w0_unsafe:
  "implementation_has_reachable_observable_bad_crash (I_relay_no_ack w0)"
proof -
  have obs:
    "observable_mismatch (dwi_state (I_relay_no_ack w0) w_crash) ec3 0"
    by (simp add: I_relay_no_ack_def w_crash_observable_mismatch_at_ec3)
  have div:
    "diverges
      (proto_of_exec_at (dwi_state (I_relay_no_ack w0) w_crash) ec3) ec3"
    by (rule observable_mismatch_imp_diverges[OF obs])
  have "reachable_observable_bad_crash (I_relay_no_ack w0)
      [DoSource ec2 (Insert 0 7), EnqueueDownstream ec2 (Insert 0 7),
       DoDownstream ec2 (Insert 0 7), DoSource ec3 (Insert 0 9), Crash ec3]
      ec3 0 w_crash"
    unfolding reachable_observable_bad_crash_def
    using w_crash_reachable_no_ack obs div by blast
  then show ?thesis
    by (auto simp: implementation_has_reachable_observable_bad_crash_def)
qed

lemma I_relay_no_ack_w0_not_running_image_faithful:
  "\<not> running_image_faithful (I_relay_no_ack w0)"
proof
  assume faithful: "running_image_faithful (I_relay_no_ack w0)"
  have run: "exec_status (dwi_state (I_relay_no_ack w0) w_src3) = Running"
    by (simp add: I_relay_no_ack_def w_src3_running)
  have le:
    "ec3 \<le> exec_finish (dwi_state (I_relay_no_ack w0) w_src3)"
    by (simp add: I_relay_no_ack_def w_src3_fields
                  src_le_refl src_le_eq_less_eq)
  from faithful w_src3_reachable_no_ack run le
  have no_mismatch:
    "\<not> mismatch_at
      (proto_of_exec_at (dwi_state (I_relay_no_ack w0) w_src3) ec3) ec3 0"
    by (simp add: running_image_faithful_def)
  moreover have
    "mismatch_at
      (proto_of_exec_at (dwi_state (I_relay_no_ack w0) w_src3) ec3) ec3 0"
    using w_src3_mismatch_ec3 by (simp add: I_relay_no_ack_def)
  ultimately show False by simp
qed


section \<open>Every reachable violation is already an image bad crash\<close>

text \<open>The concrete source-first witness @{const stale_update_plan} reaches a
  state that both acknowledges the stale event and is image-unsafe there:
  @{const acked_observable_mismatch} and @{const observable_mismatch} hold at the
  same @{term "(c, k)"}.  There is no acknowledged-only hazard the image notion
  misses.\<close>

theorem acked_violation_is_image_unsafe:
  "\<exists>s c k tr.
      dw_exec_trace
        (initial_exec_state
          (plan_base stale_update_plan)
          (plan_scope stale_update_plan)
          (plan_finish stale_update_plan))
        tr s
    \<and> acked_observable_mismatch s c k
    \<and> observable_mismatch s c k
    \<and> diverges (proto_of_exec_at s c) c"
proof -
  from stale_update_plan_has_bad_crash_execution obtain s c k tr where
      "dw_exec_trace
         (initial_exec_state (plan_base stale_update_plan)
            (plan_scope stale_update_plan) (plan_finish stale_update_plan)) tr s"
      "acked_observable_mismatch s c k" "observable_mismatch s c k"
      "diverges (proto_of_exec_at s c) c"
    by blast
  thus ?thesis by blast
qed


section \<open>Seam blindness: durability cannot separate the history-level seam\<close>

text \<open>The @{thm history_level_converse_false} witness pairs two downstreams that
  are image-equal on the monitored scope yet are different lists.  Being
  image-equal, they agree on every @{const mismatch_at}, hence on
  @{const observable_mismatch}, hence --- at equal @{const exec_acked} --- on
  @{const acked_observable_mismatch}: the notion is blind to the list/stream
  seam.\<close>

theorem acked_durable_blind_to_history_seam:
  "Src (\<lambda>_::nat. None) anti_atomic_witness_src ec3 (0::nat)
     = Src (\<lambda>_. None) (replay_down_hist anti_atomic_witness_src {0} ec3) ec3 0
   \<and> anti_atomic_witness_src \<noteq> replay_down_hist anti_atomic_witness_src {0} ec3"
  by (rule history_level_converse_false)


section \<open>State-level vacuity is not implementation durability\<close>

text \<open>
  The unacknowledged crash control is pointwise vacuous even though it belongs
  to the ack-capable label projection.  This fact alone says nothing about the
  implementation-level property: that projection also has acknowledged bad
  executions.  The genuine strictness result instead uses
  @{const I_relay_no_ack}, whose entire reachable state space is proved
  acknowledgement-free above.
\<close>

theorem unacknowledged_crash_is_pointwise_vacuous:
  "dwi_trace (I_relay_labels w0) (dwi_initial (I_relay_labels w0))
     [DoSource ec2 (Insert 0 7), EnqueueDownstream ec2 (Insert 0 7),
      DoDownstream ec2 (Insert 0 7), DoSource ec3 (Insert 0 9),
      Crash ec3]
     w_crash
 \<and> \<not> acked_observable_mismatch w_crash ec3 0"
  by (intro conjI w_crash_reachable acked_durable_holds_at_w_crash)


section \<open>The assembled collapse statement\<close>

text \<open>Conjunct one is the collapse direction at full generality: EVERY
  image-safe implementation is acknowledged-durable
  (@{thm [source] acked_durable_implied_by_image_safety} under the binder), so
  acknowledged-durability adds nothing on top of image-safety.  Conjuncts two
  and three make the collapse strict at implementation level: one no-ack
  witness is acknowledged-durable yet image-unsafe, so the converse
  implication fails.  Conjunct four records that the same witness also fails
  the faithful side of the image characterization: acknowledged-durability is
  strictly weaker than both sides of
  @{thm [source] safe_iff_running_image_faithful}.\<close>

theorem acked_durability_is_strictly_weaker_than_image_safety:
  "(\<forall>I :: ('s, 'k, 'v) dual_write_implementation.
      \<not> implementation_has_reachable_observable_bad_crash I
      \<longrightarrow> implementation_acked_durable I)
 \<and> implementation_acked_durable (I_relay_no_ack w0)
 \<and> implementation_has_reachable_observable_bad_crash (I_relay_no_ack w0)
 \<and> \<not> running_image_faithful (I_relay_no_ack w0)"
  using acked_durable_implied_by_image_safety
        I_relay_no_ack_w0_acked_durable
        I_relay_no_ack_w0_unsafe
        I_relay_no_ack_w0_not_running_image_faithful
  by blast

end
