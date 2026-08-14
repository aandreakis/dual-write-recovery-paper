(*  Title:       Dual_Write_Converse.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    The IMAGE-level converse / optimality companion to the relay construction.

    The relay theory proves the advertise-after-replay discipline SUFFICIENT for
    crash-safety.  This theory proves the matching NECESSITY at the image level,
    turning the one-directional construction into a two-sided characterization:

      for a crash-closed, refining, Running-start implementation,
        (no reachable observable bad crash)
          if and only if
        (the durable downstream image equals the committed source-log image on
         scope at every reachable Running frontier)
      --- safe_iff_running_image_faithful.

    Honest scope (deliberate, stated, NOT defects):
      * IMAGE level, not LIST level.  Safety forces the downstream IMAGE (the
        store on scope equals the committed source-log image); it does NOT force
        the relay's list-level delivery discipline (the equality of the durable
        downstream history with the scoped bounded replay).  A downstream that
        durably stores the FULL source log agrees with the scoped replay on the
        scoped image --- the reading image-level safety consumes --- yet has a
        different history list (history_level_converse_false proves the image
        agreement at the probe point and the list inequality on a concrete
        witness).  So the two relay_admits clauses
        remain SUFFICIENT modelling choices whose image consequence is necessary;
        they are not themselves forced.
      * Running-frontier scoped.  The right-hand side is stated at reachable
        Running frontiers; it does not assert safety at crashed frontiers.
      * Reachable-fragment crash-closure.  crash_closed_implementation binds
        only trace-reachable states (Crash-enabledness is demanded where
        executions can actually stand), matching the trace quantification of
        running_image_faithful.  Against an all-states crash-closure premise
        the biconditional is thereby the strictly stronger statement: a
        weaker premise carrying the same conclusion.
      * All three premises are load-bearing.  Running-start in particular is NOT
        hygiene: it excludes the already-crashed crash_only_initial_mismatch
        class, which is otherwise running-image-faithful yet unsafe
        (running_start_is_load_bearing).
      * Modest depth, by design.  The forward direction is the existing crash
        partition restricted to Running states; the only new ingredient is the
        structural predecessor lemma
        crashed_has_running_predecessor_or_crashed_start (a reachable crashed-at-c
        state has a Running predecessor with the same proto, unless the run began
        crashed).  This is deliberate pearl economy, not a deep theorem, and it is
        INDEPENDENT of the reserved abstract crash-safe / log-derived completeness
        characterization (no protocol-to-outbox hinge is used here).

    sorry/oracle/axiom-free under quick_and_dirty=false.
*)

theory Dual_Write_Converse
  imports Dual_Write_Relay
begin

section \<open>Probe A: image equality does not force the history list
  (the history-level converse fails)\<close>

text \<open>
  A downstream that durably stores the FULL source history (including
  out-of-scope events) agrees with the scoped bounded replay on the scoped
  image (@{thm [source] replay_down_hist_image_on_scope}) --- the reading an
  image-level safety verdict consumes --- yet its history is a DIFFERENT
  list.  So safety cannot force the relay's list-level delivery discipline
  (the equality @{term "exec_down_hist s = replay_down_hist H K f"}); at most
  it can force the image.  The lemma below records the concrete separation
  witness: image agreement at the probe coordinate and key, list inequality
  outright.  It states no implementation or safety predicate itself; the
  safety reading rides Probe B's image-level biconditional.
\<close>

lemma history_level_converse_false:
  \<comment> \<open>image agrees on scope, yet the histories differ\<close>
  "Src (\<lambda>_::nat. None) anti_atomic_witness_src ec3 (0::nat)
     = Src (\<lambda>_. None) (replay_down_hist anti_atomic_witness_src {0} ec3) ec3 0
   \<and> anti_atomic_witness_src \<noteq> replay_down_hist anti_atomic_witness_src {0} ec3"
proof
  show "Src (\<lambda>_::nat. None) anti_atomic_witness_src ec3 0
        = Src (\<lambda>_. None) (replay_down_hist anti_atomic_witness_src {0} ec3) ec3 0"
    by (rule replay_down_hist_image_on_scope[symmetric]) simp
  show "anti_atomic_witness_src \<noteq> replay_down_hist anti_atomic_witness_src {0} ec3"
    using anti_atomic_down_neq_src by (simp add: eq_commute)
qed


section \<open>Probe B: the IMAGE-level biconditional\<close>

text \<open>
  The thesis-aligned RHS: at every reachable RUNNING state and every in-range
  frontier, the downstream image equals the committed-log image on scope (no
  scoped mismatch).  This is ``the downstream is a faithful (image-level)
  bounded replay at every running frontier''.
\<close>

definition running_image_faithful
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "running_image_faithful I \<longleftrightarrow>
     (\<forall>xs s c k.
        dwi_trace I (dwi_initial I) xs s
      \<and> exec_status (dwi_state I s) = Running
      \<and> c \<le> exec_finish (dwi_state I s)
      \<longrightarrow> \<not> mismatch_at (proto_of_exec_at (dwi_state I s) c) c k)"


subsection \<open>Forward: safe implies running-image-faithful (from the partition layer)\<close>

theorem safe_imp_running_image_faithful:
  assumes closed:   "crash_closed_implementation I"
      and refines:  "dwi_refines_exec I"
      and safe:     "\<not> implementation_has_reachable_observable_bad_crash I"
  shows "running_image_faithful I"
  unfolding running_image_faithful_def
proof (intro allI impI, elim conjE)
  fix xs s c k
  assume tr:  "dwi_trace I (dwi_initial I) xs s"
     and run: "exec_status (dwi_state I s) = Running"
     and le:  "c \<le> exec_finish (dwi_state I s)"
  show "\<not> mismatch_at (proto_of_exec_at (dwi_state I s) c) c k"
  proof
    assume mis: "mismatch_at (proto_of_exec_at (dwi_state I s) c) c k"
    have "implementation_has_reachable_observable_bad_crash I"
      by (rule crash_closed_running_bad_crash_enabled_imp_reachable_observable_bad_crash
            [OF closed refines tr run le mis])
    with safe show False ..
  qed
qed


subsection \<open>The NEW ingredient: a reachable Crashed-at-c state has a Running
  predecessor with the same proto (unless the run started already crashed)\<close>

text \<open>
  This is the one piece not present in the partition.  It uses the structural
  facts that (i) Crash is the only step that produces a Crashed status and it
  leaves every history field fixed, (ii) Crashed states only observe or recover,
  (iii) @{const proto_of_exec_at} ignores the status field.
\<close>

lemma crashed_has_running_predecessor_or_crashed_start:
  assumes tr: "dwi_trace I s0 xs s"
  shows "dwi_refines_exec I \<and> exec_status (dwi_state I s) = Crashed c \<longrightarrow>
           (\<exists>ys s_pre. dwi_trace I s0 ys s_pre
               \<and> exec_status (dwi_state I s_pre) = Running
               \<and> proto_of_exec_at (dwi_state I s_pre) c
                   = proto_of_exec_at (dwi_state I s) c)
         \<or> (exec_status (dwi_state I s0) = Crashed c
               \<and> proto_of_exec_at (dwi_state I s0) c
                   = proto_of_exec_at (dwi_state I s) c)"
  using tr
proof (induction rule: dwi_trace.induct)
  case (dwi_trace_refl I s0)
  show ?case
  proof (intro impI, elim conjE)
    assume "exec_status (dwi_state I s0) = Crashed c"
    thus "(\<exists>ys s_pre. dwi_trace I s0 ys s_pre
             \<and> exec_status (dwi_state I s_pre) = Running
             \<and> proto_of_exec_at (dwi_state I s_pre) c
                 = proto_of_exec_at (dwi_state I s0) c)
        \<or> (exec_status (dwi_state I s0) = Crashed c
             \<and> proto_of_exec_at (dwi_state I s0) c
                 = proto_of_exec_at (dwi_state I s0) c)"
      by simp
  qed
next
  case (dwi_trace_step I s0 a s1 as s)
  show ?case
  proof (intro impI, elim conjE)
    assume refines: "dwi_refines_exec I"
       and cr: "exec_status (dwi_state I s) = Crashed c"
    have estep: "dw_exec_step (dwi_state I s0) a (dwi_state I s1)"
      using refines dwi_trace_step.hyps(1) by (auto simp: dwi_refines_exec_def)
    have IHdisj:
      "(\<exists>ys s_pre. dwi_trace I s1 ys s_pre
           \<and> exec_status (dwi_state I s_pre) = Running
           \<and> proto_of_exec_at (dwi_state I s_pre) c
               = proto_of_exec_at (dwi_state I s) c)
     \<or> (exec_status (dwi_state I s1) = Crashed c
           \<and> proto_of_exec_at (dwi_state I s1) c
               = proto_of_exec_at (dwi_state I s) c)"
      using dwi_trace_step.IH refines cr by blast
    from IHdisj show
      "(\<exists>ys s_pre. dwi_trace I s0 ys s_pre
           \<and> exec_status (dwi_state I s_pre) = Running
           \<and> proto_of_exec_at (dwi_state I s_pre) c
               = proto_of_exec_at (dwi_state I s) c)
     \<or> (exec_status (dwi_state I s0) = Crashed c
           \<and> proto_of_exec_at (dwi_state I s0) c
               = proto_of_exec_at (dwi_state I s) c)"
    proof
      assume "\<exists>ys s_pre. dwi_trace I s1 ys s_pre
               \<and> exec_status (dwi_state I s_pre) = Running
               \<and> proto_of_exec_at (dwi_state I s_pre) c
                   = proto_of_exec_at (dwi_state I s) c"
      then obtain ys s_pre where
          y_tr: "dwi_trace I s1 ys s_pre"
        and y_run: "exec_status (dwi_state I s_pre) = Running"
        and y_proto: "proto_of_exec_at (dwi_state I s_pre) c
                        = proto_of_exec_at (dwi_state I s) c"
        by blast
      have "dwi_trace I s0 (a # ys) s_pre"
        by (rule dwi_trace.dwi_trace_step[OF dwi_trace_step.hyps(1) y_tr])
      thus ?thesis using y_run y_proto by blast
    next
      assume r: "exec_status (dwi_state I s1) = Crashed c
                   \<and> proto_of_exec_at (dwi_state I s1) c
                       = proto_of_exec_at (dwi_state I s) c"
      hence r_st: "exec_status (dwi_state I s1) = Crashed c"
        and r_pr: "proto_of_exec_at (dwi_state I s1) c
                     = proto_of_exec_at (dwi_state I s) c" by simp_all
      from estep show ?thesis
      proof (cases rule: dw_exec_step.cases)
        case (do_source cc e)        \<comment> \<open>status unchanged = Running, contra Crashed\<close>
        from do_source r_st show ?thesis by simp
      next
        case (enqueue_downstream cc e)
        from enqueue_downstream r_st show ?thesis by simp
      next
        case (do_downstream cc e)
        from do_downstream r_st show ?thesis by simp
      next
        case (ack cc e)
        from ack r_st show ?thesis by simp
      next
        case (crash cc)
        \<comment> \<open>s0 Running; s1 = s0 with status Crashed cc; proto ignores status.\<close>
        from crash have run0: "exec_status (dwi_state I s0) = Running"
          and s1eq: "dwi_state I s1 = (dwi_state I s0)\<lparr>exec_status := Crashed cc\<rparr>"
          by auto
        have "proto_of_exec_at (dwi_state I s0) c
                = proto_of_exec_at (dwi_state I s) c"
          using r_pr by (simp add: s1eq)
        with run0 dwi_trace.dwi_trace_refl[of I s0] show ?thesis by blast
      next
        case (recover cc)            \<comment> \<open>status becomes Recovered, contra Crashed\<close>
        from recover r_st show ?thesis by simp
      next
        case (observe ff)
        \<comment> \<open>identity step: the reached state equals the source state.\<close>
        from observe have eq: "dwi_state I s1 = dwi_state I s0" by simp
        from r_st eq have "exec_status (dwi_state I s0) = Crashed c" by simp
        moreover from r_pr eq
          have "proto_of_exec_at (dwi_state I s0) c
                  = proto_of_exec_at (dwi_state I s) c" by simp
        ultimately show ?thesis by blast
      qed
    qed
  qed
qed


subsection \<open>Backward: running-image-faithful plus Running-start implies safe\<close>

theorem running_image_faithful_running_start_imp_safe:
  assumes refines:  "dwi_refines_exec I"
      and start_run: "exec_status (dwi_state I (dwi_initial I)) = Running"
      and faithful:  "running_image_faithful I"
  shows "\<not> implementation_has_reachable_observable_bad_crash I"
proof
  assume "implementation_has_reachable_observable_bad_crash I"
  then obtain xs c k s where
      bad: "reachable_observable_bad_crash I xs c k s"
    by (auto simp: implementation_has_reachable_observable_bad_crash_def)
  hence tr: "dwi_trace I (dwi_initial I) xs s"
    and obs: "observable_mismatch (dwi_state I s) c k"
    by (auto simp: reachable_observable_bad_crash_def)
  from obs have crashed: "exec_status (dwi_state I s) = Crashed c"
    and le_fin:  "c \<le> exec_finish (dwi_state I s)"
    and mis:     "mismatch_at (proto_of_exec_at (dwi_state I s) c) c k"
    by (auto simp: observable_mismatch_def)
  have disj:
    "(\<exists>ys s_pre. dwi_trace I (dwi_initial I) ys s_pre
         \<and> exec_status (dwi_state I s_pre) = Running
         \<and> proto_of_exec_at (dwi_state I s_pre) c
             = proto_of_exec_at (dwi_state I s) c)
   \<or> (exec_status (dwi_state I (dwi_initial I)) = Crashed c
         \<and> proto_of_exec_at (dwi_state I (dwi_initial I)) c
             = proto_of_exec_at (dwi_state I s) c)"
    using crashed_has_running_predecessor_or_crashed_start[OF tr] refines crashed
    by blast
  from disj show False
  proof
    assume "\<exists>ys s_pre. dwi_trace I (dwi_initial I) ys s_pre
              \<and> exec_status (dwi_state I s_pre) = Running
              \<and> proto_of_exec_at (dwi_state I s_pre) c
                  = proto_of_exec_at (dwi_state I s) c"
    then obtain ys s_pre where
        p_tr: "dwi_trace I (dwi_initial I) ys s_pre"
      and p_run: "exec_status (dwi_state I s_pre) = Running"
      and p_proto: "proto_of_exec_at (dwi_state I s_pre) c
                      = proto_of_exec_at (dwi_state I s) c"
      by blast
    have p_mis: "mismatch_at (proto_of_exec_at (dwi_state I s_pre) c) c k"
      using mis p_proto by simp
    have p_fin: "exec_finish (dwi_state I s_pre) = exec_finish (dwi_state I s)"
      using p_proto by (simp add: proto_of_exec_at_def)
    have p_le: "c \<le> exec_finish (dwi_state I s_pre)"
      using le_fin p_fin by simp
    from faithful p_tr p_run p_le
    have "\<not> mismatch_at (proto_of_exec_at (dwi_state I s_pre) c) c k"
      by (simp add: running_image_faithful_def)
    with p_mis show False by simp
  next
    assume "exec_status (dwi_state I (dwi_initial I)) = Crashed c
              \<and> proto_of_exec_at (dwi_state I (dwi_initial I)) c
                  = proto_of_exec_at (dwi_state I s) c"
    hence "exec_status (dwi_state I (dwi_initial I)) = Crashed c" by simp
    with start_run show False by simp
  qed
qed


subsection \<open>The biconditional (the candidate "optimality" characterization)\<close>

theorem safe_iff_running_image_faithful:
  assumes closed:    "crash_closed_implementation I"
      and refines:   "dwi_refines_exec I"
      and start_run: "exec_status (dwi_state I (dwi_initial I)) = Running"
  shows "(\<not> implementation_has_reachable_observable_bad_crash I)
         \<longleftrightarrow> running_image_faithful I"
proof
  assume "\<not> implementation_has_reachable_observable_bad_crash I"
  thus "running_image_faithful I"
    by (rule safe_imp_running_image_faithful[OF closed refines])
next
  assume "running_image_faithful I"
  thus "\<not> implementation_has_reachable_observable_bad_crash I"
    by (rule running_image_faithful_running_start_imp_safe[OF refines start_run])
qed


section \<open>Probe C: non-vacuity and the Running-start kill-test\<close>

text \<open>
  Structural fact behind the predecessor lemma: once a state is not Running it
  stays not Running (Crash needs Running; from Crashed only recover/observe).
\<close>

lemma dw_exec_step_not_running_preserved:
  assumes step: "dw_exec_step s a s'" and nr: "exec_status s \<noteq> Running"
  shows "exec_status s' \<noteq> Running"
  using step nr by (cases rule: dw_exec_step.cases) auto

lemma dw_exec_trace_not_running_preserved:
  assumes "dw_exec_trace a xs s'" and "exec_status a \<noteq> Running"
  shows "exec_status s' \<noteq> Running"
  using assms
proof (induction rule: dw_exec_trace.induct)
  case (trace_refl s) thus ?case by simp
next
  case (trace_step s b s' xs s'')
  have "exec_status s' \<noteq> Running"
    by (rule dw_exec_step_not_running_preserved[OF trace_step.hyps(1) trace_step.prems])
  thus ?case using trace_step.IH by simp
qed

lemma canonical_dwi_trace_imp_exec_trace:
  assumes "dwi_trace (canonical_dw_implementation s0) a xs s'"
  shows "dw_exec_trace a xs s'"
  using dwi_trace_refines_exec[OF canonical_dw_implementation_refines_exec assms]
  by (simp add: canonical_dw_implementation_def)


subsection \<open>The bounding class: crash-only-initial-mismatch (NOT Running-start)\<close>

text \<open>
  The canonical implementation of @{const crash_only_initial_mismatch_state}
  starts ALREADY crashed.  It is crash-closed, refining, and UNSAFE, yet
  running-image-faithful holds VACUOUSLY (no reachable Running state).  So
  dropping the Running-start premise breaks the backward direction --- the
  premise is genuinely load-bearing, and it is exactly what excludes this class.
\<close>

lemma crash_only_initial_running_image_faithful:
  "running_image_faithful
     (canonical_dw_implementation crash_only_initial_mismatch_state)"
  unfolding running_image_faithful_def
proof (intro allI impI, elim conjE)
  fix xs s c k
  let ?I = "canonical_dw_implementation crash_only_initial_mismatch_state"
  assume tr:  "dwi_trace ?I (dwi_initial ?I) xs s"
     and run: "exec_status (dwi_state ?I s) = Running"
  have init_nr: "exec_status crash_only_initial_mismatch_state \<noteq> Running"
    by (simp add: crash_only_initial_mismatch_state_def initial_exec_state_def)
  have tr0: "dwi_trace ?I crash_only_initial_mismatch_state xs s"
    using tr by (simp add: canonical_dw_implementation_def)
  have "dw_exec_trace crash_only_initial_mismatch_state xs s"
    by (rule canonical_dwi_trace_imp_exec_trace[OF tr0])
  from dw_exec_trace_not_running_preserved[OF this init_nr] run
  show "\<not> mismatch_at (proto_of_exec_at (dwi_state ?I s) c) c k"
    by (simp add: canonical_dw_implementation_def)
qed

theorem running_start_is_load_bearing:
  \<comment> \<open>closed + refining + running-image-faithful + UNSAFE + NOT Running-start:
      the backward direction would FAIL without the Running-start premise.\<close>
  "crash_closed_implementation
     (canonical_dw_implementation crash_only_initial_mismatch_state)
 \<and> dwi_refines_exec
     (canonical_dw_implementation crash_only_initial_mismatch_state)
 \<and> running_image_faithful
     (canonical_dw_implementation crash_only_initial_mismatch_state)
 \<and> implementation_has_reachable_observable_bad_crash
     (canonical_dw_implementation crash_only_initial_mismatch_state)
 \<and> exec_status (dwi_state
       (canonical_dw_implementation crash_only_initial_mismatch_state)
       (dwi_initial
         (canonical_dw_implementation crash_only_initial_mismatch_state)))
     \<noteq> Running"
proof (intro conjI)
  show "crash_closed_implementation
          (canonical_dw_implementation crash_only_initial_mismatch_state)"
    by (rule canonical_dw_implementation_crash_closed)
  show "dwi_refines_exec
          (canonical_dw_implementation crash_only_initial_mismatch_state)"
    by (rule canonical_dw_implementation_refines_exec)
  show "running_image_faithful
          (canonical_dw_implementation crash_only_initial_mismatch_state)"
    by (rule crash_only_initial_running_image_faithful)
  show "implementation_has_reachable_observable_bad_crash
          (canonical_dw_implementation crash_only_initial_mismatch_state)"
    by (rule crash_only_initial_mismatch_has_reachable_bad_crash)
  show "exec_status (dwi_state
          (canonical_dw_implementation crash_only_initial_mismatch_state)
          (dwi_initial
            (canonical_dw_implementation crash_only_initial_mismatch_state)))
        \<noteq> Running"
    by (simp add: canonical_dw_implementation_def
                  crash_only_initial_mismatch_state_def initial_exec_state_def)
qed


subsection \<open>Non-vacuity (UNSAFE side): the relay is a Running-start instance that
  IS unsafe and correspondingly is NOT running-image-faithful\<close>

lemma I_relay_labels_w0_unsafe:
  "implementation_has_reachable_observable_bad_crash (I_relay_labels w0)"
proof -
  have obs: "observable_mismatch (dwi_state (I_relay_labels w0) w_crash) ec3 0"
    by (simp add: I_relay_labels_def w_crash_observable_mismatch_at_ec3)
  have div: "diverges (proto_of_exec_at (dwi_state (I_relay_labels w0) w_crash) ec3) ec3"
    by (rule observable_mismatch_imp_diverges[OF obs])
  have "reachable_observable_bad_crash (I_relay_labels w0)
          [DoSource ec2 (Insert 0 7), EnqueueDownstream ec2 (Insert 0 7),
           DoDownstream ec2 (Insert 0 7), DoSource ec3 (Insert 0 9), Crash ec3]
          ec3 0 w_crash"
    unfolding reachable_observable_bad_crash_def
    using w_crash_reachable obs div by blast
  thus ?thesis
    by (auto simp: implementation_has_reachable_observable_bad_crash_def)
qed

lemma w_src3_running: "exec_status w_src3 = Running"
  by (simp add: w_src3_def w_down2_def w_enq2_def w_src2_def w0_def
                initial_exec_state_def)

lemma w_src3_mismatch_ec3: "mismatch_at (proto_of_exec_at w_src3 ec3) ec3 0"
proof -
  have "proto_of_exec_at w_src3 ec3 = proto_of_exec_at w_crash ec3"
    by (simp add: w_crash_def)
  thus ?thesis using w_crash_mismatch_at_ec3 by simp
qed

lemma I_relay_labels_w0_not_running_image_faithful:
  "\<not> running_image_faithful (I_relay_labels w0)"
proof
  assume rif: "running_image_faithful (I_relay_labels w0)"
  have run: "exec_status (dwi_state (I_relay_labels w0) w_src3) = Running"
    by (simp add: I_relay_labels_def w_src3_running)
  have le: "ec3 \<le> exec_finish (dwi_state (I_relay_labels w0) w_src3)"
    by (simp add: I_relay_labels_def w_src3_fields src_le_refl src_le_eq_less_eq)
  from rif w_src3_reachable_dwi run le
  have "\<not> mismatch_at (proto_of_exec_at (dwi_state (I_relay_labels w0) w_src3) ec3) ec3 0"
    by (simp add: running_image_faithful_def)
  moreover have
    "mismatch_at (proto_of_exec_at (dwi_state (I_relay_labels w0) w_src3) ec3) ec3 0"
    using w_src3_mismatch_ec3 by (simp add: I_relay_labels_def)
  ultimately show False by simp
qed

text \<open>So @{const I_relay_labels} is a crash-closed, refining, Running-start
  implementation that is UNSAFE iff it is NOT running-image-faithful --- the
  biconditional is non-vacuous on the unsafe side, with a real loaded frontier
  (@{const ec3}), not an empty/degenerate one.\<close>


subsection \<open>Non-vacuity (SAFE side): an empty-scope inhabitant\<close>

text \<open>
  Empty scope is trivially running-image-faithful (no key is ever in scope), so
  by the backward direction it is SAFE: a crash-closed, refining, Running-start,
  SAFE inhabitant --- the biconditional's safe side is non-empty.  (This also
  exercises the backward theorem.)

  WHERE THE SAFE SIDE'S BOUNDARY ACTUALLY SITS.  For the separable
  per-label implementation interface, the partition theory's obstruction
  (@{text
  separable_non_atomic_crash_closed_imp_reachable_observable_bad_crash},
  together with its genuine in-scope non-atomic bridge) rules out
  crash-closed, refining implementations containing an EFFECTIVE
  in-scope separable non-atomic completion --- the completion classes
  carry @{text effective_source_effect}, an image-changing monitored
  write completed separably.  It does not rule out safe nonempty-scope
  executions whose monitored writes are value-preserving or
  authority-neutral.  No richer safe inhabitant is currently exhibited;
  safety with EFFECTIVE in-scope delivery requires leaving the
  separable per-label interface for the shared-commit capability.
\<close>

lemma empty_scope_running_image_faithful:
  "running_image_faithful
     (canonical_dw_implementation
        (initial_exec_state (\<lambda>_::nat. None) ({}::nat set) fin))"
  unfolding running_image_faithful_def
proof (intro allI impI, elim conjE)
  fix xs s c k
  let ?I = "canonical_dw_implementation
              (initial_exec_state (\<lambda>_::nat. None) ({}::nat set) fin)"
  assume tr: "dwi_trace ?I (dwi_initial ?I) xs s"
  have tr0: "dwi_trace ?I (initial_exec_state (\<lambda>_::nat. None) {} fin) xs s"
    using tr by (simp add: canonical_dw_implementation_def)
  have "dw_exec_trace (initial_exec_state (\<lambda>_::nat. None) {} fin) xs s"
    by (rule canonical_dwi_trace_imp_exec_trace[OF tr0])
  from dw_exec_trace_scope[OF this] have sc: "exec_scope s = {}"
    by (simp add: initial_exec_state_def)
  show "\<not> mismatch_at (proto_of_exec_at (dwi_state ?I s) c) c k"
    by (simp add: mismatch_at_def proto_of_exec_at_def
                  canonical_dw_implementation_def sc)
qed

theorem empty_scope_inhabits_safe_side:
  "crash_closed_implementation
     (canonical_dw_implementation (initial_exec_state (\<lambda>_::nat. None) ({}::nat set) fin))
 \<and> dwi_refines_exec
     (canonical_dw_implementation (initial_exec_state (\<lambda>_::nat. None) ({}::nat set) fin))
 \<and> exec_status (dwi_state
       (canonical_dw_implementation (initial_exec_state (\<lambda>_::nat. None) ({}::nat set) fin))
       (dwi_initial
         (canonical_dw_implementation (initial_exec_state (\<lambda>_::nat. None) ({}::nat set) fin))))
     = Running
 \<and> \<not> implementation_has_reachable_observable_bad_crash
     (canonical_dw_implementation (initial_exec_state (\<lambda>_::nat. None) ({}::nat set) fin))"
proof (intro conjI)
  show "crash_closed_implementation
          (canonical_dw_implementation (initial_exec_state (\<lambda>_::nat. None) ({}::nat set) fin))"
    by (rule canonical_dw_implementation_crash_closed)
  show "dwi_refines_exec
          (canonical_dw_implementation (initial_exec_state (\<lambda>_::nat. None) ({}::nat set) fin))"
    by (rule canonical_dw_implementation_refines_exec)
  show "exec_status (dwi_state
          (canonical_dw_implementation (initial_exec_state (\<lambda>_::nat. None) ({}::nat set) fin))
          (dwi_initial
            (canonical_dw_implementation (initial_exec_state (\<lambda>_::nat. None) ({}::nat set) fin))))
        = Running"
    by (simp add: canonical_dw_implementation_def initial_exec_state_def)
  show "\<not> implementation_has_reachable_observable_bad_crash
          (canonical_dw_implementation (initial_exec_state (\<lambda>_::nat. None) ({}::nat set) fin))"
    by (rule running_image_faithful_running_start_imp_safe
          [OF canonical_dw_implementation_refines_exec _
              empty_scope_running_image_faithful])
       (simp add: canonical_dw_implementation_def initial_exec_state_def)
qed

end
