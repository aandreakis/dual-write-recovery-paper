(*  Title:       Dual_Write_Frontier_Seam.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    The advertised-frontier seam, witnessed at both sides: the verified relay
    is safe at an occurrence-complete frontier it advertises, while a separable
    non-atomic dual write goes wrong at a frontier IT ITSELF advertised.
    Advertisement alone is deliberately not treated as completeness.

    THE SEAM.  The development proves
      (i)  sufficiency at OCCURRENCE-COMPLETE frontiers: for the verified relay,
           no observable mismatch when relay_complete_through s f
           (relay_inv_no_observable_mismatch, Dual_Write_Relay.thy), where
           adv s is the frontier the implementation itself exposes (the
           coordinate of the last delivered downstream event); and
      (ii) an ABSOLUTE converse: crash-safety at every reachable running
           frontier iff scoped image equality (Dual_Write_Converse.thy).
    Neither theorem evaluates a DUAL WRITE at a frontier IT HAS ITSELF
    advertised.  This theory does exactly that, in both natural readings of
    "advertised" for a dual-writing service, and at witness level PLUS an
    honest class level:

      * Witness B (delivered frontier): the LITERAL same function adv and the
        LITERAL same predicate observable_mismatch as the relay theorem ---
        a crash-closed separable non-atomic dual writer reaches a state whose
        advertised frontier is loaded (> c0, in-scope delivered event) and
        observably mismatched AT that very frontier.  The relay side of the
        separation is restated on a genuinely reachable relay crash at ITS
        advertised and occurrence-complete frontier.  The unsafe side shows
        why the advertisement coordinate alone is not that contract.

      * Witness A (acked frontier): the practitioner's advertisement --- the
        service acks the caller once the source write commits.  ack_adv
        mirrors adv (last coordinate of a history field, c0 default) on
        exec_acked.  A source-first dual writer reaches a crashed state with
        an observable (indeed acked-observable) mismatch AT ack_adv.

      * Class level: for EVERY implementation admitting a separable
        completion (either side) that is crash-closed, a reachable state has
        an observable mismatch at the completion's own coordinate, and that
        coordinate is EXACTLY the natural last-based advertised frontier of
        the reached state (ack_adv for the source-first side; the relay's own
        adv for the downstream-first side) --- no discipline premise at all
        for these two.  In addition, for EVERY advertising discipline A that
        covers what the implementation has confirmed (acked source writes /
        delivered downstream events), the mismatch lies inside the advertised
        region f <= A s.  Monotonicity of A is NOT needed.  The coverage
        premises are inhabited (sup disciplines below) and are not vacuous:
        the never-advertising discipline (\<lambda>_. c0) provably violates
        coverage (negative control below).

    HONEST BOUNDARY (stated, not hidden): a discipline that never covers
    anything the implementation confirmed (e.g. constant c0) escapes the
    class theorems by advertising nothing; that is the same vacuity boundary
    the development draws for never-emitting implementations.  The witness
    theorems close it from the other side: the concrete dual writers below
    genuinely advertise loaded frontiers.

    Disclosed scope: the class-level premises are coverage-form (the
    discipline advertises at least what the implementation has confirmed on
    the respective channel), and every verdict is at the image tier ---
    scoped source/downstream image (in)equality at a frontier --- like the
    rest of this entry.

    sorry/oracle/axiom-free under quick_and_dirty=false.
*)

theory Dual_Write_Frontier_Seam
  imports Dual_Write_Relay
begin

section \<open>Advertising disciplines for a dual writer\<close>

text \<open>
  The acked-frontier mirror of the relay's @{const adv}: the coordinate of the
  last write the service has ACKNOWLEDGED to its caller (@{const c0} when
  nothing was acked).  Same shape as @{const adv} (last of a history field),
  read off the field that records the advertisement act of the machine.
\<close>

definition ack_adv :: "('k, 'v) dw_exec_state \<Rightarrow> src_coord" where
  "ack_adv s = (if exec_acked s = [] then c0
                else fst (last (exec_acked s)))"

text \<open>
  Coverage-style disciplines for the class-level theorems.  A discipline is a
  frontier-valued function of the state; coverage says it advertises at least
  what the implementation has confirmed on the respective channel.
\<close>

definition advertises_acked
  :: "(('k, 'v) dw_exec_state \<Rightarrow> src_coord) \<Rightarrow> bool"
where
  "advertises_acked A \<longleftrightarrow>
     (\<forall>s c e. (c, e) \<in> set (exec_acked s) \<longrightarrow> c \<le> A s)"

definition advertises_delivered
  :: "(('k, 'v) dw_exec_state \<Rightarrow> src_coord) \<Rightarrow> bool"
where
  "advertises_delivered A \<longleftrightarrow>
     (\<forall>s c e. (c, e) \<in> set (exec_down_hist s) \<longrightarrow> c \<le> A s)"

text \<open>Canonical inhabitants: the exact suprema of the confirmed coordinates.\<close>

definition acked_frontier_sup :: "('k, 'v) dw_exec_state \<Rightarrow> src_coord" where
  "acked_frontier_sup s = Max (insert c0 (fst ` set (exec_acked s)))"

definition delivered_frontier_sup :: "('k, 'v) dw_exec_state \<Rightarrow> src_coord" where
  "delivered_frontier_sup s = Max (insert c0 (fst ` set (exec_down_hist s)))"

definition dual_write_frontier_sup :: "('k, 'v) dw_exec_state \<Rightarrow> src_coord" where
  "dual_write_frontier_sup s =
     Max (insert c0 (fst ` set (exec_acked s) \<union> fst ` set (exec_down_hist s)))"

lemma advertises_acked_sup: "advertises_acked acked_frontier_sup"
proof (unfold advertises_acked_def, intro allI impI)
  fix s :: "('k, 'v) dw_exec_state" and c e
  assume "(c, e) \<in> set (exec_acked s)"
  hence "c \<in> insert c0 (fst ` set (exec_acked s))" by force
  thus "c \<le> acked_frontier_sup s"
    unfolding acked_frontier_sup_def by (intro Max_ge) auto
qed

lemma advertises_delivered_sup: "advertises_delivered delivered_frontier_sup"
proof (unfold advertises_delivered_def, intro allI impI)
  fix s :: "('k, 'v) dw_exec_state" and c e
  assume "(c, e) \<in> set (exec_down_hist s)"
  hence "c \<in> insert c0 (fst ` set (exec_down_hist s))" by force
  thus "c \<le> delivered_frontier_sup s"
    unfolding delivered_frontier_sup_def by (intro Max_ge) auto
qed

lemma dual_write_frontier_sup_advertises_acked:
  "advertises_acked dual_write_frontier_sup"
proof (unfold advertises_acked_def, intro allI impI)
  fix s :: "('k, 'v) dw_exec_state" and c e
  assume "(c, e) \<in> set (exec_acked s)"
  hence "c \<in> insert c0
           (fst ` set (exec_acked s) \<union> fst ` set (exec_down_hist s))"
    by force
  thus "c \<le> dual_write_frontier_sup s"
    unfolding dual_write_frontier_sup_def by (intro Max_ge) auto
qed

lemma dual_write_frontier_sup_advertises_delivered:
  "advertises_delivered dual_write_frontier_sup"
proof (unfold advertises_delivered_def, intro allI impI)
  fix s :: "('k, 'v) dw_exec_state" and c e
  assume "(c, e) \<in> set (exec_down_hist s)"
  hence "c \<in> insert c0
           (fst ` set (exec_acked s) \<union> fst ` set (exec_down_hist s))"
    by force
  thus "c \<le> dual_write_frontier_sup s"
    unfolding dual_write_frontier_sup_def by (intro Max_ge) auto
qed

text \<open>
  The relay's @{const adv} never exceeds the delivered supremum, so any
  statement about the sup discipline's advertised region covers the region
  @{const adv} spans.  (On wellformed histories the two coincide at the last
  element; the inequality is all the class theorems need.)
\<close>

lemma adv_le_delivered_frontier_sup: "adv s \<le> delivered_frontier_sup s"
proof -
  have "adv s \<in> insert c0 (fst ` set (exec_down_hist s))"
    by (cases "exec_down_hist s = []") (simp_all add: adv_def last_in_set)
  hence "adv s \<le> Max (insert c0 (fst ` set (exec_down_hist s)))"
    by (intro Max_ge) simp_all
  thus ?thesis by (simp only: delivered_frontier_sup_def)
qed

text \<open>
  On WELLFORMED histories (WF-H1: non-decreasing coordinates) the last-based
  frontiers cover their confirmed sets: every member coordinate is at or below
  the last coordinate.  So on the machine's own wellformed states --- which
  every admissible run maintains --- the relay's @{const adv} covers delivered
  events and @{const ack_adv} covers acked writes; the class-level coverage
  premises below are exactly what the natural disciplines provide there.
\<close>

lemma wellformed_hist_coord_le_last:
  assumes wf: "wellformed_src_history H"
      and mem: "(c, e) \<in> set H"
  shows "c \<le> fst (last H)"
proof -
  from mem obtain i where i: "i < length H" and nth: "H ! i = (c, e)"
    by (meson in_set_conv_nth)
  have ne: "H \<noteq> []" using mem by auto
  have step_mono: "fst (H ! a) \<le> fst (H ! b)"
    if "a \<le> b" and "b < length H" for a b
    using that
  proof (induction b)
    case 0
    then show ?case by simp
  next
    case (Suc b)
    show ?case
    proof (cases "a = Suc b")
      case True
      then show ?thesis by simp
    next
      case False
      with Suc.prems(1) have ab: "a \<le> b" by simp
      have bl: "b < length H" using Suc.prems(2) by simp
      have IH: "fst (H ! a) \<le> fst (H ! b)" by (rule Suc.IH[OF ab bl])
      have "src_le (fst (H ! b)) (fst (H ! Suc b))"
        using wf Suc.prems(2) by (auto simp: wellformed_src_history_def)
      hence "fst (H ! b) \<le> fst (H ! Suc b)"
        by (simp add: src_le_eq_less_eq)
      from order_trans[OF IH this] show ?thesis .
    qed
  qed
  have last_nth: "last H = H ! (length H - 1)"
    using ne by (simp add: last_conv_nth)
  have "fst (H ! i) \<le> fst (H ! (length H - 1))"
    by (rule step_mono) (use i in auto)
  thus ?thesis using nth last_nth by simp
qed

lemma ack_adv_covers_acked_on_wellformed:
  assumes wf: "wellformed_exec_state s"
      and mem: "(c, e) \<in> set (exec_acked s)"
  shows "c \<le> ack_adv s"
proof -
  have wfa: "wellformed_src_history (exec_acked s)"
    using wf
    by (simp add: wellformed_exec_state_def exec_histories_wellformed_def)
  have ne: "exec_acked s \<noteq> []" using mem by auto
  from wellformed_hist_coord_le_last[OF wfa mem]
  show ?thesis by (simp add: ack_adv_def ne)
qed

lemma adv_covers_delivered_on_wellformed:
  assumes wf: "wellformed_exec_state s"
      and mem: "(c, e) \<in> set (exec_down_hist s)"
  shows "c \<le> adv s"
proof -
  have wfd: "wellformed_src_history (exec_down_hist s)"
    using wf
    by (simp add: wellformed_exec_state_def exec_histories_wellformed_def)
  have ne: "exec_down_hist s \<noteq> []" using mem by auto
  from wellformed_hist_coord_le_last[OF wfd mem]
  show ?thesis by (simp add: adv_def ne)
qed


section \<open>Witness A: source-first dual write, mismatch AT the acked frontier\<close>

text \<open>
  A dual-writing service on base @{term "[0 \<mapsto> 1]"}, scope @{term "{0::nat}"}:
  it commits @{term "Update 0 2"} to the source at @{const ec1}, ACKS the
  caller (this is the advertisement: ``your write is done''), and crashes at
  @{const ec1} before the separated downstream leg (planned at @{const ec3})
  runs.  The crashed state's acked frontier is @{const ec1} --- loaded, above
  @{const c0}, carrying an in-scope committed event --- and the state is
  observably mismatched exactly there.
\<close>

definition sf0 :: "(nat, nat) dw_exec_state" where
  "sf0 = initial_exec_state [0 \<mapsto> 1] {0} ec3"

definition sf_src :: "(nat, nat) dw_exec_state" where
  "sf_src = sf0\<lparr>exec_src_hist := exec_src_hist sf0 @ [(ec1, Update 0 2)]\<rparr>"

definition sf_ack :: "(nat, nat) dw_exec_state" where
  "sf_ack = sf_src\<lparr>exec_acked := exec_acked sf_src @ [(ec1, Update 0 2)]\<rparr>"

definition sf_crash :: "(nat, nat) dw_exec_state" where
  "sf_crash = sf_ack\<lparr>exec_status := Crashed ec1\<rparr>"

lemma sf_step_src: "dw_exec_step sf0 (DoSource ec1 (Update 0 2)) sf_src"
  unfolding sf_src_def
  by (rule dw_exec_step.do_source)
     (simp add: sf0_def initial_exec_state_def)

lemma sf_step_ack: "dw_exec_step sf_src (Ack ec1 (Update 0 2)) sf_ack"
  unfolding sf_ack_def
  by (rule dw_exec_step.ack)
     (simp_all add: sf_src_def sf0_def initial_exec_state_def)

lemma sf_step_crash: "dw_exec_step sf_ack (Crash ec1) sf_crash"
  unfolding sf_crash_def
  by (rule dw_exec_step.crash)
     (simp add: sf_ack_def sf_src_def sf0_def initial_exec_state_def)

lemma sf_crash_trace:
  "dw_exec_trace sf0
     [DoSource ec1 (Update 0 2), Ack ec1 (Update 0 2), Crash ec1] sf_crash"
  by (rule dw_exec_trace.trace_step[OF sf_step_src],
      rule dw_exec_trace.trace_step[OF sf_step_ack],
      rule dw_exec_trace.trace_step[OF sf_step_crash],
      rule dw_exec_trace.trace_refl)

lemma sf_crash_fields:
  "exec_base sf_crash = [0 \<mapsto> 1]"
  "exec_src_hist sf_crash = [(ec1, Update 0 2)]"
  "exec_down_hist sf_crash = []"
  "exec_acked sf_crash = [(ec1, Update 0 2)]"
  "exec_scope sf_crash = {0}"
  "exec_finish sf_crash = ec3"
  "exec_status sf_crash = Crashed ec1"
  by (simp_all add: sf_crash_def sf_ack_def sf_src_def sf0_def
                    initial_exec_state_def)

lemma ack_adv_sf_crash: "ack_adv sf_crash = ec1"
  by (simp add: ack_adv_def sf_crash_fields)

lemma ack_adv_sf_crash_loaded: "c0 < ack_adv sf_crash"
  by (simp add: ack_adv_sf_crash ec1_def)

text \<open>The observable mismatch AT the acked (self-advertised) frontier.
  Image computation is one-shot in the landed @{thm down_image_ec3} style.\<close>

lemma sf_crash_observable_mismatch:
  "observable_mismatch sf_crash (ack_adv sf_crash) 0"
  unfolding ack_adv_sf_crash
proof (rule observable_mismatchI)
  show "exec_status sf_crash = Crashed ec1" by (simp add: sf_crash_fields)
  show "ec1 \<le> exec_finish sf_crash" by (simp add: sf_crash_fields ec_defs)
  show "0 \<in> exec_scope sf_crash" by (simp add: sf_crash_fields)
  show "Src (exec_base sf_crash) (exec_down_hist sf_crash) ec1 0
        \<noteq> Src (exec_base sf_crash) (exec_src_hist sf_crash) ec1 0"
    by (simp add: sf_crash_fields Src_def latest_src_event_def Let_def ec_ord)
qed

text \<open>...and it is an ACKED observable mismatch: the caller was told the
  write at the advertised frontier is done.\<close>

lemma sf_crash_acked_observable_mismatch:
  "acked_observable_mismatch sf_crash (ack_adv sf_crash) 0"
  unfolding acked_observable_mismatch_def
proof (intro conjI)
  show "observable_mismatch sf_crash (ack_adv sf_crash) 0"
    by (rule sf_crash_observable_mismatch)
  show "acked_source_effect_at sf_crash (ack_adv sf_crash) 0"
    unfolding acked_source_effect_at_def ack_adv_sf_crash
    by (intro exI[of _ ec1] exI[of _ "Update 0 2"])
       (simp add: sf_crash_fields Src_def latest_src_event_def Let_def ec_ord)
qed

subsection \<open>The witness implementation is a genuine crash-closed separable
  non-atomic dual writer\<close>

definition sf_completion :: "(nat, nat) separated_dual_write_completion" where
  "sf_completion =
     \<lparr> sdwc_pre = [],
       sdwc_key = 0,
       sdwc_source_at = ec1,
       sdwc_event = Update 0 2,
       sdwc_down_at = ec3,
       sdwc_down_event = Update 0 2 \<rparr>"

definition sf_enq :: "(nat, nat) dw_exec_state" where
  "sf_enq = sf_ack\<lparr>exec_enqueued := exec_enqueued sf_ack @ [(ec3, Update 0 2)],
                   exec_pending := insert (ec3, Update 0 2) (exec_pending sf_ack)\<rparr>"

definition sf_down :: "(nat, nat) dw_exec_state" where
  "sf_down = sf_enq\<lparr>exec_down_hist := exec_down_hist sf_enq @ [(ec3, Update 0 2)],
                    exec_pending := exec_pending sf_enq - {(ec3, Update 0 2)}\<rparr>"

lemma sf_step_enq: "dw_exec_step sf_ack (EnqueueDownstream ec3 (Update 0 2)) sf_enq"
  unfolding sf_enq_def
  by (rule dw_exec_step.enqueue_downstream)
     (simp add: sf_ack_def sf_src_def sf0_def initial_exec_state_def)

lemma sf_step_down: "dw_exec_step sf_enq (DoDownstream ec3 (Update 0 2)) sf_down"
  unfolding sf_down_def
  by (rule dw_exec_step.do_downstream)
     (simp_all add: sf_enq_def sf_ack_def sf_src_def sf0_def
                    initial_exec_state_def)

lemma sf_completion_schedule:
  "source_first_separated_dual_write_schedule
     (canonical_dw_implementation sf0) sf_completion"
proof -
  let ?I = "canonical_dw_implementation sf0"
  have pre: "dwi_trace ?I (dwi_initial ?I) (sdwc_pre sf_completion) sf0"
    unfolding sf_completion_def canonical_dw_implementation_def
    by (simp, rule dwi_trace.dwi_trace_refl)
  have src: "dwi_step ?I sf0
      (DoSource (sdwc_source_at sf_completion) (sdwc_event sf_completion))
      sf_src"
    using sf_step_src
    by (simp add: sf_completion_def canonical_dw_implementation_def)
  have ack: "dwi_step ?I sf_src
      (Ack (sdwc_source_at sf_completion) (sdwc_event sf_completion))
      sf_ack"
    using sf_step_ack
    by (simp add: sf_completion_def canonical_dw_implementation_def)
  have enq: "dwi_step ?I sf_ack
      (EnqueueDownstream (sdwc_down_at sf_completion)
        (sdwc_down_event sf_completion))
      sf_enq"
    using sf_step_enq
    by (simp add: sf_completion_def canonical_dw_implementation_def)
  have down: "dwi_step ?I sf_enq
      (DoDownstream (sdwc_down_at sf_completion)
        (sdwc_down_event sf_completion))
      sf_down"
    using sf_step_down
    by (simp add: sf_completion_def canonical_dw_implementation_def)
  from pre src ack enq down show ?thesis
    unfolding source_first_separated_dual_write_schedule_def by blast
qed

lemma sf_completion_source_first:
  "source_first_separable_completion
     (canonical_dw_implementation sf0) sf_completion"
  using sf_completion_schedule
  by (simp add: source_first_separable_completion_def sf_completion_def
                sf0_def canonical_dw_implementation_def dwi_refines_exec_def
                initial_exec_state_def running_labels_def running_label_def
                effective_source_effect_def same_downstream_effect_def
                no_visible_key_events_def ec_defs)

lemma sf_impl_separable_non_atomic_crash_closed:
  "separable_non_atomic_crash_closed_dual_write_implementation
     (canonical_dw_implementation sf0)"
  unfolding separable_non_atomic_crash_closed_dual_write_implementation_def
            separable_non_atomic_dual_write_implementation_def
            separable_non_atomic_dual_write_completion_def
  using canonical_dw_implementation_crash_closed sf_completion_source_first
  by (auto intro!: exI[of _ sf_completion] exI[of _ Source_Effect]
           simp: separated_completion_first_side_def)

lemma sf_crash_dwi_trace:
  "dwi_trace (canonical_dw_implementation sf0)
     (dwi_initial (canonical_dw_implementation sf0))
     [DoSource ec1 (Update 0 2), Ack ec1 (Update 0 2), Crash ec1] sf_crash"
proof -
  have init: "dwi_initial (canonical_dw_implementation sf0) = sf0"
    by (simp add: canonical_dw_implementation_def)
  show ?thesis
    unfolding init
    by (rule dw_exec_trace_imp_canonical_dwi_trace[OF sf_crash_trace])
qed

text \<open>The witness's crashed state is WELLFORMED, so the last-based
  @{const ack_adv} discipline is exactly the covered acked frontier there.\<close>

lemma sf_crash_wellformed: "wellformed_exec_state sf_crash"
proof -
  have wf0: "wellformed_exec_state sf0" by (simp add: sf0_def)
  have p1: "exec_label_preserves_history_wf sf0 (DoSource ec1 (Update 0 2))"
    by (simp add: exec_label_preserves_history_wf_def sf0_def
                  initial_exec_state_def history_can_append_def ec_defs)
  have wf1: "wellformed_exec_state sf_src"
    by (rule dw_exec_step_wellformed_exec_state[OF sf_step_src wf0 p1])
  have p2: "exec_label_preserves_history_wf sf_src (Ack ec1 (Update 0 2))"
    by (simp add: exec_label_preserves_history_wf_def sf_src_def sf0_def
                  initial_exec_state_def history_can_append_def ec_defs)
  have wf2: "wellformed_exec_state sf_ack"
    by (rule dw_exec_step_wellformed_exec_state[OF sf_step_ack wf1 p2])
  have p3: "exec_label_preserves_history_wf sf_ack (Crash ec1)"
    by (simp add: exec_label_preserves_history_wf_def)
  show ?thesis
    by (rule dw_exec_step_wellformed_exec_state[OF sf_step_crash wf2 p3])
qed

theorem seam_witness_acked_frontier:
  "separable_non_atomic_crash_closed_dual_write_implementation
     (canonical_dw_implementation sf0)
 \<and> dwi_trace (canonical_dw_implementation sf0)
     (dwi_initial (canonical_dw_implementation sf0))
     [DoSource ec1 (Update 0 2), Ack ec1 (Update 0 2), Crash ec1] sf_crash
 \<and> dwi_state (canonical_dw_implementation sf0) sf_crash = sf_crash
 \<and> ack_adv sf_crash = ec1
 \<and> c0 < ack_adv sf_crash
 \<and> (ack_adv sf_crash, Update 0 2) \<in> set (exec_acked sf_crash)
 \<and> (ack_adv sf_crash, Update 0 2) \<in> set (exec_src_hist sf_crash)
 \<and> key_of (Update 0 2 :: (nat, nat) source_event) \<in> exec_scope sf_crash
 \<and> observable_mismatch sf_crash (ack_adv sf_crash) 0
 \<and> acked_observable_mismatch sf_crash (ack_adv sf_crash) 0"
  by (intro conjI sf_impl_separable_non_atomic_crash_closed sf_crash_dwi_trace
            ack_adv_sf_crash ack_adv_sf_crash_loaded
            sf_crash_observable_mismatch sf_crash_acked_observable_mismatch)
     (simp_all add: canonical_dw_implementation_def ack_adv_sf_crash
                    sf_crash_fields)


section \<open>Witness B: the RELAY'S OWN adv function on a dual writer\<close>

text \<open>
  The landed downstream-first stale-update family, unchanged: over base
  @{term "[0 \<mapsto> 1]"} the dual writer delivers @{term "Update 0 2"} downstream
  at @{const ec1} FIRST, then crashes at @{const ec1} before the source leg
  (planned at @{const ec3}) commits.  The crashed state's @{const adv} --- the
  EXACT function under which the relay is proved safe --- is @{const ec1},
  loaded and in scope, and the state is observably mismatched exactly there.
\<close>

definition df_crash :: "(nat, nat) dw_exec_state" where
  "df_crash = downstream_first_stale_update_down_done
                \<lparr>exec_status := Crashed ec1\<rparr>"

lemma df_crash_fields:
  "exec_base df_crash = [0 \<mapsto> 1]"
  "exec_src_hist df_crash = []"
  "exec_down_hist df_crash = [(ec1, Update 0 2)]"
  "exec_scope df_crash = {0}"
  "exec_finish df_crash = ec3"
  "exec_status df_crash = Crashed ec1"
  by (simp_all add: df_crash_def downstream_first_stale_update_down_done_def
                    downstream_first_stale_update_enqueued_def
                    downstream_first_stale_update_initial_def
                    initial_exec_state_def)

lemma df_crash_dw_exec_trace:
  "dw_exec_trace downstream_first_stale_update_initial
     [EnqueueDownstream ec1 (Update 0 2), DoDownstream ec1 (Update 0 2),
      Crash ec1] df_crash"
proof -
  have labels:
    "separated_completion_bad_crash_labels Downstream_Effect
       downstream_first_stale_update_completion =
     [EnqueueDownstream ec1 (Update 0 2), DoDownstream ec1 (Update 0 2),
      Crash ec1]"
    by (simp add: separated_completion_bad_crash_labels_def
                  separated_completion_bad_precrash_labels_def
                  separated_completion_crash_frontier_def
                  downstream_first_stale_update_completion_def)
  show ?thesis
    using admissible_dw_exec_trace_imp_dw_exec_trace
            [OF downstream_first_stale_update_bad_crash_admissible_trace]
    unfolding labels df_crash_def .
qed

lemma df_crash_dwi_trace:
  "dwi_trace (canonical_dw_implementation downstream_first_stale_update_initial)
     (dwi_initial
        (canonical_dw_implementation downstream_first_stale_update_initial))
     [EnqueueDownstream ec1 (Update 0 2), DoDownstream ec1 (Update 0 2),
      Crash ec1] df_crash"
proof -
  have init:
    "dwi_initial
       (canonical_dw_implementation downstream_first_stale_update_initial)
     = downstream_first_stale_update_initial"
    by (simp add: canonical_dw_implementation_def)
  show ?thesis
    unfolding init
    by (rule dw_exec_trace_imp_canonical_dwi_trace[OF df_crash_dw_exec_trace])
qed

lemma adv_df_crash: "adv df_crash = ec1"
  by (simp add: adv_def df_crash_fields)

lemma adv_df_crash_loaded: "c0 < adv df_crash"
  by (simp add: adv_df_crash ec1_def)

lemma df_crash_observable_mismatch_at_adv:
  "observable_mismatch df_crash (adv df_crash) 0"
  unfolding adv_df_crash
proof (rule observable_mismatchI)
  show "exec_status df_crash = Crashed ec1" by (simp add: df_crash_fields)
  show "ec1 \<le> exec_finish df_crash" by (simp add: df_crash_fields ec_defs)
  show "0 \<in> exec_scope df_crash" by (simp add: df_crash_fields)
  show "Src (exec_base df_crash) (exec_down_hist df_crash) ec1 0
        \<noteq> Src (exec_base df_crash) (exec_src_hist df_crash) ec1 0"
    by (simp add: df_crash_fields Src_def latest_src_event_def Let_def ec_ord)
qed

lemma df_impl_separable_non_atomic_crash_closed:
  "separable_non_atomic_crash_closed_dual_write_implementation
     (canonical_dw_implementation downstream_first_stale_update_initial)"
  using canonical_dw_implementation_crash_closed
        downstream_first_stale_update_completion_inhabits_separable_non_atomic
  by (auto simp: separable_non_atomic_crash_closed_dual_write_implementation_def
                 separable_non_atomic_dual_write_implementation_def)

theorem seam_witness_delivered_frontier:
  "separable_non_atomic_crash_closed_dual_write_implementation
     (canonical_dw_implementation downstream_first_stale_update_initial)
 \<and> dwi_trace (canonical_dw_implementation downstream_first_stale_update_initial)
     (dwi_initial
        (canonical_dw_implementation downstream_first_stale_update_initial))
     [EnqueueDownstream ec1 (Update 0 2), DoDownstream ec1 (Update 0 2),
      Crash ec1] df_crash
 \<and> dwi_state (canonical_dw_implementation downstream_first_stale_update_initial)
     df_crash = df_crash
 \<and> adv df_crash = ec1
 \<and> c0 < adv df_crash
 \<and> (adv df_crash, Update 0 2) \<in> set (exec_down_hist df_crash)
 \<and> key_of (Update 0 2 :: (nat, nat) source_event) \<in> exec_scope df_crash
 \<and> observable_mismatch df_crash (adv df_crash) 0"
  by (intro conjI df_impl_separable_non_atomic_crash_closed df_crash_dwi_trace
            adv_df_crash adv_df_crash_loaded df_crash_observable_mismatch_at_adv)
     (simp_all add: canonical_dw_implementation_def adv_df_crash
                    df_crash_fields)


section \<open>The same-contract separation headline\<close>

text \<open>
  Both sides of the safe/unsafe dichotomy evaluated under ONE contract: the
  SAME advertised-frontier function @{const adv} and the SAME predicate
  @{const observable_mismatch}, each on a genuinely reachable crashed state
  whose advertised frontier is loaded (@{text "> c0"}, an in-scope delivered
  event sits at it).  The relay crashes AT its advertised frontier and shows
  no observable mismatch; the separable non-atomic dual writer crashes AT its
  advertised frontier and is observably mismatched.
\<close>

definition w_safe_crash :: "(nat, nat) dw_exec_state" where
  "w_safe_crash = w_src3\<lparr>exec_status := Crashed ec2\<rparr>"

lemma w_src3_status_running: "exec_status w_src3 = Running"
  by (simp add: w_src3_def w_down2_def w_enq2_def w_src2_def w0_def
                initial_exec_state_def)

lemma w_step_crash_ec2: "relay_step w_src3 (Crash ec2) w_safe_crash"
  unfolding relay_step_def relay_admits_def w_safe_crash_def
  by (intro conjI dw_exec_step.crash)
     (simp_all add: w_src3_status_running exec_label_preserves_history_wf_def)

lemma w_safe_crash_reachable:
  "dwi_trace (I_relay_labels w0) (dwi_initial (I_relay_labels w0))
     [DoSource ec2 (Insert 0 7), EnqueueDownstream ec2 (Insert 0 7),
      DoDownstream ec2 (Insert 0 7), DoSource ec3 (Insert 0 9), Crash ec2]
     w_safe_crash"
proof -
  have init: "dwi_initial (I_relay_labels w0) = w0" by (simp add: I_relay_labels_def)
  show ?thesis
    unfolding init
    by (rule dwi_trace.dwi_trace_step[OF relay_dwi_stepI[OF w_step_src2]],
        rule dwi_trace.dwi_trace_step[OF relay_dwi_stepI[OF w_step_enq2]],
        rule dwi_trace.dwi_trace_step[OF relay_dwi_stepI[OF w_step_down2]],
        rule dwi_trace.dwi_trace_step[OF relay_dwi_stepI[OF w_step_src3]],
        rule dwi_trace.dwi_trace_step[OF relay_dwi_stepI[OF w_step_crash_ec2]],
        rule dwi_trace.dwi_trace_refl)
qed

lemma adv_w_safe_crash: "adv w_safe_crash = ec2"
  by (simp add: w_safe_crash_def adv_def w_src3_fields)

lemma adv_w_safe_crash_loaded: "c0 < adv w_safe_crash"
  by (simp add: adv_w_safe_crash ec2_def)

lemma w_safe_crash_down_hist:
  "exec_down_hist w_safe_crash = [(ec2, Insert 0 7)]"
  by (simp add: w_safe_crash_def w_src3_fields)

lemma w_safe_crash_complete_at_adv:
  "relay_complete_through w_safe_crash (adv w_safe_crash)"
  by (simp add: relay_complete_through_def replay_down_hist_def
                w_safe_crash_def w_src3_fields adv_def ec_ord)

lemma w_safe_crash_no_observable_mismatch_at_adv:
  "\<not> observable_mismatch w_safe_crash (adv w_safe_crash) 0"
  unfolding adv_w_safe_crash
  unfolding w_safe_crash_def
  by (rule w_no_observable_mismatch_at_ec2_via_invariant)

theorem advertised_frontier_separation:
  \<comment> \<open>SAFE side: the verified relay, crashed AT its own advertised frontier\<close>
  "dwi_trace (I_relay_labels w0) (dwi_initial (I_relay_labels w0))
     [DoSource ec2 (Insert 0 7), EnqueueDownstream ec2 (Insert 0 7),
      DoDownstream ec2 (Insert 0 7), DoSource ec3 (Insert 0 9), Crash ec2]
     w_safe_crash
 \<and> c0 < adv w_safe_crash
 \<and> (adv w_safe_crash, Insert 0 7) \<in> set (exec_down_hist w_safe_crash)
 \<and> relay_complete_through w_safe_crash (adv w_safe_crash)
 \<and> \<not> observable_mismatch w_safe_crash (adv w_safe_crash) 0
  \<comment> \<open>UNSAFE side: a crash-closed separable non-atomic dual writer, crashed
      AT its own advertised frontier --- same @{const adv}, same predicate\<close>
 \<and> separable_non_atomic_crash_closed_dual_write_implementation
     (canonical_dw_implementation downstream_first_stale_update_initial)
 \<and> dwi_trace (canonical_dw_implementation downstream_first_stale_update_initial)
     (dwi_initial
        (canonical_dw_implementation downstream_first_stale_update_initial))
     [EnqueueDownstream ec1 (Update 0 2), DoDownstream ec1 (Update 0 2),
      Crash ec1] df_crash
 \<and> c0 < adv df_crash
 \<and> (adv df_crash, Update 0 2) \<in> set (exec_down_hist df_crash)
 \<and> observable_mismatch df_crash (adv df_crash) 0"
  by (intro conjI w_safe_crash_reachable adv_w_safe_crash_loaded
            w_safe_crash_complete_at_adv
            w_safe_crash_no_observable_mismatch_at_adv
            df_impl_separable_non_atomic_crash_closed df_crash_dwi_trace
            adv_df_crash_loaded df_crash_observable_mismatch_at_adv)
     (simp_all add: adv_w_safe_crash adv_df_crash w_safe_crash_down_hist
                    df_crash_fields)


section \<open>Class level: every separable completion, every covering discipline\<close>

text \<open>
  Source-first side.  For ANY implementation with a source-first separable
  completion, ANY crash-closed step relation, and ANY advertising discipline
  that covers acked source writes, the run source-commit; ack; crash is
  concretely reachable and its final state is observably (indeed
  acked-observably) mismatched at the completion's own source coordinate ---
  which the state has acked, hence lies inside the advertised region.
  No monotonicity of the discipline is needed.
\<close>

theorem source_first_completion_mismatch_at_acked_advertised_frontier:
  fixes A :: "('k, 'v) dw_exec_state \<Rightarrow> src_coord"
  assumes first: "source_first_separable_completion I C"
      and closed: "crash_closed_implementation I"
      and cover: "advertises_acked A"
  shows "\<exists>s_c.
      dwi_trace I (dwi_initial I)
        (sdwc_pre C @ [DoSource (sdwc_source_at C) (sdwc_event C),
                       Ack (sdwc_source_at C) (sdwc_event C),
                       Crash (sdwc_source_at C)]) s_c
    \<and> (sdwc_source_at C, sdwc_event C) \<in> set (exec_acked (dwi_state I s_c))
    \<and> ack_adv (dwi_state I s_c) = sdwc_source_at C
    \<and> sdwc_source_at C \<le> A (dwi_state I s_c)
    \<and> observable_mismatch (dwi_state I s_c) (sdwc_source_at C) (sdwc_key C)
    \<and> acked_observable_mismatch (dwi_state I s_c) (sdwc_source_at C)
        (sdwc_key C)
    \<and> diverges (proto_of_exec_at (dwi_state I s_c) (sdwc_source_at C))
        (sdwc_source_at C)"
proof -
  let ?c = "sdwc_source_at C"
  let ?e = "sdwc_event C"
  let ?k = "sdwc_key C"
  let ?s0 = "dwi_state I (dwi_initial I)"
  from first have refines: "dwi_refines_exec I"
      and schedule: "source_first_separated_dual_write_schedule I C"
      and pre_running: "running_labels (sdwc_pre C)"
      and start: "exec_status ?s0 = Running"
      and key: "key_of ?e = ?k"
      and effect: "effective_source_effect (exec_base ?s0) ?e ?k"
      and scoped: "?k \<in> exec_scope ?s0"
      and crash_le_fin: "?c \<le> exec_finish ?s0"
      and no_down:
        "no_visible_key_events
           (exec_down_hist ?s0 @ down_hist_of_labels (sdwc_pre C)) ?c ?k"
    by (auto simp: source_first_separable_completion_def)
  from schedule obtain s_pre s_src s_ack where
      pre: "dwi_trace I (dwi_initial I) (sdwc_pre C) s_pre"
      and stepS: "dwi_step I s_pre (DoSource ?c ?e) s_src"
      and stepA: "dwi_step I s_src (Ack ?c ?e) s_ack"
    by (auto simp: source_first_separated_dual_write_schedule_def)
  have two: "dwi_trace I s_pre [DoSource ?c ?e, Ack ?c ?e] s_ack"
    by (rule dwi_trace.dwi_trace_step[OF stepS],
        rule dwi_trace.dwi_trace_step[OF stepA],
        rule dwi_trace.dwi_trace_refl)
  have upto_ack:
    "dwi_trace I (dwi_initial I)
       (sdwc_pre C @ [DoSource ?c ?e] @ [Ack ?c ?e]) s_ack"
    using dwi_trace_append[OF pre two] by simp
  have running_upto:
    "running_labels (sdwc_pre C @ [DoSource ?c ?e] @ [Ack ?c ?e])"
    using pre_running by (simp add: running_labels_def running_label_def)
  have exec_upto:
    "dw_exec_trace ?s0 (sdwc_pre C @ [DoSource ?c ?e] @ [Ack ?c ?e])
       (dwi_state I s_ack)"
    by (rule dwi_trace_refines_exec[OF refines upto_ack])
  have ack_running: "exec_status (dwi_state I s_ack) = Running"
    by (rule dw_exec_trace_running_status[OF exec_upto running_upto start])
  have ack_finish: "exec_finish (dwi_state I s_ack) = exec_finish ?s0"
    by (rule dw_exec_trace_finish[OF exec_upto])
  have ack_le_fin: "?c \<le> exec_finish (dwi_state I s_ack)"
    using crash_le_fin ack_finish by simp
  have "\<exists>s_c. dwi_step I s_ack (Crash ?c) s_c"
    using closed upto_ack ack_running ack_le_fin
    unfolding crash_closed_implementation_def by blast
  then obtain s_c where crash: "dwi_step I s_ack (Crash ?c) s_c" by blast
  have crash_trace: "dwi_trace I s_ack [Crash ?c] s_c"
    by (rule dwi_trace.dwi_trace_step[OF crash dwi_trace.dwi_trace_refl])
  have full:
    "dwi_trace I (dwi_initial I)
       (sdwc_pre C @ [DoSource ?c ?e] @ [Ack ?c ?e] @ [Crash ?c]) s_c"
    using dwi_trace_append[OF upto_ack crash_trace] by simp
  \<comment> \<open>abstract engine: gap = the Ack label\<close>
  have no_later: "no_visible_key_events (src_hist_of_labels [Ack ?c ?e]) ?c ?k"
    by (simp add: no_visible_key_events_def)
  have stale:
    "Src (exec_base ?s0)
       (exec_down_hist ?s0 @ down_hist_of_labels (sdwc_pre C)
         @ down_hist_of_labels [Ack ?c ?e]) ?c ?k
     \<noteq> event_result ?e"
    using effective_source_no_visible_downstream_imp_stale[OF effect no_down]
    by simp
  have acked_in:
    "(?c, ?e) \<in> set (exec_acked ?s0
        @ acked_hist_of_labels (sdwc_pre C @ [DoSource ?c ?e] @ [Ack ?c ?e]))"
    by simp
  from executable_source_window_acked_bad_crash_extension
        [OF exec_upto running_upto start key scoped order_refl crash_le_fin
            no_later stale acked_in]
  obtain s_abs where
      abs_trace:
        "dw_exec_trace ?s0
           (sdwc_pre C @ [DoSource ?c ?e] @ [Ack ?c ?e] @ [Crash ?c]) s_abs"
      and obs: "observable_mismatch s_abs ?c ?k"
      and ackobs: "acked_observable_mismatch s_abs ?c ?k"
      and div: "diverges (proto_of_exec_at s_abs ?c) ?c"
    by blast
  have concrete_exec:
    "dw_exec_trace ?s0
       (sdwc_pre C @ [DoSource ?c ?e] @ [Ack ?c ?e] @ [Crash ?c])
       (dwi_state I s_c)"
    by (rule dwi_trace_refines_exec[OF refines full])
  have same: "dwi_state I s_c = s_abs"
    by (rule dw_exec_trace_deterministic[OF concrete_exec abs_trace])
  have mem: "(?c, ?e) \<in> set (exec_acked (dwi_state I s_c))"
    using dw_exec_trace_acked[OF concrete_exec] by simp
  \<comment> \<open>the completion's Ack is the LAST acked entry, so the natural last-based
      discipline evaluates to exactly the crash coordinate --- no coverage or
      wellformedness premise is needed for @{const ack_adv} itself\<close>
  have ack_adv_eq: "ack_adv (dwi_state I s_c) = ?c"
    using dw_exec_trace_acked[OF concrete_exec] by (simp add: ack_adv_def)
  have adv_le: "?c \<le> A (dwi_state I s_c)"
    using cover mem by (auto simp: advertises_acked_def)
  have full':
    "dwi_trace I (dwi_initial I)
       (sdwc_pre C @ [DoSource ?c ?e, Ack ?c ?e, Crash ?c]) s_c"
    using full by simp
  from full' mem ack_adv_eq adv_le obs ackobs div same show ?thesis by auto
qed

text \<open>
  Downstream-first side.  Same statement shape with the delivered-coverage
  premise: the completion's downstream delivery is the advertisement, and the
  crash before the source leg lands inside the advertised region.
\<close>

theorem downstream_first_completion_mismatch_at_delivered_advertised_frontier:
  fixes A :: "('k, 'v) dw_exec_state \<Rightarrow> src_coord"
  assumes first: "downstream_first_separable_completion I C"
      and closed: "crash_closed_implementation I"
      and cover: "advertises_delivered A"
  shows "\<exists>s_c.
      dwi_trace I (dwi_initial I)
        (separated_completion_bad_crash_labels Downstream_Effect C) s_c
    \<and> (sdwc_down_at C, sdwc_down_event C)
        \<in> set (exec_down_hist (dwi_state I s_c))
    \<and> adv (dwi_state I s_c) = sdwc_down_at C
    \<and> sdwc_down_at C \<le> A (dwi_state I s_c)
    \<and> observable_mismatch (dwi_state I s_c) (sdwc_down_at C) (sdwc_key C)"
proof -
  have side: "separated_completion_first_side I C Downstream_Effect"
    by (simp add: separated_completion_first_side_def first)
  from downstream_first_separable_completion_has_abstract_bad_crash_execution
        [OF first]
  obtain s_abs where bad_abs:
    "separated_completion_abstract_bad_crash_execution I C Downstream_Effect
       s_abs"
    by blast
  from separated_completion_crash_closed_lifts_abstract_bad_execution
        [OF closed side bad_abs]
  obtain s_c where conc:
    "separated_completion_concrete_bad_crash_execution I C Downstream_Effect
       s_c"
    by blast
  from conc have trace:
      "dwi_trace I (dwi_initial I)
         (separated_completion_bad_crash_labels Downstream_Effect C) s_c"
      and obs:
        "observable_mismatch (dwi_state I s_c)
           (separated_completion_crash_frontier Downstream_Effect C)
           (sdwc_key C)"
    by (auto simp: separated_completion_concrete_bad_crash_execution_def)
  have refines: "dwi_refines_exec I"
    by (rule separated_completion_first_side_refines[OF side])
  have exec:
    "dw_exec_trace (dwi_state I (dwi_initial I))
       (separated_completion_bad_crash_labels Downstream_Effect C)
       (dwi_state I s_c)"
    by (rule dwi_trace_refines_exec[OF refines trace])
  have mem:
    "(sdwc_down_at C, sdwc_down_event C)
       \<in> set (exec_down_hist (dwi_state I s_c))"
    using dw_exec_trace_down_hist[OF exec]
    by (simp add: separated_completion_bad_crash_labels_def
                  separated_completion_bad_precrash_labels_def)
  \<comment> \<open>the completion's delivery is the LAST downstream entry, so the RELAY'S
      OWN @{const adv} evaluates to exactly the crash coordinate here\<close>
  have adv_eq: "adv (dwi_state I s_c) = sdwc_down_at C"
    using dw_exec_trace_down_hist[OF exec]
    by (simp add: adv_def separated_completion_bad_crash_labels_def
                  separated_completion_bad_precrash_labels_def)
  have le: "sdwc_down_at C \<le> A (dwi_state I s_c)"
    using cover mem by (auto simp: advertises_delivered_def)
  from trace mem adv_eq le obs show ?thesis
    by (auto simp: separated_completion_crash_frontier_def)
qed

text \<open>
  Unified corollary: EVERY separable non-atomic completion, under EVERY
  discipline covering both confirmation channels, reaches an observable
  mismatch inside its own advertised region.  The premise pair is inhabited
  by @{const dual_write_frontier_sup} and refuted by the never-advertising
  discipline (below), so the class is neither empty nor gerrymandered.
\<close>

corollary separable_non_atomic_completion_mismatch_at_advertised_frontier:
  fixes A :: "('k, 'v) dw_exec_state \<Rightarrow> src_coord"
  assumes sep: "separable_non_atomic_dual_write_completion I C"
      and closed: "crash_closed_implementation I"
      and cover_a: "advertises_acked A"
      and cover_d: "advertises_delivered A"
  shows "\<exists>xs s_c f.
      dwi_trace I (dwi_initial I) xs s_c
    \<and> f \<le> A (dwi_state I s_c)
    \<and> observable_mismatch (dwi_state I s_c) f (sdwc_key C)"
proof -
  from sep obtain side where side: "separated_completion_first_side I C side"
    by (auto simp: separable_non_atomic_dual_write_completion_def)
  show ?thesis
  proof (cases side)
    case Source_Effect
    with side have "source_first_separable_completion I C"
      by (simp add: separated_completion_first_side_def)
    from source_first_completion_mismatch_at_acked_advertised_frontier
          [OF this closed cover_a]
    show ?thesis by blast
  next
    case Downstream_Effect
    with side have "downstream_first_separable_completion I C"
      by (simp add: separated_completion_first_side_def)
    from downstream_first_completion_mismatch_at_delivered_advertised_frontier
          [OF this closed cover_d]
    show ?thesis by blast
  qed
qed

corollary separable_completion_mismatch_at_sup_advertised_frontier:
  assumes sep: "separable_non_atomic_dual_write_completion I C"
      and closed: "crash_closed_implementation I"
  shows "\<exists>xs s_c f.
      dwi_trace I (dwi_initial I) xs s_c
    \<and> f \<le> dual_write_frontier_sup (dwi_state I s_c)
    \<and> observable_mismatch (dwi_state I s_c) f (sdwc_key C)"
  by (rule separable_non_atomic_completion_mismatch_at_advertised_frontier
        [OF sep closed dual_write_frontier_sup_advertises_acked
            dual_write_frontier_sup_advertises_delivered])

text \<open>The class theorem FIRES on the concrete witness: its premises are
  jointly inhabited, so the class is nonempty --- the general statement is
  not vacuously universal.\<close>

corollary class_theorem_fires_on_witness:
  "\<exists>s_c.
      dwi_trace (canonical_dw_implementation sf0)
        (dwi_initial (canonical_dw_implementation sf0))
        (sdwc_pre sf_completion
           @ [DoSource (sdwc_source_at sf_completion) (sdwc_event sf_completion),
              Ack (sdwc_source_at sf_completion) (sdwc_event sf_completion),
              Crash (sdwc_source_at sf_completion)]) s_c
    \<and> sdwc_source_at sf_completion
        \<le> acked_frontier_sup
             (dwi_state (canonical_dw_implementation sf0) s_c)
    \<and> observable_mismatch (dwi_state (canonical_dw_implementation sf0) s_c)
        (sdwc_source_at sf_completion) (sdwc_key sf_completion)"
  using source_first_completion_mismatch_at_acked_advertised_frontier
          [OF sf_completion_source_first canonical_dw_implementation_crash_closed
              advertises_acked_sup]
  by blast


section \<open>Non-vacuity audit of the class premises\<close>

text \<open>The never-advertising discipline violates acked coverage: the acked
  witness state has a confirmed write strictly above @{const c0}.\<close>

lemma never_advertising_violates_acked_coverage:
  "\<not> advertises_acked ((\<lambda>_. c0) :: (nat, nat) dw_exec_state \<Rightarrow> src_coord)"
proof
  assume adv0:
    "advertises_acked ((\<lambda>_. c0) :: (nat, nat) dw_exec_state \<Rightarrow> src_coord)"
  have "(ec1, Update 0 2) \<in> set (exec_acked sf_crash)"
    by (simp add: sf_crash_fields)
  with adv0 have "ec1 \<le> c0" by (auto simp: advertises_acked_def)
  thus False by (simp add: ec1_def c0_eq_coord_of_nat_0)
qed

lemma never_advertising_violates_delivered_coverage:
  "\<not> advertises_delivered ((\<lambda>_. c0) :: (nat, nat) dw_exec_state \<Rightarrow> src_coord)"
proof
  assume adv0:
    "advertises_delivered ((\<lambda>_. c0) :: (nat, nat) dw_exec_state \<Rightarrow> src_coord)"
  have "(ec1, Update 0 2) \<in> set (exec_down_hist df_crash)"
    by (simp add: df_crash_fields)
  with adv0 have "ec1 \<le> c0" by (auto simp: advertises_delivered_def)
  thus False by (simp add: ec1_def c0_eq_coord_of_nat_0)
qed

text \<open>The sup disciplines evaluate to the LOADED frontier @{const ec1} on the
  witness states --- the class premise's canonical inhabitant genuinely
  advertises the frontier at which the mismatch sits.\<close>

lemma c0_le_src_coord: "c0 \<le> (x :: src_coord)"
  by (metis bot.extremum bot_src_coord_def)

lemma acked_frontier_sup_sf_crash: "acked_frontier_sup sf_crash = ec1"
proof -
  have "acked_frontier_sup sf_crash = Max (insert c0 {ec1})"
    by (simp add: acked_frontier_sup_def sf_crash_fields)
  also have "\<dots> = max c0 ec1" by simp
  also have "\<dots> = ec1" using c0_le_src_coord by (simp add: max_def)
  finally show ?thesis .
qed

lemma dual_write_frontier_sup_df_crash:
  "dual_write_frontier_sup df_crash = ec1"
proof -
  have acked_df: "exec_acked df_crash = []"
    by (simp add: df_crash_def downstream_first_stale_update_down_done_def
                  downstream_first_stale_update_enqueued_def
                  downstream_first_stale_update_initial_def
                  initial_exec_state_def)
  have "dual_write_frontier_sup df_crash = Max (insert c0 {ec1})"
    by (simp add: dual_write_frontier_sup_def acked_df df_crash_fields)
  also have "\<dots> = max c0 ec1" by simp
  also have "\<dots> = ec1" using c0_le_src_coord by (simp add: max_def)
  finally show ?thesis .
qed

end
