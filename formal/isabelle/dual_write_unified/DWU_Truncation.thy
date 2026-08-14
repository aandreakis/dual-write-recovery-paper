(*  Title:       DWU_Truncation.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Purpose: Road-2 I5 --- U15 (fabricate-or-abandon, THE TRUNCATION HEADLINER)
             plus the U14 phantom family (U14a-d).

    "After a truncating crash the surviving journal is a length (an LSN) but not
    a content: two runs that truncate to the SAME store (and the same retained
    8-tuple view) can carry different surviving journals, and no
    retained-measured recovery policy can tell them apart --- it must either
    FABRICATE (accept an emission the journal cannot justify) or ABANDON (drop
    an emission the journal still owes)."  The witnesses ride the
    truncate-to-EMPTY trick: a DoSource is a pure exec_src_hist append, and
    UTruncCrash at c0 erases it identically in both worlds, so two worlds that
    differ only in the first committed event collapse to a LITERALLY-EQUAL
    crashed store, differing only in the surviving journal content.

    The two-horn export u_truncation_fabricate_or_abandon (section 3.5)
    restates U15 with the defeat conjunct sharpened to
    (u_premature \/ u_lost_journal): the FABRICATE branch's proved u_premature
    is exported as-is, so FABRICATE-or-ABANDON as glossed above holds at
    STATEMENT grade.  Same witnesses, same redrives; the pinned U15 statement
    is unchanged.

    Everything predicate/class/auxiliary is LANDED in DWU_Machine and REUSED
    here (u_retained_view, u_retained_measured, u_policy_redrive, u_lost_journal,
    u_justified/u_premature, the S7 live auxiliaries u_justified_live/
    u_premature_live, is_ulog/ulog_of).  This theory adds only witness states +
    witness-evaluation helper lemmas.

    Honesty regime: quick_and_dirty = false (ROOT-pinned), ZERO sorry, ZERO oops,
    no axiomatization, no consts, no oracles.  Every principal is PROVED.
    The six pinned statements are copied BYTE-IDENTICAL from the Stage-4 probe
    seed (DWU_Statement_Probe.thy).
*)

theory DWU_Truncation
  imports DWU_Recovery_Floor
begin

section \<open>0. The three business events and the surviving emission\<close>

text \<open>Two in-scope events at key 0 that differ only in value, and one out-of-scope
  event at key 2.  Key 0 and 1 are in the pinned scope @{term "{0, 1}"}; key 2 is
  not.  All three sit at coordinate @{const ec1} (so a truncation at @{const c0}
  erases them from the live source identically).\<close>

definition tt_e :: "(nat, nat) source_event" where "tt_e = Update 0 5"
definition tt_e2 :: "(nat, nat) source_event" where "tt_e2 = Update 2 5"
definition tt_ep :: "(nat, nat) source_event" where "tt_ep = Update 0 7"

text \<open>The one already-published emission: stamp 1 (journal length at publish),
  gen 0, payload @{term "(ec1, tt_e)"}.  It survives truncation inside the
  accepted ledger while the live source that would justify it is erased.\<close>

definition tt_x :: "(nat, nat) uemission" where
  "tt_x = \<lparr> ue_stamp = 1, ue_gen = 0, ue_pay = ULog (ec1, tt_e) \<rparr>"

lemma tt_e_neq_e2 [simp]: "tt_e \<noteq> tt_e2"
  by (simp add: tt_e_def tt_e2_def)

lemma tt_e_neq_ep [simp]: "tt_e \<noteq> tt_ep"
  by (simp add: tt_e_def tt_ep_def)

text \<open>Single-element source-history wellformedness at @{const ec1}, event-agnostic.\<close>

lemma wfh_ec1: "wellformed_src_history [(ec1, e)]"
  by (rule wf_hist_single) (simp add: ec_defs)


section \<open>1. Common infrastructure: the redrive post-state\<close>

text \<open>The functional post-state of @{const u_policy_redrive}: heal the store
  (down-hist replayed, pending cleared, status Recovered), journal untouched,
  batch @{term B} stamped at @{term "(length (dwu_journal t), dwu_hwm t)"} and
  fence-resolved into sent/accepted.  This is exactly the pinned
  @{const u_policy_redrive} RHS with the policy value @{term B} in place of
  @{term "P t"}, so the redrive holds definitionally.\<close>

definition tt_redrive
  :: "(nat, nat) dwu_state \<Rightarrow> frontier
      \<Rightarrow> (src_coord \<times> (nat, nat) source_event) list \<Rightarrow> (nat, nat) dwu_state"
where
  "tt_redrive t f B =
     t\<lparr> dwu_store := (dwu_store t)
           \<lparr>exec_down_hist :=
              replay_down_hist (exec_src_hist (dwu_store t))
                (exec_scope (dwu_store t)) f,
            exec_pending := {},
            exec_status := Recovered\<rparr>,
        dwu_journal := dwu_journal t,
        dwu_sent := dwu_sent t
          @ stamped_at (length (dwu_journal t)) (dwu_hwm t) B,
        dwu_accepted := dwu_accepted t
          @ filter (\<lambda>x. dwu_fence t \<le> ue_gen x)
              (stamped_at (length (dwu_journal t)) (dwu_hwm t) B) \<rparr>"

lemma tt_redrive_enabled:
  assumes "\<exists>c. exec_status (dwu_store t) = Crashed c"
      and "f \<le> exec_finish (dwu_store t)"
  shows "u_policy_redrive P t f (tt_redrive t f (P t))"
  using assms by (simp add: u_policy_redrive_def tt_redrive_def)

lemma tt_redrive_journal [simp]: "dwu_journal (tt_redrive t f B) = dwu_journal t"
  by (simp add: tt_redrive_def)

lemma tt_redrive_accepted:
  "dwu_accepted (tt_redrive t f B) =
     dwu_accepted t
       @ filter (\<lambda>x. dwu_fence t \<le> ue_gen x)
           (stamped_at (length (dwu_journal t)) (dwu_hwm t) B)"
  by (simp add: tt_redrive_def)

lemma tt_redrive_scope [simp]:
  "exec_scope (dwu_store (tt_redrive t f B)) = exec_scope (dwu_store t)"
  by (simp add: tt_redrive_def)


section \<open>2. The initial state and the shared first source step\<close>

text \<open>The pinned init state @{term "dwu_init Map.empty {0,1} ec2"} is the landed
  @{const uW0}; @{thm rf_uW0_init} names that equality.  The first source step
  (commit @{term "(ec1, tt_e)"}) lands in @{text tt_A1}, shared by U15's W1 and
  the whole phantom family.\<close>

definition tt_A1 :: "(nat, nat) dwu_state" where
  "tt_A1 = mkU (mkC [(ec1, tt_e)] [] [] {} Running) [(ec1, tt_e)] [] [] [0 \<mapsto> UProd] 0"

lemma tt_wf_A1: "wellformed_exec_state (dwu_store tt_A1)"
  by (simp add: tt_A1_def mkU_def mkC_def ws_defs wf_hist_Nil wfh_ec1)

lemma tt_g_A1_src: "exec_label_preserves_history_wf (dwu_store uW0) (DoSource ec1 tt_e)"
  by (simp add: uW0_def mkU_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma tt_step_src1: "dwu_step uW0 (ULift 0 (DoSource ec1 tt_e)) tt_A1"
proof -
  have c: "dw_exec_step (dwu_store uW0) (DoSource ec1 tt_e)
             (mkC [(ec1, tt_e)] [] [] {} Running)"
    by (rule do_sourceI) (simp_all add: uW0_def mkU_def mkC_def)
  have "dwu_step uW0 (ULift 0 (DoSource ec1 tt_e))
          (uW0\<lparr>dwu_store := mkC [(ec1, tt_e)] [] [] {} Running,
               dwu_journal := dwu_journal uW0 @ [(ec1, tt_e)]\<rparr>)"
    by (rule dwu_step.ulift_source[OF _ _ c]) (simp_all add: uW0_def mkU_def)
  also have "\<dots> = tt_A1" by (simp add: uW0_def tt_A1_def mkU_def)
  finally show ?thesis .
qed

lemma tt_reach_A1: "dwu_reachable_w tt_A1"
proof -
  have r0: "dwu_reachable Map.empty {0, 1} ec2 uW0"
    unfolding rf_uW0_init by (rule dwu_reachable_init)
  show ?thesis by (rule dwu_reach_lift[OF r0 rf_wf0 tt_g_A1_src tt_step_src1])
qed


section \<open>3. U15 --- the fabricate-or-abandon truncation headliner\<close>

subsection \<open>3.1 The two crashed worlds W1, W2 (truncate-to-empty)\<close>

text \<open>@{text tt_A2} commits the OUT-OF-SCOPE event @{term "(ec1, tt_e2)"}; the
  crash boundary @{const c0} erases both first commits to the SAME empty crashed
  store, so W1 and W2 share every retained-view coordinate and differ only in the
  surviving journal.\<close>

definition tt_A2 :: "(nat, nat) dwu_state" where
  "tt_A2 = mkU (mkC [(ec1, tt_e2)] [] [] {} Running) [(ec1, tt_e2)] [] [] [0 \<mapsto> UProd] 0"

definition tt_W1 :: "(nat, nat) dwu_state" where
  "tt_W1 = mkU (mkC [] [] [] {} (Crashed ec2)) [(ec1, tt_e)] [] [] [0 \<mapsto> UProd] 0"

definition tt_W2 :: "(nat, nat) dwu_state" where
  "tt_W2 = mkU (mkC [] [] [] {} (Crashed ec2)) [(ec1, tt_e2)] [] [] [0 \<mapsto> UProd] 0"

lemma tt_wf_A2: "wellformed_exec_state (dwu_store tt_A2)"
  by (simp add: tt_A2_def mkU_def mkC_def ws_defs wf_hist_Nil wfh_ec1)

lemma tt_g_A2_src: "exec_label_preserves_history_wf (dwu_store uW0) (DoSource ec1 tt_e2)"
  by (simp add: uW0_def mkU_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma tt_step_src2: "dwu_step uW0 (ULift 0 (DoSource ec1 tt_e2)) tt_A2"
proof -
  have c: "dw_exec_step (dwu_store uW0) (DoSource ec1 tt_e2)
             (mkC [(ec1, tt_e2)] [] [] {} Running)"
    by (rule do_sourceI) (simp_all add: uW0_def mkU_def mkC_def)
  have "dwu_step uW0 (ULift 0 (DoSource ec1 tt_e2))
          (uW0\<lparr>dwu_store := mkC [(ec1, tt_e2)] [] [] {} Running,
               dwu_journal := dwu_journal uW0 @ [(ec1, tt_e2)]\<rparr>)"
    by (rule dwu_step.ulift_source[OF _ _ c]) (simp_all add: uW0_def mkU_def)
  also have "\<dots> = tt_A2" by (simp add: uW0_def tt_A2_def mkU_def)
  finally show ?thesis .
qed

text \<open>The truncate-to-empty crash step (both worlds collapse the source to []).\<close>

lemma tt_step_trunc1: "dwu_step tt_A1 (UTruncCrash c0 ec2) tt_W1"
proof -
  have "dwu_step tt_A1 (UTruncCrash c0 ec2)
          (tt_A1\<lparr>dwu_store := truncating_crash_state (dwu_store tt_A1) c0 ec2,
                 dwu_floor := min (dwu_floor tt_A1)
                   (length (exec_src_hist
                      (truncating_crash_state (dwu_store tt_A1) c0 ec2)))\<rparr>)"
    by (rule dwu_step.utrunccrash[OF tt_wf_A1])
       (simp_all add: tt_A1_def mkU_def mkC_def less_eq_src_coord_def c0_least)
  also have "\<dots> = tt_W1"
    by (simp add: tt_A1_def tt_W1_def mkU_def mkC_def truncating_crash_state_def
                  truncating_crash_state_at_boundary_def durable_exec_state_at_boundary_def
                  durable_history_prefix_at_def single_durable_boundary_def
                  durable_pending_at_boundary_def durable_ack_frontier_def
                  ec_defs c0_eq_coord_of_nat_0)
  finally show ?thesis .
qed

lemma tt_step_trunc2: "dwu_step tt_A2 (UTruncCrash c0 ec2) tt_W2"
proof -
  have "dwu_step tt_A2 (UTruncCrash c0 ec2)
          (tt_A2\<lparr>dwu_store := truncating_crash_state (dwu_store tt_A2) c0 ec2,
                 dwu_floor := min (dwu_floor tt_A2)
                   (length (exec_src_hist
                      (truncating_crash_state (dwu_store tt_A2) c0 ec2)))\<rparr>)"
    by (rule dwu_step.utrunccrash[OF tt_wf_A2])
       (simp_all add: tt_A2_def mkU_def mkC_def less_eq_src_coord_def c0_least)
  also have "\<dots> = tt_W2"
    by (simp add: tt_A2_def tt_W2_def mkU_def mkC_def truncating_crash_state_def
                  truncating_crash_state_at_boundary_def durable_exec_state_at_boundary_def
                  durable_history_prefix_at_def single_durable_boundary_def
                  durable_pending_at_boundary_def durable_ack_frontier_def
                  ec_defs c0_eq_coord_of_nat_0)
  finally show ?thesis .
qed

lemma tt_reach_W1: "dwu_reachable_w tt_W1"
  by (rule dwu_reach_other[OF tt_reach_A1 _ _ tt_step_trunc1]) simp_all

lemma tt_reach_W2: "dwu_reachable_w tt_W2"
proof -
  have r0: "dwu_reachable Map.empty {0, 1} ec2 uW0"
    unfolding rf_uW0_init by (rule dwu_reachable_init)
  have rA2: "dwu_reachable_w tt_A2"
    by (rule dwu_reach_lift[OF r0 rf_wf0 tt_g_A2_src tt_step_src2])
  show ?thesis by (rule dwu_reach_other[OF rA2 _ _ tt_step_trunc2]) simp_all
qed

subsection \<open>3.2 The retained-view equality, the journal split, and the loss verdicts\<close>

lemma tt_views_eq: "u_retained_view tt_W1 = u_retained_view tt_W2"
  by (simp add: u_retained_view_def tt_W1_def tt_W2_def mkU_def)

lemma tt_journal_neq: "dwu_journal tt_W1 \<noteq> dwu_journal tt_W2"
  by (simp add: tt_W1_def tt_W2_def mkU_def)

lemma tt_lost_W1: "u_lost_journal ec2 tt_W1"
  by (simp add: u_lost_journal_def tt_W1_def mkU_def mkC_def replay_down_hist_def
                log_payloads_def map_filter_simps tt_e_def ec_defs)

lemma tt_notlost_W2: "\<not> u_lost_journal ec2 tt_W2"
  by (simp add: u_lost_journal_def tt_W2_def mkU_def mkC_def replay_down_hist_def
                log_payloads_def map_filter_simps tt_e2_def ec_defs)

subsection \<open>3.3 Field lemmas for the two redrive post-states\<close>

lemma tt_W1_fields [simp]:
  "dwu_journal tt_W1 = [(ec1, tt_e)]"
  "dwu_accepted tt_W1 = []"
  "dwu_fence tt_W1 = 0"
  "dwu_hwm tt_W1 = 0"
  "exec_scope (dwu_store tt_W1) = {0, 1}"
  by (simp_all add: tt_W1_def mkU_def mkC_def)

lemma tt_W2_fields [simp]:
  "dwu_journal tt_W2 = [(ec1, tt_e2)]"
  "dwu_accepted tt_W2 = []"
  "dwu_fence tt_W2 = 0"
  "dwu_hwm tt_W2 = 0"
  "exec_scope (dwu_store tt_W2) = {0, 1}"
  by (simp_all add: tt_W2_def mkU_def mkC_def)

lemma tt_W1_crashed: "\<exists>c. exec_status (dwu_store tt_W1) = Crashed c"
  by (simp add: tt_W1_def mkU_def mkC_def)

lemma tt_W2_crashed: "\<exists>c. exec_status (dwu_store tt_W2) = Crashed c"
  by (simp add: tt_W2_def mkU_def mkC_def)

lemma tt_W1_finish: "ec2 \<le> exec_finish (dwu_store tt_W1)"
  by (simp add: tt_W1_def mkU_def mkC_def)

lemma tt_W2_finish: "ec2 \<le> exec_finish (dwu_store tt_W2)"
  by (simp add: tt_W2_def mkU_def mkC_def)

subsection \<open>3.4 THE PRINCIPAL (U15, pinned VERBATIM from the probe seed)\<close>

theorem u_truncation_recovery_dilemma:
  "\<exists>W1 W2 f.
     dwu_reachable_w W1 \<and> dwu_reachable_w W2
   \<and> u_retained_view W1 = u_retained_view W2
   \<and> dwu_journal W1 \<noteq> dwu_journal W2
   \<and> u_lost_journal f W1 \<and> \<not> u_lost_journal f W2
   \<and> (\<forall>P. u_retained_measured P \<longrightarrow>
        (\<exists>t1' t2'.
           u_policy_redrive P W1 f t1'
         \<and> u_policy_redrive P W2 f t2'
         \<and> (u_effect_unsafe t2' \<or> u_lost_journal f t1')))"
proof -
  have body:
    "dwu_reachable_w tt_W1 \<and> dwu_reachable_w tt_W2
   \<and> u_retained_view tt_W1 = u_retained_view tt_W2
   \<and> dwu_journal tt_W1 \<noteq> dwu_journal tt_W2
   \<and> u_lost_journal ec2 tt_W1 \<and> \<not> u_lost_journal ec2 tt_W2
   \<and> (\<forall>P. u_retained_measured P \<longrightarrow>
        (\<exists>t1' t2'.
           u_policy_redrive P tt_W1 ec2 t1'
         \<and> u_policy_redrive P tt_W2 ec2 t2'
         \<and> (u_effect_unsafe t2' \<or> u_lost_journal ec2 t1')))"
  proof (intro conjI)
  show "dwu_reachable_w tt_W1" by (rule tt_reach_W1)
next
  show "dwu_reachable_w tt_W2" by (rule tt_reach_W2)
next
  show "u_retained_view tt_W1 = u_retained_view tt_W2" by (rule tt_views_eq)
next
  show "dwu_journal tt_W1 \<noteq> dwu_journal tt_W2" by (rule tt_journal_neq)
next
  show "u_lost_journal ec2 tt_W1" by (rule tt_lost_W1)
next
  show "\<not> u_lost_journal ec2 tt_W2" by (rule tt_notlost_W2)
next
  show "\<forall>P. u_retained_measured P \<longrightarrow>
          (\<exists>t1' t2'.
             u_policy_redrive P tt_W1 ec2 t1'
           \<and> u_policy_redrive P tt_W2 ec2 t2'
           \<and> (u_effect_unsafe t2' \<or> u_lost_journal ec2 t1'))"
  proof (intro allI impI)
    fix P :: "(nat, nat) dwu_state \<Rightarrow> (src_coord \<times> (nat, nat) source_event) list"
    assume "u_retained_measured P"
    then obtain g where g: "\<forall>t. P t = g (u_retained_view t)"
      unfolding u_retained_measured_def by blast
    have PB: "P tt_W2 = P tt_W1" using g tt_views_eq by metis
    \<comment> \<open>the two functional redrive post-states; both stamp the SAME batch @{term "P tt_W1"}\<close>
    let ?t1' = "tt_redrive tt_W1 ec2 (P tt_W1)"
    let ?t2' = "tt_redrive tt_W2 ec2 (P tt_W2)"
    have red1: "u_policy_redrive P tt_W1 ec2 ?t1'"
      by (rule tt_redrive_enabled[OF tt_W1_crashed tt_W1_finish])
    have red2: "u_policy_redrive P tt_W2 ec2 ?t2'"
      by (rule tt_redrive_enabled[OF tt_W2_crashed tt_W2_finish])
    have acc1: "dwu_accepted ?t1' = stamped_at 1 0 (P tt_W1)"
      by (simp add: tt_redrive_accepted)
    have acc2: "dwu_accepted ?t2' = stamped_at 1 0 (P tt_W1)"
      by (simp add: tt_redrive_accepted PB)
    have jour2: "dwu_journal ?t2' = [(ec1, tt_e2)]" by simp
    have disj: "u_effect_unsafe ?t2' \<or> u_lost_journal ec2 ?t1'"
    proof (cases "(ec1, tt_e) \<in> set (P tt_W1)")
      case True
      \<comment> \<open>FABRICATE: @{const tt_x} is accepted in @{term ?t2'} but its journal
          @{term "[(ec1, tt_e2)]"} cannot justify it (content @{term tt_e} was destroyed)\<close>
      have "tt_x \<in> set (dwu_accepted ?t2')"
        using True by (simp add: acc2 stamped_at_def tt_x_def)
      moreover have "\<not> u_justified ?t2' tt_x"
        by (simp add: u_justified_def tt_x_def jour2 tt_e_neq_e2)
      ultimately have "u_premature ?t2'" unfolding u_premature_def by blast
      thus ?thesis by (simp add: u_effect_unsafe_def)
    next
      case False
      \<comment> \<open>ABANDON: @{term "(ec1, tt_e)"} is owed by @{term ?t1'}'s journal but the
          policy batch @{term "P tt_W1"} does not carry it, so it is lost\<close>
      have "(ec1, tt_e)
              \<in> set (replay_down_hist (dwu_journal ?t1')
                       (exec_scope (dwu_store ?t1')) ec2)"
        by (simp add: replay_down_hist_def tt_e_def ec_defs)
      moreover have "(ec1, tt_e) \<notin> set (log_payloads (dwu_accepted ?t1'))"
        using False by (simp add: acc1)
      ultimately show ?thesis unfolding u_lost_journal_def by blast
    qed
    show "\<exists>t1' t2'.
            u_policy_redrive P tt_W1 ec2 t1'
          \<and> u_policy_redrive P tt_W2 ec2 t2'
          \<and> (u_effect_unsafe t2' \<or> u_lost_journal ec2 t1')"
      using red1 red2 disj by blast
  qed
  qed
  show ?thesis
    by (rule exI[of _ tt_W1], rule exI[of _ tt_W2], rule exI[of _ ec2]) (rule body)
qed

subsection \<open>3.5 The two-horn export (FABRICATE-or-ABANDON at statement grade)\<close>

text \<open>@{thm [source] u_truncation_recovery_dilemma} with the defeat conjunct
  sharpened to @{const u_premature}-or-@{const u_lost_journal}: the FABRICATE
  branch's proved @{const u_premature} fact is exported as-is (no weakening
  into @{const u_effect_unsafe}), and the ABANDON branch is unchanged.  A fact
  of the designed witness pair; the pinned U15 statement of record above is
  unchanged.\<close>

theorem u_truncation_fabricate_or_abandon:
  "\<exists>W1 W2 f.
     dwu_reachable_w W1 \<and> dwu_reachable_w W2
   \<and> u_retained_view W1 = u_retained_view W2
   \<and> dwu_journal W1 \<noteq> dwu_journal W2
   \<and> u_lost_journal f W1 \<and> \<not> u_lost_journal f W2
   \<and> (\<forall>P. u_retained_measured P \<longrightarrow>
        (\<exists>t1' t2'.
           u_policy_redrive P W1 f t1'
         \<and> u_policy_redrive P W2 f t2'
         \<and> (u_premature t2' \<or> u_lost_journal f t1')))"
proof -
  have body:
    "dwu_reachable_w tt_W1 \<and> dwu_reachable_w tt_W2
   \<and> u_retained_view tt_W1 = u_retained_view tt_W2
   \<and> dwu_journal tt_W1 \<noteq> dwu_journal tt_W2
   \<and> u_lost_journal ec2 tt_W1 \<and> \<not> u_lost_journal ec2 tt_W2
   \<and> (\<forall>P. u_retained_measured P \<longrightarrow>
        (\<exists>t1' t2'.
           u_policy_redrive P tt_W1 ec2 t1'
         \<and> u_policy_redrive P tt_W2 ec2 t2'
         \<and> (u_premature t2' \<or> u_lost_journal ec2 t1')))"
  proof (intro conjI)
  show "dwu_reachable_w tt_W1" by (rule tt_reach_W1)
next
  show "dwu_reachable_w tt_W2" by (rule tt_reach_W2)
next
  show "u_retained_view tt_W1 = u_retained_view tt_W2" by (rule tt_views_eq)
next
  show "dwu_journal tt_W1 \<noteq> dwu_journal tt_W2" by (rule tt_journal_neq)
next
  show "u_lost_journal ec2 tt_W1" by (rule tt_lost_W1)
next
  show "\<not> u_lost_journal ec2 tt_W2" by (rule tt_notlost_W2)
next
  show "\<forall>P. u_retained_measured P \<longrightarrow>
          (\<exists>t1' t2'.
             u_policy_redrive P tt_W1 ec2 t1'
           \<and> u_policy_redrive P tt_W2 ec2 t2'
           \<and> (u_premature t2' \<or> u_lost_journal ec2 t1'))"
  proof (intro allI impI)
    fix P :: "(nat, nat) dwu_state \<Rightarrow> (src_coord \<times> (nat, nat) source_event) list"
    assume "u_retained_measured P"
    then obtain g where g: "\<forall>t. P t = g (u_retained_view t)"
      unfolding u_retained_measured_def by blast
    have PB: "P tt_W2 = P tt_W1" using g tt_views_eq by metis
    \<comment> \<open>the two functional redrive post-states; both stamp the SAME batch @{term "P tt_W1"}\<close>
    let ?t1' = "tt_redrive tt_W1 ec2 (P tt_W1)"
    let ?t2' = "tt_redrive tt_W2 ec2 (P tt_W2)"
    have red1: "u_policy_redrive P tt_W1 ec2 ?t1'"
      by (rule tt_redrive_enabled[OF tt_W1_crashed tt_W1_finish])
    have red2: "u_policy_redrive P tt_W2 ec2 ?t2'"
      by (rule tt_redrive_enabled[OF tt_W2_crashed tt_W2_finish])
    have acc1: "dwu_accepted ?t1' = stamped_at 1 0 (P tt_W1)"
      by (simp add: tt_redrive_accepted)
    have acc2: "dwu_accepted ?t2' = stamped_at 1 0 (P tt_W1)"
      by (simp add: tt_redrive_accepted PB)
    have jour2: "dwu_journal ?t2' = [(ec1, tt_e2)]" by simp
    have disj: "u_premature ?t2' \<or> u_lost_journal ec2 ?t1'"
    proof (cases "(ec1, tt_e) \<in> set (P tt_W1)")
      case True
      \<comment> \<open>FABRICATE: @{const tt_x} is accepted in @{term ?t2'} but its journal
          @{term "[(ec1, tt_e2)]"} cannot justify it (content @{term tt_e} was
          destroyed); the proved @{const u_premature} is the exported horn\<close>
      have "tt_x \<in> set (dwu_accepted ?t2')"
        using True by (simp add: acc2 stamped_at_def tt_x_def)
      moreover have "\<not> u_justified ?t2' tt_x"
        by (simp add: u_justified_def tt_x_def jour2 tt_e_neq_e2)
      ultimately have "u_premature ?t2'" unfolding u_premature_def by blast
      thus ?thesis by blast
    next
      case False
      \<comment> \<open>ABANDON: @{term "(ec1, tt_e)"} is owed by @{term ?t1'}'s journal but the
          policy batch @{term "P tt_W1"} does not carry it, so it is lost\<close>
      have "(ec1, tt_e)
              \<in> set (replay_down_hist (dwu_journal ?t1')
                       (exec_scope (dwu_store ?t1')) ec2)"
        by (simp add: replay_down_hist_def tt_e_def ec_defs)
      moreover have "(ec1, tt_e) \<notin> set (log_payloads (dwu_accepted ?t1'))"
        using False by (simp add: acc1)
      ultimately show ?thesis unfolding u_lost_journal_def by blast
    qed
    show "\<exists>t1' t2'.
            u_policy_redrive P tt_W1 ec2 t1'
          \<and> u_policy_redrive P tt_W2 ec2 t2'
          \<and> (u_premature t2' \<or> u_lost_journal ec2 t1')"
      using red1 red2 disj by blast
  qed
  qed
  show ?thesis
    by (rule exI[of _ tt_W1], rule exI[of _ tt_W2], rule exI[of _ ec2]) (rule body)
qed


section \<open>4. The phantom witness W (U14a / U14c / U14d share it)\<close>

text \<open>Commit + enqueue + downstream @{term "(ec1, tt_e)"} (so @{const tt_x} lands
  in accepted), then truncate at @{const c0}: the live source is erased to [] but
  the journal @{term "[(ec1, tt_e)]"} and the accepted @{term "[tt_x]"} survive.\<close>

definition tt_P2 :: "(nat, nat) dwu_state" where
  "tt_P2 = mkU (mkC [(ec1, tt_e)] [] [(ec1, tt_e)] {(ec1, tt_e)} Running)
               [(ec1, tt_e)] [] [] [0 \<mapsto> UProd] 0"

definition tt_P3 :: "(nat, nat) dwu_state" where
  "tt_P3 = mkU (mkC [(ec1, tt_e)] [(ec1, tt_e)] [(ec1, tt_e)] {} Running)
               [(ec1, tt_e)] [tt_x] [tt_x] [0 \<mapsto> UProd] 0"

definition tt_W :: "(nat, nat) dwu_state" where
  "tt_W = mkU (mkC [] [] [] {} (Crashed ec2)) [(ec1, tt_e)] [tt_x] [tt_x] [0 \<mapsto> UProd] 0"

lemma tt_wf_P2: "wellformed_exec_state (dwu_store tt_P2)"
  by (simp add: tt_P2_def mkU_def mkC_def ws_defs wf_hist_Nil wfh_ec1)

lemma tt_g_A1_enq: "exec_label_preserves_history_wf (dwu_store tt_A1) (EnqueueDownstream ec1 tt_e)"
  by (simp add: tt_A1_def mkU_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma tt_g_P2_down: "exec_label_preserves_history_wf (dwu_store tt_P2) (DoDownstream ec1 tt_e)"
  by (simp add: tt_P2_def mkU_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma tt_step_enq: "dwu_step tt_A1 (ULift 0 (EnqueueDownstream ec1 tt_e)) tt_P2"
proof -
  have c: "dw_exec_step (dwu_store tt_A1) (EnqueueDownstream ec1 tt_e)
             (mkC [(ec1, tt_e)] [] [(ec1, tt_e)] {(ec1, tt_e)} Running)"
    by (rule enqueue_downstreamI) (simp_all add: tt_A1_def mkU_def mkC_def)
  have "dwu_step tt_A1 (ULift 0 (EnqueueDownstream ec1 tt_e))
          (tt_A1\<lparr>dwu_store := mkC [(ec1, tt_e)] [] [(ec1, tt_e)] {(ec1, tt_e)} Running\<rparr>)"
    by (rule dwu_step.ulift_enqueue[OF _ _ c]) (simp_all add: tt_A1_def mkU_def)
  also have "\<dots> = tt_P2" by (simp add: tt_A1_def tt_P2_def mkU_def)
  finally show ?thesis .
qed

lemma tt_step_down: "dwu_step tt_P2 (ULift 0 (DoDownstream ec1 tt_e)) tt_P3"
proof -
  have c: "dw_exec_step (dwu_store tt_P2) (DoDownstream ec1 tt_e)
             (mkC [(ec1, tt_e)] [(ec1, tt_e)] [(ec1, tt_e)] {} Running)"
    by (rule do_downstreamI) (simp_all add: tt_P2_def mkU_def mkC_def)
  have "dwu_step tt_P2 (ULift 0 (DoDownstream ec1 tt_e))
          (tt_P2\<lparr>dwu_store := mkC [(ec1, tt_e)] [(ec1, tt_e)] [(ec1, tt_e)] {} Running,
                 dwu_sent := dwu_sent tt_P2 @ [tt_x],
                 dwu_accepted := dwu_accepted tt_P2
                   @ (if dwu_fence tt_P2 \<le> ue_gen tt_x then [tt_x] else [])\<rparr>)"
    by (rule dwu_step.ulift_publish[OF _ _ c])
       (simp_all add: tt_P2_def mkU_def mkC_def tt_x_def)
  also have "\<dots> = tt_P3" by (simp add: tt_P2_def tt_P3_def mkU_def tt_x_def)
  finally show ?thesis .
qed

lemma tt_step_trunc_ph: "dwu_step tt_P3 (UTruncCrash c0 ec2) tt_W"
proof -
  have wf: "wellformed_exec_state (dwu_store tt_P3)"
    by (simp add: tt_P3_def mkU_def mkC_def ws_defs wf_hist_Nil wfh_ec1)
  have "dwu_step tt_P3 (UTruncCrash c0 ec2)
          (tt_P3\<lparr>dwu_store := truncating_crash_state (dwu_store tt_P3) c0 ec2,
                 dwu_floor := min (dwu_floor tt_P3)
                   (length (exec_src_hist
                      (truncating_crash_state (dwu_store tt_P3) c0 ec2)))\<rparr>)"
    by (rule dwu_step.utrunccrash[OF wf])
       (simp_all add: tt_P3_def mkU_def mkC_def less_eq_src_coord_def c0_least)
  also have "\<dots> = tt_W"
    by (simp add: tt_P3_def tt_W_def mkU_def mkC_def truncating_crash_state_def
                  truncating_crash_state_at_boundary_def durable_exec_state_at_boundary_def
                  durable_history_prefix_at_def single_durable_boundary_def
                  durable_pending_at_boundary_def durable_ack_frontier_def
                  ec_defs c0_eq_coord_of_nat_0)
  finally show ?thesis .
qed

lemma tt_reach_W: "dwu_reachable_w tt_W"
proof -
  have rP2: "dwu_reachable_w tt_P2"
    by (rule dwu_reach_lift[OF tt_reach_A1 tt_wf_A1 tt_g_A1_enq tt_step_enq])
  have rP3: "dwu_reachable_w tt_P3"
    by (rule dwu_reach_lift[OF rP2 tt_wf_P2 tt_g_P2_down tt_step_down])
  show ?thesis by (rule dwu_reach_other[OF rP3 _ _ tt_step_trunc_ph]) simp_all
qed

text \<open>The phantom verdicts: @{const tt_x} is journal-justified but NOT
  live-justified (the live source has been erased).\<close>

lemma tt_W_accepted [simp]: "dwu_accepted tt_W = [tt_x]"
  by (simp add: tt_W_def mkU_def)

lemma tt_W_justified: "u_justified tt_W tt_x"
  by (simp add: u_justified_def tt_W_def mkU_def tt_x_def)

lemma tt_W_not_premature: "\<not> u_premature tt_W"
  by (simp add: u_premature_def tt_W_justified)

lemma tt_W_premature_live: "u_premature_live tt_W"
proof -
  have "\<not> u_justified_live tt_W tt_x"
    by (simp add: u_justified_live_def tt_W_def mkU_def mkC_def tt_x_def)
  thus ?thesis unfolding u_premature_live_def by auto
qed


section \<open>5. U14a --- the phantom exists ("the store forgets; the effect stands")\<close>

theorem u_phantom_exists:
  "\<exists>W x. dwu_reachable_w W
   \<and> x \<in> set (dwu_accepted W)
   \<and> u_justified W x
   \<and> is_ulog x
   \<and> (\<forall>f. ulog_of x
        \<notin> set (replay_down_hist (retained_hist W) (exec_scope (dwu_store W)) f))"
proof (intro exI[of _ tt_W] exI[of _ tt_x] conjI)
  show "dwu_reachable_w tt_W" by (rule tt_reach_W)
next
  show "tt_x \<in> set (dwu_accepted tt_W)" by simp
next
  show "u_justified tt_W tt_x" by (rule tt_W_justified)
next
  show "is_ulog tt_x" by (simp add: is_ulog_def tt_x_def)
next
  show "\<forall>f. ulog_of tt_x
          \<notin> set (replay_down_hist (retained_hist tt_W) (exec_scope (dwu_store tt_W)) f)"
    by (simp add: retained_hist_def tt_W_def mkU_def mkC_def replay_down_hist_def)
qed


section \<open>6. U14c --- live reading is retroactively premature\<close>

theorem u_live_reading_retroactively_premature:
  "\<exists>W. dwu_reachable_w W \<and> u_premature_live W \<and> \<not> u_premature W"
  by (intro exI[of _ tt_W] conjI tt_reach_W tt_W_premature_live tt_W_not_premature)


section \<open>7. U14d --- resurrection: truncate-then-regrow re-justifies live\<close>

text \<open>From the phantom @{const tt_W}, the regrow path
  @{term "[ULift 0 Recover, URelease 0, ULift 0 (DoSource ec1 tt_e)]"} re-appends
  @{term "(ec1, tt_e)"}: the LIVE prematurity verdict resurrects (TRUE at
  @{const tt_W}, FALSE at @{text tt_Wp}), while the JOURNAL verdict stays FALSE.\<close>

definition tt_R1 :: "(nat, nat) dwu_state" where
  "tt_R1 = mkU (mkC [] [] [] {} Recovered) [(ec1, tt_e)] [tt_x] [tt_x] [0 \<mapsto> UProd] 0"

definition tt_R2 :: "(nat, nat) dwu_state" where
  "tt_R2 = mkU (mkC [] [] [] {} Running) [(ec1, tt_e)] [tt_x] [tt_x] [0 \<mapsto> UProd] 0"

definition tt_Wp :: "(nat, nat) dwu_state" where
  "tt_Wp = mkU (mkC [(ec1, tt_e)] [] [] {} Running)
               [(ec1, tt_e), (ec1, tt_e)] [tt_x] [tt_x] [0 \<mapsto> UProd] 0"

lemma tt_step_recover: "dwu_step tt_W (ULift 0 Recover) tt_R1"
proof -
  have st: "exec_status (dwu_store tt_W) = Crashed ec2"
    by (simp add: tt_W_def mkU_def mkC_def)
  have c: "dw_exec_step (dwu_store tt_W) Recover
             ((dwu_store tt_W)\<lparr>exec_status := Recovered\<rparr>)"
    by (rule dw_exec_step.recover[OF st])
  have "dwu_step tt_W (ULift 0 Recover)
          (tt_W\<lparr>dwu_store := (dwu_store tt_W)\<lparr>exec_status := Recovered\<rparr>\<rparr>)"
    by (rule dwu_step.ulift_nonprod[OF _ _ c]) (simp_all add: tt_W_def mkU_def)
  also have "\<dots> = tt_R1" by (simp add: tt_W_def tt_R1_def mkU_def mkC_def)
  finally show ?thesis .
qed

lemma tt_step_release: "dwu_step tt_R1 (URelease 0) tt_R2"
proof -
  have "dwu_step tt_R1 (URelease 0) (tt_R1\<lparr>dwu_store := (dwu_store tt_R1)\<lparr>exec_status := Running\<rparr>\<rparr>)"
    by (rule dwu_step.urelease) (simp add: tt_R1_def mkU_def mkC_def)
  also have "\<dots> = tt_R2" by (simp add: tt_R1_def tt_R2_def mkU_def mkC_def)
  finally show ?thesis .
qed

lemma tt_step_regrow: "dwu_step tt_R2 (ULift 0 (DoSource ec1 tt_e)) tt_Wp"
proof -
  have c: "dw_exec_step (dwu_store tt_R2) (DoSource ec1 tt_e)
             (mkC [(ec1, tt_e)] [] [] {} Running)"
    by (rule do_sourceI) (simp_all add: tt_R2_def mkU_def mkC_def)
  have "dwu_step tt_R2 (ULift 0 (DoSource ec1 tt_e))
          (tt_R2\<lparr>dwu_store := mkC [(ec1, tt_e)] [] [] {} Running,
                 dwu_journal := dwu_journal tt_R2 @ [(ec1, tt_e)]\<rparr>)"
    by (rule dwu_step.ulift_source[OF _ _ c]) (simp_all add: tt_R2_def mkU_def)
  also have "\<dots> = tt_Wp" by (simp add: tt_R2_def tt_Wp_def mkU_def)
  finally show ?thesis .
qed

lemma tt_g_W_recover: "exec_label_preserves_history_wf (dwu_store tt_W) Recover"
  by (simp add: exec_label_preserves_history_wf_def)

lemma tt_g_R2_src: "exec_label_preserves_history_wf (dwu_store tt_R2) (DoSource ec1 tt_e)"
  by (simp add: tt_R2_def mkU_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma tt_wf_W: "wellformed_exec_state (dwu_store tt_W)"
  by (simp add: tt_W_def mkU_def mkC_def ws_defs wf_hist_Nil)

lemma tt_wf_R2: "wellformed_exec_state (dwu_store tt_R2)"
  by (simp add: tt_R2_def mkU_def mkC_def ws_defs wf_hist_Nil)

lemma tt_regrow_trace:
  "dwu_temporal_trace tt_W
     [ULift 0 Recover, URelease 0, ULift 0 (DoSource ec1 tt_e)] tt_Wp"
proof -
  have t3: "dwu_temporal_trace tt_R2 [ULift 0 (DoSource ec1 tt_e)] tt_Wp"
    by (rule dwu_temporal_trace.dwu_lift_step
              [OF tt_wf_R2 tt_g_R2_src tt_step_regrow dwu_temporal_trace.dwu_refl])
  have t2: "dwu_temporal_trace tt_R1 [URelease 0, ULift 0 (DoSource ec1 tt_e)] tt_Wp"
    by (rule dwu_temporal_trace.dwu_other_step[OF _ _ tt_step_release t3]) simp_all
  show ?thesis
    by (rule dwu_temporal_trace.dwu_lift_step[OF tt_wf_W tt_g_W_recover tt_step_recover t2])
qed

lemma tt_Wp_not_premature_live: "\<not> u_premature_live tt_Wp"
  by (simp add: u_premature_live_def u_justified_live_def tt_Wp_def mkU_def mkC_def tt_x_def)

lemma tt_Wp_not_premature: "\<not> u_premature tt_Wp"
  by (simp add: u_premature_def u_justified_def tt_Wp_def mkU_def tt_x_def)

theorem u_resurrection_live_rejustifies:
  "\<exists>W W' e.
     dwu_reachable_w W
   \<and> u_premature_live W \<and> \<not> u_premature W
   \<and> dwu_temporal_trace W
       [ULift 0 Recover, URelease 0, ULift 0 (DoSource ec1 e)] W'
   \<and> \<not> u_premature_live W' \<and> \<not> u_premature W'"
  by (intro exI[of _ tt_W] exI[of _ tt_Wp] exI[of _ tt_e] conjI
            tt_reach_W tt_W_premature_live tt_W_not_premature tt_regrow_trace
            tt_Wp_not_premature_live tt_Wp_not_premature)


section \<open>8. U14b --- the safety verdict is not retained-computable\<close>

text \<open>V1 is the honest phantom @{const tt_W} (@{const tt_x} journal-justified).  V2
  sources the DIFFERENT in-scope event @{term "(ec1, tt_ep)"} but enqueues /
  downstreams @{term "(ec1, tt_e)"} (a dishonest enqueue --- legal, no
  src-membership guard), so its accepted @{const tt_x} is journal-UNJUSTIFIED.
  Both truncate to the SAME empty crashed store with the SAME retained view;
  only the destroyed journal content differs.\<close>

definition tt_V2P1 :: "(nat, nat) dwu_state" where
  "tt_V2P1 = mkU (mkC [(ec1, tt_ep)] [] [] {} Running) [(ec1, tt_ep)] [] [] [0 \<mapsto> UProd] 0"

definition tt_V2P2 :: "(nat, nat) dwu_state" where
  "tt_V2P2 = mkU (mkC [(ec1, tt_ep)] [] [(ec1, tt_e)] {(ec1, tt_e)} Running)
                 [(ec1, tt_ep)] [] [] [0 \<mapsto> UProd] 0"

definition tt_V2P3 :: "(nat, nat) dwu_state" where
  "tt_V2P3 = mkU (mkC [(ec1, tt_ep)] [(ec1, tt_e)] [(ec1, tt_e)] {} Running)
                 [(ec1, tt_ep)] [tt_x] [tt_x] [0 \<mapsto> UProd] 0"

definition tt_V2 :: "(nat, nat) dwu_state" where
  "tt_V2 = mkU (mkC [] [] [] {} (Crashed ec2)) [(ec1, tt_ep)] [tt_x] [tt_x] [0 \<mapsto> UProd] 0"

lemma tt_wf_V2P1: "wellformed_exec_state (dwu_store tt_V2P1)"
  by (simp add: tt_V2P1_def mkU_def mkC_def ws_defs wf_hist_Nil wfh_ec1)

lemma tt_wf_V2P2: "wellformed_exec_state (dwu_store tt_V2P2)"
  by (simp add: tt_V2P2_def mkU_def mkC_def ws_defs wf_hist_Nil wfh_ec1)

lemma tt_g_V2P1_src: "exec_label_preserves_history_wf (dwu_store uW0) (DoSource ec1 tt_ep)"
  by (simp add: uW0_def mkU_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma tt_g_V2P1_enq: "exec_label_preserves_history_wf (dwu_store tt_V2P1) (EnqueueDownstream ec1 tt_e)"
  by (simp add: tt_V2P1_def mkU_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma tt_g_V2P2_down: "exec_label_preserves_history_wf (dwu_store tt_V2P2) (DoDownstream ec1 tt_e)"
  by (simp add: tt_V2P2_def mkU_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma tt_step_V2_src: "dwu_step uW0 (ULift 0 (DoSource ec1 tt_ep)) tt_V2P1"
proof -
  have c: "dw_exec_step (dwu_store uW0) (DoSource ec1 tt_ep)
             (mkC [(ec1, tt_ep)] [] [] {} Running)"
    by (rule do_sourceI) (simp_all add: uW0_def mkU_def mkC_def)
  have "dwu_step uW0 (ULift 0 (DoSource ec1 tt_ep))
          (uW0\<lparr>dwu_store := mkC [(ec1, tt_ep)] [] [] {} Running,
               dwu_journal := dwu_journal uW0 @ [(ec1, tt_ep)]\<rparr>)"
    by (rule dwu_step.ulift_source[OF _ _ c]) (simp_all add: uW0_def mkU_def)
  also have "\<dots> = tt_V2P1" by (simp add: uW0_def tt_V2P1_def mkU_def)
  finally show ?thesis .
qed

lemma tt_step_V2_enq: "dwu_step tt_V2P1 (ULift 0 (EnqueueDownstream ec1 tt_e)) tt_V2P2"
proof -
  have c: "dw_exec_step (dwu_store tt_V2P1) (EnqueueDownstream ec1 tt_e)
             (mkC [(ec1, tt_ep)] [] [(ec1, tt_e)] {(ec1, tt_e)} Running)"
    by (rule enqueue_downstreamI) (simp_all add: tt_V2P1_def mkU_def mkC_def)
  have "dwu_step tt_V2P1 (ULift 0 (EnqueueDownstream ec1 tt_e))
          (tt_V2P1\<lparr>dwu_store := mkC [(ec1, tt_ep)] [] [(ec1, tt_e)] {(ec1, tt_e)} Running\<rparr>)"
    by (rule dwu_step.ulift_enqueue[OF _ _ c]) (simp_all add: tt_V2P1_def mkU_def)
  also have "\<dots> = tt_V2P2" by (simp add: tt_V2P1_def tt_V2P2_def mkU_def)
  finally show ?thesis .
qed

lemma tt_step_V2_down: "dwu_step tt_V2P2 (ULift 0 (DoDownstream ec1 tt_e)) tt_V2P3"
proof -
  have c: "dw_exec_step (dwu_store tt_V2P2) (DoDownstream ec1 tt_e)
             (mkC [(ec1, tt_ep)] [(ec1, tt_e)] [(ec1, tt_e)] {} Running)"
    by (rule do_downstreamI) (simp_all add: tt_V2P2_def mkU_def mkC_def)
  have "dwu_step tt_V2P2 (ULift 0 (DoDownstream ec1 tt_e))
          (tt_V2P2\<lparr>dwu_store := mkC [(ec1, tt_ep)] [(ec1, tt_e)] [(ec1, tt_e)] {} Running,
                   dwu_sent := dwu_sent tt_V2P2 @ [tt_x],
                   dwu_accepted := dwu_accepted tt_V2P2
                     @ (if dwu_fence tt_V2P2 \<le> ue_gen tt_x then [tt_x] else [])\<rparr>)"
    by (rule dwu_step.ulift_publish[OF _ _ c])
       (simp_all add: tt_V2P2_def mkU_def mkC_def tt_x_def)
  also have "\<dots> = tt_V2P3" by (simp add: tt_V2P2_def tt_V2P3_def mkU_def tt_x_def)
  finally show ?thesis .
qed

lemma tt_step_V2_trunc: "dwu_step tt_V2P3 (UTruncCrash c0 ec2) tt_V2"
proof -
  have wf: "wellformed_exec_state (dwu_store tt_V2P3)"
    by (simp add: tt_V2P3_def mkU_def mkC_def ws_defs wf_hist_Nil wfh_ec1)
  have "dwu_step tt_V2P3 (UTruncCrash c0 ec2)
          (tt_V2P3\<lparr>dwu_store := truncating_crash_state (dwu_store tt_V2P3) c0 ec2,
                   dwu_floor := min (dwu_floor tt_V2P3)
                     (length (exec_src_hist
                        (truncating_crash_state (dwu_store tt_V2P3) c0 ec2)))\<rparr>)"
    by (rule dwu_step.utrunccrash[OF wf])
       (simp_all add: tt_V2P3_def mkU_def mkC_def less_eq_src_coord_def c0_least)
  also have "\<dots> = tt_V2"
    by (simp add: tt_V2P3_def tt_V2_def mkU_def mkC_def truncating_crash_state_def
                  truncating_crash_state_at_boundary_def durable_exec_state_at_boundary_def
                  durable_history_prefix_at_def single_durable_boundary_def
                  durable_pending_at_boundary_def durable_ack_frontier_def
                  ec_defs c0_eq_coord_of_nat_0)
  finally show ?thesis .
qed

lemma tt_reach_V2: "dwu_reachable_w tt_V2"
proof -
  have r0: "dwu_reachable Map.empty {0, 1} ec2 uW0"
    unfolding rf_uW0_init by (rule dwu_reachable_init)
  have r1: "dwu_reachable_w tt_V2P1"
    by (rule dwu_reach_lift[OF r0 rf_wf0 tt_g_V2P1_src tt_step_V2_src])
  have r2: "dwu_reachable_w tt_V2P2"
    by (rule dwu_reach_lift[OF r1 tt_wf_V2P1 tt_g_V2P1_enq tt_step_V2_enq])
  have r3: "dwu_reachable_w tt_V2P3"
    by (rule dwu_reach_lift[OF r2 tt_wf_V2P2 tt_g_V2P2_down tt_step_V2_down])
  show ?thesis by (rule dwu_reach_other[OF r3 _ _ tt_step_V2_trunc]) simp_all
qed

lemma tt_views_eq_V: "u_retained_view tt_W = u_retained_view tt_V2"
  by (simp add: u_retained_view_def tt_W_def tt_V2_def mkU_def)

lemma tt_V2_premature: "u_premature tt_V2"
proof -
  have "tt_x \<in> set (dwu_accepted tt_V2)" by (simp add: tt_V2_def mkU_def)
  moreover have "\<not> u_justified tt_V2 tt_x"
    by (simp add: u_justified_def tt_V2_def mkU_def tt_x_def tt_e_neq_ep)
  ultimately show ?thesis unfolding u_premature_def by blast
qed

theorem u_verdict_not_retained_computable:
  "\<exists>V1 V2.
     dwu_reachable_w V1 \<and> dwu_reachable_w V2
   \<and> u_retained_view V1 = u_retained_view V2
   \<and> u_premature V2 \<and> \<not> u_premature V1"
  by (intro exI[of _ tt_W] exI[of _ tt_V2] conjI
            tt_reach_W tt_reach_V2 tt_views_eq_V tt_V2_premature tt_W_not_premature)

corollary u_premature_not_retained_measured:
  "\<not> (\<exists>g. \<forall>t :: (nat, nat) dwu_state.
        dwu_reachable_w t \<longrightarrow> (u_premature t \<longleftrightarrow> g (u_retained_view t)))"
proof
  assume "\<exists>g. \<forall>t :: (nat, nat) dwu_state.
            dwu_reachable_w t \<longrightarrow> (u_premature t \<longleftrightarrow> g (u_retained_view t))"
  then obtain g where g: "\<And>t :: (nat, nat) dwu_state.
            dwu_reachable_w t \<Longrightarrow> (u_premature t \<longleftrightarrow> g (u_retained_view t))" by blast
  have "u_premature tt_W \<longleftrightarrow> g (u_retained_view tt_W)" by (rule g[OF tt_reach_W])
  moreover have "u_premature tt_V2 \<longleftrightarrow> g (u_retained_view tt_V2)" by (rule g[OF tt_reach_V2])
  ultimately have "u_premature tt_W \<longleftrightarrow> u_premature tt_V2" by (simp add: tt_views_eq_V)
  with tt_W_not_premature tt_V2_premature show False by simp
qed

end
