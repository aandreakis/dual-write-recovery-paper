(*  Title:       DWU_Claim_Witness.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Purpose: The non-vacuity control completing the corpus witness pattern
             for the possibility headliner u_exactly_once_at_completed_claim
             (DWU_Fenced_Discipline).  A 4-action disciplined trace from the pinned
             init --- commit (ec1, e1); crash; claim UArmF 0 ec2; fire ---
             carries a NONEMPTY armed batch, discharges every premise of the
             theorem, and instantiates its conclusion.  A direct evaluation of
             the closed end-state cross-checks the theorem-derived verdict,
             and a pre-fire control shows the instance is not trivially true
             mid-window (at-least-once FAILS at the pre-fire state), so the
             completed claim's fire is load-bearing in the conclusion.
*)

theory DWU_Claim_Witness
  imports DWU_Concurrent_Recovery
begin

section \<open>The four states of the claim run\<close>

text \<open>@{const uW0} (= the pinned init) and @{const uW1} (post-commit) are the
  landed floor-chain states; the crash, claim, and fire states are new.\<close>

definition cw2 :: "(nat, nat) dwu_state" where
  "cw2 = mkU (mkC [(ec1, e1)] [] [] {} (Crashed ec2))
             [(ec1, e1)] [] [] [0 \<mapsto> UProd] 0"

definition cw3 :: "(nat, nat) dwu_state" where
  "cw3 = mkU (mkC [(ec1, e1)] [] [] {} (Crashed ec2))
             [(ec1, e1)] [] [] [0 \<mapsto> UArmed [rf_x1]] 0"

definition cw4 :: "(nat, nat) dwu_state" where
  "cw4 = mkU (mkC [(ec1, e1)] [] [] {} (Crashed ec2))
             [(ec1, e1)] [rf_x1] [rf_x1] [0 \<mapsto> UProd] 0"

definition cw_acts :: "(nat, nat) dwu_action list" where
  "cw_acts = [ULift 0 (DoSource ec1 e1), ULift 0 (Crash ec2),
              UArmF 0 ec2, UFire 0]"

section \<open>Machine steps\<close>

lemma cw_wf1: "wellformed_exec_state (dwu_store uW1)"
  by (rule rf_wf1)

lemma cw_g_crash: "exec_label_preserves_history_wf (dwu_store uW1) (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma cw_step_crash: "dwu_step uW1 (ULift 0 (Crash ec2)) cw2"
proof -
  have c: "dw_exec_step (dwu_store uW1) (Crash ec2)
             (mkC [(ec1, e1)] [] [] {} (Crashed ec2))"
    by (rule crashI) (simp_all add: uW1_def mkU_def mkC_def)
  have "dwu_step uW1 (ULift 0 (Crash ec2))
          (uW1\<lparr>dwu_store := mkC [(ec1, e1)] [] [] {} (Crashed ec2)\<rparr>)"
    by (rule dwu_step.ulift_nonprod[OF _ _ c]) (simp_all add: uW1_def mkU_def)
  also have "\<dots> = cw2" by (simp add: uW1_def cw2_def mkU_def)
  finally show ?thesis .
qed

text \<open>The claim's sink delta at the crashed state is exactly the one committed,
  never-accepted payload --- the armed batch is the landed @{const rf_x1}.\<close>

lemma cw2_delta: "u_sink_delta ec2 cw2 = [(ec1, e1)]"
  by (simp add: u_sink_delta_def retained_hist_def replay_down_hist_def
                log_payloads_def map_filter_simps cw2_def mkU_def mkC_def
                e1_def ec_defs)

lemma cw2_journal: "dwu_journal cw2 = [(ec1, e1)]"
  by (simp add: cw2_def mkU_def)

lemma cw2_batch:
  "stamped_at (length (dwu_journal cw2)) 0 (u_sink_delta ec2 cw2) = [rf_x1]"
  by (simp only: cw2_journal cw2_delta) (simp add: stamped_at_def rf_x1_def)

lemma cw_step_claim: "dwu_step cw2 (UArmF 0 ec2) cw3"
proof -
  have dom0: "0 \<in> dom (dwu_gens cw2)" by (simp add: cw2_def mkU_def)
  have crashed: "\<exists>c. exec_status (dwu_store cw2) = Crashed c"
    by (rule exI[of _ ec2]) (simp add: cw2_def mkU_def mkC_def)
  have fin: "ec2 \<le> exec_finish (dwu_store cw2)"
    by (simp add: cw2_def mkU_def mkC_def)
  have fence: "dwu_fence cw2 \<le> 0" by (simp add: cw2_def mkU_def)
  have "dwu_step cw2 (UArmF 0 ec2)
          (cw2\<lparr>dwu_fence := 0,
               dwu_gens := (dwu_gens cw2)
                 (0 \<mapsto> UArmed (stamped_at (length (dwu_journal cw2)) 0
                                 (u_sink_delta ec2 cw2)))\<rparr>)"
    by (rule dwu_step.uarmf[OF dom0 crashed fin fence])
  also have "\<dots> = cw3"
    by (simp only: cw2_batch) (simp add: cw2_def cw3_def mkU_def)
  finally show ?thesis .
qed

lemma cw_step_fire: "dwu_step cw3 (UFire 0) cw4"
proof -
  have g: "dwu_gens cw3 0 = Some (UArmed [rf_x1])"
    by (simp add: cw3_def mkU_def)
  have "dwu_step cw3 (UFire 0)
          (cw3\<lparr>dwu_sent := dwu_sent cw3 @ [rf_x1],
               dwu_accepted := dwu_accepted cw3
                 @ (if dwu_fence cw3 \<le> 0 then [rf_x1] else []),
               dwu_gens := (dwu_gens cw3)(0 \<mapsto> UProd)\<rparr>)"
    by (rule dwu_step.ufire[OF g])
  also have "\<dots> = cw4"
    by (simp add: cw3_def cw4_def mkU_def)
  finally show ?thesis .
qed

section \<open>The disciplined trace and its temporal prefixes\<close>

lemma cw_disciplined: "u_disciplined_trace uW0 cw_acts cw4"
  unfolding cw_acts_def
proof -
  have d4: "u_disciplined_trace cw4 [] cw4"
    by (rule u_disciplined_trace.ud_refl)
  have d3: "u_disciplined_trace cw3 [UFire 0] cw4"
    by (rule u_disciplined_trace.ud_fire[OF cw_step_fire d4])
  have guard: "distinct (log_payloads
                 (stamped_at (length (dwu_journal cw2)) 0 (u_sink_delta ec2 cw2)))"
    by (simp only: cw2_batch) (simp add: rf_x1_def log_payloads_def map_filter_simps)
  have d2: "u_disciplined_trace cw2 [UArmF 0 ec2, UFire 0] cw4"
    by (rule u_disciplined_trace.ud_claim[OF guard cw_step_claim d3])
  have d1: "u_disciplined_trace uW1 [ULift 0 (Crash ec2), UArmF 0 ec2, UFire 0] cw4"
    by (rule u_disciplined_trace.ud_nonpub[OF cw_wf1 cw_g_crash _ cw_step_crash d2])
       simp
  show "u_disciplined_trace uW0
          [ULift 0 (DoSource ec1 e1), ULift 0 (Crash ec2), UArmF 0 ec2, UFire 0] cw4"
    by (rule u_disciplined_trace.ud_nonpub[OF rf_wf0 rf_g0 _ rf_step0 d1]) simp
qed

lemma cw_disciplined_init:
  "u_disciplined_trace (dwu_init Map.empty {0, 1} ec2) cw_acts cw4"
  using cw_disciplined unfolding rf_uW0_init .

lemma cw_temporal_pre: "dwu_temporal_trace uW0 (take 3 cw_acts) cw3"
proof -
  have t3: "dwu_temporal_trace cw3 [] cw3" by (rule dwu_temporal_trace.dwu_refl)
  have t2: "dwu_temporal_trace cw2 [UArmF 0 ec2] cw3"
    by (rule dwu_temporal_trace.dwu_other_step[OF _ _ cw_step_claim t3]) simp_all
  have t1: "dwu_temporal_trace uW1 [ULift 0 (Crash ec2), UArmF 0 ec2] cw3"
    by (rule dwu_temporal_trace.dwu_lift_step[OF cw_wf1 cw_g_crash cw_step_crash t2])
  show ?thesis
    unfolding cw_acts_def
    by simp (rule dwu_temporal_trace.dwu_lift_step[OF rf_wf0 rf_g0 rf_step0 t1])
qed

lemma cw_temporal_post: "dwu_temporal_trace uW0 (take (Suc 3) cw_acts) cw4"
proof -
  have t4: "dwu_temporal_trace cw4 [] cw4" by (rule dwu_temporal_trace.dwu_refl)
  have t3: "dwu_temporal_trace cw3 [UFire 0] cw4"
    by (rule dwu_temporal_trace.dwu_other_step[OF _ _ cw_step_fire t4]) simp_all
  have t2: "dwu_temporal_trace cw2 [UArmF 0 ec2, UFire 0] cw4"
    by (rule dwu_temporal_trace.dwu_other_step[OF _ _ cw_step_claim t3]) simp_all
  have t1: "dwu_temporal_trace uW1
              [ULift 0 (Crash ec2), UArmF 0 ec2, UFire 0] cw4"
    by (rule dwu_temporal_trace.dwu_lift_step[OF cw_wf1 cw_g_crash cw_step_crash t2])
  show ?thesis
    unfolding cw_acts_def
    by simp (rule dwu_temporal_trace.dwu_lift_step[OF rf_wf0 rf_g0 rf_step0 t1])
qed

lemma cw_temporal_pre_init:
  "dwu_temporal_trace (dwu_init Map.empty {0, 1} ec2) (take 3 cw_acts) cw3"
  using cw_temporal_pre unfolding rf_uW0_init .

lemma cw_temporal_post_init:
  "dwu_temporal_trace (dwu_init Map.empty {0, 1} ec2) (take (Suc 3) cw_acts) cw4"
  using cw_temporal_post unfolding rf_uW0_init .

section \<open>The claim window and its freshness\<close>

lemma cw_claim: "u_claim_of cw_acts 2 3 0 ec2"
proof -
  have len: "length cw_acts = 4" by (simp add: cw_acts_def)
  have n2: "cw_acts ! 2 = UArmF 0 ec2" by (simp add: cw_acts_def)
  have n3: "cw_acts ! 3 = UFire 0" by (simp add: cw_acts_def)
  have mid: "\<forall>n. 2 < n \<and> n < 3 \<longrightarrow>
        cw_acts ! n \<noteq> UFire 0 \<and> (\<forall>f'. cw_acts ! n \<noteq> UArmF 0 f')"
    by (intro allI impI) linarith
  show ?thesis using len n2 n3 mid by (simp add: u_claim_of_def)
qed

lemma cw_fresh: "u_window_fresh cw_acts 2 3 ec2"
  unfolding u_window_fresh_def by (intro allI impI) linarith

lemma cw_fence_pre: "dwu_fence cw3 \<le> 0"
  by (simp add: cw3_def mkU_def)

section \<open>The non-vacuity verdicts\<close>

text \<open>1. The headliner's full premise set is satisfiable with a nonempty
  batch: the instantiated conclusion, obtained BY the theorem.\<close>

theorem completed_claim_premises_satisfiable:
  "u_exactly_once_at ec2 cw4"
  by (rule u_exactly_once_at_completed_claim[OF cw_disciplined_init cw_claim
        cw_fresh cw_temporal_pre_init cw_fence_pre cw_temporal_post_init])

text \<open>2. Cross-check by direct evaluation of the closed end-state.\<close>

lemma completed_claim_witness_direct_evaluation: "u_exactly_once_at ec2 cw4"
  by (simp add: u_exactly_once_at_def u_effect_unsafe_def u_premature_def
                u_duplicate_def u_justified_def u_at_least_once_at_def
                retained_hist_def replay_down_hist_def log_payloads_def
                map_filter_simps cw4_def mkU_def mkC_def rf_x1_def e1_def ec_defs)

text \<open>3. Nontriviality control: at the PRE-fire window state the at-least-once
  half FAILS --- the armed payload is owed but nothing is accepted --- so the
  completed claim's fire is load-bearing in the instantiated conclusion.\<close>

lemma completed_claim_witness_prefire_not_at_least_once:
  "\<not> u_at_least_once_at ec2 cw3"
  by (simp add: u_at_least_once_at_def retained_hist_def replay_down_hist_def
                log_payloads_def map_filter_simps cw3_def mkU_def mkC_def
                e1_def ec_defs)

text \<open>4. The fired batch is nonempty and lands exactly once.\<close>

lemma completed_claim_witness_nonempty_accept: "dwu_accepted cw4 = [rf_x1]"
  by (simp add: cw4_def mkU_def)

lemma completed_claim_witness_count_one:
  "count_list (log_payloads (dwu_accepted cw4)) (ec1, e1) = 1"
  by (simp add: cw4_def mkU_def rf_x1_def log_payloads_def map_filter_simps)

end
