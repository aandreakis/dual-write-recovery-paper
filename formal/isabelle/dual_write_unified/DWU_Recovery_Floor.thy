(*  Title:       DWU_Recovery_Floor.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Purpose: Road-2 I0.5 --- U10, THE NEGATIVE FLOOR of the unified build.

    "The sink-reading escape double-fires under concurrent recovery: check-then-
    redrive is not atomic at the sink."  A fully explicit 5-step concurrent-
    recovery witness run over the landed unified machine (DWU_Machine): build the
    reachable crashed 2-generation witness W from the six landed witness labels
    lifted at actor 0 plus one USpawn (f = ec2, owed payload p = (ec2, e2)); both
    generations arm the sink-delta, both fire at fence 0 ==> u_duplicate, not lost.

    The one pinned principal (u_concurrent_recovery_defeats_sink_delta) is copied
    VERBATIM from the Stage-4 probe seed; only the proof is new.

    Honesty regime: quick_and_dirty = false (ROOT-pinned), ZERO sorry, ZERO oops,
    no axiomatization, no consts, no oracles.  Every statement is PROVED.
*)

theory DWU_Recovery_Floor
  imports DWU_Machine
begin

section \<open>0. Shared helper (I0.5 principal candidate): sink-delta is frozen by UArm\<close>

text \<open>@{const UArm} writes only @{term "dwu_gens g"}; store, journal, floor and the
  accepted ledger are all frozen, and those are exactly the carriers
  @{const u_sink_delta} reads.  Shared by U9's clean-member control and U10's
  arm-arm constancy conjunct.\<close>

lemma u_sink_delta_arm_const:
  assumes "dwu_step t (UArm g B f') t'"
  shows "u_sink_delta f t' = u_sink_delta f t"
  using dwu_step_arm_inv[OF assms]
  by (simp add: u_sink_delta_def retained_hist_def)


section \<open>1. Reachability-by-extension helpers (mirror of the landed reach chain)\<close>

lemma dwu_reach_lift:
  assumes "dwu_reachable b K fin t"
      and "wellformed_exec_state (dwu_store t)"
      and "exec_label_preserves_history_wf (dwu_store t) a"
      and "dwu_step t (ULift g a) t'"
  shows "dwu_reachable b K fin t'"
proof -
  from assms(1) obtain xs where xs: "dwu_temporal_trace (dwu_init b K fin) xs t"
    unfolding dwu_reachable_def by blast
  have "dwu_temporal_trace t [ULift g a] t'"
    by (rule dwu_temporal_trace.dwu_lift_step
              [OF assms(2) assms(3) assms(4) dwu_temporal_trace.dwu_refl])
  with xs have "dwu_temporal_trace (dwu_init b K fin) (xs @ [ULift g a]) t'"
    by (rule dwu_temporal_trace_append)
  thus ?thesis unfolding dwu_reachable_def by blast
qed

lemma dwu_reach_other:
  assumes "dwu_reachable b K fin t"
      and "\<forall>g a. \<alpha> \<noteq> ULift g a"
      and "\<forall>g c e. \<alpha> \<noteq> UPubLost g c e"
      and "dwu_step t \<alpha> t'"
  shows "dwu_reachable b K fin t'"
proof -
  from assms(1) obtain xs where xs: "dwu_temporal_trace (dwu_init b K fin) xs t"
    unfolding dwu_reachable_def by blast
  have "dwu_temporal_trace t [\<alpha>] t'"
    by (rule dwu_temporal_trace.dwu_other_step
              [OF assms(2) assms(3) assms(4) dwu_temporal_trace.dwu_refl])
  with xs have "dwu_temporal_trace (dwu_init b K fin) (xs @ [\<alpha>]) t'"
    by (rule dwu_temporal_trace_append)
  thus ?thesis unfolding dwu_reachable_def by blast
qed


section \<open>2. The witness states (unified wrapper; stores reuse the landed mkC)\<close>

definition mkU ::
  "(nat, nat) dw_exec_state \<Rightarrow> (nat, nat) src_history
    \<Rightarrow> (nat, nat) uemission list \<Rightarrow> (nat, nat) uemission list
    \<Rightarrow> (nat \<rightharpoonup> (nat, nat) ustage) \<Rightarrow> nat \<Rightarrow> (nat, nat) dwu_state"
where
  "mkU sto jnl snt acc gns hwm =
     \<lparr> dwu_store = sto, dwu_journal = jnl, dwu_sent = snt,
       dwu_accepted = acc, dwu_fence = 0, dwu_gens = gns,
       dwu_hwm = hwm, dwu_floor = 0 \<rparr>"

text \<open>The single already-published emission (ec1 was downstreamed pre-crash).\<close>

definition rf_x1 :: "(nat, nat) uemission" where
  "rf_x1 = \<lparr> ue_stamp = 1, ue_gen = 0, ue_pay = ULog (ec1, e1) \<rparr>"

text \<open>The two armed recovery emissions --- SAME payload (ec2, e2), different gen.\<close>

definition rf_b1 :: "(nat, nat) uemission" where
  "rf_b1 = \<lparr> ue_stamp = 2, ue_gen = 0, ue_pay = ULog (ec2, e2) \<rparr>"

definition rf_b2 :: "(nat, nat) uemission" where
  "rf_b2 = \<lparr> ue_stamp = 2, ue_gen = 1, ue_pay = ULog (ec2, e2) \<rparr>"

definition rf_B1 :: "(nat, nat) uemission list" where "rf_B1 = [rf_b1]"
definition rf_B2 :: "(nat, nat) uemission list" where "rf_B2 = [rf_b2]"

text \<open>The crashed 2-generation store (= @{term "dwe_core t_mid_w"}) and the heal image
  (= @{term "dwe_core t_fin_w"}).\<close>

definition rf_sto6 :: "(nat, nat) dw_exec_state" where
  "rf_sto6 = mkC [(ec1, e1), (ec2, e2)] [(ec1, e1)]
                 [(ec1, e1), (ec2, e2)] {(ec2, e2)} (Crashed ec2)"

definition rf_stoH :: "(nat, nat) dw_exec_state" where
  "rf_stoH = mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)]
                 [(ec1, e1), (ec2, e2)] {} Recovered"

text \<open>The pre-recovery trace states (stores = the landed dwe_core W0..W5, t_mid_w).\<close>

definition uW0 :: "(nat, nat) dwu_state" where
  "uW0 = mkU (mkC [] [] [] {} Running) [] [] [] [0 \<mapsto> UProd] 0"

definition uW1 :: "(nat, nat) dwu_state" where
  "uW1 = mkU (mkC [(ec1, e1)] [] [] {} Running) [(ec1, e1)] [] [] [0 \<mapsto> UProd] 0"

definition uW2 :: "(nat, nat) dwu_state" where
  "uW2 = mkU (mkC [(ec1, e1)] [] [(ec1, e1)] {(ec1, e1)} Running)
             [(ec1, e1)] [] [] [0 \<mapsto> UProd] 0"

definition uW3 :: "(nat, nat) dwu_state" where
  "uW3 = mkU (mkC [(ec1, e1)] [(ec1, e1)] [(ec1, e1)] {} Running)
             [(ec1, e1)] [rf_x1] [rf_x1] [0 \<mapsto> UProd] 0"

definition uW4 :: "(nat, nat) dwu_state" where
  "uW4 = mkU (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1)] [(ec1, e1)] {} Running)
             [(ec1, e1), (ec2, e2)] [rf_x1] [rf_x1] [0 \<mapsto> UProd] 0"

definition uW5 :: "(nat, nat) dwu_state" where
  "uW5 = mkU (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1)]
                  [(ec1, e1), (ec2, e2)] {(ec2, e2)} Running)
             [(ec1, e1), (ec2, e2)] [rf_x1] [rf_x1] [0 \<mapsto> UProd] 0"

definition uW6 :: "(nat, nat) dwu_state" where
  "uW6 = mkU rf_sto6 [(ec1, e1), (ec2, e2)] [rf_x1] [rf_x1] [0 \<mapsto> UProd] 0"

text \<open>The witness W: after one USpawn --- two live UProd generations, hwm 1.\<close>

definition rf_W :: "(nat, nat) dwu_state" where
  "rf_W = mkU rf_sto6 [(ec1, e1), (ec2, e2)] [rf_x1] [rf_x1]
             [0 \<mapsto> UProd, 1 \<mapsto> UProd] 1"

text \<open>The five concurrent-recovery post-states.\<close>

definition rf_t1 :: "(nat, nat) dwu_state" where
  "rf_t1 = rf_W\<lparr>dwu_gens := (dwu_gens rf_W)(0 \<mapsto> UArmed rf_B1)\<rparr>"

definition rf_t2 :: "(nat, nat) dwu_state" where
  "rf_t2 = rf_t1\<lparr>dwu_gens := (dwu_gens rf_t1)(1 \<mapsto> UArmed rf_B2)\<rparr>"

definition rf_t3 :: "(nat, nat) dwu_state" where
  "rf_t3 = rf_t2\<lparr>dwu_store := rf_stoH\<rparr>"

definition rf_t4 :: "(nat, nat) dwu_state" where
  "rf_t4 = rf_t3\<lparr>dwu_sent := dwu_sent rf_t3 @ rf_B1,
                 dwu_accepted := dwu_accepted rf_t3 @ rf_B1,
                 dwu_gens := (dwu_gens rf_t3)(0 \<mapsto> UProd)\<rparr>"

definition rf_t5 :: "(nat, nat) dwu_state" where
  "rf_t5 = rf_t4\<lparr>dwu_sent := dwu_sent rf_t4 @ rf_B2,
                 dwu_accepted := dwu_accepted rf_t4 @ rf_B2,
                 dwu_gens := (dwu_gens rf_t4)(1 \<mapsto> UProd)\<rparr>"


section \<open>3. Wellformedness and label guards along the pre-recovery chain\<close>

lemma rf_uW0_init: "uW0 = dwu_init Map.empty {0, 1} ec2"
  by (simp add: uW0_def mkU_def mkC_def dwu_init_def initial_exec_state_def)

lemma rf_wf0: "wellformed_exec_state (dwu_store uW0)"
  by (simp add: uW0_def mkU_def mkC_def ws_defs wf_hist_Nil)

lemma rf_wf1: "wellformed_exec_state (dwu_store uW1)"
  by (simp add: uW1_def mkU_def mkC_def ws_defs wf_hist_Nil wfh_e1)

lemma rf_wf2: "wellformed_exec_state (dwu_store uW2)"
  by (simp add: uW2_def mkU_def mkC_def ws_defs wf_hist_Nil wfh_e1)

lemma rf_wf3: "wellformed_exec_state (dwu_store uW3)"
  by (simp add: uW3_def mkU_def mkC_def ws_defs wf_hist_Nil wfh_e1)

lemma rf_wf4: "wellformed_exec_state (dwu_store uW4)"
  by (simp add: uW4_def mkU_def mkC_def ws_defs wf_hist_Nil wfh_e1 wfh_pair)

lemma rf_wf5: "wellformed_exec_state (dwu_store uW5)"
  by (simp add: uW5_def mkU_def mkC_def ws_defs wf_hist_Nil wfh_e1 wfh_pair)

lemma rf_g0: "exec_label_preserves_history_wf (dwu_store uW0) (DoSource ec1 e1)"
  by (simp add: uW0_def mkU_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma rf_g1: "exec_label_preserves_history_wf (dwu_store uW1) (EnqueueDownstream ec1 e1)"
  by (simp add: uW1_def mkU_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma rf_g2: "exec_label_preserves_history_wf (dwu_store uW2) (DoDownstream ec1 e1)"
  by (simp add: uW2_def mkU_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma rf_g3: "exec_label_preserves_history_wf (dwu_store uW3) (DoSource ec2 e2)"
  by (simp add: uW3_def mkU_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma rf_g4: "exec_label_preserves_history_wf (dwu_store uW4) (EnqueueDownstream ec2 e2)"
  by (simp add: uW4_def mkU_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma rf_g5: "exec_label_preserves_history_wf (dwu_store uW5) (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)


section \<open>4. The seven witness steps (six lifts at actor 0, then USpawn)\<close>

lemma rf_step0: "dwu_step uW0 (ULift 0 (DoSource ec1 e1)) uW1"
proof -
  have c: "dw_exec_step (dwu_store uW0) (DoSource ec1 e1)
             (mkC [(ec1, e1)] [] [] {} Running)"
    by (rule do_sourceI) (simp_all add: uW0_def mkU_def mkC_def)
  have "dwu_step uW0 (ULift 0 (DoSource ec1 e1))
          (uW0\<lparr>dwu_store := mkC [(ec1, e1)] [] [] {} Running,
               dwu_journal := dwu_journal uW0 @ [(ec1, e1)]\<rparr>)"
    by (rule dwu_step.ulift_source[OF _ _ c]) (simp_all add: uW0_def mkU_def)
  also have "\<dots> = uW1" by (simp add: uW0_def uW1_def mkU_def)
  finally show ?thesis .
qed

lemma rf_step1: "dwu_step uW1 (ULift 0 (EnqueueDownstream ec1 e1)) uW2"
proof -
  have c: "dw_exec_step (dwu_store uW1) (EnqueueDownstream ec1 e1)
             (mkC [(ec1, e1)] [] [(ec1, e1)] {(ec1, e1)} Running)"
    by (rule enqueue_downstreamI) (simp_all add: uW1_def mkU_def mkC_def)
  have "dwu_step uW1 (ULift 0 (EnqueueDownstream ec1 e1))
          (uW1\<lparr>dwu_store := mkC [(ec1, e1)] [] [(ec1, e1)] {(ec1, e1)} Running\<rparr>)"
    by (rule dwu_step.ulift_enqueue[OF _ _ c]) (simp_all add: uW1_def mkU_def)
  also have "\<dots> = uW2" by (simp add: uW1_def uW2_def mkU_def)
  finally show ?thesis .
qed

lemma rf_step2: "dwu_step uW2 (ULift 0 (DoDownstream ec1 e1)) uW3"
proof -
  have c: "dw_exec_step (dwu_store uW2) (DoDownstream ec1 e1)
             (mkC [(ec1, e1)] [(ec1, e1)] [(ec1, e1)] {} Running)"
    by (rule do_downstreamI) (simp_all add: uW2_def mkU_def mkC_def)
  have "dwu_step uW2 (ULift 0 (DoDownstream ec1 e1))
          (uW2\<lparr>dwu_store := mkC [(ec1, e1)] [(ec1, e1)] [(ec1, e1)] {} Running,
               dwu_sent := dwu_sent uW2 @ [rf_x1],
               dwu_accepted := dwu_accepted uW2 @
                 (if dwu_fence uW2 \<le> ue_gen rf_x1 then [rf_x1] else [])\<rparr>)"
    by (rule dwu_step.ulift_publish[OF _ _ c])
       (simp_all add: uW2_def mkU_def mkC_def rf_x1_def)
  also have "\<dots> = uW3" by (simp add: uW2_def uW3_def mkU_def rf_x1_def)
  finally show ?thesis .
qed

lemma rf_step3: "dwu_step uW3 (ULift 0 (DoSource ec2 e2)) uW4"
proof -
  have c: "dw_exec_step (dwu_store uW3) (DoSource ec2 e2)
             (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1)] [(ec1, e1)] {} Running)"
    by (rule do_sourceI) (simp_all add: uW3_def mkU_def mkC_def)
  have "dwu_step uW3 (ULift 0 (DoSource ec2 e2))
          (uW3\<lparr>dwu_store := mkC [(ec1, e1), (ec2, e2)] [(ec1, e1)] [(ec1, e1)] {} Running,
               dwu_journal := dwu_journal uW3 @ [(ec2, e2)]\<rparr>)"
    by (rule dwu_step.ulift_source[OF _ _ c]) (simp_all add: uW3_def mkU_def)
  also have "\<dots> = uW4" by (simp add: uW3_def uW4_def mkU_def)
  finally show ?thesis .
qed

lemma rf_step4: "dwu_step uW4 (ULift 0 (EnqueueDownstream ec2 e2)) uW5"
proof -
  have c: "dw_exec_step (dwu_store uW4) (EnqueueDownstream ec2 e2)
             (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1)]
                  [(ec1, e1), (ec2, e2)] {(ec2, e2)} Running)"
    by (rule enqueue_downstreamI) (simp_all add: uW4_def mkU_def mkC_def)
  have "dwu_step uW4 (ULift 0 (EnqueueDownstream ec2 e2))
          (uW4\<lparr>dwu_store := mkC [(ec1, e1), (ec2, e2)] [(ec1, e1)]
                  [(ec1, e1), (ec2, e2)] {(ec2, e2)} Running\<rparr>)"
    by (rule dwu_step.ulift_enqueue[OF _ _ c]) (simp_all add: uW4_def mkU_def)
  also have "\<dots> = uW5" by (simp add: uW4_def uW5_def mkU_def)
  finally show ?thesis .
qed

lemma rf_step5: "dwu_step uW5 (ULift 0 (Crash ec2)) uW6"
proof -
  have c: "dw_exec_step (dwu_store uW5) (Crash ec2) rf_sto6"
    by (rule crashI) (simp_all add: uW5_def mkU_def mkC_def rf_sto6_def)
  have "dwu_step uW5 (ULift 0 (Crash ec2)) (uW5\<lparr>dwu_store := rf_sto6\<rparr>)"
    by (rule dwu_step.ulift_nonprod[OF _ _ c]) (simp_all add: uW5_def mkU_def)
  also have "\<dots> = uW6" by (simp add: uW5_def uW6_def mkU_def)
  finally show ?thesis .
qed

lemma rf_step6: "dwu_step uW6 USpawn rf_W"
proof -
  have "dwu_step uW6 USpawn
          (uW6\<lparr>dwu_gens := (dwu_gens uW6)(Suc (dwu_hwm uW6) \<mapsto> UProd),
               dwu_hwm := Suc (dwu_hwm uW6)\<rparr>)"
    by (rule dwu_step.uspawn)
  also have "\<dots> = rf_W" by (simp add: uW6_def rf_W_def mkU_def)
  finally show ?thesis .
qed


section \<open>5. Reachability of the witness W\<close>

lemma rf_reach_W: "dwu_reachable_w rf_W"
proof -
  have r0: "dwu_reachable Map.empty {0, 1} ec2 uW0"
    unfolding rf_uW0_init by (rule dwu_reachable_init)
  have r1: "dwu_reachable Map.empty {0, 1} ec2 uW1"
    by (rule dwu_reach_lift[OF r0 rf_wf0 rf_g0 rf_step0])
  have r2: "dwu_reachable Map.empty {0, 1} ec2 uW2"
    by (rule dwu_reach_lift[OF r1 rf_wf1 rf_g1 rf_step1])
  have r3: "dwu_reachable Map.empty {0, 1} ec2 uW3"
    by (rule dwu_reach_lift[OF r2 rf_wf2 rf_g2 rf_step2])
  have r4: "dwu_reachable Map.empty {0, 1} ec2 uW4"
    by (rule dwu_reach_lift[OF r3 rf_wf3 rf_g3 rf_step3])
  have r5: "dwu_reachable Map.empty {0, 1} ec2 uW5"
    by (rule dwu_reach_lift[OF r4 rf_wf4 rf_g4 rf_step4])
  have r6: "dwu_reachable Map.empty {0, 1} ec2 uW6"
    by (rule dwu_reach_lift[OF r5 rf_wf5 rf_g5 rf_step5])
  show "dwu_reachable_w rf_W"
    by (rule dwu_reach_other[OF r6 _ _ rf_step6]) simp_all
qed


section \<open>6. The sink-delta and the two armed batches\<close>

lemma rf_len_W: "length (dwu_journal rf_W) = 2"
  by (simp add: rf_W_def mkU_def)

lemma rf_sink_W: "u_sink_delta ec2 rf_W = [(ec2, e2)]"
  by (simp add: u_sink_delta_def retained_hist_def rf_W_def mkU_def rf_sto6_def
                mkC_def log_payloads_def rf_x1_def map_filter_simps
                replay_down_hist_def e1_def e2_def ec_defs)

lemma rf_batch1:
  "u_stamped_batch (length (dwu_journal rf_W)) 0 (map ULog (u_sink_delta ec2 rf_W)) = rf_B1"
  by (simp add: rf_len_W rf_sink_W u_stamped_batch_def rf_B1_def rf_b1_def)


section \<open>7. The five concurrent-recovery steps\<close>

lemma rf_step_arm1: "dwu_step rf_W (UArm 0 rf_B1 ec2) rf_t1"
proof -
  have "dwu_step rf_W (UArm 0 rf_B1 ec2)
          (rf_W\<lparr>dwu_gens := (dwu_gens rf_W)(0 \<mapsto> UArmed rf_B1)\<rparr>)"
    by (rule dwu_step.uarm)
       (simp_all add: rf_W_def mkU_def rf_sto6_def mkC_def rf_B1_def rf_b1_def ec_defs)
  thus ?thesis by (simp add: rf_t1_def)
qed

lemma rf_sink_t1: "u_sink_delta ec2 rf_t1 = u_sink_delta ec2 rf_W"
  by (rule u_sink_delta_arm_const[OF rf_step_arm1])

lemma rf_len_t1: "length (dwu_journal rf_t1) = 2"
  by (simp add: rf_t1_def rf_W_def mkU_def)

lemma rf_batch2:
  "u_stamped_batch (length (dwu_journal rf_t1)) 1 (map ULog (u_sink_delta ec2 rf_t1)) = rf_B2"
  by (simp add: rf_len_t1 rf_sink_t1 rf_sink_W u_stamped_batch_def rf_B2_def rf_b2_def)

lemma rf_step_arm2: "dwu_step rf_t1 (UArm 1 rf_B2 ec2) rf_t2"
proof -
  have "dwu_step rf_t1 (UArm 1 rf_B2 ec2)
          (rf_t1\<lparr>dwu_gens := (dwu_gens rf_t1)(1 \<mapsto> UArmed rf_B2)\<rparr>)"
    by (rule dwu_step.uarm)
       (simp_all add: rf_t1_def rf_W_def mkU_def rf_sto6_def mkC_def
                      rf_B2_def rf_b2_def ec_defs)
  thus ?thesis by (simp add: rf_t2_def)
qed

lemma rf_step_heal: "dwu_step rf_t2 (UHeal 0 ec2) rf_t3"
proof -
  have rel: "relay_bounded_replay_reconcile (dwu_store rf_t2) ec2 rf_stoH"
    by (simp add: relay_bounded_replay_reconcile_def rf_t2_def rf_t1_def rf_W_def
                  mkU_def rf_sto6_def rf_stoH_def mkC_def replay_down_hist_def
                  e1_def e2_def ec_defs)
  have "dwu_step rf_t2 (UHeal 0 ec2) (rf_t2\<lparr>dwu_store := rf_stoH\<rparr>)"
    by (rule dwu_step.uheal[OF rel])
  thus ?thesis by (simp add: rf_t3_def)
qed

lemma rf_step_fire1: "dwu_step rf_t3 (UFire 0) rf_t4"
proof -
  have g: "dwu_gens rf_t3 0 = Some (UArmed rf_B1)"
    by (simp add: rf_t3_def rf_t2_def rf_t1_def rf_W_def mkU_def)
  have "dwu_step rf_t3 (UFire 0)
          (rf_t3\<lparr>dwu_sent := dwu_sent rf_t3 @ rf_B1,
                 dwu_accepted := dwu_accepted rf_t3 @
                   (if dwu_fence rf_t3 \<le> 0 then rf_B1 else []),
                 dwu_gens := (dwu_gens rf_t3)(0 \<mapsto> UProd)\<rparr>)"
    by (rule dwu_step.ufire[OF g])
  also have "\<dots> = rf_t4"
    by (simp add: rf_t4_def rf_t3_def rf_t2_def rf_t1_def rf_W_def mkU_def)
  finally show ?thesis .
qed

lemma rf_step_fire2: "dwu_step rf_t4 (UFire 1) rf_t5"
proof -
  have g: "dwu_gens rf_t4 1 = Some (UArmed rf_B2)"
    by (simp add: rf_t4_def rf_t3_def rf_t2_def rf_t1_def rf_W_def mkU_def)
  have "dwu_step rf_t4 (UFire 1)
          (rf_t4\<lparr>dwu_sent := dwu_sent rf_t4 @ rf_B2,
                 dwu_accepted := dwu_accepted rf_t4 @
                   (if dwu_fence rf_t4 \<le> 1 then rf_B2 else []),
                 dwu_gens := (dwu_gens rf_t4)(1 \<mapsto> UProd)\<rparr>)"
    by (rule dwu_step.ufire[OF g])
  also have "\<dots> = rf_t5"
    by (simp add: rf_t5_def rf_t4_def rf_t3_def rf_t2_def rf_t1_def rf_W_def mkU_def)
  finally show ?thesis .
qed


section \<open>8. The verdicts on the witness endpoints\<close>

lemma rf_safe_W: "\<not> u_effect_unsafe rf_W"
  by (simp add: u_effect_unsafe_def u_premature_def u_duplicate_def u_justified_def
                rf_W_def mkU_def rf_sto6_def mkC_def rf_x1_def log_payloads_def
                map_filter_simps e1_def ec_defs)

lemma rf_dup_t5: "u_duplicate rf_t5"
  by (simp add: u_duplicate_def rf_t5_def rf_t4_def rf_t3_def rf_t2_def rf_t1_def
                rf_W_def mkU_def rf_B1_def rf_B2_def rf_b1_def rf_b2_def rf_x1_def
                log_payloads_def map_filter_simps e1_def e2_def ec_defs)

lemma rf_notlost_t5: "\<not> u_lost ec2 rf_t5"
  by (simp add: u_lost_def retained_hist_def rf_t5_def rf_t4_def rf_t3_def rf_t2_def
                rf_t1_def rf_W_def mkU_def rf_stoH_def mkC_def rf_B1_def rf_B2_def
                rf_b1_def rf_b2_def rf_x1_def log_payloads_def map_filter_simps
                replay_down_hist_def e1_def e2_def ec_defs)


section \<open>9. THE PRINCIPAL (U10, pinned VERBATIM from the probe seed)\<close>

theorem u_concurrent_recovery_defeats_sink_delta:
  "\<exists>W g1 g2 f p t1 t2 t3 t4 t5.
     dwu_reachable_w W
   \<and> (\<exists>c. exec_status (dwu_store W) = Crashed c)
   \<and> dwu_fence W = 0
   \<and> g1 \<noteq> g2
   \<and> dwu_gens W g1 = Some UProd \<and> dwu_gens W g2 = Some UProd
   \<and> \<not> u_effect_unsafe W
   \<and> u_sink_delta f W = [p]
   \<and> dwu_step W
       (UArm g1 (u_stamped_batch (length (dwu_journal W)) g1
                   (map ULog (u_sink_delta f W))) f) t1
   \<and> u_sink_delta f t1 = u_sink_delta f W
   \<and> dwu_step t1
       (UArm g2 (u_stamped_batch (length (dwu_journal t1)) g2
                   (map ULog (u_sink_delta f t1))) f) t2
   \<and> dwu_step t2 (UHeal g1 f) t3
   \<and> dwu_step t3 (UFire g1) t4
   \<and> dwu_step t4 (UFire g2) t5
   \<and> u_duplicate t5
   \<and> \<not> u_lost f t5"
proof -
  \<comment> \<open>the fully-instantiated body (witnesses W := rf_W, g1 := 0, g2 := 1, f := ec2,
      p := (ec2, e2), t1..t5 := rf_t1..rf_t5); the existentials are peeled one at a
      time afterwards so no @{text exI} eats the inner @{text "\<exists>c"} crashed witness.\<close>
  have body:
    "dwu_reachable_w rf_W
   \<and> (\<exists>c. exec_status (dwu_store rf_W) = Crashed c)
   \<and> dwu_fence rf_W = 0
   \<and> (0::nat) \<noteq> 1
   \<and> dwu_gens rf_W 0 = Some UProd \<and> dwu_gens rf_W 1 = Some UProd
   \<and> \<not> u_effect_unsafe rf_W
   \<and> u_sink_delta ec2 rf_W = [(ec2, e2)]
   \<and> dwu_step rf_W
       (UArm 0 (u_stamped_batch (length (dwu_journal rf_W)) 0
                   (map ULog (u_sink_delta ec2 rf_W))) ec2) rf_t1
   \<and> u_sink_delta ec2 rf_t1 = u_sink_delta ec2 rf_W
   \<and> dwu_step rf_t1
       (UArm 1 (u_stamped_batch (length (dwu_journal rf_t1)) 1
                   (map ULog (u_sink_delta ec2 rf_t1))) ec2) rf_t2
   \<and> dwu_step rf_t2 (UHeal 0 ec2) rf_t3
   \<and> dwu_step rf_t3 (UFire 0) rf_t4
   \<and> dwu_step rf_t4 (UFire 1) rf_t5
   \<and> u_duplicate rf_t5
   \<and> \<not> u_lost ec2 rf_t5"
  proof (intro conjI)
    show "dwu_reachable_w rf_W" by (rule rf_reach_W)
  next
    show "\<exists>c. exec_status (dwu_store rf_W) = Crashed c"
      by (rule exI[of _ ec2]) (simp add: rf_W_def mkU_def rf_sto6_def mkC_def)
  next
    show "dwu_fence rf_W = 0" by (simp add: rf_W_def mkU_def)
  next
    show "(0::nat) \<noteq> 1" by simp
  next
    show "dwu_gens rf_W 0 = Some UProd" by (simp add: rf_W_def mkU_def)
  next
    show "dwu_gens rf_W 1 = Some UProd" by (simp add: rf_W_def mkU_def)
  next
    show "\<not> u_effect_unsafe rf_W" by (rule rf_safe_W)
  next
    show "u_sink_delta ec2 rf_W = [(ec2, e2)]" by (rule rf_sink_W)
  next
    show "dwu_step rf_W
            (UArm 0 (u_stamped_batch (length (dwu_journal rf_W)) 0
                       (map ULog (u_sink_delta ec2 rf_W))) ec2) rf_t1"
      unfolding rf_batch1 by (rule rf_step_arm1)
  next
    show "u_sink_delta ec2 rf_t1 = u_sink_delta ec2 rf_W" by (rule rf_sink_t1)
  next
    show "dwu_step rf_t1
            (UArm 1 (u_stamped_batch (length (dwu_journal rf_t1)) 1
                       (map ULog (u_sink_delta ec2 rf_t1))) ec2) rf_t2"
      unfolding rf_batch2 by (rule rf_step_arm2)
  next
    show "dwu_step rf_t2 (UHeal 0 ec2) rf_t3" by (rule rf_step_heal)
  next
    show "dwu_step rf_t3 (UFire 0) rf_t4" by (rule rf_step_fire1)
  next
    show "dwu_step rf_t4 (UFire 1) rf_t5" by (rule rf_step_fire2)
  next
    show "u_duplicate rf_t5" by (rule rf_dup_t5)
  next
    show "\<not> u_lost ec2 rf_t5" by (rule rf_notlost_t5)
  qed
  show ?thesis
    by (rule exI[of _ rf_W], rule exI[of _ "0::nat"], rule exI[of _ "1::nat"],
        rule exI[of _ ec2], rule exI[of _ "(ec2, e2)"], rule exI[of _ rf_t1],
        rule exI[of _ rf_t2], rule exI[of _ rf_t3], rule exI[of _ rf_t4],
        rule exI[of _ rf_t5]) (rule body)
qed

end
