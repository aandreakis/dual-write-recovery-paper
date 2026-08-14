(*  Title:       DWU_Aliasing_Gates.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Purpose: Road-2 I4 --- U12, the aliasing-vs-fence separation (COUNT-form).

    "Generations separate what payloads cannot."  A reachable crashed dual-write
    state whose JOURNAL double-commits one payload (equal source coordinate ec1,
    the landed dd4_w aliasing template) and whose FENCE is a spawned generation
    (g = 1 > g' = 0): the fence run keeps EXACTLY the two full-generation instances
    and excludes the superseded-generation re-fire, while EVERY accept-time payload
    dedup gate D either re-admits that re-fire or fails to reach an instance count of 2 --- the
    honest observable is the count, not set-membership (the naive set-form is REFUTED
    and banked as a negative).

    Honesty fences: the fence conjunct is INSTANCE-COUNT (= 2) + superseded-re-fire-excluded,
    NEVER not-effect-unsafe (two equal ULog payloads ARE u_duplicate by design).  No
    strictly_ascending_source is consumed (the witness is deliberately non-ascending:
    equal coordinates).  No concurrency vocabulary.

    The theorem u_aliasing_defeats_payload_gates is copied VERBATIM from the Stage-4
    probe seed (P5 amended pin); only the proof is new.

    Honesty regime: quick_and_dirty = false (ROOT-pinned), ZERO sorry, ZERO oops,
    no axiomatization, no consts, no oracles.  Every statement is PROVED.
*)

theory DWU_Aliasing_Gates
  imports DWU_Fenced_Discipline
begin

section \<open>1. The U12 gate apparatus (P5 amended pin, verbatim from seed 1.10)\<close>

type_synonym ('k, 'v) u_pay_gate =
  "('k, 'v) upayload \<Rightarrow> ('k, 'v) upayload list \<Rightarrow> bool"

definition u_gate_run
  :: "('k, 'v) u_pay_gate \<Rightarrow> ('k, 'v) uemission list \<Rightarrow> ('k, 'v) uemission list"
where
  "u_gate_run D xs =
     foldl (\<lambda>acc x. if D (ue_pay x) (map ue_pay acc) then acc @ [x] else acc) [] xs"

definition u_fence_run :: "nat \<Rightarrow> ('k, 'v) uemission list \<Rightarrow> ('k, 'v) uemission list" where
  "u_fence_run F xs = filter (\<lambda>x. F \<le> ue_gen x) xs"


section \<open>2. The reachable double-commit crashed witness (equal-coordinate re-commit)\<close>

text \<open>Stores along the witness chain: an equal-coordinate re-commit of @{term "(ec1, e1)"}
  (WF-H1 @{const src_le} is non-strict, so @{term "[(ec1, e1), (ec1, e1)]"} is
  wellformed --- the landed @{thm [source] wfh_e1_pair_eq}).\<close>

definition ag_sto0 :: "(nat, nat) dw_exec_state" where
  "ag_sto0 = mkC [] [] [] {} Running"
definition ag_sto1 :: "(nat, nat) dw_exec_state" where
  "ag_sto1 = mkC [(ec1, e1)] [] [] {} Running"
definition ag_sto2 :: "(nat, nat) dw_exec_state" where
  "ag_sto2 = mkC [(ec1, e1), (ec1, e1)] [] [] {} Running"
definition ag_stoC :: "(nat, nat) dw_exec_state" where
  "ag_stoC = mkC [(ec1, e1), (ec1, e1)] [] [] {} (Crashed ec2)"

definition ag_s0 :: "(nat, nat) dwu_state" where
  "ag_s0 = mkU ag_sto0 [] [] [] [0 \<mapsto> UProd] 0"
definition ag_s1 :: "(nat, nat) dwu_state" where
  "ag_s1 = mkU ag_sto1 [(ec1, e1)] [] [] [0 \<mapsto> UProd] 0"
definition ag_s2 :: "(nat, nat) dwu_state" where
  "ag_s2 = mkU ag_sto2 [(ec1, e1), (ec1, e1)] [] [] [0 \<mapsto> UProd] 0"
definition ag_s3 :: "(nat, nat) dwu_state" where
  "ag_s3 = mkU ag_sto2 [(ec1, e1), (ec1, e1)] [] [] [0 \<mapsto> UProd, 1 \<mapsto> UProd] 1"
definition ag_s4 :: "(nat, nat) dwu_state" where
  "ag_s4 = ag_s3\<lparr>dwu_fence := 1\<rparr>"
definition ag_W :: "(nat, nat) dwu_state" where
  "ag_W = ag_s4\<lparr>dwu_store := ag_stoC\<rparr>"

text \<open>The two aliased emissions: @{term ag_xL} a full-generation instance
  (gen 1 = the fence), @{term ag_xS} a superseded-generation re-fire (gen 0 < fence) --- SAME
  payload @{term "ULog (ec1, e1)"}.\<close>

definition ag_xL :: "(nat, nat) uemission" where
  "ag_xL = \<lparr> ue_stamp = 2, ue_gen = 1, ue_pay = ULog (ec1, e1) \<rparr>"
definition ag_xS :: "(nat, nat) uemission" where
  "ag_xS = \<lparr> ue_stamp = 1, ue_gen = 0, ue_pay = ULog (ec1, e1) \<rparr>"


section \<open>3. Wellformedness, label guards, and the six witness steps\<close>

lemma ag_s0_init: "ag_s0 = dwu_init Map.empty {0, 1} ec2"
  by (simp add: ag_s0_def ag_sto0_def mkU_def mkC_def dwu_init_def initial_exec_state_def)

lemma ag_wf0: "wellformed_exec_state (dwu_store ag_s0)"
  by (simp add: ag_s0_def ag_sto0_def mkU_def mkC_def ws_defs wf_hist_Nil)

lemma ag_wf1: "wellformed_exec_state (dwu_store ag_s1)"
  by (simp add: ag_s1_def ag_sto1_def mkU_def mkC_def ws_defs wf_hist_Nil wfh_e1)

lemma ag_wf4: "wellformed_exec_state (dwu_store ag_s4)"
  by (simp add: ag_s4_def ag_s3_def ag_sto2_def mkU_def mkC_def ws_defs
                wf_hist_Nil wfh_e1_pair_eq)

lemma ag_g0: "exec_label_preserves_history_wf (dwu_store ag_s0) (DoSource ec1 e1)"
  by (simp add: ag_s0_def ag_sto0_def mkU_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma ag_g1: "exec_label_preserves_history_wf (dwu_store ag_s1) (DoSource ec1 e1)"
  by (simp add: ag_s1_def ag_sto1_def mkU_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma ag_g4: "exec_label_preserves_history_wf (dwu_store ag_s4) (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma ag_step0: "dwu_step ag_s0 (ULift 0 (DoSource ec1 e1)) ag_s1"
proof -
  have c: "dw_exec_step (dwu_store ag_s0) (DoSource ec1 e1) ag_sto1"
    by (rule do_sourceI) (simp_all add: ag_s0_def ag_sto0_def ag_sto1_def mkU_def mkC_def)
  have "dwu_step ag_s0 (ULift 0 (DoSource ec1 e1))
          (ag_s0\<lparr>dwu_store := ag_sto1, dwu_journal := dwu_journal ag_s0 @ [(ec1, e1)]\<rparr>)"
    by (rule dwu_step.ulift_source[OF _ _ c]) (simp_all add: ag_s0_def mkU_def)
  also have "\<dots> = ag_s1" by (simp add: ag_s0_def ag_s1_def mkU_def)
  finally show ?thesis .
qed

lemma ag_step1: "dwu_step ag_s1 (ULift 0 (DoSource ec1 e1)) ag_s2"
proof -
  have c: "dw_exec_step (dwu_store ag_s1) (DoSource ec1 e1) ag_sto2"
    by (rule do_sourceI) (simp_all add: ag_s1_def ag_sto1_def ag_sto2_def mkU_def mkC_def)
  have "dwu_step ag_s1 (ULift 0 (DoSource ec1 e1))
          (ag_s1\<lparr>dwu_store := ag_sto2, dwu_journal := dwu_journal ag_s1 @ [(ec1, e1)]\<rparr>)"
    by (rule dwu_step.ulift_source[OF _ _ c]) (simp_all add: ag_s1_def mkU_def)
  also have "\<dots> = ag_s2" by (simp add: ag_s1_def ag_s2_def mkU_def)
  finally show ?thesis .
qed

lemma ag_step_spawn: "dwu_step ag_s2 USpawn ag_s3"
proof -
  have "dwu_step ag_s2 USpawn
          (ag_s2\<lparr>dwu_gens := (dwu_gens ag_s2)(Suc (dwu_hwm ag_s2) \<mapsto> UProd),
                 dwu_hwm := Suc (dwu_hwm ag_s2)\<rparr>)"
    by (rule dwu_step.uspawn)
  also have "\<dots> = ag_s3" by (simp add: ag_s2_def ag_s3_def mkU_def)
  finally show ?thesis .
qed

lemma ag_step_fence: "dwu_step ag_s3 (UFenceRaise 1) ag_s4"
proof -
  have "dwu_step ag_s3 (UFenceRaise 1) (ag_s3\<lparr>dwu_fence := max (dwu_fence ag_s3) 1\<rparr>)"
    by (rule dwu_step.ufenceraise)
  also have "\<dots> = ag_s4" by (simp add: ag_s3_def ag_s4_def mkU_def)
  finally show ?thesis .
qed

lemma ag_step_crash: "dwu_step ag_s4 (ULift 0 (Crash ec2)) ag_W"
proof -
  have c: "dw_exec_step (dwu_store ag_s4) (Crash ec2) ag_stoC"
    by (rule crashI)
       (simp_all add: ag_s4_def ag_s3_def ag_sto2_def ag_stoC_def mkU_def mkC_def)
  have "dwu_step ag_s4 (ULift 0 (Crash ec2)) (ag_s4\<lparr>dwu_store := ag_stoC\<rparr>)"
    by (rule dwu_step.ulift_nonprod[OF _ _ c]) (simp_all add: ag_s4_def ag_s3_def mkU_def)
  also have "\<dots> = ag_W" by (simp add: ag_W_def)
  finally show ?thesis .
qed


section \<open>4. Reachability of the witness\<close>

lemma ag_reach_W: "dwu_reachable_w ag_W"
proof -
  have r0: "dwu_reachable Map.empty {0, 1} ec2 ag_s0"
    unfolding ag_s0_init by (rule dwu_reachable_init)
  have r1: "dwu_reachable Map.empty {0, 1} ec2 ag_s1"
    by (rule dwu_reach_lift[OF r0 ag_wf0 ag_g0 ag_step0])
  have r2: "dwu_reachable Map.empty {0, 1} ec2 ag_s2"
    by (rule dwu_reach_lift[OF r1 ag_wf1 ag_g1 ag_step1])
  have r3: "dwu_reachable Map.empty {0, 1} ec2 ag_s3"
    by (rule dwu_reach_other[OF r2 _ _ ag_step_spawn]) simp_all
  have r4: "dwu_reachable Map.empty {0, 1} ec2 ag_s4"
    by (rule dwu_reach_other[OF r3 _ _ ag_step_fence]) simp_all
  show "dwu_reachable_w ag_W"
    by (rule dwu_reach_lift[OF r4 ag_wf4 ag_g4 ag_step_crash])
qed


section \<open>5. U12 --- aliasing defeats payload gates (statement VERBATIM from seed)\<close>

theorem u_aliasing_defeats_payload_gates:
  "\<exists>W g g' xL xS.
     dwu_reachable_w W
   \<and> (\<exists>c. exec_status (dwu_store W) = Crashed c)
   \<and> ue_pay xL = ue_pay xS \<and> (\<exists>p. ue_pay xL = ULog p)
   \<and> u_justified W xL
   \<and> 2 \<le> count_list (dwu_journal W) (ulog_of xL)
   \<and> ue_gen xL = g \<and> ue_gen xS = g' \<and> g' < g \<and> dwu_fence W = g
   \<and> (let xs = [xL, xS, xL] in
          xS \<notin> set (u_fence_run (dwu_fence W) xs)
        \<and> count_list (map ue_pay (u_fence_run (dwu_fence W) xs)) (ue_pay xL) = 2)
   \<and> (\<forall>D. let xs = [xL, xS, xL] in
          xS \<in> set (u_gate_run D xs)
        \<or> count_list (map ue_pay (u_gate_run D xs)) (ue_pay xL) < 2)"
proof -
  have payL: "ue_pay ag_xL = ULog (ec1, e1)" by (simp add: ag_xL_def)
  have payS: "ue_pay ag_xS = ULog (ec1, e1)" by (simp add: ag_xS_def)
  have W_fence: "dwu_fence ag_W = 1" by (simp add: ag_W_def ag_s4_def)
  have W_journal: "dwu_journal ag_W = [(ec1, e1), (ec1, e1)]"
    by (simp add: ag_W_def ag_s4_def ag_s3_def mkU_def)
  have W_crashed: "\<exists>c. exec_status (dwu_store ag_W) = Crashed c"
    by (rule exI[of _ ec2]) (simp add: ag_W_def ag_stoC_def mkC_def)

  \<comment> \<open>the fence run keeps EXACTLY the two full-generation instances\<close>
  have fence_run: "u_fence_run (dwu_fence ag_W) [ag_xL, ag_xS, ag_xL] = [ag_xL, ag_xL]"
    by (simp add: u_fence_run_def W_fence ag_xL_def ag_xS_def)

  \<comment> \<open>THE AIRTIGHT CORE: every accept-time payload dedup gate D re-admits the
      superseded re-fire or fails to reach instance count 2 (pure, asc-free, determinism)\<close>
  have gate_horn:
    "\<forall>D. let xs = [ag_xL, ag_xS, ag_xL] in
          ag_xS \<in> set (u_gate_run D xs)
        \<or> count_list (map ue_pay (u_gate_run D xs)) (ue_pay ag_xL) < 2"
  proof (intro allI)
    fix D :: "(nat, nat) u_pay_gate"
    show "let xs = [ag_xL, ag_xS, ag_xL] in
            ag_xS \<in> set (u_gate_run D xs)
          \<or> count_list (map ue_pay (u_gate_run D xs)) (ue_pay ag_xL) < 2"
      unfolding Let_def
    proof -
      consider (c0) "\<not> D (ULog (ec1, e1)) []"
             | (c1) "D (ULog (ec1, e1)) [] \<and> D (ULog (ec1, e1)) [ULog (ec1, e1)]"
             | (c2) "D (ULog (ec1, e1)) [] \<and> \<not> D (ULog (ec1, e1)) [ULog (ec1, e1)]"
        by blast
      then show "ag_xS \<in> set (u_gate_run D [ag_xL, ag_xS, ag_xL])
               \<or> count_list (map ue_pay (u_gate_run D [ag_xL, ag_xS, ag_xL])) (ue_pay ag_xL) < 2"
      proof cases
        case c0
        \<comment> \<open>gate rejects the first instance from empty history \<Rightarrow> nothing accepted\<close>
        hence "u_gate_run D [ag_xL, ag_xS, ag_xL] = []"
          by (simp add: u_gate_run_def payL payS)
        thus ?thesis by simp
      next
        case c1
        \<comment> \<open>gate admits at history @{term "[ULog (ec1, e1)]"} \<Rightarrow> the superseded re-fire is admitted\<close>
        then have b0: "D (ULog (ec1, e1)) []"
              and b1: "D (ULog (ec1, e1)) [ULog (ec1, e1)]" by auto
        have "ag_xS \<in> set (u_gate_run D [ag_xL, ag_xS, ag_xL])"
          by (auto simp: u_gate_run_def payL payS b0 b1)
        thus ?thesis by blast
      next
        case c2
        \<comment> \<open>gate rejects at @{term "[ULog (ec1, e1)]"} \<Rightarrow> the 2nd @{term ag_xL} sees the SAME
            history and is rejected too (determinism) \<Rightarrow> only ONE instance survives\<close>
        then have b0: "D (ULog (ec1, e1)) []"
              and b1: "\<not> D (ULog (ec1, e1)) [ULog (ec1, e1)]" by auto
        have "u_gate_run D [ag_xL, ag_xS, ag_xL] = [ag_xL]"
          by (simp add: u_gate_run_def payL payS b0 b1)
        thus ?thesis by (simp add: payL)
      qed
    qed
  qed

  have body:
    "dwu_reachable_w ag_W
   \<and> (\<exists>c. exec_status (dwu_store ag_W) = Crashed c)
   \<and> ue_pay ag_xL = ue_pay ag_xS \<and> (\<exists>p. ue_pay ag_xL = ULog p)
   \<and> u_justified ag_W ag_xL
   \<and> 2 \<le> count_list (dwu_journal ag_W) (ulog_of ag_xL)
   \<and> ue_gen ag_xL = 1 \<and> ue_gen ag_xS = 0 \<and> (0::nat) < 1 \<and> dwu_fence ag_W = 1
   \<and> (let xs = [ag_xL, ag_xS, ag_xL] in
          ag_xS \<notin> set (u_fence_run (dwu_fence ag_W) xs)
        \<and> count_list (map ue_pay (u_fence_run (dwu_fence ag_W) xs)) (ue_pay ag_xL) = 2)
   \<and> (\<forall>D. let xs = [ag_xL, ag_xS, ag_xL] in
          ag_xS \<in> set (u_gate_run D xs)
        \<or> count_list (map ue_pay (u_gate_run D xs)) (ue_pay ag_xL) < 2)"
  proof (intro conjI)
    show "dwu_reachable_w ag_W" by (rule ag_reach_W)
  next
    show "\<exists>c. exec_status (dwu_store ag_W) = Crashed c" by (rule W_crashed)
  next
    show "ue_pay ag_xL = ue_pay ag_xS" by (simp add: payL payS)
  next
    show "\<exists>p. ue_pay ag_xL = ULog p" by (rule exI[of _ "(ec1, e1)"]) (rule payL)
  next
    show "u_justified ag_W ag_xL"
      by (simp add: u_justified_def ag_xL_def W_journal)
  next
    show "2 \<le> count_list (dwu_journal ag_W) (ulog_of ag_xL)"
      by (simp add: ulog_of_def ag_xL_def W_journal)
  next
    show "ue_gen ag_xL = 1" by (simp add: ag_xL_def)
  next
    show "ue_gen ag_xS = 0" by (simp add: ag_xS_def)
  next
    show "(0::nat) < 1" by simp
  next
    show "dwu_fence ag_W = 1" by (rule W_fence)
  next
    show "let xs = [ag_xL, ag_xS, ag_xL] in
            ag_xS \<notin> set (u_fence_run (dwu_fence ag_W) xs)
          \<and> count_list (map ue_pay (u_fence_run (dwu_fence ag_W) xs)) (ue_pay ag_xL) = 2"
      unfolding Let_def
    proof (intro conjI)
      show "ag_xS \<notin> set (u_fence_run (dwu_fence ag_W) [ag_xL, ag_xS, ag_xL])"
        unfolding fence_run by (simp add: ag_xL_def ag_xS_def)
    next
      show "count_list (map ue_pay (u_fence_run (dwu_fence ag_W) [ag_xL, ag_xS, ag_xL])) (ue_pay ag_xL) = 2"
        unfolding fence_run by simp
    qed
  next
    show "\<forall>D. let xs = [ag_xL, ag_xS, ag_xL] in
            ag_xS \<in> set (u_gate_run D xs)
          \<or> count_list (map ue_pay (u_gate_run D xs)) (ue_pay ag_xL) < 2"
      by (rule gate_horn)
  qed

  show ?thesis
    by (rule exI[of _ ag_W], rule exI[of _ "1::nat"], rule exI[of _ "0::nat"],
        rule exI[of _ ag_xL], rule exI[of _ ag_xS]) (rule body)
qed

end
