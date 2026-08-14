(*  Title:       Dual_Write_Effect_Witnesses.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Closed witnesses for the effect tier.  These are DESIGNED-IN boundary
    certificates: the machine was architected so that these states are
    reachable, and they are presented as such --- they feed the tier's
    general theorems, they are not discovered surprises.

    G1  dwe_duplicate_separation: two reachable states with LITERALLY EQUAL
        cores and opposite effect verdicts (machine-level negation of the
        image wall for the effect verdict).
    G2  crash_heal_reemit_bridge: crash in a genuinely loaded window; the
        SAME emitting reconcile that heals the scoped store image re-fires
        the already-emitted effect; both occurrences are justified
        (duplication is orthogonal to justification).  A certified
        illustration: the heal is the cited landed relay theorem, the
        duplicate is the rule's designed-in re-drive at a stale cursor.
    G3  effect_nonvacuity_pair: (a) a genuinely-emitting, genuinely-healing,
        SAFE recovery run (the checkpoint alone separates it from G2's
        unsafe run); (b) a genuinely-emitting premature/phantom run.
    G4  four_corner_independence: all four (P_img, effect-verdict) corners
        inhabited by reachable genuinely-emitting states at frontier ec2.
    T2.7 premature_core_invisible_pair: reorder the safe three-step window
        so the delivery precedes the source commit --- literally equal final
        cores, premature vs safe.  With G1 this closes the referee gap
        "only duplicates escape the image": BOTH effect hazards do.

    Witness instantiation ('k = 'v = nat): b0 = Map.empty, K = {0, 1},
    fin = ec2, ev1 = Insert 0 1 at ec1, ev2 = Insert 1 2 at ec2.

    Ported from the phase-2 verified scratch source (p1 Effect_Witnesses.thy)
    with statements unchanged, plus the new core-invisible premature pair
    section (the phase-3 plan's remaining must-fix T2.7).  The scratch
    original's in-source ML oracle gates are STRIPPED here: oracle-freedom
    is certified by scratch-side per-slice gate sessions with
    confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Witnesses
  imports Dual_Write_Effect_Machine
begin

section \<open>Concrete events and core states\<close>

definition ev1 :: "(nat, nat) source_event" where "ev1 = Insert 0 1"
definition ev2 :: "(nat, nat) source_event" where "ev2 = Insert 1 2"

definition s0 :: "(nat, nat) dw_exec_state" where
  "s0 = initial_exec_state Map.empty {0, 1} ec2"

definition s1 :: "(nat, nat) dw_exec_state" where
  "s1 = s0\<lparr>exec_src_hist := exec_src_hist s0 @ [(ec1, ev1)]\<rparr>"

definition s2 :: "(nat, nat) dw_exec_state" where
  "s2 = s1\<lparr>exec_enqueued := exec_enqueued s1 @ [(ec1, ev1)],
           exec_pending := insert (ec1, ev1) (exec_pending s1)\<rparr>"

definition s3 :: "(nat, nat) dw_exec_state" where
  "s3 = s2\<lparr>exec_down_hist := exec_down_hist s2 @ [(ec1, ev1)],
           exec_pending := exec_pending s2 - {(ec1, ev1)}\<rparr>"

text \<open>G1 branch: crash right after the delivered first write.\<close>

definition s3c :: "(nat, nat) dw_exec_state" where
  "s3c = s3\<lparr>exec_status := Crashed ec1\<rparr>"

definition s3r :: "(nat, nat) dw_exec_state" where
  "s3r = s3c\<lparr>exec_down_hist :=
               replay_down_hist (exec_src_hist s3c) (exec_scope s3c) ec1,
             exec_pending := {},
             exec_status := Recovered\<rparr>"

text \<open>G2 branch: second committed write enqueued but undelivered, then crash.\<close>

definition s4 :: "(nat, nat) dw_exec_state" where
  "s4 = s3\<lparr>exec_src_hist := exec_src_hist s3 @ [(ec2, ev2)]\<rparr>"

definition s5 :: "(nat, nat) dw_exec_state" where
  "s5 = s4\<lparr>exec_enqueued := exec_enqueued s4 @ [(ec2, ev2)],
           exec_pending := insert (ec2, ev2) (exec_pending s4)\<rparr>"

definition s6 :: "(nat, nat) dw_exec_state" where
  "s6 = s5\<lparr>exec_status := Crashed ec2\<rparr>"

definition s6r :: "(nat, nat) dw_exec_state" where
  "s6r = s6\<lparr>exec_down_hist :=
              replay_down_hist (exec_src_hist s6) (exec_scope s6) ec2,
            exec_pending := {},
            exec_status := Recovered\<rparr>"

text \<open>G4 fourth-corner branch: deliver the UNCOMMITTED second write, crash.\<close>

definition u2 :: "(nat, nat) dw_exec_state" where
  "u2 = s1\<lparr>exec_enqueued := exec_enqueued s1 @ [(ec2, ev2)],
           exec_pending := insert (ec2, ev2) (exec_pending s1)\<rparr>"

definition u3 :: "(nat, nat) dw_exec_state" where
  "u3 = u2\<lparr>exec_down_hist := exec_down_hist u2 @ [(ec2, ev2)],
           exec_pending := exec_pending u2 - {(ec2, ev2)}\<rparr>"

definition u4 :: "(nat, nat) dw_exec_state" where
  "u4 = u3\<lparr>exec_status := Crashed ec2\<rparr>"

text \<open>G3(b) branch: publish with NO committed source at all (stamp 0).\<close>

definition b1 :: "(nat, nat) dw_exec_state" where
  "b1 = s0\<lparr>exec_enqueued := exec_enqueued s0 @ [(ec1, ev1)],
           exec_pending := insert (ec1, ev1) (exec_pending s0)\<rparr>"

definition b2 :: "(nat, nat) dw_exec_state" where
  "b2 = b1\<lparr>exec_down_hist := exec_down_hist b1 @ [(ec1, ev1)],
           exec_pending := exec_pending b1 - {(ec1, ev1)}\<rparr>"

section \<open>Core steps\<close>

lemma st01: "dw_exec_step s0 (DoSource ec1 ev1) s1"
  unfolding s1_def
  by (rule dw_exec_step.do_source) (simp add: s0_def initial_exec_state_def)

lemma st12: "dw_exec_step s1 (EnqueueDownstream ec1 ev1) s2"
  unfolding s2_def
  by (rule dw_exec_step.enqueue_downstream)
     (simp add: s1_def s0_def initial_exec_state_def)

lemma st23: "dw_exec_step s2 (DoDownstream ec1 ev1) s3"
  unfolding s3_def
  by (rule dw_exec_step.do_downstream)
     (simp_all add: s2_def s1_def s0_def initial_exec_state_def)

lemma st3c: "dw_exec_step s3 (Crash ec1) s3c"
  unfolding s3c_def
  by (rule dw_exec_step.crash)
     (simp add: s3_def s2_def s1_def s0_def initial_exec_state_def)

lemma st34: "dw_exec_step s3 (DoSource ec2 ev2) s4"
  unfolding s4_def
  by (rule dw_exec_step.do_source)
     (simp add: s3_def s2_def s1_def s0_def initial_exec_state_def)

lemma st45: "dw_exec_step s4 (EnqueueDownstream ec2 ev2) s5"
  unfolding s5_def
  by (rule dw_exec_step.enqueue_downstream)
     (simp add: s4_def s3_def s2_def s1_def s0_def initial_exec_state_def)

lemma st56: "dw_exec_step s5 (Crash ec2) s6"
  unfolding s6_def
  by (rule dw_exec_step.crash)
     (simp add: s5_def s4_def s3_def s2_def s1_def s0_def initial_exec_state_def)

lemma stu12: "dw_exec_step s1 (EnqueueDownstream ec2 ev2) u2"
  unfolding u2_def
  by (rule dw_exec_step.enqueue_downstream)
     (simp add: s1_def s0_def initial_exec_state_def)

lemma stu23: "dw_exec_step u2 (DoDownstream ec2 ev2) u3"
  unfolding u3_def
  by (rule dw_exec_step.do_downstream)
     (simp_all add: u2_def s1_def s0_def initial_exec_state_def)

lemma stu34: "dw_exec_step u3 (Crash ec2) u4"
  unfolding u4_def
  by (rule dw_exec_step.crash)
     (simp add: u3_def u2_def s1_def s0_def initial_exec_state_def)

lemma stb01: "dw_exec_step s0 (EnqueueDownstream ec1 ev1) b1"
  unfolding b1_def
  by (rule dw_exec_step.enqueue_downstream)
     (simp add: s0_def initial_exec_state_def)

lemma stb12: "dw_exec_step b1 (DoDownstream ec1 ev1) b2"
  unfolding b2_def
  by (rule dw_exec_step.do_downstream)
     (simp_all add: b1_def s0_def initial_exec_state_def)

section \<open>Admissibility side conditions (wellformedness chained through the runs)\<close>

lemma wf_s0: "wellformed_exec_state s0"
  by (simp add: s0_def)

lemma pres_s0_do1: "exec_label_preserves_history_wf s0 (DoSource ec1 ev1)"
  by (simp add: exec_label_preserves_history_wf_def history_can_append_def
                s0_def initial_exec_state_def ec_defs)

lemma wf_s1: "wellformed_exec_state s1"
  by (rule dw_exec_step_wellformed_exec_state[OF st01 wf_s0 pres_s0_do1])

lemma pres_s1_enq1: "exec_label_preserves_history_wf s1 (EnqueueDownstream ec1 ev1)"
  by (simp add: exec_label_preserves_history_wf_def history_can_append_def
                s1_def s0_def initial_exec_state_def ec_defs)

lemma wf_s2: "wellformed_exec_state s2"
  by (rule dw_exec_step_wellformed_exec_state[OF st12 wf_s1 pres_s1_enq1])

lemma pres_s2_down1: "exec_label_preserves_history_wf s2 (DoDownstream ec1 ev1)"
  by (simp add: exec_label_preserves_history_wf_def history_can_append_def
                s2_def s1_def s0_def initial_exec_state_def ec_defs)

lemma wf_s3: "wellformed_exec_state s3"
  by (rule dw_exec_step_wellformed_exec_state[OF st23 wf_s2 pres_s2_down1])

lemma pres_s3_crash1: "exec_label_preserves_history_wf s3 (Crash ec1)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma pres_s3_do2: "exec_label_preserves_history_wf s3 (DoSource ec2 ev2)"
  by (simp add: exec_label_preserves_history_wf_def history_can_append_def
                s3_def s2_def s1_def s0_def initial_exec_state_def ec_defs)

lemma wf_s4: "wellformed_exec_state s4"
  by (rule dw_exec_step_wellformed_exec_state[OF st34 wf_s3 pres_s3_do2])

lemma pres_s4_enq2: "exec_label_preserves_history_wf s4 (EnqueueDownstream ec2 ev2)"
  by (simp add: exec_label_preserves_history_wf_def history_can_append_def
                s4_def s3_def s2_def s1_def s0_def initial_exec_state_def ec_defs)

lemma wf_s5: "wellformed_exec_state s5"
  by (rule dw_exec_step_wellformed_exec_state[OF st45 wf_s4 pres_s4_enq2])

lemma pres_s5_crash2: "exec_label_preserves_history_wf s5 (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma pres_s1_enq2: "exec_label_preserves_history_wf s1 (EnqueueDownstream ec2 ev2)"
  by (simp add: exec_label_preserves_history_wf_def history_can_append_def
                s1_def s0_def initial_exec_state_def ec_defs)

lemma wf_u2: "wellformed_exec_state u2"
  by (rule dw_exec_step_wellformed_exec_state[OF stu12 wf_s1 pres_s1_enq2])

lemma pres_u2_down2: "exec_label_preserves_history_wf u2 (DoDownstream ec2 ev2)"
  by (simp add: exec_label_preserves_history_wf_def history_can_append_def
                u2_def s1_def s0_def initial_exec_state_def ec_defs)

lemma wf_u3: "wellformed_exec_state u3"
  by (rule dw_exec_step_wellformed_exec_state[OF stu23 wf_u2 pres_u2_down2])

lemma pres_u3_crash2: "exec_label_preserves_history_wf u3 (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma pres_s0_enq1: "exec_label_preserves_history_wf s0 (EnqueueDownstream ec1 ev1)"
  by (simp add: exec_label_preserves_history_wf_def history_can_append_def
                s0_def initial_exec_state_def ec_defs)

lemma wf_b1: "wellformed_exec_state b1"
  by (rule dw_exec_step_wellformed_exec_state[OF stb01 wf_s0 pres_s0_enq1])

lemma pres_b1_down1: "exec_label_preserves_history_wf b1 (DoDownstream ec1 ev1)"
  by (simp add: exec_label_preserves_history_wf_def history_can_append_def
                b1_def s0_def initial_exec_state_def ec_defs)

section \<open>Effect-tier states\<close>

definition t0 :: "(nat, nat) dwe_state" where
  "t0 = dwe_init Map.empty {0, 1} ec2"

definition t1 :: "(nat, nat) dwe_state" where
  "t1 = \<lparr>dwe_core = s1, dwe_emitted = []\<rparr>"

definition t2 :: "(nat, nat) dwe_state" where
  "t2 = \<lparr>dwe_core = s2, dwe_emitted = []\<rparr>"

definition t3 :: "(nat, nat) dwe_state" where
  "t3 = \<lparr>dwe_core = s3, dwe_emitted = [(1, ec1, ev1)]\<rparr>"

definition t3c :: "(nat, nat) dwe_state" where
  "t3c = \<lparr>dwe_core = s3c, dwe_emitted = [(1, ec1, ev1)]\<rparr>"

definition tG1_dup :: "(nat, nat) dwe_state" where
  "tG1_dup = \<lparr>dwe_core = s3r, dwe_emitted = [(1, ec1, ev1), (1, ec1, ev1)]\<rparr>"

definition tG1_safe :: "(nat, nat) dwe_state" where
  "tG1_safe = \<lparr>dwe_core = s3r, dwe_emitted = [(1, ec1, ev1)]\<rparr>"

definition t4 :: "(nat, nat) dwe_state" where
  "t4 = \<lparr>dwe_core = s4, dwe_emitted = [(1, ec1, ev1)]\<rparr>"

definition t5 :: "(nat, nat) dwe_state" where
  "t5 = \<lparr>dwe_core = s5, dwe_emitted = [(1, ec1, ev1)]\<rparr>"

definition t_mid :: "(nat, nat) dwe_state" where
  "t_mid = \<lparr>dwe_core = s6, dwe_emitted = [(1, ec1, ev1)]\<rparr>"

definition t_fin :: "(nat, nat) dwe_state" where
  "t_fin = \<lparr>dwe_core = s6r,
            dwe_emitted = [(1, ec1, ev1), (2, ec1, ev1), (2, ec2, ev2)]\<rparr>"

definition t_safe :: "(nat, nat) dwe_state" where
  "t_safe = \<lparr>dwe_core = s6r, dwe_emitted = [(1, ec1, ev1), (2, ec2, ev2)]\<rparr>"

definition v2 :: "(nat, nat) dwe_state" where
  "v2 = \<lparr>dwe_core = u2, dwe_emitted = []\<rparr>"

definition v3 :: "(nat, nat) dwe_state" where
  "v3 = \<lparr>dwe_core = u3, dwe_emitted = [(1, ec2, ev2)]\<rparr>"

definition v4 :: "(nat, nat) dwe_state" where
  "v4 = \<lparr>dwe_core = u4, dwe_emitted = [(1, ec2, ev2)]\<rparr>"

definition w1 :: "(nat, nat) dwe_state" where
  "w1 = \<lparr>dwe_core = b1, dwe_emitted = []\<rparr>"

definition t_bad :: "(nat, nat) dwe_state" where
  "t_bad = \<lparr>dwe_core = b2, dwe_emitted = [(0, ec1, ev1)]\<rparr>"

lemma core_projections [simp]:
  "dwe_core t0 = s0" "dwe_core t1 = s1" "dwe_core t2 = s2"
  "dwe_core t3 = s3" "dwe_core t3c = s3c"
  "dwe_core tG1_dup = s3r" "dwe_core tG1_safe = s3r"
  "dwe_core t4 = s4" "dwe_core t5 = s5" "dwe_core t_mid = s6"
  "dwe_core t_fin = s6r" "dwe_core t_safe = s6r"
  "dwe_core v2 = u2" "dwe_core v3 = u3" "dwe_core v4 = u4"
  "dwe_core w1 = b1" "dwe_core t_bad = b2"
  by (simp_all add: t0_def dwe_init_def s0_def t1_def t2_def t3_def t3c_def
                    tG1_dup_def tG1_safe_def t4_def t5_def t_mid_def t_fin_def
                    t_safe_def v2_def v3_def v4_def w1_def t_bad_def)

section \<open>Effect-tier steps\<close>

lemma dst01: "dwe_step t0 (DoSource ec1 ev1) t1"
proof (rule dwe_step_lift_nonpubI)
  show "dw_exec_step (dwe_core t0) (DoSource ec1 ev1) s1"
    using st01 by simp
  show "\<forall>c e. DoSource ec1 ev1 \<noteq> DoDownstream c e" by simp
  show "t1 = \<lparr>dwe_core = s1, dwe_emitted = dwe_emitted t0\<rparr>"
    by (simp add: t1_def t0_def dwe_init_def)
qed

lemma dst12: "dwe_step t1 (EnqueueDownstream ec1 ev1) t2"
proof (rule dwe_step_lift_nonpubI)
  show "dw_exec_step (dwe_core t1) (EnqueueDownstream ec1 ev1) s2"
    using st12 by simp
  show "\<forall>c e. EnqueueDownstream ec1 ev1 \<noteq> DoDownstream c e" by simp
  show "t2 = \<lparr>dwe_core = s2, dwe_emitted = dwe_emitted t1\<rparr>"
    by (simp add: t2_def t1_def)
qed

lemma dst23: "dwe_step t2 (DoDownstream ec1 ev1) t3"
proof (rule dwe_step_publishI)
  show "dw_exec_step (dwe_core t2) (DoDownstream ec1 ev1) s3"
    using st23 by simp
  show "t3 = \<lparr>dwe_core = s3,
              dwe_emitted = dwe_emitted t2
                @ [(length (exec_src_hist (dwe_core t2)), ec1, ev1)]\<rparr>"
    by (simp add: t3_def t2_def s2_def s1_def s0_def initial_exec_state_def)
qed

lemma dst3c: "dwe_step t3 (Crash ec1) t3c"
proof (rule dwe_step_lift_nonpubI)
  show "dw_exec_step (dwe_core t3) (Crash ec1) s3c"
    using st3c by simp
  show "\<forall>c e. Crash ec1 \<noteq> DoDownstream c e" by simp
  show "t3c = \<lparr>dwe_core = s3c, dwe_emitted = dwe_emitted t3\<rparr>"
    by (simp add: t3c_def t3_def)
qed

lemma dst34: "dwe_step t3 (DoSource ec2 ev2) t4"
proof (rule dwe_step_lift_nonpubI)
  show "dw_exec_step (dwe_core t3) (DoSource ec2 ev2) s4"
    using st34 by simp
  show "\<forall>c e. DoSource ec2 ev2 \<noteq> DoDownstream c e" by simp
  show "t4 = \<lparr>dwe_core = s4, dwe_emitted = dwe_emitted t3\<rparr>"
    by (simp add: t4_def t3_def)
qed

lemma dst45: "dwe_step t4 (EnqueueDownstream ec2 ev2) t5"
proof (rule dwe_step_lift_nonpubI)
  show "dw_exec_step (dwe_core t4) (EnqueueDownstream ec2 ev2) s5"
    using st45 by simp
  show "\<forall>c e. EnqueueDownstream ec2 ev2 \<noteq> DoDownstream c e" by simp
  show "t5 = \<lparr>dwe_core = s5, dwe_emitted = dwe_emitted t4\<rparr>"
    by (simp add: t5_def t4_def)
qed

lemma dst56: "dwe_step t5 (Crash ec2) t_mid"
proof (rule dwe_step_lift_nonpubI)
  show "dw_exec_step (dwe_core t5) (Crash ec2) s6"
    using st56 by simp
  show "\<forall>c e. Crash ec2 \<noteq> DoDownstream c e" by simp
  show "t_mid = \<lparr>dwe_core = s6, dwe_emitted = dwe_emitted t5\<rparr>"
    by (simp add: t_mid_def t5_def)
qed

lemma dstu1: "dwe_step t1 (EnqueueDownstream ec2 ev2) v2"
proof (rule dwe_step_lift_nonpubI)
  show "dw_exec_step (dwe_core t1) (EnqueueDownstream ec2 ev2) u2"
    using stu12 by simp
  show "\<forall>c e. EnqueueDownstream ec2 ev2 \<noteq> DoDownstream c e" by simp
  show "v2 = \<lparr>dwe_core = u2, dwe_emitted = dwe_emitted t1\<rparr>"
    by (simp add: v2_def t1_def)
qed

lemma dstu2: "dwe_step v2 (DoDownstream ec2 ev2) v3"
proof (rule dwe_step_publishI)
  show "dw_exec_step (dwe_core v2) (DoDownstream ec2 ev2) u3"
    using stu23 by simp
  show "v3 = \<lparr>dwe_core = u3,
              dwe_emitted = dwe_emitted v2
                @ [(length (exec_src_hist (dwe_core v2)), ec2, ev2)]\<rparr>"
    by (simp add: v3_def v2_def u2_def s1_def s0_def initial_exec_state_def)
qed

lemma dstu3: "dwe_step v3 (Crash ec2) v4"
proof (rule dwe_step_lift_nonpubI)
  show "dw_exec_step (dwe_core v3) (Crash ec2) u4"
    using stu34 by simp
  show "\<forall>c e. Crash ec2 \<noteq> DoDownstream c e" by simp
  show "v4 = \<lparr>dwe_core = u4, dwe_emitted = dwe_emitted v3\<rparr>"
    by (simp add: v4_def v3_def)
qed

lemma dstb0: "dwe_step t0 (EnqueueDownstream ec1 ev1) w1"
proof (rule dwe_step_lift_nonpubI)
  show "dw_exec_step (dwe_core t0) (EnqueueDownstream ec1 ev1) b1"
    using stb01 by simp
  show "\<forall>c e. EnqueueDownstream ec1 ev1 \<noteq> DoDownstream c e" by simp
  show "w1 = \<lparr>dwe_core = b1, dwe_emitted = dwe_emitted t0\<rparr>"
    by (simp add: w1_def t0_def dwe_init_def)
qed

lemma dstb1: "dwe_step w1 (DoDownstream ec1 ev1) t_bad"
proof (rule dwe_step_publishI)
  show "dw_exec_step (dwe_core w1) (DoDownstream ec1 ev1) b2"
    using stb12 by simp
  show "t_bad = \<lparr>dwe_core = b2,
                 dwe_emitted = dwe_emitted w1
                   @ [(length (exec_src_hist (dwe_core w1)), ec1, ev1)]\<rparr>"
    by (simp add: t_bad_def w1_def b1_def s0_def initial_exec_state_def)
qed

section \<open>The four emitting reconciles\<close>

lemmas eval_arith = One_nat_def numeral_eq_Suc

lemma rec_dup: "emitting_reconcile 0 t3c ec1 tG1_dup"
  by (simp add: emitting_reconcile_def t3c_def tG1_dup_def s3r_def s3c_def
                s3_def s2_def s1_def s0_def initial_exec_state_def
                replay_down_hist_def ev1_def ec_defs eval_arith)

lemma rec_safe1: "emitting_reconcile 1 t3c ec1 tG1_safe"
  by (simp add: emitting_reconcile_def t3c_def tG1_safe_def s3r_def s3c_def
                s3_def s2_def s1_def s0_def initial_exec_state_def
                replay_down_hist_def ev1_def ec_defs eval_arith)

lemma rec_fin: "emitting_reconcile 0 t_mid ec2 t_fin"
  by (simp add: emitting_reconcile_def t_mid_def t_fin_def s6r_def s6_def
                s5_def s4_def s3_def s2_def s1_def s0_def initial_exec_state_def
                replay_down_hist_def ev1_def ev2_def ec_defs eval_arith)

lemma rec_tsafe: "emitting_reconcile 1 t_mid ec2 t_safe"
  by (simp add: emitting_reconcile_def t_mid_def t_safe_def s6r_def s6_def
                s5_def s4_def s3_def s2_def s1_def s0_def initial_exec_state_def
                replay_down_hist_def ev1_def ev2_def ec_defs eval_arith)

section \<open>Temporal traces and reachability\<close>

lemma sg01: "dwe_temporal_trace t0 [DWE_Label (DoSource ec1 ev1)] t1"
  by (rule dwe_temporal_singleI[OF dst01]) (simp_all add: wf_s0 pres_s0_do1)

lemma sg12: "dwe_temporal_trace t1 [DWE_Label (EnqueueDownstream ec1 ev1)] t2"
  by (rule dwe_temporal_singleI[OF dst12]) (simp_all add: wf_s1 pres_s1_enq1)

lemma sg23: "dwe_temporal_trace t2 [DWE_Label (DoDownstream ec1 ev1)] t3"
  by (rule dwe_temporal_singleI[OF dst23]) (simp_all add: wf_s2 pres_s2_down1)

lemma sg3c: "dwe_temporal_trace t3 [DWE_Label (Crash ec1)] t3c"
  by (rule dwe_temporal_singleI[OF dst3c]) (simp_all add: wf_s3 pres_s3_crash1)

lemma sg34: "dwe_temporal_trace t3 [DWE_Label (DoSource ec2 ev2)] t4"
  by (rule dwe_temporal_singleI[OF dst34]) (simp_all add: wf_s3 pres_s3_do2)

lemma sg45: "dwe_temporal_trace t4 [DWE_Label (EnqueueDownstream ec2 ev2)] t5"
  by (rule dwe_temporal_singleI[OF dst45]) (simp_all add: wf_s4 pres_s4_enq2)

lemma sg56: "dwe_temporal_trace t5 [DWE_Label (Crash ec2)] t_mid"
  by (rule dwe_temporal_singleI[OF dst56]) (simp_all add: wf_s5 pres_s5_crash2)

lemma sgu1: "dwe_temporal_trace t1 [DWE_Label (EnqueueDownstream ec2 ev2)] v2"
  by (rule dwe_temporal_singleI[OF dstu1]) (simp_all add: wf_s1 pres_s1_enq2)

lemma sgu2: "dwe_temporal_trace v2 [DWE_Label (DoDownstream ec2 ev2)] v3"
  by (rule dwe_temporal_singleI[OF dstu2]) (simp_all add: wf_u2 pres_u2_down2)

lemma sgu3: "dwe_temporal_trace v3 [DWE_Label (Crash ec2)] v4"
  by (rule dwe_temporal_singleI[OF dstu3]) (simp_all add: wf_u3 pres_u3_crash2)

lemma sgb0: "dwe_temporal_trace t0 [DWE_Label (EnqueueDownstream ec1 ev1)] w1"
  by (rule dwe_temporal_singleI[OF dstb0]) (simp_all add: wf_s0 pres_s0_enq1)

lemma sgb1: "dwe_temporal_trace w1 [DWE_Label (DoDownstream ec1 ev1)] t_bad"
  by (rule dwe_temporal_singleI[OF dstb1]) (simp_all add: wf_b1 pres_b1_down1)

lemma trace_t0_t3:
  "dwe_temporal_trace t0
     (map DWE_Label
        [DoSource ec1 ev1, EnqueueDownstream ec1 ev1, DoDownstream ec1 ev1])
     t3"
  using dwe_temporal_trace_append[OF sg01 dwe_temporal_trace_append[OF sg12 sg23]]
  by simp

lemma trace_t0_t3c:
  "dwe_temporal_trace t0
     (map DWE_Label
        [DoSource ec1 ev1, EnqueueDownstream ec1 ev1, DoDownstream ec1 ev1,
         Crash ec1])
     t3c"
  using dwe_temporal_trace_append[OF trace_t0_t3 sg3c] by simp

definition loaded_window :: "(nat, nat) dw_exec_label list" where
  "loaded_window =
     [DoSource ec1 ev1, EnqueueDownstream ec1 ev1, DoDownstream ec1 ev1,
      DoSource ec2 ev2, EnqueueDownstream ec2 ev2, Crash ec2]"

lemma trace_t0_t_mid:
  "dwe_temporal_trace t0 (map DWE_Label loaded_window) t_mid"
  using dwe_temporal_trace_append
          [OF trace_t0_t3
              dwe_temporal_trace_append
                [OF sg34 dwe_temporal_trace_append[OF sg45 sg56]]]
  by (simp add: loaded_window_def)

lemma trace_t0_v4:
  "dwe_temporal_trace t0
     (map DWE_Label
        [DoSource ec1 ev1, EnqueueDownstream ec2 ev2, DoDownstream ec2 ev2,
         Crash ec2])
     v4"
  using dwe_temporal_trace_append
          [OF sg01 dwe_temporal_trace_append
                     [OF sgu1 dwe_temporal_trace_append[OF sgu2 sgu3]]]
  by simp

lemma trace_t0_t_bad:
  "dwe_temporal_trace t0
     (map DWE_Label [EnqueueDownstream ec1 ev1, DoDownstream ec1 ev1])
     t_bad"
  using dwe_temporal_trace_append[OF sgb0 sgb1] by simp

lemma reach_t0: "dwe_reachable Map.empty {0, 1} ec2 t0"
  unfolding t0_def by (rule dwe_reachable_init)

lemma reach_t3c: "dwe_reachable Map.empty {0, 1} ec2 t3c"
  by (rule dwe_reachable_trace_extend[OF reach_t0 trace_t0_t3c])

lemma reach_tG1_dup: "dwe_reachable Map.empty {0, 1} ec2 tG1_dup"
  by (rule dwe_reachable_trace_extend
      [OF reach_t3c dwe_temporal_reconcile_singleI[OF rec_dup]])

lemma reach_tG1_safe: "dwe_reachable Map.empty {0, 1} ec2 tG1_safe"
  by (rule dwe_reachable_trace_extend
      [OF reach_t3c dwe_temporal_reconcile_singleI[OF rec_safe1]])

lemma reach_t_mid: "dwe_reachable Map.empty {0, 1} ec2 t_mid"
  by (rule dwe_reachable_trace_extend[OF reach_t0 trace_t0_t_mid])

lemma reach_t_fin: "dwe_reachable Map.empty {0, 1} ec2 t_fin"
  by (rule dwe_reachable_trace_extend
      [OF reach_t_mid dwe_temporal_reconcile_singleI[OF rec_fin]])

lemma reach_t_safe: "dwe_reachable Map.empty {0, 1} ec2 t_safe"
  by (rule dwe_reachable_trace_extend
      [OF reach_t_mid dwe_temporal_reconcile_singleI[OF rec_tsafe]])

lemma reach_v4: "dwe_reachable Map.empty {0, 1} ec2 v4"
  by (rule dwe_reachable_trace_extend[OF reach_t0 trace_t0_v4])

lemma reach_t_bad: "dwe_reachable Map.empty {0, 1} ec2 t_bad"
  by (rule dwe_reachable_trace_extend[OF reach_t0 trace_t0_t_bad])

section \<open>Verdict and image evaluations\<close>

lemma cores_equal_G1: "dwe_core tG1_dup = dwe_core tG1_safe"
  by (simp add: tG1_dup_def tG1_safe_def)

lemma unsafe_tG1_dup: "effect_unsafe tG1_dup"
  by (simp add: effect_unsafe_def duplicate_def tG1_dup_def)

lemma safe_tG1_safe: "\<not> effect_unsafe tG1_safe"
  by (simp add: effect_unsafe_def premature_def duplicate_def justified_at_def
                tG1_safe_def s3r_def s3c_def s3_def s2_def s1_def s0_def
                initial_exec_state_def eval_arith)

lemma obs_mismatch_t_mid: "observable_mismatch (dwe_core t_mid) ec2 1"
proof (rule observable_mismatchI)
  show "exec_status (dwe_core t_mid) = Crashed ec2"
    by (simp add: s6_def s5_def s4_def s3_def s2_def s1_def s0_def
                  initial_exec_state_def)
  show "ec2 \<le> exec_finish (dwe_core t_mid)"
    by (simp add: s6_def s5_def s4_def s3_def s2_def s1_def s0_def
                  initial_exec_state_def)
  show "(1 :: nat) \<in> exec_scope (dwe_core t_mid)"
    by (simp add: s6_def s5_def s4_def s3_def s2_def s1_def s0_def
                  initial_exec_state_def)
  show "Src (exec_base (dwe_core t_mid)) (exec_down_hist (dwe_core t_mid)) ec2 1
        \<noteq> Src (exec_base (dwe_core t_mid)) (exec_src_hist (dwe_core t_mid)) ec2 1"
    by (simp add: s6_def s5_def s4_def s3_def s2_def s1_def s0_def
                  initial_exec_state_def Src_def latest_src_event_def Let_def
                  ev1_def ev2_def ec_defs)
qed

lemma not_P_img_t_mid: "\<not> P_img t_mid ec2"
  using obs_mismatch_t_mid
  by (auto simp: P_img_def observable_mismatch_def)

lemma safe_t_mid: "\<not> effect_unsafe t_mid"
  by (simp add: effect_unsafe_def premature_def duplicate_def justified_at_def
                t_mid_def s6_def s5_def s4_def s3_def s2_def s1_def s0_def
                initial_exec_state_def eval_arith)

lemma heal_t_fin:
  "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t_fin) ec2) ec2 k"
  by (rule emitting_reconcile_heals[OF rec_fin])

lemma P_img_t_fin: "P_img t_fin ec2"
  using heal_t_fin by (simp add: P_img_def)

lemma heal_t_safe:
  "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t_safe) ec2) ec2 k"
  by (rule emitting_reconcile_heals[OF rec_tsafe])

lemma P_img_t_safe: "P_img t_safe ec2"
  using heal_t_safe by (simp add: P_img_def)

lemma unsafe_t_fin: "effect_unsafe t_fin"
  by (simp add: effect_unsafe_def duplicate_def t_fin_def)

lemma count_t_fin:
  "2 \<le> count_list (map e_payload (dwe_emitted t_fin)) (ec1, ev1)"
  by (simp add: t_fin_def ev1_def ev2_def ec_defs eval_arith)

lemma justified_t_fin:
  "\<forall>x \<in> set (dwe_emitted t_fin).
     justified_at (exec_src_hist (dwe_core t_fin)) x"
  by (simp add: justified_at_def t_fin_def s6r_def s6_def s5_def s4_def s3_def
                s2_def s1_def s0_def initial_exec_state_def eval_arith)

lemma emitted_t_safe: "dwe_emitted t_safe = [(1, ec1, ev1), (2, ec2, ev2)]"
  by (simp add: t_safe_def)

lemma safe_t_safe: "\<not> effect_unsafe t_safe"
  by (simp add: effect_unsafe_def premature_def duplicate_def justified_at_def
                t_safe_def s6r_def s6_def s5_def s4_def s3_def s2_def s1_def
                s0_def initial_exec_state_def ev1_def ev2_def ec_defs eval_arith)

lemma mismatch_v4: "mismatch_at (proto_of_exec_at (dwe_core v4) ec2) ec2 1"
  by (simp add: mismatch_at_def proto_of_exec_at_def store2_of_exec_def
                log_image_def restrict_def u4_def u3_def u2_def s1_def s0_def
                initial_exec_state_def Src_def latest_src_event_def Let_def
                ev1_def ev2_def ec_defs)

lemma not_P_img_v4: "\<not> P_img v4 ec2"
  using mismatch_v4 by (auto simp: P_img_def)

lemma unsafe_v4: "effect_unsafe v4"
  by (simp add: effect_unsafe_def premature_def justified_at_def v4_def u4_def
                u3_def u2_def s1_def s0_def initial_exec_state_def
                ev1_def ev2_def ec_defs eval_arith)

lemma nonempty_t_bad: "dwe_emitted t_bad \<noteq> []"
  by (simp add: t_bad_def)

lemma premature_t_bad: "premature t_bad"
  by (simp add: premature_def justified_at_def t_bad_def b2_def b1_def s0_def
                initial_exec_state_def)

lemma phantom_t_bad: "phantom t_bad"
  by (simp add: phantom_def t_bad_def b2_def b1_def s0_def
                initial_exec_state_def)

lemma emitting_tG1_dup: "genuinely_emitting tG1_dup"
  by (simp add: genuinely_emitting_def tG1_dup_def)

lemma emitting_tG1_safe: "genuinely_emitting tG1_safe"
  by (simp add: genuinely_emitting_def tG1_safe_def)

lemma emitting_t_mid: "genuinely_emitting t_mid"
  by (simp add: genuinely_emitting_def t_mid_def)

lemma emitting_t_fin: "genuinely_emitting t_fin"
  by (simp add: genuinely_emitting_def t_fin_def)

lemma emitting_t_safe: "genuinely_emitting t_safe"
  by (simp add: genuinely_emitting_def t_safe_def)

lemma emitting_v4: "genuinely_emitting v4"
  by (simp add: genuinely_emitting_def v4_def)

section \<open>G1: duplicate separation --- the effect verdict escapes the core (and the image)\<close>

theorem dwe_duplicate_separation:
  "\<exists>t t'. dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 t
        \<and> dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 t'
        \<and> dwe_core t = dwe_core t'
        \<and> effect_unsafe t
        \<and> \<not> effect_unsafe t'"
proof -
  have "dwe_reachable Map.empty {0, 1} ec2 tG1_dup
      \<and> dwe_reachable Map.empty {0, 1} ec2 tG1_safe
      \<and> dwe_core tG1_dup = dwe_core tG1_safe
      \<and> effect_unsafe tG1_dup
      \<and> \<not> effect_unsafe tG1_safe"
    using reach_tG1_dup reach_tG1_safe cores_equal_G1
          unsafe_tG1_dup safe_tG1_safe
    by blast
  then show ?thesis by blast
qed

text \<open>
  Corollary: NO function of the core state (a fortiori none of the scoped
  image, which is itself a function of the core) computes the effect verdict
  on reachable states --- the machine-level negation of the image wall
  (\<open>observable_mismatch_depends_only_on_down_image\<close>) for the effect tier.
\<close>

theorem effect_unsafe_not_core_function:
  "\<not> (\<exists>g. \<forall>t. dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 t
              \<longrightarrow> (effect_unsafe t \<longleftrightarrow> g (dwe_core t)))"
proof
  assume "\<exists>g. \<forall>t. dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 t
                  \<longrightarrow> (effect_unsafe t \<longleftrightarrow> g (dwe_core t))"
  then obtain g where
    g: "\<forall>t. dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 t
            \<longrightarrow> (effect_unsafe t \<longleftrightarrow> g (dwe_core t))" ..
  have "g (dwe_core tG1_dup)"
    using g reach_tG1_dup unsafe_tG1_dup by blast
  moreover have "\<not> g (dwe_core tG1_safe)"
    using g reach_tG1_safe safe_tG1_safe by blast
  ultimately show False
    using cores_equal_G1 by simp
qed

theorem effect_unsafe_not_image_function:
  "\<not> (\<exists>h. \<forall>t. dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 t
              \<longrightarrow> (effect_unsafe t \<longleftrightarrow> h (proto_of_exec_at (dwe_core t))))"
proof
  assume "\<exists>h. \<forall>t. dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 t
                  \<longrightarrow> (effect_unsafe t \<longleftrightarrow> h (proto_of_exec_at (dwe_core t)))"
  then obtain h where
    h: "\<forall>t. dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 t
            \<longrightarrow> (effect_unsafe t \<longleftrightarrow> h (proto_of_exec_at (dwe_core t)))" ..
  have "h (proto_of_exec_at (dwe_core tG1_dup))"
    using h reach_tG1_dup unsafe_tG1_dup by blast
  moreover have "\<not> h (proto_of_exec_at (dwe_core tG1_safe))"
    using h reach_tG1_safe safe_tG1_safe by blast
  ultimately show False
    using cores_equal_G1 by simp
qed

section \<open>G2: THE kill-or-continue gate --- crash, heal, re-emit\<close>

theorem crash_heal_reemit_bridge:
  "\<exists>tm tf.
     dwe_temporal_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
       (map DWE_Label loaded_window) tm
   \<and> observable_mismatch (dwe_core tm) ec2 1
   \<and> emitting_reconcile 0 tm ec2 tf
   \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core tf) ec2) ec2 k)
   \<and> 2 \<le> count_list (map e_payload (dwe_emitted tf)) (ec1, ev1)
   \<and> (\<forall>x \<in> set (dwe_emitted tf).
        justified_at (exec_src_hist (dwe_core tf)) x)"
proof -
  have trace: "dwe_temporal_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
                 (map DWE_Label loaded_window) t_mid"
    using trace_t0_t_mid unfolding t0_def .
  have all: "dwe_temporal_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
               (map DWE_Label loaded_window) t_mid
           \<and> observable_mismatch (dwe_core t_mid) ec2 1
           \<and> emitting_reconcile 0 t_mid ec2 t_fin
           \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t_fin) ec2) ec2 k)
           \<and> 2 \<le> count_list (map e_payload (dwe_emitted t_fin)) (ec1, ev1)
           \<and> (\<forall>x \<in> set (dwe_emitted t_fin).
                justified_at (exec_src_hist (dwe_core t_fin)) x)"
    using trace obs_mismatch_t_mid rec_fin heal_t_fin count_t_fin
          justified_t_fin
    by blast
  then show ?thesis by blast
qed

section \<open>G3: non-vacuity pair\<close>

theorem effect_nonvacuity_safe:
  "emitting_reconcile 1 t_mid ec2 t_safe
 \<and> dwe_emitted t_safe = [(1, ec1, ev1), (2, ec2, ev2)]
 \<and> \<not> effect_unsafe t_safe
 \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t_safe) ec2) ec2 k)"
  using rec_tsafe emitted_t_safe safe_t_safe heal_t_safe by blast

corollary t_safe_emitting_and_reachable:
  "genuinely_emitting t_safe
 \<and> dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 t_safe"
  using emitting_t_safe reach_t_safe by blast

text \<open>
  The checkpoint is the ONLY difference: from the SAME crashed mid-state, the
  two reconciles (stale cursor m = 0 vs current cursor m = 1) produce states
  with the SAME core --- both heal the store --- and opposite effect
  verdicts.  A second duplicate-separation instance, at the loaded window.
\<close>

corollary checkpoint_is_the_only_difference:
  "emitting_reconcile 0 t_mid ec2 t_fin
 \<and> emitting_reconcile 1 t_mid ec2 t_safe
 \<and> dwe_core t_fin = dwe_core t_safe
 \<and> effect_unsafe t_fin
 \<and> \<not> effect_unsafe t_safe"
  using rec_fin rec_tsafe unsafe_t_fin safe_t_safe
  by (simp add: t_fin_def t_safe_def)

theorem effect_nonvacuity_bad:
  "\<exists>tb. dwe_temporal_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
          (map DWE_Label [EnqueueDownstream ec1 ev1, DoDownstream ec1 ev1]) tb
      \<and> dwe_emitted tb \<noteq> []
      \<and> premature tb
      \<and> phantom tb"
proof -
  have trace: "dwe_temporal_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
                 (map DWE_Label [EnqueueDownstream ec1 ev1, DoDownstream ec1 ev1])
                 t_bad"
    using trace_t0_t_bad unfolding t0_def .
  then show ?thesis
    using nonempty_t_bad premature_t_bad phantom_t_bad by blast
qed

section \<open>G4 (stretch): four-corner independence at frontier ec2\<close>

theorem four_corner_independence:
  "\<exists>tPS tPU tNS tNU.
     dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 tPS
       \<and> genuinely_emitting tPS \<and> P_img tPS ec2 \<and> \<not> effect_unsafe tPS
   \<and> dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 tPU
       \<and> genuinely_emitting tPU \<and> P_img tPU ec2 \<and> effect_unsafe tPU
   \<and> dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 tNS
       \<and> genuinely_emitting tNS \<and> \<not> P_img tNS ec2 \<and> \<not> effect_unsafe tNS
   \<and> dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 tNU
       \<and> genuinely_emitting tNU \<and> \<not> P_img tNU ec2 \<and> effect_unsafe tNU"
proof -
  have all:
    "dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 t_safe
       \<and> genuinely_emitting t_safe \<and> P_img t_safe ec2 \<and> \<not> effect_unsafe t_safe
   \<and> dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 t_fin
       \<and> genuinely_emitting t_fin \<and> P_img t_fin ec2 \<and> effect_unsafe t_fin
   \<and> dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 t_mid
       \<and> genuinely_emitting t_mid \<and> \<not> P_img t_mid ec2 \<and> \<not> effect_unsafe t_mid
   \<and> dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 v4
       \<and> genuinely_emitting v4 \<and> \<not> P_img v4 ec2 \<and> effect_unsafe v4"
    using reach_t_safe emitting_t_safe P_img_t_safe safe_t_safe
          reach_t_fin emitting_t_fin P_img_t_fin unsafe_t_fin
          reach_t_mid emitting_t_mid not_P_img_t_mid safe_t_mid
          reach_v4 emitting_v4 not_P_img_v4 unsafe_v4
    by blast
  then show ?thesis by blast
qed

section \<open>T2.7: the core-invisible premature pair --- both effect hazards escape the image\<close>

text \<open>
  The safe three-step window commits the source first and then delivers ---
  @{term "[DoSource ec1 ev1, EnqueueDownstream ec1 ev1, DoDownstream ec1 ev1]"}
  reaches @{const t3}.  Reordering the SAME three labels so the delivery
  precedes the source commit ---
  @{term "[EnqueueDownstream ec1 ev1, DoDownstream ec1 ev1, DoSource ec1 ev1]"}
  --- reaches a state whose final core is LITERALLY EQUAL to @{const t3}'s:
  the late commit lands in the source history either way, and no core field
  records WHEN the publish fired relative to it.  The ledger does: the
  reordered run's emission carries stamp 0 (nothing was committed when it
  fired), is unjustified at fire time, and
  @{thm [source] justified_at_append_stable} freezes that verdict through
  the late commit --- the commit un-phantoms the emission (@{const phantom}
  is taxonomy-only and non-monotone) but cannot un-premature it.

  This closes a referee gap the duplicate separation (G1) leaves open: G1's
  unsafe witness is a duplicate, so a referee could truthfully say "only
  DUPLICATES escape the image; every premature witness is image-visible".
  The pair below refutes that: prematurity itself separates two reachable
  states with equal cores.  Together with G1, BOTH effect hazards escape
  the core (and a fortiori the scoped image).
\<close>

definition b3 :: "(nat, nat) dw_exec_state" where
  "b3 = b2\<lparr>exec_src_hist := exec_src_hist b2 @ [(ec1, ev1)]\<rparr>"

definition t_late :: "(nat, nat) dwe_state" where
  "t_late = \<lparr>dwe_core = b3, dwe_emitted = [(0, ec1, ev1)]\<rparr>"

lemma stb23: "dw_exec_step b2 (DoSource ec1 ev1) b3"
  unfolding b3_def
  by (rule dw_exec_step.do_source)
     (simp add: b2_def b1_def s0_def initial_exec_state_def)

lemma wf_b2: "wellformed_exec_state b2"
  by (rule dw_exec_step_wellformed_exec_state[OF stb12 wf_b1 pres_b1_down1])

lemma pres_b2_do1: "exec_label_preserves_history_wf b2 (DoSource ec1 ev1)"
  by (simp add: exec_label_preserves_history_wf_def history_can_append_def
                b2_def b1_def s0_def initial_exec_state_def ec_defs)

lemma dstb2: "dwe_step t_bad (DoSource ec1 ev1) t_late"
proof (rule dwe_step_lift_nonpubI)
  show "dw_exec_step (dwe_core t_bad) (DoSource ec1 ev1) b3"
    using stb23 by simp
  show "\<forall>c e. DoSource ec1 ev1 \<noteq> DoDownstream c e" by simp
  show "t_late = \<lparr>dwe_core = b3, dwe_emitted = dwe_emitted t_bad\<rparr>"
    by (simp add: t_late_def t_bad_def)
qed

lemma sgb2: "dwe_temporal_trace t_bad [DWE_Label (DoSource ec1 ev1)] t_late"
  by (rule dwe_temporal_singleI[OF dstb2]) (simp_all add: wf_b2 pres_b2_do1)

lemma trace_t0_t_late:
  "dwe_temporal_trace t0
     (map DWE_Label
        [EnqueueDownstream ec1 ev1, DoDownstream ec1 ev1, DoSource ec1 ev1])
     t_late"
  using dwe_temporal_trace_append[OF trace_t0_t_bad sgb2] by simp

lemma reach_t_late: "dwe_reachable Map.empty {0, 1} ec2 t_late"
  by (rule dwe_reachable_trace_extend[OF reach_t0 trace_t0_t_late])

lemma reach_t3: "dwe_reachable Map.empty {0, 1} ec2 t3"
  by (rule dwe_reachable_trace_extend[OF reach_t0 trace_t0_t3])

lemma cores_equal_premature_pair: "dwe_core t_late = dwe_core t3"
  by (simp add: t_late_def b3_def b2_def b1_def
                s3_def s2_def s1_def s0_def initial_exec_state_def)

lemma emitting_t_late: "genuinely_emitting t_late"
  by (simp add: genuinely_emitting_def t_late_def)

lemma emitting_t3: "genuinely_emitting t3"
  by (simp add: genuinely_emitting_def t3_def)

lemma premature_t_late: "premature t_late"
  by (simp add: premature_def justified_at_def t_late_def b3_def b2_def b1_def
                s0_def initial_exec_state_def)

lemma unsafe_t_late: "effect_unsafe t_late"
  using premature_t_late by (simp add: effect_unsafe_def)

lemma not_phantom_t_late: "\<not> phantom t_late"
  by (simp add: phantom_def t_late_def b3_def b2_def b1_def
                s0_def initial_exec_state_def)

lemma safe_t3: "\<not> effect_unsafe t3"
  by (simp add: effect_unsafe_def premature_def duplicate_def justified_at_def
                t3_def s3_def s2_def s1_def s0_def initial_exec_state_def
                eval_arith)

lemma not_premature_t3: "\<not> premature t3"
  using safe_t3 by (simp add: effect_unsafe_def)

text \<open>
  The commit un-phantoms the reordered run's emission but cannot
  un-premature it: fire-time justification is frozen by append-stability.
  (@{const t_bad} is the pre-commit state of the SAME run: phantom and
  premature there; after the commit, no longer phantom, still premature.)
\<close>

lemma premature_survives_unphantoming:
  "phantom t_bad \<and> premature t_bad
 \<and> dwe_step t_bad (DoSource ec1 ev1) t_late
 \<and> \<not> phantom t_late \<and> premature t_late"
  using phantom_t_bad premature_t_bad dstb2 not_phantom_t_late
        premature_t_late
  by blast

theorem premature_core_invisible_pair:
  "\<exists>tp ts.
     dwe_temporal_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
       (map DWE_Label
          [EnqueueDownstream ec1 ev1, DoDownstream ec1 ev1, DoSource ec1 ev1])
       tp
   \<and> dwe_temporal_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
       (map DWE_Label
          [DoSource ec1 ev1, EnqueueDownstream ec1 ev1, DoDownstream ec1 ev1])
       ts
   \<and> dwe_core tp = dwe_core ts
   \<and> genuinely_emitting tp \<and> genuinely_emitting ts
   \<and> premature tp \<and> effect_unsafe tp
   \<and> \<not> effect_unsafe ts"
proof -
  have all:
    "dwe_temporal_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
       (map DWE_Label
          [EnqueueDownstream ec1 ev1, DoDownstream ec1 ev1, DoSource ec1 ev1])
       t_late
   \<and> dwe_temporal_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
       (map DWE_Label
          [DoSource ec1 ev1, EnqueueDownstream ec1 ev1, DoDownstream ec1 ev1])
       t3
   \<and> dwe_core t_late = dwe_core t3
   \<and> genuinely_emitting t_late \<and> genuinely_emitting t3
   \<and> premature t_late \<and> effect_unsafe t_late
   \<and> \<not> effect_unsafe t3"
    using trace_t0_t_late[unfolded t0_def] trace_t0_t3[unfolded t0_def]
          cores_equal_premature_pair emitting_t_late emitting_t3
          premature_t_late unsafe_t_late safe_t3
    by blast
  then show ?thesis by blast
qed

text \<open>
  The G1 corollaries, re-proved for @{const premature} alone: no function of
  the core state --- a fortiori none of the scoped image --- computes
  prematurity on reachable states.
\<close>

theorem premature_not_core_function:
  "\<not> (\<exists>g. \<forall>t. dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 t
              \<longrightarrow> (premature t \<longleftrightarrow> g (dwe_core t)))"
proof
  assume "\<exists>g. \<forall>t. dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 t
                  \<longrightarrow> (premature t \<longleftrightarrow> g (dwe_core t))"
  then obtain g where
    g: "\<forall>t. dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 t
            \<longrightarrow> (premature t \<longleftrightarrow> g (dwe_core t))" ..
  have "g (dwe_core t_late)"
    using g reach_t_late premature_t_late by blast
  moreover have "\<not> g (dwe_core t3)"
    using g reach_t3 not_premature_t3 by blast
  ultimately show False
    using cores_equal_premature_pair by simp
qed

theorem premature_not_image_function:
  "\<not> (\<exists>h. \<forall>t. dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 t
              \<longrightarrow> (premature t \<longleftrightarrow> h (proto_of_exec_at (dwe_core t))))"
proof
  assume "\<exists>h. \<forall>t. dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 t
                  \<longrightarrow> (premature t \<longleftrightarrow> h (proto_of_exec_at (dwe_core t)))"
  then obtain h where
    h: "\<forall>t. dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 t
            \<longrightarrow> (premature t \<longleftrightarrow> h (proto_of_exec_at (dwe_core t)))" ..
  have "h (proto_of_exec_at (dwe_core t_late))"
    using h reach_t_late premature_t_late by blast
  moreover have "\<not> h (proto_of_exec_at (dwe_core t3))"
    using h reach_t3 not_premature_t3 by blast
  ultimately show False
    using cores_equal_premature_pair by simp
qed

section \<open>Definition-strength control: the stamp invariant in Gate I(c) is load-bearing\<close>

text \<open>
  On states OUTSIDE the reachable set (an over-shooting stamp), a later
  source commit can retroactively justify an emission --- so the
  monotonicity theorems genuinely need @{const stamps_bounded}, which
  @{thm [source] dwe_reachable_stamps_bounded} discharges on every
  reachable state.  This is a control, not a defect: the machine can never
  fire an emission stamped beyond its own committed history.
\<close>

definition nc_core :: "(nat, nat) dw_exec_state" where
  "nc_core = initial_exec_state Map.empty {0} ec2"

definition nc_t :: "(nat, nat) dwe_state" where
  "nc_t = \<lparr>dwe_core = nc_core, dwe_emitted = [(1, ec1, ev1)]\<rparr>"

definition nc_t' :: "(nat, nat) dwe_state" where
  "nc_t' = \<lparr>dwe_core =
              nc_core\<lparr>exec_src_hist := exec_src_hist nc_core @ [(ec1, ev1)]\<rparr>,
            dwe_emitted = [(1, ec1, ev1)]\<rparr>"

lemma nc_core_step:
  "dw_exec_step nc_core (DoSource ec1 ev1)
     (nc_core\<lparr>exec_src_hist := exec_src_hist nc_core @ [(ec1, ev1)]\<rparr>)"
  by (rule dw_exec_step.do_source) (simp add: nc_core_def initial_exec_state_def)

lemma nc_step: "dwe_step nc_t (DoSource ec1 ev1) nc_t'"
proof (rule dwe_step_lift_nonpubI)
  show "dw_exec_step (dwe_core nc_t) (DoSource ec1 ev1)
          (nc_core\<lparr>exec_src_hist := exec_src_hist nc_core @ [(ec1, ev1)]\<rparr>)"
    using nc_core_step by (simp add: nc_t_def)
  show "\<forall>c e. DoSource ec1 ev1 \<noteq> DoDownstream c e" by simp
  show "nc_t' = \<lparr>dwe_core =
                   nc_core\<lparr>exec_src_hist := exec_src_hist nc_core @ [(ec1, ev1)]\<rparr>,
                 dwe_emitted = dwe_emitted nc_t\<rparr>"
    by (simp add: nc_t'_def nc_t_def)
qed

lemma stamps_premise_load_bearing:
  "\<exists>(t :: (nat, nat) dwe_state) t' a.
     dwe_step t a t'
   \<and> \<not> stamps_bounded t
   \<and> effect_unsafe t
   \<and> \<not> effect_unsafe t'"
proof -
  have not_bounded: "\<not> stamps_bounded nc_t"
    by (simp add: stamps_bounded_def nc_t_def nc_core_def
                  initial_exec_state_def)
  have unsafe: "effect_unsafe nc_t"
    by (simp add: effect_unsafe_def premature_def justified_at_def nc_t_def
                  nc_core_def initial_exec_state_def)
  have safe': "\<not> effect_unsafe nc_t'"
    by (simp add: effect_unsafe_def premature_def duplicate_def
                  justified_at_def nc_t'_def nc_core_def
                  initial_exec_state_def eval_arith)
  show ?thesis
    using nc_step not_bounded unsafe safe' by blast
qed

end
