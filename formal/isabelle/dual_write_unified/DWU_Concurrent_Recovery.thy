(*  Title:       DWU_Concurrent_Recovery.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Purpose: Road-2 I4 --- U9, THE IMPOSSIBILITY HEADLINER of the unified build.

    "There is a crashed dual-write state on which every chooser for the loose
    two-generation arm/heal/fire extension --- each generation free to read the
    entire state, the sink included --- admits a bad completion: both
    generations arm, at least one generation fires, at least one firing
    generation heals, and a generation may fire after the store has been healed
    by its sibling WITHOUT performing its own heal.  The duplicate cell depends
    on that heal-free zombie fire; under full per-generation Arm < Heal < Fire
    ordering the universal-chooser defeat is false at the landed witness."

    The apparatus (u_pair_chooser / u_singleton_owed / the inductive u_pair_steps /
    u_oneshot_pair_extension) is copied VERBATIM from the Stage-4 probe seed section
    1.8.  The two companions (u_pair_steps_bookkeeping, u_oneshot_death_budget) port
    the seed proofs.  The headliner u_concurrent_recovery_dilemma is FRESH work: the
    witness W := rf_W is the structural sibling of U10's floor (DWU_Recovery_Floor),
    and the last conjunct is discharged by the 4-cell schedule taxonomy (case split on
    whether the owed payload appears in the two armed batches).

    The two-horn export u_concurrent_recovery_duplicate_or_lost (section 4)
    restates the headliner with the defeat conjunct sharpened to
    (u_duplicate \/ u_lost): the TT cell's proved duplicate is exported as-is,
    so the quoted "duplicates or loses" above holds at STATEMENT grade.  Same
    witness, same schedules; the landed headliner statement is unchanged.

    Plus one rightness-gated ADDITIVE corollary
    (u_exactly_once_at_completed_claim_instance_exact): the set-level completed-claim
    restated per committed instance under an ascending source.  Under that added
    premise the per-instance conjunct is equivalent to the at-least-once half the
    base theorem already delivers (the proof transports it via
    u_dedup_sink_instance_exact_iff) --- an added-premise restatement, not a
    strengthening.

    R10 ADDENDUM (section 6): the pair grammar above records FINAL SETS only, so
    u_oneshot_pair_extension also admits schedules in which a member fires without
    its own heal (an external review observed this).  Section 6 adds the
    phase-carried grammar (u_pair_steps_phased / u_oneshot_pair_extension_phased),
    proves it simulates the loose grammar, and lands the ordered silent-death
    defeat u_ordered_silent_death_defeat.  It also PROVES the headliner statement
    with the ordered extension substituted for the loose one is FALSE at rf_W
    (u_ordered_dilemma_fails_at_rf_W): one store reconcile per crash caps an
    ordered pair at one completed recovery, so the TT duplicate cell NEEDS the
    sibling's heal-free zombie fire --- the loose bookkeeping is content, not an
    oversight.

    Honesty regime: quick_and_dirty = false (ROOT-pinned), ZERO sorry, ZERO oops,
    no axiomatization, no consts, no oracles.  Every statement is PROVED.
*)

theory DWU_Concurrent_Recovery
  imports DWU_Fenced_Discipline
begin

section \<open>1. The U9 apparatus (P1 kill-gate amended pin, verbatim from seed 1.8)\<close>

type_synonym u_pair_chooser =
  "nat \<Rightarrow> (nat, nat) dwu_state \<Rightarrow> (nat, nat) upayload list"

text \<open>LIVE/retained reading: @{const u_sink_delta} reads retained history + accepted
  (design section 3), the same carriers as @{const u_lost} --- reading-consistent with
  the U9 conclusion's @{const u_lost}.  (@{const u_stamped_batch} is NOT redefined here;
  it is landed in DWU_Machine.)\<close>

definition u_singleton_owed :: "(nat, nat) dwu_state \<Rightarrow> frontier \<Rightarrow> bool" where
  "u_singleton_owed W f \<longleftrightarrow> (\<exists>p. u_sink_delta f W = [p])"

text \<open>The extension = dwu machine reachability from W restricted to actors
  @{text "{g1, g2}"} over @{text "{UArm, UHeal, UFire}"}, with grammar-level
  bookkeeping: A = armed, F = fired, H = healers.  Every step is a machine step.
  The chooser is typed at PAYLOADS and machine-stamped at the arm.\<close>

inductive u_pair_steps ::
  "u_pair_chooser \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> frontier \<Rightarrow> (nat, nat) dwu_state \<Rightarrow>
   nat set \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> (nat, nat) dwu_state \<Rightarrow> bool"
  for D g1 g2 f W
where
  upe_refl:
    "u_pair_steps D g1 g2 f W {} {} {} W"
| upe_arm:
    "\<lbrakk>u_pair_steps D g1 g2 f W A F H t; g \<in> {g1, g2}; g \<notin> A;
      dwu_step t (UArm g (u_stamped_batch (length (dwu_journal t)) g (D g t)) f) t'\<rbrakk>
     \<Longrightarrow> u_pair_steps D g1 g2 f W (insert g A) F H t'"
| upe_heal:
    "\<lbrakk>u_pair_steps D g1 g2 f W A F H t; g \<in> {g1, g2};
      dwu_step t (UHeal g f) t'\<rbrakk>
     \<Longrightarrow> u_pair_steps D g1 g2 f W A F (insert g H) t'"
| upe_fire:
    "\<lbrakk>u_pair_steps D g1 g2 f W A F H t; g \<in> {g1, g2}; g \<in> A; g \<notin> F;
      dwu_step t (UFire g) t'\<rbrakk>
     \<Longrightarrow> u_pair_steps D g1 g2 f W A (insert g F) H t'"

text \<open>BOTH-ARM (final armed set = @{text "{g1, g2}"}); at least one FIRE
  (two-actor equivalent of "at most one silent death"); at least one heal and
  every healer completes (a silent death's ONLY step is its arm).\<close>

definition u_oneshot_pair_extension ::
  "u_pair_chooser \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> frontier \<Rightarrow> (nat, nat) dwu_state
   \<Rightarrow> (nat, nat) dwu_state \<Rightarrow> bool"
where
  "u_oneshot_pair_extension D g1 g2 f W t' \<longleftrightarrow>
     (\<exists>F H. u_pair_steps D g1 g2 f W {g1, g2} F H t'
          \<and> F \<noteq> {}
          \<and> H \<noteq> {} \<and> H \<subseteq> F)"


section \<open>2. Machine-step helpers at the pinned witness (fresh; D-generic)\<close>

text \<open>A generic ARM step: at any Crashed state whose finish covers @{term f} and
  where @{term g} is a live generation, arming the machine-stamped batch of any
  payload list @{term qs} is enabled (the @{text uarm} batch guard holds because
  every stamped element carries gen = g and stamp = LSN).\<close>

lemma u_arm_stamped_step:
  assumes "g \<in> dom (dwu_gens t)"
      and "\<exists>c. exec_status (dwu_store t) = Crashed c"
      and "f \<le> exec_finish (dwu_store t)"
  shows "dwu_step t (UArm g (u_stamped_batch (length (dwu_journal t)) g qs) f)
           (t\<lparr>dwu_gens := (dwu_gens t)(g \<mapsto> UArmed (u_stamped_batch (length (dwu_journal t)) g qs))\<rparr>)"
proof (rule dwu_step.uarm[OF assms])
  show "\<forall>x \<in> set (u_stamped_batch (length (dwu_journal t)) g qs).
          ue_gen x = g \<and> ue_stamp x \<le> length (dwu_journal t)"
    by (auto simp: u_stamped_batch_def)
qed

text \<open>The heal reconcile at the floor's crashed 2-generation store (@{const rf_sto6})
  lands on @{const rf_stoH} --- independent of the healing generation.\<close>

lemma rf_reconcile: "relay_bounded_replay_reconcile rf_sto6 ec2 rf_stoH"
  by (simp add: relay_bounded_replay_reconcile_def rf_sto6_def rf_stoH_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs)

lemma u9_heal_step:
  assumes "dwu_store t = rf_sto6"
  shows "dwu_step t (UHeal g ec2) (t\<lparr>dwu_store := rf_stoH\<rparr>)"
proof -
  have "relay_bounded_replay_reconcile (dwu_store t) ec2 rf_stoH"
    unfolding assms by (rule rf_reconcile)
  from dwu_step.uheal[OF this] show ?thesis .
qed

text \<open>A FIRE step at fence 0: the armed batch is appended to accepted verbatim.\<close>

lemma u9_fire_step0:
  assumes "dwu_gens t g = Some (UArmed B)" and "dwu_fence t = 0"
  shows "dwu_step t (UFire g)
    (t\<lparr>dwu_sent := dwu_sent t @ B,
       dwu_accepted := dwu_accepted t @ B,
       dwu_gens := (dwu_gens t)(g \<mapsto> UProd)\<rparr>)"
proof -
  have step: "dwu_step t (UFire g)
    (t\<lparr>dwu_sent := dwu_sent t @ B,
       dwu_accepted := dwu_accepted t @ (if dwu_fence t \<le> g then B else []),
       dwu_gens := (dwu_gens t)(g \<mapsto> UProd)\<rparr>)"
    by (rule dwu_step.ufire[OF assms(1)])
  have "(if dwu_fence t \<le> g then B else []) = B" using assms(2) by simp
  with step show ?thesis by simp
qed

text \<open>Two constant computations at the floor's healed store: the owed replay list, and
  the distinctness of the two committed coordinates.\<close>

lemma rf_x1_lp: "log_payloads [rf_x1] = [(ec1, e1)]"
  by (simp add: log_payloads_def rf_x1_def map_filter_simps)

text \<open>@{const rf_x1} carried at the HEAD of the accepted ledger (a non-looping
  cons-form rewrite for the fired end-states, whose accepted list is
  @{term "rf_x1 # B1 @ B2"}).\<close>

lemma log_payloads_x1_batch:
  "log_payloads (rf_x1 # xs) = (ec1, e1) # log_payloads xs"
  by (simp add: log_payloads_def rf_x1_def map_filter_simps)

lemma rf_replay_stoH:
  "replay_down_hist (exec_src_hist rf_stoH) (exec_scope rf_stoH) ec2 = [(ec1, e1), (ec2, e2)]"
  by (simp add: rf_stoH_def mkC_def replay_down_hist_def e1_def e2_def ec_defs)

lemma rf_ec12_neq: "(ec1, e1) \<noteq> (ec2, e2)"
  by (simp add: ec_defs)

text \<open>The three @{text uarm} side conditions at @{const rf_W} (the witness is Crashed
  @{const ec2}, finish @{const ec2}, two live UProd generations).\<close>

lemma rf_dom0: "0 \<in> dom (dwu_gens rf_W)"
  by (simp add: rf_W_def mkU_def)

lemma rf_crashed: "\<exists>c. exec_status (dwu_store rf_W) = Crashed c"
  by (rule exI[of _ ec2]) (simp add: rf_W_def mkU_def rf_sto6_def mkC_def)

lemma rf_finish: "ec2 \<le> exec_finish (dwu_store rf_W)"
  by (simp add: rf_W_def mkU_def rf_sto6_def mkC_def)


section \<open>3. U9 companions (I4 principals; seed proofs ported)\<close>

lemma u_pair_steps_bookkeeping:
  assumes "u_pair_steps D g1 g2 f W A F H t'"
  shows "A \<subseteq> {g1, g2} \<and> F \<subseteq> A \<and> H \<subseteq> {g1, g2}"
  using assms by (induction rule: u_pair_steps.induct) auto

lemma u_oneshot_death_budget:
  assumes "g1 \<noteq> g2"
      and "u_oneshot_pair_extension D g1 g2 f W t'"
  shows "\<exists>F H. u_pair_steps D g1 g2 f W {g1, g2} F H t' \<and> card ({g1, g2} - F) \<le> 1"
proof -
  from assms(2) obtain F H where ps: "u_pair_steps D g1 g2 f W {g1, g2} F H t'"
      and Fne: "F \<noteq> {}" and HF: "H \<noteq> {} \<and> H \<subseteq> F"
    unfolding u_oneshot_pair_extension_def by blast
  from u_pair_steps_bookkeeping[OF ps] have FA: "F \<subseteq> {g1, g2}" by blast
  from Fne obtain g where gF: "g \<in> F" by blast
  with FA have g_or: "g = g1 \<or> g = g2" by blast
  have "{g1, g2} - F \<subseteq> {g1, g2} - {g}" using gF by blast
  then have "card ({g1, g2} - F) \<le> card ({g1, g2} - {g})"
    by (intro card_mono) auto
  also have "... \<le> 1" using g_or assms(1) by auto
  finally show ?thesis using ps by blast
qed


section \<open>4. U9 --- the impossibility headliner (statement VERBATIM from seed)\<close>

theorem u_concurrent_recovery_dilemma:
  "\<exists>W g1 g2 f p.
     dwu_reachable_w W
   \<and> (\<exists>c. exec_status (dwu_store W) = Crashed c)
   \<and> dwu_fence W = 0
   \<and> g1 \<noteq> g2
   \<and> dwu_gens W g1 = Some UProd \<and> dwu_gens W g2 = Some UProd
   \<and> \<not> u_effect_unsafe W
   \<and> u_sink_delta f W = [p]
   \<and> (\<forall>D :: u_pair_chooser.
        \<exists>t'. u_oneshot_pair_extension D g1 g2 f W t'
           \<and> (u_effect_unsafe t' \<or> u_lost f t'))"
proof -
  \<comment> \<open>THE NEW WORK: the last conjunct at the pinned witness (W := rf_W, g1 := 0,
      g2 := 1, f := ec2).  For an arbitrary payload chooser D, arm 0 then 1 to
      DETERMINE the two batches B1, B2, then a 4-cell case split on whether the owed
      @{term "(ec2, e2)"} appears in each batch supplies an explicit legal in-extension
      schedule that duplicates (T,T) or loses (F,F / T,F / F,T).\<close>
  have last:
    "\<forall>D :: u_pair_chooser.
       \<exists>t'. u_oneshot_pair_extension D 0 1 ec2 rf_W t'
          \<and> (u_effect_unsafe t' \<or> u_lost ec2 t')"
  proof (intro allI)
    fix D :: u_pair_chooser
    define B1 where "B1 = u_stamped_batch (length (dwu_journal rf_W)) 0 (D 0 rf_W)"
    define t1 where "t1 = rf_W\<lparr>dwu_gens := (dwu_gens rf_W)(0 \<mapsto> UArmed B1)\<rparr>"
    define B2 where "B2 = u_stamped_batch (length (dwu_journal t1)) 1 (D 1 t1)"
    define t2 where "t2 = t1\<lparr>dwu_gens := (dwu_gens t1)(1 \<mapsto> UArmed B2)\<rparr>"
    define t3 where "t3 = t2\<lparr>dwu_store := rf_stoH\<rparr>"
    define t4 where "t4 = t3\<lparr>dwu_sent := dwu_sent t3 @ B1,
                             dwu_accepted := dwu_accepted t3 @ B1,
                             dwu_gens := (dwu_gens t3)(0 \<mapsto> UProd)\<rparr>"
    define t5 where "t5 = t4\<lparr>dwu_sent := dwu_sent t4 @ B2,
                             dwu_accepted := dwu_accepted t4 @ B2,
                             dwu_gens := (dwu_gens t4)(1 \<mapsto> UProd)\<rparr>"
    define t4b where "t4b = t3\<lparr>dwu_sent := dwu_sent t3 @ B2,
                               dwu_accepted := dwu_accepted t3 @ B2,
                               dwu_gens := (dwu_gens t3)(1 \<mapsto> UProd)\<rparr>"

    \<comment> \<open>store / gens / fence book-keeping for the intermediate states\<close>
    have store_t1: "dwu_store t1 = rf_sto6" by (simp add: t1_def rf_W_def mkU_def)
    have store_t2: "dwu_store t2 = rf_sto6" by (simp add: t2_def t1_def rf_W_def mkU_def)
    have t1_dom1: "1 \<in> dom (dwu_gens t1)" by (simp add: t1_def rf_W_def mkU_def)
    have t1_crashed: "\<exists>c. exec_status (dwu_store t1) = Crashed c"
      by (rule exI[of _ ec2]) (simp add: store_t1 rf_sto6_def mkC_def)
    have t1_finish: "ec2 \<le> exec_finish (dwu_store t1)"
      by (simp add: store_t1 rf_sto6_def mkC_def)

    \<comment> \<open>the two arms (arm 0 at rf_W, arm 1 at t1) --- each is a machine step\<close>
    have arm0: "dwu_step rf_W (UArm 0 B1 ec2) t1"
      unfolding B1_def t1_def by (rule u_arm_stamped_step[OF rf_dom0 rf_crashed rf_finish])
    have arm1: "dwu_step t1 (UArm 1 B2 ec2) t2"
      unfolding B2_def t2_def by (rule u_arm_stamped_step[OF t1_dom1 t1_crashed t1_finish])

    have ps0: "u_pair_steps D 0 1 ec2 rf_W {} {} {} rf_W" by (rule u_pair_steps.upe_refl)
    have ps1: "u_pair_steps D 0 1 ec2 rf_W {0} {} {} t1"
      by (rule u_pair_steps.upe_arm[OF ps0 _ _ arm0[unfolded B1_def]]) simp_all
    have ps2': "u_pair_steps D 0 1 ec2 rf_W (insert 1 {0}) {} {} t2"
      by (rule u_pair_steps.upe_arm[OF ps1 _ _ arm1[unfolded B2_def]]) simp_all
    have ps2: "u_pair_steps D 0 1 ec2 rf_W {0, 1} {} {} t2"
      using ps2' by (simp add: insert_commute)

    \<comment> \<open>the heals (UHeal 0 for the full schedule / F,T; UHeal 1 for T,F) both land on t3\<close>
    have heal0: "dwu_step t2 (UHeal 0 ec2) t3"
      unfolding t3_def by (rule u9_heal_step[OF store_t2])
    have heal1: "dwu_step t2 (UHeal 1 ec2) t3"
      unfolding t3_def by (rule u9_heal_step[OF store_t2])
    have ps3: "u_pair_steps D 0 1 ec2 rf_W {0, 1} {} {0} t3"
      by (rule u_pair_steps.upe_heal[OF ps2 _ heal0]) simp
    have ps3_TF: "u_pair_steps D 0 1 ec2 rf_W {0, 1} {} {1} t3"
      by (rule u_pair_steps.upe_heal[OF ps2 _ heal1]) simp

    \<comment> \<open>gens/fence at t3 and t4 for the fires\<close>
    have t3_gens0: "dwu_gens t3 0 = Some (UArmed B1)"
      by (simp add: t3_def t2_def t1_def rf_W_def mkU_def)
    have t3_gens1: "dwu_gens t3 1 = Some (UArmed B2)"
      by (simp add: t3_def t2_def t1_def rf_W_def mkU_def)
    have t3_fence: "dwu_fence t3 = 0"
      by (simp add: t3_def t2_def t1_def rf_W_def mkU_def)
    have t4_gens1: "dwu_gens t4 1 = Some (UArmed B2)"
      by (simp add: t4_def t3_def t2_def t1_def rf_W_def mkU_def)
    have t4_fence: "dwu_fence t4 = 0"
      by (simp add: t4_def t3_def t2_def t1_def rf_W_def mkU_def)

    have fire0: "dwu_step t3 (UFire 0) t4"
      unfolding t4_def by (rule u9_fire_step0[OF t3_gens0 t3_fence])
    have fire1: "dwu_step t4 (UFire 1) t5"
      unfolding t5_def by (rule u9_fire_step0[OF t4_gens1 t4_fence])
    have fire1b: "dwu_step t3 (UFire 1) t4b"
      unfolding t4b_def by (rule u9_fire_step0[OF t3_gens1 t3_fence])

    have ps4: "u_pair_steps D 0 1 ec2 rf_W {0, 1} {0} {0} t4"
      by (rule u_pair_steps.upe_fire[OF ps3 _ _ _ fire0]) simp_all
    have ps5': "u_pair_steps D 0 1 ec2 rf_W {0, 1} (insert 1 {0}) {0} t5"
      by (rule u_pair_steps.upe_fire[OF ps4 _ _ _ fire1]) simp_all
    have ps5: "u_pair_steps D 0 1 ec2 rf_W {0, 1} {0, 1} {0} t5"
      using ps5' by (simp add: insert_commute)
    have ps4_TF: "u_pair_steps D 0 1 ec2 rf_W {0, 1} {1} {1} t4b"
      by (rule u_pair_steps.upe_fire[OF ps3_TF _ _ _ fire1b]) simp_all

    \<comment> \<open>the three one-shot extensions (F,H exhibited; F \<noteq> {}, H \<noteq> {}, H \<subseteq> F)\<close>
    have ext_full: "u_oneshot_pair_extension D 0 1 ec2 rf_W t5"
      unfolding u_oneshot_pair_extension_def
    proof (intro exI conjI)
      show "u_pair_steps D 0 1 ec2 rf_W {0, 1} {0, 1} {0} t5" by (rule ps5)
    qed simp_all
    have ext_TF: "u_oneshot_pair_extension D 0 1 ec2 rf_W t4b"
      unfolding u_oneshot_pair_extension_def
    proof (intro exI conjI)
      show "u_pair_steps D 0 1 ec2 rf_W {0, 1} {1} {1} t4b" by (rule ps4_TF)
    qed simp_all
    have ext_FT: "u_oneshot_pair_extension D 0 1 ec2 rf_W t4"
      unfolding u_oneshot_pair_extension_def
    proof (intro exI conjI)
      show "u_pair_steps D 0 1 ec2 rf_W {0, 1} {0} {0} t4" by (rule ps4)
    qed simp_all

    \<comment> \<open>the accepted ledgers and the owed replay at the three end-states\<close>
    have acc_t5: "dwu_accepted t5 = rf_x1 # B1 @ B2"
      by (simp add: t5_def t4_def t3_def t2_def t1_def rf_W_def mkU_def)
    have lp_t5: "log_payloads (dwu_accepted t5) = (ec1, e1) # (log_payloads B1 @ log_payloads B2)"
      by (simp add: acc_t5 log_payloads_x1_batch log_payloads_append)
    have acc_t4: "dwu_accepted t4 = rf_x1 # B1"
      by (simp add: t4_def t3_def t2_def t1_def rf_W_def mkU_def)
    have lp_t4: "log_payloads (dwu_accepted t4) = (ec1, e1) # log_payloads B1"
      by (simp add: acc_t4 log_payloads_x1_batch)
    have acc_t4b: "dwu_accepted t4b = rf_x1 # B2"
      by (simp add: t4b_def t3_def t2_def t1_def rf_W_def mkU_def)
    have lp_t4b: "log_payloads (dwu_accepted t4b) = (ec1, e1) # log_payloads B2"
      by (simp add: acc_t4b log_payloads_x1_batch)

    have store_t5: "dwu_store t5 = rf_stoH" by (simp add: t5_def t4_def t3_def)
    have floor_t5: "dwu_floor t5 = 0"
      by (simp add: t5_def t4_def t3_def t2_def t1_def rf_W_def mkU_def)
    have store_t4: "dwu_store t4 = rf_stoH" by (simp add: t4_def t3_def)
    have floor_t4: "dwu_floor t4 = 0"
      by (simp add: t4_def t3_def t2_def t1_def rf_W_def mkU_def)
    have store_t4b: "dwu_store t4b = rf_stoH" by (simp add: t4b_def t3_def)
    have floor_t4b: "dwu_floor t4b = 0"
      by (simp add: t4b_def t3_def t2_def t1_def rf_W_def mkU_def)

    have owed_t5: "(ec2, e2) \<in> set (replay_down_hist (retained_hist t5) (exec_scope (dwu_store t5)) ec2)"
      by (simp add: retained_hist_def store_t5 floor_t5 rf_replay_stoH)
    have owed_t4: "(ec2, e2) \<in> set (replay_down_hist (retained_hist t4) (exec_scope (dwu_store t4)) ec2)"
      by (simp add: retained_hist_def store_t4 floor_t4 rf_replay_stoH)
    have owed_t4b: "(ec2, e2) \<in> set (replay_down_hist (retained_hist t4b) (exec_scope (dwu_store t4b)) ec2)"
      by (simp add: retained_hist_def store_t4b floor_t4b rf_replay_stoH)

    \<comment> \<open>THE 4-CELL TAXONOMY (total split on whether the owed payload is in each batch)\<close>
    consider
        (TT) "(ec2, e2) \<in> set (log_payloads B1) \<and> (ec2, e2) \<in> set (log_payloads B2)"
      | (FF) "(ec2, e2) \<notin> set (log_payloads B1) \<and> (ec2, e2) \<notin> set (log_payloads B2)"
      | (TF) "(ec2, e2) \<in> set (log_payloads B1) \<and> (ec2, e2) \<notin> set (log_payloads B2)"
      | (FT) "(ec2, e2) \<notin> set (log_payloads B1) \<and> (ec2, e2) \<in> set (log_payloads B2)"
      by blast
    then show "\<exists>t'. u_oneshot_pair_extension D 0 1 ec2 rf_W t'
                 \<and> (u_effect_unsafe t' \<or> u_lost ec2 t')"
    proof cases
      case TT
      \<comment> \<open>fire BOTH: the owed payload lands twice \<Rightarrow> duplicate \<Rightarrow> unsafe\<close>
      have dup: "u_duplicate t5"
      proof -
        have "(ec2, e2) \<in> set (log_payloads B1)" and "(ec2, e2) \<in> set (log_payloads B2)"
          using TT by simp_all
        hence "\<not> distinct ((ec1, e1) # (log_payloads B1 @ log_payloads B2))"
          by (auto simp: distinct_append)
        thus ?thesis by (simp add: u_duplicate_def lp_t5)
      qed
      have "u_effect_unsafe t5" by (simp add: u_effect_unsafe_def dup)
      with ext_full show ?thesis by blast
    next
      case FF
      \<comment> \<open>fire BOTH but neither delivers the owed payload \<Rightarrow> lost\<close>
      have "(ec2, e2) \<notin> set (log_payloads (dwu_accepted t5))"
        using FF rf_ec12_neq by (auto simp: lp_t5)
      with owed_t5 have "u_lost ec2 t5" unfolding u_lost_def by blast
      with ext_full show ?thesis by blast
    next
      case TF
      \<comment> \<open>kill gen 0 (its arm is its only step), heal+fire gen 1; gen 1 lacks the owed \<Rightarrow> lost\<close>
      have "(ec2, e2) \<notin> set (log_payloads (dwu_accepted t4b))"
        using TF rf_ec12_neq by (auto simp: lp_t4b)
      with owed_t4b have "u_lost ec2 t4b" unfolding u_lost_def by blast
      with ext_TF show ?thesis by blast
    next
      case FT
      \<comment> \<open>symmetric: kill gen 1, heal+fire gen 0; gen 0 lacks the owed \<Rightarrow> lost\<close>
      have "(ec2, e2) \<notin> set (log_payloads (dwu_accepted t4))"
        using FT rf_ec12_neq by (auto simp: lp_t4)
      with owed_t4 have "u_lost ec2 t4" unfolding u_lost_def by blast
      with ext_FT show ?thesis by blast
    qed
  qed

  \<comment> \<open>the first eight conjuncts are the floor's witness verdicts; the ninth is @{text last}\<close>
  have body:
    "dwu_reachable_w rf_W
   \<and> (\<exists>c. exec_status (dwu_store rf_W) = Crashed c)
   \<and> dwu_fence rf_W = 0
   \<and> (0::nat) \<noteq> 1
   \<and> dwu_gens rf_W 0 = Some UProd \<and> dwu_gens rf_W 1 = Some UProd
   \<and> \<not> u_effect_unsafe rf_W
   \<and> u_sink_delta ec2 rf_W = [(ec2, e2)]
   \<and> (\<forall>D :: u_pair_chooser.
        \<exists>t'. u_oneshot_pair_extension D 0 1 ec2 rf_W t'
           \<and> (u_effect_unsafe t' \<or> u_lost ec2 t'))"
  proof (intro conjI)
    show "dwu_reachable_w rf_W" by (rule rf_reach_W)
  next
    show "\<exists>c. exec_status (dwu_store rf_W) = Crashed c" by (rule rf_crashed)
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
    show "\<forall>D :: u_pair_chooser.
            \<exists>t'. u_oneshot_pair_extension D 0 1 ec2 rf_W t'
               \<and> (u_effect_unsafe t' \<or> u_lost ec2 t')"
      by (rule last)
  qed
  show ?thesis
    by (rule exI[of _ rf_W], rule exI[of _ "0::nat"], rule exI[of _ "1::nat"],
        rule exI[of _ ec2], rule exI[of _ "(ec2, e2)"]) (rule body)
qed

text \<open>The two-horn export: the headliner statement with the defeat conjunct
  sharpened to @{const u_duplicate}-or-@{const u_lost}.  The proof replays the
  same witness, the same schedules, and the same 4-cell taxonomy; the TT cell
  exports its proved @{const u_duplicate} fact as-is (no weakening into
  @{const u_effect_unsafe}), and the three loss cells export their
  @{const u_lost} facts as theirs.  A fact of the designed witness;
  @{thm [source] u_concurrent_recovery_dilemma} stays the statement of
  record.\<close>

theorem u_concurrent_recovery_duplicate_or_lost:
  "\<exists>W g1 g2 f p.
     dwu_reachable_w W
   \<and> (\<exists>c. exec_status (dwu_store W) = Crashed c)
   \<and> dwu_fence W = 0
   \<and> g1 \<noteq> g2
   \<and> dwu_gens W g1 = Some UProd \<and> dwu_gens W g2 = Some UProd
   \<and> \<not> u_effect_unsafe W
   \<and> u_sink_delta f W = [p]
   \<and> (\<forall>D :: u_pair_chooser.
        \<exists>t'. u_oneshot_pair_extension D g1 g2 f W t'
           \<and> (u_duplicate t' \<or> u_lost f t'))"
proof -
  \<comment> \<open>Replay of the headliner's construction at the pinned witness (W := rf_W,
      g1 := 0, g2 := 1, f := ec2); only the exported horn differs --- the TT cell
      ships @{const u_duplicate} itself.\<close>
  have last:
    "\<forall>D :: u_pair_chooser.
       \<exists>t'. u_oneshot_pair_extension D 0 1 ec2 rf_W t'
          \<and> (u_duplicate t' \<or> u_lost ec2 t')"
  proof (intro allI)
    fix D :: u_pair_chooser
    define B1 where "B1 = u_stamped_batch (length (dwu_journal rf_W)) 0 (D 0 rf_W)"
    define t1 where "t1 = rf_W\<lparr>dwu_gens := (dwu_gens rf_W)(0 \<mapsto> UArmed B1)\<rparr>"
    define B2 where "B2 = u_stamped_batch (length (dwu_journal t1)) 1 (D 1 t1)"
    define t2 where "t2 = t1\<lparr>dwu_gens := (dwu_gens t1)(1 \<mapsto> UArmed B2)\<rparr>"
    define t3 where "t3 = t2\<lparr>dwu_store := rf_stoH\<rparr>"
    define t4 where "t4 = t3\<lparr>dwu_sent := dwu_sent t3 @ B1,
                             dwu_accepted := dwu_accepted t3 @ B1,
                             dwu_gens := (dwu_gens t3)(0 \<mapsto> UProd)\<rparr>"
    define t5 where "t5 = t4\<lparr>dwu_sent := dwu_sent t4 @ B2,
                             dwu_accepted := dwu_accepted t4 @ B2,
                             dwu_gens := (dwu_gens t4)(1 \<mapsto> UProd)\<rparr>"
    define t4b where "t4b = t3\<lparr>dwu_sent := dwu_sent t3 @ B2,
                               dwu_accepted := dwu_accepted t3 @ B2,
                               dwu_gens := (dwu_gens t3)(1 \<mapsto> UProd)\<rparr>"

    \<comment> \<open>store / gens / fence book-keeping for the intermediate states\<close>
    have store_t1: "dwu_store t1 = rf_sto6" by (simp add: t1_def rf_W_def mkU_def)
    have store_t2: "dwu_store t2 = rf_sto6" by (simp add: t2_def t1_def rf_W_def mkU_def)
    have t1_dom1: "1 \<in> dom (dwu_gens t1)" by (simp add: t1_def rf_W_def mkU_def)
    have t1_crashed: "\<exists>c. exec_status (dwu_store t1) = Crashed c"
      by (rule exI[of _ ec2]) (simp add: store_t1 rf_sto6_def mkC_def)
    have t1_finish: "ec2 \<le> exec_finish (dwu_store t1)"
      by (simp add: store_t1 rf_sto6_def mkC_def)

    \<comment> \<open>the two arms (arm 0 at rf_W, arm 1 at t1) --- each is a machine step\<close>
    have arm0: "dwu_step rf_W (UArm 0 B1 ec2) t1"
      unfolding B1_def t1_def by (rule u_arm_stamped_step[OF rf_dom0 rf_crashed rf_finish])
    have arm1: "dwu_step t1 (UArm 1 B2 ec2) t2"
      unfolding B2_def t2_def by (rule u_arm_stamped_step[OF t1_dom1 t1_crashed t1_finish])

    have ps0: "u_pair_steps D 0 1 ec2 rf_W {} {} {} rf_W" by (rule u_pair_steps.upe_refl)
    have ps1: "u_pair_steps D 0 1 ec2 rf_W {0} {} {} t1"
      by (rule u_pair_steps.upe_arm[OF ps0 _ _ arm0[unfolded B1_def]]) simp_all
    have ps2': "u_pair_steps D 0 1 ec2 rf_W (insert 1 {0}) {} {} t2"
      by (rule u_pair_steps.upe_arm[OF ps1 _ _ arm1[unfolded B2_def]]) simp_all
    have ps2: "u_pair_steps D 0 1 ec2 rf_W {0, 1} {} {} t2"
      using ps2' by (simp add: insert_commute)

    \<comment> \<open>the heals (UHeal 0 for the full schedule / F,T; UHeal 1 for T,F) both land on t3\<close>
    have heal0: "dwu_step t2 (UHeal 0 ec2) t3"
      unfolding t3_def by (rule u9_heal_step[OF store_t2])
    have heal1: "dwu_step t2 (UHeal 1 ec2) t3"
      unfolding t3_def by (rule u9_heal_step[OF store_t2])
    have ps3: "u_pair_steps D 0 1 ec2 rf_W {0, 1} {} {0} t3"
      by (rule u_pair_steps.upe_heal[OF ps2 _ heal0]) simp
    have ps3_TF: "u_pair_steps D 0 1 ec2 rf_W {0, 1} {} {1} t3"
      by (rule u_pair_steps.upe_heal[OF ps2 _ heal1]) simp

    \<comment> \<open>gens/fence at t3 and t4 for the fires\<close>
    have t3_gens0: "dwu_gens t3 0 = Some (UArmed B1)"
      by (simp add: t3_def t2_def t1_def rf_W_def mkU_def)
    have t3_gens1: "dwu_gens t3 1 = Some (UArmed B2)"
      by (simp add: t3_def t2_def t1_def rf_W_def mkU_def)
    have t3_fence: "dwu_fence t3 = 0"
      by (simp add: t3_def t2_def t1_def rf_W_def mkU_def)
    have t4_gens1: "dwu_gens t4 1 = Some (UArmed B2)"
      by (simp add: t4_def t3_def t2_def t1_def rf_W_def mkU_def)
    have t4_fence: "dwu_fence t4 = 0"
      by (simp add: t4_def t3_def t2_def t1_def rf_W_def mkU_def)

    have fire0: "dwu_step t3 (UFire 0) t4"
      unfolding t4_def by (rule u9_fire_step0[OF t3_gens0 t3_fence])
    have fire1: "dwu_step t4 (UFire 1) t5"
      unfolding t5_def by (rule u9_fire_step0[OF t4_gens1 t4_fence])
    have fire1b: "dwu_step t3 (UFire 1) t4b"
      unfolding t4b_def by (rule u9_fire_step0[OF t3_gens1 t3_fence])

    have ps4: "u_pair_steps D 0 1 ec2 rf_W {0, 1} {0} {0} t4"
      by (rule u_pair_steps.upe_fire[OF ps3 _ _ _ fire0]) simp_all
    have ps5': "u_pair_steps D 0 1 ec2 rf_W {0, 1} (insert 1 {0}) {0} t5"
      by (rule u_pair_steps.upe_fire[OF ps4 _ _ _ fire1]) simp_all
    have ps5: "u_pair_steps D 0 1 ec2 rf_W {0, 1} {0, 1} {0} t5"
      using ps5' by (simp add: insert_commute)
    have ps4_TF: "u_pair_steps D 0 1 ec2 rf_W {0, 1} {1} {1} t4b"
      by (rule u_pair_steps.upe_fire[OF ps3_TF _ _ _ fire1b]) simp_all

    \<comment> \<open>the three one-shot extensions (F,H exhibited; F \<noteq> {}, H \<noteq> {}, H \<subseteq> F)\<close>
    have ext_full: "u_oneshot_pair_extension D 0 1 ec2 rf_W t5"
      unfolding u_oneshot_pair_extension_def
    proof (intro exI conjI)
      show "u_pair_steps D 0 1 ec2 rf_W {0, 1} {0, 1} {0} t5" by (rule ps5)
    qed simp_all
    have ext_TF: "u_oneshot_pair_extension D 0 1 ec2 rf_W t4b"
      unfolding u_oneshot_pair_extension_def
    proof (intro exI conjI)
      show "u_pair_steps D 0 1 ec2 rf_W {0, 1} {1} {1} t4b" by (rule ps4_TF)
    qed simp_all
    have ext_FT: "u_oneshot_pair_extension D 0 1 ec2 rf_W t4"
      unfolding u_oneshot_pair_extension_def
    proof (intro exI conjI)
      show "u_pair_steps D 0 1 ec2 rf_W {0, 1} {0} {0} t4" by (rule ps4)
    qed simp_all

    \<comment> \<open>the accepted ledgers and the owed replay at the three end-states\<close>
    have acc_t5: "dwu_accepted t5 = rf_x1 # B1 @ B2"
      by (simp add: t5_def t4_def t3_def t2_def t1_def rf_W_def mkU_def)
    have lp_t5: "log_payloads (dwu_accepted t5) = (ec1, e1) # (log_payloads B1 @ log_payloads B2)"
      by (simp add: acc_t5 log_payloads_x1_batch log_payloads_append)
    have acc_t4: "dwu_accepted t4 = rf_x1 # B1"
      by (simp add: t4_def t3_def t2_def t1_def rf_W_def mkU_def)
    have lp_t4: "log_payloads (dwu_accepted t4) = (ec1, e1) # log_payloads B1"
      by (simp add: acc_t4 log_payloads_x1_batch)
    have acc_t4b: "dwu_accepted t4b = rf_x1 # B2"
      by (simp add: t4b_def t3_def t2_def t1_def rf_W_def mkU_def)
    have lp_t4b: "log_payloads (dwu_accepted t4b) = (ec1, e1) # log_payloads B2"
      by (simp add: acc_t4b log_payloads_x1_batch)

    have store_t5: "dwu_store t5 = rf_stoH" by (simp add: t5_def t4_def t3_def)
    have floor_t5: "dwu_floor t5 = 0"
      by (simp add: t5_def t4_def t3_def t2_def t1_def rf_W_def mkU_def)
    have store_t4: "dwu_store t4 = rf_stoH" by (simp add: t4_def t3_def)
    have floor_t4: "dwu_floor t4 = 0"
      by (simp add: t4_def t3_def t2_def t1_def rf_W_def mkU_def)
    have store_t4b: "dwu_store t4b = rf_stoH" by (simp add: t4b_def t3_def)
    have floor_t4b: "dwu_floor t4b = 0"
      by (simp add: t4b_def t3_def t2_def t1_def rf_W_def mkU_def)

    have owed_t5: "(ec2, e2) \<in> set (replay_down_hist (retained_hist t5) (exec_scope (dwu_store t5)) ec2)"
      by (simp add: retained_hist_def store_t5 floor_t5 rf_replay_stoH)
    have owed_t4: "(ec2, e2) \<in> set (replay_down_hist (retained_hist t4) (exec_scope (dwu_store t4)) ec2)"
      by (simp add: retained_hist_def store_t4 floor_t4 rf_replay_stoH)
    have owed_t4b: "(ec2, e2) \<in> set (replay_down_hist (retained_hist t4b) (exec_scope (dwu_store t4b)) ec2)"
      by (simp add: retained_hist_def store_t4b floor_t4b rf_replay_stoH)

    \<comment> \<open>THE 4-CELL TAXONOMY (total split on whether the owed payload is in each batch)\<close>
    consider
        (TT) "(ec2, e2) \<in> set (log_payloads B1) \<and> (ec2, e2) \<in> set (log_payloads B2)"
      | (FF) "(ec2, e2) \<notin> set (log_payloads B1) \<and> (ec2, e2) \<notin> set (log_payloads B2)"
      | (TF) "(ec2, e2) \<in> set (log_payloads B1) \<and> (ec2, e2) \<notin> set (log_payloads B2)"
      | (FT) "(ec2, e2) \<notin> set (log_payloads B1) \<and> (ec2, e2) \<in> set (log_payloads B2)"
      by blast
    then show "\<exists>t'. u_oneshot_pair_extension D 0 1 ec2 rf_W t'
                 \<and> (u_duplicate t' \<or> u_lost ec2 t')"
    proof cases
      case TT
      \<comment> \<open>fire BOTH: the owed payload lands twice \<Rightarrow> duplicate, exported as-is\<close>
      have dup: "u_duplicate t5"
      proof -
        have "(ec2, e2) \<in> set (log_payloads B1)" and "(ec2, e2) \<in> set (log_payloads B2)"
          using TT by simp_all
        hence "\<not> distinct ((ec1, e1) # (log_payloads B1 @ log_payloads B2))"
          by (auto simp: distinct_append)
        thus ?thesis by (simp add: u_duplicate_def lp_t5)
      qed
      with ext_full show ?thesis by blast
    next
      case FF
      \<comment> \<open>fire BOTH but neither delivers the owed payload \<Rightarrow> lost\<close>
      have "(ec2, e2) \<notin> set (log_payloads (dwu_accepted t5))"
        using FF rf_ec12_neq by (auto simp: lp_t5)
      with owed_t5 have "u_lost ec2 t5" unfolding u_lost_def by blast
      with ext_full show ?thesis by blast
    next
      case TF
      \<comment> \<open>kill gen 0 (its arm is its only step), heal+fire gen 1; gen 1 lacks the owed \<Rightarrow> lost\<close>
      have "(ec2, e2) \<notin> set (log_payloads (dwu_accepted t4b))"
        using TF rf_ec12_neq by (auto simp: lp_t4b)
      with owed_t4b have "u_lost ec2 t4b" unfolding u_lost_def by blast
      with ext_TF show ?thesis by blast
    next
      case FT
      \<comment> \<open>symmetric: kill gen 1, heal+fire gen 0; gen 0 lacks the owed \<Rightarrow> lost\<close>
      have "(ec2, e2) \<notin> set (log_payloads (dwu_accepted t4))"
        using FT rf_ec12_neq by (auto simp: lp_t4)
      with owed_t4 have "u_lost ec2 t4" unfolding u_lost_def by blast
      with ext_FT show ?thesis by blast
    qed
  qed

  \<comment> \<open>the first eight conjuncts are the floor's witness verdicts; the ninth is @{text last}\<close>
  have body:
    "dwu_reachable_w rf_W
   \<and> (\<exists>c. exec_status (dwu_store rf_W) = Crashed c)
   \<and> dwu_fence rf_W = 0
   \<and> (0::nat) \<noteq> 1
   \<and> dwu_gens rf_W 0 = Some UProd \<and> dwu_gens rf_W 1 = Some UProd
   \<and> \<not> u_effect_unsafe rf_W
   \<and> u_sink_delta ec2 rf_W = [(ec2, e2)]
   \<and> (\<forall>D :: u_pair_chooser.
        \<exists>t'. u_oneshot_pair_extension D 0 1 ec2 rf_W t'
           \<and> (u_duplicate t' \<or> u_lost ec2 t'))"
  proof (intro conjI)
    show "dwu_reachable_w rf_W" by (rule rf_reach_W)
  next
    show "\<exists>c. exec_status (dwu_store rf_W) = Crashed c" by (rule rf_crashed)
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
    show "\<forall>D :: u_pair_chooser.
            \<exists>t'. u_oneshot_pair_extension D 0 1 ec2 rf_W t'
               \<and> (u_duplicate t' \<or> u_lost ec2 t')"
      by (rule last)
  qed
  show ?thesis
    by (rule exI[of _ rf_W], rule exI[of _ "0::nat"], rule exI[of _ "1::nat"],
        rule exI[of _ ec2], rule exI[of _ "(ec2, e2)"]) (rule body)
qed


section \<open>5. Rightness-gated additive corollary --- per-instance form of U8\<close>

text \<open>asc consumed positive-side only; restates the set-level completed-claim
  (@{thm [source] u_exactly_once_at_completed_claim}) per committed instance under
  an ascending source.  Under asc the per-instance conjunct is equivalent to the
  base theorem's at-least-once half (transported via
  @{thm [source] u_dedup_sink_instance_exact_iff}); a restriction to ascending
  sources, not a strengthening; no store-convergence variant (boundary 17).\<close>

theorem u_exactly_once_at_completed_claim_instance_exact:
  assumes "u_disciplined_trace (dwu_init b K fin) acts t"
      and "u_claim_of acts i j g f"
      and "u_window_fresh acts i j f"
      and "dwu_temporal_trace (dwu_init b K fin) (take j acts) tj"
      and "dwu_fence tj \<le> g"
      and "dwu_temporal_trace (dwu_init b K fin) (take (Suc j) acts) tj'"
      and "strictly_ascending_source (exec_src_hist (dwu_store tj'))"
  shows "u_exactly_once_at f tj'
       \<and> (\<forall>p \<in> set (replay_down_hist (retained_hist tj') (exec_scope (dwu_store tj')) f).
             count_list (u_dedup_view tj') p
               = count_list (replay_down_hist (retained_hist tj') (exec_scope (dwu_store tj')) f) p)"
proof
  show eo: "u_exactly_once_at f tj'"
    by (rule u_exactly_once_at_completed_claim[OF assms(1,2,3,4,5,6)])
  have alo: "u_at_least_once_at f tj'"
    using eo by (simp add: u_exactly_once_at_def)
  have iff':
    "(\<forall>p \<in> set (replay_down_hist (retained_hist tj') (exec_scope (dwu_store tj')) f).
        count_list (u_dedup_view tj') p
          = count_list (replay_down_hist (retained_hist tj') (exec_scope (dwu_store tj')) f) p)
     \<longleftrightarrow> u_at_least_once_at f tj'"
    by (rule u_dedup_sink_instance_exact_iff[OF assms(7)])
  from iff' alo
  show "\<forall>p \<in> set (replay_down_hist (retained_hist tj') (exec_scope (dwu_store tj')) f).
          count_list (u_dedup_view tj') p
            = count_list (replay_down_hist (retained_hist tj') (exec_scope (dwu_store tj')) f) p"
    by (rule iffD2)
qed


section \<open>6. R10 addendum --- the phase-carried (ordered) pair grammar\<close>

text \<open>The section-1 grammar keeps SET bookkeeping only: @{const u_pair_steps} records
  WHICH members armed / fired / healed, and @{const u_oneshot_pair_extension}
  constrains the final sets.  Nothing in that statement forces a member's own heal to
  precede its fire: @{text upe_heal} does not require the healer to be armed and
  @{text upe_fire} does not require the firer to be healed, so the extension
  predicate also admits fire-without-own-heal schedules (an external review
  observed this).  The landed defeat witnesses are per-member ordered wherever a
  heal occurs at all (Arm; Arm; Heal g; Fire g with the sibling dead after its arm),
  but the full TT/FF schedule fires the SIBLING with no heal of its own --- the
  classic zombie fire: the store was already healed by the other member, and one
  @{const relay_bounded_replay_reconcile} per crash is all the machine admits (a
  second @{text UHeal} needs a @{text Crashed} status, and the heal image
  @{const rf_stoH} is @{text Recovered}).

  This section makes temporal order part of the STATEMENT: a phase map replaces the
  three sets, and each rule steps one member through
  @{text "RIdle \<rightarrow> RArmed \<rightarrow> RHealed \<rightarrow> RFired"}.  Deliverables: (i) the phased
  grammar simulates the loose one (@{text phased_extension_imp_extension}), so
  every phase-ordered defeat is a defeat of the landed statement's shape; (ii) the
  ordered silent-death defeat @{text u_ordered_silent_death_defeat}: at the landed
  witness, fully ordered one-shot pair extensions always exist, and whenever a
  member's crash-time batch misses the owed payload, an ordered schedule in which
  that member completes arm--heal--fire and its sibling dies silently right after
  arming is @{const u_lost}; and (iii) the honest boundary
  @{text u_ordered_dilemma_fails_at_rf_W}: the landed dilemma conclusion with the
  phased extension in place of the loose one is FALSE at this witness --- the
  chooser @{text u_exact_chooser} completes exactly-once under EVERY fully ordered
  pair extension, because ordering plus the single reconcile leaves at most one
  completer, and one completer whose batch carries the owed (journaled) payload is
  neither premature, nor duplicating, nor lossy.  The TT duplicate cell of the
  headliner NEEDS the zombie fire; the loose bookkeeping is load-bearing content,
  not an oversight.\<close>

subsection \<open>6.1 The phase-carried grammar\<close>

datatype u_rec_phase = RIdle | RArmed | RHealed | RFired

text \<open>Same actor set, same machine steps, same chooser-typed machine-stamped batches
  as @{const u_pair_steps}; the three sets are replaced by one phase map, and each
  rule carries the per-member temporal precondition the loose grammar leaves out:
  arm from @{text RIdle}, heal from @{text RArmed}, fire from @{text RHealed}.\<close>

inductive u_pair_steps_phased ::
  "u_pair_chooser \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> frontier \<Rightarrow> (nat, nat) dwu_state \<Rightarrow>
   (nat \<Rightarrow> u_rec_phase) \<Rightarrow> (nat, nat) dwu_state \<Rightarrow> bool"
  for D g1 g2 f W
where
  upp_refl:
    "u_pair_steps_phased D g1 g2 f W (\<lambda>g. RIdle) W"
| upp_arm:
    "\<lbrakk>u_pair_steps_phased D g1 g2 f W P t; g \<in> {g1, g2}; P g = RIdle;
      dwu_step t (UArm g (u_stamped_batch (length (dwu_journal t)) g (D g t)) f) t'\<rbrakk>
     \<Longrightarrow> u_pair_steps_phased D g1 g2 f W (P(g := RArmed)) t'"
| upp_heal:
    "\<lbrakk>u_pair_steps_phased D g1 g2 f W P t; g \<in> {g1, g2}; P g = RArmed;
      dwu_step t (UHeal g f) t'\<rbrakk>
     \<Longrightarrow> u_pair_steps_phased D g1 g2 f W (P(g := RHealed)) t'"
| upp_fire:
    "\<lbrakk>u_pair_steps_phased D g1 g2 f W P t; g \<in> {g1, g2}; P g = RHealed;
      dwu_step t (UFire g) t'\<rbrakk>
     \<Longrightarrow> u_pair_steps_phased D g1 g2 f W (P(g := RFired)) t'"

text \<open>BOTH-ARM and one-shot completion, phase-carried: every member either completed
  the full ordered arm--heal--fire recovery (@{text RFired}) or died silently right
  after arming (@{text RArmed}); at least one completed.\<close>

definition u_oneshot_pair_extension_phased ::
  "u_pair_chooser \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> frontier \<Rightarrow> (nat, nat) dwu_state
   \<Rightarrow> (nat, nat) dwu_state \<Rightarrow> bool"
where
  "u_oneshot_pair_extension_phased D g1 g2 f W t' \<longleftrightarrow>
     (\<exists>P. u_pair_steps_phased D g1 g2 f W P t'
        \<and> (\<exists>g \<in> {g1, g2}. P g = RFired)
        \<and> (\<forall>g \<in> {g1, g2}. P g = RFired \<or> P g = RArmed))"

subsection \<open>6.2 Simulation into the loose grammar\<close>

text \<open>The phase map projects onto the loose sets: armed = past @{text RIdle}, fired
  = at @{text RFired}, healers = at or past @{text RHealed} (the loose grammar
  records healing independently of firing, so a fired member stays a healer).
  Every phased run is a loose run on the projected sets.\<close>

lemma u_pair_steps_phased_imp_steps:
  assumes "u_pair_steps_phased D g1 g2 f W P t'"
  shows "u_pair_steps D g1 g2 f W
           {h \<in> {g1, g2}. P h \<noteq> RIdle}
           {h \<in> {g1, g2}. P h = RFired}
           {h \<in> {g1, g2}. P h = RHealed \<or> P h = RFired} t'"
  using assms
proof (induction rule: u_pair_steps_phased.induct)
  case upp_refl
  have eA: "{h \<in> {g1, g2}. RIdle \<noteq> RIdle} = ({} :: nat set)" by auto
  have eF: "{h \<in> {g1, g2}. RIdle = RFired} = ({} :: nat set)" by auto
  have eH: "{h \<in> {g1, g2}. RIdle = RHealed \<or> RIdle = RFired} = ({} :: nat set)" by auto
  show ?case unfolding eA eF eH by (rule u_pair_steps.upe_refl)
next
  case (upp_arm P t g t')
  have eA: "{h \<in> {g1, g2}. (P(g := RArmed)) h \<noteq> RIdle}
            = insert g {h \<in> {g1, g2}. P h \<noteq> RIdle}"
    using upp_arm.hyps(2) by auto
  have eF: "{h \<in> {g1, g2}. (P(g := RArmed)) h = RFired}
            = {h \<in> {g1, g2}. P h = RFired}"
    using upp_arm.hyps(3) by auto
  have eH: "{h \<in> {g1, g2}. (P(g := RArmed)) h = RHealed \<or> (P(g := RArmed)) h = RFired}
            = {h \<in> {g1, g2}. P h = RHealed \<or> P h = RFired}"
    using upp_arm.hyps(3) by auto
  have gnA: "g \<notin> {h \<in> {g1, g2}. P h \<noteq> RIdle}"
    using upp_arm.hyps(3) by simp
  show ?case
    unfolding eA eF eH
    by (rule u_pair_steps.upe_arm[OF upp_arm.IH upp_arm.hyps(2) gnA upp_arm.hyps(4)])
next
  case (upp_heal P t g t')
  have eA: "{h \<in> {g1, g2}. (P(g := RHealed)) h \<noteq> RIdle}
            = {h \<in> {g1, g2}. P h \<noteq> RIdle}"
    using upp_heal.hyps(3) by auto
  have eF: "{h \<in> {g1, g2}. (P(g := RHealed)) h = RFired}
            = {h \<in> {g1, g2}. P h = RFired}"
    using upp_heal.hyps(3) by auto
  have eH: "{h \<in> {g1, g2}. (P(g := RHealed)) h = RHealed \<or> (P(g := RHealed)) h = RFired}
            = insert g {h \<in> {g1, g2}. P h = RHealed \<or> P h = RFired}"
    using upp_heal.hyps(2) by auto
  show ?case
    unfolding eA eF eH
    by (rule u_pair_steps.upe_heal[OF upp_heal.IH upp_heal.hyps(2) upp_heal.hyps(4)])
next
  case (upp_fire P t g t')
  have eA: "{h \<in> {g1, g2}. (P(g := RFired)) h \<noteq> RIdle}
            = {h \<in> {g1, g2}. P h \<noteq> RIdle}"
    using upp_fire.hyps(3) by auto
  have eF: "{h \<in> {g1, g2}. (P(g := RFired)) h = RFired}
            = insert g {h \<in> {g1, g2}. P h = RFired}"
    using upp_fire.hyps(2) by auto
  have eH: "{h \<in> {g1, g2}. (P(g := RFired)) h = RHealed \<or> (P(g := RFired)) h = RFired}
            = {h \<in> {g1, g2}. P h = RHealed \<or> P h = RFired}"
    using upp_fire.hyps(2,3) by auto
  have gA: "g \<in> {h \<in> {g1, g2}. P h \<noteq> RIdle}"
    using upp_fire.hyps(2,3) by simp
  have gnF: "g \<notin> {h \<in> {g1, g2}. P h = RFired}"
    using upp_fire.hyps(3) by simp
  show ?case
    unfolding eA eF eH
    by (rule u_pair_steps.upe_fire[OF upp_fire.IH upp_fire.hyps(2) gA gnF upp_fire.hyps(4)])
qed

lemma phased_extension_imp_extension:
  assumes "u_oneshot_pair_extension_phased D g1 g2 f W t'"
  shows "u_oneshot_pair_extension D g1 g2 f W t'"
proof -
  from assms obtain P where ps: "u_pair_steps_phased D g1 g2 f W P t'"
      and fired: "\<exists>g \<in> {g1, g2}. P g = RFired"
      and lowfin: "\<forall>g \<in> {g1, g2}. P g = RFired \<or> P g = RArmed"
    unfolding u_oneshot_pair_extension_phased_def by blast
  have Aeq: "{h \<in> {g1, g2}. P h \<noteq> RIdle} = {g1, g2}"
    using lowfin by auto
  have steps: "u_pair_steps D g1 g2 f W {g1, g2}
                 {h \<in> {g1, g2}. P h = RFired}
                 {h \<in> {g1, g2}. P h = RHealed \<or> P h = RFired} t'"
    using u_pair_steps_phased_imp_steps[OF ps] unfolding Aeq .
  have Fne: "{h \<in> {g1, g2}. P h = RFired} \<noteq> {}"
    using fired by auto
  have Hne: "{h \<in> {g1, g2}. P h = RHealed \<or> P h = RFired} \<noteq> {}"
    using fired by auto
  have HF: "{h \<in> {g1, g2}. P h = RHealed \<or> P h = RFired}
              \<subseteq> {h \<in> {g1, g2}. P h = RFired}"
    using lowfin by auto
  show ?thesis
    unfolding u_oneshot_pair_extension_def
    using steps Fne Hne HF by blast
qed

text \<open>Per-run compatibility banking: every phase-ordered defeat is a defeat in the
  landed statement's exact shape.\<close>

corollary phased_defeat_is_loose_defeat:
  assumes "u_oneshot_pair_extension_phased D g1 g2 f W t'"
      and "u_effect_unsafe t' \<or> u_lost f t'"
  shows "u_oneshot_pair_extension D g1 g2 f W t' \<and> (u_effect_unsafe t' \<or> u_lost f t')"
  using phased_extension_imp_extension[OF assms(1)] assms(2) by blast

subsection \<open>6.3 Ordered completions at the pinned witness\<close>

text \<open>The two fully ordered silent-death schedules at @{const rf_W}: both members
  arm, one member completes arm--heal--fire, the sibling stays @{text RArmed}
  forever (its only step was its arm).  The left lemma is the landed T,F endpoint
  verbatim; the right lemma arms the completing member FIRST so that its batch is
  chosen at @{const rf_W} itself, keeping the statement free of chain-internal
  states.\<close>

lemma rf_dom1: "1 \<in> dom (dwu_gens rf_W)"
  by (simp add: rf_W_def mkU_def)

lemma u_ordered_completion_left:
  fixes D :: u_pair_chooser
  shows "\<exists>t'. u_oneshot_pair_extension_phased D 0 1 ec2 rf_W t'
            \<and> dwu_accepted t' = rf_x1 # u_stamped_batch (length (dwu_journal rf_W)) 0 (D 0 rf_W)
            \<and> dwu_store t' = rf_stoH
            \<and> dwu_floor t' = 0"
proof -
  define B1 where "B1 = u_stamped_batch (length (dwu_journal rf_W)) 0 (D 0 rf_W)"
  define t1 where "t1 = rf_W\<lparr>dwu_gens := (dwu_gens rf_W)(0 \<mapsto> UArmed B1)\<rparr>"
  define B2 where "B2 = u_stamped_batch (length (dwu_journal t1)) 1 (D 1 t1)"
  define t2 where "t2 = t1\<lparr>dwu_gens := (dwu_gens t1)(1 \<mapsto> UArmed B2)\<rparr>"
  define t3 where "t3 = t2\<lparr>dwu_store := rf_stoH\<rparr>"
  define t4 where "t4 = t3\<lparr>dwu_sent := dwu_sent t3 @ B1,
                           dwu_accepted := dwu_accepted t3 @ B1,
                           dwu_gens := (dwu_gens t3)(0 \<mapsto> UProd)\<rparr>"
  have store_t1: "dwu_store t1 = rf_sto6" by (simp add: t1_def rf_W_def mkU_def)
  have store_t2: "dwu_store t2 = rf_sto6" by (simp add: t2_def t1_def rf_W_def mkU_def)
  have t1_dom1: "1 \<in> dom (dwu_gens t1)" by (simp add: t1_def rf_W_def mkU_def)
  have t1_crashed: "\<exists>c. exec_status (dwu_store t1) = Crashed c"
    by (rule exI[of _ ec2]) (simp add: store_t1 rf_sto6_def mkC_def)
  have t1_finish: "ec2 \<le> exec_finish (dwu_store t1)"
    by (simp add: store_t1 rf_sto6_def mkC_def)
  have arm0: "dwu_step rf_W (UArm 0 B1 ec2) t1"
    unfolding B1_def t1_def by (rule u_arm_stamped_step[OF rf_dom0 rf_crashed rf_finish])
  have arm1: "dwu_step t1 (UArm 1 B2 ec2) t2"
    unfolding B2_def t2_def by (rule u_arm_stamped_step[OF t1_dom1 t1_crashed t1_finish])
  have heal0: "dwu_step t2 (UHeal 0 ec2) t3"
    unfolding t3_def by (rule u9_heal_step[OF store_t2])
  have t3_gens0: "dwu_gens t3 0 = Some (UArmed B1)"
    by (simp add: t3_def t2_def t1_def rf_W_def mkU_def)
  have t3_fence: "dwu_fence t3 = 0"
    by (simp add: t3_def t2_def t1_def rf_W_def mkU_def)
  have fire0: "dwu_step t3 (UFire 0) t4"
    unfolding t4_def by (rule u9_fire_step0[OF t3_gens0 t3_fence])
  have pp0: "u_pair_steps_phased D 0 1 ec2 rf_W (\<lambda>g. RIdle) rf_W"
    by (rule u_pair_steps_phased.upp_refl)
  have pp1: "u_pair_steps_phased D 0 1 ec2 rf_W ((\<lambda>g. RIdle)(0 := RArmed)) t1"
    by (rule u_pair_steps_phased.upp_arm[OF pp0 _ _ arm0[unfolded B1_def]]) simp_all
  have pp2: "u_pair_steps_phased D 0 1 ec2 rf_W
               (((\<lambda>g. RIdle)(0 := RArmed))(1 := RArmed)) t2"
    by (rule u_pair_steps_phased.upp_arm[OF pp1 _ _ arm1[unfolded B2_def]]) simp_all
  have pp3: "u_pair_steps_phased D 0 1 ec2 rf_W
               ((((\<lambda>g. RIdle)(0 := RArmed))(1 := RArmed))(0 := RHealed)) t3"
    by (rule u_pair_steps_phased.upp_heal[OF pp2 _ _ heal0]) simp_all
  have pp4: "u_pair_steps_phased D 0 1 ec2 rf_W
               (((((\<lambda>g. RIdle)(0 := RArmed))(1 := RArmed))(0 := RHealed))(0 := RFired)) t4"
    by (rule u_pair_steps_phased.upp_fire[OF pp3 _ _ fire0]) simp_all
  have ext: "u_oneshot_pair_extension_phased D 0 1 ec2 rf_W t4"
    unfolding u_oneshot_pair_extension_phased_def
  proof (intro exI conjI)
    show "u_pair_steps_phased D 0 1 ec2 rf_W
            (((((\<lambda>g. RIdle)(0 := RArmed))(1 := RArmed))(0 := RHealed))(0 := RFired)) t4"
      by (rule pp4)
  qed simp_all
  have acc_t4: "dwu_accepted t4 = rf_x1 # B1"
    by (simp add: t4_def t3_def t2_def t1_def rf_W_def mkU_def)
  have store_t4: "dwu_store t4 = rf_stoH" by (simp add: t4_def t3_def)
  have floor_t4: "dwu_floor t4 = 0"
    by (simp add: t4_def t3_def t2_def t1_def rf_W_def mkU_def)
  show ?thesis
    using ext acc_t4 store_t4 floor_t4 unfolding B1_def by blast
qed

lemma u_ordered_completion_right:
  fixes D :: u_pair_chooser
  shows "\<exists>t'. u_oneshot_pair_extension_phased D 0 1 ec2 rf_W t'
            \<and> dwu_accepted t' = rf_x1 # u_stamped_batch (length (dwu_journal rf_W)) 1 (D 1 rf_W)
            \<and> dwu_store t' = rf_stoH
            \<and> dwu_floor t' = 0"
proof -
  define C2 where "C2 = u_stamped_batch (length (dwu_journal rf_W)) 1 (D 1 rf_W)"
  define s1 where "s1 = rf_W\<lparr>dwu_gens := (dwu_gens rf_W)(1 \<mapsto> UArmed C2)\<rparr>"
  define C1 where "C1 = u_stamped_batch (length (dwu_journal s1)) 0 (D 0 s1)"
  define s2 where "s2 = s1\<lparr>dwu_gens := (dwu_gens s1)(0 \<mapsto> UArmed C1)\<rparr>"
  define s3 where "s3 = s2\<lparr>dwu_store := rf_stoH\<rparr>"
  define s4 where "s4 = s3\<lparr>dwu_sent := dwu_sent s3 @ C2,
                           dwu_accepted := dwu_accepted s3 @ C2,
                           dwu_gens := (dwu_gens s3)(1 \<mapsto> UProd)\<rparr>"
  have store_s1: "dwu_store s1 = rf_sto6" by (simp add: s1_def rf_W_def mkU_def)
  have store_s2: "dwu_store s2 = rf_sto6" by (simp add: s2_def s1_def rf_W_def mkU_def)
  have s1_dom0: "0 \<in> dom (dwu_gens s1)" by (simp add: s1_def rf_W_def mkU_def)
  have s1_crashed: "\<exists>c. exec_status (dwu_store s1) = Crashed c"
    by (rule exI[of _ ec2]) (simp add: store_s1 rf_sto6_def mkC_def)
  have s1_finish: "ec2 \<le> exec_finish (dwu_store s1)"
    by (simp add: store_s1 rf_sto6_def mkC_def)
  have arm1: "dwu_step rf_W (UArm 1 C2 ec2) s1"
    unfolding C2_def s1_def by (rule u_arm_stamped_step[OF rf_dom1 rf_crashed rf_finish])
  have arm0: "dwu_step s1 (UArm 0 C1 ec2) s2"
    unfolding C1_def s2_def by (rule u_arm_stamped_step[OF s1_dom0 s1_crashed s1_finish])
  have heal1: "dwu_step s2 (UHeal 1 ec2) s3"
    unfolding s3_def by (rule u9_heal_step[OF store_s2])
  have s3_gens1: "dwu_gens s3 1 = Some (UArmed C2)"
    by (simp add: s3_def s2_def s1_def rf_W_def mkU_def)
  have s3_fence: "dwu_fence s3 = 0"
    by (simp add: s3_def s2_def s1_def rf_W_def mkU_def)
  have fire1: "dwu_step s3 (UFire 1) s4"
    unfolding s4_def by (rule u9_fire_step0[OF s3_gens1 s3_fence])
  have pp0: "u_pair_steps_phased D 0 1 ec2 rf_W (\<lambda>g. RIdle) rf_W"
    by (rule u_pair_steps_phased.upp_refl)
  have pp1: "u_pair_steps_phased D 0 1 ec2 rf_W ((\<lambda>g. RIdle)(1 := RArmed)) s1"
    by (rule u_pair_steps_phased.upp_arm[OF pp0 _ _ arm1[unfolded C2_def]]) simp_all
  have pp2: "u_pair_steps_phased D 0 1 ec2 rf_W
               (((\<lambda>g. RIdle)(1 := RArmed))(0 := RArmed)) s2"
    by (rule u_pair_steps_phased.upp_arm[OF pp1 _ _ arm0[unfolded C1_def]]) simp_all
  have pp3: "u_pair_steps_phased D 0 1 ec2 rf_W
               ((((\<lambda>g. RIdle)(1 := RArmed))(0 := RArmed))(1 := RHealed)) s3"
    by (rule u_pair_steps_phased.upp_heal[OF pp2 _ _ heal1]) simp_all
  have pp4: "u_pair_steps_phased D 0 1 ec2 rf_W
               (((((\<lambda>g. RIdle)(1 := RArmed))(0 := RArmed))(1 := RHealed))(1 := RFired)) s4"
    by (rule u_pair_steps_phased.upp_fire[OF pp3 _ _ fire1]) simp_all
  have ext: "u_oneshot_pair_extension_phased D 0 1 ec2 rf_W s4"
    unfolding u_oneshot_pair_extension_phased_def
  proof (intro exI conjI)
    show "u_pair_steps_phased D 0 1 ec2 rf_W
            (((((\<lambda>g. RIdle)(1 := RArmed))(0 := RArmed))(1 := RHealed))(1 := RFired)) s4"
      by (rule pp4)
  qed simp_all
  have acc_s4: "dwu_accepted s4 = rf_x1 # C2"
    by (simp add: s4_def s3_def s2_def s1_def rf_W_def mkU_def)
  have store_s4: "dwu_store s4 = rf_stoH" by (simp add: s4_def s3_def)
  have floor_s4: "dwu_floor s4 = 0"
    by (simp add: s4_def s3_def s2_def s1_def rf_W_def mkU_def)
  show ?thesis
    using ext acc_s4 store_s4 floor_s4 unfolding C2_def by blast
qed

subsection \<open>6.4 The ordered silent-death defeat (fallback principal)\<close>

text \<open>What the landed T,F / F,T defeat cells prove, with the order carried by the
  statement: at the landed witness (same eight verdict conjuncts), fully ordered
  one-shot pair extensions exist for EVERY chooser, and whenever the batch a member
  would arm at the crashed witness misses the owed payload, the ordered schedule in
  which that member completes and its sibling dies silently after arming LOSES.
  (This is deliberately NOT the headliner with the phased extension substituted:
  section 6.5 proves that statement is false at this witness --- the TT cell, where
  both crash-time batches carry the owed payload, is survivable once order is
  enforced, because at most one ordered member can complete.)\<close>

theorem u_ordered_silent_death_defeat:
  "\<exists>W g1 g2 f p.
     dwu_reachable_w W
   \<and> (\<exists>c. exec_status (dwu_store W) = Crashed c)
   \<and> dwu_fence W = 0
   \<and> g1 \<noteq> g2
   \<and> dwu_gens W g1 = Some UProd \<and> dwu_gens W g2 = Some UProd
   \<and> \<not> u_effect_unsafe W
   \<and> u_sink_delta f W = [p]
   \<and> (\<forall>D :: u_pair_chooser. \<exists>t'. u_oneshot_pair_extension_phased D g1 g2 f W t')
   \<and> (\<forall>D :: u_pair_chooser. \<forall>g \<in> {g1, g2}.
        p \<notin> set (log_payloads (u_stamped_batch (length (dwu_journal W)) g (D g W)))
        \<longrightarrow> (\<exists>t'. u_oneshot_pair_extension_phased D g1 g2 f W t' \<and> u_lost f t'))"
proof -
  have exist: "\<forall>D :: u_pair_chooser. \<exists>t'. u_oneshot_pair_extension_phased D 0 1 ec2 rf_W t'"
  proof (intro allI)
    fix D :: u_pair_chooser
    show "\<exists>t'. u_oneshot_pair_extension_phased D 0 1 ec2 rf_W t'"
      using u_ordered_completion_left[of D] by blast
  qed
  have cond: "\<forall>D :: u_pair_chooser. \<forall>g \<in> {0, 1}.
       (ec2, e2) \<notin> set (log_payloads (u_stamped_batch (length (dwu_journal rf_W)) g (D g rf_W)))
       \<longrightarrow> (\<exists>t'. u_oneshot_pair_extension_phased D 0 1 ec2 rf_W t' \<and> u_lost ec2 t')"
  proof (intro allI ballI impI)
    fix D :: u_pair_chooser and g :: nat
    assume gmem: "g \<in> {0, 1}"
       and miss: "(ec2, e2) \<notin> set (log_payloads (u_stamped_batch (length (dwu_journal rf_W)) g (D g rf_W)))"
    consider (L) "g = 0" | (R) "g = 1" using gmem by blast
    then show "\<exists>t'. u_oneshot_pair_extension_phased D 0 1 ec2 rf_W t' \<and> u_lost ec2 t'"
    proof cases
      case L
      with miss have m: "(ec2, e2) \<notin> set (log_payloads (u_stamped_batch (length (dwu_journal rf_W)) 0 (D 0 rf_W)))"
        by simp
      from u_ordered_completion_left[of D] obtain t' where
        ext: "u_oneshot_pair_extension_phased D 0 1 ec2 rf_W t'" and
        acc: "dwu_accepted t' = rf_x1 # u_stamped_batch (length (dwu_journal rf_W)) 0 (D 0 rf_W)" and
        sto: "dwu_store t' = rf_stoH" and flo: "dwu_floor t' = 0" by blast
      have owed: "(ec2, e2) \<in> set (replay_down_hist (retained_hist t') (exec_scope (dwu_store t')) ec2)"
        by (simp add: retained_hist_def sto flo rf_replay_stoH)
      have notin: "(ec2, e2) \<notin> set (log_payloads (dwu_accepted t'))"
        using m rf_ec12_neq by (auto simp add: acc log_payloads_x1_batch)
      have "u_lost ec2 t'" using owed notin unfolding u_lost_def by blast
      with ext show ?thesis by blast
    next
      case R
      with miss have m: "(ec2, e2) \<notin> set (log_payloads (u_stamped_batch (length (dwu_journal rf_W)) 1 (D 1 rf_W)))"
        by simp
      from u_ordered_completion_right[of D] obtain t' where
        ext: "u_oneshot_pair_extension_phased D 0 1 ec2 rf_W t'" and
        acc: "dwu_accepted t' = rf_x1 # u_stamped_batch (length (dwu_journal rf_W)) 1 (D 1 rf_W)" and
        sto: "dwu_store t' = rf_stoH" and flo: "dwu_floor t' = 0" by blast
      have owed: "(ec2, e2) \<in> set (replay_down_hist (retained_hist t') (exec_scope (dwu_store t')) ec2)"
        by (simp add: retained_hist_def sto flo rf_replay_stoH)
      have notin: "(ec2, e2) \<notin> set (log_payloads (dwu_accepted t'))"
        using m rf_ec12_neq by (auto simp add: acc log_payloads_x1_batch)
      have "u_lost ec2 t'" using owed notin unfolding u_lost_def by blast
      with ext show ?thesis by blast
    qed
  qed
  have body:
    "dwu_reachable_w rf_W
   \<and> (\<exists>c. exec_status (dwu_store rf_W) = Crashed c)
   \<and> dwu_fence rf_W = 0
   \<and> (0::nat) \<noteq> 1
   \<and> dwu_gens rf_W 0 = Some UProd \<and> dwu_gens rf_W 1 = Some UProd
   \<and> \<not> u_effect_unsafe rf_W
   \<and> u_sink_delta ec2 rf_W = [(ec2, e2)]
   \<and> (\<forall>D :: u_pair_chooser. \<exists>t'. u_oneshot_pair_extension_phased D 0 1 ec2 rf_W t')
   \<and> (\<forall>D :: u_pair_chooser. \<forall>g \<in> {0, 1}.
        (ec2, e2) \<notin> set (log_payloads (u_stamped_batch (length (dwu_journal rf_W)) g (D g rf_W)))
        \<longrightarrow> (\<exists>t'. u_oneshot_pair_extension_phased D 0 1 ec2 rf_W t' \<and> u_lost ec2 t'))"
  proof (intro conjI)
    show "dwu_reachable_w rf_W" by (rule rf_reach_W)
  next
    show "\<exists>c. exec_status (dwu_store rf_W) = Crashed c" by (rule rf_crashed)
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
    show "\<forall>D :: u_pair_chooser. \<exists>t'. u_oneshot_pair_extension_phased D 0 1 ec2 rf_W t'"
      by (rule exist)
  next
    show "\<forall>D :: u_pair_chooser. \<forall>g \<in> {0, 1}.
        (ec2, e2) \<notin> set (log_payloads (u_stamped_batch (length (dwu_journal rf_W)) g (D g rf_W)))
        \<longrightarrow> (\<exists>t'. u_oneshot_pair_extension_phased D 0 1 ec2 rf_W t' \<and> u_lost ec2 t')"
      by (rule cond)
  qed
  show ?thesis
    by (rule exI[of _ rf_W], rule exI[of _ "0::nat"], rule exI[of _ "1::nat"],
        rule exI[of _ ec2], rule exI[of _ "(ec2, e2)"]) (rule body)
qed

subsection \<open>6.5 The boundary: full ordering defeats the defeat\<close>

text \<open>Machine-step inversions for the three extension actions (each action
  constructor is produced by exactly one @{const dwu_step} rule).\<close>

lemma u_arm_step_inv:
  assumes "dwu_step t (UArm g B f) t'"
  shows "t' = t\<lparr>dwu_gens := (dwu_gens t)(g \<mapsto> UArmed B)\<rparr>"
  using assms by (cases rule: dwu_step.cases) auto

lemma u_heal_step_inv:
  assumes "dwu_step t (UHeal g f) t'"
  shows "\<exists>s'. relay_bounded_replay_reconcile (dwu_store t) f s' \<and> t' = t\<lparr>dwu_store := s'\<rparr>"
  using assms by (cases rule: dwu_step.cases) auto

lemma u_fire_step_inv:
  assumes "dwu_step t (UFire g) t'"
  shows "\<exists>B. dwu_gens t g = Some (UArmed B)
           \<and> t' = t\<lparr>dwu_sent := dwu_sent t @ B,
                    dwu_accepted := dwu_accepted t @ (if dwu_fence t \<le> g then B else []),
                    dwu_gens := (dwu_gens t)(g \<mapsto> UProd)\<rparr>"
  using assms by (cases rule: dwu_step.cases) auto

text \<open>The chooser that reads nothing and always plans the single owed payload.
  It is journal-covered at @{const rf_W} (the witness journals
  @{term "(ec2, e2)"} at stamp 2), so its batch is @{const u_justified} wherever
  it lands.\<close>

definition u_exact_chooser :: u_pair_chooser where
  "u_exact_chooser g t = [ULog (ec2, e2)]"

text \<open>Run invariant for @{const u_exact_chooser} over the PHASED grammar at
  @{const rf_W}.  The store point: the only reachable stores are @{const rf_sto6}
  (crashed) and @{const rf_stoH} (recovered); a heal forces the crashed store, so
  while the store is still @{const rf_sto6} no member is past @{text RArmed}, and
  ever after AT MOST ONE member is --- one reconcile per crash is all the machine
  admits, so a fully ordered pair degenerates to at most one completer.\<close>

lemma u_exact_chooser_run_state:
  assumes "u_pair_steps_phased u_exact_chooser 0 1 ec2 rf_W P t"
  shows "dwu_journal t = [(ec1, e1), (ec2, e2)]
       \<and> dwu_floor t = 0
       \<and> dwu_fence t = 0
       \<and> (dwu_store t = rf_sto6 \<or> dwu_store t = rf_stoH)
       \<and> (\<forall>g B. dwu_gens t g = Some (UArmed B) \<longrightarrow> B = u_stamped_batch 2 g [ULog (ec2, e2)])
       \<and> (dwu_store t = rf_sto6 \<longrightarrow> (\<forall>g. P g = RIdle \<or> P g = RArmed))
       \<and> (\<forall>g h. \<not> (P g = RIdle \<or> P g = RArmed) \<longrightarrow> \<not> (P h = RIdle \<or> P h = RArmed) \<longrightarrow> g = h)
       \<and> ((\<forall>g. P g \<noteq> RFired) \<longrightarrow> dwu_accepted t = [rf_x1])
       \<and> (\<forall>g. P g = RFired \<longrightarrow> dwu_accepted t = rf_x1 # u_stamped_batch 2 g [ULog (ec2, e2)])"
  using assms
proof (induction rule: u_pair_steps_phased.induct)
  case upp_refl
  show ?case
    by (auto simp add: rf_W_def mkU_def split: if_split_asm)
next
  case (upp_arm P t g t')
  have ihJ: "dwu_journal t = [(ec1, e1), (ec2, e2)]" and ihFl: "dwu_floor t = 0"
    and ihFe: "dwu_fence t = 0" and ihSt: "dwu_store t = rf_sto6 \<or> dwu_store t = rf_stoH"
    and ihG: "\<forall>g' B. dwu_gens t g' = Some (UArmed B) \<longrightarrow> B = u_stamped_batch 2 g' [ULog (ec2, e2)]"
    and ihLow: "dwu_store t = rf_sto6 \<longrightarrow> (\<forall>g'. P g' = RIdle \<or> P g' = RArmed)"
    and ihUniq: "\<forall>g' h. \<not> (P g' = RIdle \<or> P g' = RArmed) \<longrightarrow> \<not> (P h = RIdle \<or> P h = RArmed) \<longrightarrow> g' = h"
    and ihAcc0: "(\<forall>g'. P g' \<noteq> RFired) \<longrightarrow> dwu_accepted t = [rf_x1]"
    and ihAccF: "\<forall>g'. P g' = RFired \<longrightarrow> dwu_accepted t = rf_x1 # u_stamped_batch 2 g' [ULog (ec2, e2)]"
    using upp_arm.IH by blast+
  have t'_eq: "t' = t\<lparr>dwu_gens := (dwu_gens t)(g \<mapsto> UArmed (u_stamped_batch (length (dwu_journal t)) g (u_exact_chooser g t)))\<rparr>"
    by (rule u_arm_step_inv[OF upp_arm.hyps(4)])
  have gnew: "dwu_gens t' = (dwu_gens t)(g \<mapsto> UArmed (u_stamped_batch 2 g [ULog (ec2, e2)]))"
    by (simp add: t'_eq ihJ u_exact_chooser_def numeral_2_eq_2)
  have sameJ: "dwu_journal t' = dwu_journal t" and sameFl: "dwu_floor t' = dwu_floor t"
    and sameFe: "dwu_fence t' = dwu_fence t" and sameSt: "dwu_store t' = dwu_store t"
    and sameAcc: "dwu_accepted t' = dwu_accepted t"
    by (simp_all add: t'_eq)
  show ?case
  proof (intro conjI)
    show "dwu_journal t' = [(ec1, e1), (ec2, e2)]" by (simp add: sameJ ihJ)
  next
    show "dwu_floor t' = 0" by (simp add: sameFl ihFl)
  next
    show "dwu_fence t' = 0" by (simp add: sameFe ihFe)
  next
    show "dwu_store t' = rf_sto6 \<or> dwu_store t' = rf_stoH" using ihSt by (simp add: sameSt)
  next
    show "\<forall>g' B. dwu_gens t' g' = Some (UArmed B) \<longrightarrow> B = u_stamped_batch 2 g' [ULog (ec2, e2)]"
      using ihG by (auto simp add: gnew split: if_split_asm)
  next
    show "dwu_store t' = rf_sto6 \<longrightarrow> (\<forall>g'. (P(g := RArmed)) g' = RIdle \<or> (P(g := RArmed)) g' = RArmed)"
      using ihLow by (auto simp add: sameSt)
  next
    show "\<forall>g' h. \<not> ((P(g := RArmed)) g' = RIdle \<or> (P(g := RArmed)) g' = RArmed) \<longrightarrow>
                 \<not> ((P(g := RArmed)) h = RIdle \<or> (P(g := RArmed)) h = RArmed) \<longrightarrow> g' = h"
      using ihUniq by (auto split: if_split_asm)
  next
    show "(\<forall>g'. (P(g := RArmed)) g' \<noteq> RFired) \<longrightarrow> dwu_accepted t' = [rf_x1]"
    proof
      assume A: "\<forall>g'. (P(g := RArmed)) g' \<noteq> RFired"
      have "\<forall>g'. P g' \<noteq> RFired"
      proof
        fix g' show "P g' \<noteq> RFired"
        proof (cases "g' = g")
          case True
          with upp_arm.hyps(3) show ?thesis by simp
        next
          case False
          then show ?thesis using A[rule_format, of g'] by simp
        qed
      qed
      with ihAcc0 show "dwu_accepted t' = [rf_x1]" by (simp add: sameAcc)
    qed
  next
    show "\<forall>h. (P(g := RArmed)) h = RFired \<longrightarrow> dwu_accepted t' = rf_x1 # u_stamped_batch 2 h [ULog (ec2, e2)]"
    proof (intro allI impI)
      fix h assume hF: "(P(g := RArmed)) h = RFired"
      have hne: "h \<noteq> g" using hF by (auto simp add: fun_upd_apply)
      with hF have "P h = RFired" by simp
      with ihAccF show "dwu_accepted t' = rf_x1 # u_stamped_batch 2 h [ULog (ec2, e2)]"
        by (simp add: sameAcc)
    qed
  qed
next
  case (upp_heal P t g t')
  have ihJ: "dwu_journal t = [(ec1, e1), (ec2, e2)]" and ihFl: "dwu_floor t = 0"
    and ihFe: "dwu_fence t = 0" and ihSt: "dwu_store t = rf_sto6 \<or> dwu_store t = rf_stoH"
    and ihG: "\<forall>g' B. dwu_gens t g' = Some (UArmed B) \<longrightarrow> B = u_stamped_batch 2 g' [ULog (ec2, e2)]"
    and ihLow: "dwu_store t = rf_sto6 \<longrightarrow> (\<forall>g'. P g' = RIdle \<or> P g' = RArmed)"
    and ihAcc0: "(\<forall>g'. P g' \<noteq> RFired) \<longrightarrow> dwu_accepted t = [rf_x1]"
    using upp_heal.IH by blast+
  from u_heal_step_inv[OF upp_heal.hyps(4)] obtain s' where
    rec: "relay_bounded_replay_reconcile (dwu_store t) ec2 s'" and
    t'_eq: "t' = t\<lparr>dwu_store := s'\<rparr>"
    by blast
  have store6: "dwu_store t = rf_sto6"
  proof (cases "dwu_store t = rf_sto6")
    case True then show ?thesis .
  next
    case False
    with ihSt have h: "dwu_store t = rf_stoH" by blast
    from rec obtain c where "exec_status (dwu_store t) = Crashed c"
      unfolding relay_bounded_replay_reconcile_def by blast
    with h show ?thesis by (simp add: rf_stoH_def mkC_def)
  qed
  have s'H: "s' = rf_stoH"
  proof -
    have r6: "relay_bounded_replay_reconcile rf_sto6 ec2 s'" using rec store6 by simp
    show ?thesis
      using r6 rf_reconcile by (simp add: relay_bounded_replay_reconcile_def)
  qed
  have lowpre: "\<forall>h. P h = RIdle \<or> P h = RArmed" using ihLow store6 by blast
  have sameJ: "dwu_journal t' = dwu_journal t" and sameFl: "dwu_floor t' = dwu_floor t"
    and sameFe: "dwu_fence t' = dwu_fence t" and sameG: "dwu_gens t' = dwu_gens t"
    and sameAcc: "dwu_accepted t' = dwu_accepted t"
    by (simp_all add: t'_eq)
  have stoH: "dwu_store t' = rf_stoH" by (simp add: t'_eq s'H)
  have neq: "rf_stoH \<noteq> rf_sto6" by (simp add: rf_stoH_def rf_sto6_def mkC_def)
  show ?case
  proof (intro conjI)
    show "dwu_journal t' = [(ec1, e1), (ec2, e2)]" by (simp add: sameJ ihJ)
  next
    show "dwu_floor t' = 0" by (simp add: sameFl ihFl)
  next
    show "dwu_fence t' = 0" by (simp add: sameFe ihFe)
  next
    show "dwu_store t' = rf_sto6 \<or> dwu_store t' = rf_stoH" by (simp add: stoH)
  next
    show "\<forall>g' B. dwu_gens t' g' = Some (UArmed B) \<longrightarrow> B = u_stamped_batch 2 g' [ULog (ec2, e2)]"
      using ihG by (simp add: sameG)
  next
    show "dwu_store t' = rf_sto6 \<longrightarrow> (\<forall>g'. (P(g := RHealed)) g' = RIdle \<or> (P(g := RHealed)) g' = RArmed)"
      by (simp add: stoH neq)
  next
    show "\<forall>g' h. \<not> ((P(g := RHealed)) g' = RIdle \<or> (P(g := RHealed)) g' = RArmed) \<longrightarrow>
                 \<not> ((P(g := RHealed)) h = RIdle \<or> (P(g := RHealed)) h = RArmed) \<longrightarrow> g' = h"
      using lowpre by (auto split: if_split_asm)
  next
    show "(\<forall>g'. (P(g := RHealed)) g' \<noteq> RFired) \<longrightarrow> dwu_accepted t' = [rf_x1]"
    proof
      assume "\<forall>g'. (P(g := RHealed)) g' \<noteq> RFired"
      have "\<forall>g'. P g' \<noteq> RFired"
      proof
        fix g' show "P g' \<noteq> RFired"
          using lowpre[rule_format, of g'] by auto
      qed
      with ihAcc0 show "dwu_accepted t' = [rf_x1]" by (simp add: sameAcc)
    qed
  next
    show "\<forall>h. (P(g := RHealed)) h = RFired \<longrightarrow> dwu_accepted t' = rf_x1 # u_stamped_batch 2 h [ULog (ec2, e2)]"
    proof (intro allI impI)
      fix h assume hF: "(P(g := RHealed)) h = RFired"
      have False
      proof (cases "h = g")
        case True with hF show False by simp
      next
        case False
        with hF have PF: "P h = RFired" by simp
        have "P h = RIdle \<or> P h = RArmed" using lowpre by blast
        with PF show False by auto
      qed
      then show "dwu_accepted t' = rf_x1 # u_stamped_batch 2 h [ULog (ec2, e2)]" ..
    qed
  qed
next
  case (upp_fire P t g t')
  have ihJ: "dwu_journal t = [(ec1, e1), (ec2, e2)]" and ihFl: "dwu_floor t = 0"
    and ihFe: "dwu_fence t = 0" and ihSt: "dwu_store t = rf_sto6 \<or> dwu_store t = rf_stoH"
    and ihG: "\<forall>g' B. dwu_gens t g' = Some (UArmed B) \<longrightarrow> B = u_stamped_batch 2 g' [ULog (ec2, e2)]"
    and ihLow: "dwu_store t = rf_sto6 \<longrightarrow> (\<forall>g'. P g' = RIdle \<or> P g' = RArmed)"
    and ihUniq: "\<forall>g' h. \<not> (P g' = RIdle \<or> P g' = RArmed) \<longrightarrow> \<not> (P h = RIdle \<or> P h = RArmed) \<longrightarrow> g' = h"
    and ihAcc0: "(\<forall>g'. P g' \<noteq> RFired) \<longrightarrow> dwu_accepted t = [rf_x1]"
    using upp_fire.IH by blast+
  from u_fire_step_inv[OF upp_fire.hyps(4)] obtain B where
    gensB: "dwu_gens t g = Some (UArmed B)" and
    t'_eq: "t' = t\<lparr>dwu_sent := dwu_sent t @ B,
                   dwu_accepted := dwu_accepted t @ (if dwu_fence t \<le> g then B else []),
                   dwu_gens := (dwu_gens t)(g \<mapsto> UProd)\<rparr>"
    by blast
  have Bpin: "B = u_stamped_batch 2 g [ULog (ec2, e2)]" using ihG gensB by blast
  have healedg: "P g = RHealed" by (rule upp_fire.hyps(3))
  have glow: "\<not> (P g = RIdle \<or> P g = RArmed)" using healedg by simp
  have stoH: "dwu_store t = rf_stoH"
  proof -
    have "dwu_store t = rf_sto6 \<Longrightarrow> P g = RIdle \<or> P g = RArmed" using ihLow by blast
    with glow have "dwu_store t \<noteq> rf_sto6" by blast
    with ihSt show ?thesis by blast
  qed
  have nofired_pre: "\<forall>h. P h \<noteq> RFired"
  proof
    fix h show "P h \<noteq> RFired"
    proof
      assume hF: "P h = RFired"
      then have "\<not> (P h = RIdle \<or> P h = RArmed)" by simp
      with glow ihUniq have "h = g" by blast
      with hF healedg show False by simp
    qed
  qed
  have accpre: "dwu_accepted t = [rf_x1]" using ihAcc0 nofired_pre by blast
  have acc_t': "dwu_accepted t' = rf_x1 # u_stamped_batch 2 g [ULog (ec2, e2)]"
    by (simp add: t'_eq accpre ihFe Bpin)
  have sameJ: "dwu_journal t' = dwu_journal t" and sameFl: "dwu_floor t' = dwu_floor t"
    and sameFe: "dwu_fence t' = dwu_fence t" and sameSt: "dwu_store t' = dwu_store t"
    by (simp_all add: t'_eq)
  have neq: "rf_stoH \<noteq> rf_sto6" by (simp add: rf_stoH_def rf_sto6_def mkC_def)
  show ?case
  proof (intro conjI)
    show "dwu_journal t' = [(ec1, e1), (ec2, e2)]" by (simp add: sameJ ihJ)
  next
    show "dwu_floor t' = 0" by (simp add: sameFl ihFl)
  next
    show "dwu_fence t' = 0" by (simp add: sameFe ihFe)
  next
    show "dwu_store t' = rf_sto6 \<or> dwu_store t' = rf_stoH" by (simp add: sameSt stoH)
  next
    show "\<forall>g' B'. dwu_gens t' g' = Some (UArmed B') \<longrightarrow> B' = u_stamped_batch 2 g' [ULog (ec2, e2)]"
      using ihG by (auto simp add: t'_eq split: if_split_asm)
  next
    show "dwu_store t' = rf_sto6 \<longrightarrow> (\<forall>g'. (P(g := RFired)) g' = RIdle \<or> (P(g := RFired)) g' = RArmed)"
      by (simp add: sameSt stoH neq)
  next
    show "\<forall>g' h. \<not> ((P(g := RFired)) g' = RIdle \<or> (P(g := RFired)) g' = RArmed) \<longrightarrow>
                 \<not> ((P(g := RFired)) h = RIdle \<or> (P(g := RFired)) h = RArmed) \<longrightarrow> g' = h"
      using ihUniq glow by (auto split: if_split_asm)
  next
    show "(\<forall>g'. (P(g := RFired)) g' \<noteq> RFired) \<longrightarrow> dwu_accepted t' = [rf_x1]"
    proof
      assume A: "\<forall>g'. (P(g := RFired)) g' \<noteq> RFired"
      from A[rule_format, of g] show "dwu_accepted t' = [rf_x1]" by simp
    qed
  next
    show "\<forall>h. (P(g := RFired)) h = RFired \<longrightarrow> dwu_accepted t' = rf_x1 # u_stamped_batch 2 h [ULog (ec2, e2)]"
    proof (intro allI impI)
      fix h assume hF: "(P(g := RFired)) h = RFired"
      show "dwu_accepted t' = rf_x1 # u_stamped_batch 2 h [ULog (ec2, e2)]"
      proof (cases "h = g")
        case True
        then show ?thesis by (simp add: acc_t')
      next
        case False
        with hF have "P h = RFired" by simp
        with nofired_pre have False by blast
        then show ?thesis ..
      qed
    qed
  qed
qed

text \<open>The exactness witness: EVERY fully ordered one-shot pair extension of
  @{const u_exact_chooser} at @{const rf_W} is neither effect-unsafe nor lossy ---
  and such extensions exist, so this is no vacuity.  With
  @{thm [source] u_ordered_silent_death_defeat} this locates the headliner's
  content precisely: ordered silent-death schedules still lose whenever a
  crash-time plan misses the owed payload, but the TT duplicate cell is
  UNREACHABLE under full ordering at this machine.\<close>

theorem u_ordered_pair_exact_completion:
  "(\<exists>t'. u_oneshot_pair_extension_phased u_exact_chooser 0 1 ec2 rf_W t')
   \<and> (\<forall>t'. u_oneshot_pair_extension_phased u_exact_chooser 0 1 ec2 rf_W t'
        \<longrightarrow> \<not> u_effect_unsafe t' \<and> \<not> u_lost ec2 t')"
proof (rule conjI)
  show "\<exists>t'. u_oneshot_pair_extension_phased u_exact_chooser 0 1 ec2 rf_W t'"
    using u_ordered_completion_left[of u_exact_chooser] by blast
next
  show "\<forall>t'. u_oneshot_pair_extension_phased u_exact_chooser 0 1 ec2 rf_W t'
        \<longrightarrow> \<not> u_effect_unsafe t' \<and> \<not> u_lost ec2 t'"
  proof (intro allI impI)
    fix t'
    assume "u_oneshot_pair_extension_phased u_exact_chooser 0 1 ec2 rf_W t'"
    then obtain P where ps: "u_pair_steps_phased u_exact_chooser 0 1 ec2 rf_W P t'"
        and fired: "\<exists>g \<in> {0, 1}. P g = RFired"
      unfolding u_oneshot_pair_extension_phased_def by blast
    from fired obtain g0 where g0: "P g0 = RFired" by blast
    note inv = u_exact_chooser_run_state[OF ps]
    have accE: "dwu_accepted t' = rf_x1 # u_stamped_batch 2 g0 [ULog (ec2, e2)]"
      using inv g0 by blast
    have J: "dwu_journal t' = [(ec1, e1), (ec2, e2)]" using inv by blast
    have flo: "dwu_floor t' = 0" using inv by blast
    have sto: "dwu_store t' = rf_stoH"
    proof -
      have "dwu_store t' = rf_sto6 \<Longrightarrow> P g0 = RIdle \<or> P g0 = RArmed" using inv by blast
      with g0 have "dwu_store t' \<noteq> rf_sto6" by auto
      with inv show ?thesis by blast
    qed
    have lp: "log_payloads (dwu_accepted t') = [(ec1, e1), (ec2, e2)]"
      by (simp add: accE log_payloads_def rf_x1_def u_stamped_batch_def map_filter_simps)
    have nodup: "\<not> u_duplicate t'"
      using rf_ec12_neq by (simp add: u_duplicate_def lp)
    have jx1: "u_justified t' rf_x1"
      by (simp add: u_justified_def rf_x1_def J eval_nat_numeral)
    have jbatch: "u_justified t' \<lparr>ue_stamp = 2, ue_gen = g0, ue_pay = ULog (ec2, e2)\<rparr>"
      by (simp add: u_justified_def J eval_nat_numeral)
    have noprem: "\<not> u_premature t'"
      using jx1 jbatch by (simp add: u_premature_def accE u_stamped_batch_def)
    have nolost: "\<not> u_lost ec2 t'"
      by (simp add: u_lost_def retained_hist_def sto flo rf_replay_stoH lp)
    show "\<not> u_effect_unsafe t' \<and> \<not> u_lost ec2 t'"
      using nodup noprem nolost by (simp add: u_effect_unsafe_def)
  qed
qed

text \<open>The machine-checked obstruction: the landed headliner's defeat conjunct with
  the phase-ordered extension substituted for the loose one FAILS at the landed
  witness instantiation.  A statement carrying full per-member order cannot be the
  T6 principal at this witness; the loose final-set grammar is what the dilemma is
  ABOUT.\<close>

corollary u_ordered_dilemma_fails_at_rf_W:
  "\<not> (\<forall>D :: u_pair_chooser.
        \<exists>t'. u_oneshot_pair_extension_phased D 0 1 ec2 rf_W t'
           \<and> (u_effect_unsafe t' \<or> u_lost ec2 t'))"
  using u_ordered_pair_exact_completion by blast

end
