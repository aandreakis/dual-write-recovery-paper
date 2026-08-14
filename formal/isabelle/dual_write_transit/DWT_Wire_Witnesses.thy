(*  Title:       DWT_Wire_Witnesses.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE WITNESS BATTERY for the wire theorem of record (WP3 of the owner
    authorization DECISIONS.md D-099).  Three concrete reachable runs of the
    DISCIPLINED wire grammar (DWT_Wire's wstep --- the record grammar,
    untouched), each exercising a different adversarial axis the record
    theorem u8_multiwriter_over_wire quantifies over, each ending in an
    evaluated safety conclusion:

      dwt_witness_multiwriter        --- two writers claim at distinct epochs
        INTERLEAVED: the second claimant's fence-raise zombifies the first
        claimant's still-in-flight batch; the superseded batch is dropped at
        arrival, the current one accepted --- the payload lands exactly once.

      dwt_witness_zombie_storm       --- FOUR in-flight carriers of the same
        payload at once (the original live send, the claim re-drive, and the
        SAME superseded-generation zombie emission sent twice); the storm
        resolves by fence-drop, in-flight LOSS, fence-drop, accept --- the
        payload lands exactly once.

      dwt_witness_adversarial_reorder --- the wire reorders BEFORE and AFTER a
        claim, fully inverting delivery order vs send order; both payloads
        land exactly once but in INVERTED order vs the journal --- a positive
        safety outcome AND an honest scope illustration: acceptance ORDER is
        not part of the safety claim.

    SCOPE (binding, acceptance-ledger): every "exactly once" below is a
    concrete list/count equation on ONE reachable state's ACCEPTANCE LEDGER
    (t_accepted).  No general delivery-completeness / at-least-once claim is
    stated or implied --- these are non-vacuity witnesses for the safety
    theorem, not completeness results.  The wsend_live guard reading and the
    strictly_ascending_source premise ledger of DWT_Wire's header apply to
    every run below.
*)

theory DWT_Wire_Witnesses
  imports DWT_Wire
begin

section \<open>1. Multi-writer interleaving: two claimants at distinct epochs\<close>

text \<open>Writer 1 claims epoch 1 and its re-drive batch enters the wire.  BEFORE
  that batch arrives, writer 2 claims epoch 2: the fence rises, the delta is
  recomputed against the (still-empty) accepted record, so writer 2 re-stages
  THE SAME payload.  Both carriers are now in flight --- the classic
  multi-writer duplicate hazard.  The fence resolves it: writer 1's carrier
  arrives superseded and is DROPPED; writer 2's arrives current and is
  ACCEPTED.  Exactly once, by fencing alone.\<close>

definition mw_p1 :: "src_coord \<times> (nat, nat) source_event" where
  "mw_p1 = (ec1, Insert 0 0)"

definition mw_x11 :: "(nat, nat) uemission" where
  "mw_x11 = \<lparr> ue_stamp = 1, ue_gen = 1, ue_pay = ULog mw_p1 \<rparr>"

definition mw_x21 :: "(nat, nat) uemission" where
  "mw_x21 = \<lparr> ue_stamp = 1, ue_gen = 2, ue_pay = ULog mw_p1 \<rparr>"

definition mw0 :: "((nat, nat) uemission, (nat, nat) ujournal) tstate" where
  "mw0 = winit Map.empty"

definition mw1 where "mw1 = mw0\<lparr>t_journal := ([mw_p1], Map.empty)\<rparr>"
definition mw2 where "mw2 = mw1\<lparr>t_fence := 1, t_pending := [mw_x11]\<rparr>"
definition mw3 where "mw3 = mw2\<lparr>t_fence := 2, t_pending := [mw_x11, mw_x21]\<rparr>"
definition mw4 where "mw4 = mw3\<lparr>t_pending := [mw_x21]\<rparr>"
definition mw5 where "mw5 = mw4\<lparr>t_pending := [], t_accepted := [mw_x21]\<rparr>"

lemma mw_step01: "wstep UNIV mw0 mw1"
  by (rule wproduceI[of _ mw_p1])
     (simp_all add: mw0_def mw1_def winit_def ainit_def strictly_ascending_source_def)

lemma mw_replay: "replay_down_hist [mw_p1] (UNIV :: nat set) ec1 = [mw_p1]"
  by (simp add: replay_down_hist_def mw_p1_def)

lemma mw_step12: "wstep UNIV mw1 mw2"
proof (rule wclaimI[where g = 1 and f = ec1])
  show "t_fence mw1 < 1"
    by (simp add: mw1_def mw0_def winit_def ainit_def)
  show "[mw_x11] = stamped_at (length (fst (t_journal mw1))) 1
          (filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted mw1)))
            (replay_down_hist (fst (t_journal mw1)) UNIV ec1))"
    by (simp add: mw1_def mw0_def winit_def ainit_def mw_replay
                  log_payloads_def map_filter_simps stamped_at_def mw_x11_def)
  show "mw2 = mw1\<lparr>t_fence := 1, t_pending := t_pending mw1 @ [mw_x11]\<rparr>"
    by (simp add: mw2_def mw1_def mw0_def winit_def ainit_def)
qed

text \<open>Writer 2 claims WHILE writer 1's batch is still in flight: the accepted
  record is still empty, so the recomputed delta re-stages the same payload at
  the fresh epoch 2.\<close>

lemma mw_step23: "wstep UNIV mw2 mw3"
proof (rule wclaimI[where g = 2 and f = ec1])
  show "t_fence mw2 < 2"
    by (simp add: mw2_def mw1_def mw0_def winit_def ainit_def)
  show "[mw_x21] = stamped_at (length (fst (t_journal mw2))) 2
          (filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted mw2)))
            (replay_down_hist (fst (t_journal mw2)) UNIV ec1))"
    by (simp add: mw2_def mw1_def mw0_def winit_def ainit_def mw_replay
                  log_payloads_def map_filter_simps stamped_at_def mw_x21_def)
  show "mw3 = mw2\<lparr>t_fence := 2, t_pending := t_pending mw2 @ [mw_x21]\<rparr>"
    by (simp add: mw3_def mw2_def mw1_def mw0_def winit_def ainit_def)
qed

text \<open>Writer 1's superseded carrier arrives: generation 1 is below the fence
  (now 2), so the arrival filter DROPS it --- the acceptance ledger does not
  move.\<close>

lemma mw_step34: "wstep UNIV mw3 mw4"
  by (rule wdeliverI[of 0])
     (simp_all add: mw3_def mw4_def mw2_def mw1_def mw0_def
                    winit_def ainit_def mw_x11_def)

lemma mw_step45: "wstep UNIV mw4 mw5"
  by (rule wdeliverI[of 0])
     (simp_all add: mw4_def mw5_def mw3_def mw2_def mw1_def mw0_def
                    winit_def ainit_def mw_x21_def)

lemma mw_reach: "(wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) mw5"
proof -
  have "(wstep UNIV)\<^sup>*\<^sup>* mw0 mw5"
    using mw_step01 mw_step12 mw_step23 mw_step34 mw_step45
    by (meson converse_rtranclp_into_rtranclp r_into_rtranclp)
  then show ?thesis by (simp add: mw0_def)
qed

theorem dwt_witness_multiwriter:
  "(wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) mw5
   \<and> log_payloads (t_accepted mw5) = [mw_p1]
   \<and> t_pending mw5 = []
   \<and> \<not> a_unsafe uj upay mw5"
proof (intro conjI)
  show "(wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) mw5" by (rule mw_reach)
  show "log_payloads (t_accepted mw5) = [mw_p1]"
    by (simp add: mw5_def mw4_def mw3_def mw2_def mw1_def mw0_def
                  winit_def ainit_def mw_x21_def log_payloads_def map_filter_simps)
  show "t_pending mw5 = []" by (simp add: mw5_def)
  show "\<not> a_unsafe uj upay mw5"
    by (rule u8_multiwriter_over_wire[OF mw_reach])
qed

section \<open>2. Duplicate-zombie storm: four same-payload carriers in flight\<close>

text \<open>After the loss of the original live send is claimed around (epoch 1
  re-drive), a superseded-generation ZOMBIE emission of the same payload
  enters the wire TWICE (the sender may duplicate; the wire never does ---
  boundary K1: a duplicate SEND enters at stage).  Four carriers of one
  payload are then simultaneously in flight: the zombified original live send
  (epoch 0), the current re-drive (epoch 1), and two copies of the stale-stamp
  zombie (epoch 0).  The storm resolves: fence-drop, in-flight LOSS,
  fence-drop, ACCEPT --- the ledger holds the payload exactly once.\<close>

definition zw_p :: "src_coord \<times> (nat, nat) source_event" where
  "zw_p = (ec1, Insert 0 0)"

definition zw_live :: "(nat, nat) uemission" where
  "zw_live = \<lparr> ue_stamp = 1, ue_gen = 0, ue_pay = ULog zw_p \<rparr>"

definition zw_redrive :: "(nat, nat) uemission" where
  "zw_redrive = \<lparr> ue_stamp = 1, ue_gen = 1, ue_pay = ULog zw_p \<rparr>"

definition zw_zomb :: "(nat, nat) uemission" where
  "zw_zomb = \<lparr> ue_stamp = 0, ue_gen = 0, ue_pay = ULog zw_p \<rparr>"

definition zw0 :: "((nat, nat) uemission, (nat, nat) ujournal) tstate" where
  "zw0 = winit Map.empty"

definition zw1 where "zw1 = zw0\<lparr>t_journal := ([zw_p], Map.empty)\<rparr>"
definition zw2 where "zw2 = zw1\<lparr>t_pending := [zw_live]\<rparr>"
definition zw3 where "zw3 = zw2\<lparr>t_fence := 1, t_pending := [zw_live, zw_redrive]\<rparr>"
definition zw4 where "zw4 = zw3\<lparr>t_pending := [zw_live, zw_redrive, zw_zomb]\<rparr>"
definition zw5 where "zw5 = zw4\<lparr>t_pending := [zw_live, zw_redrive, zw_zomb, zw_zomb]\<rparr>"
definition zw6 where "zw6 = zw5\<lparr>t_pending := [zw_zomb, zw_zomb, zw_live, zw_redrive]\<rparr>"
definition zw7 where "zw7 = zw6\<lparr>t_pending := [zw_zomb, zw_live, zw_redrive]\<rparr>"
definition zw8 where "zw8 = zw7\<lparr>t_pending := [zw_live, zw_redrive]\<rparr>"
definition zw9 where "zw9 = zw8\<lparr>t_pending := [zw_redrive]\<rparr>"
definition zw10 where "zw10 = zw9\<lparr>t_pending := [], t_accepted := [zw_redrive]\<rparr>"

lemma zw_step01: "wstep UNIV zw0 zw1"
  by (rule wproduceI[of _ zw_p])
     (simp_all add: zw0_def zw1_def winit_def ainit_def strictly_ascending_source_def)

lemma zw_step12: "wstep UNIV zw1 zw2"
  by (rule wsend_liveI[of _ _ zw_p])
     (simp_all add: zw1_def zw2_def zw0_def winit_def ainit_def a_eligible_def
                    zw_live_def log_payloads_def map_filter_simps)

lemma zw_replay: "replay_down_hist [zw_p] (UNIV :: nat set) ec1 = [zw_p]"
  by (simp add: replay_down_hist_def zw_p_def)

lemma zw_step23: "wstep UNIV zw2 zw3"
proof (rule wclaimI[where g = 1 and f = ec1])
  show "t_fence zw2 < 1"
    by (simp add: zw2_def zw1_def zw0_def winit_def ainit_def)
  show "[zw_redrive] = stamped_at (length (fst (t_journal zw2))) 1
          (filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted zw2)))
            (replay_down_hist (fst (t_journal zw2)) UNIV ec1))"
    by (simp add: zw2_def zw1_def zw0_def winit_def ainit_def zw_replay
                  log_payloads_def map_filter_simps stamped_at_def zw_redrive_def)
  show "zw3 = zw2\<lparr>t_fence := 1, t_pending := t_pending zw2 @ [zw_redrive]\<rparr>"
    by (simp add: zw3_def zw2_def zw1_def zw0_def winit_def ainit_def)
qed

text \<open>The same zombie emission enters the wire twice --- guard-free, any
  stamp, any payload, as long as its generation sits below the fence.\<close>

lemma zw_step34: "wstep UNIV zw3 zw4"
  by (rule wsend_zombieI[of zw_zomb])
     (simp_all add: zw3_def zw4_def zw2_def zw1_def zw0_def
                    winit_def ainit_def zw_zomb_def)

lemma zw_step45: "wstep UNIV zw4 zw5"
  by (rule wsend_zombieI[of zw_zomb])
     (simp_all add: zw4_def zw5_def zw3_def zw2_def zw1_def zw0_def
                    winit_def ainit_def zw_zomb_def)

lemma zw_step56: "wstep UNIV zw5 zw6"
proof (rule wstep.wreorder[of "[zw_zomb, zw_zomb, zw_live, zw_redrive]", THEN wstep_state_cong])
  show "mset [zw_zomb, zw_zomb, zw_live, zw_redrive] = mset (t_pending zw5)"
    by (simp add: zw5_def zw4_def zw3_def zw2_def zw1_def zw0_def winit_def ainit_def)
  show "zw5\<lparr>t_pending := [zw_zomb, zw_zomb, zw_live, zw_redrive]\<rparr> = zw6"
    by (simp add: zw6_def zw5_def zw4_def zw3_def zw2_def zw1_def zw0_def
                  winit_def ainit_def)
qed

lemma zw_step67: "wstep UNIV zw6 zw7"
  by (rule wdeliverI[of 0])
     (simp_all add: zw6_def zw7_def zw5_def zw4_def zw3_def zw2_def zw1_def zw0_def
                    winit_def ainit_def zw_zomb_def)

text \<open>The second zombie copy is LOST in flight --- loss inside the storm.\<close>

lemma zw_step78: "wstep UNIV zw7 zw8"
  by (rule wloseI[of 0])
     (simp_all add: zw7_def zw8_def zw6_def zw5_def zw4_def zw3_def zw2_def zw1_def
                    zw0_def winit_def ainit_def)

lemma zw_step89: "wstep UNIV zw8 zw9"
  by (rule wdeliverI[of 0])
     (simp_all add: zw8_def zw9_def zw7_def zw6_def zw5_def zw4_def zw3_def zw2_def
                    zw1_def zw0_def winit_def ainit_def zw_live_def)

lemma zw_step910: "wstep UNIV zw9 zw10"
  by (rule wdeliverI[of 0])
     (simp_all add: zw9_def zw10_def zw8_def zw7_def zw6_def zw5_def zw4_def zw3_def
                    zw2_def zw1_def zw0_def winit_def ainit_def zw_redrive_def)

lemma zw_reach: "(wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) zw10"
proof -
  have "(wstep UNIV)\<^sup>*\<^sup>* zw0 zw10"
    using zw_step01 zw_step12 zw_step23 zw_step34 zw_step45 zw_step56 zw_step67
          zw_step78 zw_step89 zw_step910
    by (meson converse_rtranclp_into_rtranclp r_into_rtranclp)
  then show ?thesis by (simp add: zw0_def)
qed

theorem dwt_witness_zombie_storm:
  "(wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) zw10
   \<and> log_payloads (t_accepted zw10) = [zw_p]
   \<and> t_pending zw10 = []
   \<and> \<not> a_unsafe uj upay zw10"
proof (intro conjI)
  show "(wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) zw10" by (rule zw_reach)
  show "log_payloads (t_accepted zw10) = [zw_p]"
    by (simp add: zw10_def zw9_def zw8_def zw7_def zw6_def zw5_def zw4_def zw3_def
                  zw2_def zw1_def zw0_def winit_def ainit_def zw_redrive_def
                  log_payloads_def map_filter_simps)
  show "t_pending zw10 = []" by (simp add: zw10_def)
  show "\<not> a_unsafe uj upay zw10"
    by (rule u8_multiwriter_over_wire[OF zw_reach])
qed

section \<open>3. Adversarial reorder: inversion before AND after a claim\<close>

text \<open>Two source events; both sent live; the wire inverts the two live sends
  BEFORE the claim; the claim (epoch 1) re-stages both payloads (the accepted
  record is still empty); the wire then fully inverts all four in-flight items
  AFTER the claim.  Delivery consumes the inverted order: the re-driven
  carriers arrive first (both ACCEPTED --- in inverted order vs the journal),
  the two original live sends arrive superseded and are DROPPED.

  HONEST SCOPE ILLUSTRATION: the final ledger is @{term "[ar_p2, ar_p1]"} ---
  each payload exactly once, but in INVERTED order vs the journal
  @{term "[ar_p1, ar_p2]"}.  The record theorem claims payload-distinctness
  and justification of the ACCEPTANCE LEDGER; acceptance ORDER is NOT part of
  the claim, and this witness evaluates that boundary concretely.\<close>

definition ar_p1 :: "src_coord \<times> (nat, nat) source_event" where
  "ar_p1 = (ec1, Insert 0 0)"

definition ar_p2 :: "src_coord \<times> (nat, nat) source_event" where
  "ar_p2 = (ec2, Insert 1 1)"

definition ar_x1 :: "(nat, nat) uemission" where
  "ar_x1 = \<lparr> ue_stamp = 2, ue_gen = 0, ue_pay = ULog ar_p1 \<rparr>"

definition ar_y1 :: "(nat, nat) uemission" where
  "ar_y1 = \<lparr> ue_stamp = 2, ue_gen = 0, ue_pay = ULog ar_p2 \<rparr>"

definition ar_x2 :: "(nat, nat) uemission" where
  "ar_x2 = \<lparr> ue_stamp = 2, ue_gen = 1, ue_pay = ULog ar_p1 \<rparr>"

definition ar_y2 :: "(nat, nat) uemission" where
  "ar_y2 = \<lparr> ue_stamp = 2, ue_gen = 1, ue_pay = ULog ar_p2 \<rparr>"

definition ar0 :: "((nat, nat) uemission, (nat, nat) ujournal) tstate" where
  "ar0 = winit Map.empty"

definition ar1 where "ar1 = ar0\<lparr>t_journal := ([ar_p1], Map.empty)\<rparr>"
definition ar2 where "ar2 = ar1\<lparr>t_journal := ([ar_p1, ar_p2], Map.empty)\<rparr>"
definition ar3 where "ar3 = ar2\<lparr>t_pending := [ar_x1]\<rparr>"
definition ar4 where "ar4 = ar3\<lparr>t_pending := [ar_x1, ar_y1]\<rparr>"
definition ar5 where "ar5 = ar4\<lparr>t_pending := [ar_y1, ar_x1]\<rparr>"
definition ar6 where "ar6 = ar5\<lparr>t_fence := 1, t_pending := [ar_y1, ar_x1, ar_x2, ar_y2]\<rparr>"
definition ar7 where "ar7 = ar6\<lparr>t_pending := [ar_y2, ar_x2, ar_y1, ar_x1]\<rparr>"
definition ar8 where "ar8 = ar7\<lparr>t_pending := [ar_x2, ar_y1, ar_x1], t_accepted := [ar_y2]\<rparr>"
definition ar9 where "ar9 = ar8\<lparr>t_pending := [ar_y1, ar_x1], t_accepted := [ar_y2, ar_x2]\<rparr>"
definition ar10 where "ar10 = ar9\<lparr>t_pending := [ar_x1]\<rparr>"
definition ar11 where "ar11 = ar10\<lparr>t_pending := []\<rparr>"

lemma ar_step01: "wstep UNIV ar0 ar1"
  by (rule wproduceI[of _ ar_p1])
     (simp_all add: ar0_def ar1_def winit_def ainit_def strictly_ascending_source_def)

text \<open>The second commit is strictly above the first (@{term "ec1 < ec2"}) ---
  the ascending premise in guard form, discharged concretely.\<close>

lemma ar_step12: "wstep UNIV ar1 ar2"
  by (rule wproduceI[of _ ar_p2])
     (simp_all add: ar1_def ar2_def ar0_def winit_def ainit_def
                    strictly_ascending_source_def ar_p1_def ar_p2_def ec_defs)

lemma ar_step23: "wstep UNIV ar2 ar3"
  by (rule wsend_liveI[of _ _ ar_p1])
     (simp_all add: ar2_def ar3_def ar1_def ar0_def winit_def ainit_def a_eligible_def
                    ar_x1_def ar_p1_def ar_p2_def log_payloads_def map_filter_simps)

text \<open>The second live send's eligible-freshness guard sees the first live
  send in flight --- distinct payloads, so the send is admitted.\<close>

lemma ar_step34: "wstep UNIV ar3 ar4"
  by (rule wsend_liveI[of _ _ ar_p2])
     (simp_all add: ar3_def ar4_def ar2_def ar1_def ar0_def winit_def ainit_def
                    a_eligible_def ar_x1_def ar_y1_def ar_p1_def ar_p2_def ec_defs
                    log_payloads_def map_filter_simps)

text \<open>Reorder BEFORE the claim: the two live sends swap.\<close>

lemma ar_step45: "wstep UNIV ar4 ar5"
proof (rule wstep.wreorder[of "[ar_y1, ar_x1]", THEN wstep_state_cong])
  show "mset [ar_y1, ar_x1] = mset (t_pending ar4)"
    by (simp add: ar4_def ar3_def ar2_def ar1_def ar0_def winit_def ainit_def
                  add_mset_commute)
  show "ar4\<lparr>t_pending := [ar_y1, ar_x1]\<rparr> = ar5"
    by (simp add: ar5_def ar4_def ar3_def ar2_def ar1_def ar0_def winit_def ainit_def)
qed

lemma ar_replay: "replay_down_hist [ar_p1, ar_p2] (UNIV :: nat set) ec2 = [ar_p1, ar_p2]"
  by (simp add: replay_down_hist_def ar_p1_def ar_p2_def ec_defs)

lemma ar_step56: "wstep UNIV ar5 ar6"
proof (rule wclaimI[where g = 1 and f = ec2])
  show "t_fence ar5 < 1"
    by (simp add: ar5_def ar4_def ar3_def ar2_def ar1_def ar0_def winit_def ainit_def)
  show "[ar_x2, ar_y2] = stamped_at (length (fst (t_journal ar5))) 1
          (filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted ar5)))
            (replay_down_hist (fst (t_journal ar5)) UNIV ec2))"
    by (simp add: ar5_def ar4_def ar3_def ar2_def ar1_def ar0_def winit_def ainit_def
                  ar_replay log_payloads_def map_filter_simps stamped_at_def
                  ar_x2_def ar_y2_def)
  show "ar6 = ar5\<lparr>t_fence := 1, t_pending := t_pending ar5 @ [ar_x2, ar_y2]\<rparr>"
    by (simp add: ar6_def ar5_def ar4_def ar3_def ar2_def ar1_def ar0_def
                  winit_def ainit_def)
qed

text \<open>Reorder AFTER the claim: full inversion of the four in-flight items ---
  the re-driven carriers overtake the zombified live sends.\<close>

lemma ar_step67: "wstep UNIV ar6 ar7"
proof (rule wstep.wreorder[of "[ar_y2, ar_x2, ar_y1, ar_x1]", THEN wstep_state_cong])
  show "mset [ar_y2, ar_x2, ar_y1, ar_x1] = mset (t_pending ar6)"
    by (simp add: ar6_def ar5_def ar4_def ar3_def ar2_def ar1_def ar0_def
                  winit_def ainit_def)
  show "ar6\<lparr>t_pending := [ar_y2, ar_x2, ar_y1, ar_x1]\<rparr> = ar7"
    by (simp add: ar7_def ar6_def ar5_def ar4_def ar3_def ar2_def ar1_def ar0_def
                  winit_def ainit_def)
qed

lemma ar_step78: "wstep UNIV ar7 ar8"
  by (rule wdeliverI[of 0])
     (simp_all add: ar7_def ar8_def ar6_def ar5_def ar4_def ar3_def ar2_def ar1_def
                    ar0_def winit_def ainit_def ar_y2_def)

lemma ar_step89: "wstep UNIV ar8 ar9"
  by (rule wdeliverI[of 0])
     (simp_all add: ar8_def ar9_def ar7_def ar6_def ar5_def ar4_def ar3_def ar2_def
                    ar1_def ar0_def winit_def ainit_def ar_x2_def)

lemma ar_step910: "wstep UNIV ar9 ar10"
  by (rule wdeliverI[of 0])
     (simp_all add: ar9_def ar10_def ar8_def ar7_def ar6_def ar5_def ar4_def ar3_def
                    ar2_def ar1_def ar0_def winit_def ainit_def ar_y1_def)

lemma ar_step1011: "wstep UNIV ar10 ar11"
  by (rule wdeliverI[of 0])
     (simp_all add: ar10_def ar11_def ar9_def ar8_def ar7_def ar6_def ar5_def ar4_def
                    ar3_def ar2_def ar1_def ar0_def winit_def ainit_def ar_x1_def)

lemma ar_reach: "(wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) ar11"
proof -
  have "(wstep UNIV)\<^sup>*\<^sup>* ar0 ar11"
    using ar_step01 ar_step12 ar_step23 ar_step34 ar_step45 ar_step56 ar_step67
          ar_step78 ar_step89 ar_step910 ar_step1011
    by (meson converse_rtranclp_into_rtranclp r_into_rtranclp)
  then show ?thesis by (simp add: ar0_def)
qed

theorem dwt_witness_adversarial_reorder:
  "(wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) ar11
   \<and> log_payloads (t_accepted ar11) = [ar_p2, ar_p1]
   \<and> fst (t_journal ar11) = [ar_p1, ar_p2]
   \<and> t_pending ar11 = []
   \<and> \<not> a_unsafe uj upay ar11"
proof (intro conjI)
  show "(wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) ar11" by (rule ar_reach)
  show "log_payloads (t_accepted ar11) = [ar_p2, ar_p1]"
    by (simp add: ar11_def ar10_def ar9_def ar8_def ar7_def ar6_def ar5_def ar4_def
                  ar3_def ar2_def ar1_def ar0_def winit_def ainit_def
                  ar_x2_def ar_y2_def log_payloads_def map_filter_simps)
  show "fst (t_journal ar11) = [ar_p1, ar_p2]"
    by (simp add: ar11_def ar10_def ar9_def ar8_def ar7_def ar6_def ar5_def ar4_def
                  ar3_def ar2_def ar1_def ar0_def winit_def ainit_def)
  show "t_pending ar11 = []" by (simp add: ar11_def)
  show "\<not> a_unsafe uj upay ar11"
    by (rule u8_multiwriter_over_wire[OF ar_reach])
qed

end
