(*  Title:       DWU_Fenced_Discipline.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Purpose: Road-2 I3 --- U8 (THE POSSIBILITY HEADLINER, both halves) + the U11
             control block, on the landed unified machine (DWU_Machine).

    "Claim-fenced recovery is effect-safe under zombies, concurrent claimants, and
     late fires; every claim the fence lets complete lands exactly-once at its own
     frontier, provided the arm-to-fire window commits above it."

    SCOPE DISCLOSURE (journal grade).  The exactly-once verdict above is
    retained-suffix-relative: u_exactly_once_at grades delivery coverage against
    retained_hist, the source history above dwu_floor.  Because URetain is
    guard-free in this machine, a disciplined run can retain away a committed,
    never-delivered obligation and still satisfy the headline while the
    journal-graded loss predicate u_lost_journal holds at the same endpoint (the
    truncation/retention axis is DWU_Truncation's subject).  The journal-grade
    forms --- the permanent-source coincidence and the retention-sound bridge,
    with the divergence run banked as a control --- live in DWU_Journal_Grade.

    Two sharper window facts hold CONDITIONALLY --- for a claim that is still AT
    the fence, which is the headline theorem's own pre-fire premise
    (dwu_fence tj <= g): while an armed batch is fence-eligible, the D1b guard
    quiesces ordinary publishes and cursor triples; and no bare UHeal production
    exists (UHeal occurs only inside the fused cursor triple), so such a window
    contains no store reconcile.  Neither fact is unconditional over
    u_disciplined_trace: ud_claim and ud_fire carry no D1b guard, and a second
    UArmF at a higher generation raises the fence past the first claim's slot,
    after which publishes and cursor triples are re-admitted inside the first
    claim's window --- that first claim's own fire then fails the headline's
    fence premise, so no theorem statement is affected.

    The amended discipline grammar (u_disciplined_trace) is an inductive restriction
    of dwu_temporal_trace (scheduler-only; no new transitions).  Two principals:

      (A) u_fenced_multiwriter_discipline_safe  --- SAFETY, ported from the timeboxed
          U8 spike: a strengthened invariant u_disc_inv (C1..C5, C4 load-bearing)
          implying (not u_effect_unsafe) and preserved per rule (11-case induction).

      (B) u_exactly_once_at_completed_claim + u_at_least_once_persists_fresh_suffix
          --- the COMPLETED-CLAIM half.  Exactly-once = (not unsafe) AND at-least-once;
          the safety conjunct is (A) at the post-fire prefix state; the at-least-once
          conjunct is the index-pair bookkeeping: the UArmF at i arms the sink-delta
          covering f's owed set, window-freshness keeps that owed set from growing,
          completed-at-the-fence (fence <= g at the pre-fire state) makes the fire's
          batch ACCEPTED, so the owed set is covered at post-j.

      (C) u_fence_at_release_unsound + u_claim_without_read_unsound
          + u_zombie_expressibility  --- the U11 controls (concrete witness runs).

    Statements are byte-identical to the Stage-4 seed
    (ref/road2_clean_slate/probe/DWU_Statement_Probe.thy, sections U8 and U11).

    D1b is FORCED (the spike confirmed it load-bearing by concrete proof): the
    5-guard discipline is honestly disclosed, not simplified away.

    Honesty regime: quick_and_dirty = false (ROOT-pinned), ZERO sorry, ZERO
    standalone oops, no axiomatization, no consts, no oracles.  Every principal PROVED.
*)

theory DWU_Fenced_Discipline
  imports DWU_Recovery_Rows DWU_Recovery_Floor
begin

section \<open>1. The amended discipline grammar (seed \<open>\<section>\<close>1.9, VERBATIM)\<close>

text \<open>@{text u_disciplined_trace}: an inductive restriction of @{const dwu_temporal_trace}
  (scheduler-only; no new transitions).  Guard table (P3): landed 3 (D1a publish
  justification+freshness; D2-cursor distinct+fresh) + multi-writer tax (D1b
  fence-eligibility quiesce, D2 claim/triple shape, D3-claim distinctness) + modality
  (D4 journal-prefix snap honesty) + scope/hygiene (D5/D6: no UTruncCrash, no
  UFenceRaise, no bare UArm or UHeal --- both occur only inside the fused cursor
  triple UArm-UHeal-UFire).  URetain and UPubLost
  admitted guard-free; zombies and late fires allowed (UFire guard-free).\<close>

inductive u_disciplined_trace
  :: "('k, 'v) dwu_state \<Rightarrow> ('k, 'v) dwu_action list \<Rightarrow> ('k, 'v) dwu_state \<Rightarrow> bool"
where
  ud_refl:
    "u_disciplined_trace t [] t"
| ud_nonpub:
    "\<lbrakk>wellformed_exec_state (dwu_store t);
      exec_label_preserves_history_wf (dwu_store t) a;
      \<forall>c e. a \<noteq> DoDownstream c e;
      dwu_step t (ULift g a) t';
      u_disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     u_disciplined_trace t (ULift g a # as) t''"
| ud_publish:
    "\<lbrakk>wellformed_exec_state (dwu_store t);
      exec_label_preserves_history_wf (dwu_store t) (DoDownstream c e);
      (c, e) \<in> set (exec_src_hist (dwu_store t));
      (c, e) \<notin> set (log_payloads (dwu_accepted t));
      \<forall>g' B. dwu_gens t g' = Some (UArmed B) \<longrightarrow> g' < dwu_fence t;
      dwu_step t (ULift g (DoDownstream c e)) t';
      u_disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     u_disciplined_trace t (ULift g (DoDownstream c e) # as) t''"
| ud_publost:
    "\<lbrakk>wellformed_exec_state (dwu_store t);
      exec_label_preserves_history_wf (dwu_store t) (DoDownstream c e);
      dwu_step t (UPubLost g c e) t';
      u_disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     u_disciplined_trace t (UPubLost g c e # as) t''"
| ud_snap:
    "\<lbrakk>v = Src (exec_base (dwu_store t)) (take (length (dwu_journal t)) (dwu_journal t)) c k;
      dwu_step t (USnapE g c k v) t';
      u_disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     u_disciplined_trace t (USnapE g c k v # as) t''"
| ud_spawn:
    "\<lbrakk>dwu_step t USpawn t'; u_disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     u_disciplined_trace t (USpawn # as) t''"
| ud_release:
    "\<lbrakk>dwu_step t (URelease g) t'; u_disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     u_disciplined_trace t (URelease g # as) t''"
| ud_claim:
    "\<lbrakk>distinct (log_payloads (stamped_at (length (dwu_journal t)) g (u_sink_delta f t)));
      dwu_step t (UArmF g f) t';
      u_disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     u_disciplined_trace t (UArmF g f # as) t''"
| ud_fire:
    "\<lbrakk>dwu_step t (UFire g) t'; u_disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     u_disciplined_trace t (UFire g # as) t''"
| ud_retain:
    "\<lbrakk>dwu_step t (URetain n) t'; u_disciplined_trace t' as t''\<rbrakk> \<Longrightarrow>
     u_disciplined_trace t (URetain n # as) t''"
| ud_cursor_recovery:
    "\<lbrakk>R = replay_down_hist (retained_hist t) (exec_scope (dwu_store t)) f;
      m \<le> length R;
      distinct (drop m R);
      set (drop m R) \<inter> set (log_payloads (dwu_accepted t)) = {};
      \<forall>g' B'. dwu_gens t g' = Some (UArmed B') \<longrightarrow> g' < dwu_fence t;
      B = stamped_at (length (dwu_journal t)) g (drop m R);
      dwu_step t (UArm g B f) t1;
      dwu_step t1 (UHeal g f) t2;
      dwu_step t2 (UFire g) t3;
      u_disciplined_trace t3 as t''\<rbrakk> \<Longrightarrow>
     u_disciplined_trace t (UArm g B f # UHeal g f # UFire g # as) t''"

definition u_claim_of
  :: "('k, 'v) dwu_action list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> frontier \<Rightarrow> bool"
where
  "u_claim_of acts i j g f \<longleftrightarrow>
     i < j \<and> j < length acts
   \<and> acts ! i = UArmF g f \<and> acts ! j = UFire g
   \<and> (\<forall>n. i < n \<and> n < j \<longrightarrow>
        acts ! n \<noteq> UFire g \<and> (\<forall>f'. acts ! n \<noteq> UArmF g f'))"

definition u_window_fresh
  :: "('k, 'v) dwu_action list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> frontier \<Rightarrow> bool"
where
  "u_window_fresh acts i j f \<longleftrightarrow>
     (\<forall>n g' c e. i < n \<and> n < j \<and> acts ! n = ULift g' (DoSource c e) \<longrightarrow> \<not> src_le c f)"


section \<open>2. The strengthened invariant (ported from the U8 spike)\<close>

text \<open>Five conjuncts (P3 \<open>\<section>\<close>3 map).  C1 acc_just + C2 acc_dist give
  @{text "\<not> u_effect_unsafe"} directly.  C3 src_perm (no truncation inside a disciplined
  trace) transfers the publish guard @{text "(c,e) \<in> exec_src_hist"} to
  journal-justification.  C4 arm_below_fence + functionality of @{const dwu_gens} give
  "at most one FENCE-ELIGIBLE armed batch".  C5 arm_coherent (distinct \<and>
  disjoint-from-accepted \<and> justified), restricted to fence-eligible batches --- the
  sub-fence ones fire nothing so are harmless.\<close>

definition u_disc_inv :: "('k, 'v) dwu_state \<Rightarrow> bool" where
  "u_disc_inv t \<longleftrightarrow>
     (\<forall>x \<in> set (dwu_accepted t). u_justified t x)                              \<comment> \<open>C1 acc_just\<close>
   \<and> distinct (log_payloads (dwu_accepted t))                                  \<comment> \<open>C2 acc_dist\<close>
   \<and> dwu_journal t = exec_src_hist (dwu_store t)                               \<comment> \<open>C3 src_perm\<close>
   \<and> (\<forall>g B. dwu_gens t g = Some (UArmed B) \<longrightarrow> g \<le> dwu_fence t)                 \<comment> \<open>C4 arm_below_fence\<close>
   \<and> (\<forall>g B. dwu_gens t g = Some (UArmed B) \<longrightarrow> dwu_fence t \<le> g \<longrightarrow>              \<comment> \<open>C5 arm_coherent\<close>
        distinct (log_payloads B)
      \<and> set (log_payloads B) \<inter> set (log_payloads (dwu_accepted t)) = {}
      \<and> (\<forall>x \<in> set B. u_justified t x))"

lemma u_disc_invD:
  assumes "u_disc_inv t"
  shows "\<forall>x \<in> set (dwu_accepted t). u_justified t x"
    and "distinct (log_payloads (dwu_accepted t))"
    and "dwu_journal t = exec_src_hist (dwu_store t)"
    and "\<And>g B. dwu_gens t g = Some (UArmed B) \<Longrightarrow> g \<le> dwu_fence t"
    and "\<And>g B. dwu_gens t g = Some (UArmed B) \<Longrightarrow> dwu_fence t \<le> g \<Longrightarrow>
          distinct (log_payloads B)
        \<and> set (log_payloads B) \<inter> set (log_payloads (dwu_accepted t)) = {}
        \<and> (\<forall>x \<in> set B. u_justified t x)"
  using assms by (auto simp: u_disc_inv_def)

text \<open>C1 + C2 discharge the safety half cleanly.\<close>

lemma u_disc_inv_safe: "u_disc_inv t \<Longrightarrow> \<not> u_effect_unsafe t"
  by (auto simp: u_disc_inv_def u_effect_unsafe_def u_premature_def u_duplicate_def)

lemma u_disc_inv_init: "u_disc_inv (dwu_init b K fin)"
  by (auto simp: u_disc_inv_def dwu_init_def initial_exec_state_def
                 log_payloads_def map_filter_simps)


subsection \<open>2.1 Hand-off support bank (justification persistence + batch facts)\<close>

text \<open>Justification is monotone: once justified, a journal-append + base-freeze keeps it.\<close>

lemma u_justified_persist:
  assumes "u_justified t x"
      and "\<exists>js. dwu_journal t' = dwu_journal t @ js"
      and "exec_base (dwu_store t') = exec_base (dwu_store t)"
  shows "u_justified t' x"
proof -
  from assms(2) obtain js where js: "dwu_journal t' = dwu_journal t @ js" ..
  from assms(1) have stamp: "ue_stamp x \<le> length (dwu_journal t)"
    by (simp add: u_justified_def)
  have take_eq: "take (ue_stamp x) (dwu_journal t') = take (ue_stamp x) (dwu_journal t)"
    unfolding js using stamp by simp
  from stamp js have len: "ue_stamp x \<le> length (dwu_journal t')" by simp
  from assms(1) show ?thesis
    by (auto simp: u_justified_def take_eq len assms(3) split: upayload.splits)
qed

text \<open>Every element of a ULog batch @{text "stamped_at (length journal) g ps"} whose payloads
  live in the journal is justified.\<close>

lemma u_justified_stamped_batch:
  assumes "x \<in> set (stamped_at (length (dwu_journal t)) g ps)"
      and "set ps \<subseteq> set (dwu_journal t)"
  shows "u_justified t x"
  using assms by (auto simp: stamped_at_def u_justified_def)

lemma log_payloads_single_ulog:
  "log_payloads [\<lparr> ue_stamp = n, ue_gen = g, ue_pay = ULog p \<rparr>] = [p]"
  by (simp add: log_payloads_def map_filter_simps)

text \<open>The replay/retained subset chain (used to journal-justify the arm batch payloads).\<close>

lemma replay_subset: "set (replay_down_hist H K f) \<subseteq> set H"
  by (auto simp: replay_down_hist_def)

lemma retained_subset:
  "set (retained_hist t) \<subseteq> set (exec_src_hist (dwu_store t))"
  by (auto simp: retained_hist_def set_drop_subset)

text \<open>Non-production labels contribute nothing to the source history.\<close>

lemma src_hist_of_labels_nonprod:
  "\<not> u_production_label a \<Longrightarrow> src_hist_of_labels [a] = []"
  by (cases a) auto

text \<open>For a non-DoDownstream ULift step: accepted / gens / fence are frozen, journal and
  source history grow identically, and base is frozen.  Consumed by the ud_nonpub case.\<close>

lemma dwu_lift_nonpub_shape:
  assumes step: "dwu_step t (ULift g a) t'"
      and notpub: "\<forall>c e. a \<noteq> DoDownstream c e"
  shows "dwu_accepted t' = dwu_accepted t
       \<and> dwu_gens t' = dwu_gens t
       \<and> dwu_fence t' = dwu_fence t
       \<and> dwu_journal t' = dwu_journal t @ src_hist_of_labels [a]
       \<and> exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t) @ src_hist_of_labels [a]
       \<and> exec_base (dwu_store t') = exec_base (dwu_store t)"
  using step notpub
  by (cases rule: dwu_step.cases)
     (auto simp: src_hist_of_labels_nonprod dest: dw_exec_step_src_hist dw_exec_step_base)


subsection \<open>2.2 Step inversion helpers (the fused-triple inversions)\<close>

lemma dwu_step_fire_full:
  assumes "dwu_step t (UFire g) t'"
  shows "\<exists>B. dwu_gens t g = Some (UArmed B)
       \<and> dwu_accepted t' = dwu_accepted t @ (if dwu_fence t \<le> g then B else [])
       \<and> dwu_gens t' = (dwu_gens t)(g \<mapsto> UProd)
       \<and> dwu_journal t' = dwu_journal t
       \<and> dwu_fence t' = dwu_fence t
       \<and> dwu_store t' = dwu_store t"
  using assms by (cases rule: dwu_step.cases) auto

lemma dwu_step_publish_full:
  assumes "dwu_step t (ULift g (DoDownstream c e)) t'"
  shows "\<exists>s'. dw_exec_step (dwu_store t) (DoDownstream c e) s'
       \<and> dwu_store t' = s'
       \<and> dwu_journal t' = dwu_journal t
       \<and> dwu_gens t' = dwu_gens t
       \<and> dwu_fence t' = dwu_fence t
       \<and> dwu_accepted t' = dwu_accepted t
            @ (if dwu_fence t \<le> g
               then [\<lparr> ue_stamp = length (dwu_journal t), ue_gen = g, ue_pay = ULog (c, e) \<rparr>]
               else [])"
  using assms by (cases rule: dwu_step.cases) auto

lemma dwu_step_heal_src_base:
  assumes "dwu_step t (UHeal g f) t'"
  shows "exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t)
       \<and> exec_base (dwu_store t') = exec_base (dwu_store t)"
  using assms by (cases rule: dwu_step.cases) (auto dest: dwu_relay_reconcile_frame)

lemma dwu_step_publost_full:
  assumes "dwu_step t (UPubLost g c e) t'"
  shows "\<exists>s'. dw_exec_step (dwu_store t) (DoDownstream c e) s'
       \<and> dwu_store t' = s' \<and> dwu_journal t' = dwu_journal t
       \<and> dwu_gens t' = dwu_gens t \<and> dwu_fence t' = dwu_fence t
       \<and> dwu_accepted t' = dwu_accepted t"
  using assms by (cases rule: dwu_step.cases) auto

lemma dwu_step_snap_full:
  assumes "dwu_step t (USnapE g c k v) t'"
  shows "dwu_store t' = dwu_store t \<and> dwu_journal t' = dwu_journal t
       \<and> dwu_gens t' = dwu_gens t \<and> dwu_fence t' = dwu_fence t
       \<and> dwu_accepted t' = dwu_accepted t
            @ (if dwu_fence t \<le> g
               then [\<lparr> ue_stamp = length (dwu_journal t), ue_gen = g, ue_pay = USnap c k v \<rparr>]
               else [])"
  using assms by (cases rule: dwu_step.cases) auto

lemma dwu_step_release_src_base:
  assumes "dwu_step t (URelease g) t'"
  shows "exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t)
       \<and> exec_base (dwu_store t') = exec_base (dwu_store t)"
  using assms by (cases rule: dwu_step.cases) auto

lemma dwu_step_retain_full:
  assumes "dwu_step t (URetain n) t'"
  shows "dwu_store t' = dwu_store t \<and> dwu_journal t' = dwu_journal t
       \<and> dwu_gens t' = dwu_gens t \<and> dwu_fence t' = dwu_fence t
       \<and> dwu_accepted t' = dwu_accepted t"
  using assms by (cases rule: dwu_step.cases) auto

lemma dwu_step_armf_full:
  assumes "dwu_step t (UArmF g f) t'"
  shows "dwu_fence t \<le> g
       \<and> dwu_store t' = dwu_store t
       \<and> dwu_journal t' = dwu_journal t
       \<and> dwu_accepted t' = dwu_accepted t
       \<and> dwu_fence t' = g
       \<and> dwu_gens t' =
           (dwu_gens t)(g \<mapsto> UArmed (stamped_at (length (dwu_journal t)) g (u_sink_delta f t)))"
  using assms by (cases rule: dwu_step.cases) auto

text \<open>Justification depends only on the journal and the base, so a step that freezes both
  keeps it unchanged.  GOTCHA: @{text u_justified_cong} DIVERGES as a simp rule (schematic
  loop) --- apply it ONLY as a one-shot rule.  It needs @{text "cases (ue_pay x)"} first.\<close>

lemma u_justified_cong:
  assumes "dwu_journal t' = dwu_journal t"
      and "exec_base (dwu_store t') = exec_base (dwu_store t)"
  shows "u_justified t' x = u_justified t x"
  using assms by (cases "ue_pay x") (simp_all add: u_justified_def)


subsection \<open>2.3 The three hard preservation cases (P3 priority)\<close>

lemma pres_fire:
  assumes inv: "u_disc_inv t"
      and step: "dwu_step t (UFire g) t'"
  shows "u_disc_inv t'"
proof -
  from dwu_step_fire_full[OF step] obtain B where
    gB: "dwu_gens t g = Some (UArmed B)" and
    acc': "dwu_accepted t' = dwu_accepted t @ (if dwu_fence t \<le> g then B else [])" and
    gens': "dwu_gens t' = (dwu_gens t)(g \<mapsto> UProd)" and
    jour': "dwu_journal t' = dwu_journal t" and
    fence': "dwu_fence t' = dwu_fence t" and
    store': "dwu_store t' = dwu_store t" by blast
  note C1 = u_disc_invD(1)[OF inv] and C2 = u_disc_invD(2)[OF inv]
   and C3 = u_disc_invD(3)[OF inv] and C4 = u_disc_invD(4)[OF inv]
   and C5 = u_disc_invD(5)[OF inv]
  have jgrow: "\<exists>js. dwu_journal t' = dwu_journal t @ js"
    by (rule exI[of _ "[]"]) (simp add: jour')
  have bconst: "exec_base (dwu_store t') = exec_base (dwu_store t)" by (simp add: store')
  have persist: "\<And>y. u_justified t y \<Longrightarrow> u_justified t' y"
    using jgrow bconst by (blast intro: u_justified_persist)
  have C3': "dwu_journal t' = exec_src_hist (dwu_store t')" using jour' store' C3 by simp
  have C1': "\<forall>y \<in> set (dwu_accepted t'). u_justified t' y"
  proof (cases "dwu_fence t \<le> g")
    case True
    from C5[OF gB True] have "\<forall>y \<in> set B. u_justified t y" by simp
    with persist have "\<forall>y \<in> set B. u_justified t' y" by blast
    with acc' True C1 persist show ?thesis by auto
  next
    case False with acc' C1 persist show ?thesis by auto
  qed
  have C2': "distinct (log_payloads (dwu_accepted t'))"
  proof (cases "dwu_fence t \<le> g")
    case True
    with acc' have "log_payloads (dwu_accepted t')
                      = log_payloads (dwu_accepted t) @ log_payloads B"
      by (simp add: log_payloads_append)
    moreover from C5[OF gB True] have
      "distinct (log_payloads B)"
      "set (log_payloads B) \<inter> set (log_payloads (dwu_accepted t)) = {}" by auto
    ultimately show ?thesis using C2 by (auto simp: distinct_append Int_commute)
  next
    case False with acc' C2 show ?thesis by simp
  qed
  have C4': "\<And>g' B'. dwu_gens t' g' = Some (UArmed B') \<Longrightarrow> g' \<le> dwu_fence t'"
    using gens' fence' C4 by (auto split: if_split_asm)
  have C5': "\<And>g' B'. dwu_gens t' g' = Some (UArmed B') \<Longrightarrow> dwu_fence t' \<le> g' \<Longrightarrow>
              distinct (log_payloads B')
            \<and> set (log_payloads B') \<inter> set (log_payloads (dwu_accepted t')) = {}
            \<and> (\<forall>x \<in> set B'. u_justified t' x)"
  proof -
    fix g' B'
    assume gB': "dwu_gens t' g' = Some (UArmed B')" and elig: "dwu_fence t' \<le> g'"
    from gB' gens' have gne: "g' \<noteq> g" by (auto split: if_split_asm)
    with gB' gens' have gtB': "dwu_gens t g' = Some (UArmed B')" by (auto split: if_split_asm)
    from elig fence' have elig_t: "dwu_fence t \<le> g'" by simp
    from C5[OF gtB' elig_t] have
      d1: "distinct (log_payloads B')" and
      d2: "set (log_payloads B') \<inter> set (log_payloads (dwu_accepted t)) = {}" and
      d3: "\<forall>x \<in> set B'. u_justified t x" by auto
    have disj': "set (log_payloads B') \<inter> set (log_payloads (dwu_accepted t')) = {}"
    proof (cases "dwu_fence t \<le> g")
      case True
      from C4[OF gB] C4[OF gtB'] True elig_t have "g' = g" by linarith
      with gne show ?thesis by simp
    next
      case False with acc' d2 show ?thesis by simp
    qed
    from d1 disj' d3 persist show
      "distinct (log_payloads B')
       \<and> set (log_payloads B') \<inter> set (log_payloads (dwu_accepted t')) = {}
       \<and> (\<forall>x \<in> set B'. u_justified t' x)" by blast
  qed
  show ?thesis
    unfolding u_disc_inv_def
    using C1' C2' C3' C4' C5' by blast
qed

lemma pres_publish:
  assumes inv: "u_disc_inv t"
      and D1a_mem: "(c, e) \<in> set (exec_src_hist (dwu_store t))"
      and D1a_fresh: "(c, e) \<notin> set (log_payloads (dwu_accepted t))"
      and D1b: "\<forall>g' B. dwu_gens t g' = Some (UArmed B) \<longrightarrow> g' < dwu_fence t"
      and step: "dwu_step t (ULift g (DoDownstream c e)) t'"
  shows "u_disc_inv t'"
proof -
  define x where "x = \<lparr> ue_stamp = length (dwu_journal t), ue_gen = g, ue_pay = ULog (c, e) \<rparr>"
  from dwu_step_publish_full[OF step] obtain s' where
    core: "dw_exec_step (dwu_store t) (DoDownstream c e) s'" and
    store': "dwu_store t' = s'" and
    jour': "dwu_journal t' = dwu_journal t" and
    gens': "dwu_gens t' = dwu_gens t" and
    fence': "dwu_fence t' = dwu_fence t" and
    acc': "dwu_accepted t' = dwu_accepted t @ (if dwu_fence t \<le> g then [x] else [])"
    unfolding x_def by blast
  note C1 = u_disc_invD(1)[OF inv] and C2 = u_disc_invD(2)[OF inv]
   and C3 = u_disc_invD(3)[OF inv] and C4 = u_disc_invD(4)[OF inv]
   and C5 = u_disc_invD(5)[OF inv]
  have bconst: "exec_base (dwu_store t') = exec_base (dwu_store t)"
    using store' core by (simp add: dw_exec_step_base)
  have srcfr: "exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t)"
    using store' core by (simp add: dw_exec_step_src_hist)
  have jgrow: "\<exists>js. dwu_journal t' = dwu_journal t @ js"
    by (rule exI[of _ "[]"]) (simp add: jour')
  have persist: "\<And>y. u_justified t y \<Longrightarrow> u_justified t' y"
    using jgrow bconst by (blast intro: u_justified_persist)
  have C3': "dwu_journal t' = exec_src_hist (dwu_store t')" using jour' srcfr C3 by simp
  have xjust: "u_justified t' x"
  proof -
    from D1a_mem C3 have "(c, e) \<in> set (dwu_journal t)" by simp
    thus ?thesis unfolding x_def u_justified_def using jour' by simp
  qed
  have C1': "\<forall>y \<in> set (dwu_accepted t'). u_justified t' y"
    using acc' C1 persist xjust by (cases "dwu_fence t \<le> g") auto
  have C2': "distinct (log_payloads (dwu_accepted t'))"
  proof (cases "dwu_fence t \<le> g")
    case True
    with acc' have "log_payloads (dwu_accepted t') = log_payloads (dwu_accepted t) @ [(c, e)]"
      by (simp add: log_payloads_append x_def log_payloads_single_ulog)
    thus ?thesis using C2 D1a_fresh by simp
  next
    case False with acc' C2 show ?thesis by simp
  qed
  have C4': "\<And>g' B. dwu_gens t' g' = Some (UArmed B) \<Longrightarrow> g' \<le> dwu_fence t'"
    using gens' fence' C4 by simp
  have C5': "\<And>g' B. dwu_gens t' g' = Some (UArmed B) \<Longrightarrow> dwu_fence t' \<le> g' \<Longrightarrow>
              distinct (log_payloads B)
            \<and> set (log_payloads B) \<inter> set (log_payloads (dwu_accepted t')) = {}
            \<and> (\<forall>x \<in> set B. u_justified t' x)"
  proof -
    fix g' B assume "dwu_gens t' g' = Some (UArmed B)" and "dwu_fence t' \<le> g'"
    with gens' fence' D1b have False by (metis leD)
    thus "distinct (log_payloads B)
        \<and> set (log_payloads B) \<inter> set (log_payloads (dwu_accepted t')) = {}
        \<and> (\<forall>x \<in> set B. u_justified t' x)" by simp
  qed
  show ?thesis unfolding u_disc_inv_def using C1' C2' C3' C4' C5' by blast
qed

lemma pres_cursor:
  assumes inv: "u_disc_inv t"
      and Rdef: "R = replay_down_hist (retained_hist t) (exec_scope (dwu_store t)) f"
      and ddist: "distinct (drop m R)"
      and ddisj: "set (drop m R) \<inter> set (log_payloads (dwu_accepted t)) = {}"
      and D1b: "\<forall>g' B'. dwu_gens t g' = Some (UArmed B') \<longrightarrow> g' < dwu_fence t"
      and Bdef: "B = stamped_at (length (dwu_journal t)) g (drop m R)"
      and s1: "dwu_step t (UArm g B f) t1"
      and s2: "dwu_step t1 (UHeal g f) t2"
      and s3: "dwu_step t2 (UFire g) t3"
  shows "u_disc_inv t3"
proof -
  from dwu_step_arm_inv[OF s1] have
    g1: "dwu_gens t1 = (dwu_gens t)(g \<mapsto> UArmed B)" and store1: "dwu_store t1 = dwu_store t" and
    jour1: "dwu_journal t1 = dwu_journal t" and acc1: "dwu_accepted t1 = dwu_accepted t" and
    fence1: "dwu_fence t1 = dwu_fence t" by auto
  from dwu_step_heal_frame[OF s2] have
    g2: "dwu_gens t2 = dwu_gens t1" and jour2: "dwu_journal t2 = dwu_journal t1" and
    acc2: "dwu_accepted t2 = dwu_accepted t1" and fence2: "dwu_fence t2 = dwu_fence t1" by auto
  from dwu_step_heal_src_base[OF s2] have
    src2: "exec_src_hist (dwu_store t2) = exec_src_hist (dwu_store t1)" and
    base2: "exec_base (dwu_store t2) = exec_base (dwu_store t1)" by auto
  from dwu_step_fire_full[OF s3] obtain B' where
    g2B: "dwu_gens t2 g = Some (UArmed B')" and
    acc3: "dwu_accepted t3 = dwu_accepted t2 @ (if dwu_fence t2 \<le> g then B' else [])" and
    g3: "dwu_gens t3 = (dwu_gens t2)(g \<mapsto> UProd)" and
    jour3: "dwu_journal t3 = dwu_journal t2" and fence3: "dwu_fence t3 = dwu_fence t2" and
    store3: "dwu_store t3 = dwu_store t2" by blast
  have BeqB': "B' = B" using g2B by (simp add: g2 g1)
  have jour3t: "dwu_journal t3 = dwu_journal t" using jour3 jour2 jour1 by simp
  have fence3t: "dwu_fence t3 = dwu_fence t" using fence3 fence2 fence1 by simp
  have acc3t: "dwu_accepted t3 = dwu_accepted t @ (if dwu_fence t \<le> g then B else [])"
    using acc3 acc2 acc1 fence2 fence1 BeqB' by simp
  have g3t: "dwu_gens t3 = (dwu_gens t)(g \<mapsto> UProd)" using g3 g2 g1 by simp
  have src3: "exec_src_hist (dwu_store t3) = exec_src_hist (dwu_store t)"
    using store3 src2 store1 by simp
  have base3: "exec_base (dwu_store t3) = exec_base (dwu_store t)"
    using store3 base2 store1 by simp
  note C1 = u_disc_invD(1)[OF inv] and C2 = u_disc_invD(2)[OF inv]
   and C3 = u_disc_invD(3)[OF inv] and C4 = u_disc_invD(4)[OF inv]
   and C5 = u_disc_invD(5)[OF inv]
  have jgrow: "\<exists>js. dwu_journal t3 = dwu_journal t @ js"
    by (rule exI[of _ "[]"]) (simp add: jour3t)
  have persist: "\<And>y. u_justified t y \<Longrightarrow> u_justified t3 y"
    using jgrow base3 by (blast intro: u_justified_persist)
  have dmR_sub: "set (drop m R) \<subseteq> set (dwu_journal t)"
  proof -
    have "set (drop m R) \<subseteq> set R" by (rule set_drop_subset)
    also have "set R \<subseteq> set (retained_hist t)" using Rdef replay_subset by simp
    also have "\<dots> \<subseteq> set (exec_src_hist (dwu_store t))" by (rule retained_subset)
    also have "\<dots> = set (dwu_journal t)" using C3 by simp
    finally show ?thesis .
  qed
  have C3': "dwu_journal t3 = exec_src_hist (dwu_store t3)" using jour3t src3 C3 by simp
  have Bjust: "\<forall>y \<in> set B. u_justified t3 y"
  proof
    fix y assume "y \<in> set B"
    hence "y \<in> set (stamped_at (length (dwu_journal t3)) g (drop m R))"
      using Bdef jour3t by simp
    thus "u_justified t3 y" using dmR_sub jour3t
      by (auto intro!: u_justified_stamped_batch)
  qed
  have C1': "\<forall>y \<in> set (dwu_accepted t3). u_justified t3 y"
    using acc3t C1 persist Bjust by (cases "dwu_fence t \<le> g") auto
  have C2': "distinct (log_payloads (dwu_accepted t3))"
  proof (cases "dwu_fence t \<le> g")
    case True
    with acc3t have "log_payloads (dwu_accepted t3) = log_payloads (dwu_accepted t) @ drop m R"
      using Bdef by (simp add: log_payloads_append)
    thus ?thesis using C2 ddist ddisj by (auto simp: distinct_append Int_commute)
  next
    case False with acc3t C2 show ?thesis by simp
  qed
  have C4': "\<And>g' B''. dwu_gens t3 g' = Some (UArmed B'') \<Longrightarrow> g' \<le> dwu_fence t3"
  proof -
    fix g' B'' assume "dwu_gens t3 g' = Some (UArmed B'')"
    with g3t have "dwu_gens t g' = Some (UArmed B'') \<and> g' \<noteq> g" by (auto split: if_split_asm)
    with D1b fence3t show "g' \<le> dwu_fence t3" by fastforce
  qed
  have C5': "\<And>g' B''. dwu_gens t3 g' = Some (UArmed B'') \<Longrightarrow> dwu_fence t3 \<le> g' \<Longrightarrow>
              distinct (log_payloads B'')
            \<and> set (log_payloads B'') \<inter> set (log_payloads (dwu_accepted t3)) = {}
            \<and> (\<forall>x \<in> set B''. u_justified t3 x)"
  proof -
    fix g' B'' assume "dwu_gens t3 g' = Some (UArmed B'')" and "dwu_fence t3 \<le> g'"
    with g3t fence3t have "dwu_gens t g' = Some (UArmed B'') \<and> dwu_fence t \<le> g'"
      by (auto split: if_split_asm)
    with D1b have False by fastforce
    thus "distinct (log_payloads B'')
        \<and> set (log_payloads B'') \<inter> set (log_payloads (dwu_accepted t3)) = {}
        \<and> (\<forall>x \<in> set B''. u_justified t3 x)" by simp
  qed
  show ?thesis unfolding u_disc_inv_def using C1' C2' C3' C4' C5' by blast
qed


subsection \<open>2.4 The easy preservation cases (frame / append / spawn / claim)\<close>

lemma u_disc_inv_frame:
  assumes inv: "u_disc_inv t"
      and A: "dwu_accepted t' = dwu_accepted t"
      and G: "dwu_gens t' = dwu_gens t"
      and F: "dwu_fence t' = dwu_fence t"
      and J: "dwu_journal t' = dwu_journal t"
      and S: "exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t)"
      and Bse: "exec_base (dwu_store t') = exec_base (dwu_store t)"
  shows "u_disc_inv t'"
proof -
  have juj: "\<And>x. u_justified t' x = u_justified t x" using J Bse by (rule u_justified_cong)
  from inv show ?thesis
    unfolding u_disc_inv_def by (simp add: A G F J S juj)
qed

lemma pres_publost:
  assumes inv: "u_disc_inv t" and step: "dwu_step t (UPubLost g c e) t'"
  shows "u_disc_inv t'"
proof -
  from dwu_step_publost_full[OF step] obtain s' where
    core: "dw_exec_step (dwu_store t) (DoDownstream c e) s'" and st: "dwu_store t' = s'" and
    J: "dwu_journal t' = dwu_journal t" and G: "dwu_gens t' = dwu_gens t" and
    F: "dwu_fence t' = dwu_fence t" and A: "dwu_accepted t' = dwu_accepted t" by blast
  show ?thesis
    by (rule u_disc_inv_frame[OF inv A G F J])
       (simp_all add: st dw_exec_step_src_hist[OF core] dw_exec_step_base[OF core])
qed

lemma pres_release:
  assumes inv: "u_disc_inv t" and step: "dwu_step t (URelease g) t'"
  shows "u_disc_inv t'"
proof -
  from dwu_step_release_frame[OF step] have
    G: "dwu_gens t' = dwu_gens t" and J: "dwu_journal t' = dwu_journal t" and
    A: "dwu_accepted t' = dwu_accepted t" and F: "dwu_fence t' = dwu_fence t" by auto
  from dwu_step_release_src_base[OF step] have
    S: "exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t)" and
    Bse: "exec_base (dwu_store t') = exec_base (dwu_store t)" by auto
  show ?thesis by (rule u_disc_inv_frame[OF inv A G F J S Bse])
qed

lemma pres_retain:
  assumes inv: "u_disc_inv t" and step: "dwu_step t (URetain n) t'"
  shows "u_disc_inv t'"
proof -
  from dwu_step_retain_full[OF step] have
    st: "dwu_store t' = dwu_store t" and J: "dwu_journal t' = dwu_journal t" and
    G: "dwu_gens t' = dwu_gens t" and F: "dwu_fence t' = dwu_fence t" and
    A: "dwu_accepted t' = dwu_accepted t" by auto
  show ?thesis by (rule u_disc_inv_frame[OF inv A G F J]) (simp_all add: st)
qed

lemma pres_nonpub:
  assumes inv: "u_disc_inv t"
      and notpub: "\<forall>c e. a \<noteq> DoDownstream c e"
      and step: "dwu_step t (ULift g a) t'"
  shows "u_disc_inv t'"
proof -
  from dwu_lift_nonpub_shape[OF step notpub] have
    A: "dwu_accepted t' = dwu_accepted t" and G: "dwu_gens t' = dwu_gens t" and
    F: "dwu_fence t' = dwu_fence t" and
    J: "dwu_journal t' = dwu_journal t @ src_hist_of_labels [a]" and
    S: "exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t) @ src_hist_of_labels [a]" and
    Bse: "exec_base (dwu_store t') = exec_base (dwu_store t)" by auto
  note C1 = u_disc_invD(1)[OF inv] and C2 = u_disc_invD(2)[OF inv]
   and C3 = u_disc_invD(3)[OF inv] and C4 = u_disc_invD(4)[OF inv]
   and C5 = u_disc_invD(5)[OF inv]
  have jgrow: "\<exists>js. dwu_journal t' = dwu_journal t @ js" using J by blast
  have persist: "\<And>y. u_justified t y \<Longrightarrow> u_justified t' y"
    using jgrow Bse by (blast intro: u_justified_persist)
  have C1': "\<forall>y \<in> set (dwu_accepted t'). u_justified t' y" using A C1 persist by auto
  have C2': "distinct (log_payloads (dwu_accepted t'))" using A C2 by simp
  have C3': "dwu_journal t' = exec_src_hist (dwu_store t')" using J S C3 by simp
  have C4': "\<And>g' B. dwu_gens t' g' = Some (UArmed B) \<Longrightarrow> g' \<le> dwu_fence t'"
    using G F C4 by auto
  have C5': "\<And>g' B. dwu_gens t' g' = Some (UArmed B) \<Longrightarrow> dwu_fence t' \<le> g' \<Longrightarrow>
              distinct (log_payloads B)
            \<and> set (log_payloads B) \<inter> set (log_payloads (dwu_accepted t')) = {}
            \<and> (\<forall>x \<in> set B. u_justified t' x)"
  proof -
    fix g' B assume gB: "dwu_gens t' g' = Some (UArmed B)" and el: "dwu_fence t' \<le> g'"
    from gB G have gt: "dwu_gens t g' = Some (UArmed B)" by simp
    from el F have elt: "dwu_fence t \<le> g'" by simp
    from C5[OF gt elt] persist A show
      "distinct (log_payloads B)
       \<and> set (log_payloads B) \<inter> set (log_payloads (dwu_accepted t')) = {}
       \<and> (\<forall>x \<in> set B. u_justified t' x)" by auto
  qed
  show ?thesis unfolding u_disc_inv_def using C1' C2' C3' C4' C5' by blast
qed

lemma pres_snap:
  assumes inv: "u_disc_inv t"
      and D4: "v = Src (exec_base (dwu_store t)) (take (length (dwu_journal t)) (dwu_journal t)) c k"
      and step: "dwu_step t (USnapE g c k v) t'"
  shows "u_disc_inv t'"
proof -
  define x where "x = \<lparr> ue_stamp = length (dwu_journal t), ue_gen = g, ue_pay = USnap c k v \<rparr>"
  from dwu_step_snap_full[OF step] have
    st: "dwu_store t' = dwu_store t" and J: "dwu_journal t' = dwu_journal t" and
    G: "dwu_gens t' = dwu_gens t" and F: "dwu_fence t' = dwu_fence t" and
    A: "dwu_accepted t' = dwu_accepted t @ (if dwu_fence t \<le> g then [x] else [])"
    unfolding x_def by auto
  note C1 = u_disc_invD(1)[OF inv] and C2 = u_disc_invD(2)[OF inv]
   and C3 = u_disc_invD(3)[OF inv] and C4 = u_disc_invD(4)[OF inv]
   and C5 = u_disc_invD(5)[OF inv]
  have basefact: "exec_base (dwu_store t') = exec_base (dwu_store t)" by (simp add: st)
  have juj: "\<And>y. u_justified t' y = u_justified t y" by (rule u_justified_cong[OF J basefact])
  have xjust: "u_justified t' x"
    unfolding x_def u_justified_def using D4 J st by simp
  have logsame: "log_payloads (dwu_accepted t') = log_payloads (dwu_accepted t)"
    using A by (cases "dwu_fence t \<le> g") (simp_all add: log_payloads_append x_def)
  have C1': "\<forall>y \<in> set (dwu_accepted t'). u_justified t' y"
    using A C1 juj xjust by (cases "dwu_fence t \<le> g") auto
  have C2': "distinct (log_payloads (dwu_accepted t'))" using logsame C2 by simp
  have C3': "dwu_journal t' = exec_src_hist (dwu_store t')" using J st C3 by simp
  have C4': "\<And>g' B. dwu_gens t' g' = Some (UArmed B) \<Longrightarrow> g' \<le> dwu_fence t'"
    using G F C4 by auto
  have C5': "\<And>g' B. dwu_gens t' g' = Some (UArmed B) \<Longrightarrow> dwu_fence t' \<le> g' \<Longrightarrow>
              distinct (log_payloads B)
            \<and> set (log_payloads B) \<inter> set (log_payloads (dwu_accepted t')) = {}
            \<and> (\<forall>x \<in> set B. u_justified t' x)"
  proof -
    fix g' B assume gB: "dwu_gens t' g' = Some (UArmed B)" and el: "dwu_fence t' \<le> g'"
    from gB G have gt: "dwu_gens t g' = Some (UArmed B)" by simp
    from el F have elt: "dwu_fence t \<le> g'" by simp
    from C5[OF gt elt] logsame juj show
      "distinct (log_payloads B)
       \<and> set (log_payloads B) \<inter> set (log_payloads (dwu_accepted t')) = {}
       \<and> (\<forall>x \<in> set B. u_justified t' x)" by simp
  qed
  show ?thesis unfolding u_disc_inv_def using C1' C2' C3' C4' C5' by blast
qed

lemma pres_spawn:
  assumes inv: "u_disc_inv t" and step: "dwu_step t USpawn t'"
  shows "u_disc_inv t'"
proof -
  from dwu_step_spawn_inv[OF step] have
    G: "dwu_gens t' = (dwu_gens t)(Suc (dwu_hwm t) \<mapsto> UProd)" and st: "dwu_store t' = dwu_store t" and
    J: "dwu_journal t' = dwu_journal t" and A: "dwu_accepted t' = dwu_accepted t" and
    F: "dwu_fence t' = dwu_fence t" by auto
  note C1 = u_disc_invD(1)[OF inv] and C2 = u_disc_invD(2)[OF inv]
   and C3 = u_disc_invD(3)[OF inv] and C4 = u_disc_invD(4)[OF inv]
   and C5 = u_disc_invD(5)[OF inv]
  have basefact: "exec_base (dwu_store t') = exec_base (dwu_store t)" by (simp add: st)
  have juj: "\<And>y. u_justified t' y = u_justified t y" by (rule u_justified_cong[OF J basefact])
  have armed: "\<And>g' B. dwu_gens t' g' = Some (UArmed B) \<Longrightarrow> dwu_gens t g' = Some (UArmed B)"
    using G by (auto split: if_split_asm)
  have C1': "\<forall>y \<in> set (dwu_accepted t'). u_justified t' y" using A C1 juj by simp
  have C2': "distinct (log_payloads (dwu_accepted t'))" using A C2 by simp
  have C3': "dwu_journal t' = exec_src_hist (dwu_store t')" using J st C3 by simp
  have C4': "\<And>g' B. dwu_gens t' g' = Some (UArmed B) \<Longrightarrow> g' \<le> dwu_fence t'"
  proof -
    fix g' B assume "dwu_gens t' g' = Some (UArmed B)"
    from C4[OF armed[OF this]] F show "g' \<le> dwu_fence t'" by simp
  qed
  have C5': "\<And>g' B. dwu_gens t' g' = Some (UArmed B) \<Longrightarrow> dwu_fence t' \<le> g' \<Longrightarrow>
              distinct (log_payloads B)
            \<and> set (log_payloads B) \<inter> set (log_payloads (dwu_accepted t')) = {}
            \<and> (\<forall>x \<in> set B. u_justified t' x)"
  proof -
    fix g' B assume gB: "dwu_gens t' g' = Some (UArmed B)" and el: "dwu_fence t' \<le> g'"
    from armed[OF gB] have gt: "dwu_gens t g' = Some (UArmed B)" .
    from el F have elt: "dwu_fence t \<le> g'" by simp
    from C5[OF gt elt] A juj show
      "distinct (log_payloads B)
       \<and> set (log_payloads B) \<inter> set (log_payloads (dwu_accepted t')) = {}
       \<and> (\<forall>x \<in> set B. u_justified t' x)" by simp
  qed
  show ?thesis unfolding u_disc_inv_def using C1' C2' C3' C4' C5' by blast
qed

lemma pres_claim:
  assumes inv: "u_disc_inv t"
      and D3: "distinct (log_payloads (stamped_at (length (dwu_journal t)) g (u_sink_delta f t)))"
      and step: "dwu_step t (UArmF g f) t'"
  shows "u_disc_inv t'"
proof -
  define nb where "nb = stamped_at (length (dwu_journal t)) g (u_sink_delta f t)"
  from dwu_step_armf_full[OF step] have
    fle: "dwu_fence t \<le> g" and st: "dwu_store t' = dwu_store t" and
    J: "dwu_journal t' = dwu_journal t" and A: "dwu_accepted t' = dwu_accepted t" and
    F: "dwu_fence t' = g" and G: "dwu_gens t' = (dwu_gens t)(g \<mapsto> UArmed nb)"
    unfolding nb_def by auto
  note C1 = u_disc_invD(1)[OF inv] and C2 = u_disc_invD(2)[OF inv]
   and C3 = u_disc_invD(3)[OF inv] and C4 = u_disc_invD(4)[OF inv]
   and C5 = u_disc_invD(5)[OF inv]
  have basefact: "exec_base (dwu_store t') = exec_base (dwu_store t)" by (simp add: st)
  have juj: "\<And>y. u_justified t' y = u_justified t y" by (rule u_justified_cong[OF J basefact])
  have sd_sub: "set (u_sink_delta f t) \<subseteq> set (dwu_journal t)"
  proof -
    have "set (u_sink_delta f t)
            \<subseteq> set (replay_down_hist (retained_hist t) (exec_scope (dwu_store t)) f)"
      by (auto simp: u_sink_delta_def)
    also have "\<dots> \<subseteq> set (retained_hist t)" by (rule replay_subset)
    also have "\<dots> \<subseteq> set (exec_src_hist (dwu_store t))" by (rule retained_subset)
    also have "\<dots> = set (dwu_journal t)" using C3 by simp
    finally show ?thesis .
  qed
  have sd_disj: "set (u_sink_delta f t) \<inter> set (log_payloads (dwu_accepted t)) = {}"
    by (auto simp: u_sink_delta_def)
  have nb_just: "\<forall>y \<in> set nb. u_justified t y"
    unfolding nb_def using sd_sub by (auto intro!: u_justified_stamped_batch)
  have C1': "\<forall>y \<in> set (dwu_accepted t'). u_justified t' y" using A C1 juj by simp
  have C2': "distinct (log_payloads (dwu_accepted t'))" using A C2 by simp
  have C3': "dwu_journal t' = exec_src_hist (dwu_store t')" using J st C3 by simp
  have C4': "\<And>g' B. dwu_gens t' g' = Some (UArmed B) \<Longrightarrow> g' \<le> dwu_fence t'"
  proof -
    fix g' B assume gB: "dwu_gens t' g' = Some (UArmed B)"
    show "g' \<le> dwu_fence t'"
    proof (cases "g' = g")
      case True thus ?thesis using F by simp
    next
      case False
      with gB G have "dwu_gens t g' = Some (UArmed B)" by (auto split: if_split_asm)
      from C4[OF this] fle F show ?thesis by simp
    qed
  qed
  have C5': "\<And>g' B. dwu_gens t' g' = Some (UArmed B) \<Longrightarrow> dwu_fence t' \<le> g' \<Longrightarrow>
              distinct (log_payloads B)
            \<and> set (log_payloads B) \<inter> set (log_payloads (dwu_accepted t')) = {}
            \<and> (\<forall>x \<in> set B. u_justified t' x)"
  proof -
    fix g' B assume gB: "dwu_gens t' g' = Some (UArmed B)" and el: "dwu_fence t' \<le> g'"
    show "distinct (log_payloads B)
        \<and> set (log_payloads B) \<inter> set (log_payloads (dwu_accepted t')) = {}
        \<and> (\<forall>x \<in> set B. u_justified t' x)"
    proof (cases "g' = g")
      case True
      with gB G have "B = nb" by simp
      thus ?thesis
        using D3 sd_disj nb_just juj A
        by (simp add: nb_def log_payloads_stamped_at)
    next
      case False
      from gB G False have gt: "dwu_gens t g' = Some (UArmed B)" by (auto split: if_split_asm)
      from C4[OF gt] fle el F have "g' = g" by simp
      with False show ?thesis by simp
    qed
  qed
  show ?thesis unfolding u_disc_inv_def using C1' C2' C3' C4' C5' by blast
qed


subsection \<open>2.5 The induction and the U8 safety headliner\<close>

lemma u_disc_inv_pres:
  "u_disciplined_trace s acts t \<Longrightarrow> u_disc_inv s \<Longrightarrow> u_disc_inv t"
proof (induction rule: u_disciplined_trace.induct)
  case (ud_refl t) thus ?case by simp
next
  case (ud_nonpub t a g t' as t'')
  from pres_nonpub[OF ud_nonpub.prems ud_nonpub.hyps(3) ud_nonpub.hyps(4)]
  show ?case using ud_nonpub.IH by blast
next
  case (ud_publish t c e g t' as t'')
  from pres_publish[OF ud_publish.prems ud_publish.hyps(3) ud_publish.hyps(4)
                       ud_publish.hyps(5) ud_publish.hyps(6)]
  show ?case using ud_publish.IH by blast
next
  case (ud_publost t c e g t' as t'')
  from pres_publost[OF ud_publost.prems ud_publost.hyps(3)]
  show ?case using ud_publost.IH by blast
next
  case (ud_snap v t c k g t' as t'')
  from pres_snap[OF ud_snap.prems ud_snap.hyps(1) ud_snap.hyps(2)]
  show ?case using ud_snap.IH by blast
next
  case (ud_spawn t t' as t'')
  from pres_spawn[OF ud_spawn.prems ud_spawn.hyps(1)]
  show ?case using ud_spawn.IH by blast
next
  case (ud_release t g t' as t'')
  from pres_release[OF ud_release.prems ud_release.hyps(1)]
  show ?case using ud_release.IH by blast
next
  case (ud_claim t g f t' as t'')
  from pres_claim[OF ud_claim.prems ud_claim.hyps(1) ud_claim.hyps(2)]
  show ?case using ud_claim.IH by blast
next
  case (ud_fire t g t' as t'')
  from pres_fire[OF ud_fire.prems ud_fire.hyps(1)]
  show ?case using ud_fire.IH by blast
next
  case (ud_retain t n t' as t'')
  from pres_retain[OF ud_retain.prems ud_retain.hyps(1)]
  show ?case using ud_retain.IH by blast
next
  case (ud_cursor_recovery R t f m B g t1 t2 t3 as t'')
  from pres_cursor[OF ud_cursor_recovery.prems ud_cursor_recovery.hyps(1)
                      ud_cursor_recovery.hyps(3) ud_cursor_recovery.hyps(4)
                      ud_cursor_recovery.hyps(5) ud_cursor_recovery.hyps(6)
                      ud_cursor_recovery.hyps(7) ud_cursor_recovery.hyps(8)
                      ud_cursor_recovery.hyps(9)]
  show ?case using ud_cursor_recovery.IH by blast
qed

text \<open>U8's safety headliner --- FULLY PROVED from the invariant.\<close>

theorem u_fenced_multiwriter_discipline_safe:
  assumes "u_disciplined_trace (dwu_init b K fin) acts t"
  shows "\<not> u_effect_unsafe t"
  using u_disc_inv_pres[OF assms u_disc_inv_init] by (rule u_disc_inv_safe)


section \<open>3. Delivery bookkeeping: the owed set and its monotonicity\<close>

text \<open>@{term "u_owed f t"} is @{term f}'s live owed set: the in-scope, frontier-bounded
  replay of the retained source history.  @{const u_at_least_once_at} says it is covered
  by the accepted ledger's log payloads.\<close>

abbreviation u_owed
  :: "frontier \<Rightarrow> ('k, 'v) dwu_state \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list"
where
  "u_owed f t \<equiv> replay_down_hist (retained_hist t) (exec_scope (dwu_store t)) f"

lemma u_at_least_once_at_owed:
  "u_at_least_once_at f t \<longleftrightarrow> set (u_owed f t) \<subseteq> set (log_payloads (dwu_accepted t))"
  by (simp add: u_at_least_once_at_def)


subsection \<open>3.1 List helpers\<close>

lemma set_drop_mono:
  assumes "m \<le> n" shows "set (drop n xs) \<subseteq> set (drop m xs)"
proof -
  have "drop n xs = drop (n - m) (drop m xs)" using assms by (simp add: drop_drop)
  thus ?thesis by (metis set_drop_subset)
qed

lemma filter_drop_snoc_notP:
  assumes "\<not> P y"
  shows "set (filter P (drop m (xs @ [y]))) \<subseteq> set (filter P (drop m xs))"
proof (cases "m \<le> length xs")
  case True
  hence "drop m (xs @ [y]) = drop m xs @ [y]" by simp
  thus ?thesis using assms by simp
next
  case False
  hence "length (xs @ [y]) \<le> m" by simp
  hence "drop m (xs @ [y]) = []" by simp
  thus ?thesis by simp
qed


subsection \<open>3.2 The owed frame lemmas\<close>

lemma u_owed_frame:
  assumes "exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t)"
      and "dwu_floor t' = dwu_floor t"
      and "exec_scope (dwu_store t') = exec_scope (dwu_store t)"
  shows "u_owed f t' = u_owed f t"
  using assms by (simp add: retained_hist_def)

lemma u_owed_src_above:
  assumes "exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t) @ [(c, e)]"
      and "dwu_floor t' = dwu_floor t"
      and "exec_scope (dwu_store t') = exec_scope (dwu_store t)"
      and "\<not> src_le c f"
  shows "set (u_owed f t') \<subseteq> set (u_owed f t)"
proof -
  have notP: "\<not> (c \<le> f \<and> key_of e \<in> exec_scope (dwu_store t))"
    using assms(4) by (simp add: src_le_eq_less_eq)
  have "set (u_owed f t')
        = set (filter (\<lambda>(c', e'). c' \<le> f \<and> key_of e' \<in> exec_scope (dwu_store t))
                 (drop (dwu_floor t) (exec_src_hist (dwu_store t) @ [(c, e)])))"
    by (simp add: replay_down_hist_def retained_hist_def assms(1) assms(2) assms(3))
  also have "\<dots> \<subseteq> set (filter (\<lambda>(c', e'). c' \<le> f \<and> key_of e' \<in> exec_scope (dwu_store t))
                 (drop (dwu_floor t) (exec_src_hist (dwu_store t))))"
    using notP by (intro filter_drop_snoc_notP) auto
  also have "\<dots> = set (u_owed f t)"
    by (simp add: replay_down_hist_def retained_hist_def)
  finally show ?thesis .
qed

lemma u_owed_floor_raise:
  assumes "exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t)"
      and "dwu_floor t \<le> dwu_floor t'"
      and "exec_scope (dwu_store t') = exec_scope (dwu_store t)"
  shows "set (u_owed f t') \<subseteq> set (u_owed f t)"
proof -
  have "set (drop (dwu_floor t') (exec_src_hist (dwu_store t)))
          \<subseteq> set (drop (dwu_floor t) (exec_src_hist (dwu_store t)))"
    by (rule set_drop_mono[OF assms(2)])
  thus ?thesis
    by (auto simp: replay_down_hist_def retained_hist_def assms(1) assms(3))
qed


subsection \<open>3.3 Per-step owed antitonicity\<close>

text \<open>A single step never GROWS the owed set below @{term f}, provided it is not a
  sub-frontier @{const DoSource} (which would add a below-@{term f} commit) and not an
  (excluded) @{const UTruncCrash}.  All other steps freeze the source history and floor
  below @{term f}, or (@{const URetain}) only raise the floor, which shrinks the retained
  view.\<close>

lemma u_step_owed_ingredients:
  assumes "dwu_step t \<alpha> t'"
  shows "exec_scope (dwu_store t') = exec_scope (dwu_store t)
       \<and> ((exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t) \<and> dwu_floor t' = dwu_floor t)
         \<or> (\<exists>g c e. \<alpha> = ULift g (DoSource c e)
              \<and> exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t) @ [(c, e)]
              \<and> dwu_floor t' = dwu_floor t)
         \<or> (\<exists>n. \<alpha> = URetain n \<and> exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t)
              \<and> dwu_floor t \<le> dwu_floor t')
         \<or> (\<exists>d c. \<alpha> = UTruncCrash d c))"
proof -
  have sc: "exec_scope (dwu_store t') = exec_scope (dwu_store t)"
    by (rule u_exec_scope_const[OF assms])
  have "(exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t) \<and> dwu_floor t' = dwu_floor t)
         \<or> (\<exists>g c e. \<alpha> = ULift g (DoSource c e)
              \<and> exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t) @ [(c, e)]
              \<and> dwu_floor t' = dwu_floor t)
         \<or> (\<exists>n. \<alpha> = URetain n \<and> exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t)
              \<and> dwu_floor t \<le> dwu_floor t')
         \<or> (\<exists>d c. \<alpha> = UTruncCrash d c)"
    using assms
  proof (cases rule: dwu_step.cases)
    case (ulift_source g c e s') then show ?thesis by (auto dest!: dw_exec_step_src_hist)
  next
    case (ulift_enqueue g c e s') then show ?thesis by (auto dest!: dw_exec_step_src_hist)
  next
    case (ulift_ack g c e s') then show ?thesis by (auto dest!: dw_exec_step_src_hist)
  next
    case (ulift_publish g c e s' x) then show ?thesis by (auto dest!: dw_exec_step_src_hist)
  next
    case (ulift_nonprod g a s') then show ?thesis
      by (auto simp: src_hist_of_labels_nonprod dest!: dw_exec_step_src_hist)
  next
    case (upublost g c e s' x) then show ?thesis by (auto dest!: dw_exec_step_src_hist)
  next
    case (usnap g c k v x) then show ?thesis by simp
  next
    case uspawn then show ?thesis by simp
  next
    case (uarm g B f) then show ?thesis by simp
  next
    case (uarmf g f) then show ?thesis by simp
  next
    case (uheal f s' g) then show ?thesis by (auto simp: relay_bounded_replay_reconcile_def)
  next
    case (ufire g B) then show ?thesis by simp
  next
    case (urelease g) then show ?thesis by simp
  next
    case (ufenceraise n) then show ?thesis by simp
  next
    case (utrunccrash d c) then show ?thesis by blast
  next
    case (uretain n) then show ?thesis by auto
  qed
  with sc show ?thesis by blast
qed

lemma u_step_owed_antitone:
  assumes step: "dwu_step t \<alpha> t'"
      and nosrc: "\<And>g c e. \<alpha> = ULift g (DoSource c e) \<Longrightarrow> \<not> src_le c f"
      and notrunc: "\<And>d c. \<alpha> \<noteq> UTruncCrash d c"
  shows "set (u_owed f t') \<subseteq> set (u_owed f t)"
proof -
  note ingr = u_step_owed_ingredients[OF step]
  from ingr have sc: "exec_scope (dwu_store t') = exec_scope (dwu_store t)"
    by (rule conjunct1)
  from ingr have disj:
    "(exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t) \<and> dwu_floor t' = dwu_floor t)
         \<or> (\<exists>g c e. \<alpha> = ULift g (DoSource c e)
              \<and> exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t) @ [(c, e)]
              \<and> dwu_floor t' = dwu_floor t)
         \<or> (\<exists>n. \<alpha> = URetain n \<and> exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t)
              \<and> dwu_floor t \<le> dwu_floor t')
         \<or> (\<exists>d c. \<alpha> = UTruncCrash d c)" by (rule conjunct2)
  from disj show ?thesis
  proof (elim disjE)
    assume A: "exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t) \<and> dwu_floor t' = dwu_floor t"
    have "u_owed f t' = u_owed f t"
      by (rule u_owed_frame[OF conjunct1[OF A] conjunct2[OF A] sc])
    thus ?thesis by simp
  next
    assume "\<exists>g c e. \<alpha> = ULift g (DoSource c e)
              \<and> exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t) @ [(c, e)]
              \<and> dwu_floor t' = dwu_floor t"
    then obtain g c e where
      A: "\<alpha> = ULift g (DoSource c e)"
        "exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t) @ [(c, e)]"
        "dwu_floor t' = dwu_floor t" by blast
    from nosrc[OF A(1)] have nsl: "\<not> src_le c f" .
    show ?thesis by (rule u_owed_src_above[OF A(2) A(3) sc nsl])
  next
    assume "\<exists>n. \<alpha> = URetain n \<and> exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t)
              \<and> dwu_floor t \<le> dwu_floor t'"
    then obtain n where
      A: "exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t)"
         "dwu_floor t \<le> dwu_floor t'" by blast
    show ?thesis by (rule u_owed_floor_raise[OF A(1) A(2) sc])
  next
    assume "\<exists>d c. \<alpha> = UTruncCrash d c"
    with notrunc show ?thesis by blast
  qed
qed


subsection \<open>3.4 Per-step accepted-ledger growth\<close>

lemma u_step_accepted_grow:
  assumes "dwu_step t \<alpha> t'"
  shows "\<exists>ys. dwu_accepted t' = dwu_accepted t @ ys"
  using assms by (cases rule: dwu_step.cases) auto


section \<open>4. Determinism (the temporal-trace linchpin)\<close>

lemma dwu_step_deterministic:
  assumes "dwu_step t \<alpha> t1" and "dwu_step t \<alpha> t2"
  shows "t1 = t2"
  using assms
  by (induction arbitrary: t2 rule: dwu_step.induct)
     (auto elim!: dwu_step.cases dest: dw_exec_step_deterministic
           simp: relay_bounded_replay_reconcile_def)

lemma dwu_temporal_trace_ConsD:
  assumes "dwu_temporal_trace s (a # rest) u"
  shows "\<exists>s1. dwu_step s a s1 \<and> dwu_temporal_trace s1 rest u"
  using assms by (cases rule: dwu_temporal_trace.cases) auto

lemma dwu_temporal_trace_deterministic:
  assumes "dwu_temporal_trace s xs u1" and "dwu_temporal_trace s xs u2"
  shows "u1 = u2"
  using assms
proof (induction arbitrary: u2 rule: dwu_temporal_trace.induct)
  case (dwu_refl t)
  thus ?case by (cases rule: dwu_temporal_trace.cases) auto
next
  case (dwu_lift_step t a g t' as t'')
  from dwu_temporal_trace_ConsD[OF dwu_lift_step.prems] obtain s1 where
    s1: "dwu_step t (ULift g a) s1" and tl: "dwu_temporal_trace s1 as u2" by blast
  from dwu_step_deterministic[OF dwu_lift_step.hyps(3) s1] have "s1 = t'" by simp
  with tl dwu_lift_step.IH show ?case by simp
next
  case (dwu_publost_step t c e g t' as t'')
  from dwu_temporal_trace_ConsD[OF dwu_publost_step.prems] obtain s1 where
    s1: "dwu_step t (UPubLost g c e) s1" and tl: "dwu_temporal_trace s1 as u2" by blast
  from dwu_step_deterministic[OF dwu_publost_step.hyps(3) s1] have "s1 = t'" by simp
  with tl dwu_publost_step.IH show ?case by simp
next
  case (dwu_other_step \<alpha> t t' as t'')
  from dwu_temporal_trace_ConsD[OF dwu_other_step.prems] obtain s1 where
    s1: "dwu_step t \<alpha> s1" and tl: "dwu_temporal_trace s1 as u2" by blast
  from dwu_step_deterministic[OF dwu_other_step.hyps(3) s1] have "s1 = t'" by simp
  with tl dwu_other_step.IH show ?case by simp
qed


section \<open>5. The disciplined trace embeds in the temporal trace\<close>

lemma u_disciplined_imp_temporal:
  assumes "u_disciplined_trace s acts t"
  shows "dwu_temporal_trace s acts t"
  using assms
proof (induction rule: u_disciplined_trace.induct)
  case (ud_refl t) show ?case by (rule dwu_temporal_trace.dwu_refl)
next
  case (ud_nonpub t a g t' as t'')
  show ?case
    by (rule dwu_temporal_trace.dwu_lift_step
              [OF ud_nonpub.hyps(1) ud_nonpub.hyps(2) ud_nonpub.hyps(4) ud_nonpub.IH])
next
  case (ud_publish t c e g t' as t'')
  show ?case
    by (rule dwu_temporal_trace.dwu_lift_step
              [OF ud_publish.hyps(1) ud_publish.hyps(2) ud_publish.hyps(6) ud_publish.IH])
next
  case (ud_publost t c e g t' as t'')
  show ?case
    by (rule dwu_temporal_trace.dwu_publost_step
              [OF ud_publost.hyps(1) ud_publost.hyps(2) ud_publost.hyps(3) ud_publost.IH])
next
  case (ud_snap v t c k g t' as t'')
  show ?case
    by (rule dwu_temporal_trace.dwu_other_step) (auto intro: ud_snap.hyps(2) ud_snap.IH)
next
  case (ud_spawn t t' as t'')
  show ?case
    by (rule dwu_temporal_trace.dwu_other_step) (auto intro: ud_spawn.hyps(1) ud_spawn.IH)
next
  case (ud_release t g t' as t'')
  show ?case
    by (rule dwu_temporal_trace.dwu_other_step) (auto intro: ud_release.hyps(1) ud_release.IH)
next
  case (ud_claim t g f t' as t'')
  show ?case
    by (rule dwu_temporal_trace.dwu_other_step) (auto intro: ud_claim.hyps(2) ud_claim.IH)
next
  case (ud_fire t g t' as t'')
  show ?case
    by (rule dwu_temporal_trace.dwu_other_step) (auto intro: ud_fire.hyps(1) ud_fire.IH)
next
  case (ud_retain t n t' as t'')
  show ?case
    by (rule dwu_temporal_trace.dwu_other_step) (auto intro: ud_retain.hyps(1) ud_retain.IH)
next
  case (ud_cursor_recovery R t f m B g t1 t2 t3 as t'')
  have tail: "dwu_temporal_trace t2 (UFire g # as) t''"
    by (rule dwu_temporal_trace.dwu_other_step)
       (auto intro: ud_cursor_recovery.hyps(9) ud_cursor_recovery.IH)
  have mid: "dwu_temporal_trace t1 (UHeal g f # UFire g # as) t''"
    by (rule dwu_temporal_trace.dwu_other_step) (auto intro: ud_cursor_recovery.hyps(8) tail)
  show ?case
    by (rule dwu_temporal_trace.dwu_other_step)
       (auto intro: ud_cursor_recovery.hyps(7) mid)
qed

text \<open>The discipline never emits a truncating crash (D5, grammar-level).\<close>

lemma u_disc_no_trunc:
  assumes "u_disciplined_trace s acts t"
  shows "\<forall>d c. UTruncCrash d c \<notin> set acts"
  using assms by (induction rule: u_disciplined_trace.induct) auto


section \<open>6. Owed / accepted monotonicity along temporal traces\<close>

lemma u_temporal_owed_antitone:
  assumes "dwu_temporal_trace s xs t"
      and "\<forall>g c e. ULift g (DoSource c e) \<in> set xs \<longrightarrow> \<not> src_le c f"
      and "\<forall>d c. UTruncCrash d c \<notin> set xs"
  shows "set (u_owed f t) \<subseteq> set (u_owed f s)"
  using assms
proof (induction rule: dwu_temporal_trace.induct)
  case (dwu_refl t) show ?case by simp
next
  case (dwu_lift_step t a g t' as t'')
  have hd: "set (u_owed f t') \<subseteq> set (u_owed f t)"
    by (rule u_step_owed_antitone[OF dwu_lift_step.hyps(3)])
       (use dwu_lift_step.prems in auto)
  from dwu_lift_step.IH dwu_lift_step.prems have "set (u_owed f t'') \<subseteq> set (u_owed f t')"
    by auto
  with hd show ?case by simp
next
  case (dwu_publost_step t c e g t' as t'')
  have hd: "set (u_owed f t') \<subseteq> set (u_owed f t)"
    by (rule u_step_owed_antitone[OF dwu_publost_step.hyps(3)]) auto
  from dwu_publost_step.IH dwu_publost_step.prems have "set (u_owed f t'') \<subseteq> set (u_owed f t')"
    by auto
  with hd show ?case by simp
next
  case (dwu_other_step \<alpha> t t' as t'')
  have hd: "set (u_owed f t') \<subseteq> set (u_owed f t)"
    by (rule u_step_owed_antitone[OF dwu_other_step.hyps(3)])
       (use dwu_other_step.hyps(1) dwu_other_step.prems in auto)
  from dwu_other_step.IH dwu_other_step.prems have "set (u_owed f t'') \<subseteq> set (u_owed f t')"
    by auto
  with hd show ?case by simp
qed

lemma u_temporal_accepted_grow:
  assumes "dwu_temporal_trace s xs t"
  shows "\<exists>ys. dwu_accepted t = dwu_accepted s @ ys"
  using assms
proof (induction rule: dwu_temporal_trace.induct)
  case (dwu_refl t) show ?case by simp
next
  case (dwu_lift_step t a g t' as t'')
  from u_step_accepted_grow[OF dwu_lift_step.hyps(3)] obtain y1 where
    "dwu_accepted t' = dwu_accepted t @ y1" by blast
  moreover from dwu_lift_step.IH obtain y2 where
    "dwu_accepted t'' = dwu_accepted t' @ y2" by blast
  ultimately show ?case by (metis append.assoc)
next
  case (dwu_publost_step t c e g t' as t'')
  from u_step_accepted_grow[OF dwu_publost_step.hyps(3)] obtain y1 where
    "dwu_accepted t' = dwu_accepted t @ y1" by blast
  moreover from dwu_publost_step.IH obtain y2 where
    "dwu_accepted t'' = dwu_accepted t' @ y2" by blast
  ultimately show ?case by (metis append.assoc)
next
  case (dwu_other_step \<alpha> t t' as t'')
  from u_step_accepted_grow[OF dwu_other_step.hyps(3)] obtain y1 where
    "dwu_accepted t' = dwu_accepted t @ y1" by blast
  moreover from dwu_other_step.IH obtain y2 where
    "dwu_accepted t'' = dwu_accepted t' @ y2" by blast
  ultimately show ?case by (metis append.assoc)
qed

lemma u_temporal_accepted_set_mono:
  assumes "dwu_temporal_trace s xs t"
  shows "set (log_payloads (dwu_accepted s)) \<subseteq> set (log_payloads (dwu_accepted t))"
proof -
  from u_temporal_accepted_grow[OF assms] obtain ys where
    "dwu_accepted t = dwu_accepted s @ ys" by blast
  thus ?thesis by (simp add: log_payloads_append)
qed


section \<open>7. U8 completed-claim, part 1: the T2.9 suffix-freshness idiom\<close>

theorem u_at_least_once_persists_fresh_suffix:   \<comment> \<open>the T2.9 suffix-freshness idiom:
  the at-least-once conjunct persists along any disciplined suffix with no
  sub-frontier DoSource\<close>
  assumes "u_disciplined_trace u acts t"
      and "u_at_least_once_at f u"
      and "\<forall>g c e. ULift g (DoSource c e) \<in> set acts \<longrightarrow> \<not> src_le c f"
  shows "u_at_least_once_at f t"
proof -
  from u_disciplined_imp_temporal[OF assms(1)] have temp: "dwu_temporal_trace u acts t" .
  from u_disc_no_trunc[OF assms(1)] have notrunc: "\<forall>d c. UTruncCrash d c \<notin> set acts" .
  have owed: "set (u_owed f t) \<subseteq> set (u_owed f u)"
    by (rule u_temporal_owed_antitone[OF temp assms(3) notrunc])
  have acc: "set (log_payloads (dwu_accepted u)) \<subseteq> set (log_payloads (dwu_accepted t))"
    by (rule u_temporal_accepted_set_mono[OF temp])
  from assms(2) have base: "set (u_owed f u) \<subseteq> set (log_payloads (dwu_accepted u))"
    by (simp add: u_at_least_once_at_owed)
  from owed base acc have "set (u_owed f t) \<subseteq> set (log_payloads (dwu_accepted t))" by blast
  thus ?thesis by (simp add: u_at_least_once_at_owed)
qed


section \<open>8. Fence monotonicity (non-decreasing along temporal traces)\<close>

lemma u_step_fence_mono:
  assumes "dwu_step t \<alpha> t'"
  shows "dwu_fence t \<le> dwu_fence t'"
  using assms by (cases rule: dwu_step.cases) auto

lemma u_temporal_fence_mono:
  assumes "dwu_temporal_trace s xs t"
  shows "dwu_fence s \<le> dwu_fence t"
  using assms
proof (induction rule: dwu_temporal_trace.induct)
  case (dwu_refl t) show ?case by simp
next
  case (dwu_lift_step t a g t' as t'')
  from u_step_fence_mono[OF dwu_lift_step.hyps(3)] dwu_lift_step.IH show ?case by simp
next
  case (dwu_publost_step t c e g t' as t'')
  from u_step_fence_mono[OF dwu_publost_step.hyps(3)] dwu_publost_step.IH show ?case by simp
next
  case (dwu_other_step \<alpha> t t' as t'')
  from u_step_fence_mono[OF dwu_other_step.hyps(3)] dwu_other_step.IH show ?case by simp
qed


section \<open>9. Prefix decomposition helpers for the completed claim\<close>

lemma dwu_temporal_NilD:
  assumes "dwu_temporal_trace s [] u" shows "u = s"
  using assms by (cases rule: dwu_temporal_trace.cases) auto

text \<open>Peel one front action off a temporal trace, pinned by determinism.\<close>

lemma dwu_temporal_peel1:
  assumes "dwu_temporal_trace s (a # rest) u" and "dwu_step s a s'"
  shows "dwu_temporal_trace s' rest u"
proof -
  from dwu_temporal_trace_ConsD[OF assms(1)] obtain s1 where
    s1: "dwu_step s a s1" and tl: "dwu_temporal_trace s1 rest u" by blast
  from dwu_step_deterministic[OF assms(2) s1] have "s' = s1" .
  with tl show ?thesis by simp
qed

lemma dwu_temporal_snocD:
  assumes "dwu_temporal_trace s ys u"
  shows "\<And>xs a. ys = xs @ [a] \<Longrightarrow> \<exists>m. dwu_temporal_trace s xs m \<and> dwu_step m a u"
  using assms
proof (induction rule: dwu_temporal_trace.induct)
  case (dwu_refl t) thus ?case by simp
next
  case (dwu_lift_step t a0 g t' as t'')
  show ?case
  proof (cases as rule: rev_cases)
    case Nil
    with dwu_lift_step.prems have xa: "xs = []" "a = ULift g a0" by auto
    from dwu_lift_step.hyps(4) Nil have "t'' = t'" by (simp add: dwu_temporal_NilD)
    with dwu_lift_step.hyps(3) xa show ?thesis
      by (auto intro: dwu_temporal_trace.dwu_refl)
  next
    case (snoc ys' b)
    with dwu_lift_step.prems have xa: "xs = ULift g a0 # ys'" "a = b" by auto
    from dwu_lift_step.IH[OF snoc] obtain m where
      m1: "dwu_temporal_trace t' ys' m" and m2: "dwu_step m b t''" by blast
    have "dwu_temporal_trace t (ULift g a0 # ys') m"
      by (rule dwu_temporal_trace.dwu_lift_step
                [OF dwu_lift_step.hyps(1) dwu_lift_step.hyps(2) dwu_lift_step.hyps(3) m1])
    with m2 xa show ?thesis by blast
  qed
next
  case (dwu_publost_step t c e g t' as t'')
  show ?case
  proof (cases as rule: rev_cases)
    case Nil
    with dwu_publost_step.prems have xa: "xs = []" "a = UPubLost g c e" by auto
    from dwu_publost_step.hyps(4) Nil have "t'' = t'" by (simp add: dwu_temporal_NilD)
    with dwu_publost_step.hyps(3) xa show ?thesis
      by (auto intro: dwu_temporal_trace.dwu_refl)
  next
    case (snoc ys' b)
    with dwu_publost_step.prems have xa: "xs = UPubLost g c e # ys'" "a = b" by auto
    from dwu_publost_step.IH[OF snoc] obtain m where
      m1: "dwu_temporal_trace t' ys' m" and m2: "dwu_step m b t''" by blast
    have "dwu_temporal_trace t (UPubLost g c e # ys') m"
      by (rule dwu_temporal_trace.dwu_publost_step
                [OF dwu_publost_step.hyps(1) dwu_publost_step.hyps(2)
                    dwu_publost_step.hyps(3) m1])
    with m2 xa show ?thesis by blast
  qed
next
  case (dwu_other_step \<alpha> t t' as t'')
  show ?case
  proof (cases as rule: rev_cases)
    case Nil
    with dwu_other_step.prems have xa: "xs = []" "a = \<alpha>" by auto
    from dwu_other_step.hyps(4) Nil have "t'' = t'" by (simp add: dwu_temporal_NilD)
    with dwu_other_step.hyps(3) xa show ?thesis
      by (auto intro: dwu_temporal_trace.dwu_refl)
  next
    case (snoc ys' b)
    with dwu_other_step.prems have xa: "xs = \<alpha> # ys'" "a = b" by auto
    from dwu_other_step.IH[OF snoc] obtain m where
      m1: "dwu_temporal_trace t' ys' m" and m2: "dwu_step m b t''" by blast
    have "dwu_temporal_trace t (\<alpha> # ys') m"
      by (rule dwu_temporal_trace.dwu_other_step
                [OF dwu_other_step.hyps(1) dwu_other_step.hyps(2) dwu_other_step.hyps(3) m1])
    with m2 xa show ?thesis by blast
  qed
qed

text \<open>Dropping @{term p} front actions shifts a claim window down by @{term p}.\<close>

lemma u_claim_of_drop:
  assumes "u_claim_of acts i j g f" and "p \<le> i"
  shows "u_claim_of (drop p acts) (i - p) (j - p) g f"
proof -
  from assms(1) have
    ij: "i < j" and jl: "j < length acts" and
    ai: "acts ! i = UArmF g f" and aj: "acts ! j = UFire g" and
    mid: "\<forall>n. i < n \<and> n < j \<longrightarrow> acts ! n \<noteq> UFire g \<and> (\<forall>f'. acts ! n \<noteq> UArmF g f')"
    by (auto simp: u_claim_of_def)
  from assms(2) ij have pj: "p < j" by linarith
  have "i - p < j - p" using ij assms(2) by linarith
  moreover have "j - p < length (drop p acts)" using jl pj assms(2) by simp
  moreover have "drop p acts ! (i - p) = UArmF g f" using ai assms(2) jl pj by simp
  moreover have "drop p acts ! (j - p) = UFire g" using aj pj jl by simp
  moreover have "\<forall>n. i - p < n \<and> n < j - p \<longrightarrow>
        drop p acts ! n \<noteq> UFire g \<and> (\<forall>f'. drop p acts ! n \<noteq> UArmF g f')"
  proof (intro allI impI)
    fix n assume "i - p < n \<and> n < j - p"
    then have n1: "i - p < n" and n2: "n < j - p" by auto
    have lo: "i < p + n" and hi: "p + n < j" using n1 n2 assms(2) by linarith+
    from lo hi mid have "acts ! (p + n) \<noteq> UFire g \<and> (\<forall>f'. acts ! (p + n) \<noteq> UArmF g f')" by simp
    moreover have "drop p acts ! n = acts ! (p + n)" using n2 jl assms(2) by simp
    ultimately show "drop p acts ! n \<noteq> UFire g \<and> (\<forall>f'. drop p acts ! n \<noteq> UArmF g f')" by simp
  qed
  ultimately show ?thesis by (simp add: u_claim_of_def)
qed

lemma u_window_fresh_drop:
  assumes "u_window_fresh acts i j f" and "p \<le> i" and "j \<le> length acts"
  shows "u_window_fresh (drop p acts) (i - p) (j - p) f"
proof (unfold u_window_fresh_def, intro allI impI)
  fix n g' c e
  assume "i - p < n \<and> n < j - p \<and> drop p acts ! n = ULift g' (DoSource c e)"
  then have n1: "i - p < n" and n2: "n < j - p" and
    nth: "drop p acts ! n = ULift g' (DoSource c e)" by auto
  from n1 assms(2) have lo: "i < p + n" by linarith
  from n2 have hi: "p + n < j" by linarith
  from n2 assms(3) assms(2) have "p + n < length acts" by linarith
  hence "drop p acts ! n = acts ! (p + n)" by simp
  with nth have "acts ! (p + n) = ULift g' (DoSource c e)" by simp
  with lo hi assms(1) show "\<not> src_le c f" by (auto simp: u_window_fresh_def)
qed

text \<open>The set-algebra core of the arm-time covering: the owed set splits into the
  already-accepted part and the sink delta.\<close>

lemma u_sink_delta_owed_split:
  "set (u_owed f t)
     \<subseteq> set (log_payloads (dwu_accepted t)) \<union> set (u_sink_delta f t)"
  by (auto simp: u_sink_delta_def)

lemma cover_step:
  assumes "set (u_owed f s') \<subseteq> set (u_owed f s)"
      and "set (log_payloads (dwu_accepted s)) \<subseteq> set (log_payloads (dwu_accepted s'))"
      and "set (u_owed f s) \<subseteq> set (log_payloads (dwu_accepted s)) \<union> set (log_payloads B)"
  shows "set (u_owed f s') \<subseteq> set (log_payloads (dwu_accepted s')) \<union> set (log_payloads B)"
  using assms by blast

lemma dwu_init_dom:
  "dom (dwu_gens (dwu_init b K fin)) \<subseteq> {0..dwu_hwm (dwu_init b K fin)}"
  by (auto simp: dwu_init_def)

lemma dwu_init_disc_inv: "u_disc_inv (dwu_init b K fin)"
  by (rule u_disc_inv_init)

text \<open>Accepted-set monotonicity for a single step, at the log-payload level.\<close>

lemma u_step_accepted_set_mono:
  assumes "dwu_step t \<alpha> t'"
  shows "set (log_payloads (dwu_accepted t)) \<subseteq> set (log_payloads (dwu_accepted t'))"
proof -
  from u_step_accepted_grow[OF assms] obtain ys where
    "dwu_accepted t' = dwu_accepted t @ ys" by blast
  thus ?thesis by (simp add: log_payloads_append)
qed

text \<open>Shifting the raw window guards down by one front action.\<close>

lemma noarm_ConsD:
  assumes "\<forall>n<j. (a # as) ! n \<noteq> UFire g \<and> (\<forall>f'. (a # as) ! n \<noteq> UArmF g f')"
  shows "\<forall>n<j - 1. as ! n \<noteq> UFire g \<and> (\<forall>f'. as ! n \<noteq> UArmF g f')"
proof (intro allI impI)
  fix n assume "n < j - 1"
  hence "Suc n < j" by linarith
  from assms[rule_format, OF this] show "as ! n \<noteq> UFire g \<and> (\<forall>f'. as ! n \<noteq> UArmF g f')"
    by simp
qed

lemma wfresh_ConsD:
  assumes "\<forall>n g' c e. n < j \<and> (a # as) ! n = ULift g' (DoSource c e) \<longrightarrow> \<not> src_le c f"
  shows "\<forall>n g' c e. n < j - 1 \<and> as ! n = ULift g' (DoSource c e) \<longrightarrow> \<not> src_le c f"
proof (intro allI impI, elim conjE)
  fix n g' c e assume lt: "n < j - 1" and nth: "as ! n = ULift g' (DoSource c e)"
  from lt have "Suc n < j" by linarith
  moreover from nth have "(a # as) ! Suc n = ULift g' (DoSource c e)" by simp
  ultimately show "\<not> src_le c f" using assms by blast
qed


section \<open>10. The window-covering invariant (arm-to-fire)\<close>

text \<open>From the post-@{const UArmF} state @{term s} (gen @{term g} armed with @{term B},
  fence @{text "\<le> g"}, the owed set covered by accepted \<union> B), a disciplined window
  with no re-arm/re-fire of @{term g} and no sub-frontier commit carries the covering to
  the pre-fire state @{term tj}.  A concurrent cursor triple cannot intervene: it would
  need every armed gen strictly below the fence, but @{term g} is armed AT the fence.\<close>

lemma window_covering:
  "u_disciplined_trace s ws t \<Longrightarrow> u_disc_inv s \<Longrightarrow> dom (dwu_gens s) \<subseteq> {0..dwu_hwm s} \<Longrightarrow>
   dwu_gens s g = Some (UArmed B) \<Longrightarrow> dwu_fence s \<le> g \<Longrightarrow>
   set (u_owed f s) \<subseteq> set (log_payloads (dwu_accepted s)) \<union> set (log_payloads B) \<Longrightarrow>
   j < length ws \<Longrightarrow> ws ! j = UFire g \<Longrightarrow>
   (\<forall>n<j. ws ! n \<noteq> UFire g \<and> (\<forall>f'. ws ! n \<noteq> UArmF g f')) \<Longrightarrow>
   (\<forall>n g' c e. n < j \<and> ws ! n = ULift g' (DoSource c e) \<longrightarrow> \<not> src_le c f) \<Longrightarrow>
   dwu_temporal_trace s (take j ws) tj \<Longrightarrow> dwu_fence tj \<le> g \<Longrightarrow>
   u_disc_inv tj \<and> dwu_gens tj g = Some (UArmed B) \<and>
     set (u_owed f tj) \<subseteq> set (log_payloads (dwu_accepted tj)) \<union> set (log_payloads B)"
proof (induction arbitrary: j tj rule: u_disciplined_trace.induct)
  case (ud_refl s) then show ?case by simp
next
  case (ud_cursor_recovery R s fu m Bu gu s1 s2 s3 as t'')
  from u_disc_invD(4)[OF ud_cursor_recovery.prems(1) ud_cursor_recovery.prems(3)]
  have "g \<le> dwu_fence s" .
  with ud_cursor_recovery.prems(4) have "dwu_fence s = g" by simp
  moreover from ud_cursor_recovery.hyps(5) ud_cursor_recovery.prems(3)
  have "g < dwu_fence s" by blast
  ultimately show ?case by simp
next
  case (ud_fire s gu s' as t'')
  show ?case
  proof (cases "j = 0")
    case True
    \<comment> \<open>the fire at the head: @{term "gu = g"}, @{term "tj = s"}\<close>
    from ud_fire.prems(7) True have gug: "gu = g" by simp
    from ud_fire.prems(10) True have "dwu_temporal_trace s [] tj" by simp
    hence "tj = s" by (rule dwu_temporal_NilD)
    with ud_fire.prems(1,3,5) show ?thesis by simp
  next
    case False
    then have j1: "0 < j" by simp
    have step: "dwu_step s (UFire gu) s'" by (rule ud_fire.hyps(1))
    from ud_fire.prems(8) j1 have "(UFire gu # as) ! 0 \<noteq> UFire g" by blast
    hence gune: "gu \<noteq> g" by simp
    have inv': "u_disc_inv s'" by (rule pres_fire[OF ud_fire.prems(1) step])
    have dom': "dom (dwu_gens s') \<subseteq> {0..dwu_hwm s'}"
      by (rule u_gens_dom_step[OF step ud_fire.prems(2)])
    from dwu_step_fire_full[OF step] obtain Bf where
      gf: "dwu_gens s' = (dwu_gens s)(gu \<mapsto> UProd)" by blast
    have armed': "dwu_gens s' g = Some (UArmed B)"
      using gf gune ud_fire.prems(3) by simp
    from ud_fire.prems(10) j1 have "dwu_temporal_trace s (UFire gu # take (j-1) as) tj"
      by (simp add: take_Cons')
    from dwu_temporal_peel1[OF this step] have tjtail: "dwu_temporal_trace s' (take (j-1) as) tj" .
    have fence': "dwu_fence s' \<le> g"
      using u_temporal_fence_mono[OF tjtail] ud_fire.prems(11) by simp
    have anti: "set (u_owed f s') \<subseteq> set (u_owed f s)"
      by (rule u_step_owed_antitone[OF step]) auto
    have grow: "set (log_payloads (dwu_accepted s)) \<subseteq> set (log_payloads (dwu_accepted s'))"
      by (rule u_step_accepted_set_mono[OF step])
    have cover': "set (u_owed f s') \<subseteq> set (log_payloads (dwu_accepted s')) \<union> set (log_payloads B)"
      by (rule cover_step[OF anti grow ud_fire.prems(5)])
    have jbound': "j - 1 < length as" using ud_fire.prems(6) j1 by simp
    have jfire': "as ! (j-1) = UFire g" using ud_fire.prems(7) j1 by (simp add: nth_Cons')
    show ?thesis
      by (rule ud_fire.IH[OF inv' dom' armed' fence' cover' jbound' jfire'
                             noarm_ConsD[OF ud_fire.prems(8)] wfresh_ConsD[OF ud_fire.prems(9)]
                             tjtail ud_fire.prems(11)])
  qed
next
  case (ud_nonpub s a gu s' as t'')
  show ?case
  proof (cases "j = 0")
    case True with ud_nonpub.prems(7) show ?thesis by simp
  next
    case False
    then have j1: "0 < j" by simp
    have step: "dwu_step s (ULift gu a) s'" by (rule ud_nonpub.hyps(4))
    have inv': "u_disc_inv s'"
      by (rule pres_nonpub[OF ud_nonpub.prems(1) ud_nonpub.hyps(3) step])
    have dom': "dom (dwu_gens s') \<subseteq> {0..dwu_hwm s'}"
      by (rule u_gens_dom_step[OF step ud_nonpub.prems(2)])
    from dwu_lift_nonpub_shape[OF step ud_nonpub.hyps(3)]
    have "dwu_gens s' = dwu_gens s" by simp
    hence armed': "dwu_gens s' g = Some (UArmed B)" using ud_nonpub.prems(3) by simp
    from ud_nonpub.prems(10) j1 have "dwu_temporal_trace s (ULift gu a # take (j-1) as) tj"
      by (simp add: take_Cons')
    from dwu_temporal_peel1[OF this step] have tjtail: "dwu_temporal_trace s' (take (j-1) as) tj" .
    have fence': "dwu_fence s' \<le> g"
      using u_temporal_fence_mono[OF tjtail] ud_nonpub.prems(11) by simp
    have anti: "set (u_owed f s') \<subseteq> set (u_owed f s)"
    proof (rule u_step_owed_antitone[OF step])
      fix gx cx ex assume "ULift gu a = ULift gx (DoSource cx ex)"
      hence "a = DoSource cx ex" and "gx = gu" by auto
      with ud_nonpub.prems(9) j1 show "\<not> src_le cx f" by fastforce
    qed auto
    have grow: "set (log_payloads (dwu_accepted s)) \<subseteq> set (log_payloads (dwu_accepted s'))"
      by (rule u_step_accepted_set_mono[OF step])
    have cover': "set (u_owed f s') \<subseteq> set (log_payloads (dwu_accepted s')) \<union> set (log_payloads B)"
      by (rule cover_step[OF anti grow ud_nonpub.prems(5)])
    have jbound': "j - 1 < length as" using ud_nonpub.prems(6) j1 by simp
    have jfire': "as ! (j-1) = UFire g" using ud_nonpub.prems(7) j1 by (simp add: nth_Cons')
    show ?thesis
      by (rule ud_nonpub.IH[OF inv' dom' armed' fence' cover' jbound' jfire'
                               noarm_ConsD[OF ud_nonpub.prems(8)] wfresh_ConsD[OF ud_nonpub.prems(9)]
                               tjtail ud_nonpub.prems(11)])
  qed
next
  case (ud_publish s c e gu s' as t'')
  show ?case
  proof (cases "j = 0")
    case True with ud_publish.prems(7) show ?thesis by simp
  next
    case False
    then have j1: "0 < j" by simp
    have step: "dwu_step s (ULift gu (DoDownstream c e)) s'" by (rule ud_publish.hyps(6))
    have inv': "u_disc_inv s'"
      by (rule pres_publish[OF ud_publish.prems(1) ud_publish.hyps(3) ud_publish.hyps(4)
                               ud_publish.hyps(5) step])
    have dom': "dom (dwu_gens s') \<subseteq> {0..dwu_hwm s'}"
      by (rule u_gens_dom_step[OF step ud_publish.prems(2)])
    from dwu_step_publish_full[OF step] have "dwu_gens s' = dwu_gens s" by blast
    hence armed': "dwu_gens s' g = Some (UArmed B)" using ud_publish.prems(3) by simp
    from ud_publish.prems(10) j1
    have "dwu_temporal_trace s (ULift gu (DoDownstream c e) # take (j-1) as) tj"
      by (simp add: take_Cons')
    from dwu_temporal_peel1[OF this step] have tjtail: "dwu_temporal_trace s' (take (j-1) as) tj" .
    have fence': "dwu_fence s' \<le> g"
      using u_temporal_fence_mono[OF tjtail] ud_publish.prems(11) by simp
    have anti: "set (u_owed f s') \<subseteq> set (u_owed f s)"
      by (rule u_step_owed_antitone[OF step]) auto
    have grow: "set (log_payloads (dwu_accepted s)) \<subseteq> set (log_payloads (dwu_accepted s'))"
      by (rule u_step_accepted_set_mono[OF step])
    have cover': "set (u_owed f s') \<subseteq> set (log_payloads (dwu_accepted s')) \<union> set (log_payloads B)"
      by (rule cover_step[OF anti grow ud_publish.prems(5)])
    have jbound': "j - 1 < length as" using ud_publish.prems(6) j1 by simp
    have jfire': "as ! (j-1) = UFire g" using ud_publish.prems(7) j1 by (simp add: nth_Cons')
    show ?thesis
      by (rule ud_publish.IH[OF inv' dom' armed' fence' cover' jbound' jfire'
                                noarm_ConsD[OF ud_publish.prems(8)] wfresh_ConsD[OF ud_publish.prems(9)]
                                tjtail ud_publish.prems(11)])
  qed
next
  case (ud_publost s c e gu s' as t'')
  show ?case
  proof (cases "j = 0")
    case True with ud_publost.prems(7) show ?thesis by simp
  next
    case False
    then have j1: "0 < j" by simp
    have step: "dwu_step s (UPubLost gu c e) s'" by (rule ud_publost.hyps(3))
    have inv': "u_disc_inv s'" by (rule pres_publost[OF ud_publost.prems(1) step])
    have dom': "dom (dwu_gens s') \<subseteq> {0..dwu_hwm s'}"
      by (rule u_gens_dom_step[OF step ud_publost.prems(2)])
    from dwu_step_publost_full[OF step] have "dwu_gens s' = dwu_gens s" by blast
    hence armed': "dwu_gens s' g = Some (UArmed B)" using ud_publost.prems(3) by simp
    from ud_publost.prems(10) j1 have "dwu_temporal_trace s (UPubLost gu c e # take (j-1) as) tj"
      by (simp add: take_Cons')
    from dwu_temporal_peel1[OF this step] have tjtail: "dwu_temporal_trace s' (take (j-1) as) tj" .
    have fence': "dwu_fence s' \<le> g"
      using u_temporal_fence_mono[OF tjtail] ud_publost.prems(11) by simp
    have anti: "set (u_owed f s') \<subseteq> set (u_owed f s)"
      by (rule u_step_owed_antitone[OF step]) auto
    have grow: "set (log_payloads (dwu_accepted s)) \<subseteq> set (log_payloads (dwu_accepted s'))"
      by (rule u_step_accepted_set_mono[OF step])
    have cover': "set (u_owed f s') \<subseteq> set (log_payloads (dwu_accepted s')) \<union> set (log_payloads B)"
      by (rule cover_step[OF anti grow ud_publost.prems(5)])
    have jbound': "j - 1 < length as" using ud_publost.prems(6) j1 by simp
    have jfire': "as ! (j-1) = UFire g" using ud_publost.prems(7) j1 by (simp add: nth_Cons')
    show ?thesis
      by (rule ud_publost.IH[OF inv' dom' armed' fence' cover' jbound' jfire'
                                noarm_ConsD[OF ud_publost.prems(8)] wfresh_ConsD[OF ud_publost.prems(9)]
                                tjtail ud_publost.prems(11)])
  qed
next
  case (ud_snap v s c k gu s' as t'')
  show ?case
  proof (cases "j = 0")
    case True with ud_snap.prems(7) show ?thesis by simp
  next
    case False
    then have j1: "0 < j" by simp
    have step: "dwu_step s (USnapE gu c k v) s'" by (rule ud_snap.hyps(2))
    have inv': "u_disc_inv s'" by (rule pres_snap[OF ud_snap.prems(1) ud_snap.hyps(1) step])
    have dom': "dom (dwu_gens s') \<subseteq> {0..dwu_hwm s'}"
      by (rule u_gens_dom_step[OF step ud_snap.prems(2)])
    from dwu_step_snap_full[OF step] have "dwu_gens s' = dwu_gens s" by simp
    hence armed': "dwu_gens s' g = Some (UArmed B)" using ud_snap.prems(3) by simp
    from ud_snap.prems(10) j1 have "dwu_temporal_trace s (USnapE gu c k v # take (j-1) as) tj"
      by (simp add: take_Cons')
    from dwu_temporal_peel1[OF this step] have tjtail: "dwu_temporal_trace s' (take (j-1) as) tj" .
    have fence': "dwu_fence s' \<le> g"
      using u_temporal_fence_mono[OF tjtail] ud_snap.prems(11) by simp
    have anti: "set (u_owed f s') \<subseteq> set (u_owed f s)"
      by (rule u_step_owed_antitone[OF step]) auto
    have grow: "set (log_payloads (dwu_accepted s)) \<subseteq> set (log_payloads (dwu_accepted s'))"
      by (rule u_step_accepted_set_mono[OF step])
    have cover': "set (u_owed f s') \<subseteq> set (log_payloads (dwu_accepted s')) \<union> set (log_payloads B)"
      by (rule cover_step[OF anti grow ud_snap.prems(5)])
    have jbound': "j - 1 < length as" using ud_snap.prems(6) j1 by simp
    have jfire': "as ! (j-1) = UFire g" using ud_snap.prems(7) j1 by (simp add: nth_Cons')
    show ?thesis
      by (rule ud_snap.IH[OF inv' dom' armed' fence' cover' jbound' jfire'
                             noarm_ConsD[OF ud_snap.prems(8)] wfresh_ConsD[OF ud_snap.prems(9)]
                             tjtail ud_snap.prems(11)])
  qed
next
  case (ud_spawn s s' as t'')
  show ?case
  proof (cases "j = 0")
    case True with ud_spawn.prems(7) show ?thesis by simp
  next
    case False
    then have j1: "0 < j" by simp
    have step: "dwu_step s USpawn s'" by (rule ud_spawn.hyps(1))
    have inv': "u_disc_inv s'" by (rule pres_spawn[OF ud_spawn.prems(1) step])
    have dom': "dom (dwu_gens s') \<subseteq> {0..dwu_hwm s'}"
      by (rule u_gens_dom_step[OF step ud_spawn.prems(2)])
    have gle: "g \<le> dwu_hwm s"
      using ud_spawn.prems(2) ud_spawn.prems(3) by (auto simp: domIff)
    from dwu_step_spawn_inv[OF step] have
      gspawn: "dwu_gens s' = (dwu_gens s)(Suc (dwu_hwm s) \<mapsto> UProd)" by simp
    have armed': "dwu_gens s' g = Some (UArmed B)"
      using gspawn gle ud_spawn.prems(3) by simp
    from ud_spawn.prems(10) j1 have "dwu_temporal_trace s (USpawn # take (j-1) as) tj"
      by (simp add: take_Cons')
    from dwu_temporal_peel1[OF this step] have tjtail: "dwu_temporal_trace s' (take (j-1) as) tj" .
    have fence': "dwu_fence s' \<le> g"
      using u_temporal_fence_mono[OF tjtail] ud_spawn.prems(11) by simp
    have anti: "set (u_owed f s') \<subseteq> set (u_owed f s)"
      by (rule u_step_owed_antitone[OF step]) auto
    have grow: "set (log_payloads (dwu_accepted s)) \<subseteq> set (log_payloads (dwu_accepted s'))"
      by (rule u_step_accepted_set_mono[OF step])
    have cover': "set (u_owed f s') \<subseteq> set (log_payloads (dwu_accepted s')) \<union> set (log_payloads B)"
      by (rule cover_step[OF anti grow ud_spawn.prems(5)])
    have jbound': "j - 1 < length as" using ud_spawn.prems(6) j1 by simp
    have jfire': "as ! (j-1) = UFire g" using ud_spawn.prems(7) j1 by (simp add: nth_Cons')
    show ?thesis
      by (rule ud_spawn.IH[OF inv' dom' armed' fence' cover' jbound' jfire'
                              noarm_ConsD[OF ud_spawn.prems(8)] wfresh_ConsD[OF ud_spawn.prems(9)]
                              tjtail ud_spawn.prems(11)])
  qed
next
  case (ud_release s gu s' as t'')
  show ?case
  proof (cases "j = 0")
    case True with ud_release.prems(7) show ?thesis by simp
  next
    case False
    then have j1: "0 < j" by simp
    have step: "dwu_step s (URelease gu) s'" by (rule ud_release.hyps(1))
    have inv': "u_disc_inv s'" by (rule pres_release[OF ud_release.prems(1) step])
    have dom': "dom (dwu_gens s') \<subseteq> {0..dwu_hwm s'}"
      by (rule u_gens_dom_step[OF step ud_release.prems(2)])
    from dwu_step_release_frame[OF step] have "dwu_gens s' = dwu_gens s" by simp
    hence armed': "dwu_gens s' g = Some (UArmed B)" using ud_release.prems(3) by simp
    from ud_release.prems(10) j1 have "dwu_temporal_trace s (URelease gu # take (j-1) as) tj"
      by (simp add: take_Cons')
    from dwu_temporal_peel1[OF this step] have tjtail: "dwu_temporal_trace s' (take (j-1) as) tj" .
    have fence': "dwu_fence s' \<le> g"
      using u_temporal_fence_mono[OF tjtail] ud_release.prems(11) by simp
    have anti: "set (u_owed f s') \<subseteq> set (u_owed f s)"
      by (rule u_step_owed_antitone[OF step]) auto
    have grow: "set (log_payloads (dwu_accepted s)) \<subseteq> set (log_payloads (dwu_accepted s'))"
      by (rule u_step_accepted_set_mono[OF step])
    have cover': "set (u_owed f s') \<subseteq> set (log_payloads (dwu_accepted s')) \<union> set (log_payloads B)"
      by (rule cover_step[OF anti grow ud_release.prems(5)])
    have jbound': "j - 1 < length as" using ud_release.prems(6) j1 by simp
    have jfire': "as ! (j-1) = UFire g" using ud_release.prems(7) j1 by (simp add: nth_Cons')
    show ?thesis
      by (rule ud_release.IH[OF inv' dom' armed' fence' cover' jbound' jfire'
                                noarm_ConsD[OF ud_release.prems(8)] wfresh_ConsD[OF ud_release.prems(9)]
                                tjtail ud_release.prems(11)])
  qed
next
  case (ud_retain s n s' as t'')
  show ?case
  proof (cases "j = 0")
    case True with ud_retain.prems(7) show ?thesis by simp
  next
    case False
    then have j1: "0 < j" by simp
    have step: "dwu_step s (URetain n) s'" by (rule ud_retain.hyps(1))
    have inv': "u_disc_inv s'" by (rule pres_retain[OF ud_retain.prems(1) step])
    have dom': "dom (dwu_gens s') \<subseteq> {0..dwu_hwm s'}"
      by (rule u_gens_dom_step[OF step ud_retain.prems(2)])
    from dwu_step_retain_full[OF step] have "dwu_gens s' = dwu_gens s" by simp
    hence armed': "dwu_gens s' g = Some (UArmed B)" using ud_retain.prems(3) by simp
    from ud_retain.prems(10) j1 have "dwu_temporal_trace s (URetain n # take (j-1) as) tj"
      by (simp add: take_Cons')
    from dwu_temporal_peel1[OF this step] have tjtail: "dwu_temporal_trace s' (take (j-1) as) tj" .
    have fence': "dwu_fence s' \<le> g"
      using u_temporal_fence_mono[OF tjtail] ud_retain.prems(11) by simp
    have anti: "set (u_owed f s') \<subseteq> set (u_owed f s)"
      by (rule u_step_owed_antitone[OF step]) auto
    have grow: "set (log_payloads (dwu_accepted s)) \<subseteq> set (log_payloads (dwu_accepted s'))"
      by (rule u_step_accepted_set_mono[OF step])
    have cover': "set (u_owed f s') \<subseteq> set (log_payloads (dwu_accepted s')) \<union> set (log_payloads B)"
      by (rule cover_step[OF anti grow ud_retain.prems(5)])
    have jbound': "j - 1 < length as" using ud_retain.prems(6) j1 by simp
    have jfire': "as ! (j-1) = UFire g" using ud_retain.prems(7) j1 by (simp add: nth_Cons')
    show ?thesis
      by (rule ud_retain.IH[OF inv' dom' armed' fence' cover' jbound' jfire'
                               noarm_ConsD[OF ud_retain.prems(8)] wfresh_ConsD[OF ud_retain.prems(9)]
                               tjtail ud_retain.prems(11)])
  qed
next
  case (ud_claim s gu fu s' as t'')
  show ?case
  proof (cases "j = 0")
    case True with ud_claim.prems(7) show ?thesis by simp
  next
    case False
    then have j1: "0 < j" by simp
    have step: "dwu_step s (UArmF gu fu) s'" by (rule ud_claim.hyps(2))
    have inv': "u_disc_inv s'" by (rule pres_claim[OF ud_claim.prems(1) ud_claim.hyps(1) step])
    have dom': "dom (dwu_gens s') \<subseteq> {0..dwu_hwm s'}"
      by (rule u_gens_dom_step[OF step ud_claim.prems(2)])
    from ud_claim.prems(8) j1 have "\<forall>f'. (UArmF gu fu # as) ! 0 \<noteq> UArmF g f'" by blast
    hence gune: "gu \<noteq> g" by auto
    from dwu_step_armf_full[OF step] have
      garmf: "dwu_gens s' = (dwu_gens s)(gu \<mapsto> UArmed (stamped_at (length (dwu_journal s)) gu (u_sink_delta fu s)))"
      by blast
    have armed': "dwu_gens s' g = Some (UArmed B)"
      using garmf gune ud_claim.prems(3) by simp
    from ud_claim.prems(10) j1 have "dwu_temporal_trace s (UArmF gu fu # take (j-1) as) tj"
      by (simp add: take_Cons')
    from dwu_temporal_peel1[OF this step] have tjtail: "dwu_temporal_trace s' (take (j-1) as) tj" .
    have fence': "dwu_fence s' \<le> g"
      using u_temporal_fence_mono[OF tjtail] ud_claim.prems(11) by simp
    have anti: "set (u_owed f s') \<subseteq> set (u_owed f s)"
      by (rule u_step_owed_antitone[OF step]) auto
    have grow: "set (log_payloads (dwu_accepted s)) \<subseteq> set (log_payloads (dwu_accepted s'))"
      by (rule u_step_accepted_set_mono[OF step])
    have cover': "set (u_owed f s') \<subseteq> set (log_payloads (dwu_accepted s')) \<union> set (log_payloads B)"
      by (rule cover_step[OF anti grow ud_claim.prems(5)])
    have jbound': "j - 1 < length as" using ud_claim.prems(6) j1 by simp
    have jfire': "as ! (j-1) = UFire g" using ud_claim.prems(7) j1 by (simp add: nth_Cons')
    show ?thesis
      by (rule ud_claim.IH[OF inv' dom' armed' fence' cover' jbound' jfire'
                              noarm_ConsD[OF ud_claim.prems(8)] wfresh_ConsD[OF ud_claim.prems(9)]
                              tjtail ud_claim.prems(11)])
  qed
qed


section \<open>11. Reaching the claim's UArmF, then covering to the fire\<close>

text \<open>The uniform one-action window shift used by every recursive case of
  @{text claim_reach}.\<close>

lemma claim_reach_step:
  assumes step: "dwu_step s a s'"
      and claim: "u_claim_of (a # as) i j g f"
      and wf: "u_window_fresh (a # as) i j f"
      and tj: "dwu_temporal_trace s (take j (a # as)) tj"
      and i1: "1 \<le> i"
  shows "u_claim_of as (i - 1) (j - 1) g f"
    and "u_window_fresh as (i - 1) (j - 1) f"
    and "dwu_temporal_trace s' (take (j - 1) as) tj"
proof -
  from claim have jl: "j < length (a # as)" and ij: "i < j" by (auto simp: u_claim_of_def)
  from jl have jle: "j \<le> length (a # as)" by simp
  from u_claim_of_drop[OF claim i1] show "u_claim_of as (i - 1) (j - 1) g f" by simp
  from u_window_fresh_drop[OF wf i1 jle] show "u_window_fresh as (i - 1) (j - 1) f" by simp
  from ij i1 have jpos: "0 < j" by linarith
  have "dwu_temporal_trace s (a # take (j - 1) as) tj" using tj jpos by (simp add: take_Cons')
  from dwu_temporal_peel1[OF this step] show "dwu_temporal_trace s' (take (j - 1) as) tj" .
qed

lemma claim_reach:
  "u_disciplined_trace s acts t \<Longrightarrow> u_disc_inv s \<Longrightarrow> dom (dwu_gens s) \<subseteq> {0..dwu_hwm s} \<Longrightarrow>
   u_claim_of acts i j g f \<Longrightarrow> u_window_fresh acts i j f \<Longrightarrow>
   dwu_temporal_trace s (take j acts) tj \<Longrightarrow> dwu_fence tj \<le> g \<Longrightarrow>
   u_disc_inv tj \<and> (\<exists>B. dwu_gens tj g = Some (UArmed B) \<and>
     set (u_owed f tj) \<subseteq> set (log_payloads (dwu_accepted tj)) \<union> set (log_payloads B))"
proof (induction arbitrary: i j tj rule: u_disciplined_trace.induct)
  case (ud_refl s) then show ?case by (simp add: u_claim_of_def)
next
  case (ud_nonpub s a gu s' as t'')
  from ud_nonpub.prems(3) have claim: "u_claim_of (ULift gu a # as) i j g f" .
  have i1: "1 \<le> i"
  proof (rule ccontr)
    assume "\<not> 1 \<le> i" hence "i = 0" by simp
    with claim show False by (simp add: u_claim_of_def)
  qed
  have step: "dwu_step s (ULift gu a) s'" by (rule ud_nonpub.hyps(4))
  have inv': "u_disc_inv s'" by (rule pres_nonpub[OF ud_nonpub.prems(1) ud_nonpub.hyps(3) step])
  have dom': "dom (dwu_gens s') \<subseteq> {0..dwu_hwm s'}"
    by (rule u_gens_dom_step[OF step ud_nonpub.prems(2)])
  note sh = claim_reach_step[OF step claim ud_nonpub.prems(4) ud_nonpub.prems(5) i1]
  show ?case by (rule ud_nonpub.IH[OF inv' dom' sh(1) sh(2) sh(3) ud_nonpub.prems(6)])
next
  case (ud_publish s c e gu s' as t'')
  from ud_publish.prems(3) have claim: "u_claim_of (ULift gu (DoDownstream c e) # as) i j g f" .
  have i1: "1 \<le> i"
  proof (rule ccontr)
    assume "\<not> 1 \<le> i" hence "i = 0" by simp
    with claim show False by (simp add: u_claim_of_def)
  qed
  have step: "dwu_step s (ULift gu (DoDownstream c e)) s'" by (rule ud_publish.hyps(6))
  have inv': "u_disc_inv s'"
    by (rule pres_publish[OF ud_publish.prems(1) ud_publish.hyps(3) ud_publish.hyps(4)
                             ud_publish.hyps(5) step])
  have dom': "dom (dwu_gens s') \<subseteq> {0..dwu_hwm s'}"
    by (rule u_gens_dom_step[OF step ud_publish.prems(2)])
  note sh = claim_reach_step[OF step claim ud_publish.prems(4) ud_publish.prems(5) i1]
  show ?case by (rule ud_publish.IH[OF inv' dom' sh(1) sh(2) sh(3) ud_publish.prems(6)])
next
  case (ud_publost s c e gu s' as t'')
  from ud_publost.prems(3) have claim: "u_claim_of (UPubLost gu c e # as) i j g f" .
  have i1: "1 \<le> i"
  proof (rule ccontr)
    assume "\<not> 1 \<le> i" hence "i = 0" by simp
    with claim show False by (simp add: u_claim_of_def)
  qed
  have step: "dwu_step s (UPubLost gu c e) s'" by (rule ud_publost.hyps(3))
  have inv': "u_disc_inv s'" by (rule pres_publost[OF ud_publost.prems(1) step])
  have dom': "dom (dwu_gens s') \<subseteq> {0..dwu_hwm s'}"
    by (rule u_gens_dom_step[OF step ud_publost.prems(2)])
  note sh = claim_reach_step[OF step claim ud_publost.prems(4) ud_publost.prems(5) i1]
  show ?case by (rule ud_publost.IH[OF inv' dom' sh(1) sh(2) sh(3) ud_publost.prems(6)])
next
  case (ud_snap v s c k gu s' as t'')
  from ud_snap.prems(3) have claim: "u_claim_of (USnapE gu c k v # as) i j g f" .
  have i1: "1 \<le> i"
  proof (rule ccontr)
    assume "\<not> 1 \<le> i" hence "i = 0" by simp
    with claim show False by (simp add: u_claim_of_def)
  qed
  have step: "dwu_step s (USnapE gu c k v) s'" by (rule ud_snap.hyps(2))
  have inv': "u_disc_inv s'" by (rule pres_snap[OF ud_snap.prems(1) ud_snap.hyps(1) step])
  have dom': "dom (dwu_gens s') \<subseteq> {0..dwu_hwm s'}"
    by (rule u_gens_dom_step[OF step ud_snap.prems(2)])
  note sh = claim_reach_step[OF step claim ud_snap.prems(4) ud_snap.prems(5) i1]
  show ?case by (rule ud_snap.IH[OF inv' dom' sh(1) sh(2) sh(3) ud_snap.prems(6)])
next
  case (ud_spawn s s' as t'')
  from ud_spawn.prems(3) have claim: "u_claim_of (USpawn # as) i j g f" .
  have i1: "1 \<le> i"
  proof (rule ccontr)
    assume "\<not> 1 \<le> i" hence "i = 0" by simp
    with claim show False by (simp add: u_claim_of_def)
  qed
  have step: "dwu_step s USpawn s'" by (rule ud_spawn.hyps(1))
  have inv': "u_disc_inv s'" by (rule pres_spawn[OF ud_spawn.prems(1) step])
  have dom': "dom (dwu_gens s') \<subseteq> {0..dwu_hwm s'}"
    by (rule u_gens_dom_step[OF step ud_spawn.prems(2)])
  note sh = claim_reach_step[OF step claim ud_spawn.prems(4) ud_spawn.prems(5) i1]
  show ?case by (rule ud_spawn.IH[OF inv' dom' sh(1) sh(2) sh(3) ud_spawn.prems(6)])
next
  case (ud_release s gu s' as t'')
  from ud_release.prems(3) have claim: "u_claim_of (URelease gu # as) i j g f" .
  have i1: "1 \<le> i"
  proof (rule ccontr)
    assume "\<not> 1 \<le> i" hence "i = 0" by simp
    with claim show False by (simp add: u_claim_of_def)
  qed
  have step: "dwu_step s (URelease gu) s'" by (rule ud_release.hyps(1))
  have inv': "u_disc_inv s'" by (rule pres_release[OF ud_release.prems(1) step])
  have dom': "dom (dwu_gens s') \<subseteq> {0..dwu_hwm s'}"
    by (rule u_gens_dom_step[OF step ud_release.prems(2)])
  note sh = claim_reach_step[OF step claim ud_release.prems(4) ud_release.prems(5) i1]
  show ?case by (rule ud_release.IH[OF inv' dom' sh(1) sh(2) sh(3) ud_release.prems(6)])
next
  case (ud_fire s gu s' as t'')
  from ud_fire.prems(3) have claim: "u_claim_of (UFire gu # as) i j g f" .
  have i1: "1 \<le> i"
  proof (rule ccontr)
    assume "\<not> 1 \<le> i" hence "i = 0" by simp
    with claim show False by (simp add: u_claim_of_def)
  qed
  have step: "dwu_step s (UFire gu) s'" by (rule ud_fire.hyps(1))
  have inv': "u_disc_inv s'" by (rule pres_fire[OF ud_fire.prems(1) step])
  have dom': "dom (dwu_gens s') \<subseteq> {0..dwu_hwm s'}"
    by (rule u_gens_dom_step[OF step ud_fire.prems(2)])
  note sh = claim_reach_step[OF step claim ud_fire.prems(4) ud_fire.prems(5) i1]
  show ?case by (rule ud_fire.IH[OF inv' dom' sh(1) sh(2) sh(3) ud_fire.prems(6)])
next
  case (ud_retain s n s' as t'')
  from ud_retain.prems(3) have claim: "u_claim_of (URetain n # as) i j g f" .
  have i1: "1 \<le> i"
  proof (rule ccontr)
    assume "\<not> 1 \<le> i" hence "i = 0" by simp
    with claim show False by (simp add: u_claim_of_def)
  qed
  have step: "dwu_step s (URetain n) s'" by (rule ud_retain.hyps(1))
  have inv': "u_disc_inv s'" by (rule pres_retain[OF ud_retain.prems(1) step])
  have dom': "dom (dwu_gens s') \<subseteq> {0..dwu_hwm s'}"
    by (rule u_gens_dom_step[OF step ud_retain.prems(2)])
  note sh = claim_reach_step[OF step claim ud_retain.prems(4) ud_retain.prems(5) i1]
  show ?case by (rule ud_retain.IH[OF inv' dom' sh(1) sh(2) sh(3) ud_retain.prems(6)])
next
  case (ud_claim s gu fu s' as t'')
  from ud_claim.prems(3) have claim: "u_claim_of (UArmF gu fu # as) i j g f" .
  from claim have ilt: "i < j" and jlen: "j < length (UArmF gu fu # as)" and
    ai: "(UArmF gu fu # as) ! i = UArmF g f" and aj: "(UArmF gu fu # as) ! j = UFire g" and
    interv: "\<forall>n. i < n \<and> n < j \<longrightarrow>
        (UArmF gu fu # as) ! n \<noteq> UFire g \<and> (\<forall>f'. (UArmF gu fu # as) ! n \<noteq> UArmF g f')"
    by (auto simp: u_claim_of_def)
  have step: "dwu_step s (UArmF gu fu) s'" by (rule ud_claim.hyps(2))
  have inv': "u_disc_inv s'" by (rule pres_claim[OF ud_claim.prems(1) ud_claim.hyps(1) step])
  have dom': "dom (dwu_gens s') \<subseteq> {0..dwu_hwm s'}"
    by (rule u_gens_dom_step[OF step ud_claim.prems(2)])
  show ?case
  proof (cases "i = 0")
    case True
    with ai have "UArmF gu fu = UArmF g f" by simp
    hence gug: "gu = g" and fuf: "fu = f" by auto
    from ilt True have jpos: "0 < j" by simp
    define Bi where "Bi = stamped_at (length (dwu_journal s)) g (u_sink_delta f s)"
    note armf = dwu_step_armf_full[OF step]
    have armf_acc: "dwu_accepted s' = dwu_accepted s" using armf by simp
    have armf_fence: "dwu_fence s' = gu" using armf by simp
    have armf_gens: "dwu_gens s' =
        (dwu_gens s)(gu \<mapsto> UArmed (stamped_at (length (dwu_journal s)) gu (u_sink_delta fu s)))"
      using armf by simp
    have armed': "dwu_gens s' g = Some (UArmed Bi)"
      using armf_gens gug fuf by (simp add: Bi_def)
    have fences': "dwu_fence s' \<le> g" using armf_fence gug by simp
    have anti: "set (u_owed f s') \<subseteq> set (u_owed f s)"
      by (rule u_step_owed_antitone[OF step]) auto
    have cover': "set (u_owed f s') \<subseteq> set (log_payloads (dwu_accepted s')) \<union> set (log_payloads Bi)"
    proof -
      have "set (u_owed f s') \<subseteq> set (u_owed f s)" by (rule anti)
      also have "\<dots> \<subseteq> set (log_payloads (dwu_accepted s)) \<union> set (u_sink_delta f s)"
        by (rule u_sink_delta_owed_split)
      also have "\<dots> = set (log_payloads (dwu_accepted s')) \<union> set (log_payloads Bi)"
        using armf_acc by (simp add: Bi_def)
      finally show ?thesis .
    qed
    have jbound': "j - 1 < length as" using jlen jpos by simp
    have jfire': "as ! (j - 1) = UFire g" using aj True ilt by (simp add: nth_Cons')
    have noarm_w: "\<forall>n<j - 1. as ! n \<noteq> UFire g \<and> (\<forall>f'. as ! n \<noteq> UArmF g f')"
    proof (intro allI impI)
      fix n assume "n < j - 1"
      with True have "i < Suc n \<and> Suc n < j" by simp
      with interv have "(UArmF gu fu # as) ! Suc n \<noteq> UFire g
          \<and> (\<forall>f'. (UArmF gu fu # as) ! Suc n \<noteq> UArmF g f')" by blast
      thus "as ! n \<noteq> UFire g \<and> (\<forall>f'. as ! n \<noteq> UArmF g f')" by simp
    qed
    have wfresh_w: "\<forall>n g' c e. n < j - 1 \<and> as ! n = ULift g' (DoSource c e) \<longrightarrow> \<not> src_le c f"
    proof (intro allI impI, elim conjE)
      fix n g' c e assume "n < j - 1" and nth: "as ! n = ULift g' (DoSource c e)"
      with True have bnd: "i < Suc n \<and> Suc n < j" by simp
      from nth have "(UArmF gu fu # as) ! Suc n = ULift g' (DoSource c e)" by simp
      with bnd have "i < Suc n \<and> Suc n < j
          \<and> (UArmF gu fu # as) ! Suc n = ULift g' (DoSource c e)" by simp
      with ud_claim.prems(4) show "\<not> src_le c f" unfolding u_window_fresh_def by blast
    qed
    have "dwu_temporal_trace s (UArmF gu fu # take (j - 1) as) tj"
      using ud_claim.prems(5) jpos by (simp add: take_Cons')
    from dwu_temporal_peel1[OF this step] have tjtail: "dwu_temporal_trace s' (take (j - 1) as) tj" .
    from window_covering[OF ud_claim.hyps(3) inv' dom' armed' fences' cover' jbound' jfire'
                            noarm_w wfresh_w tjtail ud_claim.prems(6)]
    show ?thesis by blast
  next
    case False
    hence i1: "1 \<le> i" by simp
    note sh = claim_reach_step[OF step claim ud_claim.prems(4) ud_claim.prems(5) i1]
    show ?thesis by (rule ud_claim.IH[OF inv' dom' sh(1) sh(2) sh(3) ud_claim.prems(6)])
  qed
next
  case (ud_cursor_recovery R s fu m Bu gu s1 s2 s3 as t'')
  from ud_cursor_recovery.prems(3) have
    claim: "u_claim_of (UArm gu Bu fu # UHeal gu fu # UFire gu # as) i j g f" .
  have i3: "3 \<le> i"
  proof (rule ccontr)
    assume "\<not> 3 \<le> i"
    hence "i = 0 \<or> i = 1 \<or> i = 2" by auto
    moreover from claim have "(UArm gu Bu fu # UHeal gu fu # UFire gu # as) ! i = UArmF g f"
      by (simp add: u_claim_of_def)
    ultimately show False by (auto simp: nth_Cons')
  qed
  have s1step: "dwu_step s (UArm gu Bu fu) s1" by (rule ud_cursor_recovery.hyps(7))
  have s2step: "dwu_step s1 (UHeal gu fu) s2" by (rule ud_cursor_recovery.hyps(8))
  have s3step: "dwu_step s2 (UFire gu) s3" by (rule ud_cursor_recovery.hyps(9))
  have inv': "u_disc_inv s3"
    by (rule pres_cursor[OF ud_cursor_recovery.prems(1) ud_cursor_recovery.hyps(1)
                            ud_cursor_recovery.hyps(3) ud_cursor_recovery.hyps(4)
                            ud_cursor_recovery.hyps(5) ud_cursor_recovery.hyps(6)
                            s1step s2step s3step])
  have dom1: "dom (dwu_gens s1) \<subseteq> {0..dwu_hwm s1}"
    by (rule u_gens_dom_step[OF s1step ud_cursor_recovery.prems(2)])
  have dom2: "dom (dwu_gens s2) \<subseteq> {0..dwu_hwm s2}" by (rule u_gens_dom_step[OF s2step dom1])
  have dom': "dom (dwu_gens s3) \<subseteq> {0..dwu_hwm s3}" by (rule u_gens_dom_step[OF s3step dom2])
  from claim have jl: "j < length (UArm gu Bu fu # UHeal gu fu # UFire gu # as)"
    and ij: "i < j" by (auto simp: u_claim_of_def)
  from jl have jle: "j \<le> length (UArm gu Bu fu # UHeal gu fu # UFire gu # as)" by simp
  from ij i3 have jge3: "3 \<le> j" by linarith
  have claim': "u_claim_of as (i - 3) (j - 3) g f"
    using u_claim_of_drop[OF claim i3] by simp
  have wf': "u_window_fresh as (i - 3) (j - 3) f"
    using u_window_fresh_drop[OF ud_cursor_recovery.prems(4) i3 jle] by simp
  have "take j (UArm gu Bu fu # UHeal gu fu # UFire gu # as)
        = UArm gu Bu fu # UHeal gu fu # UFire gu # take (j - 3) as"
    using jge3 by (simp add: take_Cons' numeral_2_eq_2 numeral_3_eq_3)
  with ud_cursor_recovery.prems(5)
  have "dwu_temporal_trace s (UArm gu Bu fu # UHeal gu fu # UFire gu # take (j - 3) as) tj" by simp
  from dwu_temporal_peel1[OF this s1step] have
    "dwu_temporal_trace s1 (UHeal gu fu # UFire gu # take (j - 3) as) tj" .
  from dwu_temporal_peel1[OF this s2step] have
    "dwu_temporal_trace s2 (UFire gu # take (j - 3) as) tj" .
  from dwu_temporal_peel1[OF this s3step] have
    tjtail: "dwu_temporal_trace s3 (take (j - 3) as) tj" .
  show ?case
    by (rule ud_cursor_recovery.IH[OF inv' dom' claim' wf' tjtail ud_cursor_recovery.prems(6)])
qed


section \<open>12. U8 completed-claim (the possibility headliner, both halves)\<close>

theorem u_exactly_once_at_completed_claim:
  assumes "u_disciplined_trace (dwu_init b K fin) acts t"
      and "u_claim_of acts i j g f"
      and "u_window_fresh acts i j f"
      and "dwu_temporal_trace (dwu_init b K fin) (take j acts) tj"
      and "dwu_fence tj \<le> g"   \<comment> \<open>completed AT THE FENCE: the fire's batch is accepted\<close>
      and "dwu_temporal_trace (dwu_init b K fin) (take (Suc j) acts) tj'"
  shows "u_exactly_once_at f tj'"
proof -
  note H1 = assms(1) and H2 = assms(2) and H3 = assms(3)
    and H4 = assms(4) and H5 = assms(5) and H6 = assms(6)
  from H2 have jlen: "j < length acts" and ajf: "acts ! j = UFire g"
    by (auto simp: u_claim_of_def)
  \<comment> \<open>the fire step @{term tj} \<open>\<rightarrow>\<close> @{term tj'} (pinned by determinism)\<close>
  have "take (Suc j) acts = take j acts @ [acts ! j]"
    using jlen by (rule take_Suc_conv_app_nth)
  with H6 ajf have snoc: "dwu_temporal_trace (dwu_init b K fin) (take j acts @ [UFire g]) tj'" by simp
  from dwu_temporal_snocD[OF snoc refl] obtain m where
    m1: "dwu_temporal_trace (dwu_init b K fin) (take j acts) m" and
    mfire: "dwu_step m (UFire g) tj'" by blast
  from dwu_temporal_trace_deterministic[OF m1 H4] have "m = tj" .
  with mfire have fire: "dwu_step tj (UFire g) tj'" by simp
  \<comment> \<open>the covering at the pre-fire state\<close>
  from claim_reach[OF H1 dwu_init_disc_inv dwu_init_dom H2 H3 H4 H5]
  have inv_tj: "u_disc_inv tj" and
    cov: "\<exists>B. dwu_gens tj g = Some (UArmed B) \<and>
           set (u_owed f tj) \<subseteq> set (log_payloads (dwu_accepted tj)) \<union> set (log_payloads B)"
    by auto
  from cov obtain B where
    armed_tj: "dwu_gens tj g = Some (UArmed B)" and
    cover_tj: "set (u_owed f tj) \<subseteq> set (log_payloads (dwu_accepted tj)) \<union> set (log_payloads B)"
    by blast
  \<comment> \<open>the fire delivers @{term B} (completed at the fence)\<close>
  from dwu_step_fire_full[OF fire] obtain B' where
    gB': "dwu_gens tj g = Some (UArmed B')" and
    acc': "dwu_accepted tj' = dwu_accepted tj @ (if dwu_fence tj \<le> g then B' else [])" and
    store': "dwu_store tj' = dwu_store tj" by blast
  from gB' armed_tj have "B' = B" by simp
  with acc' H5 have acctj': "dwu_accepted tj' = dwu_accepted tj @ B" by simp
  from dwu_step_fire_inv[OF fire] obtain Bx where
    floortj': "dwu_floor tj' = dwu_floor tj" by blast
  have owedtj': "u_owed f tj' = u_owed f tj"
  proof (rule u_owed_frame)
    show "exec_src_hist (dwu_store tj') = exec_src_hist (dwu_store tj)" using store' by simp
    show "dwu_floor tj' = dwu_floor tj" by (rule floortj')
    show "exec_scope (dwu_store tj') = exec_scope (dwu_store tj)" using store' by simp
  qed
  \<comment> \<open>at-least-once at the post-fire state\<close>
  have "set (u_owed f tj') \<subseteq> set (log_payloads (dwu_accepted tj'))"
  proof -
    have "set (u_owed f tj') = set (u_owed f tj)" using owedtj' by simp
    also have "\<dots> \<subseteq> set (log_payloads (dwu_accepted tj)) \<union> set (log_payloads B)"
      by (rule cover_tj)
    also have "\<dots> = set (log_payloads (dwu_accepted tj'))"
      using acctj' by (simp add: log_payloads_append)
    finally show ?thesis .
  qed
  hence alo: "u_at_least_once_at f tj'" by (simp add: u_at_least_once_at_owed)
  \<comment> \<open>safety at the post-fire state\<close>
  from pres_fire[OF inv_tj fire] have "u_disc_inv tj'" .
  hence "\<not> u_effect_unsafe tj'" by (rule u_disc_inv_safe)
  with alo show ?thesis by (simp add: u_exactly_once_at_def)
qed


section \<open>13. U11 --- the control block (P7 witness runs)\<close>

text \<open>Three concrete runs on the landed unified machine.  They reuse the I0.5 crashed
  2-generation witness @{const rf_W} (and its reach/safety/arm facts) from
  @{theory Dual_Write_Unified.DWU_Recovery_Floor}.\<close>

subsection \<open>13.1 Fence-at-release is unsound: a bare-arm zombie fires and duplicates\<close>

text \<open>@{term "t0 = rf_W"}; arm gen 0 (@{const rf_B1}), spawn, arm gen 1 (@{const rf_B2}),
  heal, then BOTH fire at fence 0 --- the same owed payload @{term "(ec2, e2)"} lands twice.\<close>

definition frl_t2 :: "(nat, nat) dwu_state" where
  "frl_t2 = rf_t1\<lparr>dwu_gens := (dwu_gens rf_t1)(2 \<mapsto> UProd), dwu_hwm := 2\<rparr>"

definition frl_t3 :: "(nat, nat) dwu_state" where
  "frl_t3 = frl_t2\<lparr>dwu_gens := (dwu_gens frl_t2)(1 \<mapsto> UArmed rf_B2)\<rparr>"

definition frl_t4 :: "(nat, nat) dwu_state" where
  "frl_t4 = frl_t3\<lparr>dwu_store := rf_stoH\<rparr>"

definition frl_t5 :: "(nat, nat) dwu_state" where
  "frl_t5 = frl_t4\<lparr>dwu_sent := dwu_sent frl_t4 @ rf_B1,
                    dwu_accepted := dwu_accepted frl_t4 @ rf_B1,
                    dwu_gens := (dwu_gens frl_t4)(0 \<mapsto> UProd)\<rparr>"

definition frl_t6 :: "(nat, nat) dwu_state" where
  "frl_t6 = frl_t5\<lparr>dwu_sent := dwu_sent frl_t5 @ rf_B2,
                    dwu_accepted := dwu_accepted frl_t5 @ rf_B2,
                    dwu_gens := (dwu_gens frl_t5)(1 \<mapsto> UProd)\<rparr>"

lemma frl_step_spawn: "dwu_step rf_t1 USpawn frl_t2"
proof -
  have "dwu_step rf_t1 USpawn
          (rf_t1\<lparr>dwu_gens := (dwu_gens rf_t1)(Suc (dwu_hwm rf_t1) \<mapsto> UProd),
                 dwu_hwm := Suc (dwu_hwm rf_t1)\<rparr>)"
    by (rule dwu_step.uspawn)
  also have "\<dots> = frl_t2"
    by (simp add: frl_t2_def rf_t1_def rf_W_def mkU_def numeral_2_eq_2)
  finally show ?thesis .
qed

lemma frl_step_arm1: "dwu_step frl_t2 (UArm 1 rf_B2 ec2) frl_t3"
proof -
  have "dwu_step frl_t2 (UArm 1 rf_B2 ec2)
          (frl_t2\<lparr>dwu_gens := (dwu_gens frl_t2)(1 \<mapsto> UArmed rf_B2)\<rparr>)"
    by (rule dwu_step.uarm)
       (simp_all add: frl_t2_def rf_t1_def rf_W_def mkU_def rf_sto6_def mkC_def
                      rf_B2_def rf_b2_def ec_defs)
  thus ?thesis by (simp add: frl_t3_def)
qed

lemma frl_relay: "relay_bounded_replay_reconcile (dwu_store frl_t3) ec2 rf_stoH"
  by (simp add: relay_bounded_replay_reconcile_def frl_t3_def frl_t2_def rf_t1_def rf_W_def
                mkU_def rf_sto6_def rf_stoH_def mkC_def replay_down_hist_def e1_def e2_def ec_defs)

lemma frl_step_heal: "dwu_step frl_t3 (UHeal 1 ec2) frl_t4"
proof -
  have "dwu_step frl_t3 (UHeal 1 ec2) (frl_t3\<lparr>dwu_store := rf_stoH\<rparr>)"
    by (rule dwu_step.uheal[OF frl_relay])
  thus ?thesis by (simp add: frl_t4_def)
qed

lemma frl_step_fire0: "dwu_step frl_t4 (UFire 0) frl_t5"
proof -
  have g: "dwu_gens frl_t4 0 = Some (UArmed rf_B1)"
    by (simp add: frl_t4_def frl_t3_def frl_t2_def rf_t1_def rf_W_def mkU_def)
  have "dwu_step frl_t4 (UFire 0)
          (frl_t4\<lparr>dwu_sent := dwu_sent frl_t4 @ rf_B1,
                  dwu_accepted := dwu_accepted frl_t4 @ (if dwu_fence frl_t4 \<le> 0 then rf_B1 else []),
                  dwu_gens := (dwu_gens frl_t4)(0 \<mapsto> UProd)\<rparr>)"
    by (rule dwu_step.ufire[OF g])
  also have "\<dots> = frl_t5"
    by (simp add: frl_t5_def frl_t4_def frl_t3_def frl_t2_def rf_t1_def rf_W_def mkU_def)
  finally show ?thesis .
qed

lemma frl_step_fire1: "dwu_step frl_t5 (UFire 1) frl_t6"
proof -
  have g: "dwu_gens frl_t5 1 = Some (UArmed rf_B2)"
    by (simp add: frl_t5_def frl_t4_def frl_t3_def frl_t2_def rf_t1_def rf_W_def mkU_def)
  have "dwu_step frl_t5 (UFire 1)
          (frl_t5\<lparr>dwu_sent := dwu_sent frl_t5 @ rf_B2,
                  dwu_accepted := dwu_accepted frl_t5 @ (if dwu_fence frl_t5 \<le> 1 then rf_B2 else []),
                  dwu_gens := (dwu_gens frl_t5)(1 \<mapsto> UProd)\<rparr>)"
    by (rule dwu_step.ufire[OF g])
  also have "\<dots> = frl_t6"
    by (simp add: frl_t6_def frl_t5_def frl_t4_def frl_t3_def frl_t2_def rf_t1_def rf_W_def mkU_def)
  finally show ?thesis .
qed

lemma frl_dup: "u_duplicate frl_t6"
  by (simp add: u_duplicate_def frl_t6_def frl_t5_def frl_t4_def frl_t3_def frl_t2_def
                rf_t1_def rf_W_def mkU_def rf_B1_def rf_B2_def rf_b1_def rf_b2_def rf_x1_def
                log_payloads_def map_filter_simps e1_def e2_def ec_defs)

theorem u_fence_at_release_unsound:   \<comment> \<open>fence late, admit the zombie: the bare-arm
  zombie's fire is accepted at fence 0 and duplicates the claimed recovery\<close>
  "\<exists>t0 t1 t2 t3 t4 t5 t6 Bz B1 f.
     dwu_reachable_w t0
   \<and> (\<exists>c. exec_status (dwu_store t0) = Crashed c)
   \<and> dwu_fence t0 = 0
   \<and> \<not> u_effect_unsafe t0
   \<and> dwu_step t0 (UArm 0 Bz f) t1
   \<and> dwu_step t1 USpawn t2
   \<and> dwu_step t2 (UArm 1 B1 f) t3
   \<and> dwu_step t3 (UHeal 1 f) t4
   \<and> dwu_step t4 (UFire 0) t5
   \<and> dwu_step t5 (UFire 1) t6
   \<and> u_duplicate t6"
proof -
  have body:
    "dwu_reachable_w rf_W
   \<and> (\<exists>c. exec_status (dwu_store rf_W) = Crashed c)
   \<and> dwu_fence rf_W = 0
   \<and> \<not> u_effect_unsafe rf_W
   \<and> dwu_step rf_W (UArm 0 rf_B1 ec2) rf_t1
   \<and> dwu_step rf_t1 USpawn frl_t2
   \<and> dwu_step frl_t2 (UArm 1 rf_B2 ec2) frl_t3
   \<and> dwu_step frl_t3 (UHeal 1 ec2) frl_t4
   \<and> dwu_step frl_t4 (UFire 0) frl_t5
   \<and> dwu_step frl_t5 (UFire 1) frl_t6
   \<and> u_duplicate frl_t6"
  proof (intro conjI)
    show "dwu_reachable_w rf_W" by (rule rf_reach_W)
  next
    show "\<exists>c. exec_status (dwu_store rf_W) = Crashed c"
      by (rule exI[of _ ec2]) (simp add: rf_W_def mkU_def rf_sto6_def mkC_def)
  next
    show "dwu_fence rf_W = 0" by (simp add: rf_W_def mkU_def)
  next
    show "\<not> u_effect_unsafe rf_W" by (rule rf_safe_W)
  next
    show "dwu_step rf_W (UArm 0 rf_B1 ec2) rf_t1" by (rule rf_step_arm1)
  next
    show "dwu_step rf_t1 USpawn frl_t2" by (rule frl_step_spawn)
  next
    show "dwu_step frl_t2 (UArm 1 rf_B2 ec2) frl_t3" by (rule frl_step_arm1)
  next
    show "dwu_step frl_t3 (UHeal 1 ec2) frl_t4" by (rule frl_step_heal)
  next
    show "dwu_step frl_t4 (UFire 0) frl_t5" by (rule frl_step_fire0)
  next
    show "dwu_step frl_t5 (UFire 1) frl_t6" by (rule frl_step_fire1)
  next
    show "u_duplicate frl_t6" by (rule frl_dup)
  qed
  show ?thesis
    by (rule exI[of _ rf_W], rule exI[of _ rf_t1], rule exI[of _ frl_t2],
        rule exI[of _ frl_t3], rule exI[of _ frl_t4], rule exI[of _ frl_t5],
        rule exI[of _ frl_t6], rule exI[of _ rf_B1], rule exI[of _ rf_B2],
        rule exI[of _ ec2]) (rule body)
qed


subsection \<open>13.2 Claim-without-read is unsound: the recovery fences out its own re-drive\<close>

text \<open>@{term "t0 = rf_W"}; arm gen 0 (@{const rf_B1}), then raise the fence to 1 (separate
  install at Suc gen) so gen 0's fire lands nothing --- accepted is unchanged and the owed
  payload is LOST.\<close>

definition cwr_t2 :: "(nat, nat) dwu_state" where
  "cwr_t2 = rf_t1\<lparr>dwu_fence := 1\<rparr>"

definition cwr_t3 :: "(nat, nat) dwu_state" where
  "cwr_t3 = cwr_t2\<lparr>dwu_sent := dwu_sent cwr_t2 @ rf_B1,
                    dwu_accepted := dwu_accepted cwr_t2 @ (if dwu_fence cwr_t2 \<le> 0 then rf_B1 else []),
                    dwu_gens := (dwu_gens cwr_t2)(0 \<mapsto> UProd)\<rparr>"

lemma cwr_step_fence: "dwu_step rf_t1 (UFenceRaise 1) cwr_t2"
proof -
  have "dwu_step rf_t1 (UFenceRaise 1) (rf_t1\<lparr>dwu_fence := max (dwu_fence rf_t1) 1\<rparr>)"
    by (rule dwu_step.ufenceraise)
  also have "\<dots> = cwr_t2" by (simp add: cwr_t2_def rf_t1_def rf_W_def mkU_def)
  finally show ?thesis .
qed

lemma cwr_step_fire: "dwu_step cwr_t2 (UFire 0) cwr_t3"
proof -
  have g: "dwu_gens cwr_t2 0 = Some (UArmed rf_B1)"
    by (simp add: cwr_t2_def rf_t1_def rf_W_def mkU_def)
  have "dwu_step cwr_t2 (UFire 0)
          (cwr_t2\<lparr>dwu_sent := dwu_sent cwr_t2 @ rf_B1,
                  dwu_accepted := dwu_accepted cwr_t2 @ (if dwu_fence cwr_t2 \<le> 0 then rf_B1 else []),
                  dwu_gens := (dwu_gens cwr_t2)(0 \<mapsto> UProd)\<rparr>)"
    by (rule dwu_step.ufire[OF g])
  thus ?thesis by (simp add: cwr_t3_def)
qed

lemma cwr_acc_same: "dwu_accepted cwr_t3 = dwu_accepted rf_W"
  by (simp add: cwr_t3_def cwr_t2_def rf_t1_def rf_W_def mkU_def)

lemma cwr_lost: "u_lost ec2 cwr_t3"
  by (simp add: u_lost_def retained_hist_def cwr_t3_def cwr_t2_def rf_t1_def rf_W_def mkU_def
                rf_sto6_def mkC_def rf_B1_def rf_b1_def rf_x1_def log_payloads_def
                map_filter_simps replay_down_hist_def e1_def e2_def ec_defs)

theorem u_claim_without_read_unsound:   \<comment> \<open>fence early / separate install at Suc gen:
  the recovery fences out its own re-drive and loses\<close>
  "\<exists>t0 t1 t2 t3 B0 f.
     dwu_reachable_w t0
   \<and> (\<exists>c. exec_status (dwu_store t0) = Crashed c)
   \<and> dwu_fence t0 = 0
   \<and> \<not> u_effect_unsafe t0
   \<and> dwu_step t0 (UArm 0 B0 f) t1
   \<and> dwu_step t1 (UFenceRaise 1) t2
   \<and> dwu_step t2 (UFire 0) t3
   \<and> dwu_accepted t3 = dwu_accepted t0
   \<and> u_lost f t3"
proof -
  have body:
    "dwu_reachable_w rf_W
   \<and> (\<exists>c. exec_status (dwu_store rf_W) = Crashed c)
   \<and> dwu_fence rf_W = 0
   \<and> \<not> u_effect_unsafe rf_W
   \<and> dwu_step rf_W (UArm 0 rf_B1 ec2) rf_t1
   \<and> dwu_step rf_t1 (UFenceRaise 1) cwr_t2
   \<and> dwu_step cwr_t2 (UFire 0) cwr_t3
   \<and> dwu_accepted cwr_t3 = dwu_accepted rf_W
   \<and> u_lost ec2 cwr_t3"
  proof (intro conjI)
    show "dwu_reachable_w rf_W" by (rule rf_reach_W)
  next
    show "\<exists>c. exec_status (dwu_store rf_W) = Crashed c"
      by (rule exI[of _ ec2]) (simp add: rf_W_def mkU_def rf_sto6_def mkC_def)
  next
    show "dwu_fence rf_W = 0" by (simp add: rf_W_def mkU_def)
  next
    show "\<not> u_effect_unsafe rf_W" by (rule rf_safe_W)
  next
    show "dwu_step rf_W (UArm 0 rf_B1 ec2) rf_t1" by (rule rf_step_arm1)
  next
    show "dwu_step rf_t1 (UFenceRaise 1) cwr_t2" by (rule cwr_step_fence)
  next
    show "dwu_step cwr_t2 (UFire 0) cwr_t3" by (rule cwr_step_fire)
  next
    show "dwu_accepted cwr_t3 = dwu_accepted rf_W" by (rule cwr_acc_same)
  next
    show "u_lost ec2 cwr_t3" by (rule cwr_lost)
  qed
  show ?thesis
    by (rule exI[of _ rf_W], rule exI[of _ rf_t1], rule exI[of _ cwr_t2],
        rule exI[of _ cwr_t3], rule exI[of _ rf_B1], rule exI[of _ ec2]) (rule body)
qed


subsection \<open>13.3 Zombie expressibility: a live superseded incarnation, accepted vs fenced\<close>

text \<open>A live gen 0 (superseded by a spawn, @{term "0 < hwm"}) publishes at fence 0 and is
  ACCEPTED; the same incarnation under a raised fence publishes and lands NOTHING.  Fence-0
  is read trace-level (the state is reachable and Running, gen 0 is a genuine live @{const UProd}).\<close>

definition zt0 :: "(nat, nat) dwu_state" where
  "zt0 = uW2\<lparr>dwu_gens := (dwu_gens uW2)(1 \<mapsto> UProd), dwu_hwm := 1\<rparr>"

definition z_ddstore :: "(nat, nat) dw_exec_state" where
  "z_ddstore = mkC [(ec1, e1)] [(ec1, e1)] [(ec1, e1)] {} Running"

definition zt1 :: "(nat, nat) dwu_state" where
  "zt1 = zt0\<lparr>dwu_store := z_ddstore, dwu_sent := dwu_sent zt0 @ [rf_x1],
             dwu_accepted := dwu_accepted zt0 @ [rf_x1]\<rparr>"

definition zu0 :: "(nat, nat) dwu_state" where
  "zu0 = zt0\<lparr>dwu_fence := 1\<rparr>"

definition zu1 :: "(nat, nat) dwu_state" where
  "zu1 = zu0\<lparr>dwu_store := z_ddstore, dwu_sent := dwu_sent zu0 @ [rf_x1]\<rparr>"

lemma z_reach_uW2: "dwu_reachable Map.empty {0, 1} ec2 uW2"
proof -
  have r0: "dwu_reachable Map.empty {0, 1} ec2 uW0"
    unfolding rf_uW0_init by (rule dwu_reachable_init)
  have r1: "dwu_reachable Map.empty {0, 1} ec2 uW1"
    by (rule dwu_reach_lift[OF r0 rf_wf0 rf_g0 rf_step0])
  show ?thesis by (rule dwu_reach_lift[OF r1 rf_wf1 rf_g1 rf_step1])
qed

lemma z_step_spawn: "dwu_step uW2 USpawn zt0"
proof -
  have "dwu_step uW2 USpawn
          (uW2\<lparr>dwu_gens := (dwu_gens uW2)(Suc (dwu_hwm uW2) \<mapsto> UProd),
               dwu_hwm := Suc (dwu_hwm uW2)\<rparr>)"
    by (rule dwu_step.uspawn)
  also have "\<dots> = zt0" by (simp add: zt0_def uW2_def mkU_def)
  finally show ?thesis .
qed

lemma z_reach_zt0: "dwu_reachable_w zt0"
  by (rule dwu_reach_other[OF z_reach_uW2 _ _ z_step_spawn]) simp_all

lemma z_core_dd: "dw_exec_step (dwu_store zt0) (DoDownstream ec1 e1) z_ddstore"
  by (rule do_downstreamI) (simp_all add: zt0_def uW2_def mkU_def mkC_def z_ddstore_def)

lemma z_step_dd_t: "dwu_step zt0 (ULift 0 (DoDownstream ec1 e1)) zt1"
proof -
  have "dwu_step zt0 (ULift 0 (DoDownstream ec1 e1))
          (zt0\<lparr>dwu_store := z_ddstore, dwu_sent := dwu_sent zt0 @ [rf_x1],
               dwu_accepted := dwu_accepted zt0
                 @ (if dwu_fence zt0 \<le> ue_gen rf_x1 then [rf_x1] else [])\<rparr>)"
    by (rule dwu_step.ulift_publish[OF _ _ z_core_dd])
       (simp_all add: zt0_def uW2_def mkU_def rf_x1_def)
  also have "\<dots> = zt1" by (simp add: zt1_def zt0_def uW2_def mkU_def rf_x1_def)
  finally show ?thesis .
qed

lemma zt1_acc: "dwu_accepted zt1 = dwu_accepted zt0 @ [rf_x1]"
  by (simp add: zt1_def)

lemma z_step_fence: "dwu_step zt0 (UFenceRaise 1) zu0"
proof -
  have "dwu_step zt0 (UFenceRaise 1) (zt0\<lparr>dwu_fence := max (dwu_fence zt0) 1\<rparr>)"
    by (rule dwu_step.ufenceraise)
  also have "\<dots> = zu0" by (simp add: zu0_def zt0_def uW2_def mkU_def)
  finally show ?thesis .
qed

lemma z_reach_zu0: "dwu_reachable_w zu0"
  by (rule dwu_reach_other[OF z_reach_zt0 _ _ z_step_fence]) simp_all

lemma z_step_dd_u: "dwu_step zu0 (ULift 0 (DoDownstream ec1 e1)) zu1"
proof -
  have core: "dw_exec_step (dwu_store zu0) (DoDownstream ec1 e1) z_ddstore"
    by (rule do_downstreamI) (simp_all add: zu0_def zt0_def uW2_def mkU_def mkC_def z_ddstore_def)
  have "dwu_step zu0 (ULift 0 (DoDownstream ec1 e1))
          (zu0\<lparr>dwu_store := z_ddstore, dwu_sent := dwu_sent zu0 @ [rf_x1],
               dwu_accepted := dwu_accepted zu0
                 @ (if dwu_fence zu0 \<le> ue_gen rf_x1 then [rf_x1] else [])\<rparr>)"
    by (rule dwu_step.ulift_publish[OF _ _ core])
       (simp_all add: zu0_def zt0_def uW2_def mkU_def rf_x1_def)
  also have "\<dots> = zu1" by (simp add: zu1_def zu0_def zt0_def uW2_def mkU_def rf_x1_def)
  finally show ?thesis .
qed

lemma zu1_acc: "dwu_accepted zu1 = dwu_accepted zu0"
  by (simp add: zu1_def)

theorem u_zombie_expressibility:   \<comment> \<open>the A4-falls pair: a LIVE superseded
  incarnation's fresh send is accepted at fence 0, and fenced out under a claim\<close>
  "\<exists>t0 t1 u0 u1 c e x.
     dwu_reachable_w t0
   \<and> 0 < dwu_hwm t0 \<and> dwu_gens t0 0 = Some UProd \<and> dwu_fence t0 = 0
   \<and> dwu_step t0 (ULift 0 (DoDownstream c e)) t1
   \<and> dwu_accepted t1 = dwu_accepted t0 @ [x] \<and> ue_gen x = 0
   \<and> dwu_reachable_w u0
   \<and> 0 < dwu_fence u0 \<and> dwu_gens u0 0 = Some UProd
   \<and> dwu_step u0 (ULift 0 (DoDownstream c e)) u1
   \<and> dwu_accepted u1 = dwu_accepted u0"
proof (intro exI conjI)
  show "dwu_reachable_w zt0" by (rule z_reach_zt0)
  show "0 < dwu_hwm zt0" by (simp add: zt0_def uW2_def mkU_def)
  show "dwu_gens zt0 0 = Some UProd" by (simp add: zt0_def uW2_def mkU_def)
  show "dwu_fence zt0 = 0" by (simp add: zt0_def uW2_def mkU_def)
  show "dwu_step zt0 (ULift 0 (DoDownstream ec1 e1)) zt1" by (rule z_step_dd_t)
  show "dwu_accepted zt1 = dwu_accepted zt0 @ [rf_x1]" by (rule zt1_acc)
  show "ue_gen rf_x1 = 0" by (simp add: rf_x1_def)
  show "dwu_reachable_w zu0" by (rule z_reach_zu0)
  show "0 < dwu_fence zu0" by (simp add: zu0_def)
  show "dwu_gens zu0 0 = Some UProd" by (simp add: zu0_def zt0_def uW2_def mkU_def)
  show "dwu_step zu0 (ULift 0 (DoDownstream ec1 e1)) zu1" by (rule z_step_dd_u)
  show "dwu_accepted zu1 = dwu_accepted zu0" by (rule zu1_acc)
qed

end
