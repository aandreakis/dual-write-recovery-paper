(*  Title:       DWT_Wire_Completed.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE COMPLETED-CLAIM HALF OVER THE WIRE (WP4 of the owner authorization
    DECISIONS.md D-099; built ONLY after --- and exactly as specified by ---
    the design gate WP4_DESIGN_GATE.md in this directory, whose fences BIND
    every use of this theory).

    The wire may LOSE the re-driven batch (wlose, guard-free), so Road-2's
    completed-claim exactly-once conjunct CANNOT transfer as-is.  This theory
    states the two honest forms the gate admitted:

      dwt_completed_claim_redrive  (form b surrogate, plain wstep) ---
        re-drive recoverability as \<exists>-extension reachability: from ANY
        reachable state, ANY payload in the run's replay scope not yet
        accepted is TWO steps (one fresh claim + one arrival) from sitting in
        the acceptance ledger EXACTLY ONCE.  Ability, not inevitability: no
        fairness exists in this corpus, and an adversarial wire may lose every
        re-drive; this is the corpus's healing idiom (reachability of a good
        state), NOT liveness and NOT at-least-once.

      dwt_completed_claim_arrival_exactly_once  (form a, labeled runs) ---
        CONDITIONAL exactly-once: at a claim staging batch B, IF every item of
        B ARRIVES (is delivered, not lost --- a trace property, expressed over
        the labeled-run instrument wrun below) AND the claim is STILL CURRENT
        at the end state (t_fence t = g), THEN the ledger holds each payload
        of B exactly once.  BOTH conditions are load-bearing and each carries
        its own machine-checked control (dwt_completed_claim_arrival_load_bearing,
        dwt_completed_claim_currency_load_bearing).

    THE FENCE (gate section 4, binding): never quote any result here as
    unconditional "exactly-once over the wire".  The arrival and currency
    conditions are part of the statement's name in any headline; the redrive
    form is "always one re-claim + one arrival away", never "eventually
    lands".  Safety (DWT_Wire) is the UNCONDITIONAL half; completeness over a
    lossy wire is conditional-or-reachability BY NATURE --- that asymmetry is
    the honest content.  All conclusions are ACCEPTANCE-LEDGER equations/counts
    (boundary row K7); downstream convergence is out of scope.

    THE INSTRUMENT (disclosed): wrun is a labeled-run inductive mirroring
    wstep rule-for-rule (the corpus's landed act-list idiom, cf.
    u_disciplined_trace), with erasure wrun_wsteps back to (wstep K)^**.
    Purely definitional: no new axiom, no change to wstep or to any record
    statement.  Arrival is at item-VALUE granularity (the machine has no token
    identity --- consistent with boundary K1's item-multiset view).

    Polarity: the two premise controls are \<exists>-witness refutations of the
    UNCONDITIONED conclusion (concrete runs where it fails); no universal
    impossibility over machines or premises is stated.
*)

theory DWT_Wire_Completed
  imports DWT_Wire
begin

section \<open>1. Monotonicity spine (plain wstep)\<close>

text \<open>The fence never falls, and the acceptance ledger never forgets --- the
  two state-local facts both WP4 forms ride.\<close>

lemma wstep_fence_mono:
  assumes "wstep K s s'"
  shows "t_fence s \<le> t_fence s'"
  using assms by (cases rule: wstep.cases) auto

lemma wsteps_fence_mono:
  assumes "(wstep K)\<^sup>*\<^sup>* s s'"
  shows "t_fence s \<le> t_fence s'"
  using assms
proof (induction rule: rtranclp_induct)
  case base show ?case by simp
next
  case (step y z)
  show ?case using step.IH wstep_fence_mono[OF step.hyps(2)] by simp
qed

lemma wstep_accepted_mono:
  assumes "wstep K s s'"
  shows "set (t_accepted s) \<subseteq> set (t_accepted s')"
  using assms by (cases rule: wstep.cases) auto

lemma wsteps_accepted_mono:
  assumes "(wstep K)\<^sup>*\<^sup>* s s'"
  shows "set (t_accepted s) \<subseteq> set (t_accepted s')"
  using assms
proof (induction rule: rtranclp_induct)
  case base show ?case by simp
next
  case (step y z)
  show ?case using step.IH wstep_accepted_mono[OF step.hyps(2)] by blast
qed

lemma log_payloads_memI:
  assumes "x \<in> set xs" and "ue_pay x = ULog p"
  shows "p \<in> set (log_payloads xs)"
  using assms
  by (induction xs)
     (auto simp: log_payloads_def map_filter_simps
           split: upayload.splits option.splits)

lemma distinct_count_mem_1:
  assumes "distinct xs" and "a \<in> set xs"
  shows "count (mset xs) a = 1"
  using assms by (induction xs) (auto simp: count_eq_zero_iff)

section \<open>2. Form (b): re-drive recoverability --- healing is always reachable\<close>

text \<open>SCOPE (binding, gate fence 2): an \<exists>-extension statement --- the
  protocol never loses the ABILITY to land a missing in-scope payload; it does
  NOT say the payload eventually lands (no fairness exists in this corpus; an
  adversarial wire may lose every re-drive).  The count-1 conclusion is on the
  ACCEPTANCE LEDGER of the extended state; at-most-once is the record safety
  theorem's contribution, at-least-once is the constructed arrival's.\<close>

theorem dwt_completed_claim_redrive:
  assumes reach: "(wstep K)\<^sup>*\<^sup>* (winit b0) s"
      and inscope: "p \<in> set (replay_down_hist (fst (t_journal s)) K f)"
      and missing: "p \<notin> set (log_payloads (t_accepted s))"
  shows "\<exists>s'. (wstep K)\<^sup>*\<^sup>* s s' \<and> (wstep K)\<^sup>*\<^sup>* (winit b0) s'
            \<and> count (mset (log_payloads (t_accepted s'))) p = 1"
proof -
  define g where "g = Suc (t_fence s)"
  define D where "D = filter (\<lambda>q. q \<notin> set (log_payloads (t_accepted s)))
                        (replay_down_hist (fst (t_journal s)) K f)"
  define B where "B = stamped_at (length (fst (t_journal s))) g D"
  define s1 where "s1 = s\<lparr>t_fence := g, t_pending := t_pending s @ B\<rparr>"
  have step1: "wstep K s s1"
    by (rule wclaimI[where g = g and f = f and B = B])
       (simp_all add: g_def B_def D_def s1_def)
  have pD: "p \<in> set D"
    using inscope missing by (simp add: D_def)
  define xB where
    "xB = \<lparr> ue_stamp = length (fst (t_journal s)), ue_gen = g, ue_pay = ULog p \<rparr>"
  have xBinB: "xB \<in> set B"
    using pD by (auto simp: B_def xB_def stamped_at_def)
  have xBpend: "xB \<in> set (t_pending s1)"
    using xBinB by (simp add: s1_def)
  then obtain i where iB: "i < length (t_pending s1)"
                  and nthi: "t_pending s1 ! i = xB"
    by (metis in_set_conv_nth)
  define s2 where
    "s2 = s1\<lparr>t_pending := take i (t_pending s1) @ drop (Suc i) (t_pending s1),
             t_accepted := t_accepted s1 @ [xB]\<rparr>"
  have nthx: "(t_pending s @ B) ! i = xB"
    using nthi by (simp add: s1_def)
  have step2: "wstep K s1 s2"
    by (rule wdeliverI[OF iB]) (simp add: s2_def s1_def nthx xB_def)
  have ext: "(wstep K)\<^sup>*\<^sup>* s s2"
    using step1 step2 by (meson converse_rtranclp_into_rtranclp r_into_rtranclp)
  have reach2: "(wstep K)\<^sup>*\<^sup>* (winit b0) s2"
    using reach ext by (rule rtranclp_trans)
  have memp: "p \<in> set (log_payloads (t_accepted s2))"
  proof -
    have "xB \<in> set (t_accepted s2)" by (simp add: s2_def)
    then show ?thesis by (rule log_payloads_memI) (simp add: xB_def)
  qed
  have dist: "distinct (log_payloads (t_accepted s2))"
    by (rule wire_accepted_duplicate_free[OF reach2])
  have cnt: "count (mset (log_payloads (t_accepted s2))) p = 1"
    by (rule distinct_count_mem_1[OF dist memp])
  show ?thesis using ext reach2 cnt by blast
qed

section \<open>3. The labeled-run instrument (arrival is a trace property)\<close>

text \<open>From a final state, an item absent from both pending and accepted is
  indistinguishably "lost" or "delivered while superseded" --- so
  arrival-conditioning cannot be stated over plain @{text "(wstep K)\<^sup>*\<^sup>*"} runs
  (gate section 1).  @{text wrun} labels each step with what happened; the
  erasure lemma maps labeled runs back onto @{const wstep} runs, so the record
  safety theorem applies to every labeled run.  Rule-for-rule mirror of
  @{const wstep}; the delivered/lost ITEM is recorded in the label.\<close>

datatype ('k, 'v) wact =
    WActProduce "src_coord \<times> ('k, 'v) source_event"
  | WActSendLive "('k, 'v) uemission"
  | WActSendZombie "('k, 'v) uemission"
  | WActClaim nat "('k, 'v) uemission list"
  | WActDeliver "('k, 'v) uemission"
  | WActLose "('k, 'v) uemission"
  | WActReorder "('k, 'v) uemission list"

inductive wrun
  :: "'k set \<Rightarrow> (('k, 'v) uemission, ('k, 'v) ujournal) tstate
      \<Rightarrow> ('k, 'v) wact list
      \<Rightarrow> (('k, 'v) uemission, ('k, 'v) ujournal) tstate \<Rightarrow> bool"
  for K
where
  wr_nil: "wrun K s [] s"
| wr_produce:
    "\<lbrakk>strictly_ascending_source (fst (t_journal s) @ [p]);
      wrun K (s\<lparr>t_journal := (fst (t_journal s) @ [p], snd (t_journal s))\<rparr>) as t\<rbrakk> \<Longrightarrow>
     wrun K s (WActProduce p # as) t"
| wr_send_live:
    "\<lbrakk>x = \<lparr> ue_stamp = length (fst (t_journal s)), ue_gen = t_fence s, ue_pay = ULog p \<rparr>;
      p \<in> set (fst (t_journal s));
      p \<notin> set (log_payloads (t_accepted s));
      p \<notin> set (log_payloads (a_eligible ue_gen s));
      wrun K (s\<lparr>t_pending := t_pending s @ [x]\<rparr>) as t\<rbrakk> \<Longrightarrow>
     wrun K s (WActSendLive x # as) t"
| wr_send_zombie:
    "\<lbrakk>ue_gen x < t_fence s;
      wrun K (s\<lparr>t_pending := t_pending s @ [x]\<rparr>) as t\<rbrakk> \<Longrightarrow>
     wrun K s (WActSendZombie x # as) t"
| wr_claim:
    "\<lbrakk>t_fence s < g;
      D = filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted s)))
            (replay_down_hist (fst (t_journal s)) K f);
      B = stamped_at (length (fst (t_journal s))) g D;
      wrun K (s\<lparr>t_fence := g, t_pending := t_pending s @ B\<rparr>) as t\<rbrakk> \<Longrightarrow>
     wrun K s (WActClaim g B # as) t"
| wr_deliver:
    "\<lbrakk>i < length (t_pending s); x = t_pending s ! i;
      wrun K (s\<lparr>t_pending := take i (t_pending s) @ drop (Suc i) (t_pending s),
               t_accepted := t_accepted s
                 @ filter (\<lambda>y. t_fence s \<le> ue_gen y) [t_pending s ! i]\<rparr>) as t\<rbrakk> \<Longrightarrow>
     wrun K s (WActDeliver x # as) t"
| wr_lose:
    "\<lbrakk>i < length (t_pending s); x = t_pending s ! i;
      wrun K (s\<lparr>t_pending := take i (t_pending s) @ drop (Suc i) (t_pending s)\<rparr>) as t\<rbrakk> \<Longrightarrow>
     wrun K s (WActLose x # as) t"
| wr_reorder:
    "\<lbrakk>mset qs = mset (t_pending s);
      wrun K (s\<lparr>t_pending := qs\<rparr>) as t\<rbrakk> \<Longrightarrow>
     wrun K s (WActReorder qs # as) t"

text \<open>Erasure: every labeled run is a disciplined wire run --- reachability,
  the invariant, and the record safety theorem all transfer.\<close>

lemma wrun_wsteps:
  assumes "wrun K s as t"
  shows "(wstep K)\<^sup>*\<^sup>* s t"
  using assms
proof (induction rule: wrun.induct)
  case (wr_nil s)
  show ?case by simp
next
  case (wr_produce s p as t)
  have "wstep K s (s\<lparr>t_journal := (fst (t_journal s) @ [p], snd (t_journal s))\<rparr>)"
    by (rule wstep.wproduce[OF wr_produce.hyps(1)])
  then show ?case
    using wr_produce.IH by (meson converse_rtranclp_into_rtranclp)
next
  case (wr_send_live x s p as t)
  have "wstep K s (s\<lparr>t_pending := t_pending s @ [x]\<rparr>)"
    by (rule wstep.wsend_live[OF wr_send_live.hyps(1) wr_send_live.hyps(2)
                                 wr_send_live.hyps(3) wr_send_live.hyps(4)])
  then show ?case
    using wr_send_live.IH by (meson converse_rtranclp_into_rtranclp)
next
  case (wr_send_zombie x s as t)
  have "wstep K s (s\<lparr>t_pending := t_pending s @ [x]\<rparr>)"
    by (rule wstep.wsend_zombie[OF wr_send_zombie.hyps(1)])
  then show ?case
    using wr_send_zombie.IH by (meson converse_rtranclp_into_rtranclp)
next
  case (wr_claim s g D f B as t)
  have "wstep K s (s\<lparr>t_fence := g, t_pending := t_pending s @ B\<rparr>)"
    by (rule wstep.wclaim[OF wr_claim.hyps(1) wr_claim.hyps(2) wr_claim.hyps(3)])
  then show ?case
    using wr_claim.IH by (meson converse_rtranclp_into_rtranclp)
next
  case (wr_deliver i s x as t)
  have "wstep K s (s\<lparr>t_pending := take i (t_pending s) @ drop (Suc i) (t_pending s),
                     t_accepted := t_accepted s
                       @ filter (\<lambda>y. t_fence s \<le> ue_gen y) [t_pending s ! i]\<rparr>)"
    by (rule wstep.wdeliver[OF wr_deliver.hyps(1)])
  then show ?case
    using wr_deliver.IH by (meson converse_rtranclp_into_rtranclp)
next
  case (wr_lose i s x as t)
  have "wstep K s (s\<lparr>t_pending := take i (t_pending s) @ drop (Suc i) (t_pending s)\<rparr>)"
    by (rule wstep.wlose[OF wr_lose.hyps(1)])
  then show ?case
    using wr_lose.IH by (meson converse_rtranclp_into_rtranclp)
next
  case (wr_reorder qs s as t)
  have "wstep K s (s\<lparr>t_pending := qs\<rparr>)"
    by (rule wstep.wreorder[OF wr_reorder.hyps(1)])
  then show ?case
    using wr_reorder.IH by (meson converse_rtranclp_into_rtranclp)
qed

text \<open>Derived equation-premise introduction rules (the landed @{text "dwc_*I"}
  idiom) for the labeled rules the witnesses and controls use.\<close>

lemma wrunI_claim:
  assumes "t_fence s < g"
      and "B = stamped_at (length (fst (t_journal s))) g
                 (filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted s)))
                   (replay_down_hist (fst (t_journal s)) K f))"
      and "s' = s\<lparr>t_fence := g, t_pending := t_pending s @ B\<rparr>"
      and "wrun K s' as t"
  shows "wrun K s (WActClaim g B # as) t"
  using assms(4) unfolding assms(3)
  by (rule wrun.wr_claim[OF assms(1) refl assms(2)])

lemma wrunI_deliver:
  assumes "i < length (t_pending s)"
      and "x = t_pending s ! i"
      and "s' = s\<lparr>t_pending := take i (t_pending s) @ drop (Suc i) (t_pending s),
                  t_accepted := t_accepted s
                    @ filter (\<lambda>y. t_fence s \<le> ue_gen y) [t_pending s ! i]\<rparr>"
      and "wrun K s' as t"
  shows "wrun K s (WActDeliver x # as) t"
  using assms(4) unfolding assms(3)
  by (rule wrun.wr_deliver[OF assms(1) assms(2)])

lemma wrunI_lose:
  assumes "i < length (t_pending s)"
      and "x = t_pending s ! i"
      and "s' = s\<lparr>t_pending := take i (t_pending s) @ drop (Suc i) (t_pending s)\<rparr>"
      and "wrun K s' as t"
  shows "wrun K s (WActLose x # as) t"
  using assms(4) unfolding assms(3)
  by (rule wrun.wr_lose[OF assms(1) assms(2)])

section \<open>4. Delivered while current implies accepted\<close>

text \<open>The at-least-once engine: if an item is DELIVERED somewhere in a labeled
  run and its generation still clears the fence AT THE END (the fence is
  monotone, so it cleared the fence at the delivery point too), then it sits
  in the acceptance ledger at the end.\<close>

lemma wrun_deliver_current_accepted:
  assumes run: "wrun K s as t"
      and del: "WActDeliver x \<in> set as"
      and cur: "t_fence t \<le> ue_gen x"
  shows "x \<in> set (t_accepted t)"
  using run del cur
proof (induction rule: wrun.induct)
  case (wr_nil s)
  then show ?case by simp
next
  case (wr_produce s p as t)
  then show ?case by simp
next
  case (wr_send_live x' s p as t)
  then show ?case by simp
next
  case (wr_send_zombie x' s as t)
  then show ?case by simp
next
  case (wr_claim s g D f B as t)
  then show ?case by simp
next
  case (wr_deliver i s x' as t)
  show ?case
  proof (cases "WActDeliver x \<in> set as")
    case True
    then show ?thesis using wr_deliver.IH wr_deliver.prems(2) by blast
  next
    case False
    with wr_deliver.prems(1) have xx': "x = x'" by simp
    have xi: "t_pending s ! i = x"
      using wr_deliver.hyps(2) xx' by simp
    let ?s1 = "s\<lparr>t_pending := take i (t_pending s) @ drop (Suc i) (t_pending s),
                 t_accepted := t_accepted s
                   @ filter (\<lambda>y. t_fence s \<le> ue_gen y) [t_pending s ! i]\<rparr>"
    have fmono: "t_fence ?s1 \<le> t_fence t"
      by (rule wsteps_fence_mono[OF wrun_wsteps[OF wr_deliver.hyps(3)]])
    then have elig: "t_fence s \<le> ue_gen x"
      using wr_deliver.prems(2) by simp
    have inacc1: "x \<in> set (t_accepted ?s1)"
      using elig by (simp add: xi)
    show ?thesis
      using wsteps_accepted_mono[OF wrun_wsteps[OF wr_deliver.hyps(3)]] inacc1
      by blast
  qed
next
  case (wr_lose i s x' as t)
  then show ?case by simp
next
  case (wr_reorder qs s as t)
  then show ?case by simp
qed

section \<open>5. Form (a): THE conditional exactly-once at a completed claim\<close>

text \<open>SCOPE (binding, gate fences 1/3/6): CONDITIONAL exactly-once --- the
  arrival premise (every batch item delivered) and the currency premise (the
  claim's epoch still the fence at the end) are part of the statement's NAME
  in any headline; each is load-bearing (section 6 controls).  Arrival is at
  item-VALUE granularity.  The conclusion is a count equation on the
  ACCEPTANCE LEDGER; at-most-once comes from the record safety theorem through
  the erased run, at-least-once from the delivered-while-current engine.  The
  currency premise needs no "no claim in the segment" side condition: the
  fence is monotone, so @{term "t_fence t = g"} pins the fence to @{term g}
  at every point of the segment.\<close>

theorem dwt_completed_claim_arrival_exactly_once:
  assumes pre: "(wstep K)\<^sup>*\<^sup>* (winit b0) s"
      and fresh: "t_fence s < g"
      and Bdef: "B = stamped_at (length (fst (t_journal s))) g
                   (filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted s)))
                     (replay_down_hist (fst (t_journal s)) K f))"
      and run: "wrun K (s\<lparr>t_fence := g, t_pending := t_pending s @ B\<rparr>) as t"
      and arrived: "\<forall>x \<in> set B. WActDeliver x \<in> set as"
      and current: "t_fence t = g"
  shows "\<forall>p \<in> set (log_payloads B).
           count (mset (log_payloads (t_accepted t))) p = 1"
proof
  fix p assume pB: "p \<in> set (log_payloads B)"
  define xB where
    "xB = \<lparr> ue_stamp = length (fst (t_journal s)), ue_gen = g, ue_pay = ULog p \<rparr>"
  have pD: "p \<in> set (filter (\<lambda>q. q \<notin> set (log_payloads (t_accepted s)))
                       (replay_down_hist (fst (t_journal s)) K f))"
    using pB by (simp add: Bdef)
  have xBinB: "xB \<in> set B"
    using pD by (auto simp: Bdef xB_def stamped_at_def)
  have delx: "WActDeliver xB \<in> set as"
    using arrived xBinB by blast
  have genx: "t_fence t \<le> ue_gen xB"
    by (simp add: current xB_def)
  have accx: "xB \<in> set (t_accepted t)"
    by (rule wrun_deliver_current_accepted[OF run delx genx])
  have memp: "p \<in> set (log_payloads (t_accepted t))"
    by (rule log_payloads_memI[OF accx]) (simp add: xB_def)
  have step_claim: "wstep K s (s\<lparr>t_fence := g, t_pending := t_pending s @ B\<rparr>)"
    by (rule wclaimI[OF fresh Bdef refl])
  have reacht: "(wstep K)\<^sup>*\<^sup>* (winit b0) t"
    using pre step_claim wrun_wsteps[OF run]
    by (meson rtranclp.rtrancl_into_rtrancl rtranclp_trans)
  have dist: "distinct (log_payloads (t_accepted t))"
    by (rule wire_accepted_duplicate_free[OF reacht])
  show "count (mset (log_payloads (t_accepted t))) p = 1"
    by (rule distinct_count_mem_1[OF dist memp])
qed

corollary dwt_completed_claim_arrival_at_least_once:
  assumes pre: "(wstep K)\<^sup>*\<^sup>* (winit b0) s"
      and fresh: "t_fence s < g"
      and Bdef: "B = stamped_at (length (fst (t_journal s))) g
                   (filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted s)))
                     (replay_down_hist (fst (t_journal s)) K f))"
      and run: "wrun K (s\<lparr>t_fence := g, t_pending := t_pending s @ B\<rparr>) as t"
      and arrived: "\<forall>x \<in> set B. WActDeliver x \<in> set as"
      and current: "t_fence t = g"
  shows "set (log_payloads B) \<subseteq> set (log_payloads (t_accepted t))"
proof
  fix p assume pB: "p \<in> set (log_payloads B)"
  have "count (mset (log_payloads (t_accepted t))) p = 1"
    using dwt_completed_claim_arrival_exactly_once[OF assms] pB by blast
  then show "p \<in> set (log_payloads (t_accepted t))"
    by (metis count_greater_zero_iff zero_less_one set_mset_mset)
qed

section \<open>6. Non-vacuity witness and the two premise controls\<close>

text \<open>All three runs live at the concrete \<open>(nat, nat)\<close> instance.  The witness
  instantiates EVERY premise of the conditional theorem and evaluates the
  count concretely; the two controls each violate EXACTLY ONE of the two
  substantive premises and evaluate the unconditioned conclusion FALSE ---
  \<exists>-witness refutations per the polarity fence (no universal impossibility
  claim).\<close>

subsection \<open>6.1 The witness: claim, arrival, currency --- count 1\<close>

definition cc_p :: "src_coord \<times> (nat, nat) source_event" where
  "cc_p = (ec1, Insert 0 0)"

definition cc_x :: "(nat, nat) uemission" where
  "cc_x = \<lparr> ue_stamp = 1, ue_gen = 1, ue_pay = ULog cc_p \<rparr>"

definition cc0 :: "((nat, nat) uemission, (nat, nat) ujournal) tstate" where
  "cc0 = winit Map.empty"

definition cc1 where "cc1 = cc0\<lparr>t_journal := ([cc_p], Map.empty)\<rparr>"
definition cc2 where "cc2 = cc1\<lparr>t_fence := 1, t_pending := [cc_x]\<rparr>"
definition cc3 where "cc3 = cc2\<lparr>t_pending := [], t_accepted := [cc_x]\<rparr>"

lemma cc_step01: "wstep UNIV cc0 cc1"
  by (rule wproduceI[of _ cc_p])
     (simp_all add: cc0_def cc1_def winit_def ainit_def strictly_ascending_source_def)

lemma cc_pre: "(wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) cc1"
proof -
  have "(wstep UNIV)\<^sup>*\<^sup>* cc0 cc1" using cc_step01 by (rule r_into_rtranclp)
  then show ?thesis by (simp add: cc0_def)
qed

lemma cc_replay: "replay_down_hist [cc_p] (UNIV :: nat set) ec1 = [cc_p]"
  by (simp add: replay_down_hist_def cc_p_def)

lemma cc_Bshape:
  "[cc_x] = stamped_at (length (fst (t_journal cc1))) 1
     (filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted cc1)))
       (replay_down_hist (fst (t_journal cc1)) UNIV ec1))"
  by (simp add: cc1_def cc0_def winit_def ainit_def cc_replay
                log_payloads_def map_filter_simps stamped_at_def cc_x_def)

lemma cc_claim_state:
  "cc2 = cc1\<lparr>t_fence := 1, t_pending := t_pending cc1 @ [cc_x]\<rparr>"
  by (simp add: cc2_def cc1_def cc0_def winit_def ainit_def)

lemma cc_run: "wrun UNIV cc2 [WActDeliver cc_x] cc3"
proof (rule wrunI_deliver[of 0])
  show "0 < length (t_pending cc2)"
    by (simp add: cc2_def)
  show "cc_x = t_pending cc2 ! 0"
    by (simp add: cc2_def)
  show "cc3 = cc2\<lparr>t_pending := take 0 (t_pending cc2) @ drop (Suc 0) (t_pending cc2),
                  t_accepted := t_accepted cc2
                    @ filter (\<lambda>y. t_fence cc2 \<le> ue_gen y) [t_pending cc2 ! 0]\<rparr>"
    by (simp add: cc3_def cc2_def cc1_def cc0_def winit_def ainit_def cc_x_def)
  show "wrun UNIV cc3 [] cc3" by (rule wrun.wr_nil)
qed

theorem dwt_completed_claim_witness:
  "(wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) cc1
   \<and> t_fence cc1 < 1
   \<and> [cc_x] = stamped_at (length (fst (t_journal cc1))) 1
        (filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted cc1)))
          (replay_down_hist (fst (t_journal cc1)) UNIV ec1))
   \<and> cc2 = cc1\<lparr>t_fence := 1, t_pending := t_pending cc1 @ [cc_x]\<rparr>
   \<and> wrun UNIV cc2 [WActDeliver cc_x] cc3
   \<and> (\<forall>x \<in> set [cc_x]. WActDeliver x \<in> set [WActDeliver cc_x])
   \<and> t_fence cc3 = 1
   \<and> count (mset (log_payloads (t_accepted cc3))) cc_p = 1"
proof (intro conjI)
  show "(wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) cc1" by (rule cc_pre)
  show "t_fence cc1 < 1"
    by (simp add: cc1_def cc0_def winit_def ainit_def)
  show "[cc_x] = stamped_at (length (fst (t_journal cc1))) 1
          (filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted cc1)))
            (replay_down_hist (fst (t_journal cc1)) UNIV ec1))"
    by (rule cc_Bshape)
  show "cc2 = cc1\<lparr>t_fence := 1, t_pending := t_pending cc1 @ [cc_x]\<rparr>"
    by (rule cc_claim_state)
  show "wrun UNIV cc2 [WActDeliver cc_x] cc3" by (rule cc_run)
  show "\<forall>x \<in> set [cc_x]. WActDeliver x \<in> set [WActDeliver cc_x]" by simp
  show "t_fence cc3 = 1"
    by (simp add: cc3_def cc2_def cc1_def cc0_def winit_def ainit_def)
  show "count (mset (log_payloads (t_accepted cc3))) cc_p = 1"
    by (simp add: cc3_def cc2_def cc1_def cc0_def winit_def ainit_def cc_x_def
                  log_payloads_def map_filter_simps)
qed

subsection \<open>6.2 Arrival is load-bearing: the lost batch\<close>

text \<open>Same claim, but the batch is LOST instead of delivered: the claim stays
  current, the wire drains, and the ledger count is 0 --- the unconditioned
  conclusion FAILS, so the arrival premise cannot be dropped from the
  conditional theorem.\<close>

definition al_p :: "src_coord \<times> (nat, nat) source_event" where
  "al_p = (ec1, Insert 0 0)"

definition al_x :: "(nat, nat) uemission" where
  "al_x = \<lparr> ue_stamp = 1, ue_gen = 1, ue_pay = ULog al_p \<rparr>"

definition al0 :: "((nat, nat) uemission, (nat, nat) ujournal) tstate" where
  "al0 = winit Map.empty"

definition al1 where "al1 = al0\<lparr>t_journal := ([al_p], Map.empty)\<rparr>"
definition al2 where "al2 = al1\<lparr>t_fence := 1, t_pending := [al_x]\<rparr>"
definition al3 where "al3 = al2\<lparr>t_pending := []\<rparr>"

lemma al_pre: "(wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) al1"
proof -
  have "wstep UNIV al0 al1"
    by (rule wproduceI[of _ al_p])
       (simp_all add: al0_def al1_def winit_def ainit_def strictly_ascending_source_def)
  then have "(wstep UNIV)\<^sup>*\<^sup>* al0 al1" by (rule r_into_rtranclp)
  then show ?thesis by (simp add: al0_def)
qed

lemma al_Bshape:
  "[al_x] = stamped_at (length (fst (t_journal al1))) 1
     (filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted al1)))
       (replay_down_hist (fst (t_journal al1)) UNIV ec1))"
  by (simp add: al1_def al0_def winit_def ainit_def replay_down_hist_def al_p_def
                log_payloads_def map_filter_simps stamped_at_def al_x_def)

lemma al_run: "wrun UNIV al2 [WActLose al_x] al3"
proof (rule wrunI_lose[of 0])
  show "0 < length (t_pending al2)" by (simp add: al2_def)
  show "al_x = t_pending al2 ! 0" by (simp add: al2_def)
  show "al3 = al2\<lparr>t_pending := take 0 (t_pending al2) @ drop (Suc 0) (t_pending al2)\<rparr>"
    by (simp add: al3_def al2_def)
  show "wrun UNIV al3 [] al3" by (rule wrun.wr_nil)
qed

theorem dwt_completed_claim_arrival_load_bearing:
  "(wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) al1
   \<and> t_fence al1 < 1
   \<and> [al_x] = stamped_at (length (fst (t_journal al1))) 1
        (filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted al1)))
          (replay_down_hist (fst (t_journal al1)) UNIV ec1))
   \<and> al2 = al1\<lparr>t_fence := 1, t_pending := t_pending al1 @ [al_x]\<rparr>
   \<and> wrun UNIV al2 [WActLose al_x] al3
   \<and> t_fence al3 = 1
   \<and> WActDeliver al_x \<notin> set [WActLose al_x]
   \<and> count (mset (log_payloads (t_accepted al3))) al_p = 0"
proof (intro conjI)
  show "(wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) al1" by (rule al_pre)
  show "t_fence al1 < 1"
    by (simp add: al1_def al0_def winit_def ainit_def)
  show "[al_x] = stamped_at (length (fst (t_journal al1))) 1
          (filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted al1)))
            (replay_down_hist (fst (t_journal al1)) UNIV ec1))"
    by (rule al_Bshape)
  show "al2 = al1\<lparr>t_fence := 1, t_pending := t_pending al1 @ [al_x]\<rparr>"
    by (simp add: al2_def al1_def al0_def winit_def ainit_def)
  show "wrun UNIV al2 [WActLose al_x] al3" by (rule al_run)
  show "t_fence al3 = 1"
    by (simp add: al3_def al2_def al1_def al0_def winit_def ainit_def)
  show "WActDeliver al_x \<notin> set [WActLose al_x]" by simp
  show "count (mset (log_payloads (t_accepted al3))) al_p = 0"
    by (simp add: al3_def al2_def al1_def al0_def winit_def ainit_def
                  log_payloads_def map_filter_simps)
qed

subsection \<open>6.3 Currency is load-bearing: the superseded claim's batch arrives\<close>

text \<open>The first claim's batch ARRIVES --- but a second claim has raised the
  fence first, so the arrival is fence-dropped and the first claim's count is
  0: arrival alone is NOT sufficient.  (The machine is behaving CORRECTLY here
  --- the superseding claim's own batch carries the payload, exactly the
  @{text dwt_witness_multiwriter} story; what fails is the FIRST claim's
  exactly-once conclusion, which is what the currency premise excludes.)\<close>

definition cy_p :: "src_coord \<times> (nat, nat) source_event" where
  "cy_p = (ec1, Insert 0 0)"

definition cy_x1 :: "(nat, nat) uemission" where
  "cy_x1 = \<lparr> ue_stamp = 1, ue_gen = 1, ue_pay = ULog cy_p \<rparr>"

definition cy_x2 :: "(nat, nat) uemission" where
  "cy_x2 = \<lparr> ue_stamp = 1, ue_gen = 2, ue_pay = ULog cy_p \<rparr>"

definition cy0 :: "((nat, nat) uemission, (nat, nat) ujournal) tstate" where
  "cy0 = winit Map.empty"

definition cy1 where "cy1 = cy0\<lparr>t_journal := ([cy_p], Map.empty)\<rparr>"
definition cy2 where "cy2 = cy1\<lparr>t_fence := 1, t_pending := [cy_x1]\<rparr>"
definition cy3 where "cy3 = cy2\<lparr>t_fence := 2, t_pending := [cy_x1, cy_x2]\<rparr>"
definition cy4 where "cy4 = cy3\<lparr>t_pending := [cy_x2]\<rparr>"

lemma cy_pre: "(wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) cy1"
proof -
  have "wstep UNIV cy0 cy1"
    by (rule wproduceI[of _ cy_p])
       (simp_all add: cy0_def cy1_def winit_def ainit_def strictly_ascending_source_def)
  then have "(wstep UNIV)\<^sup>*\<^sup>* cy0 cy1" by (rule r_into_rtranclp)
  then show ?thesis by (simp add: cy0_def)
qed

lemma cy_B1shape:
  "[cy_x1] = stamped_at (length (fst (t_journal cy1))) 1
     (filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted cy1)))
       (replay_down_hist (fst (t_journal cy1)) UNIV ec1))"
  by (simp add: cy1_def cy0_def winit_def ainit_def replay_down_hist_def cy_p_def
                log_payloads_def map_filter_simps stamped_at_def cy_x1_def)

lemma cy_run: "wrun UNIV cy2 [WActClaim 2 [cy_x2], WActDeliver cy_x1] cy4"
proof (rule wrunI_claim[where f = ec1])
  show "t_fence cy2 < 2"
    by (simp add: cy2_def cy1_def cy0_def winit_def ainit_def)
  show "[cy_x2] = stamped_at (length (fst (t_journal cy2))) 2
          (filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted cy2)))
            (replay_down_hist (fst (t_journal cy2)) UNIV ec1))"
    by (simp add: cy2_def cy1_def cy0_def winit_def ainit_def replay_down_hist_def
                  cy_p_def log_payloads_def map_filter_simps stamped_at_def cy_x2_def)
  show "cy3 = cy2\<lparr>t_fence := 2, t_pending := t_pending cy2 @ [cy_x2]\<rparr>"
    by (simp add: cy3_def cy2_def cy1_def cy0_def winit_def ainit_def)
  show "wrun UNIV cy3 [WActDeliver cy_x1] cy4"
  proof (rule wrunI_deliver[of 0])
    show "0 < length (t_pending cy3)" by (simp add: cy3_def)
    show "cy_x1 = t_pending cy3 ! 0" by (simp add: cy3_def)
    show "cy4 = cy3\<lparr>t_pending := take 0 (t_pending cy3) @ drop (Suc 0) (t_pending cy3),
                    t_accepted := t_accepted cy3
                      @ filter (\<lambda>y. t_fence cy3 \<le> ue_gen y) [t_pending cy3 ! 0]\<rparr>"
      by (simp add: cy4_def cy3_def cy2_def cy1_def cy0_def winit_def ainit_def
                    cy_x1_def)
    show "wrun UNIV cy4 [] cy4" by (rule wrun.wr_nil)
  qed
qed

theorem dwt_completed_claim_currency_load_bearing:
  "(wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) cy1
   \<and> t_fence cy1 < 1
   \<and> [cy_x1] = stamped_at (length (fst (t_journal cy1))) 1
        (filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted cy1)))
          (replay_down_hist (fst (t_journal cy1)) UNIV ec1))
   \<and> cy2 = cy1\<lparr>t_fence := 1, t_pending := t_pending cy1 @ [cy_x1]\<rparr>
   \<and> wrun UNIV cy2 [WActClaim 2 [cy_x2], WActDeliver cy_x1] cy4
   \<and> (\<forall>x \<in> set [cy_x1]. WActDeliver x \<in> set [WActClaim 2 [cy_x2], WActDeliver cy_x1])
   \<and> t_fence cy4 \<noteq> 1
   \<and> count (mset (log_payloads (t_accepted cy4))) cy_p = 0"
proof (intro conjI)
  show "(wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) cy1" by (rule cy_pre)
  show "t_fence cy1 < 1"
    by (simp add: cy1_def cy0_def winit_def ainit_def)
  show "[cy_x1] = stamped_at (length (fst (t_journal cy1))) 1
          (filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted cy1)))
            (replay_down_hist (fst (t_journal cy1)) UNIV ec1))"
    by (rule cy_B1shape)
  show "cy2 = cy1\<lparr>t_fence := 1, t_pending := t_pending cy1 @ [cy_x1]\<rparr>"
    by (simp add: cy2_def cy1_def cy0_def winit_def ainit_def)
  show "wrun UNIV cy2 [WActClaim 2 [cy_x2], WActDeliver cy_x1] cy4"
    by (rule cy_run)
  show "\<forall>x \<in> set [cy_x1]. WActDeliver x \<in> set [WActClaim 2 [cy_x2], WActDeliver cy_x1]"
    by simp
  show "t_fence cy4 \<noteq> 1"
    by (simp add: cy4_def cy3_def cy2_def cy1_def cy0_def winit_def ainit_def)
  show "count (mset (log_payloads (t_accepted cy4))) cy_p = 0"
    by (simp add: cy4_def cy3_def cy2_def cy1_def cy0_def winit_def ainit_def
                  log_payloads_def map_filter_simps)
qed

end
