(*  Title:       DWT_Wire.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE WIRE INSTANCE (owner authorization DECISIONS.md D-099; promoted from
    the GREEN rung-3 spike Spike_Transit_Wire.thy, commit 34ebaa6a, statements
    and proofs carried verbatim; three shared helper lemmas hoisted into
    DWT_Fire at promotion --- stamped_at_gen, filter_gate_stamped,
    lpays_ulog_single --- statements unchanged) --- THE NEW CONTENT.  The
    abstract transit interface instantiated at a lossy/reordering wire
    (arbitrary permutation + single-item removal, Road 1's transport regime),
    with a multi-writer fenced send/claim/arrive discipline on top, and the
    THEOREM OF RECORD

      u8_multiwriter_over_wire :
        every disciplined wire run from init has a payload-duplicate-free,
        journal-justified acceptance ledger --- under zombie sends, in-flight
        loss, and free reordering.

    WP3 RECORD NOTE (the seam, closed).  The GREEN spike proved this statement
    under the working name u8_multiwriter_over_wire_spike; the committed spike
    evidence (roads/program/spike_scratch/Spike_Transit_Wire.thy, commit
    34ebaa6a) KEEPS that historical name and remains the citation for the
    spike gate.  This theory carries the theorem-of-record name; statement and
    proof are the spike's, promoted unchanged (no back-compat alias --- nothing
    in the corpus cites the _spike name; the ladder records the mapping).  The
    WP3 companions live in sibling theories: DWT_Wire_Control (the
    grammar-local biting control witnessing the ascending premise
    load-bearing --- premise MINIMALITY is claimed NOWHERE) and
    DWT_Wire_Witnesses (the witness battery).

    WIRE-SIDE PREMISE LEDGER (binding disclosure): the ONLY substantive
    premise beyond the discipline grammar's own structural guards is
    strictly_ascending_source --- consumed as the produce-rule guard
    (wproduce), i.e. the theorem quantifies over runs whose committed source
    history stays strictly ascending (real WALs), and the claim-rule batch
    distinctness is DERIVED from it (see wstep_astep, wclaim case).  The
    remaining guards mirror Road-2's landed discipline vocabulary:
      - wsend_live's accepted-freshness   = D1a (a sink-read guard, landed);
      - wsend_live's eligible-freshness   = the producer's own unresolved
        current-epoch sends (see the honesty note at the rule);
      - wclaim's fresh epoch (fence < g)  = the UArmF fence-raise shape;
      - justification-at-stamp            = the landed stamp discipline.
    Zombie sends and losses are GUARD-FREE.  No premise of the form
    "the wire preserves order" or "no loss" is consumed anywhere.

    SCOPE FENCES (binding).  This is U8's SAFETY half over the wire
    (at-most-once + justification on the ACCEPTANCE LEDGER).  It is NOT an
    exactly-once theorem: no delivery-completeness / at-least-once conjunct is
    proved; the witness's "exactly once" below is a concrete list equation at
    one reachable state, acceptance-ledger-scoped.  This theory does not
    import Road 1's channel session and does NOT restate or recover any
    theorem of Dual_Write_Effect_Channel; the wire regime is stated against
    the shared session interface so that fire and wire differ in EXACTLY the
    transit parameter (the unification under test).
*)

theory DWT_Wire
  imports DWT_Fire
begin

section \<open>1. The wire transit: arbitrary permutation + single-item removal\<close>

definition wire_transit :: "('k, 'v) uemission list \<Rightarrow> ('k, 'v) uemission list \<Rightarrow> bool" where
  "wire_transit ps qs \<longleftrightarrow>
     mset qs = mset ps \<or> (\<exists>x. x \<in># mset ps \<and> mset qs = mset ps - {#x#})"

lemma wire_iface: "transit_iface uj ujle wire_transit"
proof unfold_locales
  fix ps qs :: "('k, 'v) uemission list"
  assume "wire_transit ps qs"
  then show "mset qs \<subseteq># mset ps"
    unfolding wire_transit_def
  proof
    assume "mset qs = mset ps"
    then show ?thesis by simp
  next
    assume "\<exists>x. x \<in># mset ps \<and> mset qs = mset ps - {#x#}"
    then obtain x where "mset qs = mset ps - {#x#}" by blast
    then show ?thesis by (simp add: diff_subset_eq_self)
  qed
qed (rule uj_J1)

text \<open>The abstract safety theorem, discharged at the wire instance --- the
  SAME once-proved theorem the fire instance consumed, at a different transit.\<close>

lemmas wire_a_safety =
  transit_iface.a_safety[OF wire_iface]

lemmas wire_a_safety_duplicate_free =
  transit_iface.a_safety_duplicate_free[OF wire_iface]

section \<open>2. The disciplined wire machine (grammar over the abstract state)\<close>

text \<open>The wire machine RUNS ON the abstract ledger state directly: pending is
  the in-flight channel population, the journal pair is (committed source
  history, frozen base).  @{text K} is the replay scope (fixed per run, as the
  landed machines fix it inside the store).

  HONESTY NOTE on @{text wsend_live}'s third guard (freshness against the
  eligible in-flight population): as a trace-grammar guard it reads the wire.
  Its producer-side reading is "do not re-send a payload you already sent this
  epoch and have not seen accepted": the invariant @{text winv} below proves
  every eligible in-flight item carries the CURRENT fence epoch, and epochs
  are claimed with a strictly fresh tag (@{text "t_fence s < g"}), so the
  eligible in-flight population is exactly the current claimant's own
  unresolved sends --- producer-local knowledge, the same knowledge Road-2's
  landed discipline grants its writers (D1a reads the sink's accepted record;
  D1b reads the arm table).  Every producer policy that tracks its own sends
  per epoch satisfies this guard; the grammar admits MORE schedulers, so the
  safety theorem covers those policies a fortiori.

  Zombie sends (@{text wsend_zombie}) are GUARD-FREE: any emission tagged
  below the fence may enter the wire at any time with any stamp and payload.
  Loss (@{text wlose}) and reordering (@{text wreorder}) are guard-free.\<close>

inductive wstep
  :: "'k set \<Rightarrow> (('k, 'v) uemission, ('k, 'v) ujournal) tstate
      \<Rightarrow> (('k, 'v) uemission, ('k, 'v) ujournal) tstate \<Rightarrow> bool"
  for K
where
  wproduce:
    "strictly_ascending_source (fst (t_journal s) @ [p]) \<Longrightarrow>
     wstep K s (s\<lparr>t_journal := (fst (t_journal s) @ [p], snd (t_journal s))\<rparr>)"
| wsend_live:
    "\<lbrakk>x = \<lparr> ue_stamp = length (fst (t_journal s)), ue_gen = t_fence s, ue_pay = ULog p \<rparr>;
      p \<in> set (fst (t_journal s));
      p \<notin> set (log_payloads (t_accepted s));
      p \<notin> set (log_payloads (a_eligible ue_gen s))\<rbrakk> \<Longrightarrow>
     wstep K s (s\<lparr>t_pending := t_pending s @ [x]\<rparr>)"
| wsend_zombie:
    "ue_gen x < t_fence s \<Longrightarrow>
     wstep K s (s\<lparr>t_pending := t_pending s @ [x]\<rparr>)"
| wclaim:
    "\<lbrakk>t_fence s < g;
      D = filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted s)))
            (replay_down_hist (fst (t_journal s)) K f);
      B = stamped_at (length (fst (t_journal s))) g D\<rbrakk> \<Longrightarrow>
     wstep K s (s\<lparr>t_fence := g, t_pending := t_pending s @ B\<rparr>)"
| wdeliver:
    "i < length (t_pending s) \<Longrightarrow>
     wstep K s
       (s\<lparr>t_pending := take i (t_pending s) @ drop (Suc i) (t_pending s),
          t_accepted := t_accepted s
            @ filter (\<lambda>x. t_fence s \<le> ue_gen x) [t_pending s ! i]\<rparr>)"
| wlose:
    "i < length (t_pending s) \<Longrightarrow>
     wstep K s (s\<lparr>t_pending := take i (t_pending s) @ drop (Suc i) (t_pending s)\<rparr>)"
| wreorder:
    "mset qs = mset (t_pending s) \<Longrightarrow>
     wstep K s (s\<lparr>t_pending := qs\<rparr>)"

definition winit :: "('k \<rightharpoonup> 'v) \<Rightarrow> (('k, 'v) uemission, ('k, 'v) ujournal) tstate" where
  "winit b0 = ainit ([], b0)"

text \<open>Derived introduction rules with the successor state as an equation
  premise (the landed @{text "dwc_*I"} idiom), for witness runs.\<close>

lemma wproduceI:
  assumes "strictly_ascending_source (fst (t_journal s) @ [p])"
      and "s' = s\<lparr>t_journal := (fst (t_journal s) @ [p], snd (t_journal s))\<rparr>"
  shows "wstep K s s'"
  unfolding assms(2) by (rule wstep.wproduce[OF assms(1)])

lemma wsend_liveI:
  assumes "x = \<lparr> ue_stamp = length (fst (t_journal s)), ue_gen = t_fence s, ue_pay = ULog p \<rparr>"
      and "p \<in> set (fst (t_journal s))"
      and "p \<notin> set (log_payloads (t_accepted s))"
      and "p \<notin> set (log_payloads (a_eligible ue_gen s))"
      and "s' = s\<lparr>t_pending := t_pending s @ [x]\<rparr>"
  shows "wstep K s s'"
  unfolding assms(5) by (rule wstep.wsend_live[OF assms(1) assms(2) assms(3) assms(4)])

lemma wsend_zombieI:
  assumes "ue_gen x < t_fence s"
      and "s' = s\<lparr>t_pending := t_pending s @ [x]\<rparr>"
  shows "wstep K s s'"
  unfolding assms(2) by (rule wstep.wsend_zombie[OF assms(1)])

lemma wclaimI:
  assumes "t_fence s < g"
      and "B = stamped_at (length (fst (t_journal s))) g
                 (filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted s)))
                   (replay_down_hist (fst (t_journal s)) K f))"
      and "s' = s\<lparr>t_fence := g, t_pending := t_pending s @ B\<rparr>"
  shows "wstep K s s'"
  unfolding assms(3) by (rule wstep.wclaim[OF assms(1) refl assms(2)])

lemma wdeliverI:
  assumes "i < length (t_pending s)"
      and "s' = s\<lparr>t_pending := take i (t_pending s) @ drop (Suc i) (t_pending s),
                  t_accepted := t_accepted s
                    @ filter (\<lambda>x. t_fence s \<le> ue_gen x) [t_pending s ! i]\<rparr>"
  shows "wstep K s s'"
  unfolding assms(2) by (rule wstep.wdeliver[OF assms(1)])

lemma wloseI:
  assumes "i < length (t_pending s)"
      and "s' = s\<lparr>t_pending := take i (t_pending s) @ drop (Suc i) (t_pending s)\<rparr>"
  shows "wstep K s s'"
  unfolding assms(2) by (rule wstep.wlose[OF assms(1)])

section \<open>3. The wire run invariant\<close>

text \<open>W1: every in-flight tag is bounded by the fence (live sends stamp the
  current fence; zombies are below it; claims outrun it and restamp).  W2: the
  committed source history is strictly ascending --- the landed named premise,
  maintained by the produce guard.\<close>

definition winv :: "(('k, 'v) uemission, ('k, 'v) ujournal) tstate \<Rightarrow> bool" where
  "winv s \<longleftrightarrow>
     (\<forall>x \<in> set (t_pending s). ue_gen x \<le> t_fence s)
   \<and> strictly_ascending_source (fst (t_journal s))"

lemma winv_init: "winv (winit b0)"
  by (simp add: winv_def winit_def ainit_def strictly_ascending_source_def)

lemma winv_step:
  assumes step: "wstep K s s'" and inv: "winv s"
  shows "winv s'"
  using step
proof (cases rule: wstep.cases)
  case (wproduce p)
  then show ?thesis using inv by (simp add: winv_def)
next
  case (wsend_live x p)
  then show ?thesis using inv by (auto simp: winv_def)
next
  case (wsend_zombie x)
  then show ?thesis using inv by (auto simp: winv_def)
next
  case (wclaim g D f B)
  have old: "\<And>x. x \<in> set (t_pending s) \<Longrightarrow> ue_gen x \<le> g"
    using inv wclaim(2) by (fastforce simp: winv_def)
  have new: "\<And>x. x \<in> set B \<Longrightarrow> ue_gen x = g"
    by (auto simp: wclaim(4) dest: stamped_at_gen)
  show ?thesis using inv old new by (auto simp: winv_def wclaim(1))
next
  case (wdeliver i)
  then show ?thesis using inv
    by (auto simp: winv_def dest: in_set_takeD in_set_dropD)
next
  case (wlose i)
  then show ?thesis using inv
    by (auto simp: winv_def dest: in_set_takeD in_set_dropD)
next
  case (wreorder qs)
  then show ?thesis using inv
    by (auto simp: winv_def dest: mset_eq_setD)
qed

section \<open>4. Every disciplined wire step is an abstract run\<close>

lemma wstep_astep:
  assumes step: "wstep K s s'" and inv: "winv s"
  shows "(astep ue_gen upay uj ujle wire_transit)\<^sup>*\<^sup>* s s'"
  using step
proof (cases rule: wstep.cases)
  case (wproduce p)
  have step: "astep ue_gen upay uj ujle wire_transit s
                (s\<lparr>t_journal := (fst (t_journal s) @ [p], snd (t_journal s))\<rparr>)"
    by (rule astep.AJournal) (auto simp: ujle_def)
  show ?thesis unfolding wproduce(1) by (rule r_into_rtranclp) (rule step)
next
  case (wsend_live x p)
  have lp: "lpays upay [x] = [p]"
    by (simp add: wsend_live(2) lpays_ulog_single)
  have just: "uj (t_journal s) x"
    unfolding wsend_live(2) uj_def using wsend_live(3) by simp
  have step: "astep ue_gen upay uj ujle wire_transit s (s\<lparr>t_pending := t_pending s @ [x]\<rparr>)"
  proof (rule astep.AStage[of "[x]"])
    show "[x] = filter (\<lambda>y. t_fence s \<le> ue_gen y) [x]" by (simp add: wsend_live(2))
    show "distinct (lpays upay [x])" by (simp add: lp)
    show "set (lpays upay [x]) \<inter> set (lpays upay (t_accepted s)) = {}"
      using wsend_live(4)
      by (simp add: wsend_live(2) lpays_is_log_payloads log_payloads_single_ulog)
    show "set (lpays upay [x]) \<inter> set (lpays upay (a_eligible ue_gen s)) = {}"
      using wsend_live(5)
      by (simp add: wsend_live(2) lpays_is_log_payloads log_payloads_single_ulog)
    show "\<forall>y \<in> set [x]. uj (t_journal s) y" using just by simp
  qed
  show ?thesis unfolding wsend_live(1) by (rule r_into_rtranclp) (rule step)
next
  case (wsend_zombie x)
  have step: "astep ue_gen upay uj ujle wire_transit s (s\<lparr>t_pending := t_pending s @ [x]\<rparr>)"
  proof (rule astep.AStage[of "[]"])
    show "[] = filter (\<lambda>y. t_fence s \<le> ue_gen y) [x]"
      using wsend_zombie(2) by simp
  qed simp_all
  show ?thesis unfolding wsend_zombie(1) by (rule r_into_rtranclp) (rule step)
next
  case (wclaim g D f B)
  let ?A = "astep ue_gen upay uj ujle wire_transit"
  let ?mid = "s\<lparr>t_fence := g\<rparr>"
  have step1: "?A s ?mid"
    using wclaim(2) by (auto intro: astep.ARaise)
  \<comment> \<open>the staged batch is wholly fence-eligible at the raised fence\<close>

  \<comment> \<open>ASC CONSUMED HERE: the journal is strictly ascending (W2), hence
      distinct, hence its filtered replay and the filtered delta are distinct\<close>
  have dj: "distinct (fst (t_journal s))"
    using inv by (simp add: winv_def strictly_ascending_distinct)
  have dD: "distinct D"
    by (simp add: wclaim(3) replay_down_hist_def dj)
  \<comment> \<open>freshness against accepted: by the delta filter itself\<close>
  have fA: "set D \<inter> set (log_payloads (t_accepted s)) = {}"
    by (auto simp: wclaim(3))
  \<comment> \<open>freshness against the eligible in-flight population: EMPTY after the
      raise, by W1 + the strictly fresh epoch\<close>
  have elig_mid: "a_eligible ue_gen ?mid = []"
  proof -
    have "\<And>x. x \<in> set (t_pending s) \<Longrightarrow> \<not> g \<le> ue_gen x"
      using inv wclaim(2) by (fastforce simp: winv_def)
    then show ?thesis
      by (simp add: a_eligible_def filter_empty_conv)
  qed
  \<comment> \<open>justification: replay payloads live in the journal at the full stamp\<close>
  have DsubJ: "set D \<subseteq> set (fst (t_journal s))"
  proof -
    have "set D \<subseteq> set (replay_down_hist (fst (t_journal s)) K f)"
      by (auto simp: wclaim(3))
    also have "\<dots> \<subseteq> set (fst (t_journal s))" by (rule replay_subset)
    finally show ?thesis .
  qed
  have justB: "\<forall>y \<in> set B. uj (t_journal ?mid) y"
  proof
    fix y assume "y \<in> set B"
    then obtain p where y: "y = \<lparr> ue_stamp = length (fst (t_journal s)),
                                  ue_gen = g, ue_pay = ULog p \<rparr>"
                    and pD: "p \<in> set D"
      by (auto simp: wclaim(4) stamped_at_def)
    from pD DsubJ have "p \<in> set (fst (t_journal s))" by blast
    then show "uj (t_journal ?mid) y"
      by (simp add: y uj_def)
  qed
  have step2: "?A ?mid (?mid\<lparr>t_pending := t_pending ?mid @ B\<rparr>)"
  proof (rule astep.AStage[of B])
    show "B = filter (\<lambda>y. t_fence ?mid \<le> ue_gen y) B"
      by (simp add: wclaim(4) filter_gate_stamped)
    show "distinct (lpays upay B)"
      by (simp add: wclaim(4) lpays_is_log_payloads dD)
    show "set (lpays upay B) \<inter> set (lpays upay (t_accepted ?mid)) = {}"
      using fA by (simp add: wclaim(4) lpays_is_log_payloads)
    show "set (lpays upay B) \<inter> set (lpays upay (a_eligible ue_gen ?mid)) = {}"
      by (simp add: elig_mid)
    show "\<forall>y \<in> set B. uj (t_journal ?mid) y" by (rule justB)
  qed
  have step2': "?A ?mid (s\<lparr>t_fence := g, t_pending := t_pending s @ B\<rparr>)"
  proof -
    have endeq: "?mid\<lparr>t_pending := t_pending ?mid @ B\<rparr>
                   = s\<lparr>t_fence := g, t_pending := t_pending s @ B\<rparr>"
      by simp
    from step2 show ?thesis unfolding endeq .
  qed
  have tail: "(astep ue_gen upay uj ujle wire_transit)\<^sup>*\<^sup>*
                ?mid (s\<lparr>t_fence := g, t_pending := t_pending s @ B\<rparr>)"
    by (rule r_into_rtranclp) (rule step2')
  show ?thesis
    unfolding wclaim(1)
    by (rule converse_rtranclp_into_rtranclp, rule step1, rule tail)
next
  case (wdeliver i)
  have msp: "mset (t_pending s)
          = mset [t_pending s ! i] + mset (take i (t_pending s) @ drop (Suc i) (t_pending s))"
    using deliver_split[OF wdeliver(2)] by simp
  have step: "astep ue_gen upay uj ujle wire_transit s
                (s\<lparr>t_pending := take i (t_pending s) @ drop (Suc i) (t_pending s),
                   t_accepted := t_accepted s
                     @ filter (\<lambda>x. t_fence s \<le> ue_gen x) [t_pending s ! i]\<rparr>)"
    by (rule astep.ADeliver[OF msp])
  show ?thesis unfolding wdeliver(1) by (rule r_into_rtranclp) (rule step)
next
  case (wlose i)
  have wt: "wire_transit (t_pending s) (take i (t_pending s) @ drop (Suc i) (t_pending s))"
  proof -
    have inm: "t_pending s ! i \<in># mset (t_pending s)"
      using wlose(2) by (simp add: nth_mem)
    have "mset (take i (t_pending s) @ drop (Suc i) (t_pending s))
            = mset (t_pending s) - {#t_pending s ! i#}"
      using deliver_split[OF wlose(2)] by simp
    with inm show ?thesis by (auto simp: wire_transit_def)
  qed
  have step: "astep ue_gen upay uj ujle wire_transit s
                (s\<lparr>t_pending := take i (t_pending s) @ drop (Suc i) (t_pending s)\<rparr>)"
    by (rule astep.ATransit) (rule wt)
  show ?thesis unfolding wlose(1) by (rule r_into_rtranclp) (rule step)
next
  case (wreorder qs)
  have wt: "wire_transit (t_pending s) qs"
    by (simp add: wire_transit_def wreorder(2))
  have step: "astep ue_gen upay uj ujle wire_transit s (s\<lparr>t_pending := qs\<rparr>)"
    by (rule astep.ATransit) (rule wt)
  show ?thesis unfolding wreorder(1) by (rule r_into_rtranclp) (rule step)
qed

section \<open>5. THE WIRE HEADLINE (theorem of record)\<close>

lemma wtrace_winv_astep:
  assumes "(wstep K)\<^sup>*\<^sup>* (winit b0) s"
  shows "winv s \<and> (astep ue_gen upay uj ujle wire_transit)\<^sup>*\<^sup>* (winit b0) s"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  show ?case by (simp add: winv_init)
next
  case (step y z)
  have wy: "winv y" and ay: "(astep ue_gen upay uj ujle wire_transit)\<^sup>*\<^sup>* (winit b0) y"
    using step.IH by auto
  have wz: "winv z" by (rule winv_step[OF step.hyps(2) wy])
  have az: "(astep ue_gen upay uj ujle wire_transit)\<^sup>*\<^sup>* (winit b0) z"
    by (rule rtranclp_trans[OF ay wstep_astep[OF step.hyps(2) wy]])
  from wz az show ?case ..
qed

text \<open>SCOPE (binding, acceptance-ledger): the conclusion speaks about the
  ACCEPTANCE LEDGER @{const t_accepted} only --- at-most-once (payload-distinct)
  plus justification of everything accepted.  No at-least-once /
  delivery-completeness / convergence conjunct is stated or implied; the
  completed-claim half over the wire is WP4 (own design gate).  The only
  substantive premise is @{const strictly_ascending_source} in guard form
  (see the header premise ledger); its load-bearing control is
  @{text DWT_Wire_Control}, and premise minimality is claimed nowhere.\<close>

theorem u8_multiwriter_over_wire:
  assumes "(wstep K)\<^sup>*\<^sup>* (winit b0) s"
  shows "\<not> a_unsafe uj upay s"
proof -
  have "(astep ue_gen upay uj ujle wire_transit)\<^sup>*\<^sup>* (ainit ([], b0)) s"
    using wtrace_winv_astep[OF assms] by (simp add: winit_def)
  from wire_a_safety[OF this] show ?thesis .
qed

corollary wire_accepted_duplicate_free:
  assumes "(wstep K)\<^sup>*\<^sup>* (winit b0) s"
  shows "distinct (log_payloads (t_accepted s))"
  using u8_multiwriter_over_wire[OF assms]
  by (simp add: a_unsafe_def a_duplicate_def lpays_is_log_payloads)

corollary wire_accepted_justified:
  assumes "(wstep K)\<^sup>*\<^sup>* (winit b0) s"
  shows "\<forall>x \<in> set (t_accepted s). uj (t_journal s) x"
  using u8_multiwriter_over_wire[OF assms]
  by (auto simp: a_unsafe_def a_premature_def)

text \<open>The premise-ledger tie-back: along every disciplined wire run the
  committed source history satisfies THE landed named premise
  @{const strictly_ascending_source} --- the produce guard is that premise in
  guard form, and nothing else about the source is assumed.\<close>

lemma wire_journal_ascending:
  assumes "(wstep K)\<^sup>*\<^sup>* (winit b0) s"
  shows "strictly_ascending_source (fst (t_journal s))"
  using wtrace_winv_astep[OF assms] by (simp add: winv_def)

lemma wstep_state_cong:
  assumes "wstep K s sa" and "sa = sb"
  shows "wstep K s sb"
  using assms by simp


section \<open>6. Non-vacuity witness: loss + re-drive + zombie + fence-drop, exactly-once outcome\<close>

text \<open>A concrete @{text "(nat, nat)"} run exercising every axis the theorem
  quantifies over: produce one source event; send it; LOSE the send in flight;
  claim epoch 1 (the fenced re-drive restages the accepted-record delta); a
  zombie copy of the same payload enters the wire at the dead epoch; the wire
  REORDERS the two in-flight items (zombie first); the zombie's arrival is
  DROPPED by the fence; the re-driven copy arrives and is ACCEPTED.  The final
  ledger holds the payload exactly once --- a concrete list equation on THIS
  witness's ACCEPTANCE LEDGER; no general delivery-completeness claim.\<close>

definition wit_p :: "src_coord \<times> (nat, nat) source_event" where
  "wit_p = (c0, Insert 0 0)"

definition wit_x1 :: "(nat, nat) uemission" where
  "wit_x1 = \<lparr> ue_stamp = 1, ue_gen = 0, ue_pay = ULog wit_p \<rparr>"

definition wit_x2 :: "(nat, nat) uemission" where
  "wit_x2 = \<lparr> ue_stamp = 1, ue_gen = 1, ue_pay = ULog wit_p \<rparr>"

definition wit_zombie :: "(nat, nat) uemission" where
  "wit_zombie = \<lparr> ue_stamp = 0, ue_gen = 0, ue_pay = ULog wit_p \<rparr>"

definition w0 :: "((nat, nat) uemission, (nat, nat) ujournal) tstate" where
  "w0 = winit Map.empty"

definition w1 where "w1 = w0\<lparr>t_journal := ([wit_p], Map.empty)\<rparr>"
definition w2 where "w2 = w1\<lparr>t_pending := [wit_x1]\<rparr>"
definition w3 where "w3 = w2\<lparr>t_pending := []\<rparr>"
definition w4 where "w4 = w3\<lparr>t_fence := 1, t_pending := [wit_x2]\<rparr>"
definition w5 where "w5 = w4\<lparr>t_pending := [wit_x2, wit_zombie]\<rparr>"
definition w6 where "w6 = w5\<lparr>t_pending := [wit_zombie, wit_x2]\<rparr>"
definition w7 where "w7 = w6\<lparr>t_pending := [wit_x2]\<rparr>"
definition w8 where "w8 = w7\<lparr>t_pending := [], t_accepted := [wit_x2]\<rparr>"

lemma wit_step01: "wstep UNIV w0 w1"
  by (rule wproduceI[of _ wit_p])
     (simp_all add: w0_def w1_def winit_def ainit_def strictly_ascending_source_def)

lemma wit_step12: "wstep UNIV w1 w2"
  by (rule wsend_liveI[of _ _ wit_p])
     (simp_all add: w0_def w1_def w2_def winit_def ainit_def a_eligible_def
                    wit_x1_def log_payloads_def map_filter_simps)

lemma wit_step23: "wstep UNIV w2 w3"
  by (rule wloseI[of 0]) (simp_all add: w2_def w3_def w1_def w0_def winit_def ainit_def)

lemma wit_replay: "replay_down_hist [wit_p] (UNIV :: nat set) c0 = [wit_p]"
  by (simp add: replay_down_hist_def wit_p_def)

lemma wit_step34: "wstep UNIV w3 w4"
proof (rule wclaimI[where g = 1 and f = c0])
  show "t_fence w3 < 1"
    by (simp add: w3_def w2_def w1_def w0_def winit_def ainit_def)
  show "[wit_x2] = stamped_at (length (fst (t_journal w3))) 1
          (filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted w3)))
            (replay_down_hist (fst (t_journal w3)) UNIV c0))"
    by (simp add: w3_def w2_def w1_def w0_def winit_def ainit_def wit_replay
                  log_payloads_def map_filter_simps stamped_at_def wit_x2_def)
  show "w4 = w3\<lparr>t_fence := 1, t_pending := t_pending w3 @ [wit_x2]\<rparr>"
    by (simp add: w4_def w3_def)
qed

lemma wit_step45: "wstep UNIV w4 w5"
  by (rule wsend_zombieI[of wit_zombie])
     (simp_all add: w4_def w5_def w3_def w2_def w1_def w0_def
                    winit_def ainit_def wit_zombie_def)

lemma wit_step56: "wstep UNIV w5 w6"
proof (rule wstep.wreorder[of "[wit_zombie, wit_x2]", THEN wstep_state_cong])
  show "mset [wit_zombie, wit_x2] = mset (t_pending w5)"
    by (simp add: w5_def w4_def add_mset_commute)
  show "w5\<lparr>t_pending := [wit_zombie, wit_x2]\<rparr> = w6"
    by (simp add: w5_def w6_def w4_def w3_def w2_def w1_def w0_def winit_def ainit_def)
qed

lemma wit_step67: "wstep UNIV w6 w7"
  by (rule wdeliverI[of 0])
     (simp_all add: w6_def w7_def w5_def w4_def w3_def w2_def w1_def w0_def
                    winit_def ainit_def wit_zombie_def)

lemma wit_step78: "wstep UNIV w7 w8"
  by (rule wdeliverI[of 0])
     (simp_all add: w7_def w8_def w6_def w5_def w4_def w3_def w2_def w1_def w0_def
                    winit_def ainit_def wit_x2_def)

lemma wit_reach: "(wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) w8"
proof -
  have "(wstep UNIV)\<^sup>*\<^sup>* w0 w8"
    using wit_step01 wit_step12 wit_step23 wit_step34 wit_step45 wit_step56
          wit_step67 wit_step78
    by (meson converse_rtranclp_into_rtranclp r_into_rtranclp)
  then show ?thesis by (simp add: w0_def)
qed

theorem wire_witness_facts:
  "(wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) w8
   \<and> log_payloads (t_accepted w8) = [wit_p]
   \<and> t_pending w8 = []
   \<and> \<not> a_unsafe uj upay w8"
proof (intro conjI)
  show "(wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) w8" by (rule wit_reach)
  show "log_payloads (t_accepted w8) = [wit_p]"
    by (simp add: w8_def w7_def w6_def w5_def w4_def w3_def w2_def w1_def w0_def
                  winit_def ainit_def wit_x2_def log_payloads_def map_filter_simps)
  show "t_pending w8 = []" by (simp add: w8_def)
  show "\<not> a_unsafe uj upay w8"
    by (rule u8_multiwriter_over_wire[OF wit_reach])
qed

end
