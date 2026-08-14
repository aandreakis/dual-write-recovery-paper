(*  Title:       DWT_Wire_Control.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE GRAMMAR-LOCAL BITING CONTROL for the wire theorem's one substantive
    premise (WP3 of the owner authorization DECISIONS.md D-099).

    WHAT THIS THEORY PROVES.  The record theorem u8_multiwriter_over_wire
    (DWT_Wire) consumes strictly_ascending_source as the wproduce guard.  This
    theory witnesses that the premise is LOAD-BEARING: the SAME grammar with
    ONLY that guard dropped (wstep_noasc below --- every other rule
    byte-identical) admits a concrete reachable state whose ACCEPTANCE LEDGER
    holds the same payload twice, i.e. the safety conclusion is FALSE over the
    guard-free grammar (dwt_asc_premise_load_bearing,
    dwt_noasc_safety_refuted).  The failure route is the aliasing double
    commit: the same source pair committed twice makes the claim-time replay
    delta contain the payload twice, the claim stages both copies at the fresh
    epoch, and both arrive fence-eligible.

    FENCE ON THE CLAIM (binding wording; do not strengthen when citing):

      - WITNESSED: dropping the ascending guard from THIS grammar breaks the
        safety conclusion, so the premise cannot simply be deleted from
        u8_multiwriter_over_wire --- it is load-bearing for this theorem over
        this grammar, hence for every proof route to it.
      - NOT CLAIMED: premise MINIMALITY or NECESSITY-up-to-equivalence.  No
        statement here says strictly_ascending_source is the weakest premise
        restoring safety, nor that a DIFFERENT machine (e.g. one whose claim
        rule deduplicates its replay delta) could not be safe without it, nor
        anything about the optimality of the interface.  The control speaks
        about exactly one grammar variant: wstep with the wproduce guard
        removed and nothing else changed.

    POLARITY (binding): this is the session's first NEGATIVE statement, and it
    follows the corpus ∃-machine discipline --- the refutation is carried by a
    concrete machine (wstep_noasc), a concrete run (na0..na5), and a concrete
    evaluated ledger equation; no universal impossibility over machines or
    routes is stated.

    SCOPE (acceptance-ledger): the evaluated hazard is a_unsafe on the
    acceptance ledger --- the same hazard vocabulary as the record theorem;
    nothing here mentions delivery completeness.
*)

theory DWT_Wire_Control
  imports DWT_Wire
begin

section \<open>1. The guard-free grammar variant (wproduce guard dropped, nothing else)\<close>

text \<open>@{const wstep} verbatim, with the @{const strictly_ascending_source}
  guard of @{text wproduce} removed (rule @{text wproduce_free}).  Every other
  rule is byte-identical to the record grammar.  This is a CONTROL grammar,
  local to this theory; the record theorem's grammar is untouched.\<close>

inductive wstep_noasc
  :: "'k set \<Rightarrow> (('k, 'v) uemission, ('k, 'v) ujournal) tstate
      \<Rightarrow> (('k, 'v) uemission, ('k, 'v) ujournal) tstate \<Rightarrow> bool"
  for K
where
  wproduce_free:
    "wstep_noasc K s (s\<lparr>t_journal := (fst (t_journal s) @ [p], snd (t_journal s))\<rparr>)"
| wsend_live:
    "\<lbrakk>x = \<lparr> ue_stamp = length (fst (t_journal s)), ue_gen = t_fence s, ue_pay = ULog p \<rparr>;
      p \<in> set (fst (t_journal s));
      p \<notin> set (log_payloads (t_accepted s));
      p \<notin> set (log_payloads (a_eligible ue_gen s))\<rbrakk> \<Longrightarrow>
     wstep_noasc K s (s\<lparr>t_pending := t_pending s @ [x]\<rparr>)"
| wsend_zombie:
    "ue_gen x < t_fence s \<Longrightarrow>
     wstep_noasc K s (s\<lparr>t_pending := t_pending s @ [x]\<rparr>)"
| wclaim:
    "\<lbrakk>t_fence s < g;
      D = filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted s)))
            (replay_down_hist (fst (t_journal s)) K f);
      B = stamped_at (length (fst (t_journal s))) g D\<rbrakk> \<Longrightarrow>
     wstep_noasc K s (s\<lparr>t_fence := g, t_pending := t_pending s @ B\<rparr>)"
| wdeliver:
    "i < length (t_pending s) \<Longrightarrow>
     wstep_noasc K s
       (s\<lparr>t_pending := take i (t_pending s) @ drop (Suc i) (t_pending s),
          t_accepted := t_accepted s
            @ filter (\<lambda>x. t_fence s \<le> ue_gen x) [t_pending s ! i]\<rparr>)"
| wlose:
    "i < length (t_pending s) \<Longrightarrow>
     wstep_noasc K s (s\<lparr>t_pending := take i (t_pending s) @ drop (Suc i) (t_pending s)\<rparr>)"
| wreorder:
    "mset qs = mset (t_pending s) \<Longrightarrow>
     wstep_noasc K s (s\<lparr>t_pending := qs\<rparr>)"

text \<open>Grammar inclusion: dropping a guard only ADDS behaviors, so every
  disciplined wire step is a control step.  The control run below therefore
  fails on the EXTENSION only --- and indeed its unsafe end state is
  unreachable in the disciplined grammar (see @{text na_unsafe_outside_wstep}
  at the end).\<close>

lemma wstep_noasc_of_wstep:
  assumes "wstep K s s'"
  shows "wstep_noasc K s s'"
  using assms
proof (cases rule: wstep.cases)
  case (wproduce p)
  show ?thesis unfolding wproduce(1) by (rule wstep_noasc.wproduce_free)
next
  case (wsend_live x p)
  show ?thesis unfolding wsend_live(1)
    by (rule wstep_noasc.wsend_live[OF wsend_live(2) wsend_live(3)
                                       wsend_live(4) wsend_live(5)])
next
  case (wsend_zombie x)
  show ?thesis unfolding wsend_zombie(1)
    by (rule wstep_noasc.wsend_zombie[OF wsend_zombie(2)])
next
  case (wclaim g D f B)
  show ?thesis unfolding wclaim(1)
    by (rule wstep_noasc.wclaim[OF wclaim(2) wclaim(3) wclaim(4)])
next
  case (wdeliver i)
  show ?thesis unfolding wdeliver(1)
    by (rule wstep_noasc.wdeliver[OF wdeliver(2)])
next
  case (wlose i)
  show ?thesis unfolding wlose(1)
    by (rule wstep_noasc.wlose[OF wlose(2)])
next
  case (wreorder qs)
  show ?thesis unfolding wreorder(1)
    by (rule wstep_noasc.wreorder[OF wreorder(2)])
qed

text \<open>Derived equation-premise introduction rules (the landed @{text "dwc_*I"}
  idiom) for the three control rules the aliasing run uses.\<close>

lemma na_produceI:
  assumes "s' = s\<lparr>t_journal := (fst (t_journal s) @ [p], snd (t_journal s))\<rparr>"
  shows "wstep_noasc K s s'"
  unfolding assms(1) by (rule wstep_noasc.wproduce_free)

lemma na_claimI:
  assumes "t_fence s < g"
      and "B = stamped_at (length (fst (t_journal s))) g
                 (filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted s)))
                   (replay_down_hist (fst (t_journal s)) K f))"
      and "s' = s\<lparr>t_fence := g, t_pending := t_pending s @ B\<rparr>"
  shows "wstep_noasc K s s'"
  unfolding assms(3) by (rule wstep_noasc.wclaim[OF assms(1) refl assms(2)])

lemma na_deliverI:
  assumes "i < length (t_pending s)"
      and "s' = s\<lparr>t_pending := take i (t_pending s) @ drop (Suc i) (t_pending s),
                  t_accepted := t_accepted s
                    @ filter (\<lambda>x. t_fence s \<le> ue_gen x) [t_pending s ! i]\<rparr>"
  shows "wstep_noasc K s s'"
  unfolding assms(2) by (rule wstep_noasc.wdeliver[OF assms(1)])

section \<open>2. The aliasing run: the same source pair committed twice\<close>

text \<open>The double commit @{text "[na_p, na_p]"} is NOT strictly ascending
  (@{term "c0 < c0"} fails), so the disciplined grammar's @{text wproduce}
  refuses the second commit; @{text wproduce_free} admits it.  The claim-time
  replay delta then contains the payload TWICE --- the delta filter
  deduplicates against the ACCEPTED record, not within the batch; batch-level
  distinctness is exactly what the ascending premise buys
  (@{text wstep_astep}, wclaim case) --- and both copies arrive
  fence-eligible.\<close>

definition na_p :: "src_coord \<times> (nat, nat) source_event" where
  "na_p = (c0, Insert 0 0)"

definition na_x :: "(nat, nat) uemission" where
  "na_x = \<lparr> ue_stamp = 2, ue_gen = 1, ue_pay = ULog na_p \<rparr>"

definition na0 :: "((nat, nat) uemission, (nat, nat) ujournal) tstate" where
  "na0 = winit Map.empty"

definition na1 where "na1 = na0\<lparr>t_journal := ([na_p], Map.empty)\<rparr>"
definition na2 where "na2 = na1\<lparr>t_journal := ([na_p, na_p], Map.empty)\<rparr>"
definition na3 where "na3 = na2\<lparr>t_fence := 1, t_pending := [na_x, na_x]\<rparr>"
definition na4 where "na4 = na3\<lparr>t_pending := [na_x], t_accepted := [na_x]\<rparr>"
definition na5 where "na5 = na4\<lparr>t_pending := [], t_accepted := [na_x, na_x]\<rparr>"

lemma na_step01: "wstep_noasc UNIV na0 na1"
  by (rule na_produceI[of _ _ na_p])
     (simp add: na0_def na1_def winit_def ainit_def)

lemma na_step12: "wstep_noasc UNIV na1 na2"
  by (rule na_produceI[of _ _ na_p])
     (simp add: na0_def na1_def na2_def winit_def ainit_def)

lemma na_replay: "replay_down_hist [na_p, na_p] (UNIV :: nat set) c0 = [na_p, na_p]"
  by (simp add: replay_down_hist_def na_p_def)

lemma na_step23: "wstep_noasc UNIV na2 na3"
proof (rule na_claimI[where g = 1 and f = c0])
  show "t_fence na2 < 1"
    by (simp add: na2_def na1_def na0_def winit_def ainit_def)
  show "[na_x, na_x] = stamped_at (length (fst (t_journal na2))) 1
          (filter (\<lambda>p. p \<notin> set (log_payloads (t_accepted na2)))
            (replay_down_hist (fst (t_journal na2)) UNIV c0))"
    by (simp add: na2_def na1_def na0_def winit_def ainit_def na_replay
                  log_payloads_def map_filter_simps stamped_at_def na_x_def)
  show "na3 = na2\<lparr>t_fence := 1, t_pending := t_pending na2 @ [na_x, na_x]\<rparr>"
    by (simp add: na3_def na2_def na1_def na0_def winit_def ainit_def)
qed

lemma na_step34: "wstep_noasc UNIV na3 na4"
  by (rule na_deliverI[of 0])
     (simp_all add: na3_def na4_def na2_def na1_def na0_def
                    winit_def ainit_def na_x_def)

lemma na_step45: "wstep_noasc UNIV na4 na5"
  by (rule na_deliverI[of 0])
     (simp_all add: na4_def na5_def na3_def na2_def na1_def na0_def
                    winit_def ainit_def na_x_def)

lemma na_reach: "(wstep_noasc UNIV)\<^sup>*\<^sup>* (winit Map.empty) na5"
proof -
  have "(wstep_noasc UNIV)\<^sup>*\<^sup>* na0 na5"
    using na_step01 na_step12 na_step23 na_step34 na_step45
    by (meson converse_rtranclp_into_rtranclp r_into_rtranclp)
  then show ?thesis by (simp add: na0_def)
qed

section \<open>3. The control facts\<close>

text \<open>The evaluated ledger: the payload sits in the ACCEPTANCE LEDGER twice
  --- @{const a_duplicate}, hence @{const a_unsafe}.  This is the biting
  control: the safety conclusion of the record theorem FAILS on the guard-free
  grammar, witnessed by one concrete run.  (Read with the header fence: the
  premise is load-bearing; minimality is claimed nowhere.)\<close>

lemma na5_ledger: "log_payloads (t_accepted na5) = [na_p, na_p]"
  by (simp add: na5_def na4_def na3_def na2_def na1_def na0_def
                winit_def ainit_def na_x_def log_payloads_def map_filter_simps)

lemma na5_unsafe: "a_unsafe uj upay na5"
proof -
  have "\<not> distinct (lpays upay (t_accepted na5))"
    by (simp add: lpays_is_log_payloads na5_ledger)
  then show ?thesis
    by (simp add: a_unsafe_def a_duplicate_def)
qed

theorem dwt_asc_premise_load_bearing:
  "(wstep_noasc UNIV)\<^sup>*\<^sup>* (winit Map.empty) na5
   \<and> log_payloads (t_accepted na5) = [na_p, na_p]
   \<and> a_unsafe uj upay na5"
  by (intro conjI na_reach na5_ledger na5_unsafe)

text \<open>The premise-free analogue of @{thm [source] u8_multiwriter_over_wire}
  over the guard-free grammar is FALSE --- an \<exists>-witness refutation at the
  concrete \<open>(nat, nat)\<close> instance.\<close>

corollary dwt_noasc_safety_refuted:
  "\<not> (\<forall>(b0 :: nat \<rightharpoonup> nat) s.
        (wstep_noasc UNIV)\<^sup>*\<^sup>* (winit b0) s \<longrightarrow> \<not> a_unsafe uj upay s)"
  using na_reach na5_unsafe by blast

text \<open>The unsafe end state is UNREACHABLE in the disciplined grammar --- the
  record theorem itself rules it out.  Together with the grammar inclusion
  @{thm [source] wstep_noasc_of_wstep}, this pins the failure to the dropped
  guard: the aliasing run lives strictly in the extension.\<close>

corollary na_unsafe_outside_wstep:
  "\<not> (wstep UNIV)\<^sup>*\<^sup>* (winit Map.empty) na5"
  using u8_multiwriter_over_wire na5_unsafe by blast

text \<open>Sharper, step-local localization: the double-commit transition itself
  (@{text "na1 \<rightarrow> na2"}) is NOT a disciplined step --- the ONLY rule that can
  produce it is @{text wproduce}, and its ascending guard evaluates to
  @{term False} on the doubled journal.\<close>

lemma na_alias_step_not_disciplined: "\<not> wstep UNIV na1 na2"
proof
  assume "wstep UNIV na1 na2"
  then show False
  proof (cases rule: wstep.cases)
    case (wproduce p)
    have "p = na_p"
      using wproduce(1)
      by (simp add: na2_def na1_def na0_def winit_def ainit_def)
    with wproduce(2) show False
      by (simp add: na1_def na0_def winit_def ainit_def na_p_def
                    strictly_ascending_source_def)
  next
    case (wsend_live x p)
    then show False
      by (simp add: na2_def na1_def na0_def winit_def ainit_def)
  next
    case (wsend_zombie x)
    then show False
      by (simp add: na2_def na1_def na0_def winit_def ainit_def)
  next
    case (wclaim g D f B)
    then show False
      by (simp add: na2_def na1_def na0_def winit_def ainit_def)
  next
    case (wdeliver i)
    then show False
      by (simp add: na2_def na1_def na0_def winit_def ainit_def)
  next
    case (wlose i)
    then show False
      by (simp add: na2_def na1_def na0_def winit_def ainit_def)
  next
    case (wreorder qs)
    then show False
      by (simp add: na2_def na1_def na0_def winit_def ainit_def)
  qed
qed

end
