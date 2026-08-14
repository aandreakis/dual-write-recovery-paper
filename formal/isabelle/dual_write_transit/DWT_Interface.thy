(*  Title:       DWT_Interface.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE TRANSIT-KERNEL INTERFACE (owner authorization DECISIONS.md D-099;
    promoted from the GREEN rung-3 spike Spike_Transit_Core.thy, commit
    34ebaa6a, statements and proofs carried verbatim) --- the abstract
    justification+delivery ("transit") interface.

    THE QUESTION THIS SESSION ANSWERS.  U8-style safety (payload-duplicate-
    freedom + justification of everything accepted) is proved ONCE against an
    abstract transit interface and discharged on TWO delivery regimes: the
    fire-point machine (Road 2's corpus regime, DWT_Fire + the WP2 pullback in
    DWT_Fire_Pullback) and a lossy/reordering wire grammar (DWT_Wire --- a
    self-contained sibling instance in the STYLE of Road 1's transport axis;
    it is not the landed channel machine of the effect tier, and no theorem
    relates the two).  The two instances differ in EXACTLY the transit
    parameter.

    This theory is corpus-generic: it imports nothing from the dual-write
    sessions.  It provides

      - the abstract ledger state (pending / accepted / fence / journal),
      - the fence-gated, transit-parametric guarded step relation  astep
        (stage, transit, deliver, fence-raise, journal-growth), with derived
        equation-premise introduction rules (the landed dwc_*I idiom) for
        instance work,
      - THE one invariant  a_deliver_distinct  over accepted (+) eligible-pending,
        plus its justification twin  a_inv_just,
      - the locale  transit_iface  whose named assumptions are the transit
        axioms, and the once-proved abstract safety theorem  a_safety :
        reachable abstract states are neither premature nor payload-duplicated.

    THE INTERFACE AXIOMS (spike finding, adopted at record grade; disclosed in
    THEOREM_LADDER.md).  The design's two transit-axiom faces collapse to ONE
    structural axiom in this list rendering:

      T1: transit ps qs ==> mset qs subseteq# mset ps

    (the surviving in-transit ITEM multiset never grows: reorder / delay / drop
    allowed, fabricate / duplicate impossible).  Both design faces are DERIVED
    lemmas (T1_payload_non_increasing, T2_identity_preserving).  Read literally,
    the two design faces (payload-level non-increase + set-level identity of
    survivors) would UNDER-specify: a transit could duplicate an item while the
    payload multiset and the item set stay legal-looking; the item-multiset
    axiom is the sound rendering.  J1 (justification append-stability) is the
    second interface axiom --- the abstract face of the landed
    u_justified_persist.

    SCOPE FENCES (binding; carried by MODEL_BOUNDARY_CONTRACTS.md).  Safety
    half ONLY: nothing here states or implies exactly-once / at-least-once /
    delivery completeness.  No optimality claim is made about this interface
    (other interfaces were not searched).  All results are positive
    forall-statements over the session's own trace grammars.

    Honesty regime: quick_and_dirty = false (ROOT-pinned), ZERO sorry, no
    axiomatization, no consts, no oracles; the only assumptions live in the
    named locale.
*)

theory DWT_Interface
  imports "HOL-Library.Multiset"
begin

section \<open>1. Abstract ledger state\<close>

text \<open>@{text t_pending} is the in-transit population (Road 2: armed batches;
  Road 1: the channel).  @{text t_accepted} is the sink's acceptance ledger.
  @{text t_fence} is the sink-side acceptance authority.  @{text t_journal} is
  an OPAQUE justification context (instances put source history + base here).\<close>

record ('e, 'j) tstate =
  t_pending  :: "'e list"
  t_accepted :: "'e list"
  t_fence    :: nat
  t_journal  :: 'j

definition ainit :: "'j \<Rightarrow> ('e, 'j) tstate" where
  "ainit j0 = \<lparr> t_pending = [], t_accepted = [], t_fence = 0, t_journal = j0 \<rparr>"

section \<open>2. Payload, eligibility, and the hazard vocabulary (parametric)\<close>

text \<open>@{text pay} projects an emission to its ledger payload (@{const None} =
  snapshot-like, contributes nothing to duplicate counting); @{text gen} is the
  fence-read tag (Road 2: @{text ue_gen}; Road 1: the emission epoch).\<close>

definition lpays :: "('e \<Rightarrow> 'p option) \<Rightarrow> 'e list \<Rightarrow> 'p list" where
  "lpays pay xs = List.map_filter pay xs"

definition a_eligible :: "('e \<Rightarrow> nat) \<Rightarrow> ('e, 'j) tstate \<Rightarrow> 'e list" where
  "a_eligible gen s = filter (\<lambda>x. t_fence s \<le> gen x) (t_pending s)"

definition a_premature :: "('j \<Rightarrow> 'e \<Rightarrow> bool) \<Rightarrow> ('e, 'j) tstate \<Rightarrow> bool" where
  "a_premature justified s \<longleftrightarrow> (\<exists>x \<in> set (t_accepted s). \<not> justified (t_journal s) x)"

definition a_duplicate :: "('e \<Rightarrow> 'p option) \<Rightarrow> ('e, 'j) tstate \<Rightarrow> bool" where
  "a_duplicate pay s \<longleftrightarrow> \<not> distinct (lpays pay (t_accepted s))"

definition a_unsafe
  :: "('j \<Rightarrow> 'e \<Rightarrow> bool) \<Rightarrow> ('e \<Rightarrow> 'p option) \<Rightarrow> ('e, 'j) tstate \<Rightarrow> bool"
where
  "a_unsafe justified pay s \<longleftrightarrow> a_premature justified s \<or> a_duplicate pay s"

section \<open>3. THE invariant: deliver-distinct over accepted (+) eligible-pending\<close>

definition a_deliver_distinct
  :: "('e \<Rightarrow> nat) \<Rightarrow> ('e \<Rightarrow> 'p option) \<Rightarrow> ('e, 'j) tstate \<Rightarrow> bool"
where
  "a_deliver_distinct gen pay s \<longleftrightarrow>
     distinct (lpays pay (t_accepted s) @ lpays pay (a_eligible gen s))"

definition a_inv_just
  :: "('e \<Rightarrow> nat) \<Rightarrow> ('j \<Rightarrow> 'e \<Rightarrow> bool) \<Rightarrow> ('e, 'j) tstate \<Rightarrow> bool"
where
  "a_inv_just gen justified s \<longleftrightarrow>
     (\<forall>x \<in> set (t_accepted s) \<union> set (a_eligible gen s). justified (t_journal s) x)"

definition a_inv where
  "a_inv gen pay justified s \<longleftrightarrow> a_deliver_distinct gen pay s \<and> a_inv_just gen justified s"

section \<open>4. List/multiset support\<close>

lemma lpays_Nil [simp]: "lpays pay [] = []"
  by (simp add: lpays_def map_filter_simps)

lemma lpays_append: "lpays pay (xs @ ys) = lpays pay xs @ lpays pay ys"
  by (simp add: lpays_def List.map_filter_def)

lemma mset_lpays:
  "mset (lpays pay xs)
     = image_mset (the \<circ> pay) (filter_mset (\<lambda>x. pay x \<noteq> None) (mset xs))"
  by (simp add: lpays_def List.map_filter_def mset_filter mset_map)

lemma mset_lpays_mono:
  assumes "mset qs \<subseteq># mset ps"
  shows "mset (lpays pay qs) \<subseteq># mset (lpays pay ps)"
  unfolding mset_lpays
  by (intro image_mset_subseteq_mono multiset_filter_mono assms)

text \<open>@{term distinct} through the multiset lens: the three workhorse facts.\<close>

lemma distinct_count_le1: "distinct xs \<longleftrightarrow> (\<forall>a. count (mset xs) a \<le> 1)"
proof (induction xs)
  case Nil show ?case by simp
next
  case (Cons x xs)
  have cx: "count (mset xs) x = 0 \<longleftrightarrow> x \<notin> set xs"
    by (simp add: count_eq_zero_iff)
  show ?case
  proof
    assume D: "distinct (x # xs)"
    show "\<forall>a. count (mset (x # xs)) a \<le> 1"
    proof
      fix a
      show "count (mset (x # xs)) a \<le> 1"
      proof (cases "a = x")
        case True
        from D have "x \<notin> set xs" by simp
        with cx have "count (mset xs) x = 0" by simp
        with True show ?thesis by simp
      next
        case False with D Cons show ?thesis by simp
      qed
    qed
  next
    assume C: "\<forall>a. count (mset (x # xs)) a \<le> 1"
    have ex: "count (mset (x # xs)) x = Suc (count (mset xs) x)" by simp
    have "count (mset (x # xs)) x \<le> 1" using C by blast
    with ex have x0: "count (mset xs) x = 0" by linarith
    have "\<forall>a. count (mset xs) a \<le> 1"
    proof
      fix a
      show "count (mset xs) a \<le> 1"
      proof (cases "a = x")
        case True show ?thesis by (simp only: True x0 le0)
      next
        case False
        then have "count (mset (x # xs)) a = count (mset xs) a" by simp
        moreover have "count (mset (x # xs)) a \<le> 1" using C by blast
        ultimately show ?thesis by linarith
      qed
    qed
    with x0 cx Cons show "distinct (x # xs)" by simp
  qed
qed

lemma distinct_mset_le:
  assumes sub: "mset qs \<subseteq># mset ps" and d: "distinct ps"
  shows "distinct qs"
  unfolding distinct_count_le1
proof
  fix a
  have "count (mset qs) a \<le> count (mset ps) a" using sub by (rule mset_subset_eq_count)
  also have "\<dots> \<le> 1" using d unfolding distinct_count_le1 by blast
  finally show "count (mset qs) a \<le> 1" .
qed

lemma distinct_mset_eq: "mset qs = mset ps \<Longrightarrow> distinct qs \<longleftrightarrow> distinct ps"
  by (simp add: distinct_count_le1)

lemma mset_filter_mono_pred:
  assumes imp: "\<And>x. P' x \<Longrightarrow> P x"
  shows "mset (filter P' xs) \<subseteq># mset (filter P xs)"
  using imp by (induction xs) (auto simp: subseteq_mset_def)

lemma mset_filter_mono_sub:
  assumes "mset qs \<subseteq># mset ps"
  shows "mset (filter P qs) \<subseteq># mset (filter P ps)"
  using multiset_filter_mono[OF assms, of P] by (simp add: mset_filter)

lemma mset_append_mono_right:
  assumes "mset ys' \<subseteq># mset ys"
  shows "mset (xs @ ys') \<subseteq># mset (xs @ ys)"
  unfolding subseteq_mset_def
proof
  fix a
  have "count (mset ys') a \<le> count (mset ys) a"
    using assms unfolding subseteq_mset_def by blast
  then show "count (mset (xs @ ys')) a \<le> count (mset (xs @ ys)) a" by simp
qed

lemma deliver_split:
  assumes i: "i < length xs"
  shows "mset xs = add_mset (xs ! i) (mset (take i xs @ drop (Suc i) xs))"
proof -
  have "mset xs = mset (take i xs @ xs ! i # drop (Suc i) xs)"
    using id_take_nth_drop[OF i] by simp
  also have "\<dots> = add_mset (xs ! i) (mset (take i xs @ drop (Suc i) xs))"
    by simp
  finally show ?thesis .
qed

section \<open>5. The abstract guarded step relation\<close>

text \<open>Five rule shapes.  @{text AStage} is the only guarded producer-side rule:
  the staged batch's ELIGIBLE part must be payload-distinct, payload-fresh
  against accepted and against the eligible in-transit population, and
  justified at the staging journal.  Sub-fence staged items are unconstrained
  (they can never be accepted while the fence only rises --- the zombie face).
  @{text ADeliver} is the ONE fence-gate: an arbitrary in-transit sub-multiset
  resolves, and exactly its fence-eligible part enters the ledger --- Road 2's
  @{text "if fence \<le> gen then B else []"} fire/publish gate and Road 1's
  arrive-accept/arrive-drop index-pop are both literal instances of this
  filter.  @{text ATransit} is the parameter under test.\<close>

inductive astep
  :: "('e \<Rightarrow> nat) \<Rightarrow> ('e \<Rightarrow> 'p option) \<Rightarrow> ('j \<Rightarrow> 'e \<Rightarrow> bool) \<Rightarrow> ('j \<Rightarrow> 'j \<Rightarrow> bool)
      \<Rightarrow> ('e list \<Rightarrow> 'e list \<Rightarrow> bool)
      \<Rightarrow> ('e, 'j) tstate \<Rightarrow> ('e, 'j) tstate \<Rightarrow> bool"
  for gen pay justified jle transit
where
  AJournal:
    "jle (t_journal s) j' \<Longrightarrow>
     astep gen pay justified jle transit s (s\<lparr>t_journal := j'\<rparr>)"
| AStage:
    "\<lbrakk>EB = filter (\<lambda>x. t_fence s \<le> gen x) B;
      distinct (lpays pay EB);
      set (lpays pay EB) \<inter> set (lpays pay (t_accepted s)) = {};
      set (lpays pay EB) \<inter> set (lpays pay (a_eligible gen s)) = {};
      \<forall>x \<in> set EB. justified (t_journal s) x\<rbrakk> \<Longrightarrow>
     astep gen pay justified jle transit s (s\<lparr>t_pending := t_pending s @ B\<rparr>)"
| ATransit:
    "transit (t_pending s) qs \<Longrightarrow>
     astep gen pay justified jle transit s (s\<lparr>t_pending := qs\<rparr>)"
| ADeliver:
    "mset (t_pending s) = mset B + mset qs \<Longrightarrow>
     astep gen pay justified jle transit s
       (s\<lparr>t_pending := qs,
          t_accepted := t_accepted s @ filter (\<lambda>x. t_fence s \<le> gen x) B\<rparr>)"
| ARaise:
    "t_fence s \<le> n \<Longrightarrow>
     astep gen pay justified jle transit s (s\<lparr>t_fence := n\<rparr>)"

subsection \<open>5.1 Derived introduction rules (equation-premise form)\<close>

text \<open>The landed @{text "dwc_*I"} idiom, equation-FIRST so that structured
  @{text "proof (rule \<dots>)"} blocks pin the successor state up front.  Added at
  promotion for instance work (the WP2 pullback and future instance
  discharges); each is proved from its @{const astep} rule --- no new content.\<close>

lemma astepJournalI:
  assumes "s' = s\<lparr>t_journal := j'\<rparr>"
      and "jle (t_journal s) j'"
  shows "astep gen pay justified jle transit s s'"
  unfolding assms(1) by (rule astep.AJournal) (rule assms(2))

lemma astepStageI:
  assumes "s' = s\<lparr>t_pending := t_pending s @ B\<rparr>"
      and "EB = filter (\<lambda>x. t_fence s \<le> gen x) B"
      and "distinct (lpays pay EB)"
      and "set (lpays pay EB) \<inter> set (lpays pay (t_accepted s)) = {}"
      and "set (lpays pay EB) \<inter> set (lpays pay (a_eligible gen s)) = {}"
      and "\<forall>x \<in> set EB. justified (t_journal s) x"
  shows "astep gen pay justified jle transit s s'"
  unfolding assms(1)
  by (rule astep.AStage)
     (rule assms(2), rule assms(3), rule assms(4), rule assms(5), rule assms(6))

lemma astepTransitI:
  assumes "s' = s\<lparr>t_pending := qs\<rparr>"
      and "transit (t_pending s) qs"
  shows "astep gen pay justified jle transit s s'"
  unfolding assms(1) by (rule astep.ATransit) (rule assms(2))

lemma astepDeliverI:
  assumes "s' = s\<lparr>t_pending := qs,
                  t_accepted := t_accepted s @ filter (\<lambda>x. t_fence s \<le> gen x) B\<rparr>"
      and "mset (t_pending s) = mset B + mset qs"
  shows "astep gen pay justified jle transit s s'"
  unfolding assms(1) by (rule astep.ADeliver) (rule assms(2))

lemma astepRaiseI:
  assumes "s' = s\<lparr>t_fence := n\<rparr>"
      and "t_fence s \<le> n"
  shows "astep gen pay justified jle transit s s'"
  unfolding assms(1) by (rule astep.ARaise) (rule assms(2))

section \<open>6. The transit interface and the once-proved safety theorem\<close>

text \<open>The transit axioms in this list rendering: transit relates concrete
  emission lists, so ONE structural axiom @{text T1} (the surviving in-transit
  multiset never grows: reorder / delay / drop allowed, fabricate / duplicate
  impossible) carries BOTH design faces --- payload-non-increase is derived
  below as @{text T1_payload_non_increasing}, and identity-preservation (a
  surviving item is byte-identical to a staged one: stamps, tags, payloads
  intact) as @{text T2_identity_preserving}.  @{text J1} is the design's
  justification append-stability.\<close>

locale transit_iface =
  fixes justified :: "'j \<Rightarrow> 'e \<Rightarrow> bool"
    and jle :: "'j \<Rightarrow> 'j \<Rightarrow> bool"
    and transit :: "'e list \<Rightarrow> 'e list \<Rightarrow> bool"
  assumes T1: "transit ps qs \<Longrightarrow> mset qs \<subseteq># mset ps"
      and J1: "\<lbrakk>justified j x; jle j j'\<rbrakk> \<Longrightarrow> justified j' x"
begin

text \<open>The tag and payload projections @{text gen} / @{text pay} are NOT
  constrained by any interface axiom, so they stay schematic in every lemma
  below (each instance supplies its own).  Only the three constrained
  parameters are locale-fixed.\<close>

lemma T1_payload_non_increasing:
  "transit ps qs \<Longrightarrow> mset (lpays pay qs) \<subseteq># mset (lpays pay ps)"
  by (intro mset_lpays_mono T1)

lemma T2_identity_preserving:
  "transit ps qs \<Longrightarrow> x \<in> set qs \<Longrightarrow> x \<in> set ps"
  by (drule T1) (metis mset_subset_eqD set_mset_mset)

lemma a_inv_init: "a_inv gen pay justified (ainit j0)"
  by (simp add: a_inv_def a_deliver_distinct_def a_inv_just_def a_eligible_def ainit_def)

subsection \<open>Per-rule preservation\<close>

lemma a_inv_step:
  assumes step: "astep gen pay justified jle transit s s'"
      and inv: "a_inv gen pay justified s"
  shows "a_inv gen pay justified s'"
proof -
  have ddold: "distinct (lpays pay (t_accepted s) @ lpays pay (a_eligible gen s))"
    and jold: "\<forall>x \<in> set (t_accepted s) \<union> set (a_eligible gen s). justified (t_journal s) x"
    using inv by (simp_all add: a_inv_def a_deliver_distinct_def a_inv_just_def)
  from step show ?thesis
  proof (cases rule: astep.cases)
    case (AJournal j')
    have el: "a_eligible gen (s\<lparr>t_journal := j'\<rparr>) = a_eligible gen s"
      by (simp add: a_eligible_def)
    have dd: "a_deliver_distinct gen pay (s\<lparr>t_journal := j'\<rparr>)"
      using ddold by (simp add: a_deliver_distinct_def el)
    have ij: "a_inv_just gen justified (s\<lparr>t_journal := j'\<rparr>)"
      unfolding a_inv_just_def el
      using jold by (auto intro: J1[OF _ AJournal(2)])
    show ?thesis by (simp add: AJournal(1) a_inv_def dd ij)
  next
    case (AStage EB B)
    note s'eq = AStage(1) and EBdef = AStage(2) and Bdist = AStage(3)
     and Bacc = AStage(4) and Belig = AStage(5) and Bjust = AStage(6)
    have el: "a_eligible gen (s\<lparr>t_pending := t_pending s @ B\<rparr>) = a_eligible gen s @ EB"
      by (simp add: a_eligible_def EBdef)
    have dd: "a_deliver_distinct gen pay (s\<lparr>t_pending := t_pending s @ B\<rparr>)"
      unfolding a_deliver_distinct_def
      using ddold Bdist Bacc Belig
      by (auto simp: el lpays_append distinct_append)
    have ij: "a_inv_just gen justified (s\<lparr>t_pending := t_pending s @ B\<rparr>)"
      unfolding a_inv_just_def using jold Bjust by (auto simp: el)
    show ?thesis by (simp add: s'eq a_inv_def dd ij)
  next
    case (ATransit qs)
    have sub: "mset qs \<subseteq># mset (t_pending s)" by (rule T1[OF ATransit(2)])
    have elsub: "mset (a_eligible gen (s\<lparr>t_pending := qs\<rparr>)) \<subseteq># mset (a_eligible gen s)"
      using mset_filter_mono_sub[OF sub] by (simp add: a_eligible_def)
    have paysub:
      "mset (lpays pay (t_accepted s) @ lpays pay (a_eligible gen (s\<lparr>t_pending := qs\<rparr>)))
         \<subseteq># mset (lpays pay (t_accepted s) @ lpays pay (a_eligible gen s))"
      by (rule mset_append_mono_right[OF mset_lpays_mono[OF elsub]])
    have ddnew: "distinct (lpays pay (t_accepted s)
                    @ lpays pay (a_eligible gen (s\<lparr>t_pending := qs\<rparr>)))"
      by (rule distinct_mset_le[OF paysub ddold])
    have dd: "a_deliver_distinct gen pay (s\<lparr>t_pending := qs\<rparr>)"
      using ddnew by (simp add: a_deliver_distinct_def)
    have elset: "set (a_eligible gen (s\<lparr>t_pending := qs\<rparr>)) \<subseteq> set (a_eligible gen s)"
      using elsub by (metis mset_subset_eqD set_mset_mset subsetI)
    have ij: "a_inv_just gen justified (s\<lparr>t_pending := qs\<rparr>)"
      unfolding a_inv_just_def using jold elset by auto
    show ?thesis by (simp add: ATransit(1) a_inv_def dd ij)
  next
    case (ADeliver B qs)
    let ?P = "\<lambda>x. t_fence s \<le> gen x"
    let ?s' = "s\<lparr>t_pending := qs, t_accepted := t_accepted s @ filter ?P B\<rparr>"
    have msplit: "mset (t_pending s) = mset B + mset qs" by (rule ADeliver(2))
    have elsplit:
      "mset (a_eligible gen s) = mset (filter ?P B) + mset (filter ?P qs)"
      by (simp add: a_eligible_def mset_filter msplit filter_union_mset)
    have el': "a_eligible gen ?s' = filter ?P qs"
      by (simp add: a_eligible_def)
    \<comment> \<open>the payload multiset of accepted (+) eligible is EXACTLY preserved\<close>
    have lpsplit: "mset (lpays pay (a_eligible gen s))
            = mset (lpays pay (filter ?P B)) + mset (lpays pay (filter ?P qs))"
      unfolding mset_lpays by (simp add: elsplit filter_union_mset image_mset_union)
    have paymove:
      "mset (lpays pay (t_accepted ?s') @ lpays pay (a_eligible gen ?s'))
         = mset (lpays pay (t_accepted s) @ lpays pay (a_eligible gen s))"
      by (simp add: el' lpays_append lpsplit ac_simps)
    have ddnew: "distinct (lpays pay (t_accepted ?s') @ lpays pay (a_eligible gen ?s'))"
      using ddold distinct_mset_eq[OF paymove] by blast
    have dd: "a_deliver_distinct gen pay ?s'"
      using ddnew by (simp add: a_deliver_distinct_def)
    have BsubP: "mset B \<subseteq># mset (t_pending s)"
      unfolding msplit subseteq_mset_def by simp
    have qsubP: "mset qs \<subseteq># mset (t_pending s)"
      unfolding msplit subseteq_mset_def by simp
    have Bsub: "set (filter ?P B) \<subseteq> set (a_eligible gen s)"
    proof
      fix x assume "x \<in> set (filter ?P B)"
      then have xB: "x \<in> set B" and xP: "?P x" by auto
      from xB BsubP have "x \<in> set (t_pending s)"
        by (metis mset_subset_eqD set_mset_mset)
      with xP show "x \<in> set (a_eligible gen s)" by (simp add: a_eligible_def)
    qed
    have qsub: "set (filter ?P qs) \<subseteq> set (a_eligible gen s)"
    proof
      fix x assume "x \<in> set (filter ?P qs)"
      then have xq: "x \<in> set qs" and xP: "?P x" by auto
      from xq qsubP have "x \<in> set (t_pending s)"
        by (metis mset_subset_eqD set_mset_mset)
      with xP show "x \<in> set (a_eligible gen s)" by (simp add: a_eligible_def)
    qed
    have ij: "a_inv_just gen justified ?s'"
      unfolding a_inv_just_def using jold Bsub qsub by (auto simp: el')
    show ?thesis by (simp add: ADeliver(1) a_inv_def dd ij)
  next
    case (ARaise n)
    let ?s' = "s\<lparr>t_fence := n\<rparr>"
    have imp: "\<And>x. n \<le> gen x \<Longrightarrow> t_fence s \<le> gen x"
      by (rule order_trans[OF ARaise(2)])
    have elsub: "mset (a_eligible gen ?s') \<subseteq># mset (a_eligible gen s)"
    proof -
      have "mset (filter (\<lambda>x. n \<le> gen x) (t_pending s))
              \<subseteq># mset (filter (\<lambda>x. t_fence s \<le> gen x) (t_pending s))"
        by (rule mset_filter_mono_pred) (rule imp)
      then show ?thesis by (simp add: a_eligible_def)
    qed
    have paysub:
      "mset (lpays pay (t_accepted s) @ lpays pay (a_eligible gen ?s'))
         \<subseteq># mset (lpays pay (t_accepted s) @ lpays pay (a_eligible gen s))"
      by (rule mset_append_mono_right[OF mset_lpays_mono[OF elsub]])
    have ddnew: "distinct (lpays pay (t_accepted s) @ lpays pay (a_eligible gen ?s'))"
      by (rule distinct_mset_le[OF paysub ddold])
    have dd: "a_deliver_distinct gen pay ?s'"
      using ddnew by (simp add: a_deliver_distinct_def)
    have elset: "set (a_eligible gen ?s') \<subseteq> set (a_eligible gen s)"
      using elsub by (metis mset_subset_eqD set_mset_mset subsetI)
    have ij: "a_inv_just gen justified ?s'"
      unfolding a_inv_just_def using jold elset by auto
    show ?thesis by (simp add: ARaise(1) a_inv_def dd ij)
  qed
qed

lemma a_inv_reach:
  assumes "(astep gen pay justified jle transit)\<^sup>*\<^sup>* s0 s"
      and "a_inv gen pay justified s0"
  shows "a_inv gen pay justified s"
  using assms by (induction rule: rtranclp_induct) (auto intro: a_inv_step)

lemma a_inv_safe:
  assumes "a_inv gen pay justified s"
  shows "\<not> a_unsafe justified pay s"
proof -
  have "distinct (lpays pay (t_accepted s))"
    using assms by (simp add: a_inv_def a_deliver_distinct_def)
  moreover have "\<forall>x \<in> set (t_accepted s). justified (t_journal s) x"
    using assms by (simp add: a_inv_def a_inv_just_def)
  ultimately show ?thesis
    by (simp add: a_unsafe_def a_premature_def a_duplicate_def)
qed

subsection \<open>The abstract U8-safety statement, proved ONCE\<close>

theorem a_safety:
  assumes "(astep gen pay justified jle transit)\<^sup>*\<^sup>* (ainit j0) s"
  shows "\<not> a_unsafe justified pay s"
  by (rule a_inv_safe[OF a_inv_reach[OF assms a_inv_init]])

corollary a_safety_duplicate_free:
  assumes "(astep gen pay justified jle transit)\<^sup>*\<^sup>* (ainit j0) s"
  shows "distinct (lpays pay (t_accepted s))"
  using a_safety[OF assms] by (simp add: a_unsafe_def a_duplicate_def)

corollary a_safety_no_premature:
  assumes "(astep gen pay justified jle transit)\<^sup>*\<^sup>* (ainit j0) s"
  shows "\<forall>x \<in> set (t_accepted s). justified (t_journal s) x"
  using a_safety[OF assms] by (auto simp: a_unsafe_def a_premature_def)

end  \<comment> \<open>locale @{text transit_iface}\<close>

end
