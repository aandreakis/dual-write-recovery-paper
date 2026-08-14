(*  Title:       DWT_Fire.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE FIRE-POINT INSTANCE (owner authorization DECISIONS.md D-099; promoted
    from the GREEN rung-3 spike Spike_Transit_Fire.thy, commit 34ebaa6a,
    statements and proofs carried verbatim; three shared helper lemmas hoisted
    here from the spike's wire theory --- see subsection 1.1) --- the abstract
    transit interface instantiated at Road-2's emission/justification
    vocabulary, with STATEMENT-LEVEL INSTANCE CORRESPONDENCE to Road-2's U8
    (u_fenced_multiwriter_discipline_safe at
    dual_write_unified/DWU_Fenced_Discipline.thy).

    WHAT THIS THEORY ESTABLISHES (the spike's disclosed statement-level
    reading): the abstract safety statement, instantiated at (ue_gen, upay, uj,
    ujle, fire_transit), yields U8's statement SHAPE --- the instantiated
    hazard predicate is proved LITERALLY EQUAL to Road-2's u_effect_unsafe
    under a definitional ledger projection (fire_hazard_correspondence), the
    fence gate "accepted @ (if fence <= gen then B else [])" of ulift_publish /
    usnap / ufire is proved to be the abstract deliver-filter instance
    (fire_gate_shape), and the justification/payload projections coincide
    definitionally (uj_is_u_justified, lpays_is_log_payloads).

    THE PULLBACK (the full dwu-trace simulation --- every disciplined dwu trace
    abstractly replayed, making Road-2's U8 conclusion a corollary of the
    interface theorem) is NOT in this theory: it is WP2, landed as the sibling
    DWT_Fire_Pullback.  The landed u_fenced_multiwriter_discipline_safe REMAINS
    the theorem of record and the pinned principal.

    ONE shared justification+payload instantiation (upay, uj, ujle at the
    corpus uemission type) serves BOTH instances (fire here, wire in DWT_Wire),
    so fire and wire differ in EXACTLY the transit parameter.

    NOTHING in the frozen sessions is touched; this theory only IMPORTS them.
*)

theory DWT_Fire
  imports
    DWT_Interface
    "Dual_Write_Unified.DWU_Fenced_Discipline"
begin

section \<open>1. The shared justification+payload interface at the corpus types\<close>

text \<open>ONE payload projection and ONE justification interface serve BOTH
  instances (fire here, wire in the sibling theory); the two instances differ
  ONLY in the transit parameter.  @{text upay} projects @{const ULog} payloads
  (snapshot emissions carry no ledger payload --- exactly Road-2's
  @{const log_payloads} treatment); the journal type pairs the committed source
  history with the frozen base, exactly the two inputs Road-2's
  @{const u_justified} reads.\<close>

definition upay :: "('k, 'v) uemission \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) option" where
  "upay x = (case ue_pay x of ULog p \<Rightarrow> Some p | USnap c k v \<Rightarrow> None)"

type_synonym ('k, 'v) ujournal = "('k, 'v) src_history \<times> ('k \<rightharpoonup> 'v)"

definition uj :: "('k, 'v) ujournal \<Rightarrow> ('k, 'v) uemission \<Rightarrow> bool" where
  "uj J x \<longleftrightarrow>
     ue_stamp x \<le> length (fst J) \<and>
     (case ue_pay x of
        ULog p \<Rightarrow> p \<in> set (take (ue_stamp x) (fst J))
      | USnap c k v \<Rightarrow> v = Src (snd J) (take (ue_stamp x) (fst J)) c k)"

definition ujle :: "('k, 'v) ujournal \<Rightarrow> ('k, 'v) ujournal \<Rightarrow> bool" where
  "ujle J J' \<longleftrightarrow> (\<exists>js. fst J' = fst J @ js) \<and> snd J' = snd J"

text \<open>J1 (justification append-stability) --- the abstract face of the landed
  @{thm [source] u_justified_persist}, proved on the abstract journal pair.\<close>

lemma uj_J1:
  assumes j: "uj J x" and le: "ujle J J'"
  shows "uj J' x"
proof -
  from le obtain js where js: "fst J' = fst J @ js" and b: "snd J' = snd J"
    by (auto simp: ujle_def)
  from j have stamp: "ue_stamp x \<le> length (fst J)" by (simp add: uj_def)
  have take_eq: "take (ue_stamp x) (fst J') = take (ue_stamp x) (fst J)"
    unfolding js using stamp by simp
  from stamp js have len: "ue_stamp x \<le> length (fst J')" by simp
  from j show ?thesis
    by (cases "ue_pay x") (simp_all add: uj_def take_eq len b)
qed

subsection \<open>1.1 Shared batch helpers (hoisted from the spike wire theory)\<close>

text \<open>Lemmas about the SHARED @{const stamped_at} tagging vocabulary, stated
  byte-identically to the spike's wire theory and hoisted here at promotion
  because the WP2 pullback (DWT_Fire_Pullback) consumes them on the fire side
  too.  (Their @{const upay} companion @{text lpays_ulog_single} is hoisted
  into subsection 3.1 below, next to the projection identity it needs.)\<close>

lemma stamped_at_gen: "x \<in> set (stamped_at m g D) \<Longrightarrow> ue_gen x = g"
  by (auto simp: stamped_at_def)

lemma filter_gate_stamped:
  "filter (\<lambda>x. g \<le> ue_gen x) (stamped_at m g D) = stamped_at m g D"
  by (simp add: stamped_at_def filter_map o_def)

section \<open>2. The fire-point transit and the interface discharge\<close>

text \<open>Road-2's armed content does not move in transit: batches sit still until
  fired, and the only in-transit mutation is a claim OVERWRITING the armed slot
  (@{text uarmf} on an already-armed generation) --- an in-transit discard.
  @{text fire_transit} is exactly that: identity or discard.\<close>

definition fire_transit :: "('k, 'v) uemission list \<Rightarrow> ('k, 'v) uemission list \<Rightarrow> bool" where
  "fire_transit ps qs \<longleftrightarrow> qs = ps \<or> qs = []"

lemma fire_iface: "transit_iface uj ujle fire_transit"
  by unfold_locales (auto simp: fire_transit_def intro: uj_J1)

text \<open>The abstract safety theorem, discharged at the fire instance.  (The
  @{text gen} and @{text pay} slots of the interface carry no axiom and are
  schematic in the exported theorem; the fire statements below pin them to
  @{const ue_gen} / @{const upay} at the @{const astep} instance.)\<close>

lemmas fire_a_safety =
  transit_iface.a_safety[OF fire_iface]

lemmas fire_a_safety_duplicate_free =
  transit_iface.a_safety_duplicate_free[OF fire_iface]

lemmas fire_a_safety_no_premature =
  transit_iface.a_safety_no_premature[OF fire_iface]

section \<open>3. Statement-level instance correspondence with Road-2's U8\<close>

subsection \<open>3.1 The projections coincide definitionally\<close>

lemma upay_alt: "upay = (\<lambda>x. case ue_pay x of ULog p \<Rightarrow> Some p | _ \<Rightarrow> None)"
  by (rule ext) (simp add: upay_def split: upayload.split)

lemma lpays_is_log_payloads: "lpays upay xs = log_payloads xs"
  by (simp add: lpays_def upay_alt log_payloads_def)

lemma uj_is_u_justified:
  "uj (dwu_journal t, exec_base (dwu_store t)) x \<longleftrightarrow> u_justified t x"
  by (simp add: uj_def u_justified_def split: upayload.split)

text \<open>The @{const upay} companion of the subsection-1.1 helpers (hoisted from
  the spike wire theory; placed here because it rides the projection identity).\<close>

lemma lpays_ulog_single:
  "lpays upay [\<lparr> ue_stamp = n, ue_gen = g, ue_pay = ULog p \<rparr>] = [p]"
  by (simp add: lpays_is_log_payloads log_payloads_single_ulog)

subsection \<open>3.2 The fence gate of the machine rules is the deliver filter\<close>

text \<open>Road-2's acceptance shape --- @{text "dwu_accepted t @ (if dwu_fence t \<le>
  ue_gen x then [x] else [])"} in @{text ulift_publish}/@{text usnap} and
  @{text "@ (if dwu_fence t \<le> g then B else [])"} in @{text ufire} (armed
  batches are generation-uniform by the arm rules) --- is the abstract
  deliver-filter at @{const ue_gen}.  The same lemma covers Road-1's
  arrive-accept/arrive-drop pair at singleton batches; the two machines'
  fence gates are ONE shape.\<close>

lemma fire_gate_shape:
  assumes "\<forall>x \<in> set B. ue_gen x = g"
  shows "filter (\<lambda>x. n \<le> ue_gen x) B = (if n \<le> g then B else [])"
  using assms by (induction B) auto

lemma fire_gate_singleton:
  "filter (\<lambda>x. n \<le> ue_gen x) [x] = (if n \<le> ue_gen x then [x] else [])"
  by simp

subsection \<open>3.3 The hazard predicates coincide under the ledger projection\<close>

text \<open>@{text dwu_ledger_proj} is a TOTAL, definitional projection of a
  dwu-state onto the abstract ledger state: the acceptance ledger, the fence,
  the justification context, and (as the in-transit population) the
  fence-eligible armed slot --- by Road-2's invariant C4 plus map
  functionality, at most one armed batch is ever fence-eligible, and it is the
  slot at the fence.  No reachability hypothesis is consumed anywhere in this
  subsection.\<close>

definition dwu_ledger_proj
  :: "('k, 'v) dwu_state \<Rightarrow> (('k, 'v) uemission, ('k, 'v) ujournal) tstate"
where
  "dwu_ledger_proj t =
     \<lparr> t_pending = (case dwu_gens t (dwu_fence t) of Some (UArmed B) \<Rightarrow> B | _ \<Rightarrow> []),
       t_accepted = dwu_accepted t,
       t_fence = dwu_fence t,
       t_journal = (dwu_journal t, exec_base (dwu_store t)) \<rparr>"

theorem fire_hazard_correspondence:
  "a_unsafe uj upay (dwu_ledger_proj t) \<longleftrightarrow> u_effect_unsafe t"
proof -
  have prem: "a_premature uj (dwu_ledger_proj t) \<longleftrightarrow> u_premature t"
    by (simp add: a_premature_def dwu_ledger_proj_def u_premature_def
                  uj_is_u_justified)
  have dup: "a_duplicate upay (dwu_ledger_proj t) \<longleftrightarrow> u_duplicate t"
    by (simp add: a_duplicate_def dwu_ledger_proj_def u_duplicate_def
                  lpays_is_log_payloads)
  show ?thesis
    by (simp add: a_unsafe_def u_effect_unsafe_def prem dup)
qed

subsection \<open>3.4 The instantiated statement in U8's shape\<close>

text \<open>The abstract safety statement at the fire instance, re-expressed through
  the hazard correspondence: every abstractly reachable state whose ledger
  projects a dwu-state satisfies U8's conclusion @{term "\<not> u_effect_unsafe t"}
  --- the SAME conclusion, the SAME hazard taxonomy, the SAME fence-gate shape.
  This is the disclosed statement-level reading; the trace-level upgrade
  (every disciplined dwu trace abstractly replayed, so that the reachability
  hypothesis below is DISCHARGED rather than assumed) is the WP2 pullback in
  DWT_Fire_Pullback.\<close>

theorem u8_statement_shape_recovered_fire:
  assumes reach: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (ainit J0) s"
      and proj: "s = dwu_ledger_proj t"
  shows "\<not> u_effect_unsafe t"
  using fire_a_safety[OF reach] by (simp add: proj fire_hazard_correspondence)

text \<open>Guard-vocabulary correspondence, recorded as facts rather than prose:
  the abstract stage guard's three obligations are exactly Road-2's discipline
  guards.  (i) D1a publish freshness discharges the accepted-side freshness for
  a singleton stage; (ii) D1b quiesce (no fence-eligible armed batch) makes the
  eligible-pending freshness VACUOUS at publish time --- projected, D1b says the
  projected pending is empty; (iii) the claim triple's distinctness guard D3 is
  the staged-batch distinctness.  Each is a one-line lemma against the landed
  guard forms.\<close>

lemma d1b_projects_empty_pending:
  assumes "\<forall>g' B. dwu_gens t g' = Some (UArmed B) \<longrightarrow> g' < dwu_fence t"
  shows "t_pending (dwu_ledger_proj t) = []"
proof -
  have "dwu_gens t (dwu_fence t) = Some (UArmed B) \<Longrightarrow> False" for B
    using assms by fastforce
  then show ?thesis
    by (auto simp: dwu_ledger_proj_def split: option.split ustage.split)
qed

lemma d1a_is_accepted_freshness:
  assumes "(c, e) \<notin> set (log_payloads (dwu_accepted t))"
  shows "set (lpays upay [\<lparr> ue_stamp = n, ue_gen = g, ue_pay = ULog (c, e) \<rparr>])
           \<inter> set (lpays upay (t_accepted (dwu_ledger_proj t))) = {}"
  using assms
  by (simp add: lpays_is_log_payloads dwu_ledger_proj_def log_payloads_single_ulog)

lemma d3_is_stage_distinctness:
  assumes "distinct (log_payloads (stamped_at n g ps))"
  shows "distinct (lpays upay (stamped_at n g ps))"
  using assms by (simp add: lpays_is_log_payloads)

end
