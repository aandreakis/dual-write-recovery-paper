(*  Title:       Dual_Write_Effect_Exactly_Once.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    T2.11: the DEDUP-SINK / EXACTLY-ONCE reading of the landed
    recovery-information dilemma (T2.10) --- a reading, never a new
    impossibility.

    Content: (i) exactly_once_at, a state-level frontier-relative predicate
    with TWO named conjuncts --- safety (the landed effect_unsafe negated)
    and delivery completeness (at_least_once_at, literally the complement
    of the landed lost_effect); (ii) the dedup sink modeled twice --- the
    ledger-view operator sink_dedup_view (remdups of the payload stream)
    and the landed sink_delta policy; (iii) the dedup-sink iff in two
    disclosed layers --- payload-level premise-free (layer 1), and
    instance-level under strictly_ascending_source (layer 2), with a
    machine-reachable aliasing control showing layer 2's premise is
    load-bearing; (iv) the cursor connection (a covered cursor IS
    at-least-once; the over-advanced cursor bites the liveness conjunct);
    (v) the positive side --- the sink-reading policy achieves exactly-once
    under EXACTLY the landed B1 premises, inhabited at the dilemma's own
    loss-side witness where the delta IS the m = 1 cursor rule; and
    (vi) the necessity face --- the landed dilemma theorems translated into
    the exactly-once vocabulary (cited, not re-proved).

    S5 design source: paper/dual_write/phase3/s5_design/
    t29_t211_ledger_semantics.md section 3, with the gate's
    canonicalizations C-1 (authority-premise attribution) and C-4
    (empty-replay vacuity remark) folded in.

    The scratch original's in-source ML oracle gates are STRIPPED here:
    oracle-freedom is certified by scratch-side per-slice gate sessions
    with confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Exactly_Once
  imports Dual_Write_Effect_Dilemma Dual_Write_Effect_Discipline
begin

section \<open>Delivery completeness, the exactly-once predicate, the dedup view\<close>

text \<open>
  EXACTLY-ONCE, stated honestly.  @{text exactly_once_at} below is a
  state-level, FRONTIER-RELATIVE predicate with TWO named conjuncts:

  \<^item> SAFETY: @{term "\<not> effect_unsafe t"} --- every emission justified at
    its fire-time stamp, and the ledger globally payload-duplicate-free.

  \<^item> DELIVERY COMPLETENESS: @{text at_least_once_at} --- every payload of
    the scoped, frontier-bounded replay of the state's OWN committed
    source prefix appears in the emission ledger.  This is the machine's
    disclosed SKIP ASYMMETRY made an explicit component:
    @{const effect_unsafe} deliberately cannot see what was never emitted
    (the Cyclic skip-disclosure block), so any definition of exactly-once
    that omitted this conjunct would silently count skipped deliveries as
    exactly-once.  It is literally the complement of the landed
    @{const lost_effect} (the definitional bridge below) and inherits its
    disclosed status: a TERMINAL-STATE STAND-IN for delivery liveness ---
    a model boundary of the same kind as acknowledgement durability in
    the landed tier-1 development, not a temporal eventually.

  Out-of-scope / beyond-frontier emissions are constrained by the safety
  conjunct only.  Counting is PAYLOAD-level: (coordinate, event) pairs
  with stamps and epochs projected away --- two emissions of one payload
  in different epochs are still a duplicate (e.g. the banked
  @{const f_amp_w}).

  THE TWO PINNED NAMED PREMISES (the Cyclic header's prose block), with
  their distinct pinned roles --- two separate premises, neither folded
  into the other:

  \<^item> @{text authority_effect_blind} stays WHOLLY PROSE (a hypothesis of no
    theorem here): the source authority's schema stores business facts,
    never emission-attempt counters, so emission multiplicity is
    image-invisible.  Its machine-checked SHADOWS in the landed corpus:
    the wrapper schema itself (no core field sees the ledger),
    @{thm [source] effect_unsafe_not_core_function}, and the
    store-measured dilemma (T2.10,
    @{thm [source] recovery_information_dilemma}) --- the store cannot
    arbitrate multiplicity.

  \<^item> @{const strictly_ascending_source} is FORMAL (landed in the Dilemma
    theory): real WALs have strictly increasing coordinates, so payload
    identity never aliases distinct business facts and payload-level
    dedup is exact.  It formalizes its OWN pinned dedup-exactness role;
    it appears as an explicit hypothesis EXACTLY where the layer-2
    instance-exactness direction and the B1-derived positive theorem
    consume it (the premise table below), and nowhere else.

  NAME DISCIPLINE: the formal name is @{text exactly_once_at} ---
  frontier-relative; the bare phrase "exactly-once" is never a formal
  name, and prose citing this theory must keep the qualifier.
\<close>

definition at_least_once_at :: "frontier \<Rightarrow> ('k, 'v) dwe_state \<Rightarrow> bool" where
  "at_least_once_at f t \<longleftrightarrow>
     set (replay_down_hist (exec_src_hist (dwe_core t))
            (exec_scope (dwe_core t)) f)
       \<subseteq> e_payload ` set (dwe_emitted t)"

text \<open>The definitional bridge: delivery completeness IS the complement of
  the landed loss predicate (pinned @{typ "(nat, nat) dwe_state"} because
  @{const lost_effect} is; the definition above is polymorphic).\<close>

lemma at_least_once_iff_not_lost:
  "at_least_once_at f t \<longleftrightarrow> \<not> lost_effect f t"
  by (auto simp: at_least_once_at_def lost_effect_def)

definition exactly_once_at :: "frontier \<Rightarrow> ('k, 'v) dwe_state \<Rightarrow> bool" where
  "exactly_once_at f t \<longleftrightarrow> \<not> effect_unsafe t \<and> at_least_once_at f t"

text \<open>
  Vacuity corner, disclosed (C-4): when the scoped replay at @{term f} is
  empty --- e.g. at the init state --- @{const at_least_once_at} holds
  vacuously and @{const exactly_once_at} reduces to the safety conjunct.
  The frontier-relative reading covers this in substance; the lemma makes
  the corner checkable.
\<close>

lemma exactly_once_at_empty_replay:
  assumes "replay_down_hist (exec_src_hist (dwe_core t))
             (exec_scope (dwe_core t)) f = []"
  shows "exactly_once_at f t \<longleftrightarrow> \<not> effect_unsafe t"
  using assms by (simp add: exactly_once_at_def at_least_once_at_def)

text \<open>
  THE DEDUP SINK, operator face: the idempotent consumer's
  EXECUTED-effect stream is a payload-deduplicated view of the delivery
  stream.  Duplicate-freedom of the executed stream holds BY CONSTRUCTION
  (@{text sink_dedup_view_distinct} below) --- that is what "idempotent
  sink" means here.  The occurrence/order choice @{const remdups} makes is
  irrelevant: only set membership and distinctness are consumed below ---
  disclosed, not exploited.  The POLICY face of the same sink is the
  landed @{const sink_delta} (sink-side payload filtering at recovery),
  consumed in the positive theorem below.
\<close>

definition sink_dedup_view
  :: "('k, 'v) dwe_state \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list"
where
  "sink_dedup_view t = remdups (map e_payload (dwe_emitted t))"

text \<open>Local counting helper --- HOL's @{const count_list} library is
  intentionally minimal and has no distinct-implies-count-one lemma
  (verified against the installed sources); this helper is load-bearing
  for the count form and both iff layers.\<close>

lemma count_list_distinct_mem:
  "distinct xs \<Longrightarrow> count_list xs x = (if x \<in> set xs then 1 else 0)"
  by (induction xs) auto

lemma sink_dedup_view_distinct: "distinct (sink_dedup_view t)"
  by (simp add: sink_dedup_view_def)

lemma sink_dedup_view_set:
  "set (sink_dedup_view t) = e_payload ` set (dwe_emitted t)"
  by (simp add: sink_dedup_view_def)

lemma sink_dedup_view_count:
  "count_list (sink_dedup_view t) p
     = (if p \<in> e_payload ` set (dwe_emitted t) then 1 else 0)"
  by (simp add: count_list_distinct_mem[OF sink_dedup_view_distinct]
                sink_dedup_view_set)


section \<open>The count-form reading of the exactly-once predicate\<close>

text \<open>
  The COUNT FORM --- the honest count-level reading: each scoped committed
  obligation at @{term f} delivered exactly once, every emission justified
  at its fire-time stamp, no payload ever delivered twice anywhere.  The
  liveness claim is relativized to the scoped prefix at @{term f}; the
  safety claim stays global.
\<close>

theorem exactly_once_count_form:
  "exactly_once_at f t \<longleftrightarrow>
     (\<forall>x \<in> set (dwe_emitted t).
        justified_at (exec_src_hist (dwe_core t)) x)
   \<and> distinct (map e_payload (dwe_emitted t))
   \<and> (\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                   (exec_scope (dwe_core t)) f).
        count_list (map e_payload (dwe_emitted t)) p = 1)"
proof
  assume eo: "exactly_once_at f t"
  then have safe: "\<not> effect_unsafe t" and alo: "at_least_once_at f t"
    by (simp_all add: exactly_once_at_def)
  have just: "\<forall>x \<in> set (dwe_emitted t).
                justified_at (exec_src_hist (dwe_core t)) x"
    and dist: "distinct (map e_payload (dwe_emitted t))"
    using safe by (auto simp: effect_safe_alt)
  have cnt: "\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                         (exec_scope (dwe_core t)) f).
               count_list (map e_payload (dwe_emitted t)) p = 1"
  proof
    fix p
    assume "p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                       (exec_scope (dwe_core t)) f)"
    then have "p \<in> e_payload ` set (dwe_emitted t)"
      using alo by (auto simp: at_least_once_at_def)
    then have "p \<in> set (map e_payload (dwe_emitted t))" by simp
    then show "count_list (map e_payload (dwe_emitted t)) p = 1"
      by (simp add: count_list_distinct_mem[OF dist])
  qed
  show "(\<forall>x \<in> set (dwe_emitted t).
           justified_at (exec_src_hist (dwe_core t)) x)
      \<and> distinct (map e_payload (dwe_emitted t))
      \<and> (\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                      (exec_scope (dwe_core t)) f).
           count_list (map e_payload (dwe_emitted t)) p = 1)"
    using just dist cnt by blast
next
  assume rhs:
    "(\<forall>x \<in> set (dwe_emitted t).
        justified_at (exec_src_hist (dwe_core t)) x)
   \<and> distinct (map e_payload (dwe_emitted t))
   \<and> (\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                   (exec_scope (dwe_core t)) f).
        count_list (map e_payload (dwe_emitted t)) p = 1)"
  then have just: "\<forall>x \<in> set (dwe_emitted t).
                     justified_at (exec_src_hist (dwe_core t)) x"
    and dist: "distinct (map e_payload (dwe_emitted t))"
    and cnt: "\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                          (exec_scope (dwe_core t)) f).
                count_list (map e_payload (dwe_emitted t)) p = 1"
    by blast+
  have safe: "\<not> effect_unsafe t"
    using just dist by (simp add: effect_safe_alt)
  have alo: "at_least_once_at f t"
    unfolding at_least_once_at_def
  proof
    fix p
    assume p: "p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                          (exec_scope (dwe_core t)) f)"
    have "count_list (map e_payload (dwe_emitted t)) p = 1"
      using cnt p by blast
    then have "count_list (map e_payload (dwe_emitted t)) p \<noteq> 0" by simp
    then have "p \<in> set (map e_payload (dwe_emitted t))"
      using count_list_0_iff[of "map e_payload (dwe_emitted t)" p] by simp
    then show "p \<in> e_payload ` set (dwe_emitted t)" by simp
  qed
  show "exactly_once_at f t"
    using safe alo by (simp add: exactly_once_at_def)
qed


section \<open>LAYER 1: the premise-free dedup-sink iff (the T2.11 kernel)\<close>

text \<open>
  THE IFF IN TWO DISCLOSED LAYERS --- the payload/instance distinction:

  \<^item> LAYER 1 (payload-level, PREMISE-FREE): with a dedup sink, the
    per-obligation executed count is 1 IFF delivery was at-least-once.
    Pure counting; true for every state.

  \<^item> LAYER 2 (instance-level): executed counts agree with
    COMMITTED-INSTANCE counts iff at-least-once.  The direction
    "at-least-once implies instance agreement" consumes
    @{const strictly_ascending_source} (under equal-coordinate aliasing
    one payload stands for two committed business instances, and every
    payload-dedup view executes it once); the converse direction is
    premise-free.  The aliasing control below shows the premise is
    load-bearing at a machine-reachable state.

  WHICH PREMISE WHERE (exact):

  \<^item> layer-1 iff, both directions: none
  \<^item> layer-2 iff, agreement implies at-least-once: none
  \<^item> layer-2 iff, at-least-once implies agreement:
    @{const strictly_ascending_source}
  \<^item> the positive theorem (the sink delta achieves exactly-once from a
    crashed state): exactly the landed B1 premises --- effect-safe pre +
    crashed + frontier within finish + @{const strictly_ascending_source}
  \<^item> the necessity face (no store-measured recovery is exactly-once):
    none (a concrete pair defeats every such policy)
\<close>

theorem dedup_sink_exactly_once_iff_at_least_once:
  "(\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                 (exec_scope (dwe_core t)) f).
      count_list (sink_dedup_view t) p = 1)
   \<longleftrightarrow> at_least_once_at f t"
  by (auto simp: sink_dedup_view_count at_least_once_at_def subset_iff)

text \<open>
  Reading: the idempotent consumer executes each scoped committed
  obligation exactly once IFF the delivery stream was at-least-once ---
  the folklore "exactly-once = at-least-once + idempotence" as a machine
  iff, at the payload level, with NO premise.  Duplicate-freedom of the
  executed stream is by construction
  (@{thm [source] sink_dedup_view_distinct}); the ONLY question a dedup
  sink leaves open is coverage, and coverage IS at-least-once.  The
  theorem is definitional at the view layer: with duplicate-freedom
  held by construction, the displayed iff reduces to that coverage
  reading, and its "exactly once" is the payload-counted verdict on the
  absorbing deduplicated view, NOT the machine predicate
  @{const exactly_once_at}.  The substantive per-instance form under an
  ascending source is the later @{text dedup_sink_instance_exact_iff}.
\<close>


section \<open>LAYER 2: instance-level exactness under the named premise\<close>

text \<open>Under the ascending premise the scoped obligation list is distinct
  --- the @{text dist_R} step inside the landed B1 proof, named as a
  reusable fact (the replay is a filter of the committed prefix).\<close>

lemma ascending_obligations_distinct:
  assumes "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "distinct (replay_down_hist (exec_src_hist (dwe_core t))
                     (exec_scope (dwe_core t)) f)"
  using strictly_ascending_distinct[OF assms]
  unfolding replay_down_hist_def by simp

text \<open>The premise-free direction: agreement at every scoped obligation
  already forces coverage (a member's own count is nonzero).\<close>

lemma instance_agreement_gives_at_least_once:
  assumes agree:
    "\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                  (exec_scope (dwe_core t)) f).
       count_list (sink_dedup_view t) p
         = count_list (replay_down_hist (exec_src_hist (dwe_core t))
                         (exec_scope (dwe_core t)) f) p"
  shows "at_least_once_at f t"
  unfolding at_least_once_at_def
proof
  fix p
  assume p: "p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                        (exec_scope (dwe_core t)) f)"
  have "count_list (replay_down_hist (exec_src_hist (dwe_core t))
                      (exec_scope (dwe_core t)) f) p \<noteq> 0"
    using p by (simp add: count_list_0_iff)
  then have "count_list (sink_dedup_view t) p \<noteq> 0"
    using agree p by simp
  then show "p \<in> e_payload ` set (dwe_emitted t)"
    by (simp add: sink_dedup_view_count split: if_split_asm)
qed

theorem dedup_sink_instance_exact_iff:
  assumes asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "(\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                       (exec_scope (dwe_core t)) f).
            count_list (sink_dedup_view t) p
              = count_list (replay_down_hist (exec_src_hist (dwe_core t))
                              (exec_scope (dwe_core t)) f) p)
       \<longleftrightarrow> at_least_once_at f t"
proof
  let ?R = "replay_down_hist (exec_src_hist (dwe_core t))
              (exec_scope (dwe_core t)) f"
  assume "\<forall>p \<in> set ?R.
            count_list (sink_dedup_view t) p = count_list ?R p"
  then show "at_least_once_at f t"
    by (rule instance_agreement_gives_at_least_once)
next
  let ?R = "replay_down_hist (exec_src_hist (dwe_core t))
              (exec_scope (dwe_core t)) f"
  assume alo: "at_least_once_at f t"
  show "\<forall>p \<in> set ?R.
          count_list (sink_dedup_view t) p = count_list ?R p"
  proof
    fix p
    assume p: "p \<in> set ?R"
    have obl: "count_list ?R p = 1"
      using ascending_obligations_distinct[OF asc] p
      by (simp add: count_list_distinct_mem)
    have "p \<in> e_payload ` set (dwe_emitted t)"
      using alo p by (auto simp: at_least_once_at_def)
    then have "count_list (sink_dedup_view t) p = 1"
      by (simp add: sink_dedup_view_count)
    with obl show "count_list (sink_dedup_view t) p = count_list ?R p"
      by simp
  qed
qed

subsection \<open>The aliasing control: layer 2's premise is load-bearing\<close>

text \<open>
  THE ALIASING CONTROL, at the banked equal-coordinate chain reached by
  the machine itself (WF-H1's guard is non-strict, so the equal-coordinate
  re-commit is admissible): at @{const dd4_w} the payload
  @{term "(ec1, e1)"} aliases TWO committed business instances.  The state
  is at-least-once --- so the payload-level layer-1 iff still holds there
  --- but every payload-dedup view executes the payload ONCE while its
  committed-instance count is TWO: instance exactness is off by one.
  Exactly the boundary @{const strictly_ascending_source} names, in its
  own pinned dedup-exactness role.
\<close>

text \<open>Reachability, derived locally (the Discipline theory lands the
  temporal trace but names no reachability lemma for @{const dd4_w}).\<close>

lemma reach_dd4: "dwe_reachable dd4_w"
  unfolding dwe_reachable_def using dd_trace_init by blast

lemma dd4_not_asc:
  "\<not> strictly_ascending_source (exec_src_hist (dwe_core dd4_w))"
  by (simp add: strictly_ascending_source_def dd4_w_def mkT_def mkC_def)

lemma dd4_at_least_once: "at_least_once_at ec1 dd4_w"
  by (simp add: at_least_once_at_def dd4_w_def mkT_def mkC_def
                replay_down_hist_def e1_def ec_defs eval_nat_numeral)

lemma dd4_replay_count:
  "count_list (replay_down_hist (exec_src_hist (dwe_core dd4_w))
                 (exec_scope (dwe_core dd4_w)) ec1) (ec1, e1) = 2"
  by (simp add: dd4_w_def mkT_def mkC_def replay_down_hist_def e1_def ec_defs
                eval_nat_numeral)

lemma dd4_view_count: "count_list (sink_dedup_view dd4_w) (ec1, e1) = 1"
  by (simp add: sink_dedup_view_def dd4_w_def mkT_def e1_def ec_defs)

theorem aliasing_defeats_instance_exactness:
  "dwe_reachable dd4_w
 \<and> \<not> strictly_ascending_source (exec_src_hist (dwe_core dd4_w))
 \<and> at_least_once_at ec1 dd4_w
 \<and> count_list (replay_down_hist (exec_src_hist (dwe_core dd4_w))
                  (exec_scope (dwe_core dd4_w)) ec1) (ec1, e1) = 2
 \<and> count_list (sink_dedup_view dd4_w) (ec1, e1) = 1"
  by (intro conjI reach_dd4 dd4_not_asc dd4_at_least_once dd4_replay_count
        dd4_view_count)


section \<open>The cursor connection: at-least-once IS a covered cursor\<close>

text \<open>
  If everything before the cursor position @{term m} is already in the
  ledger --- the pre-ledger covers the take-@{term m} prefix of the replay
  --- the re-drive is at-least-once at its own frontier.  The positional
  "@{term m} at or below the delivered position" reading is the special
  case where the pre-ledger is exactly a replay prefix.
\<close>

text \<open>Local projection, two lines.  (The Converse re-landing branch
  carries an identical fact, but that branch is not an ancestor of this
  theory --- the import DAG here is Dilemma + Discipline only; a distinct
  name keeps the session free of duplicate fact names.)\<close>

lemma emitting_reconcile_scope_unchanged:
  assumes "emitting_reconcile m t f t'"
  shows "exec_scope (dwe_core t') = exec_scope (dwe_core t)"
  using assms by (simp add: emitting_reconcile_def)

theorem cursor_within_delivered_at_least_once:
  assumes rec: "emitting_reconcile m t f t'"
      and covered: "set (take m (replay_down_hist (exec_src_hist (dwe_core t))
                                   (exec_scope (dwe_core t)) f))
                      \<subseteq> e_payload ` set (dwe_emitted t)"
  shows "at_least_once_at f t'"
proof -
  define R where "R = replay_down_hist (exec_src_hist (dwe_core t))
                        (exec_scope (dwe_core t)) f"
  have em': "dwe_emitted t' = dwe_emitted t
               @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                                dwe_epoch t, c, e)) (drop m R)"
    using emitting_reconcile_emitted[OF rec] by (simp add: R_def)
  have img': "e_payload ` set (dwe_emitted t')
              = e_payload ` set (dwe_emitted t) \<union> set (drop m R)"
    by (simp add: em' image_Un image_image)
  have src': "exec_src_hist (dwe_core t') = exec_src_hist (dwe_core t)"
    by (rule emitting_reconcile_src_same[OF rec])
  have scope': "exec_scope (dwe_core t') = exec_scope (dwe_core t)"
    by (rule emitting_reconcile_scope_unchanged[OF rec])
  have split: "set R = set (take m R) \<union> set (drop m R)"
    by (metis append_take_drop_id set_append)
  have "set R \<subseteq> e_payload ` set (dwe_emitted t) \<union> set (drop m R)"
    using split covered by (auto simp: R_def)
  then have "set R \<subseteq> e_payload ` set (dwe_emitted t')"
    using img' by simp
  then show ?thesis
    by (simp add: at_least_once_at_def src' scope' R_def)
qed

subsection \<open>The skip control: the liveness conjunct bites\<close>

text \<open>
  The banked skip twin, as the cursor-beyond-delivered control AND the
  liveness-conjunct-bites control in one: the m = 2 cursor reconcile from
  the banked loaded window emits nothing, stays effect-SAFE, yet the
  committed second effect never reaches the ledger --- effect-safe but not
  @{const exactly_once_at}.  The delivery-completeness conjunct is not
  decorative; what silent skipping costs is measured HERE, not by
  @{const effect_unsafe}.
\<close>

lemma t_mid_take2_not_covered:
  "\<not> (set (take 2 (replay_down_hist (exec_src_hist (dwe_core t_mid_w))
                     (exec_scope (dwe_core t_mid_w)) ec2))
        \<subseteq> e_payload ` set (dwe_emitted t_mid_w))"
proof -
  have inr: "(ec2, e2) \<in> set (take 2 (replay_down_hist
                (exec_src_hist (dwe_core t_mid_w))
                (exec_scope (dwe_core t_mid_w)) ec2))"
    by (simp add: t_mid_w_def mkT_def mkC_def replay_down_hist_def
                  e1_def e2_def ec_defs eval_nat_numeral)
  have notin: "(ec2, e2) \<notin> e_payload ` set (dwe_emitted t_mid_w)"
    by (simp add: t_mid_w_def mkT_def e1_def e2_def ec_defs)
  from inr notin show ?thesis by blast
qed

lemma t_skip_not_unsafe: "\<not> effect_unsafe t_skip_w"
  by (simp add: effect_unsafe_def premature_def duplicate_def justified_at_def
                t_skip_w_def mkT_def mkC_def e1_def e2_def ec_defs
                eval_nat_numeral)

lemma t_skip_not_at_least_once: "\<not> at_least_once_at ec2 t_skip_w"
proof -
  have inrep: "(ec2, e2) \<in> set (replay_down_hist
                  (exec_src_hist (dwe_core t_skip_w))
                  (exec_scope (dwe_core t_skip_w)) ec2)"
    by (simp add: t_skip_w_def mkT_def mkC_def replay_down_hist_def
                  e1_def e2_def ec_defs eval_nat_numeral)
  have notin: "(ec2, e2) \<notin> e_payload ` set (dwe_emitted t_skip_w)"
    by (simp add: t_skip_w_def mkT_def e1_def e2_def ec_defs)
  show ?thesis
    unfolding at_least_once_at_def using inrep notin by blast
qed

lemma t_skip_not_exactly_once: "\<not> exactly_once_at ec2 t_skip_w"
  using t_skip_not_at_least_once by (simp add: exactly_once_at_def)

theorem cursor_beyond_delivered_loses:
  "emitting_reconcile 2 t_mid_w ec2 t_skip_w
 \<and> \<not> (set (take 2 (replay_down_hist (exec_src_hist (dwe_core t_mid_w))
                      (exec_scope (dwe_core t_mid_w)) ec2))
        \<subseteq> e_payload ` set (dwe_emitted t_mid_w))
 \<and> \<not> effect_unsafe t_skip_w
 \<and> \<not> at_least_once_at ec2 t_skip_w
 \<and> \<not> exactly_once_at ec2 t_skip_w"
  by (intro conjI rec_skip t_mid_take2_not_covered t_skip_not_unsafe
        t_skip_not_at_least_once t_skip_not_exactly_once)


section \<open>Witness corners: both conjuncts independently load-bearing\<close>

text \<open>Positive inhabitation at reachable states --- including INSIDE the
  dilemma pair (@{const d1_w}): the exactly-once predicate is not exotic.\<close>

lemma t_safe_at_least_once: "at_least_once_at ec2 t_safe_w"
  by (simp add: at_least_once_at_def t_safe_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs eval_nat_numeral)

lemma t_safe_exactly_once: "exactly_once_at ec2 t_safe_w"
  by (simp add: exactly_once_at_def t_safe_not_unsafe t_safe_at_least_once)

lemma d1_at_least_once: "at_least_once_at ec2 d1_w"
  by (simp add: at_least_once_at_def d1_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs eval_nat_numeral)

lemma d1_exactly_once: "exactly_once_at ec2 d1_w"
  by (simp add: exactly_once_at_def d1_not_unsafe d1_at_least_once)

theorem exactly_once_inhabited:
  "dwe_reachable t_safe_w \<and> exactly_once_at ec2 t_safe_w
 \<and> dwe_reachable d1_w \<and> exactly_once_at ec2 d1_w"
  by (intro conjI reach_t_safe t_safe_exactly_once reach_d1 d1_exactly_once)

text \<open>The safety conjunct bites: the banked stale-cursor duplicate is
  at-least-once (its ledger covers the replay) yet not exactly-once.
  Together with @{thm [source] cursor_beyond_delivered_loses}: the two
  conjuncts are independently falsifiable at reachable states --- neither
  is decorative.\<close>

lemma t_fin_at_least_once: "at_least_once_at ec2 t_fin_w"
  by (simp add: at_least_once_at_def t_fin_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs eval_nat_numeral)

theorem duplicate_defeats_exactly_once:
  "at_least_once_at ec2 t_fin_w
 \<and> effect_unsafe t_fin_w
 \<and> \<not> exactly_once_at ec2 t_fin_w"
  using t_fin_at_least_once t_fin_unsafe by (simp add: exactly_once_at_def)


section \<open>The positive side: the sink-reading policy achieves exactly-once\<close>

text \<open>
  THE POSITIVE SIDE.  The premises are EXACTLY the landed B1 premises of
  @{thm [source] sink_reading_escape_general} --- none added, none
  dropped; the proof is the landed theorem plus the two definitional
  bridges.  The delivery-completeness conjunct of the conclusion is the
  @{const lost_effect} complement (the bridge above), so its liveness
  status is exactly the landed one: a terminal-state stand-in for
  delivery liveness, disclosed --- not a temporal claim.
\<close>

theorem sink_delta_achieves_exactly_once:
  assumes safe: "\<not> effect_unsafe t"
      and crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and fin: "f \<le> exec_finish (dwe_core t)"
      and asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "(\<exists>t'. policy_redrive (sink_delta f) t f t')
       \<and> (\<forall>t'. policy_redrive (sink_delta f) t f t' \<longrightarrow>
            (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k)
          \<and> exactly_once_at f t')"
proof -
  have gen: "(\<exists>t'. policy_redrive (sink_delta f) t f t')
       \<and> (\<forall>t'. policy_redrive (sink_delta f) t f t' \<longrightarrow>
            (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k)
          \<and> \<not> effect_unsafe t'
          \<and> \<not> lost_effect f t')"
    by (rule sink_reading_escape_general[OF safe crashed fin asc])
  show ?thesis
  proof (rule conjI)
    show "\<exists>t'. policy_redrive (sink_delta f) t f t'"
      using gen by blast
  next
    show "\<forall>t'. policy_redrive (sink_delta f) t f t' \<longrightarrow>
            (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k)
          \<and> exactly_once_at f t'"
    proof (intro allI impI)
      fix t'
      assume pr: "policy_redrive (sink_delta f) t f t'"
      have heal: "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k"
        and s: "\<not> effect_unsafe t'"
        and l: "\<not> lost_effect f t'"
        using gen pr by blast+
      have "exactly_once_at f t'"
        using s l
        by (simp add: exactly_once_at_def at_least_once_iff_not_lost)
      with heal show "(\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f)
                             f k)
                    \<and> exactly_once_at f t'"
        by blast
    qed
  qed
qed

subsection \<open>Inhabitation at the dilemma's own loss-side witness\<close>

text \<open>
  At @{const d2_w} --- reached by the machine itself --- the sink-reading
  delta coincides with the m = 1 cursor rule: the sink tells the recovery
  the right cursor, and the redrive result is a machine reconcile.  On
  generality: @{const sink_delta} is NOT in general a contiguous
  @{term "drop m"} cursor suffix (deliveries need not form a replay
  prefix); at this witness it is --- disclosed, not generalized.
\<close>

lemma d2_crashed: "\<exists>c. exec_status (dwe_core d2_w) = Crashed c"
  by (simp add: d2_fields)

lemma d2_fin: "ec2 \<le> exec_finish (dwe_core d2_w)"
  by (simp add: d2_fields)

lemma sink_delta_d2_is_cursor_suffix:
  "sink_delta ec2 d2_w
     = drop 1 (replay_down_hist (exec_src_hist (dwe_core d2_w))
                 (exec_scope (dwe_core d2_w)) ec2)"
  by (simp add: sink_delta_def d2_w_def mkT_def mkC_def replay_down_hist_def
                e1_def e2_def ec_defs eval_nat_numeral)

lemma rec_d2_delta:
  "emitting_reconcile 1 d2_w ec2 (redrive_result (sink_delta ec2) d2_w ec2)"
  by (simp add: emitting_reconcile_def redrive_result_def sink_delta_def
                d2_w_def mkT_def mkC_def replay_down_hist_def
                e1_def e2_def ec_defs eval_nat_numeral)

lemma reach_d2_delta:
  "dwe_reachable (redrive_result (sink_delta ec2) d2_w ec2)"
  by (rule dwe_reachable_reconcile_ext[OF reach_d2 rec_d2_delta])

lemma d2_delta_exactly_once:
  "exactly_once_at ec2 (redrive_result (sink_delta ec2) d2_w ec2)"
proof -
  have pr: "policy_redrive (sink_delta ec2) d2_w ec2
              (redrive_result (sink_delta ec2) d2_w ec2)"
    by (rule policy_redriveI[OF d2_crashed d2_fin])
  show ?thesis
    using sink_delta_achieves_exactly_once
            [OF d2_not_unsafe d2_crashed d2_fin d2_asc] pr
    by blast
qed

theorem sink_delta_restores_exactly_once_at_d2:
  "sink_delta ec2 d2_w
     = drop 1 (replay_down_hist (exec_src_hist (dwe_core d2_w))
                 (exec_scope (dwe_core d2_w)) ec2)
 \<and> emitting_reconcile 1 d2_w ec2 (redrive_result (sink_delta ec2) d2_w ec2)
 \<and> dwe_reachable (redrive_result (sink_delta ec2) d2_w ec2)
 \<and> exactly_once_at ec2 (redrive_result (sink_delta ec2) d2_w ec2)"
  by (intro conjI sink_delta_d2_is_cursor_suffix rec_d2_delta reach_d2_delta
        d2_delta_exactly_once)


section \<open>The necessity face: the dilemma in exactly-once vocabulary\<close>

text \<open>
  THE NECESSITY FACE, translated --- not re-proved: the landed
  @{thm [source] recovery_information_dilemma} horn
  @{term "effect_unsafe t1' \<or> lost_effect ec2 t2'"} maps through the
  definitional bridge to the negated exactly-once conjunction --- the
  unsafe disjunct kills the safety conjunct on one member, the loss
  disjunct kills delivery completeness on the other.  Together with the
  positive theorem above and the landed
  @{thm [source] sink_reading_escape_not_store_measured}: exactly-once
  effect recovery EXISTS and REQUIRES reading the sink.  T2.11 is the
  exactly-once READING of the landed T2.10, not a new impossibility.
\<close>

theorem no_store_measured_exactly_once_recovery:
  "\<forall>P. store_measured P \<longrightarrow>
     (\<exists>t1 t2 t1' t2'.
        dwe_reachable t1 \<and> dwe_reachable t2
      \<and> dwe_core t1 = dwe_core t2
      \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
      \<and> policy_redrive P t1 ec2 t1'
      \<and> policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
      \<and> \<not> (exactly_once_at ec2 t1' \<and> exactly_once_at ec2 t2'))"
proof (intro allI impI)
  fix P :: redrive_policy
  assume sm: "store_measured P"
  obtain t1 t2 t1' t2' where
    r1: "dwe_reachable t1" and r2: "dwe_reachable t2"
    and ceq: "dwe_core t1 = dwe_core t2"
    and s1: "\<not> effect_unsafe t1" and s2: "\<not> effect_unsafe t2"
    and pr1: "policy_redrive P t1 ec2 t1'"
    and pr2: "policy_redrive P t2 ec2 t2'"
    and h1: "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k"
    and h2: "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k"
    and horn: "effect_unsafe t1' \<or> lost_effect ec2 t2'"
    using recovery_information_dilemma sm by blast
  have neo: "\<not> (exactly_once_at ec2 t1' \<and> exactly_once_at ec2 t2')"
    using horn
    by (auto simp: exactly_once_at_def at_least_once_iff_not_lost)
  show "\<exists>t1 t2 t1' t2'.
        dwe_reachable t1 \<and> dwe_reachable t2
      \<and> dwe_core t1 = dwe_core t2
      \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
      \<and> policy_redrive P t1 ec2 t1'
      \<and> policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
      \<and> \<not> (exactly_once_at ec2 t1' \<and> exactly_once_at ec2 t2')"
    using r1 r2 ceq s1 s2 pr1 pr2 h1 h2 neo by blast
qed

text \<open>GAP-2 continuity: the same translation over the landed epoch
  extension --- policies reading a persisted recovery-generation counter
  in addition to the store are covered by the same pair.\<close>

corollary no_store_epoch_measured_exactly_once_recovery:
  "\<forall>P. store_epoch_measured P \<longrightarrow>
     (\<exists>t1 t2 t1' t2'.
        dwe_reachable t1 \<and> dwe_reachable t2
      \<and> dwe_core t1 = dwe_core t2
      \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
      \<and> policy_redrive P t1 ec2 t1'
      \<and> policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
      \<and> \<not> (exactly_once_at ec2 t1' \<and> exactly_once_at ec2 t2'))"
proof (intro allI impI)
  fix P :: redrive_policy
  assume sem: "store_epoch_measured P"
  obtain t1 t2 t1' t2' where
    r1: "dwe_reachable t1" and r2: "dwe_reachable t2"
    and ceq: "dwe_core t1 = dwe_core t2"
    and s1: "\<not> effect_unsafe t1" and s2: "\<not> effect_unsafe t2"
    and pr1: "policy_redrive P t1 ec2 t1'"
    and pr2: "policy_redrive P t2 ec2 t2'"
    and h1: "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k"
    and h2: "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k"
    and horn: "effect_unsafe t1' \<or> lost_effect ec2 t2'"
    using epoch_measured_dilemma sem by blast
  have neo: "\<not> (exactly_once_at ec2 t1' \<and> exactly_once_at ec2 t2')"
    using horn
    by (auto simp: exactly_once_at_def at_least_once_iff_not_lost)
  show "\<exists>t1 t2 t1' t2'.
        dwe_reachable t1 \<and> dwe_reachable t2
      \<and> dwe_core t1 = dwe_core t2
      \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
      \<and> policy_redrive P t1 ec2 t1'
      \<and> policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
      \<and> \<not> (exactly_once_at ec2 t1' \<and> exactly_once_at ec2 t2')"
    using r1 r2 ceq s1 s2 pr1 pr2 h1 h2 neo by blast
qed


section \<open>The guard bridge: one ladder from T2.8 through T2.11\<close>

text \<open>
  Under the ascending premise the escape policy's batch always satisfies
  the discipline's reconcile-suffix guard --- the two conjuncts stated
  inline here are literally the @{const disciplined_trace} reconcile
  guard (and the T2.9 theory names the same pair
  @{text reconcile_suffix_ok}).  The positive discipline (T2.8), the
  suffix-freshness law (T2.9), the dilemma (T2.10), and the exactly-once
  reading (T2.11) are one story.
\<close>

lemma sink_delta_batch_fresh_distinct:
  assumes asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "distinct (sink_delta f t)
       \<and> set (sink_delta f t) \<inter> e_payload ` set (dwe_emitted t) = {}"
proof
  have dist_R: "distinct (replay_down_hist (exec_src_hist (dwe_core t))
                            (exec_scope (dwe_core t)) f)"
    by (rule ascending_obligations_distinct[OF asc])
  then show "distinct (sink_delta f t)"
    by (simp add: sink_delta_def)
  show "set (sink_delta f t) \<inter> e_payload ` set (dwe_emitted t) = {}"
    by (auto simp: sink_delta_def)
qed

end
