(*  Title:       Dual_Write_Effect_Suffix_Freshness.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    T2.9: RECONCILE-SUFFIX FRESHNESS on the cyclic effect machine,
    presented as DISCIPLINE SOUNDNESS plus NECESSITY AT A LOADED WINDOW.

    The landed discipline (Dual_Write_Effect_Discipline, T2.8) guards
    every emitting reconcile with two conjuncts: the re-driven suffix is
    internally payload-distinct and ledger-fresh.  This theory names that
    guard (reconcile_suffix_ok), re-surfaces the landed soundness lemma at
    its landed generality, and adds the converse as LIST BOOKKEEPING: a
    reconcile appends its suffix to an append-only ledger, so a
    duplicate-free result forces the appended suffix fresh and internally
    distinct by distinct_append unfolded through the stamp projection.
    The theorem carrying the T2.9 designation is the resulting conditional
    equivalence INSTANTIATED AT THE BANKED LOADED WINDOW t_mid_w
    (reachable, crashed mid-delivery, genuinely emitting, effect-safe);
    the general conditional form lands as a supporting theorem whose text
    self-describes as bookkeeping.  This theory deliberately makes NO
    characterization claim about effect safety.

    Controls: both sides of the window equivalence are inhabited by the
    banked safe reconcile; each guard conjunct is independently violated
    at a reachable window (the banked stale-cursor and equal-coordinate
    controls, recast in the named vocabulary); and a NEW reachable
    extension of the landed refire chain (rf6/rf7/rf8) witnesses the
    pre-safety hypothesis load-bearing: a guard-passing, genuinely
    re-driving reconcile from an unsafe crashed state stays unsafe.

    Statement audit (D-S5-1, gate-ruled): NEITHER direction of the
    equivalence consumes the prose premise strictly_ascending_source ---
    soundness is the landed discipline step lemma (no reachability, no
    ordering premise), necessity is list bookkeeping with no order
    content.  The theory is therefore asc-free; planting an unconsumed
    hypothesis would repeat the defect class the S1 audit removed from
    the escape theorem.  The premise's honest roles live in the
    Exactly_Once theory (T2.11, formal layer-2 consumption) and in the
    aliased-window prose remark next to the distinctness control below.

    The scratch original's in-source ML oracle gates are STRIPPED here:
    oracle-freedom is certified by scratch-side per-slice gate sessions
    with confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Suffix_Freshness
  imports Dual_Write_Effect_Discipline
begin

section \<open>The named reconcile-suffix guard\<close>

text \<open>
  T2.9 FRAMING (binding): suffix freshness is presented as discipline
  soundness plus necessity at a loaded window; the necessity direction is
  list bookkeeping (@{thm [source] distinct_append} through the stamp
  projection @{thm [source] map_e_payload_restamp}).  This theory
  deliberately makes NO characterization claim about effect safety: every
  statement below constrains ONE emitting reconcile step against the
  machine's own ledger, and the general equivalence is stated only
  conditionally on an effect-safe pre-state (witnessed load-bearing at
  the end of this theory).

  The definition names LITERALLY the reconcile guard of the landed
  @{const disciplined_trace} (its \<open>disciplined_reconcile\<close> case): the
  re-driven suffix --- the scoped, frontier-bounded replay of the
  committed source prefix from the persisted consumer cursor \<open>m\<close> --- is
  internally payload-distinct and disjoint from the payloads already on
  the emission ledger.  Type discipline: the guard is polymorphic,
  exactly as the discipline's rules are; only the window and control
  sections below pin \<open>(nat, nat)\<close> via the banked witnesses.
\<close>

definition reconcile_suffix_ok
  :: "nat \<Rightarrow> ('k, 'v) dwe_state \<Rightarrow> frontier \<Rightarrow> bool"
where
  "reconcile_suffix_ok m t f \<longleftrightarrow>
     distinct (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                         (exec_scope (dwe_core t)) f))
   \<and> set (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                    (exec_scope (dwe_core t)) f))
       \<inter> e_payload ` set (dwe_emitted t) = {}"

text \<open>Bridge lemma: the named guard provably coincides with the landed
  discipline's reconcile case --- a guard-satisfying reconcile step IS a
  one-step disciplined trace.\<close>

lemma reconcile_suffix_ok_discipline_guard:
  assumes rec: "emitting_reconcile m t f t'"
      and ok: "reconcile_suffix_ok m t f"
  shows "disciplined_trace t [DWE_Reconcile m f] t'"
proof -
  have dist: "distinct (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                                  (exec_scope (dwe_core t)) f))"
    and fresh: "set (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                               (exec_scope (dwe_core t)) f))
                  \<inter> e_payload ` set (dwe_emitted t) = {}"
    using ok unfolding reconcile_suffix_ok_def by blast+
  show ?thesis
    by (rule disciplined_reconcile_singleI[OF rec dist fresh])
qed


section \<open>(a) Soundness: the landed discipline step lemma re-surfaced\<close>

text \<open>
  The soundness half is the landed discipline step lemma
  @{thm [source] reconcile_preserves_effect_safe}, re-surfaced at its
  landed generality: polymorphic, no reachability hypothesis, no
  crash-status hypothesis beyond the reconcile rule's own guard, no
  source-ordering premise.  NOTHING NEW IS CLAIMED HERE --- this is a
  thin named citation, recorded so the T2.9 vocabulary provably meets
  the T2.8 proof.
\<close>

theorem reconcile_suffix_freshness_sound:
  assumes rec: "emitting_reconcile m t f t'"
      and ok: "reconcile_suffix_ok m t f"
      and pre: "\<not> effect_unsafe t"
  shows "\<not> effect_unsafe t'"
proof -
  have dist: "distinct (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                                  (exec_scope (dwe_core t)) f))"
    and fresh: "set (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                               (exec_scope (dwe_core t)) f))
                  \<inter> e_payload ` set (dwe_emitted t) = {}"
    using ok unfolding reconcile_suffix_ok_def by blast+
  show ?thesis
    by (rule reconcile_preserves_effect_safe[OF rec dist fresh pre])
qed


section \<open>(b) Necessity, general form: distinct\_append unfolded\<close>

text \<open>
  The necessity direction is BOOKKEEPING, and needs no pre-state
  hypothesis at all: the reconcile appends its re-driven suffix to the
  append-only ledger (@{thm [source] emitting_reconcile_emitted}), the
  stamp projection strips the (stamp, epoch) decoration
  (@{thm [source] map_e_payload_restamp}), and a duplicate-free RESULT
  ledger is a distinct concatenation --- @{thm [source] distinct_append}
  hands back both guard conjuncts.  The \<open>payload_eq\<close> step is a literal
  \<open>simp only:\<close> rewrite (the eager map fusion of the default simpset
  would defeat the double-map shape before
  @{thm [source] map_e_payload_restamp} can fire --- the S1-probe
  forensics recorded at the landed
  @{thm [source] reconcile_preserves_effect_safe}).
\<close>

lemma reconcile_safe_result_forces_suffix_ok:
  assumes rec: "emitting_reconcile m t f t'"
      and nodup: "\<not> duplicate t'"
  shows "reconcile_suffix_ok m t f"
proof -
  let ?S = "exec_src_hist (dwe_core t)"
  let ?R = "replay_down_hist ?S (exec_scope (dwe_core t)) f"
  let ?sfx = "drop m ?R"
  have emitted: "dwe_emitted t'
                 = dwe_emitted t
                     @ map (\<lambda>(c, e). (length ?S, dwe_epoch t, c, e)) ?sfx"
    by (rule emitting_reconcile_emitted[OF rec])
  have payload_eq: "map e_payload (dwe_emitted t')
                    = map e_payload (dwe_emitted t) @ ?sfx"
    by (simp only: emitted map_append map_e_payload_restamp)
  have dist_all: "distinct (map e_payload (dwe_emitted t) @ ?sfx)"
    using nodup by (simp only: duplicate_def not_not payload_eq)
  have dist_parts: "distinct (map e_payload (dwe_emitted t))
                  \<and> distinct ?sfx
                  \<and> set (map e_payload (dwe_emitted t)) \<inter> set ?sfx = {}"
    using dist_all by (simp only: distinct_append)
  have d_sfx: "distinct ?sfx"
    using dist_parts by blast
  have fresh0: "set (map e_payload (dwe_emitted t)) \<inter> set ?sfx = {}"
    using dist_parts by blast
  have fresh: "set ?sfx \<inter> e_payload ` set (dwe_emitted t) = {}"
    using fresh0 unfolding set_map by (simp add: Int_commute)
  show ?thesis
    unfolding reconcile_suffix_ok_def using d_sfx fresh by blast
qed

corollary reconcile_effect_safe_result_forces_suffix_ok:
  assumes rec: "emitting_reconcile m t f t'"
      and safe: "\<not> effect_unsafe t'"
  shows "reconcile_suffix_ok m t f"
proof -
  have "\<not> duplicate t'"
    using safe by (simp add: effect_unsafe_def)
  then show ?thesis
    by (rule reconcile_safe_result_forces_suffix_ok[OF rec])
qed


section \<open>(c) The general conditional equivalence (supporting theorem)\<close>

text \<open>
  This equivalence is DISCIPLINE SOUNDNESS plus a bookkeeping converse.
  The backward direction is the landed discipline step lemma.  The
  forward direction is @{thm [source] distinct_append} unfolded through
  the stamp projection: the reconcile appends its suffix to an
  append-only ledger, so a duplicate-free result forces the appended
  suffix fresh and internally distinct by list bookkeeping alone.
  Neither direction inspects reachability, the crash coordinate, or the
  source order; nothing here is a characterization of effect safety ---
  the statement constrains ONE reconcile step, conditional on an
  effect-safe pre-state (a load-bearing hypothesis, witnessed below by
  the rf7/rf8 control).  The T2.9 designation belongs to the
  loaded-window instantiation in the next section, not to this
  supporting form.
\<close>

theorem reconcile_effect_safe_iff_suffix_ok:
  assumes rec: "emitting_reconcile m t f t'"
      and pre: "\<not> effect_unsafe t"
  shows "\<not> effect_unsafe t' \<longleftrightarrow> reconcile_suffix_ok m t f"
proof
  assume "\<not> effect_unsafe t'"
  then show "reconcile_suffix_ok m t f"
    by (rule reconcile_effect_safe_result_forces_suffix_ok[OF rec])
next
  assume ok: "reconcile_suffix_ok m t f"
  show "\<not> effect_unsafe t'"
    by (rule reconcile_suffix_freshness_sound[OF rec ok pre])
qed


section \<open>(d) T2.9: necessity at the loaded window\<close>

text \<open>
  THE T2.9 THEOREM.  The banked loaded window @{const t_mid_w} ---
  reachable, crashed mid-delivery (event 2 committed and enqueued with
  its delivery still in flight), genuinely emitting, effect-safe ---
  and, at it, the equivalence for EVERY emitting reconcile: the result
  is effect-safe iff the re-driven suffix is ledger-fresh and internally
  payload-distinct.  The name says window: this is the conditional
  equivalence of the previous section instantiated at one banked
  reachable state, and it is the statement the freeze ladder and any
  prose cite as T2.9.

  SKIP DISCLOSURE (mandatory, carried with the headline): the empty
  suffix (a cursor \<open>m\<close> at or beyond the replay length) satisfies
  @{const reconcile_suffix_ok} vacuously and preserves effect safety
  while silently SKIPPING undelivered committed effects ---
  @{const effect_unsafe} cannot see never-emitted deliveries (the
  machine's disclosed liveness axis; see the skip-asymmetry block of
  \<open>Dual_Write_Effect_Cyclic\<close>).  What skipping costs is measured by the
  delivery-completeness component of the Exactly\_Once theory
  (\<open>Dual_Write_Effect_Exactly_Once\<close>, T2.11), not here.
\<close>

theorem freshness_necessity_at_loaded_window:
  "dwe_reachable t_mid_w
 \<and> exec_status (dwe_core t_mid_w) = Crashed ec2
 \<and> genuinely_emitting t_mid_w
 \<and> \<not> effect_unsafe t_mid_w
 \<and> (\<forall>m f t'. emitting_reconcile m t_mid_w f t' \<longrightarrow>
      (\<not> effect_unsafe t' \<longleftrightarrow> reconcile_suffix_ok m t_mid_w f))"
proof -
  have status: "exec_status (dwe_core t_mid_w) = Crashed ec2"
    by (simp add: t_mid_w_def mkT_def mkC_def)
  have emitting: "genuinely_emitting t_mid_w"
    by (simp add: genuinely_emitting_def t_mid_w_def mkT_def)
  have quant: "\<forall>m f t'. emitting_reconcile m t_mid_w f t' \<longrightarrow>
                 (\<not> effect_unsafe t' \<longleftrightarrow> reconcile_suffix_ok m t_mid_w f)"
  proof (intro allI impI)
    fix m f t'
    assume "emitting_reconcile m t_mid_w f t'"
    then show "\<not> effect_unsafe t' \<longleftrightarrow> reconcile_suffix_ok m t_mid_w f"
      by (rule reconcile_effect_safe_iff_suffix_ok[OF _ t_mid_not_unsafe])
  qed
  show ?thesis
    by (intro conjI reach_t_mid status emitting t_mid_not_unsafe quant)
qed


section \<open>Non-vacuity and per-conjunct violation controls at the window\<close>

text \<open>Both sides of the window equivalence are inhabited by the banked
  safe reconcile: the warm-cursor re-drive (m = 1) passes the named
  guard and its result is effect-safe.\<close>

theorem window_iff_nonvacuous:
  "emitting_reconcile 1 t_mid_w ec2 t_safe_w
 \<and> reconcile_suffix_ok 1 t_mid_w ec2
 \<and> \<not> effect_unsafe t_safe_w"
proof -
  have ok: "reconcile_suffix_ok 1 t_mid_w ec2"
    unfolding reconcile_suffix_ok_def
    using dv_suffix_distinct dv_suffix_fresh by blast
  show ?thesis
    by (intro conjI rec_safe ok t_safe_not_unsafe)
qed

text \<open>The FRESHNESS conjunct violated in the named vocabulary: the banked
  stale-cursor reconcile (m = 0) from the same window re-drives a suffix
  that is internally DISTINCT yet not ledger-fresh --- the guard fails on
  its freshness conjunct alone, and the result is unsafe.  The heavy
  content stays cited from the landed control
  @{thm [source] reconcile_freshness_guard_load_bearing}.\<close>

corollary window_freshness_violation:
  "emitting_reconcile 0 t_mid_w ec2 t_fin_w
 \<and> distinct (drop 0 (replay_down_hist (exec_src_hist (dwe_core t_mid_w))
                       (exec_scope (dwe_core t_mid_w)) ec2))
 \<and> \<not> reconcile_suffix_ok 0 t_mid_w ec2
 \<and> effect_unsafe t_fin_w"
proof -
  have not_ok: "\<not> reconcile_suffix_ok 0 t_mid_w ec2"
  proof
    assume "reconcile_suffix_ok 0 t_mid_w ec2"
    then have "set (drop 0 (replay_down_hist (exec_src_hist (dwe_core t_mid_w))
                              (exec_scope (dwe_core t_mid_w)) ec2))
                 \<inter> e_payload ` set (dwe_emitted t_mid_w) = {}"
      unfolding reconcile_suffix_ok_def by blast
    with tfin_suffix_not_fresh_c show False by blast
  qed
  show ?thesis
    by (intro conjI rec_fin tfin_suffix_distinct_c not_ok t_fin_unsafe)
qed

text \<open>
  The DISTINCTNESS conjunct violated in the named vocabulary: the banked
  equal-coordinate chain (@{const dd3_w}, reached by the machine) offers
  a suffix that is ledger-FRESH yet internally duplicated --- the guard
  fails on its distinctness conjunct alone, and the result is unsafe.
  The heavy content stays cited from the landed control
  @{thm [source] reconcile_distinctness_guard_load_bearing}.

  ALIASING REMARK (prose, mandatory): this second window is the ALIASED
  window --- an equal-coordinate re-commit admitted by WF-H1's non-strict
  guard, the in-model shadow of dropping the prose premise
  @{text strictly_ascending_source}.  At an aliased window every
  guard-passing re-drive under-emits relative to business-instance
  counts; @{text strictly_ascending_source} restores instance
  faithfulness --- consumed FORMALLY in the Exactly\_Once theory
  (\<open>Dual_Write_Effect_Exactly_Once\<close>, layer-2 equivalence, with the
  aliasing control at @{const dd4_w}), and deliberately NOT a hypothesis
  here: it is consumed by neither direction of the equivalence above,
  and an unconsumed premise would repeat the defect the S1 audit removed
  from the escape theorem.
\<close>

corollary window_distinctness_violation:
  "emitting_reconcile 0 dd3_w ec1 dd4_w
 \<and> set (drop 0 (replay_down_hist (exec_src_hist (dwe_core dd3_w))
                  (exec_scope (dwe_core dd3_w)) ec1))
     \<inter> e_payload ` set (dwe_emitted dd3_w) = {}
 \<and> \<not> reconcile_suffix_ok 0 dd3_w ec1
 \<and> effect_unsafe dd4_w"
proof -
  have not_ok: "\<not> reconcile_suffix_ok 0 dd3_w ec1"
    unfolding reconcile_suffix_ok_def using dd_suffix_not_distinct by blast
  show ?thesis
    by (intro conjI rec_dd dd_suffix_fresh not_ok unsafe_dd4)
qed


section \<open>The pre-safety hypothesis is load-bearing (new refire extension)\<close>

text \<open>
  The conditional equivalence's pre-state hypothesis is not decorative.
  New witness states extend the landed refire chain (@{const rf5_w}, the
  Running duplicate with committed source \<open>[(ec1, e1)]\<close>): commit event 2
  (\<open>rf6_w\<close>), crash at @{const ec2} (\<open>rf7_w\<close>), then a
  GUARD-PASSING, GENUINELY EMITTING reconcile (m = 1, non-empty suffix
  \<open>[(ec2, e2)]\<close>, fresh and distinct) into \<open>rf8_w\<close> --- and the
  unsafe verdict persists: the suffix guard constrains what the
  reconcile ADDS, and the ledger it appends to cannot be un-written
  (@{thm [source] effect_unsafe_monotone}).
\<close>

definition rf6_w :: "(nat, nat) dwe_state" where
  "rf6_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec1, e1)]
                  [(ec1, e1), (ec1, e1)] {} Running)
               [(1, 0, ec1, e1), (1, 0, ec1, e1)] 0"

definition rf7_w :: "(nat, nat) dwe_state" where
  "rf7_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec1, e1)]
                  [(ec1, e1), (ec1, e1)] {} (Crashed ec2))
               [(1, 0, ec1, e1), (1, 0, ec1, e1)] 0"

definition rf8_w :: "(nat, nat) dwe_state" where
  "rf8_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)]
                  [(ec1, e1), (ec1, e1)] {} Recovered)
               [(1, 0, ec1, e1), (1, 0, ec1, e1), (2, 0, ec2, e2)] 0"

subsection \<open>Wellformedness and admissibility of the extension\<close>

lemma wf_rf5: "wellformed_exec_state (dwe_core rf5_w)"
  by (simp add: rf5_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e1
                wfh_e1_pair_eq)

lemma wf_rf6: "wellformed_exec_state (dwe_core rf6_w)"
  by (simp add: rf6_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_pair
                wfh_e1_pair_eq)

lemma g_rf5_src2:
  "exec_label_preserves_history_wf (dwe_core rf5_w) (DoSource ec2 e2)"
  by (simp add: rf5_w_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_rf6_crash:
  "exec_label_preserves_history_wf (dwe_core rf6_w) (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

subsection \<open>The extension steps and the guard-passing reconcile\<close>

lemma ws_rf6: "dwe_step rf5_w (DoSource ec2 e2) rf6_w"
proof -
  have c: "dw_exec_step (dwe_core rf5_w) (DoSource ec2 e2) (dwe_core rf6_w)"
    by (rule do_sourceI) (simp_all add: rf5_w_def rf6_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: rf5_w_def rf6_w_def mkT_def)
qed

lemma ws_rf7: "dwe_step rf6_w (Crash ec2) rf7_w"
proof -
  have c: "dw_exec_step (dwe_core rf6_w) (Crash ec2) (dwe_core rf7_w)"
    by (rule crashI) (simp_all add: rf6_w_def rf7_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: rf6_w_def rf7_w_def mkT_def)
qed

lemma rec_rf8: "emitting_reconcile 1 rf7_w ec2 rf8_w"
  by (simp add: emitting_reconcile_def rf7_w_def rf8_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs eval_nat_numeral)

subsection \<open>Reachability of the extension\<close>

lemma reach_rf5: "dwe_reachable rf5_w"
  using semi_disciplined_imp_temporal[OF semi_trace_init_rf5]
  unfolding dwe_reachable_def by blast

lemma reach_rf6: "dwe_reachable rf6_w"
  by (rule dwe_reachable_label_ext[OF reach_rf5 wf_rf5 g_rf5_src2 ws_rf6])

lemma reach_rf7: "dwe_reachable rf7_w"
  by (rule dwe_reachable_label_ext[OF reach_rf6 wf_rf6 g_rf6_crash ws_rf7])

lemma reach_rf8: "dwe_reachable rf8_w"
  by (rule dwe_reachable_reconcile_ext[OF reach_rf7 rec_rf8])

subsection \<open>Verdicts along the extension\<close>

lemma rf7_suffix_ok: "reconcile_suffix_ok 1 rf7_w ec2"
  unfolding reconcile_suffix_ok_def
  by (simp add: rf7_w_def mkT_def mkC_def replay_down_hist_def
                e1_def e2_def ec_defs eval_nat_numeral)

lemma rf7_suffix_nonempty:
  "drop 1 (replay_down_hist (exec_src_hist (dwe_core rf7_w))
             (exec_scope (dwe_core rf7_w)) ec2) \<noteq> []"
  by (simp add: rf7_w_def mkT_def mkC_def replay_down_hist_def
                e1_def e2_def ec_defs eval_nat_numeral)

lemma unsafe_rf7: "effect_unsafe rf7_w"
  by (simp add: effect_unsafe_def duplicate_def rf7_w_def mkT_def)

lemma unsafe_rf8: "effect_unsafe rf8_w"
  by (simp add: effect_unsafe_def duplicate_def rf8_w_def mkT_def)

text \<open>
  HEADLINE (pre-safety control).  A reachable, unsafe, crashed state
  admits a reconcile whose suffix passes the named guard and is
  NON-EMPTY (genuinely re-driving), yet the result stays unsafe: the
  suffix guard alone does not imply an effect-safe result --- the
  equivalence above genuinely needs its effect-safe pre-state.
\<close>

theorem pre_safety_premise_load_bearing:
  "dwe_reachable rf7_w
 \<and> emitting_reconcile 1 rf7_w ec2 rf8_w
 \<and> reconcile_suffix_ok 1 rf7_w ec2
 \<and> drop 1 (replay_down_hist (exec_src_hist (dwe_core rf7_w))
             (exec_scope (dwe_core rf7_w)) ec2) \<noteq> []
 \<and> effect_unsafe rf7_w
 \<and> effect_unsafe rf8_w"
  by (intro conjI reach_rf7 rec_rf8 rf7_suffix_ok rf7_suffix_nonempty
        unsafe_rf7 unsafe_rf8)

corollary suffix_ok_alone_insufficient:
  "\<not> (\<forall>m f t t'. emitting_reconcile m t f t' \<longrightarrow>
        reconcile_suffix_ok m t f \<longrightarrow>
        \<not> effect_unsafe (t' :: (nat, nat) dwe_state))"
  using pre_safety_premise_load_bearing by blast

end
