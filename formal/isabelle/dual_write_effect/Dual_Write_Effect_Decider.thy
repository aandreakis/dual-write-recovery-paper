(*  Title:       Dual_Write_Effect_Decider.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    T2.12: the TWO-TIER EXECUTABLE POINT EVALUATOR --- the "Programs" leg
    of the effect tier, mirroring the landed store-tier decider
    (Dual_Write_Core.Dual_Write_Decider) on the promoted cyclic machine.

    WHAT THIS THEORY IS (the honest scope).  A certified, executable POINT
    EVALUATOR for the two-tier verdict of a concrete (nat, nat)-instantiable
    cyclic effect state: given a wrapper state t, a frontier f and a key k,
    one total function computes (store tier) whether the durable core
    exhibits an observable crash mismatch at (f, k) --- the exact predicate
    the landed Dual_Write_Decider decides for schedules --- and (effect
    tier) whether the emission ledger carries a premature or duplicate
    emission.  It is proved to agree with the declarative predicates,
    evaluated on the banked witness states by oracle-free kernel evaluation
    (code_simp), and exported to Standard ML.  It is NOT a model checker:
    it answers "is THIS given state bad", never "is a bad state reachable"
    --- no reachability decision, no trace enumeration, no search.  And it
    is deliberately NOT a schedule-level executor (gate ruling D-S5-2): the
    landed tier-1 decider owns the schedule-level story (state_of_labels /
    schedule_bad_crash_at); on the effect tier, SCHEDULES are governed by
    the for-all discipline theorem (general_positive_discipline constrains
    disciplined action lists), while this theory answers point questions
    about given STATES.

    HONESTY NOTE (fence-critical).  The landed store-tier decider bridged
    a REAL gap: relational trace semantics to a total executable fold,
    with a proved agreement.  On the effect tier THERE IS NO SUCH GAP TO
    SELL: premature, duplicate, effect_unsafe and justified_at were
    DESIGNED as state-computable list/quantifier formulas (that design is
    the fire-time-stamp defence of T1).  The per-hazard correctness iffs
    below are INTERFACE CERTIFICATES --- a bounded quantifier re-expressed
    as a list program (list_ex / distinct) plus the kernel-evaluated
    verdicts and the SML export; the effect-side gap closed here is
    bounded-quantifier-to-list-program, NOT relational-to-executable ---
    and they are advertised as nothing more.  The genuinely NEW
    mathematical content of this theory is exactly three items:

    1. the TWO-TIER PAIRING as one function with a two-sided fate theorem
       ("a positive store verdict is one banked reconcile away from a
       clean store at its frontier; a positive effect verdict never clears
       again") --- the slogan in verdict form;

    2. the stamps_bounded-premised TRACE-LEVEL persistence theorem on the
       cyclic machine --- the premise-general form of the
       reachability-premised effect_unsafe_trace_monotone banked in the
       S4d wave (Dual_Write_Effect_Segment_Boundaries, not an ancestor of
       this theory, so the fact is unavailable here and the general form
       is proved directly from the single-step effect_unsafe_monotone);
       the NAME effect_unsafe_trace_persistent otherwise exists only on
       the terminal machine;

    3. the decider-level boundary certificates: the store component of the
       verdict factors through dwe_core BY CONSTRUCTION, while the effect
       component provably CANNOT (computed on two banked equal-core
       pairs, one per hazard axis) --- the G1 separation restated as a
       fact about deciders, presented as designed-in, never discovered.

    IMPORTS (each earns its place).  The cyclic branch only: Dilemma
    (banked dilemma pair d1_w/d2_w, t_skip_w, lost_effect --- consumed
    FORMALLY by the skip-asymmetry control) and Discipline (rf5_w, the
    only banked Running-time duplicate, for per-hazard discrimination),
    both converging on Dual_Write_Effect_Cyclic; plus the locked-session
    decider theory Dual_Write_Core.Dual_Write_Decider, the SINGLE home of
    the src_coord code setup (equal instance, code_datatype coord_of_nat,
    the coordinate code lemmas) --- inherited here, never re-instantiated
    --- and of observable_mismatch's certified executability.  The
    terminal branch (Dual_Write_Effect_Machine / _Witnesses) is
    deliberately NOT imported: it defines same-named hazard constants
    (justified_at, premature, duplicate, effect_unsafe, e_payload, ...)
    and importing it alongside the cyclic branch would make every
    unqualified hazard name ambiguous.  The terminal T2.7 pair is cited in
    text below, never evaluated here.
*)

theory Dual_Write_Effect_Decider
  imports
    Dual_Write_Effect_Dilemma
    Dual_Write_Effect_Discipline
    "Dual_Write_Core.Dual_Write_Decider"
begin

section \<open>The per-hazard executable deciders\<close>

text \<open>
  Each hazard predicate of the cyclic machine is already a bounded
  list/quantifier formula over the given state; the deciders below
  re-express the bounded quantifiers as list programs.  The per-emission
  evaluator first: fire-time justification against the stamped committed
  prefix, as a @{const list_ex} program.
\<close>

definition justified_at_decider
  :: "('k, 'v) src_history \<Rightarrow> ('k, 'v) emission \<Rightarrow> bool"
where
  "justified_at_decider S x \<longleftrightarrow>
     e_stamp x \<le> length S
   \<and> list_ex (\<lambda>p. p = e_payload x) (take (e_stamp x) S)"

definition dwe_premature_decider :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "dwe_premature_decider t \<longleftrightarrow>
     list_ex (\<lambda>x. \<not> justified_at_decider (exec_src_hist (dwe_core t)) x)
       (dwe_emitted t)"

text \<open>@{const duplicate} is ALREADY a list program; the decider body below
  is verbatim the declarative predicate --- there is no gap here and none
  is claimed.\<close>

definition dwe_duplicate_decider :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "dwe_duplicate_decider t \<longleftrightarrow> \<not> distinct (map e_payload (dwe_emitted t))"

text \<open>@{const phantom} is taxonomy-only on the machine (non-monotone; it
  absorbs into @{const premature}, @{thm [source] phantom_imp_premature}).
  Its decider exists to build the stamp-blind rival below and for taxonomy
  evaluation only --- the same disclaimer the machine theory carries.\<close>

definition dwe_phantom_decider :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "dwe_phantom_decider t \<longleftrightarrow>
     list_ex (\<lambda>x. \<not> list_ex (\<lambda>p. p = e_payload x)
                     (exec_src_hist (dwe_core t)))
       (dwe_emitted t)"

definition dwe_effect_unsafe_decider :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "dwe_effect_unsafe_decider t \<longleftrightarrow>
     dwe_premature_decider t \<or> dwe_duplicate_decider t"

text \<open>The STAMP-BLIND RIVAL (negative-control apparatus, not part of the
  verdict): the plausible-but-wrong evaluator that judges emissions against
  the FINAL committed history (phantom) instead of the fire-time stamped
  prefix --- exactly the T1 image-collapse trap, now as a rival decider.
  The controls below prove it sound but counterexample-incomplete.\<close>

definition image_taxonomy_decider :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "image_taxonomy_decider t \<longleftrightarrow>
     dwe_phantom_decider t \<or> dwe_duplicate_decider t"

subsection \<open>Interface certificates: the per-hazard correctness iffs\<close>

lemma justified_at_decider_correct [simp]:
  "justified_at_decider S x \<longleftrightarrow> justified_at S x"
  by (simp add: justified_at_decider_def justified_at_def list_ex_iff)

theorem dwe_premature_decider_correct:
  "dwe_premature_decider t \<longleftrightarrow> premature t"
  by (simp add: dwe_premature_decider_def premature_def list_ex_iff)

theorem dwe_duplicate_decider_correct:
  "dwe_duplicate_decider t \<longleftrightarrow> duplicate t"
  by (simp add: dwe_duplicate_decider_def duplicate_def)

theorem dwe_phantom_decider_correct:
  "dwe_phantom_decider t \<longleftrightarrow> phantom t"
  by (simp add: dwe_phantom_decider_def phantom_def list_ex_iff)

theorem dwe_effect_unsafe_decider_correct:
  "dwe_effect_unsafe_decider t \<longleftrightarrow> effect_unsafe t"
  by (simp add: dwe_effect_unsafe_decider_def effect_unsafe_def
                dwe_premature_decider_correct dwe_duplicate_decider_correct)


section \<open>The two-tier verdict function and the corner classifier\<close>

definition dwe_two_tier_verdict
  :: "('k, 'v) dwe_state \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> bool \<times> bool"
where
  "dwe_two_tier_verdict t f k =
     (observable_mismatch (dwe_core t) f k, dwe_effect_unsafe_decider t)"

datatype tier_verdict = TT_clean | TT_store | TT_effect | TT_both

definition dwe_classify
  :: "('k, 'v) dwe_state \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> tier_verdict"
where
  "dwe_classify t f k =
     (case dwe_two_tier_verdict t f k of
        (False, False) \<Rightarrow> TT_clean  | (True,  False) \<Rightarrow> TT_store
      | (False, True)  \<Rightarrow> TT_effect | (True,  True)  \<Rightarrow> TT_both)"

text \<open>
  The store component reads ONLY @{term "dwe_core t"} --- it is the landed
  @{const observable_mismatch} verbatim, reused and never cloned (that IS
  the two-tier split at type level); the effect component reads ONLY
  @{term "dwe_emitted t"} and @{term "exec_src_hist (dwe_core t)"}.  Three
  scope disclosures, all load-bearing:

  (a) The store verdict is POINTED at (f, k) --- the landed decider's
  signature --- while the four-corner gate's @{const P_img} statements
  quantify over ALL keys.  The corner evaluations below reproduce the four
  corners at the witnessed key 1; the universal corner statements remain
  @{thm [source] four_corner_independence}'s.

  (b) SKIP ASYMMETRY carries verbatim: verdict (False, False) means "no
  scoped store mismatch at (f, k) and no emission fired early or twice" ---
  NOT exactly-once.  @{const effect_unsafe} cannot see never-emitted
  deliveries; delivery completeness is a liveness axis this verdict
  disowns, and the control @{text skip_asymmetry_verdict_control} below
  makes the disowned axis COMPUTED-VISIBLE (a clean effect verdict on a
  reachable state that provably lost a committed effect).

  (c) The decider takes the sink's emission ledger as INPUT; by the named
  prose premise @{text authority_effect_blind} (the source authority's
  schema stores business facts, never emission-attempt counters) no
  store-derived input could replace it.  The formal surrogate for that
  schema claim is the boundary-certificate pair below (the effect verdict
  computed differently on two banked equal-core reachable pairs); the
  schema claim itself stays named prose --- it is about real-world
  schemas, not about this model.
\<close>

theorem dwe_two_tier_verdict_correct:
  "dwe_two_tier_verdict t f k =
     (observable_mismatch (dwe_core t) f k, effect_unsafe t)"
  by (simp add: dwe_two_tier_verdict_def dwe_effect_unsafe_decider_correct)

text \<open>The @{text fst} component equals @{const observable_mismatch} BY
  CONSTRUCTION (reuse of the landed predicate --- the honest mirror of
  "@{const dwe_core} feeds the landed decider"); the certified content of
  the equation above is the effect component's iff.\<close>

theorem dwe_classify_correct:
  "dwe_classify t f k =
     (if observable_mismatch (dwe_core t) f k
      then if effect_unsafe t then TT_both else TT_store
      else if effect_unsafe t then TT_effect else TT_clean)"
  unfolding dwe_classify_def dwe_two_tier_verdict_correct
  by (cases "observable_mismatch (dwe_core t) f k";
      cases "effect_unsafe t") simp_all


section \<open>Store-side fate: sound, and one banked reconcile from clean\<close>

theorem two_tier_store_verdict_sound:
  assumes "fst (dwe_two_tier_verdict t f k)"
  shows "diverges (proto_of_exec_at (dwe_core t) f) f"
proof -
  have "observable_mismatch (dwe_core t) f k"
    using assms by (simp add: dwe_two_tier_verdict_def)
  then show ?thesis by (rule observable_mismatch_imp_diverges)
qed

text \<open>
  A positive store verdict is one banked reconcile away from a clean
  store at its frontier.  MANDATORY honesty note on the conjuncts: the
  THIRD conjunct (the verdict clears everywhere) holds for the TRIVIAL
  status reason --- a Recovered state cannot exhibit an observable crash
  mismatch at any (f', k') --- while the SECOND conjunct (every scoped
  mismatch at the frontier is healed) is the content, cited through
  @{thm [source] emitting_reconcile_heals} into the landed relay heal
  theorems.  Both are stated so the verdict-clearing cannot be mistaken
  for the heal theorem.
\<close>

theorem store_verdict_one_reconcile_from_clean:
  assumes "fst (dwe_two_tier_verdict t f k)"
  shows "\<exists>t'. emitting_reconcile 0 t f t'
            \<and> (\<forall>k'. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k')
            \<and> (\<forall>f' k'. \<not> fst (dwe_two_tier_verdict t' f' k'))"
proof -
  have om: "observable_mismatch (dwe_core t) f k"
    using assms by (simp add: dwe_two_tier_verdict_def)
  have crashed: "exec_status (dwe_core t) = Crashed f"
    and fin: "f \<le> exec_finish (dwe_core t)"
    using om by (simp_all add: observable_mismatch_def)
  define t' where "t' = t\<lparr>dwe_core := (dwe_core t)
       \<lparr>exec_down_hist :=
          replay_down_hist (exec_src_hist (dwe_core t))
            (exec_scope (dwe_core t)) f,
        exec_pending := {},
        exec_status := Recovered\<rparr>,
     dwe_emitted := dwe_emitted t
       @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                        dwe_epoch t, c, e))
           (drop 0 (replay_down_hist (exec_src_hist (dwe_core t))
                      (exec_scope (dwe_core t)) f))\<rparr>"
  have rec: "emitting_reconcile 0 t f t'"
    unfolding emitting_reconcile_def t'_def
    using crashed fin by simp
  have heal: "\<forall>k'. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k'"
    by (rule emitting_reconcile_heals[OF rec])
  have status': "exec_status (dwe_core t') = Recovered"
    by (simp add: t'_def)
  have clear: "\<forall>f' k'. \<not> fst (dwe_two_tier_verdict t' f' k')"
    by (simp add: dwe_two_tier_verdict_def observable_mismatch_def status')
  show ?thesis using rec heal clear by blast
qed


section \<open>Effect-side fate: trace-level persistence and verdict permanence\<close>

text \<open>
  Trace-level persistence on the cyclic machine at the @{text stamps_bounded}
  premise: the premise-general sibling of the reachability-premised
  @{text effect_unsafe_trace_monotone} banked in
  @{text Dual_Write_Effect_Segment_Boundaries} (a ROOT-sibling outside this
  theory's import cone, so the general form is proved directly), and the
  cyclic analogue of the terminal machine's
  @{text effect_unsafe_trace_persistent} (same name, different machine ---
  the corpus already reuses hazard names across the two machine theories);
  it is proved here because the verdict-permanence corollary consumes it.
  The cyclic theory banks the single-step @{thm [source]
  effect_unsafe_monotone}; the induction below threads the stamps-bounded
  invariant through all four trace cases, mirroring @{thm [source]
  dwe_trace_stamps_bounded}.  The @{const stamps_bounded} premise is
  LOAD-BEARING, not decorative: the unconditional form is false (an
  over-stamped alien emission could become justified when the source later
  commits --- the machine theory's own disclosure), and the premise holds
  at every reachable state (@{thm [source] dwe_reachable_stamps_bounded}).
\<close>

theorem effect_unsafe_trace_persistent:
  assumes "dwe_temporal_trace t acts t'"
      and "stamps_bounded t"
      and "effect_unsafe t"
  shows "effect_unsafe t'"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  then show ?case by simp
next
  case (dwe_label_step t a t' as t'')
  have sb': "stamps_bounded t'"
    by (rule dwe_step_stamps_bounded[OF dwe_label_step.hyps(3)
          dwe_label_step.prems(1)])
  have un': "effect_unsafe t'"
    by (rule effect_unsafe_monotone[OF dwe_label_step.prems(1)
          dwe_label_step.prems(2) disjI1[OF dwe_label_step.hyps(3)]])
  show ?case by (rule dwe_label_step.IH[OF sb' un'])
next
  case (dwe_reconcile_step m t f t' as t'')
  have sb': "stamps_bounded t'"
    by (rule emitting_reconcile_stamps_bounded[OF dwe_reconcile_step.hyps(1)
          dwe_reconcile_step.prems(1)])
  have un': "effect_unsafe t'"
    by (rule effect_unsafe_monotone[OF dwe_reconcile_step.prems(1)
          dwe_reconcile_step.prems(2)
          disjI2[OF disjI1[OF dwe_reconcile_step.hyps(1)]]])
  show ?case by (rule dwe_reconcile_step.IH[OF sb' un'])
next
  case (dwe_resume_step t t' as t'')
  have sb': "stamps_bounded t'"
    by (rule dwe_resume_stamps_bounded[OF dwe_resume_step.hyps(1)
          dwe_resume_step.prems(1)])
  have un': "effect_unsafe t'"
    by (rule effect_unsafe_monotone[OF dwe_resume_step.prems(1)
          dwe_resume_step.prems(2)
          disjI2[OF disjI2[OF dwe_resume_step.hyps(1)]]])
  show ?case by (rule dwe_resume_step.IH[OF sb' un'])
qed

text \<open>Verdict permanence, (nat, nat)-monomorphic via the machine's pinned
  @{const dwe_reachable}.  The @{text snd} component is frontier- and
  key-independent BY CONSTRUCTION, so the generality in f' and k' below is
  definitional --- said so here, claimed as nothing more.\<close>

corollary effect_verdict_permanent:
  assumes reach: "dwe_reachable t"
      and pos: "snd (dwe_two_tier_verdict t f k)"
      and tr: "dwe_temporal_trace t acts t'"
  shows "snd (dwe_two_tier_verdict t' f' k')"
proof -
  have sb: "stamps_bounded t"
    by (rule dwe_reachable_stamps_bounded[OF reach])
  have un: "effect_unsafe t"
    using pos
    by (simp add: dwe_two_tier_verdict_def dwe_effect_unsafe_decider_correct)
  have "effect_unsafe t'"
    by (rule effect_unsafe_trace_persistent[OF tr sb un])
  then show ?thesis
    by (simp add: dwe_two_tier_verdict_def dwe_effect_unsafe_decider_correct)
qed


section \<open>Witness scaffolding: the decider-level core-invisible premature pair\<close>

text \<open>
  @{text tb2_w} below is the banked @{const t_bad_w} after one
  @{term "DoSource ec1 e1"} step: the premature stamp-0 publish whose
  payload the source commits LATER.  Its durable core is LITERALLY
  @{const W3}'s core (both are the one-committed / one-delivered Running
  window); the emission ledgers differ ONLY in the STAMP --- (0, 0, ec1, e1)
  here against W3's (1, 0, ec1, e1) --- so fire-time information alone
  flips the verdict.  This is the cyclic, decider-level restatement of the
  landed TERMINAL machine's core-invisible premature pair (the T2.7 pair of
  @{text Dual_Write_Effect_Witnesses}: two reorderings of one three-step window
  with equal final cores and opposite verdicts) --- restated with disclosed
  scope on the promoted machine; the terminal original stays the terminal
  branch's and is not evaluated here.
\<close>

definition tb2_w :: "(nat, nat) dwe_state" where
  "tb2_w = mkT (mkC [(ec1, e1)] [(ec1, e1)] [(ec1, e1)] {} Running)
               [(0, 0, ec1, e1)] 0"

lemma wf_t_bad: "wellformed_exec_state (dwe_core t_bad_w)"
  by (simp add: t_bad_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e1)

lemma g_t_bad_src1:
  "exec_label_preserves_history_wf (dwe_core t_bad_w) (DoSource ec1 e1)"
  by (simp add: t_bad_w_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma ws_tb2: "dwe_step t_bad_w (DoSource ec1 e1) tb2_w"
proof -
  have c: "dw_exec_step (dwe_core t_bad_w) (DoSource ec1 e1) (dwe_core tb2_w)"
    by (rule do_sourceI) (simp_all add: t_bad_w_def tb2_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: t_bad_w_def tb2_w_def mkT_def)
qed

lemma reach_tb2: "dwe_reachable tb2_w"
  by (rule dwe_reachable_label_ext[OF reach_t_bad wf_t_bad g_t_bad_src1 ws_tb2])

lemma tb2_cores_eq: "dwe_core tb2_w = dwe_core W3"
  by (simp add: tb2_w_def W3_def mkT_def)


section \<open>The two-tier asymmetry package and the boundary certificates\<close>

text \<open>
  THE SLOGAN IN VERDICT FORM --- a RESTATEMENT of banked facts, never new
  depth: the first conjunct packages the one-reconcile-from-clean fate of
  a positive store verdict (the landed heal, through
  @{thm [source] emitting_reconcile_heals}); the second packages the
  trace-level permanence of a positive effect verdict.  The store verdict
  heals; the effect verdict does not.  Both conjuncts are stated at the
  pinned (nat, nat) witness type so they share one statement (the facts
  they cite hold at the generality of the theorems above).
\<close>

theorem two_tier_verdict_asymmetry:
  "(\<forall>t :: (nat, nat) dwe_state. \<forall>f k.
        fst (dwe_two_tier_verdict t f k)
      \<longrightarrow> (\<exists>t'. emitting_reconcile 0 t f t'
              \<and> (\<forall>k'. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k')))
 \<and> (\<forall>t acts t' f k f' k'.
        dwe_reachable t \<longrightarrow> snd (dwe_two_tier_verdict t f k)
      \<longrightarrow> dwe_temporal_trace t acts t'
      \<longrightarrow> snd (dwe_two_tier_verdict t' f' k'))"
proof (intro conjI allI impI)
  fix t :: "(nat, nat) dwe_state" and f :: frontier and k :: nat
  assume "fst (dwe_two_tier_verdict t f k)"
  from store_verdict_one_reconcile_from_clean[OF this]
  obtain t' where "emitting_reconcile 0 t f t'"
    and "\<forall>k'. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k'"
    by blast
  then show "\<exists>t'. emitting_reconcile 0 t f t'
              \<and> (\<forall>k'. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k')"
    by blast
next
  fix t :: "(nat, nat) dwe_state" and acts :: "(nat, nat) dwe_action list"
    and t' :: "(nat, nat) dwe_state" and f :: frontier and k :: nat
    and f' :: frontier and k' :: nat
  assume "dwe_reachable t"
     and "snd (dwe_two_tier_verdict t f k)"
     and "dwe_temporal_trace t acts t'"
  then show "snd (dwe_two_tier_verdict t' f' k')"
    by (rule effect_verdict_permanent)
qed

text \<open>Boundary certificate, positive half: the store component factors
  through the core BY CONSTRUCTION --- presented as designed, the foil to
  the negative half below.\<close>

theorem store_component_core_measured:
  assumes "dwe_core t = dwe_core t'"
  shows "fst (dwe_two_tier_verdict t f k) = fst (dwe_two_tier_verdict t' f k)"
  by (simp add: dwe_two_tier_verdict_def assms)

text \<open>Boundary certificate, negative half: the effect component provably
  CANNOT factor through the core --- the G1 duplicate separation restated
  at decider level, on the banked g1 pair (equal cores, cursor 0 vs 1).\<close>

theorem effect_decider_not_core_computable:
  "\<not> (\<exists>g. \<forall>t. dwe_reachable t
              \<longrightarrow> dwe_effect_unsafe_decider t = g (dwe_core t))"
proof
  assume "\<exists>g. \<forall>t. dwe_reachable t
              \<longrightarrow> dwe_effect_unsafe_decider t = g (dwe_core t)"
  then obtain g where g: "\<forall>t. dwe_reachable t
              \<longrightarrow> dwe_effect_unsafe_decider t = g (dwe_core t)"
    by blast
  have "g (dwe_core g1_unsafe_w)"
    using g reach_g1_unsafe g1u_unsafe
    by (simp add: dwe_effect_unsafe_decider_correct)
  moreover have "\<not> g (dwe_core g1_safe_w)"
    using g reach_g1_safe g1s_safe
    by (simp add: dwe_effect_unsafe_decider_correct)
  ultimately show False
    by (simp add: g1_cores_eq)
qed

text \<open>
  The PREMATURE-axis instance of the same boundary, via the new pair
  (@{const tb2_w}, @{const W3}): equal cores, opposite effect verdicts,
  both reachable --- so BOTH hazard axes witness the boundary at decider
  level, mirroring the role of the landed terminal T2.7 pair.  The last
  conjunct is the two-tier punchline: the store tier CANNOT break the tie
  on this pair at ANY (f, k); only the ledger-reading tier can --- and the
  two ledgers differ only in the STAMP, so fire-time information alone
  flips the verdict.
\<close>

lemma decider_tb2_unsafe: "dwe_effect_unsafe_decider tb2_w"
  by code_simp

lemma decider_W3_safe: "\<not> dwe_effect_unsafe_decider W3"
  by code_simp

lemma decider_premature_pair:
  "dwe_reachable tb2_w \<and> dwe_reachable W3
 \<and> dwe_core tb2_w = dwe_core W3
 \<and> dwe_effect_unsafe_decider tb2_w \<and> \<not> dwe_effect_unsafe_decider W3
 \<and> (\<forall>f k. fst (dwe_two_tier_verdict tb2_w f k)
            = fst (dwe_two_tier_verdict W3 f k))"
  by (intro conjI allI reach_tb2 reach_W3 tb2_cores_eq decider_tb2_unsafe
        decider_W3_safe store_component_core_measured[OF tb2_cores_eq])


section \<open>The witness evaluation battery (kernel evaluations)\<close>

text \<open>
  Every decider output value is witnessed at least once and all four
  @{type tier_verdict} constructors are hit, by ORACLE-FREE KERNEL
  EVALUATION (@{method code_simp}) on the banked witness states --- the
  landed decider's method, matched and not exceeded.  The states: the G2
  incident state @{const t_fin_w} (duplicate), the warm-cursor
  @{const t_safe_w}, the crashed loaded window @{const t_mid_w}, the
  fourth corner @{const t_corner4_w}, the Running-time refire duplicate
  @{const rf5_w} (duplicate WITHOUT premature), the stamp-0 publish
  @{const t_bad_w} (premature WITHOUT duplicate, and the phantom taxonomy
  witness), the two-epoch amplification state @{const f_amp_w} (epoch tags
  projected away correctly), and the new pair (@{const tb2_w},
  @{const W3}).
\<close>

lemma decider_t_fin_unsafe: "dwe_effect_unsafe_decider t_fin_w"
  by code_simp

lemma decider_t_safe_safe: "\<not> dwe_effect_unsafe_decider t_safe_w"
  by code_simp

lemma decider_rf5_duplicate_only:
  "dwe_duplicate_decider rf5_w \<and> \<not> dwe_premature_decider rf5_w"
  by code_simp

lemma decider_t_bad_premature_only:
  "dwe_premature_decider t_bad_w \<and> \<not> dwe_duplicate_decider t_bad_w"
  by code_simp

lemma decider_phantom_pair:
  "dwe_phantom_decider t_bad_w \<and> \<not> dwe_phantom_decider tb2_w"
  by code_simp

lemma decider_f_amp_unsafe: "dwe_effect_unsafe_decider f_amp_w"
  by code_simp

lemma decider_rival_true: "image_taxonomy_decider t_fin_w"
  by code_simp

text \<open>The dilemma pair, at verdict level: both members are effect-clean
  and their store components agree at EVERY (f, k) --- the pair is
  VERDICT-LEVEL INDISTINGUISHABLE.  This is exactly why the
  recovery-information dilemma needed BATCH-level separation (what a
  policy emits), not verdict-level separation: no point verdict on the
  pair can arbitrate the dilemma.\<close>

lemma decider_dilemma_pair:
  "\<not> dwe_effect_unsafe_decider d1_w \<and> \<not> dwe_effect_unsafe_decider d2_w"
  by code_simp

lemma dilemma_pair_verdict_indistinguishable:
  "fst (dwe_two_tier_verdict d1_w f k) = fst (dwe_two_tier_verdict d2_w f k)"
  by (rule store_component_core_measured[OF d_cores_eq])

text \<open>The four corners of the two-tier verdict, computed at the witnessed
  key 1 and the pinned frontier @{const ec2} --- the pointed, computed
  reproduction of the four-corner gate (disclosure (a) above).\<close>

lemma two_tier_four_corner_values:
  "dwe_two_tier_verdict t_safe_w    ec2 1 = (False, False)
 \<and> dwe_two_tier_verdict t_mid_w     ec2 1 = (True,  False)
 \<and> dwe_two_tier_verdict t_fin_w     ec2 1 = (False, True)
 \<and> dwe_two_tier_verdict t_corner4_w ec2 1 = (True,  True)"
  by code_simp

lemma classify_four_corners:
  "dwe_classify t_safe_w    ec2 1 = TT_clean
 \<and> dwe_classify t_mid_w     ec2 1 = TT_store
 \<and> dwe_classify t_fin_w     ec2 1 = TT_effect
 \<and> dwe_classify t_corner4_w ec2 1 = TT_both"
  by code_simp


section \<open>Negative controls: the biting pair\<close>

text \<open>
  THE CONTROL: the final-image rival PASSES a reachable, genuinely
  premature state --- @{const tb2_w}'s emission is stamped 0 against an
  empty committed prefix (premature), yet its payload IS in the final
  committed history (not phantom) and the ledger is duplicate-free.
  Fire-time stamping is load-bearing IN THE DECIDER, and the decider
  provably does not collapse into the image taxonomy.
\<close>

lemma decider_tb2_rival_clean: "\<not> image_taxonomy_decider tb2_w"
  by code_simp

lemma unsafe_tb2: "effect_unsafe tb2_w"
  using decider_tb2_unsafe by (simp add: dwe_effect_unsafe_decider_correct)

theorem stamp_blind_rival_unsound_control:
  "dwe_reachable tb2_w
 \<and> effect_unsafe tb2_w
 \<and> \<not> image_taxonomy_decider tb2_w"
  by (intro conjI reach_tb2 unsafe_tb2 decider_tb2_rival_clean)

text \<open>Directionality made explicit: the rival is SOUND but INCOMPLETE ---
  together with the control above this is a strict-containment
  certificate (phantom absorbs into premature; the converse fails at
  @{const tb2_w}).\<close>

lemma rival_one_way_absorption:
  assumes "image_taxonomy_decider t"
  shows "dwe_effect_unsafe_decider t"
proof -
  from assms have "phantom t \<or> duplicate t"
    by (simp add: image_taxonomy_decider_def dwe_phantom_decider_correct
                  dwe_duplicate_decider_correct)
  then have "effect_unsafe t"
    using phantom_imp_premature by (auto simp: effect_unsafe_def)
  then show ?thesis
    by (simp add: dwe_effect_unsafe_decider_correct)
qed

text \<open>
  THE FENCE WITNESS (disclosure (b) above, computed): a CLEAN effect
  verdict on a reachable state that provably LOST a committed effect ---
  @{const t_skip_w} is the m = 2 over-advanced-cursor skip: its ledger is
  justified and duplicate-free (effect-safe), yet the committed (ec2, e2)
  never appears in its emission payloads.  The disowned liveness axis,
  consuming the Dilemma's @{const lost_effect} formally.
\<close>

lemma decider_t_skip_safe: "\<not> dwe_effect_unsafe_decider t_skip_w"
  by code_simp

lemma lost_t_skip: "lost_effect ec2 t_skip_w"
  by (simp add: lost_effect_def t_skip_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs eval_nat_numeral)

theorem skip_asymmetry_verdict_control:
  "dwe_reachable t_skip_w
 \<and> \<not> dwe_effect_unsafe_decider t_skip_w
 \<and> lost_effect ec2 t_skip_w"
  by (intro conjI reach_t_skip decider_t_skip_safe lost_t_skip)


section \<open>Standard ML export (the executability capstone)\<close>

text \<open>The decider stack generates and type-checks as Standard ML ---
  @{command export_code} with @{text "checking SML"} plus the
  @{method code_simp} witness theorems above is exactly the landed
  decider's bar: matched, not exceeded (no file export, no eval or
  normalization oracles).\<close>

export_code
  justified_at_decider dwe_premature_decider dwe_duplicate_decider
  dwe_phantom_decider dwe_effect_unsafe_decider image_taxonomy_decider
  dwe_two_tier_verdict dwe_classify
  dwe_init mkT mkC tb2_w
  checking SML

end
