(*  Title:       Dual_Write_Effect_Sink_Delta_Convergence.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Retry-loop convergence, frontier robustness, and the certified
    executable form of the sink-reading delta (theory-backlog items I
    and J) --- an additive post-freeze slice under the freeze's own
    protocol: no landed statement, proof, definition, name, import, or
    session-DAG change to the frozen corpus.  This theory ITERATES and
    EXPORTS the landed section-18 lane
    (Dual_Write_Effect_Sink_Delta_Idempotence); it adds no machine, no
    rule, and no reachability claim.

    EVERY ROUND STATE IS A MODELED INTERMEDIATE.  The landed re-drive
    reconcile is an atomic big-step rule (disclosed model boundary:
    store heal and ledger append happen together), so a crash DURING a
    re-drive is inexpressible on the machine --- and this theory does
    NOT change that.  The rounds iterator below applies, purely at the
    FUNCTION level, the ledger footprint an interrupted sink-delta
    re-drive would leave (a stamped prefix of the currently computed
    batch, the landed section-18 shape), any number of times in
    sequence; the core is deliberately NEVER healed by a round, so the
    iterator models repeated crash-interrupted re-drives against a
    fixed committed source --- the referee's repeated-crash-during-
    redrive scenario --- not any sequence of machine transitions.
    Under the named strictly-ascending-source premise the recomputed
    delta after rounds with fired-prefix lengths ns is exactly the
    drop (sum_list ns) remainder of the original batch
    (partial_redrive_rounds_delta); the cumulative ledger footprint is
    exactly the take (sum_list ns) prefix, stamped once
    (partial_redrive_rounds_emitted); no payload is ever fired twice
    across the whole loop (partial_redrive_rounds_no_duplication);
    once the cumulative fired count reaches the batch length the
    recomputed delta is empty (partial_redrive_rounds_complete), and
    with per-round progress that happens within batch-length rounds
    (partial_redrive_rounds_effective_complete); and every round state
    is still effect-safe from an effect-safe start
    (partial_redrive_rounds_effect_safe).  "Convergence" everywhere
    below is exactly these function equations at modeled-intermediate
    states --- never a delivery, liveness, or scheduling claim.

    FRONTIER ROBUSTNESS (item I(b)) is a FUNCTION EQUATION about
    source appends: any state whose committed source history extends
    the original by entries with coordinates strictly beyond the
    frontier f --- scope and ledger unchanged --- computes the same
    sink_delta at f (sink_delta_source_append_beyond_frontier).  No
    ordering premise is consumed: the frontier-bounded replay simply
    never reads past f.  This says NOTHING about machine-level
    interleaving of source commits with re-drives: no small-step
    machine exists here, and the priced small-step reconcile design
    (the D design study) remains the machine-level contingency; the
    equation is cited for exactly what it is.

    THE EXPORT CAPSTONE (item J) makes the sink-reading escape's owed
    batch RUNNABLE: @{text export_code} generates and type-checks
    Standard ML for sink_delta, matching the landed decider capstone's
    bar exactly (checking SML; no file export, no eval or
    normalization oracles), with kernel-evaluated (@{method code_simp})
    witnesses.  sink_delta is a POINT FUNCTION from one state to the
    owed batch --- never a schedule executor, verifier, or model
    checker (gate ruling D-S5-2); its behavioral certificate is the
    landed section-18 remainder/completion laws plus the convergence
    laws above.

    VOCABULARY FENCES (binding, from the freeze documents):
    "retry-idempotence", "convergence", and "completion" are prose
    descriptions of function equations at modeled-intermediate states;
    no unqualified exactly-once claim is made or implied; the
    strictly-ascending-source premise (per-event unique coordinates,
    the CDC practitioner reading) is consumed load-bearing wherever
    batch distinctness is needed and is witnessed biting by the
    multi-round control at the end; the impossibility half of the
    landed corpus consumes NO ordering premise --- this theory sits
    entirely on the positive side.

    IMPORTS (each earns its place).  Dual_Write_Effect_Sink_Delta_
    Idempotence: the landed section-18 lane this theory iterates (its
    remainder law, completion corollaries, effect-safety theorem, and
    the psl_w control state are consumed directly); through it the
    cyclic branch (Dilemma / Cyclic).  Dual_Write_Core.Dual_Write_
    Decider: the locked-core session's decider theory, the SINGLE home
    of the src_coord code setup (equal instance, code_datatype
    coord_of_nat, the coordinate code lemmas) --- inherited here for
    the item-J export, never re-instantiated, exactly the landed
    effect-decider precedent.  The terminal branch (Dual_Write_Effect_
    Machine / _Witnesses) is deliberately NOT imported (namespace
    rule: the two branches share hazard names by design).

    PROVENANCE: theory-backlog second-wave items I and J
    (paper/dual_write/theory_backlog/BACKLOG_EXPLORATION.md section 6;
    both discovered by item C's landing).  Everything below is
    filter/take/drop/fold algebra over the landed definitions.

    In-source ML oracle gates are STRIPPED at landing: oracle-freedom
    is certified by scratch-side per-slice gate sessions with
    confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Sink_Delta_Convergence
  imports
    Dual_Write_Effect_Sink_Delta_Idempotence
    "Dual_Write_Core.Dual_Write_Decider"
begin

section \<open>The rounds iterator: repeated partial firing, core never healed\<close>

text \<open>
  One round with fired-prefix length @{term n}: append to the ledger the
  length-@{term n} prefix of the CURRENTLY computed batch, stamped
  exactly as the landed re-drive rule stamps (committed-prefix length
  and current epoch --- the @{thm [source] policy_redrive_emitted}
  footprint, so each round leaves precisely the ledger shape an
  interrupted sink-delta re-drive would leave under the landed
  stamping).  The frontier is FIXED across rounds --- the loop retries
  one delivery --- and the core is NEVER touched: a round is a ledger
  extension only, so the iterator composes modeled intermediates, not
  machine transitions.  Empty rounds (@{term "n = (0::nat)"}) and
  overshooting rounds (@{term n} beyond the remaining batch) are
  deliberately legal: @{term take} clamps, and the laws below hold for
  EVERY list of round lengths.
\<close>

fun partial_redrive_rounds
  :: "frontier \<Rightarrow> nat list \<Rightarrow> (nat, nat) dwe_state \<Rightarrow> (nat, nat) dwe_state"
where
  "partial_redrive_rounds f [] t = t"
| "partial_redrive_rounds f (n # ns) t =
     partial_redrive_rounds f ns
       (t\<lparr>dwe_emitted := dwe_emitted t
            @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                             dwe_epoch t, c, e))
                (take n (sink_delta f t))\<rparr>)"

text \<open>Rounds are ledger-only: the core and the epoch are invariant, so
  the named ascending premise --- a property of the committed source
  history alone --- survives every round unchanged.\<close>

lemma partial_redrive_rounds_core [simp]:
  "dwe_core (partial_redrive_rounds f ns t) = dwe_core t"
  by (induction f ns t rule: partial_redrive_rounds.induct) simp_all

lemma partial_redrive_rounds_epoch [simp]:
  "dwe_epoch (partial_redrive_rounds f ns t) = dwe_epoch t"
  by (induction f ns t rule: partial_redrive_rounds.induct) simp_all


section \<open>Multi-round convergence: the iterated remainder law\<close>

text \<open>
  THE CONVERGENCE LAW (item I(a), main form).  At any state of the
  pinned type (the landed any-state posture --- deliberately no
  reachability premise) with a strictly ascending committed source,
  after rounds with fired-prefix lengths @{term ns} the recomputed
  delta is exactly the @{term "drop (sum_list ns)"} remainder of the
  ORIGINAL batch: the landed single-round remainder law
  (@{thm [source] sink_delta_partial_append_remainder}, via its
  stamped corollary) composes with itself because a round changes
  neither the core nor the epoch.  Monotone progress, no restart, no
  re-emission --- in the function-equation sense fenced in the header,
  at modeled-intermediate states.
\<close>

theorem partial_redrive_rounds_delta:
  "strictly_ascending_source (exec_src_hist (dwe_core t)) \<Longrightarrow>
   sink_delta f (partial_redrive_rounds f ns t)
     = drop (sum_list ns) (sink_delta f t)"
proof (induction ns arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons n ns)
  let ?t1 = "t\<lparr>dwe_emitted := dwe_emitted t
                @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                                 dwe_epoch t, c, e))
                    (take n (sink_delta f t))\<rparr>"
  have asc1: "strictly_ascending_source (exec_src_hist (dwe_core ?t1))"
    using Cons.prems by simp
  have d1: "sink_delta f ?t1 = drop n (sink_delta f t)"
    by (rule sink_delta_partial_redrive_remainder[OF Cons.prems])
  have "sink_delta f (partial_redrive_rounds f (n # ns) t)
      = sink_delta f (partial_redrive_rounds f ns ?t1)"
    by simp
  also have "\<dots> = drop (sum_list ns) (sink_delta f ?t1)"
    by (rule Cons.IH[OF asc1])
  also have "\<dots> = drop (sum_list ns) (drop n (sink_delta f t))"
    using d1 by simp
  also have "\<dots> = drop (sum_list (n # ns)) (sink_delta f t)"
    by (simp add: drop_drop add.commute)
  finally show ?case .
qed

text \<open>
  THE CUMULATIVE FOOTPRINT.  The whole loop's ledger extension is ONE
  stamped map of the @{term "take (sum_list ns)"} prefix of the
  original batch --- successive rounds fire consecutive segments that
  reassemble by @{thm [source] take_add}, and the stamp is constant
  across rounds because core and epoch are.  Emission-level equality,
  not merely payload-level: rounds duplicate nothing and reorder
  nothing.
\<close>

theorem partial_redrive_rounds_emitted:
  "strictly_ascending_source (exec_src_hist (dwe_core t)) \<Longrightarrow>
   dwe_emitted (partial_redrive_rounds f ns t)
     = dwe_emitted t
       @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                        dwe_epoch t, c, e))
           (take (sum_list ns) (sink_delta f t))"
proof (induction ns arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons n ns)
  let ?st = "\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                       dwe_epoch t, c, e)"
  let ?t1 = "t\<lparr>dwe_emitted := dwe_emitted t
                @ map ?st (take n (sink_delta f t))\<rparr>"
  have asc1: "strictly_ascending_source (exec_src_hist (dwe_core ?t1))"
    using Cons.prems by simp
  have d1: "sink_delta f ?t1 = drop n (sink_delta f t)"
    by (rule sink_delta_partial_redrive_remainder[OF Cons.prems])
  have "dwe_emitted (partial_redrive_rounds f (n # ns) t)
      = dwe_emitted (partial_redrive_rounds f ns ?t1)"
    by simp
  also have "\<dots> = dwe_emitted ?t1
      @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core ?t1)),
                       dwe_epoch ?t1, c, e))
          (take (sum_list ns) (sink_delta f ?t1))"
    by (rule Cons.IH[OF asc1])
  also have "\<dots> = dwe_emitted t
      @ map ?st (take n (sink_delta f t))
      @ map ?st (take (sum_list ns) (drop n (sink_delta f t)))"
    using d1 by simp
  also have "\<dots> = dwe_emitted t
      @ map ?st (take n (sink_delta f t)
                 @ take (sum_list ns) (drop n (sink_delta f t)))"
    by simp
  also have "\<dots> = dwe_emitted t
      @ map ?st (take (n + sum_list ns) (sink_delta f t))"
    by (simp only: take_add[symmetric])
  also have "\<dots> = dwe_emitted t
      @ map ?st (take (sum_list (n # ns)) (sink_delta f t))"
    by simp
  finally show ?case .
qed

corollary partial_redrive_rounds_emitted_payloads:
  assumes asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "map e_payload (dwe_emitted (partial_redrive_rounds f ns t))
           = map e_payload (dwe_emitted t)
             @ take (sum_list ns) (sink_delta f t)"
  by (simp add: partial_redrive_rounds_emitted[OF asc])

text \<open>
  NO DUPLICATION ACROSS THE LOOP.  From a duplicate-free ledger, the
  whole multi-round loop keeps the payload projection duplicate-free:
  each round's fired segment is disjoint from every earlier round's
  (consecutive segments of one batch made internally distinct by the
  named ascending premise --- the landed B1 pipeline) and from the
  pre-existing ledger (the batch was computed against it).  This is
  the multi-round face of the landed duplicate-freedom argument.
\<close>

theorem partial_redrive_rounds_no_duplication:
  assumes asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
      and old: "distinct (map e_payload (dwe_emitted t))"
  shows "distinct (map e_payload (dwe_emitted (partial_redrive_rounds f ns t)))"
proof -
  have pay: "map e_payload (dwe_emitted (partial_redrive_rounds f ns t))
      = map e_payload (dwe_emitted t) @ take (sum_list ns) (sink_delta f t)"
    by (rule partial_redrive_rounds_emitted_payloads[OF asc])
  have dist_take: "distinct (take (sum_list ns) (sink_delta f t))"
    by (rule distinct_take[OF ascending_sink_delta_distinct[OF asc]])
  have fresh: "set (sink_delta f t) \<inter> set (map e_payload (dwe_emitted t)) = {}"
    by (auto simp: sink_delta_def)
  have disj: "set (take (sum_list ns) (sink_delta f t))
                \<inter> set (map e_payload (dwe_emitted t)) = {}"
    using fresh set_take_subset[of "sum_list ns" "sink_delta f t"] by blast
  show ?thesis
    unfolding pay using old dist_take disj by auto
qed

text \<open>
  COMPLETION, cumulative form: once the cumulative fired count reaches
  the batch length, the recomputed delta is empty --- the landed
  full-append corollary generalized to any number of rounds.  No
  progress premise: the bound is on the SUM.
\<close>

corollary partial_redrive_rounds_complete:
  assumes asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
      and len: "length (sink_delta f t) \<le> sum_list ns"
  shows "sink_delta f (partial_redrive_rounds f ns t) = []"
  using partial_redrive_rounds_delta[OF asc] len by simp

text \<open>Progress bound: rounds that each fire at least one element sum to
  at least their count --- the only place a progress premise is
  genuinely needed.\<close>

lemma rounds_progress_sum_bound:
  "\<forall>n \<in> set ns. 0 < n \<Longrightarrow> length ns \<le> sum_list ns"
proof (induction ns)
  case Nil
  then show ?case by simp
next
  case (Cons a ns)
  have len: "length ns \<le> sum_list ns"
    using Cons by simp
  have pos: "0 < a"
    using Cons.prems by simp
  have "Suc (length ns) \<le> a + sum_list ns"
    using len pos by linarith
  then show ?case by simp
qed

text \<open>
  COMPLETION, effective-rounds form: if every round makes progress
  (fires at least one element), batch-length many rounds suffice ---
  the modeled retry loop needs at most @{term "length (sink_delta f t)"}
  effective rounds to owe nothing.
\<close>

corollary partial_redrive_rounds_effective_complete:
  assumes asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
      and prog: "\<forall>n \<in> set ns. 0 < n"
      and len: "length (sink_delta f t) \<le> length ns"
  shows "sink_delta f (partial_redrive_rounds f ns t) = []"
  by (rule partial_redrive_rounds_complete[OF asc
        le_trans[OF len rounds_progress_sum_bound[OF prog]]])

text \<open>
  HAZARD-FREEDOM ACROSS THE LOOP: from an effect-safe start under the
  ascending premise, EVERY round state is effect-safe --- the landed
  single-round effect-safety theorem (@{thm [source]
  sink_delta_partial_state_effect_safe}, instantiated at each round's
  own epoch) iterated along the loop.  The modeled intermediates are
  hazard-free throughout, not merely delta-recomputable.
\<close>

theorem partial_redrive_rounds_effect_safe:
  "\<not> effect_unsafe t \<Longrightarrow>
   strictly_ascending_source (exec_src_hist (dwe_core t)) \<Longrightarrow>
   \<not> effect_unsafe (partial_redrive_rounds f ns t)"
proof (induction ns arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons n ns)
  let ?t1 = "t\<lparr>dwe_emitted := dwe_emitted t
                @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                                 dwe_epoch t, c, e))
                    (take n (sink_delta f t))\<rparr>"
  have safe1: "\<not> effect_unsafe ?t1"
    by (rule sink_delta_partial_state_effect_safe[OF Cons.prems])
  have asc1: "strictly_ascending_source (exec_src_hist (dwe_core ?t1))"
    using Cons.prems(2) by simp
  have "\<not> effect_unsafe (partial_redrive_rounds f ns ?t1)"
    by (rule Cons.IH[OF safe1 asc1])
  then show ?case by simp
qed


section \<open>Frontier robustness: source appends beyond the frontier\<close>

text \<open>
  The engine: the frontier-bounded replay never reads coordinates past
  the frontier, so appending such entries to the source history leaves
  it unchanged.  Premise-free apart from the coordinate bound --- no
  ordering premise is consumed anywhere in this section.
\<close>

lemma replay_down_hist_append_beyond:
  assumes "\<forall>x \<in> set E. f < fst x"
  shows "replay_down_hist (H @ E) K f = replay_down_hist H K f"
proof -
  have "filter (\<lambda>(c, e). c \<le> f \<and> key_of e \<in> K) E = []"
    using assms by (intro filter_False) (auto simp: case_prod_beta not_le)
  then show ?thesis
    by (simp add: replay_down_hist_def)
qed

text \<open>
  FRONTIER-APPEND INVARIANCE (item I(b)).  Any state whose committed
  source history extends the original by entries with coordinates
  strictly beyond the frontier --- scope and ledger unchanged, every
  other field free --- computes the SAME delta at that frontier.
  Stated as a relation between two states of the pinned type: this is
  a FUNCTION EQUATION about the source-append shape, deliberately
  silent on how (or whether) a machine could produce the second state;
  machine-level interleaving of commits with re-drives is the priced
  small-step design's domain and is NOT claimed here.
\<close>

theorem sink_delta_source_append_beyond_frontier:
  assumes src': "exec_src_hist (dwe_core t') = exec_src_hist (dwe_core t) @ E"
      and scope': "exec_scope (dwe_core t') = exec_scope (dwe_core t)"
      and em': "dwe_emitted t' = dwe_emitted t"
      and beyond: "\<forall>x \<in> set E. f < fst x"
  shows "sink_delta f t' = sink_delta f t"
  by (simp add: sink_delta_def src' scope' em'
                replay_down_hist_append_beyond[OF beyond])

corollary sink_delta_source_append_invariant:
  assumes beyond: "\<forall>x \<in> set E. f < fst x"
  shows "sink_delta f
           (t\<lparr>dwe_core := (dwe_core t)
                \<lparr>exec_src_hist := exec_src_hist (dwe_core t) @ E\<rparr>\<rparr>)
       = sink_delta f t"
  by (rule sink_delta_source_append_beyond_frontier[OF _ _ _ beyond]) simp_all


section \<open>Load-bearing controls: both premises bite\<close>

text \<open>
  CONTROL 1 (the ascending premise bites, multi-round face).  At the
  landed WF-H1-legal equal-coordinate control state @{const psl_w}
  (one business payload committed twice --- the landed aliasing axis),
  ONE round of length 1 payload-blocks BOTH occurrences: the recomputed
  delta is @{term "[]"} instead of the one-element remainder, so the
  convergence law fails without the premise --- exactly the landed
  single-round control (@{thm [source] partial_append_asc_load_bearing})
  surfacing through the iterator.  The control state is a state of the
  type, not claimed reachable --- matching the laws' premise set.
\<close>

lemma rounds_psl_starves:
  "sink_delta ec1 (partial_redrive_rounds ec1 [1] psl_w) = []"
  by (simp add: psl_w_def mkT_def mkC_def sink_delta_def
                replay_down_hist_def e1_def ec_defs)

lemma rounds_psl_remainder_ne:
  "sink_delta ec1 (partial_redrive_rounds ec1 [1] psl_w)
     \<noteq> drop (sum_list [1]) (sink_delta ec1 psl_w)"
  using rounds_psl_starves psl_remainder by simp

theorem rounds_asc_load_bearing:
  "\<exists>(t :: (nat, nat) dwe_state) f ns.
     wellformed_src_history (exec_src_hist (dwe_core t))
   \<and> sink_delta f (partial_redrive_rounds f ns t)
       \<noteq> drop (sum_list ns) (sink_delta f t)"
  using psl_wf rounds_psl_remainder_ne by blast

text \<open>
  CONTROL 2 (the beyond-the-frontier bound bites).  Appending an entry
  AT the frontier is not covered and genuinely changes the delta: at
  an empty-history state, appending the in-scope entry
  @{term "(ec1, e1)"} with the frontier at @{const ec1} turns the
  computed delta from @{term "[]"} into a singleton.
\<close>

definition fb_w :: "(nat, nat) dwe_state" where
  "fb_w = mkT (mkC [] [] [] {} Running) [] 0"

lemma fb_base: "sink_delta ec1 fb_w = []"
  by (simp add: fb_w_def mkT_def mkC_def sink_delta_def
                replay_down_hist_def)

lemma fb_appended:
  "sink_delta ec1
     (fb_w\<lparr>dwe_core := (dwe_core fb_w)
             \<lparr>exec_src_hist := exec_src_hist (dwe_core fb_w) @ [(ec1, e1)]\<rparr>\<rparr>)
   = [(ec1, e1)]"
  by (simp add: fb_w_def mkT_def mkC_def sink_delta_def
                replay_down_hist_def e1_def ec_defs)

lemma fb_not_beyond: "\<not> (\<forall>x \<in> set [(ec1, e1)]. ec1 < fst x)"
  by simp

theorem frontier_bound_load_bearing:
  "\<exists>(t :: (nat, nat) dwe_state) E f.
     \<not> (\<forall>x \<in> set E. f < fst x)
   \<and> sink_delta f
       (t\<lparr>dwe_core := (dwe_core t)
            \<lparr>exec_src_hist := exec_src_hist (dwe_core t) @ E\<rparr>\<rparr>)
       \<noteq> sink_delta f t"
proof -
  have ne: "sink_delta ec1
       (fb_w\<lparr>dwe_core := (dwe_core fb_w)
               \<lparr>exec_src_hist := exec_src_hist (dwe_core fb_w) @ [(ec1, e1)]\<rparr>\<rparr>)
       \<noteq> sink_delta ec1 fb_w"
    by (simp add: fb_appended fb_base)
  show ?thesis
    using fb_not_beyond ne by blast
qed


section \<open>Standard ML export: the escape's owed batch, runnable (item J)\<close>

text \<open>
  The sink-reading delta generates and type-checks as Standard ML ---
  @{command export_code} with @{text "checking SML"} plus the
  @{method code_simp} witness theorems below is exactly the landed
  decider capstone's bar: matched, not exceeded (no file export, no
  eval or normalization oracles).  @{const sink_delta} is a POINT
  function from one state to the owed batch --- never a schedule
  executor (gate ruling D-S5-2); state constructors and the two-tier
  verdict stack are already exported by the landed decider theory.
  Its behavioral certificate is the landed section-18 laws together
  with the convergence laws above.
\<close>

export_code sink_delta checking SML

text \<open>Kernel-evaluated witnesses (oracle-free @{method code_simp}, the
  landed decider discipline): the exported function computes --- on the
  landed aliasing control state it owes the duplicated payload twice
  (the ascending premise's bite, executably visible), and on the
  empty-history state it owes nothing.\<close>

lemma sink_delta_code_witness:
  "sink_delta ec1 psl_w = [(ec1, e1), (ec1, e1)]"
  by code_simp

lemma sink_delta_code_witness_empty:
  "sink_delta ec1 fb_w = []"
  by code_simp


end
