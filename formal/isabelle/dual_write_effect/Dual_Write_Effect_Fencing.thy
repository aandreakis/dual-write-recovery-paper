(*  Title:       Dual_Write_Effect_Fencing.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE FENCE: the positive payload of the D-091 channel/fencing wave
    (ladder section 34) --- an additive post-freeze slice under the
    freeze's own protocol (no landed statement, proof, definition,
    name, import, or session-DAG change), the third slice of the wave,
    completing the N/P contrast pair opened by the zombie of ladder
    section 33.

    READ THE SINK --- AND FENCE IT.  The zombie slice showed that on
    the channel machine the honest sink-reading escape is defeated by
    the wire alone: a superseded generation's in-flight copy arrives
    AFTER the recovery's read and duplicates the accepted record.  This
    theory proves the positive half: the ATOMIC FENCED RE-DRIVE --- the
    same sink-reading recovery with the fence raised to the successor
    of the crash-time epoch in the same rule --- restores exactly-once
    on the accepted record, at its own frontier, from EVERY
    accepted-safe crashed state with a strictly ascending committed
    source (fenced_redrive_exactly_once: premises = the landed B1 four,
    transported verbatim to the accepted record, NO fifth premise).  At
    the composite's result the ENTIRE residual wire is sub-fence
    (fenced_redrive_all_stale), so every later arrival of every prior
    generation is a guard-level rejection: arrive/lose-only
    continuations leave the accepted record LITERALLY unchanged
    (fenced_result_wire_preserves_eo).  The premises are state-level,
    so the guarantee holds at every crash (the every-crash corollary),
    and the two-composite multi-crash witness resolves the
    second-frontier accounting (second_fence_drop_rescoped).

    THE CONTROLS.  The biting control is the zombie schedule itself
    with ONE action constructor changed --- DWC_Fenced for DWC_Escape:
    the same wire traffic, the same labels, the same arrival order, and
    the straggler that duplicated the unfenced run is DROPPED at fence
    one (fence_load_bearing; the unfenced verdict is cited from the
    zombie slice).  The rescue-conversion control (gate amendment MF-8)
    exhibits the fence's COST side: when the recovery UNDER-SCOPES its
    frontier, the unfenced machine can still be rescued by the late
    arrival of the missed send, while the fenced twin converts that
    rescue into a certain drop --- duplicate-or-lose at the wire, one
    action constructor apart (fence_rescue_conversion).  The loss
    bonus: the accepted-record delta is loss-oblivious by construction,
    so a fenced re-drive heals a send the WIRE lost exactly like a
    never-arrived one (fenced_redrive_heals_lost_send), and at that
    state the landed SENT-side verdict and the machine's ACCEPTED-side
    verdict provably diverge (sent_accepted_verdicts_diverge) --- the
    re-reading of the records is owned as a theorem, not buried prose.

    NAME DISCIPLINE AND INHERITED STAND-IN STATUS.  "Exactly-once"
    below is the frontier-qualified accepted-record verdict dwc_eo_at;
    unless a statement says otherwise it is evaluated at the composite's
    own frontier at its own result state, and the two theorems that
    deliberately evaluate elsewhere scope their own reading explicitly
    (fence_rescue_conversion reads the ec2 verdict across both
    composites' continuations; fence_load_bearing reads it several
    actions past its composite).  The bare phrase is never a formal
    name.  Its
    delivery-completeness conjunct dwc_alo_at is a TERMINAL-STATE
    STAND-IN for delivery liveness of the landed
    acknowledgement-durability kind (boundary row 4), NOT a temporal
    eventually; between recoveries an in-flight entry is UNRESOLVED
    (neither delivered nor lost).

    FINITE-TRACE MAXIMUM, disclosed as such.  A temporal "eventually
    delivered under fair scheduling" claim would need infinite traces,
    coinduction, and a fairness predicate --- machinery this corpus
    deliberately does not have; any finite-trace rendering of that
    question reduces to runs whose crash windows end with a completed
    recovery.  The preservation theorem below is scoped accordingly
    (wave-design finding F-3): unscoped preservation is FALSE on this
    machine AND on the landed one --- a post-resume application
    re-publish of an already-accepted payload breaks the safety
    conjunct both places --- so the honest package is: exactly-once at
    the composite's own frontier at its result, verbatim preservation
    over arrive/lose-only continuations, the redrive-free growth bound
    (slice 1), and the per-frontier re-scoping of the next composite
    (the multi-crash witness).  Nothing temporal is claimed or implied.

    WHAT THE FENCE IS AND IS NOT.  The fence governs the WIRE (which
    arrivals are accepted), never the POLICY (which batch is
    re-driven): the positive rides the accepted-record delta batch plus
    strictly_ascending_source exactly as the landed B1 did; a
    store-measured or cursor batch through the same composite family
    retains BOTH landed horns on the accepted record.  The fence is
    necessary (the unfenced sibling is machine-defeated, slice 2) and
    not alone sufficient (non-stale duplicate-freedom still rides the
    ascending premise): necessary, never magic.

    IMPORTS: Dual_Write_Effect_Zombie alone --- the z-chain witness kit
    this slice reuses, and through it the channel machine, its fence
    invariant package, the exactly-once vocabulary, and the locked
    core.  The terminal branch enters no cone of this theory.

    PROVENANCE: owner decision D-091; the channel-wave design gate
    (paper/dual_write/theory_backlog/channel_wave/CHANNEL_WAVE_DESIGN.md,
    ratified COHERENT-GO with amendments MF-1..MF-10 by
    channel_wave/GATE_REPORT.md, 2026-07-07).  This slice executes the
    design section 4.5/4.6/4.7/4.8/4.9/4.10 content with gate
    amendment MF-8 (the pinned fence_rescue_conversion contrast
    control) applied.

    In-source ML oracle gates are STRIPPED at landing: oracle-freedom
    is certified by scratch-side per-slice gate sessions with
    confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Fencing
  imports Dual_Write_Effect_Zombie
begin

section \<open>P --- the fenced re-drive is exactly-once on the accepted record\<close>

text \<open>
  THE POSITIVE THEOREM, premise accounting exact: the four premises are
  the landed B1 set (@{thm [source] sink_reading_escape_general})
  transported to the accepted record --- effect-safe-pre becomes
  accepted-safe-pre; crashed, frontier, and
  @{const strictly_ascending_source} verbatim.  NO fifth premise.  The
  conclusion: the composite is enabled; every result heals every scoped
  store mismatch at the frontier (the landed heal, by the
  constant-batch @{const policy_redrive} projection --- a citation, not
  a re-proof); the result is exactly-once AT ITS OWN FRONTIER on the
  accepted record; and the fence stands at the successor of the
  crash-time epoch.  The proof is the landed B1 proof with the sent
  ledger systematically replaced by the accepted record: old entries
  keep their verdicts because the committed prefix is untouched, batch
  entries are fresh by the filter, justified generically, and
  internally distinct by the ascending premise.

  The fence is necessary, not alone sufficient: non-stale
  duplicate-freedom still rides @{const strictly_ascending_source},
  exactly as landed --- the consumption table of the exactly-once
  theory extends by this row at the same polarity.
\<close>

theorem fenced_redrive_exactly_once:
  fixes t :: "(nat, nat) dwc_state"
  assumes acc_safe: "\<not> dwc_accepted_unsafe t"
      and crashed:  "\<exists>c. exec_status (dwe_core (dwc_inner t)) = Crashed c"
      and fin:      "f \<le> exec_finish (dwe_core (dwc_inner t))"
      and asc:      "strictly_ascending_source (dwc_src t)"
  shows "(\<exists>t'. dwc_fenced_redrive f t t')
       \<and> (\<forall>t'. dwc_fenced_redrive f t t' \<longrightarrow>
            (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core (dwc_inner t')) f) f k)
          \<and> dwc_eo_at f t'
          \<and> dwc_fence t' = Suc (dwe_epoch (dwc_inner t)))"
proof (rule conjI)
  show "\<exists>t'. dwc_fenced_redrive f t t'"
    using dwc_fenced_redriveI[OF crashed fin refl] by blast
next
  show "\<forall>t'. dwc_fenced_redrive f t t' \<longrightarrow>
          (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core (dwc_inner t')) f) f k)
        \<and> dwc_eo_at f t'
        \<and> dwc_fence t' = Suc (dwe_epoch (dwc_inner t))"
  proof (intro allI impI)
    fix t'
    assume pr: "dwc_fenced_redrive f t t'"

    \<comment> \<open>abbreviations for the state components\<close>
    define S where "S = dwc_src t"
    define R where "R = dwc_replay f t"
    define D where "D = dwc_sink_delta f t"
    have D_eq: "D = filter (\<lambda>p. p \<notin> e_payload ` set (dwc_accepted t)) R"
      by (simp add: D_def dwc_sink_delta_def R_def)
    have R_eq: "R = replay_down_hist S (dwc_scope t) f"
      by (simp add: R_def dwc_replay_def S_def)

    \<comment> \<open>the constant-batch policy projection: heal, src, scope by citation\<close>
    have proj: "policy_redrive (\<lambda>_. dwc_sink_delta f t) (dwc_inner t) f (dwc_inner t')"
      by (rule dwc_fenced_redrive_inner_projects[OF pr])
    have heal: "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core (dwc_inner t')) f) f k"
      by (rule policy_redrive_heals[OF proj])
    have src': "dwc_src t' = S"
      using policy_redrive_src_same[OF proj] by (simp add: dwc_src_def S_def)
    have scope': "dwc_scope t' = dwc_scope t"
      using policy_redrive_scope_same[OF proj] by (simp add: dwc_scope_def)
    have replay': "dwc_replay f t' = R"
      by (simp add: dwc_replay_def src' scope' R_eq)

    \<comment> \<open>the accepted record extends by the stamped delta batch\<close>
    have acc': "dwc_accepted t' = dwc_accepted t @ map (dwc_stamp t) D"
      using dwc_fenced_redrive_components(2)[OF pr] by (simp add: D_def)

    \<comment> \<open>the two safety verdicts inherited from the pre-state\<close>
    have old_just: "\<forall>x \<in> set (dwc_accepted t). justified_at S x"
      using acc_safe
      by (simp add: dwc_accepted_unsafe_def dwc_accepted_premature_def S_def)
    have old_dist: "distinct (map e_payload (dwc_accepted t))"
      using acc_safe
      by (simp add: dwc_accepted_unsafe_def dwc_accepted_duplicate_def)

    \<comment> \<open>distinctness pipeline from the ascending premise\<close>
    have dist_S: "distinct S"
      using strictly_ascending_distinct[OF asc] by (simp add: S_def)
    have dist_R: "distinct R"
      unfolding R_eq replay_down_hist_def using dist_S by simp
    have dist_D: "distinct D"
      unfolding D_eq using dist_R by simp

    \<comment> \<open>NOT premature: old entries frozen, new entries generically justified\<close>
    have just': "\<forall>x \<in> set (dwc_accepted t'). justified_at S x"
    proof
      fix x assume "x \<in> set (dwc_accepted t')"
      then consider (old) "x \<in> set (dwc_accepted t)"
        | (new) "x \<in> set (map (dwc_stamp t) D)"
        unfolding acc' by auto
      then show "justified_at S x"
      proof cases
        case old
        then show ?thesis using old_just by blast
      next
        case new
        have st: "e_stamp x = length S" and pay: "e_payload x \<in> set D"
          using dwc_stamped_elem[OF new] by (simp_all add: S_def)
        have "e_payload x \<in> set (replay_down_hist S (dwc_scope t) f)"
          using pay unfolding D_eq R_eq by auto
        then show ?thesis
          using redrive_emissions_justified st by blast
      qed
    qed
    have not_prem: "\<not> dwc_accepted_premature t'"
      using just' unfolding dwc_accepted_premature_def src' by blast

    \<comment> \<open>NOT duplicate: old distinct, new distinct, disjoint by the filter\<close>
    have pay': "map e_payload (dwc_accepted t')
        = map e_payload (dwc_accepted t) @ D"
      by (simp add: acc' o_def)
    have disj: "set D \<inter> set (map e_payload (dwc_accepted t)) = {}"
      unfolding D_eq by auto
    have "distinct (map e_payload (dwc_accepted t'))"
      unfolding pay' using old_dist dist_D disj by auto
    then have not_dup: "\<not> dwc_accepted_duplicate t'"
      by (simp add: dwc_accepted_duplicate_def)

    \<comment> \<open>at-least-once: every replay payload is accepted-before or kept by the filter\<close>
    have img': "e_payload ` set (dwc_accepted t')
        = e_payload ` set (dwc_accepted t) \<union> set D"
      by (simp add: acc' image_Un image_image)
    have alo: "dwc_alo_at f t'"
      unfolding dwc_alo_at_def replay'
    proof
      fix p assume p_in: "p \<in> set R"
      show "p \<in> e_payload ` set (dwc_accepted t')"
      proof (cases "p \<in> e_payload ` set (dwc_accepted t)")
        case True
        then show ?thesis using img' by blast
      next
        case False
        then have "p \<in> set D"
          unfolding D_eq using p_in by simp
        then show ?thesis using img' by blast
      qed
    qed

    \<comment> \<open>the fence stands at the successor of the crash-time epoch\<close>
    have fence: "dwc_fence t' = Suc (dwe_epoch (dwc_inner t))"
      by (rule dwc_fenced_redrive_components(3)[OF pr])

    show "(\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core (dwc_inner t')) f) f k)
        \<and> dwc_eo_at f t'
        \<and> dwc_fence t' = Suc (dwe_epoch (dwc_inner t))"
      using heal not_prem not_dup alo fence
      by (simp add: dwc_eo_at_def dwc_accepted_unsafe_def)
  qed
qed

text \<open>Non-vacuity of the premise set, computed at the zombie slice's
  crash state: the accepted record there is safe, the inner is crashed,
  the crash frontier is within the finish, and the committed source is
  strictly ascending --- the fenced composite's positive guarantee is
  exercised by the p-chain below on exactly this state.\<close>

lemma z8_satisfies_P_premises:
  "\<not> dwc_accepted_unsafe z8
 \<and> (\<exists>c. exec_status (dwe_core (dwc_inner z8)) = Crashed c)
 \<and> ec2 \<le> exec_finish (dwe_core (dwc_inner z8))
 \<and> strictly_ascending_source (dwc_src z8)"
  by (intro conjI)
     (simp_all add: dwc_accepted_unsafe_def dwc_accepted_premature_def
                    dwc_accepted_duplicate_def justified_at_def
                    strictly_ascending_source_def dwc_src_def z8_def mkZ_def
                    zi8_def mkT_def mkC_def e1_def e2_def ec_defs
                    eval_nat_numeral)

subsection \<open>All residual wire entries are sub-fence at the composite's result\<close>

text \<open>
  THE ANTI-ZOMBIE STATE FACT: the composite leaves the channel
  untouched and raises the fence above the crash-time epoch, and every
  in-flight entry is epoch-bounded by the pre-state's invariant --- so
  at the composite's result the ENTIRE residual wire, every in-flight
  emission of every prior generation, the recovery's predecessor
  included, is strictly below the fence.  The
  @{const dwc_epoch_bounds} premise is discharged at every reachable
  state by the slice-1 invariant (@{thm [source]
  dwc_reachable_fence_inv}); it is stated as a premise so the headline
  theorem above stays B1-premise-exact.
\<close>

theorem fenced_redrive_all_stale:
  assumes eb: "dwc_epoch_bounds t"
      and fr: "dwc_fenced_redrive f t t'"
  shows "\<forall>x \<in> set (dwc_channel t'). e_epoch x < dwc_fence t'"
proof
  fix x assume "x \<in> set (dwc_channel t')"
  then have "x \<in> set (dwc_channel t)"
    using dwc_fenced_redrive_components(1)[OF fr] by simp
  then have "e_epoch x \<le> dwe_epoch (dwc_inner t)"
    using eb unfolding dwc_epoch_bounds_def by blast
  then show "e_epoch x < dwc_fence t'"
    using dwc_fenced_redrive_components(3)[OF fr] by simp
qed

subsection \<open>The every-crash corollary\<close>

text \<open>The positive theorem's premises are STATE-LEVEL, so the guarantee
  re-applies at every crash whose state satisfies them --- no induction
  over the number of crashes exists or is needed.  Fences strictly rise
  between composites (a Resume is forced between two crashes, bumping
  the epoch), and the second-frontier accounting is resolved concretely
  by the multi-crash witness below.\<close>

corollary fenced_redrive_exactly_once_every_crash:
  "\<forall>(t :: (nat, nat) dwc_state) f.
     \<not> dwc_accepted_unsafe t
   \<and> (\<exists>c. exec_status (dwe_core (dwc_inner t)) = Crashed c)
   \<and> f \<le> exec_finish (dwe_core (dwc_inner t))
   \<and> strictly_ascending_source (dwc_src t)
   \<longrightarrow> (\<exists>t'. dwc_fenced_redrive f t t')
     \<and> (\<forall>t'. dwc_fenced_redrive f t t' \<longrightarrow>
          (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core (dwc_inner t')) f) f k)
        \<and> dwc_eo_at f t'
        \<and> dwc_fence t' = Suc (dwe_epoch (dwc_inner t)))"
proof (intro allI impI)
  fix t :: "(nat, nat) dwc_state" and f
  assume A: "\<not> dwc_accepted_unsafe t
           \<and> (\<exists>c. exec_status (dwe_core (dwc_inner t)) = Crashed c)
           \<and> f \<le> exec_finish (dwe_core (dwc_inner t))
           \<and> strictly_ascending_source (dwc_src t)"
  have a1: "\<not> dwc_accepted_unsafe t"
   and a2: "\<exists>c. exec_status (dwe_core (dwc_inner t)) = Crashed c"
   and a3: "f \<le> exec_finish (dwe_core (dwc_inner t))"
   and a4: "strictly_ascending_source (dwc_src t)"
    using A by blast+
  show "(\<exists>t'. dwc_fenced_redrive f t t')
      \<and> (\<forall>t'. dwc_fenced_redrive f t t' \<longrightarrow>
           (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core (dwc_inner t')) f) f k)
         \<and> dwc_eo_at f t'
         \<and> dwc_fence t' = Suc (dwe_epoch (dwc_inner t)))"
    by (rule fenced_redrive_exactly_once[OF a1 a2 a3 a4])
qed

section \<open>Honest preservation: the residual wire cannot touch the record\<close>

text \<open>
  WHAT "EVERY LATER STEP" HONESTLY MEANS (wave-design finding F-3
  applied).  The unscoped form --- "preserved by arbitrary
  continuations including new application work" --- is FALSE on this
  machine AND on the landed one: a post-resume application re-publish
  of an already-accepted payload breaks the safety conjunct both
  places, because the landed core carries no freshness guard.  The
  honest form: over arrive/lose-only continuations from the
  composite's result, the accepted record is LITERALLY unchanged ---
  by the all-stale fact every arrival is a guard-level rejection, no
  rule in the class adds channel entries, and the inner is untouched
  --- so exactly-once transports verbatim.  The zombie does not merely
  fail to duplicate; it cannot touch the record.  Combined with the
  slice-1 redrive-free growth bound (@{thm [source]
  accepted_growth_fenced}) this is the complete anti-zombie
  preservation story with zero temporal vocabulary; the
  cross-generation composition is per-frontier, per recovery, exactly
  the corpus's recurrence discipline.
\<close>

lemma wire_stale_frozen:
  assumes "dwc_temporal_trace u ys v"
      and "\<forall>a \<in> set ys. (\<exists>i. a = DWC_Arrive i) \<or> (\<exists>i. a = DWC_Lose i)"
      and "\<forall>x \<in> set (dwc_channel u). e_epoch x < dwc_fence u"
  shows "dwc_accepted v = dwc_accepted u \<and> dwc_inner v = dwc_inner u
       \<and> dwc_fence v = dwc_fence u
       \<and> (\<forall>x \<in> set (dwc_channel v). e_epoch x < dwc_fence v)"
  using assms
proof (induction rule: dwc_temporal_trace.induct)
  case (dwc_refl t)
  then show ?case by simp
next
  case (dwc_label_step t a t' as t'')
  then show ?case using dwc_label_step.prems(1) by simp
next
  case (dwc_reconcile_step m t f t' as t'')
  then show ?case using dwc_reconcile_step.prems(1) by simp
next
  case (dwc_resume_step t t' as t'')
  then show ?case using dwc_resume_step.prems(1) by simp
next
  case (dwc_arrive_step t i t' as t'')
  have fn: "dwc_fence t' = dwc_fence t"
    by (rule dwc_arrive_fence_same[OF dwc_arrive_step.hyps(1)])
  have inner: "dwc_inner t' = dwc_inner t"
    by (rule dwc_arrive_inner_stutter[OF dwc_arrive_step.hyps(1)])
  have len: "i < length (dwc_channel t)"
    using dwc_arrive_shape[OF dwc_arrive_step.hyps(1)] by blast
  have acc_same: "dwc_accepted t' = dwc_accepted t"
    using arrive_accept_respects_fence[OF dwc_arrive_step.hyps(1)]
  proof (elim disjE)
    assume "dwc_accepted t' = dwc_accepted t"
    then show ?thesis .
  next
    assume A: "dwc_fence t \<le> e_epoch (dwc_channel t ! i)
             \<and> dwc_accepted t' = dwc_accepted t @ [dwc_channel t ! i]"
    have "dwc_channel t ! i \<in> set (dwc_channel t)"
      by (rule nth_mem[OF len])
    then have lt: "e_epoch (dwc_channel t ! i) < dwc_fence t"
      using dwc_arrive_step.prems(2) by blast
    have False
      using conjunct1[OF A] lt by linarith
    then show ?thesis ..
  qed
  have stale': "\<forall>x \<in> set (dwc_channel t'). e_epoch x < dwc_fence t'"
    using dwc_arrive_channel_subset[OF dwc_arrive_step.hyps(1)]
          dwc_arrive_step.prems(2) fn by fastforce
  have cls': "\<forall>a \<in> set as. (\<exists>i. a = DWC_Arrive i) \<or> (\<exists>i. a = DWC_Lose i)"
    using dwc_arrive_step.prems(1) by simp
  have i1: "dwc_accepted t'' = dwc_accepted t'"
   and i2: "dwc_inner t'' = dwc_inner t'"
   and i3: "dwc_fence t'' = dwc_fence t'"
   and i4: "\<forall>x \<in> set (dwc_channel t''). e_epoch x < dwc_fence t''"
    using dwc_arrive_step.IH[OF cls' stale'] by blast+
  show ?case
  proof (intro conjI)
    show "dwc_accepted t'' = dwc_accepted t" by (simp add: i1 acc_same)
    show "dwc_inner t'' = dwc_inner t" by (simp add: i2 inner)
    show "dwc_fence t'' = dwc_fence t" by (simp add: i3 fn)
    show "\<forall>x \<in> set (dwc_channel t''). e_epoch x < dwc_fence t''"
      by (rule i4)
  qed
next
  case (dwc_lose_step t i t' as t'')
  have fn: "dwc_fence t' = dwc_fence t"
    by (rule dwc_lose_fence_same[OF dwc_lose_step.hyps(1)])
  have inner: "dwc_inner t' = dwc_inner t"
    by (rule dwc_lose_inner_stutter[OF dwc_lose_step.hyps(1)])
  have acc_same: "dwc_accepted t' = dwc_accepted t"
    by (rule dwc_lose_accepted_same[OF dwc_lose_step.hyps(1)])
  have stale': "\<forall>x \<in> set (dwc_channel t'). e_epoch x < dwc_fence t'"
    using dwc_lose_channel_subset[OF dwc_lose_step.hyps(1)]
          dwc_lose_step.prems(2) fn by fastforce
  have cls': "\<forall>a \<in> set as. (\<exists>i. a = DWC_Arrive i) \<or> (\<exists>i. a = DWC_Lose i)"
    using dwc_lose_step.prems(1) by simp
  have i1: "dwc_accepted t'' = dwc_accepted t'"
   and i2: "dwc_inner t'' = dwc_inner t'"
   and i3: "dwc_fence t'' = dwc_fence t'"
   and i4: "\<forall>x \<in> set (dwc_channel t''). e_epoch x < dwc_fence t''"
    using dwc_lose_step.IH[OF cls' stale'] by blast+
  show ?case
  proof (intro conjI)
    show "dwc_accepted t'' = dwc_accepted t" by (simp add: i1 acc_same)
    show "dwc_inner t'' = dwc_inner t" by (simp add: i2 inner)
    show "dwc_fence t'' = dwc_fence t" by (simp add: i3 fn)
    show "\<forall>x \<in> set (dwc_channel t''). e_epoch x < dwc_fence t''"
      by (rule i4)
  qed
next
  case (dwc_escape_step f t t' as t'')
  then show ?case using dwc_escape_step.prems(1) by simp
next
  case (dwc_fenced_step f t t' as t'')
  then show ?case using dwc_fenced_step.prems(1) by simp
qed

theorem fenced_result_wire_preserves_eo:
  assumes eb: "dwc_epoch_bounds t"
      and fr: "dwc_fenced_redrive f t t'"
      and eo: "dwc_eo_at f t'"
      and tr: "dwc_temporal_trace t' ys v"
      and cls: "\<forall>a \<in> set ys. (\<exists>i. a = DWC_Arrive i) \<or> (\<exists>i. a = DWC_Lose i)"
  shows "dwc_eo_at f v \<and> dwc_accepted v = dwc_accepted t'"
proof -
  have stale: "\<forall>x \<in> set (dwc_channel t'). e_epoch x < dwc_fence t'"
    by (rule fenced_redrive_all_stale[OF eb fr])
  have frz: "dwc_accepted v = dwc_accepted t' \<and> dwc_inner v = dwc_inner t'
           \<and> dwc_fence v = dwc_fence t'
           \<and> (\<forall>x \<in> set (dwc_channel v). e_epoch x < dwc_fence v)"
    by (rule wire_stale_frozen[OF tr cls stale])
  have acc_eq: "dwc_accepted v = dwc_accepted t'"
   and inner_eq: "dwc_inner v = dwc_inner t'"
    using frz by blast+
  have "dwc_eo_at f v \<longleftrightarrow> dwc_eo_at f t'"
    by (simp add: dwc_eo_at_def dwc_accepted_unsafe_def
                  dwc_accepted_premature_def dwc_accepted_duplicate_def
                  dwc_alo_at_def dwc_replay_def dwc_src_def dwc_scope_def
                  acc_eq inner_eq)
  then show ?thesis using eo acc_eq by simp
qed

section \<open>The packaged reachable-state form: one citable fence theorem\<close>

text \<open>
  ONE theorem with the explicit premise list, for citation as a unit.
  At any REACHABLE crashed state --- reachability discharges the
  epoch-bounds invariant via
  @{thm [source] dwc_reachable_fence_inv} --- satisfying the positive
  theorem's own premises (accepted-safe, crashed, in-range frontier,
  strictly ascending committed source), the atomic fenced re-drive at
  @{term f}:

  \<^item> EXISTS;
  \<^item> heals every scoped store mismatch at @{term f} and is EXACTLY-ONCE
    at @{term f} on the accepted record at its own result, with the
    fence raised to the successor of the crash-time epoch;
  \<^item> leaves EVERY residual wire entry strictly below the new fence
    (every in-flight emission of every prior generation is a guard-level
    rejection on arrival);
  \<^item> and over every arrive/lose-only continuation the accepted record ---
    and with it the @{term f}-verdict --- is literally unchanged.

  The conjuncts are the landed
  @{thm [source] fenced_redrive_exactly_once},
  @{thm [source] fenced_redrive_all_stale}, and
  @{thm [source] fenced_result_wire_preserves_eo}, discharged together
  under one premise list; nothing is re-proved and nothing beyond them
  is claimed.  The continuation conjunct is scoped to arrive/lose-only
  traces exactly as the preservation theorem is: unscoped preservation
  is FALSE on this machine and on the landed one (a post-resume
  application re-publish of an already-accepted payload breaks the
  safety conjunct), and between recoveries an in-flight entry is
  UNRESOLVED --- nothing temporal is claimed.
\<close>

theorem fenced_redrive_reachable_package:
  fixes t :: "(nat, nat) dwc_state"
  assumes reach:    "dwc_reachable t"
      and acc_safe: "\<not> dwc_accepted_unsafe t"
      and crashed:  "\<exists>c. exec_status (dwe_core (dwc_inner t)) = Crashed c"
      and fin:      "f \<le> exec_finish (dwe_core (dwc_inner t))"
      and asc:      "strictly_ascending_source (dwc_src t)"
  shows "(\<exists>t'. dwc_fenced_redrive f t t')
       \<and> (\<forall>t'. dwc_fenced_redrive f t t' \<longrightarrow>
            (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core (dwc_inner t')) f) f k)
          \<and> dwc_eo_at f t'
          \<and> dwc_fence t' = Suc (dwe_epoch (dwc_inner t))
          \<and> (\<forall>x \<in> set (dwc_channel t'). e_epoch x < dwc_fence t')
          \<and> (\<forall>ys v. dwc_temporal_trace t' ys v
               \<longrightarrow> (\<forall>a \<in> set ys.
                      (\<exists>i. a = DWC_Arrive i) \<or> (\<exists>i. a = DWC_Lose i))
               \<longrightarrow> dwc_eo_at f v \<and> dwc_accepted v = dwc_accepted t'))"
proof -
  have eb: "dwc_epoch_bounds t"
    using dwc_reachable_fence_inv[OF reach]
    by (simp add: dwc_fence_inv_def)
  have pos: "(\<exists>t'. dwc_fenced_redrive f t t')
       \<and> (\<forall>t'. dwc_fenced_redrive f t t' \<longrightarrow>
            (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core (dwc_inner t')) f) f k)
          \<and> dwc_eo_at f t'
          \<and> dwc_fence t' = Suc (dwe_epoch (dwc_inner t)))"
    by (rule fenced_redrive_exactly_once[OF acc_safe crashed fin asc])
  show ?thesis
  proof (rule conjI)
    show "\<exists>t'. dwc_fenced_redrive f t t'"
      using pos by blast
  next
    show "\<forall>t'. dwc_fenced_redrive f t t' \<longrightarrow>
            (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core (dwc_inner t')) f) f k)
          \<and> dwc_eo_at f t'
          \<and> dwc_fence t' = Suc (dwe_epoch (dwc_inner t))
          \<and> (\<forall>x \<in> set (dwc_channel t'). e_epoch x < dwc_fence t')
          \<and> (\<forall>ys v. dwc_temporal_trace t' ys v
               \<longrightarrow> (\<forall>a \<in> set ys.
                      (\<exists>i. a = DWC_Arrive i) \<or> (\<exists>i. a = DWC_Lose i))
               \<longrightarrow> dwc_eo_at f v \<and> dwc_accepted v = dwc_accepted t')"
    proof (intro allI impI)
      fix t'
      assume fr: "dwc_fenced_redrive f t t'"
      have heal: "\<forall>k. \<not> mismatch_at
                    (proto_of_exec_at (dwe_core (dwc_inner t')) f) f k"
        using pos fr by blast
      have eo: "dwc_eo_at f t'"
        using pos fr by blast
      have fence: "dwc_fence t' = Suc (dwe_epoch (dwc_inner t))"
        using pos fr by blast
      have stale: "\<forall>x \<in> set (dwc_channel t'). e_epoch x < dwc_fence t'"
        by (rule fenced_redrive_all_stale[OF eb fr])
      have cont: "\<forall>ys v. dwc_temporal_trace t' ys v
               \<longrightarrow> (\<forall>a \<in> set ys.
                      (\<exists>i. a = DWC_Arrive i) \<or> (\<exists>i. a = DWC_Lose i))
               \<longrightarrow> dwc_eo_at f v \<and> dwc_accepted v = dwc_accepted t'"
      proof (intro allI impI)
        fix ys v
        assume tr: "dwc_temporal_trace t' ys v"
           and cls: "\<forall>a \<in> set ys.
                       (\<exists>i. a = DWC_Arrive i) \<or> (\<exists>i. a = DWC_Lose i)"
        show "dwc_eo_at f v \<and> dwc_accepted v = dwc_accepted t'"
          by (rule fenced_result_wire_preserves_eo[OF eb fr eo tr cls])
      qed
      show "(\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core (dwc_inner t')) f) f k)
          \<and> dwc_eo_at f t'
          \<and> dwc_fence t' = Suc (dwe_epoch (dwc_inner t))
          \<and> (\<forall>x \<in> set (dwc_channel t'). e_epoch x < dwc_fence t')
          \<and> (\<forall>ys v. dwc_temporal_trace t' ys v
               \<longrightarrow> (\<forall>a \<in> set ys.
                      (\<exists>i. a = DWC_Arrive i) \<or> (\<exists>i. a = DWC_Lose i))
               \<longrightarrow> dwc_eo_at f v \<and> dwc_accepted v = dwc_accepted t')"
        using heal eo fence stale cont by blast
    qed
  qed
qed

section \<open>The biting control: the zombie schedule with the fence on\<close>

text \<open>
  THE MINIMAL PAIR.  The p-chain is the zombie slice's z-chain with
  EXACTLY ONE action constructor changed: @{term "DWC_Fenced ec2"} at
  the recovery instead of @{term "DWC_Escape ec2"}.  Labels, wire
  actions, and arrival order are identical.  The fenced composite
  computes the SAME delta (the read is the same read), raises the
  fence to one, and the run continues verbatim: Resume, the epoch-one
  third event, the fresh emission's arrival (epoch one clears fence
  one).  Then the superseded generation's straggler --- the arrival
  that DUPLICATED the unfenced run --- meets the fence: epoch zero
  below fence one, an @{text arrive_drop} step, the rejection
  exhibited.  Fence off: hazard (the zombie slice's end state,
  cited).  Fence on: the same wire traffic is harmless.
\<close>

definition p9 :: "(nat, nat) dwc_state" where
  "p9 = mkZ zi9 [(2, 0, ec2, e2)] [(1, 0, ec1, e1), (2, 0, ec2, e2)] 1"

definition p10 :: "(nat, nat) dwc_state" where
  "p10 = mkZ zi10 [(2, 0, ec2, e2)] [(1, 0, ec1, e1), (2, 0, ec2, e2)] 1"

definition p11 :: "(nat, nat) dwc_state" where
  "p11 = mkZ zi11 [(2, 0, ec2, e2)] [(1, 0, ec1, e1), (2, 0, ec2, e2)] 1"

definition p12 :: "(nat, nat) dwc_state" where
  "p12 = mkZ zi12 [(2, 0, ec2, e2)] [(1, 0, ec1, e1), (2, 0, ec2, e2)] 1"

definition p13 :: "(nat, nat) dwc_state" where
  "p13 = mkZ zi13 [(2, 0, ec2, e2), (3, 1, ec3, ev3)]
           [(1, 0, ec1, e1), (2, 0, ec2, e2)] 1"

definition p14 :: "(nat, nat) dwc_state" where
  "p14 = mkZ zi13 [(2, 0, ec2, e2)]
           [(1, 0, ec1, e1), (2, 0, ec2, e2), (3, 1, ec3, ev3)] 1"

definition p15 :: "(nat, nat) dwc_state" where
  "p15 = mkZ zi13 []
           [(1, 0, ec1, e1), (2, 0, ec2, e2), (3, 1, ec3, ev3)] 1"

text \<open>The fenced recovery at the crash state: same read, same delta,
  same synchronous re-drive as the zombie slice's escape --- plus the
  fence raised to the successor of the crash-time epoch, in the same
  rule.  The inner result is byte-identical to the escape's.\<close>

lemma pfen9: "dwc_fenced_redrive ec2 z8 p9"
  by (rule dwc_fenced_redriveI)
     (simp_all add: z8_def p9_def mkZ_def zi8_def zi9_def mkT_def mkC_def
                    dwc_sink_delta_def dwc_replay_def dwc_src_def
                    dwc_scope_def replay_down_hist_def e1_def e2_def ec_defs
                    eval_nat_numeral)

lemma pres10: "dwc_resume_lift p9 p10"
proof -
  have i: "dwe_resume (dwc_inner p9) zi10"
    using zi_resume by (simp add: p9_def)
  show ?thesis
    by (rule dwc_resume_liftI[OF i]) (simp add: p9_def p10_def mkZ_def)
qed

lemma ps11: "dwc_step p10 (DoSource ec3 ev3) p11"
proof -
  have i: "dwe_step (dwc_inner p10) (DoSource ec3 ev3) zi11"
    using zi_src3 by (simp add: p10_def)
  show ?thesis
    by (rule dwc_lift_nonpubI[OF i]) (simp_all add: p10_def p11_def mkZ_def)
qed

lemma ps12: "dwc_step p11 (EnqueueDownstream ec3 ev3) p12"
proof -
  have i: "dwe_step (dwc_inner p11) (EnqueueDownstream ec3 ev3) zi12"
    using zi_enq3 by (simp add: p11_def)
  show ?thesis
    by (rule dwc_lift_nonpubI[OF i]) (simp_all add: p11_def p12_def mkZ_def)
qed

lemma ps13: "dwc_step p12 (DoDownstream ec3 ev3) p13"
proof -
  have i: "dwe_step (dwc_inner p12) (DoDownstream ec3 ev3) zi13"
    using zi_down3 by (simp add: p12_def)
  show ?thesis
    by (rule dwc_send_pubI[OF i])
       (simp add: p12_def p13_def mkZ_def zi12_def mkT_def mkC_def
                  dwc_src_def eval_nat_numeral)
qed

text \<open>The fresh epoch-one emission clears fence one: born acceptable.\<close>

lemma ps14: "dwc_arrive p13 1 p14"
  by (rule dwc_arrive_acceptI)
     (simp_all add: p13_def p14_def mkZ_def eval_nat_numeral)

text \<open>THE REJECTION: the zombie slice's defeat step, re-run against the
  raised fence --- epoch zero below fence one, a drop, the accepted
  record untouched.\<close>

lemma ps15: "dwc_arrive p14 0 p15"
  by (rule dwc_arrive_dropI)
     (simp_all add: p14_def p15_def mkZ_def eval_nat_numeral)

lemma reach_p9: "dwc_reachable p9"
  by (rule dwc_reachable_fenced_ext[OF reach_z8 pfen9])

lemma reach_p10: "dwc_reachable p10"
  by (rule dwc_reachable_resume_ext[OF reach_p9 pres10])

lemma reach_p11: "dwc_reachable p11"
  by (rule dwc_reachable_label_ext[OF reach_p10 _ _ ps11])
     (simp_all add: p10_def wf_zi10 g_zi10_src3)

lemma reach_p12: "dwc_reachable p12"
  by (rule dwc_reachable_label_ext[OF reach_p11 _ _ ps12])
     (simp_all add: p11_def wf_zi11 g_zi11_enq3)

lemma reach_p13: "dwc_reachable p13"
  by (rule dwc_reachable_label_ext[OF reach_p12 _ _ ps13])
     (simp_all add: p12_def wf_zi12 g_zi12_down3)

lemma reach_p14: "dwc_reachable p14"
  by (rule dwc_reachable_arrive_ext[OF reach_p13 ps14])

lemma reach_p15: "dwc_reachable p15"
  by (rule dwc_reachable_arrive_ext[OF reach_p14 ps15])

lemma p15_eo: "dwc_eo_at ec2 p15"
  by (simp add: dwc_eo_at_def dwc_accepted_unsafe_def
                dwc_accepted_premature_def dwc_accepted_duplicate_def
                dwc_alo_at_def justified_at_def dwc_replay_def dwc_src_def
                dwc_scope_def replay_down_hist_def p15_def mkZ_def zi13_def
                mkT_def mkC_def e1_def e2_def ev3_def ec_defs
                eval_nat_numeral)

lemma p15_no_duplicate: "\<not> dwc_accepted_duplicate p15"
  by (simp add: dwc_accepted_duplicate_def p15_def mkZ_def e1_def e2_def
                ev3_def ec_defs)

lemma p15_accepted:
  "dwc_accepted p15 = [(1, 0, ec1, e1), (2, 0, ec2, e2), (3, 1, ec3, ev3)]"
  by (simp add: p15_def)

lemma p15_channel: "dwc_channel p15 = []"
  by (simp add: p15_def)

lemma p15_fence: "dwc_fence p15 = 1"
  by (simp add: p15_def)

theorem fence_load_bearing:
  "dwc_reachable p15
 \<and> dwc_eo_at ec2 p15 \<and> \<not> dwc_accepted_duplicate p15
 \<and> dwc_accepted p15 = [(1, 0, ec1, e1), (2, 0, ec2, e2), (3, 1, ec3, ev3)]
 \<and> dwc_channel p15 = []
 \<and> dwc_fence p15 = 1
 \<and> dwc_accepted_duplicate z15
   \<comment> \<open>cited from the zombie slice --- same schedule, fence off, duplicate\<close>"
  by (intro conjI reach_p15 p15_eo p15_no_duplicate p15_accepted p15_channel
            p15_fence z15_duplicate)

section \<open>Multi-crash: the second frontier, both branches accounted\<close>

text \<open>
  EXACT FRONTIER SCOPING (binding wording): @{const dwc_eo_at} is
  evaluated at each composite's OWN frontier at its OWN result state
  (and preserved across the residual wire per the preservation theorem
  above).  A fence-drop is NEVER a loss at the next composite's
  frontier, because @{const dwc_alo_at} reads replay-vs-accepted and
  the composite's delta re-scopes every committed not-yet-accepted
  payload --- dropped-in-flight work is re-driven (branch A below),
  already-accepted work is filtered (branch B).  Between composites,
  in-flight entries are UNRESOLVED (neither delivered nor lost) ---
  the model's first-class rendering of the ambiguous-outcome state.

  THE WITNESS.  The mc-chain continues the p-chain past its first
  fenced recovery: after Resume the application re-commits AT THE SAME
  COORDINATE @{const ec2} --- a landed-legal equal-coordinate re-commit
  (the history append guard is non-strict) --- and publishes it at
  epoch one; the emission @{term "(3, 1, ec2, ev3')"} is a legitimate
  epoch-one in-flight publish.  A second crash and a second fenced
  composite raise the fence to two, so that legitimate epoch-one
  publish is now SUB-FENCE: its later arrival is a drop.  Branch A
  (dropped-but-rescoped): the publish never arrived before crash two
  --- the second composite's delta CONTAINS its payload (committed, in
  replay, not accepted), re-drives it synchronously, and the wire copy
  is fenced out on arrival: exactly once.  Branch B (accepted-before):
  the same publish DID arrive before crash two --- the delta EXCLUDES
  it and appends nothing: again exactly once.  Both branches are
  machine-evaluated on closed records; the mc-chain's source is
  deliberately NOT strictly ascending after the re-commit, so the
  accounting is shown without consuming the ascending premise, and the
  positive theorem's universal form is not invoked here.
\<close>

definition ev3' :: "(nat, nat) source_event" where "ev3' = Insert 1 3"

text \<open>The equal-coordinate three-event history is wellformed --- derived
  through the landed core append lemma, whose guard is non-strict
  (@{term "hist_coord y \<le> hist_coord x"}): the re-commit at
  @{const ec2} is landed-legal.\<close>

lemma wfh_triple_recommit:
  "wellformed_src_history [(ec1, e1), (ec2, e2), (ec2, ev3')]"
proof -
  have "wellformed_src_history ([(ec1, e1), (ec2, e2)] @ [(ec2, ev3')])"
    by (rule wellformed_src_history_append_one[OF wfh_pair])
       (simp add: history_can_append_def ec_defs)
  then show ?thesis by simp
qed

subsection \<open>The inner states of the multi-crash run\<close>

definition mci11 :: "(nat, nat) dwe_state" where
  "mci11 = mkT (mkC [(ec1, e1), (ec2, e2), (ec2, ev3')]
                  [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)] {} Running)
               [(1, 0, ec1, e1), (2, 0, ec2, e2), (2, 0, ec2, e2)] 1"

definition mci12 :: "(nat, nat) dwe_state" where
  "mci12 = mkT (mkC [(ec1, e1), (ec2, e2), (ec2, ev3')]
                  [(ec1, e1), (ec2, e2)]
                  [(ec1, e1), (ec2, e2), (ec2, ev3')] {(ec2, ev3')} Running)
               [(1, 0, ec1, e1), (2, 0, ec2, e2), (2, 0, ec2, e2)] 1"

definition mci13 :: "(nat, nat) dwe_state" where
  "mci13 = mkT (mkC [(ec1, e1), (ec2, e2), (ec2, ev3')]
                  [(ec1, e1), (ec2, e2), (ec2, ev3')]
                  [(ec1, e1), (ec2, e2), (ec2, ev3')] {} Running)
               [(1, 0, ec1, e1), (2, 0, ec2, e2), (2, 0, ec2, e2),
                (3, 1, ec2, ev3')] 1"

definition mci14 :: "(nat, nat) dwe_state" where
  "mci14 = mkT (mkC [(ec1, e1), (ec2, e2), (ec2, ev3')]
                  [(ec1, e1), (ec2, e2), (ec2, ev3')]
                  [(ec1, e1), (ec2, e2), (ec2, ev3')] {} (Crashed ec2))
               [(1, 0, ec1, e1), (2, 0, ec2, e2), (2, 0, ec2, e2),
                (3, 1, ec2, ev3')] 1"

definition mcAi_fin :: "(nat, nat) dwe_state" where
  "mcAi_fin = mkT (mkC [(ec1, e1), (ec2, e2), (ec2, ev3')]
                     [(ec1, e1), (ec2, e2), (ec2, ev3')]
                     [(ec1, e1), (ec2, e2), (ec2, ev3')] {} Recovered)
                  [(1, 0, ec1, e1), (2, 0, ec2, e2), (2, 0, ec2, e2),
                   (3, 1, ec2, ev3'), (3, 1, ec2, ev3')] 1"

definition mcBi_fin :: "(nat, nat) dwe_state" where
  "mcBi_fin = mkT (mkC [(ec1, e1), (ec2, e2), (ec2, ev3')]
                     [(ec1, e1), (ec2, e2), (ec2, ev3')]
                     [(ec1, e1), (ec2, e2), (ec2, ev3')] {} Recovered)
                  [(1, 0, ec1, e1), (2, 0, ec2, e2), (2, 0, ec2, e2),
                   (3, 1, ec2, ev3')] 1"

subsection \<open>The channel states of the multi-crash run\<close>

definition mc11 :: "(nat, nat) dwc_state" where
  "mc11 = mkZ mci11 [(2, 0, ec2, e2)] [(1, 0, ec1, e1), (2, 0, ec2, e2)] 1"

definition mc12 :: "(nat, nat) dwc_state" where
  "mc12 = mkZ mci12 [(2, 0, ec2, e2)] [(1, 0, ec1, e1), (2, 0, ec2, e2)] 1"

definition mc13 :: "(nat, nat) dwc_state" where
  "mc13 = mkZ mci13 [(2, 0, ec2, e2), (3, 1, ec2, ev3')]
            [(1, 0, ec1, e1), (2, 0, ec2, e2)] 1"

definition mc14 :: "(nat, nat) dwc_state" where
  "mc14 = mkZ mci14 [(2, 0, ec2, e2), (3, 1, ec2, ev3')]
            [(1, 0, ec1, e1), (2, 0, ec2, e2)] 1"

definition mcA15 :: "(nat, nat) dwc_state" where
  "mcA15 = mkZ mcAi_fin [(2, 0, ec2, e2), (3, 1, ec2, ev3')]
             [(1, 0, ec1, e1), (2, 0, ec2, e2), (3, 1, ec2, ev3')] 2"

definition mcA_fin :: "(nat, nat) dwc_state" where
  "mcA_fin = mkZ mcAi_fin [(2, 0, ec2, e2)]
               [(1, 0, ec1, e1), (2, 0, ec2, e2), (3, 1, ec2, ev3')] 2"

definition mcB14 :: "(nat, nat) dwc_state" where
  "mcB14 = mkZ mci13 [(2, 0, ec2, e2)]
             [(1, 0, ec1, e1), (2, 0, ec2, e2), (3, 1, ec2, ev3')] 1"

definition mcB15 :: "(nat, nat) dwc_state" where
  "mcB15 = mkZ mci14 [(2, 0, ec2, e2)]
             [(1, 0, ec1, e1), (2, 0, ec2, e2), (3, 1, ec2, ev3')] 1"

definition mcB_fin :: "(nat, nat) dwc_state" where
  "mcB_fin = mkZ mcBi_fin [(2, 0, ec2, e2)]
               [(1, 0, ec1, e1), (2, 0, ec2, e2), (3, 1, ec2, ev3')] 2"

subsection \<open>Wellformedness and admissibility guards\<close>

lemma wf_mci11: "wellformed_exec_state (dwe_core mci11)"
  by (simp add: mci11_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_pair
                wfh_triple_recommit)

lemma wf_mci12: "wellformed_exec_state (dwe_core mci12)"
  by (simp add: mci12_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_pair
                wfh_triple_recommit)

lemma wf_mci13: "wellformed_exec_state (dwe_core mci13)"
  by (simp add: mci13_def mkT_def mkC_def ws_defs wf_hist_Nil
                wfh_triple_recommit)

lemma g_zi10_src_recommit:
  "exec_label_preserves_history_wf (dwe_core zi10) (DoSource ec2 ev3')"
  by (simp add: zi10_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_mci11_enq_recommit:
  "exec_label_preserves_history_wf (dwe_core mci11)
     (EnqueueDownstream ec2 ev3')"
  by (simp add: mci11_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_mci12_down_recommit:
  "exec_label_preserves_history_wf (dwe_core mci12)
     (DoDownstream ec2 ev3')"
  by (simp add: mci12_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_mci13_crash:
  "exec_label_preserves_history_wf (dwe_core mci13) (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

subsection \<open>The inner witness steps\<close>

lemma mi_src_recommit: "dwe_step zi10 (DoSource ec2 ev3') mci11"
proof -
  have c: "dw_exec_step (dwe_core zi10) (DoSource ec2 ev3') (dwe_core mci11)"
    by (rule do_sourceI) (simp_all add: zi10_def mci11_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c])
       (simp_all add: zi10_def mci11_def mkT_def)
qed

lemma mi_enq_recommit: "dwe_step mci11 (EnqueueDownstream ec2 ev3') mci12"
proof -
  have c: "dw_exec_step (dwe_core mci11) (EnqueueDownstream ec2 ev3')
             (dwe_core mci12)"
    by (rule enqueue_downstreamI)
       (simp_all add: mci11_def mci12_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c])
       (simp_all add: mci11_def mci12_def mkT_def)
qed

lemma mi_down_recommit: "dwe_step mci12 (DoDownstream ec2 ev3') mci13"
proof -
  have c: "dw_exec_step (dwe_core mci12) (DoDownstream ec2 ev3')
             (dwe_core mci13)"
    by (rule do_downstreamI)
       (simp_all add: mci12_def mci13_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_publish_emitI[OF c])
       (simp add: mci12_def mci13_def mkT_def mkC_def eval_nat_numeral)
qed

lemma mi_crash_recommit: "dwe_step mci13 (Crash ec2) mci14"
proof -
  have c: "dw_exec_step (dwe_core mci13) (Crash ec2) (dwe_core mci14)"
    by (rule crashI) (simp_all add: mci13_def mci14_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c])
       (simp_all add: mci13_def mci14_def mkT_def)
qed

subsection \<open>The shared prefix: re-commit, publish, crash\<close>

lemma mcs11: "dwc_step p10 (DoSource ec2 ev3') mc11"
proof -
  have i: "dwe_step (dwc_inner p10) (DoSource ec2 ev3') mci11"
    using mi_src_recommit by (simp add: p10_def)
  show ?thesis
    by (rule dwc_lift_nonpubI[OF i]) (simp_all add: p10_def mc11_def mkZ_def)
qed

lemma mcs12: "dwc_step mc11 (EnqueueDownstream ec2 ev3') mc12"
proof -
  have i: "dwe_step (dwc_inner mc11) (EnqueueDownstream ec2 ev3') mci12"
    using mi_enq_recommit by (simp add: mc11_def)
  show ?thesis
    by (rule dwc_lift_nonpubI[OF i]) (simp_all add: mc11_def mc12_def mkZ_def)
qed

lemma mcs13: "dwc_step mc12 (DoDownstream ec2 ev3') mc13"
proof -
  have i: "dwe_step (dwc_inner mc12) (DoDownstream ec2 ev3') mci13"
    using mi_down_recommit by (simp add: mc12_def)
  show ?thesis
    by (rule dwc_send_pubI[OF i])
       (simp add: mc12_def mc13_def mkZ_def mci12_def mkT_def mkC_def
                  dwc_src_def eval_nat_numeral)
qed

lemma mcs14: "dwc_step mc13 (Crash ec2) mc14"
proof -
  have i: "dwe_step (dwc_inner mc13) (Crash ec2) mci14"
    using mi_crash_recommit by (simp add: mc13_def)
  show ?thesis
    by (rule dwc_lift_nonpubI[OF i]) (simp_all add: mc13_def mc14_def mkZ_def)
qed

lemma reach_mc11: "dwc_reachable mc11"
  by (rule dwc_reachable_label_ext[OF reach_p10 _ _ mcs11])
     (simp_all add: p10_def wf_zi10 g_zi10_src_recommit)

lemma reach_mc12: "dwc_reachable mc12"
  by (rule dwc_reachable_label_ext[OF reach_mc11 _ _ mcs12])
     (simp_all add: mc11_def wf_mci11 g_mci11_enq_recommit)

lemma reach_mc13: "dwc_reachable mc13"
  by (rule dwc_reachable_label_ext[OF reach_mc12 _ _ mcs13])
     (simp_all add: mc12_def wf_mci12 g_mci12_down_recommit)

lemma reach_mc14: "dwc_reachable mc14"
  by (rule dwc_reachable_label_ext[OF reach_mc13 _ _ mcs14])
     (simp_all add: mc13_def wf_mci13 g_mci13_crash)

subsection \<open>Branch A: dropped but re-scoped\<close>

text \<open>The second composite at crash epoch one: the delta computes to
  exactly the never-accepted payload of the in-flight epoch-one
  publish; the fence rises to two.\<close>

lemma mcA_delta: "dwc_sink_delta ec2 mc14 = [(ec2, ev3')]"
  by (simp add: dwc_sink_delta_def dwc_replay_def dwc_src_def dwc_scope_def
                replay_down_hist_def mc14_def mkZ_def mci14_def mkT_def
                mkC_def e1_def e2_def ev3'_def ec_defs)

lemma mcA_fen: "dwc_fenced_redrive ec2 mc14 mcA15"
  by (rule dwc_fenced_redriveI)
     (simp_all add: mc14_def mcA15_def mkZ_def mci14_def mcAi_fin_def
                    mkT_def mkC_def dwc_sink_delta_def dwc_replay_def
                    dwc_src_def dwc_scope_def replay_down_hist_def e1_def
                    e2_def ev3'_def ec_defs eval_nat_numeral)

text \<open>The fenced-out arrival: the legitimate epoch-one wire copy meets
  fence two and is dropped --- its payload is already in the accepted
  record, put there by the re-scoping delta.\<close>

lemma mcA_drop: "dwc_arrive mcA15 1 mcA_fin"
  by (rule dwc_arrive_dropI)
     (simp_all add: mcA15_def mcA_fin_def mkZ_def eval_nat_numeral)

lemma reach_mcA15: "dwc_reachable mcA15"
  by (rule dwc_reachable_fenced_ext[OF reach_mc14 mcA_fen])

lemma reach_mcA_fin: "dwc_reachable mcA_fin"
  by (rule dwc_reachable_arrive_ext[OF reach_mcA15 mcA_drop])

lemma mcA_fin_eo: "dwc_eo_at ec2 mcA_fin"
  by (simp add: dwc_eo_at_def dwc_accepted_unsafe_def
                dwc_accepted_premature_def dwc_accepted_duplicate_def
                dwc_alo_at_def justified_at_def dwc_replay_def dwc_src_def
                dwc_scope_def replay_down_hist_def mcA_fin_def mkZ_def
                mcAi_fin_def mkT_def mkC_def e1_def e2_def ev3'_def ec_defs
                eval_nat_numeral)

lemma mcA_fin_count:
  "count_list (map e_payload (dwc_accepted mcA_fin)) (ec2, ev3') = 1"
  by (simp add: mcA_fin_def mkZ_def e1_def e2_def ev3'_def ec_defs)

subsection \<open>Branch B: accepted before the second crash\<close>

text \<open>The same in-flight publish arrives BEFORE crash two (epoch one
  clears fence one), the crash and the second composite follow, and the
  delta excludes the already-accepted payload: it appends nothing.\<close>

lemma mcB_arr: "dwc_arrive mc13 1 mcB14"
  by (rule dwc_arrive_acceptI)
     (simp_all add: mc13_def mcB14_def mkZ_def eval_nat_numeral)

lemma mcB_crash: "dwc_step mcB14 (Crash ec2) mcB15"
proof -
  have i: "dwe_step (dwc_inner mcB14) (Crash ec2) mci14"
    using mi_crash_recommit by (simp add: mcB14_def)
  show ?thesis
    by (rule dwc_lift_nonpubI[OF i])
       (simp_all add: mcB14_def mcB15_def mkZ_def)
qed

lemma mcB_delta: "dwc_sink_delta ec2 mcB15 = []"
  by (simp add: dwc_sink_delta_def dwc_replay_def dwc_src_def dwc_scope_def
                replay_down_hist_def mcB15_def mkZ_def mci14_def mkT_def
                mkC_def e1_def e2_def ev3'_def ec_defs)

lemma mcB_fen: "dwc_fenced_redrive ec2 mcB15 mcB_fin"
  by (rule dwc_fenced_redriveI)
     (simp_all add: mcB15_def mcB_fin_def mkZ_def mci14_def mcBi_fin_def
                    mkT_def mkC_def dwc_sink_delta_def dwc_replay_def
                    dwc_src_def dwc_scope_def replay_down_hist_def e1_def
                    e2_def ev3'_def ec_defs eval_nat_numeral)

lemma reach_mcB14: "dwc_reachable mcB14"
  by (rule dwc_reachable_arrive_ext[OF reach_mc13 mcB_arr])

lemma reach_mcB15: "dwc_reachable mcB15"
  by (rule dwc_reachable_label_ext[OF reach_mcB14 _ _ mcB_crash])
     (simp_all add: mcB14_def wf_mci13 g_mci13_crash)

lemma reach_mcB_fin: "dwc_reachable mcB_fin"
  by (rule dwc_reachable_fenced_ext[OF reach_mcB15 mcB_fen])

lemma mcB_fin_eo: "dwc_eo_at ec2 mcB_fin"
  by (simp add: dwc_eo_at_def dwc_accepted_unsafe_def
                dwc_accepted_premature_def dwc_accepted_duplicate_def
                dwc_alo_at_def justified_at_def dwc_replay_def dwc_src_def
                dwc_scope_def replay_down_hist_def mcB_fin_def mkZ_def
                mcBi_fin_def mkT_def mkC_def e1_def e2_def ev3'_def ec_defs
                eval_nat_numeral)

lemma mcB_fin_count:
  "count_list (map e_payload (dwc_accepted mcB_fin)) (ec2, ev3') = 1"
  by (simp add: mcB_fin_def mkZ_def e1_def e2_def ev3'_def ec_defs)

theorem second_fence_drop_rescoped:
  "\<comment> \<open>branch A (dropped-but-rescoped): the in-flight epoch-one publish never
      arrived before crash two --- composite two's delta CONTAINS its payload,
      re-drives it synchronously, and the wire copy is fenced out on arrival:
      the accepted record carries the payload EXACTLY ONCE and the
      exactly-once verdict holds at composite two's result and after the drop.\<close>
   dwc_eo_at ec2 mcA_fin
 \<and> count_list (map e_payload (dwc_accepted mcA_fin)) (ec2, ev3') = 1
 \<and> \<comment> \<open>branch B (accepted-before): the same publish DID arrive before crash two
      --- composite two's delta EXCLUDES it (already accepted) and appends
      nothing for it: again exactly once.\<close>
   dwc_eo_at ec2 mcB_fin
 \<and> count_list (map e_payload (dwc_accepted mcB_fin)) (ec2, ev3') = 1"
  by (intro conjI mcA_fin_eo mcA_fin_count mcB_fin_eo mcB_fin_count)

section \<open>The loss bonus: a fenced re-drive heals a lost send\<close>

text \<open>
  The accepted-record delta is LOSS-OBLIVIOUS by construction: it
  filters replay against the accepted record only, so it cannot and
  need not distinguish a never-arrived send from a dropped or LOST one.
  The l-chain loses the in-flight second publish on the wire (the
  fold-in loss rule), crashes, and runs the fenced composite: the delta
  is exactly the missing effect, the record is healed, exactly-once
  holds at the frontier.  The landed SENT-reading delta would compute
  EMPTY here --- the lost send is in the sent ledger --- and lose the
  effect at the frontier: that contrast is the divergence theorem
  below.
\<close>

definition l8 :: "(nat, nat) dwc_state" where
  "l8 = mkZ zi7 [] [(1, 0, ec1, e1)] 0"

definition l9 :: "(nat, nat) dwc_state" where
  "l9 = mkZ zi8 [] [(1, 0, ec1, e1)] 0"

definition lf :: "(nat, nat) dwc_state" where
  "lf = mkZ zi9 [] [(1, 0, ec1, e1), (2, 0, ec2, e2)] 1"

text \<open>The wire loses the in-flight second publish; the producer, still
  Running, crashes only afterwards.\<close>

lemma lls8: "dwc_lose z7 0 l8"
  by (rule dwc_loseI) (simp_all add: z7_def l8_def mkZ_def)

lemma lls9: "dwc_step l8 (Crash ec2) l9"
proof -
  have i: "dwe_step (dwc_inner l8) (Crash ec2) zi8"
    using zi_crash by (simp add: l8_def)
  show ?thesis
    by (rule dwc_lift_nonpubI[OF i]) (simp_all add: l8_def l9_def mkZ_def)
qed

text \<open>What the recovery reads at the crash state with the lost send:
  the replay holds both committed events, the accepted record holds
  event one only --- the delta is exactly the missing effect, whether
  its send was lost, dropped, or never resolved.\<close>

lemma l9_delta: "dwc_sink_delta ec2 l9 = [(ec2, e2)]"
  by (simp add: dwc_sink_delta_def dwc_replay_def dwc_src_def dwc_scope_def
                replay_down_hist_def l9_def mkZ_def zi8_def mkT_def mkC_def
                e1_def e2_def ec_defs)

lemma lfen: "dwc_fenced_redrive ec2 l9 lf"
  by (rule dwc_fenced_redriveI)
     (simp_all add: l9_def lf_def mkZ_def zi8_def zi9_def mkT_def mkC_def
                    dwc_sink_delta_def dwc_replay_def dwc_src_def
                    dwc_scope_def replay_down_hist_def e1_def e2_def ec_defs
                    eval_nat_numeral)

lemma reach_l8: "dwc_reachable l8"
  by (rule dwc_reachable_lose_ext[OF reach_z7 lls8])

lemma reach_l9: "dwc_reachable l9"
  by (rule dwc_reachable_label_ext[OF reach_l8 _ _ lls9])
     (simp_all add: l8_def wf_zi7 g_zi7_crash)

lemma reach_lf: "dwc_reachable lf"
  by (rule dwc_reachable_fenced_ext[OF reach_l9 lfen])

lemma lf_eo: "dwc_eo_at ec2 lf"
  by (simp add: dwc_eo_at_def dwc_accepted_unsafe_def
                dwc_accepted_premature_def dwc_accepted_duplicate_def
                dwc_alo_at_def justified_at_def dwc_replay_def dwc_src_def
                dwc_scope_def replay_down_hist_def lf_def mkZ_def zi9_def
                mkT_def mkC_def e1_def e2_def ec_defs eval_nat_numeral)

lemma lf_count:
  "count_list (map e_payload (dwc_accepted lf)) (ec2, e2) = 1"
  by (simp add: lf_def mkZ_def e1_def e2_def ec_defs)

theorem fenced_redrive_heals_lost_send:
  "dwc_reachable lf \<and> dwc_eo_at ec2 lf
 \<and> count_list (map e_payload (dwc_accepted lf)) (ec2, e2) = 1"
  by (intro conjI reach_lf lf_eo lf_count)

section \<open>Owning the re-reading: the sent and accepted verdicts diverge\<close>

text \<open>
  At the healed loss state the SENT ledger holds the payload twice (the
  lost send and the re-drive), while the ACCEPTED record holds it once.
  Both verdicts are true of their own records: the landed sent-side
  @{const effect_unsafe} is a real fact of the inner (and persists, by
  the slice-1 lifted monotonicity), and the machine's accepted-side
  exactly-once is a real fact of the sink's durable record.  The third
  conjunct is the contrast that makes the re-reading LOAD-BEARING: the
  landed wire-omniscient @{const sink_delta} computes EMPTY at this
  state --- it would re-drive nothing, and the effect would be lost at
  the frontier.  The modelling choice (hazards move to the accepted
  record) is thereby owned as a theorem-visible divergence, not buried
  prose: the variant discloses which record the sink's contract lives
  on.
\<close>

lemma lf_sent_unsafe: "effect_unsafe (dwc_inner lf)"
  by (simp add: effect_unsafe_def duplicate_def lf_def mkZ_def zi9_def
                mkT_def mkC_def e1_def e2_def ec_defs)

lemma lf_landed_delta_empty: "sink_delta ec2 (dwc_inner lf) = []"
  by (simp add: sink_delta_def replay_down_hist_def lf_def mkZ_def zi9_def
                mkT_def mkC_def e1_def e2_def ec_defs)

theorem sent_accepted_verdicts_diverge:
  "dwc_reachable lf
 \<and> effect_unsafe (dwc_inner lf)
     \<comment> \<open>the landed sent-side verdict: duplicate\<close>
 \<and> dwc_eo_at ec2 lf
     \<comment> \<open>the machine's accepted-side verdict: exactly-once\<close>
 \<and> sink_delta ec2 (dwc_inner lf) = []
     \<comment> \<open>the landed SENT-reading delta is empty here: a wire-omniscient
        reading would re-drive nothing and the effect would be lost at the
        frontier\<close>"
  by (intro conjI reach_lf lf_sent_unsafe lf_eo lf_landed_delta_empty)

section \<open>The rescue conversion: what the fence costs at the wire (gate amendment MF-8)\<close>

text \<open>
  THE COST SIDE OF THE FENCE, exhibited as a minimal pair.  Both chains
  share the zombie prefix to the crash state and then recover
  UNDER-SCOPED: the recovery frontier is @{const ec1}, strictly below
  the committed second event at @{const ec2}, so the delta at the
  recovery's own frontier is EMPTY on both sides --- the recovery
  re-drives nothing, and the in-flight second publish is the only copy
  of its payload anywhere.  The unfenced chain (@{term "DWC_Escape
  ec1"}): the straggler ARRIVES at the never-raised fence zero and
  RESCUES the record --- exactly-once at @{const ec2} holds at the end
  state, by wire luck, not by the recovery's doing.  The fenced twin
  (@{term "DWC_Fenced ec1"}), same schedule: the SAME straggler is
  DROPPED at fence one --- certain loss at @{const ec2}, while the
  fenced guarantee holds exactly at ITS OWN frontier @{const ec1}.
  One action constructor is the entire difference.

  This is the frontier qualification made vivid, and the honest
  pricing of the fence: it converts the wire's late-arrival rescue
  into a certain drop when the recovery under-scopes ---
  duplicate-or-lose at the wire.  The fenced guarantee is exact AT the
  frontier the recovery chose; it neither claims nor delivers anything
  beyond it.
\<close>

text \<open>The under-scoped recovery's inner result: the heal is scoped to
  @{const ec1} (the downstream history rewinds to the replay at the
  under-scoped frontier), the delta is empty, the sent ledger is
  unchanged.  Shared by both chains --- the composites differ in the
  fence field alone.\<close>

definition ui9 :: "(nat, nat) dwe_state" where
  "ui9 = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1)]
                [(ec1, e1), (ec2, e2)] {} Recovered)
             [(1, 0, ec1, e1), (2, 0, ec2, e2)] 0"

definition ui10 :: "(nat, nat) dwe_state" where
  "ui10 = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1)]
                 [(ec1, e1), (ec2, e2)] {} Running)
              [(1, 0, ec1, e1), (2, 0, ec2, e2)] 1"

definition u9 :: "(nat, nat) dwc_state" where
  "u9 = mkZ ui9 [(2, 0, ec2, e2)] [(1, 0, ec1, e1)] 0"

definition u10 :: "(nat, nat) dwc_state" where
  "u10 = mkZ ui10 [(2, 0, ec2, e2)] [(1, 0, ec1, e1)] 0"

definition u_fin :: "(nat, nat) dwc_state" where
  "u_fin = mkZ ui10 [] [(1, 0, ec1, e1), (2, 0, ec2, e2)] 0"

definition f9 :: "(nat, nat) dwc_state" where
  "f9 = mkZ ui9 [(2, 0, ec2, e2)] [(1, 0, ec1, e1)] 1"

definition f10 :: "(nat, nat) dwc_state" where
  "f10 = mkZ ui10 [(2, 0, ec2, e2)] [(1, 0, ec1, e1)] 1"

definition f_fin :: "(nat, nat) dwc_state" where
  "f_fin = mkZ ui10 [] [(1, 0, ec1, e1)] 1"

text \<open>The under-scoped delta is empty on both sides: the replay at
  @{const ec1} is the first event alone, and it is already accepted.\<close>

lemma z8_delta_ec1: "dwc_sink_delta ec1 z8 = []"
  by (simp add: dwc_sink_delta_def dwc_replay_def dwc_src_def dwc_scope_def
                replay_down_hist_def z8_def mkZ_def zi8_def mkT_def mkC_def
                e1_def e2_def ec_defs)

subsection \<open>The unfenced chain: the straggler rescues\<close>

lemma uesc9: "dwc_escape_redrive ec1 z8 u9"
  by (rule dwc_escape_redriveI)
     (simp_all add: z8_def u9_def mkZ_def zi8_def ui9_def mkT_def mkC_def
                    dwc_sink_delta_def dwc_replay_def dwc_src_def
                    dwc_scope_def replay_down_hist_def e1_def e2_def ec_defs
                    eval_nat_numeral)

lemma ures10: "dwc_resume_lift u9 u10"
proof -
  have i: "dwe_resume (dwc_inner u9) ui10"
    by (simp add: u9_def dwe_resume_def ui9_def ui10_def mkT_def mkC_def
                  eval_nat_numeral)
  show ?thesis
    by (rule dwc_resume_liftI[OF i]) (simp add: u9_def u10_def mkZ_def)
qed

lemma us_fin: "dwc_arrive u10 0 u_fin"
  by (rule dwc_arrive_acceptI) (simp_all add: u10_def u_fin_def mkZ_def)

lemma reach_u9: "dwc_reachable u9"
  by (rule dwc_reachable_escape_ext[OF reach_z8 uesc9])

lemma reach_u10: "dwc_reachable u10"
  by (rule dwc_reachable_resume_ext[OF reach_u9 ures10])

lemma reach_u_fin: "dwc_reachable u_fin"
  by (rule dwc_reachable_arrive_ext[OF reach_u10 us_fin])

lemma u_fin_eo: "dwc_eo_at ec2 u_fin"
  by (simp add: dwc_eo_at_def dwc_accepted_unsafe_def
                dwc_accepted_premature_def dwc_accepted_duplicate_def
                dwc_alo_at_def justified_at_def dwc_replay_def dwc_src_def
                dwc_scope_def replay_down_hist_def u_fin_def mkZ_def
                ui10_def mkT_def mkC_def e1_def e2_def ec_defs
                eval_nat_numeral)

lemma u_fin_count:
  "count_list (map e_payload (dwc_accepted u_fin)) (ec2, e2) = 1"
  by (simp add: u_fin_def mkZ_def e1_def e2_def ec_defs)

subsection \<open>The fenced twin: the same straggler is dropped\<close>

lemma ffen9: "dwc_fenced_redrive ec1 z8 f9"
  by (rule dwc_fenced_redriveI)
     (simp_all add: z8_def f9_def mkZ_def zi8_def ui9_def mkT_def mkC_def
                    dwc_sink_delta_def dwc_replay_def dwc_src_def
                    dwc_scope_def replay_down_hist_def e1_def e2_def ec_defs
                    eval_nat_numeral)

lemma fres10: "dwc_resume_lift f9 f10"
proof -
  have i: "dwe_resume (dwc_inner f9) ui10"
    by (simp add: f9_def dwe_resume_def ui9_def ui10_def mkT_def mkC_def
                  eval_nat_numeral)
  show ?thesis
    by (rule dwc_resume_liftI[OF i]) (simp add: f9_def f10_def mkZ_def)
qed

lemma fs_fin: "dwc_arrive f10 0 f_fin"
  by (rule dwc_arrive_dropI) (simp_all add: f10_def f_fin_def mkZ_def)

lemma reach_f9: "dwc_reachable f9"
  by (rule dwc_reachable_fenced_ext[OF reach_z8 ffen9])

lemma reach_f10: "dwc_reachable f10"
  by (rule dwc_reachable_resume_ext[OF reach_f9 fres10])

lemma reach_f_fin: "dwc_reachable f_fin"
  by (rule dwc_reachable_arrive_ext[OF reach_f10 fs_fin])

lemma f_fin_not_alo: "\<not> dwc_alo_at ec2 f_fin"
  by (simp add: dwc_alo_at_def dwc_replay_def dwc_src_def dwc_scope_def
                replay_down_hist_def f_fin_def mkZ_def ui10_def mkT_def
                mkC_def e1_def e2_def ec_defs)

lemma f_fin_payload_absent:
  "(ec2, e2) \<notin> e_payload ` set (dwc_accepted f_fin)"
  by (simp add: f_fin_def mkZ_def e1_def e2_def ec_defs)

lemma f_fin_eo_own_frontier: "dwc_eo_at ec1 f_fin"
  by (simp add: dwc_eo_at_def dwc_accepted_unsafe_def
                dwc_accepted_premature_def dwc_accepted_duplicate_def
                dwc_alo_at_def justified_at_def dwc_replay_def dwc_src_def
                dwc_scope_def replay_down_hist_def f_fin_def mkZ_def
                ui10_def mkT_def mkC_def e1_def e2_def ec_defs
                eval_nat_numeral)

theorem fence_rescue_conversion:
  "dwc_reachable u_fin \<and> dwc_eo_at ec2 u_fin
 \<and> count_list (map e_payload (dwc_accepted u_fin)) (ec2, e2) = 1
     \<comment> \<open>unfenced under-scoped recovery (\<open>DWC_Escape ec1\<close>): the straggler ARRIVES and RESCUES\<close>
 \<and> dwc_reachable f_fin \<and> \<not> dwc_alo_at ec2 f_fin
 \<and> (ec2, e2) \<notin> e_payload ` set (dwc_accepted f_fin)
     \<comment> \<open>fenced twin (\<open>DWC_Fenced ec1\<close>), same schedule: the same straggler is DROPPED --- certain loss at ec2\<close>
 \<and> dwc_eo_at ec1 f_fin
     \<comment> \<open>the fenced guarantee is exact at ITS OWN frontier --- the frontier qualification made vivid\<close>"
  by (intro conjI reach_u_fin u_fin_eo u_fin_count reach_f_fin f_fin_not_alo
            f_fin_payload_absent f_fin_eo_own_frontier)

end
