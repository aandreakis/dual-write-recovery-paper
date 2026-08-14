(*  Title:       Dual_Write_Effect_Dichotomy.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Referee-proofing additions over the frozen Dual_Write_Effect corpus
    (the C2 micro-slice recommended by the S6 review, section C) ---
    ADDITIVE under the freeze's own protocol: no landed statement, proof,
    definition, name, import, or session-DAG change.  Everything here is
    assembled from banked facts; the landed theorems are cited, not
    re-proved.  Three pieces:

    1.  disciplined_pair_reachable: BOTH members of the landed dilemma
        pair (d1_w, d2_w) are reached by fully T2.8-DISCIPLINED traces
        from the pinned initial state --- the two traces differ in the
        reconcile's persisted cursor alone (m = 1 vs m = 2).  The pair is
        not an artifact of an undisciplined scheduler: a run that obeys
        every discipline guard still presents the equal-core, equal-epoch,
        divergent-ledger pair to its recovery.

    2.  ledger_blind + ledger_blind_iff_store_epoch_measured: a policy
        whose batch cannot distinguish states differing at most in the
        emission ledger is EXACTLY a (core, epoch)-measured policy.  The
        wrapper record has exactly three fields (dwe_state_fields_eqI is
        the formal carrier of "exactly three"), so "does not read the
        ledger" and "factors through (core, epoch)" coincide.

    3.  redrive_policy_dichotomy + exactly_once_recovery_dichotomy: the
        literally exhaustive case split over ALL re-drive policies on the
        pinned witness machine.  Every policy either is ledger-blind ---
        equivalently (core, epoch)-measured, and then the landed dilemma
        theorems defeat it on the designed-in pair (the exactly-once form
        cites the landed necessity face over the frontier-relative
        exactly_once_at, whose delivery-completeness conjunct is the
        disclosed terminal-state liveness stand-in) --- or its output
        distinguishes two states that agree on the whole durable core and
        the recovery epoch and differ in the emission ledger: it reads
        the sink.  Both horns are witnessed inhabited (the banked cursor
        policy; the landed sink_delta).

    Import note: the single import Dual_Write_Effect_Exactly_Once
    transitively provides Dual_Write_Effect_Dilemma and
    Dual_Write_Effect_Discipline; it is consumed directly by the
    exactly-once dichotomy (the landed necessity face).  The terminal
    branch (Machine/Witnesses) is deliberately NOT in the import cone.

    The scratch original's in-source ML oracle gates are STRIPPED here:
    oracle-freedom is certified by scratch-side per-slice gate sessions
    with confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Dichotomy
  imports Dual_Write_Effect_Exactly_Once
begin

section \<open>The dilemma pair is reachable under the full T2.8 discipline\<close>

text \<open>
  The landed pair @{const d1_w} / @{const d2_w} was banked through plain
  reachability (@{thm [source] reach_d1}, @{thm [source] reach_d2}).
  Here both endpoints are re-derived through @{const disciplined_trace}
  --- every publish fire-time justified and ledger-fresh, every reconcile
  suffix ledger-fresh and internally distinct, Resume guard-free --- from
  the pinned initial state.  The two action lists are identical except
  for the reconcile's persisted cursor: m = 1 re-drives the missing
  effect (the safe member's route), m = 2 re-drives nothing (the skip
  member's route).  Effect safety of both endpoints is exactly what T2.8
  (@{thm [source] general_positive_discipline_pinned}) predicts, and
  agrees with the banked point evaluations
  (@{thm [source] d1_not_unsafe}, @{thm [source] d2_not_unsafe});
  reachability of both is recovered via
  @{thm [source] disciplined_runs_are_reachable}, matching the banked
  facts.
\<close>

lemma disciplined_to_mid:
  "disciplined_trace W0 (map DWE_Label witness_labels) t_mid_w"
  using disciplined_trace_append[OF dv_sg1
          disciplined_trace_append[OF dv_sg2
            disciplined_trace_append[OF dv_sg3
              disciplined_trace_append[OF dv_sg4
                disciplined_trace_append[OF dv_sg5 dv_sg6]]]]]
  by (simp add: witness_labels_def)

text \<open>
  The skip member's reconcile guard holds VACUOUSLY: the m = 2 cursor
  drops the whole 2-element replay, so the re-driven suffix is empty and
  both guard conjuncts are trivial.  The guard governs what is RE-DRIVEN;
  it cannot see the skip.  That axis is the machine's disclosed skip
  asymmetry, costed by the landed T2.11 skip controls, not here.
\<close>

lemma disciplined_skip_reconcile:
  "disciplined_trace t_mid_w [DWE_Reconcile 2 ec2] t_skip_w"
  by (rule disciplined_reconcile_singleI[OF rec_skip])
     (simp_all add: t_mid_w_def mkT_def mkC_def replay_down_hist_def
                    e1_def e2_def ec_defs eval_nat_numeral)

lemma disciplined_crash_d1:
  "disciplined_trace r_safe_w [DWE_Label (Crash ec2)] d1_w"
  by (rule disciplined_nonpub_singleI[OF crash_d1 wf_r_safe g_r_safe_crash])
     simp

lemma disciplined_crash_d2:
  "disciplined_trace r_skip_w [DWE_Label (Crash ec2)] d2_w"
  by (rule disciplined_nonpub_singleI[OF crash_d2 wf_r_skip g_r_skip_crash])
     simp

theorem disciplined_pair_reachable:
  "disciplined_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
     (map DWE_Label witness_labels
      @ [DWE_Reconcile 1 ec2, DWE_Resume, DWE_Label (Crash ec2)]) d1_w
 \<and> disciplined_trace (dwe_init (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2)
     (map DWE_Label witness_labels
      @ [DWE_Reconcile 2 ec2, DWE_Resume, DWE_Label (Crash ec2)]) d2_w
 \<and> dwe_core d1_w = dwe_core d2_w
 \<and> dwe_epoch d1_w = dwe_epoch d2_w
 \<and> dwe_emitted d1_w \<noteq> dwe_emitted d2_w
 \<and> \<not> effect_unsafe d1_w \<and> \<not> effect_unsafe d2_w
 \<and> genuinely_emitting d1_w \<and> genuinely_emitting d2_w"
proof -
  have a1: "disciplined_trace W0
     (map DWE_Label witness_labels
      @ [DWE_Reconcile 1 ec2, DWE_Resume, DWE_Label (Crash ec2)]) d1_w"
    using disciplined_trace_append[OF disciplined_to_mid
            disciplined_trace_append[OF dv_sg7
              disciplined_trace_append[OF
                disciplined_resume_singleI[OF res_safe]
                disciplined_crash_d1]]]
    by simp
  have a2: "disciplined_trace W0
     (map DWE_Label witness_labels
      @ [DWE_Reconcile 2 ec2, DWE_Resume, DWE_Label (Crash ec2)]) d2_w"
    using disciplined_trace_append[OF disciplined_to_mid
            disciplined_trace_append[OF disciplined_skip_reconcile
              disciplined_trace_append[OF
                disciplined_resume_singleI[OF res_skip]
                disciplined_crash_d2]]]
    by simp
  have ep: "dwe_epoch d1_w = dwe_epoch d2_w"
    by (simp add: d1_fields d2_fields)
  show ?thesis
    using a1 a2 d_cores_eq ep d_emitted_neq d1_not_unsafe d2_not_unsafe
          d1_emitting d2_emitting
    unfolding W0_init by blast
qed

section \<open>Ledger-blindness is (core, epoch)-measurability\<close>

text \<open>
  The wrapper record has EXACTLY three fields: the durable core, the
  emission ledger, and the recovery epoch.  The extensionality lemma is
  the formal carrier of "exactly three": two wrapper states agreeing on
  all three fields are equal --- there is no fourth component a policy
  could read.
\<close>

lemma dwe_state_fields_eqI:
  fixes t t' :: "('k, 'v) dwe_state"
  assumes "dwe_core t = dwe_core t'"
      and "dwe_emitted t = dwe_emitted t'"
      and "dwe_epoch t = dwe_epoch t'"
  shows "t = t'"
  by (rule dwe_state.equality) (simp_all add: assms)

text \<open>
  Ledger-blindness, stated honestly: the policy's batch cannot
  distinguish two states that agree on the durable core and the recovery
  epoch (hence differ at most in the emission ledger).  Pinned at the
  witness instantiation, like the landed policy classes.
\<close>

definition ledger_blind :: "redrive_policy \<Rightarrow> bool" where
  "ledger_blind P \<longleftrightarrow>
     (\<forall>t t'. dwe_core t = dwe_core t' \<and> dwe_epoch t = dwe_epoch t'
             \<longrightarrow> P t = P t')"

text \<open>
  THE BRIDGE: ledger-blindness IS the landed
  @{const store_epoch_measured} --- an iff, not a containment.  Forward,
  the measuring function evaluates the policy at a canonical state
  carrying an empty ledger; backward is substitution.
\<close>

theorem ledger_blind_iff_store_epoch_measured:
  "ledger_blind P \<longleftrightarrow> store_epoch_measured P"
proof
  assume lb: "ledger_blind P"
  define g where "g = (\<lambda>c ep. P (mkT c [] ep))"
  have key: "\<forall>t. P t = g (dwe_core t) (dwe_epoch t)"
  proof
    fix t :: "(nat, nat) dwe_state"
    have "P t = P (mkT (dwe_core t) [] (dwe_epoch t))"
      by (rule lb[unfolded ledger_blind_def, rule_format])
         (simp add: mkT_def)
    then show "P t = g (dwe_core t) (dwe_epoch t)"
      by (simp add: g_def)
  qed
  show "store_epoch_measured P"
    unfolding store_epoch_measured_def
    by (intro exI[of _ g]) (rule key)
next
  assume "store_epoch_measured P"
  then obtain g where g: "\<forall>t. P t = g (dwe_core t) (dwe_epoch t)"
    unfolding store_epoch_measured_def by blast
  show "ledger_blind P"
    unfolding ledger_blind_def
  proof (intro allI impI)
    fix t t' :: "(nat, nat) dwe_state"
    assume "dwe_core t = dwe_core t' \<and> dwe_epoch t = dwe_epoch t'"
    then show "P t = P t'"
      using g by metis
  qed
qed

section \<open>The dichotomy: ledger-blind (defeated) or reads the sink\<close>

text \<open>
  A policy that is NOT ledger-blind distinguishes two states that agree
  on the core and the epoch --- by three-field extensionality those
  states differ in the emission ledger, so the policy's output depends
  on the ledger: it reads the sink.
\<close>

lemma not_ledger_blind_distinguishes_ledger:
  assumes "\<not> ledger_blind P"
  shows "\<exists>t t'. dwe_core t = dwe_core t' \<and> dwe_epoch t = dwe_epoch t'
              \<and> dwe_emitted t \<noteq> dwe_emitted t' \<and> P t \<noteq> P t'"
proof -
  from assms obtain t t' where ceq: "dwe_core t = dwe_core t'"
      and eeq: "dwe_epoch t = dwe_epoch t'" and pneq: "P t \<noteq> P t'"
    unfolding ledger_blind_def by blast
  have "dwe_emitted t \<noteq> dwe_emitted t'"
  proof
    assume em: "dwe_emitted t = dwe_emitted t'"
    have "t = t'" by (rule dwe_state_fields_eqI[OF ceq em eeq])
    with pneq show False by simp
  qed
  with ceq eeq pneq show ?thesis by blast
qed

text \<open>
  THE STRUCTURAL DICHOTOMY, literally exhaustive over all re-drive
  policies: every policy is (core, epoch)-measured --- the class the
  landed @{thm [source] epoch_measured_dilemma} defeats on the
  designed-in pair --- or distinguishes some ledger behind an equal
  (core, epoch) front.  Naming note: the S6 review sketched this
  corollary as "@{text reachable_store_measured}"; that name matches neither a
  reachability quantification (there is none here) nor the epoch
  extension actually proved, so the theorem is named for its content.
\<close>

theorem redrive_policy_dichotomy:
  fixes P :: redrive_policy
  shows "store_epoch_measured P
       \<or> (\<exists>t t'. dwe_core t = dwe_core t' \<and> dwe_epoch t = dwe_epoch t'
                \<and> dwe_emitted t \<noteq> dwe_emitted t' \<and> P t \<noteq> P t')"
proof (cases "ledger_blind P")
  case True
  then show ?thesis
    by (simp add: ledger_blind_iff_store_epoch_measured)
next
  case False
  show ?thesis
    by (rule disjI2) (rule not_ledger_blind_distinguishes_ledger[OF False])
qed

text \<open>
  The exactly-once reading, with the defeat inlined: every re-drive
  policy either is (core, epoch)-measured AND fails frontier-relative
  exactly-once recovery on the designed-in pair (the landed necessity
  face @{thm [source] no_store_epoch_measured_exactly_once_recovery},
  cited with its body verbatim --- @{const exactly_once_at} is
  frontier-relative and its delivery-completeness conjunct is the
  disclosed terminal-state liveness stand-in), or it reads the sink.
  Together with the landed positive side
  (@{thm [source] sink_delta_achieves_exactly_once}): exactly-once
  effect recovery exists and requires reading the sink --- as ONE
  exhaustive case split instead of a three-theorem juxtaposition.
\<close>

theorem exactly_once_recovery_dichotomy:
  fixes P :: redrive_policy
  shows
  "(store_epoch_measured P
    \<and> (\<exists>t1 t2 t1' t2'.
         dwe_reachable t1 \<and> dwe_reachable t2
       \<and> dwe_core t1 = dwe_core t2
       \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
       \<and> policy_redrive P t1 ec2 t1'
       \<and> policy_redrive P t2 ec2 t2'
       \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
       \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
       \<and> \<not> (exactly_once_at ec2 t1' \<and> exactly_once_at ec2 t2')))
 \<or> (\<exists>t t'. dwe_core t = dwe_core t' \<and> dwe_epoch t = dwe_epoch t'
          \<and> dwe_emitted t \<noteq> dwe_emitted t' \<and> P t \<noteq> P t')"
proof (cases "ledger_blind P")
  case True
  then have sem: "store_epoch_measured P"
    by (simp add: ledger_blind_iff_store_epoch_measured)
  have "\<exists>t1 t2 t1' t2'.
         dwe_reachable t1 \<and> dwe_reachable t2
       \<and> dwe_core t1 = dwe_core t2
       \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
       \<and> policy_redrive P t1 ec2 t1'
       \<and> policy_redrive P t2 ec2 t2'
       \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
       \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
       \<and> \<not> (exactly_once_at ec2 t1' \<and> exactly_once_at ec2 t2')"
    by (rule no_store_epoch_measured_exactly_once_recovery
             [rule_format, OF sem])
  with sem show ?thesis by blast
next
  case False
  show ?thesis
    by (rule disjI2) (rule not_ledger_blind_distinguishes_ledger[OF False])
qed

text \<open>
  Both horns are inhabited --- the dichotomy is not vacuous packaging.
  The banked cursor policy (every persisted cursor) is ledger-blind;
  the landed sink-reading @{const sink_delta} is not: it computes
  differently on the two members of the equal-core, equal-epoch pair.
\<close>

lemma cursor_policy_ledger_blind:
  "ledger_blind
     (\<lambda>s. drop m (replay_down_hist (exec_src_hist (dwe_core s))
                    (exec_scope (dwe_core s)) f))"
  unfolding ledger_blind_iff_store_epoch_measured
  by (rule store_measured_imp_epoch_measured[OF cursor_policy_store_measured])

lemma sink_delta_not_ledger_blind:
  "\<not> ledger_blind (sink_delta ec2)"
proof
  assume lb: "ledger_blind (sink_delta ec2)"
  have "sink_delta ec2 d1_w = sink_delta ec2 d2_w"
    by (rule lb[unfolded ledger_blind_def, rule_format])
       (simp add: d_cores_eq d1_fields d2_fields)
  then show False
    by (simp add: sink_delta_def d1_w_def d2_w_def mkT_def mkC_def
                  replay_down_hist_def e1_def e2_def ec_defs)
qed

end
