(*  Title:       Dual_Write_Effect_Completeness.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE COMPLETENESS AXES (image + order) ON THE CYCLIC MACHINE, per
    segment and across epochs (S4d site 8).  Every list-level and
    state-level tier-1 completeness fact transfers verbatim and is CITED,
    never restated; what re-lands machine-side is additive: the ledger
    stream-shape invariants (epoch-sorted, stamp-sorted, and the
    epoch-block concatenation identity), the whole-trace append-only
    bookkeeping of the acked stream, the collapse-contrast bundle (every
    store-measured stream verdict collapses to the core; the emission
    ledger provably does not), the multiset order-invariance of the
    effect verdict, and per-segment existence witnesses for the
    durability-violation class in BOTH segment kinds (epoch 0 and
    epoch 1).  A restatement carrier with disclosed scope, never an
    upgrade.

    Produced by the S4d proof-wave P5 prover per the committed design
    (paper/dual_write/phase3/s4d_design/site_5_8_witnesses_completeness.md,
    gate-canonicalized); the scratch original's in-source ML oracle gates are STRIPPED here:
    oracle-freedom is certified by scratch-side per-slice gate sessions
    with confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Completeness
  imports
    Dual_Write_Effect_Segments
    "Dual_Write_Core.Dual_Write_Image_Completeness"
    "Dual_Write_Core.Dual_Write_Order_Completeness"
begin

section \<open>8.0 Classification: the cite-only set\<close>

text \<open>
  PER-SEGMENT STATUS OF THE COMPLETENESS AXES ON THE CYCLIC MACHINE
  (restatement inventory, plan \S7 item 8).  Every list-level and
  state-level completeness fact of the landed tier-1 corpus transfers
  VERBATIM to this machine and is cited, never restated:

  \<^item> The general principle
    @{thm [source] observable_mismatch_depends_only_on_down_image} is a
    fact about ONE @{typ "('k, 'v) dw_exec_state"}; @{const dwe_core} of
    any cyclic state IS such a state, so it applies directly --- no
    wrapper duplicate is landed.  The same holds for the state-level
    facts @{thm [source] acked_durable_holds_at_w_crash} and
    @{thm [source] RV_observable_mismatch}.

  \<^item> The order axes are list-level and mention no machine at all:
    @{thm [source] necessity_fails_crosskey},
    @{thm [source] necessity_fails_samekey_equalvalue},
    @{thm [source] conditional_necessity_fails_under_full_delivery},
    @{thm [source] sufficiency_fails_inorder_drop}, and the collapse
    @{thm [source] image_faithful_invariant_under_key_sub_agreement};
    likewise the seam fact
    @{thm [source] acked_durable_blind_to_history_seam}.

  \<^item> The implementation-level facts
    @{thm [source] acked_durable_implied_by_image_safety},
    @{thm [source] I_relay_no_ack_acked_durable},
    @{thm [source] acked_violation_is_image_unsafe},
    @{thm [source] unacknowledged_crash_is_pointwise_vacuous}, and the bundle
    @{thm [source] acked_durability_is_strictly_weaker_than_image_safety} quantify over the
    landed implementation layer (or pin landed initial states), which is
    independent of this machine's Resume cycle; they transfer verbatim,
    whole-trace, not merely per-segment.

  EXPLICIT ANTI-VACUITY FLAG: the naive machine-level restatement of the
  durability implication on THIS pinned machine --- ``if no reachable
  state has an observable mismatch then no reachable state has an acked
  observable mismatch'' --- is VACUOUSLY true, because the pinned machine
  is image-unsafe (@{thm [source] t_mid_mismatch} at the reachable
  @{const t_mid_w}, @{thm [source] reach_t_mid}).  Landing that
  implication would be a true-but-empty restatement; it is deliberately
  NOT landed.  The machine-level re-landing below is additive instead:
  stream-shape theorems, the collapse-contrast bundle, the multiset
  order-invariance, and the per-segment existence witnesses.
\<close>

section \<open>8.1 Stream invariants: which streams honestly span epochs\<close>

text \<open>
  STREAM AUDIT (the one silent-strengthening trap on this site, fenced).
  Of the four streams a cyclic state carries:

  \<^item> the emission ledger @{const dwe_emitted} is append-only under all
    three rules (@{thm [source] dwe_step_emitted_ext},
    @{thm [source] emitting_reconcile_emitted_ext},
    @{thm [source] dwe_resume_emitted_same}) --- it CONCATENATES across
    epochs, epoch-tagged; within one segment all new entries carry the
    segment's epoch (@{thm [source] dwe_segment_emissions_current_epoch});
    across segments the ledger is the epoch-ordered concatenation of its
    per-epoch blocks (theorems below);

  \<^item> the acked stream @{const exec_acked} is appended only by the
    @{const Ack} label and untouched by the reconcile and by Resume ---
    it concatenates whole-trace (theorems below);

  \<^item> the committed source history @{const exec_src_hist} is append-only
    (banked @{thm [source] dwe_trace_src_ext});

  \<^item> the DELIVERED stream @{const exec_down_hist} does NOT concatenate:
    the reconcile REWRITES it wholesale to a scoped replay --- that is
    the tier-1 heal, by design, on both architectures.  Any claim that
    ``the delivered stream concatenates across segments'' would be FALSE.
    The honest per-epoch reading of the delivered stream is ``rewritten
    within a segment by heal, preserved by Resume'', and it is
    deliberately given no concatenation theorem.
\<close>

lemma sorted_map_constant:
  assumes "\<forall>x \<in> set xs. f x = (c :: 'c :: linorder)"
  shows "sorted (map f xs)"
  using assms by (induction xs) auto

lemma dwe_trace_ledger_epochs_sorted:
  assumes "dwe_temporal_trace t xs t'"
      and "sorted (map e_epoch (dwe_emitted t))"
      and "epochs_bounded t"
  shows "sorted (map e_epoch (dwe_emitted t'))"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  then show ?case by simp
next
  case (dwe_label_step t a t' as t'')
  obtain es where es: "dwe_emitted t' = dwe_emitted t @ es"
      and new: "\<forall>x \<in> set es. e_epoch x = dwe_epoch t"
    using dwe_step_new_epochs[OF dwe_label_step.hyps(3)] by blast
  have eb': "epochs_bounded t'"
    by (rule dwe_step_epochs_bounded[OF dwe_label_step.hyps(3)
          dwe_label_step.prems(2)])
  have "sorted (map e_epoch es)"
    by (rule sorted_map_constant[OF new])
  moreover have "\<forall>u \<in> set (map e_epoch (dwe_emitted t)).
                   \<forall>v \<in> set (map e_epoch es). u \<le> v"
    using dwe_label_step.prems(2) new
    unfolding epochs_bounded_def by auto
  ultimately have sorted': "sorted (map e_epoch (dwe_emitted t'))"
    using dwe_label_step.prems(1) by (simp add: es sorted_append)
  show ?case by (rule dwe_label_step.IH[OF sorted' eb'])
next
  case (dwe_reconcile_step m t f t' as t'')
  obtain es where es: "dwe_emitted t' = dwe_emitted t @ es"
      and new: "\<forall>x \<in> set es. e_epoch x = dwe_epoch t"
    using emitting_reconcile_new_epochs[OF dwe_reconcile_step.hyps(1)] by blast
  have eb': "epochs_bounded t'"
    by (rule emitting_reconcile_epochs_bounded[OF dwe_reconcile_step.hyps(1)
          dwe_reconcile_step.prems(2)])
  have "sorted (map e_epoch es)"
    by (rule sorted_map_constant[OF new])
  moreover have "\<forall>u \<in> set (map e_epoch (dwe_emitted t)).
                   \<forall>v \<in> set (map e_epoch es). u \<le> v"
    using dwe_reconcile_step.prems(2) new
    unfolding epochs_bounded_def by auto
  ultimately have sorted': "sorted (map e_epoch (dwe_emitted t'))"
    using dwe_reconcile_step.prems(1) by (simp add: es sorted_append)
  show ?case by (rule dwe_reconcile_step.IH[OF sorted' eb'])
next
  case (dwe_resume_step t t' as t'')
  have em: "dwe_emitted t' = dwe_emitted t"
    by (rule dwe_resume_emitted_same[OF dwe_resume_step.hyps(1)])
  have eb': "epochs_bounded t'"
    by (rule dwe_resume_epochs_bounded[OF dwe_resume_step.hyps(1)
          dwe_resume_step.prems(2)])
  have sorted': "sorted (map e_epoch (dwe_emitted t'))"
    using dwe_resume_step.prems(1) by (simp add: em)
  show ?case by (rule dwe_resume_step.IH[OF sorted' eb'])
qed

theorem dwe_reachable_ledger_epochs_sorted:
  assumes "dwe_reachable t"
  shows "sorted (map e_epoch (dwe_emitted t))"
proof -
  obtain xs where xs: "dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2) xs t"
    using assms unfolding dwe_reachable_def by blast
  have s0: "sorted (map e_epoch (dwe_emitted (dwe_init Map.empty {0, 1} ec2)))"
    by (simp add: dwe_init_def)
  show ?thesis
    by (rule dwe_trace_ledger_epochs_sorted[OF xs s0 dwe_init_epochs_bounded])
qed

text \<open>
  Stamp sortedness, same route with the banked stamps-bounded invariant:
  both emitting rules stamp the CURRENT committed-prefix length, which
  bounds every older stamp, and the committed prefix is append-only.
\<close>

lemma dwe_step_new_stamps_exact:
  assumes "dwe_step t a t'"
  shows "\<exists>es. dwe_emitted t' = dwe_emitted t @ es
            \<and> (\<forall>x \<in> set es. e_stamp x = length (exec_src_hist (dwe_core t)))"
  using assms
proof (induction rule: dwe_step.induct)
  case (lift_nonpub t a c')
  show ?case by (intro exI[of _ "[]"]) simp
next
  case (publish_emit t c e c')
  show ?case
    by (intro exI[of _ "[(length (exec_src_hist (dwe_core t)), dwe_epoch t, c, e)]"])
       simp
qed

lemma emitting_reconcile_new_stamps_exact:
  assumes "emitting_reconcile m t f t'"
  shows "\<exists>es. dwe_emitted t' = dwe_emitted t @ es
            \<and> (\<forall>x \<in> set es. e_stamp x = length (exec_src_hist (dwe_core t)))"
proof -
  have em: "dwe_emitted t' = dwe_emitted t
              @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                               dwe_epoch t, c, e))
                  (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                             (exec_scope (dwe_core t)) f))"
    using assms by (simp add: emitting_reconcile_def)
  show ?thesis
    unfolding em by (intro exI conjI) (auto simp: e_stamp_def)
qed

lemma dwe_trace_ledger_stamps_sorted:
  assumes "dwe_temporal_trace t xs t'"
      and "sorted (map e_stamp (dwe_emitted t))"
      and "stamps_bounded t"
  shows "sorted (map e_stamp (dwe_emitted t'))"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  then show ?case by simp
next
  case (dwe_label_step t a t' as t'')
  obtain es where es: "dwe_emitted t' = dwe_emitted t @ es"
      and new: "\<forall>x \<in> set es. e_stamp x = length (exec_src_hist (dwe_core t))"
    using dwe_step_new_stamps_exact[OF dwe_label_step.hyps(3)] by blast
  have sb': "stamps_bounded t'"
    by (rule dwe_step_stamps_bounded[OF dwe_label_step.hyps(3)
          dwe_label_step.prems(2)])
  have "sorted (map e_stamp es)"
    by (rule sorted_map_constant[OF new])
  moreover have "\<forall>u \<in> set (map e_stamp (dwe_emitted t)).
                   \<forall>v \<in> set (map e_stamp es). u \<le> v"
    using dwe_label_step.prems(2) new
    unfolding stamps_bounded_def by auto
  ultimately have sorted': "sorted (map e_stamp (dwe_emitted t'))"
    using dwe_label_step.prems(1) by (simp add: es sorted_append)
  show ?case by (rule dwe_label_step.IH[OF sorted' sb'])
next
  case (dwe_reconcile_step m t f t' as t'')
  obtain es where es: "dwe_emitted t' = dwe_emitted t @ es"
      and new: "\<forall>x \<in> set es. e_stamp x = length (exec_src_hist (dwe_core t))"
    using emitting_reconcile_new_stamps_exact[OF dwe_reconcile_step.hyps(1)]
    by blast
  have sb': "stamps_bounded t'"
    by (rule emitting_reconcile_stamps_bounded[OF dwe_reconcile_step.hyps(1)
          dwe_reconcile_step.prems(2)])
  have "sorted (map e_stamp es)"
    by (rule sorted_map_constant[OF new])
  moreover have "\<forall>u \<in> set (map e_stamp (dwe_emitted t)).
                   \<forall>v \<in> set (map e_stamp es). u \<le> v"
    using dwe_reconcile_step.prems(2) new
    unfolding stamps_bounded_def by auto
  ultimately have sorted': "sorted (map e_stamp (dwe_emitted t'))"
    using dwe_reconcile_step.prems(1) by (simp add: es sorted_append)
  show ?case by (rule dwe_reconcile_step.IH[OF sorted' sb'])
next
  case (dwe_resume_step t t' as t'')
  have em: "dwe_emitted t' = dwe_emitted t"
    by (rule dwe_resume_emitted_same[OF dwe_resume_step.hyps(1)])
  have sb': "stamps_bounded t'"
    by (rule dwe_resume_stamps_bounded[OF dwe_resume_step.hyps(1)
          dwe_resume_step.prems(2)])
  have sorted': "sorted (map e_stamp (dwe_emitted t'))"
    using dwe_resume_step.prems(1) by (simp add: em)
  show ?case by (rule dwe_resume_step.IH[OF sorted' sb'])
qed

theorem dwe_reachable_ledger_stamps_sorted:
  assumes "dwe_reachable t"
  shows "sorted (map e_stamp (dwe_emitted t))"
proof -
  obtain xs where xs: "dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2) xs t"
    using assms unfolding dwe_reachable_def by blast
  have s0: "sorted (map e_stamp (dwe_emitted (dwe_init Map.empty {0, 1} ec2)))"
    by (simp add: dwe_init_def)
  show ?thesis
    by (rule dwe_trace_ledger_stamps_sorted[OF xs s0 dwe_init_stamps_bounded])
qed

subsection \<open>The acked stream spans epochs (durability-axis bookkeeping)\<close>

text \<open>
  HONESTY: these are BOOKKEEPING facts (``the acked stream is
  epoch-spanning append-only''), the durability axis's ``spans epochs''
  statement --- explicitly contrasted with the delivered stream, whose
  reconcile REWRITE (the heal) is the disclosed non-concatenating stream
  of the audit above.  No new durability characterization is stated or
  implied.
\<close>

lemma dw_exec_step_acked_ext:
  assumes "dw_exec_step s a s'"
  shows "\<exists>es. exec_acked s' = exec_acked s @ es"
  using dw_exec_step_acked[OF assms] by blast

lemma emitting_reconcile_acked_same:
  assumes "emitting_reconcile m t f t'"
  shows "exec_acked (dwe_core t') = exec_acked (dwe_core t)"
  using assms by (simp add: emitting_reconcile_def)

lemma dwe_resume_acked_same:
  assumes "dwe_resume t t'"
  shows "exec_acked (dwe_core t') = exec_acked (dwe_core t)"
  using assms by (simp add: dwe_resume_def)

theorem dwe_trace_acked_append_only:
  assumes "dwe_temporal_trace t xs t'"
  shows "\<exists>es. exec_acked (dwe_core t') = exec_acked (dwe_core t) @ es"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  show ?case by (intro exI[of _ "[]"]) simp
next
  case (dwe_label_step t a t' as t'')
  obtain e1 where 1: "exec_acked (dwe_core t') = exec_acked (dwe_core t) @ e1"
    using dw_exec_step_acked_ext[OF dwe_step_core[OF dwe_label_step.hyps(3)]]
    by blast
  obtain e2 where 2: "exec_acked (dwe_core t'') = exec_acked (dwe_core t') @ e2"
    using dwe_label_step.IH by blast
  show ?case by (intro exI[of _ "e1 @ e2"]) (simp add: 1 2)
next
  case (dwe_reconcile_step m t f t' as t'')
  obtain e2 where 2: "exec_acked (dwe_core t'') = exec_acked (dwe_core t') @ e2"
    using dwe_reconcile_step.IH by blast
  show ?case
    by (intro exI[of _ e2])
       (simp add: 2 emitting_reconcile_acked_same[OF dwe_reconcile_step.hyps(1)])
next
  case (dwe_resume_step t t' as t'')
  obtain e2 where 2: "exec_acked (dwe_core t'') = exec_acked (dwe_core t') @ e2"
    using dwe_resume_step.IH by blast
  show ?case
    by (intro exI[of _ e2])
       (simp add: 2 dwe_resume_acked_same[OF dwe_resume_step.hyps(1)])
qed

section \<open>8.2 The collapse-contrast bundle\<close>

text \<open>
  HONESTY FENCE (mandatory): the first half below is a DESIGNED boundary
  certificate, disclosed as definitional --- the durability verdict
  @{const acked_observable_mismatch} reads only the durable core BY
  CONSTRUCTION, so it trivially factors through @{const dwe_core} (the
  G1 architected-in tradition, plan \S10 bullet 1).  The pair is the
  tier-2 reading of the tier-1 completeness axes: EVERY store-measured
  stream verdict collapses to the core; the emission ledger provably
  does not (@{thm [source] effect_unsafe_not_core_function}, the banked
  G1 separation).  It is presented as that designed contrast --- never as
  a discovery about acked durability.
\<close>

lemma acked_verdict_core_measured:
  "\<exists>g. \<forall>t :: (nat, nat) dwe_state.
         acked_observable_mismatch (dwe_core t) c k = g (dwe_core t)"
  by (intro exI[of _ "\<lambda>s. acked_observable_mismatch s c k"]) simp

theorem store_stream_collapse_vs_ledger_escape:
  "(\<forall>c k. \<exists>g. \<forall>t :: (nat, nat) dwe_state.
        acked_observable_mismatch (dwe_core t) c k = g (dwe_core t))
 \<and> \<not> (\<exists>g. \<forall>t. dwe_reachable t \<longrightarrow> effect_unsafe t = g (dwe_core t))"
  using acked_verdict_core_measured effect_unsafe_not_core_function
  by blast

section \<open>8.4 The order axis at tier 2: ledger-order invariance\<close>

text \<open>
  HONESTY FENCE (mandatory): this is DEFINITIONAL PROPAGATION --- the
  hazard predicates are set/multiset-shaped by construction
  (@{const premature} quantifies over @{term "set (dwe_emitted t)"};
  @{const duplicate} is distinctness of payloads, a multiset quantity) ---
  pearl economy, the same disclosure style as tier 1's alias demotion.
  It is presented as the DESIGNED order-axis boundary of the effect
  verdict, the tier-2 analogue of tier 1's order collapse
  @{thm [source] image_faithful_invariant_under_key_sub_agreement}
  (image-faithfulness is order-invisible up to per-key subsequences;
  the effect verdict is invisible to LEDGER ORDER outright) --- never as
  a discovery.  The sharp division it certifies: what the ledger's ORDER
  cannot affect, its MULTIPLICITY does --- the banked amplification
  witness @{thm [source] resume_cycle_amplification} raises a payload's
  @{const count_list} to three and flips the verdict, the tier-2 echo of
  ``the only harmful reorder is already a mismatch''.
\<close>

lemma premature_mset_invariant:
  assumes "mset (dwe_emitted t) = mset (dwe_emitted t')"
      and "exec_src_hist (dwe_core t) = exec_src_hist (dwe_core t')"
  shows "premature t \<longleftrightarrow> premature t'"
proof -
  have "set (dwe_emitted t) = set (dwe_emitted t')"
    using assms(1) by (rule mset_eq_setD)
  then show ?thesis
    by (simp add: premature_def assms(2))
qed

lemma duplicate_mset_invariant:
  assumes "mset (dwe_emitted t) = mset (dwe_emitted t')"
  shows "duplicate t \<longleftrightarrow> duplicate t'"
proof -
  have pay: "mset (map e_payload (dwe_emitted t))
               = mset (map e_payload (dwe_emitted t'))"
    using assms by simp
  have st: "set (map e_payload (dwe_emitted t))
              = set (map e_payload (dwe_emitted t'))"
    by (rule mset_eq_setD[OF pay])
  show ?thesis
    unfolding duplicate_def distinct_count_atmost_1 pay st by simp
qed

theorem effect_verdict_ledger_order_invariant:
  assumes "mset (dwe_emitted t) = mset (dwe_emitted t')"
      and "exec_src_hist (dwe_core t) = exec_src_hist (dwe_core t')"
  shows "effect_unsafe t \<longleftrightarrow> effect_unsafe t'"
  using premature_mset_invariant[OF assms] duplicate_mset_invariant[OF assms(1)]
  by (simp add: effect_unsafe_def)

section \<open>8.3 Per-segment existence witnesses (the negative controls)\<close>

text \<open>
  The tier-1 machine-anchored durability witnesses are pinned at LANDED
  initial states (@{thm [source] acked_violation_is_image_unsafe} at the
  @{const stale_update_plan} start;
  @{thm [source] unacknowledged_crash_is_pointwise_vacuous} at
  @{term "I_relay_labels w0"}).
  Neither pin is the cyclic machine's.  The two theorems below give the
  pinned cyclic machine its own witnesses, one per segment kind --- the
  negative controls restated per segment: the durability-violation class
  (an acked entry over a diverging scoped image at the crash) is
  INHABITED in epoch 0 and RECURS in epoch 1, on a state whose ledger
  already carries epoch-0 effects.
\<close>

text \<open>Equation-form intro rule for the landed @{text ack} step (mirrors
  the banked @{thm [source] crashI} scaffolding style).\<close>

lemma ackI:
  assumes "exec_status s = Running"
      and "(c, e) \<in> set (exec_src_hist s)"
      and "s' = s\<lparr>exec_acked := exec_acked s @ [(c, e)]\<rparr>"
  shows "dw_exec_step s (Ack c e) s'"
  unfolding assms(3) by (rule dw_exec_step.ack[OF assms(1) assms(2)])

subsection \<open>Epoch 0: commit, ack, crash\<close>

definition a2_w :: "(nat, nat) dwe_state" where
  "a2_w = mkT ((mkC [(ec1, e1)] [] [] {} Running)
                 \<lparr>exec_acked := [(ec1, e1)]\<rparr>) [] 0"

definition a3_w :: "(nat, nat) dwe_state" where
  "a3_w = mkT ((mkC [(ec1, e1)] [] [] {} (Crashed ec1))
                 \<lparr>exec_acked := [(ec1, e1)]\<rparr>) [] 0"

lemma g_W1_ack1: "exec_label_preserves_history_wf (dwe_core W1) (Ack ec1 e1)"
  by (simp add: W1_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma ws_a1: "dwe_step W1 (Ack ec1 e1) a2_w"
proof -
  have c: "dw_exec_step (dwe_core W1) (Ack ec1 e1) (dwe_core a2_w)"
    by (rule ackI) (simp_all add: W1_def a2_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: W1_def a2_w_def mkT_def)
qed

lemma wf_a2: "wellformed_exec_state (dwe_core a2_w)"
  by (simp add: a2_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e1)

lemma g_a2_crash: "exec_label_preserves_history_wf (dwe_core a2_w) (Crash ec1)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma ws_a2: "dwe_step a2_w (Crash ec1) a3_w"
proof -
  have c: "dw_exec_step (dwe_core a2_w) (Crash ec1) (dwe_core a3_w)"
    by (rule crashI) (simp_all add: a2_w_def a3_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: a2_w_def a3_w_def mkT_def)
qed

lemma reach_a2: "dwe_reachable a2_w"
  by (rule dwe_reachable_label_ext[OF reach_W1 wf_W1 g_W1_ack1 ws_a1])

lemma reach_a3: "dwe_reachable a3_w"
  by (rule dwe_reachable_label_ext[OF reach_a2 wf_a2 g_a2_crash ws_a2])

lemma a3_acked_mismatch: "acked_observable_mismatch (dwe_core a3_w) ec1 0"
  by (simp add: acked_observable_mismatch_def observable_mismatch_def
                acked_source_effect_at_def a3_w_def eval_defs eval_nat_numeral)

theorem dwe_acked_violation_reachable_epoch0:
  "\<exists>t. dwe_reachable t \<and> dwe_epoch t = 0
     \<and> acked_observable_mismatch (dwe_core t) ec1 0
     \<and> observable_mismatch (dwe_core t) ec1 0"
proof (intro exI[of _ a3_w] conjI)
  show "dwe_reachable a3_w" by (rule reach_a3)
  show "dwe_epoch a3_w = 0" by (simp add: a3_w_def mkT_def)
  show "acked_observable_mismatch (dwe_core a3_w) ec1 0"
    by (rule a3_acked_mismatch)
  show "observable_mismatch (dwe_core a3_w) ec1 0"
    by (rule acked_observable_mismatch_imp_observable_mismatch[OF a3_acked_mismatch])
qed

subsection \<open>Epoch 1: re-commit, ack, crash --- from the post-Resume state\<close>

text \<open>
  HONESTY (the epoch-1 witness and the \<open>\<le>\<close> re-commit).  The chain below
  re-commits key 0 AT THE SAME COORDINATE @{const ec2} --- legal because
  WF-H1 requires only non-decreasing coordinates (\<open>\<le>\<close>); the legality
  shape is the landed equal-coordinate re-commit precedent (the
  discipline theory's @{text wfh_e1_pair_eq} pattern, re-proved below as
  @{text wfh_recommit_triple} rather than imported, per the wave's
  dependency-hygiene ruling).  The witness therefore does NOT assume the
  named premise @{text strictly_ascending_source} (real WALs have
  strictly increasing coordinates; the cyclic machine's header discloses
  the premise as named-but-not-consumed).  Under that premise this
  witness shape would be unavailable at the pinned finish @{const ec2}:
  a strictly later coordinate is invisible at frontiers at or below
  @{const ec2}, a real pin constraint recorded here so the \<open>\<le>\<close>
  re-commit is understood as the correct witness at this pin, not a
  convenience.
\<close>

definition b1e_w :: "(nat, nat) dwe_state" where
  "b1e_w = mkT (mkC [(ec1, e1), (ec2, e2), (ec2, Insert 0 5)]
                  [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)] {} Running)
               [(1, 0, ec1, e1), (2, 0, ec1, e1), (2, 0, ec2, e2)] 1"

definition b2e_w :: "(nat, nat) dwe_state" where
  "b2e_w = mkT ((mkC [(ec1, e1), (ec2, e2), (ec2, Insert 0 5)]
                   [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)] {} Running)
                  \<lparr>exec_acked := [(ec2, Insert 0 5)]\<rparr>)
               [(1, 0, ec1, e1), (2, 0, ec1, e1), (2, 0, ec2, e2)] 1"

definition b3e_w :: "(nat, nat) dwe_state" where
  "b3e_w = mkT ((mkC [(ec1, e1), (ec2, e2), (ec2, Insert 0 5)]
                   [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)] {} (Crashed ec2))
                  \<lparr>exec_acked := [(ec2, Insert 0 5)]\<rparr>)
               [(1, 0, ec1, e1), (2, 0, ec1, e1), (2, 0, ec2, e2)] 1"

lemma wfh_recommit_triple:
  "wellformed_src_history [(ec1, e1), (ec2, e2), (ec2, Insert 0 5)]"
proof -
  have can: "history_can_append [(ec1, e1), (ec2, e2)] (ec2, Insert 0 5)"
    by (simp add: history_can_append_def ec_defs)
  from wellformed_src_history_append_one[OF wfh_pair can] show ?thesis by simp
qed

lemma wfh_e5: "wellformed_src_history [(ec2, Insert 0 5)]"
  by (rule wf_hist_single) (simp add: ec_defs)

lemma g_f_run_src5:
  "exec_label_preserves_history_wf (dwe_core f_run_w) (DoSource ec2 (Insert 0 5))"
  by (simp add: f_run_w_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma ws_b1: "dwe_step f_run_w (DoSource ec2 (Insert 0 5)) b1e_w"
proof -
  have c: "dw_exec_step (dwe_core f_run_w) (DoSource ec2 (Insert 0 5)) (dwe_core b1e_w)"
    by (rule do_sourceI) (simp_all add: f_run_w_def b1e_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: f_run_w_def b1e_w_def mkT_def)
qed

lemma wf_b1e: "wellformed_exec_state (dwe_core b1e_w)"
  by (simp add: b1e_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_pair
                wfh_recommit_triple)

lemma g_b1e_ack:
  "exec_label_preserves_history_wf (dwe_core b1e_w) (Ack ec2 (Insert 0 5))"
  by (simp add: b1e_w_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma ws_b2: "dwe_step b1e_w (Ack ec2 (Insert 0 5)) b2e_w"
proof -
  have c: "dw_exec_step (dwe_core b1e_w) (Ack ec2 (Insert 0 5)) (dwe_core b2e_w)"
    by (rule ackI) (simp_all add: b1e_w_def b2e_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: b1e_w_def b2e_w_def mkT_def)
qed

lemma wf_b2e: "wellformed_exec_state (dwe_core b2e_w)"
  by (simp add: b2e_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_pair
                wfh_recommit_triple wfh_e5)

lemma g_b2e_crash: "exec_label_preserves_history_wf (dwe_core b2e_w) (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma ws_b3: "dwe_step b2e_w (Crash ec2) b3e_w"
proof -
  have c: "dw_exec_step (dwe_core b2e_w) (Crash ec2) (dwe_core b3e_w)"
    by (rule crashI) (simp_all add: b2e_w_def b3e_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: b2e_w_def b3e_w_def mkT_def)
qed

lemma reach_b1e: "dwe_reachable b1e_w"
  by (rule dwe_reachable_label_ext[OF reach_f_run wf_f_run g_f_run_src5 ws_b1])

lemma reach_b2e: "dwe_reachable b2e_w"
  by (rule dwe_reachable_label_ext[OF reach_b1e wf_b1e g_b1e_ack ws_b2])

lemma reach_b3e: "dwe_reachable b3e_w"
  by (rule dwe_reachable_label_ext[OF reach_b2e wf_b2e g_b2e_crash ws_b3])

lemma b3e_acked_mismatch: "acked_observable_mismatch (dwe_core b3e_w) ec2 0"
  by (simp add: acked_observable_mismatch_def observable_mismatch_def
                acked_source_effect_at_def b3e_w_def eval_defs eval_nat_numeral)

theorem dwe_acked_violation_reachable_epoch1:
  "\<exists>t. dwe_reachable t \<and> dwe_epoch t = 1
     \<and> acked_observable_mismatch (dwe_core t) ec2 0
     \<and> (\<exists>x \<in> set (dwe_emitted t). e_epoch x = 0)"
proof (intro exI[of _ b3e_w] conjI)
  show "dwe_reachable b3e_w" by (rule reach_b3e)
  show "dwe_epoch b3e_w = 1" by (simp add: b3e_w_def mkT_def)
  show "acked_observable_mismatch (dwe_core b3e_w) ec2 0"
    by (rule b3e_acked_mismatch)
  show "\<exists>x \<in> set (dwe_emitted b3e_w). e_epoch x = 0"
    by (simp add: b3e_w_def mkT_def)
qed

section \<open>The headline cross-epoch statement: epoch-block concatenation\<close>

text \<open>
  The ledger is the concatenation of its per-epoch blocks, in epoch
  order --- the honest cross-epoch concatenation form, derived purely
  from the sorted + bounded invariants above via one general list lemma.
  Non-vacuity of the cross-epoch reading is the banked amplification
  witness (@{thm [source] resume_cycle_amplification}: ledger entries
  with epoch 0 AND epoch 1 coexist at @{const f_amp_w}).
\<close>

lemma concat_map_Nil: "concat (map (\<lambda>_. []) l) = []"
  by (induction l) auto

lemma sorted_key_concat_filter_partition:
  assumes "sorted (map f xs)" and "\<forall>x \<in> set xs. f x < n"
  shows "xs = concat (map (\<lambda>i. filter (\<lambda>x. f x = i) xs) [0 ..< n])"
  using assms
proof (induction xs)
  case Nil
  show ?case by (simp add: concat_map_Nil)
next
  case (Cons x xs)
  have hd_min: "\<forall>y \<in> set xs. f x \<le> f y"
    using Cons.prems(1) by simp
  have sorted_tl: "sorted (map f xs)"
    using Cons.prems(1) by simp
  have bnd: "\<forall>y \<in> set xs. f y < n"
    using Cons.prems(2) by simp
  have fxn: "f x < n"
    using Cons.prems(2) by simp
  have IH: "xs = concat (map (\<lambda>i. filter (\<lambda>y. f y = i) xs) [0..<n])"
    by (rule Cons.IH[OF sorted_tl bnd])
  have fxn_le: "f x \<le> n" using fxn by simp
  have upt_split: "[0..<n] = [0..<f x] @ [f x..<n]"
    using upt_add_eq_append[of 0 "f x" "n - f x"] fxn_le
    by (simp add: le_add_diff_inverse)
  have upt_fx_cons: "[f x..<n] = f x # [Suc (f x)..<n]"
    by (rule upt_conv_Cons[OF fxn])
  have low_cons: "\<And>i. i < f x \<Longrightarrow> filter (\<lambda>y. f y = i) (x # xs) = []"
  proof -
    fix i assume i: "i < f x"
    have "\<forall>y \<in> set (x # xs). f y \<noteq> i"
      using hd_min i by fastforce
    then show "filter (\<lambda>y. f y = i) (x # xs) = []"
      by (simp add: filter_empty_conv)
  qed
  have low_xs: "\<And>i. i < f x \<Longrightarrow> filter (\<lambda>y. f y = i) xs = []"
  proof -
    fix i assume i: "i < f x"
    have "\<forall>y \<in> set xs. f y \<noteq> i"
      using hd_min i by fastforce
    then show "filter (\<lambda>y. f y = i) xs = []"
      by (simp add: filter_empty_conv)
  qed
  have low_zero: "map (\<lambda>i. filter (\<lambda>y. f y = i) (x # xs)) [0..<f x]
                = map (\<lambda>i. []) [0..<f x]"
    by (rule map_cong[OF refl]) (rule low_cons, simp)
  have low_zero_xs: "map (\<lambda>i. filter (\<lambda>y. f y = i) xs) [0..<f x]
                   = map (\<lambda>i. []) [0..<f x]"
    by (rule map_cong[OF refl]) (simp add: low_xs)
  have high_eq: "map (\<lambda>i. filter (\<lambda>y. f y = i) (x # xs)) [Suc (f x)..<n]
               = map (\<lambda>i. filter (\<lambda>y. f y = i) xs) [Suc (f x)..<n]"
    by (rule map_cong[OF refl]) auto
  \<comment> \<open>Full \<open>simp\<close> rewrites \<open>filter\<close>-over-cons UNDER the \<open>map\<close> binders and
      destroys the literal shapes the block equations need, so the whole
      calculation runs on \<open>simp only:\<close> with exact instance equations.\<close>
  have c1: "concat (map (\<lambda>i. filter (\<lambda>y. f y = i) (x # xs)) [0..<n])
          = concat (map (\<lambda>i. filter (\<lambda>y. f y = i) (x # xs)) [0..<f x])
            @ concat (map (\<lambda>i. filter (\<lambda>y. f y = i) (x # xs)) [f x..<n])"
    by (simp only: upt_split map_append concat_append)
  have c2: "concat (map (\<lambda>i. filter (\<lambda>y. f y = i) (x # xs)) [0..<f x]) = []"
    by (simp only: low_zero concat_map_Nil)
  have c3: "concat (map (\<lambda>i. filter (\<lambda>y. f y = i) (x # xs)) [f x..<n])
          = filter (\<lambda>y. f y = f x) (x # xs)
            @ concat (map (\<lambda>i. filter (\<lambda>y. f y = i) (x # xs)) [Suc (f x)..<n])"
    by (simp only: upt_fx_cons list.map concat.simps)
  have c4: "filter (\<lambda>y. f y = f x) (x # xs) = x # filter (\<lambda>y. f y = f x) xs"
    by simp
  have c5: "concat (map (\<lambda>i. filter (\<lambda>y. f y = i) (x # xs)) [Suc (f x)..<n])
          = concat (map (\<lambda>i. filter (\<lambda>y. f y = i) xs) [Suc (f x)..<n])"
    by (simp only: high_eq)
  have lhs_eq:
    "concat (map (\<lambda>i. filter (\<lambda>y. f y = i) (x # xs)) [0..<n])
       = x # (filter (\<lambda>y. f y = f x) xs
              @ concat (map (\<lambda>i. filter (\<lambda>y. f y = i) xs) [Suc (f x)..<n]))"
    by (simp only: c1 c2 c3 c4 c5 append_Nil append_Cons)
  have d1: "concat (map (\<lambda>i. filter (\<lambda>y. f y = i) xs) [0..<n])
          = concat (map (\<lambda>i. filter (\<lambda>y. f y = i) xs) [0..<f x])
            @ concat (map (\<lambda>i. filter (\<lambda>y. f y = i) xs) [f x..<n])"
    by (simp only: upt_split map_append concat_append)
  have d2: "concat (map (\<lambda>i. filter (\<lambda>y. f y = i) xs) [0..<f x]) = []"
    by (simp only: low_zero_xs concat_map_Nil)
  have d3: "concat (map (\<lambda>i. filter (\<lambda>y. f y = i) xs) [f x..<n])
          = filter (\<lambda>y. f y = f x) xs
            @ concat (map (\<lambda>i. filter (\<lambda>y. f y = i) xs) [Suc (f x)..<n])"
    by (simp only: upt_fx_cons list.map concat.simps)
  have d_all: "concat (map (\<lambda>i. filter (\<lambda>y. f y = i) xs) [0..<n])
             = filter (\<lambda>y. f y = f x) xs
               @ concat (map (\<lambda>i. filter (\<lambda>y. f y = i) xs) [Suc (f x)..<n])"
    by (simp only: d1 d2 d3 append_Nil)
  have rhs_eq:
    "xs = filter (\<lambda>y. f y = f x) xs
          @ concat (map (\<lambda>i. filter (\<lambda>y. f y = i) xs) [Suc (f x)..<n])"
    by (rule trans[OF IH d_all])
  show ?case
    by (simp only: lhs_eq rhs_eq[symmetric])
qed

theorem dwe_reachable_ledger_epoch_blocks:
  assumes "dwe_reachable t"
  shows "dwe_emitted t
           = concat (map (\<lambda>i. filter (\<lambda>x. e_epoch x = i) (dwe_emitted t))
                         [0 ..< Suc (dwe_epoch t)])"
proof (rule sorted_key_concat_filter_partition)
  show "sorted (map e_epoch (dwe_emitted t))"
    by (rule dwe_reachable_ledger_epochs_sorted[OF assms])
  show "\<forall>x \<in> set (dwe_emitted t). e_epoch x < Suc (dwe_epoch t)"
    using dwe_reachable_epochs_bounded[OF assms]
    unfolding epochs_bounded_def by (simp add: less_Suc_eq_le)
qed

end
