(*  Title:       Dual_Write_Effect_Recovery_Grammar.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE RECOVERY GRAMMAR, RE-READ ON THE CYCLIC MACHINE: how the cyclic
    trace grammar relates to the landed recovery temporal grammar
    (Dual_Write_Recovery), with every guard difference disclosed, and the
    landed grammar-layer corollaries restated per epoch.  Label-only
    fragments embed VERBATIM into the landed grammar; reconcile-bearing
    segments do NOT embed syntactically (the landed corpus itself proves
    relay-replay and wholesale reconcile different transformers); the
    correspondence for reconciles is semantic, through the landed
    effective-redelivery interface that the landed convergence layer
    consumes --- so the landed convergence theorems re-land in EVERY epoch
    with their landed proofs cited verbatim.  A restatement carrier with
    disclosed scope, never an upgrade.

    Produced by the S4d proof-wave P1 prover per the committed design
    (paper/dual_write/phase3/s4d_design/, gate-canonicalized); the scratch
    original's in-source ML oracle gates are STRIPPED here: oracle-freedom
    is certified by scratch-side per-slice gate sessions with
    confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Recovery_Grammar
  imports Dual_Write_Effect_Segments
begin

section \<open>The guard-placement re-check: cyclic grammar vs landed grammar\<close>

text \<open>
  The cyclic @{const dwe_temporal_trace} IS the Resume-extended grammar.
  Re-checking it row by row against the landed
  @{const recovery_temporal_trace} (@{text Dual_Write_Recovery}):

  \<^enum> LABEL RULE: the landed grammar's label rule is UNGUARDED; the cyclic
    grammar adds @{const wellformed_exec_state} +
    @{const exec_label_preserves_history_wf}.  Direction of strength:
    every cyclic label word is a landed-grammar label word (a
    sub-grammar); nothing admitted by the cyclic machine is outside the
    landed grammar's label fragment.  The verbatim embedding is
    @{text dwe_label_segment_landed_grammar} below.

  \<^enum> RECONCILE RULE: the SAME word shape (@{term "Recovery_Reconcile f"}
    vs @{term "DWE_Reconcile m f"} up to cursor erasure) but a DIFFERENT
    transformer: the landed rule applies the WHOLESALE
    @{const recovery_reconciled_state} (copies the full source history),
    the cyclic core applies the relay bounded replay (a scoped,
    frontier-bounded filter).  The landed corpus itself proves them
    different (@{thm [source] anti_atomic_down_neq_src}).  CONSEQUENCE:
    there is NO syntactic embedding of reconcile-bearing cyclic segments
    into @{const recovery_temporal_trace}; the correspondence is
    (i) syntactic into the new @{const core_relay_temporal_trace}
    (@{thm [source] dwe_segment_core_trace}), (ii) label-only fragments
    syntactically into the landed grammar (below), and (iii) semantic at
    theorem level through
    @{const recovery_effectively_redelivers_source_history_at} --- which
    the cyclic reconcile inhabits
    (@{thm [source] emitting_reconcile_effective}) and which is exactly
    the interface the landed grammar's convergence layer consumes, so the
    landed convergence theorems re-derive per epoch with their landed
    proofs cited verbatim (@{text dwe_reconcile_temporal_convergence}
    below).

  \<^enum> RECONCILE ENABLEDNESS: the landed rule fires from
    @{term "Crashed c"} OR from @{term Recovered}
    (@{thm [source] recovery_reconcile_step.reconcile_from_recovered});
    @{const emitting_reconcile} fires ONLY from @{term "Crashed c"}, per
    the pinned phase-2 spec.  CONSEQUENCE: in-place re-reconciliation
    from @{term Recovered} is inexpressible on the cyclic machine; the
    operational path is Resume, then Crash, then reconcile --- which
    costs one epoch (the Recovered-heal restatement below carries the
    @{term Suc}-epoch cost IN its statement).

  \<^enum> NEW PRODUCTION: @{const DWE_Resume} corresponds to NO landed action
    (@{thm [source] resume_breaks_core_simulation}), is image-INERT
    (@{text dwe_resume_preserves_proto} below: it heals nothing and
    breaks nothing on the image; it only flips status and opens the next
    epoch), and is the ONLY epoch-increasing production
    (@{thm [source] dwe_trace_epoch_count}).

  Also disclosed: @{term Recovered} is reachable BOTH by the lifted
  @{const Recover} label (status-only) and by the reconcile (healing) ---
  the cyclic grammar keeps the landed distinction, and the r-chain
  witness of the Segments theory shows Resume does not care which one
  produced it.
\<close>

section \<open>Label fragments land in the LANDED grammar verbatim\<close>

lemma core_action_of_label_only:
  assumes "dwe_label_only xs"
  shows "map core_action_of xs = map Recovery_Label (map dwe_label_of xs)"
  using assms
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  from Cons.prems obtain a where rg_wit: "x = DWE_Label a"
    by (auto simp: dwe_label_only_def)
  have tail: "dwe_label_only xs"
    using Cons.prems by (simp add: dwe_label_only_def)
  show ?case using Cons.IH[OF tail] by (simp add: rg_wit)
qed

theorem dwe_label_segment_landed_grammar:
  assumes "dwe_temporal_trace t xs t'"
      and "dwe_label_only xs"
  shows "recovery_temporal_trace (dwe_core t)
           (map core_action_of xs) (dwe_core t')"
proof -
  have "recovery_temporal_trace (dwe_core t)
          (map Recovery_Label (map dwe_label_of xs)) (dwe_core t')"
    by (rule dw_exec_trace_imp_recovery_temporal_trace[OF
          dwe_label_run_core_trace[OF assms]])
  then show ?thesis
    by (simp add: core_action_of_label_only[OF assms(2)])
qed

section \<open>Resume is image-inert\<close>

text \<open>
  The epoch counter and the status flip heal nothing --- only the
  reconcile changes the image.  This is what licenses extending the
  landed no-reconciliation persistence law ACROSS epochs below.
\<close>

lemma dwe_resume_preserves_proto:
  assumes "dwe_resume t t'"
  shows "proto_of_exec_at (dwe_core t') c = proto_of_exec_at (dwe_core t) c"
  unfolding dwe_resume_core[OF assms] by simp

section \<open>Cross-epoch persistence: the landed negative, strengthened scope\<close>

text \<open>
  Counterparts of @{thm [source] no_reconciliation_mismatch_persists} and
  @{thm [source] observation_only_recovery_does_not_converge_from_mismatch}.
  The cyclic form is STRICTLY STRONGER in scope --- and named plainly as
  such, a persistence NEGATIVE, not a safety upgrade: the no-reconcile
  persistence now crosses Resume, i.e. crosses epochs, because Resume is
  image-inert.  Observation words here may contain the landed observation
  labels AND Resume.
\<close>

definition dwe_observation_action :: "('k, 'v) dwe_action \<Rightarrow> bool" where
  "dwe_observation_action x \<longleftrightarrow>
     (\<exists>a. x = DWE_Label a \<and> recovery_observation_label a) \<or> x = DWE_Resume"

lemma dwe_observation_resume_trace_preserves_proto:
  assumes "dwe_temporal_trace t xs t'"
      and "list_all dwe_observation_action xs"
  shows "proto_of_exec_at (dwe_core t') c = proto_of_exec_at (dwe_core t) c"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  show ?case by simp
next
  case (dwe_label_step t a t' as t'')
  have obs: "recovery_observation_label a"
    using dwe_label_step.prems by (auto simp: dwe_observation_action_def)
  have step: "proto_of_exec_at (dwe_core t') c = proto_of_exec_at (dwe_core t) c"
    by (rule recovery_observation_step_preserves_proto[OF
          dwe_step_core[OF dwe_label_step.hyps(3)] obs])
  have tail: "proto_of_exec_at (dwe_core t'') c = proto_of_exec_at (dwe_core t') c"
    using dwe_label_step.IH dwe_label_step.prems by simp
  from tail step show ?case by simp
next
  case (dwe_reconcile_step m t f t' as t'')
  then show ?case by (simp add: dwe_observation_action_def)
next
  case (dwe_resume_step t t' as t'')
  have step: "proto_of_exec_at (dwe_core t') c = proto_of_exec_at (dwe_core t) c"
    by (rule dwe_resume_preserves_proto[OF dwe_resume_step.hyps(1)])
  have tail: "proto_of_exec_at (dwe_core t'') c = proto_of_exec_at (dwe_core t') c"
    using dwe_resume_step.IH dwe_resume_step.prems by simp
  from tail step show ?case by simp
qed

theorem dwe_observation_resume_trace_preserves_mismatch:
  assumes "dwe_temporal_trace t xs t'"
      and "list_all dwe_observation_action xs"
  shows "mismatch_at (proto_of_exec_at (dwe_core t') c) c k
       = mismatch_at (proto_of_exec_at (dwe_core t) c) c k"
  using dwe_observation_resume_trace_preserves_proto[OF assms] by simp

corollary dwe_observation_resume_only_does_not_converge_from_mismatch:
  assumes "dwe_temporal_trace t xs t'"
      and "list_all dwe_observation_action xs"
      and "mismatch_at (proto_of_exec_at (dwe_core t) f) f k"
  shows "\<not> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k)"
proof
  assume all: "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k"
  have "mismatch_at (proto_of_exec_at (dwe_core t') f) f k"
    using dwe_observation_resume_trace_preserves_mismatch[OF assms(1) assms(2)]
          assms(3) by simp
  with all show False by blast
qed

section \<open>Per-epoch temporal convergence: the grammar's positive payload\<close>

text \<open>
  Counterpart of @{thm [source] recovery_reconcile_temporal_convergence}
  and --- the form that actually matches the cyclic reconcile --- of
  @{thm [source] relay_bounded_replay_temporal_convergence}.  SCOPE
  DISCLOSURE: @{term t} is ANY cyclic state, including post-Resume states
  in any epoch, so the landed diverges-before / converged-after law is
  available in EVERY epoch; the wait and the reconcile stay within the
  current epoch (a label-only wait and the reconcile are epoch-constant).
  THIS, not a grammar embedding, is the honest sense in which the landed
  convergence layer re-lands per epoch.
\<close>

theorem dwe_reconcile_temporal_convergence:
  assumes "dwe_temporal_trace t wait t_wait"
      and "dwe_label_only wait"
      and "list_all recovery_observation_label (map dwe_label_of wait)"
      and "diverges (proto_of_exec_at (dwe_core t) f) f"
      and "emitting_reconcile m t_wait f t_done"
  shows "diverges (proto_of_exec_at (dwe_core t_wait) f) f
       \<and> \<not> diverges (proto_of_exec_at (dwe_core t_done) f) f"
  by (rule relay_bounded_replay_temporal_convergence[OF
        dwe_label_run_core_trace[OF assms(1) assms(2)] assms(3) assms(4)
        emitting_reconcile_core[OF assms(5)]])

section \<open>Store-loss freedom, cyclic form\<close>

text \<open>
  NAME COLLISION FENCE (mandatory, read before using this definition).
  "Recovery loss" in @{text dwe_no_permanent_recovery_loss} is the LANDED
  STORE-side notion: a scoped image value that is never redelivered to
  the downstream STORE --- freedom from it says a heal of the durable
  image remains reachable.  It is DISJOINT from the recovery-information
  dilemma's @{text lost_effect} (@{text Dual_Write_Effect_Dilemma}), which is a
  LEDGER/EFFECT-side notion: a committed effect that the external world
  never receives.  A state can be store-loss-free and still lose an
  effect, and vice versa; neither vocabulary substitutes for the other.

  DEFINITION DELTA vs the landed @{const no_permanent_recovery_loss}: the
  landed wait is an UNGUARDED @{const dw_exec_trace}; the cyclic wait
  below is the machine's own guarded trace (admissible labels).  The
  cyclic definition therefore demands a STRONGER witness --- disclosed,
  not hidden.  Enabledness row 3 of the guard table also applies: the
  cyclic form is inhabited from crashed states within the epoch; from
  @{term Recovered} states it requires the next epoch (Resume, Crash,
  reconcile --- see the Recovered-heal restatement below).

  DIVISION OF LABOR with the effect verdict (designed contrast, not a
  discovery): the SAME wait+reconcile shape witnessing
  @{text dwe_no_permanent_recovery_loss} at the banked crashed witness
  @{const t_mid_w} produces, with cold cursor @{term "m = 0"}, the
  duplicate-carrying @{const t_fin_w} (@{thm [source] t_fin_unsafe},
  gate G2: @{thm [source] crash_heal_reemit_bridge}) and, with warm
  cursor @{term "m = 1"}, the effect-safe @{const t_safe_w}
  (@{thm [source] t_safe_not_unsafe}, gate G1:
  @{thm [source] dwe_duplicate_separation}).  The store-no-loss verdict
  is cursor-blind; the effect verdict is not.
\<close>

definition dwe_no_permanent_recovery_loss
  :: "('k, 'v) dwe_state \<Rightarrow> frontier \<Rightarrow> bool"
where
  "dwe_no_permanent_recovery_loss t f \<longleftrightarrow>
     (\<exists>wait t_wait m t_done.
        dwe_label_only wait
      \<and> list_all recovery_observation_label (map dwe_label_of wait)
      \<and> dwe_temporal_trace t wait t_wait
      \<and> emitting_reconcile m t_wait f t_done)"

theorem dwe_no_permanent_recovery_loss_temporal_convergence:
  assumes "dwe_no_permanent_recovery_loss t f"
  shows "\<exists>wait t_wait m t_done.
      dwe_label_only wait
    \<and> dwe_temporal_trace t wait t_wait
    \<and> emitting_reconcile m t_wait f t_done
    \<and> dwe_temporal_trace t (wait @ [DWE_Reconcile m f]) t_done
    \<and> exec_status (dwe_core t_done) = Recovered
    \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t_done) f) f k)
    \<and> \<not> diverges (proto_of_exec_at (dwe_core t_done) f) f"
proof -
  from assms obtain wait t_wait m t_done where
    lab: "dwe_label_only wait"
    and obs: "list_all recovery_observation_label (map dwe_label_of wait)"
    and tr: "dwe_temporal_trace t wait t_wait"
    and rec: "emitting_reconcile m t_wait f t_done"
    unfolding dwe_no_permanent_recovery_loss_def by blast
  have one: "dwe_temporal_trace t_wait [DWE_Reconcile m f] t_done"
    by (rule dwe_temporal_trace.dwe_reconcile_step[OF rec
          dwe_temporal_trace.dwe_refl])
  have whole: "dwe_temporal_trace t (wait @ [DWE_Reconcile m f]) t_done"
    by (rule dwe_temporal_trace_append[OF tr one])
  have status: "exec_status (dwe_core t_done) = Recovered"
    using rec by (simp add: emitting_reconcile_def)
  have heal: "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t_done) f) f k"
    by (rule emitting_reconcile_heals[OF rec])
  have nodiv: "\<not> diverges (proto_of_exec_at (dwe_core t_done) f) f"
    using heal by (auto simp: diverges_iff_mismatch_at)
  from lab tr rec whole status heal nodiv show ?thesis by blast
qed

lemma dwe_no_permanent_recovery_loss_nonvacuous:
  "dwe_no_permanent_recovery_loss t_mid_w ec2"
  unfolding dwe_no_permanent_recovery_loss_def
  by (intro exI[of _ "[]"] exI[of _ t_mid_w] exI[of _ 0] exI[of _ t_fin_w])
     (simp add: dwe_label_only_def dwe_temporal_trace.dwe_refl rec_fin)

section \<open>Recovered-state corollaries, cyclic counterparts\<close>

text \<open>
  Counterparts of @{thm [source] recovered_state_still_diverges} and
  @{thm [source] recovered_status_not_enough_for_no_divergence}.  The
  landed witnesses live at OTHER machine parameters (the
  downstream-first stale-update family); they cannot be reused under the
  pinned @{const dwe_reachable}, hence the fresh r-chain of the Segments
  theory.  The landed core-level facts themselves remain citable verbatim
  at core level; these wrapper forms add the pinned-reachability content.
\<close>

lemma r_rec_mismatch:
  "mismatch_at (proto_of_exec_at (dwe_core r_rec_w) ec1) ec1 0"
  by (simp add: r_rec_w_def eval_defs eval_nat_numeral)

lemma r_rec_diverges:
  "diverges (proto_of_exec_at (dwe_core r_rec_w) ec1) ec1"
  using r_rec_mismatch
  by (auto simp: diverges_iff_mismatch_at proto_of_exec_at_def r_rec_w_def
                 mkT_def mkC_def ec_defs)

theorem dwe_recovered_diverging_reachable:
  "dwe_reachable r_rec_w
 \<and> exec_status (dwe_core r_rec_w) = Recovered
 \<and> mismatch_at (proto_of_exec_at (dwe_core r_rec_w) ec1) ec1 0
 \<and> diverges (proto_of_exec_at (dwe_core r_rec_w) ec1) ec1"
  by (intro conjI reach_r_rec r_rec_mismatch r_rec_diverges)
     (simp add: r_rec_w_def mkT_def mkC_def)

corollary dwe_recovered_status_not_enough_for_no_divergence:
  "\<not> (\<forall>t. dwe_reachable t \<and> exec_status (dwe_core t) = Recovered
        \<longrightarrow> \<not> diverges (proto_of_exec_at (dwe_core t) ec1) ec1)"
proof
  assume all: "\<forall>t. dwe_reachable t \<and> exec_status (dwe_core t) = Recovered
        \<longrightarrow> \<not> diverges (proto_of_exec_at (dwe_core t) ec1) ec1"
  have status: "exec_status (dwe_core r_rec_w) = Recovered"
    by (simp add: r_rec_w_def mkT_def mkC_def)
  from all reach_r_rec status r_rec_diverges show False by blast
qed

subsection \<open>The Recovered-heal restatement along Resume, Crash, reconcile\<close>

text \<open>
  Counterpart of
  @{thm [source] recovered_mismatch_observe_then_redeliver_converges}.
  DISCLOSURE (mandatory): the landed corollary re-heals from
  @{term Recovered} IN PLACE via
  @{thm [source] recovery_reconcile_step.reconcile_from_recovered}; the
  cyclic machine has no such rule --- @{const emitting_reconcile} demands
  @{term "Crashed c"}, and no Crash label fires from @{term Recovered} ---
  so the re-drive requires re-entering @{term Running} and re-crashing,
  i.e. one full Resume cycle, at the cost of ONE EPOCH.  The epoch cost
  is part of the statement (@{term "Suc (dwe_epoch r_rec_w)"}), not a
  footnote.  Design freedom note: the cursor @{term "m = 0"} is chosen so
  the heal is ALSO the emitting re-drive (its ledger consequences are
  banked, site-independent facts); @{term "m = 1"} would heal
  emission-free --- see the skip-asymmetry block of the Cyclic theory;
  nothing about liveness is claimed either way.
\<close>

definition r_cr1_w :: "(nat, nat) dwe_state" where
  "r_cr1_w = mkT (mkC [(ec1, e1)] [] [] {} (Crashed ec1)) [] 1"

definition r_done1_w :: "(nat, nat) dwe_state" where
  "r_done1_w = mkT (mkC [(ec1, e1)] [(ec1, e1)] [] {} Recovered)
                   [(1, 1, ec1, e1)] 1"

lemma g_r_run1_crash:
  "exec_label_preserves_history_wf (dwe_core r_run1_w) (Crash ec1)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma ws_rc1: "dwe_step r_run1_w (Crash ec1) r_cr1_w"
proof -
  have c: "dw_exec_step (dwe_core r_run1_w) (Crash ec1) (dwe_core r_cr1_w)"
    by (rule crashI) (simp_all add: r_run1_w_def r_cr1_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c])
       (simp_all add: r_run1_w_def r_cr1_w_def mkT_def)
qed

lemma rec_r1: "emitting_reconcile 0 r_cr1_w ec1 r_done1_w"
  by (simp add: emitting_reconcile_def r_cr1_w_def r_done1_w_def mkT_def mkC_def
                replay_down_hist_def e1_def ec_defs eval_nat_numeral)

lemma r_cycle_trace:
  "dwe_temporal_trace r_rec_w
     [DWE_Resume, DWE_Label (Crash ec1), DWE_Reconcile 0 ec1] r_done1_w"
proof -
  have a3: "dwe_temporal_trace r_cr1_w [DWE_Reconcile 0 ec1] r_done1_w"
    by (rule dwe_temporal_trace.dwe_reconcile_step[OF rec_r1
          dwe_temporal_trace.dwe_refl])
  have a2: "dwe_temporal_trace r_run1_w
              [DWE_Label (Crash ec1), DWE_Reconcile 0 ec1] r_done1_w"
    by (rule dwe_temporal_trace.dwe_label_step[OF wf_r_run1 g_r_run1_crash
          ws_rc1 a3])
  show ?thesis
    by (rule dwe_temporal_trace.dwe_resume_step[OF res_r a2])
qed

theorem dwe_recovered_mismatch_resume_crash_redeliver_converges:
  "\<exists>t_run t_cr t_done.
      dwe_reachable r_rec_w
    \<and> exec_status (dwe_core r_rec_w) = Recovered
    \<and> diverges (proto_of_exec_at (dwe_core r_rec_w) ec1) ec1
    \<and> dwe_resume r_rec_w t_run
    \<and> dwe_step t_run (Crash ec1) t_cr
    \<and> emitting_reconcile 0 t_cr ec1 t_done
    \<and> dwe_temporal_trace r_rec_w
        [DWE_Resume, DWE_Label (Crash ec1), DWE_Reconcile 0 ec1] t_done
    \<and> dwe_epoch t_done = Suc (dwe_epoch r_rec_w)
    \<and> exec_status (dwe_core t_done) = Recovered
    \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t_done) ec1) ec1 k)
    \<and> \<not> diverges (proto_of_exec_at (dwe_core t_done) ec1) ec1"
proof (intro exI conjI)
  show "dwe_reachable r_rec_w" by (rule reach_r_rec)
  show "exec_status (dwe_core r_rec_w) = Recovered"
    by (simp add: r_rec_w_def mkT_def mkC_def)
  show "diverges (proto_of_exec_at (dwe_core r_rec_w) ec1) ec1"
    by (rule r_rec_diverges)
  show "dwe_resume r_rec_w r_run1_w" by (rule res_r)
  show "dwe_step r_run1_w (Crash ec1) r_cr1_w" by (rule ws_rc1)
  show "emitting_reconcile 0 r_cr1_w ec1 r_done1_w" by (rule rec_r1)
  show "dwe_temporal_trace r_rec_w
          [DWE_Resume, DWE_Label (Crash ec1), DWE_Reconcile 0 ec1] r_done1_w"
    by (rule r_cycle_trace)
  show "dwe_epoch r_done1_w = Suc (dwe_epoch r_rec_w)"
    by (simp add: r_done1_w_def r_rec_w_def mkT_def)
  show "exec_status (dwe_core r_done1_w) = Recovered"
    by (simp add: r_done1_w_def mkT_def mkC_def)
  show "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core r_done1_w) ec1) ec1 k"
    by (rule emitting_reconcile_heals[OF rec_r1])
  show "\<not> diverges (proto_of_exec_at (dwe_core r_done1_w) ec1) ec1"
    using emitting_reconcile_heals[OF rec_r1]
    by (auto simp: diverges_iff_mismatch_at)
qed

text \<open>
  DELIBERATELY OUT OF SCOPE for this theory:
  @{thm [source] source_first_no_permanent_loss_redelivery_witness} is
  Ack/CDC-replay flavored (acked source effects, cdc-only streams,
  execution-replay derivations) and belongs to the completeness-axes
  restatement if anywhere; the landed fact stays citable verbatim at core
  level.
\<close>

end
