(*  Title:       Dual_Write_Effect_Tightness.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE PREMISE-TIGHTNESS CONTROLS ON THE CYCLIC MACHINE (S4d site 5).
    The landed tightness triptych for the tier-1 characterization is
    implementation-layer and transfers VERBATIM --- cited, never
    restated.  What the cycle changes is the premise PROFILE of the
    per-epoch reading: Running-start and crash-closure are DISCHARGED
    structurally at every segment start / Running core (discharge
    lemmas, with the discharge-is-not-tightness fence), and the
    refinement axis gains the machine-native controls the terminal
    machine provably cannot express --- the promoted machine itself,
    packaged at the landed implementation record, exits the refining
    class at a reachable state with Resume the exact exiting rule
    (a designed non-falsifying inhabitant, both sides of the landed
    biconditional genuinely false).  The epoch-1 recurrence witness
    banks in-segment mismatch recurrence one epoch up.

    Produced by the S4d proof-wave P5 prover per the committed design
    (paper/dual_write/phase3/s4d_design/site_5_8_witnesses_completeness.md,
    gate-canonicalized: the segment-start cluster is cited from the
    Segments foundation per gate finding F4); the scratch original's in-source ML oracle gates are STRIPPED here:
    oracle-freedom is certified by scratch-side per-slice gate sessions
    with confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Tightness
  imports
    Dual_Write_Effect_Segments
    "Dual_Write_Core.Dual_Write_Converse"
    "Dual_Write_Core.Dual_Write_Refinement_Tightness"
    "Dual_Write_Core.Dual_Write_Premise_Tightness"
begin

section \<open>5.1 The verbatim-transfer principle (cite, never restate)\<close>

text \<open>
  PREMISE-TIGHTNESS STATUS ON THE CYCLIC MACHINE (restatement inventory,
  per plan \S7 item 5).  The landed tightness triptych for
  @{thm [source] safe_iff_running_image_faithful} --- crash-closure
  (@{thm [source] crash_closed_is_load_bearing}, with its corollary
  @{thm [source] crash_closed_drop_breaks_forward}), Running-start
  (@{thm [source] running_start_is_load_bearing}), refinement in both
  directions (@{thm [source] refinement_drop_falsifies_forward} with
  @{thm [source] refinement_drop_breaks_forward} and
  @{thm [source] refinement_drop_falsifies_biconditional}, the
  exec-record clones
  @{thm [source] refinement_drop_falsifies_forward_exec_type} and
  @{thm [source] refinement_drop_breaks_forward_exec_type}, and
  @{thm [source] refinement_drop_falsifies_backward}) --- together with
  the non-falsifying refinement control
  (@{thm [source] refining_structurally_required_in_converse}, its
  biconditional-holds form
  @{thm [source] sf_non_refining_biconditional_holds}, and the
  non-vacuity companion
  @{thm [source] sf_non_refining_both_sides_genuinely_false}) --- is
  stated over the implementation layer, which is independent of this
  machine's Resume cycle: none of these facts mentions any machine's
  initial state or reachable set, and a counterexample to a
  premise-dropped implication stays a counterexample no matter what new
  machine exists.  Every one of these twelve facts transfers VERBATIM ---
  whole-trace, not merely per-segment: this theory cites them and
  re-proves none.

  What the cycle changes is the premise PROFILE of the per-epoch-segment
  reading: at every segment start the Running-start premise is
  DISCHARGED structurally (the initial state is Running by
  @{thm [source] dwe_init_core_running}; a Resume target is Running by
  @{thm [source] post_resume_core_running}, with the epoch increment
  @{thm [source] dwe_resume_epoch_Suc}; the packaged form is
  @{thm [source] dwe_segment_start_running}), and crash-closure is
  DISCHARGED on the machine itself (Crash is enabled at every Running
  core, the lemma below).  A per-epoch ``re-verification'' of those two
  controls would therefore be VACUOUS and is deliberately NOT landed;
  the discharge lemma below records the discharge fact instead, and the
  refinement axis gains the machine-native controls that the terminal
  machine provably cannot express.
\<close>

section \<open>5.2 Discharge lemmas (the honest per-epoch replacements)\<close>

text \<open>
  HONESTY FENCE (mandatory): these are DISCHARGE facts, not tightness
  results.  The load-bearing-ness of the Running-start and crash-closure
  premises remains witnessed at the implementation layer --- cited above
  (@{thm [source] running_start_is_load_bearing},
  @{thm [source] crash_closed_is_load_bearing}) --- and discharging a
  premise on ONE machine is not evidence the premise is redundant in the
  \<open>\<forall>\<close>-statement: the landed controls prove it is not.  The epoch-0
  start-Running discharge is the Segments foundation's
  @{thm [source] dwe_init_core_running} (this theory's design draft of
  the same statement was canonicalized away, gate finding F4); the
  post-Resume discharge is @{thm [source] post_resume_core_running}.
  The crash-enabledness discharge is new here:
\<close>

lemma dwe_crash_enabled_at_running_core:
  assumes "exec_status (dwe_core t) = Running"
  shows "\<exists>t'. dwe_step t (Crash c) t'"
proof -
  have c: "dw_exec_step (dwe_core t) (Crash c)
             ((dwe_core t)\<lparr>exec_status := Crashed c\<rparr>)"
    by (rule dw_exec_step.crash[OF assms])
  have "dwe_step t (Crash c) (t\<lparr>dwe_core := (dwe_core t)\<lparr>exec_status := Crashed c\<rparr>\<rparr>)"
    by (rule dwe_lift_nonpubI[OF c]) simp_all
  then show ?thesis by blast
qed

section \<open>5.3 Machine-native refinement controls (the cyclic-only additions)\<close>

text \<open>
  The refinement axis is the one the cycle genuinely enriches: the
  promoted machine ITSELF exits the refining class, at a REACHABLE
  state, and Resume is the exact exiting rule.  First the reachable seam
  inhabitant, machine-level:
\<close>

theorem cyclic_refinement_seam_reachable:
  "\<exists>t t'. dwe_reachable t \<and> dwe_resume t t'
        \<and> \<not> (\<exists>a. dw_exec_step (dwe_core t) a (dwe_core t'))"
  using reach_t_fin res_f resume_breaks_core_simulation[OF res_f] by blast

text \<open>
  The machine packaged at the LANDED implementation record
  @{typ "((nat, nat) dwe_state, nat, nat) dual_write_implementation"}:
  the label fragment alone refines; adding Resume (under an arbitrary
  label) exits the refining class.

  HONESTY FENCES (mandatory): (i) the label assignment for Resume
  (@{term "Observe f"}) is ARBITRARY packaging --- the record forces a
  @{typ "('k, 'v) dw_exec_label"}, and the failure is label-independent
  (@{thm [source] resume_breaks_core_simulation} kills every label at
  once).  (ii) The reconcile is EXCLUDED from the packaging because it
  is outside the implementation layer on BOTH architectures --- it is
  recovery-grammar content (plan \S7 item 7); even on the terminal
  machine the wrapper-as-a-whole never refined @{const dw_exec_step}.
  Resume is the only wrapper rule alien to the recovery grammar as well,
  and THAT is the seam being made implementation-level here; blaming the
  reconcile's non-refinement on the cycle would be an overclaim.
  (iii) @{text I_cyclic_lr} below is a machine-native INHABITANT of the
  non-refining class (a designed boundary certificate in the G1
  tradition, mirroring
  @{thm [source] refining_structurally_required_in_converse}) --- NOT a
  new falsifier: the falsifying members of the non-refining class remain
  the landed L1 witnesses, cited in the inventory above.  Cross-reference:
  the converse theory's @{text canonical_dwe_implementation} packages the
  same machine at a NEW record type over the full cyclic action grammar
  and SUCCEEDS at refining its own machine --- the landed-record
  packaging here FAILS refinement against the landed core; the pair is
  the L1 type-escape story one tier up, complementary by design.
\<close>

definition I_cyclic_labels
  :: "((nat, nat) dwe_state, nat, nat) dual_write_implementation"
where
  "I_cyclic_labels =
     \<lparr> dwi_initial = dwe_init Map.empty {0, 1} ec2,
       dwi_step = (\<lambda>t a t'. dwe_step t a t'),
       dwi_state = dwe_core \<rparr>"

definition I_cyclic_lr
  :: "((nat, nat) dwe_state, nat, nat) dual_write_implementation"
where
  "I_cyclic_lr =
     \<lparr> dwi_initial = dwe_init Map.empty {0, 1} ec2,
       dwi_step = (\<lambda>t a t'. dwe_step t a t'
                          \<or> ((\<exists>f. a = Observe f) \<and> dwe_resume t t')),
       dwi_state = dwe_core \<rparr>"

lemma I_cyclic_labels_sel [simp]:
  "dwi_initial I_cyclic_labels = dwe_init Map.empty {0, 1} ec2"
  "dwi_step I_cyclic_labels = (\<lambda>t a t'. dwe_step t a t')"
  "dwi_state I_cyclic_labels = dwe_core"
  by (simp_all add: I_cyclic_labels_def)

lemma I_cyclic_lr_sel [simp]:
  "dwi_initial I_cyclic_lr = dwe_init Map.empty {0, 1} ec2"
  "dwi_step I_cyclic_lr = (\<lambda>t a t'. dwe_step t a t'
                          \<or> ((\<exists>f. a = Observe f) \<and> dwe_resume t t'))"
  "dwi_state I_cyclic_lr = dwe_core"
  by (simp_all add: I_cyclic_lr_def)

lemma I_cyclic_labels_refines: "dwi_refines_exec I_cyclic_labels"
  by (auto simp: dwi_refines_exec_def intro: dwe_step_core)

subsection \<open>The label+Resume fragment: premise checklist\<close>

lemma I_cyclic_lr_crash_closed: "crash_closed_implementation I_cyclic_lr"
  unfolding crash_closed_implementation_def
proof (intro allI impI, elim conjE)
  fix s :: "(nat, nat) dwe_state" and c :: frontier
  assume "exec_status (dwi_state I_cyclic_lr s) = Running"
  then have run: "exec_status (dwe_core s) = Running" by simp
  obtain s' where "dwe_step s (Crash c) s'"
    using dwe_crash_enabled_at_running_core[OF run] by blast
  then have "dwi_step I_cyclic_lr s (Crash c) s'" by simp
  then show "\<exists>s'. dwi_step I_cyclic_lr s (Crash c) s'" by blast
qed

lemma I_cyclic_lr_start_running:
  "exec_status (dwi_state I_cyclic_lr (dwi_initial I_cyclic_lr)) = Running"
  by (simp add: dwe_init_core_running)

lemma I_cyclic_lr_not_refines: "\<not> dwi_refines_exec I_cyclic_lr"
proof
  assume ref: "dwi_refines_exec I_cyclic_lr"
  have step: "dwi_step I_cyclic_lr t_fin_w (Observe ec2) f_run_w"
    using res_f by simp
  from ref step have "dw_exec_step (dwi_state I_cyclic_lr t_fin_w) (Observe ec2)
                        (dwi_state I_cyclic_lr f_run_w)"
    unfolding dwi_refines_exec_def by blast
  then have "dw_exec_step (dwe_core t_fin_w) (Observe ec2) (dwe_core f_run_w)"
    by simp
  with resume_breaks_core_simulation[OF res_f] show False by blast
qed

subsection \<open>Both sides of the landed biconditional are genuinely false\<close>

text \<open>
  The @{const dwi_trace} notion carries NO wellformedness guards (unlike
  @{const dwe_temporal_trace}), so the banked witness steps chain into
  it directly.
\<close>

lemma I_cyclic_lr_stepI:
  assumes "dwe_step t a t'"
  shows "dwi_step I_cyclic_lr t a t'"
  using assms by simp

lemma I_cyclic_lr_trace_t_mid:
  "dwi_trace I_cyclic_lr (dwi_initial I_cyclic_lr) witness_labels t_mid_w"
proof -
  have "dwi_trace I_cyclic_lr W0 witness_labels t_mid_w"
    unfolding witness_labels_def
    by (rule dwi_trace.dwi_trace_step[OF I_cyclic_lr_stepI[OF ws1]
             dwi_trace.dwi_trace_step[OF I_cyclic_lr_stepI[OF ws2]
             dwi_trace.dwi_trace_step[OF I_cyclic_lr_stepI[OF ws3]
             dwi_trace.dwi_trace_step[OF I_cyclic_lr_stepI[OF ws4]
             dwi_trace.dwi_trace_step[OF I_cyclic_lr_stepI[OF ws5]
             dwi_trace.dwi_trace_step[OF I_cyclic_lr_stepI[OF ws6]
             dwi_trace.dwi_trace_refl]]]]]])
  then show ?thesis by (simp add: W0_init)
qed

lemma I_cyclic_lr_trace_W4:
  "dwi_trace I_cyclic_lr (dwi_initial I_cyclic_lr)
     [DoSource ec1 e1, EnqueueDownstream ec1 e1, DoDownstream ec1 e1,
      DoSource ec2 e2] W4"
proof -
  have "dwi_trace I_cyclic_lr W0
          [DoSource ec1 e1, EnqueueDownstream ec1 e1, DoDownstream ec1 e1,
           DoSource ec2 e2] W4"
    by (rule dwi_trace.dwi_trace_step[OF I_cyclic_lr_stepI[OF ws1]
             dwi_trace.dwi_trace_step[OF I_cyclic_lr_stepI[OF ws2]
             dwi_trace.dwi_trace_step[OF I_cyclic_lr_stepI[OF ws3]
             dwi_trace.dwi_trace_step[OF I_cyclic_lr_stepI[OF ws4]
             dwi_trace.dwi_trace_refl]]]])
  then show ?thesis by (simp add: W0_init)
qed

lemma I_cyclic_lr_unsafe:
  "implementation_has_reachable_observable_bad_crash I_cyclic_lr"
proof -
  have "reachable_observable_bad_crash I_cyclic_lr witness_labels ec2 1 t_mid_w"
    unfolding reachable_observable_bad_crash_def
    using I_cyclic_lr_trace_t_mid t_mid_mismatch
          observable_mismatch_imp_diverges[OF t_mid_mismatch]
    by simp
  then show ?thesis
    unfolding implementation_has_reachable_observable_bad_crash_def by blast
qed

lemma W4_running_mismatch:
  "mismatch_at (proto_of_exec_at (dwe_core W4) ec2) ec2 1"
  by (simp add: W4_def eval_defs eval_nat_numeral)

lemma I_cyclic_lr_not_faithful: "\<not> running_image_faithful I_cyclic_lr"
proof
  assume rif: "running_image_faithful I_cyclic_lr"
  have run: "exec_status (dwe_core W4) = Running"
    by (simp add: W4_def mkT_def mkC_def)
  have fin: "ec2 \<le> exec_finish (dwe_core W4)"
    by (simp add: W4_def mkT_def mkC_def)
  have inst: "dwi_trace I_cyclic_lr (dwi_initial I_cyclic_lr)
                [DoSource ec1 e1, EnqueueDownstream ec1 e1,
                 DoDownstream ec1 e1, DoSource ec2 e2] W4
            \<and> exec_status (dwi_state I_cyclic_lr W4) = Running
            \<and> ec2 \<le> exec_finish (dwi_state I_cyclic_lr W4)"
    using I_cyclic_lr_trace_W4 run fin by simp
  have "\<not> mismatch_at (proto_of_exec_at (dwi_state I_cyclic_lr W4) ec2) ec2 1"
    by (rule rif[unfolded running_image_faithful_def, rule_format, OF inst])
  then show False
    using W4_running_mismatch by simp
qed

subsection \<open>The assembled controls\<close>

theorem cyclic_resume_exits_refining_class:
  "crash_closed_implementation I_cyclic_lr
 \<and> exec_status (dwi_state I_cyclic_lr (dwi_initial I_cyclic_lr)) = Running
 \<and> \<not> dwi_refines_exec I_cyclic_lr
 \<and> ((\<not> implementation_has_reachable_observable_bad_crash I_cyclic_lr)
      \<longleftrightarrow> running_image_faithful I_cyclic_lr)"
  using I_cyclic_lr_crash_closed I_cyclic_lr_start_running
        I_cyclic_lr_not_refines I_cyclic_lr_unsafe I_cyclic_lr_not_faithful
  by blast

theorem I_cyclic_lr_both_sides_genuinely_false:
  "implementation_has_reachable_observable_bad_crash I_cyclic_lr
 \<and> \<not> running_image_faithful I_cyclic_lr"
  using I_cyclic_lr_unsafe I_cyclic_lr_not_faithful by blast

section \<open>5.4 Epoch-1 recurrence control\<close>

text \<open>
  The landed tightness story is anchored at witness states reachable
  from the initial state (epoch 0).  The cyclic machine's new reachable
  family --- post-Resume Running states with non-empty ledgers
  (@{thm [source] post_resume_running_reachable}) --- supports the same
  loaded shapes one epoch up: from @{const f_run_w} one lifted
  equal-coordinate re-commit (legal: WF-H1 is \<open>\<le>\<close>; the same
  disclosed-premise note as the completeness theory's epoch-1 witness
  applies, and the witness does NOT assume
  @{text strictly_ascending_source}) produces a Running scoped mismatch
  in epoch 1 with epoch-0 emissions in the ledger.

  Reading (the honest wording): the state family that makes the landed
  ``reachable Running frontier'' arguments re-scope per epoch is
  INHABITED at epoch 1 with a genuinely loaded window --- the per-epoch
  re-verification of the tightness axis is not hypothetical hygiene.
  NOT claimed: any new falsification of any landed theorem.  (The
  completeness theory's durability witness extends this same chain to
  an acked violation; this theorem banks the Running-mismatch recurrence
  the tightness prose consumes.)
\<close>

definition f_mis_w :: "(nat, nat) dwe_state" where
  "f_mis_w = mkT (mkC [(ec1, e1), (ec2, e2), (ec2, Insert 0 5)]
                    [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)] {} Running)
                 [(1, 0, ec1, e1), (2, 0, ec1, e1), (2, 0, ec2, e2)] 1"

lemma g_f_run_mis:
  "exec_label_preserves_history_wf (dwe_core f_run_w) (DoSource ec2 (Insert 0 5))"
  by (simp add: f_run_w_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma ws_fm1: "dwe_step f_run_w (DoSource ec2 (Insert 0 5)) f_mis_w"
proof -
  have c: "dw_exec_step (dwe_core f_run_w) (DoSource ec2 (Insert 0 5))
             (dwe_core f_mis_w)"
    by (rule do_sourceI) (simp_all add: f_run_w_def f_mis_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: f_run_w_def f_mis_w_def mkT_def)
qed

lemma reach_f_mis: "dwe_reachable f_mis_w"
  by (rule dwe_reachable_label_ext[OF reach_f_run wf_f_run g_f_run_mis ws_fm1])

lemma f_mis_mismatch:
  "mismatch_at (proto_of_exec_at (dwe_core f_mis_w) ec2) ec2 0"
  by (simp add: f_mis_w_def eval_defs eval_nat_numeral)

theorem epoch1_running_mismatch_reachable:
  "\<exists>t. dwe_reachable t \<and> dwe_epoch t = 1
     \<and> exec_status (dwe_core t) = Running
     \<and> mismatch_at (proto_of_exec_at (dwe_core t) ec2) ec2 0
     \<and> genuinely_emitting t"
proof (intro exI[of _ f_mis_w] conjI)
  show "dwe_reachable f_mis_w" by (rule reach_f_mis)
  show "dwe_epoch f_mis_w = 1" by (simp add: f_mis_w_def mkT_def)
  show "exec_status (dwe_core f_mis_w) = Running"
    by (simp add: f_mis_w_def mkT_def mkC_def)
  show "mismatch_at (proto_of_exec_at (dwe_core f_mis_w) ec2) ec2 0"
    by (rule f_mis_mismatch)
  show "genuinely_emitting f_mis_w"
    by (simp add: f_mis_w_def mkT_def genuinely_emitting_def)
qed

end
