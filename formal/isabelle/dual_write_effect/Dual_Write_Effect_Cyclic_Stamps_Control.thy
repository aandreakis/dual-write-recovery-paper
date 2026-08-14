(*  Title:       Dual_Write_Effect_Cyclic_Stamps_Control.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    The load-bearing stamp-invariant control restated on the promoted
    OPERATIONAL (cyclic) machine (theory-backlog item B) --- an additive
    post-freeze slice under the freeze's own protocol: no landed
    statement, proof, definition, name, import, or session-DAG change to
    the frozen corpus.

    WHAT THE CONTROL GUARDS.  The cyclic monotonicity family is premised
    on the stamp invariant: effect_unsafe_monotone shows that on
    stamp-bounded states no transition of any kind (label, reconcile,
    Resume) heals effect_unsafe, and reachability discharges that
    premise (dwe_reachable_stamps_bounded).  This theory witnesses the
    premise LOAD-BEARING on this machine: at a state OUTSIDE the
    invariant --- an emission stamped beyond the committed source prefix
    --- one source-commit label step, injected into the same
    label/reconcile/Resume wrapper the monotonicity theorem consumes,
    retroactively justifies the over-stamped entry and heals
    effect_unsafe.  This is a control, not a defect: the machine itself
    cannot fire an emission stamped beyond its own committed history, so
    the control state is off the reachable set by design.

    TWIN DISCLOSURE (freeze process rule 1, statement fingerprint).  The
    terminal branch banks the same control shape at its own record:
    stamps_premise_load_bearing in the terminal Witnesses theory.  The
    two statements are ANALOGOUS, NOT IDENTICAL --- a whitespace-
    normalized statement comparison distinguishes them: the record here
    carries the wrapper-level dwe_epoch field the terminal record does
    not have, and the transition position here is the cyclic three-way
    wrapper (label step, emitting reconcile, Resume) matching this
    machine's single monotonicity theorem, where the terminal control
    quantifies over that branch's label-step relation alone, matching
    its per-kind monotonicity theorems.  The shared name follows the
    established two-branch twin pattern of this session
    (dwe_duplicate_separation, effect_nonvacuity_safe,
    four_corner_independence, and the record name dwe_state itself);
    the branches share no import cone, and cross-branch references stay
    at the prose level per the freeze's namespace rule.

    WHAT THIS CLOSES.  The S6 review had verified by probe that the
    cyclic analogue of the terminal control holds; this theory replaces
    that analogy-suffices note with a landed theorem --- control-set
    symmetry on the promoted machine: both branches now carry the
    stamp-invariant control at their own record.

    PROVENANCE: theory-backlog item B
    (paper/dual_write/theory_backlog/BACKLOG_EXPLORATION.md section 1;
    S6 review section C defer list; Table 2 "What heals" row of
    MODEL_BOUNDARY_CONTRACTS.md).  Everything below is stated over the
    cyclic-branch machine alone; the import is that single sibling.

    In-source ML oracle gates are STRIPPED at landing: oracle-freedom is
    certified by scratch-side per-slice gate sessions with
    confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Cyclic_Stamps_Control
  imports Dual_Write_Effect_Cyclic
begin

section \<open>Definition-strength control: the stamp invariant in the cyclic
  monotonicity family is load-bearing\<close>

text \<open>
  On states OUTSIDE the reachable set (an over-shooting stamp), a later
  source commit can retroactively justify an emission --- so the cyclic
  monotonicity theorem @{thm [source] effect_unsafe_monotone} (and its
  reachable corollary @{thm [source] effect_unsafe_monotone_reachable})
  genuinely needs @{const stamps_bounded}, which
  @{thm [source] dwe_reachable_stamps_bounded} discharges on every
  reachable state.  This is a control, not a defect: the machine itself
  cannot fire an emission stamped beyond its own committed history ---
  every emitting rule stamps with the CURRENT committed prefix length,
  which is exactly what the invariant proof of
  @{thm [source] dwe_reachable_stamps_bounded} tracks through all four
  rule kinds, Resume included.

  The control statement below drops exactly the @{const stamps_bounded}
  premise of @{thm [source] effect_unsafe_monotone} and exhibits
  healing, quantifying over the same three-way transition wrapper
  (label step, emitting reconcile, Resume) that theorem consumes; the
  witness transition is a @{const DoSource} label step, injected as the
  wrapper's label disjunct.  The added @{const dwe_epoch} field of this
  machine's record rides along inert (label steps preserve it,
  @{thm [source] dwe_step_epoch_const}; both witness states sit in
  epoch 0): the healing is stamp-versus-history arithmetic, exactly as
  on the terminal branch.
\<close>

text \<open>
  TWIN DISCLOSURE (freeze process rule 1, statement fingerprint) and
  what this slice closes.  The terminal branch banks the same control
  shape at its own record: @{text stamps_premise_load_bearing} in the
  terminal @{text Dual_Write_Effect_Witnesses} theory --- a prose
  citation, deliberately not an import (the freeze's namespace rule
  keeps the two branches import-disjoint; they share names by design).
  The two statements are analogous, not statement-identical: the
  record here carries @{const dwe_epoch}, and the transition position
  here is the three-way wrapper matching
  @{thm [source] effect_unsafe_monotone}, where the terminal control
  quantifies over that branch's label-step relation alone, matching
  its per-kind monotonicity theorems.  The S6 review had verified the
  cyclic analogue by probe; this theory replaces that analogy-suffices
  note with a landed theorem: control-set symmetry --- both branches
  now carry the stamp-invariant control at their own record.
\<close>

text \<open>
  The witness pair, in this theory's own literal-state style: an
  over-stamped ledger --- one emission stamped 1 (and tagged epoch 0)
  against an EMPTY committed source history --- so the entry is
  premature (hence @{const effect_unsafe}) and the state violates
  @{const stamps_bounded}.  One @{const DoSource} step commits the
  matching event: the stamp is now in bounds and the payload sits in
  the stamped prefix, so the post-state is effect-safe.  One step
  healed @{const effect_unsafe} outside the invariant.
\<close>

definition nc_t_w :: "(nat, nat) dwe_state" where
  "nc_t_w = mkT (mkC [] [] [] {} Running) [(1, 0, ec1, e1)] 0"

definition nc_t'_w :: "(nat, nat) dwe_state" where
  "nc_t'_w = mkT (mkC [(ec1, e1)] [] [] {} Running) [(1, 0, ec1, e1)] 0"

lemma nc_not_bounded: "\<not> stamps_bounded nc_t_w"
  by (simp add: stamps_bounded_def nc_t_w_def mkT_def mkC_def)

lemma nc_unsafe: "effect_unsafe nc_t_w"
  by (simp add: effect_unsafe_def premature_def justified_at_def
                nc_t_w_def mkT_def mkC_def)

lemma nc_step: "dwe_step nc_t_w (DoSource ec1 e1) nc_t'_w"
proof -
  have c: "dw_exec_step (dwe_core nc_t_w) (DoSource ec1 e1) (dwe_core nc_t'_w)"
    by (rule do_sourceI) (simp_all add: nc_t_w_def nc_t'_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: nc_t_w_def nc_t'_w_def mkT_def)
qed

lemma nc_safe': "\<not> effect_unsafe nc_t'_w"
  by (simp add: effect_unsafe_def premature_def duplicate_def justified_at_def
                nc_t'_w_def mkT_def mkC_def eval_nat_numeral)

text \<open>
  The packaged control.  Premise-for-premise against
  @{thm [source] effect_unsafe_monotone}: the transition wrapper and the
  @{const effect_unsafe} pre-state premise are kept, the
  @{const stamps_bounded} premise is dropped, and the conclusion is
  negated --- so the invariant premise is exactly what stands between
  the monotonicity theorem and this counterexample.  The reconcile
  parameters @{term "m :: nat"} and @{term f} are existentially bound
  because the wrapper mentions them; the witness inhabits the label
  disjunct, so their instantiation is immaterial.
\<close>

theorem stamps_premise_load_bearing:
  "\<exists>(t :: (nat, nat) dwe_state) t' a m f.
     (dwe_step t a t' \<or> emitting_reconcile m t f t' \<or> dwe_resume t t')
   \<and> \<not> stamps_bounded t
   \<and> effect_unsafe t
   \<and> \<not> effect_unsafe t'"
proof -
  have "(dwe_step nc_t_w (DoSource ec1 e1) nc_t'_w
         \<or> emitting_reconcile 0 nc_t_w ec1 nc_t'_w
         \<or> dwe_resume nc_t_w nc_t'_w)
      \<and> \<not> stamps_bounded nc_t_w
      \<and> effect_unsafe nc_t_w
      \<and> \<not> effect_unsafe nc_t'_w"
    using nc_step nc_not_bounded nc_unsafe nc_safe' by blast
  then show ?thesis by blast
qed

end
