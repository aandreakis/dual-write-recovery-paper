(*  Title:       Dual_Write_Effect_Cyclic_Class_Violation.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    The cyclic machine is OFF the absorbing-atomic-recovery class, at
    the absorbing assumption (theory-backlog item K, slice K3) --- an
    additive post-freeze slice under the freeze's own protocol: no
    landed statement, proof, definition, name, import, or session-DAG
    change to the frozen corpus.

    THIS THEORY LIVES ON THE CYCLIC (promoted operational) BRANCH.  It
    imports the branch-neutral class theory
    (Dual_Write_Effect_Recovery_Class) and the landed cyclic lane
    (Dual_Write_Effect_Dilemma, through it Dual_Write_Effect_Cyclic);
    nothing terminal sits in its import cone (the freeze's namespace
    rule; the terminal branch's membership certificate is this theory's
    sibling on the other branch, cited as prose only).

    WHAT IT PACKAGES --- WITNESS/CONTROL THROUGHOUT, NO NEW LAW.  The
    class theory's necessity control N1 (one extra rule exits the
    absorbed status, and the equal-core observation-divergent crashed
    pair becomes reachable) is an abstract toy BY DESIGN; this theory
    exhibits the same pole ON THE REAL MACHINE, from landed evidence
    alone: (i) the Resume rule exits the absorbed status --- every
    dwe_resume step starts absorbed and ends not absorbed, realized at
    the landed reachable witness pair t_fin_w/f_run_w (the landed
    designed control recovered_not_absorbing_cyclic and the
    amplification witness resume_cycle_amplification are the same
    evidence one branch-file later, cited as prose --- the freeze's
    namespace rule keeps that file out of this cone); hence (ii) NO
    completion of the class parameters --- no init family, no core
    projection, no observable, no anchor, no crashed predicate ---
    makes the cyclic machine's unified transition relation a class
    member at the Recovered reading of absorbed, because the violated
    assumption mentions only the step relation and the absorbed
    predicate; and (iii) the landed dilemma pair d1_w/d2_w IS a
    reachable equal-core payload-divergent crashed pair --- the exact
    certificate shape the class law rules out for members, reachable
    here (payload projections [(ec1, e1), (ec2, e2)] vs [(ec1, e1)],
    computed below from the landed public definitions).

    THE TWO FACTS ARE PACKAGED SIDE BY SIDE, NOT DERIVED FROM EACH
    OTHER.  Class-membership failure does NOT imply pair reachability
    in general (the class theory records the counterexample; the law is
    one-directional and stays so); the pair's reachability here is the
    landed dilemma chain's own theorem (reach_d1/reach_d2), proved long
    before this slice, and this theory only restates its class-shaped
    face.  Nothing below states or suggests a converse, and the class
    law's \<forall> stays on the inexpressibility side: the landed defeat
    theorems keep their exists-system polarity untouched --- this
    theory adds NO defeat claim and NO impossibility claim; it is the
    load-bearing-premise certificate for the class law's absorbing
    assumption, in vivo.

    "ABSORBED" IS THE CLASS-SCOPED READING exec_status = Recovered.
    On this machine Recovered is deliberately NOT absorbing --- that is
    the machine's designed purpose (owner decision D5's cycle), and
    the landed corpus already says so; this theory turns that designed
    break into the statement "off-class at the absorbing assumption"
    without making or implying any whole-trace absorption claim about
    any machine.

    PROVENANCE: theory-backlog item K
    (paper/dual_write/theory_backlog/BACKLOG_EXPLORATION.md section 6,
    flipped to conditional candidate by the design spike
    paper/dual_write/theory_backlog/KL_LOCALE_DESIGN.md, whose section
    5 pins the two-divergence-sources package and its
    NOT-an-iff fence).

    In-source ML oracle gates are STRIPPED at landing: oracle-freedom
    is certified by scratch-side per-slice gate sessions with
    confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Cyclic_Class_Violation
  imports Dual_Write_Effect_Recovery_Class
          Dual_Write_Effect_Dilemma
begin

section \<open>The cyclic unified step and the absorbed reading\<close>

text \<open>
  The cyclic machine's OWN temporal action vocabulary
  (@{typ "('k, 'v) dwe_action"} of the cyclic branch:
  @{const DWE_Label}, @{const DWE_Reconcile}, @{const DWE_Resume})
  already tags all three transition kinds, so the unified step is a
  case split over the landed type, mirroring the terminal sibling's
  construction one constructor wider.  Only these two parameter slots
  are pinned in this theory --- the step relation and the absorbed
  reading --- because the class assumption the machine violates
  (@{text absorbing}) mentions no other slot.
\<close>

definition cyclic_class_step
  :: "('k, 'v) dwe_state \<Rightarrow> ('k, 'v) dwe_action \<Rightarrow>
      ('k, 'v) dwe_state \<Rightarrow> bool"
where
  "cyclic_class_step t a t' \<longleftrightarrow>
     (case a of
        DWE_Label l \<Rightarrow> dwe_step t l t'
      | DWE_Reconcile m f \<Rightarrow> emitting_reconcile m t f t'
      | DWE_Resume \<Rightarrow> dwe_resume t t')"

definition cyclic_class_absorbed :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "cyclic_class_absorbed t \<longleftrightarrow> exec_status (dwe_core t) = Recovered"

section \<open>Resume exits the absorbed status --- every time, and reachably\<close>

text \<open>Both facts are one unfolding of the landed @{const dwe_resume}:
  a resume step fires FROM the absorbed status and lands OUTSIDE it
  (status @{const Running}).  This is the machine-level content of the
  class theory's N1 pole.\<close>

lemma dwe_resume_from_absorbed:
  assumes "dwe_resume t t'"
  shows "cyclic_class_absorbed t"
  using assms by (simp add: dwe_resume_def cyclic_class_absorbed_def)

lemma dwe_resume_exits_absorbed:
  assumes "dwe_resume t t'"
  shows "\<not> cyclic_class_absorbed t'"
  using assms by (auto simp: dwe_resume_def cyclic_class_absorbed_def)

text \<open>
  The violation REALIZED IN VIVO: at the landed reachable witnesses
  @{const t_fin_w} (post-reconcile, absorbed) and @{const f_run_w}
  (post-resume, running) --- the landed facts
  @{thm [source] reach_t_fin}, @{thm [source] reach_f_run},
  @{thm [source] res_f} consumed verbatim --- one unified step of the
  cyclic machine leaves the absorbed status from a REACHABLE absorbed
  state.  The landed designed control
  @{text recovered_not_absorbing_cyclic}
  (@{text Dual_Write_Effect_Segment_Boundaries}, outside this import cone)
  packages the same landed evidence for the per-segment scoping story;
  this theorem packages it for the class story.
\<close>

theorem cyclic_class_absorbing_violated:
  "\<exists>t a t'. dwe_reachable t \<and> dwe_reachable t'
          \<and> cyclic_class_step t a t'
          \<and> cyclic_class_absorbed t \<and> \<not> cyclic_class_absorbed t'"
proof -
  have step: "cyclic_class_step t_fin_w DWE_Resume f_run_w"
    by (simp add: cyclic_class_step_def res_f)
  show ?thesis
    using reach_t_fin reach_f_run step
          dwe_resume_from_absorbed[OF res_f]
          dwe_resume_exits_absorbed[OF res_f]
    by blast
qed

section \<open>OFF-CLASS: no parameter completion yields membership\<close>

text \<open>
  The probe state below is the init state with its status set to
  @{const Recovered} --- a state OF THE TYPE, deliberately NOT claimed
  reachable (the house control posture; the reachable realization is
  the theorem above, monomorphic at the landed witness machine).  Its
  purpose is generality: with it the no-membership statement holds at
  EVERY type instance and EVERY choice of the remaining five class
  parameters, because the @{text absorbing} assumption of the class
  quantifies over ALL steps of the relation --- reachable or not ---
  and mentions only the step relation and the absorbed predicate.
\<close>

definition off_class_probe_w :: "('k, 'v) dwe_state" where
  "off_class_probe_w =
     (dwe_init Map.empty {} ec1)
       \<lparr>dwe_core := (dwe_core (dwe_init Map.empty {} ec1))
          \<lparr>exec_status := Recovered\<rparr>\<rparr>"

definition off_class_probe_w' :: "('k, 'v) dwe_state" where
  "off_class_probe_w' =
     off_class_probe_w
       \<lparr>dwe_core := (dwe_core off_class_probe_w)\<lparr>exec_status := Running\<rparr>,
        dwe_epoch := Suc 0\<rparr>"

lemma off_class_probe_resume:
  "dwe_resume off_class_probe_w off_class_probe_w'"
  by (simp add: dwe_resume_def off_class_probe_w_def off_class_probe_w'_def
                dwe_init_def initial_exec_state_def)

theorem cyclic_off_class:
  "\<not> absorbing_atomic_recovery cyclic_class_step inits core obs anchor
       cyclic_class_absorbed crashed"
proof
  assume mem: "absorbing_atomic_recovery cyclic_class_step inits core obs
                 anchor cyclic_class_absorbed crashed"
  have step: "cyclic_class_step off_class_probe_w DWE_Resume off_class_probe_w'"
    by (simp add: cyclic_class_step_def off_class_probe_resume)
  show False
    using absorbing_atomic_recovery.absorbing
            [OF mem step dwe_resume_from_absorbed[OF off_class_probe_resume]]
          dwe_resume_exits_absorbed[OF off_class_probe_resume]
    by blast
qed

section \<open>The landed dilemma pair, in the class law's certificate shape\<close>

text \<open>
  The landed pair @{const d1_w} / @{const d2_w} (the dilemma theory's
  designed-in equal-core divergent-ledger pair, its reachability the
  landed @{thm [source] reach_d1} / @{thm [source] reach_d2}) is
  exactly the shape the class law rules out for class members: two
  reachable crashed states, equal cores, divergent payload
  projections.  The payload projections are computed from the landed
  public definitions --- nothing about the pair is re-proved, and its
  reachability is NOT inferred from the off-class facts above (no such
  inference exists: the law is one-directional).  Stated in the
  machine's own landed reachability vocabulary; the class's reach is
  never instantiated on this machine (there is no membership to
  instantiate it through).
\<close>

lemma d_pair_payload_values:
  "map e_payload (dwe_emitted d1_w) = [(ec1, e1), (ec2, e2)]"
  "map e_payload (dwe_emitted d2_w) = [(ec1, e1)]"
  by (simp_all add: d1_fields d2_fields)

lemma d_pair_payload_divergent:
  "map e_payload (dwe_emitted d1_w) \<noteq> map e_payload (dwe_emitted d2_w)"
  by (simp add: d_pair_payload_values)

theorem cyclic_divergent_crashed_pair_witness:
  "dwe_reachable d1_w \<and> dwe_reachable d2_w
 \<and> (\<exists>c. exec_status (dwe_core d1_w) = Crashed c)
 \<and> (\<exists>c'. exec_status (dwe_core d2_w) = Crashed c')
 \<and> dwe_core d1_w = dwe_core d2_w
 \<and> map e_payload (dwe_emitted d1_w) \<noteq> map e_payload (dwe_emitted d2_w)"
  using reach_d1 reach_d2 d1_fields(1) d2_fields(1) d_cores_eq
        d_pair_payload_divergent
  by blast

theorem cyclic_divergent_crashed_pair:
  "\<exists>t t'. dwe_reachable t \<and> dwe_reachable t'
        \<and> (\<exists>c. exec_status (dwe_core t) = Crashed c)
        \<and> (\<exists>c'. exec_status (dwe_core t') = Crashed c')
        \<and> dwe_core t = dwe_core t'
        \<and> map e_payload (dwe_emitted t) \<noteq> map e_payload (dwe_emitted t')"
  using cyclic_divergent_crashed_pair_witness by blast


end
