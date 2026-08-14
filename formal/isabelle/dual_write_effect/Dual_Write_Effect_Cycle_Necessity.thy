(*  Title:       Dual_Write_Effect_Cycle_Necessity.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Cycle necessity on the machine of record, with the fire-pole
    contrast that witnesses its scope (discovery candidate B-1) --- an
    additive post-freeze slice under the freeze's own protocol: no
    landed statement, proof, definition, name, import, or session-DAG
    change to the frozen corpus.

    THIS THEORY LIVES ON THE CYCLIC (promoted operational) BRANCH.  It
    imports the small-step robustness certificate
    (Dual_Write_Effect_Small_Step) and the cyclic class-violation
    certificate (Dual_Write_Effect_Cyclic_Class_Violation, through it
    the branch-neutral class theory Dual_Write_Effect_Recovery_Class);
    nothing terminal sits in its import cone (the freeze's namespace
    rule; the terminal branch's crashed-sync law and membership
    certificate are cited as prose only).

    WHAT IT PACKAGES.  The landed R1 scope sentence --- "the
    operational dilemma needs the recovery cycle", per-machine, for the
    landed atomic rule set --- is theorem-backed on the TERMINAL
    machine (its inexpressibility law) and at class level (the
    branch-neutral toys isolate the resume pole and the fire pole
    abstractly).  On the machine of record, where the headline law
    actually lives, the per-machine reading had no bearer of its own.
    This theory gives it one, by mining the landed section-21
    separation engine (epoch0_pre_recovery_sync /
    dwe_reachable_epoch0_crashed_sync --- proved there to separate the
    variant from the landed machine, and consumed here unchanged as the
    bearer of record):

    Part 1 (the machine of record).  Before the first Resume --- at
    epoch 0 --- no pair of reachable crashed states of the LANDED
    cyclic machine has equal cores and payload-divergent ledgers: the
    pair's certificate shape is not reachable pre-cycle.  Composed with
    the landed epoch-factorization primitive
    (dwe_trace_no_resume_epoch_const), the trace form follows: a
    reachable equal-core payload-divergent crashed pair REQUIRES a
    Resume in its history.  The necessity is inhabited: the landed
    dilemma pair d1_w/d2_w sits at epoch 1 --- it genuinely consumed
    the cycle.

    Part 2 (the variant, R1's qualifier witnessed).  On the small-step
    variant the same certificate shape is reached WITHOUT any Resume:
    one landed fire step connects t_mid_w to ss_inflight_w --- a
    Resume-free, epoch-0, fire-only variant trace between two
    ss-reachable crashed states with equal cores and payload-divergent
    ledgers.  The same step violates the class's atomic_divergence
    assumption in vivo at ss-reachable states (the class theory's N2
    pole, previously realized only by an abstract toy), and the
    variant's unified step relation is off the class at EVERY
    completion of the five unpinned parameter slots (the sibling's
    off-class route, one rule wider: the inherited Resume violates the
    absorbing assumption).  So R1's qualifier --- "for the landed
    atomic rule set" --- is itself a theorem-level witness, not only a
    disclosure.

    Part 3 (the class tie-back).  The cyclic machine's
    pre-first-recovery fragment IS a class member: at absorbed :=
    Recovered-or-epoch-positive the unified cyclic step interprets the
    section-22 locale, with atomic_divergence discharged through the
    class theory's own guarded-shape adapter fed by the landed
    dwe_step_epoch0_sync (the landed engine lemma IS the guarded shape
    at this absorbed reading).  The Part-1 statement re-derives through
    the class under a new name --- a sanity tie-back, never a
    replacement: the landed dwe_reachable_epoch0_crashed_sync stays the
    bearer of record.  This is the class's second substantive in-vivo
    membership, packaged side by side with the landed off-class fact at
    the Recovered reading (the sibling theory) --- membership at one
    absorbed reading, off-class at the other, the section-24 pattern:
    the two absorbed readings are different predicates and neither fact
    is derived from the other.

    NOT AN IFF, AND NOT A DEFEAT CLAIM.  Every new statement is a
    structural negative, a necessity fact, or a witness fact.  Nothing
    below states or suggests a characterization: "the pair's
    certificate shape requires a Resume in its history" is a fact about
    the certificate shape on this machine, never a statement that any
    dilemma is impossible anywhere, and the landed defeat theorems keep
    their exists-system polarity untouched --- this theory adds NO
    defeat claim, NO impossibility claim about policies, and NO new
    premise on any landed statement.  The landed R1 scope sentence is
    PRESERVED exactly as landed and gains evidence, not new wording:
    whether or not a reader takes the terminal law plus the abstract
    class toys as already answering the per-machine question, these
    theorems only strengthen that story --- no priority claim is made
    for them, and no landed bearer is displaced.

    PROVENANCE: discovery candidate B-1
    (paper/dual_write/theory_review/discovery/LENS_B_GENERALITY.md,
    probe LensB_Probe.thy green x2; shelf items 5-7 there fence what
    this theory deliberately does NOT contain: no abstract transfer
    lemma, no class law without the crashed slot, no replacement of the
    landed sync engine).

    In-source ML oracle gates are STRIPPED at landing: oracle-freedom
    is certified by scratch-side per-slice gate sessions with
    confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Cycle_Necessity
  imports Dual_Write_Effect_Small_Step
          Dual_Write_Effect_Cyclic_Class_Violation
begin

section \<open>Part 1: the certificate shape needs the cycle, on the machine of record\<close>

text \<open>
  The landed separation engine, mined: @{thm [source]
  dwe_reachable_epoch0_crashed_sync} was proved in the small-step slice
  to show the fire-reached in-flight state is cyclic-unreachable; the
  same law says that at epoch 0 every reachable crashed state's ledger
  payload projection equals its core's durable downstream history ---
  so two such states with EQUAL cores cannot have divergent
  projections.  The statement below is the cyclic analogue, at epoch 0,
  of the certificate-shape negative the terminal branch proves at all
  epochs (that branch is outside this import cone; the analogy is
  prose).  It is a structural negative about the PAIR'S CERTIFICATE
  SHAPE; it neither states nor implies anything about re-drive
  policies, and no landed defeat theorem is touched.
\<close>

theorem cyclic_epoch0_no_divergent_crashed_pair:
  "\<not> (\<exists>t t'. dwe_reachable t \<and> dwe_reachable t'
        \<and> dwe_epoch t = 0 \<and> dwe_epoch t' = 0
        \<and> (\<exists>c. exec_status (dwe_core t) = Crashed c)
        \<and> (\<exists>c'. exec_status (dwe_core t') = Crashed c')
        \<and> dwe_core t = dwe_core t'
        \<and> map e_payload (dwe_emitted t) \<noteq> map e_payload (dwe_emitted t'))"
  using dwe_reachable_epoch0_crashed_sync by metis

text \<open>
  The trace form: composed with the landed epoch-factorization
  primitive @{thm [source] dwe_trace_no_resume_epoch_const}, the
  epoch-0 negative becomes a NECESSITY fact about histories --- any two
  traces of the landed machine that exhibit the pair's certificate
  shape carry a Resume between them.  This is the per-machine content
  of the landed R1 scope sentence ("the operational dilemma needs the
  recovery cycle", per-machine, for the landed atomic rule set), stated
  on the machine of record for the certificate shape the headline law's
  pair inhabits.
\<close>

theorem cyclic_divergent_crashed_pair_needs_resume:
  assumes tr1: "dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2) xs
                  (t :: (nat, nat) dwe_state)"
      and tr2: "dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2) ys
                  (t' :: (nat, nat) dwe_state)"
      and c1: "exec_status (dwe_core t) = Crashed c"
      and c2: "exec_status (dwe_core t') = Crashed c'"
      and cores: "dwe_core t = dwe_core t'"
      and divg: "map e_payload (dwe_emitted t) \<noteq> map e_payload (dwe_emitted t')"
  shows "DWE_Resume \<in> set xs \<or> DWE_Resume \<in> set ys"
proof (rule ccontr)
  assume nres: "\<not> (DWE_Resume \<in> set xs \<or> DWE_Resume \<in> set ys)"
  have e1: "dwe_epoch t = 0"
    using dwe_trace_no_resume_epoch_const[OF tr1] nres
    by (simp add: dwe_init_def)
  have e2: "dwe_epoch t' = 0"
    using dwe_trace_no_resume_epoch_const[OF tr2] nres
    by (simp add: dwe_init_def)
  have r1: "dwe_reachable t"
    using tr1 unfolding dwe_reachable_def by blast
  have r2: "dwe_reachable t'"
    using tr2 unfolding dwe_reachable_def by blast
  have s1: "map e_payload (dwe_emitted t) = exec_down_hist (dwe_core t)"
    by (rule dwe_reachable_epoch0_crashed_sync[OF r1 e1 c1])
  have s2: "map e_payload (dwe_emitted t') = exec_down_hist (dwe_core t')"
    by (rule dwe_reachable_epoch0_crashed_sync[OF r2 e2 c2])
  show False using divg s1 s2 cores by simp
qed

text \<open>Non-vacuity of the necessity: the landed dilemma pair lives at
  epoch 1 --- it genuinely consumed the cycle, so the Resume the trace
  theorem demands is the one the landed reachability chains actually
  take.\<close>

lemma landed_pair_lives_at_epoch_one:
  "dwe_epoch d1_w = 1 \<and> dwe_epoch d2_w = 1"
  by (simp add: d1_fields d2_fields)

section \<open>Part 2: the fire-pole contrast on the variant --- R1's qualifier witnessed\<close>

text \<open>
  The variant's OWN action vocabulary (@{type ss_action}) already tags
  all four transition kinds, so its unified step is a case split over
  the landed type --- the sibling theory's construction one rule wider.
  As there, only the slots a violated assumption mentions are pinned;
  everything else stays a free parameter.
\<close>

definition ss_class_step
  :: "(nat, nat) dwe_state \<Rightarrow> ss_action \<Rightarrow> (nat, nat) dwe_state \<Rightarrow> bool"
where
  "ss_class_step t a t' \<longleftrightarrow>
     (case a of
        SS_Label l \<Rightarrow> dwe_step t l t'
      | SS_Reconcile m f \<Rightarrow> emitting_reconcile m t f t'
      | SS_Resume \<Rightarrow> dwe_resume t t'
      | SS_Fire f p \<Rightarrow> ss_fire_one f p t t')"

text \<open>
  One fire step from a synced, non-absorbed, ss-reachable crashed state
  produces a payload-divergent, still-non-absorbed state: the class's
  @{text atomic_divergence} assumption violated IN VIVO, at ss-reachable
  states of a machine of this development --- the class theory's N2
  pole (previously realized only by the abstract per-entry-fire toy),
  at the Recovered reading of absorbed the sibling theory pins.  A
  witness fact about one step of the variant; no law is stated.
\<close>

theorem ss_fire_atomic_divergence_violated:
  "\<exists>t a t'. dwe_ss_reachable t \<and> dwe_ss_reachable t'
       \<and> ss_class_step t a t'
       \<and> \<not> cyclic_class_absorbed t
       \<and> map e_payload (dwe_emitted t) = exec_down_hist (dwe_core t)
       \<and> \<not> (map e_payload (dwe_emitted t') = exec_down_hist (dwe_core t')
            \<or> cyclic_class_absorbed t')"
proof -
  have step: "ss_class_step t_mid_w (SS_Fire ec2 (ec2, e2)) ss_inflight_w"
    by (simp add: ss_class_step_def fire_inflight)
  have sync_mid: "map e_payload (dwe_emitted t_mid_w)
                    = exec_down_hist (dwe_core t_mid_w)"
    by (simp add: t_mid_w_def mkT_def mkC_def)
  have status_mid: "\<not> cyclic_class_absorbed t_mid_w"
    by (simp add: cyclic_class_absorbed_def t_mid_w_def mkT_def mkC_def)
  have div': "map e_payload (dwe_emitted ss_inflight_w)
                \<noteq> exec_down_hist (dwe_core ss_inflight_w)"
    by (simp add: ss_inflight_w_def mkT_def mkC_def)
  have status': "\<not> cyclic_class_absorbed ss_inflight_w"
    by (simp add: cyclic_class_absorbed_def ss_inflight_w_def mkT_def mkC_def)
  have r_mid: "dwe_ss_reachable t_mid_w"
    by (rule ss_reachable_of_reachable[OF reach_t_mid])
  show ?thesis
    using r_mid ss_inflight_ss_reachable step sync_mid status_mid div' status'
    by blast
qed

text \<open>
  OFF-CLASS at every completion of the five unpinned parameter slots,
  via the inherited Resume --- the sibling theory's route, one rule
  wider: the violated @{text absorbing} assumption mentions only the
  step relation and the absorbed predicate, and the variant inherits
  the landed Resume unchanged.  As in the sibling, class-membership
  failure implies nothing about pair reachability (the class law is
  one-directional and stays so); the pair fact below is proved from the
  variant's own physics, never from this.
\<close>

theorem ss_off_class:
  "\<not> absorbing_atomic_recovery ss_class_step inits core obs anchor
       cyclic_class_absorbed crashed"
proof
  assume mem: "absorbing_atomic_recovery ss_class_step inits core obs anchor
                 cyclic_class_absorbed crashed"
  have step: "ss_class_step off_class_probe_w SS_Resume off_class_probe_w'"
    by (simp add: ss_class_step_def off_class_probe_resume)
  show False
    using absorbing_atomic_recovery.absorbing
            [OF mem step dwe_resume_from_absorbed[OF off_class_probe_resume]]
          dwe_resume_exits_absorbed[OF off_class_probe_resume]
    by blast
qed

text \<open>
  The certificate shape WITHOUT the cycle: the landed witnesses
  @{const t_mid_w} and @{const ss_inflight_w} are two ss-reachable
  crashed states with equal cores and payload-divergent ledgers, both
  at epoch 0, connected by a single fire --- a Resume-free, epoch-0,
  fire-only variant trace.  On the landed machine the same shape
  provably requires a Resume in its history (Part 1); on the variant it
  does not.  This is R1's qualifier ("for the landed atomic rule set")
  witnessed at theorem level: adding the per-entry fire rule is exactly
  what forfeits the necessity.  A witness fact about the variant; the
  landed machine's theorems, the landed defeat family, and the
  variant's own dilemma restatements are all untouched by it.
\<close>

theorem ss_divergent_crashed_pair_without_cycle:
  "dwe_ss_reachable t_mid_w \<and> dwe_ss_reachable ss_inflight_w
 \<and> (\<exists>c. exec_status (dwe_core t_mid_w) = Crashed c)
 \<and> (\<exists>c'. exec_status (dwe_core ss_inflight_w) = Crashed c')
 \<and> dwe_core t_mid_w = dwe_core ss_inflight_w
 \<and> map e_payload (dwe_emitted t_mid_w)
     \<noteq> map e_payload (dwe_emitted ss_inflight_w)
 \<and> dwe_epoch t_mid_w = 0 \<and> dwe_epoch ss_inflight_w = 0
 \<and> dwe_ss_temporal_trace t_mid_w [SS_Fire ec2 (ec2, e2)] ss_inflight_w"
proof -
  have r_mid: "dwe_ss_reachable t_mid_w"
    by (rule ss_reachable_of_reachable[OF reach_t_mid])
  have tr: "dwe_ss_temporal_trace t_mid_w [SS_Fire ec2 (ec2, e2)] ss_inflight_w"
    by (rule dwe_ss_temporal_trace.dwe_ss_fire_step[OF fire_inflight
          dwe_ss_temporal_trace.dwe_ss_refl])
  have stat_mid: "exec_status (dwe_core t_mid_w) = Crashed ec2"
    by (simp add: t_mid_w_def mkT_def mkC_def)
  have ep_mid: "dwe_epoch t_mid_w = 0"
    by (simp add: t_mid_w_def mkT_def)
  have pay_mid: "map e_payload (dwe_emitted t_mid_w) = [(ec1, e1)]"
    by (simp add: t_mid_w_def mkT_def)
  show ?thesis
    using r_mid ss_inflight_ss_reachable stat_mid ss_inflight_fields(1)
          ss_inflight_fields(3) pay_mid ss_inflight_fields(4)
          ep_mid ss_inflight_fields(2) tr
    by auto
qed

section \<open>Part 3: the pre-first-recovery fragment is a class member\<close>

text \<open>
  The absorbed reading that carries the membership: a state is absorbed
  once it is Recovered OR its epoch is positive --- the pre-first-
  recovery fragment's exit set.  This is a DIFFERENT predicate from the
  sibling theory's Recovered reading (under which the same unified step
  is provably off-class): membership at one reading beside off-class at
  the other is the section-24 packaging pattern, and neither fact is
  derived from the other.  The landed engine invariant
  @{const epoch0_pre_recovery_sync} is literally the class's guarded
  invariant at this reading (@{text epoch0_inv_iff} below), which is
  why the interpretation discharges from landed facts alone.
\<close>

definition pre_cycle_absorbed :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "pre_cycle_absorbed t \<longleftrightarrow>
     exec_status (dwe_core t) = Recovered \<or> 0 < dwe_epoch t"

definition epoch0_crashed :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "epoch0_crashed t \<longleftrightarrow>
     (\<exists>c. exec_status (dwe_core t) = Crashed c) \<and> dwe_epoch t = 0"

lemma epoch0_inv_iff:
  "epoch0_pre_recovery_sync t \<longleftrightarrow>
     (\<not> pre_cycle_absorbed t \<longrightarrow>
        map e_payload (dwe_emitted t) = exec_down_hist (dwe_core t))"
  by (auto simp: epoch0_pre_recovery_sync_def pre_cycle_absorbed_def)

text \<open>
  The four obligations as named lemmas (house-debuggable), each
  consuming landed facts as-is.  The one genuinely machine-specific
  fact --- the landed @{thm [source] dwe_step_epoch0_sync} --- enters
  through the class theory's guarded-shape adapter exactly as its
  terminal sibling's does, because at this absorbed reading the landed
  engine lemma IS the guarded shape.
\<close>

lemma pre_cycle_init_sync:
  assumes "(t :: (nat, nat) dwe_state) \<in> {dwe_init Map.empty {0, 1} ec2}"
  shows "map e_payload (dwe_emitted t) = exec_down_hist (dwe_core t)"
  using assms by (simp add: dwe_init_def initial_exec_state_def)

lemma pre_cycle_absorbed_preserved:
  assumes step: "cyclic_class_step (t :: (nat, nat) dwe_state) a t'"
      and abs: "pre_cycle_absorbed t"
  shows "pre_cycle_absorbed t'"
proof (cases a)
  case (DWE_Label l)
  then have st: "dwe_step t l t'"
    using step by (simp add: cyclic_class_step_def)
  have ep: "dwe_epoch t' = dwe_epoch t"
    by (rule dwe_step_epoch_const[OF st])
  have core_step: "dw_exec_step (dwe_core t) l (dwe_core t')"
    by (rule dwe_step_core[OF st])
  show ?thesis
    using abs ep recovered_stays_recovered[OF core_step]
    by (auto simp: pre_cycle_absorbed_def)
next
  case (DWE_Reconcile m f)
  then have rec: "emitting_reconcile m t f t'"
    using step by (simp add: cyclic_class_step_def)
  show ?thesis
    using emitting_reconcile_ends_recovered[OF rec]
    by (simp add: pre_cycle_absorbed_def)
next
  case DWE_Resume
  then have res: "dwe_resume t t'"
    using step by (simp add: cyclic_class_step_def)
  show ?thesis
    using dwe_resume_epoch_Suc[OF res]
    by (simp add: pre_cycle_absorbed_def)
qed

text \<open>The landed engine invariant is preserved by every UNIFIED cyclic
  step --- the label case is the landed @{thm [source]
  dwe_step_epoch0_sync} verbatim; the reconcile case lands Recovered
  (@{thm [source] emitting_reconcile_ends_recovered}); the Resume case
  leaves epoch 0 (@{thm [source] dwe_resume_epoch_Suc}) --- so the
  guard is vacuous in both non-label cases.\<close>

lemma cyclic_class_step_epoch0_sync:
  assumes step: "cyclic_class_step (t :: (nat, nat) dwe_state) a t'"
      and inv: "epoch0_pre_recovery_sync t"
  shows "epoch0_pre_recovery_sync t'"
proof (cases a)
  case (DWE_Label l)
  then have st: "dwe_step t l t'"
    using step by (simp add: cyclic_class_step_def)
  show ?thesis
    by (rule dwe_step_epoch0_sync[OF st inv])
next
  case (DWE_Reconcile m f)
  then have rec: "emitting_reconcile m t f t'"
    using step by (simp add: cyclic_class_step_def)
  show ?thesis
    using emitting_reconcile_ends_recovered[OF rec]
    by (simp add: epoch0_pre_recovery_sync_def)
next
  case DWE_Resume
  then have res: "dwe_resume t t'"
    using step by (simp add: cyclic_class_step_def)
  show ?thesis
    using dwe_resume_epoch_Suc[OF res]
    by (simp add: epoch0_pre_recovery_sync_def)
qed

text \<open>The same fact in the adapter's guarded shape (the class
  parameters spelled out via @{thm [source] epoch0_inv_iff}), then
  @{text atomic_divergence} via the class theory's
  @{thm [source] atomic_divergence_from_guarded} --- the
  verbatim-discharge route, executed on the cyclic branch.\<close>

lemma pre_cycle_guarded_shape:
  assumes "cyclic_class_step (t :: (nat, nat) dwe_state) a t'"
      and "\<not> pre_cycle_absorbed t \<longrightarrow>
             map e_payload (dwe_emitted t) = exec_down_hist (dwe_core t)"
  shows "\<not> pre_cycle_absorbed t' \<longrightarrow>
           map e_payload (dwe_emitted t') = exec_down_hist (dwe_core t')"
  using cyclic_class_step_epoch0_sync[OF assms(1)] assms(2)
  by (simp add: epoch0_inv_iff)

lemma pre_cycle_atomic_divergence:
  assumes "cyclic_class_step (t :: (nat, nat) dwe_state) a t'"
      and "\<not> pre_cycle_absorbed t"
      and "map e_payload (dwe_emitted t) = exec_down_hist (dwe_core t)"
  shows "map e_payload (dwe_emitted t') = exec_down_hist (dwe_core t')
         \<or> pre_cycle_absorbed t'"
  by (rule atomic_divergence_from_guarded[where step = cyclic_class_step
        and absorbed = pre_cycle_absorbed
        and obs = "\<lambda>t. map e_payload (dwe_emitted t)"
        and anchor = exec_down_hist and core = dwe_core,
        OF pre_cycle_guarded_shape assms])

lemma pre_cycle_crashed_not_absorbed:
  assumes "epoch0_crashed (t :: (nat, nat) dwe_state)"
  shows "\<not> pre_cycle_absorbed t"
  using assms by (auto simp: epoch0_crashed_def pre_cycle_absorbed_def)

text \<open>
  The membership certificate.  Everything the class proves --- the
  disjunctive invariant, the anchored-crashed-state equation, and the
  no-pair law --- becomes a theorem of the cyclic machine's
  pre-first-recovery fragment at these parameter readings.  The init
  slot is the PINNED witness init (the landed @{const dwe_reachable}
  is pinned there too), monomorphic at the landed witness machine ---
  deliberately narrower than the terminal sibling's cross-parameter
  family, matching the landed cyclic reachability vocabulary this
  theory ties back to.
\<close>

interpretation pre_cycle:
  absorbing_atomic_recovery cyclic_class_step
    "{dwe_init Map.empty {0, 1} ec2} :: (nat, nat) dwe_state set"
    dwe_core "\<lambda>t. map e_payload (dwe_emitted t)" exec_down_hist
    pre_cycle_absorbed epoch0_crashed
proof (unfold_locales)
  show "\<And>t. t \<in> ({dwe_init Map.empty {0, 1} ec2} :: (nat, nat) dwe_state set)
          \<Longrightarrow> map e_payload (dwe_emitted t) = exec_down_hist (dwe_core t)"
    by (rule pre_cycle_init_sync)
  show "\<And>t a t'. cyclic_class_step (t :: (nat, nat) dwe_state) a t' \<Longrightarrow>
          pre_cycle_absorbed t \<Longrightarrow> pre_cycle_absorbed t'"
    by (rule pre_cycle_absorbed_preserved)
  show "\<And>t a t'. cyclic_class_step (t :: (nat, nat) dwe_state) a t' \<Longrightarrow>
          \<not> pre_cycle_absorbed t \<Longrightarrow>
          map e_payload (dwe_emitted t) = exec_down_hist (dwe_core t) \<Longrightarrow>
          map e_payload (dwe_emitted t') = exec_down_hist (dwe_core t')
          \<or> pre_cycle_absorbed t'"
    by (rule pre_cycle_atomic_divergence)
  show "\<And>t. epoch0_crashed (t :: (nat, nat) dwe_state)
          \<Longrightarrow> \<not> pre_cycle_absorbed t"
    by (rule pre_cycle_crashed_not_absorbed)
qed

section \<open>Reachability glue: landed reachability lands inside class reach\<close>

text \<open>
  As in the terminal sibling, the class's reach closes the unified step
  over the init WITHOUT the temporal trace's wellformedness side
  conditions on label steps.  Dropping side conditions only ENLARGES
  the reachable set, and every class conclusion consumed here is a
  negative over reach, so the conclusions for the landed
  @{const dwe_reachable} states follow a fortiori --- the safe
  direction, said here once and relied on below.  Concrete glue for the
  pinned machine only; no abstract transfer lemma is stated (the shelf
  fence).
\<close>

lemma dwe_temporal_trace_pre_cycle_reach:
  assumes "dwe_temporal_trace t xs t'"
      and "pre_cycle.reach t"
  shows "pre_cycle.reach t'"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  then show ?case .
next
  case (dwe_label_step t a t' as t'')
  have "cyclic_class_step t (DWE_Label a) t'"
    using dwe_label_step.hyps by (simp add: cyclic_class_step_def)
  then have "pre_cycle.reach t'"
    using dwe_label_step.prems by (rule pre_cycle.reach_step[rotated])
  then show ?case by (rule dwe_label_step.IH)
next
  case (dwe_reconcile_step m t f t' as t'')
  have "cyclic_class_step t (DWE_Reconcile m f) t'"
    using dwe_reconcile_step.hyps by (simp add: cyclic_class_step_def)
  then have "pre_cycle.reach t'"
    using dwe_reconcile_step.prems by (rule pre_cycle.reach_step[rotated])
  then show ?case by (rule dwe_reconcile_step.IH)
next
  case (dwe_resume_step t t' as t'')
  have "cyclic_class_step t DWE_Resume t'"
    using dwe_resume_step.hyps by (simp add: cyclic_class_step_def)
  then have "pre_cycle.reach t'"
    using dwe_resume_step.prems by (rule pre_cycle.reach_step[rotated])
  then show ?case by (rule dwe_resume_step.IH)
qed

lemma dwe_reachable_pre_cycle_reach:
  assumes "dwe_reachable t"
  shows "pre_cycle.reach t"
proof -
  obtain xs where tr: "dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2) xs t"
    using assms unfolding dwe_reachable_def by blast
  have i: "pre_cycle.reach (dwe_init Map.empty {0, 1} ec2)"
    by (rule pre_cycle.reach_init) simp
  show ?thesis
    by (rule dwe_temporal_trace_pre_cycle_reach[OF tr i])
qed

section \<open>The sanity tie-back: Part 1 re-derived through the class\<close>

text \<open>
  The Part-1 statement as an interpretation corollary under a new name
  --- the class's second substantive in-vivo membership doing real
  work.  A sanity tie-back, never a replacement: the landed
  @{thm [source] dwe_reachable_epoch0_crashed_sync} stays the bearer of
  record for Part 1, exactly as the landed terminal headline stays the
  theorem of record beside its own interpretation corollary.
\<close>

theorem cyclic_epoch0_no_divergent_crashed_pair_via_class:
  "\<not> (\<exists>t t'. dwe_reachable t \<and> dwe_reachable t'
        \<and> epoch0_crashed t \<and> epoch0_crashed t'
        \<and> dwe_core t = dwe_core t'
        \<and> map e_payload (dwe_emitted t) \<noteq> map e_payload (dwe_emitted t'))"
  using pre_cycle.no_divergent_crashed_pair dwe_reachable_pre_cycle_reach
  by blast


end
