(*  Title:       Dual_Write_Effect_Redrive_Mechanics.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    RESTORE-MECHANICS INVARIANCE of the recovery-information dilemma's
    batch-agreement kernel: the defeat never reads the restored store or
    the stamps.

    Boundary row 4's BULK-RESTORE reading ("the store heals regardless of
    the cursor; the cursor governs only which suffix is FIRED; loss
    charges exactly the fired-side gap") is a disclosed model reading a
    referee can attack as load-bearing: "a faithful restore-from-cursor
    model would make loss a store-tier failure and collapse the two-tier
    separation."  This theory flips that disclosure to a theorem, the
    exact row-1/W2 precedent one row down (there the small-step variant
    made the atomic-reconcile disclosure a robustness theorem,
    ss_batch_agreement_dilemma): on the SAME landed pair, every
    batch-agreeing policy is defeated under EVERY src-preserving
    installer of the post-crash core and EVERY appended emission block
    whose payload projection is the policy's batch --- stamps and epochs
    fully free --- so no restore semantics rescues the defeated classes.
    A ROBUSTNESS FACE of batch_agreement_dilemma, never a new
    impossibility class: the landed kernel remains the visible transfer
    shape, the exists-system polarity is verbatim, and no converse or
    iff is stated anywhere.

    Provenance: discovery-track candidate A2 (the binding spec is
    paper/dual_write/theory_review/discovery/LENS_A_REFEREE.md, CANDIDATE
    A2, banked at commit 477922c), ported against the landed definitions
    from the probe-proved artifact paper/dual_write/theory_review/
    discovery/probes/LensA_Probe.thy (md5 f7f21f879b40c00bfa3d9e82289ce614,
    probe GREEN against the landed stack at 928e793, qd=false, isolated
    USER_HOME) --- the pinned statements land verbatim; the landing plan's
    two measurability faces (the landed quantifier plumbing) and the
    epoch-continuity fact are added per the spec.
*)

theory Dual_Write_Effect_Redrive_Mechanics
  imports Dual_Write_Effect_Dilemma
begin

section \<open>The abstract restore mechanics: what the defeat actually reads\<close>

text \<open>
  The landed kernel's redrives are @{const policy_redrive} transitions:
  the installer is the bulk restore (install the scoped, frontier-bounded
  replay as the new durable downstream history), and the appended block
  is stamped @{term "(length (exec_src_hist (dwe_core t)), dwe_epoch t)"}
  at fire time.  Here BOTH mechanics are made abstract: an arbitrary
  installer \<open>\<rho>\<close> rewrites the crashed core, and an arbitrary emission
  block \<open>E\<close> is appended to the ledger.  The defeat survives because its
  three-case horn analysis is a payload-level fact about the ledger, the
  committed source, and the contract scope of the post-states:

  \<^item> the LOSS horn reads the post-state's committed source and scope
    (through the replay) and the post-state's ledger payloads --- so the
    loss side needs \<open>\<rho>\<close> to preserve src and scope, nothing else;

  \<^item> the DUPLICATE horn is payload-level distinctness of the post-state
    ledger --- it reads no core field and no stamp at all;

  \<^item> the PREMATURE horn evaluates @{const justified_at} against the
    post-state's committed source: an alien payload is unjustified at
    EVERY stamp value, because the take-prefix of the committed source
    never contains it (@{thm [source] set_take_subset}, instantiated
    explicitly) --- so the safe side needs \<open>\<rho>\<close> to preserve src only.

  STAMPS FULLY FREE means exactly this: the defeat never reads the
  stamps.  The blocks \<open>E1\<close>, \<open>E2\<close> carry arbitrary stamp and epoch
  components --- only their payload projections are constrained (to be
  the policy's batch, which is what "the policy fired its batch" means).

  The minimal premise set is deliberately asymmetric --- SRC-PRESERVATION
  ON BOTH SIDES, SCOPE-PRESERVATION ON THE LOSS SIDE ONLY (the probe's
  finding) --- and the scope-clearing control below shows why the one
  scope premise cannot be dropped: a "recovery" that abandons the
  contract scope dodges loss by redefinition.  The premise class
  (recovery rewrites the DOWNSTREAM state, never the committed log or
  the contract scope) is exactly the architecture's own reading of what
  a restore is allowed to touch.

  Two honesty notes, disclosed up front.  First, an arbitrary installer
  need not heal: the invariant statement carries NO heal conjunct ---
  healing is the landed rule's separately-proved bonus
  (@{thm [source] policy_redrive_heals}), recovered for the landed
  mechanics through the instance bridge at the end of this theory.
  Second, the post-states of an arbitrary installer are record-level
  constructions, not claimed machine-reachable; the hazard and loss
  predicates are state functions, so the defeat is a statement about
  every restore RESULT of the designed pair --- the landed rule's
  results are one machine-realized instance (the bridge), and any
  restore-from-cursor machine variant's recovery results are another,
  which is why such a variant is subsumed without building it.

  Scope fences, binding: this face quantifies over restore MECHANICS at
  the landed pair; it never generalizes the pair parametrically (the
  dropped item-H ambition stays dropped --- exists-system claims need
  the concrete designed pair), and no membership-style converse is
  stated (the class-study fence: membership failure does not imply pair
  reachability).
\<close>

section \<open>THE ROBUSTNESS FACE: the kernel under abstract restore mechanics\<close>

text \<open>
  The landed batch-agreement argument re-run with \<open>\<rho>\<close> and \<open>E\<close> abstract,
  on the SAME designed pair @{const d1_w}, @{const d2_w} --- presented as
  a robustness face OF @{thm [source] batch_agreement_dilemma}, never a
  new impossibility class.  Case (i): the shared batch is empty and the
  loss side's replay payload @{term "(ec2, e2)"} is not in its post-state
  ledger.  Case (ii): some batch payload re-fires an already-delivered
  payload --- payload-level duplicate.  Case (iii): a non-empty alien
  batch is unjustified at any stamp --- premature.  Loss stays a HORN,
  not a premise: refusing to emit lands in case (i).
\<close>

theorem batch_agreement_dilemma_mechanics_invariant:
  "\<exists>t1 t2.
     dwe_reachable t1 \<and> dwe_reachable t2
   \<and> dwe_core t1 = dwe_core t2
   \<and> dwe_epoch t1 = dwe_epoch t2
   \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
   \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
   \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
   \<and> (\<forall>P \<rho>1 \<rho>2 E1 E2.
        P t1 = P t2
      \<longrightarrow> exec_src_hist (\<rho>1 (dwe_core t1)) = exec_src_hist (dwe_core t1)
      \<longrightarrow> exec_src_hist (\<rho>2 (dwe_core t2)) = exec_src_hist (dwe_core t2)
      \<longrightarrow> exec_scope (\<rho>2 (dwe_core t2)) = exec_scope (dwe_core t2)
      \<longrightarrow> map e_payload E1 = P t1
      \<longrightarrow> map e_payload E2 = P t2
      \<longrightarrow> (effect_unsafe (t1\<lparr>dwe_core := \<rho>1 (dwe_core t1),
                              dwe_emitted := dwe_emitted t1 @ E1\<rparr>)
         \<or> lost_effect ec2 (t2\<lparr>dwe_core := \<rho>2 (dwe_core t2),
                                dwe_emitted := dwe_emitted t2 @ E2\<rparr>)))"
proof -
  have inner: "\<forall>P \<rho>1 \<rho>2 E1 E2.
        P d1_w = P d2_w
      \<longrightarrow> exec_src_hist (\<rho>1 (dwe_core d1_w)) = exec_src_hist (dwe_core d1_w)
      \<longrightarrow> exec_src_hist (\<rho>2 (dwe_core d2_w)) = exec_src_hist (dwe_core d2_w)
      \<longrightarrow> exec_scope (\<rho>2 (dwe_core d2_w)) = exec_scope (dwe_core d2_w)
      \<longrightarrow> map e_payload E1 = P d1_w
      \<longrightarrow> map e_payload E2 = P d2_w
      \<longrightarrow> (effect_unsafe (d1_w\<lparr>dwe_core := \<rho>1 (dwe_core d1_w),
                               dwe_emitted := dwe_emitted d1_w @ E1\<rparr>)
         \<or> lost_effect ec2 (d2_w\<lparr>dwe_core := \<rho>2 (dwe_core d2_w),
                                  dwe_emitted := dwe_emitted d2_w @ E2\<rparr>))"
  proof (intro allI impI)
    fix P :: redrive_policy
    fix \<rho>1 \<rho>2 :: "(nat, nat) dw_exec_state \<Rightarrow> (nat, nat) dw_exec_state"
    fix E1 E2 :: "(nat, nat) emission list"
    assume PB: "P d1_w = P d2_w"
       and s1: "exec_src_hist (\<rho>1 (dwe_core d1_w))
                = exec_src_hist (dwe_core d1_w)"
       and s2: "exec_src_hist (\<rho>2 (dwe_core d2_w))
                = exec_src_hist (dwe_core d2_w)"
       and sc2: "exec_scope (\<rho>2 (dwe_core d2_w)) = exec_scope (dwe_core d2_w)"
       and pe1: "map e_payload E1 = P d1_w"
       and pe2: "map e_payload E2 = P d2_w"
    define B where "B = P d1_w"
    define t1' where
      "t1' = d1_w\<lparr>dwe_core := \<rho>1 (dwe_core d1_w),
                  dwe_emitted := dwe_emitted d1_w @ E1\<rparr>"
    define t2' where
      "t2' = d2_w\<lparr>dwe_core := \<rho>2 (dwe_core d2_w),
                  dwe_emitted := dwe_emitted d2_w @ E2\<rparr>"
    have src1: "exec_src_hist (dwe_core t1') = [(ec1, e1), (ec2, e2)]"
      unfolding t1'_def using s1 by (simp add: d1_fields)
    have src2: "exec_src_hist (dwe_core t2') = [(ec1, e1), (ec2, e2)]"
      unfolding t2'_def using s2 by (simp add: d2_fields)
    have scope2: "exec_scope (dwe_core t2') = {0, 1}"
      unfolding t2'_def using sc2 by (simp add: d2_fields)
    have em1: "dwe_emitted t1' = [(1, 0, ec1, e1), (2, 0, ec2, e2)] @ E1"
      unfolding t1'_def by (simp add: d1_fields)
    have em2: "dwe_emitted t2' = [(1, 0, ec1, e1)] @ E2"
      unfolding t2'_def by (simp add: d2_fields)
    have pay1: "map e_payload (dwe_emitted t1') = [(ec1, e1), (ec2, e2)] @ B"
      by (simp add: em1 pe1 B_def)
    show "effect_unsafe (d1_w\<lparr>dwe_core := \<rho>1 (dwe_core d1_w),
                              dwe_emitted := dwe_emitted d1_w @ E1\<rparr>)
        \<or> lost_effect ec2 (d2_w\<lparr>dwe_core := \<rho>2 (dwe_core d2_w),
                                 dwe_emitted := dwe_emitted d2_w @ E2\<rparr>)"
    proof (cases "B = []")
      case True
      \<comment> \<open>(i) the policy refuses to emit: the loss side LOSES effect 2
          under ANY src/scope-preserving installer\<close>
      have E2nil: "E2 = []"
        using pe2 PB True unfolding B_def by simp
      have em2': "dwe_emitted t2' = [(1, 0, ec1, e1)]"
        using em2 by (simp add: E2nil)
      have inrep: "(ec2, e2) \<in> set (replay_down_hist
                      (exec_src_hist (dwe_core t2'))
                      (exec_scope (dwe_core t2')) ec2)"
        by (simp add: src2 scope2 replay_down_hist_def e1_def e2_def ec_defs
                      eval_nat_numeral)
      have notin: "(ec2, e2) \<notin> e_payload ` set (dwe_emitted t2')"
        by (simp add: em2' e1_def e2_def ec_defs)
      have "lost_effect ec2 t2'"
        unfolding lost_effect_def using inrep notin by blast
      then show ?thesis unfolding t2'_def by blast
    next
      case False
      then obtain p0 where p0: "p0 \<in> set B"
        by (cases B) auto
      show ?thesis
      proof (cases "\<exists>p \<in> set B. p \<in> {(ec1, e1), (ec2, e2)}")
        case True
        \<comment> \<open>(ii) the batch re-fires an already-delivered payload:
            DUPLICATE, read off the payload projection alone --- no core
            field, no stamp\<close>
        have "\<not> distinct (map e_payload (dwe_emitted t1'))"
          unfolding pay1 using True by auto
        then have "effect_unsafe t1'"
          by (simp add: effect_unsafe_def duplicate_def)
        then show ?thesis unfolding t1'_def by blast
      next
        case False
        \<comment> \<open>(iii) a non-empty alien batch: unjustified at ANY stamp ---
            the take-prefix of the committed source never contains an
            alien payload (@{thm [source] set_take_subset}, explicit
            rule composition)\<close>
        have p0_out: "p0 \<notin> {(ec1, e1), (ec2, e2)}"
          using False p0 by blast
        have "p0 \<in> set (map e_payload E1)"
          using p0 pe1 B_def by simp
        then obtain x where x_in1: "x \<in> set E1" and x_pay: "e_payload x = p0"
          by auto
        have x_in: "x \<in> set (dwe_emitted t1')"
          using x_in1 by (simp add: em1)
        have take_sub: "set (take (e_stamp x) [(ec1, e1), (ec2, e2)])
                          \<subseteq> {(ec1, e1), (ec2, e2)}"
          using set_take_subset[of "e_stamp x" "[(ec1, e1), (ec2, e2)]"]
          by simp
        have "\<not> justified_at (exec_src_hist (dwe_core t1')) x"
          unfolding justified_at_def src1 x_pay
          using p0_out take_sub by blast
        then have "premature t1'"
          unfolding premature_def using x_in by blast
        then have "effect_unsafe t1'"
          by (simp add: effect_unsafe_def)
        then show ?thesis unfolding t1'_def by blast
      qed
    qed
  qed
  have epochs: "dwe_epoch d1_w = dwe_epoch d2_w"
    by (simp add: d1_fields d2_fields)
  show ?thesis
    by (intro exI[of _ d1_w] exI[of _ d2_w])
       (use reach_d1 reach_d2 d_cores_eq epochs d_emitted_neq d1_not_unsafe
            d2_not_unsafe d1_emitting d2_emitting inner in blast)
qed

section \<open>The measurability faces: the landed quantifier plumbing\<close>

text \<open>
  The classes enter exactly as they enter the landed dilemma --- through
  one fact: their policies cannot distinguish the pair.  Store-measured
  policies agree because the cores are literally equal;
  (core, epoch)-measured policies agree because the epochs are equal too.
  The plumbing is the landed
  @{thm [source] recovery_information_dilemma} /
  @{thm [source] epoch_measured_dilemma} derivation, unchanged, with the
  abstract-mechanics defeat in place of the landed redrive conclusion.
\<close>

corollary mechanics_invariant_recovery_dilemma:
  "\<forall>P. store_measured P \<longrightarrow>
     (\<exists>t1 t2.
        dwe_reachable t1 \<and> dwe_reachable t2
      \<and> dwe_core t1 = dwe_core t2
      \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
      \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
      \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
      \<and> (\<forall>\<rho>1 \<rho>2 E1 E2.
           exec_src_hist (\<rho>1 (dwe_core t1)) = exec_src_hist (dwe_core t1)
         \<longrightarrow> exec_src_hist (\<rho>2 (dwe_core t2)) = exec_src_hist (dwe_core t2)
         \<longrightarrow> exec_scope (\<rho>2 (dwe_core t2)) = exec_scope (dwe_core t2)
         \<longrightarrow> map e_payload E1 = P t1
         \<longrightarrow> map e_payload E2 = P t2
         \<longrightarrow> (effect_unsafe (t1\<lparr>dwe_core := \<rho>1 (dwe_core t1),
                                 dwe_emitted := dwe_emitted t1 @ E1\<rparr>)
            \<or> lost_effect ec2 (t2\<lparr>dwe_core := \<rho>2 (dwe_core t2),
                                   dwe_emitted := dwe_emitted t2 @ E2\<rparr>))))"
proof (intro allI impI)
  fix P :: redrive_policy
  assume sm: "store_measured P"
  obtain t1 t2 where
    base: "dwe_reachable t1" "dwe_reachable t2"
          "dwe_core t1 = dwe_core t2" "dwe_epoch t1 = dwe_epoch t2"
          "dwe_emitted t1 \<noteq> dwe_emitted t2"
          "\<not> effect_unsafe t1" "\<not> effect_unsafe t2"
          "genuinely_emitting t1" "genuinely_emitting t2"
    and agree: "\<forall>P \<rho>1 \<rho>2 E1 E2.
        P t1 = P t2
      \<longrightarrow> exec_src_hist (\<rho>1 (dwe_core t1)) = exec_src_hist (dwe_core t1)
      \<longrightarrow> exec_src_hist (\<rho>2 (dwe_core t2)) = exec_src_hist (dwe_core t2)
      \<longrightarrow> exec_scope (\<rho>2 (dwe_core t2)) = exec_scope (dwe_core t2)
      \<longrightarrow> map e_payload E1 = P t1
      \<longrightarrow> map e_payload E2 = P t2
      \<longrightarrow> (effect_unsafe (t1\<lparr>dwe_core := \<rho>1 (dwe_core t1),
                              dwe_emitted := dwe_emitted t1 @ E1\<rparr>)
         \<or> lost_effect ec2 (t2\<lparr>dwe_core := \<rho>2 (dwe_core t2),
                                dwe_emitted := dwe_emitted t2 @ E2\<rparr>))"
    using batch_agreement_dilemma_mechanics_invariant by blast
  from sm obtain g where g: "\<forall>t. P t = g (dwe_core t)"
    unfolding store_measured_def by blast
  have PB: "P t1 = P t2"
    using g base(3) by metis
  have inner: "\<forall>\<rho>1 \<rho>2 E1 E2.
        exec_src_hist (\<rho>1 (dwe_core t1)) = exec_src_hist (dwe_core t1)
      \<longrightarrow> exec_src_hist (\<rho>2 (dwe_core t2)) = exec_src_hist (dwe_core t2)
      \<longrightarrow> exec_scope (\<rho>2 (dwe_core t2)) = exec_scope (dwe_core t2)
      \<longrightarrow> map e_payload E1 = P t1
      \<longrightarrow> map e_payload E2 = P t2
      \<longrightarrow> (effect_unsafe (t1\<lparr>dwe_core := \<rho>1 (dwe_core t1),
                              dwe_emitted := dwe_emitted t1 @ E1\<rparr>)
         \<or> lost_effect ec2 (t2\<lparr>dwe_core := \<rho>2 (dwe_core t2),
                                dwe_emitted := dwe_emitted t2 @ E2\<rparr>))"
    using agree PB by blast
  show "\<exists>t1 t2.
        dwe_reachable t1 \<and> dwe_reachable t2
      \<and> dwe_core t1 = dwe_core t2
      \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
      \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
      \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
      \<and> (\<forall>\<rho>1 \<rho>2 E1 E2.
           exec_src_hist (\<rho>1 (dwe_core t1)) = exec_src_hist (dwe_core t1)
         \<longrightarrow> exec_src_hist (\<rho>2 (dwe_core t2)) = exec_src_hist (dwe_core t2)
         \<longrightarrow> exec_scope (\<rho>2 (dwe_core t2)) = exec_scope (dwe_core t2)
         \<longrightarrow> map e_payload E1 = P t1
         \<longrightarrow> map e_payload E2 = P t2
         \<longrightarrow> (effect_unsafe (t1\<lparr>dwe_core := \<rho>1 (dwe_core t1),
                                 dwe_emitted := dwe_emitted t1 @ E1\<rparr>)
            \<or> lost_effect ec2 (t2\<lparr>dwe_core := \<rho>2 (dwe_core t2),
                                   dwe_emitted := dwe_emitted t2 @ E2\<rparr>)))"
    using base(1,2,3,5,6,7,8,9) inner by blast
qed

text \<open>
  GAP-2 CONTINUITY, by construction: the abstract mechanics shape touches
  only @{const dwe_core} and @{const dwe_emitted} --- the wrapper's
  recovery-generation counter @{const dwe_epoch} is untouched for EVERY
  installer and every block.  So the defeat's post-states sit in the same
  recovery generation as the crashed pre-states (no abstract restore can
  smuggle in an epoch bump), and the landed rule's own epoch preservation
  is the special case at the instance bridge below
  (@{text landed_redrive_is_instance}).  Stated at the pinned type of the
  kernel's quantifiers.
\<close>

lemma mechanics_update_epoch_continuity:
  fixes t :: "(nat, nat) dwe_state"
    and \<rho> :: "(nat, nat) dw_exec_state \<Rightarrow> (nat, nat) dw_exec_state"
    and E :: "(nat, nat) emission list"
  shows "dwe_epoch (t\<lparr>dwe_core := \<rho> (dwe_core t),
                      dwe_emitted := dwe_emitted t @ E\<rparr>) = dwe_epoch t"
  by simp

text \<open>
  GAP-2, the class face: a real recovery routine may read a persisted
  recovery-generation counter in addition to the store.  The pair has
  equal epochs, so (core, epoch)-measured policies cannot distinguish it
  either --- the same defeat, under every restore mechanics.
\<close>

corollary mechanics_invariant_epoch_measured_dilemma:
  "\<forall>P. store_epoch_measured P \<longrightarrow>
     (\<exists>t1 t2.
        dwe_reachable t1 \<and> dwe_reachable t2
      \<and> dwe_core t1 = dwe_core t2
      \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
      \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
      \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
      \<and> (\<forall>\<rho>1 \<rho>2 E1 E2.
           exec_src_hist (\<rho>1 (dwe_core t1)) = exec_src_hist (dwe_core t1)
         \<longrightarrow> exec_src_hist (\<rho>2 (dwe_core t2)) = exec_src_hist (dwe_core t2)
         \<longrightarrow> exec_scope (\<rho>2 (dwe_core t2)) = exec_scope (dwe_core t2)
         \<longrightarrow> map e_payload E1 = P t1
         \<longrightarrow> map e_payload E2 = P t2
         \<longrightarrow> (effect_unsafe (t1\<lparr>dwe_core := \<rho>1 (dwe_core t1),
                                 dwe_emitted := dwe_emitted t1 @ E1\<rparr>)
            \<or> lost_effect ec2 (t2\<lparr>dwe_core := \<rho>2 (dwe_core t2),
                                   dwe_emitted := dwe_emitted t2 @ E2\<rparr>))))"
proof (intro allI impI)
  fix P :: redrive_policy
  assume sem: "store_epoch_measured P"
  obtain t1 t2 where
    base: "dwe_reachable t1" "dwe_reachable t2"
          "dwe_core t1 = dwe_core t2" "dwe_epoch t1 = dwe_epoch t2"
          "dwe_emitted t1 \<noteq> dwe_emitted t2"
          "\<not> effect_unsafe t1" "\<not> effect_unsafe t2"
          "genuinely_emitting t1" "genuinely_emitting t2"
    and agree: "\<forall>P \<rho>1 \<rho>2 E1 E2.
        P t1 = P t2
      \<longrightarrow> exec_src_hist (\<rho>1 (dwe_core t1)) = exec_src_hist (dwe_core t1)
      \<longrightarrow> exec_src_hist (\<rho>2 (dwe_core t2)) = exec_src_hist (dwe_core t2)
      \<longrightarrow> exec_scope (\<rho>2 (dwe_core t2)) = exec_scope (dwe_core t2)
      \<longrightarrow> map e_payload E1 = P t1
      \<longrightarrow> map e_payload E2 = P t2
      \<longrightarrow> (effect_unsafe (t1\<lparr>dwe_core := \<rho>1 (dwe_core t1),
                              dwe_emitted := dwe_emitted t1 @ E1\<rparr>)
         \<or> lost_effect ec2 (t2\<lparr>dwe_core := \<rho>2 (dwe_core t2),
                                dwe_emitted := dwe_emitted t2 @ E2\<rparr>))"
    using batch_agreement_dilemma_mechanics_invariant by blast
  from sem obtain g where g: "\<forall>t. P t = g (dwe_core t) (dwe_epoch t)"
    unfolding store_epoch_measured_def by blast
  have PB: "P t1 = P t2"
    using g base(3) base(4) by metis
  have inner: "\<forall>\<rho>1 \<rho>2 E1 E2.
        exec_src_hist (\<rho>1 (dwe_core t1)) = exec_src_hist (dwe_core t1)
      \<longrightarrow> exec_src_hist (\<rho>2 (dwe_core t2)) = exec_src_hist (dwe_core t2)
      \<longrightarrow> exec_scope (\<rho>2 (dwe_core t2)) = exec_scope (dwe_core t2)
      \<longrightarrow> map e_payload E1 = P t1
      \<longrightarrow> map e_payload E2 = P t2
      \<longrightarrow> (effect_unsafe (t1\<lparr>dwe_core := \<rho>1 (dwe_core t1),
                              dwe_emitted := dwe_emitted t1 @ E1\<rparr>)
         \<or> lost_effect ec2 (t2\<lparr>dwe_core := \<rho>2 (dwe_core t2),
                                dwe_emitted := dwe_emitted t2 @ E2\<rparr>))"
    using agree PB by blast
  show "\<exists>t1 t2.
        dwe_reachable t1 \<and> dwe_reachable t2
      \<and> dwe_core t1 = dwe_core t2
      \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
      \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
      \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
      \<and> (\<forall>\<rho>1 \<rho>2 E1 E2.
           exec_src_hist (\<rho>1 (dwe_core t1)) = exec_src_hist (dwe_core t1)
         \<longrightarrow> exec_src_hist (\<rho>2 (dwe_core t2)) = exec_src_hist (dwe_core t2)
         \<longrightarrow> exec_scope (\<rho>2 (dwe_core t2)) = exec_scope (dwe_core t2)
         \<longrightarrow> map e_payload E1 = P t1
         \<longrightarrow> map e_payload E2 = P t2
         \<longrightarrow> (effect_unsafe (t1\<lparr>dwe_core := \<rho>1 (dwe_core t1),
                                 dwe_emitted := dwe_emitted t1 @ E1\<rparr>)
            \<or> lost_effect ec2 (t2\<lparr>dwe_core := \<rho>2 (dwe_core t2),
                                   dwe_emitted := dwe_emitted t2 @ E2\<rparr>)))"
    using base(1,2,3,5,6,7,8,9) inner by blast
qed

section \<open>The minimal premise set, witnessed: the scope-clearing control\<close>

text \<open>
  LOAD-BEARING CONTROL for the loss side's scope preservation: a
  scope-clearing installer with the empty batch dodges BOTH horns ---
  "recovery" that abandons the contract scope trivially loses nothing
  by redefinition (the scoped replay of an empty scope is empty), and
  the empty batch alone never fires the unsafe horn (the safe member's
  post-state is the safe member itself).  So the one scope premise
  cannot be dropped, and the premise class (recovery rewrites the
  DOWNSTREAM state, never the committed log or the contract scope) is
  exactly the architecture's own reading.  Note the clearing installer
  PRESERVES src --- src-preservation alone is provably not enough on the
  loss side.
\<close>

lemma scope_preservation_load_bearing:
  "\<not> lost_effect ec2
       (d2_w\<lparr>dwe_core := (dwe_core d2_w)\<lparr>exec_scope := {}\<rparr>,
             dwe_emitted := dwe_emitted d2_w @ []\<rparr>)
 \<and> \<not> effect_unsafe
       (d1_w\<lparr>dwe_core := dwe_core d1_w,
             dwe_emitted := dwe_emitted d1_w @ []\<rparr>)"
proof (rule conjI)
  show "\<not> lost_effect ec2
          (d2_w\<lparr>dwe_core := (dwe_core d2_w)\<lparr>exec_scope := {}\<rparr>,
                dwe_emitted := dwe_emitted d2_w @ []\<rparr>)"
    by (simp add: lost_effect_def replay_down_hist_def d2_w_def mkT_def
                  mkC_def)
next
  have "(d1_w\<lparr>dwe_core := dwe_core d1_w,
              dwe_emitted := dwe_emitted d1_w @ []\<rparr>) = d1_w"
    by simp
  then show "\<not> effect_unsafe
               (d1_w\<lparr>dwe_core := dwe_core d1_w,
                     dwe_emitted := dwe_emitted d1_w @ []\<rparr>)"
    using d1_not_unsafe by simp
qed

section \<open>The landed rule as one instance: the heal clause, honestly placed\<close>

text \<open>
  SANITY BRIDGE: the landed @{const policy_redrive} IS an instance of the
  invariant shape --- its installer (the bulk restore) preserves src and
  scope, and its block's payload projection is the policy batch.  This is
  where the heal clause honestly lives: the invariant quantifies over
  installers that need not heal, and the landed rule's healing is its
  separately-proved bonus (@{thm [source] policy_redrive_heals}) --- the
  defeat above never consumed it.  Consequently boundary row 4's
  bulk-restore reading carries no load in the impossibility half: the
  landed kernel's defeat is the \<open>\<rho> =\<close> bulk-restore, \<open>E =\<close> fire-time-
  stamped instance of a theorem that holds for every restore semantics.
\<close>

lemma landed_redrive_is_instance:
  assumes pr: "policy_redrive P t f t'"
  shows "\<exists>\<rho> E. t' = t\<lparr>dwe_core := \<rho> (dwe_core t),
                      dwe_emitted := dwe_emitted t @ E\<rparr>
             \<and> exec_src_hist (\<rho> (dwe_core t)) = exec_src_hist (dwe_core t)
             \<and> exec_scope (\<rho> (dwe_core t)) = exec_scope (dwe_core t)
             \<and> map e_payload E = P t"
proof -
  let ?\<rho> = "\<lambda>c. c\<lparr>exec_down_hist :=
                    replay_down_hist (exec_src_hist (dwe_core t))
                      (exec_scope (dwe_core t)) f,
                  exec_pending := {},
                  exec_status := Recovered\<rparr>"
  let ?E = "map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                           dwe_epoch t, c, e)) (P t)"
  have "t' = t\<lparr>dwe_core := ?\<rho> (dwe_core t),
               dwe_emitted := dwe_emitted t @ ?E\<rparr>"
    using pr by (simp add: policy_redrive_def)
  moreover have "exec_src_hist (?\<rho> (dwe_core t)) = exec_src_hist (dwe_core t)"
    by simp
  moreover have "exec_scope (?\<rho> (dwe_core t)) = exec_scope (dwe_core t)"
    by simp
  moreover have "map e_payload ?E = P t"
    by simp
  ultimately show ?thesis
    by (intro exI[of _ ?\<rho>] exI[of _ ?E]) blast
qed


end
