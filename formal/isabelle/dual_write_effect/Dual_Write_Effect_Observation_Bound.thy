(*  Title:       Dual_Write_Effect_Observation_Bound.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE PAIR-AGREEMENT LOWER BOUND (external-review Edit C) --- an
    additive post-freeze slice under the freeze's own protocol: no landed
    statement, proof, definition, name, import, or session-DAG change to
    the frozen corpus.

    The landed Presence_Bound theory pins the sink-reading escape's
    information requirement from ABOVE (the escape needs no more than the
    recovery window's delivered-payload presence).  This theory is its
    LOWER-BOUND TWIN on the impossibility side: it pins, from BELOW, what
    a recovery-metadata channel must be able to SEE to survive the
    headline dilemma at all.  The landed kernel
    (batch_agreement_dilemma) quantifies over policies that emit the same
    batch on the designed equal-core, equal-epoch, divergent-ledger pair;
    its inner batch-agreement derivation is PROOF-LOCAL there (a
    "have inner:" inside the kernel's proof).  Here that derivation is
    replayed verbatim as an exported theorem with the policy fixed
    (pair_batch_agreement_defeated), then lifted to ANY observation
    channel: if a policy factors through an observation --- an external
    cursor, a generation counter, a dedup digest, ANY recovery metadata
    of ANY type --- and that observation fails to distinguish the two
    members of the designed pair, the policy is defeated wholesale: its
    own redrive heals every scoped store mismatch on both members, yet
    duplicates or goes premature on one member or loses a committed
    effect on the other (pair_agreeing_observation_defeated), packaged in
    the landed exists-pair family shape (observation_measured_dilemma).

    The HONEST BOUNDARY is carried in-theory, both directions.  An
    ACCURATE delivery-count cursor persisted outside the store DOES
    distinguish the pair --- the ledgers have lengths 2 and 1
    (ledger_length_separates_pair) --- so it fails the agreement premise
    of every theorem above and lies outside every class this theory
    defeats; and any POLICY whose batch separates the pair --- as such a
    cursor enables --- is not ledger-blind, i.e. sits on the sink-reading
    side of the landed dichotomy (pair_separating_not_ledger_blind, a
    statement about the policy's batch, not about the observation
    channel itself).  Whether such a cursor also
    EARNS the escape's guarantees (heals, stays effect-safe, loses
    nothing) is Theorem-B territory, proved for the landed sink_delta
    policy alone; nothing new is claimed here about the escape side.
    Conversely, defeat is about PAIR-AGREEMENT, not ledger-blindness: a
    ledger-READING observation (ledger emptiness) that happens to agree
    on the pair is exhibited defeated
    (ledger_reading_observation_still_defeated).  Membership of the
    ledger-blind class is not what the defeat theorems test; no landed
    lemma certifies a strict extension of that class (the exhibited
    family also contains ledger-blind members, e.g. constant g).

    Exists-system polarity preserved throughout (boundary row 5): every
    statement lives at the designed pair of the pinned witness machine
    --- "there is a dual-write system on which ..." --- never a
    for-every-system claim, and the landed defeat theorems keep their
    exact landed shape (this theory only re-exports and lifts the
    kernel's own derivation; no new impossibility class, no iff, no
    minimality claim).

    In-source ML oracle gates are STRIPPED at landing: oracle-freedom is
    certified by scratch-side per-slice gate sessions with
    confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Observation_Bound
  imports Dual_Write_Effect_Dichotomy
begin

section \<open>Scope: the lower side of the recovery-information requirement\<close>

text \<open>
  The landed kernel @{thm [source] batch_agreement_dilemma} banks the
  batch-agreement defeat as an exists-pair theorem whose inner
  derivation --- every policy emitting the same batch on both members of
  the designed pair @{const d1_w} / @{const d2_w} is defeated --- is
  proof-local.  This theory exports that derivation at the pair
  (statement level: the policy fixed, the agreement premise explicit)
  and lifts it one abstraction rung: from batch agreement to agreement
  of ANY observation the policy factors through.  The upper-bound twin
  (@{text Dual_Write_Effect_Presence_Bound}, not in this import cone)
  bounds what the landed escape needs to read; this theory bounds what
  every surviving recovery-metadata channel must be able to
  distinguish.  Both statements live at the designed pair of the pinned
  witness machine --- exists-system polarity, boundary row 5.
\<close>

section \<open>The exported kernel derivation: batch agreement defeats\<close>

text \<open>
  The replay is verbatim from the landed kernel's proof: the three
  total cases on the shared batch (empty --- the skip side loses the
  committed second effect; a payload already delivered --- the safe side
  duplicates; a non-empty alien batch --- the safe side is premature),
  with both redrives healing every scoped store mismatch at the
  frontier.  It consumes only exported field facts
  (@{thm [source] d1_fields}, @{thm [source] d2_fields}) and the landed
  redrive plumbing --- which is exactly why it can be exported here
  without touching the frozen kernel.
\<close>

theorem pair_batch_agreement_defeated:
  fixes P :: redrive_policy
  assumes PB: "P d1_w = P d2_w"
  shows "\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')"
proof -
  define B where "B = P d1_w"

  \<comment> \<open>the two policy redrives at the frontier ec2\<close>
  have grd1: "\<exists>c. exec_status (dwe_core d1_w) = Crashed c"
    by (simp add: d1_fields)
  have grd2: "\<exists>c. exec_status (dwe_core d2_w) = Crashed c"
    by (simp add: d2_fields)
  have fin1: "ec2 \<le> exec_finish (dwe_core d1_w)"
    by (simp add: d1_fields)
  have fin2: "ec2 \<le> exec_finish (dwe_core d2_w)"
    by (simp add: d2_fields)
  define t1' where "t1' = redrive_result P d1_w ec2"
  define t2' where "t2' = redrive_result P d2_w ec2"
  have pr1: "policy_redrive P d1_w ec2 t1'"
    unfolding t1'_def by (rule policy_redriveI[OF grd1 fin1])
  have pr2: "policy_redrive P d2_w ec2 t2'"
    unfolding t2'_def by (rule policy_redriveI[OF grd2 fin2])

  \<comment> \<open>concrete ledgers and cores of the post-states\<close>
  have em1: "dwe_emitted t1'
      = [(1, 0, ec1, e1), (2, 0, ec2, e2)] @ map (\<lambda>(c, e). (2, 1, c, e)) B"
    unfolding t1'_def B_def redrive_result_def
    by (simp add: d1_w_def mkT_def mkC_def eval_nat_numeral)
  have em2: "dwe_emitted t2'
      = [(1, 0, ec1, e1)] @ map (\<lambda>(c, e). (2, 1, c, e)) (P d2_w)"
    unfolding t2'_def redrive_result_def
    by (simp add: d2_w_def mkT_def mkC_def eval_nat_numeral)
  have src1: "exec_src_hist (dwe_core t1') = [(ec1, e1), (ec2, e2)]"
    unfolding t1'_def redrive_result_def
    by (simp add: d1_w_def mkT_def mkC_def)
  have src2: "exec_src_hist (dwe_core t2') = [(ec1, e1), (ec2, e2)]"
    unfolding t2'_def redrive_result_def
    by (simp add: d2_w_def mkT_def mkC_def)
  have scope2: "exec_scope (dwe_core t2') = {0, 1}"
    unfolding t2'_def redrive_result_def
    by (simp add: d2_w_def mkT_def mkC_def)

  \<comment> \<open>payload list of the safe-side post-state\<close>
  have pay1: "map e_payload (dwe_emitted t1') = [(ec1, e1), (ec2, e2)] @ B"
    by (simp add: em1)

  \<comment> \<open>THE THREE TOTAL CASES on the shared batch B (loss is a horn, not a
      premise: refusing to emit lands in case (i))\<close>
  have horn: "effect_unsafe t1' \<or> lost_effect ec2 t2'"
  proof (cases "B = []")
    case True
    \<comment> \<open>(i) the policy refuses to emit: the skip side LOSES effect 2\<close>
    have P2: "P d2_w = []"
      using PB True unfolding B_def by simp
    have em2': "dwe_emitted t2' = [(1, 0, ec1, e1)]"
      using em2 by (simp add: P2)
    have inrep: "(ec2, e2) \<in> set (replay_down_hist
                    (exec_src_hist (dwe_core t2'))
                    (exec_scope (dwe_core t2')) ec2)"
      by (simp add: src2 scope2 replay_down_hist_def e1_def e2_def ec_defs
                    eval_nat_numeral)
    have notin: "(ec2, e2) \<notin> e_payload ` set (dwe_emitted t2')"
      by (simp add: em2' e1_def e2_def ec_defs)
    have "lost_effect ec2 t2'"
      unfolding lost_effect_def using inrep notin by blast
    then show ?thesis ..
  next
    case False
    then obtain p0 where p0: "p0 \<in> set B"
      by (cases B) auto
    show ?thesis
    proof (cases "\<exists>p \<in> set B. p \<in> {(ec1, e1), (ec2, e2)}")
      case True
      \<comment> \<open>(ii) the batch re-fires an already-delivered payload: DUPLICATE\<close>
      have "\<not> distinct (map e_payload (dwe_emitted t1'))"
        unfolding pay1 using True by auto
      then have "effect_unsafe t1'"
        by (simp add: effect_unsafe_def duplicate_def)
      then show ?thesis ..
    next
      case False
      \<comment> \<open>(iii) a non-empty alien batch: stamped at the full prefix but
          outside it --- PREMATURE\<close>
      have p0_out: "p0 \<notin> {(ec1, e1), (ec2, e2)}"
        using False p0 by blast
      obtain c e where p_eq: "p0 = (c, e)" by (cases p0)
      have x_in: "(2, 1, c, e) \<in> set (dwe_emitted t1')"
        using p0 p_eq by (force simp: em1)
      have "\<not> justified_at (exec_src_hist (dwe_core t1')) (2, 1, c, e)"
        using p0_out p_eq
        by (simp add: justified_at_def src1 eval_nat_numeral)
      then have "premature t1'"
        unfolding premature_def using x_in by blast
      then have "effect_unsafe t1'"
        by (simp add: effect_unsafe_def)
      then show ?thesis ..
    qed
  qed

  \<comment> \<open>both redrives heal every scoped mismatch at the frontier\<close>
  have heal1: "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k"
    by (rule policy_redrive_heals[OF pr1])
  have heal2: "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k"
    by (rule policy_redrive_heals[OF pr2])

  show ?thesis
    using pr1 pr2 heal1 heal2 horn by blast
qed

section \<open>The lift: any pair-agreeing observation channel is defeated\<close>

text \<open>
  A recovery-metadata CHANNEL is an arbitrary observation
  @{typ "(nat, nat) dwe_state \<Rightarrow> 'r"} --- the result type is free, so
  this covers an externally persisted cursor value, a generation
  counter, a dedup digest, a boolean flag, any tuple of such.  A policy
  READS ONLY that channel when it factors through it.  If the channel
  agrees on the designed pair, the factored policy emits the same batch
  on both members and the exported kernel derivation applies verbatim.
  The class of defeated policies is parameterized by the observation,
  one abstraction rung above the landed @{const store_measured} /
  @{const store_epoch_measured} pattern (both are instances: project
  the core, or the core-epoch pair --- equal on the pair by
  @{thm [source] d_cores_eq} and the exported epoch fields).
\<close>

theorem pair_agreeing_observation_defeated:
  fixes obs :: "(nat, nat) dwe_state \<Rightarrow> 'r"
    and g :: "'r \<Rightarrow> (src_coord \<times> (nat, nat) source_event) list"
    and P :: redrive_policy
  assumes agree: "obs d1_w = obs d2_w"
      and factor: "\<And>t. P t = g (obs t)"
  shows "\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')"
proof -
  have "P d1_w = g (obs d1_w)" by (rule factor)
  also have "\<dots> = g (obs d2_w)" by (simp add: agree)
  also have "\<dots> = P d2_w" by (simp add: factor)
  finally have "P d1_w = P d2_w" .
  then show ?thesis by (rule pair_batch_agreement_defeated)
qed

section \<open>The exists-pair family shape\<close>

text \<open>
  The landed family shape (one designed pair defeats a whole class),
  restated with the class abstracted to observation-measured: one
  reachable, equal-core, equal-epoch, divergent-ledger, effect-safe,
  genuinely emitting pair defeats every policy that factors through any
  observation agreeing on the pair.  The result type of the observation
  is schematic, so the exists-statement below is one theorem PER result
  type; the same-pair-across-all-types reading is carried by
  @{thm [source] pair_agreeing_observation_defeated}, stated at the
  named pair @{const d1_w}/@{const d2_w} with the result type
  schematic.  The
  landed @{thm [source] batch_agreement_dilemma} is the SELF-OBSERVATION
  face (@{text "obs = P, g = id"}: the observation is the policy's own
  batch, so pair-agreement of the observation IS batch agreement; the
  identity observation would instead make the agreement premise
  @{text "d1_w = d2_w"}, refuted by the pair's divergent ledgers); the
  store-measured and (core, epoch)-measured theorems are the core and
  core-epoch projections.
\<close>

theorem observation_measured_dilemma:
  "\<exists>t1 t2.
     dwe_reachable t1 \<and> dwe_reachable t2
   \<and> dwe_core t1 = dwe_core t2
   \<and> dwe_epoch t1 = dwe_epoch t2
   \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
   \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
   \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
   \<and> (\<forall>(obs :: (nat, nat) dwe_state \<Rightarrow> 'r) g P.
        obs t1 = obs t2 \<longrightarrow> (\<forall>t. P t = g (obs t)) \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')))"
proof -
  have inner: "\<forall>(obs :: (nat, nat) dwe_state \<Rightarrow> 'r) g P.
        obs d1_w = obs d2_w \<longrightarrow> (\<forall>t. P t = g (obs t)) \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2'))"
  proof (intro allI impI)
    fix obs :: "(nat, nat) dwe_state \<Rightarrow> 'r"
      and g :: "'r \<Rightarrow> (src_coord \<times> (nat, nat) source_event) list"
      and P :: redrive_policy
    assume a1: "obs d1_w = obs d2_w" and a2: "\<forall>t. P t = g (obs t)"
    have fac: "\<And>t. P t = g (obs t)" using a2 by simp
    show "\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')"
      by (rule pair_agreeing_observation_defeated
                 [where obs = obs and g = g and P = P, OF a1 fac])
  qed
  have epochs: "dwe_epoch d1_w = dwe_epoch d2_w"
    by (simp add: d1_fields d2_fields)
  have all:
    "dwe_reachable d1_w \<and> dwe_reachable d2_w
   \<and> dwe_core d1_w = dwe_core d2_w
   \<and> dwe_epoch d1_w = dwe_epoch d2_w
   \<and> dwe_emitted d1_w \<noteq> dwe_emitted d2_w
   \<and> \<not> effect_unsafe d1_w \<and> \<not> effect_unsafe d2_w
   \<and> genuinely_emitting d1_w \<and> genuinely_emitting d2_w
   \<and> (\<forall>(obs :: (nat, nat) dwe_state \<Rightarrow> 'r) g P.
        obs d1_w = obs d2_w \<longrightarrow> (\<forall>t. P t = g (obs t)) \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')))"
    using reach_d1 reach_d2 d_cores_eq epochs d_emitted_neq d1_not_unsafe
          d2_not_unsafe d1_emitting d2_emitting inner
    by blast
  show ?thesis
    by (rule exI[of _ d1_w], rule exI[of _ d2_w], rule all)
qed

section \<open>The two-horn sharpening: duplicate or leave owed\<close>

text \<open>
  The kernel's two-horn form
  (@{thm [source] pair_batch_agreement_duplicate_or_lost}: at the
  designed pair the shared batch either re-fires a delivered payload ---
  the safe side DUPLICATES --- or never covers the committed second
  effect --- the skip side stays OWED; going premature is no escape from
  the pair's accounting), lifted through the same observation
  factoring as above.  Same redrives, same heal conjuncts; only the
  defeat disjunct sharpens from
  @{term "effect_unsafe t1' \<or> lost_effect ec2 t2'"} to
  @{term "duplicate t1' \<or> lost_effect ec2 t2'"}.  Facts of the designed
  pair, exists-system polarity throughout.
\<close>

theorem pair_agreeing_observation_duplicate_or_lost:
  fixes obs :: "(nat, nat) dwe_state \<Rightarrow> 'r"
    and g :: "'r \<Rightarrow> (src_coord \<times> (nat, nat) source_event) list"
    and P :: redrive_policy
  assumes agree: "obs d1_w = obs d2_w"
      and factor: "\<And>t. P t = g (obs t)"
  shows "\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (duplicate t1' \<or> lost_effect ec2 t2')"
proof -
  have "P d1_w = g (obs d1_w)" by (rule factor)
  also have "\<dots> = g (obs d2_w)" by (simp add: agree)
  also have "\<dots> = P d2_w" by (simp add: factor)
  finally have "P d1_w = P d2_w" .
  then show ?thesis by (rule pair_batch_agreement_duplicate_or_lost)
qed

text \<open>The exists-pair family shape with the sharpened disjunct,
  mirroring @{thm [source] observation_measured_dilemma}.\<close>

theorem observation_duplicate_or_lost:
  "\<exists>t1 t2.
     dwe_reachable t1 \<and> dwe_reachable t2
   \<and> dwe_core t1 = dwe_core t2
   \<and> dwe_epoch t1 = dwe_epoch t2
   \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
   \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
   \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
   \<and> (\<forall>(obs :: (nat, nat) dwe_state \<Rightarrow> 'r) g P.
        obs t1 = obs t2 \<longrightarrow> (\<forall>t. P t = g (obs t)) \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (duplicate t1' \<or> lost_effect ec2 t2')))"
proof -
  have inner: "\<forall>(obs :: (nat, nat) dwe_state \<Rightarrow> 'r) g P.
        obs d1_w = obs d2_w \<longrightarrow> (\<forall>t. P t = g (obs t)) \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (duplicate t1' \<or> lost_effect ec2 t2'))"
  proof (intro allI impI)
    fix obs :: "(nat, nat) dwe_state \<Rightarrow> 'r"
      and g :: "'r \<Rightarrow> (src_coord \<times> (nat, nat) source_event) list"
      and P :: redrive_policy
    assume a1: "obs d1_w = obs d2_w" and a2: "\<forall>t. P t = g (obs t)"
    have fac: "\<And>t. P t = g (obs t)" using a2 by simp
    show "\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (duplicate t1' \<or> lost_effect ec2 t2')"
      by (rule pair_agreeing_observation_duplicate_or_lost
                 [where obs = obs and g = g and P = P, OF a1 fac])
  qed
  have epochs: "dwe_epoch d1_w = dwe_epoch d2_w"
    by (simp add: d1_fields d2_fields)
  have all:
    "dwe_reachable d1_w \<and> dwe_reachable d2_w
   \<and> dwe_core d1_w = dwe_core d2_w
   \<and> dwe_epoch d1_w = dwe_epoch d2_w
   \<and> dwe_emitted d1_w \<noteq> dwe_emitted d2_w
   \<and> \<not> effect_unsafe d1_w \<and> \<not> effect_unsafe d2_w
   \<and> genuinely_emitting d1_w \<and> genuinely_emitting d2_w
   \<and> (\<forall>(obs :: (nat, nat) dwe_state \<Rightarrow> 'r) g P.
        obs d1_w = obs d2_w \<longrightarrow> (\<forall>t. P t = g (obs t)) \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (duplicate t1' \<or> lost_effect ec2 t2')))"
    using reach_d1 reach_d2 d_cores_eq epochs d_emitted_neq d1_not_unsafe
          d2_not_unsafe d1_emitting d2_emitting inner
    by blast
  show ?thesis
    by (rule exI[of _ d1_w], rule exI[of _ d2_w], rule all)
qed

section \<open>The honest boundary: an accurate delivery count separates\<close>

text \<open>
  The defeated class has a hard edge, and it is exactly where the
  dilemma's own escape lives.  A cursor persisted OUTSIDE the store that
  ACCURATELY tracks deliveries evaluates to 2 on @{const d1_w} and 1 on
  @{const d2_w} --- the members differ precisely in the emission ledger
  --- so it fails the agreement premise of every theorem above: no
  statement of this theory defeats it.  By the Dichotomy lane's bridge
  (@{thm [source] ledger_blind_iff_store_epoch_measured}) any policy
  whose batch separates the pair is NOT ledger-blind --- it reads the
  sink, landing on the sink-reading horn of
  @{thm [source] redrive_policy_dichotomy}.  Whether a given
  sink-reading policy also EARNS the escape's guarantees (heals, stays
  effect-safe, loses nothing) is a separate question, answered
  positively for the landed @{const sink_delta} policy alone
  (@{thm [source] sink_reading_escape_general},
  @{thm [source] sink_delta_achieves_exactly_once}); this theory adds
  no new claim on the escape side.
\<close>

lemma ledger_length_separates_pair:
  "length (dwe_emitted d1_w) = 2 \<and> length (dwe_emitted d2_w) = 1"
  by (simp add: d1_fields d2_fields)

text \<open>
  The tie-back to the landed dichotomy: separating the designed pair
  already certifies sink-reading --- the pair's cores are literally
  equal and its epochs are both 1, so a pair-separating policy violates
  ledger-blindness at the pair itself.
\<close>

lemma pair_separating_not_ledger_blind:
  fixes P :: redrive_policy
  assumes sep: "P d1_w \<noteq> P d2_w"
  shows "\<not> ledger_blind P"
proof
  assume lb: "ledger_blind P"
  have "P d1_w = P d2_w"
    by (rule lb[unfolded ledger_blind_def, rule_format])
       (simp add: d_cores_eq d1_fields d2_fields)
  with sep show False by simp
qed

section \<open>Defeat is pair-agreement, not ledger-blindness\<close>

text \<open>
  The defeated class is not delimited by the ledger-blind
  (= (core, epoch)-measured, by the Dichotomy bridge) criterion: here is
  an observation that genuinely READS the ledger --- its emptiness bit
  --- yet agrees on the designed pair (both ledgers are non-empty), so
  every policy factoring through it is still defeated.  (The family
  also contains ledger-blind members --- constant @{text g} --- so this
  exhibits reach beyond the ledger-blind criterion, not a landed strict
  class extension.)  Reading the
  sink is necessary for survival, not sufficient: the channel must
  resolve the pair, i.e. carry the delivered-suffix information the
  members actually differ in.
\<close>

corollary ledger_reading_observation_still_defeated:
  fixes g :: "bool \<Rightarrow> (src_coord \<times> (nat, nat) source_event) list"
    and P :: redrive_policy
  assumes factor: "\<And>t. P t = g (dwe_emitted t = [])"
  shows "\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')"
proof -
  have agree: "(dwe_emitted d1_w = []) = (dwe_emitted d2_w = [])"
    by (simp add: d1_fields d2_fields)
  show ?thesis
    by (rule pair_agreeing_observation_defeated
               [where obs = "\<lambda>t. dwe_emitted t = []" and g = g and P = P,
                OF agree factor])
qed

end
