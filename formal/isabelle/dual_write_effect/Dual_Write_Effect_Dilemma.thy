(*  Title:       Dual_Write_Effect_Dilemma.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE HEADLINE LAW: the RECOVERY-INFORMATION DILEMMA on the operational
    cyclic effect machine.

    Theorem A (recovery_information_dilemma): EVERY store-measured re-drive
    policy --- any recovery rule whose emitted batch is a function of the
    crashed core alone, subsuming every store-persisted cursor (any
    checkpoint value recoverable from the crashed store, however adaptively
    chosen from it) and every store-side dedup filter --- is defeated on
    the cyclic effect
    machine: there is an equal-core reachable pair of effect-safe,
    genuinely-emitting crashed states on which the policy's OWN redrive
    either duplicates an already-delivered effect (or emits an unjustified
    one) on one member, or loses a committed effect on the other.  Loss is
    a HORN, not a premise: a policy cannot escape by refusing to emit.

    Theorem B (the sink-reading escape): the payload-delta policy that READS
    THE SINK (filters the frontier-bounded replay against the payloads
    already in the emission ledger) heals, never duplicates, never goes
    premature, and never loses --- under the named strictly-ascending-source
    premise --- and is provably NOT store-measured (B2), via the same
    equal-core pair.  So the dilemma is real and the escape must read
    information outside the store.

    A cursor persisted outside the store that accurately tracks deliveries
    is exactly such outside information: the designed pair's members agree
    on the whole durable core and on the recovery epoch and differ only in
    the emission ledger (the wrapper record has exactly these three
    fields), so any recovery input that distinguishes them is
    ledger-derived --- a policy consulting it cannot factor through
    (core, epoch) and is therefore outside every class Theorem A and its
    epoch extension defeat.  Whether such a policy also EARNS the escape's
    guarantees is the separate positive question Theorem B answers for the
    sink-reading payload-delta policy; the dichotomy theory's exhaustive
    split locates every pair-distinguishing policy on its sink-reading
    side.

    DESIGN PROPERTY (checked): NO advertised-frontier scoping appears
    anywhere; the redrive rule carries only its own f <= exec_finish guard.

    Ported from the S1-audited artifact (paper/dual_write/phase3/scratch/
    s1_dilemma/Dilemma.thy: machine-checked green, independently rebuilt,
    gate-panel audited) with the audited theorem statements UNCHANGED, plus
    the C1 punch-list strengthenings landed at port time:

    - batch_agreement_dilemma: the proof's content as a BATCH-AGREEMENT
      kernel in exists-pair form --- ONE designed-in equal-core, equal-epoch,
      divergent-ledger pair defeats every policy that emits the same batch
      on both members.  The audited Theorem A, its exists-pair/for-all-P
      form, and the epoch-extended corollary all derive from this kernel.
    - store_epoch_measured + epoch_measured_dilemma (GAP-2): policies
      reading (core, epoch) --- e.g. a persisted recovery-generation
      counter --- are covered by the same pair.
    - cursor_policy_store_measured (GAP-1): the cursor rule's policy form
      provably factors through the core, so cursor subsumption is fully
      machine-checked, not prose.
    - sink_reading_escape_general (B1 premise-free): the audited B1's
      reachability premise is never consumed (S1 audit finding); the
      general form drops it and the audited statement follows by weakening.

    The scratch original's in-source ML oracle gates are STRIPPED here:
    oracle-freedom is certified by scratch-side per-slice gate sessions
    with confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Dilemma
  imports Dual_Write_Effect_Cyclic
begin

section \<open>Re-drive policies and the pinned policy redrive rule\<close>

text \<open>
  A re-drive policy inspects the crashed wrapper state and returns the
  payload batch to emit during recovery.  Pinned at the witness
  instantiation @{typ "(nat, nat) dwe_state"}, matching
  @{const dwe_reachable}.
\<close>

type_synonym redrive_policy =
  "(nat, nat) dwe_state \<Rightarrow> (src_coord \<times> (nat, nat) source_event) list"

text \<open>
  The pinned reconcile with the policy batch replacing the cursor suffix
  @{term "drop m R"}: the core part is literally the landed
  @{const relay_bounded_replay_reconcile}; the ledger appends the policy's
  batch, stamped with the current committed-prefix length and epoch.
  The ONLY frontier condition is the rule's own
  @{term "f \<le> exec_finish (dwe_core t)"} guard --- no advertised-frontier
  scoping (design property).
\<close>

definition policy_redrive
  :: "redrive_policy \<Rightarrow> (nat, nat) dwe_state \<Rightarrow> frontier \<Rightarrow>
      (nat, nat) dwe_state \<Rightarrow> bool"
where
  "policy_redrive P t f t' \<longleftrightarrow>
     (\<exists>c. exec_status (dwe_core t) = Crashed c)
   \<and> f \<le> exec_finish (dwe_core t)
   \<and> t' = t\<lparr>dwe_core := (dwe_core t)
              \<lparr>exec_down_hist :=
                 replay_down_hist (exec_src_hist (dwe_core t))
                   (exec_scope (dwe_core t)) f,
               exec_pending := {},
               exec_status := Recovered\<rparr>,
            dwe_emitted := dwe_emitted t
              @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                               dwe_epoch t, c, e))
                  (P t)\<rparr>"

text \<open>The unique result state, as a function (for witness construction).\<close>

definition redrive_result
  :: "redrive_policy \<Rightarrow> (nat, nat) dwe_state \<Rightarrow> frontier \<Rightarrow>
      (nat, nat) dwe_state"
where
  "redrive_result P t f =
     t\<lparr>dwe_core := (dwe_core t)
         \<lparr>exec_down_hist :=
            replay_down_hist (exec_src_hist (dwe_core t))
              (exec_scope (dwe_core t)) f,
          exec_pending := {},
          exec_status := Recovered\<rparr>,
       dwe_emitted := dwe_emitted t
         @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                          dwe_epoch t, c, e))
             (P t)\<rparr>"

lemma policy_redriveI:
  assumes "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and "f \<le> exec_finish (dwe_core t)"
  shows "policy_redrive P t f (redrive_result P t f)"
  using assms by (simp add: policy_redrive_def redrive_result_def)

lemma policy_redrive_result:
  assumes "policy_redrive P t f t'"
  shows "t' = redrive_result P t f"
  using assms by (simp add: policy_redrive_def redrive_result_def)

text \<open>
  SANITY (the cursor rule is a policy instance): the banked
  @{const emitting_reconcile} with persisted cursor @{term m} is EXACTLY
  the policy redrive for the drop-@{term m}-of-the-replay policy, up to the
  cursor's own in-range guard.  So Theorem A quantifies over every value
  of the rule's store-persisted cursor.
\<close>

lemma cursor_rule_is_policy_instance:
  "emitting_reconcile m t f t' \<longleftrightarrow>
     m \<le> length (replay_down_hist (exec_src_hist (dwe_core t))
                    (exec_scope (dwe_core t)) f)
   \<and> policy_redrive
       (\<lambda>s. drop m (replay_down_hist (exec_src_hist (dwe_core s))
                      (exec_scope (dwe_core s)) f))
       t f t'"
  by (auto simp: emitting_reconcile_def policy_redrive_def)

section \<open>Store-measured policies, loss, and the sink-reading delta\<close>

text \<open>
  Type-level obliviousness: the policy's batch factors through the crashed
  CORE alone.  This subsumes every store-persisted cursor (the cursor
  value is a function of nothing at all, hence of the core) and every
  store-side dedup filter (any function of the whole core record:
  base/src/down/enqueued/pending/scope/finish/status/acked --- an
  acknowledgement-log reader is inside the class and defeated with it).
\<close>

definition store_measured :: "redrive_policy \<Rightarrow> bool" where
  "store_measured P \<longleftrightarrow> (\<exists>g. \<forall>t. P t = g (dwe_core t))"

text \<open>
  GAP-1 (cursor subsumption, fully machine-checked): the cursor rule's
  policy form --- @{thm [source] cursor_rule_is_policy_instance} above ---
  provably factors through the crashed core, so Theorem A's quantifier
  covers every store-persisted cursor by THEOREM, not by prose.
\<close>

lemma cursor_policy_store_measured:
  "store_measured
     (\<lambda>s. drop m (replay_down_hist (exec_src_hist (dwe_core s))
                    (exec_scope (dwe_core s)) f))"
  unfolding store_measured_def
  by (intro exI[of _ "\<lambda>c. drop m (replay_down_hist (exec_src_hist c)
                                    (exec_scope c) f)"]) simp

text \<open>
  Loss, evaluated at the reconcile's OWN frontier @{term f}: some payload
  of the scoped, frontier-bounded replay of the committed source prefix
  never appears in the emission ledger.  NO advertised-frontier side
  condition (design property).

  Two pinned readings so neither horn can be read as more than the model
  claims:

  BULK-RESTORE reading: the emitting reconcile installs the full scoped,
  frontier-bounded replay as the new durable downstream history --- the
  store heals at f regardless of the cursor m (the landed heal theorems);
  m governs only which suffix is FIRED.  Healing never implies firing,
  and loss charges the policy with exactly the fired-side gap of that
  bulk restore, never with a store mismatch.

  TERMINAL-STATE STAND-IN reading: @{text lost_effect} is a state-level reading
  at the redrive's own frontier --- a stand-in for delivery liveness of
  the same kind as the landed tier-1 acknowledgement-durability boundary,
  not a temporal eventually.  Emissions of a later Running segment are
  new application work, not the recovery's redrive; the exactly-once
  theory's definitional bridge (at-least-once iff not lost) carries this
  disclosed status forward.
\<close>

definition lost_effect :: "frontier \<Rightarrow> (nat, nat) dwe_state \<Rightarrow> bool" where
  "lost_effect f t' \<longleftrightarrow>
     (\<exists>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t'))
                   (exec_scope (dwe_core t')) f).
        p \<notin> e_payload ` set (dwe_emitted t'))"

text \<open>
  The named premise (now consumed): source coordinates strictly increase
  along the history, so payload-level dedup is exact.  It implies distinct
  entries, hence distinct payloads of any filtered sublist.
\<close>

definition strictly_ascending_source :: "('k, 'v) src_history \<Rightarrow> bool" where
  "strictly_ascending_source H \<longleftrightarrow> sorted_wrt (\<lambda>p q. fst p < fst q) H"

lemma strictly_ascending_distinct:
  assumes "strictly_ascending_source H"
  shows "distinct H"
  using assms unfolding strictly_ascending_source_def
  by (induction H) auto

text \<open>
  The SINK-READING policy: emit exactly the frontier-bounded replay
  payloads that are NOT already in the emission ledger.  It reads
  @{const dwe_emitted} --- the sink --- which no store-measured policy can.
\<close>

definition sink_delta
  :: "frontier \<Rightarrow> (nat, nat) dwe_state \<Rightarrow>
      (src_coord \<times> (nat, nat) source_event) list"
where
  "sink_delta f t =
     filter (\<lambda>p. p \<notin> e_payload ` set (dwe_emitted t))
       (replay_down_hist (exec_src_hist (dwe_core t))
          (exec_scope (dwe_core t)) f)"

section \<open>Generic redrive facts: core projection, healing, justification\<close>

lemma policy_redrive_core:
  assumes "policy_redrive P t f t'"
  shows "relay_bounded_replay_reconcile (dwe_core t) f (dwe_core t')"
  using assms
  by (simp add: policy_redrive_def relay_bounded_replay_reconcile_def)

theorem policy_redrive_effective:
  assumes "policy_redrive P t f t'"
  shows "recovery_effectively_redelivers_source_history_at
           (dwe_core t) f (dwe_core t')"
  by (rule relay_bounded_replay_reconcile_effective[OF policy_redrive_core[OF assms]])

corollary policy_redrive_heals:
  assumes "policy_redrive P t f t'"
  shows "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k"
  by (rule recovery_effective_redelivery_no_mismatch[OF policy_redrive_effective[OF assms]])

lemma policy_redrive_src_same:
  assumes "policy_redrive P t f t'"
  shows "exec_src_hist (dwe_core t') = exec_src_hist (dwe_core t)"
  using assms by (simp add: policy_redrive_def)

lemma policy_redrive_scope_same:
  assumes "policy_redrive P t f t'"
  shows "exec_scope (dwe_core t') = exec_scope (dwe_core t)"
  using assms by (simp add: policy_redrive_def)

lemma policy_redrive_emitted:
  assumes "policy_redrive P t f t'"
  shows "dwe_emitted t' = dwe_emitted t
           @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                            dwe_epoch t, c, e))
               (P t)"
  using assms by (simp add: policy_redrive_def)

text \<open>Payload bookkeeping for stamped batches.  Because tuples nest to the
  right, the stamping function IS the right-nested pairing
  @{term "\<lambda>p. (n, ep, p)"}, so payload extraction is the identity on the
  batch --- stated as pointwise @{method simp} rules.\<close>

lemma stamp_case_collapse [simp]:
  "(\<lambda>(c, e). (n, ep, c, e)) = (\<lambda>p. (n, ep, p))"
  by (simp add: fun_eq_iff case_prod_beta)

lemma e_payload_stamp [simp]: "e_payload (n, ep, p) = p"
  by (simp add: e_payload_def)

lemma payload_stamp_comp [simp]:
  "e_payload \<circ> (\<lambda>p. (n, ep, p)) = (\<lambda>p. p)"
  by (rule ext) simp

lemma map_payload_stamped:
  "map e_payload (map (\<lambda>(c, e). (n, ep, c, e)) B) = B"
  by simp

lemma stamped_elem:
  assumes "x \<in> set (map (\<lambda>(c, e). (n, ep, c, e)) B)"
  shows "e_stamp x = n \<and> e_epoch x = ep \<and> e_payload x \<in> set B"
  using assms by (auto simp: e_stamp_def e_epoch_def)

lemma stamped_payload_set:
  "e_payload ` set (map (\<lambda>(c, e). (n, ep, c, e)) B) = set B"
  by (simp add: image_image)

text \<open>The replay is a filter of the committed source prefix.\<close>

lemma replay_down_hist_subset:
  "set (replay_down_hist S K f) \<subseteq> set S"
  unfolding replay_down_hist_def by auto

text \<open>
  THE GENERIC JUSTIFICATION LEMMA: any emission stamped with the full
  committed-prefix length whose payload comes from the frontier-bounded
  replay is justified --- for EVERY policy, every batch member, every
  epoch.  Duplication is orthogonal to justification as a for-all fact,
  not a per-witness evaluation.
\<close>

lemma redrive_emissions_justified:
  assumes "e_payload x \<in> set (replay_down_hist S K f)"
      and "e_stamp x = length S"
  shows "justified_at S x"
proof -
  have "e_payload x \<in> set S"
    using assms(1) replay_down_hist_subset by blast
  then show ?thesis
    by (simp add: justified_at_def assms(2))
qed

section \<open>The equal-core divergent-ledger pair: witness states\<close>

text \<open>
  @{const t_mid_w} (banked) is the crashed loaded window with ledger
  @{term "[(1, 0, ec1, e1)]"}.  Its m = 2 reconcile SKIPS the still-missing
  second effect: the suffix @{term "drop 2 R"} is empty, the ledger stays,
  the core heals to the same record as @{const t_safe_w}'s core.
\<close>

definition t_skip_w :: "(nat, nat) dwe_state" where
  "t_skip_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)]
                     [(ec1, e1), (ec2, e2)] {} Recovered)
                  [(1, 0, ec1, e1)] 0"

text \<open>Resume both recovered states into epoch 1 ...\<close>

definition r_safe_w :: "(nat, nat) dwe_state" where
  "r_safe_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)]
                     [(ec1, e1), (ec2, e2)] {} Running)
                  [(1, 0, ec1, e1), (2, 0, ec2, e2)] 1"

definition r_skip_w :: "(nat, nat) dwe_state" where
  "r_skip_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)]
                     [(ec1, e1), (ec2, e2)] {} Running)
                  [(1, 0, ec1, e1)] 1"

text \<open>... and crash both at @{const ec2}: LITERALLY EQUAL cores, divergent
  ledgers, both effect-safe, both genuinely emitting.\<close>

definition d1_w :: "(nat, nat) dwe_state" where
  "d1_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)]
                 [(ec1, e1), (ec2, e2)] {} (Crashed ec2))
              [(1, 0, ec1, e1), (2, 0, ec2, e2)] 1"

definition d2_w :: "(nat, nat) dwe_state" where
  "d2_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)]
                 [(ec1, e1), (ec2, e2)] {} (Crashed ec2))
              [(1, 0, ec1, e1)] 1"

subsection \<open>Witness transitions\<close>

lemma rec_skip: "emitting_reconcile 2 t_mid_w ec2 t_skip_w"
  by (simp add: emitting_reconcile_def t_mid_w_def t_skip_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs eval_nat_numeral)

lemma res_safe: "dwe_resume t_safe_w r_safe_w"
  by (simp add: dwe_resume_def t_safe_w_def r_safe_w_def mkT_def mkC_def
                eval_nat_numeral)

lemma res_skip: "dwe_resume t_skip_w r_skip_w"
  by (simp add: dwe_resume_def t_skip_w_def r_skip_w_def mkT_def mkC_def
                eval_nat_numeral)

lemma wf_r_safe: "wellformed_exec_state (dwe_core r_safe_w)"
  by (simp add: r_safe_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_pair)

lemma wf_r_skip: "wellformed_exec_state (dwe_core r_skip_w)"
  by (simp add: r_skip_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_pair)

lemma g_r_safe_crash:
  "exec_label_preserves_history_wf (dwe_core r_safe_w) (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma g_r_skip_crash:
  "exec_label_preserves_history_wf (dwe_core r_skip_w) (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma crash_d1: "dwe_step r_safe_w (Crash ec2) d1_w"
proof -
  have c: "dw_exec_step (dwe_core r_safe_w) (Crash ec2) (dwe_core d1_w)"
    by (rule crashI) (simp_all add: r_safe_w_def d1_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: r_safe_w_def d1_w_def mkT_def)
qed

lemma crash_d2: "dwe_step r_skip_w (Crash ec2) d2_w"
proof -
  have c: "dw_exec_step (dwe_core r_skip_w) (Crash ec2) (dwe_core d2_w)"
    by (rule crashI) (simp_all add: r_skip_w_def d2_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: r_skip_w_def d2_w_def mkT_def)
qed

subsection \<open>Reachability\<close>

lemma reach_t_skip: "dwe_reachable t_skip_w"
  by (rule dwe_reachable_reconcile_ext[OF reach_t_mid rec_skip])

lemma reach_r_safe: "dwe_reachable r_safe_w"
  by (rule dwe_reachable_resume_ext[OF reach_t_safe res_safe])

lemma reach_r_skip: "dwe_reachable r_skip_w"
  by (rule dwe_reachable_resume_ext[OF reach_t_skip res_skip])

lemma reach_d1: "dwe_reachable d1_w"
  by (rule dwe_reachable_label_ext[OF reach_r_safe wf_r_safe g_r_safe_crash crash_d1])

lemma reach_d2: "dwe_reachable d2_w"
  by (rule dwe_reachable_label_ext[OF reach_r_skip wf_r_skip g_r_skip_crash crash_d2])

subsection \<open>Verdict evaluations on the pair\<close>

lemma d_cores_eq: "dwe_core d1_w = dwe_core d2_w"
  by (simp add: d1_w_def d2_w_def mkT_def)

lemma d_emitted_neq: "dwe_emitted d1_w \<noteq> dwe_emitted d2_w"
  by (simp add: d1_w_def d2_w_def mkT_def)

lemma d1_not_unsafe: "\<not> effect_unsafe d1_w"
  by (simp add: effect_unsafe_def premature_def duplicate_def justified_at_def
                d1_w_def mkT_def mkC_def e1_def e2_def ec_defs eval_nat_numeral)

lemma d2_not_unsafe: "\<not> effect_unsafe d2_w"
  by (simp add: effect_unsafe_def premature_def duplicate_def justified_at_def
                d2_w_def mkT_def mkC_def e1_def e2_def ec_defs eval_nat_numeral)

lemma d1_emitting: "genuinely_emitting d1_w"
  by (simp add: genuinely_emitting_def d1_w_def mkT_def)

lemma d2_emitting: "genuinely_emitting d2_w"
  by (simp add: genuinely_emitting_def d2_w_def mkT_def)

text \<open>Field-level normal forms consumed by the dilemma's case analysis.\<close>

lemma d1_fields:
  "exec_status (dwe_core d1_w) = Crashed ec2"
  "exec_finish (dwe_core d1_w) = ec2"
  "exec_src_hist (dwe_core d1_w) = [(ec1, e1), (ec2, e2)]"
  "exec_scope (dwe_core d1_w) = {0, 1}"
  "dwe_epoch d1_w = 1"
  "dwe_emitted d1_w = [(1, 0, ec1, e1), (2, 0, ec2, e2)]"
  by (simp_all add: d1_w_def mkT_def mkC_def)

lemma d2_fields:
  "exec_status (dwe_core d2_w) = Crashed ec2"
  "exec_finish (dwe_core d2_w) = ec2"
  "exec_src_hist (dwe_core d2_w) = [(ec1, e1), (ec2, e2)]"
  "exec_scope (dwe_core d2_w) = {0, 1}"
  "dwe_epoch d2_w = 1"
  "dwe_emitted d2_w = [(1, 0, ec1, e1)]"
  by (simp_all add: d2_w_def mkT_def mkC_def)

lemma replay_pair_eval:
  "replay_down_hist [(ec1, e1), (ec2, e2)] {0, 1} ec2 = [(ec1, e1), (ec2, e2)]"
  by (simp add: replay_down_hist_def e1_def e2_def ec_defs)

section \<open>THEOREM A: the recovery-information dilemma\<close>

text \<open>
  Every store-measured policy P emits the SAME batch B on the equal-core
  pair.  Three total cases on B: (i) B empty --- the skip-side redrive
  loses the committed second effect; (ii) some batch payload is already
  in the safe-side ledger --- the safe-side redrive duplicates; (iii) B
  non-empty with only alien payloads --- the safe-side redrive is
  premature (stamped at the full prefix, payload outside it).  Loss is a
  horn, not a premise; coverage is total.  Both redrives HEAL every
  scoped mismatch at the frontier --- healing cannot arbitrate.
\<close>

text \<open>
  The proof's information content is banked once, as a BATCH-AGREEMENT
  kernel in exists-pair form: the designed-in equal-core, equal-epoch,
  divergent-ledger pair defeats EVERY policy that emits the same batch on
  both of its members.  A measurability class enters only through one
  fact: its policies cannot distinguish the pair.  Store-measured policies
  agree because the cores are literally equal (Theorem A below);
  (core, epoch)-measured policies agree because the epochs are equal too
  (the corollary below); and the sink-reading escape of Theorem B is
  exactly a policy that CAN distinguish the pair --- it reads the one
  component on which the members differ.
\<close>

theorem batch_agreement_dilemma:
  "\<exists>t1 t2.
     dwe_reachable t1 \<and> dwe_reachable t2
   \<and> dwe_core t1 = dwe_core t2
   \<and> dwe_epoch t1 = dwe_epoch t2
   \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
   \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
   \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
   \<and> (\<forall>P. P t1 = P t2 \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')))"
proof -
  have inner: "\<forall>P. P d1_w = P d2_w \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2'))"
  proof (intro allI impI)
    fix P :: redrive_policy
    assume PB: "P d1_w = P d2_w"
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

    show "\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')"
      using pr1 pr2 heal1 heal2 horn by blast
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
   \<and> (\<forall>P. P d1_w = P d2_w \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')))"
    using reach_d1 reach_d2 d_cores_eq epochs d_emitted_neq d1_not_unsafe
          d2_not_unsafe d1_emitting d2_emitting inner
    by blast
  then show ?thesis by blast
qed

text \<open>
  The exists-pair/for-all-P form for the store-measured class: ONE pair
  defeats ALL store-measured policies (the audited Theorem A statement,
  which re-orders the quantifiers, follows below).
\<close>

theorem recovery_information_dilemma_pair:
  "\<exists>t1 t2.
     dwe_reachable t1 \<and> dwe_reachable t2
   \<and> dwe_core t1 = dwe_core t2
   \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
   \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
   \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
   \<and> (\<forall>P. store_measured P \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')))"
proof -
  obtain t1 t2 where
    r1: "dwe_reachable t1" and r2: "dwe_reachable t2"
    and ceq: "dwe_core t1 = dwe_core t2"
    and lneq: "dwe_emitted t1 \<noteq> dwe_emitted t2"
    and s1: "\<not> effect_unsafe t1" and s2: "\<not> effect_unsafe t2"
    and g1: "genuinely_emitting t1" and g2: "genuinely_emitting t2"
    and agree: "\<forall>P. P t1 = P t2 \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2'))"
    using batch_agreement_dilemma by blast
  have sm: "\<forall>P. store_measured P \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2'))"
  proof (intro allI impI)
    fix P :: redrive_policy
    assume "store_measured P"
    then obtain g where "\<forall>t. P t = g (dwe_core t)"
      unfolding store_measured_def by blast
    then have "P t1 = P t2"
      using ceq by metis
    then show "\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')"
      using agree by blast
  qed
  have all:
    "dwe_reachable t1 \<and> dwe_reachable t2
   \<and> dwe_core t1 = dwe_core t2
   \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
   \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
   \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
   \<and> (\<forall>P. store_measured P \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')))"
    using r1 r2 ceq lneq s1 s2 g1 g2 sm by blast
  then show ?thesis by blast
qed

text \<open>The audited Theorem A statement, verbatim: derived by re-ordering
  the quantifiers of the exists-pair form.\<close>

theorem recovery_information_dilemma:
  "\<forall>P. store_measured P \<longrightarrow>
     (\<exists>t1 t2 t1' t2'.
        dwe_reachable t1 \<and> dwe_reachable t2
      \<and> dwe_core t1 = dwe_core t2
      \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
      \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
      \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
      \<and> policy_redrive P t1 ec2 t1'
      \<and> policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
      \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2'))"
proof (intro allI impI)
  fix P :: redrive_policy
  assume sm: "store_measured P"
  obtain t1 t2 where
    base: "dwe_reachable t1" "dwe_reachable t2"
          "dwe_core t1 = dwe_core t2"
          "dwe_emitted t1 \<noteq> dwe_emitted t2"
          "\<not> effect_unsafe t1" "\<not> effect_unsafe t2"
          "genuinely_emitting t1" "genuinely_emitting t2"
    and inner: "\<forall>P. store_measured P \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2'))"
    using recovery_information_dilemma_pair by blast
  obtain t1' t2' where
    prim: "policy_redrive P t1 ec2 t1'" "policy_redrive P t2 ec2 t2'"
          "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k"
          "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k"
          "effect_unsafe t1' \<or> lost_effect ec2 t2'"
    using inner sm by blast
  show "\<exists>t1 t2 t1' t2'.
        dwe_reachable t1 \<and> dwe_reachable t2
      \<and> dwe_core t1 = dwe_core t2
      \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
      \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
      \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
      \<and> policy_redrive P t1 ec2 t1'
      \<and> policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
      \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')"
    using base prim by blast
qed

section \<open>The epoch extension: policies reading the recovery generation\<close>

text \<open>
  GAP-2: a real recovery routine may read a persisted recovery-generation
  counter in addition to the store.  The dilemma pair has EQUAL epochs, so
  the same kernel defeats every policy factoring through (core, epoch) ---
  a store-measured policy is trivially (core, epoch)-measured, so this
  class is strictly larger.
\<close>

definition store_epoch_measured :: "redrive_policy \<Rightarrow> bool" where
  "store_epoch_measured P \<longleftrightarrow>
     (\<exists>g. \<forall>t. P t = g (dwe_core t) (dwe_epoch t))"

lemma store_measured_imp_epoch_measured:
  assumes "store_measured P"
  shows "store_epoch_measured P"
proof -
  from assms obtain g where g: "\<forall>t. P t = g (dwe_core t)"
    unfolding store_measured_def by blast
  show ?thesis
    unfolding store_epoch_measured_def
    by (intro exI[of _ "\<lambda>c ep. g c"]) (simp add: g)
qed

text \<open>
  The exists-pair/for-all-P form for the (store, epoch)-measured class,
  mirroring @{thm [source] recovery_information_dilemma_pair}: ONE designed
  pair --- its members carry EQUAL epochs --- defeats ALL
  (store, epoch)-measured policies.  The quantifier-reordered form follows
  as a corollary.
\<close>

theorem epoch_measured_dilemma_pair:
  "\<exists>t1 t2.
     dwe_reachable t1 \<and> dwe_reachable t2
   \<and> dwe_core t1 = dwe_core t2
   \<and> dwe_epoch t1 = dwe_epoch t2
   \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
   \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
   \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
   \<and> (\<forall>P. store_epoch_measured P \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')))"
proof -
  obtain t1 t2 where
    base: "dwe_reachable t1" "dwe_reachable t2"
          "dwe_core t1 = dwe_core t2"
          "dwe_epoch t1 = dwe_epoch t2"
          "dwe_emitted t1 \<noteq> dwe_emitted t2"
          "\<not> effect_unsafe t1" "\<not> effect_unsafe t2"
          "genuinely_emitting t1" "genuinely_emitting t2"
    and agree: "\<forall>P. P t1 = P t2 \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2'))"
    using batch_agreement_dilemma by blast
  have sem_all: "\<forall>P. store_epoch_measured P \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2'))"
  proof (intro allI impI)
    fix P :: redrive_policy
    assume "store_epoch_measured P"
    then obtain g where "\<forall>t. P t = g (dwe_core t) (dwe_epoch t)"
      unfolding store_epoch_measured_def by blast
    then have "P t1 = P t2"
      using base(3) base(4) by metis
    then show "\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')"
      using agree by blast
  qed
  have all:
    "dwe_reachable t1 \<and> dwe_reachable t2
   \<and> dwe_core t1 = dwe_core t2
   \<and> dwe_epoch t1 = dwe_epoch t2
   \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
   \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
   \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
   \<and> (\<forall>P. store_epoch_measured P \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')))"
    using base sem_all by blast
  then show ?thesis by blast
qed

text \<open>The quantifier-reordered form, now a corollary of the fixed pair.\<close>

theorem epoch_measured_dilemma:
  "\<forall>P. store_epoch_measured P \<longrightarrow>
     (\<exists>t1 t2 t1' t2'.
        dwe_reachable t1 \<and> dwe_reachable t2
      \<and> dwe_core t1 = dwe_core t2
      \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
      \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
      \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
      \<and> policy_redrive P t1 ec2 t1'
      \<and> policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
      \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2'))"
proof (intro allI impI)
  fix P :: redrive_policy
  assume sem: "store_epoch_measured P"
  obtain t1 t2 where
    base: "dwe_reachable t1" "dwe_reachable t2"
          "dwe_core t1 = dwe_core t2"
          "dwe_epoch t1 = dwe_epoch t2"
          "dwe_emitted t1 \<noteq> dwe_emitted t2"
          "\<not> effect_unsafe t1" "\<not> effect_unsafe t2"
          "genuinely_emitting t1" "genuinely_emitting t2"
    and inner: "\<forall>P. store_epoch_measured P \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2'))"
    using epoch_measured_dilemma_pair by blast
  obtain t1' t2' where
    prim: "policy_redrive P t1 ec2 t1'" "policy_redrive P t2 ec2 t2'"
          "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k"
          "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k"
          "effect_unsafe t1' \<or> lost_effect ec2 t2'"
    using inner sem by blast
  show "\<exists>t1 t2 t1' t2'.
        dwe_reachable t1 \<and> dwe_reachable t2
      \<and> dwe_core t1 = dwe_core t2
      \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
      \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
      \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
      \<and> policy_redrive P t1 ec2 t1'
      \<and> policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
      \<and> (effect_unsafe t1' \<or> lost_effect ec2 t2')"
    using base(1,2,3,5,6,7,8,9) prim by blast
qed

section \<open>The two-horn sharpening at the designed pair: duplicate or leave owed\<close>

text \<open>
  The kernel's defeat disjunct names three hazards --- premature or
  duplicate on the first member's redrive, loss on the second member's.
  At the designed pair the accounting is really TWO-horned: the shared
  batch either re-fires an already-delivered payload --- the safe side
  DUPLICATES --- or it contains no already-delivered payload at all, and
  then it never covers the committed second effect either (that effect,
  @{term "(ec2, e2)"}, IS a delivered payload of the safe member), so
  the skip side still OWES it.  The kernel proof's empty-batch and
  alien-batch cases both land in the loss horn; in particular going
  premature buys no third outcome --- a policy whose batch is premature
  on the safe member without re-firing a delivered payload still loses
  the committed effect on the skip member, and one that does re-fire
  lands in the duplicate horn.  Checked below as corollaries at the same
  designed pair, with the same redrives and the same heal conjuncts;
  only the defeat disjunct sharpens, from
  @{term "effect_unsafe t1' \<or> lost_effect ec2 t2'"} to
  @{term "duplicate t1' \<or> lost_effect ec2 t2'"}.  These are facts OF
  THE DESIGNED PAIR (exists-system polarity, like the whole family),
  not new for-all laws over states.
\<close>

theorem pair_batch_agreement_duplicate_or_lost:
  fixes P :: redrive_policy
  assumes PB: "P d1_w = P d2_w"
  shows "\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (duplicate t1' \<or> lost_effect ec2 t2')"
proof -
  define B where "B = P d1_w"
  have PB2: "P d2_w = B"
    using PB unfolding B_def by simp

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

  \<comment> \<open>concrete ledgers of the post-states, both expressed in the shared B\<close>
  have em1: "dwe_emitted t1'
      = [(1, 0, ec1, e1), (2, 0, ec2, e2)] @ map (\<lambda>(c, e). (2, 1, c, e)) B"
    unfolding t1'_def B_def redrive_result_def
    by (simp add: d1_w_def mkT_def mkC_def eval_nat_numeral)
  have em2': "dwe_emitted t2'
      = [(1, 0, ec1, e1)] @ map (\<lambda>(c, e). (2, 1, c, e)) (P d2_w)"
    unfolding t2'_def redrive_result_def
    by (simp add: d2_w_def mkT_def mkC_def eval_nat_numeral)
  have em2: "dwe_emitted t2'
      = [(1, 0, ec1, e1)] @ map (\<lambda>(c, e). (2, 1, c, e)) B"
    using em2' by (simp add: PB2)
  have src2: "exec_src_hist (dwe_core t2') = [(ec1, e1), (ec2, e2)]"
    unfolding t2'_def redrive_result_def
    by (simp add: d2_w_def mkT_def mkC_def)
  have scope2: "exec_scope (dwe_core t2') = {0, 1}"
    unfolding t2'_def redrive_result_def
    by (simp add: d2_w_def mkT_def mkC_def)
  have pay1: "map e_payload (dwe_emitted t1') = [(ec1, e1), (ec2, e2)] @ B"
    by (simp add: em1)

  \<comment> \<open>THE TWO TOTAL CASES on the shared batch B: does it mention an
      already-delivered payload of the safe member, or not?\<close>
  have horn: "duplicate t1' \<or> lost_effect ec2 t2'"
  proof (cases "\<exists>p \<in> set B. p \<in> {(ec1, e1), (ec2, e2)}")
    case True
    \<comment> \<open>the batch re-fires a delivered payload: the safe side DUPLICATES\<close>
    have "\<not> distinct (map e_payload (dwe_emitted t1'))"
      unfolding pay1 using True by auto
    then have "duplicate t1'"
      by (simp add: duplicate_def)
    then show ?thesis ..
  next
    case False
    \<comment> \<open>the batch never re-covers the committed second effect --- whether
        it is empty (the kernel's loss case) or alien non-empty (the
        kernel's premature case), the skip side still OWES effect 2\<close>
    have inrep: "(ec2, e2) \<in> set (replay_down_hist
                    (exec_src_hist (dwe_core t2'))
                    (exec_scope (dwe_core t2')) ec2)"
      by (simp add: src2 scope2 replay_down_hist_def e1_def e2_def ec_defs
                    eval_nat_numeral)
    have notB: "(ec2, e2) \<notin> set B"
      using False by auto
    have notin: "(ec2, e2) \<notin> e_payload ` set (dwe_emitted t2')"
      using notB by (auto simp: em2 e1_def e2_def ec_defs)
    have "lost_effect ec2 t2'"
      unfolding lost_effect_def using inrep notin by blast
    then show ?thesis ..
  qed

  \<comment> \<open>both redrives heal every scoped mismatch at the frontier\<close>
  have heal1: "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k"
    by (rule policy_redrive_heals[OF pr1])
  have heal2: "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k"
    by (rule policy_redrive_heals[OF pr2])

  show ?thesis
    using pr1 pr2 heal1 heal2 horn by blast
qed

text \<open>The exists-pair/for-all-P two-horn form for the store-measured
  class, mirroring @{thm [source] recovery_information_dilemma_pair}:
  the ONE designed pair drives every store-measured policy into
  duplicate-or-lost.\<close>

theorem recovery_duplicate_or_lost_pair:
  "\<exists>t1 t2.
     dwe_reachable t1 \<and> dwe_reachable t2
   \<and> dwe_core t1 = dwe_core t2
   \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
   \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
   \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
   \<and> (\<forall>P. store_measured P \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (duplicate t1' \<or> lost_effect ec2 t2')))"
proof -
  have sm: "\<forall>P. store_measured P \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (duplicate t1' \<or> lost_effect ec2 t2'))"
  proof (intro allI impI)
    fix P :: redrive_policy
    assume "store_measured P"
    then obtain g where "\<forall>t. P t = g (dwe_core t)"
      unfolding store_measured_def by blast
    then have "P d1_w = P d2_w"
      using d_cores_eq by metis
    then show "\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (duplicate t1' \<or> lost_effect ec2 t2')"
      by (rule pair_batch_agreement_duplicate_or_lost)
  qed
  have all:
    "dwe_reachable d1_w \<and> dwe_reachable d2_w
   \<and> dwe_core d1_w = dwe_core d2_w
   \<and> dwe_emitted d1_w \<noteq> dwe_emitted d2_w
   \<and> \<not> effect_unsafe d1_w \<and> \<not> effect_unsafe d2_w
   \<and> genuinely_emitting d1_w \<and> genuinely_emitting d2_w
   \<and> (\<forall>P. store_measured P \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (duplicate t1' \<or> lost_effect ec2 t2')))"
    using reach_d1 reach_d2 d_cores_eq d_emitted_neq d1_not_unsafe
          d2_not_unsafe d1_emitting d2_emitting sm
    by blast
  then show ?thesis by blast
qed

text \<open>The same two-horn form for the (store, epoch)-measured class,
  mirroring @{thm [source] epoch_measured_dilemma_pair}.\<close>

theorem epoch_duplicate_or_lost_pair:
  "\<exists>t1 t2.
     dwe_reachable t1 \<and> dwe_reachable t2
   \<and> dwe_core t1 = dwe_core t2
   \<and> dwe_epoch t1 = dwe_epoch t2
   \<and> dwe_emitted t1 \<noteq> dwe_emitted t2
   \<and> \<not> effect_unsafe t1 \<and> \<not> effect_unsafe t2
   \<and> genuinely_emitting t1 \<and> genuinely_emitting t2
   \<and> (\<forall>P. store_epoch_measured P \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P t1 ec2 t1'
         \<and> policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (duplicate t1' \<or> lost_effect ec2 t2')))"
proof -
  have sem_all: "\<forall>P. store_epoch_measured P \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (duplicate t1' \<or> lost_effect ec2 t2'))"
  proof (intro allI impI)
    fix P :: redrive_policy
    assume "store_epoch_measured P"
    then obtain g where "\<forall>t. P t = g (dwe_core t) (dwe_epoch t)"
      unfolding store_epoch_measured_def by blast
    then have "P d1_w = P d2_w"
      using d_cores_eq d1_fields(5) d2_fields(5) by metis
    then show "\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (duplicate t1' \<or> lost_effect ec2 t2')"
      by (rule pair_batch_agreement_duplicate_or_lost)
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
   \<and> (\<forall>P. store_epoch_measured P \<longrightarrow>
        (\<exists>t1' t2'.
           policy_redrive P d1_w ec2 t1'
         \<and> policy_redrive P d2_w ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t2') ec2) ec2 k)
         \<and> (duplicate t1' \<or> lost_effect ec2 t2')))"
    using reach_d1 reach_d2 d_cores_eq epochs d_emitted_neq d1_not_unsafe
          d2_not_unsafe d1_emitting d2_emitting sem_all
    by blast
  then show ?thesis by blast
qed

section \<open>THEOREM B1: the sink-reading escape\<close>

text \<open>
  The payload-delta policy heals, never duplicates, never goes premature,
  and never loses --- at the redrive's own frontier, from EVERY effect-safe
  crashed state with a strictly ascending committed source.  New entries
  are fresh by the filter, justified by @{thm redrive_emissions_justified},
  and internally distinct by the ascending premise; old verdicts are
  frozen because the redrive leaves the committed prefix untouched.

  Stated PREMISE-FREE in the general form (the S1 audit found the pinned
  statement's reachability premise is never consumed: the redrive leaves
  the committed prefix untouched, so nothing about the escape depends on
  how the crashed state arose); the pinned, audited statement follows
  below by weakening.
\<close>

theorem sink_reading_escape_general:
  assumes safe: "\<not> effect_unsafe t"
      and crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and fin: "f \<le> exec_finish (dwe_core t)"
      and asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "(\<exists>t'. policy_redrive (sink_delta f) t f t')
       \<and> (\<forall>t'. policy_redrive (sink_delta f) t f t' \<longrightarrow>
            (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k)
          \<and> \<not> effect_unsafe t'
          \<and> \<not> lost_effect f t')"
proof (rule conjI)
  show "\<exists>t'. policy_redrive (sink_delta f) t f t'"
    using policy_redriveI[OF crashed fin] by blast
next
  show "\<forall>t'. policy_redrive (sink_delta f) t f t' \<longrightarrow>
          (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k)
        \<and> \<not> effect_unsafe t'
        \<and> \<not> lost_effect f t'"
  proof (intro allI impI)
    fix t'
    assume pr: "policy_redrive (sink_delta f) t f t'"
  \<comment> \<open>abbreviations for the state components\<close>
  define S where "S = exec_src_hist (dwe_core t)"
  define K where "K = exec_scope (dwe_core t)"
  define R where "R = replay_down_hist S K f"
  define D where "D = sink_delta f t"
  have D_eq: "D = filter (\<lambda>p. p \<notin> e_payload ` set (dwe_emitted t)) R"
    by (simp add: D_def sink_delta_def R_def S_def K_def)
  have em': "dwe_emitted t'
      = dwe_emitted t @ map (\<lambda>(c, e). (length S, dwe_epoch t, c, e)) D"
    using policy_redrive_emitted[OF pr] by (simp add: S_def D_def)
  have src': "exec_src_hist (dwe_core t') = S"
    using policy_redrive_src_same[OF pr] by (simp add: S_def)
  have scope': "exec_scope (dwe_core t') = K"
    using policy_redrive_scope_same[OF pr] by (simp add: K_def)

  \<comment> \<open>the two safety verdicts inherited from the pre-state\<close>
  have old_just: "\<forall>x \<in> set (dwe_emitted t). justified_at S x"
    using safe by (simp add: effect_unsafe_def premature_def S_def)
  have old_dist: "distinct (map e_payload (dwe_emitted t))"
    using safe by (simp add: effect_unsafe_def duplicate_def)

  \<comment> \<open>distinctness pipeline from the ascending premise\<close>
  have dist_S: "distinct S"
    using strictly_ascending_distinct[OF asc] by (simp add: S_def)
  have dist_R: "distinct R"
    unfolding R_def replay_down_hist_def using dist_S by simp
  have dist_D: "distinct D"
    unfolding D_eq using dist_R by simp

  \<comment> \<open>NOT premature: old entries frozen, new entries generically justified\<close>
  have "\<forall>x \<in> set (dwe_emitted t'). justified_at S x"
  proof
    fix x assume "x \<in> set (dwe_emitted t')"
    then consider (old) "x \<in> set (dwe_emitted t)"
      | (new) "x \<in> set (map (\<lambda>(c, e). (length S, dwe_epoch t, c, e)) D)"
      unfolding em' by auto
    then show "justified_at S x"
    proof cases
      case old
      then show ?thesis using old_just by blast
    next
      case new
      have "e_stamp x = length S" and "e_payload x \<in> set D"
        using stamped_elem[OF new] by simp_all
      then have "e_payload x \<in> set R"
        unfolding D_eq by auto
      then show ?thesis
        using redrive_emissions_justified \<open>e_stamp x = length S\<close>
        unfolding R_def by blast
    qed
  qed
  then have not_prem: "\<not> premature t'"
    unfolding premature_def src' by blast

  \<comment> \<open>NOT duplicate: old distinct, new distinct, disjoint by the filter\<close>
  have pay': "map e_payload (dwe_emitted t')
      = map e_payload (dwe_emitted t) @ D"
    by (simp add: em')
  have disj: "set D \<inter> set (map e_payload (dwe_emitted t)) = {}"
    unfolding D_eq by auto
  have "distinct (map e_payload (dwe_emitted t'))"
    unfolding pay' using old_dist dist_D disj by auto
  then have not_dup: "\<not> duplicate t'"
    by (simp add: duplicate_def)

  \<comment> \<open>NOT lost: every replay payload is an old payload or kept by the filter\<close>
  have img': "e_payload ` set (dwe_emitted t')
      = e_payload ` set (dwe_emitted t) \<union> set D"
    by (simp add: em' image_Un image_image)
  have no_loss: "\<not> lost_effect f t'"
    unfolding lost_effect_def src' scope'
  proof
    assume "\<exists>p \<in> set (replay_down_hist S K f).
              p \<notin> e_payload ` set (dwe_emitted t')"
    then obtain p where p_in: "p \<in> set R"
        and p_out: "p \<notin> e_payload ` set (dwe_emitted t')"
      unfolding R_def by blast
    have "p \<notin> e_payload ` set (dwe_emitted t)"
      using p_out img' by blast
    then have "p \<in> set D"
      unfolding D_eq using p_in by simp
    then show False using p_out img' by blast
  qed

    show "(\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k)
        \<and> \<not> effect_unsafe t' \<and> \<not> lost_effect f t'"
      using policy_redrive_heals[OF pr] not_prem not_dup no_loss
      by (auto simp: effect_unsafe_def)
  qed
qed

text \<open>The pinned, audited B1 statement, verbatim (a weakening of the
  general form; its reachability premise is deliberately unused).\<close>

theorem sink_reading_escape:
  assumes reach: "dwe_reachable t"
      and safe: "\<not> effect_unsafe t"
      and crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and fin: "f \<le> exec_finish (dwe_core t)"
      and asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "(\<exists>t'. policy_redrive (sink_delta f) t f t')
       \<and> (\<forall>t'. policy_redrive (sink_delta f) t f t' \<longrightarrow>
            (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k)
          \<and> \<not> effect_unsafe t'
          \<and> \<not> lost_effect f t')"
  by (rule sink_reading_escape_general[OF safe crashed fin asc])

text \<open>Non-vacuity: the escape's premises are inhabited by the dilemma's
  own loss-side witness, whose committed source is strictly ascending.\<close>

lemma d2_asc: "strictly_ascending_source (exec_src_hist (dwe_core d2_w))"
  by (simp add: strictly_ascending_source_def d2_w_def mkT_def mkC_def
                e1_def e2_def ec_defs)

corollary sink_escape_inhabited:
  "(\<exists>t'. policy_redrive (sink_delta ec2) d2_w ec2 t')
 \<and> (\<forall>t'. policy_redrive (sink_delta ec2) d2_w ec2 t' \<longrightarrow>
      (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') ec2) ec2 k)
    \<and> \<not> effect_unsafe t' \<and> \<not> lost_effect ec2 t')"
proof -
  have crashed: "\<exists>c. exec_status (dwe_core d2_w) = Crashed c"
    by (simp add: d2_fields)
  have fin: "ec2 \<le> exec_finish (dwe_core d2_w)"
    by (simp add: d2_fields)
  show ?thesis
    by (rule sink_reading_escape[OF reach_d2 d2_not_unsafe crashed fin d2_asc])
qed

section \<open>THEOREM B2: the escape is NOT store-measured\<close>

text \<open>
  On the dilemma's equal-core pair the delta evaluates to @{term "[]"} on
  the safe side and @{term "[(ec2, e2)]"} on the skip side --- so no
  function of the core computes it.  Reading the sink is exactly the
  information a store-measured policy lacks.
\<close>

theorem sink_reading_escape_not_store_measured:
  "\<not> store_measured (sink_delta ec2)"
proof
  assume "store_measured (sink_delta ec2)"
  then obtain g where g: "\<forall>t. sink_delta ec2 t = g (dwe_core t)"
    unfolding store_measured_def by blast
  have eval1: "sink_delta ec2 d1_w = []"
    by (simp add: sink_delta_def d1_w_def mkT_def mkC_def replay_down_hist_def
                  e1_def e2_def ec_defs)
  have eval2: "sink_delta ec2 d2_w = [(ec2, e2)]"
    by (simp add: sink_delta_def d2_w_def mkT_def mkC_def replay_down_hist_def
                  e1_def e2_def ec_defs)
  have "sink_delta ec2 d1_w = sink_delta ec2 d2_w"
    using g d_cores_eq by metis
  then show False
    by (simp add: eval1 eval2)
qed

end
