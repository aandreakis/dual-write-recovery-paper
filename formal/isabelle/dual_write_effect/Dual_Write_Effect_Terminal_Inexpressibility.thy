(*  Title:       Dual_Write_Effect_Terminal_Inexpressibility.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Terminal-inexpressibility of the dilemma pair (theory-backlog item A)
    --- an additive post-freeze slice under the freeze's own protocol: no
    landed statement, proof, definition, name, import, or session-DAG
    change to the frozen corpus.

    THIS THEORY LIVES ON THE TERMINAL (Design B) BRANCH.  It imports the
    landed Dual_Write_Effect_Witnesses alone, so everything below is about
    the terminal wrapper machine, whose emitting reconcile ends in the
    status Recovered and stays there.  The promoted operational machine
    (the cyclic branch) deliberately BREAKS the absorption property this
    theory turns on: its Resume rule exits Recovered and re-opens the
    crash/re-drive cycle --- see the cyclic branch's designed negative
    control recovered_not_absorbing_cyclic and its multi-crash
    amplification witness resume_cycle_amplification (prose-level
    cross-branch citations here and in the text blocks below; the
    freeze's namespace rule keeps the cyclic branch out of this import
    cone).

    WHAT IT CLOSES.  Owner decision D5 promoted the cyclic machine on the
    rationale that the operational recovery-information dilemma NEEDS the
    recovery cycle.  This theory makes the terminal half of that
    rationale machine-checked: on the terminal machine there is NO pair
    of reachable crashed states with equal cores and payload-divergent
    ledgers, at any machine parameters
    (terminal_no_payload_divergent_crashed_pair).  The dilemma's
    designed-in certificate shape --- an equal-core, divergent-ledger
    pair of crashed states, the shape the cyclic dilemma pair inhabits
    --- is therefore inexpressible at the states every recovery
    transition of the terminal machine fires from (status Crashed).  The
    reason is structural: the sole ledger/down-history divergence source,
    the emitting reconcile, ends Recovered; Recovered is absorbing ON
    THIS TERMINAL MACHINE (dwe_trace_recovered_stays,
    recovered_never_crashes_again); so the states that DO exhibit payload
    divergence (t_fin/t_safe-style) sit beyond every further
    crash/recovery transition.

    THE PAYLOAD-LEVEL QUALIFIER IS LOAD-BEARING.  Stamp-divergent,
    payload-EQUAL equal-core crashed pairs ARE reachable
    (crashed_stamp_divergence below), so "equal cores at Crashed implies
    equal ledgers" is FALSE on this machine; the honest negative is
    stated at the payload projection, and this theory says so wherever
    it states it.

    THE RECOVERY-RELEVANT CONSEQUENCE, stated carefully: at every
    reachable terminal-machine state whose status is Crashed, the
    ledger's payload projection literally equals exec_down_hist of the
    core (terminal_crashed_ledger_matches_down) --- a core field --- so
    the payload content a recovery decision could condition on at those
    states is core-determined.  That is a machine-checked equation about
    THIS machine's crashed states; it is not a policy-class theorem, and
    no claim about recovery-policy classes is made in this theory.

    PROVENANCE: statement-faithful port of the S1 shadow leg's Task 2 and
    nuance sections (paper/dual_write/phase3/scratch/s1_shadow/Shadow.thy,
    the machine-checked basis of D5's pricing), plus the new
    negative-existence packaging.  The shadow leg's Task 1 (the
    batch-hypothetical shadow dilemma) is deliberately NOT landed: the
    landed cyclic Dilemma theory carries the operational dilemma of
    record (its policy-measurability and loss definitions are the
    definitions of record), and the shadow's hypothetical batch extension
    is not a machine transition --- landing it would buy an honesty
    burden for no new paper claim.  Deltas against the banked source, all
    declared: the import is the landed sibling; Task 1 and the s6r
    evaluation lemmas that it alone consumed are dropped; the banked
    shadow_core_projections is renamed nuance_core_projections (the word
    "shadow" names the not-landed Task-1 artifact); the two
    negative-existence statements and their text blocks are new; section
    titles and text blocks are reworded for the terminal-scope fences
    with every ported statement unchanged.

    In-source ML oracle gates are STRIPPED at landing: oracle-freedom is
    certified by scratch-side per-slice gate sessions with
    confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Terminal_Inexpressibility
  imports Dual_Write_Effect_Witnesses
begin

section \<open>Scope: the terminal branch, and what this theory closes\<close>

text \<open>
  Everything in this theory is about the TERMINAL (Design B) machine of
  @{const dwe_step} / @{const emitting_reconcile}: the wrapper whose
  emitting reconcile ends in the status @{const Recovered} and has no rule
  out of it.  The promoted operational machine (the cyclic branch)
  deliberately breaks that absorption with its Resume rule --- its own
  designed negative control @{text recovered_not_absorbing_cyclic} and the
  amplification witness @{text resume_cycle_amplification} certify the
  break (prose-level cross-branch citations: the freeze's namespace rule
  keeps the cyclic branch out of this import cone).  So the absorption
  facts below are terminal-scoped by construction, and every statement
  here should be read with that scope attached.

  What the theory adds to the frozen corpus: owner decision D5's rationale
  --- the operational recovery-information dilemma NEEDS the recovery
  cycle --- becomes a theorem about the terminal machine.  The dilemma's
  certificate shape needs a pair of reachable crashed states with equal
  cores and payload-divergent ledgers; the headline below proves the
  terminal machine has no such pair, at any machine parameters.  The
  nuance witness (@{text crashed_stamp_divergence}, proved at the end)
  keeps the claim honest: stamp-divergent, payload-equal pairs ARE
  reachable, so the negative is stated at the payload projection and
  would be FALSE one level finer.
\<close>

section \<open>The terminal operational limitation, machine-checked\<close>

text \<open>
  Why the OPERATIONAL dilemma cannot exist on the terminal machine: the
  sole ledger/down-history divergence source is the emitting reconcile,
  which ends @{const Recovered}; on this terminal machine
  @{const Recovered} is absorbing (every @{const dw_exec_step} rule except
  @{text Observe} requires @{const Running} or @{const Crashed} status,
  and @{text Observe} is the identity); a crash requires @{const Running}.
  Hence every state the machine can ever be CRASHED in --- i.e. every
  state at which a recovery transition of this machine fires --- has its
  ledger payload projection literally equal to the durable downstream
  history, which IS a core field.  The payload content a recovery decision
  could condition on at those states is therefore core-determined: a
  machine-checked equation about this machine's crashed states, not a
  policy-class statement.
\<close>

definition ledger_matches_down :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "ledger_matches_down t \<longleftrightarrow>
     map e_payload (dwe_emitted t) = exec_down_hist (dwe_core t)"

definition pre_recovery_sync :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "pre_recovery_sync t \<longleftrightarrow>
     (exec_status (dwe_core t) \<noteq> Recovered \<longrightarrow> ledger_matches_down t)"

subsection \<open>Recovered is absorbing on the terminal machine (checked against every dw\_exec\_step rule)\<close>

text \<open>
  The core-level absorption statement below coincides with the cyclic
  branch's @{text recovered_stays_recovered} (both speak about the shared
  landed @{const dw_exec_step}); that theory sits outside this import cone
  by the freeze's namespace rule, so the fact is proved directly here ---
  the same forced-duplication pattern the Decider theory discloses for its
  trace-persistence lemma.  The wrapper-level and trace-level forms are
  terminal-specific: the cyclic machine falsifies the trace-level form by
  design (@{text recovered_not_absorbing_cyclic}).
\<close>

lemma dw_exec_step_recovered_stays:
  assumes "dw_exec_step s a s'"
      and "exec_status s = Recovered"
  shows "exec_status s' = Recovered"
  using assms by (cases rule: dw_exec_step.cases) auto

lemma dw_exec_step_status_nonrecovered:
  assumes "dw_exec_step s a s'"
      and "exec_status s' \<noteq> Recovered"
  shows "exec_status s \<noteq> Recovered"
  using assms dw_exec_step_recovered_stays by blast

lemma dwe_step_recovered_stays:
  assumes "dwe_step t a t'"
      and "exec_status (dwe_core t) = Recovered"
  shows "exec_status (dwe_core t') = Recovered"
  using dw_exec_step_recovered_stays[OF dwe_step_core[OF assms(1)] assms(2)] .

lemma no_reconcile_from_recovered:
  assumes "exec_status (dwe_core t) = Recovered"
  shows "\<not> emitting_reconcile m t f t'"
  using assms by (auto simp: emitting_reconcile_def)

lemma emitting_reconcile_status_recovered:
  assumes "emitting_reconcile m t f t'"
  shows "exec_status (dwe_core t') = Recovered"
  using assms by (auto simp: emitting_reconcile_def)

theorem dwe_trace_recovered_stays:
  assumes "dwe_temporal_trace t acts t'"
      and "exec_status (dwe_core t) = Recovered"
  shows "exec_status (dwe_core t') = Recovered"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_temporal_refl t)
  then show ?case .
next
  case (dwe_temporal_label_step t a t' as t'')
  have "exec_status (dwe_core t') = Recovered"
    by (rule dwe_step_recovered_stays
        [OF dwe_temporal_label_step.hyps(1) dwe_temporal_label_step.prems])
  then show ?case by (rule dwe_temporal_label_step.IH)
next
  case (dwe_temporal_reconcile_step m t f t' as t'')
  have False
    using no_reconcile_from_recovered
          [OF dwe_temporal_reconcile_step.prems]
          dwe_temporal_reconcile_step.hyps(1)
    by blast
  then show ?case ..
qed

corollary recovered_never_crashes_again:
  assumes "dwe_temporal_trace t acts t'"
      and "exec_status (dwe_core t) = Recovered"
  shows "\<nexists>c. exec_status (dwe_core t') = Crashed c"
  using dwe_trace_recovered_stays[OF assms] by simp

subsection \<open>The pre-recovery sync invariant\<close>

lemma down_hist_of_labels_nonpub:
  assumes "\<forall>c e. a \<noteq> DoDownstream c e"
  shows "down_hist_of_labels [a] = []"
  using assms by (cases a) simp_all

text \<open>Shape lemma: robust elimination for @{const dwe_step} without
  positional case-hypothesis references.\<close>

lemma dwe_step_shape:
  assumes "dwe_step t a t'"
  shows "(dw_exec_step (dwe_core t) a (dwe_core t')
          \<and> (\<forall>c e. a \<noteq> DoDownstream c e)
          \<and> dwe_emitted t' = dwe_emitted t)
       \<or> (\<exists>c e. a = DoDownstream c e
          \<and> dw_exec_step (dwe_core t) a (dwe_core t')
          \<and> dwe_emitted t' = dwe_emitted t
              @ [(length (exec_src_hist (dwe_core t)), c, e)])"
  using assms by (cases rule: dwe_step.cases) auto

lemma dwe_step_pre_recovery_sync:
  assumes step: "dwe_step t a t'"
      and inv: "pre_recovery_sync t"
  shows "pre_recovery_sync t'"
proof (cases "exec_status (dwe_core t') = Recovered")
  case True
  then show ?thesis by (simp add: pre_recovery_sync_def)
next
  case False
  have core_step: "dw_exec_step (dwe_core t) a (dwe_core t')"
    by (rule dwe_step_core[OF step])
  have pre_nonrec: "exec_status (dwe_core t) \<noteq> Recovered"
    by (rule dw_exec_step_status_nonrecovered[OF core_step False])
  with inv have pre_eq:
    "map e_payload (dwe_emitted t) = exec_down_hist (dwe_core t)"
    by (simp add: pre_recovery_sync_def ledger_matches_down_def)
  from dwe_step_shape[OF step] show ?thesis
  proof
    assume nonpub:
      "dw_exec_step (dwe_core t) a (dwe_core t')
       \<and> (\<forall>c e. a \<noteq> DoDownstream c e)
       \<and> dwe_emitted t' = dwe_emitted t"
    have down_eq: "exec_down_hist (dwe_core t') = exec_down_hist (dwe_core t)"
      using dw_exec_step_down_hist[OF core_step]
            down_hist_of_labels_nonpub nonpub
      by auto
    show ?thesis
      using nonpub
      by (simp add: pre_recovery_sync_def ledger_matches_down_def
                    down_eq pre_eq)
  next
    assume "\<exists>c e. a = DoDownstream c e
            \<and> dw_exec_step (dwe_core t) a (dwe_core t')
            \<and> dwe_emitted t' = dwe_emitted t
                @ [(length (exec_src_hist (dwe_core t)), c, e)]"
    then obtain c e where a_eq: "a = DoDownstream c e"
        and emit_eq: "dwe_emitted t' = dwe_emitted t
                        @ [(length (exec_src_hist (dwe_core t)), c, e)]"
      by blast
    have down_eq:
      "exec_down_hist (dwe_core t') = exec_down_hist (dwe_core t) @ [(c, e)]"
      using dw_exec_step_down_hist[OF core_step] a_eq by simp
    show ?thesis
      by (simp add: pre_recovery_sync_def ledger_matches_down_def
                    emit_eq down_eq pre_eq)
  qed
qed

lemma dwe_temporal_trace_pre_recovery_sync:
  assumes trace: "dwe_temporal_trace t acts t'"
      and inv: "pre_recovery_sync t"
  shows "pre_recovery_sync t'"
  using trace inv
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_temporal_refl t)
  then show ?case .
next
  case (dwe_temporal_label_step t a t' as t'')
  have "pre_recovery_sync t'"
    by (rule dwe_step_pre_recovery_sync
        [OF dwe_temporal_label_step.hyps(1) dwe_temporal_label_step.prems])
  then show ?case by (rule dwe_temporal_label_step.IH)
next
  case (dwe_temporal_reconcile_step m t f t' as t'')
  have "pre_recovery_sync t'"
    using emitting_reconcile_status_recovered
          [OF dwe_temporal_reconcile_step.hyps(1)]
    by (simp add: pre_recovery_sync_def)
  then show ?case by (rule dwe_temporal_reconcile_step.IH)
qed

lemma pre_recovery_sync_init: "pre_recovery_sync (dwe_init b K fin)"
  by (simp add: pre_recovery_sync_def ledger_matches_down_def dwe_init_def
                initial_exec_state_def)

theorem terminal_crashed_ledger_matches_down:
  assumes reach: "dwe_reachable b K fin t"
      and crashed: "exec_status (dwe_core t) = Crashed c"
  shows "map e_payload (dwe_emitted t) = exec_down_hist (dwe_core t)"
proof -
  from reach obtain acts
    where "dwe_temporal_trace (dwe_init b K fin) acts t"
    by (auto simp: dwe_reachable_def)
  from dwe_temporal_trace_pre_recovery_sync[OF this pre_recovery_sync_init]
  have "pre_recovery_sync t" .
  with crashed show ?thesis
    by (simp add: pre_recovery_sync_def ledger_matches_down_def)
qed

theorem terminal_crashed_equal_core_ledger_payload_equal:
  assumes "dwe_reachable b K fin t"
      and "dwe_reachable b' K' fin' t'"
      and "exec_status (dwe_core t) = Crashed c"
      and "exec_status (dwe_core t') = Crashed c'"
      and "dwe_core t = dwe_core t'"
  shows "map e_payload (dwe_emitted t) = map e_payload (dwe_emitted t')"
  using terminal_crashed_ledger_matches_down[OF assms(1) assms(3)]
        terminal_crashed_ledger_matches_down[OF assms(2) assms(4)]
        assms(5)
  by simp

section \<open>HEADLINE: no payload-divergent equal-core crashed pair, at any parameters\<close>

text \<open>
  The negative-existence packaging of the two theorems above --- the form
  the paper cites for owner decision D5's rationale: the terminal machine
  has NO pair of reachable crashed states with equal cores and
  payload-divergent ledgers, at any machine parameters (the two sides may
  even be reached at DIFFERENT parameters @{term "(b, K, fin)"} and
  @{term "(b', K', fin')"}, matching the cross-parameter strength of
  @{thm [source] terminal_crashed_equal_core_ledger_payload_equal}).  The
  statement is deliberately conjunct-free inside the negation: adding
  conjuncts such as effect safety or genuine emission would WEAKEN a
  no-existence claim, so the bare form is the strongest honest reading.
  A conjunct-bearing echo of the cyclic dilemma pair's certificate shape
  follows it as a disclosed weakening, restated for citation symmetry.

  Scope, said plainly: this is a theorem about the TERMINAL machine's
  crashed states.  The payload-level qualifier is load-bearing --- the
  nuance section below exhibits reachable stamp-divergent, payload-equal
  equal-core crashed pairs, so an entry-level (stamp-inclusive) version
  of this negative would be FALSE.
\<close>

theorem terminal_no_payload_divergent_crashed_pair:
  "\<not> (\<exists>(t :: ('k, 'v) dwe_state) t' b K fin b' K' fin' c c'.
        dwe_reachable b K fin t
      \<and> dwe_reachable b' K' fin' t'
      \<and> exec_status (dwe_core t) = Crashed c
      \<and> exec_status (dwe_core t') = Crashed c'
      \<and> dwe_core t = dwe_core t'
      \<and> map e_payload (dwe_emitted t) \<noteq> map e_payload (dwe_emitted t'))"
proof
  assume "\<exists>(t :: ('k, 'v) dwe_state) t' b K fin b' K' fin' c c'.
            dwe_reachable b K fin t
          \<and> dwe_reachable b' K' fin' t'
          \<and> exec_status (dwe_core t) = Crashed c
          \<and> exec_status (dwe_core t') = Crashed c'
          \<and> dwe_core t = dwe_core t'
          \<and> map e_payload (dwe_emitted t) \<noteq> map e_payload (dwe_emitted t')"
  then obtain t t' b K fin b' K' fin' c c'
    where reach: "dwe_reachable b K fin (t :: ('k, 'v) dwe_state)"
      and reach': "dwe_reachable b' K' fin' t'"
      and crashed: "exec_status (dwe_core t) = Crashed c"
      and crashed': "exec_status (dwe_core t') = Crashed c'"
      and cores: "dwe_core t = dwe_core t'"
      and diverge: "map e_payload (dwe_emitted t) \<noteq> map e_payload (dwe_emitted t')"
    by blast
  from terminal_crashed_equal_core_ledger_payload_equal
         [OF reach reach' crashed crashed' cores]
  have "map e_payload (dwe_emitted t) = map e_payload (dwe_emitted t')" .
  with diverge show False ..
qed

text \<open>
  The certificate-shape echo, DISCLOSED AS A WEAKENING restated for
  citation symmetry with the cyclic pair: requiring in addition that both
  members be effect-safe and genuinely emitting --- the conjuncts the
  cyclic dilemma pair's certificate carries (its
  @{text batch_agreement_dilemma} pair is reachable, effect-safe,
  genuinely emitting, equal-core, equal-epoch, divergent-ledger) --- is a
  fortiori impossible.  Adding hypotheses inside a negated existential
  makes the claim strictly weaker than the headline above; this corollary
  exists so the paper can cite the terminal negative in the cyclic
  certificate's own shape.
\<close>

corollary terminal_no_dilemma_shaped_crashed_pair:
  "\<not> (\<exists>(t :: ('k, 'v) dwe_state) t' b K fin b' K' fin' c c'.
        dwe_reachable b K fin t
      \<and> dwe_reachable b' K' fin' t'
      \<and> exec_status (dwe_core t) = Crashed c
      \<and> exec_status (dwe_core t') = Crashed c'
      \<and> dwe_core t = dwe_core t'
      \<and> map e_payload (dwe_emitted t) \<noteq> map e_payload (dwe_emitted t')
      \<and> \<not> effect_unsafe t \<and> \<not> effect_unsafe t'
      \<and> genuinely_emitting t \<and> genuinely_emitting t')"
proof
  assume "\<exists>(t :: ('k, 'v) dwe_state) t' b K fin b' K' fin' c c'.
            dwe_reachable b K fin t
          \<and> dwe_reachable b' K' fin' t'
          \<and> exec_status (dwe_core t) = Crashed c
          \<and> exec_status (dwe_core t') = Crashed c'
          \<and> dwe_core t = dwe_core t'
          \<and> map e_payload (dwe_emitted t) \<noteq> map e_payload (dwe_emitted t')
          \<and> \<not> effect_unsafe t \<and> \<not> effect_unsafe t'
          \<and> genuinely_emitting t \<and> genuinely_emitting t'"
  then obtain t t' b K fin b' K' fin' c c'
    where reach: "dwe_reachable b K fin (t :: ('k, 'v) dwe_state)"
      and reach': "dwe_reachable b' K' fin' t'"
      and crashed: "exec_status (dwe_core t) = Crashed c"
      and crashed': "exec_status (dwe_core t') = Crashed c'"
      and cores: "dwe_core t = dwe_core t'"
      and diverge: "map e_payload (dwe_emitted t) \<noteq> map e_payload (dwe_emitted t')"
    by blast
  from terminal_crashed_equal_core_ledger_payload_equal
         [OF reach reach' crashed crashed' cores]
  have "map e_payload (dwe_emitted t) = map e_payload (dwe_emitted t')" .
  with diverge show False ..
qed

section \<open>NUANCE: stamp-divergent, payload-equal crashed equal-core pairs are reachable\<close>

text \<open>
  The invariant is PAYLOAD-level, and that is tight: delivering the e1
  write BEFORE vs AFTER the second source commit yields two reachable
  Crashed states with literally equal cores whose ledgers differ in the
  STAMP ((1, ec1, ev1) vs (2, ec1, ev1)) while their payload projections
  agree.  So "equal cores at Crashed \<open>\<Longrightarrow>\<close> equal ledgers" is FALSE on this
  machine; what is core-determined at crashed states is the payload
  projection, and the headline negative is stated at exactly that level.
  This does NOT re-open an operational terminal dilemma: the effect-hazard
  taxonomy is itself payload-level (@{const duplicate} reads the payload
  multiset; @{const premature} judges a payload against the committed
  prefix at its stamp; the loss the cyclic dilemma prices is the absence
  of a committed payload from the ledger), so a stamp difference with
  agreeing payloads separates none of them.  Both witnesses are
  effect-safe, so neither side is already condemned.  This pair is a
  designed disclosure: without it the headline would read stronger than
  it is.
\<close>

definition sA :: "(nat, nat) dw_exec_state" where
  "sA = s4\<lparr>exec_status := Crashed ec2\<rparr>"

definition z3 :: "(nat, nat) dw_exec_state" where
  "z3 = s2\<lparr>exec_src_hist := exec_src_hist s2 @ [(ec2, ev2)]\<rparr>"

definition z4 :: "(nat, nat) dw_exec_state" where
  "z4 = z3\<lparr>exec_down_hist := exec_down_hist z3 @ [(ec1, ev1)],
           exec_pending := exec_pending z3 - {(ec1, ev1)}\<rparr>"

definition sB :: "(nat, nat) dw_exec_state" where
  "sB = z4\<lparr>exec_status := Crashed ec2\<rparr>"

definition tA :: "(nat, nat) dwe_state" where
  "tA = \<lparr>dwe_core = sA, dwe_emitted = [(1, ec1, ev1)]\<rparr>"

definition tz3 :: "(nat, nat) dwe_state" where
  "tz3 = \<lparr>dwe_core = z3, dwe_emitted = []\<rparr>"

definition tz4 :: "(nat, nat) dwe_state" where
  "tz4 = \<lparr>dwe_core = z4, dwe_emitted = [(2, ec1, ev1)]\<rparr>"

definition tB :: "(nat, nat) dwe_state" where
  "tB = \<lparr>dwe_core = sB, dwe_emitted = [(2, ec1, ev1)]\<rparr>"

lemma nuance_core_projections [simp]:
  "dwe_core tA = sA" "dwe_core tz3 = z3" "dwe_core tz4 = z4" "dwe_core tB = sB"
  by (simp_all add: tA_def tz3_def tz4_def tB_def)

subsection \<open>Path A: deliver e1, THEN commit e2, then crash\<close>

lemma stA: "dw_exec_step s4 (Crash ec2) sA"
  unfolding sA_def
  by (rule dw_exec_step.crash)
     (simp add: s4_def s3_def s2_def s1_def s0_def initial_exec_state_def)

lemma pres_s4_crash2: "exec_label_preserves_history_wf s4 (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma dstA: "dwe_step t4 (Crash ec2) tA"
proof (rule dwe_step_lift_nonpubI)
  show "dw_exec_step (dwe_core t4) (Crash ec2) sA"
    using stA by simp
  show "\<forall>c e. Crash ec2 \<noteq> DoDownstream c e" by simp
  show "tA = \<lparr>dwe_core = sA, dwe_emitted = dwe_emitted t4\<rparr>"
    by (simp add: tA_def t4_def)
qed

lemma sgA: "dwe_temporal_trace t4 [DWE_Label (Crash ec2)] tA"
  by (rule dwe_temporal_singleI[OF dstA]) (simp_all add: wf_s4 pres_s4_crash2)

lemma trace_t0_t4:
  "dwe_temporal_trace t0
     (map DWE_Label
        [DoSource ec1 ev1, EnqueueDownstream ec1 ev1, DoDownstream ec1 ev1,
         DoSource ec2 ev2])
     t4"
  using dwe_temporal_trace_append[OF trace_t0_t3 sg34] by simp

lemma reach_tA: "dwe_reachable Map.empty {0, 1} ec2 tA"
  by (rule dwe_reachable_trace_extend
      [OF dwe_reachable_trace_extend[OF reach_t0 trace_t0_t4] sgA])

subsection \<open>Path B: commit e2 BEFORE delivering e1 (stamp 2), then crash\<close>

lemma stz23: "dw_exec_step s2 (DoSource ec2 ev2) z3"
  unfolding z3_def
  by (rule dw_exec_step.do_source)
     (simp add: s2_def s1_def s0_def initial_exec_state_def)

lemma stz34: "dw_exec_step z3 (DoDownstream ec1 ev1) z4"
  unfolding z4_def
  by (rule dw_exec_step.do_downstream)
     (simp_all add: z3_def s2_def s1_def s0_def initial_exec_state_def)

lemma stz45: "dw_exec_step z4 (Crash ec2) sB"
  unfolding sB_def
  by (rule dw_exec_step.crash)
     (simp add: z4_def z3_def s2_def s1_def s0_def initial_exec_state_def)

lemma pres_s2_do2: "exec_label_preserves_history_wf s2 (DoSource ec2 ev2)"
  by (simp add: exec_label_preserves_history_wf_def history_can_append_def
                s2_def s1_def s0_def initial_exec_state_def ec_defs)

lemma wf_z3: "wellformed_exec_state z3"
  by (rule dw_exec_step_wellformed_exec_state[OF stz23 wf_s2 pres_s2_do2])

lemma pres_z3_down1: "exec_label_preserves_history_wf z3 (DoDownstream ec1 ev1)"
  by (simp add: exec_label_preserves_history_wf_def history_can_append_def
                z3_def s2_def s1_def s0_def initial_exec_state_def ec_defs)

lemma wf_z4: "wellformed_exec_state z4"
  by (rule dw_exec_step_wellformed_exec_state[OF stz34 wf_z3 pres_z3_down1])

lemma pres_z4_crash2: "exec_label_preserves_history_wf z4 (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma dstz2: "dwe_step t2 (DoSource ec2 ev2) tz3"
proof (rule dwe_step_lift_nonpubI)
  show "dw_exec_step (dwe_core t2) (DoSource ec2 ev2) z3"
    using stz23 by simp
  show "\<forall>c e. DoSource ec2 ev2 \<noteq> DoDownstream c e" by simp
  show "tz3 = \<lparr>dwe_core = z3, dwe_emitted = dwe_emitted t2\<rparr>"
    by (simp add: tz3_def t2_def)
qed

lemma dstz3: "dwe_step tz3 (DoDownstream ec1 ev1) tz4"
proof (rule dwe_step_publishI)
  show "dw_exec_step (dwe_core tz3) (DoDownstream ec1 ev1) z4"
    using stz34 by simp
  show "tz4 = \<lparr>dwe_core = z4,
               dwe_emitted = dwe_emitted tz3
                 @ [(length (exec_src_hist (dwe_core tz3)), ec1, ev1)]\<rparr>"
    by (simp add: tz4_def tz3_def z3_def s2_def s1_def s0_def
                  initial_exec_state_def)
qed

lemma dstz4: "dwe_step tz4 (Crash ec2) tB"
proof (rule dwe_step_lift_nonpubI)
  show "dw_exec_step (dwe_core tz4) (Crash ec2) sB"
    using stz45 by simp
  show "\<forall>c e. Crash ec2 \<noteq> DoDownstream c e" by simp
  show "tB = \<lparr>dwe_core = sB, dwe_emitted = dwe_emitted tz4\<rparr>"
    by (simp add: tB_def tz4_def)
qed

lemma sgz2: "dwe_temporal_trace t2 [DWE_Label (DoSource ec2 ev2)] tz3"
  by (rule dwe_temporal_singleI[OF dstz2]) (simp_all add: wf_s2 pres_s2_do2)

lemma sgz3: "dwe_temporal_trace tz3 [DWE_Label (DoDownstream ec1 ev1)] tz4"
  by (rule dwe_temporal_singleI[OF dstz3]) (simp_all add: wf_z3 pres_z3_down1)

lemma sgz4: "dwe_temporal_trace tz4 [DWE_Label (Crash ec2)] tB"
  by (rule dwe_temporal_singleI[OF dstz4]) (simp_all add: wf_z4 pres_z4_crash2)

lemma trace_t0_tB:
  "dwe_temporal_trace t0
     (map DWE_Label
        [DoSource ec1 ev1, EnqueueDownstream ec1 ev1, DoSource ec2 ev2,
         DoDownstream ec1 ev1, Crash ec2])
     tB"
  using dwe_temporal_trace_append
          [OF sg01 dwe_temporal_trace_append
                     [OF sg12 dwe_temporal_trace_append
                                [OF sgz2 dwe_temporal_trace_append
                                           [OF sgz3 sgz4]]]]
  by simp

lemma reach_tB: "dwe_reachable Map.empty {0, 1} ec2 tB"
  by (rule dwe_reachable_trace_extend[OF reach_t0 trace_t0_tB])

subsection \<open>The stamp-divergence facts\<close>

lemma cores_equal_stamp_pair: "dwe_core tA = dwe_core tB"
  by (simp add: tA_def tB_def sA_def sB_def z4_def z3_def s4_def s3_def
                s2_def s1_def s0_def initial_exec_state_def)

lemma crashed_tA: "exec_status (dwe_core tA) = Crashed ec2"
  by (simp add: sA_def)

lemma crashed_tB: "exec_status (dwe_core tB) = Crashed ec2"
  by (simp add: sB_def z4_def z3_def s2_def s1_def s0_def
                initial_exec_state_def)

lemma ledgers_stamp_divergent: "dwe_emitted tA \<noteq> dwe_emitted tB"
  by (simp add: tA_def tB_def)

lemma payloads_equal_stamp_pair:
  "map e_payload (dwe_emitted tA) = map e_payload (dwe_emitted tB)"
  by (simp add: tA_def tB_def)

lemma safe_tA: "\<not> effect_unsafe tA"
  by (simp add: effect_unsafe_def premature_def duplicate_def justified_at_def
                tA_def sA_def s4_def s3_def s2_def s1_def s0_def
                initial_exec_state_def eval_arith)

lemma safe_tB: "\<not> effect_unsafe tB"
  by (simp add: effect_unsafe_def premature_def duplicate_def justified_at_def
                tB_def sB_def z4_def z3_def s2_def s1_def s0_def
                initial_exec_state_def eval_arith)

theorem crashed_stamp_divergence:
  "dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 tA
 \<and> dwe_reachable (Map.empty :: nat \<rightharpoonup> nat) {0, 1} ec2 tB
 \<and> exec_status (dwe_core tA) = Crashed ec2
 \<and> exec_status (dwe_core tB) = Crashed ec2
 \<and> dwe_core tA = dwe_core tB
 \<and> dwe_emitted tA \<noteq> dwe_emitted tB
 \<and> map e_payload (dwe_emitted tA) = map e_payload (dwe_emitted tB)
 \<and> \<not> effect_unsafe tA \<and> \<not> effect_unsafe tB"
  using reach_tA reach_tB crashed_tA crashed_tB cores_equal_stamp_pair
        ledgers_stamp_divergent payloads_equal_stamp_pair safe_tA safe_tB
  by blast

end
