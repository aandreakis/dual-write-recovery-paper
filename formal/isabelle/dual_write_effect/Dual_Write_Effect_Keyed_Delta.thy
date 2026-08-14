(*  Title:       Dual_Write_Effect_Keyed_Delta.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE COORDINATE-KEYED DELTA (theory-roadmap Wave 2, slice W2d;
    gap-hunt register rank 13): keyed dedup equals payload dedup under
    the named ascending premise --- the machine-checked "derive the key
    once / stable key" anchor.

    PROVENANCE: THEORY_IMPROVEMENT_ROADMAP.md Wave 2 +
    paper/dual_write/prose_phase/framing_exploration/gap_hunt_2026-07-07/
    GAP_HUNT_FLEET_CAPTURE.md section A2, "Coordinate-keyed delta lemma"
    (register rank 13; solo hunter: near-definitional).  An additive
    slice on the LANDED cyclic machine: no landed statement, proof,
    definition, name, import, or session-DAG change to the frozen
    corpus; imports are the plain cyclic-lane siblings Dilemma (the
    escape and its vocabulary) and Discipline (the landed
    equal-coordinate aliasing chain).

    CONTENT.  Practitioners dedup re-drives by a KEY derived from the
    record's stable source coordinate (LSN / offset / event id), not by
    comparing whole payloads.  This theory locates that rule exactly:

    (i)   keyed_delta --- the coordinate-keyed variant of the landed
          sink-reading escape's batch: filter the scoped,
          frontier-bounded replay against the DELIVERED COORDINATES
          (fst of the ledger payloads) instead of the delivered
          payloads.  Premise-free structure: the keyed delta is a
          sub-filter of the landed sink_delta --- keying can only drop
          MORE, never re-fire more, so its failure mode is pure loss.

    (ii)  THE EQUIVALENCE (rank-13 payload): under
          strictly_ascending_source on the state's committed source
          history, PLUS the ledger-membership premise that every
          delivered payload lies in that history (literally the negation
          of the landed phantom hazard), the keyed delta EQUALS the
          payload delta.  Each premise is needed and witnessed
          load-bearing at a reachable control state; the membership
          premise is discharged by the escape's own effect-safe premise
          (phantom_imp_premature), so the keyed policy inherits the
          landed B1 escape verbatim under EXACTLY the landed premises
          (keyed_reading_escape), and is provably not store-measured.

    (iii) THE ALIASING CONTROL: the machine itself reaches (WF-H1 is
          non-strict) a crashed state whose source carries TWO DISTINCT
          committed payloads at ONE coordinate, the first delivered.
          There the two deltas differ and the keyed one is WRONG: its
          own redrive drops the genuinely distinct committed second
          payload and ends in the landed loss verdict, while the payload
          delta re-drives it, loses nothing, and stays effect-safe.
          The LANDED equal-payload aliasing witness (dd4_w) is imported
          and shown NOT to separate the two deltas --- equal-payload
          aliasing starves both equally --- which is exactly why this
          control state (distinct events, one coordinate) is the minimal
          separating witness.

    (iv)  THE MEMBERSHIP CONTROL: a reachable state with a strictly
          ascending source but a phantom delivery sharing a committed
          coordinate, where the keyed delta again starves a committed
          payload --- the second premise bites independently of the
          first.

    This theory contains no ML and no oracle-bearing commands;
    oracle-freedom is re-certified at the wave's landing gate
    (per-slice theorem-dependency checks with confirmed-biting negative
    controls), kept outside the landed sources.
*)

theory Dual_Write_Effect_Keyed_Delta
  imports Dual_Write_Effect_Dilemma Dual_Write_Effect_Discipline
begin

section \<open>The coordinate-keyed delta and its premise-free structure\<close>

text \<open>
  The delivered-coordinate set: the first components (source
  coordinates) of the payloads already in the emission ledger --- the
  set of KEYS the sink has seen.  The coordinate-keyed delta is the
  landed @{const sink_delta} with ONE change: the filter tests the
  replay entry's COORDINATE against this set instead of testing the
  whole payload against the delivered-payload set.  Pinned at the
  witness instantiation @{typ "(nat, nat) dwe_state"} exactly as
  @{const sink_delta} is, so @{term "keyed_delta f"} is a
  @{typ redrive_policy} and every landed policy fact applies to it.
\<close>

definition delivered_coords :: "('k, 'v) dwe_state \<Rightarrow> src_coord set" where
  "delivered_coords t = fst ` e_payload ` set (dwe_emitted t)"

definition keyed_delta
  :: "frontier \<Rightarrow> (nat, nat) dwe_state \<Rightarrow>
      (src_coord \<times> (nat, nat) source_event) list"
where
  "keyed_delta f t =
     filter (\<lambda>p. fst p \<notin> delivered_coords t)
       (replay_down_hist (exec_src_hist (dwe_core t))
          (exec_scope (dwe_core t)) f)"

text \<open>
  Premise-free structure: a delivered PAYLOAD always contributes its
  coordinate, so passing the keyed filter is at least as hard as
  passing the payload filter --- the keyed delta is a SUB-FILTER of the
  landed @{const sink_delta}.  Keying can only drop more entries than
  payload dedup, never fewer: relative to the landed escape the keyed
  policy's failure mode is pure LOSS, never extra re-fires.
\<close>

lemma keyed_delta_subfilter:
  "keyed_delta f t
     = filter (\<lambda>p. fst p \<notin> delivered_coords t) (sink_delta f t)"
  unfolding keyed_delta_def sink_delta_def filter_filter
  by (rule filter_cong[OF refl]) (auto simp: delivered_coords_def)

corollary keyed_delta_subset:
  "set (keyed_delta f t) \<subseteq> set (sink_delta f t)"
  unfolding keyed_delta_subfilter by auto

section \<open>Coordinate uniqueness under the ascending premise\<close>

text \<open>
  The landed premise @{const strictly_ascending_source} (coordinates
  strictly increase along the committed history) makes the coordinate a
  FAITHFUL key on the source history: among committed entries, equal
  coordinates force equal payloads.  This is the exact content behind
  the practitioner's "the key is stable and unique"; the landed
  @{thm [source] strictly_ascending_distinct} is the payload-level
  shadow of this fact.
\<close>

lemma strictly_ascending_coord_determines:
  assumes "strictly_ascending_source H"
      and "p \<in> set H" and "q \<in> set H" and "fst p = fst q"
  shows "p = q"
  using assms unfolding strictly_ascending_source_def
  by (induction H) auto

section \<open>THE KEYED-DELTA EQUIVALENCE (register rank 13)\<close>

text \<open>
  THE EQUIVALENCE.  Two premises, each with a pinned role and each
  witnessed load-bearing at a reachable control state below:

  \<^item> @{const strictly_ascending_source} on the state's committed source
    history: the coordinate determines the payload among COMMITTED
    entries (the lemma above).  Without it, one delivered coordinate
    can alias two genuinely distinct committed payloads, and the keyed
    filter blocks both --- the aliasing control below.

  \<^item> LEDGER MEMBERSHIP: every delivered payload lies in the committed
    source history --- literally the negation of the landed
    @{const phantom} hazard.  The equivalence compares a replay entry
    (always committed: the replay is a filter of the source history)
    against LEDGER entries; the ascending premise only speaks about the
    source history, so the ledger witness of a coordinate match must
    itself be pinned into the source before coordinate-determinism can
    identify it with the replay entry.  Reachability alone does NOT
    provide this: the machine reaches phantom states (its stamps are
    bounded on the reachable set, but stamp bounds say nothing about
    payload membership) --- the membership control below reaches one
    whose phantom shares a committed coordinate.  What DOES provide it
    is the landed hazard taxonomy: @{thm [source] phantom_imp_premature}
    discharges membership from the escape's own effect-safe premise,
    so the corollaries below need nothing beyond the landed B1 premise
    set.

  Direction bookkeeping: coordinate-absent implies payload-absent with
  NO premise (the sub-filter above); both premises are consumed only by
  the converse direction, payload-absent implies coordinate-absent, on
  replay entries.
\<close>

theorem keyed_delta_eq_sink_delta:
  assumes asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
      and led: "\<forall>x \<in> set (dwe_emitted t).
                  e_payload x \<in> set (exec_src_hist (dwe_core t))"
  shows "keyed_delta f t = sink_delta f t"
  unfolding keyed_delta_def sink_delta_def
proof (rule filter_cong[OF refl])
  fix p
  assume pR: "p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                          (exec_scope (dwe_core t)) f)"
  have pS: "p \<in> set (exec_src_hist (dwe_core t))"
    using pR replay_down_hist_subset by blast
  show "(fst p \<notin> delivered_coords t)
          = (p \<notin> e_payload ` set (dwe_emitted t))"
  proof
    assume "fst p \<notin> delivered_coords t"
    then show "p \<notin> e_payload ` set (dwe_emitted t)"
      by (auto simp: delivered_coords_def)
  next
    assume pout: "p \<notin> e_payload ` set (dwe_emitted t)"
    show "fst p \<notin> delivered_coords t"
    proof
      assume "fst p \<in> delivered_coords t"
      then obtain q where qpf: "fst p = fst q"
          and qDP: "q \<in> e_payload ` set (dwe_emitted t)"
        unfolding delivered_coords_def by (rule imageE)
      have qc: "fst q = fst p"
        by (rule qpf[symmetric])
      have qS: "q \<in> set (exec_src_hist (dwe_core t))"
        using qDP led by auto
      have "q = p"
        by (rule strictly_ascending_coord_determines[OF asc qS pS qc])
      with qDP pout show False by simp
    qed
  qed
qed

text \<open>The membership premise in its landed taxonomy form: it is
  literally @{term "\<not> phantom t"}.\<close>

lemma not_phantom_delivered_in_source:
  assumes "\<not> phantom t"
  shows "\<forall>x \<in> set (dwe_emitted t).
           e_payload x \<in> set (exec_src_hist (dwe_core t))"
  using assms unfolding phantom_def by blast

corollary keyed_delta_eq_sink_delta_not_phantom:
  assumes "strictly_ascending_source (exec_src_hist (dwe_core t))"
      and "\<not> phantom t"
  shows "keyed_delta f t = sink_delta f t"
  by (rule keyed_delta_eq_sink_delta
        [OF assms(1) not_phantom_delivered_in_source[OF assms(2)]])

text \<open>Under the escape's own effect-safe premise the membership half is
  automatic (@{thm [source] phantom_imp_premature}): effect-safe states
  carry no phantom, so ONLY the named ascending premise remains --- the
  B1-aligned form of the equivalence.\<close>

corollary keyed_delta_eq_sink_delta_effect_safe:
  assumes asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
      and safe: "\<not> effect_unsafe t"
  shows "keyed_delta f t = sink_delta f t"
proof -
  have "\<not> premature t"
    using safe by (simp add: effect_unsafe_def)
  then have "\<not> phantom t"
    using phantom_imp_premature by blast
  then show ?thesis
    by (rule keyed_delta_eq_sink_delta_not_phantom[OF asc])
qed

section \<open>The keyed policy inherits the sink-reading escape\<close>

text \<open>
  The pinned policy redrive consumes only the policy's batch AT the
  crashed state, so a pointwise batch equation transports every landed
  redrive fact --- the keyed policy earns the landed B1 escape verbatim
  under EXACTLY the landed premises: it heals every scoped mismatch at
  its own frontier, stays effect-safe, and loses nothing.  This is the
  positive half of the practitioner rule: dedup by the stable key alone
  IS the escape, when the key is stable.
\<close>

theorem keyed_reading_escape:
  assumes safe: "\<not> effect_unsafe t"
      and crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
      and fin: "f \<le> exec_finish (dwe_core t)"
      and asc: "strictly_ascending_source (exec_src_hist (dwe_core t))"
  shows "(\<exists>t'. policy_redrive (keyed_delta f) t f t')
       \<and> (\<forall>t'. policy_redrive (keyed_delta f) t f t' \<longrightarrow>
            (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k)
          \<and> \<not> effect_unsafe t'
          \<and> \<not> lost_effect f t')"
proof -
  have eq: "keyed_delta f t = sink_delta f t"
    by (rule keyed_delta_eq_sink_delta_effect_safe[OF asc safe])
  have same: "\<And>t'. policy_redrive (keyed_delta f) t f t'
                     \<longleftrightarrow> policy_redrive (sink_delta f) t f t'"
    by (simp add: policy_redrive_def eq)
  show ?thesis
    unfolding same
    by (rule sink_reading_escape_general[OF safe crashed fin asc])
qed

text \<open>Non-vacuity at the landed loss-side dilemma witness: the escape
  premises hold at @{const d2_w} (@{thm [source] d2_asc},
  @{thm [source] d2_not_unsafe}), so the equivalence bites there ---
  the keyed batch IS the landed escape's batch at the landed witness.\<close>

corollary keyed_matches_payload_at_dilemma_witness:
  "keyed_delta ec2 d2_w = sink_delta ec2 d2_w"
  by (rule keyed_delta_eq_sink_delta_effect_safe[OF d2_asc d2_not_unsafe])

text \<open>
  And the keyed policy is a genuine SINK READER: on the dilemma's
  equal-core pair it computes different batches, so no function of the
  crashed core computes it --- the landed B2 face, mirrored.  Together
  with the escape above, the keyed policy sits on the sink-reading side
  of the landed dichotomy, exactly where the payload delta sits.
\<close>

theorem keyed_delta_not_store_measured:
  "\<not> store_measured (keyed_delta ec2)"
proof
  assume "store_measured (keyed_delta ec2)"
  then obtain g where g: "\<forall>t. keyed_delta ec2 t = g (dwe_core t)"
    unfolding store_measured_def by blast
  have eval1: "keyed_delta ec2 d1_w = []"
    by (simp add: keyed_delta_def delivered_coords_def d1_w_def mkT_def
                  mkC_def replay_down_hist_def e1_def e2_def ec_defs)
  have eval2: "keyed_delta ec2 d2_w = [(ec2, e2)]"
    by (simp add: keyed_delta_def delivered_coords_def d2_w_def mkT_def
                  mkC_def replay_down_hist_def e1_def e2_def ec_defs)
  have "keyed_delta ec2 d1_w = keyed_delta ec2 d2_w"
    using g d_cores_eq by metis
  then show False
    by (simp add: eval1 eval2)
qed

section \<open>THE ALIASING CONTROL: without the ascending premise, keyed
  dedup loses\<close>

text \<open>
  The machine walks into the separating window itself.  WF-H1 is
  non-strict (@{const history_can_append} admits an equal-coordinate
  re-commit --- the same locked-core guard the landed Discipline control
  chain exercises), so from the landed @{const W3} (event 1 committed
  AND delivered, ledger @{term "[(1, 0, ec1, e1)]"}) one more source
  commit puts a SECOND, genuinely distinct business event at the SAME
  coordinate @{const ec1}, and a crash closes the window:

  \<^item> committed source: @{term "[(ec1, e1), (ec1, e2)]"} --- two distinct
    payloads, one coordinate;
  \<^item> emission ledger: @{term "[(1, 0, ec1, e1)]"} --- the first payload
    delivered, so the coordinate @{const ec1} is a delivered KEY;
  \<^item> owed at frontier @{const ec1}: exactly @{term "(ec1, e2)"}.

  The payload delta computes exactly that owed batch.  The keyed delta
  computes NOTHING: the still-missing @{term "(ec1, e2)"} shares its
  key with the delivered @{term "(ec1, e1)"} and is dropped --- keyed
  dedup under aliasing loses, in the landed loss verdict, from a
  REACHABLE crashed state.  Note the isolation: the membership premise
  HOLDS at this state (its one delivered payload is committed --- no
  @{const phantom} emission), so the failure is attributable to the
  ascending premise alone.  Presentation mirrors the landed instance-exactness
  aliasing control of the exactly-once theory, on the same axis.
\<close>

definition alias_run_w :: "(nat, nat) dwe_state" where
  "alias_run_w = mkT (mkC [(ec1, e1), (ec1, e2)] [(ec1, e1)] [(ec1, e1)]
                        {} Running)
                     [(1, 0, ec1, e1)] 0"

definition alias_crash_w :: "(nat, nat) dwe_state" where
  "alias_crash_w = mkT (mkC [(ec1, e1), (ec1, e2)] [(ec1, e1)] [(ec1, e1)]
                          {} (Crashed ec1))
                       [(1, 0, ec1, e1)] 0"

text \<open>The equal-coordinate re-commit is admissible, and the aliased
  history is WF-legal (WF-H1 is non-strict).\<close>

lemma g_W3_src_alias:
  "exec_label_preserves_history_wf (dwe_core W3) (DoSource ec1 e2)"
  by (simp add: W3_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma wfh_alias_pair: "wellformed_src_history [(ec1, e1), (ec1, e2)]"
  by (rule wf_hist_pair) (simp_all add: ec_defs)

lemma wf_alias_run: "wellformed_exec_state (dwe_core alias_run_w)"
  by (simp add: alias_run_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e1
                wfh_alias_pair)

lemma g_alias_crash:
  "exec_label_preserves_history_wf (dwe_core alias_run_w) (Crash ec1)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma ws_alias1: "dwe_step W3 (DoSource ec1 e2) alias_run_w"
proof -
  have c: "dw_exec_step (dwe_core W3) (DoSource ec1 e2) (dwe_core alias_run_w)"
    by (rule do_sourceI) (simp_all add: W3_def alias_run_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c])
       (simp_all add: W3_def alias_run_w_def mkT_def)
qed

lemma ws_alias2: "dwe_step alias_run_w (Crash ec1) alias_crash_w"
proof -
  have c: "dw_exec_step (dwe_core alias_run_w) (Crash ec1)
             (dwe_core alias_crash_w)"
    by (rule crashI)
       (simp_all add: alias_run_w_def alias_crash_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c])
       (simp_all add: alias_run_w_def alias_crash_w_def mkT_def)
qed

lemma reach_alias_run: "dwe_reachable alias_run_w"
  by (rule dwe_reachable_label_ext[OF reach_W3 wf_W3 g_W3_src_alias ws_alias1])

lemma reach_alias_crash: "dwe_reachable alias_crash_w"
  by (rule dwe_reachable_label_ext[OF reach_alias_run wf_alias_run
        g_alias_crash ws_alias2])

subsection \<open>Verdict evaluations at the control state\<close>

lemma alias_not_asc:
  "\<not> strictly_ascending_source (exec_src_hist (dwe_core alias_crash_w))"
  by (simp add: strictly_ascending_source_def alias_crash_w_def mkT_def
                mkC_def)

lemma alias_not_phantom: "\<not> phantom alias_crash_w"
  by (simp add: phantom_def alias_crash_w_def mkT_def mkC_def)

lemma alias_committed_distinct_shared_coord:
  "(ec1, e2) \<in> set (exec_src_hist (dwe_core alias_crash_w))
 \<and> (ec1, e1) \<in> e_payload ` set (dwe_emitted alias_crash_w)
 \<and> fst (ec1, e2) = fst (ec1, e1)
 \<and> (ec1, e2) \<noteq> (ec1, e1)"
  by (simp add: alias_crash_w_def mkT_def mkC_def e1_def e2_def)

lemma alias_sink_delta: "sink_delta ec1 alias_crash_w = [(ec1, e2)]"
  by (simp add: sink_delta_def alias_crash_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs)

lemma alias_keyed_delta: "keyed_delta ec1 alias_crash_w = []"
  by (simp add: keyed_delta_def delivered_coords_def alias_crash_w_def
                mkT_def mkC_def replay_down_hist_def e1_def e2_def ec_defs)

lemma alias_deltas_differ:
  "keyed_delta ec1 alias_crash_w \<noteq> sink_delta ec1 alias_crash_w"
  by (simp add: alias_keyed_delta alias_sink_delta)

text \<open>The keyed redrive from the control state ends in the landed loss
  verdict; the payload redrive from the SAME state loses nothing and is
  effect-safe --- evaluated concretely at this witness (the general
  payload-side guarantee is the landed B1 and does need the ascending
  premise; the point here is only that at THIS state the keyed delta is
  the wrong one of the two).\<close>

lemma alias_keyed_redrive_loses:
  "lost_effect ec1 (redrive_result (keyed_delta ec1) alias_crash_w ec1)"
  by (simp add: lost_effect_def redrive_result_def keyed_delta_def
                delivered_coords_def alias_crash_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs eval_nat_numeral)

lemma alias_payload_redrive_no_loss:
  "\<not> lost_effect ec1 (redrive_result (sink_delta ec1) alias_crash_w ec1)"
  by (simp add: lost_effect_def redrive_result_def sink_delta_def
                alias_crash_w_def mkT_def mkC_def replay_down_hist_def
                e1_def e2_def ec_defs eval_nat_numeral)

lemma alias_payload_redrive_safe:
  "\<not> effect_unsafe (redrive_result (sink_delta ec1) alias_crash_w ec1)"
  by (simp add: effect_unsafe_def premature_def duplicate_def
                justified_at_def redrive_result_def sink_delta_def
                alias_crash_w_def mkT_def mkC_def replay_down_hist_def
                e1_def e2_def ec_defs eval_nat_numeral)

theorem keyed_dedup_aliasing_loses:
  "dwe_reachable alias_crash_w
 \<and> \<not> strictly_ascending_source (exec_src_hist (dwe_core alias_crash_w))
 \<and> \<not> phantom alias_crash_w
 \<and> sink_delta ec1 alias_crash_w = [(ec1, e2)]
 \<and> keyed_delta ec1 alias_crash_w = []
 \<and> keyed_delta ec1 alias_crash_w \<noteq> sink_delta ec1 alias_crash_w
 \<and> lost_effect ec1 (redrive_result (keyed_delta ec1) alias_crash_w ec1)
 \<and> \<not> lost_effect ec1 (redrive_result (sink_delta ec1) alias_crash_w ec1)
 \<and> \<not> effect_unsafe (redrive_result (sink_delta ec1) alias_crash_w ec1)"
  by (intro conjI reach_alias_crash alias_not_asc alias_not_phantom
        alias_sink_delta alias_keyed_delta alias_deltas_differ
        alias_keyed_redrive_loses alias_payload_redrive_no_loss
        alias_payload_redrive_safe)

subsection \<open>The landed equal-payload aliasing witness does not separate\<close>

text \<open>
  Honest scoping of the witness choice: the LANDED aliasing state
  @{const dd4_w} (the Discipline chain's equal-coordinate re-commit of
  the SAME payload, the exactly-once theory's instance-exactness
  control) does NOT separate the two deltas --- with both committed
  instances carrying one payload, payload dedup and key dedup starve
  the second instance EQUALLY, and the two batches agree.  Separating
  the deltas requires two DISTINCT payloads at one coordinate, which is
  precisely what the control state above adds; it also shows the
  equivalence's premises are sufficient, not necessary.
\<close>

lemma dd4_not_ascending:
  "\<not> strictly_ascending_source (exec_src_hist (dwe_core dd4_w))"
  by (simp add: strictly_ascending_source_def dd4_w_def mkT_def mkC_def)

lemma equal_payload_alias_sink_delta: "sink_delta ec1 dd4_w = []"
  by (simp add: sink_delta_def dd4_w_def mkT_def mkC_def
                replay_down_hist_def e1_def ec_defs)

lemma equal_payload_alias_keyed_delta: "keyed_delta ec1 dd4_w = []"
  by (simp add: keyed_delta_def delivered_coords_def dd4_w_def mkT_def
                mkC_def replay_down_hist_def e1_def ec_defs)

theorem equal_payload_alias_not_separating:
  "\<not> strictly_ascending_source (exec_src_hist (dwe_core dd4_w))
 \<and> duplicate dd4_w
 \<and> keyed_delta ec1 dd4_w = sink_delta ec1 dd4_w"
  by (intro conjI dd4_not_ascending duplicate_dd4)
     (simp add: equal_payload_alias_keyed_delta equal_payload_alias_sink_delta)

section \<open>THE MEMBERSHIP CONTROL: the no-phantom premise bites\<close>

text \<open>
  The second premise, isolated: a REACHABLE state whose committed
  source IS strictly ascending but whose ledger carries a PHANTOM
  delivery (an uncommitted payload) at a committed coordinate.  The
  chain is legal on the locked core --- enqueue and deliver are guarded
  only by Running status plus per-history append admissibility, which
  is how the landed premature corner is reached too: from the landed
  @{const W1} (event 1 committed), enqueue and deliver the DIFFERENT
  event @{const e2} at the SAME coordinate @{const ec1}, then crash.
  The delivered coordinate again blocks the committed
  @{term "(ec1, e1)"} in the keyed filter, and the keyed redrive
  starves it --- while the payload delta re-drives it.  So the
  equivalence genuinely needs BOTH halves: source-side key uniqueness
  (the ascending premise) and ledger-side key honesty (delivered
  payloads committed).  On effect-safe states the second half is free
  (@{thm [source] phantom_imp_premature}); this control lives exactly
  in the effect-UNSAFE corner the bare equation does not exclude.
\<close>

definition ph_enq_w :: "(nat, nat) dwe_state" where
  "ph_enq_w = mkT (mkC [(ec1, e1)] [] [(ec1, e2)] {(ec1, e2)} Running) [] 0"

definition ph_del_w :: "(nat, nat) dwe_state" where
  "ph_del_w = mkT (mkC [(ec1, e1)] [(ec1, e2)] [(ec1, e2)] {} Running)
                  [(1, 0, ec1, e2)] 0"

definition ph_crash_w :: "(nat, nat) dwe_state" where
  "ph_crash_w = mkT (mkC [(ec1, e1)] [(ec1, e2)] [(ec1, e2)] {}
                       (Crashed ec1))
                    [(1, 0, ec1, e2)] 0"

lemma g_W1_enq_alias:
  "exec_label_preserves_history_wf (dwe_core W1) (EnqueueDownstream ec1 e2)"
  by (simp add: W1_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma wfh_e2_at_ec1: "wellformed_src_history [(ec1, e2)]"
  by (rule wf_hist_single) (simp add: ec_defs)

lemma wf_ph_enq: "wellformed_exec_state (dwe_core ph_enq_w)"
  by (simp add: ph_enq_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e1
                wfh_e2_at_ec1)

lemma g_ph_enq_down:
  "exec_label_preserves_history_wf (dwe_core ph_enq_w) (DoDownstream ec1 e2)"
  by (simp add: ph_enq_w_def mkT_def mkC_def
                exec_label_preserves_history_wf_def history_can_append_def
                ec_defs)

lemma wf_ph_del: "wellformed_exec_state (dwe_core ph_del_w)"
  by (simp add: ph_del_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e1
                wfh_e2_at_ec1)

lemma g_ph_del_crash:
  "exec_label_preserves_history_wf (dwe_core ph_del_w) (Crash ec1)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma ws_ph1: "dwe_step W1 (EnqueueDownstream ec1 e2) ph_enq_w"
proof -
  have c: "dw_exec_step (dwe_core W1) (EnqueueDownstream ec1 e2)
             (dwe_core ph_enq_w)"
    by (rule enqueue_downstreamI)
       (simp_all add: W1_def ph_enq_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c])
       (simp_all add: W1_def ph_enq_w_def mkT_def)
qed

lemma ws_ph2: "dwe_step ph_enq_w (DoDownstream ec1 e2) ph_del_w"
proof -
  have c: "dw_exec_step (dwe_core ph_enq_w) (DoDownstream ec1 e2)
             (dwe_core ph_del_w)"
    by (rule do_downstreamI)
       (simp_all add: ph_enq_w_def ph_del_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_publish_emitI[OF c])
       (simp add: ph_enq_w_def ph_del_w_def mkT_def mkC_def eval_nat_numeral)
qed

lemma ws_ph3: "dwe_step ph_del_w (Crash ec1) ph_crash_w"
proof -
  have c: "dw_exec_step (dwe_core ph_del_w) (Crash ec1) (dwe_core ph_crash_w)"
    by (rule crashI)
       (simp_all add: ph_del_w_def ph_crash_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c])
       (simp_all add: ph_del_w_def ph_crash_w_def mkT_def)
qed

lemma reach_ph_enq: "dwe_reachable ph_enq_w"
  by (rule dwe_reachable_label_ext[OF reach_W1 wf_W1 g_W1_enq_alias ws_ph1])

lemma reach_ph_del: "dwe_reachable ph_del_w"
  by (rule dwe_reachable_label_ext[OF reach_ph_enq wf_ph_enq g_ph_enq_down
        ws_ph2])

lemma reach_ph_crash: "dwe_reachable ph_crash_w"
  by (rule dwe_reachable_label_ext[OF reach_ph_del wf_ph_del g_ph_del_crash
        ws_ph3])

lemma ph_asc:
  "strictly_ascending_source (exec_src_hist (dwe_core ph_crash_w))"
  by (simp add: strictly_ascending_source_def ph_crash_w_def mkT_def mkC_def)

lemma ph_phantom: "phantom ph_crash_w"
  by (simp add: phantom_def ph_crash_w_def mkT_def mkC_def e1_def e2_def)

lemma ph_sink_delta: "sink_delta ec1 ph_crash_w = [(ec1, e1)]"
  by (simp add: sink_delta_def ph_crash_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs)

lemma ph_keyed_delta: "keyed_delta ec1 ph_crash_w = []"
  by (simp add: keyed_delta_def delivered_coords_def ph_crash_w_def mkT_def
                mkC_def replay_down_hist_def e1_def e2_def ec_defs)

lemma ph_deltas_differ:
  "keyed_delta ec1 ph_crash_w \<noteq> sink_delta ec1 ph_crash_w"
  by (simp add: ph_keyed_delta ph_sink_delta)

lemma ph_keyed_redrive_loses:
  "lost_effect ec1 (redrive_result (keyed_delta ec1) ph_crash_w ec1)"
  by (simp add: lost_effect_def redrive_result_def keyed_delta_def
                delivered_coords_def ph_crash_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs eval_nat_numeral)

theorem phantom_defeats_keyed_delta:
  "dwe_reachable ph_crash_w
 \<and> strictly_ascending_source (exec_src_hist (dwe_core ph_crash_w))
 \<and> phantom ph_crash_w
 \<and> sink_delta ec1 ph_crash_w = [(ec1, e1)]
 \<and> keyed_delta ec1 ph_crash_w = []
 \<and> keyed_delta ec1 ph_crash_w \<noteq> sink_delta ec1 ph_crash_w
 \<and> lost_effect ec1 (redrive_result (keyed_delta ec1) ph_crash_w ec1)"
  by (intro conjI reach_ph_crash ph_asc ph_phantom ph_sink_delta
        ph_keyed_delta ph_deltas_differ ph_keyed_redrive_loses)

section \<open>The derive-once / stable-key rule, located exactly\<close>

text \<open>
  THE PRACTITIONER RULE, machine-checked.  Deployed CDC and outbox
  pipelines do not dedup re-drives by comparing whole payloads; they
  derive an idempotency KEY once, at commit time, from the record's
  stable source coordinate (LSN, offset, event id) and let the sink
  drop anything whose key it has already seen.  In this model that rule
  is @{const keyed_delta}, and this theory locates it exactly:

  \<^item> THE RULE IS EXACTLY THE NAMED PREMISES.  "Derive once from a stable
    key" is @{const strictly_ascending_source} (each commit gets a
    fresh, strictly larger coordinate: the key never aliases two
    business facts) together with ledger key-honesty (every delivered
    key was derived from a committed record: no @{const phantom}
    emission, free on effect-safe states).  Under them, keyed dedup IS payload
    dedup (@{thm [source] keyed_delta_eq_sink_delta}), and the keyed
    recovery inherits the landed escape verbatim
    (@{thm [source] keyed_reading_escape}): heal, no duplicate, no
    premature emission, no loss --- while remaining a genuine sink
    reader (@{thm [source] keyed_delta_not_store_measured}), consistent
    with the landed dilemma: reading the KEYS of the emission ledger is
    already reading the sink.

  \<^item> WHEN THE KEY IS NOT STABLE, THE RULE FAILS, AND FAILS SILENTLY
    TOWARD LOSS.  At the reachable equal-coordinate re-commit the key
    aliases two distinct committed facts; keyed dedup drops the
    undelivered one and the redrive ends in the landed loss verdict
    (@{thm [source] keyed_dedup_aliasing_loses}), while payload dedup
    at the same state re-drives it and stays effect-safe.  The failure
    is one-sided by construction: the keyed batch is a sub-filter of
    the payload batch (@{thm [source] keyed_delta_subfilter}), so
    key-based recovery never re-fires more than the escape --- its
    entire error budget is starvation, the hard-to-observe direction
    (the landed skip asymmetry: the effect verdict cannot see what was
    never emitted).

  \<^item> THE SCOPE IS THEORY-SIDE.  Both controls are reachable states of
    the pinned witness machine; the equivalence and its corollaries are
    stated at the landed vocabulary (@{const sink_delta},
    @{const policy_redrive}, @{const lost_effect}) with no new machine,
    rule, or hazard, and no claim beyond the landed B1/B2 family that
    they transport.
\<close>

end
