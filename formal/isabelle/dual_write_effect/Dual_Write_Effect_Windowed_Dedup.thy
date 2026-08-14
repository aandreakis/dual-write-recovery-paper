(*  Title:       Dual_Write_Effect_Windowed_Dedup.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE WINDOWED-DEDUP NEGATIVE CONTROL (Wave 2, slice W2c) --- an additive
    post-freeze slice under the freeze's own protocol: no landed statement,
    proof, definition, name, import, or session-DAG change to the frozen
    corpus.

    The landed folklore theorems (T2.11's layer-1 iff and its instance
    layer) consume sink_dedup_view = remdups over the WHOLE emission
    ledger: an idempotent consumer whose dedup memory is UNBOUNDED and
    PERMANENT --- an identifier, once seen, is remembered forever.
    Production dedup memories are TTL'd or capacity-bounded: idempotency
    keys expire after a day, an idempotent producer's sequence state is
    discarded after days of inactivity, consumer dedup tables are
    compacted.  Their absorption horizon is a WINDOW, not forever.  This
    theory prices that boundary: a windowed analogue of the landed view,
    its degeneration laws (at full window it literally IS the landed view,
    so everything landed is the unbounded special case), the positive
    calibration (below the horizon the landed folklore iff is intact at
    every state), and THE NEGATIVE CONTROL --- at the landed multi-cycle
    amplification state the original-to-duplicate gap exceeds a window of
    one, the windowed view carries the payload TWICE where the landed view
    carries it once, and the folklore iff instance is FALSE at that state
    for that window.  A TTL'd dedup memory CAN void the folklore iff once
    an original-to-duplicate gap exceeds the window (witnessed at window
    1); for the constructed run both sides of the threshold are witnessed
    at one state, between windows 1 and 2.  Windows count LEDGER
    POSITIONS, not time; the all-pairs gap condition is sufficient for the
    iff, not necessary (the window-2 restore holds while dup_gaps_within 2
    fails --- chained absorption).

    The landed theorems stand exactly as scoped: nothing here weakens
    them.  The control shows their dedup-memory model is load-bearing ---
    the same certificate shape as the landed aliasing control for the
    ascending premise (aliasing_defeats_instance_exactness), one
    disclosed-boundary rung further out.

    Machine of record: the LANDED CYCLIC MACHINE (dwe_state of
    Dual_Write_Effect_Cyclic), via the Exactly_Once import; the terminal
    branch and the channel branch are outside this import cone.  All
    witness states and transitions are the landed ones --- no new machine,
    rule, record, or witness chain; the window enters only as a parameter
    of a pure ledger view, the dedup-view precedent.

    PROVENANCE: THEORY_IMPROVEMENT_ROADMAP.md Wave 2 (slice W2c) +
    GAP_HUNT_FLEET_CAPTURE.md section A2 --- gap-hunt register rank 12
    (triple-convergent), lens capture candidate
    "idempotent-dedup-memory-ttl-undisclosed"
    (LENS_REDO_sink_retention: Stripe idempotency keys expire after 24
    hours; Kafka idempotent-producer sequence state after 7 days of
    inactivity; after an outage longer than the TTL the consumer's record
    of the original delivery has expired and it processes the re-driven
    duplicate as new).
*)

theory Dual_Write_Effect_Windowed_Dedup
  imports Dual_Write_Effect_Exactly_Once
begin

section \<open>The windowed dedup operator\<close>

text \<open>
  MODEL CHOICE, pinned.  @{const remdups} --- the landed view's engine ---
  keeps, of each payload's occurrences, the LAST one: an occurrence is
  absorbed exactly when the same value occurs anywhere later in the list.
  The windowed operator below limits that absorption test to a horizon of
  @{term w} entries: an occurrence is absorbed exactly when the same value
  occurs within the NEXT @{term w} entries.  Per payload, the ledger's
  occurrences fall into maximal chains whose consecutive gaps are at most
  @{term w}, and the view executes each chain once --- an occurrence whose
  distance from every other occurrence of its payload exceeds the window
  starts a new chain and is processed as new.

  The operational memory-bound consumer --- "remember the payloads of the
  last @{term w} received entries; execute what is not remembered" ---
  keeps the FIRST occurrence of each such chain instead of the last.  The
  two conventions are the keep-first/keep-last mirror of the same chain
  structure: same presence set, one executed occurrence per chain, same
  within-window absorption and same beyond-window boundary.  That mirror
  is exactly the occurrence choice the landed theory already discloses as
  irrelevant for @{const remdups} itself (only set membership,
  distinctness, and the counts they induce are ever consumed); the
  keep-first form is deliberately not formalized here --- every formal
  statement below is about the pinned operator.  The keep-last convention
  is pinned BECAUSE it degenerates literally: at full window
  @{text windowed_remdups} IS @{const remdups} by equation
  (@{text windowed_remdups_full} below), so the landed view is the
  unbounded special case of the windowed one by rewriting, not by
  paraphrase.
\<close>

fun windowed_remdups :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "windowed_remdups w [] = []"
| "windowed_remdups w (x # xs) =
     (if x \<in> set (take w xs) then windowed_remdups w xs
      else x # windowed_remdups w xs)"

text \<open>The two extremes: no memory executes the raw stream; a window
  covering the whole list is the landed unbounded dedup.\<close>

lemma windowed_remdups_zero: "windowed_remdups 0 xs = xs"
  by (induction xs) simp_all

lemma windowed_remdups_full:
  assumes "length xs \<le> w"
  shows "windowed_remdups w xs = remdups xs"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  from Cons.prems have "Suc (length xs) \<le> w" by simp
  then have lx: "length xs \<le> w" by (rule Suc_leD)
  show ?case
    using Cons.IH[OF lx] by (simp add: take_all[OF lx])
qed

text \<open>Presence is window-independent: the window changes MULTIPLICITY,
  never coverage --- shrinking the memory makes the consumer re-execute,
  it never makes a delivered payload disappear.\<close>

lemma windowed_remdups_set: "set (windowed_remdups w xs) = set xs"
  by (induction xs) (auto dest: in_set_takeD)

text \<open>Memory monotonicity: a longer memory never executes more often.
  Each entry's verdict tests membership in a take-prefix of the raw tail,
  and those prefixes grow with the window.\<close>

lemma windowed_remdups_count_antitone:
  assumes ww: "w \<le> w'"
  shows "count_list (windowed_remdups w' xs) p
           \<le> count_list (windowed_remdups w xs) p"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have sub: "set (take w xs) \<subseteq> set (take w' xs)"
    by (rule set_take_subset_set_take[OF ww])
  consider (both) "x \<in> set (take w xs)" "x \<in> set (take w' xs)"
    | (only_wide) "x \<notin> set (take w xs)" "x \<in> set (take w' xs)"
    | (neither) "x \<notin> set (take w xs)" "x \<notin> set (take w' xs)"
    using sub by blast
  then show ?case
  proof cases
    case both
    then show ?thesis using Cons.IH by simp
  next
    case only_wide
    have "count_list (windowed_remdups w' (x # xs)) p
            = count_list (windowed_remdups w' xs) p"
      using only_wide(2) by simp
    also have "\<dots> \<le> count_list (windowed_remdups w xs) p"
      by (rule Cons.IH)
    also have "\<dots> \<le> count_list (x # windowed_remdups w xs) p"
      by simp
    also have "count_list (x # windowed_remdups w xs) p
                 = count_list (windowed_remdups w (x # xs)) p"
      using only_wide(1) by simp
    finally show ?thesis .
  next
    case neither
    have "count_list (x # windowed_remdups w' xs) p
            \<le> count_list (x # windowed_remdups w xs) p"
      using Cons.IH by simp
    then show ?thesis using neither(1) neither(2) by simp
  qed
qed

lemma windowed_remdups_count_le_raw:
  "count_list (windowed_remdups w xs) p \<le> count_list xs p"
  using windowed_remdups_count_antitone[of 0 w xs p]
  by (simp add: windowed_remdups_zero)

lemma remdups_count_le_windowed_remdups:
  "count_list (remdups xs) p \<le> count_list (windowed_remdups w xs) p"
proof (cases "w \<le> length xs")
  case True
  then show ?thesis
    using windowed_remdups_count_antitone[of w "length xs" xs p]
    by (simp add: windowed_remdups_full)
next
  case False
  then have "length xs \<le> w" by linarith
  then show ?thesis by (simp add: windowed_remdups_full)
qed

section \<open>Distinctness within the horizon\<close>

text \<open>
  The dedup memory works within its horizon: if every pair of equal
  entries sits within @{term w} positions of each other, the windowed
  view is distinct --- the within-memory analogue of the landed
  @{text sink_dedup_view_distinct}.  The gap predicate quantifies over
  ALL equal-value position pairs; it is the honest cheap sufficient
  condition, not a characterization (chained duplicates whose consecutive
  gaps each fit the window also absorb, witnessed at the control state
  below with the window covering the largest consecutive gap).
\<close>

definition dup_gaps_within :: "nat \<Rightarrow> 'a list \<Rightarrow> bool" where
  "dup_gaps_within w xs \<longleftrightarrow>
     (\<forall>i j. i < j \<longrightarrow> j < length xs \<longrightarrow> xs ! i = xs ! j \<longrightarrow> j - i \<le> w)"

lemma dup_gaps_within_Cons:
  assumes "dup_gaps_within w (x # xs)"
  shows "dup_gaps_within w xs"
  unfolding dup_gaps_within_def
proof (intro allI impI)
  fix i j :: nat
  assume ij: "i < j" and jlen: "j < length xs" and eq: "xs ! i = xs ! j"
  have "Suc i < Suc j" and "Suc j < length (x # xs)"
    and "(x # xs) ! Suc i = (x # xs) ! Suc j"
    using ij jlen eq by simp_all
  then have "Suc j - Suc i \<le> w"
    using assms[unfolded dup_gaps_within_def, rule_format, of "Suc i" "Suc j"]
    by blast
  then show "j - i \<le> w" by simp
qed

lemma dup_gaps_within_head_in_window:
  assumes gaps: "dup_gaps_within w (x # xs)"
      and mem: "x \<in> set xs"
  shows "x \<in> set (take w xs)"
proof -
  from mem obtain j where j: "j < length xs" and xj: "xs ! j = x"
    by (auto simp: in_set_conv_nth)
  have "(0::nat) < Suc j" and "Suc j < length (x # xs)"
    and "(x # xs) ! 0 = (x # xs) ! Suc j"
    using j xj by simp_all
  then have "Suc j - 0 \<le> w"
    using gaps[unfolded dup_gaps_within_def, rule_format, of 0 "Suc j"]
    by blast
  then have jw: "j < w" by simp
  have len: "j < length (take w xs)"
    using j jw by simp
  have "take w xs ! j = x"
    using jw xj by (simp add: nth_take)
  with nth_mem[OF len] show ?thesis by simp
qed

lemma windowed_remdups_within_horizon_distinct:
  assumes "dup_gaps_within w xs"
  shows "distinct (windowed_remdups w xs)"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have tail: "dup_gaps_within w xs"
    by (rule dup_gaps_within_Cons[OF Cons.prems])
  show ?case
  proof (cases "x \<in> set (take w xs)")
    case True
    then show ?thesis using Cons.IH[OF tail] by simp
  next
    case False
    then have "x \<notin> set xs"
      using dup_gaps_within_head_in_window[OF Cons.prems] by blast
    then have "x \<notin> set (windowed_remdups w xs)"
      by (simp add: windowed_remdups_set)
    with False Cons.IH[OF tail] show ?thesis by simp
  qed
qed

section \<open>The windowed view and its degeneration laws\<close>

text \<open>
  The windowed/TTL analogue of the landed @{const sink_dedup_view}: the
  idempotent consumer's executed-effect stream when its dedup memory has
  horizon @{term w} over the emission ledger, as a pure ledger view ---
  a projection of @{term "dwe_emitted t"}, the dedup-view precedent; no
  machine extension, no new rule.  The landed view is the unbounded
  special case (the bridge theorem below); @{term "w = 0"} is the
  memoryless consumer executing the raw delivery stream.
\<close>

definition windowed_dedup_view
  :: "nat \<Rightarrow> ('k, 'v) dwe_state \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list"
where
  "windowed_dedup_view w t = windowed_remdups w (map e_payload (dwe_emitted t))"

lemma windowed_dedup_view_zero:
  "windowed_dedup_view 0 t = map e_payload (dwe_emitted t)"
  by (simp add: windowed_dedup_view_def windowed_remdups_zero)

text \<open>THE BRIDGE: at full window the windowed view IS the landed view ---
  literal equality, so every landed @{const sink_dedup_view} fact is the
  unbounded instance of the windowed family by rewriting.  The landed
  folklore theorems carry an implicit window premise, and this equation
  is that premise made explicit.\<close>

theorem windowed_dedup_view_full_window:
  assumes "length (dwe_emitted t) \<le> w"
  shows "windowed_dedup_view w t = sink_dedup_view t"
  using assms
  by (simp add: windowed_dedup_view_def sink_dedup_view_def
                windowed_remdups_full)

corollary windowed_dedup_view_full_window_distinct:
  "length (dwe_emitted t) \<le> w \<Longrightarrow> distinct (windowed_dedup_view w t)"
  by (simp add: windowed_dedup_view_full_window sink_dedup_view_distinct)

lemma windowed_dedup_view_set:
  "set (windowed_dedup_view w t) = e_payload ` set (dwe_emitted t)"
  by (simp add: windowed_dedup_view_def windowed_remdups_set)

text \<open>The count sandwich: every windowed count sits between the landed
  unbounded view's count and the raw delivery stream's count --- bounded
  memory interpolates between the landed idempotent consumer and no
  consumer-side dedup at all.\<close>

theorem windowed_count_sandwich:
  "count_list (sink_dedup_view t) p \<le> count_list (windowed_dedup_view w t) p
 \<and> count_list (windowed_dedup_view w t) p
     \<le> count_list (map e_payload (dwe_emitted t)) p"
  by (simp add: windowed_dedup_view_def sink_dedup_view_def
                remdups_count_le_windowed_remdups windowed_remdups_count_le_raw)

section \<open>The positive calibration: below the horizon the folklore iff is intact\<close>

text \<open>
  When every duplicate pair of the ledger's payload stream sits within
  the window, the windowed view still absorbs exactly as the landed
  unbounded view does: each delivered payload executes once, and the
  landed folklore iff --- the layer-1 kernel
  @{thm [source] dedup_sink_exactly_once_iff_at_least_once} --- holds
  verbatim with the windowed view in place of the landed one, at every
  state and every frontier.  This is the folklore's actual production
  contract: at-least-once delivery plus an idempotent consumer is
  exactly-once WHILE the duplicate arrives inside the dedup memory's
  horizon.
\<close>

theorem windowed_dedup_view_count_within_horizon:
  assumes gaps: "dup_gaps_within w (map e_payload (dwe_emitted t))"
  shows "count_list (windowed_dedup_view w t) p
           = (if p \<in> e_payload ` set (dwe_emitted t) then 1 else 0)"
proof -
  have dist: "distinct (windowed_dedup_view w t)"
    unfolding windowed_dedup_view_def
    by (rule windowed_remdups_within_horizon_distinct[OF gaps])
  show ?thesis
    by (simp add: count_list_distinct_mem[OF dist] windowed_dedup_view_set)
qed

theorem windowed_folklore_iff_within_horizon:
  assumes gaps: "dup_gaps_within w (map e_payload (dwe_emitted t))"
  shows "(\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                      (exec_scope (dwe_core t)) f).
            count_list (windowed_dedup_view w t) p = 1)
       \<longleftrightarrow> at_least_once_at f t"
  by (auto simp: windowed_dedup_view_count_within_horizon[OF gaps]
                 at_least_once_at_def subset_iff)

text \<open>At full window the same iff is literally the landed theorem.\<close>

theorem windowed_folklore_iff_full_window:
  assumes "length (dwe_emitted t) \<le> w"
  shows "(\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t))
                      (exec_scope (dwe_core t)) f).
            count_list (windowed_dedup_view w t) p = 1)
       \<longleftrightarrow> at_least_once_at f t"
  unfolding windowed_dedup_view_full_window[OF assms]
  by (rule dedup_sink_exactly_once_iff_at_least_once)

subsection \<open>The within-horizon witness: the first crash cycle's duplicate\<close>

text \<open>
  The landed first-cycle duplicate state @{const t_fin_w} (crash, cold
  re-drive, payload count 2) has its duplicate pair ADJACENT in the
  ledger: gap 1.  A dedup memory of one entry --- the smallest
  non-degenerate window --- already absorbs it: the windowed view equals
  the landed view literally (at a window strictly below full: the ledger
  has three entries), and the folklore iff instance holds with both sides
  true.  Below the horizon, the landed story is unchanged.
\<close>

lemma t_fin_payloads:
  "map e_payload (dwe_emitted t_fin_w) = [(ec1, e1), (ec1, e1), (ec2, e2)]"
  by (simp add: t_fin_w_def mkT_def)

lemma t_fin_dup_gaps_within:
  "dup_gaps_within 1 (map e_payload (dwe_emitted t_fin_w))"
  unfolding t_fin_payloads dup_gaps_within_def
proof (intro allI impI)
  fix i j :: nat
  assume ij: "i < j"
     and jlen: "j < length [(ec1, e1), (ec1, e1), (ec2, e2)]"
     and eq: "[(ec1, e1), (ec1, e1), (ec2, e2)] ! i
                = [(ec1, e1), (ec1, e1), (ec2, e2)] ! j"
  have j3: "j < 3" using jlen by (simp add: eval_nat_numeral)
  show "j - i \<le> 1"
  proof (cases "j = 1")
    case True
    with ij show ?thesis by auto
  next
    case False
    with ij j3 have j2: "j = 2" by auto
    with eq have "[(ec1, e1), (ec1, e1), (ec2, e2)] ! i = (ec2, e2)"
      by (simp add: eval_nat_numeral)
    moreover from ij j2 have "i = 0 \<or> i = 1" by auto
    ultimately have False by (auto simp: e1_def e2_def eval_nat_numeral)
    then show ?thesis ..
  qed
qed

lemma t_fin_windowed_view_eq_landed:
  "windowed_dedup_view 1 t_fin_w = sink_dedup_view t_fin_w"
  by (simp add: windowed_dedup_view_def sink_dedup_view_def t_fin_w_def
                mkT_def e1_def e2_def ec_defs eval_nat_numeral)

theorem windowed_dedup_absorbs_within_horizon:
  "dwe_reachable t_fin_w
 \<and> dup_gaps_within 1 (map e_payload (dwe_emitted t_fin_w))
 \<and> windowed_dedup_view 1 t_fin_w = sink_dedup_view t_fin_w
 \<and> ((\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t_fin_w))
                  (exec_scope (dwe_core t_fin_w)) ec2).
       count_list (windowed_dedup_view 1 t_fin_w) p = 1)
    \<longleftrightarrow> at_least_once_at ec2 t_fin_w)
 \<and> at_least_once_at ec2 t_fin_w"
  by (intro conjI reach_t_fin t_fin_dup_gaps_within
        t_fin_windowed_view_eq_landed
        windowed_folklore_iff_within_horizon[OF t_fin_dup_gaps_within]
        t_fin_at_least_once)

section \<open>The negative control: beyond the horizon the folklore iff fails\<close>

text \<open>
  THE PAYLOAD.  The landed multi-cycle amplification state
  @{const f_amp_w} (the G5 chain: crash, cold re-drive, Resume into epoch
  1, crash again, cold re-drive again ---
  @{thm [source] resume_cycle_amplification}) carries the payload
  @{term "(ec1, e1)"} at ledger positions 0, 1 and 3: the epoch-0 pair is
  adjacent (gap 1), and the epoch-1 re-emission sits at gap 2 from its
  nearest earlier occurrence --- the second crash/recovery cycle
  interposed the re-driven @{term "(ec2, e2)"} between them.  For the
  window @{term "w = 1"} the state is exactly the register's outage
  pattern: the original-to-duplicate gap EXCEEDS the window.

  At that state and that window, counted at the landed obligation
  @{term "(ec1, e1)"}:

  \<^item> the raw delivery stream carries it 3 times (the landed amplification
    count);

  \<^item> the windowed view carries it TWICE --- the within-window adjacent
    pair collapses (3 drops to 2: the dedup memory still works below its
    horizon), but the beyond-window occurrence is processed as new;

  \<^item> the landed unbounded view carries it once, and the landed folklore
    iff instance is TRUE at this very state --- unbounded memory absorbs
    everything, which is exactly the assumption being priced.

  The folklore iff stated with the windowed view --- the landed
  @{thm [source] dedup_sink_exactly_once_iff_at_least_once} with
  @{term "windowed_dedup_view 1"} in place of @{const sink_dedup_view},
  at the landed theorem's own frontier --- is FALSE at this reachable
  state: delivery is at-least-once, yet the TTL'd consumer executes a
  scoped obligation twice.
\<close>

lemma f_amp_payloads:
  "map e_payload (dwe_emitted f_amp_w)
     = [(ec1, e1), (ec1, e1), (ec2, e2), (ec1, e1), (ec2, e2)]"
  by (simp add: f_amp_w_def mkT_def)

lemma f_amp_gap_geometry:
  "map e_payload (dwe_emitted f_amp_w) ! 0 = (ec1, e1)
 \<and> map e_payload (dwe_emitted f_amp_w) ! 1 = (ec1, e1)
 \<and> map e_payload (dwe_emitted f_amp_w) ! 3 = (ec1, e1)"
  by (simp add: f_amp_payloads eval_nat_numeral)

lemma f_amp_gap_exceeds_window:
  "\<not> dup_gaps_within 1 (map e_payload (dwe_emitted f_amp_w))"
proof
  assume g: "dup_gaps_within 1 (map e_payload (dwe_emitted f_amp_w))"
  have len: "(3::nat) < length (map e_payload (dwe_emitted f_amp_w))"
    by (simp add: f_amp_payloads)
  have eq: "map e_payload (dwe_emitted f_amp_w) ! 1
              = map e_payload (dwe_emitted f_amp_w) ! 3"
    using f_amp_gap_geometry by simp
  have "(3::nat) - 1 \<le> 1"
    using g[unfolded dup_gaps_within_def, rule_format, of 1 3] len eq
    by simp
  then show False by simp
qed

lemma f_amp_at_least_once: "at_least_once_at ec2 f_amp_w"
  by (simp add: at_least_once_at_def f_amp_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs eval_nat_numeral)

lemma f_amp_obligation_mem:
  "(ec1, e1) \<in> set (replay_down_hist (exec_src_hist (dwe_core f_amp_w))
                      (exec_scope (dwe_core f_amp_w)) ec2)"
  by (simp add: f_amp_w_def mkT_def mkC_def replay_down_hist_def
                e1_def e2_def ec_defs eval_nat_numeral)

lemma f_amp_raw_count:
  "count_list (map e_payload (dwe_emitted f_amp_w)) (ec1, e1) = 3"
  by (simp add: f_amp_w_def mkT_def e1_def e2_def ec_defs eval_nat_numeral)

lemma f_amp_windowed_count:
  "count_list (windowed_dedup_view 1 f_amp_w) (ec1, e1) = 2"
  by (simp add: windowed_dedup_view_def f_amp_w_def mkT_def
                e1_def e2_def ec_defs eval_nat_numeral)

lemma f_amp_unbounded_count:
  "count_list (sink_dedup_view f_amp_w) (ec1, e1) = 1"
  by (simp add: sink_dedup_view_def f_amp_w_def mkT_def
                e1_def e2_def ec_defs eval_nat_numeral)

text \<open>The failing instance, stated against the landed theorem's exact
  form: the landed iff with the windowed view substituted, negated.\<close>

theorem windowed_folklore_iff_fails_beyond_window:
  "\<not> ((\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core f_amp_w))
                   (exec_scope (dwe_core f_amp_w)) ec2).
        count_list (windowed_dedup_view 1 f_amp_w) p = 1)
      \<longleftrightarrow> at_least_once_at ec2 f_amp_w)"
proof
  assume iff: "(\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core f_amp_w))
                            (exec_scope (dwe_core f_amp_w)) ec2).
                  count_list (windowed_dedup_view 1 f_amp_w) p = 1)
               \<longleftrightarrow> at_least_once_at ec2 f_amp_w"
  then have "count_list (windowed_dedup_view 1 f_amp_w) (ec1, e1) = 1"
    using f_amp_at_least_once f_amp_obligation_mem by blast
  with f_amp_windowed_count show False by simp
qed

text \<open>The register-shaped package: reachable state, epoch-1 gap beyond
  the window, at-least-once delivery, the 3/2/1 count sandwich instance,
  the landed unbounded instance TRUE at the same state, the windowed
  instance FALSE.\<close>

theorem ttl_dedup_memory_voids_folklore:
  "dwe_reachable f_amp_w
 \<and> dwe_epoch f_amp_w = 1
 \<and> \<not> dup_gaps_within 1 (map e_payload (dwe_emitted f_amp_w))
 \<and> at_least_once_at ec2 f_amp_w
 \<and> count_list (map e_payload (dwe_emitted f_amp_w)) (ec1, e1) = 3
 \<and> count_list (windowed_dedup_view 1 f_amp_w) (ec1, e1) = 2
 \<and> count_list (sink_dedup_view f_amp_w) (ec1, e1) = 1
 \<and> (\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core f_amp_w))
                 (exec_scope (dwe_core f_amp_w)) ec2).
      count_list (sink_dedup_view f_amp_w) p = 1)
 \<and> \<not> ((\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core f_amp_w))
                    (exec_scope (dwe_core f_amp_w)) ec2).
         count_list (windowed_dedup_view 1 f_amp_w) p = 1)
       \<longleftrightarrow> at_least_once_at ec2 f_amp_w)"
proof -
  have epoch: "dwe_epoch f_amp_w = 1"
    by (simp add: f_amp_w_def mkT_def)
  have landed: "\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core f_amp_w))
                            (exec_scope (dwe_core f_amp_w)) ec2).
                  count_list (sink_dedup_view f_amp_w) p = 1"
    using dedup_sink_exactly_once_iff_at_least_once f_amp_at_least_once
    by blast
  show ?thesis
    by (intro conjI reach_f_amp epoch f_amp_gap_exceeds_window
          f_amp_at_least_once f_amp_raw_count f_amp_windowed_count
          f_amp_unbounded_count landed
          windowed_folklore_iff_fails_beyond_window)
qed

subsection \<open>The boundary is the window: both sides at one state\<close>

text \<open>
  At the SAME state, widening the window from 1 to 2 --- covering the
  largest consecutive same-payload gap --- restores the landed view
  literally, and with it the folklore iff instance.  One state, one
  parameter, verdict flipped.

  SCOPE, exactly: the theorem below locates the threshold between
  windows 1 and 2 FOR THIS CONSTRUCTED RUN --- the @{const f_amp_w}
  ledger's duplicate-gap geometry --- not a universal exact
  characterization of where a windowed consumer fails; on another run
  the threshold sits wherever that run's gaps put it.  The window unit
  is LEDGER POSITIONS (entries of @{term "dwe_emitted t"}), not time: a
  TTL translates into positions only through the delivery rate.  And
  @{const dup_gaps_within} is a SUFFICIENT condition for the folklore
  equivalence (@{thm [source] windowed_folklore_iff_within_horizon}),
  proven NON-NECESSARY in this same file: the window-2 equivalence in
  the theorem below holds while @{term "dup_gaps_within 2"} FAILS on the
  same ledger (the pair at positions 0 and 3 spans gap 3) ---
  consecutive-gap chaining absorbs too.  Two qualifiers are made formal
  conjuncts rather than prose: the window 2 sits strictly below the
  full-window bridge (the ledger has five entries), and the all-pairs
  gap predicate is FALSE at window 2.
\<close>

lemma f_amp_window_two_restores:
  "windowed_dedup_view 2 f_amp_w = sink_dedup_view f_amp_w"
  by (simp add: windowed_dedup_view_def sink_dedup_view_def f_amp_w_def
                mkT_def e1_def e2_def ec_defs eval_nat_numeral)

lemma f_amp_not_dup_gaps_within_two:
  "\<not> dup_gaps_within 2 (map e_payload (dwe_emitted f_amp_w))"
proof
  assume g: "dup_gaps_within 2 (map e_payload (dwe_emitted f_amp_w))"
  have len: "(3::nat) < length (map e_payload (dwe_emitted f_amp_w))"
    by (simp add: f_amp_payloads)
  have eq: "map e_payload (dwe_emitted f_amp_w) ! 0
              = map e_payload (dwe_emitted f_amp_w) ! 3"
    using f_amp_gap_geometry by simp
  have "(3::nat) - 0 \<le> 2"
    using g[unfolded dup_gaps_within_def, rule_format, of 0 3] len eq
    by simp
  then show False by simp
qed

theorem f_amp_window1_fails_window2_restores:
  "count_list (windowed_dedup_view 1 f_amp_w) (ec1, e1) = 2
 \<and> \<not> ((\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core f_amp_w))
                    (exec_scope (dwe_core f_amp_w)) ec2).
         count_list (windowed_dedup_view 1 f_amp_w) p = 1)
       \<longleftrightarrow> at_least_once_at ec2 f_amp_w)
 \<and> windowed_dedup_view 2 f_amp_w = sink_dedup_view f_amp_w
 \<and> 2 < length (dwe_emitted f_amp_w)
 \<and> \<not> dup_gaps_within 2 (map e_payload (dwe_emitted f_amp_w))
 \<and> ((\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core f_amp_w))
                  (exec_scope (dwe_core f_amp_w)) ec2).
       count_list (windowed_dedup_view 2 f_amp_w) p = 1)
    \<longleftrightarrow> at_least_once_at ec2 f_amp_w)"
proof -
  have w2: "(\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core f_amp_w))
                         (exec_scope (dwe_core f_amp_w)) ec2).
               count_list (windowed_dedup_view 2 f_amp_w) p = 1)
            \<longleftrightarrow> at_least_once_at ec2 f_amp_w"
    unfolding f_amp_window_two_restores
    by (rule dedup_sink_exactly_once_iff_at_least_once)
  have len2: "2 < length (dwe_emitted f_amp_w)"
    by (simp add: f_amp_w_def mkT_def eval_nat_numeral)
  show ?thesis
    by (intro conjI f_amp_windowed_count
          windowed_folklore_iff_fails_beyond_window
          f_amp_window_two_restores len2 f_amp_not_dup_gaps_within_two w2)
qed

section \<open>The machine continuation: the outage outgrows the memory\<close>

text \<open>
  The two witness states sit on ONE landed machine chain: from
  @{const t_fin_w} the landed transitions Resume
  (@{thm [source] res_f}), crash (@{thm [source] wsf1}) and cold
  re-drive (@{thm [source] rec_amp}) reach @{const f_amp_w}.  At the
  chain's first duplicate state the gap-1 pair sits inside the
  one-entry memory and the windowed folklore iff instance HOLDS; the
  machine's own second crash/recovery cycle lands the re-emission at gap
  2, and the SAME memory processes it as new --- the iff instance FAILS.
  This is the register's outage pattern as a theorem: the dedup TTL
  survived the first incident and was outgrown by the second, with no
  parameter of the view changed in between.
\<close>

theorem window_voided_along_machine_continuation:
  "dwe_reachable t_fin_w
 \<and> ((\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core t_fin_w))
                  (exec_scope (dwe_core t_fin_w)) ec2).
       count_list (windowed_dedup_view 1 t_fin_w) p = 1)
    \<longleftrightarrow> at_least_once_at ec2 t_fin_w)
 \<and> dwe_resume t_fin_w f_run_w
 \<and> dwe_step f_run_w (Crash ec2) f_crash_w
 \<and> emitting_reconcile 0 f_crash_w ec2 f_amp_w
 \<and> \<not> ((\<forall>p \<in> set (replay_down_hist (exec_src_hist (dwe_core f_amp_w))
                    (exec_scope (dwe_core f_amp_w)) ec2).
         count_list (windowed_dedup_view 1 f_amp_w) p = 1)
       \<longleftrightarrow> at_least_once_at ec2 f_amp_w)"
  by (intro conjI reach_t_fin
        windowed_folklore_iff_within_horizon[OF t_fin_dup_gaps_within]
        res_f wsf1 rec_amp windowed_folklore_iff_fails_beyond_window)

section \<open>The named boundary: unbounded, permanent dedup memory\<close>

text \<open>
  THE ASSUMPTION THE LANDED FOLKLORE THEOREMS CARRY, named (a theory-side
  boundary note).  The landed
  @{thm [source] dedup_sink_exactly_once_iff_at_least_once} and
  @{thm [source] dedup_sink_instance_exact_iff} --- and every landed
  statement consuming @{const sink_dedup_view} --- model the idempotent
  consumer's dedup memory as @{const remdups} over the WHOLE emission
  ledger: an unbounded, permanent memory that never expires an
  identifier, however far in the past the original delivery lies and
  however many crash/recovery cycles separate it from the re-drive.
  Production dedup memories have a horizon: idempotency keys and producer
  sequence state expire, dedup tables are bounded and compacted.  Under a
  horizon the folklore iff's true form is window-conditional:

  \<^item> BELOW the horizon it is intact --- verbatim, at every state and
    frontier (@{thm [source] windowed_folklore_iff_within_horizon}), and
    at full window it IS the landed theorem by literal view equality
    (@{thm [source] windowed_dedup_view_full_window});

  \<^item> BEYOND the horizon it has a reachable counterexample on the machine's
    own multi-cycle chain
    (@{thm [source] ttl_dedup_memory_voids_folklore}), where delivery is
    at-least-once and the TTL'd consumer nevertheless executes a scoped
    obligation twice --- the boundary crossed by nothing but the landed
    machine's own second crash/recovery cycle
    (@{thm [source] window_voided_along_machine_continuation}).

  The landed theorems stand exactly as scoped --- their view is the
  unbounded one BY DEFINITION, and this theory changes none of them.
  What the control adds is the price tag: reading the landed folklore
  iff as a statement about a real consumer silently assumes the dedup
  memory outlives every original-to-duplicate gap the recovery can
  produce, and the landed amplification chain already produces a gap
  that a one-entry memory does not survive.  The same discipline as the
  landed aliasing control for @{const strictly_ascending_source}: name
  the premise, witness it load-bearing at a reachable state, leave the
  theorem of record untouched.
\<close>

end
