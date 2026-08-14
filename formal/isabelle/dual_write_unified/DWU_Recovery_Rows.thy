(*  Title:       DWU_Recovery_Rows.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Purpose: Road-2 I2 — THE R-ROW BLOCK (conservativity's payoff).

    The landed dilemma / escape / anti-healing / dedup theorems recovered as
    corollaries of the unified machine, STRENGTHENED where the pins say so:

      U4  u_batch_agreement_dilemma        (R1: the exists-pair defeat)
          u_recovery_information_dilemma   (R2: store-measured face)
          u_control_plane_measured_dilemma (R3 STRENGTHENED: reads the whole
                                            control plane and still loses)
      U5  u_sink_reading_escape            (R4: two explicit premises)
          u_escape_not_store_measured      (R5)
          u_escape_not_control_plane_measured
      U6  u_effect_unsafe_monotone         (R7 MACHINE-WIDE incl. UTruncCrash)
          u_effect_unsafe_trace_persistent
      U7  u_dedup_sink_exactly_once_iff_at_least_once
          u_dedup_sink_instance_exact_iff
          u_aliasing_control_embedded
          u_no_store_measured_exactly_once (necessity face, from U4/R2 kernel)
      R6  u_solo_positive_discipline       (Pi-pullback over solo_disciplined_trace,
          u_solo_discipline_projects        STANDALONE / decoupled from U8)
          u_landed_discipline_lifts
          u_general_positive_discipline_solo

    Reuses the I1 fused-triple package (fused_triple_endpoint etc.), the S1 gens
    invariant / S2 exec_base constancy / S4 stamps invariant from DWU_Machine,
    and the U1/U2/U3 conservativity principals.

    Honesty regime: quick_and_dirty = false (ROOT-pinned), ZERO sorry, ZERO
    oops, no axiomatization, no consts, no oracles.  Every principal PROVED,
    statement byte-identical to the Stage-3 probe seed.
*)

theory DWU_Recovery_Rows
  imports DWU_Conservativity
begin

section \<open>0. Shared infrastructure\<close>

subsection \<open>0.1 The @{const \<iota>} hazard/ledger bridges\<close>

text \<open>@{const log_payloads} of a @{const ulift}-image reads back the landed
  payload list, as a list.\<close>

lemma log_payloads_map_ulift [simp]:
  "log_payloads (map ulift es) = map e_payload es"
  by (induction es) (auto simp: log_payloads_def map_filter_simps ulift_def)

text \<open>The three hazard verdicts commute at @{term "\<iota> t"} on the nose (the
  fragment premises are automatic under @{const \<iota>}), collapsing via the section
  law to the landed verdict.\<close>

lemma u_hazards_once_\<iota>:
  "(u_premature (\<iota> t) \<longleftrightarrow> premature t)
 \<and> (u_duplicate (\<iota> t) \<longleftrightarrow> duplicate t)
 \<and> (u_effect_unsafe (\<iota> t) \<longleftrightarrow> effect_unsafe t)"
proof -
  have p1: "dwu_sent (\<iota> t) = dwu_accepted (\<iota> t)" by simp
  have p2: "dwu_journal (\<iota> t) = exec_src_hist (dwu_store (\<iota> t))" by simp
  have p3: "\<forall>x \<in> set (dwu_sent (\<iota> t)). is_ulog x" by (auto simp: \<iota>_sent)
  from u_hazards_once[OF p1 p2 p3] show ?thesis by (simp add: \<Pi>_section)
qed

lemma u_effect_unsafe_\<iota> [simp]: "u_effect_unsafe (\<iota> t) \<longleftrightarrow> effect_unsafe t"
  using u_hazards_once_\<iota> by blast

lemma u_genuinely_emitting_\<iota> [simp]:
  "u_genuinely_emitting (\<iota> t) \<longleftrightarrow> genuinely_emitting t"
  by (simp add: u_genuinely_emitting_def genuinely_emitting_def \<iota>_accepted)

text \<open>Sink-delta / loss / at-least-once commute at @{term "\<iota> t"} (floor 0,
  ledgers equal).\<close>

lemma u_lost_\<iota> [simp]:
  fixes t :: "(nat, nat) dwe_state"
  shows "u_lost f (\<iota> t) \<longleftrightarrow> lost_effect f t"
proof -
  have s: "dwu_sent (\<iota> t) = dwu_accepted (\<iota> t)" by simp
  have f0: "dwu_floor (\<iota> t) = 0" by simp
  have "u_lost f (\<iota> t) \<longleftrightarrow> lost_effect f (\<Pi> (\<iota> t))"
    using u_sink_delta_commutes[OF s f0] by blast
  then show ?thesis by (simp add: \<Pi>_section)
qed

lemma u_at_least_once_\<iota> [simp]:
  fixes t :: "(nat, nat) dwe_state"
  shows "u_at_least_once_at f (\<iota> t) \<longleftrightarrow> at_least_once_at f t"
proof -
  have s: "dwu_sent (\<iota> t) = dwu_accepted (\<iota> t)" by simp
  have f0: "dwu_floor (\<iota> t) = 0" by simp
  have "u_at_least_once_at f (\<iota> t) \<longleftrightarrow> at_least_once_at f (\<Pi> (\<iota> t))"
    using u_sink_delta_commutes[OF s f0] by blast
  then show ?thesis by (simp add: \<Pi>_section)
qed

lemma u_sink_delta_\<iota>:
  fixes t :: "(nat, nat) dwe_state"
  shows "u_sink_delta f (\<iota> t) = sink_delta f t"
proof -
  have s: "dwu_sent (\<iota> t) = dwu_accepted (\<iota> t)" by simp
  have f0: "dwu_floor (\<iota> t) = 0" by simp
  have "u_sink_delta f (\<iota> t) = sink_delta f (\<Pi> (\<iota> t))"
    using u_sink_delta_commutes[OF s f0] by blast
  then show ?thesis by (simp add: \<Pi>_section)
qed

subsection \<open>0.2 The unified policy redrive: field extractors and the healing fact\<close>

lemma u_policy_redrive_journal:
  "u_policy_redrive P t f t' \<Longrightarrow> dwu_journal t' = dwu_journal t"
  by (simp add: u_policy_redrive_def)

lemma u_policy_redrive_floor:
  "u_policy_redrive P t f t' \<Longrightarrow> dwu_floor t' = dwu_floor t"
  by (simp add: u_policy_redrive_def)

lemma u_policy_redrive_fence:
  "u_policy_redrive P t f t' \<Longrightarrow> dwu_fence t' = dwu_fence t"
  by (simp add: u_policy_redrive_def)

lemma u_policy_redrive_hwm:
  "u_policy_redrive P t f t' \<Longrightarrow> dwu_hwm t' = dwu_hwm t"
  by (simp add: u_policy_redrive_def)

lemma u_policy_redrive_sent:
  "u_policy_redrive P t f t' \<Longrightarrow>
     dwu_sent t' = dwu_sent t @ stamped_at (length (dwu_journal t)) (dwu_hwm t) (P t)"
  by (simp add: u_policy_redrive_def)

lemma u_policy_redrive_accepted:
  "u_policy_redrive P t f t' \<Longrightarrow>
     dwu_accepted t' = dwu_accepted t
       @ filter (\<lambda>x. dwu_fence t \<le> ue_gen x)
           (stamped_at (length (dwu_journal t)) (dwu_hwm t) (P t))"
  by (simp add: u_policy_redrive_def)

lemma u_policy_redrive_src:
  "u_policy_redrive P t f t' \<Longrightarrow>
     exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t)"
  by (simp add: u_policy_redrive_def)

lemma u_policy_redrive_scope:
  "u_policy_redrive P t f t' \<Longrightarrow>
     exec_scope (dwu_store t') = exec_scope (dwu_store t)"
  by (simp add: u_policy_redrive_def)

lemma u_policy_redrive_exists:
  assumes "\<exists>c. exec_status (dwu_store t) = Crashed c"
      and "f \<le> exec_finish (dwu_store t)"
  shows "\<exists>t'. u_policy_redrive P t f t'"
  using assms unfolding u_policy_redrive_def by blast

text \<open>The redrive installs the relay heal image on the store, so it heals every
  scoped mismatch at its own frontier (the landed heal chain, store-lifted).\<close>

lemma u_policy_redrive_heals:
  assumes "u_policy_redrive P t f t'"
  shows "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t') f) f k"
proof -
  have "relay_bounded_replay_reconcile (dwu_store t) f (dwu_store t')"
    using assms by (simp add: u_policy_redrive_def relay_bounded_replay_reconcile_def)
  from relay_bounded_replay_reconcile_effective[OF this]
  show ?thesis by (rule recovery_effective_redelivery_no_mismatch)
qed

text \<open>On a @{term "\<iota> t"}-state (fence 0, ledgers = @{const ulift} images) the
  redriven accepted ledger's payload list is the old landed payloads followed by
  the whole policy batch --- the stamp/hwm are erased by
  @{thm log_payloads_stamped_at}, the fence keeps every entry.\<close>

lemma log_payloads_redrive_\<iota>:
  assumes "u_policy_redrive P (\<iota> t) f t'"
  shows "log_payloads (dwu_accepted t') = map e_payload (dwe_emitted t) @ P (\<iota> t)"
proof -
  have "dwu_accepted t'
      = map ulift (dwe_emitted t)
        @ stamped_at (length (dwu_journal (\<iota> t))) (dwu_hwm (\<iota> t)) (P (\<iota> t))"
    using u_policy_redrive_accepted[OF assms] by (simp add: \<iota>_accepted \<iota>_fence)
  then show ?thesis by (simp add: log_payloads_append)
qed

subsection \<open>0.3 Justification append-stability and machine-wide ledger append\<close>

text \<open>A stamp bounded by the current journal is verdict-stable under any journal
  extension with the base frozen --- BOTH the ULog and the USnap clause freeze
  (the USnap clause reads @{const exec_base} and a journal prefix).\<close>

lemma u_justified_append_stable:
  assumes bnd: "ue_stamp x \<le> length (dwu_journal t)"
      and jr: "dwu_journal t' = dwu_journal t @ ext"
      and bs: "exec_base (dwu_store t') = exec_base (dwu_store t)"
  shows "u_justified t' x \<longleftrightarrow> u_justified t x"
proof -
  have tk: "take (ue_stamp x) (dwu_journal t') = take (ue_stamp x) (dwu_journal t)"
    using bnd by (simp add: jr)
  have le: "ue_stamp x \<le> length (dwu_journal t')" using bnd by (simp add: jr)
  show ?thesis
    unfolding u_justified_def by (simp add: tk le bnd bs split: upayload.split)
qed

lemma u_accepted_single_writer:
  assumes "dwu_step t \<alpha> t'"
  shows "dwu_accepted t' = dwu_accepted t
       \<or> (\<exists>es. dwu_accepted t' = dwu_accepted t @ es)"
  using assms by (induction rule: dwu_step.induct) auto

lemma u_accepted_append_only:
  assumes "dwu_step t \<alpha> t'"
  shows "\<exists>es. dwu_accepted t' = dwu_accepted t @ es"
  using u_accepted_single_writer[OF assms] by (metis append_Nil2)

text \<open>The two anti-healing preservation facts, parameterized on the append/base
  frame (so they apply to any writer): a journal-bounded premature verdict
  freezes through a journal extension with the base frozen, a duplicate freezes
  through any accepted extension.\<close>

lemma u_premature_preserved:
  assumes bnd: "\<forall>x \<in> set (dwu_accepted t). ue_stamp x \<le> length (dwu_journal t)"
      and pre: "u_premature t"
      and acc: "\<exists>es. dwu_accepted t' = dwu_accepted t @ es"
      and jour: "\<exists>ext. dwu_journal t' = dwu_journal t @ ext"
      and base: "exec_base (dwu_store t') = exec_base (dwu_store t)"
  shows "u_premature t'"
proof -
  from pre obtain x where x: "x \<in> set (dwu_accepted t)" and nj: "\<not> u_justified t x"
    unfolding u_premature_def by blast
  from acc obtain es where es: "dwu_accepted t' = dwu_accepted t @ es" by blast
  from jour obtain ext where ext: "dwu_journal t' = dwu_journal t @ ext" by blast
  have bx: "ue_stamp x \<le> length (dwu_journal t)" using bnd x by blast
  have "\<not> u_justified t' x"
    using u_justified_append_stable[OF bx ext base] nj by simp
  moreover have "x \<in> set (dwu_accepted t')" using x es by simp
  ultimately show ?thesis unfolding u_premature_def by blast
qed

lemma u_duplicate_preserved:
  assumes dup: "u_duplicate t"
      and acc: "\<exists>es. dwu_accepted t' = dwu_accepted t @ es"
  shows "u_duplicate t'"
proof -
  from acc obtain es where es: "dwu_accepted t' = dwu_accepted t @ es" by blast
  show ?thesis using dup unfolding u_duplicate_def es by (simp add: log_payloads_append)
qed


section \<open>1. U4 — the dilemma trio (R1 / R2 / R3-strengthened)\<close>

subsection \<open>1.1 U4a: the batch-agreement kernel (R1)\<close>

text \<open>The unified batch-agreement dilemma, at the embedded equal-control-plane
  divergent-ledger pair @{term "\<iota> d1_w"} / @{term "\<iota> d2_w"}: reachable, equal on
  all six control-plane coordinates (store / journal / fence / gens / hwm /
  floor --- gens via S1's determination, both epoch 1), divergent ledgers, both
  effect-safe, both genuinely emitting.  Every policy that agrees on the pair
  emits the same batch @{term B}; the landed 3-case horn (empty \<Rightarrow> loss,
  re-fire \<Rightarrow> duplicate, alien \<Rightarrow> premature) transplants, both redrives heal.\<close>

theorem u_batch_agreement_dilemma:
  "\<exists>t1 t2.
     dwu_reachable_w t1 \<and> dwu_reachable_w t2
   \<and> dwu_store t1 = dwu_store t2
   \<and> dwu_journal t1 = dwu_journal t2
   \<and> dwu_fence t1 = dwu_fence t2
   \<and> dwu_gens t1 = dwu_gens t2
   \<and> dwu_hwm t1 = dwu_hwm t2
   \<and> dwu_floor t1 = dwu_floor t2
   \<and> dwu_sent t1 \<noteq> dwu_sent t2
   \<and> dwu_accepted t1 \<noteq> dwu_accepted t2
   \<and> \<not> u_effect_unsafe t1 \<and> \<not> u_effect_unsafe t2
   \<and> u_genuinely_emitting t1 \<and> u_genuinely_emitting t2
   \<and> (\<forall>P. P t1 = P t2 \<longrightarrow>
        (\<exists>t1' t2'.
           u_policy_redrive P t1 ec2 t1'
         \<and> u_policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t2') ec2) ec2 k)
         \<and> (u_effect_unsafe t1' \<or> u_lost ec2 t2')))"
proof -
  have R1: "dwu_reachable_w (\<iota> d1_w)" by (rule u_reachable_pullback[OF reach_d1])
  have R2: "dwu_reachable_w (\<iota> d2_w)" by (rule u_reachable_pullback[OF reach_d2])
  have ST: "dwu_store (\<iota> d1_w) = dwu_store (\<iota> d2_w)" by (simp add: d_cores_eq)
  have JN: "dwu_journal (\<iota> d1_w) = dwu_journal (\<iota> d2_w)" by (simp add: d_cores_eq)
  have FN: "dwu_fence (\<iota> d1_w) = dwu_fence (\<iota> d2_w)" by simp
  have GN: "dwu_gens (\<iota> d1_w) = dwu_gens (\<iota> d2_w)" by (simp add: d1_fields d2_fields)
  have HW: "dwu_hwm (\<iota> d1_w) = dwu_hwm (\<iota> d2_w)" by (simp add: d1_fields d2_fields)
  have FL: "dwu_floor (\<iota> d1_w) = dwu_floor (\<iota> d2_w)" by simp
  have SN: "dwu_sent (\<iota> d1_w) \<noteq> dwu_sent (\<iota> d2_w)"
    by (simp add: \<iota>_sent d1_fields d2_fields)
  have AN: "dwu_accepted (\<iota> d1_w) \<noteq> dwu_accepted (\<iota> d2_w)"
    by (simp add: \<iota>_accepted d1_fields d2_fields)
  have SF1: "\<not> u_effect_unsafe (\<iota> d1_w)" by (simp add: d1_not_unsafe)
  have SF2: "\<not> u_effect_unsafe (\<iota> d2_w)" by (simp add: d2_not_unsafe)
  have GE1: "u_genuinely_emitting (\<iota> d1_w)" by (simp add: d1_emitting)
  have GE2: "u_genuinely_emitting (\<iota> d2_w)" by (simp add: d2_emitting)
  have inner: "\<forall>P. P (\<iota> d1_w) = P (\<iota> d2_w) \<longrightarrow>
        (\<exists>t1' t2'.
           u_policy_redrive P (\<iota> d1_w) ec2 t1'
         \<and> u_policy_redrive P (\<iota> d2_w) ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t2') ec2) ec2 k)
         \<and> (u_effect_unsafe t1' \<or> u_lost ec2 t2'))"
  proof (intro allI impI)
    fix P :: "(nat, nat) dwu_state \<Rightarrow> (src_coord \<times> (nat, nat) source_event) list"
    assume PB: "P (\<iota> d1_w) = P (\<iota> d2_w)"
    define B where "B = P (\<iota> d1_w)"

    \<comment> \<open>the two policy redrives at the frontier ec2\<close>
    have grd1: "\<exists>c. exec_status (dwu_store (\<iota> d1_w)) = Crashed c" by (simp add: d1_fields)
    have grd2: "\<exists>c. exec_status (dwu_store (\<iota> d2_w)) = Crashed c" by (simp add: d2_fields)
    have fin1: "ec2 \<le> exec_finish (dwu_store (\<iota> d1_w))" by (simp add: d1_fields)
    have fin2: "ec2 \<le> exec_finish (dwu_store (\<iota> d2_w))" by (simp add: d2_fields)
    obtain t1' where pr1: "u_policy_redrive P (\<iota> d1_w) ec2 t1'"
      using u_policy_redrive_exists[OF grd1 fin1] by blast
    obtain t2' where pr2: "u_policy_redrive P (\<iota> d2_w) ec2 t2'"
      using u_policy_redrive_exists[OF grd2 fin2] by blast

    \<comment> \<open>the safe-side accepted ledger's payload list (the stamp is erased by
        @{thm log_payloads_stamped_at}, so no length numeral is needed)\<close>
    have pay1: "log_payloads (dwu_accepted t1') = [(ec1, e1), (ec2, e2)] @ B"
      using log_payloads_redrive_\<iota>[OF pr1] by (simp add: d1_fields e_payload_def B_def)

    \<comment> \<open>the skip-side replay: floor 0, heal-frozen source and scope\<close>
    have replay2: "replay_down_hist (retained_hist t2')
                     (exec_scope (dwu_store t2')) ec2 = [(ec1, e1), (ec2, e2)]"
      using u_policy_redrive_floor[OF pr2] u_policy_redrive_src[OF pr2]
            u_policy_redrive_scope[OF pr2]
      by (simp del: One_nat_def
               add: retained_hist_def \<iota>_store d2_fields replay_pair_eval)

    \<comment> \<open>the three total cases on the shared batch @{term B}\<close>
    have horn: "u_effect_unsafe t1' \<or> u_lost ec2 t2'"
    proof (cases "B = []")
      case True
      have P2: "P (\<iota> d2_w) = []" using PB True B_def by metis
      have lp2: "log_payloads (dwu_accepted t2') = [(ec1, e1)]"
        using log_payloads_redrive_\<iota>[OF pr2] P2 by (simp add: d2_fields e_payload_def)
      have "u_lost ec2 t2'"
        unfolding u_lost_def using replay2 lp2 by (auto simp: e1_def e2_def ec_defs)
      then show ?thesis ..
    next
      case False
      then obtain p0 where p0: "p0 \<in> set B" by (cases B) auto
      show ?thesis
      proof (cases "\<exists>p \<in> set B. p \<in> {(ec1, e1), (ec2, e2)}")
        case True
        have "\<not> distinct (log_payloads (dwu_accepted t1'))"
          unfolding pay1 using True by (auto simp: e1_def e2_def ec_defs)
        then have "u_effect_unsafe t1'"
          by (simp add: u_effect_unsafe_def u_duplicate_def)
        then show ?thesis ..
      next
        case False
        have p0_out: "p0 \<notin> {(ec1, e1), (ec2, e2)}" using False p0 by blast
        obtain c e where p_eq: "p0 = (c, e)" by (cases p0)
        define x where "x = \<lparr> ue_stamp = length (dwu_journal (\<iota> d1_w)),
                              ue_gen = dwu_hwm (\<iota> d1_w), ue_pay = ULog (c, e) \<rparr>"
        have x_in: "x \<in> set (dwu_accepted t1')"
          using p0 p_eq u_policy_redrive_accepted[OF pr1]
          by (auto simp: \<iota>_accepted \<iota>_fence stamped_at_def x_def B_def)
        have "\<not> u_justified t1' x"
          using p0_out p_eq
          by (simp add: u_justified_def x_def u_policy_redrive_journal[OF pr1]
                        \<iota>_journal d1_fields e1_def e2_def ec_defs)
        then have "u_premature t1'"
          unfolding u_premature_def using x_in by blast
        then have "u_effect_unsafe t1'" by (simp add: u_effect_unsafe_def)
        then show ?thesis ..
      qed
    qed

    have heal1: "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t1') ec2) ec2 k"
      by (rule u_policy_redrive_heals[OF pr1])
    have heal2: "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t2') ec2) ec2 k"
      by (rule u_policy_redrive_heals[OF pr2])

    show "\<exists>t1' t2'.
           u_policy_redrive P (\<iota> d1_w) ec2 t1'
         \<and> u_policy_redrive P (\<iota> d2_w) ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t2') ec2) ec2 k)
         \<and> (u_effect_unsafe t1' \<or> u_lost ec2 t2')"
      using pr1 pr2 heal1 heal2 horn by blast
  qed
  show ?thesis
    using R1 R2 ST JN FN GN HW FL SN AN SF1 SF2 GE1 GE2 inner by blast
qed

subsection \<open>1.2 U4b: the store-measured face (R2)\<close>

text \<open>Every store-measured policy agrees on the pair (equal stores), so the
  batch-agreement kernel fires --- one policy defeat per store-measured @{term P}.\<close>

theorem u_recovery_information_dilemma:
  "\<forall>P. u_store_measured P \<longrightarrow>
     (\<exists>t1 t2 t1' t2'.
        dwu_reachable_w t1 \<and> dwu_reachable_w t2
      \<and> dwu_store t1 = dwu_store t2
      \<and> dwu_sent t1 \<noteq> dwu_sent t2
      \<and> \<not> u_effect_unsafe t1 \<and> \<not> u_effect_unsafe t2
      \<and> u_genuinely_emitting t1 \<and> u_genuinely_emitting t2
      \<and> u_policy_redrive P t1 ec2 t1'
      \<and> u_policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t2') ec2) ec2 k)
      \<and> (u_effect_unsafe t1' \<or> u_lost ec2 t2'))"
proof (intro allI impI)
  fix P :: "(nat, nat) dwu_state \<Rightarrow> (src_coord \<times> (nat, nat) source_event) list"
  assume sm: "u_store_measured P"
  from u_batch_agreement_dilemma obtain t1 t2 where
      r1: "dwu_reachable_w t1" and r2: "dwu_reachable_w t2"
      and st: "dwu_store t1 = dwu_store t2"
      and sn: "dwu_sent t1 \<noteq> dwu_sent t2"
      and sf1: "\<not> u_effect_unsafe t1" and sf2: "\<not> u_effect_unsafe t2"
      and ge1: "u_genuinely_emitting t1" and ge2: "u_genuinely_emitting t2"
      and DEF: "\<forall>P. P t1 = P t2 \<longrightarrow>
        (\<exists>t1' t2'.
           u_policy_redrive P t1 ec2 t1'
         \<and> u_policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t2') ec2) ec2 k)
         \<and> (u_effect_unsafe t1' \<or> u_lost ec2 t2'))"
    by blast
  from sm obtain g where g: "\<forall>t. P t = g (dwu_store t)"
    unfolding u_store_measured_def by blast
  have PB: "P t1 = P t2" using g st by metis
  from DEF[rule_format, OF PB] obtain t1' t2' where
    D: "u_policy_redrive P t1 ec2 t1'
      \<and> u_policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t2') ec2) ec2 k)
      \<and> (u_effect_unsafe t1' \<or> u_lost ec2 t2')" by blast
  show "\<exists>t1 t2 t1' t2'.
        dwu_reachable_w t1 \<and> dwu_reachable_w t2
      \<and> dwu_store t1 = dwu_store t2
      \<and> dwu_sent t1 \<noteq> dwu_sent t2
      \<and> \<not> u_effect_unsafe t1 \<and> \<not> u_effect_unsafe t2
      \<and> u_genuinely_emitting t1 \<and> u_genuinely_emitting t2
      \<and> u_policy_redrive P t1 ec2 t1'
      \<and> u_policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t2') ec2) ec2 k)
      \<and> (u_effect_unsafe t1' \<or> u_lost ec2 t2')"
    using r1 r2 st sn sf1 sf2 ge1 ge2 D by blast
qed

subsection \<open>1.3 U4c: the control-plane-measured dilemma (R3 STRENGTHENED)\<close>

text \<open>The genuinely-stronger face: reading the WHOLE control plane
  (@{const u_control_plane_view} = store / LSN / fence / incarnation table /
  hwm / floor --- everything except the two ledgers) still fails to arbitrate,
  because the embedded pair is equal on every control-plane coordinate.\<close>

theorem u_control_plane_measured_dilemma:
  "\<forall>P. u_control_plane_measured P \<longrightarrow>
     (\<exists>t1 t2 t1' t2'.
        dwu_reachable_w t1 \<and> dwu_reachable_w t2
      \<and> u_control_plane_view t1 = u_control_plane_view t2
      \<and> dwu_sent t1 \<noteq> dwu_sent t2
      \<and> \<not> u_effect_unsafe t1 \<and> \<not> u_effect_unsafe t2
      \<and> u_genuinely_emitting t1 \<and> u_genuinely_emitting t2
      \<and> u_policy_redrive P t1 ec2 t1'
      \<and> u_policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t2') ec2) ec2 k)
      \<and> (u_effect_unsafe t1' \<or> u_lost ec2 t2'))"
proof (intro allI impI)
  fix P :: "(nat, nat) dwu_state \<Rightarrow> (src_coord \<times> (nat, nat) source_event) list"
  assume cm: "u_control_plane_measured P"
  from u_batch_agreement_dilemma obtain t1 t2 where
      r1: "dwu_reachable_w t1" and r2: "dwu_reachable_w t2"
      and st: "dwu_store t1 = dwu_store t2"
      and jn: "dwu_journal t1 = dwu_journal t2"
      and fn: "dwu_fence t1 = dwu_fence t2"
      and gn: "dwu_gens t1 = dwu_gens t2"
      and hw: "dwu_hwm t1 = dwu_hwm t2"
      and fl: "dwu_floor t1 = dwu_floor t2"
      and sn: "dwu_sent t1 \<noteq> dwu_sent t2"
      and sf1: "\<not> u_effect_unsafe t1" and sf2: "\<not> u_effect_unsafe t2"
      and ge1: "u_genuinely_emitting t1" and ge2: "u_genuinely_emitting t2"
      and DEF: "\<forall>P. P t1 = P t2 \<longrightarrow>
        (\<exists>t1' t2'.
           u_policy_redrive P t1 ec2 t1'
         \<and> u_policy_redrive P t2 ec2 t2'
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t1') ec2) ec2 k)
         \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t2') ec2) ec2 k)
         \<and> (u_effect_unsafe t1' \<or> u_lost ec2 t2'))"
    by blast
  have VIEW: "u_control_plane_view t1 = u_control_plane_view t2"
    using st jn fn gn hw fl by (simp add: u_control_plane_view_def)
  from cm obtain g where g: "\<forall>t. P t = g (u_control_plane_view t)"
    unfolding u_control_plane_measured_def by blast
  have PB: "P t1 = P t2" using g VIEW by metis
  from DEF[rule_format, OF PB] obtain t1' t2' where
    D: "u_policy_redrive P t1 ec2 t1'
      \<and> u_policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t2') ec2) ec2 k)
      \<and> (u_effect_unsafe t1' \<or> u_lost ec2 t2')" by blast
  show "\<exists>t1 t2 t1' t2'.
        dwu_reachable_w t1 \<and> dwu_reachable_w t2
      \<and> u_control_plane_view t1 = u_control_plane_view t2
      \<and> dwu_sent t1 \<noteq> dwu_sent t2
      \<and> \<not> u_effect_unsafe t1 \<and> \<not> u_effect_unsafe t2
      \<and> u_genuinely_emitting t1 \<and> u_genuinely_emitting t2
      \<and> u_policy_redrive P t1 ec2 t1'
      \<and> u_policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t2') ec2) ec2 k)
      \<and> (u_effect_unsafe t1' \<or> u_lost ec2 t2')"
    using r1 r2 VIEW sn sf1 sf2 ge1 ge2 D by blast
qed


section \<open>2. U5 — the sink-reading escape (R4) + the not-measured face (R5)\<close>

subsection \<open>2.1 U5: the escape, with its two explicit premises (R4)\<close>

text \<open>The sink-delta policy heals, never duplicates, never goes premature and
  never loses, from EVERY effect-safe crashed permanent-source state with a
  strictly-ascending committed source and the fence below the hwm.  The two
  extra premises the pin adds are load-bearing for the TWO-HISTORY object: the
  delta reads @{const retained_hist} while justification reads the journal, so
  @{const u_permanent_source} (journal = source, floor 0) co-houses them, and
  @{term "dwu_fence W \<le> dwu_hwm W"} makes the fresh batch land in accepted.  Both
  are vacuous on @{const solo_inv} states.\<close>

theorem u_sink_reading_escape:
  fixes W :: "(nat, nat) dwu_state"
  assumes "\<not> u_effect_unsafe W"
      and "\<exists>c. exec_status (dwu_store W) = Crashed c"
      and "f \<le> exec_finish (dwu_store W)"
      and "strictly_ascending_source (exec_src_hist (dwu_store W))"
      and "u_permanent_source W"
      and "dwu_fence W \<le> dwu_hwm W"
  shows "(\<exists>W'. u_policy_redrive (u_sink_delta f) W f W')
       \<and> (\<forall>W'. u_policy_redrive (u_sink_delta f) W f W' \<longrightarrow>
            (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store W') f) f k)
          \<and> \<not> u_effect_unsafe W'
          \<and> \<not> u_lost f W')"
proof (rule conjI)
  show "\<exists>W'. u_policy_redrive (u_sink_delta f) W f W'"
    using u_policy_redrive_exists[OF assms(2) assms(3)] by blast
next
  show "\<forall>W'. u_policy_redrive (u_sink_delta f) W f W' \<longrightarrow>
          (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store W') f) f k)
        \<and> \<not> u_effect_unsafe W' \<and> \<not> u_lost f W'"
  proof (intro allI impI)
    fix W' assume pr: "u_policy_redrive (u_sink_delta f) W f W'"
    note safe = assms(1) and asc = assms(4) and perm = assms(5) and fence = assms(6)
    \<comment> \<open>the permanent-source unfolding: journal = source, floor 0\<close>
    have permJ: "dwu_journal W = exec_src_hist (dwu_store W)"
      using perm by (simp add: u_permanent_source_def)
    have permF: "dwu_floor W = 0" using perm by (simp add: u_permanent_source_def)
    \<comment> \<open>the redrive's frozen frame\<close>
    have jW': "dwu_journal W' = dwu_journal W" by (rule u_policy_redrive_journal[OF pr])
    have baseW': "exec_base (dwu_store W') = exec_base (dwu_store W)"
      using pr by (simp add: u_policy_redrive_def)
    \<comment> \<open>the delta reads the (floor-0) retained history = the source\<close>
    have D_eq: "u_sink_delta f W =
        filter (\<lambda>p. p \<notin> set (log_payloads (dwu_accepted W)))
          (replay_down_hist (exec_src_hist (dwu_store W)) (exec_scope (dwu_store W)) f)"
      by (simp add: u_sink_delta_def retained_hist_def permF)
    \<comment> \<open>fence \<le> hwm keeps every stamped entry: accepted gains the whole delta\<close>
    have keep: "filter (\<lambda>x. dwu_fence W \<le> ue_gen x)
          (stamped_at (length (dwu_journal W)) (dwu_hwm W) (u_sink_delta f W))
        = stamped_at (length (dwu_journal W)) (dwu_hwm W) (u_sink_delta f W)"
      using fence by (auto simp: stamped_at_def filter_id_conv)
    have accW': "dwu_accepted W' = dwu_accepted W
        @ stamped_at (length (dwu_journal W)) (dwu_hwm W) (u_sink_delta f W)"
      using u_policy_redrive_accepted[OF pr] keep by simp
    have lpW': "log_payloads (dwu_accepted W')
        = log_payloads (dwu_accepted W) @ u_sink_delta f W"
      by (simp add: accW' log_payloads_append)
    \<comment> \<open>distinctness pipeline from the ascending premise\<close>
    have distS: "distinct (exec_src_hist (dwu_store W))"
      by (rule strictly_ascending_distinct[OF asc])
    have distR: "distinct (replay_down_hist (exec_src_hist (dwu_store W))
                   (exec_scope (dwu_store W)) f)"
      unfolding replay_down_hist_def using distS by simp
    have distD: "distinct (u_sink_delta f W)" by (simp add: D_eq distR)
    have disj: "set (log_payloads (dwu_accepted W)) \<inter> set (u_sink_delta f W) = {}"
      by (auto simp: D_eq)

    \<comment> \<open>NOT premature: old verdicts frozen, new entries source-justified\<close>
    have oldjust: "\<forall>x \<in> set (dwu_accepted W). u_justified W' x"
    proof
      fix x assume x: "x \<in> set (dwu_accepted W)"
      have jx: "u_justified W x"
        using safe x by (auto simp: u_effect_unsafe_def u_premature_def)
      then have bnd: "ue_stamp x \<le> length (dwu_journal W)" by (simp add: u_justified_def)
      have jr': "dwu_journal W' = dwu_journal W @ []" by (simp add: jW')
      show "u_justified W' x"
        using u_justified_append_stable[OF bnd jr' baseW'] jx by simp
    qed
    have newjust: "\<forall>x \<in> set (stamped_at (length (dwu_journal W)) (dwu_hwm W)
                        (u_sink_delta f W)). u_justified W' x"
    proof
      fix x assume "x \<in> set (stamped_at (length (dwu_journal W)) (dwu_hwm W)
                        (u_sink_delta f W))"
      then obtain p where p: "p \<in> set (u_sink_delta f W)"
          and xdef: "x = \<lparr> ue_stamp = length (dwu_journal W),
                            ue_gen = dwu_hwm W, ue_pay = ULog p \<rparr>"
        by (auto simp: stamped_at_def)
      have pR: "p \<in> set (replay_down_hist (exec_src_hist (dwu_store W))
                   (exec_scope (dwu_store W)) f)"
        using p by (simp add: D_eq)
      then have pS: "p \<in> set (exec_src_hist (dwu_store W))"
        using replay_down_hist_subset by blast
      show "u_justified W' x"
        unfolding u_justified_def xdef by (simp add: jW' permJ pS)
    qed
    have not_prem: "\<not> u_premature W'"
      unfolding u_premature_def using oldjust newjust by (auto simp: accW')

    \<comment> \<open>NOT duplicate: old distinct, delta distinct, disjoint by the filter\<close>
    have olddist: "distinct (log_payloads (dwu_accepted W))"
      using safe by (auto simp: u_effect_unsafe_def u_duplicate_def)
    have not_dup: "\<not> u_duplicate W'"
      unfolding u_duplicate_def lpW'
      using olddist distD disj by (simp add: distinct_append)

    \<comment> \<open>NOT lost: every replay payload is old or kept by the filter\<close>
    have replayW': "replay_down_hist (retained_hist W') (exec_scope (dwu_store W')) f
        = replay_down_hist (exec_src_hist (dwu_store W)) (exec_scope (dwu_store W)) f"
      using u_policy_redrive_floor[OF pr] u_policy_redrive_src[OF pr]
            u_policy_redrive_scope[OF pr] permF
      by (simp add: retained_hist_def)
    have not_lost: "\<not> u_lost f W'"
      unfolding u_lost_def
    proof
      assume "\<exists>p \<in> set (replay_down_hist (retained_hist W') (exec_scope (dwu_store W')) f).
                 p \<notin> set (log_payloads (dwu_accepted W'))"
      then obtain p where pin: "p \<in> set (replay_down_hist (exec_src_hist (dwu_store W))
                                    (exec_scope (dwu_store W)) f)"
          and pout: "p \<notin> set (log_payloads (dwu_accepted W'))"
        using replayW' by auto
      have "p \<notin> set (log_payloads (dwu_accepted W))" using pout lpW' by simp
      then have "p \<in> set (u_sink_delta f W)" using pin by (simp add: D_eq)
      then have "p \<in> set (log_payloads (dwu_accepted W'))" by (simp add: lpW')
      with pout show False by simp
    qed

    show "(\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store W') f) f k)
        \<and> \<not> u_effect_unsafe W' \<and> \<not> u_lost f W'"
      using u_policy_redrive_heals[OF pr] not_prem not_dup not_lost
      by (simp add: u_effect_unsafe_def)
  qed
qed

subsection \<open>2.2 U5b: the escape is not store- / control-plane-measured (R5)\<close>

text \<open>On the dilemma pair the delta is @{term "[]"} on the safe side and
  @{term "[(ec2, e2)]"} on the skip side --- so no function of the store, nor of
  the WHOLE control plane, computes it (only the accepted ledger separates the
  pair).\<close>

lemma u_sink_delta_d1: "u_sink_delta ec2 (\<iota> d1_w) = []"
  by (simp add: u_sink_delta_\<iota> sink_delta_def d1_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs)

lemma u_sink_delta_d2: "u_sink_delta ec2 (\<iota> d2_w) = [(ec2, e2)]"
  by (simp add: u_sink_delta_\<iota> sink_delta_def d2_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs)

theorem u_escape_not_store_measured:
  "\<not> u_store_measured (u_sink_delta ec2)"
proof
  assume "u_store_measured (u_sink_delta ec2)"
  \<comment> \<open>the equal stores force equal deltas --- but the deltas differ\<close>
  have store_eq: "dwu_store (\<iota> d1_w) = dwu_store (\<iota> d2_w)" by (simp add: d_cores_eq)
  from \<open>u_store_measured (u_sink_delta ec2)\<close>
  have "u_sink_delta ec2 (\<iota> d1_w) = u_sink_delta ec2 (\<iota> d2_w)"
    unfolding u_store_measured_def using store_eq by metis
  then show False using u_sink_delta_d1 u_sink_delta_d2 by simp
qed

theorem u_escape_not_control_plane_measured:
  "\<not> u_control_plane_measured (u_sink_delta ec2)"
proof
  assume "u_control_plane_measured (u_sink_delta ec2)"
  have view_eq: "u_control_plane_view (\<iota> d1_w) = u_control_plane_view (\<iota> d2_w)"
    by (simp add: u_control_plane_view_def d_cores_eq d1_fields d2_fields)
  from \<open>u_control_plane_measured (u_sink_delta ec2)\<close>
  have "u_sink_delta ec2 (\<iota> d1_w) = u_sink_delta ec2 (\<iota> d2_w)"
    unfolding u_control_plane_measured_def using view_eq by metis
  then show False using u_sink_delta_d1 u_sink_delta_d2 by simp
qed


section \<open>3. U6 — anti-healing, MACHINE-WIDE incl. UTruncCrash (R7)\<close>

text \<open>Effect-unsafety is monotone under EVERY unified rule --- the journal and
  the accepted ledger only ever append (verified rule-by-rule inside
  @{thm u_journal_append_only} / @{thm u_accepted_append_only}), the base is
  unconditionally constant (@{thm u_exec_base_const} --- so the USnap
  justification clause freezes), and UTruncCrash truncates only the LIVE source,
  not the commit journal against which the verdict is read.  The journal-stamps
  premise stays load-bearing: the unconditional form is false (an over-stamped
  alien entry can become justified once the journal grows).\<close>

theorem u_effect_unsafe_monotone:
  assumes "\<forall>x \<in> set (dwu_accepted t). ue_stamp x \<le> length (dwu_journal t)"
      and "u_effect_unsafe t"
      and "dwu_step t \<alpha> t'"
  shows "u_effect_unsafe t'"
proof -
  have acc: "\<exists>es. dwu_accepted t' = dwu_accepted t @ es"
    by (rule u_accepted_append_only[OF assms(3)])
  have jour: "\<exists>ext. dwu_journal t' = dwu_journal t @ ext"
    by (rule u_journal_append_only[OF assms(3)])
  have base: "exec_base (dwu_store t') = exec_base (dwu_store t)"
    by (rule u_exec_base_const[OF assms(3)])
  from assms(2) show ?thesis
    unfolding u_effect_unsafe_def
    using u_premature_preserved[OF assms(1) _ acc jour base]
          u_duplicate_preserved[OF _ acc]
    by blast
qed

text \<open>Trace-persistent form: along ANY temporal trace, effect-unsafety persists
  under the journal-stamps invariant (S4), which is itself preserved step by
  step.\<close>

theorem u_effect_unsafe_trace_persistent:
  assumes "u_journal_stamps_bounded t"
      and "u_effect_unsafe t"
      and "dwu_temporal_trace t as t'"
  shows "u_effect_unsafe t'"
  using assms(3,1,2)
proof (induction rule: dwu_temporal_trace.induct)
  case (dwu_refl t)
  then show ?case by blast
next
  case (dwu_lift_step t a g t' as t'')
  have bnd: "\<forall>x \<in> set (dwu_accepted t). ue_stamp x \<le> length (dwu_journal t)"
    using dwu_lift_step.prems(1) by (simp add: u_journal_stamps_bounded_def)
  have un': "u_effect_unsafe t'"
    by (rule u_effect_unsafe_monotone[OF bnd dwu_lift_step.prems(2) dwu_lift_step.hyps(3)])
  have jsb': "u_journal_stamps_bounded t'"
    by (rule u_journal_stamps_bounded_step[OF dwu_lift_step.hyps(3) dwu_lift_step.prems(1)])
  show ?case by (rule dwu_lift_step.IH[OF jsb' un'])
next
  case (dwu_publost_step t c e g t' as t'')
  have bnd: "\<forall>x \<in> set (dwu_accepted t). ue_stamp x \<le> length (dwu_journal t)"
    using dwu_publost_step.prems(1) by (simp add: u_journal_stamps_bounded_def)
  have un': "u_effect_unsafe t'"
    by (rule u_effect_unsafe_monotone[OF bnd dwu_publost_step.prems(2) dwu_publost_step.hyps(3)])
  have jsb': "u_journal_stamps_bounded t'"
    by (rule u_journal_stamps_bounded_step[OF dwu_publost_step.hyps(3) dwu_publost_step.prems(1)])
  show ?case by (rule dwu_publost_step.IH[OF jsb' un'])
next
  case (dwu_other_step \<alpha> t t' as t'')
  have bnd: "\<forall>x \<in> set (dwu_accepted t). ue_stamp x \<le> length (dwu_journal t)"
    using dwu_other_step.prems(1) by (simp add: u_journal_stamps_bounded_def)
  have un': "u_effect_unsafe t'"
    by (rule u_effect_unsafe_monotone[OF bnd dwu_other_step.prems(2) dwu_other_step.hyps(3)])
  have jsb': "u_journal_stamps_bounded t'"
    by (rule u_journal_stamps_bounded_step[OF dwu_other_step.hyps(3) dwu_other_step.prems(1)])
  show ?case by (rule dwu_other_step.IH[OF jsb' un'])
qed


section \<open>4. U7 — the dedup layer + necessity face (R8)\<close>

subsection \<open>4.1 The @{const u_dedup_view} count algebra\<close>

lemma u_dedup_view_distinct: "distinct (u_dedup_view t)"
  by (simp add: u_dedup_view_def)

lemma u_dedup_view_set:
  "set (u_dedup_view t) = set (log_payloads (dwu_accepted t))"
  by (simp add: u_dedup_view_def)

lemma u_dedup_view_count:
  "count_list (u_dedup_view t) p
     = (if p \<in> set (log_payloads (dwu_accepted t)) then 1 else 0)"
  by (simp add: count_list_distinct_mem[OF u_dedup_view_distinct] u_dedup_view_set)

subsection \<open>4.2 Layer 1: the premise-free dedup-sink iff\<close>

text \<open>With a dedup sink the per-obligation executed count is 1 IFF delivery was
  at-least-once --- pure counting, true for every state (snaps are filtered out
  of @{const log_payloads} by construction, so they never enter the count).\<close>

theorem u_dedup_sink_exactly_once_iff_at_least_once:
  "(\<forall>p \<in> set (replay_down_hist (retained_hist t) (exec_scope (dwu_store t)) f).
      count_list (u_dedup_view t) p = 1)
   \<longleftrightarrow> u_at_least_once_at f t"
  by (auto simp: u_dedup_view_count u_at_least_once_at_def subset_iff)

subsection \<open>4.3 Layer 2: instance-level exactness under the ascending premise\<close>

lemma u_ascending_obligations_distinct:
  assumes "strictly_ascending_source (exec_src_hist (dwu_store t))"
  shows "distinct (replay_down_hist (retained_hist t) (exec_scope (dwu_store t)) f)"
proof -
  have "distinct (exec_src_hist (dwu_store t))"
    by (rule strictly_ascending_distinct[OF assms])
  then have "distinct (retained_hist t)"
    unfolding retained_hist_def by (metis append_take_drop_id distinct_append)
  then show ?thesis unfolding replay_down_hist_def by simp
qed

lemma u_instance_agreement_gives_at_least_once:
  assumes agree:
    "\<forall>p \<in> set (replay_down_hist (retained_hist t) (exec_scope (dwu_store t)) f).
       count_list (u_dedup_view t) p
         = count_list (replay_down_hist (retained_hist t)
                         (exec_scope (dwu_store t)) f) p"
  shows "u_at_least_once_at f t"
  unfolding u_at_least_once_at_def
proof
  fix p
  assume p: "p \<in> set (replay_down_hist (retained_hist t) (exec_scope (dwu_store t)) f)"
  have "count_list (replay_down_hist (retained_hist t)
          (exec_scope (dwu_store t)) f) p \<noteq> 0"
    using p by (simp add: count_list_0_iff)
  then have "count_list (u_dedup_view t) p \<noteq> 0" using agree p by simp
  then show "p \<in> set (log_payloads (dwu_accepted t))"
    by (simp add: u_dedup_view_count split: if_split_asm)
qed

theorem u_dedup_sink_instance_exact_iff:
  assumes "strictly_ascending_source (exec_src_hist (dwu_store t))"
  shows "(\<forall>p \<in> set (replay_down_hist (retained_hist t) (exec_scope (dwu_store t)) f).
            count_list (u_dedup_view t) p
              = count_list (replay_down_hist (retained_hist t)
                              (exec_scope (dwu_store t)) f) p)
       \<longleftrightarrow> u_at_least_once_at f t"
proof
  let ?R = "replay_down_hist (retained_hist t) (exec_scope (dwu_store t)) f"
  assume "\<forall>p \<in> set ?R. count_list (u_dedup_view t) p = count_list ?R p"
  then show "u_at_least_once_at f t"
    by (rule u_instance_agreement_gives_at_least_once)
next
  let ?R = "replay_down_hist (retained_hist t) (exec_scope (dwu_store t)) f"
  assume alo: "u_at_least_once_at f t"
  show "\<forall>p \<in> set ?R. count_list (u_dedup_view t) p = count_list ?R p"
  proof
    fix p assume p: "p \<in> set ?R"
    have obl: "count_list ?R p = 1"
      using u_ascending_obligations_distinct[OF assms] p
      by (simp add: count_list_distinct_mem)
    have "p \<in> set (log_payloads (dwu_accepted t))"
      using alo p by (auto simp: u_at_least_once_at_def)
    then have "count_list (u_dedup_view t) p = 1" by (simp add: u_dedup_view_count)
    with obl show "count_list (u_dedup_view t) p = count_list ?R p" by simp
  qed
qed

subsection \<open>4.4 The aliasing biting control, embedded at @{term "\<iota> dd4_w"}\<close>

text \<open>The landed @{const dd4_w} equal-coordinate chain, embedded via the U1
  pullback: reachable, NOT ascending, at-least-once at @{term ec1}, but the
  payload @{term "(ec1, e1)"} aliases two committed instances (replay count 2)
  while the dedup view executes it once --- instance exactness is off by one, the
  premise is load-bearing at a fragment-reachable state.\<close>

theorem u_aliasing_control_embedded:
  "dwu_reachable_w (\<iota> dd4_w)
 \<and> \<not> strictly_ascending_source (exec_src_hist (dwu_store (\<iota> dd4_w)))
 \<and> u_at_least_once_at ec1 (\<iota> dd4_w)
 \<and> count_list (replay_down_hist (retained_hist (\<iota> dd4_w))
                  (exec_scope (dwu_store (\<iota> dd4_w))) ec1) (ec1, e1) = 2
 \<and> count_list (u_dedup_view (\<iota> dd4_w)) (ec1, e1) = 1"
proof (intro conjI)
  show "dwu_reachable_w (\<iota> dd4_w)" by (rule u_reachable_pullback[OF reach_dd4])
next
  show "\<not> strictly_ascending_source (exec_src_hist (dwu_store (\<iota> dd4_w)))"
    using dd4_not_asc by simp
next
  show "u_at_least_once_at ec1 (\<iota> dd4_w)"
    using dd4_at_least_once by (simp add: u_at_least_once_\<iota>)
next
  show "count_list (replay_down_hist (retained_hist (\<iota> dd4_w))
                       (exec_scope (dwu_store (\<iota> dd4_w))) ec1) (ec1, e1) = 2"
    using dd4_replay_count by (simp add: retained_hist_def)
next
  show "count_list (u_dedup_view (\<iota> dd4_w)) (ec1, e1) = 1"
    using dd4_view_count by (simp add: u_dedup_view_def sink_dedup_view_def)
qed

subsection \<open>4.5 The necessity face: no store-measured recovery is exactly-once\<close>

text \<open>Consumes U4/R2's kernel EXACTLY as landed: the recovery-information horn
  (@{thm u_recovery_information_dilemma}) maps through
  @{const u_exactly_once_at} + @{thm u_at_least_once_iff_not_lost} to defeat
  every store-measured recovery policy.\<close>

theorem u_no_store_measured_exactly_once:
  "\<forall>P. u_store_measured P \<longrightarrow>
     (\<exists>t1 t2 t1' t2'.
        dwu_reachable_w t1 \<and> dwu_reachable_w t2
      \<and> dwu_store t1 = dwu_store t2
      \<and> \<not> u_effect_unsafe t1 \<and> \<not> u_effect_unsafe t2
      \<and> u_policy_redrive P t1 ec2 t1'
      \<and> u_policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t2') ec2) ec2 k)
      \<and> \<not> (u_exactly_once_at ec2 t1' \<and> u_exactly_once_at ec2 t2'))"
proof (intro allI impI)
  fix P :: "(nat, nat) dwu_state \<Rightarrow> (src_coord \<times> (nat, nat) source_event) list"
  assume sm: "u_store_measured P"
  from u_recovery_information_dilemma[rule_format, OF sm]
  obtain t1 t2 t1' t2' where D:
      "dwu_reachable_w t1 \<and> dwu_reachable_w t2
     \<and> dwu_store t1 = dwu_store t2
     \<and> dwu_sent t1 \<noteq> dwu_sent t2
     \<and> \<not> u_effect_unsafe t1 \<and> \<not> u_effect_unsafe t2
     \<and> u_genuinely_emitting t1 \<and> u_genuinely_emitting t2
     \<and> u_policy_redrive P t1 ec2 t1'
     \<and> u_policy_redrive P t2 ec2 t2'
     \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t1') ec2) ec2 k)
     \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t2') ec2) ec2 k)
     \<and> (u_effect_unsafe t1' \<or> u_lost ec2 t2')" by blast
  have neo: "\<not> (u_exactly_once_at ec2 t1' \<and> u_exactly_once_at ec2 t2')"
    using D by (auto simp: u_exactly_once_at_def u_at_least_once_iff_not_lost)
  show "\<exists>t1 t2 t1' t2'.
        dwu_reachable_w t1 \<and> dwu_reachable_w t2
      \<and> dwu_store t1 = dwu_store t2
      \<and> \<not> u_effect_unsafe t1 \<and> \<not> u_effect_unsafe t2
      \<and> u_policy_redrive P t1 ec2 t1'
      \<and> u_policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t2') ec2) ec2 k)
      \<and> \<not> (u_exactly_once_at ec2 t1' \<and> u_exactly_once_at ec2 t2')"
    using D neo by blast
qed


section \<open>5. R6 — landed T2.8 recovered by the solo-discipline pullback (STANDALONE)\<close>

text \<open>The solo discipline (P2/P3 re-routed pin): the four solo productions with
  the landed guards transported verbatim.  This block is DECOUPLED from U8 --- it
  routes T2.8 through @{term \<Pi>} + @{thm u_hazards_once}, NOT through any
  multi-writer @{text u_disciplined_trace} grammar.\<close>

inductive solo_disciplined_trace
  :: "('k, 'v) dwu_state \<Rightarrow> ('k, 'v) dwu_action list \<Rightarrow> ('k, 'v) dwe_action list
      \<Rightarrow> ('k, 'v) dwu_state \<Rightarrow> bool"
where
  sd_refl:
    "solo_disciplined_trace u [] [] u"
| sd_lift_nonpub:
    "\<lbrakk>wellformed_exec_state (dwu_store u);
      exec_label_preserves_history_wf (dwu_store u) a;
      \<forall>c e. a \<noteq> DoDownstream c e;
      dwu_step u (ULift (dwu_hwm u) a) u1;
      solo_disciplined_trace u1 ys zs u'\<rbrakk> \<Longrightarrow>
     solo_disciplined_trace u (ULift (dwu_hwm u) a # ys) (DWE_Label a # zs) u'"
| sd_lift_publish:
    "\<lbrakk>wellformed_exec_state (dwu_store u);
      exec_label_preserves_history_wf (dwu_store u) (DoDownstream c e);
      (c, e) \<in> set (dwu_journal u);
      (c, e) \<notin> set (log_payloads (dwu_accepted u));
      dwu_step u (ULift (dwu_hwm u) (DoDownstream c e)) u1;
      solo_disciplined_trace u1 ys zs u'\<rbrakk> \<Longrightarrow>
     solo_disciplined_trace u (ULift (dwu_hwm u) (DoDownstream c e) # ys)
       (DWE_Label (DoDownstream c e) # zs) u'"
| sd_reconcile:
    "\<lbrakk>g = dwu_hwm u;
      R = replay_down_hist (retained_hist u) (exec_scope (dwu_store u)) f;
      m \<le> length R;
      distinct (drop m R);
      set (drop m R) \<inter> set (log_payloads (dwu_accepted u)) = {};
      B = stamped_at (length (dwu_journal u)) g (drop m R);
      dwu_step u (UArm g B f) u1;
      dwu_step u1 (UHeal g f) u2;
      dwu_step u2 (UFire g) u3;
      solo_disciplined_trace u3 ys zs u'\<rbrakk> \<Longrightarrow>
     solo_disciplined_trace u (UArm g B f # UHeal g f # UFire g # ys)
       (DWE_Reconcile m f # zs) u'"
| sd_turnover:
    "\<lbrakk>dwu_step u USpawn u1;
      dwu_step u1 (URelease (dwu_hwm u1)) u2;
      solo_disciplined_trace u2 ys zs u'\<rbrakk> \<Longrightarrow>
     solo_disciplined_trace u (USpawn # URelease (dwu_hwm u1) # ys)
       (DWE_Resume # zs) u'"

text \<open>@{term \<Pi>} of @{const dwu_init} is @{const dwe_init} (section law + init
  alignment).\<close>

lemma \<Pi>_init: "\<Pi> (dwu_init b K fin) = dwe_init b K fin"
  by (metis \<iota>_init \<Pi>_section)

subsection \<open>5.1 The forward projection: solo discipline projects to landed discipline\<close>

text \<open>Each solo-disciplined production projects to the landed
  @{const disciplined_trace} guard (under @{const solo_inv}: journal = source and
  @{text "log_payloads(accepted) = e_payload-image(Pi-emitted)"} make every
  transported guard literally the landed guard at @{term "\<Pi> u"}), threading the
  fragment invariant.\<close>

lemma solo_disc_project:
  assumes "solo_disciplined_trace u ys zs u'" and "solo_inv u"
  shows "disciplined_trace (\<Pi> u) zs (\<Pi> u') \<and> solo_inv u'"
  using assms
proof (induction rule: solo_disciplined_trace.induct)
  case (sd_refl u)
  show ?case using sd_refl.prems by (simp add: disciplined_trace.disciplined_refl)
next
  case (sd_lift_nonpub u a u1 ys zs u')
  from solo_lift_project[OF sd_lift_nonpub.hyps(4) sd_lift_nonpub.prems]
  have proj: "dwe_step (\<Pi> u) a (\<Pi> u1)" and inv1: "solo_inv u1" by simp_all
  from sd_lift_nonpub.IH[OF inv1]
  have tr: "disciplined_trace (\<Pi> u1) zs (\<Pi> u')" and inv': "solo_inv u'" by simp_all
  have wf: "wellformed_exec_state (dwe_core (\<Pi> u))"
    using sd_lift_nonpub.hyps(1) by simp
  have wfh: "exec_label_preserves_history_wf (dwe_core (\<Pi> u)) a"
    using sd_lift_nonpub.hyps(2) by simp
  have "disciplined_trace (\<Pi> u) (DWE_Label a # zs) (\<Pi> u')"
    by (rule disciplined_trace.disciplined_nonpub
              [OF proj wf wfh sd_lift_nonpub.hyps(3) tr])
  then show ?case using inv' by blast
next
  case (sd_lift_publish u c e u1 ys zs u')
  from solo_lift_project[OF sd_lift_publish.hyps(5) sd_lift_publish.prems]
  have proj: "dwe_step (\<Pi> u) (DoDownstream c e) (\<Pi> u1)" and inv1: "solo_inv u1"
    by simp_all
  from sd_lift_publish.IH[OF inv1]
  have tr: "disciplined_trace (\<Pi> u1) zs (\<Pi> u')" and inv': "solo_inv u'" by simp_all
  have js: "dwu_journal u = exec_src_hist (dwu_store u)"
    using sd_lift_publish.prems by (simp add: solo_inv_def)
  have sa: "dwu_sent u = dwu_accepted u"
    using sd_lift_publish.prems by (simp add: solo_inv_def)
  have wf: "wellformed_exec_state (dwe_core (\<Pi> u))"
    using sd_lift_publish.hyps(1) by simp
  have wfh: "exec_label_preserves_history_wf (dwe_core (\<Pi> u)) (DoDownstream c e)"
    using sd_lift_publish.hyps(2) by simp
  have mem1: "(c, e) \<in> set (exec_src_hist (dwe_core (\<Pi> u)))"
    using sd_lift_publish.hyps(3) js by simp
  have notmem: "(c, e) \<notin> e_payload ` set (dwe_emitted (\<Pi> u))"
    using sd_lift_publish.hyps(4) sa by (simp add: set_\<Pi>_emitted_payloads)
  have "disciplined_trace (\<Pi> u) (DWE_Label (DoDownstream c e) # zs) (\<Pi> u')"
    by (rule disciplined_trace.disciplined_publish[OF proj wf wfh mem1 notmem tr])
  then show ?case using inv' by blast
next
  case (sd_reconcile g u R f m B u1 u2 u3 ys zs u')
  from solo_reconcile_project[OF sd_reconcile.prems sd_reconcile.hyps(1)
        sd_reconcile.hyps(2) sd_reconcile.hyps(3) sd_reconcile.hyps(6)
        sd_reconcile.hyps(7) sd_reconcile.hyps(8) sd_reconcile.hyps(9)]
  have er: "emitting_reconcile m (\<Pi> u) f (\<Pi> u3)" and inv3: "solo_inv u3" by simp_all
  from sd_reconcile.IH[OF inv3]
  have tr: "disciplined_trace (\<Pi> u3) zs (\<Pi> u')" and inv': "solo_inv u'" by simp_all
  have f0: "dwu_floor u = 0" using sd_reconcile.prems by (simp add: solo_inv_def)
  have sa: "dwu_sent u = dwu_accepted u" using sd_reconcile.prems by (simp add: solo_inv_def)
  have R_full: "R = replay_down_hist (exec_src_hist (dwe_core (\<Pi> u)))
                    (exec_scope (dwe_core (\<Pi> u))) f"
    using sd_reconcile.hyps(2) f0 by (simp add: retained_hist_def)
  have dist': "distinct (drop m (replay_down_hist (exec_src_hist (dwe_core (\<Pi> u)))
                  (exec_scope (dwe_core (\<Pi> u))) f))"
    using sd_reconcile.hyps(4) R_full by simp
  have disj': "set (drop m (replay_down_hist (exec_src_hist (dwe_core (\<Pi> u)))
                  (exec_scope (dwe_core (\<Pi> u))) f)) \<inter> e_payload ` set (dwe_emitted (\<Pi> u)) = {}"
    using sd_reconcile.hyps(5) R_full by (simp add: set_\<Pi>_emitted_payloads sa)
  have "disciplined_trace (\<Pi> u) (DWE_Reconcile m f # zs) (\<Pi> u')"
    by (rule disciplined_trace.disciplined_reconcile[OF er dist' disj' tr])
  then show ?case using inv' by blast
next
  case (sd_turnover u u1 u2 ys zs u')
  from solo_turnover_project[OF sd_turnover.prems sd_turnover.hyps(1) sd_turnover.hyps(2)]
  have dr: "dwe_resume (\<Pi> u) (\<Pi> u2)" and inv2: "solo_inv u2" by simp_all
  from sd_turnover.IH[OF inv2]
  have tr: "disciplined_trace (\<Pi> u2) zs (\<Pi> u')" and inv': "solo_inv u'" by simp_all
  have "disciplined_trace (\<Pi> u) (DWE_Resume # zs) (\<Pi> u')"
    by (rule disciplined_trace.disciplined_resume[OF dr tr])
  then show ?case using inv' by blast
qed

theorem u_solo_discipline_projects:
  assumes "solo_disciplined_trace (dwu_init b K fin) ys zs u'"
  shows "disciplined_trace (dwe_init b K fin) zs (\<Pi> u')"
proof -
  have "disciplined_trace (\<Pi> (dwu_init b K fin)) zs (\<Pi> u')"
    using solo_disc_project[OF assms solo_inv_init] by simp
  then show ?thesis by (simp add: \<Pi>_init)
qed

subsection \<open>5.2 R6: solo positive discipline (the pullback recovery)\<close>

text \<open>@{const solo_disciplined_trace} \<Rightarrow> landed @{const disciplined_trace}
  (project) \<Rightarrow> @{text "\<not> effect_unsafe"} (landed T2.8) \<Rightarrow> pull back through
  @{thm u_hazards_once} (the endpoint keeps @{const solo_inv}) \<Rightarrow>
  @{text "\<not> u_effect_unsafe"}.\<close>

theorem u_solo_positive_discipline:
  assumes "solo_disciplined_trace (dwu_init b K fin) ys zs u'"
  shows "\<not> u_effect_unsafe u'"
proof -
  have proj: "disciplined_trace (dwe_init b K fin) zs (\<Pi> u')"
    by (rule u_solo_discipline_projects[OF assms])
  have inv': "solo_inv u'"
    using solo_disc_project[OF assms solo_inv_init] by simp
  have safe: "\<not> effect_unsafe (\<Pi> u')" by (rule general_positive_discipline[OF proj])
  have p1: "dwu_sent u' = dwu_accepted u'" using inv' by (simp add: solo_inv_def)
  have p2: "dwu_journal u' = exec_src_hist (dwu_store u')" using inv' by (simp add: solo_inv_def)
  have p3: "\<forall>x \<in> set (dwu_sent u'). is_ulog x" using inv' by (simp add: solo_inv_def)
  have "u_effect_unsafe u' \<longleftrightarrow> effect_unsafe (\<Pi> u')"
    using u_hazards_once[OF p1 p2 p3] by blast
  then show ?thesis using safe by simp
qed

subsection \<open>5.3 The reverse embedding: landed discipline lifts to solo discipline\<close>

text \<open>The disciplined reconcile / resume constructions at @{term "\<iota> t"} (the fused
  cursor triple / adjacent turnover pair), carrying the transported distinctness
  and freshness guards.\<close>

lemma \<iota>_emitting_reconcile_solo_disc:
  assumes er: "emitting_reconcile m t f t'"
      and dist: "distinct (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                    (exec_scope (dwe_core t)) f))"
      and disj: "set (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                    (exec_scope (dwe_core t)) f)) \<inter> e_payload ` set (dwe_emitted t) = {}"
      and tail: "solo_disciplined_trace (\<iota> t') ys zs u'"
  shows "\<exists>ws. solo_disciplined_trace (\<iota> t) ws (DWE_Reconcile m f # zs) u'"
proof -
  define g where "g = dwe_epoch t"
  define R where "R = replay_down_hist (exec_src_hist (dwe_core t)) (exec_scope (dwe_core t)) f"
  define B where "B = stamped_at (length (exec_src_hist (dwe_core t))) g (drop m R)"
  define s0 where "s0 = (dwe_core t)\<lparr>exec_down_hist := R, exec_pending := {}, exec_status := Recovered\<rparr>"
  define u1 where "u1 = (\<iota> t)\<lparr>dwu_gens := (dwu_gens (\<iota> t))(g \<mapsto> UArmed B)\<rparr>"
  define u2 where "u2 = u1\<lparr>dwu_store := s0\<rparr>"
  from er have crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
    by (simp add: emitting_reconcile_def)
  from er have fle: "f \<le> exec_finish (dwe_core t)"
    by (simp add: emitting_reconcile_def)
  from er have mle: "m \<le> length R"
    by (simp add: emitting_reconcile_def R_def)
  from er have t'eq:
    "t' = t\<lparr>dwe_core := s0,
            dwe_emitted := dwe_emitted t
              @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)), dwe_epoch t, c, e))
                  (drop m R)\<rparr>"
    by (simp add: emitting_reconcile_def R_def s0_def)
  have g_eq: "g = dwu_hwm (\<iota> t)" by (simp add: g_def)
  have R_eq: "R = replay_down_hist (retained_hist (\<iota> t)) (exec_scope (dwu_store (\<iota> t))) f"
    by (simp add: R_def retained_hist_def)
  have B_eq: "B = stamped_at (length (dwu_journal (\<iota> t))) g (drop m R)"
    by (simp add: B_def)
  have dist': "distinct (drop m R)" using dist by (simp add: R_def)
  have disj': "set (drop m R) \<inter> set (log_payloads (dwu_accepted (\<iota> t))) = {}"
    using disj by (simp add: R_def \<iota>_accepted)
  have Bguard: "\<forall>x \<in> set B. ue_gen x = g \<and> ue_stamp x \<le> length (dwu_journal (\<iota> t))"
    by (auto simp: B_def stamped_at_def)
  have arm: "dwu_step (\<iota> t) (UArm g B f) u1"
    unfolding u1_def
    by (rule dwu_step.uarm)
       (use crashed fle Bguard in \<open>simp_all add: g_def domIff\<close>)
  have relay: "relay_bounded_replay_reconcile (dwu_store u1) f s0"
    using crashed fle by (simp add: relay_bounded_replay_reconcile_def u1_def s0_def R_def)
  have heal: "dwu_step u1 (UHeal g f) u2"
    unfolding u2_def by (rule dwu_step.uheal[OF relay])
  have g2: "dwu_gens u2 g = Some (UArmed B)"
    by (simp add: u2_def u1_def)
  have fire0: "dwu_step u2 (UFire g)
        (u2\<lparr>dwu_sent := dwu_sent u2 @ B,
             dwu_accepted := dwu_accepted u2 @ (if dwu_fence u2 \<le> g then B else []),
             dwu_gens := (dwu_gens u2)(g \<mapsto> UProd)\<rparr>)"
    by (rule dwu_step.ufire[OF g2])
  have fireeq:
    "u2\<lparr>dwu_sent := dwu_sent u2 @ B,
        dwu_accepted := dwu_accepted u2 @ (if dwu_fence u2 \<le> g then B else []),
        dwu_gens := (dwu_gens u2)(g \<mapsto> UProd)\<rparr> = \<iota> t'"
    by (simp add: u2_def u1_def s0_def \<iota>_def t'eq g_def B_def
                  stamped_at_eq_map_ulift fun_upd_idem)
  have fire: "dwu_step u2 (UFire g) (\<iota> t')"
    using fire0 fireeq by simp
  have "solo_disciplined_trace (\<iota> t) (UArm g B f # UHeal g f # UFire g # ys)
          (DWE_Reconcile m f # zs) u'"
    by (rule solo_disciplined_trace.sd_reconcile
              [OF g_eq R_eq mle dist' disj' B_eq arm heal fire tail])
  then show ?thesis by blast
qed

lemma \<iota>_dwe_resume_solo_disc:
  assumes dr: "dwe_resume t t'"
      and tail: "solo_disciplined_trace (\<iota> t') ys zs u'"
  shows "\<exists>ws. solo_disciplined_trace (\<iota> t) ws (DWE_Resume # zs) u'"
proof -
  define u1 where "u1 = (\<iota> t)\<lparr>dwu_gens := (dwu_gens (\<iota> t))(Suc (dwu_hwm (\<iota> t)) \<mapsto> UProd),
                              dwu_hwm := Suc (dwu_hwm (\<iota> t))\<rparr>"
  from dr have rec: "exec_status (dwe_core t) = Recovered"
    by (simp add: dwe_resume_def)
  from dr have t'eq: "t' = t\<lparr>dwe_core := (dwe_core t)\<lparr>exec_status := Running\<rparr>,
                            dwe_epoch := Suc (dwe_epoch t)\<rparr>"
    by (simp add: dwe_resume_def)
  have spawn: "dwu_step (\<iota> t) USpawn u1"
    unfolding u1_def by (rule dwu_step.uspawn)
  have store_u1: "dwu_store u1 = dwe_core t" by (simp add: u1_def)
  have rel0: "dwu_step u1 (URelease (dwu_hwm u1))
        (u1\<lparr>dwu_store := (dwu_store u1)\<lparr>exec_status := Running\<rparr>\<rparr>)"
    by (rule dwu_step.urelease) (simp add: store_u1 rec)
  have releq: "u1\<lparr>dwu_store := (dwu_store u1)\<lparr>exec_status := Running\<rparr>\<rparr> = \<iota> t'"
    by (simp add: u1_def \<iota>_def t'eq fun_eq_iff le_Suc_eq)
  have rel: "dwu_step u1 (URelease (dwu_hwm u1)) (\<iota> t')"
    using rel0 releq by simp
  have "solo_disciplined_trace (\<iota> t) (USpawn # URelease (dwu_hwm u1) # ys) (DWE_Resume # zs) u'"
    by (rule solo_disciplined_trace.sd_turnover[OF spawn rel tail])
  then show ?thesis by blast
qed

lemma landed_disc_embed:
  assumes "disciplined_trace t bs t'"
  shows "\<exists>ys. solo_disciplined_trace (\<iota> t) ys bs (\<iota> t')"
  using assms
proof (induction rule: disciplined_trace.induct)
  case (disciplined_refl t)
  show ?case by (intro exI[of _ "[]"] solo_disciplined_trace.sd_refl)
next
  case (disciplined_nonpub t a t' as t'')
  from disciplined_nonpub.IH obtain ys
    where ys: "solo_disciplined_trace (\<iota> t') ys as (\<iota> t'')" ..
  have wf: "wellformed_exec_state (dwu_store (\<iota> t))"
    using disciplined_nonpub.hyps(2) by simp
  have wfh: "exec_label_preserves_history_wf (dwu_store (\<iota> t)) a"
    using disciplined_nonpub.hyps(3) by simp
  have step: "dwu_step (\<iota> t) (ULift (dwu_hwm (\<iota> t)) a) (\<iota> t')"
    using \<iota>_dwe_label_sim[OF disciplined_nonpub.hyps(1)] by simp
  have "solo_disciplined_trace (\<iota> t) (ULift (dwu_hwm (\<iota> t)) a # ys) (DWE_Label a # as) (\<iota> t'')"
    by (rule solo_disciplined_trace.sd_lift_nonpub
              [OF wf wfh disciplined_nonpub.hyps(4) step ys])
  then show ?case by blast
next
  case (disciplined_publish t c e t' as t'')
  from disciplined_publish.IH obtain ys
    where ys: "solo_disciplined_trace (\<iota> t') ys as (\<iota> t'')" ..
  have wf: "wellformed_exec_state (dwu_store (\<iota> t))"
    using disciplined_publish.hyps(2) by simp
  have wfh: "exec_label_preserves_history_wf (dwu_store (\<iota> t)) (DoDownstream c e)"
    using disciplined_publish.hyps(3) by simp
  have mem: "(c, e) \<in> set (dwu_journal (\<iota> t))"
    using disciplined_publish.hyps(4) by simp
  have notmem: "(c, e) \<notin> set (log_payloads (dwu_accepted (\<iota> t)))"
    using disciplined_publish.hyps(5) by (simp add: \<iota>_accepted)
  have step: "dwu_step (\<iota> t) (ULift (dwu_hwm (\<iota> t)) (DoDownstream c e)) (\<iota> t')"
    using \<iota>_dwe_label_sim[OF disciplined_publish.hyps(1)] by simp
  have "solo_disciplined_trace (\<iota> t) (ULift (dwu_hwm (\<iota> t)) (DoDownstream c e) # ys)
          (DWE_Label (DoDownstream c e) # as) (\<iota> t'')"
    by (rule solo_disciplined_trace.sd_lift_publish[OF wf wfh mem notmem step ys])
  then show ?case by blast
next
  case (disciplined_reconcile m t f t' as t'')
  from disciplined_reconcile.IH obtain ys
    where ys: "solo_disciplined_trace (\<iota> t') ys as (\<iota> t'')" ..
  from \<iota>_emitting_reconcile_solo_disc[OF disciplined_reconcile.hyps(1)
        disciplined_reconcile.hyps(2) disciplined_reconcile.hyps(3) ys]
  show ?case by blast
next
  case (disciplined_resume t t' as t'')
  from disciplined_resume.IH obtain ys
    where ys: "solo_disciplined_trace (\<iota> t') ys as (\<iota> t'')" ..
  from \<iota>_dwe_resume_solo_disc[OF disciplined_resume.hyps(1) ys]
  show ?case by blast
qed

theorem u_landed_discipline_lifts:
  assumes "disciplined_trace (dwe_init b K fin) bs t'"
  shows "\<exists>ys u'. solo_disciplined_trace (dwu_init b K fin) ys bs u' \<and> \<Pi> u' = t'"
proof -
  from landed_disc_embed[OF assms] obtain ys
    where sdt: "solo_disciplined_trace (\<iota> (dwe_init b K fin)) ys bs (\<iota> t')" ..
  have "solo_disciplined_trace (dwu_init b K fin) ys bs (\<iota> t') \<and> \<Pi> (\<iota> t') = t'"
    using sdt by (simp add: \<iota>_init \<Pi>_section)
  then show ?thesis by blast
qed

subsection \<open>5.4 The landed T2.8, recovered through the unified machine\<close>

text \<open>The recovery route is lift + solo safety + hazard transport (NOT a DIRECT
  citation of the landed theorem at THIS site — it routes through the unified
  machine's R6 \<open>u_solo_positive_discipline\<close>, which itself applies landed T2.8
  internally via \<Pi>-transport; so this corollary RE-OBTAINS T2.8's statement
  through the unified machine, it does not independently re-derive T2.8):
  a landed disciplined run lifts to a solo-disciplined run of @{term "\<iota> t"}, whose
  endpoint is @{text "\<not> u_effect_unsafe"} by R6, which transports back to
  @{text "\<not> effect_unsafe t'"} through the section law.\<close>

corollary u_general_positive_discipline_solo:
  assumes "disciplined_trace (dwe_init b K fin) bs t'"
  shows "\<not> effect_unsafe t'"
proof -
  from landed_disc_embed[OF assms] obtain ys
    where sdt: "solo_disciplined_trace (\<iota> (dwe_init b K fin)) ys bs (\<iota> t')" ..
  then have "solo_disciplined_trace (dwu_init b K fin) ys bs (\<iota> t')"
    by (simp add: \<iota>_init)
  then have "\<not> u_effect_unsafe (\<iota> t')" by (rule u_solo_positive_discipline)
  then show ?thesis by simp
qed

end
