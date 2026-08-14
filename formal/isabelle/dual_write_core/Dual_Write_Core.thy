(*  Title:       Dual_Write_Core.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Shared protocol layer for the Dual-Write development. This theory
    introduces the protocol record, its base-aware committed-log image, the
    scoped mismatch/divergence vocabulary, the log-derived replay boundary, and
    the older absence-shaped asymmetric_store locale. The side-parametric
    operational headline lives in Dual_Write_Execution; this file supplies its
    protocol-level safety kernel and closed witnesses.

    This is a self-contained development over the shared DBLog-free Layer-0
    substrate (source coordinates, histories, and scope), with no dependency
    on any downstream run/certificate machinery (decouple-and-subordinate).
*)

theory Dual_Write_Core
  imports
    Dual_Write_Layer0.Source_Coordinates
    Dual_Write_Layer0.Source_History
    Dual_Write_Layer0.Scope
begin

section \<open>The dual-write protocol: mismatch, divergence, and replay boundaries\<close>

subsection \<open>The shared protocol record\<close>

text \<open>
  One record, no tag field. \<open>store2\<close> is the second, independently-written
  downstream store; the authoritative first store is \<^emph>\<open>defined\<close> below as the
  committed-log materialization \<open>log_image\<close>, not carried as a free field. The
  store codomain \<open>'k \<rightharpoonup> 'v\<close> matches \<open>restrict\<close> / \<open>Src\<close>, so
  \<open>s2 P f = log_image P f\<close> elaborates.
\<close>

record ('k, 'v) proto =
  pbase  :: "'k \<rightharpoonup> 'v"
  psrc   :: "('k, 'v) src_history"
  pscope :: "'k set"
  pcrash :: "frontier"
  pfin   :: "frontier"
  store2 :: "frontier \<Rightarrow> ('k \<rightharpoonup> 'v)"

definition log_image :: "('k, 'v) proto \<Rightarrow> frontier \<Rightarrow> ('k \<rightharpoonup> 'v)" where
  "log_image P f = restrict (Src (pbase P) (psrc P) f) (pscope P)"

abbreviation s2 :: "('k, 'v) proto \<Rightarrow> frontier \<Rightarrow> ('k \<rightharpoonup> 'v)" where
  "s2 P f \<equiv> restrict (store2 P f) (pscope P)"

fun event_result :: "('k, 'v) source_event \<Rightarrow> 'v option" where
  "event_result (Insert _ v) = Some v"
| "event_result (Update _ v) = Some v"
| "event_result (Delete _) = None"

definition same_downstream_effect
  :: "('k, 'v) source_event \<Rightarrow> ('k, 'v) source_event \<Rightarrow> 'k \<Rightarrow> bool"
where
  "same_downstream_effect e_src e_down k \<longleftrightarrow>
     key_of e_src = k
   \<and> key_of e_down = k
   \<and> event_result e_down = event_result e_src"

definition effective_source_effect
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) source_event \<Rightarrow> 'k \<Rightarrow> bool"
where
  "effective_source_effect b e k \<longleftrightarrow>
     key_of e = k \<and> event_result e \<noteq> b k"

lemma Src_empty [simp]: "Src b [] f = b"
  by (simp add: Src_def latest_src_event_def fun_eq_iff Let_def)

lemma Src_single_event_at_key:
  assumes "key_of e = k"
      and "c \<le> f"
  shows "Src b [(c, e)] f k = event_result e"
  using assms
  by (cases e; simp add: Src_def latest_src_event_def Let_def src_le_eq_less_eq)

lemma Src_single_event_before_key:
  assumes "f < c"
  shows "Src b [(c, e)] f k = b k"
proof -
  from assms have "\<not> c \<le> f" by simp
  thus ?thesis
    by (simp add: Src_def latest_src_event_def Let_def src_le_eq_less_eq)
qed


subsection \<open>The positive class: \<open>log_derived\<close>\<close>

text \<open>
  The downstream store \<^emph>\<open>is\<close> the committed-log function on scope, up to the
  final frontier. Genesis is automatic (\<open>log_image P c0\<close> agrees with the empty
  map on scope by \<open>Src_at_base\<close>), so it is not assumed.
\<close>

definition log_derived :: "('k, 'v) proto \<Rightarrow> bool" where
  "log_derived P \<longleftrightarrow>
     wellformed_src_history (psrc P)
   \<and> pcrash P \<le> pfin P
   \<and> (\<forall>f. f \<le> pfin P \<longrightarrow> s2 P f = log_image P f)"


subsection \<open>The negative class: the \<open>asymmetric_store\<close> locale\<close>

text \<open>
  Two independent non-atomic writes with the authority (the committed source
  log / \<open>log_image\<close>) committed early and the downstream \<open>store2\<close> lagging
  across a crash. \<open>asymmetric_store\<close> is the \<^emph>\<open>abstract\<close> negative class: it fixes
  the proof-critical crash-asymmetry premises plus one final-value fidelity
  guard. The divergence is \<^emph>\<open>derived\<close> (authority present at the crash +
  downstream absent through the crash), not assumed.

  Proof-critical premises for Results 1 and 2: \<open>C1_le\<close> (the crash frontier
  precedes completion), \<open>C1_store2_absent_through_crash\<close> (the downstream is
  absent through the crash on the witness key), and \<open>C1_log_committed\<close> (the
  authority is committed by the crash). Scope membership \<open>k0 \<in> pscope P\<close> is
  \<^emph>\<open>not\<close> a premise --- it is \<^emph>\<open>derived\<close> (\<open>k0_in_scope\<close> below) from
  \<open>C1_log_committed\<close>, since \<open>log_image\<close> is restricted to the scope.

  The fourth premise \<open>C1_value_fidelity\<close> is a modelling guard rather than a
  proof-critical premise for those two results: it pins the downstream's
  \<^emph>\<open>final\<close> value on the witness key to the committed-log image at completion.
  When the final committed-log image carries a value, this rules out a final
  value mismatch; when the final image is \<open>None\<close>, the equality can be
  satisfied as \<open>None = None\<close>. Thus the premise is value fidelity at
  completion, not by itself an eventual-presence or "second write lands"
  premise. The concrete witness \<open>proto_dw2\<close> below shows that adding this guard
  does not empty the class.

  Premises that a \<^emph>\<open>realistic\<close> dual write also satisfies but that the results do
  not need --- a wellformed committed log, and an eventually-present and
  monotone downstream --- are \<^emph>\<open>not\<close> imposed on the abstract class (adding them
  would only narrow an impossibility). That they nevertheless hold of the
  witness, so the divergent class genuinely contains a realistic dual write, is
  recorded at the witness level (\<open>proto_dw2_wellformed_log\<close> /
  \<open>proto_dw2_downstream_present_at_completion\<close> /
  \<open>proto_dw2_downstream_monotone\<close>), not as locale premises.
\<close>

locale asymmetric_store =
  fixes P :: "('k, 'v) proto" and k0 :: "'k"
  assumes C1_le:      "pcrash P \<le> pfin P"
      and C1_store2_absent_through_crash:
            "\<And>f. f \<le> pcrash P \<Longrightarrow> store2 P f k0 = None"
      and C1_log_committed: "log_image P (pcrash P) k0 \<noteq> None"
      and C1_value_fidelity: "store2 P (pfin P) k0 = log_image P (pfin P) k0"

text \<open>
  Scope membership is derived, not assumed: \<open>log_image\<close> is restricted to
  \<open>pscope P\<close>, so a non-\<open>None\<close> committed-log value at \<open>k0\<close> forces
  \<open>k0 \<in> pscope P\<close>.
\<close>

lemma (in asymmetric_store) k0_in_scope: "k0 \<in> pscope P"
proof -
  have "log_image P (pcrash P) k0 \<noteq> None" by (rule C1_log_committed)
  thus ?thesis by (auto simp: log_image_def restrict_def split: if_splits)
qed


subsection \<open>Divergence\<close>

definition mismatch_at :: "('k, 'v) proto \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> bool" where
  "mismatch_at P f k \<longleftrightarrow>
     k \<in> pscope P \<and> store2 P f k \<noteq> log_image P f k"

definition diverges :: "('k, 'v) proto \<Rightarrow> frontier \<Rightarrow> bool" where
  "diverges P f \<longleftrightarrow>
     f \<le> pfin P \<and> (\<exists>k. k \<in> pscope P \<and> store2 P f k \<noteq> log_image P f k)"

lemma diverges_iff_mismatch_at:
  "diverges P f \<longleftrightarrow> f \<le> pfin P \<and> (\<exists>k. mismatch_at P f k)"
  by (simp add: diverges_def mismatch_at_def)

lemma s2_neq_log_image_iff_mismatch_at:
  "s2 P f \<noteq> log_image P f \<longleftrightarrow> (\<exists>k. mismatch_at P f k)"
proof
  assume ne: "s2 P f \<noteq> log_image P f"
  then obtain k where k: "s2 P f k \<noteq> log_image P f k"
    by (auto simp: fun_eq_iff)
  have "k \<in> pscope P"
  proof (rule ccontr)
    assume "k \<notin> pscope P"
    hence "s2 P f k = None" "log_image P f k = None"
      by (simp_all add: restrict_def log_image_def)
    with k show False by simp
  qed
  with k show "\<exists>k. mismatch_at P f k"
    by (auto simp: mismatch_at_def restrict_def)
next
  assume "\<exists>k. mismatch_at P f k"
  thus "s2 P f \<noteq> log_image P f"
    by (auto simp: mismatch_at_def restrict_def fun_eq_iff)
qed

theorem diverges_iff_s2_neq_log_image:
  "diverges P f \<longleftrightarrow> f \<le> pfin P \<and> s2 P f \<noteq> log_image P f"
  by (simp add: diverges_iff_mismatch_at s2_neq_log_image_iff_mismatch_at)


subsection \<open>The minimal crash-mismatch locale\<close>

text \<open>
  The theorem core is just scoped mismatch at a crash frontier that is still
  within the modelled execution interval. This locale is deliberately weaker
  than \<open>asymmetric_store\<close>: it does not require an absent downstream, a
  source-present value, or final catch-up. It is the neutral safety kernel for
  inserts, stale updates, and stale deletes.
\<close>

locale crash_mismatch =
  fixes P :: "('k, 'v) proto" and k0 :: "'k"
  assumes CM_le: "pcrash P \<le> pfin P"
      and CM_mismatch: "mismatch_at P (pcrash P) k0"

theorem (in crash_mismatch) crash_mismatch_diverges_at_crash:
  "diverges P (pcrash P)"
  using CM_le CM_mismatch by (auto simp: diverges_iff_mismatch_at)

theorem crash_mismatch_class_diverges:
  assumes "crash_mismatch P k0"
  shows   "diverges P (pcrash P)"
proof -
  from assms interpret cm: crash_mismatch P k0 .
  show ?thesis by (rule cm.crash_mismatch_diverges_at_crash)
qed

lemma (in asymmetric_store) asymmetric_store_mismatch_at_crash:
  "mismatch_at P (pcrash P) k0"
proof -
  have absent: "store2 P (pcrash P) k0 = None"
    by (rule C1_store2_absent_through_crash[OF order_refl])
  have committed: "log_image P (pcrash P) k0 \<noteq> None"
    by (rule C1_log_committed)
  have "store2 P (pcrash P) k0 \<noteq> log_image P (pcrash P) k0"
  proof
    assume "store2 P (pcrash P) k0 = log_image P (pcrash P) k0"
    with absent committed show False by simp
  qed
  with k0_in_scope show ?thesis
    by (simp add: mismatch_at_def)
qed

theorem (in asymmetric_store) asymmetric_store_crash_mismatch:
  "crash_mismatch P k0"
  by (unfold_locales; rule C1_le asymmetric_store_mismatch_at_crash)


subsection \<open>Non-vacuity witnesses\<close>

text \<open>
  \<open>proto_dw2\<close> is the impossibility witness: a one-\<open>Insert\<close> history so the
  committed log carries the event at the crash while the downstream lags
  (witnessed below by \<open>interpretation asymmetric_store proto_dw2 0\<close>).
  \<open>proto_ld\<close> inhabits \<open>log_derived\<close>, witnessing non-vacuity of the bridge
  result. The \<open>psrc\<close> fields are \<open>(src_coord \<times> source_event)\<close> lists.
\<close>

definition proto_dw2 :: "(nat, nat) proto" where
  "proto_dw2 =
     \<lparr> pbase  = (\<lambda>_. None),
       psrc   = [(ec1, Insert 0 7)],
       pscope = {0},
       pcrash = ec2,
       pfin   = ec3,
       store2 = (\<lambda>f. if ec3 \<le> f then [0 \<mapsto> 7] else (\<lambda>_. None)) \<rparr>"

definition proto_ld :: "(nat, nat) proto" where
  "proto_ld =
     \<lparr> pbase  = (\<lambda>_. None),
       psrc   = [],
       pscope = {0},
       pcrash = ec4,
       pfin   = ec4,
       store2 = (\<lambda>f. Src (\<lambda>_. None) [] f) \<rparr>"


subsection \<open>Result 1 --- impossibility (the crash-divergence theorem)\<close>

text \<open>
  A protocol in the \<open>asymmetric_store\<close> class --- authority committed by the
  crash, downstream lagging through it --- disagrees with the authority at the
  crash frontier. On the witness key \<open>k0\<close> the downstream is absent
  (\<open>C1_store2_absent_through_crash\<close> at \<open>pcrash P\<close>) while the committed log is
  present (\<open>C1_log_committed\<close>), so the two stores differ. The divergence is
  therefore \<^emph>\<open>derived\<close> from the protocol premises, not assumed.
\<close>

theorem (in asymmetric_store) asymmetric_store_diverges_at_crash:
  "diverges P (pcrash P)"
  by (rule crash_mismatch_class_diverges[OF asymmetric_store_crash_mismatch])

corollary (in asymmetric_store) asymmetric_store_diverges:
  "\<exists>f. diverges P f"
  using asymmetric_store_diverges_at_crash by blast


subsection \<open>Result 1 as a global class theorem\<close>

text \<open>
  The theorems above are stated inside the \<open>asymmetric_store\<close> context. The next
  two restate Result 1 as top-level theorems quantified over \<^emph>\<open>all\<close> protocols
  and witness keys that satisfy the \<open>asymmetric_store\<close> premises, making the
  class-universality explicit: every protocol exhibiting the asymmetric-crash
  pattern diverges at its crash frontier. They are exactly the locale results,
  un-localed --- they add and weaken no premise.
\<close>

theorem asymmetric_store_class_diverges:
  assumes "asymmetric_store P k0"
  shows   "diverges P (pcrash P)"
proof -
  from assms interpret dw: asymmetric_store P k0 .
  show ?thesis by (rule dw.asymmetric_store_diverges_at_crash)
qed

corollary asymmetric_store_class_diverges_ex:
  assumes "asymmetric_store P k0"
  shows   "\<exists>f. diverges P f"
  using asymmetric_store_class_diverges[OF assms] by blast


subsection \<open>Non-vacuity: \<open>proto_dw2\<close> inhabits \<open>asymmetric_store\<close>\<close>

text \<open>
  The one-\<open>Insert\<close> witness \<open>proto_dw2\<close> discharges all four \<open>C1_*\<close> premises, so
  the \<open>asymmetric_store\<close> locale is non-empty and Result 1 is not vacuously true.
  The committed log carries the event at the crash (\<open>log_image proto_dw2 ec2 0 =
  Some 7\<close>) while the downstream \<open>store2\<close> stays absent until \<open>ec3\<close>.
\<close>

lemma proto_dw2_asymmetric_store: "asymmetric_store proto_dw2 (0::nat)"
proof (rule asymmetric_store.intro)
  show "pcrash proto_dw2 \<le> pfin proto_dw2"
    by (simp add: proto_dw2_def ec_defs)
next
  fix f :: frontier
  assume "f \<le> pcrash proto_dw2"
  hence "f \<le> ec2" by (simp add: proto_dw2_def)
  also have "ec2 < ec3" by (simp add: ec_defs)
  finally have "f < ec3" .
  hence "\<not> ec3 \<le> f" by simp
  thus "store2 proto_dw2 f 0 = None"
    by (simp add: proto_dw2_def)
next
  show "log_image proto_dw2 (pcrash proto_dw2) 0 \<noteq> None"
    by (simp add: log_image_def proto_dw2_def Src_def latest_src_event_def
                  restrict_def ec_defs Let_def)
next
  show "store2 proto_dw2 (pfin proto_dw2) 0 = log_image proto_dw2 (pfin proto_dw2) 0"
    by (simp add: log_image_def proto_dw2_def Src_def latest_src_event_def
                  restrict_def ec_defs Let_def)
qed

interpretation dw2: asymmetric_store proto_dw2 "0::nat"
  by (rule proto_dw2_asymmetric_store)

text \<open>
  The instantiated divergence fact at the concrete witness --- a closed term
  certifying Result 1 is non-vacuous.
\<close>

lemma proto_dw2_diverges_at_crash: "diverges proto_dw2 (pcrash proto_dw2)"
  by (rule dw2.asymmetric_store_diverges_at_crash)

text \<open>
  Faithfulness: \<open>proto_dw2\<close> is a \<^emph>\<open>realistic\<close> dual write. The properties pruned
  from the abstract \<open>asymmetric_store\<close> class --- a wellformed committed log, and
  an eventually-present and monotone downstream --- all hold of the witness, so
  the divergent class genuinely contains a realistic dual write and Result 1 is
  not an artifact of a degenerate (never-written-downstream) model. They are
  recorded here as witness facts rather than imposed as locale premises (which
  would only narrow the impossibility).
\<close>

lemma proto_dw2_wellformed_log: "wellformed_src_history (psrc proto_dw2)"
  by (simp add: proto_dw2_def wellformed_src_history_def ec_defs)

lemma proto_dw2_downstream_present_at_completion:
  "store2 proto_dw2 (pfin proto_dw2) 0 \<noteq> None"
  by (simp add: proto_dw2_def ec_defs)

lemma proto_dw2_downstream_monotone:
  assumes "f \<le> f'" and "f' \<le> pfin proto_dw2"
      and "store2 proto_dw2 f 0 \<noteq> None"
  shows   "store2 proto_dw2 f' 0 \<noteq> None"
proof -
  from assms(3) have ec3f: "ec3 \<le> f"
    by (simp add: proto_dw2_def split: if_splits)
  from ec3f assms(1) have "ec3 \<le> f'" by (rule order_trans)
  thus ?thesis by (simp add: proto_dw2_def)
qed


subsection \<open>A realistic subclass of \<open>asymmetric_store\<close>\<close>

text \<open>
  The abstract \<open>asymmetric_store\<close> class is deliberately small: Result 1 needs
  only the crash-asymmetry premises and final value fidelity. For review hygiene
  we also name a stricter subclass that packages the realistic side conditions
  exhibited by \<open>proto_dw2\<close>: the authoritative log is wellformed, the witness key
  still has a non-delete value at completion, the downstream has a value at
  completion, and downstream presence is monotone up to completion. The
  divergence theorem is inherited unchanged from the abstract class.
\<close>

locale realistic_asymmetric_store = asymmetric_store P k0
  for P :: "('k, 'v) proto" and k0 :: "'k" +
  assumes R_wellformed_log: "wellformed_src_history (psrc P)"
      and R_final_log_present: "log_image P (pfin P) k0 \<noteq> None"
      and R_downstream_present_at_completion: "store2 P (pfin P) k0 \<noteq> None"
      and R_downstream_monotone:
            "\<And>f f'. \<lbrakk>f \<le> f'; f' \<le> pfin P; store2 P f k0 \<noteq> None\<rbrakk>
             \<Longrightarrow> store2 P f' k0 \<noteq> None"

theorem (in realistic_asymmetric_store) realistic_asymmetric_store_diverges_at_crash:
  "diverges P (pcrash P)"
  by (rule asymmetric_store_diverges_at_crash)

theorem realistic_asymmetric_store_class_diverges:
  assumes "realistic_asymmetric_store P k0"
  shows   "diverges P (pcrash P)"
proof -
  from assms interpret dw: realistic_asymmetric_store P k0 .
  show ?thesis by (rule dw.realistic_asymmetric_store_diverges_at_crash)
qed

lemma proto_dw2_final_log_present:
  "log_image proto_dw2 (pfin proto_dw2) 0 \<noteq> None"
  by (simp add: log_image_def proto_dw2_def Src_def latest_src_event_def
                restrict_def ec_defs Let_def)

lemma proto_dw2_realistic_asymmetric_store:
  "realistic_asymmetric_store proto_dw2 (0::nat)"
  by (unfold_locales;
      simp add: proto_dw2_def log_image_def Src_def latest_src_event_def
                restrict_def wellformed_src_history_def ec_defs Let_def
          split: if_splits)

interpretation dw2_realistic: realistic_asymmetric_store proto_dw2 "0::nat"
  by (rule proto_dw2_realistic_asymmetric_store)


subsection \<open>Premises bite: dropping the absence premise kills divergence\<close>

text \<open>
  \<open>proto_present\<close> keeps everything in \<open>proto_dw2\<close> but makes the downstream
  \<open>store2\<close> present from the start (\<open>[0 \<mapsto> 7]\<close> at every frontier). It still
  satisfies the divergence-relevant conditions (\<open>k0 \<in> pscope\<close>, \<open>C1_le\<close>, and
  \<open>C1_log_committed\<close>) but violates \<open>C1_store2_absent_through_crash\<close> --- and at
  the crash it does \<^emph>\<open>not\<close> diverge, because the downstream already agrees with
  the committed log there. This is concrete evidence that
  \<open>C1_store2_absent_through_crash\<close> is load-bearing, not decoration.
\<close>

definition proto_present :: "(nat, nat) proto" where
  "proto_present =
     \<lparr> pbase  = (\<lambda>_. None),
       psrc   = [(ec1, Insert 0 7)],
       pscope = {0},
       pcrash = ec2,
       pfin   = ec3,
       store2 = (\<lambda>f. [0 \<mapsto> 7]) \<rparr>"

lemma proto_present_scope: "(0::nat) \<in> pscope proto_present"
  by (simp add: proto_present_def)

lemma proto_present_le: "pcrash proto_present \<le> pfin proto_present"
  by (simp add: proto_present_def ec_defs)

lemma proto_present_log_committed:
  "log_image proto_present (pcrash proto_present) 0 \<noteq> None"
  by (simp add: log_image_def proto_present_def Src_def latest_src_event_def
                restrict_def ec_defs Let_def)

lemma proto_present_store2_present_at_crash:
  "store2 proto_present (pcrash proto_present) 0 \<noteq> None"
  by (simp add: proto_present_def)

lemma proto_present_not_diverges:
  "\<not> diverges proto_present (pcrash proto_present)"
  by (simp add: diverges_def proto_present_def log_image_def Src_def
                latest_src_event_def restrict_def ec_defs Let_def)


subsection \<open>Neutral mismatch witnesses: stale update and stale delete\<close>

text \<open>
  The neutral \<open>mismatch_at\<close> predicate is strictly broader than the original
  absent-downstream crash gap. It also covers stale updates (the downstream
  still carries an old value) and stale deletes (the authority has removed a
  value while the downstream still carries it). These witnesses are not meant to
  inhabit \<open>asymmetric_store\<close>; they witness why the next operational layer should
  reason about mismatch, not only source-present/downstream-absent insert gaps.
\<close>

definition proto_stale_update :: "(nat, nat) proto" where
  "proto_stale_update =
     \<lparr> pbase  = [0 \<mapsto> 1],
       psrc   = [(ec1, Update 0 2)],
       pscope = {0},
       pcrash = ec2,
       pfin   = ec3,
       store2 = (\<lambda>f. if ec3 \<le> f then [0 \<mapsto> 2] else [0 \<mapsto> 1]) \<rparr>"

lemma proto_stale_update_mismatch_at_crash:
  "mismatch_at proto_stale_update (pcrash proto_stale_update) 0"
  by (simp add: mismatch_at_def proto_stale_update_def log_image_def
                Src_def latest_src_event_def restrict_def ec_defs Let_def)

lemma proto_stale_update_diverges_at_crash:
  "diverges proto_stale_update (pcrash proto_stale_update)"
  using proto_stale_update_mismatch_at_crash
  by (auto simp: diverges_iff_mismatch_at proto_stale_update_def ec_defs)

definition proto_stale_delete :: "(nat, nat) proto" where
  "proto_stale_delete =
     \<lparr> pbase  = [0 \<mapsto> 1],
       psrc   = [(ec1, Delete 0)],
       pscope = {0},
       pcrash = ec2,
       pfin   = ec3,
       store2 = (\<lambda>f. if ec3 \<le> f then (\<lambda>_. None) else [0 \<mapsto> 1]) \<rparr>"

lemma proto_stale_delete_mismatch_at_crash:
  "mismatch_at proto_stale_delete (pcrash proto_stale_delete) 0"
  by (simp add: mismatch_at_def proto_stale_delete_def log_image_def
                Src_def latest_src_event_def restrict_def ec_defs Let_def)

lemma proto_stale_delete_diverges_at_crash:
  "diverges proto_stale_delete (pcrash proto_stale_delete)"
  using proto_stale_delete_mismatch_at_crash
  by (auto simp: diverges_iff_mismatch_at proto_stale_delete_def ec_defs)

lemma proto_stale_delete_not_asymmetric_store:
  "\<not> asymmetric_store proto_stale_delete (0::nat)"
proof
  assume "asymmetric_store proto_stale_delete (0::nat)"
  then interpret dw: asymmetric_store proto_stale_delete "0::nat" .
  have "log_image proto_stale_delete (pcrash proto_stale_delete) 0 = None"
    by (simp add: log_image_def proto_stale_delete_def Src_def
                  latest_src_event_def restrict_def ec_defs Let_def)
  with dw.C1_log_committed show False by simp
qed


subsection \<open>Result 2 --- bridge / exclusion\<close>

text \<open>
  The \<open>asymmetric_store\<close> locale fixes two parameters \<open>(P, k0)\<close>, so the reified
  predicate is \<open>asymmetric_store P k0\<close>; the exclusion existentially closes \<open>k0\<close>.
\<close>

text \<open>
  \<open>proto_ld\<close> inhabits \<open>log_derived\<close>, so Result 2 (the bridge) is not vacuously
  true: together with the fact \<open>asymmetric_store proto_dw2 0\<close>, both classes are
  non-empty. The \<open>\<forall>f\<close> clause is immediate --- \<open>store2 proto_ld =
  (\<lambda>f. Src (\<lambda>_. None) [] f)\<close>, \<open>pscope proto_ld = {0}\<close> and
  \<open>psrc proto_ld = []\<close>, so \<open>s2 proto_ld f\<close> and \<open>log_image proto_ld f\<close>
  unfold to the \<^emph>\<open>same\<close> term \<open>restrict (Src (\<lambda>_. None) [] f) {0}\<close>
  for every \<open>f\<close> (no \<open>Src\<close> unfolding needed). The remaining conjuncts are
  \<open>wellformed_src_history []\<close> (vacuous) and \<open>ec4 \<le> ec4\<close>.
\<close>

lemma log_derived_proto_ld: "log_derived proto_ld"
  unfolding log_derived_def
proof (intro conjI allI impI)
  show "wellformed_src_history (psrc proto_ld)"
    by (simp add: proto_ld_def wellformed_src_history_def)
next
  show "pcrash proto_ld \<le> pfin proto_ld"
    by (simp add: proto_ld_def)
next
  fix f :: frontier
  show "s2 proto_ld f = log_image proto_ld f"
    by (simp add: log_image_def proto_ld_def)
qed

text \<open>
  The bridge is \<^emph>\<open>tag-free\<close>: it routes through the \<open>store2\<close>-vs-\<open>log_image\<close>
  value collision at the crash frontier alone. At \<open>f = pcrash P\<close> (\<open>\<le> pfin P\<close>
  by \<open>C1_le\<close>) \<open>log_derived\<close> forces \<open>s2 P (pcrash P) = log_image P (pcrash P)\<close>;
  applied at the witness key \<open>k0 \<in> pscope P\<close> this would equate the
  absent-through-crash downstream (\<open>None\<close>, by \<open>C1_store2_absent_through_crash\<close>)
  with the committed log (\<open>\<noteq> None\<close>, by \<open>C1_log_committed\<close>) --- a contradiction.
  No case split on \<open>P\<close>, no wellformedness beyond what \<open>log_derived\<close> and the
  locale already supply.
\<close>

theorem log_derived_excludes_asymmetric_store:
  assumes "log_derived P"
  shows   "\<not> (\<exists>k0. asymmetric_store P k0)"
proof (rule notI)
  assume "\<exists>k0. asymmetric_store P k0"
  then obtain k0 where "asymmetric_store P k0" ..
  then interpret dw: asymmetric_store P k0 .
  have le: "pcrash P \<le> pfin P" by (rule dw.C1_le)
  \<comment> \<open>instantiate the \<open>\<forall>f\<close> clause of \<open>log_derived\<close> at the crash frontier\<close>
  from assms le have s2_eq: "s2 P (pcrash P) = log_image P (pcrash P)"
    by (auto simp: log_derived_def)
  \<comment> \<open>apply the function equality at the witness key \<open>k0\<close>\<close>
  have at_k0: "restrict (store2 P (pcrash P)) (pscope P) k0
                 = log_image P (pcrash P) k0"
    using fun_cong[OF s2_eq, of k0] by simp
  \<comment> \<open>\<open>k0 \<in> pscope P\<close> (derived, \<open>k0_in_scope\<close>) drops the restriction on the left\<close>
  from at_k0 dw.k0_in_scope
  have store_eq_log: "store2 P (pcrash P) k0 = log_image P (pcrash P) k0"
    by (simp add: restrict_def)
  have "store2 P (pcrash P) k0 = None"
    by (rule dw.C1_store2_absent_through_crash[OF order_refl])
  moreover have "log_image P (pcrash P) k0 \<noteq> None"
    by (rule dw.C1_log_committed)
  ultimately show False using store_eq_log by simp
qed

theorem crash_agreement_excludes_asymmetric_store:
  assumes "s2 P (pcrash P) = log_image P (pcrash P)"
  shows   "\<not> (\<exists>k0. asymmetric_store P k0)"
proof
  assume "\<exists>k0. asymmetric_store P k0"
  then obtain k0 where "asymmetric_store P k0" ..
  then interpret dw: asymmetric_store P k0 .
  have at_k0: "restrict (store2 P (pcrash P)) (pscope P) k0 =
               log_image P (pcrash P) k0"
    using fun_cong[OF assms, of k0] by simp
  with dw.k0_in_scope have store_eq_log:
    "store2 P (pcrash P) k0 = log_image P (pcrash P) k0"
    by (simp add: restrict_def)
  have "store2 P (pcrash P) k0 = None"
    by (rule dw.C1_store2_absent_through_crash[OF order_refl])
  moreover have "log_image P (pcrash P) k0 \<noteq> None"
    by (rule dw.C1_log_committed)
  ultimately show False using store_eq_log by simp
qed


subsection \<open>Result 2 strengthened --- exclusion over the larger two-frontier class\<close>

text \<open>
  \<open>log_derived\<close> demands downstream/authority agreement on scope at \<^emph>\<open>every\<close>
  frontier up to completion, yet the exclusion (Result 2) consumes only
  agreement at the \<^emph>\<open>crash\<close> frontier. We therefore weaken the positive class to
  \<open>log_derived_weak\<close>: agreement on scope at the crash frontier \<^emph>\<open>and\<close> at the
  final frontier only --- the downstream is correct at the two boundaries but
  may lag in between. This is a strictly larger class that tolerates a realistic
  lag-then-catch-up replica, and the identical exclusion still holds over it.
\<close>

definition log_derived_weak :: "('k, 'v) proto \<Rightarrow> bool" where
  "log_derived_weak P \<longleftrightarrow>
     wellformed_src_history (psrc P)
   \<and> pcrash P \<le> pfin P
   \<and> s2 P (pcrash P) = log_image P (pcrash P)
   \<and> s2 P (pfin P) = log_image P (pfin P)"

text \<open>
  Containment: \<open>log_derived\<close> implies \<open>log_derived_weak\<close>, since agreement at every
  frontier up to completion specialises to the crash and final frontiers (both
  \<open>\<le> pfin P\<close>).
\<close>

lemma log_derived_imp_log_derived_weak:
  assumes "log_derived P"
  shows   "log_derived_weak P"
proof -
  from assms have wf: "wellformed_src_history (psrc P)"
    and le: "pcrash P \<le> pfin P"
    and ag: "\<forall>f. f \<le> pfin P \<longrightarrow> s2 P f = log_image P f"
    by (auto simp: log_derived_def)
  from ag le have "s2 P (pcrash P) = log_image P (pcrash P)" by blast
  moreover from ag have "s2 P (pfin P) = log_image P (pfin P)"
    by (meson order_refl)
  ultimately show ?thesis using wf le by (simp add: log_derived_weak_def)
qed

theorem log_derived_iff_no_divergence_before_completion:
  "log_derived P \<longleftrightarrow>
     wellformed_src_history (psrc P)
   \<and> pcrash P \<le> pfin P
   \<and> (\<forall>f. f \<le> pfin P \<longrightarrow> \<not> diverges P f)"
proof
  assume ld: "log_derived P"
  hence wf: "wellformed_src_history (psrc P)"
    and le: "pcrash P \<le> pfin P"
    and agree: "\<forall>f. f \<le> pfin P \<longrightarrow> s2 P f = log_image P f"
    by (auto simp: log_derived_def)
  from agree have no_div: "\<forall>f. f \<le> pfin P \<longrightarrow> \<not> diverges P f"
    by (simp add: diverges_iff_s2_neq_log_image)
  show "wellformed_src_history (psrc P) \<and>
        pcrash P \<le> pfin P \<and>
        (\<forall>f. f \<le> pfin P \<longrightarrow> \<not> diverges P f)"
    using wf le no_div by blast
next
  assume rhs:
    "wellformed_src_history (psrc P) \<and>
     pcrash P \<le> pfin P \<and>
     (\<forall>f. f \<le> pfin P \<longrightarrow> \<not> diverges P f)"
  hence wf: "wellformed_src_history (psrc P)"
    and le: "pcrash P \<le> pfin P"
    and no_div: "\<forall>f. f \<le> pfin P \<longrightarrow> \<not> diverges P f"
    by blast+
  have agree: "\<forall>f. f \<le> pfin P \<longrightarrow> s2 P f = log_image P f"
  proof (intro allI impI)
    fix f
    assume f_le: "f \<le> pfin P"
    with no_div have "\<not> diverges P f" by blast
    with f_le show "s2 P f = log_image P f"
      by (simp add: diverges_iff_s2_neq_log_image)
  qed
  show "log_derived P"
    using wf le agree by (simp add: log_derived_def)
qed

theorem log_derived_weak_iff_no_boundary_divergence:
  "log_derived_weak P \<longleftrightarrow>
     wellformed_src_history (psrc P)
   \<and> pcrash P \<le> pfin P
   \<and> \<not> diverges P (pcrash P)
   \<and> \<not> diverges P (pfin P)"
proof
  assume weak: "log_derived_weak P"
  hence wf: "wellformed_src_history (psrc P)"
    and le: "pcrash P \<le> pfin P"
    and crash_agree: "s2 P (pcrash P) = log_image P (pcrash P)"
    and fin_agree: "s2 P (pfin P) = log_image P (pfin P)"
    by (auto simp: log_derived_weak_def)
  have "\<not> diverges P (pcrash P)"
    using crash_agree le by (simp add: diverges_iff_s2_neq_log_image)
  moreover have "\<not> diverges P (pfin P)"
    using fin_agree by (simp add: diverges_iff_s2_neq_log_image)
  ultimately show "wellformed_src_history (psrc P) \<and>
                   pcrash P \<le> pfin P \<and>
                   \<not> diverges P (pcrash P) \<and>
                   \<not> diverges P (pfin P)"
    using wf le by blast
next
  assume rhs:
    "wellformed_src_history (psrc P) \<and>
     pcrash P \<le> pfin P \<and>
     \<not> diverges P (pcrash P) \<and>
     \<not> diverges P (pfin P)"
  hence wf: "wellformed_src_history (psrc P)"
    and le: "pcrash P \<le> pfin P"
    and no_crash: "\<not> diverges P (pcrash P)"
    and no_fin: "\<not> diverges P (pfin P)"
    by blast+
  from no_crash le have crash_agree:
    "s2 P (pcrash P) = log_image P (pcrash P)"
    by (simp add: diverges_iff_s2_neq_log_image)
  from no_fin have fin_agree:
    "s2 P (pfin P) = log_image P (pfin P)"
    by (simp add: diverges_iff_s2_neq_log_image)
  show "log_derived_weak P"
    using wf le crash_agree fin_agree by (simp add: log_derived_weak_def)
qed

theorem log_derived_weak_excludes_crash_mismatch:
  assumes weak: "log_derived_weak P"
  shows "\<not> (\<exists>k0. crash_mismatch P k0)"
proof
  assume "\<exists>k0. crash_mismatch P k0"
  then obtain k0 where cm: "crash_mismatch P k0" ..
  have no_crash: "\<not> diverges P (pcrash P)"
    using weak log_derived_weak_iff_no_boundary_divergence by blast
  have crash_div: "diverges P (pcrash P)"
    by (rule crash_mismatch_class_diverges[OF cm])
  from no_crash crash_div show False by simp
qed

corollary log_derived_excludes_crash_mismatch:
  assumes "log_derived P"
  shows "\<not> (\<exists>k0. crash_mismatch P k0)"
  by (rule log_derived_weak_excludes_crash_mismatch
      [OF log_derived_imp_log_derived_weak[OF assms]])

text \<open>
  The strengthened exclusion: no protocol in the larger \<open>log_derived_weak\<close> class
  is an asymmetric store. The proof is the original crash-frontier value
  collision --- it consumes only the crash-frontier conjunct of
  \<open>log_derived_weak\<close> (the final-frontier conjunct is part of the class
  definition, not used by the exclusion).
\<close>

theorem log_derived_weak_excludes_asymmetric_store:
  assumes "log_derived_weak P"
  shows   "\<not> (\<exists>k0. asymmetric_store P k0)"
proof (rule notI)
  assume "\<exists>k0. asymmetric_store P k0"
  then obtain k0 where "asymmetric_store P k0" ..
  then interpret dw: asymmetric_store P k0 .
  from assms have s2_eq: "s2 P (pcrash P) = log_image P (pcrash P)"
    by (simp add: log_derived_weak_def)
  have at_k0: "restrict (store2 P (pcrash P)) (pscope P) k0
                 = log_image P (pcrash P) k0"
    using fun_cong[OF s2_eq, of k0] by simp
  from at_k0 dw.k0_in_scope
  have store_eq_log: "store2 P (pcrash P) k0 = log_image P (pcrash P) k0"
    by (simp add: restrict_def)
  have "store2 P (pcrash P) k0 = None"
    by (rule dw.C1_store2_absent_through_crash[OF order_refl])
  moreover have "log_image P (pcrash P) k0 \<noteq> None"
    by (rule dw.C1_log_committed)
  ultimately show False using store_eq_log by simp
qed


subsection \<open>The containment is strict: a lag-then-catch-up witness\<close>

text \<open>
  \<open>proto_lag\<close> lies in \<open>log_derived_weak\<close> but not in \<open>log_derived\<close>. The authority
  commits an \<open>Insert\<close> at \<open>ec3\<close>; the downstream is absent through \<open>ec3\<close> and catches
  up at \<open>ec4\<close>. It agrees with the authority on scope at the crash frontier \<open>ec1\<close>
  (both empty: the insert has not yet happened) and at completion \<open>ec4\<close> (both
  \<open>[0 \<mapsto> 7]\<close>), but lags at the intermediate frontier \<open>ec3\<close>, where the authority is
  already present. So \<open>log_derived\<close> is a \<^emph>\<open>proper\<close> subclass of \<open>log_derived_weak\<close>,
  and the strengthened exclusion is over a strictly larger class. The lagging
  replica is itself \<^emph>\<open>not\<close> a dual write (its authority is not committed at its
  crash frontier), consistent with the exclusion.
\<close>

definition proto_lag :: "(nat, nat) proto" where
  "proto_lag =
     \<lparr> pbase  = (\<lambda>_. None),
       psrc   = [(ec3, Insert 0 7)],
       pscope = {0},
       pcrash = ec1,
       pfin   = ec4,
       store2 = (\<lambda>f. if ec4 \<le> f then [0 \<mapsto> 7] else (\<lambda>_. None)) \<rparr>"

lemma log_derived_weak_proto_lag: "log_derived_weak proto_lag"
  unfolding log_derived_weak_def
proof (intro conjI)
  show "wellformed_src_history (psrc proto_lag)"
    by (simp add: proto_lag_def wellformed_src_history_def ec_defs)
next
  show "pcrash proto_lag \<le> pfin proto_lag"
    by (simp add: proto_lag_def ec_defs)
next
  show "s2 proto_lag (pcrash proto_lag) = log_image proto_lag (pcrash proto_lag)"
    by (simp add: proto_lag_def log_image_def Src_def latest_src_event_def
                  restrict_def ec_defs Let_def)
next
  show "s2 proto_lag (pfin proto_lag) = log_image proto_lag (pfin proto_lag)"
    by (simp add: proto_lag_def log_image_def Src_def latest_src_event_def
                  restrict_def ec_defs Let_def fun_eq_iff)
qed

lemma not_log_derived_proto_lag: "\<not> log_derived proto_lag"
proof
  assume ld: "log_derived proto_lag"
  from ld[unfolded log_derived_def]
  have all: "\<forall>f. f \<le> pfin proto_lag \<longrightarrow> s2 proto_lag f = log_image proto_lag f"
    by blast
  have "ec3 \<le> pfin proto_lag" by (simp add: proto_lag_def ec_defs)
  with all have eq: "s2 proto_lag ec3 = log_image proto_lag ec3" by blast
  have lhs: "s2 proto_lag ec3 0 = None"
    by (simp add: proto_lag_def restrict_def ec_defs)
  have rhs: "log_image proto_lag ec3 0 = Some 7"
    by (simp add: proto_lag_def log_image_def Src_def latest_src_event_def
                  restrict_def ec_defs Let_def)
  from fun_cong[OF eq, of 0] lhs rhs show False by simp
qed

text \<open>
  Strictness, packaged at the witness: \<open>proto_lag\<close> is in \<open>log_derived_weak\<close> but
  not in \<open>log_derived\<close>, so together with \<open>log_derived_imp_log_derived_weak\<close>
  (the \<open>\<subseteq>\<close> direction) the inclusion \<open>log_derived \<subseteq> log_derived_weak\<close> is proper.
\<close>

lemma log_derived_weak_strictly_larger:
  "log_derived_weak proto_lag \<and> \<not> log_derived proto_lag"
  by (rule conjI[OF log_derived_weak_proto_lag not_log_derived_proto_lag])

end
