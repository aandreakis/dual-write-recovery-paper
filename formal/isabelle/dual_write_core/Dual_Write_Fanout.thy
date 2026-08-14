(*  Title:       Dual_Write_Fanout.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Fan-out generalization for the dual-write safety kernel.  A fan-out
    protocol has one source authority and an indexed family of independent
    downstream stores.  The two-store theorem is recovered by projecting any
    one target back to the existing proto record.
*)

theory Dual_Write_Fanout
  imports Dual_Write_Core
begin

section \<open>Fan-out as pairwise downstream projections\<close>

text \<open>
  The core theorem is pairwise: one authority log and one independently-written
  downstream store.  Fan-out keeps the same authority and indexes the
  downstream store by a target identifier.  Each target projection is an
  ordinary \<open>proto\<close>, so the existing two-store mismatch theorem remains the
  primitive proof step.
\<close>

record ('i, 'k, 'v) fanout_proto =
  fbase  :: "'k \<rightharpoonup> 'v"
  fsrc   :: "('k, 'v) src_history"
  fscope :: "'k set"
  fcrash :: frontier
  ffin   :: frontier
  fstore :: "'i \<Rightarrow> frontier \<Rightarrow> ('k \<rightharpoonup> 'v)"

definition fanout_log_image
  :: "('i, 'k, 'v) fanout_proto \<Rightarrow> frontier \<Rightarrow> ('k \<rightharpoonup> 'v)"
where
  "fanout_log_image F f =
     restrict (Src (fbase F) (fsrc F) f) (fscope F)"

definition fanout_target_proto
  :: "('i, 'k, 'v) fanout_proto \<Rightarrow> 'i \<Rightarrow> ('k, 'v) proto"
where
  "fanout_target_proto F i =
     \<lparr> pbase = fbase F,
       psrc = fsrc F,
       pscope = fscope F,
       pcrash = fcrash F,
       pfin = ffin F,
       store2 = fstore F i \<rparr>"

lemma fanout_target_proto_fields [simp]:
  "pbase (fanout_target_proto F i) = fbase F"
  "psrc (fanout_target_proto F i) = fsrc F"
  "pscope (fanout_target_proto F i) = fscope F"
  "pcrash (fanout_target_proto F i) = fcrash F"
  "pfin (fanout_target_proto F i) = ffin F"
  "store2 (fanout_target_proto F i) = fstore F i"
  by (simp_all add: fanout_target_proto_def)

lemma restrict_log_image_scope [simp]:
  "restrict (log_image P f) (pscope P) = log_image P f"
  by (rule ext) (simp add: log_image_def restrict_def)

abbreviation fanout_s2
  :: "('i, 'k, 'v) fanout_proto \<Rightarrow> 'i \<Rightarrow>
      frontier \<Rightarrow> ('k \<rightharpoonup> 'v)"
where
  "fanout_s2 F i f \<equiv> restrict (fstore F i f) (fscope F)"

definition fanout_mismatch_at
  :: "('i, 'k, 'v) fanout_proto \<Rightarrow> 'i \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> bool"
where
  "fanout_mismatch_at F i f k \<longleftrightarrow>
     k \<in> fscope F \<and> fstore F i f k \<noteq> fanout_log_image F f k"

definition fanout_target_diverges
  :: "('i, 'k, 'v) fanout_proto \<Rightarrow> 'i \<Rightarrow> frontier \<Rightarrow> bool"
where
  "fanout_target_diverges F i f \<longleftrightarrow>
     f \<le> ffin F \<and> (\<exists>k. fanout_mismatch_at F i f k)"

definition fanout_diverges
  :: "('i, 'k, 'v) fanout_proto \<Rightarrow> frontier \<Rightarrow> bool"
where
  "fanout_diverges F f \<longleftrightarrow>
     f \<le> ffin F \<and> (\<exists>i k. fanout_mismatch_at F i f k)"

definition fanout_target_lags_authority_at
  :: "('i, 'k, 'v) fanout_proto \<Rightarrow> 'i \<Rightarrow> frontier \<Rightarrow> 'k \<Rightarrow> bool"
where
  "fanout_target_lags_authority_at F i f k \<longleftrightarrow>
     fanout_mismatch_at F i f k"

definition fanout_some_target_lags_authority_at
  :: "('i, 'k, 'v) fanout_proto \<Rightarrow> frontier \<Rightarrow> bool"
where
  "fanout_some_target_lags_authority_at F f \<longleftrightarrow>
     (\<exists>i k. fanout_target_lags_authority_at F i f k)"

definition fanout_diverges_on
  :: "('i, 'k, 'v) fanout_proto \<Rightarrow> 'i set \<Rightarrow> frontier \<Rightarrow> bool"
where
  "fanout_diverges_on F I f \<longleftrightarrow>
     f \<le> ffin F \<and> (\<exists>i \<in> I. \<exists>k. fanout_mismatch_at F i f k)"

definition fanout_some_target_lags_authority_on
  :: "('i, 'k, 'v) fanout_proto \<Rightarrow> 'i set \<Rightarrow> frontier \<Rightarrow> bool"
where
  "fanout_some_target_lags_authority_on F I f \<longleftrightarrow>
     (\<exists>i \<in> I. \<exists>k. fanout_target_lags_authority_at F i f k)"

lemma fanout_target_proto_log_image [simp]:
  "log_image (fanout_target_proto F i) f = fanout_log_image F f"
  by (simp add: fanout_target_proto_def fanout_log_image_def log_image_def)

lemma fanout_target_proto_mismatch_at [simp]:
  "mismatch_at (fanout_target_proto F i) f k \<longleftrightarrow>
     fanout_mismatch_at F i f k"
  by (simp add: fanout_target_proto_def fanout_mismatch_at_def
                mismatch_at_def fanout_log_image_def log_image_def)

lemma fanout_target_proto_diverges [simp]:
  "diverges (fanout_target_proto F i) f \<longleftrightarrow>
     fanout_target_diverges F i f"
  by (auto simp: diverges_iff_mismatch_at fanout_target_diverges_def)

theorem fanout_diverges_iff_exists_target_diverges:
  "fanout_diverges F f \<longleftrightarrow>
     (\<exists>i. diverges (fanout_target_proto F i) f)"
  by (auto simp: fanout_diverges_def fanout_target_diverges_def)

theorem fanout_diverges_on_iff_some_target_diverges:
  "fanout_diverges_on F I f \<longleftrightarrow>
     (\<exists>i \<in> I. diverges (fanout_target_proto F i) f)"
  by (auto simp: fanout_diverges_on_def fanout_target_diverges_def)

theorem fanout_crash_diverges_iff_some_target_diverges:
  "fanout_diverges F (fcrash F) \<longleftrightarrow>
     (\<exists>i. diverges (fanout_target_proto F i) (fcrash F))"
  by (rule fanout_diverges_iff_exists_target_diverges)

theorem fanout_crash_diverges_on_iff_some_target_diverges:
  "fanout_diverges_on F I (fcrash F) \<longleftrightarrow>
     (\<exists>i \<in> I. diverges (fanout_target_proto F i) (fcrash F))"
  by (rule fanout_diverges_on_iff_some_target_diverges)

theorem fanout_diverges_iff_some_target_lags_authority:
  "fanout_diverges F f \<longleftrightarrow>
     f \<le> ffin F \<and> fanout_some_target_lags_authority_at F f"
  by (auto simp: fanout_diverges_def
                 fanout_some_target_lags_authority_at_def
                 fanout_target_lags_authority_at_def)

theorem fanout_diverges_on_iff_some_target_lags_authority:
  "fanout_diverges_on F I f \<longleftrightarrow>
     f \<le> ffin F \<and> fanout_some_target_lags_authority_on F I f"
  by (auto simp: fanout_diverges_on_def
                 fanout_some_target_lags_authority_on_def
                 fanout_target_lags_authority_at_def)

theorem fanout_crash_diverges_iff_some_target_lags_authority:
  "fanout_diverges F (fcrash F) \<longleftrightarrow>
     fcrash F \<le> ffin F
   \<and> fanout_some_target_lags_authority_at F (fcrash F)"
  by (rule fanout_diverges_iff_some_target_lags_authority)

theorem fanout_crash_diverges_on_iff_some_target_lags_authority:
  "fanout_diverges_on F I (fcrash F) \<longleftrightarrow>
     fcrash F \<le> ffin F
   \<and> fanout_some_target_lags_authority_on F I (fcrash F)"
  by (rule fanout_diverges_on_iff_some_target_lags_authority)

subsection \<open>Pairwise negative and positive lifts\<close>

definition fanout_target_asymmetric_store
  :: "('i, 'k, 'v) fanout_proto \<Rightarrow> 'i \<Rightarrow> 'k \<Rightarrow> bool"
where
  "fanout_target_asymmetric_store F i k \<longleftrightarrow>
     asymmetric_store (fanout_target_proto F i) k"

theorem fanout_target_asymmetric_store_imp_crash_diverges:
  assumes "fanout_target_asymmetric_store F i k"
  shows "fanout_diverges F (fcrash F)"
proof -
  from assms have "asymmetric_store (fanout_target_proto F i) k"
    by (simp add: fanout_target_asymmetric_store_def)
  hence "diverges (fanout_target_proto F i) (pcrash (fanout_target_proto F i))"
    by (rule asymmetric_store_class_diverges)
  hence "diverges (fanout_target_proto F i) (fcrash F)"
    by simp
  thus ?thesis
    by (auto simp: fanout_crash_diverges_iff_some_target_diverges)
qed

theorem fanout_target_asymmetric_store_imp_crash_diverges_on:
  assumes "i \<in> I"
      and "fanout_target_asymmetric_store F i k"
  shows "fanout_diverges_on F I (fcrash F)"
proof -
  from assms(2) have "asymmetric_store (fanout_target_proto F i) k"
    by (simp add: fanout_target_asymmetric_store_def)
  hence "diverges (fanout_target_proto F i) (pcrash (fanout_target_proto F i))"
    by (rule asymmetric_store_class_diverges)
  hence "diverges (fanout_target_proto F i) (fcrash F)"
    by simp
  with assms(1) show ?thesis
    by (auto simp: fanout_crash_diverges_on_iff_some_target_diverges)
qed

definition fanout_log_derived :: "('i, 'k, 'v) fanout_proto \<Rightarrow> bool"
where
  "fanout_log_derived F \<longleftrightarrow>
     wellformed_src_history (fsrc F)
   \<and> fcrash F \<le> ffin F
   \<and> (\<forall>i f. f \<le> ffin F \<longrightarrow>
        fanout_s2 F i f = fanout_log_image F f)"

definition fanout_log_derived_on
  :: "('i, 'k, 'v) fanout_proto \<Rightarrow> 'i set \<Rightarrow> bool"
where
  "fanout_log_derived_on F I \<longleftrightarrow>
     wellformed_src_history (fsrc F)
   \<and> fcrash F \<le> ffin F
   \<and> (\<forall>i \<in> I. \<forall>f. f \<le> ffin F \<longrightarrow>
        fanout_s2 F i f = fanout_log_image F f)"

theorem fanout_log_derived_iff_all_targets_log_derived:
  "fanout_log_derived F \<longleftrightarrow>
     wellformed_src_history (fsrc F)
   \<and> fcrash F \<le> ffin F
   \<and> (\<forall>i. log_derived (fanout_target_proto F i))"
  by (auto simp: fanout_log_derived_def log_derived_def
                 fanout_target_proto_def fanout_log_image_def log_image_def)

theorem fanout_log_derived_on_iff_all_targets_log_derived:
  "fanout_log_derived_on F I \<longleftrightarrow>
     wellformed_src_history (fsrc F)
   \<and> fcrash F \<le> ffin F
   \<and> (\<forall>i \<in> I. log_derived (fanout_target_proto F i))"
  by (auto simp: fanout_log_derived_on_def log_derived_def
                 fanout_target_proto_def fanout_log_image_def log_image_def)

theorem fanout_log_derived_no_divergence:
  assumes "fanout_log_derived F"
      and "f \<le> ffin F"
  shows "\<not> fanout_diverges F f"
proof
  assume "fanout_diverges F f"
  then obtain i where div: "diverges (fanout_target_proto F i) f"
    by (auto simp: fanout_diverges_iff_exists_target_diverges)
  from assms(1) have ld: "log_derived (fanout_target_proto F i)"
    by (simp add: fanout_log_derived_iff_all_targets_log_derived)
  from ld have no_div:
    "\<forall>f. f \<le> pfin (fanout_target_proto F i) \<longrightarrow>
      \<not> diverges (fanout_target_proto F i) f"
    by (simp add: log_derived_iff_no_divergence_before_completion)
  from assms(2) have "f \<le> pfin (fanout_target_proto F i)"
    by simp
  with no_div div show False by blast
qed

theorem fanout_log_derived_on_no_divergence:
  assumes "fanout_log_derived_on F I"
      and "f \<le> ffin F"
  shows "\<not> fanout_diverges_on F I f"
proof
  assume "fanout_diverges_on F I f"
  then obtain i where in_I: "i \<in> I"
      and div: "diverges (fanout_target_proto F i) f"
    by (auto simp: fanout_diverges_on_iff_some_target_diverges)
  from assms(1) in_I have ld: "log_derived (fanout_target_proto F i)"
    by (simp add: fanout_log_derived_on_iff_all_targets_log_derived)
  from ld have no_div:
    "\<forall>f. f \<le> pfin (fanout_target_proto F i) \<longrightarrow>
      \<not> diverges (fanout_target_proto F i) f"
    by (simp add: log_derived_iff_no_divergence_before_completion)
  from assms(2) have "f \<le> pfin (fanout_target_proto F i)"
    by simp
  with no_div div show False by blast
qed

theorem fanout_log_derived_excludes_target_asymmetric_store:
  assumes "fanout_log_derived F"
  shows "\<not> (\<exists>i k. fanout_target_asymmetric_store F i k)"
  using assms log_derived_excludes_asymmetric_store
  by (auto simp: fanout_log_derived_iff_all_targets_log_derived
                 fanout_target_asymmetric_store_def)

theorem fanout_log_derived_on_excludes_target_asymmetric_store:
  assumes "fanout_log_derived_on F I"
  shows "\<not> (\<exists>i \<in> I. \<exists>k. fanout_target_asymmetric_store F i k)"
  using assms log_derived_excludes_asymmetric_store
  by (auto simp: fanout_log_derived_on_iff_all_targets_log_derived
                 fanout_target_asymmetric_store_def)

lemma all_targets_agree_at_crash_no_fanout_divergence_on:
  assumes "\<forall>i \<in> I.
      fanout_s2 F i (fcrash F) = fanout_log_image F (fcrash F)"
  shows "\<not> fanout_diverges_on F I (fcrash F)"
proof
  assume "fanout_diverges_on F I (fcrash F)"
  then obtain i k where in_I: "i \<in> I"
      and scoped: "k \<in> fscope F"
      and neq:
        "fstore F i (fcrash F) k \<noteq> fanout_log_image F (fcrash F) k"
    by (auto simp: fanout_diverges_on_def fanout_mismatch_at_def)
  from assms in_I have eq:
    "fanout_s2 F i (fcrash F) = fanout_log_image F (fcrash F)"
    by blast
  from fun_cong[OF eq, of k] scoped have
    "fstore F i (fcrash F) k = fanout_log_image F (fcrash F) k"
    by (simp add: restrict_def)
  with neq show False by simp
qed

subsection \<open>The two-store theorem as the single-target case\<close>

definition unit_fanout_of_proto :: "('k, 'v) proto \<Rightarrow> (unit, 'k, 'v) fanout_proto"
where
  "unit_fanout_of_proto P =
     \<lparr> fbase = pbase P,
       fsrc = psrc P,
       fscope = pscope P,
       fcrash = pcrash P,
       ffin = pfin P,
       fstore = (\<lambda>_. store2 P) \<rparr>"

lemma fanout_target_proto_unit [simp]:
  "fanout_target_proto (unit_fanout_of_proto P) () = P"
  by (simp add: unit_fanout_of_proto_def fanout_target_proto_def)

theorem unit_fanout_diverges_iff_proto_diverges:
  "fanout_diverges (unit_fanout_of_proto P) f \<longleftrightarrow> diverges P f"
  by (auto simp: fanout_diverges_iff_exists_target_diverges)

theorem unit_fanout_diverges_on_iff_proto_diverges:
  "fanout_diverges_on (unit_fanout_of_proto P) {()} f \<longleftrightarrow> diverges P f"
  by (auto simp: fanout_diverges_on_iff_some_target_diverges)

theorem unit_fanout_crash_diverges_iff_proto_crash_diverges:
  "fanout_diverges (unit_fanout_of_proto P)
      (fcrash (unit_fanout_of_proto P))
   \<longleftrightarrow> diverges P (pcrash P)"
proof -
  have "fcrash (unit_fanout_of_proto P) = pcrash P"
    by (simp add: unit_fanout_of_proto_def)
  thus ?thesis
    by (simp add: unit_fanout_diverges_iff_proto_diverges)
qed

theorem unit_fanout_log_derived_iff_proto_log_derived:
  "fanout_log_derived (unit_fanout_of_proto P) \<longleftrightarrow> log_derived P"
  by (auto simp: fanout_log_derived_iff_all_targets_log_derived
                unit_fanout_of_proto_def fanout_log_image_def
                log_derived_def log_image_def)

theorem unit_fanout_log_derived_on_iff_proto_log_derived:
  "fanout_log_derived_on (unit_fanout_of_proto P) {()} \<longleftrightarrow> log_derived P"
  by (auto simp: fanout_log_derived_on_iff_all_targets_log_derived
                unit_fanout_of_proto_def fanout_log_image_def
                log_derived_def log_image_def)

lemma unit_fanout_asymmetric_store_recovers_two_store:
  assumes "asymmetric_store P k"
  shows "fanout_diverges (unit_fanout_of_proto P)
      (fcrash (unit_fanout_of_proto P))"
  using assms asymmetric_store_class_diverges
  by (simp add: unit_fanout_crash_diverges_iff_proto_crash_diverges)

lemma unit_fanout_proto_ld_log_derived:
  "fanout_log_derived (unit_fanout_of_proto proto_ld)"
  by (simp add: unit_fanout_log_derived_iff_proto_log_derived
                log_derived_proto_ld)

subsection \<open>Closed fan-out witness\<close>

definition fanout_one_lag_proto :: "(nat, nat, nat) fanout_proto"
where
  "fanout_one_lag_proto =
     \<lparr> fbase = pbase proto_dw2,
       fsrc = psrc proto_dw2,
       fscope = pscope proto_dw2,
       fcrash = pcrash proto_dw2,
       ffin = pfin proto_dw2,
       fstore =
         (\<lambda>i f. if i = 0 then store2 proto_dw2 f else log_image proto_dw2 f) \<rparr>"

lemma fanout_one_lag_target0_proto [simp]:
  "fanout_target_proto fanout_one_lag_proto (0::nat) = proto_dw2"
  by (simp add: fanout_one_lag_proto_def fanout_target_proto_def proto_dw2_def)

lemma fanout_one_lag_target0_asymmetric_store:
  "fanout_target_asymmetric_store fanout_one_lag_proto (0::nat) (0::nat)"
  by (simp add: fanout_target_asymmetric_store_def proto_dw2_asymmetric_store)

lemma fanout_one_lag_diverges_at_crash:
  "fanout_diverges fanout_one_lag_proto (fcrash fanout_one_lag_proto)"
  using fanout_one_lag_target0_asymmetric_store
  by (rule fanout_target_asymmetric_store_imp_crash_diverges)

lemma fanout_one_lag_diverges_on_targets_at_crash:
  "fanout_diverges_on fanout_one_lag_proto {0, 1}
      (fcrash fanout_one_lag_proto)"
  by (rule fanout_target_asymmetric_store_imp_crash_diverges_on
        [where i = "0::nat" and k = "0::nat"])
     (simp_all add: fanout_one_lag_target0_asymmetric_store)

lemma fanout_one_lag_target1_not_diverges_at_crash:
  "\<not> diverges (fanout_target_proto fanout_one_lag_proto (1::nat))
        (fcrash fanout_one_lag_proto)"
proof -
  have "\<not> fanout_target_diverges
      fanout_one_lag_proto (1::nat) (fcrash fanout_one_lag_proto)"
    by (auto simp: fanout_target_diverges_def fanout_mismatch_at_def
                   fanout_one_lag_proto_def fanout_log_image_def
                   log_image_def restrict_def)
  thus ?thesis by simp
qed

lemma fanout_one_lag_not_log_derived_on_targets:
  "\<not> fanout_log_derived_on fanout_one_lag_proto {0, 1}"
proof
  assume ld: "fanout_log_derived_on fanout_one_lag_proto {0, 1}"
  have no_div:
    "\<not> fanout_diverges_on fanout_one_lag_proto {0, 1}
        (fcrash fanout_one_lag_proto)"
    by (rule fanout_log_derived_on_no_divergence[OF ld])
       (simp add: fanout_one_lag_proto_def proto_dw2_def ec_defs)
  with fanout_one_lag_diverges_on_targets_at_crash show False by simp
qed

end
