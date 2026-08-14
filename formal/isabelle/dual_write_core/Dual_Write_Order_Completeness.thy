(*  Title:       Dual_Write_Order_Completeness.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Image completeness for crash-safety: the delivery-order axis.

    Companion to Dual_Write_Image_Completeness (durability axis).  This theory
    settles the most counterintuitive stream candidate: does the ORDER of the
    delivered CDC stream carry a two-sided crash-safety characterization?  It
    does not --- delivery order is invisible to crash-safety except where it
    already shows up as an image mismatch.

    The structural root is Src_eq_on_key_sub: the scoped image at a key factors
    through that key's subsequence (key_sub), so cross-key delivery order never
    changes the image.  From it:

      Necessity fails.  A cross-key reorder (CK_down) is image-faithful at every
      frontier yet not a wellformed (in-order) history; and even a same-key
      EQUAL-value swap (SK_down) is image-identical yet reordered --- so
      image-safety does not force in-order delivery, even restricted to
      full-delivery (permutation, no drop) downstreams.

      Sufficiency fails.  In-order delivery that DROPS a later update (ST_down)
      is perfectly wellformed yet image-unfaithful --- so order alone carries no
      safety.

      The collapse.  image_faithful_invariant_under_key_sub_agreement: image
      faithfulness depends only on the per-key subsequences, hence is invariant
      under every cross-key permutation.  The only harmful reorder is a same-key
      DISTINCT-value swap, and that is already an observable_mismatch
      (RV_observable_mismatch) --- inside the landed image characterization.

    Adds no axiom, sorry, or oracle; headline facts are certified oracle-free by
    a separate build gate.
*)

theory Dual_Write_Order_Completeness
  imports
    Dual_Write_Execution
    Dual_Write_Relay
    Dual_Write_Converse
begin

section \<open>Part A: the per-key subsequence\<close>

text \<open>The per-key subsequence of a history keeps exactly the events touching a
  given key.  The image at that key is a function of this subsequence only ---
  the exact sense in which cross-key delivery order is image-invisible.\<close>

definition key_sub
  :: "('k, 'v) src_history \<Rightarrow> 'k \<Rightarrow> ('k, 'v) src_history"
where
  "key_sub H k = filter (\<lambda>x. key_of (snd x) = k) H"

lemma key_sub_Nil [simp]: "key_sub [] k = []"
  by (simp add: key_sub_def)

lemma key_sub_snoc:
  "key_sub (H @ [x]) k =
     (if key_of (snd x) = k then key_sub H k @ [x] else key_sub H k)"
  by (simp add: key_sub_def)

text \<open>The image factors through the per-key subsequence: dropping events for
  other keys never changes @{term "Src b H f k"}.\<close>

lemma Src_eq_on_key_sub:
  "Src b H f k = Src b (key_sub H k) f k"
proof (induction H rule: rev_induct)
  case Nil show ?case by simp
next
  case (snoc x H)
  obtain c e where x_def: "x = (c, e)" by (cases x)
  show ?case
  proof (cases "key_of (snd x) = k")
    case True
    then have key_e: "key_of e = k" using x_def by simp
    have kept: "key_sub (H @ [x]) k = key_sub H k @ [x]"
      using True by (simp add: key_sub_snoc)
    show ?thesis
    proof (cases "src_le c f")
      case True
      then have cf: "c \<le> f" by (simp add: src_le_eq_less_eq)
      have l: "Src b (H @ [x]) f k = event_result e"
        using Src_snoc_event_at_key[OF key_e cf] x_def by simp
      have r: "Src b (key_sub H k @ [x]) f k = event_result e"
        using Src_snoc_event_at_key[OF key_e cf] x_def by simp
      show ?thesis using l r kept by simp
    next
      case False
      have inv: "\<not> visible_src_event_at f k x"
        using False x_def by (simp add: visible_src_event_at_def src_le_eq_less_eq)
      have l: "Src b (H @ [x]) f k = Src b H f k"
        by (rule Src_snoc_invisible[OF inv])
      have r: "Src b (key_sub H k @ [x]) f k = Src b (key_sub H k) f k"
        by (rule Src_snoc_invisible[OF inv])
      show ?thesis using l r kept snoc.IH by simp
    qed
  next
    case False
    have inv: "\<not> visible_src_event_at f k x"
      using False by (simp add: visible_src_event_at_def)
    have "Src b (H @ [x]) f k = Src b H f k"
      by (rule Src_snoc_invisible[OF inv])
    with False snoc.IH show ?thesis by (simp add: key_sub_snoc)
  qed
qed


section \<open>Part B: the candidate safety notion and discipline\<close>

text \<open>Image-faithfulness on scope: the downstream image equals the source image
  on scope at a frontier (the store side is @{const Src} of the delivered
  history, the authority side @{const Src} of the source history), lifted to
  every frontier for the running-image-faithful shape.\<close>

definition image_faithful_on
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) src_history \<Rightarrow> ('k, 'v) src_history
      \<Rightarrow> 'k set \<Rightarrow> frontier \<Rightarrow> bool"
where
  "image_faithful_on b0 D H K f \<longleftrightarrow>
     (\<forall>k \<in> K. Src b0 D f k = Src b0 H f k)"

definition image_faithful_all
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) src_history \<Rightarrow> ('k, 'v) src_history
      \<Rightarrow> 'k set \<Rightarrow> bool"
where
  "image_faithful_all b0 D H K \<longleftrightarrow>
     (\<forall>f. image_faithful_on b0 D H K f)"

text \<open>Per-key no-reorder: every per-key subsequence is a
  @{const wellformed_src_history} (this allows cross-key permutation but forbids
  same-key reorder).  Raw no-reorder --- wellformedness of the whole delivered
  list --- is strictly stronger.\<close>

definition perkey_no_reorder
  :: "('k, 'v) src_history \<Rightarrow> bool"
where
  "perkey_no_reorder D \<longleftrightarrow> (\<forall>k. wellformed_src_history (key_sub D k))"


section \<open>Part C: necessity fails (image-safety does not force no-reorder)\<close>

subsection \<open>Cross-key reorder: image-faithful at every frontier, yet not wellformed\<close>

definition ck_a :: "(nat,nat) source_event" where "ck_a = Insert 0 7"
definition ck_b :: "(nat,nat) source_event" where "ck_b = Insert 1 9"

definition CK_src :: "(nat,nat) src_history" where
  "CK_src = [(ec2, ck_a), (ec3, ck_b)]"
definition CK_down :: "(nat,nat) src_history" where
  "CK_down = [(ec3, ck_b), (ec2, ck_a)]"

lemma CK_image_faithful_all:
  "image_faithful_all (\<lambda>_. None) CK_down CK_src {0,1}"
  unfolding image_faithful_all_def image_faithful_on_def
proof (intro allI ballI)
  fix f k assume "k \<in> {0::nat,1}"
  show "Src (\<lambda>_. None) CK_down f k = Src (\<lambda>_. None) CK_src f k"
    by (cases "src_le ec3 f"; cases "src_le ec2 f")
       (auto simp: CK_down_def CK_src_def ck_a_def ck_b_def Src_def
                   latest_src_event_def Let_def ec_defs src_le_eq_less_eq
             split: if_splits)
qed

lemma CK_down_not_wf: "\<not> wellformed_src_history CK_down"
proof
  assume "wellformed_src_history CK_down"
  then have "src_le (hist_coord (CK_down ! 0)) (hist_coord (CK_down ! Suc 0))"
    by (simp add: wellformed_src_history_def CK_down_def)
  thus False by (simp add: CK_down_def ec_defs src_le_eq_less_eq)
qed

lemma okc_wf_singleton:
  "hist_coord x \<noteq> c0 \<Longrightarrow> wellformed_src_history [x]"
  by (simp add: wellformed_src_history_def source_pos_order_def)

lemma okc_wf_Nil [simp]: "wellformed_src_history []"
  by (simp add: wellformed_src_history_def source_pos_order_def)

lemma CK_down_perkey: "perkey_no_reorder CK_down"
proof (unfold perkey_no_reorder_def, rule allI)
  fix k :: nat
  consider "k = 0" | "k = 1" | "k \<noteq> 0 \<and> k \<noteq> 1" by blast
  then show "wellformed_src_history (key_sub CK_down k)"
  proof cases
    case 1
    then have "key_sub CK_down k = [(ec2, ck_a)]"
      by (simp add: key_sub_def CK_down_def ck_a_def ck_b_def)
    then show ?thesis by (simp add: okc_wf_singleton ec_defs)
  next
    case 2
    then have "key_sub CK_down k = [(ec3, ck_b)]"
      by (simp add: key_sub_def CK_down_def ck_a_def ck_b_def)
    then show ?thesis by (simp add: okc_wf_singleton ec_defs)
  next
    case 3
    then have "key_sub CK_down k = []"
      by (simp add: key_sub_def CK_down_def ck_a_def ck_b_def)
    then show ?thesis by simp
  qed
qed

theorem necessity_fails_crosskey:
  "image_faithful_all (\<lambda>_. None) CK_down CK_src {0,1}
   \<and> perkey_no_reorder CK_down
   \<and> \<not> wellformed_src_history CK_down"
  using CK_image_faithful_all CK_down_perkey CK_down_not_wf by blast

subsection \<open>Same-key equal-value reorder is also image-invisible\<close>

definition sk_a :: "(nat,nat) source_event" where "sk_a = Insert 0 7"
definition sk_b :: "(nat,nat) source_event" where "sk_b = Insert 0 7"

definition SK_src :: "(nat,nat) src_history" where
  "SK_src = [(ec2, sk_a), (ec3, sk_b)]"
definition SK_down :: "(nat,nat) src_history" where
  "SK_down = [(ec3, sk_b), (ec2, sk_a)]"

lemma SK_image_faithful_all:
  "image_faithful_all (\<lambda>_. None) SK_down SK_src {0}"
  unfolding image_faithful_all_def image_faithful_on_def
proof (intro allI ballI)
  fix f k assume "k \<in> {0::nat}"
  show "Src (\<lambda>_. None) SK_down f k = Src (\<lambda>_. None) SK_src f k"
    by (cases "src_le ec3 f"; cases "src_le ec2 f")
       (auto simp: SK_down_def SK_src_def sk_a_def sk_b_def Src_def
                   latest_src_event_def Let_def ec_defs src_le_eq_less_eq
             split: if_splits)
qed

lemma SK_down_not_wf: "\<not> wellformed_src_history SK_down"
proof
  assume "wellformed_src_history SK_down"
  then have "src_le (hist_coord (SK_down ! 0)) (hist_coord (SK_down ! Suc 0))"
    by (simp add: wellformed_src_history_def SK_down_def)
  thus False by (simp add: SK_down_def ec_defs src_le_eq_less_eq)
qed

lemma SK_down_not_perkey: "\<not> perkey_no_reorder SK_down"
proof
  assume "perkey_no_reorder SK_down"
  then have "wellformed_src_history (key_sub SK_down 0)"
    by (simp add: perkey_no_reorder_def)
  moreover have "key_sub SK_down 0 = SK_down"
    by (simp add: key_sub_def SK_down_def sk_a_def sk_b_def)
  ultimately show False using SK_down_not_wf by simp
qed

theorem necessity_fails_samekey_equalvalue:
  "image_faithful_all (\<lambda>_. None) SK_down SK_src {0}
   \<and> \<not> perkey_no_reorder SK_down
   \<and> SK_down \<noteq> SK_src"
  using SK_image_faithful_all SK_down_not_perkey
  by (simp add: SK_down_def SK_src_def sk_a_def sk_b_def ec_defs)

text \<open>Even restricting to full delivery (a permutation, nothing dropped),
  image-safety does not force order: @{const SK_down} is a permutation of
  @{const SK_src} that is image-faithful yet not per-key in-order.\<close>

lemma SK_down_perm_of_src: "mset SK_down = mset SK_src"
  by (simp add: SK_down_def SK_src_def)

theorem conditional_necessity_fails_under_full_delivery:
  "mset SK_down = mset SK_src
   \<and> image_faithful_all (\<lambda>_. None) SK_down SK_src {0}
   \<and> \<not> perkey_no_reorder SK_down"
  using SK_down_perm_of_src SK_image_faithful_all SK_down_not_perkey by blast


section \<open>Part D: sufficiency fails (no-reorder does not force image-safety)\<close>

subsection \<open>In-order delivery of a dropped update is wellformed yet unfaithful\<close>

definition st_a :: "(nat,nat) source_event" where "st_a = Insert 0 7"
definition st_b :: "(nat,nat) source_event" where "st_b = Insert 0 9"

definition ST_src :: "(nat,nat) src_history" where
  "ST_src = [(ec2, st_a), (ec3, st_b)]"
definition ST_down :: "(nat,nat) src_history" where
  "ST_down = [(ec2, st_a)]"

lemma ST_down_wf: "wellformed_src_history ST_down"
  by (simp add: ST_down_def wellformed_src_history_def st_a_def ec_defs
                source_pos_order_def src_lt_eq_less src_le_eq_less_eq)

lemma ST_down_perkey: "perkey_no_reorder ST_down"
proof (unfold perkey_no_reorder_def, rule allI)
  fix k :: nat
  show "wellformed_src_history (key_sub ST_down k)"
    by (cases "k = 0")
       (simp_all add: key_sub_def ST_down_def st_a_def ec_defs
                      wellformed_src_history_def source_pos_order_def
                      src_lt_eq_less src_le_eq_less_eq)
qed

lemma ST_image_unfaithful_terminal:
  "\<not> image_faithful_on (\<lambda>_. None) ST_down ST_src {0} ec3"
  unfolding image_faithful_on_def
proof
  assume "\<forall>k \<in> {0::nat}. Src (\<lambda>_. None) ST_down ec3 k = Src (\<lambda>_. None) ST_src ec3 k"
  then have "Src (\<lambda>_. None) ST_down ec3 0 = Src (\<lambda>_. None) ST_src ec3 0" by simp
  moreover have "Src (\<lambda>_. None) ST_down ec3 0 = Some 7"
    by (simp add: ST_down_def st_a_def Src_def latest_src_event_def Let_def
                  ec_defs src_le_eq_less_eq)
  moreover have "Src (\<lambda>_. None) ST_src ec3 0 = Some 9"
    by (simp add: ST_src_def st_a_def st_b_def Src_def latest_src_event_def
                  Let_def ec_defs src_le_eq_less_eq)
  ultimately show False by simp
qed

theorem sufficiency_fails_inorder_drop:
  "perkey_no_reorder ST_down
   \<and> wellformed_src_history ST_down
   \<and> \<not> image_faithful_on (\<lambda>_. None) ST_down ST_src {0} ec3"
  using ST_down_perkey ST_down_wf ST_image_unfaithful_terminal by blast


section \<open>Part E: the collapse (image-safety is order-invariant per-key content)\<close>

text \<open>Image-faithfulness depends only on the per-key subsequences: any two
  delivered histories with the same per-key subsequences are
  image-indistinguishable, however their cross-key order differs.  So the
  discipline image-safety forces is at most per-key subsequence agreement --- an
  image quantity, not an order quantity.\<close>

theorem image_faithful_invariant_under_key_sub_agreement:
  assumes "\<And>k. key_sub D1 k = key_sub D2 k"
  shows "image_faithful_all b0 D1 H K = image_faithful_all b0 D2 H K"
proof -
  have "\<And>f k. Src b0 D1 f k = Src b0 D2 f k"
  proof -
    fix f k
    have "Src b0 D1 f k = Src b0 (key_sub D1 k) f k"
      by (rule Src_eq_on_key_sub)
    also have "\<dots> = Src b0 (key_sub D2 k) f k"
      using assms by simp
    also have "\<dots> = Src b0 D2 f k"
      by (rule Src_eq_on_key_sub[symmetric])
    finally show "Src b0 D1 f k = Src b0 D2 f k" .
  qed
  thus ?thesis
    by (simp add: image_faithful_all_def image_faithful_on_def)
qed


section \<open>Part F: the harmful reorder is exactly an observable mismatch\<close>

text \<open>A same-key distinct-value swap yields a real @{const observable_mismatch}
  under a crash: the harmful part of reorder lives entirely inside
  @{const mismatch_at}, i.e. inside the landed image characterization.  The
  visible/invisible split is exactly distinct-value versus equal-value or
  cross-key.\<close>

definition rv_a :: "(nat,nat) source_event" where "rv_a = Insert 0 7"
definition rv_b :: "(nat,nat) source_event" where "rv_b = Insert 0 9"

definition RV_src :: "(nat,nat) src_history" where
  "RV_src = [(ec2, rv_a), (ec3, rv_b)]"
definition RV_down :: "(nat,nat) src_history" where
  "RV_down = [(ec3, rv_b), (ec2, rv_a)]"

definition RV_state :: "(nat,nat) dw_exec_state" where
  "RV_state =
     (initial_exec_state (\<lambda>_. None) {0::nat} ec3)
        \<lparr> exec_src_hist := RV_src,
          exec_down_hist := RV_down,
          exec_status := Crashed ec3 \<rparr>"

lemma RV_observable_mismatch: "observable_mismatch RV_state ec3 0"
  by (rule observable_mismatchI)
     (simp_all add: RV_state_def initial_exec_state_def RV_src_def RV_down_def
                    rv_a_def rv_b_def Src_def latest_src_event_def Let_def
                    ec_defs src_le_eq_less_eq)

end
