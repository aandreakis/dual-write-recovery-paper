(*  Title:       Outbox_Continuation.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Class-free outbox / CDC-continuation prong for the Dual-Write
    companion development, now importing the shared Layer-0 virtual-cut-state
    interface used by both DBLog_Virtual_Cuts and Dual_Write_Core.

    Every definition/lemma/theorem below the witness section is
    transplanted byte-for-byte from the author's own BSD-3 Layer-0
    sources (Virtual_Cut.thy, DBLog_Run_Core.thy, Continuation.thy);
    only the imports are reparented --- no proof body is edited. No
    DBLog run-model object is referenced (the run model, chunk plan,
    clean-prefix accessor, certificate carrier, and verifier substrate
    are all excluded).
*)

theory Outbox_Continuation
  imports
    Dual_Write_Layer0.Replay
    Dual_Write_Layer0.Source_Coordinates
    Dual_Write_Layer0.Scope
    Dual_Write_Layer0.Virtual_Cut_State
begin

section \<open>The outbox/CDC prong and the continuation algebra\<close>

subsection \<open>Shared virtual cut state\<close>

text \<open>
  @{const virtual_cut_state} is imported from the shared Layer-0 entry
  @{theory Dual_Write_Layer0.Virtual_Cut_State}. This outbox/CDC prong and the
  DBLog development therefore use one HOL constant for the interface predicate.
\<close>

subsection \<open>Generic list lemmas (hoisted; misfiled in a run theory)\<close>

lemma last_filter_index:
  fixes xs :: "'a list"
  assumes nonempty: "filter P xs \<noteq> []"
  shows "\<exists>i. i < length xs
          \<and> P (xs ! i)
          \<and> xs ! i = last (filter P xs)
          \<and> (\<forall>j. i < j \<and> j < length xs \<longrightarrow> \<not> P (xs ! j))"
  using nonempty
proof (induction xs rule: rev_induct)
  case Nil
  thus ?case by simp
next
  case (snoc x xs)
  show ?case
  proof (cases "P x")
    case True
    have idx_lt: "length xs < length (xs @ [x])" by simp
    have P_idx: "P ((xs @ [x]) ! length xs)" using True by simp
    have last_idx: "(xs @ [x]) ! length xs = last (filter P (xs @ [x]))"
      using True by simp
    have no_later:
      "\<forall>j. length xs < j \<and> j < length (xs @ [x])
            \<longrightarrow> \<not> P ((xs @ [x]) ! j)"
      by auto
    show ?thesis
      using idx_lt P_idx last_idx no_later
      by (intro exI[where x = "length xs"]) simp
  next
    case False
    note nPx = False
    have filter_xs_nonempty: "filter P xs \<noteq> []"
      using snoc.prems nPx by simp
    obtain i where i_lt_xs: "i < length xs"
      and Pi_xs: "P (xs ! i)"
      and last_xs: "xs ! i = last (filter P xs)"
      and no_later_xs: "\<forall>j. i < j \<and> j < length xs \<longrightarrow> \<not> P (xs ! j)"
      using snoc.IH[OF filter_xs_nonempty] by blast
    have i_lt: "i < length (xs @ [x])" using i_lt_xs by simp
    have Pi: "P ((xs @ [x]) ! i)" using Pi_xs i_lt_xs by (simp add: nth_append)
    have filter_append_eq: "filter P (xs @ [x]) = filter P xs"
      using nPx by simp
    have last_eq: "(xs @ [x]) ! i = last (filter P (xs @ [x]))"
    proof -
      have "(xs @ [x]) ! i = xs ! i"
        using i_lt_xs by (simp add: nth_append)
      also have "\<dots> = last (filter P xs)"
        using last_xs .
      also have "\<dots> = last (filter P (xs @ [x]))"
        using filter_append_eq by simp
      finally show ?thesis .
    qed
    have no_later:
      "\<forall>j. i < j \<and> j < length (xs @ [x]) \<longrightarrow> \<not> P ((xs @ [x]) ! j)"
    proof (intro allI impI)
      fix j
      assume j_assm: "i < j \<and> j < length (xs @ [x])"
      show "\<not> P ((xs @ [x]) ! j)"
      proof (cases "j < length xs")
        case True
        thus ?thesis using no_later_xs j_assm by (simp add: nth_append)
      next
        case False
        hence "j = length xs" using j_assm by simp
        thus ?thesis using nPx by simp
      qed
    qed
    show ?thesis
      using i_lt Pi last_eq no_later by blast
  qed
qed

lemma last_filter_upt_eq:
  fixes P :: "nat \<Rightarrow> bool"
  assumes i_lt: "i < n"
      and Pi: "P i"
      and no_after: "\<forall>j. i < j \<and> j < n \<longrightarrow> \<not> P j"
  shows "filter P [0..<n] \<noteq> [] \<and> last (filter P [0..<n]) = i"
  using i_lt Pi no_after
proof (induction n arbitrary: i)
  case 0
  thus ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "i = n")
    case True
    have upt: "[0..<Suc n] = [0..<n] @ [n]"
      by (simp add: upt_Suc_append)
    have "filter P [0..<Suc n] = filter P [0..<n] @ [n]"
      using True Suc.prems(2) upt by simp
    thus ?thesis using True by simp
  next
    case False
    hence i_lt_n: "i < n" using Suc.prems(1) by simp
    have Pn_false: "\<not> P n"
      using Suc.prems False by simp
    have no_after_n: "\<forall>j. i < j \<and> j < n \<longrightarrow> \<not> P j"
      using Suc.prems(3) by auto
    have ih: "filter P [0..<n] \<noteq> [] \<and> last (filter P [0..<n]) = i"
      by (rule Suc.IH[OF i_lt_n Suc.prems(2) no_after_n])
    have upt: "[0..<Suc n] = [0..<n] @ [n]"
      by (simp add: upt_Suc_append)
    have "filter P [0..<Suc n] = filter P [0..<n]"
      using Pn_false upt by simp
    thus ?thesis using ih by simp
  qed
qed

lemma append_no_B_before_A:
  fixes xs ys zs :: "'a list"
    and A B :: "'a \<Rightarrow> bool"
    and i j :: nat
  assumes zs_eq: "zs = xs @ ys"
      and xs_A: "\<forall>x \<in> set xs. A x"
      and ys_B: "\<forall>y \<in> set ys. B y"
      and disj: "\<And>z. A z \<Longrightarrow> B z \<Longrightarrow> False"
      and ij: "i < j"
      and j_lt: "j < length zs"
      and zi_B: "B (zs ! i)"
      and zj_A: "A (zs ! j)"
  shows False
proof (cases "i < length xs")
  case True
  hence "A (zs ! i)"
    using zs_eq xs_A by (simp add: nth_append)
  thus False using zi_B disj by blast
next
  case False
  hence j_ge: "length xs \<le> j" using ij by simp
  have "j - length xs < length ys"
    using zs_eq j_lt j_ge by simp
  hence "B (zs ! j)"
    using zs_eq ys_B j_ge by (simp add: nth_append)
  thus False using zj_A disj by blast
qed

subsection \<open>Source-history helper lemmas\<close>

lemma wellformed_src_history_coord_mono:
  fixes H :: "('k, 'v) src_history"
  assumes wf_h: "wellformed_src_history H"
      and ij: "i \<le> j"
      and j_lt: "j < length H"
  shows "src_le (hist_coord (H ! i)) (hist_coord (H ! j))"
proof -
  from wf_h have adj:
    "\<forall>i. Suc i < length H
          \<longrightarrow> src_le (hist_coord (H ! i)) (hist_coord (H ! Suc i))"
    unfolding wellformed_src_history_def by blast
  have step:
    "\<And>n. i + n < length H
      \<Longrightarrow> src_le (hist_coord (H ! i)) (hist_coord (H ! (i + n)))"
  proof -
    fix n
    assume bound: "i + n < length H"
    show "src_le (hist_coord (H ! i)) (hist_coord (H ! (i + n)))"
      using bound
    proof (induction n)
      case 0
      show ?case by (simp add: src_le_refl)
    next
      case (Suc n)
      have ih_bound: "i + n < length H" using Suc.prems by simp
      have ih:
        "src_le (hist_coord (H ! i)) (hist_coord (H ! (i + n)))"
        using Suc.IH[OF ih_bound] .
      have adj_step:
        "src_le (hist_coord (H ! (i + n))) (hist_coord (H ! Suc (i + n)))"
        using adj Suc.prems by simp
      have "src_le (hist_coord (H ! i)) (hist_coord (H ! Suc (i + n)))"
        using src_le_trans[OF ih adj_step] .
      thus ?case by (simp add: add_Suc_right)
    qed
  qed
  have j_eq: "j = i + (j - i)" using ij by simp
  show ?thesis
    using step[of "j - i"] j_lt j_eq by simp
qed

lemma src_eq_when_no_later_src_event_for_k:
  fixes b0 :: "'k \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
    and c' f :: frontier
    and k :: 'k
  assumes c'_le_f: "src_le c' f"
      and no_later:
        "\<forall> i < length H. src_lt c' (hist_coord (H ! i))
                          \<and> src_le (hist_coord (H ! i)) f
                          \<longrightarrow> key_of (hist_event (H ! i)) \<noteq> k"
  shows "Src b0 H f k = Src b0 H c' k"
proof -
  let ?cand_f =
    "filter (\<lambda>i. src_le (hist_coord (H ! i)) f
              \<and> key_of (hist_event (H ! i)) = k)
            [0..<length H]"
  let ?cand_c' =
    "filter (\<lambda>i. src_le (hist_coord (H ! i)) c'
              \<and> key_of (hist_event (H ! i)) = k)
            [0..<length H]"
  let ?Pf  = "\<lambda>i. src_le (hist_coord (H ! i)) f
                  \<and> key_of (hist_event (H ! i)) = k"
  let ?Pc' = "\<lambda>i. src_le (hist_coord (H ! i)) c'
                  \<and> key_of (hist_event (H ! i)) = k"

  \<comment> \<open>The two candidate filters coincide.\<close>
  have cand_eq: "?cand_f = ?cand_c'"
  proof -
    have "\<And>i. i \<in> set [0..<length H] \<Longrightarrow> ?Pf i = ?Pc' i"
    proof -
      fix i assume i_in: "i \<in> set [0..<length H]"
      hence i_lt: "i < length H" by simp
      show "?Pf i = ?Pc' i"
      proof
        assume Pf: "?Pf i"
        hence le_f: "src_le (hist_coord (H ! i)) f"
          and key_eq: "key_of (hist_event (H ! i)) = k"
          by auto
        have "src_le (hist_coord (H ! i)) c'"
        proof (rule ccontr)
          assume "\<not> src_le (hist_coord (H ! i)) c'"
          hence "src_le c' (hist_coord (H ! i))"
                "hist_coord (H ! i) \<noteq> c'"
            using src_le_total
            by (auto simp: less_eq_src_coord_def)
          hence "src_lt c' (hist_coord (H ! i))"
            unfolding src_lt_def by simp
          with no_later i_lt le_f have "key_of (hist_event (H ! i)) \<noteq> k"
            by blast
          with key_eq show False by simp
        qed
        thus "?Pc' i" using key_eq by simp
      next
        assume Pc': "?Pc' i"
        hence le_c': "src_le (hist_coord (H ! i)) c'"
          and key_eq: "key_of (hist_event (H ! i)) = k"
          by auto
        have "src_le (hist_coord (H ! i)) f"
          using le_c' c'_le_f src_le_trans by blast
        thus "?Pf i" using key_eq by simp
      qed
    qed
    thus ?thesis by (rule filter_cong[OF refl])
  qed

  have "latest_src_event H f k = latest_src_event H c' k"
    unfolding latest_src_event_def using cand_eq by simp
  thus ?thesis
    unfolding Src_def by simp
qed

subsection \<open>The continuation segment\<close>

definition cdc_segment_between
  :: "('k, 'v) src_history \<Rightarrow> 'k set \<Rightarrow> frontier \<Rightarrow> frontier
      \<Rightarrow> ('k, 'v) replay_event list \<Rightarrow> bool"
where
  "cdc_segment_between H K f f' \<delta> \<longleftrightarrow>
     f \<le> f'
   \<and> \<delta> = map (\<lambda>(c, e). cdc_lift c e)
              (filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e \<in> K) H)"

lemma wellformed_src_history_sorted:
  assumes wfH: "wellformed_src_history H"
  shows "sorted (map hist_coord H)"
  unfolding sorted_iff_nth_mono
proof (intro allI impI)
  fix i j
  assume ij: "i \<le> j" and j_lt: "j < length (map hist_coord H)"
  have j_lt_H: "j < length H" using j_lt by simp
  have i_lt: "i < length H" using ij j_lt_H by (rule le_less_trans)
  have "src_le (hist_coord (H ! i)) (hist_coord (H ! j))"
    by (rule wellformed_src_history_coord_mono[OF wfH ij j_lt_H])
  thus "map hist_coord H ! i \<le> map hist_coord H ! j"
    by (simp add: src_le_eq_less_eq nth_map i_lt j_lt_H)
qed

lemma filter_src_interval_concat:
  fixes H :: "('k, 'v) src_history"
  assumes ff':   "f \<le> f'"
      and f'f'': "f' \<le> f''"
      and srt:   "sorted (map hist_coord H)"
  shows "filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e \<in> K) H
           @ filter (\<lambda>(c, e). f' < c \<and> c \<le> f'' \<and> key_of e \<in> K) H
         = filter (\<lambda>(c, e). f < c \<and> c \<le> f'' \<and> key_of e \<in> K) H"
  using srt
proof (induction H)
  case Nil
  show ?case by simp
next
  case (Cons p H')
  obtain pc pe where p: "p = (pc, pe)" by (cases p)
  have srt': "sorted (map hist_coord H')"
    using Cons.prems by simp
  have IH: "filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e \<in> K) H'
              @ filter (\<lambda>(c, e). f' < c \<and> c \<le> f'' \<and> key_of e \<in> K) H'
            = filter (\<lambda>(c, e). f < c \<and> c \<le> f'' \<and> key_of e \<in> K) H'"
    by (rule Cons.IH[OF srt'])
  show ?case
  proof (cases "pc \<le> f'")
    case lo: True
    \<comment> \<open>Head in the lower interval: it joins the lower and combined
        segments identically; the tail closes by induction.\<close>
    have pcf'': "pc \<le> f''" using lo f'f'' by (rule order_trans)
    have not_f': "\<not> f' < pc" using lo by simp
    show ?thesis using p lo pcf'' not_f' IH by simp
  next
    case hi: False
    \<comment> \<open>Head strictly above \<open>f'\<close>: sortedness puts the whole tail
        above \<open>f'\<close>, so the lower segment of the tail is empty.\<close>
    hence f'_lt: "f' < pc" by simp
    have f_lt: "f < pc" using ff' f'_lt by (rule le_less_trans)
    have tail_above: "f' < hist_coord q" if q_in: "q \<in> set H'" for q
    proof -
      have "sorted (pc # map hist_coord H')"
        using Cons.prems p by simp
      moreover have "hist_coord q \<in> set (map hist_coord H')"
        using q_in by auto
      ultimately have pc_le_q: "pc \<le> hist_coord q" by auto
      show "f' < hist_coord q" using f'_lt pc_le_q by (rule less_le_trans)
    qed
    have lo_empty:
      "filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e \<in> K) H' = []"
    proof -
      have "\<not> (case q of (c, e) \<Rightarrow> f < c \<and> c \<le> f' \<and> key_of e \<in> K)"
        if q_in: "q \<in> set H'" for q
        using tail_above[OF q_in] by (auto simp: case_prod_beta)
      thus ?thesis by (simp add: filter_empty_conv)
    qed
    show ?thesis
      using p hi f'_lt f_lt IH lo_empty by simp
  qed
qed

lemma cdc_segment_between_concat:
  assumes wfH:  "wellformed_src_history H"
      and seg1: "cdc_segment_between H K f f' \<delta>1"
      and seg2: "cdc_segment_between H K f' f'' \<delta>2"
  shows "cdc_segment_between H K f f'' (\<delta>1 @ \<delta>2)"
proof -
  from seg1 have ff': "f \<le> f'"
    and \<delta>1_eq: "\<delta>1 = map (\<lambda>(c, e). cdc_lift c e)
                       (filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e \<in> K) H)"
    unfolding cdc_segment_between_def by simp_all
  from seg2 have f'f'': "f' \<le> f''"
    and \<delta>2_eq: "\<delta>2 = map (\<lambda>(c, e). cdc_lift c e)
                       (filter (\<lambda>(c, e). f' < c \<and> c \<le> f'' \<and> key_of e \<in> K) H)"
    unfolding cdc_segment_between_def by simp_all
  have ff'': "f \<le> f''" using ff' f'f'' by (rule order_trans)
  have "\<delta>1 @ \<delta>2
          = map (\<lambda>(c, e). cdc_lift c e)
                (filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e \<in> K) H
                 @ filter (\<lambda>(c, e). f' < c \<and> c \<le> f'' \<and> key_of e \<in> K) H)"
    unfolding \<delta>1_eq \<delta>2_eq by simp
  also have "\<dots> = map (\<lambda>(c, e). cdc_lift c e)
                      (filter (\<lambda>(c, e). f < c \<and> c \<le> f'' \<and> key_of e \<in> K) H)"
    by (simp only:
          filter_src_interval_concat
            [OF ff' f'f'' wellformed_src_history_sorted[OF wfH]])
  finally show ?thesis
    unfolding cdc_segment_between_def using ff'' by simp
qed

lemma cdc_segment_between_event_key_filter:
  assumes seg: "cdc_segment_between H K f f' \<delta>"
      and kK:  "k \<in> K"
  shows "filter (\<lambda>e. event_key e = k) \<delta>
           = map (\<lambda>(c, e). cdc_lift c e)
                 (filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e = k) H)"
proof -
  from seg have \<delta>_eq:
    "\<delta> = map (\<lambda>(c, e). cdc_lift c e)
             (filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e \<in> K) H)"
    unfolding cdc_segment_between_def by simp
  have key_filter:
    "filter ((\<lambda>e. event_key e = k) \<circ> (\<lambda>(c, e). cdc_lift c e))
            (filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e \<in> K) H)
       = filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e = k) H"
    unfolding filter_filter
    by (rule filter_cong[OF refl])
       (use kK in \<open>auto simp: cdc_lift_def case_prod_beta\<close>)
  show ?thesis
    by (simp only: \<delta>_eq filter_map key_filter)
qed

subsection \<open>Replay-append and source-state interval lemmas\<close>

lemma Apply_append:
  "Apply (\<sigma> @ \<delta>) = foldl apply_step (Apply \<sigma>) \<delta>"
  unfolding Apply_def by (simp add: foldl_append)

lemma Src_interval_decomposition:
  fixes b0 :: "'k \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
  assumes wfH:  "wellformed_src_history H"
      and f_le: "f \<le> f'"
  shows
    "Src b0 H f' k
       = (let segk = filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e = k) H
          in if segk = []
             then Src b0 H f k
             else (case snd (last segk) of
                     Insert _ v \<Rightarrow> Some v
                   | Update _ v \<Rightarrow> Some v
                   | Delete _   \<Rightarrow> None))"
proof -
  define Q where
    "Q = (\<lambda>p :: src_coord \<times> ('k, 'v) source_event.
            f < hist_coord p \<and> hist_coord p \<le> f'
            \<and> key_of (hist_event p) = k)"
  have segk_eq:
    "filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e = k) H = filter Q H"
    by (rule filter_cong[OF refl]) (simp add: Q_def case_prod_beta)
  show ?thesis
  proof (cases "filter Q H = []")
    case True
    \<comment> \<open>No source event for \<open>k\<close> in \<open>(f, f']\<close>: Src is unchanged.\<close>
    have no_later:
      "\<forall>i < length H. src_lt f (hist_coord (H ! i))
                       \<and> src_le (hist_coord (H ! i)) f'
                       \<longrightarrow> key_of (hist_event (H ! i)) \<noteq> k"
    proof (intro allI impI)
      fix i
      assume i_lt: "i < length H"
        and between: "src_lt f (hist_coord (H ! i))
                       \<and> src_le (hist_coord (H ! i)) f'"
      have "\<not> Q (H ! i)"
        using True i_lt by (metis filter_empty_conv nth_mem)
      thus "key_of (hist_event (H ! i)) \<noteq> k"
        using between
        by (auto simp: Q_def src_lt_eq_less src_le_eq_less_eq)
    qed
    have src_eq: "Src b0 H f' k = Src b0 H f k"
    proof (rule src_eq_when_no_later_src_event_for_k[OF _ no_later])
      show "src_le f f'"
        using f_le by (simp add: src_le_eq_less_eq)
    qed
    show ?thesis
      using src_eq True segk_eq by (simp add: Let_def)
  next
    case False
    \<comment> \<open>The latest \<open>k\<close>-event in \<open>(f, f']\<close> determines Src at \<open>f'\<close>.\<close>
    obtain i where
      i_lt: "i < length H" and
      Q_i: "Q (H ! i)" and
      H_i_last: "H ! i = last (filter Q H)" and
      no_after_Q: "\<forall>j. i < j \<and> j < length H \<longrightarrow> \<not> Q (H ! j)"
      using last_filter_index[OF False] by blast
    let ?P = "\<lambda>j. src_le (hist_coord (H ! j)) f'
                  \<and> key_of (hist_event (H ! j)) = k"
    have P_i: "?P i"
      using Q_i by (simp add: Q_def src_le_eq_less_eq)
    have f_lt_i: "f < hist_coord (H ! i)"
      using Q_i by (simp add: Q_def)
    have no_after_P: "\<forall>j. i < j \<and> j < length H \<longrightarrow> \<not> ?P j"
    proof (intro allI impI)
      fix j
      assume j_assm: "i < j \<and> j < length H"
      hence i_le_j: "i \<le> j" and j_lt: "j < length H" by auto
      show "\<not> ?P j"
      proof
        assume P_j: "?P j"
        hence j_le_f': "src_le (hist_coord (H ! j)) f'"
          and j_key: "key_of (hist_event (H ! j)) = k"
          by auto
        have coord_mono:
          "src_le (hist_coord (H ! i)) (hist_coord (H ! j))"
          by (rule wellformed_src_history_coord_mono[OF wfH i_le_j j_lt])
        have "f < hist_coord (H ! j)"
        proof -
          have "hist_coord (H ! i) \<le> hist_coord (H ! j)"
            using coord_mono by (simp add: src_le_eq_less_eq)
          with f_lt_i show ?thesis by (rule less_le_trans)
        qed
        hence "Q (H ! j)"
          using j_le_f' j_key
          by (simp add: Q_def src_le_eq_less_eq)
        with no_after_Q j_assm show False by blast
      qed
    qed
    have cand_ne: "filter ?P [0..<length H] \<noteq> []"
      and cand_last: "last (filter ?P [0..<length H]) = i"
      using last_filter_upt_eq[OF i_lt P_i no_after_P] by auto
    have latest_eq: "latest_src_event H f' k = Some i"
      using cand_ne cand_last
      unfolding latest_src_event_def by (simp add: Let_def)
    have "Src b0 H f' k = (case hist_event (H ! i) of
                             Insert _ v \<Rightarrow> Some v
                           | Update _ v \<Rightarrow> Some v
                           | Delete _   \<Rightarrow> None)"
      unfolding Src_def using latest_eq by simp
    thus ?thesis
      using segk_eq False H_i_last by (simp add: Let_def)
  qed
qed

subsection \<open>Continuation across frontiers\<close>

theorem virtual_cut_state_continuation:
  fixes b0 :: "'k \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
  assumes wfH: "wellformed_src_history H"
      and cut: "virtual_cut_state b0 \<sigma> K f H"
      and seg: "cdc_segment_between H K f f' \<delta>"
  shows "virtual_cut_state b0 (\<sigma> @ \<delta>) K f' H"
proof -
  from seg have f_le: "f \<le> f'"
    unfolding cdc_segment_between_def by simp
  have cut_k: "Apply \<sigma> k = Src b0 H f k" if "k \<in> K" for k
  proof -
    have "restrict (Apply \<sigma>) K k = restrict (Src b0 H f) K k"
      using cut unfolding virtual_cut_state_def by simp
    thus ?thesis using that by (simp add: restrict_def)
  qed
  have key_eq: "Apply (\<sigma> @ \<delta>) k = Src b0 H f' k" if kK: "k \<in> K" for k
  proof -
    define segk where
      "segk = filter (\<lambda>(c, e). f < c \<and> c \<le> f' \<and> key_of e = k) H"
    have \<delta>_k: "filter (\<lambda>e. event_key e = k) \<delta>
                 = map (\<lambda>(c, e). cdc_lift c e) segk"
      unfolding segk_def
      by (rule cdc_segment_between_event_key_filter[OF seg kK])
    have src_f':
      "Src b0 H f' k
         = (if segk = []
            then Src b0 H f k
            else (case snd (last segk) of
                    Insert _ v \<Rightarrow> Some v
                  | Update _ v \<Rightarrow> Some v
                  | Delete _   \<Rightarrow> None))"
      unfolding segk_def
      using Src_interval_decomposition[OF wfH f_le] by (simp add: Let_def)
    have filt_app: "filter (\<lambda>e. event_key e = k) (\<sigma> @ \<delta>)
                      = filter (\<lambda>e. event_key e = k) \<sigma>
                        @ map (\<lambda>(c, e). cdc_lift c e) segk"
      using \<delta>_k by simp
    show ?thesis
    proof (cases "segk = []")
      case True
      \<comment> \<open>No source event for \<open>k\<close> in \<open>(f, f']\<close>: replay of \<open>\<sigma> @ \<delta>\<close> at
          \<open>k\<close> reduces to replay of \<open>\<sigma>\<close>, and Src is unchanged.\<close>
      have "Apply (\<sigma> @ \<delta>) k
              = Apply (filter (\<lambda>e. event_key e = k) (\<sigma> @ \<delta>)) k"
        by (rule apply_eq_apply_filter_key)
      also have "\<dots> = Apply (filter (\<lambda>e. event_key e = k) \<sigma>) k"
        using filt_app True by simp
      also have "\<dots> = Apply \<sigma> k"
        by (rule apply_eq_apply_filter_key[symmetric])
      also have "\<dots> = Src b0 H f k"
        by (rule cut_k[OF kK])
      also have "\<dots> = Src b0 H f' k"
        using src_f' True by simp
      finally show ?thesis .
    next
      case False
      \<comment> \<open>The latest \<open>k\<close>-event lies in \<open>\<delta>\<close>; it is the \<^const>\<open>cdc_lift\<close>
          of the latest interval source event for \<open>k\<close>.\<close>
      have map_ne: "map (\<lambda>(c, e). cdc_lift c e) segk \<noteq> []"
        using False by simp
      have filt_ne: "filter (\<lambda>e. event_key e = k) (\<sigma> @ \<delta>) \<noteq> []"
        using filt_app map_ne by simp
      have last_eq: "last (filter (\<lambda>e. event_key e = k) (\<sigma> @ \<delta>))
                       = Cdc (fst (last segk)) (snd (last segk))"
      proof -
        have "last (filter (\<lambda>e. event_key e = k) (\<sigma> @ \<delta>))
                = last (map (\<lambda>(c, e). cdc_lift c e) segk)"
          using filt_app map_ne by (simp add: last_appendR)
        also have "\<dots> = (\<lambda>(c, e). cdc_lift c e) (last segk)"
          using False by (simp add: last_map)
        also have "\<dots> = Cdc (fst (last segk)) (snd (last segk))"
          by (simp add: cdc_lift_def case_prod_beta)
        finally show ?thesis .
      qed
      have step: "Apply (\<sigma> @ \<delta>) k
              = (case filter (\<lambda>e. event_key e = k) (\<sigma> @ \<delta>) of
                   [] \<Rightarrow> None
                 | _ # _ \<Rightarrow>
                     (case last (filter (\<lambda>e. event_key e = k) (\<sigma> @ \<delta>)) of
                        Cdc _ (Insert _ v) \<Rightarrow> Some v
                      | Cdc _ (Update _ v) \<Rightarrow> Some v
                      | Cdc _ (Delete _)   \<Rightarrow> None
                      | Refresh _ m_obs _  \<Rightarrow> m_obs))"
        by (rule apply_latest_event_wins)
      obtain z zs where
        zzs: "filter (\<lambda>e. event_key e = k) (\<sigma> @ \<delta>) = z # zs"
        by (metis filt_ne neq_Nil_conv)
      have "Apply (\<sigma> @ \<delta>) k = (case snd (last segk) of
                                  Insert _ v \<Rightarrow> Some v
                                | Update _ v \<Rightarrow> Some v
                                | Delete _   \<Rightarrow> None)"
        unfolding step last_eq using zzs by simp
      also have "\<dots> = Src b0 H f' k"
        using src_f' False by simp
      finally show ?thesis .
    qed
  qed
  show ?thesis
    unfolding virtual_cut_state_def
  proof (rule ext)
    fix k
    show "restrict (Apply (\<sigma> @ \<delta>)) K k = restrict (Src b0 H f') K k"
      using key_eq unfolding restrict_def by (cases "k \<in> K") auto
  qed
qed

subsection \<open>Restriction to a sub-scope\<close>

theorem virtual_cut_state_restrict_scope:
  fixes b0 :: "'k \<rightharpoonup> 'v"
  assumes cut: "virtual_cut_state b0 \<sigma> K f H"
      and sub: "K' \<subseteq> K"
  shows "virtual_cut_state b0 \<sigma> K' f H"
proof -
  have eqK: "restrict (Apply \<sigma>) K = restrict (Src b0 H f) K"
    using cut by (simp add: virtual_cut_state_def)
  show ?thesis
    unfolding virtual_cut_state_def
  proof (rule ext)
    fix k
    from eqK have "restrict (Apply \<sigma>) K k = restrict (Src b0 H f) K k"
      by simp
    with sub show "restrict (Apply \<sigma>) K' k = restrict (Src b0 H f) K' k"
      by (auto simp: restrict_def)
  qed
qed

subsection \<open>Whole-table continuation\<close>

theorem whole_table_state_continuation:
  fixes b0 :: "'k \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
  assumes wfH: "wellformed_src_history H"
      and tab: "Apply \<sigma> = Src b0 H f"
      and seg: "cdc_segment_between H UNIV f f' \<delta>"
  shows "Apply (\<sigma> @ \<delta>) = Src b0 H f'"
proof -
  have univ: "restrict m UNIV = m" for m :: "'k \<rightharpoonup> 'v"
    by (simp add: restrict_def)
  have "virtual_cut_state b0 \<sigma> UNIV f H"
    unfolding virtual_cut_state_def using tab by (simp add: univ)
  from virtual_cut_state_continuation[OF wfH this seg]
  have "virtual_cut_state b0 (\<sigma> @ \<delta>) UNIV f' H" .
  thus ?thesis
    unfolding virtual_cut_state_def by (simp add: univ)
qed

subsection \<open>Fresh DBLog-free non-vacuity witness\<close>

text \<open>
  A closed, Layer-0-only instance of @{thm virtual_cut_state_continuation}:
  an empty cut at frontier @{term ec1} on scope @{term "{0::nat}"} over the
  one-event history @{term "[(ec2, Insert 0 7)]"} continues, by appending the
  faithful interval segment for @{text "(ec1, ec3]"}, to a virtual cut at
  @{term ec3}. The segment is non-empty (it carries the @{term ec2} insert),
  so the continuation does real work: the continued replay yields
  @{term "Some 7"} at key @{term "0::nat"}. No DBLog object is used.
\<close>

definition wH :: "(nat, nat) src_history" where
  "wH = [(ec2, Insert 0 7)]"

lemma wH_wellformed: "wellformed_src_history wH"
  by (simp add: wH_def wellformed_src_history_def ec_defs)

lemma w_initial_cut: "virtual_cut_state (\<lambda>_. None) [] {0} ec1 wH"
  by (simp add: virtual_cut_state_def wH_def Apply_def Src_def
                latest_src_event_def restrict_def ec_defs Let_def)

lemma w_segment: "cdc_segment_between wH {0} ec1 ec3 [Cdc ec2 (Insert 0 7)]"
  by (simp add: cdc_segment_between_def wH_def cdc_lift_def ec_defs)

theorem outbox_continuation_witness:
  "virtual_cut_state (\<lambda>_. None) ([] @ [Cdc ec2 (Insert 0 7)]) {0} ec3 wH"
  by (rule virtual_cut_state_continuation[OF wH_wellformed w_initial_cut w_segment])

lemma outbox_witness_nontrivial:
  "Apply ([] @ [Cdc ec2 (Insert 0 7)]) (0::nat) = Some 7"
  by (simp add: Apply_def)


subsection \<open>Source-state at the base frontier (hoisted source-history helper)\<close>

lemma Src_at_base:
  assumes wfH: "wellformed_src_history H"
  shows "Src b0 H c0 = b0"
proof (rule ext)
  fix k
  have no_event_at_c0:
    "\<not> src_le (hist_coord (H ! i)) c0" if i_lt: "i < length H" for i
  proof
    assume "src_le (hist_coord (H ! i)) c0"
    moreover have "src_le c0 (hist_coord (H ! i))" by (rule c0_least)
    ultimately have "hist_coord (H ! i) = c0" by (rule src_le_antisym)
    moreover have "hist_coord (H ! i) \<noteq> c0"
      using wfH i_lt unfolding wellformed_src_history_def by blast
    ultimately show False by simp
  qed
  have "filter (\<lambda>i. src_le (hist_coord (H ! i)) c0
                     \<and> key_of (hist_event (H ! i)) = k) [0..<length H] = []"
    by (auto simp: filter_empty_conv no_event_at_c0)
  hence "latest_src_event H c0 k = None"
    unfolding latest_src_event_def by (simp add: Let_def)
  thus "Src b0 H c0 k = b0 k"
    unfolding Src_def by simp
qed

subsection \<open>The outbox / CDC prong (packaged, class-free)\<close>

text \<open>
  The packaged prong-i theorem of the modest unification: any faithful CDC
  segment from the base frontier certifies a virtual cut, and the segment is
  \<open>cdc_only\<close> (refresh-free). Transplanted byte-for-byte from the locked
  \<open>dual_write/Dual_Write_Unification.thy\<close>; class-free (no \<open>k::linorder\<close>).
\<close>

definition cdc_only :: "('k, 'v) replay_event list \<Rightarrow> bool" where
  "cdc_only \<sigma> \<longleftrightarrow> (\<forall>e \<in> set \<sigma>. \<not> is_refresh e)"

lemma cdc_segment_imp_cdc_only:
  assumes "cdc_segment_between H K f f' \<delta>"
  shows   "cdc_only \<delta>"
  using assms
  by (auto simp: cdc_only_def cdc_segment_between_def cdc_lift_def
           split: prod.splits)

theorem virtual_cut_certifies_outbox:
  assumes "wellformed_src_history H"
      and "cdc_segment_between H K c0 f \<sigma>"
  shows   "cdc_only \<sigma> \<and> virtual_cut_state (\<lambda>_. None) \<sigma> K f H"
proof
  show "cdc_only \<sigma>" by (rule cdc_segment_imp_cdc_only[OF assms(2)])
next
  \<comment> \<open>conjunct 2 = the \<open>exact_log_replay_sound\<close> pattern at \<open>b0 = \<lambda>_. None\<close>:
      genesis-on-scope is automatic (\<open>restrict (\<lambda>_. None) K = restrict (\<lambda>_. None) K\<close>).\<close>
  have seed: "virtual_cut_state (\<lambda>_. None) [] K c0 H"
    unfolding virtual_cut_state_def
    using Src_at_base[OF assms(1), of "\<lambda>_. None"]
    by (simp add: Apply_def)
  have "virtual_cut_state (\<lambda>_. None) ([] @ \<sigma>) K f H"
    by (rule virtual_cut_state_continuation[OF assms(1) seed assms(2)])
  thus "virtual_cut_state (\<lambda>_. None) \<sigma> K f H" by simp
qed

subsection \<open>A concrete, DBLog-free cdc-only outbox instance\<close>

text \<open>
  The witness segment of @{thm outbox_continuation_witness} is \<open>cdc_only\<close> ---
  a from-first-principles, refresh-free inhabitant. Paired with the DBLog
  instances \<open>dblog_prong_not_cdc_only\<close> (refresh-bearing), this is the
  outbox side of the two-genuinely-distinct-inhabitants demonstration.
\<close>

lemma outbox_prong_cdc_only: "cdc_only [Cdc ec2 (Insert (0::nat) (7::nat))]"
  by (rule cdc_segment_imp_cdc_only[OF w_segment])

end
