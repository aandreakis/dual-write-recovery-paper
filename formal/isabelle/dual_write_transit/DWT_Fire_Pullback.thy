(*  Title:       DWT_Fire_Pullback.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    WP2 OF THE TRANSIT-KERNEL BUILD (owner authorization DECISIONS.md D-099)
    --- the fire-instance FULL discharge.  The promoted spike (DWT_Fire)
    established STATEMENT-LEVEL instance correspondence with Road-2's U8; this
    theory upgrades that reading to the PULLBACK:

      dwt_fire_tracking : every u_disciplined_trace of the landed unified
        machine is tracked, under the TOTAL definitional ledger projection
        dwu_ledger_proj, by a run of the abstract machine at the fire instance
        (a case induction over the discipline grammar, mirroring the landed
        pres_* preservation bank of DWU_Fenced_Discipline);

      dwt_fire_pullback : hence the projection of every disciplined-reachable
        dwu-state is abstractly reachable from ainit ([], b);

      u8_safety_via_transit_interface : hence Road-2's U8 safety conclusion
        --- the LITERAL statement of the landed
        u_fenced_multiwriter_discipline_safe --- is a COROLLARY of the
        once-proved interface theorem a_safety, via fire_a_safety and the
        definitional hazard identity fire_hazard_correspondence.

    THE LANDED U8 REMAINS THE THEOREM OF RECORD AND THE PINNED PRINCIPAL
    (dual_write_unified/DWU_Fenced_Discipline.thy,
    u_fenced_multiwriter_discipline_safe).  The corollary here is the BRIDGE
    --- its name says so --- not a replacement.

    NON-CIRCULARITY (the honest content of the pullback).  The tracking
    invariant dwt_track_inv is GEOMETRIC bookkeeping only: journal/source
    agreement (the C3 face), arm-below-fence (the C4 face), and armed-batch
    generation-uniformity (harvested from the uarm/uarmf rule shapes).  It
    does NOT carry the safety ledger facts (C1 accepted-justification, C2
    accepted-distinctness, C5 armed-batch coherence), and NO proof below
    consumes the landed U8 theorem, u_disc_inv, or u_disc_inv_pres: the
    duplicate-freedom and justification of the acceptance ledger flow ONLY
    through the abstract invariant behind a_safety.  The discipline grammar's
    own rule guards (D1a/D1b/D3/D4 and the cursor-triple side conditions) are
    consumed as trace hypotheses, exactly as the landed proof consumes them.

    MOVE BUDGET (recorded for the reader; one lemma per grammar rule below):
    ud_refl 0; ud_nonpub 1 (AJournal); ud_publish 2 or 0 (AStage+ADeliver when
    fence-eligible --- D1b empties the projected pending --- else the
    projection is unchanged); ud_publost 0; ud_snap 2 or 0 (a snapshot stages
    payload-free, so no freshness obligation arises even against a nonempty
    pending); ud_spawn 1 (ATransit: fire_transit covers both the unchanged
    slot and the UProd overwrite of an armed fence slot); ud_release 0;
    ud_claim 3 (ATransit discard of the overwritten slot + ARaise + AStage ---
    the claim-overwrite is exactly fire_transit's discard face); ud_fire 1 or
    0 (ADeliver; the C4 face forces g = fence in the eligible case, so the
    fired batch IS the projected pending); ud_retain 0; ud_cursor_recovery
    2 or 0 (AStage+ADeliver across the fused triple, simulated t -> t3 in one
    piece --- the intermediate arm/heal states are never projected).

    Scope fences: safety half ONLY (nothing here states or implies
    exactly-once / at-least-once); no "settles"; no interface-optimality
    claim.  Honesty regime: quick_and_dirty = false (ROOT-pinned), ZERO sorry,
    no axiomatization, no consts, no oracles.
*)

theory DWT_Fire_Pullback
  imports DWT_Fire
begin

section \<open>1. The tracking invariant (geometric bookkeeping only)\<close>

text \<open>Three conjuncts.  (i) journal/source agreement --- inside a disciplined
  trace there is no truncation, so the commit journal and the store's source
  history coincide (the landed C3 face, re-proved here independently); it
  transfers the publish guard @{text "(c,e) \<in> exec_src_hist"} and the
  replay-subset chains to journal-justification.  (ii) arm-below-fence --- the
  landed C4 face, re-proved independently: with map functionality it makes the
  fence slot the ONLY possibly-eligible armed batch, which is exactly what the
  projection @{const dwu_ledger_proj} reads.  (iii) armed-batch
  generation-uniformity --- every armed batch is tagged at its own slot
  (@{text uarm} guards it; @{text uarmf} stamps it), which turns the abstract
  deliver-filter into Road-2's all-or-nothing batch gate
  (@{thm [source] fire_gate_shape}).  NO ledger-safety conjunct appears here;
  see the header's non-circularity note.\<close>

definition dwt_track_inv :: "('k, 'v) dwu_state \<Rightarrow> bool" where
  "dwt_track_inv t \<longleftrightarrow>
     dwu_journal t = exec_src_hist (dwu_store t)
   \<and> (\<forall>g B. dwu_gens t g = Some (UArmed B) \<longrightarrow> g \<le> dwu_fence t)
   \<and> (\<forall>g B. dwu_gens t g = Some (UArmed B) \<longrightarrow> (\<forall>x \<in> set B. ue_gen x = g))"

lemma dwt_track_invD:
  assumes "dwt_track_inv t"
  shows "dwu_journal t = exec_src_hist (dwu_store t)"
    and "\<And>g B. dwu_gens t g = Some (UArmed B) \<Longrightarrow> g \<le> dwu_fence t"
    and "\<And>g B x. \<lbrakk>dwu_gens t g = Some (UArmed B); x \<in> set B\<rbrakk> \<Longrightarrow> ue_gen x = g"
  using assms by (auto simp: dwt_track_inv_def)

lemma dwt_track_inv_init: "dwt_track_inv (dwu_init b K fin)"
  by (auto simp: dwt_track_inv_def dwu_init_def initial_exec_state_def)

section \<open>2. Projection support\<close>

lemma dwu_ledger_proj_cong:
  assumes "dwu_gens t' (dwu_fence t') = dwu_gens t (dwu_fence t)"
      and "dwu_accepted t' = dwu_accepted t"
      and "dwu_fence t' = dwu_fence t"
      and "dwu_journal t' = dwu_journal t"
      and "exec_base (dwu_store t') = exec_base (dwu_store t)"
  shows "dwu_ledger_proj t' = dwu_ledger_proj t"
  using assms by (simp add: dwu_ledger_proj_def)

lemma dwu_ledger_proj_init:
  "dwu_ledger_proj (dwu_init b K fin) = ainit ([], b)"
  by (simp add: dwu_ledger_proj_def dwu_init_def initial_exec_state_def ainit_def)

section \<open>3. The per-rule simulation bank (mirrors the landed pres_* bank)\<close>

text \<open>One lemma per discipline-grammar rule: from the tracking invariant and
  the rule's own guards, the invariant is preserved AND the ledger projection
  moves by the recorded abstract-move budget.  The frame facts are extracted
  with the SAME landed inversion lemmas the pres_* bank uses
  (@{thm [source] dwu_step_publish_full} etc.); no landed theorem about
  safety is consumed.\<close>

subsection \<open>3.1 Zero-move frames: publost / release / retain\<close>

lemma dwt_sim_publost:
  assumes inv: "dwt_track_inv t"
      and step: "dwu_step t (UPubLost g c e) t'"
  shows "dwt_track_inv t'
       \<and> (astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t) (dwu_ledger_proj t')"
proof -
  from dwu_step_publost_full[OF step] obtain s' where
    core: "dw_exec_step (dwu_store t) (DoDownstream c e) s'" and st: "dwu_store t' = s'" and
    J: "dwu_journal t' = dwu_journal t" and G: "dwu_gens t' = dwu_gens t" and
    F: "dwu_fence t' = dwu_fence t" and A: "dwu_accepted t' = dwu_accepted t" by blast
  have srcfr: "exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t)"
    using st core by (simp add: dw_exec_step_src_hist)
  have bconst: "exec_base (dwu_store t') = exec_base (dwu_store t)"
    using st core by (simp add: dw_exec_step_base)
  have inv': "dwt_track_inv t'"
    using inv by (simp add: dwt_track_inv_def J G F srcfr)
  have "dwu_ledger_proj t' = dwu_ledger_proj t"
    by (rule dwu_ledger_proj_cong) (simp_all add: G F A J bconst)
  then show ?thesis using inv' by simp
qed

lemma dwt_sim_release:
  assumes inv: "dwt_track_inv t"
      and step: "dwu_step t (URelease g) t'"
  shows "dwt_track_inv t'
       \<and> (astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t) (dwu_ledger_proj t')"
proof -
  from dwu_step_release_frame[OF step] have
    G: "dwu_gens t' = dwu_gens t" and J: "dwu_journal t' = dwu_journal t" and
    A: "dwu_accepted t' = dwu_accepted t" and F: "dwu_fence t' = dwu_fence t" by auto
  from dwu_step_release_src_base[OF step] have
    S: "exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t)" and
    Bse: "exec_base (dwu_store t') = exec_base (dwu_store t)" by auto
  have inv': "dwt_track_inv t'"
    using inv by (simp add: dwt_track_inv_def J G F S)
  have "dwu_ledger_proj t' = dwu_ledger_proj t"
    by (rule dwu_ledger_proj_cong) (simp_all add: G F A J Bse)
  then show ?thesis using inv' by simp
qed

lemma dwt_sim_retain:
  assumes inv: "dwt_track_inv t"
      and step: "dwu_step t (URetain n) t'"
  shows "dwt_track_inv t'
       \<and> (astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t) (dwu_ledger_proj t')"
proof -
  from dwu_step_retain_full[OF step] have
    st: "dwu_store t' = dwu_store t" and J: "dwu_journal t' = dwu_journal t" and
    G: "dwu_gens t' = dwu_gens t" and F: "dwu_fence t' = dwu_fence t" and
    A: "dwu_accepted t' = dwu_accepted t" by auto
  have inv': "dwt_track_inv t'"
    using inv by (simp add: dwt_track_inv_def J G F st)
  have "dwu_ledger_proj t' = dwu_ledger_proj t"
    by (rule dwu_ledger_proj_cong) (simp_all add: G F A J st)
  then show ?thesis using inv' by simp
qed

subsection \<open>3.2 The journal move: non-publish lifts\<close>

lemma dwt_sim_nonpub:
  assumes inv: "dwt_track_inv t"
      and notpub: "\<forall>c e. a \<noteq> DoDownstream c e"
      and step: "dwu_step t (ULift g a) t'"
  shows "dwt_track_inv t'
       \<and> (astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t) (dwu_ledger_proj t')"
proof -
  from dwu_lift_nonpub_shape[OF step notpub] have
    A: "dwu_accepted t' = dwu_accepted t" and
    G: "dwu_gens t' = dwu_gens t" and
    F: "dwu_fence t' = dwu_fence t" and
    J: "dwu_journal t' = dwu_journal t @ src_hist_of_labels [a]" and
    S: "exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t) @ src_hist_of_labels [a]" and
    Bse: "exec_base (dwu_store t') = exec_base (dwu_store t)" by auto
  have inv': "dwt_track_inv t'"
    using inv by (simp add: dwt_track_inv_def J S G F)
  have mv: "astep ue_gen upay uj ujle fire_transit (dwu_ledger_proj t) (dwu_ledger_proj t')"
  proof (rule astepJournalI)
    show "dwu_ledger_proj t'
            = (dwu_ledger_proj t)\<lparr>t_journal := (dwu_journal t', exec_base (dwu_store t'))\<rparr>"
      by (simp add: dwu_ledger_proj_def A G F)
    show "ujle (t_journal (dwu_ledger_proj t)) (dwu_journal t', exec_base (dwu_store t'))"
      by (auto simp: dwu_ledger_proj_def ujle_def J Bse)
  qed
  have moves: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>*
                 (dwu_ledger_proj t) (dwu_ledger_proj t')"
    by (rule r_into_rtranclp) (rule mv)
  from inv' moves show ?thesis ..
qed

subsection \<open>3.3 The stage+deliver pair: publish\<close>

lemma dwt_sim_publish:
  assumes inv: "dwt_track_inv t"
      and D1a_mem: "(c, e) \<in> set (exec_src_hist (dwu_store t))"
      and D1a_fresh: "(c, e) \<notin> set (log_payloads (dwu_accepted t))"
      and D1b: "\<forall>g' B. dwu_gens t g' = Some (UArmed B) \<longrightarrow> g' < dwu_fence t"
      and step: "dwu_step t (ULift g (DoDownstream c e)) t'"
  shows "dwt_track_inv t'
       \<and> (astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t) (dwu_ledger_proj t')"
proof -
  define x where "x = \<lparr> ue_stamp = length (dwu_journal t), ue_gen = g, ue_pay = ULog (c, e) \<rparr>"
  from dwu_step_publish_full[OF step] obtain s' where
    core: "dw_exec_step (dwu_store t) (DoDownstream c e) s'" and
    store': "dwu_store t' = s'" and
    jour': "dwu_journal t' = dwu_journal t" and
    gens': "dwu_gens t' = dwu_gens t" and
    fence': "dwu_fence t' = dwu_fence t" and
    acc': "dwu_accepted t' = dwu_accepted t @ (if dwu_fence t \<le> g then [x] else [])"
    unfolding x_def by blast
  have srcfr: "exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t)"
    using store' core by (simp add: dw_exec_step_src_hist)
  have bconst: "exec_base (dwu_store t') = exec_base (dwu_store t)"
    using store' core by (simp add: dw_exec_step_base)
  have inv': "dwt_track_inv t'"
    using inv by (simp add: dwt_track_inv_def jour' srcfr gens' fence')
  have P0: "t_pending (dwu_ledger_proj t) = []"
    by (rule d1b_projects_empty_pending[OF D1b])
  have P0raw: "(case dwu_gens t (dwu_fence t) of Some (UArmed B) \<Rightarrow> B | _ \<Rightarrow> []) = []"
    using P0 by (simp add: dwu_ledger_proj_def)
  show ?thesis
  proof (cases "dwu_fence t \<le> g")
    case True
    have genx: "ue_gen x = g" by (simp add: x_def)
    have lpx: "lpays upay [x] = [(c, e)]"
      by (simp add: x_def lpays_ulog_single)
    have justx: "uj (t_journal (dwu_ledger_proj t)) x"
    proof -
      have "(c, e) \<in> set (dwu_journal t)"
        using D1a_mem dwt_track_invD(1)[OF inv] by simp
      then show ?thesis
        by (simp add: dwu_ledger_proj_def uj_def x_def)
    qed
    define mid where "mid = (dwu_ledger_proj t)\<lparr>t_pending := [x]\<rparr>"
    have m1: "astep ue_gen upay uj ujle fire_transit (dwu_ledger_proj t) mid"
    proof (rule astepStageI)
      show "mid = (dwu_ledger_proj t)\<lparr>t_pending := t_pending (dwu_ledger_proj t) @ [x]\<rparr>"
        by (simp add: mid_def P0)
      show "[x] = filter (\<lambda>y. t_fence (dwu_ledger_proj t) \<le> ue_gen y) [x]"
        by (simp add: dwu_ledger_proj_def genx True)
      show "distinct (lpays upay [x])" by (simp add: lpx)
      show "set (lpays upay [x]) \<inter> set (lpays upay (t_accepted (dwu_ledger_proj t))) = {}"
        using D1a_fresh
        by (simp add: x_def dwu_ledger_proj_def lpays_is_log_payloads
                      log_payloads_single_ulog)
      show "set (lpays upay [x]) \<inter> set (lpays upay (a_eligible ue_gen (dwu_ledger_proj t))) = {}"
        by (simp add: a_eligible_def P0)
      show "\<forall>y \<in> set [x]. uj (t_journal (dwu_ledger_proj t)) y" using justx by simp
    qed
    have m2: "astep ue_gen upay uj ujle fire_transit mid (dwu_ledger_proj t')"
    proof (rule astepDeliverI)
      show "dwu_ledger_proj t'
              = mid\<lparr>t_pending := [],
                    t_accepted := t_accepted mid @ filter (\<lambda>y. t_fence mid \<le> ue_gen y) [x]\<rparr>"
        by (simp add: mid_def dwu_ledger_proj_def gens' fence' acc' jour' bconst
                      genx True P0raw)
      show "mset (t_pending mid) = mset [x] + mset []"
        by (simp add: mid_def)
    qed
    have moves: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>*
                   (dwu_ledger_proj t) (dwu_ledger_proj t')"
      using m1 m2 by (meson converse_rtranclp_into_rtranclp r_into_rtranclp)
    from inv' moves show ?thesis ..
  next
    case False
    have "dwu_ledger_proj t' = dwu_ledger_proj t"
      by (rule dwu_ledger_proj_cong) (simp_all add: gens' fence' acc' jour' bconst False)
    then show ?thesis using inv' by simp
  qed
qed

subsection \<open>3.4 The stage+deliver pair: snapshot (payload-free stage)\<close>

lemma dwt_sim_snap:
  assumes inv: "dwt_track_inv t"
      and D4: "v = Src (exec_base (dwu_store t)) (take (length (dwu_journal t)) (dwu_journal t)) c k"
      and step: "dwu_step t (USnapE g c k v) t'"
  shows "dwt_track_inv t'
       \<and> (astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t) (dwu_ledger_proj t')"
proof -
  define x where "x = \<lparr> ue_stamp = length (dwu_journal t), ue_gen = g, ue_pay = USnap c k v \<rparr>"
  from dwu_step_snap_full[OF step] have
    st: "dwu_store t' = dwu_store t" and J: "dwu_journal t' = dwu_journal t" and
    G: "dwu_gens t' = dwu_gens t" and F: "dwu_fence t' = dwu_fence t" and
    A: "dwu_accepted t' = dwu_accepted t @ (if dwu_fence t \<le> g then [x] else [])"
    unfolding x_def by auto
  have inv': "dwt_track_inv t'"
    using inv by (simp add: dwt_track_inv_def J G F st)
  show ?thesis
  proof (cases "dwu_fence t \<le> g")
    case True
    have genx: "ue_gen x = g" by (simp add: x_def)
    have lpx: "lpays upay [x] = []"
      by (simp add: x_def lpays_is_log_payloads)
    have justx: "uj (t_journal (dwu_ledger_proj t)) x"
      by (simp add: dwu_ledger_proj_def uj_def x_def D4)
    define mid where
      "mid = (dwu_ledger_proj t)\<lparr>t_pending := t_pending (dwu_ledger_proj t) @ [x]\<rparr>"
    have m1: "astep ue_gen upay uj ujle fire_transit (dwu_ledger_proj t) mid"
    proof (rule astepStageI)
      show "mid = (dwu_ledger_proj t)\<lparr>t_pending := t_pending (dwu_ledger_proj t) @ [x]\<rparr>"
        by (simp add: mid_def)
      show "[x] = filter (\<lambda>y. t_fence (dwu_ledger_proj t) \<le> ue_gen y) [x]"
        by (simp add: dwu_ledger_proj_def genx True)
      show "distinct (lpays upay [x])" by (simp add: lpx)
      show "set (lpays upay [x]) \<inter> set (lpays upay (t_accepted (dwu_ledger_proj t))) = {}"
        by (simp add: lpx)
      show "set (lpays upay [x]) \<inter> set (lpays upay (a_eligible ue_gen (dwu_ledger_proj t))) = {}"
        by (simp add: lpx)
      show "\<forall>y \<in> set [x]. uj (t_journal (dwu_ledger_proj t)) y" using justx by simp
    qed
    have m2: "astep ue_gen upay uj ujle fire_transit mid (dwu_ledger_proj t')"
    proof (rule astepDeliverI)
      show "dwu_ledger_proj t'
              = mid\<lparr>t_pending := t_pending (dwu_ledger_proj t),
                    t_accepted := t_accepted mid @ filter (\<lambda>y. t_fence mid \<le> ue_gen y) [x]\<rparr>"
        by (simp add: mid_def dwu_ledger_proj_def G F A J st genx True)
      show "mset (t_pending mid) = mset [x] + mset (t_pending (dwu_ledger_proj t))"
        by (simp add: mid_def ac_simps)
    qed
    have moves: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>*
                   (dwu_ledger_proj t) (dwu_ledger_proj t')"
      using m1 m2 by (meson converse_rtranclp_into_rtranclp r_into_rtranclp)
    from inv' moves show ?thesis ..
  next
    case False
    have "dwu_ledger_proj t' = dwu_ledger_proj t"
      by (rule dwu_ledger_proj_cong) (simp_all add: G F A J st False)
    then show ?thesis using inv' by simp
  qed
qed

subsection \<open>3.5 The transit move: spawn (a UProd overwrite is a discard)\<close>

lemma dwt_sim_spawn:
  assumes inv: "dwt_track_inv t"
      and step: "dwu_step t USpawn t'"
  shows "dwt_track_inv t'
       \<and> (astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t) (dwu_ledger_proj t')"
proof -
  from dwu_step_spawn_inv[OF step] have
    G: "dwu_gens t' = (dwu_gens t)(Suc (dwu_hwm t) \<mapsto> UProd)" and
    st: "dwu_store t' = dwu_store t" and J: "dwu_journal t' = dwu_journal t" and
    A: "dwu_accepted t' = dwu_accepted t" and F: "dwu_fence t' = dwu_fence t" by auto
  have inv': "dwt_track_inv t'"
  proof -
    have C3': "dwu_journal t' = exec_src_hist (dwu_store t')"
      using dwt_track_invD(1)[OF inv] by (simp add: J st)
    have C4': "\<And>g' B. dwu_gens t' g' = Some (UArmed B) \<Longrightarrow> g' \<le> dwu_fence t'"
    proof -
      fix g' B assume "dwu_gens t' g' = Some (UArmed B)"
      with G have "dwu_gens t g' = Some (UArmed B)" by (auto split: if_split_asm)
      from dwt_track_invD(2)[OF inv this] show "g' \<le> dwu_fence t'" by (simp add: F)
    qed
    have U': "\<And>g' B x. \<lbrakk>dwu_gens t' g' = Some (UArmed B); x \<in> set B\<rbrakk> \<Longrightarrow> ue_gen x = g'"
    proof -
      fix g' B x assume gB: "dwu_gens t' g' = Some (UArmed B)" and xB: "x \<in> set B"
      from gB G have "dwu_gens t g' = Some (UArmed B)" by (auto split: if_split_asm)
      from dwt_track_invD(3)[OF inv this xB] show "ue_gen x = g'" .
    qed
    show ?thesis unfolding dwt_track_inv_def using C3' C4' U' by blast
  qed
  have wt: "fire_transit (t_pending (dwu_ledger_proj t)) (t_pending (dwu_ledger_proj t'))"
  proof (cases "dwu_fence t = Suc (dwu_hwm t)")
    case True
    have "t_pending (dwu_ledger_proj t') = []"
      by (simp add: dwu_ledger_proj_def G F True)
    then show ?thesis by (simp add: fire_transit_def)
  next
    case False
    have "t_pending (dwu_ledger_proj t') = t_pending (dwu_ledger_proj t)"
      by (simp add: dwu_ledger_proj_def G F False)
    then show ?thesis by (simp add: fire_transit_def)
  qed
  have mv: "astep ue_gen upay uj ujle fire_transit (dwu_ledger_proj t) (dwu_ledger_proj t')"
  proof (rule astepTransitI)
    show "dwu_ledger_proj t'
            = (dwu_ledger_proj t)\<lparr>t_pending := t_pending (dwu_ledger_proj t')\<rparr>"
      by (simp add: dwu_ledger_proj_def G F A J st)
    show "fire_transit (t_pending (dwu_ledger_proj t)) (t_pending (dwu_ledger_proj t'))"
      by (rule wt)
  qed
  have moves: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>*
                 (dwu_ledger_proj t) (dwu_ledger_proj t')"
    by (rule r_into_rtranclp) (rule mv)
  from inv' moves show ?thesis ..
qed

subsection \<open>3.6 The claim: discard + raise + stage\<close>

lemma dwt_sim_claim:
  assumes inv: "dwt_track_inv t"
      and D3: "distinct (log_payloads (stamped_at (length (dwu_journal t)) g (u_sink_delta f t)))"
      and step: "dwu_step t (UArmF g f) t'"
  shows "dwt_track_inv t'
       \<and> (astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t) (dwu_ledger_proj t')"
proof -
  define nb where "nb = stamped_at (length (dwu_journal t)) g (u_sink_delta f t)"
  from dwu_step_armf_full[OF step] have
    fle: "dwu_fence t \<le> g" and st: "dwu_store t' = dwu_store t" and
    J: "dwu_journal t' = dwu_journal t" and A: "dwu_accepted t' = dwu_accepted t" and
    F: "dwu_fence t' = g" and G: "dwu_gens t' = (dwu_gens t)(g \<mapsto> UArmed nb)"
    unfolding nb_def by auto
  have inv': "dwt_track_inv t'"
  proof -
    have C3': "dwu_journal t' = exec_src_hist (dwu_store t')"
      using dwt_track_invD(1)[OF inv] by (simp add: J st)
    have C4': "\<And>g' B. dwu_gens t' g' = Some (UArmed B) \<Longrightarrow> g' \<le> dwu_fence t'"
    proof -
      fix g' B assume gB: "dwu_gens t' g' = Some (UArmed B)"
      show "g' \<le> dwu_fence t'"
      proof (cases "g' = g")
        case True then show ?thesis by (simp add: F)
      next
        case False
        with gB G have "dwu_gens t g' = Some (UArmed B)" by (auto split: if_split_asm)
        from dwt_track_invD(2)[OF inv this] fle show ?thesis by (simp add: F)
      qed
    qed
    have U': "\<And>g' B x. \<lbrakk>dwu_gens t' g' = Some (UArmed B); x \<in> set B\<rbrakk> \<Longrightarrow> ue_gen x = g'"
    proof -
      fix g' B x assume gB: "dwu_gens t' g' = Some (UArmed B)" and xB: "x \<in> set B"
      show "ue_gen x = g'"
      proof (cases "g' = g")
        case True
        with gB G have "B = nb" by simp
        with xB True show ?thesis by (simp add: nb_def stamped_at_gen)
      next
        case False
        with gB G have "dwu_gens t g' = Some (UArmed B)" by (auto split: if_split_asm)
        from dwt_track_invD(3)[OF inv this xB] show ?thesis .
      qed
    qed
    show ?thesis unfolding dwt_track_inv_def using C3' C4' U' by blast
  qed
  \<comment> \<open>the three abstract moves\<close>
  define s1 where "s1 = (dwu_ledger_proj t)\<lparr>t_pending := []\<rparr>"
  define s2 where "s2 = s1\<lparr>t_fence := g\<rparr>"
  have m1: "astep ue_gen upay uj ujle fire_transit (dwu_ledger_proj t) s1"
  proof (rule astepTransitI)
    show "s1 = (dwu_ledger_proj t)\<lparr>t_pending := []\<rparr>" by (simp add: s1_def)
    show "fire_transit (t_pending (dwu_ledger_proj t)) []"
      by (simp add: fire_transit_def)
  qed
  have m2: "astep ue_gen upay uj ujle fire_transit s1 s2"
  proof (rule astepRaiseI)
    show "s2 = s1\<lparr>t_fence := g\<rparr>" by (simp add: s2_def)
    show "t_fence s1 \<le> g"
      by (simp add: s1_def dwu_ledger_proj_def fle)
  qed
  have sd_sub: "set (u_sink_delta f t) \<subseteq> set (dwu_journal t)"
  proof -
    have "set (u_sink_delta f t)
            \<subseteq> set (replay_down_hist (retained_hist t) (exec_scope (dwu_store t)) f)"
      by (auto simp: u_sink_delta_def)
    also have "\<dots> \<subseteq> set (retained_hist t)" by (rule replay_subset)
    also have "\<dots> \<subseteq> set (exec_src_hist (dwu_store t))" by (rule retained_subset)
    also have "\<dots> = set (dwu_journal t)" using dwt_track_invD(1)[OF inv] by simp
    finally show ?thesis .
  qed
  have m3: "astep ue_gen upay uj ujle fire_transit s2 (dwu_ledger_proj t')"
  proof (rule astepStageI)
    show "dwu_ledger_proj t' = s2\<lparr>t_pending := t_pending s2 @ nb\<rparr>"
      by (simp add: s2_def s1_def dwu_ledger_proj_def G F A J st)
    show "nb = filter (\<lambda>y. t_fence s2 \<le> ue_gen y) nb"
      by (simp add: s2_def nb_def filter_gate_stamped)
    show "distinct (lpays upay nb)"
      using D3 by (simp add: nb_def lpays_is_log_payloads)
    show "set (lpays upay nb) \<inter> set (lpays upay (t_accepted s2)) = {}"
      by (auto simp: s2_def s1_def dwu_ledger_proj_def nb_def lpays_is_log_payloads
                     u_sink_delta_def)
    show "set (lpays upay nb) \<inter> set (lpays upay (a_eligible ue_gen s2)) = {}"
      by (simp add: s2_def s1_def a_eligible_def)
    show "\<forall>y \<in> set nb. uj (t_journal s2) y"
    proof
      fix y assume "y \<in> set nb"
      then obtain p where y: "y = \<lparr> ue_stamp = length (dwu_journal t),
                                    ue_gen = g, ue_pay = ULog p \<rparr>"
                      and pD: "p \<in> set (u_sink_delta f t)"
        by (auto simp: nb_def stamped_at_def)
      from pD sd_sub have pJ: "p \<in> set (dwu_journal t)" by blast
      show "uj (t_journal s2) y"
        by (simp add: s2_def s1_def dwu_ledger_proj_def uj_def y pJ)
    qed
  qed
  have moves: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>*
                 (dwu_ledger_proj t) (dwu_ledger_proj t')"
    using m1 m2 m3 by (meson converse_rtranclp_into_rtranclp r_into_rtranclp)
  from inv' moves show ?thesis ..
qed

subsection \<open>3.7 The fire: one guard-free deliver\<close>

lemma dwt_sim_fire:
  assumes inv: "dwt_track_inv t"
      and step: "dwu_step t (UFire g) t'"
  shows "dwt_track_inv t'
       \<and> (astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t) (dwu_ledger_proj t')"
proof -
  from dwu_step_fire_full[OF step] obtain B where
    gB: "dwu_gens t g = Some (UArmed B)" and
    acc': "dwu_accepted t' = dwu_accepted t @ (if dwu_fence t \<le> g then B else [])" and
    gens': "dwu_gens t' = (dwu_gens t)(g \<mapsto> UProd)" and
    jour': "dwu_journal t' = dwu_journal t" and
    fence': "dwu_fence t' = dwu_fence t" and
    store': "dwu_store t' = dwu_store t" by blast
  have inv': "dwt_track_inv t'"
  proof -
    have C3': "dwu_journal t' = exec_src_hist (dwu_store t')"
      using dwt_track_invD(1)[OF inv] by (simp add: jour' store')
    have C4': "\<And>g' B'. dwu_gens t' g' = Some (UArmed B') \<Longrightarrow> g' \<le> dwu_fence t'"
    proof -
      fix g' B' assume "dwu_gens t' g' = Some (UArmed B')"
      with gens' have "dwu_gens t g' = Some (UArmed B')" by (auto split: if_split_asm)
      from dwt_track_invD(2)[OF inv this] show "g' \<le> dwu_fence t'" by (simp add: fence')
    qed
    have U': "\<And>g' B' x. \<lbrakk>dwu_gens t' g' = Some (UArmed B'); x \<in> set B'\<rbrakk> \<Longrightarrow> ue_gen x = g'"
    proof -
      fix g' B' x assume gB': "dwu_gens t' g' = Some (UArmed B')" and xB: "x \<in> set B'"
      from gB' gens' have "dwu_gens t g' = Some (UArmed B')" by (auto split: if_split_asm)
      from dwt_track_invD(3)[OF inv this xB] show "ue_gen x = g'" .
    qed
    show ?thesis unfolding dwt_track_inv_def using C3' C4' U' by blast
  qed
  show ?thesis
  proof (cases "dwu_fence t \<le> g")
    case True
    have geq: "g = dwu_fence t"
      using dwt_track_invD(2)[OF inv gB] True by (intro antisym)
    have genB: "\<forall>x \<in> set B. ue_gen x = g"
      using dwt_track_invD(3)[OF inv gB] by blast
    have fB: "filter (\<lambda>y. dwu_fence t \<le> ue_gen y) B = B"
      using fire_gate_shape[OF genB, of "dwu_fence t"] True by simp
    have P0: "t_pending (dwu_ledger_proj t) = B"
      by (simp add: dwu_ledger_proj_def geq[symmetric] gB)
    have mv: "astep ue_gen upay uj ujle fire_transit (dwu_ledger_proj t) (dwu_ledger_proj t')"
    proof (rule astepDeliverI)
      show "dwu_ledger_proj t'
              = (dwu_ledger_proj t)\<lparr>t_pending := [],
                    t_accepted := t_accepted (dwu_ledger_proj t)
                      @ filter (\<lambda>y. t_fence (dwu_ledger_proj t) \<le> ue_gen y) B\<rparr>"
        by (simp add: dwu_ledger_proj_def gens' fence' acc' jour' store' fB geq)
      show "mset (t_pending (dwu_ledger_proj t)) = mset B + mset []"
        by (simp add: P0)
    qed
    have moves: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>*
                   (dwu_ledger_proj t) (dwu_ledger_proj t')"
      by (rule r_into_rtranclp) (rule mv)
    from inv' moves show ?thesis ..
  next
    case False
    have fne: "dwu_fence t \<noteq> g" using False by auto
    have "dwu_ledger_proj t' = dwu_ledger_proj t"
      by (rule dwu_ledger_proj_cong)
         (simp_all add: gens' fence' acc' jour' store' False fne)
    then show ?thesis using inv' by simp
  qed
qed

subsection \<open>3.8 The fused cursor triple: stage + deliver across arm/heal/fire\<close>

lemma dwt_sim_cursor:
  assumes inv: "dwt_track_inv t"
      and Rdef: "R = replay_down_hist (retained_hist t) (exec_scope (dwu_store t)) f"
      and ddist: "distinct (drop m R)"
      and ddisj: "set (drop m R) \<inter> set (log_payloads (dwu_accepted t)) = {}"
      and D1b: "\<forall>g' B'. dwu_gens t g' = Some (UArmed B') \<longrightarrow> g' < dwu_fence t"
      and Bdef: "B = stamped_at (length (dwu_journal t)) g (drop m R)"
      and s1: "dwu_step t (UArm g B f) t1"
      and s2: "dwu_step t1 (UHeal g f) t2"
      and s3: "dwu_step t2 (UFire g) t3"
  shows "dwt_track_inv t3
       \<and> (astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t) (dwu_ledger_proj t3)"
proof -
  from dwu_step_arm_inv[OF s1] have
    g1: "dwu_gens t1 = (dwu_gens t)(g \<mapsto> UArmed B)" and store1: "dwu_store t1 = dwu_store t" and
    jour1: "dwu_journal t1 = dwu_journal t" and acc1: "dwu_accepted t1 = dwu_accepted t" and
    fence1: "dwu_fence t1 = dwu_fence t" by auto
  from dwu_step_heal_frame[OF s2] have
    g2: "dwu_gens t2 = dwu_gens t1" and jour2: "dwu_journal t2 = dwu_journal t1" and
    acc2: "dwu_accepted t2 = dwu_accepted t1" and fence2: "dwu_fence t2 = dwu_fence t1" by auto
  from dwu_step_heal_src_base[OF s2] have
    src2: "exec_src_hist (dwu_store t2) = exec_src_hist (dwu_store t1)" and
    base2: "exec_base (dwu_store t2) = exec_base (dwu_store t1)" by auto
  from dwu_step_fire_full[OF s3] obtain B' where
    g2B: "dwu_gens t2 g = Some (UArmed B')" and
    acc3: "dwu_accepted t3 = dwu_accepted t2 @ (if dwu_fence t2 \<le> g then B' else [])" and
    g3: "dwu_gens t3 = (dwu_gens t2)(g \<mapsto> UProd)" and
    jour3: "dwu_journal t3 = dwu_journal t2" and fence3: "dwu_fence t3 = dwu_fence t2" and
    store3: "dwu_store t3 = dwu_store t2" by blast
  have BeqB': "B' = B" using g2B by (simp add: g2 g1)
  have jour3t: "dwu_journal t3 = dwu_journal t" using jour3 jour2 jour1 by simp
  have fence3t: "dwu_fence t3 = dwu_fence t" using fence3 fence2 fence1 by simp
  have acc3t: "dwu_accepted t3 = dwu_accepted t @ (if dwu_fence t \<le> g then B else [])"
    using acc3 acc2 acc1 fence2 fence1 BeqB' by simp
  have g3t: "dwu_gens t3 = (dwu_gens t)(g \<mapsto> UProd)" using g3 g2 g1 by simp
  have src3: "exec_src_hist (dwu_store t3) = exec_src_hist (dwu_store t)"
    using store3 src2 store1 by simp
  have base3: "exec_base (dwu_store t3) = exec_base (dwu_store t)"
    using store3 base2 store1 by simp
  have inv3: "dwt_track_inv t3"
  proof -
    have C3': "dwu_journal t3 = exec_src_hist (dwu_store t3)"
      using dwt_track_invD(1)[OF inv] by (simp add: jour3t src3)
    have C4': "\<And>g' B''. dwu_gens t3 g' = Some (UArmed B'') \<Longrightarrow> g' \<le> dwu_fence t3"
    proof -
      fix g' B'' assume "dwu_gens t3 g' = Some (UArmed B'')"
      with g3t have "dwu_gens t g' = Some (UArmed B'') \<and> g' \<noteq> g"
        by (auto split: if_split_asm)
      with D1b fence3t show "g' \<le> dwu_fence t3" by fastforce
    qed
    have U': "\<And>g' B'' x. \<lbrakk>dwu_gens t3 g' = Some (UArmed B''); x \<in> set B''\<rbrakk> \<Longrightarrow> ue_gen x = g'"
    proof -
      fix g' B'' x assume gB'': "dwu_gens t3 g' = Some (UArmed B'')" and xB: "x \<in> set B''"
      from gB'' g3t have "dwu_gens t g' = Some (UArmed B'')" by (auto split: if_split_asm)
      from dwt_track_invD(3)[OF inv this xB] show "ue_gen x = g'" .
    qed
    show ?thesis unfolding dwt_track_inv_def using C3' C4' U' by blast
  qed
  have P0: "t_pending (dwu_ledger_proj t) = []"
    by (rule d1b_projects_empty_pending[OF D1b])
  have P3: "t_pending (dwu_ledger_proj t3) = []"
  proof -
    have "\<forall>g' B''. dwu_gens t3 g' = Some (UArmed B'') \<longrightarrow> g' < dwu_fence t3"
      using D1b by (auto simp: g3t fence3t split: if_split_asm)
    then show ?thesis by (rule d1b_projects_empty_pending)
  qed
  have P3raw: "(case dwu_gens t3 (dwu_fence t) of Some (UArmed BB) \<Rightarrow> BB | _ \<Rightarrow> []) = []"
    using P3 by (simp add: dwu_ledger_proj_def fence3t)
  show ?thesis
  proof (cases "dwu_fence t \<le> g")
    case True
    have genB: "\<forall>x \<in> set B. ue_gen x = g"
      by (auto simp: Bdef dest: stamped_at_gen)
    have fB: "filter (\<lambda>y. dwu_fence t \<le> ue_gen y) B = B"
      using fire_gate_shape[OF genB, of "dwu_fence t"] True by simp
    have dmR_sub: "set (drop m R) \<subseteq> set (dwu_journal t)"
    proof -
      have "set (drop m R) \<subseteq> set R" by (rule set_drop_subset)
      also have "set R \<subseteq> set (retained_hist t)" using Rdef replay_subset by simp
      also have "\<dots> \<subseteq> set (exec_src_hist (dwu_store t))" by (rule retained_subset)
      also have "\<dots> = set (dwu_journal t)" using dwt_track_invD(1)[OF inv] by simp
      finally show ?thesis .
    qed
    define mid where "mid = (dwu_ledger_proj t)\<lparr>t_pending := B\<rparr>"
    have m1: "astep ue_gen upay uj ujle fire_transit (dwu_ledger_proj t) mid"
    proof (rule astepStageI)
      show "mid = (dwu_ledger_proj t)\<lparr>t_pending := t_pending (dwu_ledger_proj t) @ B\<rparr>"
        by (simp add: mid_def P0)
      show "B = filter (\<lambda>y. t_fence (dwu_ledger_proj t) \<le> ue_gen y) B"
        by (simp add: dwu_ledger_proj_def fB)
      show "distinct (lpays upay B)"
        using ddist by (simp add: Bdef lpays_is_log_payloads)
      show "set (lpays upay B) \<inter> set (lpays upay (t_accepted (dwu_ledger_proj t))) = {}"
        using ddisj by (simp add: Bdef lpays_is_log_payloads dwu_ledger_proj_def)
      show "set (lpays upay B) \<inter> set (lpays upay (a_eligible ue_gen (dwu_ledger_proj t))) = {}"
        by (simp add: a_eligible_def P0)
      show "\<forall>y \<in> set B. uj (t_journal (dwu_ledger_proj t)) y"
      proof
        fix y assume "y \<in> set B"
        then obtain p where y: "y = \<lparr> ue_stamp = length (dwu_journal t),
                                      ue_gen = g, ue_pay = ULog p \<rparr>"
                        and pD: "p \<in> set (drop m R)"
          by (auto simp: Bdef stamped_at_def)
        from pD dmR_sub have pJ: "p \<in> set (dwu_journal t)" by blast
        show "uj (t_journal (dwu_ledger_proj t)) y"
          by (simp add: dwu_ledger_proj_def uj_def y pJ)
      qed
    qed
    have m2: "astep ue_gen upay uj ujle fire_transit mid (dwu_ledger_proj t3)"
    proof (rule astepDeliverI)
      show "dwu_ledger_proj t3
              = mid\<lparr>t_pending := [],
                    t_accepted := t_accepted mid @ filter (\<lambda>y. t_fence mid \<le> ue_gen y) B\<rparr>"
        by (simp add: mid_def dwu_ledger_proj_def acc3t jour3t fence3t base3
                      True fB P3raw)
      show "mset (t_pending mid) = mset B + mset []"
        by (simp add: mid_def)
    qed
    have moves: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>*
                   (dwu_ledger_proj t) (dwu_ledger_proj t3)"
      using m1 m2 by (meson converse_rtranclp_into_rtranclp r_into_rtranclp)
    from inv3 moves show ?thesis ..
  next
    case False
    have fne: "dwu_fence t \<noteq> g" using False by auto
    have "dwu_ledger_proj t3 = dwu_ledger_proj t"
      by (rule dwu_ledger_proj_cong)
         (simp_all add: g3t fence3t acc3t jour3t base3 False fne)
    then show ?thesis using inv3 by simp
  qed
qed

section \<open>4. The tracking induction (the pullback)\<close>

lemma dwt_fire_tracking:
  "u_disciplined_trace s acts t \<Longrightarrow> dwt_track_inv s \<Longrightarrow>
     dwt_track_inv t
   \<and> (astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj s) (dwu_ledger_proj t)"
proof (induction rule: u_disciplined_trace.induct)
  case (ud_refl t) then show ?case by simp
next
  case (ud_nonpub t a g t' as t'')
  from dwt_sim_nonpub[OF ud_nonpub.prems ud_nonpub.hyps(3) ud_nonpub.hyps(4)]
  have i1: "dwt_track_inv t'"
    and m1: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t) (dwu_ledger_proj t')"
    by blast+
  from ud_nonpub.IH[OF i1]
  have i2: "dwt_track_inv t''"
    and m2: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t') (dwu_ledger_proj t'')"
    by blast+
  show ?case using i2 rtranclp_trans[OF m1 m2] by blast
next
  case (ud_publish t c e g t' as t'')
  from dwt_sim_publish[OF ud_publish.prems ud_publish.hyps(3) ud_publish.hyps(4)
                          ud_publish.hyps(5) ud_publish.hyps(6)]
  have i1: "dwt_track_inv t'"
    and m1: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t) (dwu_ledger_proj t')"
    by blast+
  from ud_publish.IH[OF i1]
  have i2: "dwt_track_inv t''"
    and m2: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t') (dwu_ledger_proj t'')"
    by blast+
  show ?case using i2 rtranclp_trans[OF m1 m2] by blast
next
  case (ud_publost t c e g t' as t'')
  from dwt_sim_publost[OF ud_publost.prems ud_publost.hyps(3)]
  have i1: "dwt_track_inv t'"
    and m1: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t) (dwu_ledger_proj t')"
    by blast+
  from ud_publost.IH[OF i1]
  have i2: "dwt_track_inv t''"
    and m2: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t') (dwu_ledger_proj t'')"
    by blast+
  show ?case using i2 rtranclp_trans[OF m1 m2] by blast
next
  case (ud_snap v t c k g t' as t'')
  from dwt_sim_snap[OF ud_snap.prems ud_snap.hyps(1) ud_snap.hyps(2)]
  have i1: "dwt_track_inv t'"
    and m1: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t) (dwu_ledger_proj t')"
    by blast+
  from ud_snap.IH[OF i1]
  have i2: "dwt_track_inv t''"
    and m2: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t') (dwu_ledger_proj t'')"
    by blast+
  show ?case using i2 rtranclp_trans[OF m1 m2] by blast
next
  case (ud_spawn t t' as t'')
  from dwt_sim_spawn[OF ud_spawn.prems ud_spawn.hyps(1)]
  have i1: "dwt_track_inv t'"
    and m1: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t) (dwu_ledger_proj t')"
    by blast+
  from ud_spawn.IH[OF i1]
  have i2: "dwt_track_inv t''"
    and m2: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t') (dwu_ledger_proj t'')"
    by blast+
  show ?case using i2 rtranclp_trans[OF m1 m2] by blast
next
  case (ud_release t g t' as t'')
  from dwt_sim_release[OF ud_release.prems ud_release.hyps(1)]
  have i1: "dwt_track_inv t'"
    and m1: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t) (dwu_ledger_proj t')"
    by blast+
  from ud_release.IH[OF i1]
  have i2: "dwt_track_inv t''"
    and m2: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t') (dwu_ledger_proj t'')"
    by blast+
  show ?case using i2 rtranclp_trans[OF m1 m2] by blast
next
  case (ud_claim t g f t' as t'')
  from dwt_sim_claim[OF ud_claim.prems ud_claim.hyps(1) ud_claim.hyps(2)]
  have i1: "dwt_track_inv t'"
    and m1: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t) (dwu_ledger_proj t')"
    by blast+
  from ud_claim.IH[OF i1]
  have i2: "dwt_track_inv t''"
    and m2: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t') (dwu_ledger_proj t'')"
    by blast+
  show ?case using i2 rtranclp_trans[OF m1 m2] by blast
next
  case (ud_fire t g t' as t'')
  from dwt_sim_fire[OF ud_fire.prems ud_fire.hyps(1)]
  have i1: "dwt_track_inv t'"
    and m1: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t) (dwu_ledger_proj t')"
    by blast+
  from ud_fire.IH[OF i1]
  have i2: "dwt_track_inv t''"
    and m2: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t') (dwu_ledger_proj t'')"
    by blast+
  show ?case using i2 rtranclp_trans[OF m1 m2] by blast
next
  case (ud_retain t n t' as t'')
  from dwt_sim_retain[OF ud_retain.prems ud_retain.hyps(1)]
  have i1: "dwt_track_inv t'"
    and m1: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t) (dwu_ledger_proj t')"
    by blast+
  from ud_retain.IH[OF i1]
  have i2: "dwt_track_inv t''"
    and m2: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t') (dwu_ledger_proj t'')"
    by blast+
  show ?case using i2 rtranclp_trans[OF m1 m2] by blast
next
  case (ud_cursor_recovery R t f m B g t1 t2 t3 as t'')
  from dwt_sim_cursor[OF ud_cursor_recovery.prems ud_cursor_recovery.hyps(1)
                         ud_cursor_recovery.hyps(3) ud_cursor_recovery.hyps(4)
                         ud_cursor_recovery.hyps(5) ud_cursor_recovery.hyps(6)
                         ud_cursor_recovery.hyps(7) ud_cursor_recovery.hyps(8)
                         ud_cursor_recovery.hyps(9)]
  have i1: "dwt_track_inv t3"
    and m1: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t) (dwu_ledger_proj t3)"
    by blast+
  from ud_cursor_recovery.IH[OF i1]
  have i2: "dwt_track_inv t''"
    and m2: "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (dwu_ledger_proj t3) (dwu_ledger_proj t'')"
    by blast+
  show ?case using i2 rtranclp_trans[OF m1 m2] by blast
qed

section \<open>5. The pullback theorems and the U8 bridge corollary\<close>

text \<open>The pullback proper: the ledger projection of every disciplined-reachable
  dwu-state is abstractly reachable at the fire instance --- the reachability
  hypothesis of @{thm [source] u8_statement_shape_recovered_fire} is
  DISCHARGED, not assumed.\<close>

theorem dwt_fire_pullback:
  assumes "u_disciplined_trace (dwu_init b K fin) acts t"
  shows "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>* (ainit ([], b)) (dwu_ledger_proj t)"
proof -
  from dwt_fire_tracking[OF assms dwt_track_inv_init]
  have "(astep ue_gen upay uj ujle fire_transit)\<^sup>*\<^sup>*
          (dwu_ledger_proj (dwu_init b K fin)) (dwu_ledger_proj t)" by blast
  then show ?thesis by (simp add: dwu_ledger_proj_init)
qed

text \<open>The abstract-side face: the projection lands in the abstract safe region
  (the interface theorem, consumed at the fire instance).\<close>

corollary dwt_fire_projection_safe:
  assumes "u_disciplined_trace (dwu_init b K fin) acts t"
  shows "\<not> a_unsafe uj upay (dwu_ledger_proj t)"
  by (rule fire_a_safety[OF dwt_fire_pullback[OF assms]])

text \<open>THE BRIDGE: Road-2's U8 safety conclusion as a corollary of the interface
  theorem.  The statement below is LITERALLY the statement of the landed
  @{thm [source] u_fenced_multiwriter_discipline_safe}
  (DWU_Fenced_Discipline.thy); the landed theorem REMAINS the theorem of
  record and the pinned principal --- this corollary exhibits the second,
  interface-factored proof route: tracking (geometric bookkeeping) + a_safety
  (the once-proved ledger safety) + the definitional hazard identity.\<close>

theorem u8_safety_via_transit_interface:
  assumes "u_disciplined_trace (dwu_init b K fin) acts t"
  shows "\<not> u_effect_unsafe t"
  using dwt_fire_projection_safe[OF assms]
  by (simp add: fire_hazard_correspondence)

corollary u8_duplicate_free_via_transit_interface:
  assumes "u_disciplined_trace (dwu_init b K fin) acts t"
  shows "distinct (log_payloads (dwu_accepted t))"
  using u8_safety_via_transit_interface[OF assms]
  by (simp add: u_effect_unsafe_def u_duplicate_def)

corollary u8_justified_via_transit_interface:
  assumes "u_disciplined_trace (dwu_init b K fin) acts t"
  shows "\<forall>x \<in> set (dwu_accepted t). u_justified t x"
  using u8_safety_via_transit_interface[OF assms]
  by (auto simp: u_effect_unsafe_def u_premature_def)

end
