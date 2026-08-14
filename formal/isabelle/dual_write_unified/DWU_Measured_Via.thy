(*  Title:       DWU_Measured_Via.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE M-VIEW SLICE (reference-object program, Phase 2; owner decisions
    D-095/D-097) --- an additive post-freeze sibling under the freeze's
    own protocol: no landed statement, proof, definition, name, import,
    or session-DAG change to the frozen corpus.  Discipline: ONE
    definitional schema + characterizations and re-derivations of
    already-proved facts.  No new claim territory: every dilemma-shaped
    statement below is the LANDED R2/R3 statement re-derived, verbatim,
    from the schema.

    THE SCHEMA.  The four landed measurability classes
    (u_store_measured / u_control_plane_measured / u_retained_measured /
    u_retention_respecting, DWU_Machine.thy:371-406) are literally one
    pattern differing only in the vantage:

        measured_via view P  <->  (EX g. ALL t. P t = g (view t))

    "P is a function of what the vantage shows."  This theory names the
    pattern once, proves the four classes are its instances (one
    unfolding each), and banks the two general laws every landed
    dilemma proof reuses:

      - agreement: a measured policy cannot distinguish states its
        vantage identifies (measured_via_agreement);
      - monotonicity: if one vantage factors through another, being
        measured through the coarser implies being measured through the
        finer (measured_via_mono) --- giving the measurability LATTICE
        store <= control-plane <= retained and retention <= retained as
        three one-line corollaries.

    THE DILEMMA SCHEMA.  The landed batch-agreement kernel's designed
    pair (u_batch_agreement_dilemma, DWU_Recovery_Rows.thy:258) is equal
    on ALL SIX control-plane coordinates and divergent exactly on the
    two emission ledgers.  Hence ONE schema covers every vantage that
    factors through the control plane: for ANY h,

        every (h o u_control_plane_view)-measured policy is defeated
        (u_control_plane_vantage_dilemma below),

    and the landed R2/R3 statements drop out as instances:
    R3 = the schema at h = identity; R2 = the schema plus the lattice
    leg store <= control-plane (the "R2 <== R3 for free" collapse).
    Both are re-derived below AS THE LANDED STATEMENTS, VERBATIM
    (named *_via_schema; the landed theorems stay untouched and remain
    the pinned principals).

    THE DISCLOSED CEILING (this fence travels with every quotation):
    the schema stops exactly at the ledgers.  The kernel pair AGREES on
    the whole control plane and DIFFERS exactly in (sent, accepted) ---
    so no instance of this schema can defeat a retained-measured
    (ledger-reading) policy, and it must not: the sink-reading escape
    (u_sink_reading_escape, R4) lives there.  The vantage lattice's
    defeated segment tops out strictly below the ledgers.  This is the
    unified-machine face of the effect tier's observation bound
    ("recovery can only restore what it can observe",
    observation_bound = observation_measured_dilemma, effect ladder
    section 40/31 --- cited as prose here; the effect theory is not in
    this session's import cone): a vantage that cannot see the sink's
    accepted record cannot arbitrate re-delivery, and the ONLY
    coordinates the designed pair hides from are exactly the sink
    ledgers.

    Exists-machine polarity throughout: every defeat below is "at the
    kernel's designed pair" --- there IS a reachable pair on which every
    such policy fails --- never a for-every-system claim, and never
    "exactly-once is impossible" as a pure negative.  The retention
    deviation disclosed at DWU_Machine.thy:364-369 (the above-floor view
    concretization) is inherited unchanged; this theory adds no new
    reading of it.

    Provenance: reference-object program Phase-2 M-view slice
    (roads/program/, owner decisions D-095, D-097 L14; design source
    roads/road3/_evidence/road3_explorers.json "M-view"), gate
    EGate-R2-M1.  In-source ML oracle gates are STRIPPED at landing per
    house rule; oracle-freedom is certified by the scratch-side gate
    session with confirmed-biting negative controls
    (roads/program/phase2_gates/egate_r2_m1/).
*)

theory DWU_Measured_Via
  imports DWU_Recovery_Rows
begin

section \<open>The measured-via schema\<close>

definition measured_via :: "('s \<Rightarrow> 'a) \<Rightarrow> ('s \<Rightarrow> 'b) \<Rightarrow> bool" where
  "measured_via view P \<longleftrightarrow> (\<exists>g. \<forall>t. P t = g (view t))"

text \<open>The two general laws every landed measured-dilemma proof reuses.\<close>

lemma measured_via_agreement:
  assumes "measured_via view P" and "view t1 = view t2"
  shows "P t1 = P t2"
  using assms unfolding measured_via_def by metis

lemma measured_via_mono:
  assumes MV: "measured_via view P"
      and F: "\<And>t. view t = h (view' t)"
  shows "measured_via view' P"
proof -
  from MV obtain g where g: "\<forall>t. P t = g (view t)"
    unfolding measured_via_def by blast
  have "\<forall>t. P t = (g \<circ> h) (view' t)" using g F by simp
  then show ?thesis unfolding measured_via_def by blast
qed

section \<open>The four landed classes are instances (one unfolding each)\<close>

lemma u_store_measured_measured_via:
  "u_store_measured P \<longleftrightarrow> measured_via dwu_store P"
  unfolding u_store_measured_def measured_via_def by simp

lemma u_control_plane_measured_measured_via:
  "u_control_plane_measured P \<longleftrightarrow> measured_via u_control_plane_view P"
  unfolding u_control_plane_measured_def measured_via_def by simp

lemma u_retained_measured_measured_via:
  "u_retained_measured P \<longleftrightarrow> measured_via u_retained_view P"
  unfolding u_retained_measured_def measured_via_def by simp

lemma u_retention_respecting_measured_via:
  "u_retention_respecting P \<longleftrightarrow> measured_via u_retention_view P"
  unfolding u_retention_respecting_def measured_via_def by simp

section \<open>The vantage lattice (factoring projections, hence measurability inclusions)\<close>

text \<open>Each leg exhibits the explicit factoring @{text h} and applies
  @{thm [source] measured_via_mono}.  The store is the first coordinate
  of the control-plane view; the control-plane view is the first six
  coordinates of the retained view; the retention view is the retained
  view with the store's history component replaced by its own
  above-floor suffix (@{const retained_hist} reads only the store and
  the floor, both retained-view coordinates).\<close>

lemma dwu_store_factors_control_plane:
  "dwu_store t = fst (u_control_plane_view t)"
  by (simp add: u_control_plane_view_def)

lemma u_control_plane_factors_retained:
  "u_control_plane_view t =
     (\<lambda>(st, lsn, fn, gs, hw, fl, sn, ac). (st, lsn, fn, gs, hw, fl))
       (u_retained_view t)"
  by (simp add: u_control_plane_view_def u_retained_view_def)

lemma u_retention_factors_retained:
  "u_retention_view t =
     (\<lambda>(st, lsn, fn, gs, hw, fl, sn, ac).
        (st\<lparr>exec_src_hist := drop fl (exec_src_hist st)\<rparr>, lsn, fn, gs, hw, fl, sn, ac))
       (u_retained_view t)"
  by (simp add: u_retention_view_def u_retained_view_def retained_hist_def)

lemma u_store_measured_imp_control_plane_measured:
  assumes "u_store_measured P"
  shows "u_control_plane_measured P"
proof -
  have "measured_via dwu_store P"
    using assms by (simp add: u_store_measured_measured_via)
  then have "measured_via u_control_plane_view P"
    by (rule measured_via_mono) (rule dwu_store_factors_control_plane)
  then show ?thesis by (simp add: u_control_plane_measured_measured_via)
qed

lemma u_control_plane_measured_imp_retained_measured:
  assumes "u_control_plane_measured P"
  shows "u_retained_measured P"
proof -
  have "measured_via u_control_plane_view P"
    using assms by (simp add: u_control_plane_measured_measured_via)
  then have "measured_via u_retained_view P"
    by (rule measured_via_mono) (rule u_control_plane_factors_retained)
  then show ?thesis by (simp add: u_retained_measured_measured_via)
qed

lemma u_retention_respecting_imp_retained_measured:
  assumes "u_retention_respecting P"
  shows "u_retained_measured P"
proof -
  have "measured_via u_retention_view P"
    using assms by (simp add: u_retention_respecting_measured_via)
  then have "measured_via u_retained_view P"
    by (rule measured_via_mono) (rule u_retention_factors_retained)
  then show ?thesis by (simp add: u_retained_measured_measured_via)
qed

section \<open>The dilemma schema: every control-plane vantage is defeated\<close>

text \<open>The kernel's designed pair is equal on all six control-plane
  coordinates (@{thm [source] u_batch_agreement_dilemma}), so ANY
  vantage of the form @{text "h \<circ> u_control_plane_view"} agrees on it,
  and every policy measured through such a vantage is defeated.  The
  conclusion below is the landed R3 conclusion, verbatim.  CEILING
  (disclosed): the pair's ledgers DIFFER, so no instance of this schema
  reaches a retained-measured (ledger-reading) vantage --- correctly,
  since the sink-reading escape lives exactly there.\<close>

theorem u_control_plane_vantage_dilemma:
  fixes h :: "(nat, nat) dw_exec_state \<times> nat \<times> nat \<times> (nat \<rightharpoonup> (nat, nat) ustage) \<times> nat \<times> nat \<Rightarrow> 'a"
  shows "\<forall>P. measured_via (\<lambda>t. h (u_control_plane_view t)) P \<longrightarrow>
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
  assume mv: "measured_via (\<lambda>t. h (u_control_plane_view t)) P"
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
  have AGREE: "(\<lambda>t. h (u_control_plane_view t)) t1 = (\<lambda>t. h (u_control_plane_view t)) t2"
    using VIEW by simp
  have PB: "P t1 = P t2"
    by (rule measured_via_agreement[OF mv AGREE])
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

section \<open>The landed R3 and R2 statements, re-derived from the schema\<close>

text \<open>R3 verbatim = the schema at @{text "h = identity"}.\<close>

corollary u_control_plane_measured_dilemma_via_schema:
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
  assume "u_control_plane_measured P"
  then have "measured_via (\<lambda>t. (\<lambda>v. v) (u_control_plane_view t)) P"
    by (simp add: u_control_plane_measured_measured_via)
  from u_control_plane_vantage_dilemma[rule_format, OF this]
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
      \<and> (u_effect_unsafe t1' \<or> u_lost ec2 t2')" .
qed

text \<open>R2 verbatim = the schema plus the lattice leg
  store \<le> control-plane, with the pair's control-plane equality
  weakened to the store equality R2 states (first-coordinate
  projection).  This is the "R2 \<Longleftarrow> R3 for free" collapse, exhibited.\<close>

corollary u_recovery_information_dilemma_via_schema:
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
  assume "u_store_measured P"
  then have "u_control_plane_measured P"
    by (rule u_store_measured_imp_control_plane_measured)
  then have "measured_via (\<lambda>t. (\<lambda>v. v) (u_control_plane_view t)) P"
    by (simp add: u_control_plane_measured_measured_via)
  from u_control_plane_vantage_dilemma[rule_format, OF this] obtain t1 t2 t1' t2' where
    C: "dwu_reachable_w t1 \<and> dwu_reachable_w t2
      \<and> u_control_plane_view t1 = u_control_plane_view t2
      \<and> dwu_sent t1 \<noteq> dwu_sent t2
      \<and> \<not> u_effect_unsafe t1 \<and> \<not> u_effect_unsafe t2
      \<and> u_genuinely_emitting t1 \<and> u_genuinely_emitting t2
      \<and> u_policy_redrive P t1 ec2 t1'
      \<and> u_policy_redrive P t2 ec2 t2'
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t1') ec2) ec2 k)
      \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwu_store t2') ec2) ec2 k)
      \<and> (u_effect_unsafe t1' \<or> u_lost ec2 t2')" by blast
  have "dwu_store t1 = dwu_store t2"
    using C dwu_store_factors_control_plane by (metis (mono_tags, lifting))
  then show "\<exists>t1 t2 t1' t2'.
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
    using C by blast
qed

end
