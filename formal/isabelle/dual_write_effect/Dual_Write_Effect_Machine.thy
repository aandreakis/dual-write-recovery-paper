(*  Title:       Dual_Write_Effect_Machine.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    The emitted-effect tier (tier 2) of the dual-write development: a
    conservative wrapper machine over the locked Dual_Write_Core execution
    layer (Design B, Checkpointed Emitting Re-drive Reconcile).  Every
    downstream publish is an externally visible EMISSION recorded in an
    append-only ledger, and recovery's re-drive is itself emitting work
    driven by a persisted consumer cursor.  Ported from the phase-2 verified
    scratch source (p1 Effect_Machine.thy) with statements unchanged; the
    scratch-side oracle gates certify each landed slice separately.

    TWIN DISCLOSURE: this theory is the TERMINAL branch of two effect
    machines that share constant names.  The headline effect theorems
    live on the cyclic machine (Dual_Write_Effect_Cyclic, which imports
    Dual_Write_Core.Dual_Write_Relay and NOT this theory) and on the
    channel machine built downstream of that cyclic branch (T4-T5); none
    is stated over this theory.  This branch is imported only by
    Dual_Write_Effect_Witnesses.

    ARCHITECTURE NOTES (the two traps this theory answers by construction):

    T1 (image collapse): emission justification is defined AT EMISSION TIME
    against the committed durable source prefix, never via the final image.
    Each emission carries a STAMP = |exec_src_hist| at fire time; because
    exec_src_hist is append-only under every rule (only do_source touches it;
    the reconcile writes down_hist/pending/status only), the state-readable
    check "payload is in the first `stamp` entries of the current source
    history" provably equals the fire-time check (justified_at_append_stable).

    T3 (thinness vs exec_enqueued): the emission ledger is NOT a
    reconcile-surviving copy of any delivered list.  The emitting reconcile
    APPENDS its re-driven suffix to the ledger while exec_enqueued (and every
    other core field except down_hist/pending/status) is reconcile-inert, so
    no landed core field can witness the re-drive (see
    reconcile_extends_ledger_not_enqueued and, decisively, the G1 separation:
    two reachable states with LITERALLY EQUAL cores and opposite verdicts).

    NAMED MODELLING PREMISES (prose, deliberately NOT theorems):

    * authority_effect_blind -- the source-of-truth schema stores business
      facts (e.g. paid : bool), never emission-attempt counters.  No image
      over the authority's own schema can recover emission multiplicity;
      if the authority logged attempt counts, duplicates would be
      image-visible and this tier would collapse into the landed image
      characterization.  This is why the separation below is possible, and
      it is a hypothesis about schemas, not a derived fact.

    * strictly_ascending_source -- real WALs have strictly increasing
      coordinates, so payload-level dedup is exact.  In-model, WF-H1 only
      requires non-decreasing coordinates, so an equal-coordinate re-commit
      is legal and would alias a payload-level duplicate.  All witnesses in
      this development use distinct coordinates, so no gate needs this
      premise; a future effect-safety characterization would.

    * checkpoint-as-cursor -- the reconcile parameter m models the PERSISTED
      CONSUMER CURSOR of an at-least-once delivery channel: the re-drive
      replays the scoped committed prefix from position m.  A crashed
      consumer whose cursor was persisted BEFORE its last delivery (m = 0
      after one delivery) re-fires that delivery: the at-least-once window
      IS a stale cursor.  m is a rule parameter, not an adversary's oracle.

    Two further disclosed boundaries carried as text blocks in the body:
    the two-store reading of the state record (durable core vs the external
    world's received effects --- why the world does not roll back), and the
    skip asymmetry of effect_unsafe (a disowned liveness axis).  The
    reconcile is one ATOMIC big-step rule: a crash DURING a re-drive is
    inexpressible in this machine; that boundary is disclosed here rather
    than hidden.
*)

theory Dual_Write_Effect_Machine
  imports
    Dual_Write_Core.Dual_Write_Relay
    Dual_Write_Core.Dual_Write_Recovery
begin

section \<open>Emissions and the effect-tier state\<close>

type_synonym ('k, 'v) emission = "nat \<times> src_coord \<times> ('k, 'v) source_event"

definition e_stamp :: "('k, 'v) emission \<Rightarrow> nat" where
  "e_stamp = fst"

definition e_payload
  :: "('k, 'v) emission \<Rightarrow> src_coord \<times> ('k, 'v) source_event"
where
  "e_payload = snd"

lemma e_stamp_simp [simp]: "e_stamp (n, c, e) = n"
  by (simp add: e_stamp_def)

lemma e_payload_simp [simp]: "e_payload (n, c, e) = (c, e)"
  by (simp add: e_payload_def)

record ('k, 'v) dwe_state =
  dwe_core    :: "('k, 'v) dw_exec_state"
  dwe_emitted :: "('k, 'v) emission list"

text \<open>
  The two-store boundary this tier is about.  @{const dwe_core} is the
  DURABLE STORE side: everything a recovery procedure can rewrite in place
  --- the landed heal theorems live there.  @{const dwe_emitted} is the
  EXTERNAL WORLD's record of received effects: messages already published to
  consumers outside the system's write authority (webhooks fired, emails
  sent, downstream systems notified).  The world does not roll back: no rule
  of this machine removes a ledger entry, and no landed core field can see
  the ledger.  Everything the effect tier proves is a consequence of placing
  the model boundary exactly at this line.
\<close>

definition dwe_init
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'k set \<Rightarrow> frontier \<Rightarrow> ('k, 'v) dwe_state"
where
  "dwe_init b K fin =
     \<lparr> dwe_core = initial_exec_state b K fin, dwe_emitted = [] \<rparr>"

section \<open>The effect-tier step relation: emission IS the externally visible publish\<close>

inductive dwe_step
  :: "('k, 'v) dwe_state \<Rightarrow> ('k, 'v) dw_exec_label \<Rightarrow>
      ('k, 'v) dwe_state \<Rightarrow> bool"
where
  lift_nonpub:
    "dw_exec_step (dwe_core t) a c' \<Longrightarrow>
     (\<forall>c e. a \<noteq> DoDownstream c e) \<Longrightarrow>
     dwe_step t a \<lparr> dwe_core = c', dwe_emitted = dwe_emitted t \<rparr>"
| publish_emit:
    "dw_exec_step (dwe_core t) (DoDownstream c e) c' \<Longrightarrow>
     dwe_step t (DoDownstream c e)
       \<lparr> dwe_core = c',
         dwe_emitted = dwe_emitted t
           @ [(length (exec_src_hist (dwe_core t)), c, e)] \<rparr>"

text \<open>Derived introduction rules with an explicit successor equation (for witnesses).\<close>

lemma dwe_step_lift_nonpubI:
  assumes "dw_exec_step (dwe_core t) a c'"
      and "\<forall>c e. a \<noteq> DoDownstream c e"
      and "t' = \<lparr> dwe_core = c', dwe_emitted = dwe_emitted t \<rparr>"
  shows "dwe_step t a t'"
  using assms dwe_step.lift_nonpub by blast

lemma dwe_step_publishI:
  assumes "dw_exec_step (dwe_core t) (DoDownstream c e) c'"
      and "t' = \<lparr> dwe_core = c',
                  dwe_emitted = dwe_emitted t
                    @ [(length (exec_src_hist (dwe_core t)), c, e)] \<rparr>"
  shows "dwe_step t (DoDownstream c e) t'"
  using assms dwe_step.publish_emit by blast

section \<open>The checkpointed EMITTING re-drive reconcile\<close>

text \<open>
  The core part is literally @{const relay_bounded_replay_reconcile}
  (@{text Dual_Write_Relay}): the scoped, frontier-bounded replay of the committed
  source history becomes the new durable downstream history.  The NEW content
  is on the ledger: the re-driven suffix @{term "drop m R"} is EMITTED (the
  re-drive is externally visible work), stamped with the current committed
  source length.

  @{term m} is the PERSISTED CONSUMER CURSOR of an at-least-once delivery
  channel: the re-drive replays the scoped committed prefix from position
  @{term m}.  A crashed consumer whose cursor was persisted BEFORE its last
  delivery re-fires that delivery --- the at-least-once window IS a stale
  cursor.  @{term m} is a rule parameter (a fact about the crashed state's
  durable checkpoint), not an adversary's oracle.

  The reconcile is one ATOMIC big-step rule: the store heal and the ledger
  append happen together, so a crash DURING a re-drive is inexpressible in
  this machine.  This is a disclosed model boundary of the same kind as
  acknowledgement durability in the landed tier, not a claim that real
  re-drives are atomic.
\<close>

definition emitting_reconcile
  :: "nat \<Rightarrow> ('k, 'v) dwe_state \<Rightarrow> frontier \<Rightarrow> ('k, 'v) dwe_state \<Rightarrow> bool"
where
  "emitting_reconcile m t f t' \<longleftrightarrow>
     (\<exists>c. exec_status (dwe_core t) = Crashed c)
   \<and> f \<le> exec_finish (dwe_core t)
   \<and> m \<le> length (replay_down_hist (exec_src_hist (dwe_core t))
                    (exec_scope (dwe_core t)) f)
   \<and> t' = \<lparr> dwe_core =
              (dwe_core t)\<lparr> exec_down_hist :=
                              replay_down_hist (exec_src_hist (dwe_core t))
                                (exec_scope (dwe_core t)) f,
                            exec_pending := {},
                            exec_status := Recovered \<rparr>,
            dwe_emitted =
              dwe_emitted t
              @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)), c, e))
                  (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                             (exec_scope (dwe_core t)) f)) \<rparr>"

section \<open>Temporal traces and reachability\<close>

datatype ('k, 'v) dwe_action =
    DWE_Label "('k, 'v) dw_exec_label"
  | DWE_Reconcile nat frontier

inductive dwe_temporal_trace
  :: "('k, 'v) dwe_state \<Rightarrow> ('k, 'v) dwe_action list \<Rightarrow>
      ('k, 'v) dwe_state \<Rightarrow> bool"
where
  dwe_temporal_refl:
    "dwe_temporal_trace t [] t"
| dwe_temporal_label_step:
    "\<lbrakk>dwe_step t a t';
      wellformed_exec_state (dwe_core t);
      exec_label_preserves_history_wf (dwe_core t) a;
      dwe_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwe_temporal_trace t (DWE_Label a # as) t''"
| dwe_temporal_reconcile_step:
    "\<lbrakk>emitting_reconcile m t f t';
      dwe_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwe_temporal_trace t (DWE_Reconcile m f # as) t''"

lemma dwe_temporal_trace_append:
  assumes "dwe_temporal_trace t as t'"
      and "dwe_temporal_trace t' bs t''"
  shows "dwe_temporal_trace t (as @ bs) t''"
  using assms
  by (induction rule: dwe_temporal_trace.induct)
     (auto intro: dwe_temporal_trace.intros)

lemma dwe_temporal_singleI:
  assumes "dwe_step t a t'"
      and "wellformed_exec_state (dwe_core t)"
      and "exec_label_preserves_history_wf (dwe_core t) a"
  shows "dwe_temporal_trace t [DWE_Label a] t'"
  by (rule dwe_temporal_trace.dwe_temporal_label_step
      [OF assms dwe_temporal_trace.dwe_temporal_refl])

lemma dwe_temporal_reconcile_singleI:
  assumes "emitting_reconcile m t f t'"
  shows "dwe_temporal_trace t [DWE_Reconcile m f] t'"
  by (rule dwe_temporal_trace.dwe_temporal_reconcile_step
      [OF assms dwe_temporal_trace.dwe_temporal_refl])

definition dwe_reachable
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'k set \<Rightarrow> frontier \<Rightarrow> ('k, 'v) dwe_state \<Rightarrow> bool"
where
  "dwe_reachable b K fin t \<longleftrightarrow>
     (\<exists>acts. dwe_temporal_trace (dwe_init b K fin) acts t)"

lemma dwe_reachable_init: "dwe_reachable b K fin (dwe_init b K fin)"
  unfolding dwe_reachable_def
  by (blast intro: dwe_temporal_trace.dwe_temporal_refl)

lemma dwe_reachable_trace_extend:
  assumes "dwe_reachable b K fin t"
      and "dwe_temporal_trace t acts t'"
  shows "dwe_reachable b K fin t'"
  using assms unfolding dwe_reachable_def
  by (blast intro: dwe_temporal_trace_append)

section \<open>Emission-time justification and the hazard taxonomy\<close>

text \<open>
  @{term "justified_at S x"}: the emission's payload sits in the first
  @{term "e_stamp x"} entries of the committed source history --- i.e. it was
  covered by the durable committed prefix AT THE MOMENT IT FIRED.  The stamp
  makes the fire-time check state-readable (T1 defence).
\<close>

definition justified_at
  :: "('k, 'v) src_history \<Rightarrow> ('k, 'v) emission \<Rightarrow> bool"
where
  "justified_at S x \<longleftrightarrow>
     e_stamp x \<le> length S \<and> e_payload x \<in> set (take (e_stamp x) S)"

definition premature :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "premature t \<longleftrightarrow>
     (\<exists>x \<in> set (dwe_emitted t).
        \<not> justified_at (exec_src_hist (dwe_core t)) x)"

text \<open>
  @{term phantom} is TAXONOMY ONLY: it reads the final source history, hence
  is non-monotone (a later commit can un-phantom an emission), and it is NOT
  part of @{term effect_unsafe}.  Its content is the absorption lemma below.
\<close>

definition phantom :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "phantom t \<longleftrightarrow>
     (\<exists>x \<in> set (dwe_emitted t).
        e_payload x \<notin> set (exec_src_hist (dwe_core t)))"

definition duplicate :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "duplicate t \<longleftrightarrow> \<not> distinct (map e_payload (dwe_emitted t))"

definition effect_unsafe :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "effect_unsafe t \<longleftrightarrow> premature t \<or> duplicate t"

definition genuinely_emitting :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "genuinely_emitting t \<longleftrightarrow> dwe_emitted t \<noteq> []"

text \<open>
  SKIP ASYMMETRY (a disclosed, disowned liveness axis).
  @{const effect_unsafe} is a SAFETY predicate over what WAS emitted: an emission
  fired too early (@{const premature}) or fired twice (@{const duplicate}).
  It deliberately cannot see what was never emitted.  A reconcile whose
  cursor @{term m} lies at or beyond the length of its re-drive suffix
  emits nothing (@{term "drop m R = []"} when @{term "length R \<le> m"}), so an
  over-advanced cursor silently SKIPS deliveries and the resulting state is
  effect-safe.  Delivery completeness is a liveness question this predicate
  disowns --- the exact reason an emitted-count characterization of
  effect-safety is false for this machine, and a boundary any later
  characterization built on @{const effect_unsafe} must account for
  separately.
\<close>

text \<open>
  The status-blind scoped-image predicate used by the corner statements
  (@{const observable_mismatch} hard-requires @{const Crashed} status, so it
  is used only for the mid-run crashed clause).
\<close>

definition P_img :: "('k, 'v) dwe_state \<Rightarrow> frontier \<Rightarrow> bool" where
  "P_img t f \<longleftrightarrow>
     (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t) f) f k)"

lemma phantom_imp_premature:
  assumes "phantom t"
  shows "premature t"
proof -
  from assms obtain x where x_in: "x \<in> set (dwe_emitted t)"
      and notin: "e_payload x \<notin> set (exec_src_hist (dwe_core t))"
    by (auto simp: phantom_def)
  have "\<not> justified_at (exec_src_hist (dwe_core t)) x"
  proof
    assume "justified_at (exec_src_hist (dwe_core t)) x"
    hence "e_payload x \<in> set (take (e_stamp x) (exec_src_hist (dwe_core t)))"
      by (simp add: justified_at_def)
    hence "e_payload x \<in> set (exec_src_hist (dwe_core t))"
      using set_take_subset by fastforce
    with notin show False ..
  qed
  with x_in show ?thesis by (auto simp: premature_def)
qed

section \<open>Gate I(a): the effect tier is a conservative wrapper (simulation)\<close>

theorem dwe_step_core:
  assumes "dwe_step t a t'"
  shows "dw_exec_step (dwe_core t) a (dwe_core t')"
  using assms by (cases rule: dwe_step.cases) simp_all

lemma dwe_step_emitted_extends:
  assumes "dwe_step t a t'"
  shows "\<exists>ys. dwe_emitted t' = dwe_emitted t @ ys"
  using assms by (cases rule: dwe_step.cases) auto

lemma dwe_step_src_hist_extends:
  assumes "dwe_step t a t'"
  shows "\<exists>zs. exec_src_hist (dwe_core t')
              = exec_src_hist (dwe_core t) @ zs"
  using dw_exec_step_src_hist[OF dwe_step_core[OF assms]] by blast

lemma emitting_reconcile_src_hist:
  assumes "emitting_reconcile m t f t'"
  shows "exec_src_hist (dwe_core t') = exec_src_hist (dwe_core t)"
  using assms by (auto simp: emitting_reconcile_def)

lemma emitting_reconcile_emitted:
  assumes "emitting_reconcile m t f t'"
  shows "dwe_emitted t' =
           dwe_emitted t
           @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)), c, e))
               (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                          (exec_scope (dwe_core t)) f))"
  using assms by (auto simp: emitting_reconcile_def)

text \<open>
  T3 witness at the lemma level: the reconcile EXTENDS the ledger while
  @{const exec_enqueued} (the landed append-only field recovery never touches)
  is reconcile-inert --- no landed core field can record the re-drive.
\<close>

lemma reconcile_extends_ledger_not_enqueued:
  assumes "emitting_reconcile m t f t'"
  shows "exec_enqueued (dwe_core t') = exec_enqueued (dwe_core t)"
    and "exec_acked (dwe_core t') = exec_acked (dwe_core t)"
    and "\<exists>ys. dwe_emitted t' = dwe_emitted t @ ys"
  using assms by (auto simp: emitting_reconcile_def)

section \<open>Gate I(b): the stamp invariant and fire-time stability\<close>

definition stamps_bounded :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "stamps_bounded t \<longleftrightarrow>
     (\<forall>x \<in> set (dwe_emitted t).
        e_stamp x \<le> length (exec_src_hist (dwe_core t)))"

lemma dwe_step_stamps_bounded:
  assumes step: "dwe_step t a t'"
      and inv: "stamps_bounded t"
  shows "stamps_bounded t'"
  using step inv
proof (induction rule: dwe_step.induct)
  case (lift_nonpub t a c')
  have "exec_src_hist c'
        = exec_src_hist (dwe_core t) @ src_hist_of_labels [a]"
    by (rule dw_exec_step_src_hist[OF lift_nonpub.hyps(1)])
  with lift_nonpub.prems show ?case
    by (fastforce simp: stamps_bounded_def intro: trans_le_add1)
next
  case (publish_emit t c e c')
  have "exec_src_hist c' = exec_src_hist (dwe_core t)"
    using dw_exec_step_src_hist[OF publish_emit.hyps(1)] by simp
  with publish_emit.prems show ?case
    by (auto simp: stamps_bounded_def)
qed

lemma emitting_reconcile_stamps_bounded:
  assumes rec: "emitting_reconcile m t f t'"
      and inv: "stamps_bounded t"
  shows "stamps_bounded t'"
proof -
  have src: "exec_src_hist (dwe_core t') = exec_src_hist (dwe_core t)"
    by (rule emitting_reconcile_src_hist[OF rec])
  have new: "\<And>x. x \<in> set (dwe_emitted t') \<Longrightarrow>
               x \<in> set (dwe_emitted t)
             \<or> e_stamp x = length (exec_src_hist (dwe_core t))"
    using emitting_reconcile_emitted[OF rec]
    by (auto simp: e_stamp_def split_beta)
  show ?thesis
    using inv new src by (fastforce simp: stamps_bounded_def)
qed

lemma dwe_temporal_trace_stamps_bounded:
  assumes trace: "dwe_temporal_trace t acts t'"
      and inv: "stamps_bounded t"
  shows "stamps_bounded t'"
  using trace inv
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_temporal_refl t)
  then show ?case .
next
  case (dwe_temporal_label_step t a t' as t'')
  have "stamps_bounded t'"
    by (rule dwe_step_stamps_bounded
        [OF dwe_temporal_label_step.hyps(1) dwe_temporal_label_step.prems])
  then show ?case by (rule dwe_temporal_label_step.IH)
next
  case (dwe_temporal_reconcile_step m t f t' as t'')
  have "stamps_bounded t'"
    by (rule emitting_reconcile_stamps_bounded
        [OF dwe_temporal_reconcile_step.hyps(1)
            dwe_temporal_reconcile_step.prems])
  then show ?case by (rule dwe_temporal_reconcile_step.IH)
qed

theorem dwe_reachable_stamps_bounded:
  assumes "dwe_reachable b K fin t"
  shows "stamps_bounded t"
proof -
  from assms obtain acts
    where trace: "dwe_temporal_trace (dwe_init b K fin) acts t"
    by (auto simp: dwe_reachable_def)
  have "stamps_bounded (dwe_init b K fin)"
    by (simp add: stamps_bounded_def dwe_init_def)
  with trace show ?thesis
    by (rule dwe_temporal_trace_stamps_bounded)
qed

text \<open>
  Fire-time stability (the T1 defence made precise): for an in-bounds stamp,
  the justification verdict is FROZEN by every later source append --- in both
  directions.  So the state-readable check equals the fire-time check.
\<close>

lemma justified_at_append_stable:
  assumes "e_stamp x \<le> length S"
  shows "justified_at (S @ S') x \<longleftrightarrow> justified_at S x"
proof -
  have "take (e_stamp x) (S @ S') = take (e_stamp x) S"
    using assms by simp
  with assms show ?thesis
    by (simp add: justified_at_def)
qed

section \<open>Gate I(c): effect\_unsafe is MONOTONE (the anti-healing negation of the image wall)\<close>

theorem effect_unsafe_monotone_step:
  assumes inv: "stamps_bounded t"
      and unsafe: "effect_unsafe t"
      and step: "dwe_step t a t'"
  shows "effect_unsafe t'"
proof -
  obtain ys where ys: "dwe_emitted t' = dwe_emitted t @ ys"
    using dwe_step_emitted_extends[OF step] by blast
  obtain zs where zs: "exec_src_hist (dwe_core t')
                       = exec_src_hist (dwe_core t) @ zs"
    using dwe_step_src_hist_extends[OF step] by blast
  from unsafe show ?thesis
    unfolding effect_unsafe_def
  proof
    assume "premature t"
    then obtain x where x_in: "x \<in> set (dwe_emitted t)"
        and nj: "\<not> justified_at (exec_src_hist (dwe_core t)) x"
      by (auto simp: premature_def)
    have bound: "e_stamp x \<le> length (exec_src_hist (dwe_core t))"
      using inv x_in by (auto simp: stamps_bounded_def)
    have "\<not> justified_at (exec_src_hist (dwe_core t')) x"
      using nj bound by (simp add: zs justified_at_append_stable)
    moreover have "x \<in> set (dwe_emitted t')"
      using x_in ys by simp
    ultimately show "premature t' \<or> duplicate t'"
      by (auto simp: premature_def)
  next
    assume "duplicate t"
    then show "premature t' \<or> duplicate t'"
      by (auto simp: duplicate_def ys)
  qed
qed

theorem effect_unsafe_monotone_reconcile:
  assumes inv: "stamps_bounded t"
      and unsafe: "effect_unsafe t"
      and rec: "emitting_reconcile m t f t'"
  shows "effect_unsafe t'"
proof -
  obtain ys where ys: "dwe_emitted t' = dwe_emitted t @ ys"
    using reconcile_extends_ledger_not_enqueued(3)[OF rec] by blast
  have src: "exec_src_hist (dwe_core t') = exec_src_hist (dwe_core t)"
    by (rule emitting_reconcile_src_hist[OF rec])
  from unsafe show ?thesis
    unfolding effect_unsafe_def
  proof
    assume "premature t"
    then show "premature t' \<or> duplicate t'"
      using ys src by (auto simp: premature_def)
  next
    assume "duplicate t"
    then show "premature t' \<or> duplicate t'"
      by (auto simp: duplicate_def ys)
  qed
qed

corollary reachable_effect_unsafe_monotone:
  assumes "dwe_reachable b K fin t"
      and "effect_unsafe t"
      and "dwe_step t a t' \<or> emitting_reconcile m t f t'"
  shows "effect_unsafe t'"
  using dwe_reachable_stamps_bounded[OF assms(1)] assms(2,3)
        effect_unsafe_monotone_step effect_unsafe_monotone_reconcile
  by blast

text \<open>Once unsafe, unsafe forever: along EVERY temporal continuation ---
  in particular no reconcile, however chosen, can heal the ledger.\<close>

theorem effect_unsafe_trace_persistent:
  assumes trace: "dwe_temporal_trace t acts t'"
      and inv: "stamps_bounded t"
      and unsafe: "effect_unsafe t"
  shows "effect_unsafe t'"
  using trace inv unsafe
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_temporal_refl t)
  then show ?case by blast
next
  case (dwe_temporal_label_step t a t' as t'')
  have inv': "stamps_bounded t'"
    by (rule dwe_step_stamps_bounded
        [OF dwe_temporal_label_step.hyps(1)
            dwe_temporal_label_step.prems(1)])
  have unsafe': "effect_unsafe t'"
    by (rule effect_unsafe_monotone_step
        [OF dwe_temporal_label_step.prems(1)
            dwe_temporal_label_step.prems(2)
            dwe_temporal_label_step.hyps(1)])
  show ?case by (rule dwe_temporal_label_step.IH[OF inv' unsafe'])
next
  case (dwe_temporal_reconcile_step m t f t' as t'')
  have inv': "stamps_bounded t'"
    by (rule emitting_reconcile_stamps_bounded
        [OF dwe_temporal_reconcile_step.hyps(1)
            dwe_temporal_reconcile_step.prems(1)])
  have unsafe': "effect_unsafe t'"
    by (rule effect_unsafe_monotone_reconcile
        [OF dwe_temporal_reconcile_step.prems(1)
            dwe_temporal_reconcile_step.prems(2)
            dwe_temporal_reconcile_step.hyps(1)])
  show ?case by (rule dwe_temporal_reconcile_step.IH[OF inv' unsafe'])
qed

section \<open>Gate I(d): the reconcile's core action is the landed relay reconcile\<close>

lemma emitting_reconcile_core_relay:
  assumes "emitting_reconcile m t f t'"
  shows "relay_bounded_replay_reconcile (dwe_core t) f (dwe_core t')"
  using assms
  by (auto simp: emitting_reconcile_def relay_bounded_replay_reconcile_def)

theorem emitting_reconcile_effective:
  assumes "emitting_reconcile m t f t'"
  shows "recovery_effectively_redelivers_source_history_at
           (dwe_core t) f (dwe_core t')"
  by (rule relay_bounded_replay_reconcile_effective
      [OF emitting_reconcile_core_relay[OF assms]])

corollary emitting_reconcile_heals:
  assumes "emitting_reconcile m t f t'"
  shows "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k"
  by (rule recovery_effective_redelivery_no_mismatch
      [OF emitting_reconcile_effective[OF assms]])

end
