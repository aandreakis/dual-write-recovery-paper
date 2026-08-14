(*  Title:       Dual_Write_Effect_Cyclic.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    The OPERATIONAL (cyclic) effect machine of tier 2 --- the promoted
    primary (owner decision D5 at checkpoint C1, evidence-backed by the S1
    kill gate): the same wrapper shape as the terminal machine --- a durable
    core plus an append-only emission ledger --- extended with a
    wrapper-level EPOCH counter and an explicit Recovered-to-Running Resume
    rule that increments it.  Every emission is stamped with
    (|exec_src_hist|, epoch) at fire time.  The scoped emitting re-drive
    reconcile (core part literally relay_bounded_replay_reconcile) is
    unchanged from the terminal machine.  (The record-extension form and
    the wholesale down_hist := src_hist reconcile of the original Design A
    are deliberately NOT used, per the pinned phase-2 spec.)

    The Resume cycle is what makes the operational recovery-information
    dilemma and multi-crash duplicate amplification expressible; its priced
    cost is the machine-checked SIMULATION SEAM: a Resume step corresponds
    to NO dw_exec_step of the landed core (resume_breaks_core_simulation),
    which is exactly why the landed tier-1 facts are re-scoped per epoch on
    this machine.  The epoch-factorization primitives that re-scoping
    builds on (dwe_trace_epoch_mono, dwe_trace_no_resume_epoch_const) are
    proved here.

    Gates carried by this theory: I (infra), G1 duplicate separation, G2
    crash->heal->re-emit bridge, G3 non-vacuity pair, G4 four corners, plus
    the cyclic-specific facts the terminal machine cannot express: a
    reachable post-recovery Running state (epoch 1) and multi-crash
    duplicate AMPLIFICATION (payload count 3) across two crash/reconcile
    cycles.

    Ported from the phase-2 verified scratch source (p2 Effect_Fallback.thy,
    the machine the S1 kill gate proved the dilemma on) with statements
    unchanged; the scratch-side oracle gates certify each landed slice
    separately.
*)

theory Dual_Write_Effect_Cyclic
  imports "Dual_Write_Core.Dual_Write_Relay"
begin

section \<open>The emission ledger: stamped, epoch-tagged, append-only\<close>

text \<open>
  An emission is one externally visible publish: (stamp, epoch, coord, event).
  The STAMP is the length of the committed durable source prefix at fire
  time; the EPOCH is the number of Resume transitions taken before the
  emission fired.  The stamp makes the fire-time justification check
  state-readable (T1 anti-circularity: justification is against the
  committed prefix AT EMISSION TIME, never the final image); the epoch
  tags which crash/recover/resume generation fired the effect.
\<close>

type_synonym ('k, 'v) emission =
  "nat \<times> nat \<times> src_coord \<times> ('k, 'v) source_event"

definition e_stamp :: "('k, 'v) emission \<Rightarrow> nat" where
  "e_stamp x = fst x"

definition e_epoch :: "('k, 'v) emission \<Rightarrow> nat" where
  "e_epoch x = fst (snd x)"

definition e_payload :: "('k, 'v) emission \<Rightarrow> src_coord \<times> ('k, 'v) source_event" where
  "e_payload x = snd (snd x)"

lemma e_stamp_tuple [simp]: "e_stamp (n, ep, c, e) = n"
  by (simp add: e_stamp_def)

lemma e_epoch_tuple [simp]: "e_epoch (n, ep, c, e) = ep"
  by (simp add: e_epoch_def)

lemma e_payload_tuple [simp]: "e_payload (n, ep, c, e) = (c, e)"
  by (simp add: e_payload_def)

text \<open>
  Fire-time justification: the emission's payload lies in the stamped
  committed durable source prefix.  Because @{const exec_src_hist} is
  append-only under every rule of the machine below, this check is stable:
  it never changes value after the emission fires (proved as
  @{text justified_at_append_stable} + the stamps-bounded invariant).
\<close>

definition justified_at
  :: "('k, 'v) src_history \<Rightarrow> ('k, 'v) emission \<Rightarrow> bool"
where
  "justified_at S x \<longleftrightarrow>
     e_stamp x \<le> length S \<and> e_payload x \<in> set (take (e_stamp x) S)"

lemma justified_at_append_stable:
  assumes "e_stamp x \<le> length S"
  shows "justified_at (S @ ext) x \<longleftrightarrow> justified_at S x"
proof -
  have take_eq: "take (e_stamp x) (S @ ext) = take (e_stamp x) S"
    using assms by simp
  show ?thesis
    using assms by (simp add: justified_at_def take_eq)
qed

text \<open>
  NAMED PREMISES (prose, not theorems --- per the pinned spec):

  \<^item> @{text authority_effect_blind}: the source authority's schema stores
    BUSINESS FACTS (latest committed value per key, via @{const Src} /
    @{const latest_src_event}), never emission-attempt counters.  This is
    why emission multiplicity is image-invisible and why the effect
    verdict below can escape the image wall.  (T6: if the source logged
    attempt counts, duplicates would be image-visible.)

  \<^item> @{text strictly_ascending_source}: real WALs have strictly increasing
    coordinates, so payload-level dedup is exact.  In-model, WF-H1 uses
    @{text "\<le>"}, so equal-coordinate re-commits are legal and a payload
    duplicate can alias a legitimate re-commit; the gates below only use
    witnesses with distinct coordinates, but any future effect-safety
    characterization needs this premise named.  Not consumed here.
\<close>


section \<open>The fallback machine: wrapper + emission ledger + epoch + Resume\<close>

record ('k, 'v) dwe_state =
  dwe_core    :: "('k, 'v) dw_exec_state"
  dwe_emitted :: "('k, 'v) emission list"
  dwe_epoch   :: nat

text \<open>
  The two-store boundary, unchanged from the terminal machine.
  @{const dwe_core} is the DURABLE STORE side: everything a recovery
  procedure can rewrite in place --- the landed heal theorems live there.
  @{const dwe_emitted} is the EXTERNAL WORLD's record of received effects:
  messages already published to consumers outside the system's write
  authority (webhooks fired, emails sent, downstream systems notified).
  The world does not roll back: no rule of this machine --- Resume
  included --- removes a ledger entry, and no landed core field can see
  the ledger.  @{const dwe_epoch} is wrapper state as well: a persisted
  recovery-generation counter, readable by the machine (every emission
  carries it) but invisible to the landed core.  Everything the effect
  tier proves is a consequence of placing the model boundary exactly at
  this line.
\<close>

definition dwe_init
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'k set \<Rightarrow> frontier \<Rightarrow> ('k, 'v) dwe_state"
where
  "dwe_init b K fin =
     \<lparr> dwe_core = initial_exec_state b K fin,
       dwe_emitted = [],
       dwe_epoch = 0 \<rparr>"

text \<open>
  Label steps: every non-publish label lifts unchanged (T3 answer: the
  ledger is written ONLY by externally visible publishes and by the
  re-drive reconcile below --- it is not a passive copy of any core field).
  A @{const DoDownstream} publish appends one emission stamped with the
  length of the committed source prefix and the current epoch.
\<close>

inductive dwe_step
  :: "('k, 'v) dwe_state \<Rightarrow> ('k, 'v) dw_exec_label \<Rightarrow> ('k, 'v) dwe_state \<Rightarrow> bool"
where
  lift_nonpub:
    "dw_exec_step (dwe_core t) a c' \<Longrightarrow>
     \<forall>c e. a \<noteq> DoDownstream c e \<Longrightarrow>
     dwe_step t a (t\<lparr>dwe_core := c'\<rparr>)"
| publish_emit:
    "dw_exec_step (dwe_core t) (DoDownstream c e) c' \<Longrightarrow>
     dwe_step t (DoDownstream c e)
       (t\<lparr>dwe_core := c',
          dwe_emitted := dwe_emitted t
            @ [(length (exec_src_hist (dwe_core t)), dwe_epoch t, c, e)]\<rparr>)"

lemma dwe_lift_nonpubI:
  assumes "dw_exec_step (dwe_core t) a c'"
      and "\<forall>c e. a \<noteq> DoDownstream c e"
      and "t' = t\<lparr>dwe_core := c'\<rparr>"
  shows "dwe_step t a t'"
  unfolding assms(3) by (rule dwe_step.lift_nonpub[OF assms(1) assms(2)])

lemma dwe_publish_emitI:
  assumes "dw_exec_step (dwe_core t) (DoDownstream c e) c'"
      and "t' = t\<lparr>dwe_core := c',
                 dwe_emitted := dwe_emitted t
                   @ [(length (exec_src_hist (dwe_core t)), dwe_epoch t, c, e)]\<rparr>"
  shows "dwe_step t (DoDownstream c e) t'"
  unfolding assms(2) by (rule dwe_step.publish_emit[OF assms(1)])

text \<open>
  The emitting re-drive reconcile: the core part is literally
  @{const relay_bounded_replay_reconcile} (scoped, frontier-bounded
  replay); the ledger part appends the re-driven suffix from checkpoint
  @{term m} (the persisted consumer cursor: entries before @{term m} are
  known-delivered and not re-fired; @{term "m = 0"} is the cold cursor
  that re-fires everything).  Emissions stamp with the CURRENT epoch;
  the reconcile itself does not change the epoch.

  @{term m} is a rule parameter (a fact about the crashed state's durable
  checkpoint), not an adversary's oracle: a crashed consumer whose cursor
  was persisted BEFORE its last delivery re-fires that delivery --- the
  at-least-once window IS a stale cursor.

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
   \<and> t' = t\<lparr>dwe_core := (dwe_core t)
              \<lparr>exec_down_hist :=
                 replay_down_hist (exec_src_hist (dwe_core t))
                   (exec_scope (dwe_core t)) f,
               exec_pending := {},
               exec_status := Recovered\<rparr>,
            dwe_emitted := dwe_emitted t
              @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                               dwe_epoch t, c, e))
                  (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                             (exec_scope (dwe_core t)) f))\<rparr>"

text \<open>
  THE FALLBACK'S CYCLE: an explicit Resume rule.  A Recovered machine may
  return to Running, opening the next epoch.  This is the rule the landed
  terminal machine does not have (Recovered admits no DoDownstream /
  DoSource, @{thm [source] recovered_cannot_do_downstream}), and it is what
  makes multi-crash amplification expressible --- at the priced cost that
  the landed tier-1 "reachable running frontier" family no longer
  transfers verbatim (see the simulation-seam lemmas below).
\<close>

definition dwe_resume :: "('k, 'v) dwe_state \<Rightarrow> ('k, 'v) dwe_state \<Rightarrow> bool" where
  "dwe_resume t t' \<longleftrightarrow>
     exec_status (dwe_core t) = Recovered
   \<and> t' = t\<lparr>dwe_core := (dwe_core t)\<lparr>exec_status := Running\<rparr>,
            dwe_epoch := Suc (dwe_epoch t)\<rparr>"

section \<open>Temporal traces and reachability\<close>

datatype ('k, 'v) dwe_action =
    DWE_Label "('k, 'v) dw_exec_label"
  | DWE_Reconcile nat frontier
  | DWE_Resume

inductive dwe_temporal_trace
  :: "('k, 'v) dwe_state \<Rightarrow> ('k, 'v) dwe_action list \<Rightarrow> ('k, 'v) dwe_state \<Rightarrow> bool"
where
  dwe_refl:
    "dwe_temporal_trace t [] t"
| dwe_label_step:
    "\<lbrakk>wellformed_exec_state (dwe_core t);
      exec_label_preserves_history_wf (dwe_core t) a;
      dwe_step t a t';
      dwe_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwe_temporal_trace t (DWE_Label a # as) t''"
| dwe_reconcile_step:
    "\<lbrakk>emitting_reconcile m t f t';
      dwe_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwe_temporal_trace t (DWE_Reconcile m f # as) t''"
| dwe_resume_step:
    "\<lbrakk>dwe_resume t t';
      dwe_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwe_temporal_trace t (DWE_Resume # as) t''"

lemma dwe_temporal_trace_append:
  assumes "dwe_temporal_trace s as s'"
      and "dwe_temporal_trace s' bs s''"
  shows "dwe_temporal_trace s (as @ bs) s''"
  using assms
proof (induction arbitrary: bs s'' rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  then show ?case by simp
next
  case (dwe_label_step t a t' as t'')
  then show ?case
    by (auto intro: dwe_temporal_trace.dwe_label_step)
next
  case (dwe_reconcile_step m t f t' as t'')
  then show ?case
    by (auto intro: dwe_temporal_trace.dwe_reconcile_step)
next
  case (dwe_resume_step t t' as t'')
  then show ?case
    by (auto intro: dwe_temporal_trace.dwe_resume_step)
qed

text \<open>Reachability, fixed at the witness instantiation of the pinned spec:
  @{typ "'k"} = @{typ "'v"} = @{typ nat}, empty base, scope @{term "{0, 1}"},
  finish frontier @{const ec2}.\<close>

definition dwe_reachable :: "(nat, nat) dwe_state \<Rightarrow> bool" where
  "dwe_reachable t \<longleftrightarrow>
     (\<exists>xs. dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2) xs t)"

lemma dwe_reachable_init: "dwe_reachable (dwe_init Map.empty {0, 1} ec2)"
  unfolding dwe_reachable_def
  by (intro exI[of _ "[]"] dwe_temporal_trace.dwe_refl)

lemma dwe_reachable_label_ext:
  assumes "dwe_reachable t"
      and "wellformed_exec_state (dwe_core t)"
      and "exec_label_preserves_history_wf (dwe_core t) a"
      and "dwe_step t a t'"
  shows "dwe_reachable t'"
proof -
  obtain xs where xs: "dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2) xs t"
    using assms(1) unfolding dwe_reachable_def by blast
  have one: "dwe_temporal_trace t [DWE_Label a] t'"
    by (rule dwe_temporal_trace.dwe_label_step[OF assms(2) assms(3) assms(4)
          dwe_temporal_trace.dwe_refl])
  show ?thesis
    unfolding dwe_reachable_def
    using dwe_temporal_trace_append[OF xs one] by blast
qed

lemma dwe_reachable_reconcile_ext:
  assumes "dwe_reachable t"
      and "emitting_reconcile m t f t'"
  shows "dwe_reachable t'"
proof -
  obtain xs where xs: "dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2) xs t"
    using assms(1) unfolding dwe_reachable_def by blast
  have one: "dwe_temporal_trace t [DWE_Reconcile m f] t'"
    by (rule dwe_temporal_trace.dwe_reconcile_step[OF assms(2)
          dwe_temporal_trace.dwe_refl])
  show ?thesis
    unfolding dwe_reachable_def
    using dwe_temporal_trace_append[OF xs one] by blast
qed

lemma dwe_reachable_resume_ext:
  assumes "dwe_reachable t"
      and "dwe_resume t t'"
  shows "dwe_reachable t'"
proof -
  obtain xs where xs: "dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2) xs t"
    using assms(1) unfolding dwe_reachable_def by blast
  have one: "dwe_temporal_trace t [DWE_Resume] t'"
    by (rule dwe_temporal_trace.dwe_resume_step[OF assms(2)
          dwe_temporal_trace.dwe_refl])
  show ?thesis
    unfolding dwe_reachable_def
    using dwe_temporal_trace_append[OF xs one] by blast
qed


section \<open>Hazards and the effect verdict\<close>

definition premature :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "premature t \<longleftrightarrow>
     (\<exists>x \<in> set (dwe_emitted t).
        \<not> justified_at (exec_src_hist (dwe_core t)) x)"

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
  SKIP ASYMMETRY (a disclosed, disowned liveness axis) --- unchanged from
  the terminal machine.  @{const effect_unsafe} is a SAFETY predicate over
  what WAS emitted: an emission fired too early (@{const premature}) or
  fired twice (@{const duplicate}).  It deliberately cannot see what was
  never emitted.  A reconcile whose cursor @{term m} lies at or beyond the
  length of its re-drive suffix emits nothing, so an over-advanced cursor
  silently SKIPS deliveries and the resulting state is effect-safe.
  Delivery completeness is a liveness question this predicate disowns ---
  the exact reason an emitted-count characterization of effect-safety is
  false for this machine, and a boundary any later characterization built
  on @{const effect_unsafe} must account for separately.
\<close>

text \<open>Scoped-image predicate for the corner statements (status-blind).\<close>

definition P_img :: "('k, 'v) dwe_state \<Rightarrow> frontier \<Rightarrow> bool" where
  "P_img t f \<longleftrightarrow>
     (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t) f) f k)"

text \<open>phantom is taxonomy-only (non-monotone); it absorbs into premature.\<close>

lemma phantom_imp_premature:
  assumes "phantom t"
  shows "premature t"
proof -
  from assms obtain x where x: "x \<in> set (dwe_emitted t)"
      and notin: "e_payload x \<notin> set (exec_src_hist (dwe_core t))"
    unfolding phantom_def by blast
  have "\<not> justified_at (exec_src_hist (dwe_core t)) x"
  proof
    assume "justified_at (exec_src_hist (dwe_core t)) x"
    then have "e_payload x \<in> set (take (e_stamp x) (exec_src_hist (dwe_core t)))"
      by (simp add: justified_at_def)
    then have "e_payload x \<in> set (exec_src_hist (dwe_core t))"
      by (rule in_set_takeD)
    with notin show False by simp
  qed
  with x show ?thesis unfolding premature_def by blast
qed


section \<open>Gate I(a): label steps project to the landed core\<close>

lemma dwe_step_core:
  assumes "dwe_step t a t'"
  shows "dw_exec_step (dwe_core t) a (dwe_core t')"
  using assms by (induction rule: dwe_step.induct) simp_all

lemma dwe_step_emitted_ext:
  assumes "dwe_step t a t'"
  shows "\<exists>es. dwe_emitted t' = dwe_emitted t @ es"
  using assms by (induction rule: dwe_step.induct) auto

lemma dwe_step_epoch_const:
  assumes "dwe_step t a t'"
  shows "dwe_epoch t' = dwe_epoch t"
  using assms by (induction rule: dwe_step.induct) simp_all

lemma dw_exec_step_src_ext:
  assumes "dw_exec_step s a s'"
  shows "\<exists>ext. exec_src_hist s' = exec_src_hist s @ ext"
  using assms
proof (induction rule: dw_exec_step.induct)
  case (do_source s c e)
  then show ?case by (intro exI[of _ "[(c, e)]"]) simp
next
  case (enqueue_downstream s c e)
  then show ?case by (intro exI[of _ "[]"]) simp
next
  case (do_downstream s c e)
  then show ?case by (intro exI[of _ "[]"]) simp
next
  case (ack s c e)
  then show ?case by (intro exI[of _ "[]"]) simp
next
  case (crash s c)
  then show ?case by (intro exI[of _ "[]"]) simp
next
  case (recover s c)
  then show ?case by (intro exI[of _ "[]"]) simp
next
  case (observe s f)
  then show ?case by (intro exI[of _ "[]"]) simp
qed

lemma dw_exec_step_src_len:
  assumes "dw_exec_step s a s'"
  shows "length (exec_src_hist s) \<le> length (exec_src_hist s')"
  using dw_exec_step_src_ext[OF assms] by auto


section \<open>Gate I(d): the emitting reconcile IS the landed relay re-drive\<close>

lemma emitting_reconcile_core:
  assumes "emitting_reconcile m t f t'"
  shows "relay_bounded_replay_reconcile (dwe_core t) f (dwe_core t')"
  using assms
  by (simp add: emitting_reconcile_def relay_bounded_replay_reconcile_def)

theorem emitting_reconcile_effective:
  assumes "emitting_reconcile m t f t'"
  shows "recovery_effectively_redelivers_source_history_at
           (dwe_core t) f (dwe_core t')"
  by (rule relay_bounded_replay_reconcile_effective[OF emitting_reconcile_core[OF assms]])

corollary emitting_reconcile_heals:
  assumes "emitting_reconcile m t f t'"
  shows "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t') f) f k"
  by (rule recovery_effective_redelivery_no_mismatch[OF emitting_reconcile_effective[OF assms]])

lemma emitting_reconcile_src_same:
  assumes "emitting_reconcile m t f t'"
  shows "exec_src_hist (dwe_core t') = exec_src_hist (dwe_core t)"
  using assms by (simp add: emitting_reconcile_def)

lemma emitting_reconcile_emitted_ext:
  assumes "emitting_reconcile m t f t'"
  shows "\<exists>es. dwe_emitted t' = dwe_emitted t @ es"
  using assms by (auto simp: emitting_reconcile_def)

lemma emitting_reconcile_epoch_const:
  assumes "emitting_reconcile m t f t'"
  shows "dwe_epoch t' = dwe_epoch t"
  using assms by (simp add: emitting_reconcile_def)


section \<open>The fallback's simulation seam (the priced tier-1 cost)\<close>

lemma dwe_resume_core:
  assumes "dwe_resume t t'"
  shows "dwe_core t' = (dwe_core t)\<lparr>exec_status := Running\<rparr>"
  using assms by (simp add: dwe_resume_def)

lemma dwe_resume_epoch_Suc:
  assumes "dwe_resume t t'"
  shows "dwe_epoch t' = Suc (dwe_epoch t)"
  using assms by (simp add: dwe_resume_def)

lemma dwe_resume_emitted_same:
  assumes "dwe_resume t t'"
  shows "dwe_emitted t' = dwe_emitted t"
  using assms by (simp add: dwe_resume_def)

lemma dwe_resume_src_same:
  assumes "dwe_resume t t'"
  shows "exec_src_hist (dwe_core t') = exec_src_hist (dwe_core t)"
  using assms by (simp add: dwe_resume_def)

lemma recovered_stays_recovered:
  assumes "dw_exec_step s a s'"
      and "exec_status s = Recovered"
  shows "exec_status s' = Recovered"
  using assms by (induction rule: dw_exec_step.induct) simp_all

text \<open>
  THE SEAM, machine-checked: a Resume transition is simulated by NO label
  step of the landed core machine.  This is the precise reason the landed
  "reachable running frontier" theorem family (crash-closure, partition,
  converse, tightness, the completeness axes) does not transfer verbatim
  to this architecture and must be re-landed per-epoch --- the +2-4 week
  cost the pinned spec prices for the fallback.
\<close>

theorem resume_breaks_core_simulation:
  assumes "dwe_resume t t'"
  shows "\<not> (\<exists>a. dw_exec_step (dwe_core t) a (dwe_core t'))"
proof
  assume "\<exists>a. dw_exec_step (dwe_core t) a (dwe_core t')"
  then obtain a where step: "dw_exec_step (dwe_core t) a (dwe_core t')" by blast
  have rec: "exec_status (dwe_core t) = Recovered"
    using assms by (simp add: dwe_resume_def)
  have "exec_status (dwe_core t') = Recovered"
    by (rule recovered_stays_recovered[OF step rec])
  moreover have "exec_status (dwe_core t') = Running"
    using dwe_resume_core[OF assms] by simp
  ultimately show False by simp
qed

text \<open>Epoch bookkeeping: the segment-factorization primitives.  Epochs are
  constant across label and reconcile steps, strictly increase across
  Resume, hence are monotone along traces and constant on Resume-free
  segments --- the interface the per-epoch re-landing would consume.\<close>

lemma dwe_trace_epoch_mono:
  assumes "dwe_temporal_trace t xs t'"
  shows "dwe_epoch t \<le> dwe_epoch t'"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  then show ?case by simp
next
  case (dwe_label_step t a t' as t'')
  then show ?case using dwe_step_epoch_const by fastforce
next
  case (dwe_reconcile_step m t f t' as t'')
  then show ?case using emitting_reconcile_epoch_const by fastforce
next
  case (dwe_resume_step t t' as t'')
  then show ?case using dwe_resume_epoch_Suc by fastforce
qed

lemma dwe_trace_no_resume_epoch_const:
  assumes "dwe_temporal_trace t xs t'"
      and "DWE_Resume \<notin> set xs"
  shows "dwe_epoch t' = dwe_epoch t"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  then show ?case by simp
next
  case (dwe_label_step t a t' as t'')
  then show ?case using dwe_step_epoch_const by fastforce
next
  case (dwe_reconcile_step m t f t' as t'')
  then show ?case using emitting_reconcile_epoch_const by fastforce
next
  case (dwe_resume_step t t' as t'')
  then show ?case by simp
qed


section \<open>Gate I(b): the stamps-bounded invariant\<close>

definition stamps_bounded :: "('k, 'v) dwe_state \<Rightarrow> bool" where
  "stamps_bounded t \<longleftrightarrow>
     (\<forall>x \<in> set (dwe_emitted t).
        e_stamp x \<le> length (exec_src_hist (dwe_core t)))"

lemma dwe_step_new_stamps:
  assumes "dwe_step t a t'"
  shows "\<exists>es. dwe_emitted t' = dwe_emitted t @ es
            \<and> (\<forall>x \<in> set es. e_stamp x \<le> length (exec_src_hist (dwe_core t)))"
  using assms
proof (induction rule: dwe_step.induct)
  case (lift_nonpub t a c')
  show ?case by (intro exI[of _ "[]"]) simp
next
  case (publish_emit t c e c')
  show ?case
    by (intro exI[of _ "[(length (exec_src_hist (dwe_core t)), dwe_epoch t, c, e)]"])
       simp
qed

lemma dwe_step_stamps_bounded:
  assumes step: "dwe_step t a t'"
      and sb: "stamps_bounded t"
  shows "stamps_bounded t'"
proof -
  obtain es where es: "dwe_emitted t' = dwe_emitted t @ es"
      and new: "\<forall>x \<in> set es. e_stamp x \<le> length (exec_src_hist (dwe_core t))"
    using dwe_step_new_stamps[OF step] by blast
  have len: "length (exec_src_hist (dwe_core t))
               \<le> length (exec_src_hist (dwe_core t'))"
    by (rule dw_exec_step_src_len[OF dwe_step_core[OF step]])
  show ?thesis
    unfolding stamps_bounded_def
  proof
    fix x
    assume "x \<in> set (dwe_emitted t')"
    then have "x \<in> set (dwe_emitted t) \<or> x \<in> set es"
      by (simp add: es)
    then have "e_stamp x \<le> length (exec_src_hist (dwe_core t))"
      using sb new unfolding stamps_bounded_def by blast
    then show "e_stamp x \<le> length (exec_src_hist (dwe_core t'))"
      using len by (rule le_trans)
  qed
qed

lemma emitting_reconcile_stamps_bounded:
  assumes rec: "emitting_reconcile m t f t'"
      and sb: "stamps_bounded t"
  shows "stamps_bounded t'"
proof -
  have src: "exec_src_hist (dwe_core t') = exec_src_hist (dwe_core t)"
    by (rule emitting_reconcile_src_same[OF rec])
  have em: "dwe_emitted t' = dwe_emitted t
              @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)),
                               dwe_epoch t, c, e))
                  (drop m (replay_down_hist (exec_src_hist (dwe_core t))
                             (exec_scope (dwe_core t)) f))"
    using rec by (simp add: emitting_reconcile_def)
  show ?thesis
    unfolding stamps_bounded_def src em
    using sb unfolding stamps_bounded_def by fastforce
qed

lemma dwe_resume_stamps_bounded:
  assumes "dwe_resume t t'"
      and "stamps_bounded t"
  shows "stamps_bounded t'"
  using assms by (simp add: dwe_resume_def stamps_bounded_def)

lemma dwe_trace_stamps_bounded:
  assumes "dwe_temporal_trace t xs t'"
      and "stamps_bounded t"
  shows "stamps_bounded t'"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  then show ?case by simp
next
  case (dwe_label_step t a t' as t'')
  then show ?case using dwe_step_stamps_bounded by blast
next
  case (dwe_reconcile_step m t f t' as t'')
  then show ?case using emitting_reconcile_stamps_bounded by blast
next
  case (dwe_resume_step t t' as t'')
  then show ?case using dwe_resume_stamps_bounded by blast
qed

lemma dwe_init_stamps_bounded: "stamps_bounded (dwe_init b K fin)"
  by (simp add: stamps_bounded_def dwe_init_def)

theorem dwe_reachable_stamps_bounded:
  assumes "dwe_reachable t"
  shows "stamps_bounded t"
proof -
  obtain xs where "dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2) xs t"
    using assms unfolding dwe_reachable_def by blast
  from dwe_trace_stamps_bounded[OF this dwe_init_stamps_bounded]
  show ?thesis .
qed


section \<open>Gate I(c): effect\_unsafe is MONOTONE (the anti-healing negation)\<close>

text \<open>
  Once unsafe, always unsafe --- along label steps, along the emitting
  reconcile, AND along Resume.  This is the anti-healing property that the
  image verdict provably lacks (the reconcile heals every scoped mismatch,
  @{thm [source] recovery_effective_redelivery_no_mismatch}); the stamped
  ledger cannot be un-written.  Stated under the stamps-bounded invariant,
  which holds at every reachable state (I(b)); the unconditional form is
  FALSE (an over-stamped alien emission could become justified when the
  source later commits), so the invariant is load-bearing, not decorative.
\<close>

lemma premature_preserved:
  assumes sb: "stamps_bounded t"
      and pre: "premature t"
      and em: "\<exists>es. dwe_emitted t' = dwe_emitted t @ es"
      and src: "\<exists>ext. exec_src_hist (dwe_core t')
                        = exec_src_hist (dwe_core t) @ ext"
  shows "premature t'"
proof -
  from pre obtain x where x: "x \<in> set (dwe_emitted t)"
      and nj: "\<not> justified_at (exec_src_hist (dwe_core t)) x"
    unfolding premature_def by blast
  from em obtain es where es: "dwe_emitted t' = dwe_emitted t @ es" by blast
  from src obtain ext where ext: "exec_src_hist (dwe_core t')
                                    = exec_src_hist (dwe_core t) @ ext" by blast
  have bound: "e_stamp x \<le> length (exec_src_hist (dwe_core t))"
    using sb x unfolding stamps_bounded_def by blast
  have "\<not> justified_at (exec_src_hist (dwe_core t')) x"
    unfolding ext using justified_at_append_stable[OF bound] nj by simp
  moreover have "x \<in> set (dwe_emitted t')"
    using x es by simp
  ultimately show ?thesis unfolding premature_def by blast
qed

lemma duplicate_preserved:
  assumes dup: "duplicate t"
      and em: "\<exists>es. dwe_emitted t' = dwe_emitted t @ es"
  shows "duplicate t'"
proof -
  from em obtain es where es: "dwe_emitted t' = dwe_emitted t @ es" by blast
  show ?thesis
    using dup unfolding duplicate_def es by auto
qed

theorem effect_unsafe_monotone:
  assumes sb: "stamps_bounded t"
      and un: "effect_unsafe t"
      and step: "dwe_step t a t' \<or> emitting_reconcile m t f t' \<or> dwe_resume t t'"
  shows "effect_unsafe t'"
proof -
  have em: "\<exists>es. dwe_emitted t' = dwe_emitted t @ es"
    using step dwe_step_emitted_ext emitting_reconcile_emitted_ext
          dwe_resume_emitted_same
    by (metis append_Nil2)
  have src: "\<exists>ext. exec_src_hist (dwe_core t')
                     = exec_src_hist (dwe_core t) @ ext"
    using step dwe_step_core dw_exec_step_src_ext
          emitting_reconcile_src_same dwe_resume_src_same
    by (metis append_Nil2)
  from un show ?thesis
    unfolding effect_unsafe_def
    using premature_preserved[OF sb _ em src] duplicate_preserved[OF _ em]
    by blast
qed

corollary effect_unsafe_monotone_reachable:
  assumes "dwe_reachable t"
      and "effect_unsafe t"
      and "dwe_step t a t' \<or> emitting_reconcile m t f t' \<or> dwe_resume t t'"
  shows "effect_unsafe t'"
  by (rule effect_unsafe_monotone[OF dwe_reachable_stamps_bounded[OF assms(1)]
        assms(2) assms(3)])

section \<open>Witness scaffolding\<close>

text \<open>Equation-form intro rules for the landed core steps (so witness states
  can be stated as closed record literals and discharged by @{method simp}).\<close>

lemma do_sourceI:
  assumes "exec_status s = Running"
      and "s' = s\<lparr>exec_src_hist := exec_src_hist s @ [(c, e)]\<rparr>"
  shows "dw_exec_step s (DoSource c e) s'"
  unfolding assms(2) by (rule dw_exec_step.do_source[OF assms(1)])

lemma enqueue_downstreamI:
  assumes "exec_status s = Running"
      and "s' = s\<lparr>exec_enqueued := exec_enqueued s @ [(c, e)],
                 exec_pending := insert (c, e) (exec_pending s)\<rparr>"
  shows "dw_exec_step s (EnqueueDownstream c e) s'"
  unfolding assms(2) by (rule dw_exec_step.enqueue_downstream[OF assms(1)])

lemma do_downstreamI:
  assumes "exec_status s = Running"
      and "(c, e) \<in> exec_pending s"
      and "s' = s\<lparr>exec_down_hist := exec_down_hist s @ [(c, e)],
                 exec_pending := exec_pending s - {(c, e)}\<rparr>"
  shows "dw_exec_step s (DoDownstream c e) s'"
  unfolding assms(3) by (rule dw_exec_step.do_downstream[OF assms(1) assms(2)])

lemma crashI:
  assumes "exec_status s = Running"
      and "s' = s\<lparr>exec_status := Crashed c\<rparr>"
  shows "dw_exec_step s (Crash c) s'"
  unfolding assms(2) by (rule dw_exec_step.crash[OF assms(1)])

text \<open>Concrete-history wellformedness helpers.\<close>

lemma wf_hist_Nil: "wellformed_src_history []"
  by (simp add: wellformed_src_history_def)

lemma wf_hist_single:
  assumes "c \<noteq> c0"
  shows "wellformed_src_history [(c, e)]"
  using assms
  by (auto simp add: wellformed_src_history_def source_pos_order_def less_Suc_eq)

lemma wf_hist_pair:
  assumes "c \<noteq> c0" and "c' \<noteq> c0" and "src_le c c'"
  shows "wellformed_src_history [(c, e), (c', e')]"
  using assms
  by (auto simp add: wellformed_src_history_def source_pos_order_def
                     src_lt_def less_Suc_eq nth_Cons')

text \<open>The two committed business events and the state constructors.\<close>

definition e1 :: "(nat, nat) source_event" where "e1 = Insert 0 1"
definition e2 :: "(nat, nat) source_event" where "e2 = Insert 1 2"

definition mkC
  :: "(nat, nat) src_history \<Rightarrow> (nat, nat) src_history \<Rightarrow>
      (nat, nat) src_history \<Rightarrow>
      (src_coord \<times> (nat, nat) source_event) set \<Rightarrow>
      dw_run_status \<Rightarrow> (nat, nat) dw_exec_state"
where
  "mkC sh dh eh pnd st =
     \<lparr> exec_base = Map.empty,
       exec_src_hist = sh,
       exec_down_hist = dh,
       exec_enqueued = eh,
       exec_pending = pnd,
       exec_scope = {0, 1},
       exec_finish = ec2,
       exec_status = st,
       exec_acked = [] \<rparr>"

definition mkT
  :: "(nat, nat) dw_exec_state \<Rightarrow> (nat, nat) emission list \<Rightarrow> nat \<Rightarrow>
      (nat, nat) dwe_state"
where
  "mkT c em ep = \<lparr> dwe_core = c, dwe_emitted = em, dwe_epoch = ep \<rparr>"

lemma wfh_e1: "wellformed_src_history [(ec1, e1)]"
  by (rule wf_hist_single) (simp add: ec_defs)

lemma wfh_e2: "wellformed_src_history [(ec2, e2)]"
  by (rule wf_hist_single) (simp add: ec_defs)

lemma wfh_pair: "wellformed_src_history [(ec1, e1), (ec2, e2)]"
  by (rule wf_hist_pair) (simp_all add: ec_defs)

lemmas ws_defs =
  wellformed_exec_state_def exec_histories_wellformed_def
  pending_enqueued_consistent_def acked_source_consistent_def

text \<open>
  The loaded-window witness chain (G2): commit+deliver event 1, commit
  event 2 with its delivery still in flight, crash at @{const ec2}.
\<close>

definition witness_labels :: "(nat, nat) dw_exec_label list" where
  "witness_labels =
     [DoSource ec1 e1, EnqueueDownstream ec1 e1, DoDownstream ec1 e1,
      DoSource ec2 e2, EnqueueDownstream ec2 e2, Crash ec2]"

definition W0 :: "(nat, nat) dwe_state" where
  "W0 = mkT (mkC [] [] [] {} Running) [] 0"

definition W1 :: "(nat, nat) dwe_state" where
  "W1 = mkT (mkC [(ec1, e1)] [] [] {} Running) [] 0"

definition W2 :: "(nat, nat) dwe_state" where
  "W2 = mkT (mkC [(ec1, e1)] [] [(ec1, e1)] {(ec1, e1)} Running) [] 0"

definition W3 :: "(nat, nat) dwe_state" where
  "W3 = mkT (mkC [(ec1, e1)] [(ec1, e1)] [(ec1, e1)] {} Running)
            [(1, 0, ec1, e1)] 0"

definition W4 :: "(nat, nat) dwe_state" where
  "W4 = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1)] [(ec1, e1)] {} Running)
            [(1, 0, ec1, e1)] 0"

definition W5 :: "(nat, nat) dwe_state" where
  "W5 = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1)]
               [(ec1, e1), (ec2, e2)] {(ec2, e2)} Running)
            [(1, 0, ec1, e1)] 0"

definition t_mid_w :: "(nat, nat) dwe_state" where
  "t_mid_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1)]
                    [(ec1, e1), (ec2, e2)] {(ec2, e2)} (Crashed ec2))
                 [(1, 0, ec1, e1)] 0"

definition t_fin_w :: "(nat, nat) dwe_state" where
  "t_fin_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)]
                    [(ec1, e1), (ec2, e2)] {} Recovered)
                 [(1, 0, ec1, e1), (2, 0, ec1, e1), (2, 0, ec2, e2)] 0"

definition t_safe_w :: "(nat, nat) dwe_state" where
  "t_safe_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)]
                     [(ec1, e1), (ec2, e2)] {} Recovered)
                  [(1, 0, ec1, e1), (2, 0, ec2, e2)] 0"

text \<open>G1 chain: single committed+delivered event, crash at @{const ec1},
  then the same reconcile with cursor 0 vs cursor 1.\<close>

definition g1_crash_w :: "(nat, nat) dwe_state" where
  "g1_crash_w = mkT (mkC [(ec1, e1)] [(ec1, e1)] [(ec1, e1)] {} (Crashed ec1))
                    [(1, 0, ec1, e1)] 0"

definition g1_unsafe_w :: "(nat, nat) dwe_state" where
  "g1_unsafe_w = mkT (mkC [(ec1, e1)] [(ec1, e1)] [(ec1, e1)] {} Recovered)
                     [(1, 0, ec1, e1), (1, 0, ec1, e1)] 0"

definition g1_safe_w :: "(nat, nat) dwe_state" where
  "g1_safe_w = mkT (mkC [(ec1, e1)] [(ec1, e1)] [(ec1, e1)] {} Recovered)
                   [(1, 0, ec1, e1)] 0"

text \<open>G3(b) chain: publish with NO source commit at all (stamp 0).\<close>

definition b1_w :: "(nat, nat) dwe_state" where
  "b1_w = mkT (mkC [] [] [(ec1, e1)] {(ec1, e1)} Running) [] 0"

definition t_bad_w :: "(nat, nat) dwe_state" where
  "t_bad_w = mkT (mkC [] [(ec1, e1)] [(ec1, e1)] {} Running)
                 [(0, 0, ec1, e1)] 0"

text \<open>G4 fourth corner: deliver the UNCOMMITTED event 2 (source only has
  event 1), then crash --- premature emission AND scoped mismatch.\<close>

definition q2_w :: "(nat, nat) dwe_state" where
  "q2_w = mkT (mkC [(ec1, e1)] [] [(ec2, e2)] {(ec2, e2)} Running) [] 0"

definition q3_w :: "(nat, nat) dwe_state" where
  "q3_w = mkT (mkC [(ec1, e1)] [(ec2, e2)] [(ec2, e2)] {} Running)
              [(1, 0, ec2, e2)] 0"

definition t_corner4_w :: "(nat, nat) dwe_state" where
  "t_corner4_w = mkT (mkC [(ec1, e1)] [(ec2, e2)] [(ec2, e2)] {} (Crashed ec2))
                     [(1, 0, ec2, e2)] 0"

text \<open>G5 chain (fallback-specific): Resume out of @{const t_fin_w} into
  epoch 1, crash again, reconcile again with a cold cursor.\<close>

definition f_run_w :: "(nat, nat) dwe_state" where
  "f_run_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)]
                    [(ec1, e1), (ec2, e2)] {} Running)
                 [(1, 0, ec1, e1), (2, 0, ec1, e1), (2, 0, ec2, e2)] 1"

definition f_crash_w :: "(nat, nat) dwe_state" where
  "f_crash_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)]
                      [(ec1, e1), (ec2, e2)] {} (Crashed ec2))
                   [(1, 0, ec1, e1), (2, 0, ec1, e1), (2, 0, ec2, e2)] 1"

definition f_amp_w :: "(nat, nat) dwe_state" where
  "f_amp_w = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)]
                    [(ec1, e1), (ec2, e2)] {} Recovered)
                 [(1, 0, ec1, e1), (2, 0, ec1, e1), (2, 0, ec2, e2),
                  (2, 1, ec1, e1), (2, 1, ec2, e2)] 1"

lemmas state_defs =
  W0_def W1_def W2_def W3_def W4_def W5_def
  t_mid_w_def t_fin_w_def t_safe_w_def
  g1_crash_w_def g1_unsafe_w_def g1_safe_w_def
  b1_w_def t_bad_w_def
  q2_w_def q3_w_def t_corner4_w_def
  f_run_w_def f_crash_w_def f_amp_w_def
  mkT_def mkC_def

lemma W0_init: "W0 = dwe_init Map.empty {0, 1} ec2"
  by (simp add: dwe_init_def initial_exec_state_def W0_def mkT_def mkC_def)

section \<open>Wellformedness and admissibility guards along the witness chains\<close>

lemma wf_W0: "wellformed_exec_state (dwe_core W0)"
  by (simp add: W0_def mkT_def mkC_def ws_defs wf_hist_Nil)

lemma wf_W1: "wellformed_exec_state (dwe_core W1)"
  by (simp add: W1_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e1)

lemma wf_W2: "wellformed_exec_state (dwe_core W2)"
  by (simp add: W2_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e1)

lemma wf_W3: "wellformed_exec_state (dwe_core W3)"
  by (simp add: W3_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e1)

lemma wf_W4: "wellformed_exec_state (dwe_core W4)"
  by (simp add: W4_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e1 wfh_pair)

lemma wf_W5: "wellformed_exec_state (dwe_core W5)"
  by (simp add: W5_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e1 wfh_pair)

lemma wf_b1: "wellformed_exec_state (dwe_core b1_w)"
  by (simp add: b1_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e1)

lemma wf_q2: "wellformed_exec_state (dwe_core q2_w)"
  by (simp add: q2_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e1 wfh_e2)

lemma wf_q3: "wellformed_exec_state (dwe_core q3_w)"
  by (simp add: q3_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_e1 wfh_e2)

lemma wf_f_run: "wellformed_exec_state (dwe_core f_run_w)"
  by (simp add: f_run_w_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_pair)

lemma g_W0_src1: "exec_label_preserves_history_wf (dwe_core W0) (DoSource ec1 e1)"
  by (simp add: W0_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_W1_enq1: "exec_label_preserves_history_wf (dwe_core W1)
                    (EnqueueDownstream ec1 e1)"
  by (simp add: W1_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_W2_down1: "exec_label_preserves_history_wf (dwe_core W2)
                     (DoDownstream ec1 e1)"
  by (simp add: W2_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_W3_src2: "exec_label_preserves_history_wf (dwe_core W3) (DoSource ec2 e2)"
  by (simp add: W3_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_W4_enq2: "exec_label_preserves_history_wf (dwe_core W4)
                    (EnqueueDownstream ec2 e2)"
  by (simp add: W4_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_W5_crash: "exec_label_preserves_history_wf (dwe_core W5) (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma g_W3_crash: "exec_label_preserves_history_wf (dwe_core W3) (Crash ec1)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma g_W0_enq1: "exec_label_preserves_history_wf (dwe_core W0)
                    (EnqueueDownstream ec1 e1)"
  by (simp add: W0_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_b1_down1: "exec_label_preserves_history_wf (dwe_core b1_w)
                     (DoDownstream ec1 e1)"
  by (simp add: b1_w_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_W1_enq2: "exec_label_preserves_history_wf (dwe_core W1)
                    (EnqueueDownstream ec2 e2)"
  by (simp add: W1_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_q2_down2: "exec_label_preserves_history_wf (dwe_core q2_w)
                     (DoDownstream ec2 e2)"
  by (simp add: q2_w_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_q3_crash: "exec_label_preserves_history_wf (dwe_core q3_w) (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma g_f_run_crash: "exec_label_preserves_history_wf (dwe_core f_run_w) (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

section \<open>The witness steps\<close>

lemma ws1: "dwe_step W0 (DoSource ec1 e1) W1"
proof -
  have c: "dw_exec_step (dwe_core W0) (DoSource ec1 e1) (dwe_core W1)"
    by (rule do_sourceI) (simp_all add: W0_def W1_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: W0_def W1_def mkT_def)
qed

lemma ws2: "dwe_step W1 (EnqueueDownstream ec1 e1) W2"
proof -
  have c: "dw_exec_step (dwe_core W1) (EnqueueDownstream ec1 e1) (dwe_core W2)"
    by (rule enqueue_downstreamI) (simp_all add: W1_def W2_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: W1_def W2_def mkT_def)
qed

lemma ws3: "dwe_step W2 (DoDownstream ec1 e1) W3"
proof -
  have c: "dw_exec_step (dwe_core W2) (DoDownstream ec1 e1) (dwe_core W3)"
    by (rule do_downstreamI) (simp_all add: W2_def W3_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_publish_emitI[OF c])
       (simp add: W2_def W3_def mkT_def mkC_def eval_nat_numeral)
qed

lemma ws4: "dwe_step W3 (DoSource ec2 e2) W4"
proof -
  have c: "dw_exec_step (dwe_core W3) (DoSource ec2 e2) (dwe_core W4)"
    by (rule do_sourceI) (simp_all add: W3_def W4_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: W3_def W4_def mkT_def)
qed

lemma ws5: "dwe_step W4 (EnqueueDownstream ec2 e2) W5"
proof -
  have c: "dw_exec_step (dwe_core W4) (EnqueueDownstream ec2 e2) (dwe_core W5)"
    by (rule enqueue_downstreamI) (simp_all add: W4_def W5_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: W4_def W5_def mkT_def)
qed

lemma ws6: "dwe_step W5 (Crash ec2) t_mid_w"
proof -
  have c: "dw_exec_step (dwe_core W5) (Crash ec2) (dwe_core t_mid_w)"
    by (rule crashI) (simp_all add: W5_def t_mid_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: W5_def t_mid_w_def mkT_def)
qed

lemma wsg1: "dwe_step W3 (Crash ec1) g1_crash_w"
proof -
  have c: "dw_exec_step (dwe_core W3) (Crash ec1) (dwe_core g1_crash_w)"
    by (rule crashI) (simp_all add: W3_def g1_crash_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: W3_def g1_crash_w_def mkT_def)
qed

lemma wsb1: "dwe_step W0 (EnqueueDownstream ec1 e1) b1_w"
proof -
  have c: "dw_exec_step (dwe_core W0) (EnqueueDownstream ec1 e1) (dwe_core b1_w)"
    by (rule enqueue_downstreamI) (simp_all add: W0_def b1_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: W0_def b1_w_def mkT_def)
qed

lemma wsb2: "dwe_step b1_w (DoDownstream ec1 e1) t_bad_w"
proof -
  have c: "dw_exec_step (dwe_core b1_w) (DoDownstream ec1 e1) (dwe_core t_bad_w)"
    by (rule do_downstreamI) (simp_all add: b1_w_def t_bad_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_publish_emitI[OF c])
       (simp add: b1_w_def t_bad_w_def mkT_def mkC_def)
qed

lemma wsq1: "dwe_step W1 (EnqueueDownstream ec2 e2) q2_w"
proof -
  have c: "dw_exec_step (dwe_core W1) (EnqueueDownstream ec2 e2) (dwe_core q2_w)"
    by (rule enqueue_downstreamI) (simp_all add: W1_def q2_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: W1_def q2_w_def mkT_def)
qed

lemma wsq2: "dwe_step q2_w (DoDownstream ec2 e2) q3_w"
proof -
  have c: "dw_exec_step (dwe_core q2_w) (DoDownstream ec2 e2) (dwe_core q3_w)"
    by (rule do_downstreamI) (simp_all add: q2_w_def q3_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_publish_emitI[OF c])
       (simp add: q2_w_def q3_w_def mkT_def mkC_def eval_nat_numeral)
qed

lemma wsq3: "dwe_step q3_w (Crash ec2) t_corner4_w"
proof -
  have c: "dw_exec_step (dwe_core q3_w) (Crash ec2) (dwe_core t_corner4_w)"
    by (rule crashI) (simp_all add: q3_w_def t_corner4_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c])
       (simp_all add: q3_w_def t_corner4_w_def mkT_def)
qed

lemma wsf1: "dwe_step f_run_w (Crash ec2) f_crash_w"
proof -
  have c: "dw_exec_step (dwe_core f_run_w) (Crash ec2) (dwe_core f_crash_w)"
    by (rule crashI) (simp_all add: f_run_w_def f_crash_w_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c])
       (simp_all add: f_run_w_def f_crash_w_def mkT_def)
qed

section \<open>The reconcile and resume witness transitions\<close>

lemma rec_fin: "emitting_reconcile 0 t_mid_w ec2 t_fin_w"
  by (simp add: emitting_reconcile_def t_mid_w_def t_fin_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs eval_nat_numeral)

lemma rec_safe: "emitting_reconcile 1 t_mid_w ec2 t_safe_w"
  by (simp add: emitting_reconcile_def t_mid_w_def t_safe_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs eval_nat_numeral)

lemma rec_g1u: "emitting_reconcile 0 g1_crash_w ec1 g1_unsafe_w"
  by (simp add: emitting_reconcile_def g1_crash_w_def g1_unsafe_w_def
                mkT_def mkC_def replay_down_hist_def e1_def e2_def ec_defs
                eval_nat_numeral)

lemma rec_g1s: "emitting_reconcile 1 g1_crash_w ec1 g1_safe_w"
  by (simp add: emitting_reconcile_def g1_crash_w_def g1_safe_w_def
                mkT_def mkC_def replay_down_hist_def e1_def e2_def ec_defs
                eval_nat_numeral)

lemma res_f: "dwe_resume t_fin_w f_run_w"
  by (simp add: dwe_resume_def t_fin_w_def f_run_w_def mkT_def mkC_def
                eval_nat_numeral)

lemma rec_amp: "emitting_reconcile 0 f_crash_w ec2 f_amp_w"
  by (simp add: emitting_reconcile_def f_crash_w_def f_amp_w_def mkT_def mkC_def
                replay_down_hist_def e1_def e2_def ec_defs eval_nat_numeral)

section \<open>Trace assembly and reachability of the witnesses\<close>

lemma trace_to_t_mid_raw:
  "dwe_temporal_trace W0
     [DWE_Label (DoSource ec1 e1), DWE_Label (EnqueueDownstream ec1 e1),
      DWE_Label (DoDownstream ec1 e1), DWE_Label (DoSource ec2 e2),
      DWE_Label (EnqueueDownstream ec2 e2), DWE_Label (Crash ec2)]
     t_mid_w"
proof -
  have a6: "dwe_temporal_trace W5 [DWE_Label (Crash ec2)] t_mid_w"
    by (rule dwe_temporal_trace.dwe_label_step[OF wf_W5 g_W5_crash ws6
          dwe_temporal_trace.dwe_refl])
  have a5: "dwe_temporal_trace W4
              [DWE_Label (EnqueueDownstream ec2 e2), DWE_Label (Crash ec2)]
              t_mid_w"
    by (rule dwe_temporal_trace.dwe_label_step[OF wf_W4 g_W4_enq2 ws5 a6])
  have a4: "dwe_temporal_trace W3
              [DWE_Label (DoSource ec2 e2), DWE_Label (EnqueueDownstream ec2 e2),
               DWE_Label (Crash ec2)] t_mid_w"
    by (rule dwe_temporal_trace.dwe_label_step[OF wf_W3 g_W3_src2 ws4 a5])
  have a3: "dwe_temporal_trace W2
              [DWE_Label (DoDownstream ec1 e1), DWE_Label (DoSource ec2 e2),
               DWE_Label (EnqueueDownstream ec2 e2), DWE_Label (Crash ec2)]
              t_mid_w"
    by (rule dwe_temporal_trace.dwe_label_step[OF wf_W2 g_W2_down1 ws3 a4])
  have a2: "dwe_temporal_trace W1
              [DWE_Label (EnqueueDownstream ec1 e1),
               DWE_Label (DoDownstream ec1 e1), DWE_Label (DoSource ec2 e2),
               DWE_Label (EnqueueDownstream ec2 e2), DWE_Label (Crash ec2)]
              t_mid_w"
    by (rule dwe_temporal_trace.dwe_label_step[OF wf_W1 g_W1_enq1 ws2 a3])
  show ?thesis
    by (rule dwe_temporal_trace.dwe_label_step[OF wf_W0 g_W0_src1 ws1 a2])
qed

lemma trace_to_t_mid:
  "dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2)
     (map DWE_Label witness_labels) t_mid_w"
  using trace_to_t_mid_raw unfolding W0_init witness_labels_def by simp

lemma reach_W0: "dwe_reachable W0"
  unfolding W0_init by (rule dwe_reachable_init)

lemma reach_W1: "dwe_reachable W1"
  by (rule dwe_reachable_label_ext[OF reach_W0 wf_W0 g_W0_src1 ws1])

lemma reach_W2: "dwe_reachable W2"
  by (rule dwe_reachable_label_ext[OF reach_W1 wf_W1 g_W1_enq1 ws2])

lemma reach_W3: "dwe_reachable W3"
  by (rule dwe_reachable_label_ext[OF reach_W2 wf_W2 g_W2_down1 ws3])

lemma reach_W4: "dwe_reachable W4"
  by (rule dwe_reachable_label_ext[OF reach_W3 wf_W3 g_W3_src2 ws4])

lemma reach_W5: "dwe_reachable W5"
  by (rule dwe_reachable_label_ext[OF reach_W4 wf_W4 g_W4_enq2 ws5])

lemma reach_t_mid: "dwe_reachable t_mid_w"
  by (rule dwe_reachable_label_ext[OF reach_W5 wf_W5 g_W5_crash ws6])

lemma reach_t_fin: "dwe_reachable t_fin_w"
  by (rule dwe_reachable_reconcile_ext[OF reach_t_mid rec_fin])

lemma reach_t_safe: "dwe_reachable t_safe_w"
  by (rule dwe_reachable_reconcile_ext[OF reach_t_mid rec_safe])

lemma reach_g1_crash: "dwe_reachable g1_crash_w"
  by (rule dwe_reachable_label_ext[OF reach_W3 wf_W3 g_W3_crash wsg1])

lemma reach_g1_unsafe: "dwe_reachable g1_unsafe_w"
  by (rule dwe_reachable_reconcile_ext[OF reach_g1_crash rec_g1u])

lemma reach_g1_safe: "dwe_reachable g1_safe_w"
  by (rule dwe_reachable_reconcile_ext[OF reach_g1_crash rec_g1s])

lemma reach_b1: "dwe_reachable b1_w"
  by (rule dwe_reachable_label_ext[OF reach_W0 wf_W0 g_W0_enq1 wsb1])

lemma reach_t_bad: "dwe_reachable t_bad_w"
  by (rule dwe_reachable_label_ext[OF reach_b1 wf_b1 g_b1_down1 wsb2])

lemma reach_q2: "dwe_reachable q2_w"
  by (rule dwe_reachable_label_ext[OF reach_W1 wf_W1 g_W1_enq2 wsq1])

lemma reach_q3: "dwe_reachable q3_w"
  by (rule dwe_reachable_label_ext[OF reach_q2 wf_q2 g_q2_down2 wsq2])

lemma reach_t_corner4: "dwe_reachable t_corner4_w"
  by (rule dwe_reachable_label_ext[OF reach_q3 wf_q3 g_q3_crash wsq3])

lemma reach_f_run: "dwe_reachable f_run_w"
  by (rule dwe_reachable_resume_ext[OF reach_t_fin res_f])

lemma reach_f_crash: "dwe_reachable f_crash_w"
  by (rule dwe_reachable_label_ext[OF reach_f_run wf_f_run g_f_run_crash wsf1])

lemma reach_f_amp: "dwe_reachable f_amp_w"
  by (rule dwe_reachable_reconcile_ext[OF reach_f_crash rec_amp])


section \<open>Verdict evaluations on the witnesses\<close>

lemmas eval_defs =
  mismatch_at_def proto_of_exec_at_def store2_of_exec_def log_image_def
  restrict_def Src_def latest_src_event_def Let_def
  mkT_def mkC_def e1_def e2_def ec_defs

lemma t_mid_mismatch: "observable_mismatch (dwe_core t_mid_w) ec2 1"
  by (simp add: observable_mismatch_def t_mid_w_def eval_defs eval_nat_numeral)

lemma t_fin_heal:
  "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t_fin_w) ec2) ec2 k"
  by (rule emitting_reconcile_heals[OF rec_fin])

lemma t_safe_heal:
  "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t_safe_w) ec2) ec2 k"
  by (rule emitting_reconcile_heals[OF rec_safe])

lemma t_fin_count:
  "2 \<le> count_list (map e_payload (dwe_emitted t_fin_w)) (ec1, e1)"
  by (simp add: t_fin_w_def mkT_def e1_def e2_def ec_defs eval_nat_numeral)

lemma t_fin_justified:
  "\<forall>x \<in> set (dwe_emitted t_fin_w).
     justified_at (exec_src_hist (dwe_core t_fin_w)) x"
  by (simp add: t_fin_w_def mkT_def mkC_def justified_at_def
                e1_def e2_def ec_defs eval_nat_numeral)

lemma t_fin_unsafe: "effect_unsafe t_fin_w"
  by (simp add: effect_unsafe_def duplicate_def t_fin_w_def mkT_def
                e1_def e2_def ec_defs)

lemma t_safe_not_unsafe: "\<not> effect_unsafe t_safe_w"
  by (simp add: effect_unsafe_def premature_def duplicate_def justified_at_def
                t_safe_w_def mkT_def mkC_def e1_def e2_def ec_defs
                eval_nat_numeral)

lemma t_mid_not_unsafe: "\<not> effect_unsafe t_mid_w"
  by (simp add: effect_unsafe_def premature_def duplicate_def justified_at_def
                t_mid_w_def mkT_def mkC_def e1_def e2_def ec_defs
                eval_nat_numeral)

lemma g1_cores_eq: "dwe_core g1_unsafe_w = dwe_core g1_safe_w"
  by (simp add: g1_unsafe_w_def g1_safe_w_def mkT_def)

lemma g1u_unsafe: "effect_unsafe g1_unsafe_w"
  by (simp add: effect_unsafe_def duplicate_def g1_unsafe_w_def mkT_def)

lemma g1s_safe: "\<not> effect_unsafe g1_safe_w"
  by (simp add: effect_unsafe_def premature_def duplicate_def justified_at_def
                g1_safe_w_def mkT_def mkC_def e1_def ec_defs eval_nat_numeral)

lemma t_bad_emitting: "genuinely_emitting t_bad_w"
  by (simp add: genuinely_emitting_def t_bad_w_def mkT_def)

lemma t_bad_premature: "premature t_bad_w"
  by (simp add: premature_def justified_at_def t_bad_w_def mkT_def mkC_def)

lemma t_bad_phantom: "phantom t_bad_w"
  by (simp add: phantom_def t_bad_w_def mkT_def mkC_def)

lemma corner4_mismatch:
  "mismatch_at (proto_of_exec_at (dwe_core t_corner4_w) ec2) ec2 1"
  by (simp add: t_corner4_w_def eval_defs eval_nat_numeral)

lemma corner4_unsafe: "effect_unsafe t_corner4_w"
  by (simp add: effect_unsafe_def premature_def justified_at_def
                t_corner4_w_def mkT_def mkC_def e1_def e2_def ec_defs
                eval_nat_numeral)


section \<open>GATE G1: duplicate separation on the reachable machine\<close>

text \<open>
  Two REACHABLE states with LITERALLY IDENTICAL cores (hence identical
  scoped images, statuses, pendings, everything the landed development can
  see) and OPPOSITE effect verdicts.  The only difference is the persisted
  consumer cursor @{term m} of the reconcile (0 = cold cursor re-fires the
  already-emitted effect; 1 = the cursor recorded the delivery).  This is
  the machine-level negation of the image wall for the effect verdict.
\<close>

theorem dwe_duplicate_separation:
  "\<exists>t t'. dwe_reachable t \<and> dwe_reachable t'
        \<and> dwe_core t = dwe_core t'
        \<and> effect_unsafe t \<and> \<not> effect_unsafe t'"
  using reach_g1_unsafe reach_g1_safe g1_cores_eq g1u_unsafe g1s_safe
  by blast

corollary effect_unsafe_not_core_function:
  "\<not> (\<exists>g. \<forall>t. dwe_reachable t \<longrightarrow> effect_unsafe t = g (dwe_core t))"
proof
  assume "\<exists>g. \<forall>t. dwe_reachable t \<longrightarrow> effect_unsafe t = g (dwe_core t)"
  then obtain g where g: "\<forall>t. dwe_reachable t \<longrightarrow> effect_unsafe t = g (dwe_core t)"
    by blast
  have "g (dwe_core g1_unsafe_w)"
    using g reach_g1_unsafe g1u_unsafe by blast
  moreover have "\<not> g (dwe_core g1_safe_w)"
    using g reach_g1_safe g1s_safe by blast
  ultimately show False
    by (simp add: g1_cores_eq)
qed


section \<open>GATE G2: the crash-heal-re-emit bridge (kill-or-continue)\<close>

text \<open>
  The flagship conjunction, on the CYCLIC fallback machine, closed inside
  one crash segment: a genuinely loaded window (two committed events, one
  delivered), a real observable mismatch at the crash, and then THE SAME
  scoped re-drive reconcile that heals every scoped mismatch at the
  frontier fires the already-emitted effect a SECOND time --- with every
  ledger entry individually justified against the committed source prefix
  (duplication is orthogonal to justification).
\<close>

theorem crash_heal_reemit_bridge_named:
  "dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2)
     (map DWE_Label witness_labels) t_mid_w
 \<and> observable_mismatch (dwe_core t_mid_w) ec2 1
 \<and> emitting_reconcile 0 t_mid_w ec2 t_fin_w
 \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t_fin_w) ec2) ec2 k)
 \<and> 2 \<le> count_list (map e_payload (dwe_emitted t_fin_w)) (ec1, e1)
 \<and> (\<forall>x \<in> set (dwe_emitted t_fin_w).
      justified_at (exec_src_hist (dwe_core t_fin_w)) x)"
  by (intro conjI trace_to_t_mid t_mid_mismatch rec_fin t_fin_heal
        t_fin_count t_fin_justified)

theorem crash_heal_reemit_bridge:
  "\<exists>t_mid t_fin.
     dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2)
       (map DWE_Label witness_labels) t_mid
   \<and> observable_mismatch (dwe_core t_mid) ec2 1
   \<and> emitting_reconcile 0 t_mid ec2 t_fin
   \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t_fin) ec2) ec2 k)
   \<and> 2 \<le> count_list (map e_payload (dwe_emitted t_fin)) (ec1, e1)
   \<and> (\<forall>x \<in> set (dwe_emitted t_fin).
        justified_at (exec_src_hist (dwe_core t_fin)) x)"
  using crash_heal_reemit_bridge_named by blast


section \<open>GATE G3: the non-vacuity pair\<close>

text \<open>(a) From the SAME crashed state @{const t_mid_w}, the reconcile with
  the warm cursor (m = 1) is genuinely emitting (it fires the still-missing
  second effect DURING recovery), genuinely healing, and effect-safe ---
  the cursor alone separates it from G2's duplicate.\<close>

theorem effect_nonvacuity_safe:
  "emitting_reconcile 1 t_mid_w ec2 t_safe_w
 \<and> dwe_emitted t_safe_w = [(1, 0, ec1, e1), (2, 0, ec2, e2)]
 \<and> \<not> effect_unsafe t_safe_w
 \<and> genuinely_emitting t_safe_w
 \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core t_safe_w) ec2) ec2 k)
 \<and> dwe_reachable t_safe_w"
  by (intro conjI rec_safe t_safe_not_unsafe t_safe_heal reach_t_safe)
     (simp_all add: t_safe_w_def mkT_def genuinely_emitting_def)

text \<open>(b) A genuinely-emitting PREMATURE (and phantom) run: publish with no
  source commit at all --- stamp 0 against an empty committed prefix.\<close>

theorem effect_nonvacuity_premature:
  "dwe_reachable t_bad_w
 \<and> genuinely_emitting t_bad_w
 \<and> premature t_bad_w
 \<and> phantom t_bad_w
 \<and> effect_unsafe t_bad_w"
  using reach_t_bad t_bad_emitting t_bad_premature t_bad_phantom
  by (auto simp: effect_unsafe_def)


section \<open>GATE G4: four-corner independence at frontier ec2\<close>

theorem four_corner_independence:
  "P_img t_safe_w ec2 \<and> \<not> effect_unsafe t_safe_w
     \<and> genuinely_emitting t_safe_w \<and> dwe_reachable t_safe_w
 \<and> P_img t_fin_w ec2 \<and> effect_unsafe t_fin_w
     \<and> genuinely_emitting t_fin_w \<and> dwe_reachable t_fin_w
 \<and> \<not> P_img t_mid_w ec2 \<and> \<not> effect_unsafe t_mid_w
     \<and> genuinely_emitting t_mid_w \<and> dwe_reachable t_mid_w
 \<and> \<not> P_img t_corner4_w ec2 \<and> effect_unsafe t_corner4_w
     \<and> genuinely_emitting t_corner4_w \<and> dwe_reachable t_corner4_w"
proof -
  have c1: "P_img t_safe_w ec2"
    unfolding P_img_def by (rule t_safe_heal)
  have c2: "P_img t_fin_w ec2"
    unfolding P_img_def by (rule t_fin_heal)
  have c3: "\<not> P_img t_mid_w ec2"
    unfolding P_img_def
    using t_mid_mismatch by (auto simp: observable_mismatch_def)
  have c4: "\<not> P_img t_corner4_w ec2"
    unfolding P_img_def using corner4_mismatch by blast
  show ?thesis
    by (intro conjI c1 c2 c3 c4 t_safe_not_unsafe t_fin_unsafe t_mid_not_unsafe
          corner4_unsafe reach_t_safe reach_t_fin reach_t_mid reach_t_corner4)
       (simp_all add: genuinely_emitting_def t_safe_w_def t_fin_w_def
          t_mid_w_def t_corner4_w_def mkT_def)
qed


section \<open>GATE G5 (fallback-specific): the Resume cycle and amplification\<close>

text \<open>
  What the terminal primary machine CANNOT express and this fallback can:
  (i) a reachable post-recovery RUNNING state in epoch 1 that already
  carries a non-empty ledger --- the exact state family whose existence
  forces the per-epoch re-landing of the landed tier-1 "reachable running
  frontier" theorems; and (ii) multi-crash duplicate AMPLIFICATION: a
  second crash/re-drive cycle raises the payload count of the same
  committed effect to THREE, all entries justified, with ledger entries
  from two distinct epochs.  This is the retry-storm content named as the
  fallback's trigger condition (i) in the pinned spec.
\<close>

theorem post_resume_running_reachable:
  "dwe_reachable f_run_w
 \<and> exec_status (dwe_core f_run_w) = Running
 \<and> dwe_epoch f_run_w = 1
 \<and> genuinely_emitting f_run_w"
  by (intro conjI reach_f_run)
     (simp_all add: f_run_w_def mkT_def mkC_def genuinely_emitting_def)

theorem resume_cycle_amplification:
  "dwe_reachable f_amp_w
 \<and> 3 \<le> count_list (map e_payload (dwe_emitted f_amp_w)) (ec1, e1)
 \<and> (\<forall>x \<in> set (dwe_emitted f_amp_w).
      justified_at (exec_src_hist (dwe_core f_amp_w)) x)
 \<and> effect_unsafe f_amp_w
 \<and> dwe_epoch f_amp_w = 1
 \<and> (\<exists>x \<in> set (dwe_emitted f_amp_w). e_epoch x = 0)
 \<and> (\<exists>x \<in> set (dwe_emitted f_amp_w). e_epoch x = 1)"
proof -
  have count: "3 \<le> count_list (map e_payload (dwe_emitted f_amp_w)) (ec1, e1)"
    by (simp add: f_amp_w_def mkT_def e1_def e2_def ec_defs eval_nat_numeral)
  have just: "\<forall>x \<in> set (dwe_emitted f_amp_w).
                justified_at (exec_src_hist (dwe_core f_amp_w)) x"
    by (simp add: f_amp_w_def mkT_def mkC_def justified_at_def
                  e1_def e2_def ec_defs eval_nat_numeral)
  have unsafe: "effect_unsafe f_amp_w"
    by (simp add: effect_unsafe_def duplicate_def f_amp_w_def mkT_def
                  e1_def e2_def ec_defs)
  have ep0: "\<exists>x \<in> set (dwe_emitted f_amp_w). e_epoch x = 0"
    by (simp add: f_amp_w_def mkT_def)
  have ep1: "\<exists>x \<in> set (dwe_emitted f_amp_w). e_epoch x = 1"
    by (simp add: f_amp_w_def mkT_def)
  show ?thesis
    by (intro conjI reach_f_amp count just unsafe ep0 ep1)
       (simp add: f_amp_w_def mkT_def)
qed


end
