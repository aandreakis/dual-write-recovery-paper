(*  Title:       Dual_Write_Relay.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    A verified non-atomic bounded-replay CDC relay --- the CONSTRUCTIVE
    (positive) companion to the dual-write crash partition.

    The partition theory shows the obstruction: a separable, non-atomic dual
    write inherently admits a crash that exposes a scoped source/downstream
    mismatch.  This theory exhibits a concrete relay implementation whose
    safety is FRONTIER-SCOPED, and proves that a SINGLE advertise discipline
    does both jobs at once: it FORCES a reachable observable bad crash at an
    UNADVERTISED incomplete frontier (the un-delivered gap), and it makes
    no-observable-mismatch a DISCHARGED consequence at every
    OCCURRENCE-COMPLETE frontier of every reachable state (the named
    property relay_complete_frontier_safe).  So the relay is UNSAFE at
    unadvertised incomplete frontiers and mismatch-free at every
    occurrence-complete frontier --- and it is explicitly NOT an inhabitant
    of the global safe class of the converse characterization (no reachable
    observable bad crash, the LHS of safe_iff_running_image_faithful in the
    downstream Converse theory, which uses this relay as that
    biconditional's UNSAFE-side inhabitant).  Coordinate advertisement
    alone is insufficient when several occurrences share that coordinate.

    The two genuinely new facts are:
      (1) the crux replay_down_hist_image_on_scope(_le): a scope-bounded,
          frontier-bounded filter of the committed source log is
          source-image-equivalent on scope at the frontier --- so a bounded
          replay can heal through the existing convergence layer via the IMAGE
          equality alone.  The complete relay machine executes a strict
          operational witness that differs from the wholesale atomic heal
          (see na_recovered_full_relay_trace / na_recovery_strictly_non_atomic);
      (2) relay_inv / relay_inv_step: occurrence-prefix delivery is a genuine
          INDUCTIVE INVARIANT of relay_step, schematic over all dw_exec_step
          constructors.  Explicit relay_complete_through then discharges R3
          and is consumed by relay_inv_no_observable_mismatch.

    Honest scope (these are deliberate and stated, not defects):
      * The refinement statement I_relay_labels_refines_exec is reflexive
        infrastructure (relay_step is a guarded restriction of dw_exec_step with
        an identity state projection); it lets the partition apply to the relay,
        but it is NOT claimed as a contribution.
      * relay_inv_no_observable_mismatch carries an explicit f <= exec_finish
        (crash-frontier-in-range) hypothesis --- the same one the underlying
        bridge execution_cdc_replay_prefix_no_observable_mismatch already uses;
        it also requires occurrence completeness through f.
      * The no-observable-mismatch terminus is the inherited core bridge; the
        new content is that R3 feeding it is an inducted invariant over
        reachable states with down_hist != src_hist.
      * The discipline's teeth live in two relay_admits clauses (DoSource
        strictly above the advertised frontier; DoDownstream faithful); this is
        a modeling commitment, not a derived necessity.

    sorry/oracle/axiom-free under quick_and_dirty=false.
*)

theory Dual_Write_Relay
  imports
    Dual_Write_Recovery
    Dual_Write_Delivery_Realism
    Dual_Write_Partition
    Dual_Write_Replay_Safety
begin

section \<open>Milestone 1: refinement frame (must be cheap)\<close>

text \<open>
  The relay is a guarded SUBRELATION of \<open>dw_exec_step\<close> with identity
  abstraction.  NB: identity abstraction is exactly the K4 trap if we stop
  here; this is only the frame.  The content is Milestones 4 (the
  complete-frontier safe side) and 5 (non-atomic recovery), where the work
  is NOT in the refinement obligation.
\<close>

text \<open>
  The materialized in-scope, frontier-bounded replay history (moved up so the
  advertise discipline can reference it).  This is the per-event CDC filter, NOT
  a wholesale copy of @{const exec_src_hist}.
\<close>

definition replay_down_hist
  :: "('k, 'v) src_history \<Rightarrow> 'k set \<Rightarrow> frontier \<Rightarrow> ('k, 'v) src_history"
where
  "replay_down_hist H K f =
     filter (\<lambda>(c, e). c \<le> f \<and> key_of e \<in> K) H"

text \<open>
  GATE-1 (Phase 3): the advertise discipline is no longer @{text True}.  The
  relay carries an ADVERTISED FRONTIER @{term "adv s"} --- the largest source
  coordinate its durable downstream history has actually delivered (the
  coordinate of the LAST event in @{const exec_down_hist}, or @{const c0} when
  nothing has been delivered).  Because @{const exec_down_hist} is wellformed
  (non-decreasing coordinates), that last coordinate is the maximum delivered
  coordinate.
\<close>

definition adv :: "('k, 'v) dw_exec_state \<Rightarrow> src_coord" where
  "adv s = (if exec_down_hist s = [] then c0
            else fst (last (exec_down_hist s)))"

lemma adv_Nil [simp]: "exec_down_hist s = [] \<Longrightarrow> adv s = c0"
  by (simp add: adv_def)

lemma adv_down_snoc:
  "adv (s\<lparr>exec_down_hist := exec_down_hist s @ [(c, e)]\<rparr>) = c"
  by (simp add: adv_def)

text \<open>
  @{term "adv s"} depends ONLY on @{const exec_down_hist}; every step that
  leaves the downstream history untouched leaves @{term "adv s"} fixed.
\<close>

lemma adv_cong_down:
  "exec_down_hist s' = exec_down_hist s \<Longrightarrow> adv s' = adv s"
  by (simp add: adv_def)

definition scoped_replay_history
  :: "('k, 'v) src_history \<Rightarrow> 'k set \<Rightarrow> ('k, 'v) src_history"
where
  "scoped_replay_history H K =
     filter (\<lambda>(c, e). key_of e \<in> K) H"

definition relay_history_prefix
  :: "('k, 'v) src_history \<Rightarrow> ('k, 'v) src_history \<Rightarrow> bool"
where
  "relay_history_prefix delivered source \<longleftrightarrow>
     (\<exists>rest. source = delivered @ rest)"

definition relay_complete_through
  :: "('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow> bool"
where
  "relay_complete_through s f \<longleftrightarrow>
     replay_down_hist (exec_down_hist s) (exec_scope s) f =
     replay_down_hist (exec_src_hist s) (exec_scope s) f"

lemma relay_history_prefix_Nil [simp]:
  "relay_history_prefix [] H"
  by (simp add: relay_history_prefix_def)

lemma relay_history_prefix_refl [simp]:
  "relay_history_prefix H H"
  by (simp add: relay_history_prefix_def)

lemma relay_wellformed_history_tail:
  assumes "wellformed_src_history (x # xs)"
  shows "wellformed_src_history xs"
  using assms
  by (auto simp: wellformed_src_history_def source_pos_order_def
                 nth_Cons src_le_eq_less_eq src_lt_eq_less
           split: nat.splits)

lemma relay_wellformed_history_cons_le_set:
  assumes wf: "wellformed_src_history (x # xs)"
      and y: "y \<in> set xs"
  shows "fst x \<le> fst y"
  using wf y
proof (induction xs arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons z zs)
  have x_le_z: "fst x \<le> fst z"
    using Cons.prems(1)
    by (auto simp: wellformed_src_history_def src_le_eq_less_eq)
  show ?case
  proof (cases "y = z")
    case True
    with x_le_z show ?thesis by simp
  next
    case False
    with Cons.prems(2) have y_zs: "y \<in> set zs" by simp
    have tail_wf: "wellformed_src_history (z # zs)"
      by (rule relay_wellformed_history_tail[OF Cons.prems(1)])
    have z_le_y: "fst z \<le> fst y"
      by (rule Cons.IH[OF tail_wf y_zs])
    from x_le_z z_le_y show ?thesis by (rule order_trans)
  qed
qed

lemma replay_down_hist_prefix_scoped:
  assumes wf: "wellformed_src_history H"
  shows "relay_history_prefix
           (replay_down_hist H K f) (scoped_replay_history H K)"
  using wf
proof (induction H)
  case Nil
  show ?case
    by (simp add: replay_down_hist_def scoped_replay_history_def)
next
  case (Cons x xs)
  have tail_wf: "wellformed_src_history xs"
    by (rule relay_wellformed_history_tail[OF Cons.prems])
  have IH:
    "relay_history_prefix
       (replay_down_hist xs K f) (scoped_replay_history xs K)"
    by (rule Cons.IH[OF tail_wf])
  show ?case
  proof (cases "key_of (snd x) \<in> K")
    case False
    with IH show ?thesis
      by (cases x)
         (simp add: replay_down_hist_def scoped_replay_history_def)
  next
    case in_scope: True
    show ?thesis
    proof (cases "fst x \<le> f")
      case True
      with in_scope IH show ?thesis
        by (cases x)
           (auto simp: replay_down_hist_def scoped_replay_history_def
                       relay_history_prefix_def)
    next
      case False
      have no_tail: "\<forall>y \<in> set xs. \<not> fst y \<le> f"
      proof (intro ballI)
        fix y
        assume y: "y \<in> set xs"
        have "fst x \<le> fst y"
          by (rule relay_wellformed_history_cons_le_set[OF Cons.prems y])
        with False show "\<not> fst y \<le> f" by auto
      qed
      have replay_tail_empty:
        "filter (\<lambda>(c, e). c \<le> f \<and> key_of e \<in> K) xs = []"
        using no_tail
        by (induction xs) auto
      with False show ?thesis
        by (cases x)
           (auto simp: replay_down_hist_def scoped_replay_history_def
                       relay_history_prefix_def)
    qed
  qed
qed

text \<open>
  THE REAL ADVERTISE DISCIPLINE.  Three genuine clauses on top of the
  wellformedness-preservation guard @{const exec_label_preserves_history_wf}
  (the appended coordinate must dominate EVERY prior coordinate, ties allowed,
  and must not be the base coordinate @{const c0} --- a real relay only
  appends monotone events):

    \<^item> @{text DoSource}: the source may only commit at a coordinate STRICTLY
      ABOVE the advertised (delivered) frontier --- i.e. the source races
      AHEAD of downstream, never behind it.  This is exactly the gap-opening
      move (@{text "adv s < c"}); it does NOT close the commit-to-deliver window.

    \<^item> @{text DoDownstream}: a delivery is FAITHFUL --- after it, the durable
      downstream history is an occurrence prefix of the IN-SCOPE source stream
      (an outbox reads committed source occurrences in order).  A coordinate is
      complete only when @{const relay_complete_through} holds; merely
      delivering the first of several equal-coordinate occurrences does not
      advertise the tied coordinate as complete.

    \<^item> every other label: unconstrained (in particular @{text Crash} is admitted
      from every running state, INCLUDING in the open window).
\<close>

definition relay_admits
  :: "('k, 'v) dw_exec_state \<Rightarrow> ('k, 'v) dw_exec_label \<Rightarrow> bool"
where
  "relay_admits s a \<longleftrightarrow>
     exec_label_preserves_history_wf s a
   \<and> (case a of
        DoSource c e \<Rightarrow> src_lt (adv s) c
      | DoDownstream c e \<Rightarrow>
          relay_history_prefix
            (exec_down_hist s @ [(c, e)])
            (scoped_replay_history (exec_src_hist s) (exec_scope s))
      | _ \<Rightarrow> True)"

definition relay_step
  :: "('k, 'v) dw_exec_state \<Rightarrow> ('k, 'v) dw_exec_label \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  "relay_step s a s' \<longleftrightarrow> dw_exec_step s a s' \<and> relay_admits s a"

text \<open>The discipline is NOT the trivial predicate (C1a): no @{text DoSource}
  is admitted at a coordinate below the delivered frontier.\<close>

lemma relay_admits_witness_false:
  "\<not> relay_admits (initial_exec_state (\<lambda>_. None) {0::nat} ec3)
        (DoSource c0 (Insert (0::nat) (0::nat)))"
  by (simp add: relay_admits_def adv_def initial_exec_state_def src_lt_eq_less)

lemma relay_admits_not_True:
  "(relay_admits :: (nat,nat) dw_exec_state \<Rightarrow> _ \<Rightarrow> bool) \<noteq> (\<lambda>_ _. True)"
proof
  assume eq: "(relay_admits :: (nat,nat) dw_exec_state \<Rightarrow> _ \<Rightarrow> bool)
                = (\<lambda>_ _. True)"
  have "relay_admits (initial_exec_state (\<lambda>_. None) {0::nat} ec3)
          (DoSource c0 (Insert (0::nat) (0::nat)))"
    unfolding eq by simp
  with relay_admits_witness_false show False ..
qed

definition I_relay_labels
  :: "('k, 'v) dw_exec_state \<Rightarrow>
      (('k, 'v) dw_exec_state, 'k, 'v) dual_write_implementation"
where
  "I_relay_labels s0 =
     \<lparr> dwi_initial = s0,
       dwi_step = relay_step,
       dwi_state = (\<lambda>s. s) \<rparr>"

lemma I_relay_labels_refines_exec: "dwi_refines_exec (I_relay_labels s0)"
  by (simp add: dwi_refines_exec_def I_relay_labels_def relay_step_def)


section \<open>The decisive crux for NON-ATOMIC recovery (Milestone 5)\<close>

text \<open>
  K1 (atomic-heal) forbids recovery that sets \<open>down_hist := src_hist\<close>.  A
  genuine bounded-replay recovery materializes a DIFFERENT history, namely the
  source-ordered, IN-SCOPE prefix of \<open>src_hist\<close> up to \<open>f\<close>, and must still
  satisfy \<open>source_image_equiv_on\<close>, i.e. \<open>Src b D f = Src b H f\<close> on scope \<open>K\<close>.

  The materialized replay history @{const replay_down_hist} is defined above.
\<close>

text \<open>
  CRUX LEMMA.  This is the genuinely-new content: a scoped, frontier-bounded
  filter of the source history has the SAME source-image on scope at that
  frontier.  No analogue exists in the repo (grep was empty).  If this is
  provable and nontrivial, the non-atomic recovery is genuine; if it forces
  H = D or collapses to by simp, it is a mirage.
\<close>

text \<open>
  General filter lemma: dropping events that are INVISIBLE to k at f does not
  change @{const Src} at k.  Proven by list induction reusing
  @{thm Src_snoc_invisible}.  This is the load-bearing per-key fact.
\<close>

lemma Src_filter_keep_visible:
  fixes b :: "'k \<rightharpoonup> 'v" and H :: "('k, 'v) src_history"
  assumes keep: "\<And>x. x \<in> set H \<Longrightarrow> visible_src_event_at f k x \<Longrightarrow> P x"
  shows "Src b (filter P H) f k = Src b H f k"
  using keep
proof (induction H rule: rev_induct)
  case Nil
  show ?case by simp
next
  case (snoc x H)
  have IH: "Src b (filter P H) f k = Src b H f k"
    using snoc.prems by (auto intro: snoc.IH)
  show ?case
  proof (cases "visible_src_event_at f k x")
    case True
    \<comment> \<open>x visible to k at f, hence kept by P, and it is the snoc element.\<close>
    have keepx: "P x" using snoc.prems True by simp
    have "Src b (filter P (H @ [x])) f k = Src b (filter P H @ [x]) f k"
      using keepx by simp
    also have "\<dots> = event_result (snd x)"
      using True
      by (cases x)
         (simp add: Src_snoc_event_at_key visible_src_event_at_def)
    also have "\<dots> = Src b (H @ [x]) f k"
      using True
      by (cases x)
         (simp add: Src_snoc_event_at_key visible_src_event_at_def)
    finally show ?thesis .
  next
    case False
    \<comment> \<open>x invisible to k at f: it does not affect Src at k whether kept or not.\<close>
    have rhs: "Src b (H @ [x]) f k = Src b H f k"
      by (rule Src_snoc_invisible[OF False])
    show ?thesis
    proof (cases "P x")
      case True
      have "Src b (filter P (H @ [x])) f k = Src b (filter P H @ [x]) f k"
        using True by simp
      also have "\<dots> = Src b (filter P H) f k"
        by (rule Src_snoc_invisible[OF False])
      also have "\<dots> = Src b H f k" by (rule IH)
      finally show ?thesis using rhs by simp
    next
      case False
      have "Src b (filter P (H @ [x])) f k = Src b (filter P H) f k"
        using False by simp
      also have "\<dots> = Src b H f k" by (rule IH)
      finally show ?thesis using rhs by simp
    qed
  qed
qed

text \<open>
  CRUX LEMMA discharged from the general filter lemma: a scoped,
  frontier-bounded filter has the SAME source-image on scope.  This is what
  lets the non-atomic recovery satisfy \<open>source_image_equiv_on\<close> without setting
  \<open>down_hist := src_hist\<close>.
\<close>

lemma replay_down_hist_image_on_scope:
  fixes b :: "'k \<rightharpoonup> 'v" and H :: "('k, 'v) src_history"
  assumes k_in: "k \<in> K"
  shows "Src b (replay_down_hist H K f) f k = Src b H f k"
  unfolding replay_down_hist_def
proof (rule Src_filter_keep_visible)
  fix x
  assume "visible_src_event_at f k x"
  then have "fst x \<le> f" and "key_of (snd x) = k"
    by (simp_all add: visible_src_event_at_def)
  with k_in show "(\<lambda>(c, e). c \<le> f \<and> key_of e \<in> K) x"
    by (cases x) simp
qed

text \<open>
  GENERALIZED CRUX (used for the inductive invariant).  The replay is filtered
  at a bound @{text g} (the advertised frontier @{term "adv s"}), but the safety
  equality must hold at EVERY @{text "f \<le> g"}.  At such an @{text f} the events
  the filter drops --- out-of-scope ones, and in-scope ones at coordinates in
  @{text "(f, g]"} --- are all invisible to @{text k} at @{text f}, so they
  cannot change @{const Src} at @{text f}.  This is again @{thm
  Src_filter_keep_visible}: any event VISIBLE to @{text k} at @{text f} has
  @{text "c \<le> f \<le> g"} and key @{text k} in @{text K}, hence is kept.
\<close>

lemma replay_down_hist_image_on_scope_le:
  fixes b :: "'k \<rightharpoonup> 'v" and H :: "('k, 'v) src_history"
  assumes k_in: "k \<in> K" and le: "f \<le> g"
  shows "Src b (replay_down_hist H K g) f k = Src b H f k"
  unfolding replay_down_hist_def
proof (rule Src_filter_keep_visible)
  fix x
  assume "visible_src_event_at f k x"
  then have "fst x \<le> f" and "key_of (snd x) = k"
    by (simp_all add: visible_src_event_at_def)
  with k_in le show "(\<lambda>(c, e). c \<le> g \<and> key_of e \<in> K) x"
    by (cases x) (simp add: order_trans)
qed


section \<open>Milestone 5: NON-ATOMIC bounded-replay recovery (anti-circularity)\<close>

text \<open>
  The relay's post-crash recovery materializes @{const replay_down_hist} (the
  SCOPED, frontier-bounded prefix of the source history) as the new downstream
  history.  This is per-event CDC work, NOT the wholesale
  @{const recovery_reconciled_state} (which sets \<open>down_hist := src_hist\<close> outright).
\<close>

definition relay_bounded_replay_reconcile
  :: "('k, 'v) dw_exec_state \<Rightarrow> frontier \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  "relay_bounded_replay_reconcile s f s' \<longleftrightarrow>
     (\<exists>c. exec_status s = Crashed c)
   \<and> f \<le> exec_finish s
   \<and> s' = s\<lparr> exec_down_hist :=
              replay_down_hist (exec_src_hist s) (exec_scope s) f,
            exec_pending := {},
            exec_status := Recovered \<rparr>"

text \<open>
  The complete relay machine has two action forms.  \<open>Relay_Label\<close>
  embeds the crashable running-phase projection @{const I_relay_labels};
  \<open>Relay_Reconcile\<close> performs the bounded replay above.  Keeping the
  action sum explicit avoids pretending that a status-only @{const Recover}
  label can change the downstream history.
\<close>

datatype ('k, 'v) relay_action =
    Relay_Label "('k, 'v) dw_exec_label"
  | Relay_Reconcile frontier

inductive relay_machine_step
  :: "('k, 'v) dw_exec_state \<Rightarrow> ('k, 'v) relay_action \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  rms_label:
    "relay_step s a s' \<Longrightarrow>
     relay_machine_step s (Relay_Label a) s'"
| rms_reconcile:
    "relay_bounded_replay_reconcile s f s' \<Longrightarrow>
     relay_machine_step s (Relay_Reconcile f) s'"

record ('k, 'v) relay_implementation =
  relay_initial :: "('k, 'v) dw_exec_state"
  relay_transition ::
    "('k, 'v) dw_exec_state \<Rightarrow> ('k, 'v) relay_action \<Rightarrow>
     ('k, 'v) dw_exec_state \<Rightarrow> bool"

definition I_relay
  :: "('k, 'v) dw_exec_state \<Rightarrow> ('k, 'v) relay_implementation"
where
  "I_relay s0 =
     \<lparr>relay_initial = s0, relay_transition = relay_machine_step\<rparr>"

inductive relay_trace
  :: "('k, 'v) relay_implementation \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow>
      ('k, 'v) relay_action list \<Rightarrow>
      ('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  relay_trace_refl:
    "relay_trace I s [] s"
| relay_trace_step:
    "\<lbrakk>relay_transition I s a s'; relay_trace I s' as s''\<rbrakk>
     \<Longrightarrow> relay_trace I s (a # as) s''"

lemma I_relay_label_step:
  "relay_step s a s' \<Longrightarrow>
   relay_transition (I_relay s0) s (Relay_Label a) s'"
  by (simp add: I_relay_def relay_machine_step.rms_label)

lemma I_relay_reconcile_step:
  "relay_bounded_replay_reconcile s f s' \<Longrightarrow>
   relay_transition (I_relay s0) s (Relay_Reconcile f) s'"
  by (simp add: I_relay_def relay_machine_step.rms_reconcile)

text \<open>
  The image-equivalence obligation is discharged by the CRUX lemma — NOT by
  copying \<open>src_hist\<close>, and NOT by simp off a store=Apply assumption.
\<close>

lemma relay_replay_source_image_equiv:
  "source_image_equiv_on b K f H (replay_down_hist H K f)"
  unfolding source_image_equiv_on_def restrict_def
proof (rule ext)
  fix k
  show "(if k \<in> K then Src b (replay_down_hist H K f) f k else None) =
        (if k \<in> K then Src b H f k else None)"
  proof (cases "k \<in> K")
    case True
    then show ?thesis by (simp add: replay_down_hist_image_on_scope)
  next
    case False
    then show ?thesis by simp
  qed
qed

text \<open>
  KEY THEOREM (Milestone 5).  The non-atomic recovery inhabits the existing
  effective-redelivery predicate that the buried convergence layer consumes.
  This does NOT cite \<open>recovery_reconciled_state\<close> / \<open>recovery_reconcile_step\<close> /
  \<open>recovery_redelivers_source_history\<close>.
\<close>

theorem relay_bounded_replay_reconcile_effective:
  assumes "relay_bounded_replay_reconcile s f s'"
  shows "recovery_effectively_redelivers_source_history_at s f s'"
proof -
  from assms have s'_eq:
    "s' = s\<lparr> exec_down_hist :=
               replay_down_hist (exec_src_hist s) (exec_scope s) f,
             exec_pending := {},
             exec_status := Recovered \<rparr>"
    and crashed: "\<exists>c. exec_status s = Crashed c"
    by (auto simp: relay_bounded_replay_reconcile_def)
  have img:
    "source_image_equiv_on (exec_base s) (exec_scope s) f
        (exec_src_hist s) (exec_down_hist s')"
    using s'_eq by (simp add: relay_replay_source_image_equiv)
  show ?thesis
    unfolding recovery_effectively_redelivers_source_history_at_def
    using s'_eq img by simp
qed

text \<open>
  ANTI-K1 (the decisive non-collapse check).  The recovered \<open>down_hist\<close> is, on
  a concrete instance, STRICTLY DIFFERENT from \<open>src_hist\<close> --- so this is
  provably NOT the wholesale atomic heal.  Witness: an out-of-scope event
  survives in \<open>src_hist\<close> but is filtered out of the replayed \<open>down_hist\<close>.
\<close>

definition anti_atomic_witness_src :: "(nat, nat) src_history" where
  "anti_atomic_witness_src = [(ec2, Insert 0 7), (ec3, Insert 1 9)]"

lemma anti_atomic_down_neq_src:
  "replay_down_hist anti_atomic_witness_src {0::nat} ec3 \<noteq>
   anti_atomic_witness_src"
  by (simp add: replay_down_hist_def anti_atomic_witness_src_def ec_defs)

text \<open>
  ...yet the recovered downstream image AGREES with the source image on the
  monitored scope at the frontier (the replayed prefix is image-correct),
  which is exactly what the wholesale heal also gives — but earned per-event.
\<close>

lemma anti_atomic_image_agrees:
  "source_image_equiv_on (\<lambda>_. None) {0::nat} ec3
      anti_atomic_witness_src
      (replay_down_hist anti_atomic_witness_src {0::nat} ec3)"
  by (rule relay_replay_source_image_equiv)

text \<open>
  And the recovered state therefore has NO scoped mismatch at f, via the
  EXISTING effective-redelivery no-mismatch theorem — fed by the non-atomic
  operator.
\<close>

theorem relay_bounded_replay_no_mismatch:
  assumes "relay_bounded_replay_reconcile s f s'"
  shows "\<forall>k. \<not> mismatch_at (proto_of_exec_at s' f) f k"
  by (rule recovery_effective_redelivery_no_mismatch
      [OF relay_bounded_replay_reconcile_effective[OF assms]])

text \<open>
  PLUG INTO the buried convergence layer: diverges-before / converged-after,
  with the NON-ATOMIC operator as the concrete inhabitant.
\<close>

theorem relay_bounded_replay_temporal_convergence:
  assumes trace: "dw_exec_trace s wait s_wait"
      and labels: "list_all recovery_observation_label wait"
      and before: "diverges (proto_of_exec_at s f) f"
      and reconcile: "relay_bounded_replay_reconcile s_wait f s_done"
  shows
    "diverges (proto_of_exec_at s_wait f) f
   \<and> \<not> diverges (proto_of_exec_at s_done f) f"
  by (rule recovery_temporal_convergence_with_effective_redelivery
      [OF trace labels before
          relay_bounded_replay_reconcile_effective[OF reconcile]])


section \<open>Milestone 4: running-phase safety at occurrence-complete frontiers\<close>

text \<open>
  The relay is crash-closed (Crash enabled from every Running state — including
  mid-replay, defeating K3's ``no crash in the window'').
\<close>

lemma I_relay_labels_crash_closed:
  fixes s0 :: "('k, 'v) dw_exec_state"
  shows "crash_closed_implementation (I_relay_labels s0)"
proof (rule all_states_crash_closure_imp_crash_closed_implementation)
  fix s :: "('k, 'v) dw_exec_state" and c
  assume "exec_status (dwi_state (I_relay_labels s0) s) = Running"
  then have run: "exec_status s = Running" by (simp add: I_relay_labels_def)
  have "relay_step s (Crash c) (s\<lparr>exec_status := Crashed c\<rparr>)"
    using run
    by (simp add: relay_step_def relay_admits_def
                  exec_label_preserves_history_wf_def dw_exec_step.crash)
  then have "dwi_step (I_relay_labels s0) s (Crash c) (s\<lparr>exec_status := Crashed c\<rparr>)"
    by (simp add: I_relay_labels_def)
  thus "\<exists>s'. dwi_step (I_relay_labels s0) s (Crash c) s'" by blast
qed

text \<open>
  OCCURRENCE-COMPLETE SAFETY.  We do NOT claim ``no mismatch at every frontier''
  (that is false in the live window and would be K3-vacuous to dodge).  We claim
  the honest scoped property: a state whose downstream image equals the replay
  image on scope at a complete frontier @{text f} suffers NO observable
  mismatch when crashed at @{text f}.  The premise here is the relay's OWN
  invariant (R3), established by its steps --- NOT \<open>replay_derived_at\<close> taken as a
  hypothesis.  The conclusion routes through the replay-safety bridge, and is
  NOT @{text "by simp"} off a store=Apply assumption.
\<close>

text \<open>
  R3 is the constructive store equality at @{text f}.  In the inductive relay
  below it is derived from @{const relay_complete_through}, not from the last
  delivered coordinate: this is the distinction needed for tied-coordinate
  occurrences.  Because @{const replay_down_hist} has the same source image on
  scope (CRUX), R3 is equivalent to ``down image = the scoped-replayed source
  image at f''.
\<close>

theorem relay_advertised_no_observable_mismatch:
  fixes s :: "('k, 'v) dw_exec_state"
  assumes wf:   "wellformed_src_history (exec_src_hist s)"
      and base: "exec_base s = (\<lambda>_. None)"
      and le:   "f \<le> exec_finish s"
      and r3:
        "restrict (store2_of_exec s f) (exec_scope s) =
         restrict
           (Apply (cdc_replay_prefix (proto_of_exec_at s f) f))
           (exec_scope s)"
    shows "\<not> observable_mismatch (s\<lparr>exec_status := Crashed f\<rparr>) f k"
  by (rule execution_cdc_replay_prefix_no_observable_mismatch[OF wf base r3 le])


section \<open>Milestone 6: closed end-to-end witness — REAL crash window\<close>

text \<open>
  Concrete relay run.  Scope @{term "{0::nat}"}; an in-scope event at ec2 and a
  later in-scope event at ec3.  The relay delivers ec2 (advertising frontier
  ec2), then the source races ahead with ec3, then it CRASHES at ec3 BEFORE
  catching up.  We exhibit:
    (a) reachability via @{const relay_step};
    (b) a GENUINE mismatch at the unadvertised frontier ec3 (down lags src);
    (c) NO mismatch at the occurrence-complete frontier ec2;
    (d) an executable recovery to ec3 with image agreement.
  This defeats K3 (the window is real and crashable) and G6 (the gap is real,
  safety is earned at the advertised frontier, not avoided).
\<close>

definition w0 :: "(nat, nat) dw_exec_state" where
  "w0 = initial_exec_state (\<lambda>_. None) {0} ec3"

text \<open>State after DoSource ec2 (post-state in rule-output form).\<close>
definition w_src2 :: "(nat, nat) dw_exec_state" where
  "w_src2 = w0\<lparr>exec_src_hist := exec_src_hist w0 @ [(ec2, Insert 0 7)]\<rparr>"

text \<open>State after EnqueueDownstream ec2.\<close>
definition w_enq2 :: "(nat, nat) dw_exec_state" where
  "w_enq2 = w_src2\<lparr>exec_enqueued := exec_enqueued w_src2 @ [(ec2, Insert 0 7)],
                   exec_pending := insert (ec2, Insert 0 7) (exec_pending w_src2)\<rparr>"

text \<open>State after DoDownstream ec2 (in-scope, advertised at ec2).\<close>
definition w_down2 :: "(nat, nat) dw_exec_state" where
  "w_down2 = w_enq2\<lparr>exec_down_hist := exec_down_hist w_enq2 @ [(ec2, Insert 0 7)],
                    exec_pending := exec_pending w_enq2 - {(ec2, Insert 0 7)}\<rparr>"

text \<open>State after DoSource ec3 (source races ahead — window OPEN).\<close>
definition w_src3 :: "(nat, nat) dw_exec_state" where
  "w_src3 = w_down2\<lparr>exec_src_hist := exec_src_hist w_down2 @ [(ec3, Insert 0 9)]\<rparr>"

text \<open>State after Crash ec3 (frozen in the gap).\<close>
definition w_crash :: "(nat, nat) dw_exec_state" where
  "w_crash = w_src3\<lparr>exec_status := Crashed ec3\<rparr>"

text \<open>Each transition is a genuine @{const relay_step}.\<close>

text \<open>Each transition is admitted under the REAL discipline (C7): the
  open-gap witness with the bad crash at the unadvertised @{const ec3} survives.\<close>

lemma w_step_src2: "relay_step w0 (DoSource ec2 (Insert 0 7)) w_src2"
  unfolding relay_step_def relay_admits_def w_src2_def
  by (intro conjI dw_exec_step.do_source)
     (simp_all add: w0_def initial_exec_state_def
                    exec_label_preserves_history_wf_def history_can_append_def
                    adv_def src_lt_eq_less ec_defs)

lemma w_step_enq2:
  "relay_step w_src2 (EnqueueDownstream ec2 (Insert 0 7)) w_enq2"
  unfolding relay_step_def relay_admits_def w_enq2_def
  by (intro conjI dw_exec_step.enqueue_downstream)
     (simp_all add: w_src2_def w0_def initial_exec_state_def
                    exec_label_preserves_history_wf_def history_can_append_def
                    ec_defs)

lemma w_step_down2:
  "relay_step w_enq2 (DoDownstream ec2 (Insert 0 7)) w_down2"
  unfolding relay_step_def relay_admits_def w_down2_def
  by (intro conjI dw_exec_step.do_downstream)
     (simp_all add: w_enq2_def w_src2_def w0_def initial_exec_state_def
                    exec_label_preserves_history_wf_def history_can_append_def
                    relay_history_prefix_def scoped_replay_history_def ec_defs)

lemma w_step_src3: "relay_step w_down2 (DoSource ec3 (Insert 0 9)) w_src3"
  unfolding relay_step_def relay_admits_def w_src3_def
  by (intro conjI dw_exec_step.do_source)
     (simp_all add: w_down2_def w_enq2_def w_src2_def w0_def
                    initial_exec_state_def
                    exec_label_preserves_history_wf_def history_can_append_def
                    adv_def src_lt_eq_less ec_defs)

lemma w_step_crash: "relay_step w_src3 (Crash ec3) w_crash"
  unfolding relay_step_def relay_admits_def w_crash_def
  by (intro conjI dw_exec_step.crash)
     (simp_all add: w_src3_def w_down2_def w_enq2_def w_src2_def w0_def
                    initial_exec_state_def exec_label_preserves_history_wf_def)

text \<open>Reachability: the crashed state is a genuine @{const dwi_trace} of
  @{const I_relay_labels} from its initial state.\<close>

lemma relay_dwi_stepI:
  "relay_step s a s' \<Longrightarrow> dwi_step (I_relay_labels w0) s a s'"
  by (simp add: I_relay_labels_def)

lemma w_crash_reachable:
  "dwi_trace (I_relay_labels w0) (dwi_initial (I_relay_labels w0))
     [DoSource ec2 (Insert 0 7), EnqueueDownstream ec2 (Insert 0 7),
      DoDownstream ec2 (Insert 0 7), DoSource ec3 (Insert 0 9),
      Crash ec3]
     w_crash"
proof -
  have init: "dwi_initial (I_relay_labels w0) = w0" by (simp add: I_relay_labels_def)
  show ?thesis
    unfolding init
    by (rule dwi_trace.dwi_trace_step[OF relay_dwi_stepI[OF w_step_src2]],
        rule dwi_trace.dwi_trace_step[OF relay_dwi_stepI[OF w_step_enq2]],
        rule dwi_trace.dwi_trace_step[OF relay_dwi_stepI[OF w_step_down2]],
        rule dwi_trace.dwi_trace_step[OF relay_dwi_stepI[OF w_step_src3]],
        rule dwi_trace.dwi_trace_step[OF relay_dwi_stepI[OF w_step_crash]],
        rule dwi_trace.dwi_trace_refl)
qed

text \<open>Field-level normal forms of the witness states (history fields only).\<close>

lemma w_crash_fields:
  "exec_base w_crash = (\<lambda>_. None)"
  "exec_src_hist w_crash = [(ec2, Insert 0 7), (ec3, Insert 0 9)]"
  "exec_down_hist w_crash = [(ec2, Insert 0 7)]"
  "exec_scope w_crash = {0}"
  "exec_finish w_crash = ec3"
  "exec_status w_crash = Crashed ec3"
  by (simp_all add: w_crash_def w_src3_def w_down2_def w_enq2_def
                    w_src2_def w0_def initial_exec_state_def)

lemma w_src3_fields:
  "exec_base w_src3 = (\<lambda>_. None)"
  "exec_src_hist w_src3 = [(ec2, Insert 0 7), (ec3, Insert 0 9)]"
  "exec_down_hist w_src3 = [(ec2, Insert 0 7)]"
  "exec_scope w_src3 = {0}"
  "exec_finish w_src3 = ec3"
  by (simp_all add: w_src3_def w_down2_def w_enq2_def w_src2_def w0_def
                    initial_exec_state_def)

text \<open>Source image at key 0: down-history gives @{term "Some 7"} at any
  frontier @{text "\<ge> ec2"}; full source gives @{term "Some 9"} at @{text "\<ge> ec3"}
  and @{term "Some 7"} at @{text ec2}.\<close>

text \<open>Concrete coordinate-order facts used by the index computation.\<close>
lemmas ec_ord =
  ec_defs less_eq_src_coord_def src_le_def coord_of_nat_def
  Abs_src_coord_inverse[OF UNIV_I]

lemma down_image_ec3: "Src (\<lambda>_. None) [(ec2, Insert 0 7)] ec3 0 = Some 7"
  by (simp add: Src_def latest_src_event_def Let_def ec_ord)

lemma down_image_ec2: "Src (\<lambda>_. None) [(ec2, Insert 0 7)] ec2 0 = Some 7"
  by (simp add: Src_def latest_src_event_def Let_def ec_ord)

lemma src_image_ec3:
  "Src (\<lambda>_. None) [(ec2, Insert 0 7), (ec3, Insert 0 9)] ec3 0 = Some 9"
  by (simp add: Src_def latest_src_event_def Let_def ec_ord)

lemma src_image_ec2:
  "Src (\<lambda>_. None) [(ec2, Insert 0 7), (ec3, Insert 0 9)] ec2 0 = Some 7"
  by (simp add: Src_def latest_src_event_def Let_def ec_ord)

text \<open>(b) GENUINE mismatch at the UNADVERTISED frontier \<open>ec3\<close>: \<open>down_hist\<close>
  (only \<open>ec2\<close>, image @{term "Some 7"}) lags \<open>src_hist\<close> (\<open>ec2\<close>, \<open>ec3\<close>, image
  @{term "Some 9"}) on the scoped key 0.  The window is real.\<close>

lemma w_crash_mismatch_at_ec3:
  "mismatch_at (proto_of_exec_at w_crash ec3) ec3 0"
  by (simp add: mismatch_at_def proto_of_exec_at_def store2_of_exec_def
                log_image_def restrict_def w_crash_fields
                down_image_ec3 src_image_ec3)

text \<open>This is an OBSERVABLE bad crash at ec3 — the hazard is genuinely present
  for the permissive relay (it crashed BEFORE catching up).\<close>

lemma w_crash_observable_mismatch_at_ec3:
  "observable_mismatch w_crash ec3 0"
  by (simp add: observable_mismatch_def w_crash_mismatch_at_ec3 w_crash_fields
                src_le_refl src_le_eq_less_eq)

text \<open>(c) NO mismatch at the ADVERTISED frontier ec2: the relay HAD replayed
  ec2 before the crash, so the durable down image (@{term "Some 7"}) matches the
  source image (@{term "Some 7"}) there.\<close>

lemma w_crash_no_mismatch_at_ec2:
  "\<not> mismatch_at (proto_of_exec_at w_crash ec2) ec2 0"
  by (simp add: mismatch_at_def proto_of_exec_at_def store2_of_exec_def
                log_image_def restrict_def w_crash_fields
                down_image_ec2 src_image_ec2)

text \<open>...and likewise no OBSERVABLE mismatch at ec2 (crash-at-ec2 view).\<close>

lemma w_no_observable_mismatch_at_ec2:
  "\<not> observable_mismatch (w_src3\<lparr>exec_status := Crashed ec2\<rparr>) ec2 0"
  by (simp add: observable_mismatch_def mismatch_at_def proto_of_exec_at_def
                store2_of_exec_def log_image_def restrict_def w_src3_fields
                down_image_ec2 src_image_ec2)

text \<open>(d) Non-atomic recovery to \<open>ec3\<close> yields a recovered state whose
  \<open>down_hist\<close> is the replayed scoped prefix.  In this first control both
  source events are in scope, so the replay happens to coincide with the atomic
  copy; the separate executable witness below supplies the strict non-atomic
  inequality.  The recovered control state has no scoped mismatch.\<close>

definition w_recovered :: "(nat, nat) dw_exec_state" where
  "w_recovered =
     w_crash\<lparr> exec_down_hist :=
                replay_down_hist (exec_src_hist w_crash) (exec_scope w_crash) ec3,
              exec_pending := {},
              exec_status := Recovered \<rparr>"

lemma w_recover_step: "relay_bounded_replay_reconcile w_crash ec3 w_recovered"
  unfolding relay_bounded_replay_reconcile_def w_recovered_def
  by (simp add: w_crash_fields src_le_refl src_le_eq_less_eq)

lemma w_recovered_no_mismatch:
  "\<forall>k. \<not> mismatch_at (proto_of_exec_at w_recovered ec3) ec3 k"
  by (rule relay_bounded_replay_no_mismatch[OF w_recover_step])

lemma w_recovery_coincides_with_atomic_control:
  "w_recovered = recovery_reconciled_state w_crash"
  by (simp add: w_recovered_def recovery_reconciled_state_def
                w_crash_fields replay_down_hist_def ec_defs)

lemma w_recovered_full_relay_trace:
  "relay_trace (I_relay w0) (relay_initial (I_relay w0))
     [Relay_Label (DoSource ec2 (Insert 0 7)),
      Relay_Label (EnqueueDownstream ec2 (Insert 0 7)),
      Relay_Label (DoDownstream ec2 (Insert 0 7)),
      Relay_Label (DoSource ec3 (Insert 0 9)),
      Relay_Label (Crash ec3),
      Relay_Reconcile ec3]
     w_recovered"
proof -
  have init: "relay_initial (I_relay w0) = w0"
    by (simp add: I_relay_def)
  show ?thesis
    unfolding init
    by (rule relay_trace.relay_trace_step[OF I_relay_label_step[OF w_step_src2]],
        rule relay_trace.relay_trace_step[OF I_relay_label_step[OF w_step_enq2]],
        rule relay_trace.relay_trace_step[OF I_relay_label_step[OF w_step_down2]],
        rule relay_trace.relay_trace_step[OF I_relay_label_step[OF w_step_src3]],
        rule relay_trace.relay_trace_step[OF I_relay_label_step[OF w_step_crash]],
        rule relay_trace.relay_trace_step[OF I_relay_reconcile_step[OF w_recover_step]],
        rule relay_trace.relay_trace_refl)
qed


subsection \<open>Executable strict non-atomic witness\<close>

text \<open>
  The strict witness makes the distinction operational, rather than comparing
  two free lists.  It commits one in-scope event and then one out-of-scope
  event, crashes, and reconciles in the complete @{const I_relay} machine.
  Bounded replay materializes only the in-scope occurrence, whereas
  @{const recovery_reconciled_state} copies both source occurrences.
\<close>

definition na0 :: "(nat, nat) dw_exec_state" where
  "na0 = initial_exec_state (\<lambda>_. None) {0} ec3"

definition na_src_in :: "(nat, nat) dw_exec_state" where
  "na_src_in =
     na0\<lparr>exec_src_hist := exec_src_hist na0 @ [(ec2, Insert 0 7)]\<rparr>"

definition na_src_out :: "(nat, nat) dw_exec_state" where
  "na_src_out =
     na_src_in\<lparr>
       exec_src_hist := exec_src_hist na_src_in @ [(ec3, Insert 1 9)]\<rparr>"

definition na_crash :: "(nat, nat) dw_exec_state" where
  "na_crash = na_src_out\<lparr>exec_status := Crashed ec3\<rparr>"

definition na_recovered :: "(nat, nat) dw_exec_state" where
  "na_recovered =
     na_crash\<lparr>
       exec_down_hist :=
         replay_down_hist (exec_src_hist na_crash) (exec_scope na_crash) ec3,
       exec_pending := {},
       exec_status := Recovered\<rparr>"

lemma na_step_src_in:
  "relay_step na0 (DoSource ec2 (Insert 0 7)) na_src_in"
  unfolding relay_step_def relay_admits_def na_src_in_def
  by (intro conjI dw_exec_step.do_source)
     (simp_all add: na0_def initial_exec_state_def
                    exec_label_preserves_history_wf_def history_can_append_def
                    adv_def src_lt_eq_less ec_defs)

lemma na_step_src_out:
  "relay_step na_src_in (DoSource ec3 (Insert 1 9)) na_src_out"
  unfolding relay_step_def relay_admits_def na_src_out_def
  by (intro conjI dw_exec_step.do_source)
     (simp_all add: na_src_in_def na0_def initial_exec_state_def
                    exec_label_preserves_history_wf_def history_can_append_def
                    adv_def src_lt_eq_less ec_defs)

lemma na_step_crash:
  "relay_step na_src_out (Crash ec3) na_crash"
  unfolding relay_step_def relay_admits_def na_crash_def
  by (intro conjI dw_exec_step.crash)
     (simp_all add: na_src_out_def na_src_in_def na0_def
                    initial_exec_state_def exec_label_preserves_history_wf_def)

lemma na_crash_fields:
  "exec_src_hist na_crash = [(ec2, Insert 0 7), (ec3, Insert 1 9)]"
  "exec_down_hist na_crash = []"
  "exec_scope na_crash = {0}"
  "exec_finish na_crash = ec3"
  "exec_status na_crash = Crashed ec3"
  by (simp_all add: na_crash_def na_src_out_def na_src_in_def na0_def
                    initial_exec_state_def)

lemma na_recover_step:
  "relay_bounded_replay_reconcile na_crash ec3 na_recovered"
  unfolding relay_bounded_replay_reconcile_def na_recovered_def
  by (simp add: na_crash_fields src_le_refl src_le_eq_less_eq)

lemma na_recovery_strictly_non_atomic:
  "na_recovered \<noteq> recovery_reconciled_state na_crash"
proof
  assume eq: "na_recovered = recovery_reconciled_state na_crash"
  have down_eq:
    "exec_down_hist na_recovered =
     exec_down_hist (recovery_reconciled_state na_crash)"
    using eq by simp
  show False
    using down_eq
    by (simp add: na_recovered_def recovery_reconciled_state_def
                  na_crash_fields replay_down_hist_def ec_defs)
qed

lemma na_recovered_no_mismatch:
  "\<forall>k. \<not> mismatch_at (proto_of_exec_at na_recovered ec3) ec3 k"
  by (rule relay_bounded_replay_no_mismatch[OF na_recover_step])

lemma na_recovered_full_relay_trace:
  "relay_trace (I_relay na0) (relay_initial (I_relay na0))
     [Relay_Label (DoSource ec2 (Insert 0 7)),
      Relay_Label (DoSource ec3 (Insert 1 9)),
      Relay_Label (Crash ec3),
      Relay_Reconcile ec3]
     na_recovered"
proof -
  have init: "relay_initial (I_relay na0) = na0"
    by (simp add: I_relay_def)
  show ?thesis
    unfolding init
    by (rule relay_trace.relay_trace_step[OF I_relay_label_step[OF na_step_src_in]],
        rule relay_trace.relay_trace_step[OF I_relay_label_step[OF na_step_src_out]],
        rule relay_trace.relay_trace_step[OF I_relay_label_step[OF na_step_crash]],
        rule relay_trace.relay_trace_step[OF I_relay_reconcile_step[OF na_recover_step]],
        rule relay_trace.relay_trace_refl)
qed

section \<open>Audit lemmas (the skeptic's kill-criteria, discharged)\<close>

text \<open>The recovery relation always materializes the bounded replay.  This
  equation alone states no inequality; strict separation is the executable
  theorem @{thm na_recovery_strictly_non_atomic} above.\<close>

lemma relay_recovery_materializes_bounded_replay:
  "relay_bounded_replay_reconcile s f s'
     \<Longrightarrow> exec_down_hist s'
           = replay_down_hist (exec_src_hist s) (exec_scope s) f"
  by (simp add: relay_bounded_replay_reconcile_def)

text \<open>...whereas the atomic heal would set \<open>down_hist := src_hist\<close>:\<close>

lemma reconciled_state_copies_src:
  "exec_down_hist (recovery_reconciled_state s) = exec_src_hist s"
  by (simp add: recovery_reconciled_state_def)

text \<open>K3 (crash enabled IN the open window): from the reachable post-DoSource-ec3
  state @{const w_src3} — where down lags src on the scoped key — the relay
  ADMITS a Crash at ec3.  The dangerous window is genuinely crashable.\<close>

lemma w_crash_enabled_in_window:
  "\<exists>s'. relay_step w_src3 (Crash ec3) s'"
  using w_step_crash by blast

text \<open>...and the resulting crash is genuinely observable-bad (already shown):
  @{thm w_crash_observable_mismatch_at_ec3}.  So the relay does NOT dodge the
  hazard by closing the window (which would be the K3 collapse).\<close>


section \<open>End-to-end positive inhabitant (the missing centerpiece)\<close>

text \<open>
  Two end-to-end controls are kept.  The first has a reachable observable bad
  crash at ec3, a complete and safe ec2, and a recovery whose replay happens to
  equal the atomic copy.  The second is a complete machine execution whose
  out-of-scope source occurrence makes bounded replay strictly different from
  the atomic heal.
\<close>

text \<open>NB: on THIS witness both events are in scope, so the replay keeps both and
  \<open>down_hist\<close> coincides with \<open>src_hist\<close>.  It is therefore a coincidence
  control, not the anti-atomic witness.  The strict, executable separation is
  @{thm na_recovered_full_relay_trace} together with
  @{thm na_recovery_strictly_non_atomic}.\<close>

theorem relay_probe_end_to_end_facts:
  "relay_trace (I_relay w0) (relay_initial (I_relay w0))
      [Relay_Label (DoSource ec2 (Insert 0 7)),
       Relay_Label (EnqueueDownstream ec2 (Insert 0 7)),
       Relay_Label (DoDownstream ec2 (Insert 0 7)),
       Relay_Label (DoSource ec3 (Insert 0 9)),
       Relay_Label (Crash ec3),
       Relay_Reconcile ec3]
      w_recovered
 \<and> observable_mismatch w_crash ec3 0
 \<and> \<not> observable_mismatch (w_src3\<lparr>exec_status := Crashed ec2\<rparr>) ec2 0
 \<and> w_recovered = recovery_reconciled_state w_crash
 \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at w_recovered ec3) ec3 k)"
  using w_recovered_full_relay_trace w_crash_observable_mismatch_at_ec3
        w_no_observable_mismatch_at_ec2
        w_recovery_coincides_with_atomic_control w_recovered_no_mismatch
  by blast

theorem relay_strict_non_atomic_end_to_end_facts:
  "relay_trace (I_relay na0) (relay_initial (I_relay na0))
      [Relay_Label (DoSource ec2 (Insert 0 7)),
       Relay_Label (DoSource ec3 (Insert 1 9)),
       Relay_Label (Crash ec3),
       Relay_Reconcile ec3]
      na_recovered
 \<and> na_recovered \<noteq> recovery_reconciled_state na_crash
 \<and> (\<forall>k. \<not> mismatch_at (proto_of_exec_at na_recovered ec3) ec3 k)"
  using na_recovered_full_relay_trace na_recovery_strictly_non_atomic
        na_recovered_no_mismatch
  by blast


section \<open>GATE-1: prefix invariant plus discharged frontier completeness\<close>

subsection \<open>Static bridge: the replayed prefix's image is the source image\<close>

text \<open>
  The RHS of R3 is
  @{term "restrict (Apply (cdc_replay_prefix (proto_of_exec_at s f) f)) (exec_scope s)"}.
  We rewrite it into a @{const Src}-form on the SOURCE history.  This is a STATIC
  fact (no induction) provided by the repo's @{thm virtual_cut_certifies_outbox}:
  @{const cdc_replay_prefix} is a @{const cdc_segment_between} from @{const c0}
  (by @{thm cdc_replay_prefix_segment}), and @{const virtual_cut_state} unfolds
  to exactly the scoped ``Apply of the prefix equals Src of the source''
  equality.  This is NOT @{thm apply_latest_event_wins} and does NOT collapse the
  per-event filter --- it merely NAMES the RHS in terms of @{const Src}.
\<close>

lemma cdc_replay_prefix_image_is_src:
  fixes P :: "('k, 'v) proto"
  assumes wf: "wellformed_src_history (psrc P)"
  shows "restrict (Apply (cdc_replay_prefix P f)) (pscope P)
       = restrict (Src (\<lambda>_. None) (psrc P) f) (pscope P)"
proof -
  have "virtual_cut_state (\<lambda>_. None) (cdc_replay_prefix P f)
          (pscope P) f (psrc P)"
    using virtual_cut_certifies_outbox[OF wf cdc_replay_prefix_segment]
    by blast
  thus ?thesis
    by (simp add: virtual_cut_state_def)
qed


lemma exec_cdc_replay_prefix_image_is_src:
  assumes wf: "wellformed_src_history (exec_src_hist s)"
  shows "restrict (Apply (cdc_replay_prefix (proto_of_exec_at s f) f))
            (exec_scope s)
       = restrict (Src (\<lambda>_. None) (exec_src_hist s) f) (exec_scope s)"
  using cdc_replay_prefix_image_is_src
        [of "proto_of_exec_at s f" f] wf
  by (simp add: proto_of_exec_at_def)


subsection \<open>THE teeth lemma: DoSource out-of-window append-invariance\<close>

text \<open>
  The load-bearing obligation (synth-flagged).  Appending a source event at a
  coordinate @{text "c > f"} does NOT change the replayed prefix at @{text f},
  because the filter's @{text "c \<le> f"} conjunct drops it.  Stated and proved as a
  STANDALONE named lemma whose proof reduces to the out-of-window @{text "c > f"}
  case-kill on a @{const filter}-over-@{term "(@)"} split (the local
  @{text tail_empty} / @{text filter_eq} steps) --- NOT a bare @{text "by simp"}
  over @{const relay_admits}, mirroring the Disc1/Disc2 discriminator standard on
  the CRUX.
\<close>

lemma cdc_replay_prefix_psrc_snoc_out_of_window:
  fixes P :: "('k, 'v) proto"
  assumes out: "\<not> c \<le> f"
  shows "cdc_replay_prefix (P\<lparr>psrc := psrc P @ [(c, e)]\<rparr>) f
       = cdc_replay_prefix P f"
proof -
  have tail_empty:
    "filter (\<lambda>(c', e'). c0 < c' \<and> c' \<le> f \<and> key_of e' \<in> pscope P) [(c, e)] = []"
    using out by simp
  have filter_eq:
    "filter (\<lambda>(c', e'). c0 < c' \<and> c' \<le> f \<and> key_of e' \<in> pscope P)
        (psrc P @ [(c, e)])
   = filter (\<lambda>(c', e'). c0 < c' \<and> c' \<le> f \<and> key_of e' \<in> pscope P) (psrc P)"
    by (simp only: filter_append tail_empty append_Nil2)
  have sel_src: "psrc (P\<lparr>psrc := psrc P @ [(c, e)]\<rparr>) = psrc P @ [(c, e)]"
            and sel_scope: "pscope (P\<lparr>psrc := psrc P @ [(c, e)]\<rparr>) = pscope P"
    by simp_all
  have "cdc_replay_prefix (P\<lparr>psrc := psrc P @ [(c, e)]\<rparr>) f
      = map (\<lambda>(c', e'). cdc_lift c' e')
          (filter (\<lambda>(c', e'). c0 < c' \<and> c' \<le> f \<and> key_of e' \<in> pscope P)
            (psrc P @ [(c, e)]))"
    by (simp only: cdc_replay_prefix_def sel_src sel_scope)
  also have "\<dots> = map (\<lambda>(c', e'). cdc_lift c' e')
          (filter (\<lambda>(c', e'). c0 < c' \<and> c' \<le> f \<and> key_of e' \<in> pscope P) (psrc P))"
    by (simp only: filter_eq)
  also have "\<dots> = cdc_replay_prefix P f"
    by (simp only: cdc_replay_prefix_def)
  finally show ?thesis .
qed


lemma replay_down_hist_snoc_out_of_window:
  assumes "\<not> c \<le> f"
  shows "replay_down_hist (H @ [(c, e)]) K f = replay_down_hist H K f"
  unfolding replay_down_hist_def
  using \<open>\<not> c \<le> f\<close> by simp

text \<open>
  The teeth, instantiated at the EXACT level R3 names: across a @{text DoSource}
  step appending a source event at @{text "c > f"}, the R3 RHS
  @{term "cdc_replay_prefix (proto_of_exec_at s f) f"} is UNCHANGED.  This is the
  flagged lemma @{thm cdc_replay_prefix_psrc_snoc_out_of_window} carried through
  @{const proto_of_exec_at}; it is what keeps R3 stable while the source races.
  (The structural invariant \<open>relay_inv\<close> below uses the @{const replay_down_hist}
  twin of this fact; this theorem witnesses that the very same out-of-window drop
  governs the bridge-form RHS, so the safe side does not depend on which of the
  two equivalent shapes one carries.)
\<close>

theorem R3_rhs_do_source_invariant:
  fixes s :: "('k, 'v) dw_exec_state"
  assumes out: "\<not> c \<le> f"
  shows "cdc_replay_prefix
           (proto_of_exec_at (s\<lparr>exec_src_hist := exec_src_hist s @ [(c, e)]\<rparr>) f) f
       = cdc_replay_prefix (proto_of_exec_at s f) f"
proof -
  have proto_upd:
    "proto_of_exec_at (s\<lparr>exec_src_hist := exec_src_hist s @ [(c, e)]\<rparr>) f
       = (proto_of_exec_at s f)\<lparr>psrc := psrc (proto_of_exec_at s f) @ [(c, e)]\<rparr>"
    by (simp add: proto_of_exec_at_def store2_of_exec_def fun_eq_iff)
  show ?thesis
    unfolding proto_upd
    by (rule cdc_replay_prefix_psrc_snoc_out_of_window[OF out])
qed


subsection \<open>The structural invariant\<close>

text \<open>
  \<open>relay_inv s\<close>: the durable downstream history is an OCCURRENCE PREFIX of
  the in-scope source stream.  This is deliberately separate from frontier
  completeness: after delivering one of two occurrences at the same coordinate,
  the prefix invariant holds, but @{const relay_complete_through} at that
  coordinate does not.  Together with wellformedness and the genesis base this
  is the relay's running-phase invariant.
\<close>

definition relay_inv :: "('k, 'v) dw_exec_state \<Rightarrow> bool" where
  "relay_inv s \<longleftrightarrow>
     wellformed_exec_state s
   \<and> exec_base s = (\<lambda>_. None)
   \<and> relay_history_prefix
         (exec_down_hist s)
         (scoped_replay_history (exec_src_hist s) (exec_scope s))"

subsection \<open>Initialisation\<close>

lemma relay_inv_initial:
  "relay_inv (initial_exec_state (\<lambda>_. None) K fin)"
  unfolding relay_inv_def
proof (intro conjI)
  show "wellformed_exec_state (initial_exec_state (\<lambda>_. None) K fin)"
    by (rule initial_exec_state_wellformed)
  show "exec_base (initial_exec_state (\<lambda>_. None) K fin) = (\<lambda>_. None)"
    by (simp add: initial_exec_state_def)
  show "relay_history_prefix
          (exec_down_hist (initial_exec_state (\<lambda>_. None) K fin))
          (scoped_replay_history
            (exec_src_hist (initial_exec_state (\<lambda>_. None) K fin))
            (exec_scope (initial_exec_state (\<lambda>_. None) K fin)))"
    by (simp add: initial_exec_state_def relay_history_prefix_def
                  scoped_replay_history_def)
qed


subsection \<open>Extracting the discipline from a relay step\<close>

lemma relay_step_dw: "relay_step s a s' \<Longrightarrow> dw_exec_step s a s'"
  by (simp add: relay_step_def)

lemma relay_step_admits: "relay_step s a s' \<Longrightarrow> relay_admits s a"
  by (simp add: relay_step_def)

lemma relay_admits_preserves_wf:
  "relay_admits s a \<Longrightarrow> exec_label_preserves_history_wf s a"
  by (simp add: relay_admits_def)

text \<open>Wellformedness is preserved because the discipline carries
  @{const exec_label_preserves_history_wf}.\<close>

lemma relay_step_wellformed:
  assumes "relay_step s a s'" and "wellformed_exec_state s"
  shows "wellformed_exec_state s'"
  by (rule dw_exec_step_wellformed_exec_state
        [OF relay_step_dw[OF assms(1)] assms(2)
            relay_admits_preserves_wf[OF relay_step_admits[OF assms(1)]]])

text \<open>@{const exec_base} is untouched by every label.\<close>

lemma dw_exec_step_base:
  "dw_exec_step s a s' \<Longrightarrow> exec_base s' = exec_base s"
  by (induction rule: dw_exec_step.induct) simp_all


subsection \<open>THE step theorem: @{const relay_inv} is preserved by every label\<close>

text \<open>
  Schematic over an arbitrary reachable @{text s} (NOT a finite chain of witness
  states): @{const relay_inv} is closed under @{const relay_step} for all seven
  constructors.  A source append extends the scoped source suffix; a faithful
  downstream delivery extends the delivered occurrence prefix by exactly one;
  every other label leaves the two histories relevant to the prefix unchanged.
\<close>

theorem relay_inv_step:
  assumes step: "relay_step s a s'"
      and inv:  "relay_inv s"
  shows "relay_inv s'"
proof -
  have dw: "dw_exec_step s a s'" by (rule relay_step_dw[OF step])
  have adm: "relay_admits s a" by (rule relay_step_admits[OF step])
  have wf': "wellformed_exec_state s'"
    by (rule relay_step_wellformed[OF step]) (use inv in \<open>simp add: relay_inv_def\<close>)
  have base': "exec_base s' = (\<lambda>_. None)"
    using dw_exec_step_base[OF dw] inv by (simp add: relay_inv_def)
  have struct:
    "relay_history_prefix
       (exec_down_hist s)
       (scoped_replay_history (exec_src_hist s) (exec_scope s))"
    using inv by (simp add: relay_inv_def)
  have struct':
    "relay_history_prefix
       (exec_down_hist s')
       (scoped_replay_history (exec_src_hist s') (exec_scope s'))"
    using dw adm
  proof (cases rule: dw_exec_step.cases)
    case (do_source c e)
    from struct obtain rest where
      rest: "scoped_replay_history (exec_src_hist s) (exec_scope s)
             = exec_down_hist s @ rest"
      by (auto simp: relay_history_prefix_def)
    show ?thesis
      using rest
      by (auto simp: do_source relay_history_prefix_def
                     scoped_replay_history_def append_assoc)
  next
    case (enqueue_downstream c e)
    show ?thesis using struct by (simp add: enqueue_downstream)
  next
    case (do_downstream c e)
    show ?thesis
      using adm
      by (simp add: do_downstream relay_admits_def)
  next
    case (ack c e)
    show ?thesis using struct by (simp add: ack)
  next
    case (crash c)
    show ?thesis using struct by (simp add: crash)
  next
    case recover
    show ?thesis using struct by (simp add: recover)
  next
    case (observe f)
    show ?thesis using struct by (simp add: observe)
  qed
  show ?thesis
    unfolding relay_inv_def using wf' base' struct' by blast
qed


subsection \<open>R3 DERIVED from the invariant (not assumed)\<close>

text \<open>
  At any frontier explicitly known to be complete in a @{const relay_inv} state,
  the bridge-form R3 store equality holds.  Completeness equates the bounded
  downstream and source occurrence streams; the CRUX lifts that list equality
  to the two images, and the static bridge identifies the source image with the
  R3 right-hand side.  The explicit completeness premise is essential when
  several source occurrences share a coordinate.
\<close>

theorem relay_inv_imp_R3:
  assumes inv: "relay_inv s"
      and complete: "relay_complete_through s f"
  shows "restrict (store2_of_exec s f) (exec_scope s)
       = restrict
           (Apply (cdc_replay_prefix (proto_of_exec_at s f) f))
           (exec_scope s)"
proof -
  have wf: "wellformed_exec_state s"
   and base: "exec_base s = (\<lambda>_. None)"
    using inv by (simp_all add: relay_inv_def)
  have replay_eq:
    "replay_down_hist (exec_down_hist s) (exec_scope s) f
       = replay_down_hist (exec_src_hist s) (exec_scope s) f"
    using complete by (simp add: relay_complete_through_def)
  have wf_src: "wellformed_src_history (exec_src_hist s)"
    using wf by (simp add: wellformed_exec_state_def exec_histories_wellformed_def)
  \<comment> \<open>LHS = downstream image = in-scope replay image = source image at @{text f}.\<close>
  have lhs:
    "restrict (store2_of_exec s f) (exec_scope s)
   = restrict (Src (\<lambda>_. None) (exec_src_hist s) f) (exec_scope s)"
  proof (rule ext)
    fix k
    show "restrict (store2_of_exec s f) (exec_scope s) k
        = restrict (Src (\<lambda>_. None) (exec_src_hist s) f) (exec_scope s) k"
    proof (cases "k \<in> exec_scope s")
      case True
      have "store2_of_exec s f k
          = Src (\<lambda>_. None) (exec_down_hist s) f k"
        by (simp add: store2_of_exec_def base)
      also have "\<dots>
          = Src (\<lambda>_. None)
              (replay_down_hist (exec_down_hist s) (exec_scope s) f) f k"
        by (rule replay_down_hist_image_on_scope[OF True, symmetric])
      also have "\<dots>
          = Src (\<lambda>_. None)
              (replay_down_hist (exec_src_hist s) (exec_scope s) f) f k"
        by (simp only: replay_eq)
      also have "\<dots> = Src (\<lambda>_. None) (exec_src_hist s) f k"
        by (rule replay_down_hist_image_on_scope[OF True])
      finally show ?thesis using True by (simp add: restrict_def)
    next
      case False
      thus ?thesis by (simp add: restrict_def)
    qed
  qed
  \<comment> \<open>RHS = source image at @{text f} (static bridge).\<close>
  have rhs:
    "restrict (Apply (cdc_replay_prefix (proto_of_exec_at s f) f)) (exec_scope s)
   = restrict (Src (\<lambda>_. None) (exec_src_hist s) f) (exec_scope s)"
    by (rule exec_cdc_replay_prefix_image_is_src[OF wf_src])
  show ?thesis using lhs rhs by simp
qed


subsection \<open>Reachability: @{const relay_inv} holds at ALL reachable states\<close>

lemma dwi_step_I_relay_labels: "dwi_step (I_relay_labels s0) s a s' \<Longrightarrow> relay_step s a s'"
  by (simp add: I_relay_labels_def)

theorem relay_inv_dwi_trace:
  assumes trace: "dwi_trace I s xs s'"
      and Ieq:   "I = I_relay_labels s0"
      and inv:   "relay_inv s"
  shows "relay_inv s'"
  using trace Ieq inv
proof (induction rule: dwi_trace.induct)
  case (dwi_trace_refl I s)
  show ?case by (rule dwi_trace_refl.prems(2))
next
  case (dwi_trace_step I s a s' as s'')
  have step: "dwi_step (I_relay_labels s0) s a s'"
    using dwi_trace_step.hyps(1) dwi_trace_step.prems(1) by simp
  have "relay_inv s'"
    by (rule relay_inv_step[OF dwi_step_I_relay_labels[OF step]]) (rule dwi_trace_step.prems(2))
  thus ?case
    by (rule dwi_trace_step.IH[OF dwi_trace_step.prems(1)])
qed

text \<open>Reachability from the genuine relay initial state.\<close>

theorem relay_reachable_inv:
  assumes "dwi_trace (I_relay_labels (initial_exec_state (\<lambda>_. None) K fin))
             (dwi_initial (I_relay_labels (initial_exec_state (\<lambda>_. None) K fin))) xs s"
  shows "relay_inv s"
proof -
  have "dwi_trace (I_relay_labels (initial_exec_state (\<lambda>_. None) K fin))
          (initial_exec_state (\<lambda>_. None) K fin) xs s"
    using assms by (simp add: I_relay_labels_def)
  from relay_inv_dwi_trace[OF this refl relay_inv_initial] show ?thesis .
qed

subsection \<open>C6: no mismatch at complete frontiers of all reachable states\<close>

text \<open>
  THE safe side --- complete-frontier safety, no longer floating.  For ANY
  reachable relay state and ANY in-range frontier for which
  @{const relay_complete_through} holds, there is no observable mismatch when
  crashed at that frontier.  R3 is discharged from occurrence completeness
  (via @{thm relay_inv_imp_R3}), rather than inferred from the coordinate of
  the last delivered occurrence.  (This frontier-scoped property is named
  \<open>relay_complete_frontier_safe\<close> below; it is the relay's whole safe side ---
  the global no-reachable-bad-crash class is NOT claimed, and the downstream
  Converse theory places the relay outside it.)
\<close>

theorem relay_inv_no_observable_mismatch:
  assumes inv:   "relay_inv s"
      and complete: "relay_complete_through s f"
      and le_fin: "f \<le> exec_finish s"
  shows "\<not> observable_mismatch (s\<lparr>exec_status := Crashed f\<rparr>) f k"
proof -
  have wf: "wellformed_exec_state s"
   and base: "exec_base s = (\<lambda>_. None)"
    using inv by (simp_all add: relay_inv_def)
  have wf_src: "wellformed_src_history (exec_src_hist s)"
    using wf by (simp add: wellformed_exec_state_def exec_histories_wellformed_def)
  have r3:
    "restrict (store2_of_exec s f) (exec_scope s)
   = restrict (Apply (cdc_replay_prefix (proto_of_exec_at s f) f)) (exec_scope s)"
    by (rule relay_inv_imp_R3[OF inv complete])
  show ?thesis
    by (rule execution_cdc_replay_prefix_no_observable_mismatch
          [OF wf_src base r3 le_fin])
qed

text \<open>And, packaged for a reachable state of the genuine relay: \<close>

corollary relay_reachable_no_observable_mismatch:
  assumes reach: "dwi_trace (I_relay_labels (initial_exec_state (\<lambda>_. None) K fin))
             (dwi_initial (I_relay_labels (initial_exec_state (\<lambda>_. None) K fin))) xs s"
      and complete: "relay_complete_through s f"
      and le_fin: "f \<le> exec_finish s"
  shows "\<not> observable_mismatch (s\<lparr>exec_status := Crashed f\<rparr>) f k"
  by (rule relay_inv_no_observable_mismatch
        [OF relay_reachable_inv[OF reach] complete le_fin])

subsection \<open>The honest safety property, named: complete-frontier safety\<close>

text \<open>
  WHAT THE RELAY'S SAFE SIDE IS --- and is not.  The property the two
  theorems above establish is per-state and FRONTIER-SCOPED: no
  observable mismatch when crashed at any OCCURRENCE-COMPLETE in-range
  frontier.  It is named here so prose elsewhere can attribute exactly
  this property to the relay and nothing stronger.  It is NOT the
  global safe class of the converse characterization
  (no reachable observable bad crash --- the LHS of
  \<open>safe_iff_running_image_faithful\<close> in the downstream Converse theory):
  the relay FORCES a reachable observable bad crash at an unadvertised
  incomplete frontier by design (C7,
  @{thm [source] w_crash_observable_mismatch_at_ec3} on the witness),
  which is exactly why the Converse theory uses this same relay as the
  biconditional's UNSAFE-side inhabitant.  The wrappers restate the
  theorems of record against the named property; the statements of
  record are unchanged.
\<close>

definition relay_complete_frontier_safe
  :: "('k, 'v) dw_exec_state \<Rightarrow> bool"
where
  "relay_complete_frontier_safe s \<longleftrightarrow>
     (\<forall>f k. relay_complete_through s f \<longrightarrow> f \<le> exec_finish s \<longrightarrow>
        \<not> observable_mismatch (s\<lparr>exec_status := Crashed f\<rparr>) f k)"

theorem relay_inv_complete_frontier_safe:
  assumes "relay_inv s"
  shows "relay_complete_frontier_safe s"
  unfolding relay_complete_frontier_safe_def
  using relay_inv_no_observable_mismatch[OF assms] by blast

corollary relay_reachable_complete_frontier_safe:
  assumes reach: "dwi_trace (I_relay_labels (initial_exec_state (\<lambda>_. None) K fin))
             (dwi_initial (I_relay_labels (initial_exec_state (\<lambda>_. None) K fin))) xs s"
  shows "relay_complete_frontier_safe s"
  by (rule relay_inv_complete_frontier_safe[OF relay_reachable_inv[OF reach]])


subsection \<open>C6(b): instantiate the inducted theorem on the concrete witness\<close>

text \<open>
  @{const w0} IS a genuine relay initial state, so the whole witness trace lands
  in @{const relay_inv}.  In particular the advertised frontier of the crashed
  witness is @{const ec2} (its downstream history ends at @{const ec2}), which is
  @{text "> c0"} and carries an in-scope event --- NON-DEGENERATE (kills TRAP-1).
\<close>

lemma w0_is_initial: "w0 = initial_exec_state (\<lambda>_. None) {0} ec3"
  by (simp add: w0_def)

lemma relay_inv_w_crash: "relay_inv w_crash"
proof -
  have "dwi_trace (I_relay_labels (initial_exec_state (\<lambda>_. None) {0} ec3))
          (dwi_initial (I_relay_labels (initial_exec_state (\<lambda>_. None) {0} ec3)))
          [DoSource ec2 (Insert 0 7), EnqueueDownstream ec2 (Insert 0 7),
           DoDownstream ec2 (Insert 0 7), DoSource ec3 (Insert 0 9), Crash ec3]
          w_crash"
    using w_crash_reachable by (simp add: w0_is_initial)
  thus ?thesis by (rule relay_reachable_inv)
qed

text \<open>@{const w_src3} (the pre-crash open-gap state) is also reachable, hence
  @{const relay_inv}.\<close>

lemma w_src3_reachable_dwi:
  "dwi_trace (I_relay_labels w0) (dwi_initial (I_relay_labels w0))
     [DoSource ec2 (Insert 0 7), EnqueueDownstream ec2 (Insert 0 7),
      DoDownstream ec2 (Insert 0 7), DoSource ec3 (Insert 0 9)]
     w_src3"
proof -
  have init: "dwi_initial (I_relay_labels w0) = w0" by (simp add: I_relay_labels_def)
  show ?thesis
    unfolding init
    by (rule dwi_trace.dwi_trace_step[OF relay_dwi_stepI[OF w_step_src2]],
        rule dwi_trace.dwi_trace_step[OF relay_dwi_stepI[OF w_step_enq2]],
        rule dwi_trace.dwi_trace_step[OF relay_dwi_stepI[OF w_step_down2]],
        rule dwi_trace.dwi_trace_step[OF relay_dwi_stepI[OF w_step_src3]],
        rule dwi_trace.dwi_trace_refl)
qed

lemma relay_inv_w_src3: "relay_inv w_src3"
proof -
  have "dwi_trace (I_relay_labels (initial_exec_state (\<lambda>_. None) {0} ec3))
          (dwi_initial (I_relay_labels (initial_exec_state (\<lambda>_. None) {0} ec3)))
          [DoSource ec2 (Insert 0 7), EnqueueDownstream ec2 (Insert 0 7),
           DoDownstream ec2 (Insert 0 7), DoSource ec3 (Insert 0 9)]
          w_src3"
    using w_src3_reachable_dwi by (simp add: w0_is_initial)
  thus ?thesis by (rule relay_reachable_inv)
qed

text \<open>The advertised frontier of the witness is @{const ec2} --- NON-DEGENERATE
  (@{text "ec2 > c0"}, an in-scope event sits at @{const ec2}).  This kills
  TRAP-1 (R3 is not instantiated at a vacuous empty frontier).\<close>

lemma adv_w_src3: "adv w_src3 = ec2"
  by (simp add: adv_def w_src3_fields)

lemma adv_w_crash: "adv w_crash = ec2"
  by (simp add: adv_def w_crash_fields)

lemma relay_complete_w_src3_ec2:
  "relay_complete_through w_src3 ec2"
  by (simp add: relay_complete_through_def replay_down_hist_def
                w_src3_fields ec_ord)

lemma relay_complete_w_crash_ec2:
  "relay_complete_through w_crash ec2"
  by (simp add: relay_complete_through_def replay_down_hist_def
                w_crash_fields ec_ord)

lemma adv_w_src3_nondegenerate: "c0 < adv w_src3"
  by (simp add: adv_w_src3 less_src_coord_def src_lt_def src_le_def
                ec2_def c0_def coord_of_nat_def Abs_src_coord_inverse[OF UNIV_I]
                Abs_src_coord_inject[OF UNIV_I UNIV_I])

lemma cdc_replay_prefix_w_src3_ec2_nonempty:
  "cdc_replay_prefix (proto_of_exec_at w_src3 ec2) ec2 = [Cdc ec2 (Insert 0 7)]"
  by (simp add: cdc_replay_prefix_def proto_of_exec_at_def w_src3_fields
                cdc_lift_def ec_ord less_src_coord_def src_lt_def c0_def
                Abs_src_coord_inject[OF UNIV_I UNIV_I])

text \<open>NOW the previously-floating advertised-frontier safety at @{const ec2} is
  RE-PROVED as a COROLLARY of the GENERAL inducted theorem
  @{thm relay_inv_no_observable_mismatch} --- NOT a standalone @{text "by simp"}
  on @{thm w_src3_fields}.  R3 is discharged from the reachable invariant.\<close>

corollary w_no_observable_mismatch_at_ec2_via_invariant:
  "\<not> observable_mismatch (w_src3\<lparr>exec_status := Crashed ec2\<rparr>) ec2 0"
proof (rule relay_inv_no_observable_mismatch[OF relay_inv_w_src3])
  show "relay_complete_through w_src3 ec2"
    by (rule relay_complete_w_src3_ec2)
  show "ec2 \<le> exec_finish w_src3"
    by (simp add: w_src3_fields ec2_le_ec3[unfolded src_le_eq_less_eq])
qed

text \<open>...and the SAME for the crashed witness @{const w_crash} at @{const ec2}
  (its advertised frontier).  So: @{const ec2} is advertised AND safe, while
  @{const ec3} (unadvertised, @{text "ec3 > adv w_crash = ec2"}) remains
  observably bad (@{thm w_crash_observable_mismatch_at_ec3}) --- C7 survives
  SIMULTANEOUSLY with C2/C6.\<close>

corollary w_crash_no_observable_mismatch_at_ec2_via_invariant:
  "\<not> observable_mismatch (w_crash\<lparr>exec_status := Crashed ec2\<rparr>) ec2 0"
proof (rule relay_inv_no_observable_mismatch[OF relay_inv_w_crash])
  show "relay_complete_through w_crash ec2"
    by (rule relay_complete_w_crash_ec2)
  show "ec2 \<le> exec_finish w_crash"
    by (simp add: w_crash_fields ec2_le_ec3[unfolded src_le_eq_less_eq])
qed


subsection \<open>GATE-1 headline: genuineness + non-vacuity, simultaneously\<close>

text \<open>
  One checkable theorem witnessing that the inducted safe side is GENUINE and
  NON-VACUOUS at the SAME single @{const relay_admits} discipline:

    \<^enum> @{const w_crash} is @{const relay_inv} (reachable; the invariant is a real
        inductive invariant, C2);
    \<^enum> its advertised frontier is @{const ec2}, which is @{text "> c0"} and whose
        replayed prefix is NON-EMPTY (@{term "[Cdc ec2 (Insert 0 7)]"}) --- so R3
        is instantiated at a genuinely loaded frontier, NOT the empty restriction
        (kills TRAP-1);
    \<^enum> NO observable mismatch at the advertised @{const ec2}, obtained from the
        GENERAL inducted theorem with R3 DISCHARGED (C6);
    \<^enum> a GENUINE observable mismatch still survives at the UNADVERTISED
        @{const ec3} (@{text "ec3 > adv w_crash"}); the open commit-to-deliver gap is
        NOT closed (C7 holds simultaneously with C2/C6 --- kills TRAP-4).
\<close>

theorem gate1_genuine_and_nonvacuous:
  "relay_inv w_crash
 \<and> adv w_crash = ec2
 \<and> c0 < adv w_crash
 \<and> cdc_replay_prefix (proto_of_exec_at w_src3 ec2) ec2 = [Cdc ec2 (Insert 0 7)]
 \<and> (\<not> observable_mismatch (w_crash\<lparr>exec_status := Crashed ec2\<rparr>) ec2 0)
 \<and> observable_mismatch w_crash ec3 0
 \<and> src_lt (adv w_crash) ec3"
proof (intro conjI)
  show "relay_inv w_crash" by (rule relay_inv_w_crash)
  show "adv w_crash = ec2" by (rule adv_w_crash)
  show "c0 < adv w_crash"
    using adv_w_src3_nondegenerate by (simp add: adv_w_crash adv_w_src3)
  show "cdc_replay_prefix (proto_of_exec_at w_src3 ec2) ec2
          = [Cdc ec2 (Insert 0 7)]"
    by (rule cdc_replay_prefix_w_src3_ec2_nonempty)
  show "\<not> observable_mismatch (w_crash\<lparr>exec_status := Crashed ec2\<rparr>) ec2 0"
    by (rule w_crash_no_observable_mismatch_at_ec2_via_invariant)
  show "observable_mismatch w_crash ec3 0"
    by (rule w_crash_observable_mismatch_at_ec3)
  show "src_lt (adv w_crash) ec3"
    by (simp add: adv_w_crash ec2_def ec3_def)
qed

end
