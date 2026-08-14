(*  Title:       Dual_Write_Partition.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    The two-sided crash-divergence PARTITION for crash-closed faithful
    dual-write implementations.  This is the additive headline upgrade: it turns
    the separately-witnessed safe and unsafe classes into a single total
    biconditional over the whole domain of crash-closed refining implementations.

    A crash-closed faithful implementation can suffer a durable divergent crash
    (an observable source/downstream mismatch frozen by a crash, within the
    modelled interval) IF AND ONLY IF it can reach an EXPOSABLE scoped mismatch:
    a reachable state that disagrees with the committed-log image on a scoped key
    at some in-interval frontier c, and that is either still Running (so a crash
    can freeze the disagreement) or already Crashed exactly at c (so the
    disagreement is already observable).

    The exposability disjunct (Running or Crashed-at-c) is what makes the
    equivalence TOTAL: it absorbs, rather than excludes, the already-crashed
    diverging state that refutes the premise-free structured-gap characterization
    (crash_only_initial_mismatch_refutes_premise_free_characterization in
    Dual_Write_Characterization).  The forward direction is the real content and
    is exactly where crash-closure is load-bearing (a reachable Running scoped
    mismatch is crashable into an observable one); the backward direction hands
    the observable-mismatch witness over verbatim through the Crashed-at-c
    disjunct (a definitional unpacking of observable_mismatch).

    This theory then deepens the partition by showing the safe side is
    essentially TRIVIAL.  It certifies the unsafe pole in-file (the
    downstream-first stale-update canonical implementation), and proves that any
    faithful crash-closed implementation that ever performs an EFFECTIVE
    non-atomic source write on a monitored, in-interval key --- one that moves
    the key to a value the downstream does not yet hold --- reaches an exposable
    scoped mismatch, hence can suffer an observable bad crash.  The
    non-triviality boundary is effectiveness, not scope size (idempotent
    re-writes and all-None scopes stay safe), and the implication is
    one-directional, so no safe-iff-trivial biconditional is claimed.

    This theory also records a multi-event, refresh-free, DBLog-free positive
    inhabitant of the shared virtual_cut_state interface, complementing the
    single-event outbox_continuation_witness.

    A final subsumption section shows the structured source-first impossibility
    ladder, the separable non-atomic class, and the effective-source-write
    mechanism all factor through the single partition predicate (containment,
    not equivalence: the partition predicate is strictly more general).

    Additive: it imports the existing development and proves new facts only; no
    existing theory is modified.  Sorry-free and axiom-free over the imported
    base.
*)

theory Dual_Write_Partition
  imports Dual_Write_Characterization
begin

section \<open>The exposable reachable scoped-mismatch gap\<close>

text \<open>
  The right-hand side of the partition.  An implementation reaches an
  \emph{exposable} scoped mismatch when some reachable state disagrees with the
  committed-log image on a scoped key at an in-interval frontier \<open>c\<close>, and that
  state is either still \<open>Running\<close> (a live, crashable window) or already
  \<open>Crashed\<close> exactly at \<open>c\<close> (already observable).  This is precisely the shape a
  reachable observable bad crash supplies, which is why the biconditional below
  is total.
\<close>

definition implementation_reaches_exposable_scoped_mismatch
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "implementation_reaches_exposable_scoped_mismatch I \<longleftrightarrow>
     (\<exists>xs s c k.
        dwi_trace I (dwi_initial I) xs s
      \<and> c \<le> exec_finish (dwi_state I s)
      \<and> mismatch_at (proto_of_exec_at (dwi_state I s) c) c k
      \<and> (exec_status (dwi_state I s) = Running
         \<or> exec_status (dwi_state I s) = Crashed c))"


section \<open>Backward direction (a reachable bad crash reaches an exposable mismatch)\<close>

text \<open>
  Near-definitional: \<open>observable_mismatch\<close> already packages \<open>Crashed c\<close>,
  \<open>c \<le> exec_finish\<close>, and \<open>mismatch_at\<close> at \<open>c\<close>, so the reaching trace hands the
  exposable-mismatch witness over verbatim (with the \<open>Crashed\<close>-at-\<open>c\<close> disjunct).
  It is a direct weakening of \<open>observable_mismatch\<close>, not a contrapositive
  argument: the scoped alignment-safety lemmas
  (\<open>source_downstream_history_aligned_no_mismatch_at\<close> and friends) are the
  intuition for why alignment is safe, but they are not invoked in this proof.
\<close>

lemma reachable_observable_bad_crash_imp_reaches_exposable_scoped_mismatch:
  assumes "reachable_observable_bad_crash I xs c k s"
  shows "implementation_reaches_exposable_scoped_mismatch I"
proof -
  from assms have tr: "dwi_trace I (dwi_initial I) xs s"
      and obs: "observable_mismatch (dwi_state I s) c k"
    by (auto simp: reachable_observable_bad_crash_def)
  from obs have "exec_status (dwi_state I s) = Crashed c"
      and "c \<le> exec_finish (dwi_state I s)"
      and "mismatch_at (proto_of_exec_at (dwi_state I s) c) c k"
    by (auto simp: observable_mismatch_def)
  with tr show ?thesis
    by (auto simp: implementation_reaches_exposable_scoped_mismatch_def)
qed


section \<open>Forward direction (crash-closure exposes the gap)\<close>

text \<open>
  A \<open>Crash c\<close> step mirrors the canonical crash, so under refinement the reached
  \<open>dwi_state\<close> is the status-update of the source one.
\<close>

lemma dwi_crash_step_state:
  assumes refines: "dwi_refines_exec I"
      and step: "dwi_step I s (Crash c) s'"
  shows "dwi_state I s' = (dwi_state I s)\<lparr>exec_status := Crashed c\<rparr>"
proof -
  have "dw_exec_step (dwi_state I s) (Crash c) (dwi_state I s')"
    using refines step by (auto simp: dwi_refines_exec_def)
  thus ?thesis
    by (cases rule: dw_exec_step.cases) auto
qed

text \<open>
  The \<open>dwi\<close>-level lift of \<open>bad_crash_enabled_extend\<close>: from a reachable
  \<open>Running\<close> state whose \<open>dwi_state\<close> mismatches on a scoped key at \<open>c \<le> finish\<close>,
  crash-closure provides a \<open>Crash c\<close> step; refinement makes the reached state
  the status-update, on which the mismatch and the bound persist, yielding a
  reachable observable bad crash.  Crash-closure is load-bearing here.
\<close>

lemma crash_closed_running_bad_crash_enabled_imp_reachable_observable_bad_crash:
  assumes closed: "crash_closed_implementation I"
      and refines: "dwi_refines_exec I"
      and tr: "dwi_trace I (dwi_initial I) xs s"
      and run: "exec_status (dwi_state I s) = Running"
      and le_fin: "c \<le> exec_finish (dwi_state I s)"
      and mis: "mismatch_at (proto_of_exec_at (dwi_state I s) c) c k"
  shows "implementation_has_reachable_observable_bad_crash I"
proof -
  from closed tr run le_fin obtain s' where step: "dwi_step I s (Crash c) s'"
    by (auto simp: crash_closed_implementation_def)
  have st: "dwi_state I s' = (dwi_state I s)\<lparr>exec_status := Crashed c\<rparr>"
    by (rule dwi_crash_step_state[OF refines step])
  have tr': "dwi_trace I (dwi_initial I) (xs @ [Crash c]) s'"
    using tr
    by (rule dwi_trace_append[OF _ dwi_trace.dwi_trace_step
          [OF step dwi_trace.dwi_trace_refl]])
  have obs: "observable_mismatch (dwi_state I s') c k"
    using le_fin mis
    by (simp add: st observable_mismatch_def)
  have div: "diverges (proto_of_exec_at (dwi_state I s') c) c"
    by (rule observable_mismatch_imp_diverges[OF obs])
  from tr' obs div
  have "reachable_observable_bad_crash I (xs @ [Crash c]) c k s'"
    by (simp add: reachable_observable_bad_crash_def)
  thus ?thesis
    by (auto simp: implementation_has_reachable_observable_bad_crash_def)
qed

text \<open>
  The forward direction proper: case-split on the exposability disjunct.  A
  \<open>Running\<close> reached state uses crash-closure (previous lemma); a state already
  \<open>Crashed\<close> at exactly \<open>c\<close> is observable directly, with no further crash step.
\<close>

lemma crash_closed_reaches_scoped_mismatch_running_or_at_crash_imp_bad_crash:
  assumes closed: "crash_closed_implementation I"
      and refines: "dwi_refines_exec I"
      and tr: "dwi_trace I (dwi_initial I) xs s"
      and le_fin: "c \<le> exec_finish (dwi_state I s)"
      and mis: "mismatch_at (proto_of_exec_at (dwi_state I s) c) c k"
      and disj: "exec_status (dwi_state I s) = Running
                 \<or> exec_status (dwi_state I s) = Crashed c"
  shows "implementation_has_reachable_observable_bad_crash I"
  using disj
proof
  assume "exec_status (dwi_state I s) = Running"
  thus ?thesis
    by (rule crash_closed_running_bad_crash_enabled_imp_reachable_observable_bad_crash
        [OF closed refines tr _ le_fin mis])
next
  assume crashed: "exec_status (dwi_state I s) = Crashed c"
  have obs: "observable_mismatch (dwi_state I s) c k"
    using crashed le_fin mis by (simp add: observable_mismatch_def)
  have div: "diverges (proto_of_exec_at (dwi_state I s) c) c"
    by (rule observable_mismatch_imp_diverges[OF obs])
  from tr obs div
  have "reachable_observable_bad_crash I xs c k s"
    by (simp add: reachable_observable_bad_crash_def)
  thus ?thesis
    by (auto simp: implementation_has_reachable_observable_bad_crash_def)
qed


section \<open>The headline partition\<close>

text \<open>
  For a crash-closed faithful (refining) implementation, divergence-reachability
  and exposable-scoped-mismatch-reachability coincide.  This is a TOTAL
  biconditional over the whole domain: the exposability disjunct absorbs the
  already-crashed third class, so no implementation falls outside either side.
\<close>

theorem crash_closed_diverges_iff_reaches_exposable_scoped_mismatch:
  assumes closed: "crash_closed_implementation I"
      and refines: "dwi_refines_exec I"
  shows "implementation_has_reachable_observable_bad_crash I
         \<longleftrightarrow> implementation_reaches_exposable_scoped_mismatch I"
proof
  assume "implementation_has_reachable_observable_bad_crash I"
  then obtain xs c k s where "reachable_observable_bad_crash I xs c k s"
    by (auto simp: implementation_has_reachable_observable_bad_crash_def)
  thus "implementation_reaches_exposable_scoped_mismatch I"
    by (rule reachable_observable_bad_crash_imp_reaches_exposable_scoped_mismatch)
next
  assume "implementation_reaches_exposable_scoped_mismatch I"
  then obtain xs s c k where
      tr: "dwi_trace I (dwi_initial I) xs s"
    and le_fin: "c \<le> exec_finish (dwi_state I s)"
    and mis: "mismatch_at (proto_of_exec_at (dwi_state I s) c) c k"
    and disj: "exec_status (dwi_state I s) = Running
               \<or> exec_status (dwi_state I s) = Crashed c"
    by (auto simp: implementation_reaches_exposable_scoped_mismatch_def)
  show "implementation_has_reachable_observable_bad_crash I"
    by (rule crash_closed_reaches_scoped_mismatch_running_or_at_crash_imp_bad_crash
        [OF closed refines tr le_fin mis disj])
qed

text \<open>The contrapositive ``safe iff never diverges'' framing: a crash-closed
  faithful implementation never reaches an exposable scoped mismatch iff it can
  never suffer an observable bad crash.\<close>

theorem crash_closed_no_exposable_mismatch_iff_never_diverges:
  assumes closed: "crash_closed_implementation I"
      and refines: "dwi_refines_exec I"
  shows "(\<not> implementation_reaches_exposable_scoped_mismatch I)
         \<longleftrightarrow> (\<not> implementation_has_reachable_observable_bad_crash I)"
  using crash_closed_diverges_iff_reaches_exposable_scoped_mismatch[OF closed refines]
  by blast


section \<open>The safe side is inhabited at the implementation level (the trivial case)\<close>

text \<open>
  We exhibit a crash-closed faithful implementation that provably never reaches
  an observable bad crash: a canonical implementation started with an
  \emph{empty} scope.  (The unsafe pole is certified in-file in the next
  section, by the downstream-first stale-update canonical witness.)  Since \<open>mismatch_at\<close> requires the key to lie in the
  protocol scope, and the execution scope is invariant along every trace, no
  reachable state of an empty-scope implementation can exhibit a scoped
  mismatch, hence none can suffer an observable bad crash.  This shows the safe
  side of the partition is non-empty as an implementation property, not only at
  the bespoke-relation trace level.
\<close>

lemma dw_exec_trace_scope:
  assumes "dw_exec_trace s xs s'"
  shows "exec_scope s' = exec_scope s"
  using assms
  by (induction rule: dw_exec_trace.induct) (auto dest: dw_exec_step_scope)

lemma mismatch_at_proto_of_exec_imp_in_scope:
  assumes "mismatch_at (proto_of_exec_at s c) c k"
  shows "k \<in> exec_scope s"
  using assms by (simp add: mismatch_at_def proto_of_exec_at_def)

lemma canonical_empty_scope_no_reachable_observable_bad_crash:
  "\<not> implementation_has_reachable_observable_bad_crash
       (canonical_dw_implementation (initial_exec_state b {} fin))"
proof
  let ?I = "canonical_dw_implementation (initial_exec_state b {} fin)"
  assume "implementation_has_reachable_observable_bad_crash ?I"
  then obtain xs c k s where
    roc: "reachable_observable_bad_crash ?I xs c k s"
    by (auto simp: implementation_has_reachable_observable_bad_crash_def)
  from roc have tr: "dwi_trace ?I (dwi_initial ?I) xs s"
      and obs: "observable_mismatch (dwi_state ?I s) c k"
    by (auto simp: reachable_observable_bad_crash_def)
  have ex: "dw_exec_trace (dwi_state ?I (dwi_initial ?I)) xs (dwi_state ?I s)"
    by (rule dwi_trace_refines_exec[OF canonical_dw_implementation_refines_exec tr])
  have "exec_scope (dwi_state ?I s) = exec_scope (dwi_state ?I (dwi_initial ?I))"
    by (rule dw_exec_trace_scope[OF ex])
  hence scope_empty: "exec_scope (dwi_state ?I s) = {}"
    by (simp add: canonical_dw_implementation_def initial_exec_state_def)
  from obs have "mismatch_at (proto_of_exec_at (dwi_state ?I s) c) c k"
    by (auto simp: observable_mismatch_def)
  hence "k \<in> exec_scope (dwi_state ?I s)"
    by (rule mismatch_at_proto_of_exec_imp_in_scope)
  with scope_empty show False by simp
qed

theorem safe_implementation_has_no_reachable_observable_bad_crash:
  "\<exists>I :: ((nat, nat) dw_exec_state, nat, nat) dual_write_implementation.
      crash_closed_implementation I
    \<and> dwi_refines_exec I
    \<and> \<not> implementation_has_reachable_observable_bad_crash I"
proof (intro exI[of _ "canonical_dw_implementation
        (initial_exec_state ((\<lambda>_. None) :: nat \<rightharpoonup> nat) ({} :: nat set) c0)"] conjI)
  show "crash_closed_implementation (canonical_dw_implementation
          (initial_exec_state ((\<lambda>_. None) :: nat \<rightharpoonup> nat) ({} :: nat set) c0))"
    by (rule canonical_dw_implementation_crash_closed)
next
  show "dwi_refines_exec (canonical_dw_implementation
          (initial_exec_state ((\<lambda>_. None) :: nat \<rightharpoonup> nat) ({} :: nat set) c0))"
    by (rule canonical_dw_implementation_refines_exec)
next
  show "\<not> implementation_has_reachable_observable_bad_crash (canonical_dw_implementation
          (initial_exec_state ((\<lambda>_. None) :: nat \<rightharpoonup> nat) ({} :: nat set) c0))"
    by (rule canonical_empty_scope_no_reachable_observable_bad_crash)
qed


section \<open>Both poles certified, and the safe side is essentially trivial\<close>

text \<open>
  This section certifies the UNSAFE pole of the partition in-file (so both
  poles are now machine-checked here, not only the safe one), and then proves
  the deepening the partition was built for: the safe side is essentially
  trivial.  The structural root is that the small-step relation
  \<open>dw_exec_step\<close> has no atomic both-store write --- source and downstream are
  advanced by separate steps, with a crash enabled between them.  Hence any
  faithful crash-closed implementation that performs an \emph{effective}
  non-atomic source write on a monitored, in-interval key (one that moves the
  key to a value the downstream does not yet hold) reaches an exposable scoped
  mismatch, and can therefore suffer an observable bad crash.

  The non-triviality boundary is \emph{effectiveness}, not scope size: an
  implementation with a non-empty scope whose every monitored write is
  value-preserving (idempotent) or whose monitored keys carry no committed
  authority value keeps \<open>store2 = log_image\<close> on scope and stays safe.  The
  empty-scope witness above is the minimal representative of this trivial
  class.  The implication proved here is one-directional --- an effective
  non-atomic write forces unsafety, but unsafety can also arise without one
  (e.g. an initially-crashed mismatch) --- so no \<open>safe \<longleftrightarrow> trivial\<close>
  biconditional is claimed.
\<close>

subsection \<open>The unsafe pole, certified in-file\<close>

text \<open>
  The admissible separable non-atomic crash-closed class weakens to the plain
  class consumed by the Characterization bridge.
\<close>

lemma admissible_separable_non_atomic_crash_closed_imp_plain:
  assumes "admissible_separable_non_atomic_crash_closed_dual_write_implementation I"
  shows "separable_non_atomic_crash_closed_dual_write_implementation I"
proof -
  from assms have closed: "crash_closed_implementation I"
    and adm: "admissible_separable_non_atomic_dual_write_implementation I"
    by (simp_all add:
        admissible_separable_non_atomic_crash_closed_dual_write_implementation_def)
  from adm obtain C where
    "admissible_separable_non_atomic_dual_write_completion I C"
    by (auto simp: admissible_separable_non_atomic_dual_write_implementation_def)
  hence "separable_non_atomic_dual_write_completion I C"
    by (simp add: admissible_separable_non_atomic_dual_write_completion_def)
  hence "separable_non_atomic_dual_write_implementation I"
    by (auto simp: separable_non_atomic_dual_write_implementation_def)
  with closed show ?thesis
    by (simp add: separable_non_atomic_crash_closed_dual_write_implementation_def)
qed

lemma separable_non_atomic_crash_closed_imp_reachable_observable_bad_crash:
  assumes "separable_non_atomic_crash_closed_dual_write_implementation I"
  shows "implementation_has_reachable_observable_bad_crash I"
  using separable_non_atomic_crash_closed_imp_reconstructable_bad_crash[OF assms]
  by (auto simp: implementation_has_reconstructable_bad_crash_def
                 implementation_has_reachable_observable_bad_crash_def)

text \<open>The existing downstream-first stale-update canonical witness reaches an
  exposable scoped mismatch, so the TRUE-TRUE corner is inhabited in-file.\<close>

lemma downstream_first_stale_update_reaches_exposable_scoped_mismatch:
  "implementation_reaches_exposable_scoped_mismatch
     (canonical_dw_implementation downstream_first_stale_update_initial)"
proof -
  let ?I = "canonical_dw_implementation downstream_first_stale_update_initial"
  have closed: "crash_closed_implementation ?I"
    by (rule canonical_dw_implementation_crash_closed)
  have refines: "dwi_refines_exec ?I"
    by (rule canonical_dw_implementation_refines_exec)
  have plain: "separable_non_atomic_crash_closed_dual_write_implementation ?I"
    by (rule admissible_separable_non_atomic_crash_closed_imp_plain
        [OF downstream_first_stale_update_admissible_crash_closed_implementation])
  have bad: "implementation_has_reachable_observable_bad_crash ?I"
    by (rule separable_non_atomic_crash_closed_imp_reachable_observable_bad_crash[OF plain])
  show ?thesis
    using crash_closed_diverges_iff_reaches_exposable_scoped_mismatch[OF closed refines] bad
    by blast
qed

theorem true_true_corner_inhabited:
  "\<exists>I :: ((nat, nat) dw_exec_state, nat, nat) dual_write_implementation.
      crash_closed_implementation I
    \<and> dwi_refines_exec I
    \<and> implementation_reaches_exposable_scoped_mismatch I"
proof (intro exI conjI)
  show "crash_closed_implementation
          (canonical_dw_implementation downstream_first_stale_update_initial)"
    by (rule canonical_dw_implementation_crash_closed)
next
  show "dwi_refines_exec
          (canonical_dw_implementation downstream_first_stale_update_initial)"
    by (rule canonical_dw_implementation_refines_exec)
next
  show "implementation_reaches_exposable_scoped_mismatch
          (canonical_dw_implementation downstream_first_stale_update_initial)"
    by (rule downstream_first_stale_update_reaches_exposable_scoped_mismatch)
qed

subsection \<open>Genuine non-atomic dual writes reach an exposable mismatch\<close>

text \<open>
  Reuse bridge: the pre-existing predicate for a genuine non-atomic, in-scope,
  crash-closed dual write already implies an exposable scoped mismatch.  This is
  one-directional only; the converse is false, witnessed by the
  already-crashed-initial-mismatch class in @{theory_text Dual_Write_Characterization}.
\<close>

corollary separable_non_atomic_reaches_exposable_scoped_mismatch:
  assumes impl: "separable_non_atomic_crash_closed_dual_write_implementation I"
  shows "implementation_reaches_exposable_scoped_mismatch I"
proof -
  from impl have closed: "crash_closed_implementation I"
    by (simp add: separable_non_atomic_crash_closed_dual_write_implementation_def)
  from impl obtain C side where side: "separated_completion_first_side I C side"
    by (auto simp: separable_non_atomic_crash_closed_dual_write_implementation_def
                   separable_non_atomic_dual_write_implementation_def
                   separable_non_atomic_dual_write_completion_def)
  have refines: "dwi_refines_exec I"
    by (rule separated_completion_first_side_refines[OF side])
  have bad: "implementation_has_reachable_observable_bad_crash I"
    by (rule separable_non_atomic_crash_closed_imp_reachable_observable_bad_crash[OF impl])
  show ?thesis
    using crash_closed_diverges_iff_reaches_exposable_scoped_mismatch[OF closed refines] bad
    by blast
qed

subsection \<open>The self-contained \<open>do_source\<close> mechanism\<close>

text \<open>
  A faithful \<open>DoSource\<close> step changes only the source history of the
  projection, and the source state must have been \<open>Running\<close>.
\<close>

lemma dwi_do_source_state:
  assumes refines: "dwi_refines_exec I"
      and step: "dwi_step I s (DoSource c e) s'"
  shows "dwi_state I s'
           = (dwi_state I s)\<lparr>exec_src_hist := exec_src_hist (dwi_state I s) @ [(c, e)]\<rparr>"
    and "exec_status (dwi_state I s) = Running"
proof -
  have estep: "dw_exec_step (dwi_state I s) (DoSource c e) (dwi_state I s')"
    using refines step by (simp add: dwi_refines_exec_def)
  show "dwi_state I s'
          = (dwi_state I s)\<lparr>exec_src_hist := exec_src_hist (dwi_state I s) @ [(c, e)]\<rparr>"
    using estep by (cases rule: dw_exec_step.cases) auto
  show "exec_status (dwi_state I s) = Running"
    using estep by (cases rule: dw_exec_step.cases) auto
qed

text \<open>
  The effect of that source write on \<open>mismatch_at\<close> at the just-written
  frontier: the new source value differs from the (unchanged) downstream value
  on the scoped key, so the post-step state mismatches there.
\<close>

lemma do_source_creates_mismatch_at:
  assumes refines: "dwi_refines_exec I"
      and step: "dwi_step I s (DoSource c e) s'"
      and key: "key_of e = k"
      and inscope: "k \<in> exec_scope (dwi_state I s)"
      and le_fin: "c \<le> exec_finish (dwi_state I s)"
      and effective:
        "Src (exec_base (dwi_state I s)) (exec_down_hist (dwi_state I s)) c k
           \<noteq> event_result e"
  shows "mismatch_at (proto_of_exec_at (dwi_state I s') c) c k"
proof -
  have s'eq: "dwi_state I s'
           = (dwi_state I s)\<lparr>exec_src_hist := exec_src_hist (dwi_state I s) @ [(c, e)]\<rparr>"
    by (rule dwi_do_source_state(1)[OF refines step])
  have src_side:
    "Src (exec_base (dwi_state I s'))
         (exec_src_hist (dwi_state I s')) c k = event_result e"
    using key le_fin by (simp add: s'eq Src_snoc_event_at_key)
  have down_side:
    "Src (exec_base (dwi_state I s'))
         (exec_down_hist (dwi_state I s')) c k
       = Src (exec_base (dwi_state I s))
             (exec_down_hist (dwi_state I s)) c k"
    by (simp add: s'eq)
  have scope': "k \<in> exec_scope (dwi_state I s')"
    using inscope by (simp add: s'eq)
  show ?thesis
    using effective src_side down_side scope'
    by (simp add: mismatch_at_def proto_of_exec_at_def
                  store2_of_exec_def log_image_def restrict_def)
qed

text \<open>
  The non-triviality predicate: from a reachable state, the projection performs
  a single faithful \<open>DoSource\<close> of an effective (value-changing relative to what
  the downstream already holds), in-scope, in-interval event.
\<close>

definition performs_effective_nonatomic_source_write
  :: "('s, 'k, 'v) dual_write_implementation \<Rightarrow> bool"
where
  "performs_effective_nonatomic_source_write I \<longleftrightarrow>
     (\<exists>xs s s' c e.
        dwi_trace I (dwi_initial I) xs s
      \<and> dwi_step I s (DoSource c e) s'
      \<and> key_of e \<in> exec_scope (dwi_state I s)
      \<and> c \<le> exec_finish (dwi_state I s)
      \<and> Src (exec_base (dwi_state I s)) (exec_down_hist (dwi_state I s)) c (key_of e)
          \<noteq> event_result e)"

text \<open>
  The core mechanism theorem: the reached post-source state is itself the
  exposable \<open>Running\<close> witness, so no extra crash is needed for the right-hand
  side of the partition.
\<close>

theorem effective_nonatomic_source_write_reaches_exposable_scoped_mismatch:
  assumes refines: "dwi_refines_exec I"
      and trig: "performs_effective_nonatomic_source_write I"
  shows "implementation_reaches_exposable_scoped_mismatch I"
proof -
  from trig obtain xs s s' c e where
      tr: "dwi_trace I (dwi_initial I) xs s"
    and step: "dwi_step I s (DoSource c e) s'"
    and inscope: "key_of e \<in> exec_scope (dwi_state I s)"
    and le_fin: "c \<le> exec_finish (dwi_state I s)"
    and eff: "Src (exec_base (dwi_state I s)) (exec_down_hist (dwi_state I s)) c (key_of e)
                \<noteq> event_result e"
    by (auto simp: performs_effective_nonatomic_source_write_def)
  have s'eq: "dwi_state I s'
           = (dwi_state I s)\<lparr>exec_src_hist := exec_src_hist (dwi_state I s) @ [(c, e)]\<rparr>"
    by (rule dwi_do_source_state(1)[OF refines step])
  have runs: "exec_status (dwi_state I s) = Running"
    by (rule dwi_do_source_state(2)[OF refines step])
  have run': "exec_status (dwi_state I s') = Running"
    by (simp add: s'eq runs)
  have fin': "c \<le> exec_finish (dwi_state I s')"
    using le_fin by (simp add: s'eq)
  have mis': "mismatch_at (proto_of_exec_at (dwi_state I s') c) c (key_of e)"
    by (rule do_source_creates_mismatch_at[OF refines step refl inscope le_fin eff])
  have tr': "dwi_trace I (dwi_initial I) (xs @ [DoSource c e]) s'"
    by (rule dwi_trace_append
        [OF tr dwi_trace.dwi_trace_step[OF step dwi_trace.dwi_trace_refl]])
  from tr' fin' mis' run'
  show ?thesis
    by (auto simp: implementation_reaches_exposable_scoped_mismatch_def)
qed

text \<open>Headline corollary: an effective non-atomic source write can fail.\<close>

corollary effective_nonatomic_source_write_imp_reachable_observable_bad_crash:
  assumes closed: "crash_closed_implementation I"
      and refines: "dwi_refines_exec I"
      and trig: "performs_effective_nonatomic_source_write I"
  shows "implementation_has_reachable_observable_bad_crash I"
  using effective_nonatomic_source_write_reaches_exposable_scoped_mismatch[OF refines trig]
        crash_closed_diverges_iff_reaches_exposable_scoped_mismatch[OF closed refines]
  by blast

text \<open>
  Safe-side characterization (one-directional): a safe faithful crash-closed
  implementation performs no effective non-atomic source write --- it never
  lets the two stores disagree on a monitored in-interval key.
\<close>

corollary safe_imp_no_effective_nonatomic_source_write:
  assumes closed: "crash_closed_implementation I"
      and refines: "dwi_refines_exec I"
      and safe: "\<not> implementation_has_reachable_observable_bad_crash I"
  shows "\<not> performs_effective_nonatomic_source_write I"
  using effective_nonatomic_source_write_imp_reachable_observable_bad_crash[OF closed refines] safe
  by blast


section \<open>A multi-event DBLog-free positive instance of \<open>virtual_cut_state\<close>\<close>

text \<open>
  A two-event, refresh-free CDC outbox over the source history
  \<open>[(ec2, Insert 0 7), (ec3, Insert 1 9)]\<close> on scope \<open>{0, 1}\<close>.  It certifies a
  virtual cut at frontier \<open>ec4\<close> through \<open>virtual_cut_certifies_outbox\<close>, and the
  continued replay reconstructs both keys (\<open>Apply\<close> gives \<open>Some 7\<close> at key \<open>0\<close> and
  \<open>Some 9\<close> at key \<open>1\<close>).  No DBLog object is used, so the shared interface has a
  second, multi-event, non-DBLog inhabitant alongside the single-event
  \<open>outbox_continuation_witness\<close> and the DBLog instance in the companion session.
\<close>

definition wH2 :: "(nat, nat) src_history" where
  "wH2 = [(ec2, Insert 0 7), (ec3, Insert 1 9)]"

lemma wH2_wellformed: "wellformed_src_history wH2"
  unfolding wH2_def wellformed_src_history_def source_pos_order_def
  by (auto simp: ec1_def ec2_def ec3_def ec4_def c0_eq_coord_of_nat_0 less_Suc_eq)

lemma w2_segment:
  "cdc_segment_between wH2 {0, 1} c0 ec4
     [Cdc ec2 (Insert 0 7), Cdc ec3 (Insert 1 9)]"
  by (simp add: cdc_segment_between_def wH2_def cdc_lift_def
                ec1_def ec2_def ec3_def ec4_def c0_eq_coord_of_nat_0)

theorem multi_event_outbox_virtual_cut_witness:
  "cdc_only [Cdc ec2 (Insert 0 7), Cdc ec3 (Insert (1::nat) (9::nat))]
   \<and> virtual_cut_state (\<lambda>_. None)
       [Cdc ec2 (Insert 0 7), Cdc ec3 (Insert (1::nat) (9::nat))]
       {0, 1} ec4 wH2"
  by (rule virtual_cut_certifies_outbox[OF wH2_wellformed w2_segment])

lemma multi_event_outbox_reconstructs_both_keys:
  "Apply [Cdc ec2 (Insert 0 7), Cdc ec3 (Insert 1 9)] (0::nat) = Some 7
 \<and> Apply [Cdc ec2 (Insert 0 7), Cdc ec3 (Insert 1 9)] (1::nat) = Some 9"
  by (simp add: Apply_def)


section \<open>Subsumption: the structured unsafe ladder collapses to the partition\<close>

text \<open>
  The development proves many structured impossibility theorems of the shape
  \<open>\<dots>_has_concrete_bad_crash_execution\<close>: from some source-first window / gap /
  capability premise each produces a \<open>dwi_trace\<close> reaching a state that satisfies
  \<open>bad_crash_execution_for_gap\<close>.  That predicate ALREADY packages an
  \<open>observable_mismatch\<close> and \<open>diverges\<close> at the gap's crash frontier and key, so a
  single uniform \emph{gap-bridge} sends \emph{every} theorem of this shape ---
  the whole source-first ladder, not just the entries named below --- to
  \<open>implementation_has_reachable_observable_bad_crash\<close>, which, for crash-closed
  faithful implementations, the partition characterizes as
  \<open>implementation_reaches_exposable_scoped_mismatch\<close>.  The separable non-atomic
  class concludes a \emph{different} bad-crash predicate
  (\<open>separated_completion\<dots>\<close>) and reaches the same target through its own bridge;
  the effective-source-write mechanism is a third route.  So these converge on
  the one partition predicate --- convergence of target via the uniform
  gap-bridge plus two further bridges, not a single bridge for all.

  This is CONTAINMENT, not equivalence: the partition predicate is strictly more
  general than the separable non-atomic route --- it is inhabited by the
  already-crashed class, which reaches an exposable scoped mismatch yet carries
  no source-first separated-completion structure
  (\<open>crash_only_initial_mismatch_not_separable\<close>); the effective-\<open>do_source\<close>
  route is expected to inhabit it as well, but is not separately exhibited here.
  So the subsumption organises the ladder under the partition rather than
  collapsing the two into one class.  The named disjunction below is a representative bundle: the uniform
  gap-bridge already covers the whole source-first family, and
  \<open>source_first_gap_crash_admissible_implementation\<close> is its most general member.
\<close>

subsection \<open>The uniform bridge\<close>

text \<open>Any \<open>bad_crash_execution_for_gap\<close> reached by a \<open>dwi_trace\<close> is a reachable
  observable bad crash --- the gap's own crash frontier and key are the witness.\<close>

lemma bad_crash_execution_for_gap_imp_has_reachable_observable_bad_crash:
  assumes tr: "dwi_trace I (dwi_initial I) xs s"
      and bad: "bad_crash_execution_for_gap G (dwi_state I s)"
  shows "implementation_has_reachable_observable_bad_crash I"
proof -
  from bad have
      obs: "observable_mismatch (dwi_state I s) (osg_crash_at G) (osg_key G)"
    and div: "diverges (proto_of_exec_at (dwi_state I s) (osg_crash_at G)) (osg_crash_at G)"
    by (auto simp: bad_crash_execution_for_gap_def)
  from tr obs div
  have "reachable_observable_bad_crash I xs (osg_crash_at G) (osg_key G) s"
    by (auto simp: reachable_observable_bad_crash_def)
  thus ?thesis
    by (auto simp: implementation_has_reachable_observable_bad_crash_def)
qed

subsection \<open>Per-route bridges\<close>

lemma source_first_gap_crash_admissible_imp_bad_crash:
  assumes "source_first_gap_crash_admissible_implementation I"
  shows "implementation_has_reachable_observable_bad_crash I"
proof -
  from source_first_gap_crash_admissible_implementation_has_concrete_bad_crash_execution[OF assms]
  obtain W s where
      "dwi_trace I (dwi_initial I) (implementation_gap_crash_labels W) s"
    and "bad_crash_execution_for_gap (operational_gap_of_implementation_gap I W) (dwi_state I s)"
    by blast
  thus ?thesis
    by (rule bad_crash_execution_for_gap_imp_has_reachable_observable_bad_crash)
qed

lemma no_shared_commit_source_first_crash_admissible_imp_bad_crash:
  assumes "no_shared_commit_source_first_crash_admissible_implementation I"
  shows "implementation_has_reachable_observable_bad_crash I"
proof -
  from no_shared_commit_source_first_crash_admissible_implementation_has_concrete_bad_crash_execution[OF assms]
  obtain W s where
      "dwi_trace I (dwi_initial I)
         (implementation_gap_crash_labels (implementation_gap_of_no_shared_commit_window W)) s"
    and "bad_crash_execution_for_gap
           (operational_gap_of_implementation_gap I
             (implementation_gap_of_no_shared_commit_window W)) (dwi_state I s)"
    by blast
  thus ?thesis
    by (rule bad_crash_execution_for_gap_imp_has_reachable_observable_bad_crash)
qed

lemma non_atomic_no_shared_commit_crash_admissible_imp_bad_crash:
  assumes "non_atomic_no_shared_commit_crash_admissible_implementation I"
  shows "implementation_has_reachable_observable_bad_crash I"
proof -
  from non_atomic_no_shared_commit_crash_admissible_implementation_has_concrete_bad_crash_execution[OF assms]
  obtain W s where
      "dwi_trace I (dwi_initial I) (implementation_gap_crash_labels W) s"
    and "bad_crash_execution_for_gap (operational_gap_of_implementation_gap I W) (dwi_state I s)"
    by blast
  thus ?thesis
    by (rule bad_crash_execution_for_gap_imp_has_reachable_observable_bad_crash)
qed

lemma adversarial_pending_intent_crash_admissible_imp_bad_crash:
  assumes "adversarial_pending_intent_crash_admissible_implementation I"
  shows "implementation_has_reachable_observable_bad_crash I"
proof -
  from adversarial_pending_intent_crash_admissible_implementation_has_concrete_bad_crash_execution[OF assms]
  obtain W s where
      "dwi_trace I (dwi_initial I) (implementation_gap_crash_labels W) s"
    and "bad_crash_execution_for_gap (operational_gap_of_implementation_gap I W) (dwi_state I s)"
    by blast
  thus ?thesis
    by (rule bad_crash_execution_for_gap_imp_has_reachable_observable_bad_crash)
qed

lemma source_first_separated_completion_crash_closed_imp_bad_crash:
  assumes "source_first_separated_completion_crash_closed_implementation I"
  shows "implementation_has_reachable_observable_bad_crash I"
proof -
  from source_first_separated_completion_crash_closed_implementation_has_concrete_bad_crash_execution[OF assms]
  obtain C G s where
      "dwi_trace I (dwi_initial I) (implementation_gap_crash_labels G) s"
    and "bad_crash_execution_for_gap (operational_gap_of_implementation_gap I G) (dwi_state I s)"
    by blast
  thus ?thesis
    by (rule bad_crash_execution_for_gap_imp_has_reachable_observable_bad_crash)
qed

subsection \<open>The capstone: every structured route factors through the partition\<close>

theorem source_first_structured_routes_subsumed:
  assumes "source_first_gap_crash_admissible_implementation I
           \<or> no_shared_commit_source_first_crash_admissible_implementation I
           \<or> non_atomic_no_shared_commit_crash_admissible_implementation I
           \<or> adversarial_pending_intent_crash_admissible_implementation I
           \<or> source_first_separated_completion_crash_closed_implementation I"
  shows "implementation_has_reachable_observable_bad_crash I"
  using assms
  by (auto intro: source_first_gap_crash_admissible_imp_bad_crash
                  no_shared_commit_source_first_crash_admissible_imp_bad_crash
                  non_atomic_no_shared_commit_crash_admissible_imp_bad_crash
                  adversarial_pending_intent_crash_admissible_imp_bad_crash
                  source_first_separated_completion_crash_closed_imp_bad_crash)

text \<open>
  For a crash-closed faithful implementation, the principal unsafe routes reach
  the single partition predicate \<open>implementation_reaches_exposable_scoped_mismatch\<close>:
  five named source-first structured classes (the uniform gap-bridge above covers
  the rest of the source-first ladder), the separable non-atomic class, and the
  effective-source-write mechanism.  Five of the seven enumerated routes are
  inhabited by the development's canonical witnesses (the source-first capability
  classes via the crash-closed stale-update witness, the separable class via the
  downstream-first witness); the separated-completion route is a structural
  premise class and the effective-source-write route is the safe-boundary
  mechanism, both included for the convergence statement rather than as
  separately exhibited inhabitants.
\<close>

corollary structured_routes_reach_exposable_scoped_mismatch:
  assumes closed: "crash_closed_implementation I"
      and refines: "dwi_refines_exec I"
      and route: "source_first_gap_crash_admissible_implementation I
           \<or> no_shared_commit_source_first_crash_admissible_implementation I
           \<or> non_atomic_no_shared_commit_crash_admissible_implementation I
           \<or> adversarial_pending_intent_crash_admissible_implementation I
           \<or> source_first_separated_completion_crash_closed_implementation I
           \<or> separable_non_atomic_crash_closed_dual_write_implementation I
           \<or> performs_effective_nonatomic_source_write I"
  shows "implementation_reaches_exposable_scoped_mismatch I"
proof -
  have "implementation_has_reachable_observable_bad_crash I"
    using route
    by (auto intro: source_first_structured_routes_subsumed
                    separable_non_atomic_crash_closed_imp_reachable_observable_bad_crash
                    effective_nonatomic_source_write_imp_reachable_observable_bad_crash
                       [OF closed refines])
  thus ?thesis
    using crash_closed_diverges_iff_reaches_exposable_scoped_mismatch[OF closed refines]
    by blast
qed

end
