(*  Title:       Dual_Write_Effect_Recovery_Class.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    The absorbing-atomic-recovery class (theory-backlog item K, slice K1)
    --- an additive post-freeze slice under the freeze's own protocol: no
    landed statement, proof, definition, name, import, or session-DAG
    change to the frozen corpus.

    THIS THEORY IS BRANCH-NEUTRAL BY DESIGN: it imports Main alone ---
    neither effect-machine branch sits in its import cone (the terminal
    and cyclic interpretation theories of this wave import IT, one per
    branch, so no theory ever sits downstream of both branches).  What
    it states is the abstract residue of the landed section-17 proof
    (Dual_Write_Effect_Terminal_Inexpressibility, cited here as prose
    only): a locale of four assumptions --- initial ledger/anchor sync,
    an absorbed status no transition exits, atomically-born divergence
    (any step from a synced non-absorbed state either preserves sync or
    lands absorbed in that same step), and crashed-is-not-absorbed ---
    under which NO pair of reachable crashed states with equal cores
    and divergent observations exists (no_divergent_crashed_pair).

    THE LAW IS ONE-DIRECTIONAL, PLUS NECESSITY CONTROLS --- never a
    two-directional statement.  Class membership rules the pair out;
    the two toy structures below show each of the two load-bearing
    assumptions is necessary for that conclusion (drop exactly one and
    the pair becomes reachable); and membership FAILURE does not imply
    pair-reachability --- a fire rule that also writes a core scratch
    field violates atomic_divergence while keeping all crashed cores
    unequal, so no equal-core pair is ever reachable (the design study
    records this counterexample; it is why no converse is stated or
    suggested anywhere in this theory).

    THE TWO NECESSITY CONTROLS ARE ABSTRACT TOYS BY DESIGN.  N1 (one
    extra rule exits the absorbed status) is the abstract skeleton of
    the cyclic machine's Resume pole --- its real-machine realization
    is the cyclic-branch violation theory of this wave, packaging the
    landed dwe_resume evidence and the landed dilemma pair.  N2
    (per-entry recovery that never absorbs) is the abstract skeleton of
    the per-entry-fire pole; its natural-machine reading deliberately
    STAYS design prose (building a terminal-side fire machine would
    re-open a narrative surface the design study prices and declines),
    so the toy is the honest machine-checked control.

    "ABSORBED" AND "ABSORBING" ARE CLASS-SCOPED WORDS HERE: absorbing
    is an ASSUMPTION defining membership, discharged by the terminal
    machine and provably violated by the cyclic machine (that violation
    is the point of the cyclic-branch certificate).  No whole-trace
    absorption claim about any concrete machine is made in this theory.

    PROVENANCE: theory-backlog item K
    (paper/dual_write/theory_backlog/BACKLOG_EXPLORATION.md section 6,
    flipped to conditional candidate by the design spike
    paper/dual_write/theory_backlog/KL_LOCALE_DESIGN.md, whose sections
    2 and 5 pin the locale and the not-an-iff fence); the proofs port
    the banked green probe
    paper/dual_write/theory_backlog/k_probe/K_Locale_Probe.thy.

    In-source ML oracle gates are STRIPPED at landing: oracle-freedom
    is certified by scratch-side per-slice gate sessions with
    confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Recovery_Class
  imports Main
begin

section \<open>The class: absorbing atomic recovery\<close>

text \<open>
  The seven parameters are the abstract residue of the landed
  section-17 vocabulary (the intended readings, recorded as prose):
  @{term step} is ONE unified transition relation (labels and
  reconciles together); @{term inits} is an init FAMILY --- a set, so
  the whole machine-parameter family enters at once and the pair law
  below is cross-parameter for free; @{term core} projects the durable
  store; @{term obs} is the divergence observable (the ledger's payload
  projection, on the landed machines); @{term anchor} computes the
  observable from the core alone (the durable downstream history);
  @{term absorbed} is the terminal recovery status; @{term crashed} is
  the status every recovery transition fires from.

  The four assumptions, in machine terms: the initial ledger agrees
  with its anchor; no transition of ANY kind exits the absorbed status
  (the class assumption @{text absorbing}); any step from a synced,
  non-absorbed state either preserves sync or lands absorbed IN THAT
  SAME step (@{text atomic_divergence} --- heal-and-emit happen
  together, so there is no state where divergence already exists while
  recovery is still in progress at a non-absorbed status); and a
  crashed state is never absorbed.  "Single divergence source" is not a
  class-stateable rule count --- @{text atomic_divergence} is its
  honest abstract form (the design study, section 1).
\<close>

locale absorbing_atomic_recovery =
  fixes step     :: "'t \<Rightarrow> 'a \<Rightarrow> 't \<Rightarrow> bool"   \<comment> \<open>one unified transition relation (labels + reconciles)\<close>
    and inits    :: "'t set"                              \<comment> \<open>the init FAMILY: cross-parameter = all machine parameters at once\<close>
    and core     :: "'t \<Rightarrow> 's"                       \<comment> \<open>durable-store projection\<close>
    and obs      :: "'t \<Rightarrow> 'o"                       \<comment> \<open>divergence observable\<close>
    and anchor   :: "'s \<Rightarrow> 'o"                       \<comment> \<open>core-determined anchor\<close>
    and absorbed :: "'t \<Rightarrow> bool"                     \<comment> \<open>terminal recovery status\<close>
    and crashed  :: "'t \<Rightarrow> bool"                     \<comment> \<open>the status recovery fires from\<close>
  assumes init_sync:
      "t \<in> inits \<Longrightarrow> obs t = anchor (core t)"
    and absorbing:
      "\<lbrakk>step t a t'; absorbed t\<rbrakk> \<Longrightarrow> absorbed t'"
    and atomic_divergence:
      "\<lbrakk>step t a t'; \<not> absorbed t; obs t = anchor (core t)\<rbrakk>
         \<Longrightarrow> obs t' = anchor (core t') \<or> absorbed t'"
    and crashed_not_absorbed:
      "crashed t \<Longrightarrow> \<not> absorbed t"
begin

inductive reach :: "'t \<Rightarrow> bool" where
  reach_init: "t \<in> inits \<Longrightarrow> reach t"
| reach_step: "reach t \<Longrightarrow> step t a t' \<Longrightarrow> reach t'"

text \<open>
  The disjunctive invariant that carries the law: every reachable state
  is either still anchored or already absorbed.  This is the abstract
  form of the landed guarded invariant @{text pre_recovery_sync} (its
  contrapositive bookkeeping happens once, here, instead of inside each
  machine proof).
\<close>

definition live_sync :: "'t \<Rightarrow> bool" where
  "live_sync t \<longleftrightarrow> obs t = anchor (core t) \<or> absorbed t"

lemma reach_live_sync:
  assumes "reach t"
  shows "live_sync t"
  using assms
proof (induction rule: reach.induct)
  case (reach_init t)
  then show ?case by (simp add: live_sync_def init_sync)
next
  case (reach_step t a t')
  then show ?case
    unfolding live_sync_def
    using absorbing atomic_divergence by blast
qed

theorem crashed_obs_anchored:
  assumes "reach t" and "crashed t"
  shows "obs t = anchor (core t)"
  using reach_live_sync[OF assms(1)] crashed_not_absorbed[OF assms(2)]
  by (simp add: live_sync_def)

text \<open>
  THE CLASS LAW, negative-existence form: within the class, no pair of
  reachable crashed states has equal cores and divergent observations
  --- the certificate shape of the landed dilemma pair is unreachable
  at crashed states, for EVERY member of the class at once.  The
  \<open>\<forall>\<close>-quantification ranges over the named premise class on the
  inexpressibility side ONLY; no defeat theorem of the landed corpus is
  restated, strengthened, or generalized by it (those stay
  exists-system, on their own branch).
\<close>

theorem no_divergent_crashed_pair:
  "\<not> (\<exists>t t'. reach t \<and> reach t'
            \<and> crashed t \<and> crashed t'
            \<and> core t = core t'
            \<and> obs t \<noteq> obs t')"
  using crashed_obs_anchored by metis

end

section \<open>Verbatim-discharge adapter: the landed guarded-invariant shape\<close>

text \<open>
  The landed terminal step-preservation lemma
  (@{text dwe_step_pre_recovery_sync}) has the guarded shape
  "step + (not-absorbed implies sync) preserved"; the landed reconcile
  lemma (@{text emitting_reconcile_status_recovered}) lands absorbed.
  This derived rule certifies that the guarded shape discharges
  @{text atomic_divergence} with no rework: the terminal interpretation
  theory of this wave consumes it verbatim.
\<close>

lemma atomic_divergence_from_guarded:
  assumes guarded:
    "\<And>t a t'. step t a t' \<Longrightarrow>
       (\<not> absorbed t \<longrightarrow> obs t = anchor (core t)) \<Longrightarrow>
       (\<not> absorbed t' \<longrightarrow> obs t' = anchor (core t'))"
  shows "\<lbrakk>step t a t'; \<not> absorbed t; obs t = anchor (core t)\<rbrakk>
           \<Longrightarrow> obs t' = anchor (core t') \<or> absorbed t'"
  using guarded by blast

section \<open>Necessity control N1: dropping only \<open>absorbing\<close> (the resume pole)\<close>

text \<open>
  A four-rule toy: run, crash, reconcile (emit one unit and absorb),
  and ONE extra rule that exits the absorbed status.  All other class
  assumptions hold (@{text n1_sane_init}, @{text n1_atomic_holds},
  @{text n1_crashed_not_absorbed}); @{text absorbing} alone fails
  (@{text n1_absorbing_fails}); and an equal-core, observation-divergent
  crashed pair is reachable (@{text n1_pair_reachable}) --- the core is
  the one-point type, so all cores are equal by construction and the
  toy isolates exactly the observation divergence.  This is the
  abstract skeleton of the cyclic machine's Resume rule; the
  real-machine realization (landed @{text dwe_resume} evidence plus the landed
  dilemma pair) is packaged by the cyclic-branch violation theory of
  this wave.
\<close>

datatype n1_mode = N1Run | N1Crash | N1Rec

datatype n1_act = N1Go | N1Reconcile | N1Resume | N1CrashA

fun n1_step :: "n1_mode \<times> nat \<Rightarrow> n1_act \<Rightarrow> n1_mode \<times> nat \<Rightarrow> bool" where
  "n1_step (N1Run, n)   N1CrashA    s' = (s' = (N1Crash, n))"
| "n1_step (N1Crash, n) N1Reconcile s' = (s' = (N1Rec, Suc n))"
| "n1_step (N1Rec, n)   N1Resume    s' = (s' = (N1Run, n))"
| "n1_step _ _ _ = False"

definition n1_obs :: "n1_mode \<times> nat \<Rightarrow> nat" where "n1_obs = snd"
definition n1_core :: "n1_mode \<times> nat \<Rightarrow> unit" where "n1_core _ = ()"
definition n1_anchor :: "unit \<Rightarrow> nat" where "n1_anchor _ = 0"
definition n1_absorbed :: "n1_mode \<times> nat \<Rightarrow> bool" where
  "n1_absorbed s \<longleftrightarrow> fst s = N1Rec"
definition n1_crashed :: "n1_mode \<times> nat \<Rightarrow> bool" where
  "n1_crashed s \<longleftrightarrow> fst s = N1Crash"

inductive n1_reach :: "n1_mode \<times> nat \<Rightarrow> bool" where
  "n1_reach (N1Run, 0)"
| "n1_reach s \<Longrightarrow> n1_step s a s' \<Longrightarrow> n1_reach s'"

lemma n1_sane_init: "n1_obs (N1Run, 0) = n1_anchor (n1_core (N1Run, 0))"
  by (simp add: n1_obs_def n1_anchor_def)

lemma n1_atomic_holds:
  "\<lbrakk>n1_step s a s'; \<not> n1_absorbed s; n1_obs s = n1_anchor (n1_core s)\<rbrakk>
     \<Longrightarrow> n1_obs s' = n1_anchor (n1_core s') \<or> n1_absorbed s'"
  by (cases s; cases a)
     (auto simp: n1_absorbed_def n1_obs_def n1_anchor_def n1_core_def
           elim: n1_step.elims)

lemma n1_crashed_not_absorbed: "n1_crashed s \<Longrightarrow> \<not> n1_absorbed s"
  by (simp add: n1_crashed_def n1_absorbed_def)

lemma n1_absorbing_fails:
  "\<exists>s a s'. n1_step s a s' \<and> n1_absorbed s \<and> \<not> n1_absorbed s'"
  by (intro exI[of _ "(N1Rec, 1)"] exI[of _ N1Resume] exI[of _ "(N1Run, 1)"])
     (simp add: n1_absorbed_def)

lemma n1_pair_reachable:
  "\<exists>s s'. n1_reach s \<and> n1_reach s'
        \<and> n1_crashed s \<and> n1_crashed s'
        \<and> n1_core s = n1_core s'
        \<and> n1_obs s \<noteq> n1_obs s'"
proof -
  have r0: "n1_reach (N1Run, 0)" by (rule n1_reach.intros(1))
  have c0: "n1_reach (N1Crash, 0)"
    by (rule n1_reach.intros(2)[OF r0, of N1CrashA]) simp
  have rec1: "n1_reach (N1Rec, 1)"
    by (rule n1_reach.intros(2)[OF c0, of N1Reconcile]) simp
  have run1: "n1_reach (N1Run, 1)"
    by (rule n1_reach.intros(2)[OF rec1, of N1Resume]) simp
  have c1: "n1_reach (N1Crash, 1)"
    by (rule n1_reach.intros(2)[OF run1, of N1CrashA]) simp
  have "n1_reach (N1Crash, 0) \<and> n1_reach (N1Crash, 1)
      \<and> n1_crashed (N1Crash, 0) \<and> n1_crashed (N1Crash, 1)
      \<and> n1_core (N1Crash, 0) = n1_core (N1Crash, 1)
      \<and> n1_obs (N1Crash, 0) \<noteq> n1_obs (N1Crash, 1)"
    using c0 c1 by (simp add: n1_crashed_def n1_core_def n1_obs_def)
  then show ?thesis by blast
qed

section \<open>Necessity control N2: dropping only \<open>atomic_divergence\<close> (the per-entry-fire pole)\<close>

text \<open>
  Recovery fires ONE unit at a time and STAYS crashed: nothing ever
  absorbs, so the class assumption @{text absorbing} holds vacuously
  (@{text n2_absorbing_holds}) while @{text atomic_divergence} fails
  (@{text n2_atomic_fails}) --- divergence is born WITHOUT absorbing
  --- and the mid-fire crashed states form the pair
  (@{text n2_pair_reachable}).  This control is why the naive class
  statement "absorbing emitting-recovery rules the pair out" would be
  FALSE without the atomic assumption; the design study's section 8
  construction is the natural-machine prose reading, kept as prose on
  purpose (no terminal-side fire machine is built anywhere in this
  wave).
\<close>

datatype n2_mode = N2Run | N2Crash

datatype n2_act = N2CrashA | N2Fire

fun n2_step :: "n2_mode \<times> nat \<Rightarrow> n2_act \<Rightarrow> n2_mode \<times> nat \<Rightarrow> bool" where
  "n2_step (N2Run, n)   N2CrashA s' = (s' = (N2Crash, n))"
| "n2_step (N2Crash, n) N2Fire   s' = (s' = (N2Crash, Suc n))"
| "n2_step _ _ _ = False"

definition n2_obs :: "n2_mode \<times> nat \<Rightarrow> nat" where "n2_obs = snd"
definition n2_core :: "n2_mode \<times> nat \<Rightarrow> unit" where "n2_core _ = ()"
definition n2_anchor :: "unit \<Rightarrow> nat" where "n2_anchor _ = 0"
definition n2_absorbed :: "n2_mode \<times> nat \<Rightarrow> bool" where
  "n2_absorbed s \<longleftrightarrow> False"
definition n2_crashed :: "n2_mode \<times> nat \<Rightarrow> bool" where
  "n2_crashed s \<longleftrightarrow> fst s = N2Crash"

inductive n2_reach :: "n2_mode \<times> nat \<Rightarrow> bool" where
  "n2_reach (N2Run, 0)"
| "n2_reach s \<Longrightarrow> n2_step s a s' \<Longrightarrow> n2_reach s'"

lemma n2_absorbing_holds:
  "\<lbrakk>n2_step s a s'; n2_absorbed s\<rbrakk> \<Longrightarrow> n2_absorbed s'"
  by (simp add: n2_absorbed_def)

lemma n2_atomic_fails:
  "\<exists>s a s'. n2_step s a s' \<and> \<not> n2_absorbed s
          \<and> n2_obs s = n2_anchor (n2_core s)
          \<and> \<not> (n2_obs s' = n2_anchor (n2_core s') \<or> n2_absorbed s')"
  by (intro exI[of _ "(N2Crash, 0)"] exI[of _ N2Fire] exI[of _ "(N2Crash, 1)"])
     (simp add: n2_absorbed_def n2_obs_def n2_anchor_def n2_core_def)

lemma n2_pair_reachable:
  "\<exists>s s'. n2_reach s \<and> n2_reach s'
        \<and> n2_crashed s \<and> n2_crashed s'
        \<and> n2_core s = n2_core s'
        \<and> n2_obs s \<noteq> n2_obs s'"
proof -
  have r0: "n2_reach (N2Run, 0)" by (rule n2_reach.intros(1))
  have c0: "n2_reach (N2Crash, 0)"
    by (rule n2_reach.intros(2)[OF r0, of N2CrashA]) simp
  have c1: "n2_reach (N2Crash, 1)"
    by (rule n2_reach.intros(2)[OF c0, of N2Fire]) simp
  have "n2_reach (N2Crash, 0) \<and> n2_reach (N2Crash, 1)
      \<and> n2_crashed (N2Crash, 0) \<and> n2_crashed (N2Crash, 1)
      \<and> n2_core (N2Crash, 0) = n2_core (N2Crash, 1)
      \<and> n2_obs (N2Crash, 0) \<noteq> n2_obs (N2Crash, 1)"
    using c0 c1 by (simp add: n2_crashed_def n2_core_def n2_obs_def)
  then show ?thesis by blast
qed

section \<open>Non-vacuity: the class is inhabited\<close>

text \<open>The degenerate member with no transitions at all discharges every
  assumption; the substantive member is the terminal machine, on its
  own branch (the terminal interpretation theory of this wave).\<close>

interpretation trivial_member:
  absorbing_atomic_recovery "\<lambda>t (a :: unit) t'. False" "{(0 :: nat)}"
    "\<lambda>t. t" "\<lambda>t. t" "\<lambda>s. s" "\<lambda>t. False" "\<lambda>t. False"
  by unfold_locales auto


end
