(*  Title:       DWU_Monotone_Floor.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE MONOTONE-FLOOR SLICE (reference-object program, Phase 2; owner
    decisions D-095, D-097 L11 "build-now") --- an additive post-freeze
    sibling under the freeze's own protocol: no landed statement, proof,
    definition, name, import, or session-DAG change to the frozen
    corpus.  Discipline: definitional order-condition predicates +
    characterizations and re-derivations of ALREADY-PROVED facts.  The
    landed theorems stay untouched and remain the pinned principals.

    THE ORDER CONDITION.  The U8 fencing mechanism is order-theoretic:
    the fence is a MONOTONE FLOOR on the generation order, and the
    machine's acceptance filter (dwu_fence t <= ue_gen x, the gate at
    DWU_Machine.thy ulift_publish :221-226 / usnap :234-239 / ufire
    :262-267 and u_policy_redrive :360-362) admits an emission into the
    accepted ledger only if its generation clears the floor in force at
    its acceptance point.  This theory names that reading once and
    proves it from landed facts, on three levels:

      - per step (u_step_monotone_floor): every machine step satisfies
        the monotone-floor condition --- floor non-decreasing (landed
        u_step_fence_mono), LSN non-decreasing (landed
        u_journal_append_only), and every NEWLY accepted emission
        clears the floor at its acceptance point and stamps within the
        LSN at its acceptance point (the (generation, LSN, acceptance)
        triple of the design brief);

      - along traces (u_temporal_monotone_floor /
        u_reachable_monotone_floor): the condition composes, giving the
        floor law u_new_acceptance_clears_floor --- once the floor
        stands at n, every emission accepted from then on, by any
        incarnation, zombie or live, carries generation >= n;

      - at the invariant (THE CHARACTERIZATION,
        u_arm_below_fence_iff_floor_section +
        u_disc_inv_floor_factorization): the C4 clause of the landed
        U8 invariant u_disc_inv (arm_below_fence,
        DWU_Fenced_Discipline.thy:144) is EQUIVALENT to the section
        condition "every fence-eligible armed slot of the incarnation
        table IS the floor" (u_floor_section) --- the fence-eligible
        image of the armed table is a section of the generation order
        at the floor.  (The design source guessed the section would sit
        over the OWED set; where the machine actually carries it is the
        armed incarnation table --- the owed set enters through the
        batch the floor's own slot arms, u_claim_sets_floor.)  And
        u_disc_inv factors as (content residue) AND (section), through
        which the landed U8 safety headliner re-derives verbatim
        (u_fenced_discipline_safe_via_floor).

    WHICH LANDED STRUCTURE THE IFF CHARACTERIZES (state it precisely):
    the iff characterizes C4 --- the fence-GUARD clause of u_disc_inv,
    the discipline's zombie-fence mechanism --- together with the
    acceptance filter it gates.  It does NOT characterize the safety
    conclusion itself, and honestly cannot:

      (i) safety at a state consumes only the content fragment
          (u_disc_content_safe; C1 acc_just + C2 acc_dist suffice, as
          in the landed u_disc_inv_safe); the section is the INDUCTIVE
          guard that lets safety survive fires (the C4 appeal inside
          the landed pres_fire), not a pointwise consequence of it ---
          the machine reaches safe states without the section
          (u_safe_state_without_floor_section; the witness is the
          landed U10 mid-state rf_t2, the very state the landed defeat
          run drives to a duplicate two fires later, rf_dup_t5);

     (ii) the per-step law is one-directional soundness: every machine
          step satisfies the order condition; the order condition does
          not pin the step relation (it says nothing about the store);

    (iii) the visible-fire corollary (u_ledger_visible_fire_at_floor)
          is one-directional: an EMPTY armed batch above the floor
          fires ledger-invisibly, so "all ledger-visible fires happen
          at the floor" does not conversely imply the section;

     (iv) the non-order residue is named, not hidden (u_disc_content):
          C1's payload-membership justification, C2's distinctness,
          C3's journal permanence, and C5's batch coherence are CONTENT
          conditions on payloads and ledgers --- of the invariant's
          five clauses, exactly C4 is order-shaped on
          (generation, LSN, acceptance), plus C1's stamp bound which
          is the landed S4 (u_journal_stamps_bounded_invariant).

    TWO FLOORS, DISAMBIGUATED (do not conflate): dwu_floor is the
    RETENTION floor on the source history (availability on
    recovery-side reads, boundary row 16).  The monotone floor of THIS
    theory is dwu_fence on the GENERATION order --- a different field
    on a different axis.  Every formal statement below says dwu_fence.
    Relatedly: the fence <= hwm factorization is U16's separately
    landed fact, honestly scoped to the UFenceRaise-free sub-grammar
    (u_fence_le_hwm_no_free_raise, DWU_Segments.thy); it is neither
    used nor restated here.

    Ledger scoping (boundary row 17): the floor law is about the
    ACCEPTED ledger --- the sink's truth, what the fence let through
    --- never about dwu_sent (UPubLost appends to sent and never to
    accepted; the law constrains acceptance only).  Exists-machine
    polarity throughout: the one existential statement below
    (u_safe_state_without_floor_section) is a positive existence
    statement over the machine's own reachable states, quoted to bound
    the characterization; no for-every-system claim is made anywhere.

    Provenance: reference-object program Phase-2 monotone-floor slice
    (roads/program/, owner decisions D-095, D-097 L11/L14; design
    source roads/road3/_evidence/road3_critics.json idea J
    "Fencing-as-monotone-acceptance-floor"), gate EGate-R2-F1
    (roads/program/phase2_gates/egate_r2_f1/).  In-source ML oracle
    gates are STRIPPED at landing per house rule; oracle-freedom is
    certified by the scratch-side gate session with confirmed-biting
    negative controls.
*)

theory DWU_Monotone_Floor
  imports DWU_Fenced_Discipline
begin

section \<open>1. The order vocabulary (definitional; frozen-machine fields only)\<close>

text \<open>The armed-slot order clause C4 of the landed invariant, extracted verbatim
  as a named predicate (@{thm [source] u_disc_invD} (4) is its destructor form).\<close>

definition u_arm_below_fence :: "('k, 'v) dwu_state \<Rightarrow> bool" where
  "u_arm_below_fence t \<longleftrightarrow>
     (\<forall>g B. dwu_gens t g = Some (UArmed B) \<longrightarrow> g \<le> dwu_fence t)"

text \<open>The SECTION reading of the same structure: every fence-eligible armed slot
  IS the floor.  Since @{const dwu_gens} is a function, the fence-eligible part
  of the armed table is then (at most) the single slot at the floor --- a section
  of the generation order at @{term "dwu_fence t"}.\<close>

definition u_floor_section :: "('k, 'v) dwu_state \<Rightarrow> bool" where
  "u_floor_section t \<longleftrightarrow>
     (\<forall>g B. dwu_gens t g = Some (UArmed B) \<longrightarrow> dwu_fence t \<le> g \<longrightarrow> g = dwu_fence t)"

text \<open>The non-order residue of the landed invariant: clauses C1, C2, C3, C5
  verbatim (everything except the order clause C4).  C5 remains fence-INDEXED
  content --- coherence is demanded only of fence-eligible batches --- which is
  disclosed, not simplified away.\<close>

definition u_disc_content :: "('k, 'v) dwu_state \<Rightarrow> bool" where
  "u_disc_content t \<longleftrightarrow>
     (\<forall>x \<in> set (dwu_accepted t). u_justified t x)
   \<and> distinct (log_payloads (dwu_accepted t))
   \<and> dwu_journal t = exec_src_hist (dwu_store t)
   \<and> (\<forall>g B. dwu_gens t g = Some (UArmed B) \<longrightarrow> dwu_fence t \<le> g \<longrightarrow>
        distinct (log_payloads B)
      \<and> set (log_payloads B) \<inter> set (log_payloads (dwu_accepted t)) = {}
      \<and> (\<forall>x \<in> set B. u_justified t x))"

text \<open>The two-state monotone-floor condition on (generation, LSN, acceptance):
  the floor never falls, the LSN never falls, acceptance is append-only, and
  every emission accepted across the pair clears the STARTING floor and stamps
  within the ENDING LSN.  For a single machine step the two readings coincide
  with the acceptance-point readings: every accepting rule (publish / snap /
  fire) freezes both the fence and the journal, so "clears @{term "dwu_fence t"}"
  IS "clears the floor at its acceptance point" and "stamps within
  @{term "length (dwu_journal t')"}" IS "stamps within the LSN at its acceptance
  point".  The end-side LSN bound is what makes the condition transitive.\<close>

definition u_monotone_floor_step
  :: "('k, 'v) dwu_state \<Rightarrow> ('k, 'v) dwu_state \<Rightarrow> bool"
where
  "u_monotone_floor_step t t' \<longleftrightarrow>
     dwu_fence t \<le> dwu_fence t'
   \<and> length (dwu_journal t) \<le> length (dwu_journal t')
   \<and> (\<exists>ys. dwu_accepted t' = dwu_accepted t @ ys
        \<and> (\<forall>x \<in> set ys. dwu_fence t \<le> ue_gen x
                       \<and> ue_stamp x \<le> length (dwu_journal t')))"

text \<open>The support invariant: every armed batch is stamped at its own slot.  This
  is the machine's own arming truth --- @{text uarm} guards it
  (@{term "\<forall>x \<in> set B. ue_gen x = g"}, DWU_Machine.thy:248) and @{text uarmf}
  stamps it (@{const stamped_at} at @{term g}, :258) --- named here because the
  @{text ufire} gate reads the TABLE index @{term g} while the floor law speaks
  of the EMISSION generation @{term "ue_gen x"}; exactness is what identifies
  the two.\<close>

definition u_armed_gen_exact :: "('k, 'v) dwu_state \<Rightarrow> bool" where
  "u_armed_gen_exact t \<longleftrightarrow>
     (\<forall>g B. dwu_gens t g = Some (UArmed B) \<longrightarrow> (\<forall>x \<in> set B. ue_gen x = g))"

lemma u_monotone_floor_step_refl: "u_monotone_floor_step t t"
  by (auto simp: u_monotone_floor_step_def intro!: exI[of _ "[]"])

lemma u_monotone_floor_step_trans:
  assumes "u_monotone_floor_step t1 t2"
      and "u_monotone_floor_step t2 t3"
  shows "u_monotone_floor_step t1 t3"
proof -
  from assms(1) obtain ys1 where
    f12: "dwu_fence t1 \<le> dwu_fence t2" and
    j12: "length (dwu_journal t1) \<le> length (dwu_journal t2)" and
    a12: "dwu_accepted t2 = dwu_accepted t1 @ ys1" and
    b1: "\<forall>x \<in> set ys1. dwu_fence t1 \<le> ue_gen x
                      \<and> ue_stamp x \<le> length (dwu_journal t2)"
    unfolding u_monotone_floor_step_def by blast
  from assms(2) obtain ys2 where
    f23: "dwu_fence t2 \<le> dwu_fence t3" and
    j23: "length (dwu_journal t2) \<le> length (dwu_journal t3)" and
    a23: "dwu_accepted t3 = dwu_accepted t2 @ ys2" and
    b2: "\<forall>x \<in> set ys2. dwu_fence t2 \<le> ue_gen x
                      \<and> ue_stamp x \<le> length (dwu_journal t3)"
    unfolding u_monotone_floor_step_def by blast
  have acc: "dwu_accepted t3 = dwu_accepted t1 @ (ys1 @ ys2)"
    by (simp add: a23 a12)
  have bnd: "\<forall>x \<in> set (ys1 @ ys2). dwu_fence t1 \<le> ue_gen x
                                  \<and> ue_stamp x \<le> length (dwu_journal t3)"
  proof
    fix x assume "x \<in> set (ys1 @ ys2)"
    then consider "x \<in> set ys1" | "x \<in> set ys2" by auto
    then show "dwu_fence t1 \<le> ue_gen x \<and> ue_stamp x \<le> length (dwu_journal t3)"
    proof cases
      case 1
      with b1 j23 show ?thesis by fastforce
    next
      case 2
      with b2 f12 show ?thesis by fastforce
    qed
  qed
  from f12 f23 j12 j23 acc bnd show ?thesis
    unfolding u_monotone_floor_step_def by (blast intro: order_trans)
qed


section \<open>2. The support invariant: armed batches are stamped at their slot\<close>

lemma u_armed_gen_exact_init: "u_armed_gen_exact (dwu_init b K fin)"
  by (auto simp: u_armed_gen_exact_def dwu_init_def split: if_split_asm)

lemma u_armed_gen_exact_step:
  assumes "dwu_step t \<alpha> t'"
      and "u_armed_gen_exact t"
  shows "u_armed_gen_exact t'"
  using assms
  by (cases rule: dwu_step.cases)
     (auto simp: u_armed_gen_exact_def stamped_at_def split: if_split_asm)

lemma u_armed_gen_exact_trace:
  assumes "dwu_temporal_trace u xs u'"
      and "u_armed_gen_exact u"
  shows "u_armed_gen_exact u'"
  using assms
  by (induction rule: dwu_temporal_trace.induct) (meson u_armed_gen_exact_step)+

theorem u_armed_gen_exact_invariant:
  assumes "dwu_reachable b K fin t"
  shows "u_armed_gen_exact t"
proof -
  from assms obtain xs where xs: "dwu_temporal_trace (dwu_init b K fin) xs t"
    unfolding dwu_reachable_def by blast
  show ?thesis by (rule u_armed_gen_exact_trace[OF xs u_armed_gen_exact_init])
qed


section \<open>3. The per-step monotone-floor law (machine-wide, all 16 rules)\<close>

text \<open>The acceptance half: every step appends to the accepted ledger only
  emissions whose generation clears the floor at the acceptance point and whose
  stamp is within the LSN at the acceptance point.  The three accepting rules
  carry the gate syntactically (@{text ulift_publish} / @{text usnap} on
  @{term "ue_gen x"}; @{text ufire} on the table index @{term g}, identified
  with @{term "ue_gen x"} by exactness); the fire's stamp bound is the armed
  clause of the landed S4 (@{thm [source] u_journal_stamps_bounded_invariant}'s
  per-step form); the remaining thirteen rules leave the ledger untouched.\<close>

lemma u_step_new_acceptance_bounded:
  assumes step: "dwu_step t \<alpha> t'"
      and gex: "u_armed_gen_exact t"
      and stb: "u_journal_stamps_bounded t"
  shows "\<exists>ys. dwu_accepted t' = dwu_accepted t @ ys
           \<and> (\<forall>x \<in> set ys. dwu_fence t \<le> ue_gen x
                          \<and> ue_stamp x \<le> length (dwu_journal t'))"
  using step
proof (cases rule: dwu_step.cases)
  case ulift_source
  then show ?thesis by (intro exI[of _ "[]"]) auto
next
  case ulift_enqueue
  then show ?thesis by (intro exI[of _ "[]"]) auto
next
  case ulift_ack
  then show ?thesis by (intro exI[of _ "[]"]) auto
next
  case (ulift_publish g c e s' x)
  then show ?thesis
    by (intro exI[of _ "if dwu_fence t \<le> ue_gen x then [x] else []"]) auto
next
  case ulift_nonprod
  then show ?thesis by (intro exI[of _ "[]"]) auto
next
  case upublost
  then show ?thesis by (intro exI[of _ "[]"]) auto
next
  case (usnap g x c k v)
  then show ?thesis
    by (intro exI[of _ "if dwu_fence t \<le> ue_gen x then [x] else []"]) auto
next
  case uspawn
  then show ?thesis by (intro exI[of _ "[]"]) auto
next
  case uarm
  then show ?thesis by (intro exI[of _ "[]"]) auto
next
  case uarmf
  then show ?thesis by (intro exI[of _ "[]"]) auto
next
  case uheal
  then show ?thesis by (intro exI[of _ "[]"]) auto
next
  case (ufire g B)
  from ufire gex have genB: "\<forall>x \<in> set B. ue_gen x = g"
    by (auto simp: u_armed_gen_exact_def)
  from ufire stb have stampB: "\<forall>x \<in> set B. ue_stamp x \<le> length (dwu_journal t)"
    by (auto simp: u_journal_stamps_bounded_def)
  from ufire genB stampB show ?thesis
    by (intro exI[of _ "if dwu_fence t \<le> g then B else []"]) auto
next
  case urelease
  then show ?thesis by (intro exI[of _ "[]"]) auto
next
  case ufenceraise
  then show ?thesis by (intro exI[of _ "[]"]) auto
next
  case utrunccrash
  then show ?thesis by (intro exI[of _ "[]"]) auto
next
  case uretain
  then show ?thesis by (intro exI[of _ "[]"]) auto
qed

theorem u_step_monotone_floor:
  assumes step: "dwu_step t \<alpha> t'"
      and gex: "u_armed_gen_exact t"
      and stb: "u_journal_stamps_bounded t"
  shows "u_monotone_floor_step t t'"
proof -
  have f: "dwu_fence t \<le> dwu_fence t'" by (rule u_step_fence_mono[OF step])
  from u_journal_append_only[OF step] obtain js
    where "dwu_journal t' = dwu_journal t @ js" ..
  then have j: "length (dwu_journal t) \<le> length (dwu_journal t')" by simp
  from u_step_new_acceptance_bounded[OF step gex stb] f j show ?thesis
    unfolding u_monotone_floor_step_def by blast
qed

text \<open>The redrive row satisfies the same acceptance half BY DEFINITION: the
  landed @{thm [source] u_policy_redrive_accepted} exhibits the accepted suffix
  as literally the floor filter of the stamped batch (and the landed
  @{thm [source] u_policy_redrive_fence} freezes the floor across it).\<close>

lemma u_redrive_new_acceptance_clears_floor:
  assumes "u_policy_redrive P t f t'"
  shows "\<exists>ys. dwu_accepted t' = dwu_accepted t @ ys
           \<and> (\<forall>x \<in> set ys. dwu_fence t \<le> ue_gen x)"
  using u_policy_redrive_accepted[OF assms]
  by (intro exI[of _ "filter (\<lambda>x. dwu_fence t \<le> ue_gen x)
                        (stamped_at (length (dwu_journal t)) (dwu_hwm t) (P t))"])
     auto


section \<open>4. The floor law along traces\<close>

lemma u_temporal_monotone_floor:
  assumes "dwu_temporal_trace s xs t"
      and "u_armed_gen_exact s"
      and "u_journal_stamps_bounded s"
  shows "u_monotone_floor_step s t"
  using assms
proof (induction rule: dwu_temporal_trace.induct)
  case (dwu_refl t)
  show ?case by (rule u_monotone_floor_step_refl)
next
  case (dwu_lift_step t a g t' as t'')
  have hd: "u_monotone_floor_step t t'"
    by (rule u_step_monotone_floor[OF dwu_lift_step.hyps(3)
              dwu_lift_step.prems(1) dwu_lift_step.prems(2)])
  have g': "u_armed_gen_exact t'"
    by (rule u_armed_gen_exact_step[OF dwu_lift_step.hyps(3) dwu_lift_step.prems(1)])
  have s': "u_journal_stamps_bounded t'"
    by (rule u_journal_stamps_bounded_step[OF dwu_lift_step.hyps(3) dwu_lift_step.prems(2)])
  show ?case by (rule u_monotone_floor_step_trans[OF hd dwu_lift_step.IH[OF g' s']])
next
  case (dwu_publost_step t c e g t' as t'')
  have hd: "u_monotone_floor_step t t'"
    by (rule u_step_monotone_floor[OF dwu_publost_step.hyps(3)
              dwu_publost_step.prems(1) dwu_publost_step.prems(2)])
  have g': "u_armed_gen_exact t'"
    by (rule u_armed_gen_exact_step[OF dwu_publost_step.hyps(3) dwu_publost_step.prems(1)])
  have s': "u_journal_stamps_bounded t'"
    by (rule u_journal_stamps_bounded_step[OF dwu_publost_step.hyps(3) dwu_publost_step.prems(2)])
  show ?case by (rule u_monotone_floor_step_trans[OF hd dwu_publost_step.IH[OF g' s']])
next
  case (dwu_other_step \<alpha> t t' as t'')
  have hd: "u_monotone_floor_step t t'"
    by (rule u_step_monotone_floor[OF dwu_other_step.hyps(3)
              dwu_other_step.prems(1) dwu_other_step.prems(2)])
  have g': "u_armed_gen_exact t'"
    by (rule u_armed_gen_exact_step[OF dwu_other_step.hyps(3) dwu_other_step.prems(1)])
  have s': "u_journal_stamps_bounded t'"
    by (rule u_journal_stamps_bounded_step[OF dwu_other_step.hyps(3) dwu_other_step.prems(2)])
  show ?case by (rule u_monotone_floor_step_trans[OF hd dwu_other_step.IH[OF g' s']])
qed

theorem u_reachable_monotone_floor:
  assumes r: "dwu_reachable b K fin s"
      and tr: "dwu_temporal_trace s xs t"
  shows "u_monotone_floor_step s t"
  by (rule u_temporal_monotone_floor[OF tr u_armed_gen_exact_invariant[OF r]
            u_journal_stamps_bounded_invariant[OF r]])

corollary u_init_monotone_floor:
  assumes "dwu_reachable b K fin t"
  shows "u_monotone_floor_step (dwu_init b K fin) t"
proof -
  from assms obtain xs where "dwu_temporal_trace (dwu_init b K fin) xs t"
    unfolding dwu_reachable_def by blast
  from u_reachable_monotone_floor[OF dwu_reachable_init this] show ?thesis .
qed

text \<open>THE FLOOR LAW, pointwise: once the floor stands at @{term "dwu_fence s"},
  every emission accepted from then on --- by any incarnation, zombie or live ---
  carries a generation that clears it, and a stamp within the final LSN.  This is
  the order-theoretic face of zombie fencing: raising the floor permanently
  excludes lower generations from FUTURE acceptance (it never revokes past
  acceptances --- acceptance is append-only, landed
  @{thm [source] u_temporal_accepted_grow}).\<close>

corollary u_new_acceptance_clears_floor:
  assumes r: "dwu_reachable b K fin s"
      and tr: "dwu_temporal_trace s xs t"
      and x: "x \<in> set (dwu_accepted t)"
      and nx: "x \<notin> set (dwu_accepted s)"
  shows "dwu_fence s \<le> ue_gen x \<and> ue_stamp x \<le> length (dwu_journal t)"
proof -
  from u_reachable_monotone_floor[OF r tr] obtain ys where
    a: "dwu_accepted t = dwu_accepted s @ ys" and
    b: "\<forall>y \<in> set ys. dwu_fence s \<le> ue_gen y \<and> ue_stamp y \<le> length (dwu_journal t)"
    unfolding u_monotone_floor_step_def by blast
  from a x nx have "x \<in> set ys" by auto
  with b show ?thesis by blast
qed

text \<open>The disciplined grammar is a restriction of the temporal grammar (landed
  @{thm [source] u_disciplined_imp_temporal}), so the floor law holds along
  disciplined traces unchanged.\<close>

corollary u_disciplined_monotone_floor:
  assumes "u_disciplined_trace (dwu_init b K fin) acts t"
  shows "u_monotone_floor_step (dwu_init b K fin) t"
  by (rule u_reachable_monotone_floor[OF dwu_reachable_init
            u_disciplined_imp_temporal[OF assms]])


section \<open>5. THE CHARACTERIZATION: C4 is the floor-section condition\<close>

text \<open>The iff.  Forward: an armed slot at or below the fence that is also
  fence-eligible is pinched to the fence.  Backward: a slot strictly above the
  fence would be fence-eligible yet distinct from the fence, contradicting the
  section --- so every armed slot sits at or below the fence.  The
  characterization is of the LANDED guard structure: C4 verbatim on one side,
  the section reading on the other.\<close>

theorem u_arm_below_fence_iff_floor_section:
  "u_arm_below_fence t \<longleftrightarrow> u_floor_section t"
  unfolding u_arm_below_fence_def u_floor_section_def
  by (metis le_antisym nat_le_linear order_refl)

lemma u_disc_inv_arm_below_fence:
  "u_disc_inv t \<Longrightarrow> u_arm_below_fence t"
  by (simp add: u_disc_inv_def u_arm_below_fence_def)

lemma u_disc_inv_floor_section:
  "u_disc_inv t \<Longrightarrow> u_floor_section t"
  using u_disc_inv_arm_below_fence u_arm_below_fence_iff_floor_section by blast

text \<open>The factorization: the landed U8 invariant is exactly (content residue)
  AND (floor section).  The split is by clauses --- @{const u_disc_content} is
  C1 \<open>\<and>\<close> C2 \<open>\<and>\<close> C3 \<open>\<and>\<close> C5 verbatim, and C4 is traded for the section through
  the iff above.\<close>

lemma u_disc_inv_content_below_fence:
  "u_disc_inv t \<longleftrightarrow> u_disc_content t \<and> u_arm_below_fence t"
  unfolding u_disc_inv_def u_disc_content_def u_arm_below_fence_def by blast

theorem u_disc_inv_floor_factorization:
  "u_disc_inv t \<longleftrightarrow> u_disc_content t \<and> u_floor_section t"
  by (simp add: u_disc_inv_content_below_fence u_arm_below_fence_iff_floor_section)

text \<open>Safety at a state consumes only the content residue (C1 + C2, exactly as
  in the landed @{thm [source] u_disc_inv_safe}); the section's role is
  inductive, not pointwise.\<close>

lemma u_disc_content_safe:
  "u_disc_content t \<Longrightarrow> \<not> u_effect_unsafe t"
  by (auto simp: u_disc_content_def u_effect_unsafe_def
                 u_premature_def u_duplicate_def)

text \<open>The composite reading at the floor (C4 + C5 through the factorization):
  a fence-eligible armed batch IS the floor's own batch, and it is coherent ---
  payload-distinct, disjoint from the accepted ledger, justified.  "The
  fence-eligible image of the armed table is a coherent section at the floor."\<close>

theorem u_disc_inv_floor_batch_coherent:
  assumes inv: "u_disc_inv t"
      and gB: "dwu_gens t g = Some (UArmed B)"
      and el: "dwu_fence t \<le> g"
  shows "g = dwu_fence t
       \<and> distinct (log_payloads B)
       \<and> set (log_payloads B) \<inter> set (log_payloads (dwu_accepted t)) = {}
       \<and> (\<forall>x \<in> set B. u_justified t x)"
proof -
  from u_disc_inv_floor_section[OF inv] gB el have "g = dwu_fence t"
    unfolding u_floor_section_def by blast
  with u_disc_invD(5)[OF inv gB el] show ?thesis by blast
qed


section \<open>6. The gate mechanism, read through the floor\<close>

text \<open>Sub-floor fires are inert on the accepted ledger: the gate filters the
  whole batch.  (This is the general form of the landed control computation
  @{thm [source] cwr_acc_same} --- the claim-without-read run's fenced-out
  fire.)  The sent ledger still receives the batch: the wire/audit carrier and
  the sink's truth separate exactly here (boundary row 17).\<close>

lemma u_subfloor_fire_inert:
  assumes "dwu_step t (UFire g) t'"
      and "g < dwu_fence t"
  shows "dwu_accepted t' = dwu_accepted t"
proof -
  from dwu_step_fire_full[OF assms(1)] obtain B where
    "dwu_accepted t' = dwu_accepted t @ (if dwu_fence t \<le> g then B else [])" by blast
  with assms(2) show ?thesis by simp
qed

text \<open>Under the section, every LEDGER-VISIBLE fire happens exactly at the
  floor.  One-directional by design: an empty armed batch above the floor would
  fire ledger-invisibly, so the converse does not recover the section (disclosed
  in the header).\<close>

lemma u_ledger_visible_fire_at_floor:
  assumes sec: "u_floor_section t"
      and step: "dwu_step t (UFire g) t'"
      and vis: "dwu_accepted t' \<noteq> dwu_accepted t"
  shows "g = dwu_fence t"
proof -
  from dwu_step_fire_full[OF step] obtain B where
    gB: "dwu_gens t g = Some (UArmed B)" and
    acc': "dwu_accepted t' = dwu_accepted t @ (if dwu_fence t \<le> g then B else [])"
    by blast
  have el: "dwu_fence t \<le> g"
  proof (rule ccontr)
    assume "\<not> dwu_fence t \<le> g"
    with acc' have "dwu_accepted t' = dwu_accepted t" by simp
    with vis show False by simp
  qed
  from sec gB el show ?thesis unfolding u_floor_section_def by blast
qed

text \<open>The claim raises the floor to its own generation and re-arms AT the new
  floor, in one rule (the landed atomic claim-arm, boundary row 12) --- and it
  PRESERVES the section: the new slot is the new floor, and every older armed
  slot sits at or below the old floor, hence strictly below eligibility.\<close>

lemma u_claim_sets_floor:
  assumes "dwu_step t (UArmF g f) t'"
  shows "dwu_fence t \<le> g \<and> dwu_fence t' = g
       \<and> dwu_gens t' g =
           Some (UArmed (stamped_at (length (dwu_journal t)) g (u_sink_delta f t)))"
  using dwu_step_armf_full[OF assms] by simp

lemma u_claim_preserves_floor_section:
  assumes sec: "u_floor_section t"
      and step: "dwu_step t (UArmF g f) t'"
  shows "u_floor_section t'"
proof -
  have abf: "u_arm_below_fence t"
    using sec by (simp add: u_arm_below_fence_iff_floor_section)
  from dwu_step_armf_full[OF step] have
    fle: "dwu_fence t \<le> g" and F: "dwu_fence t' = g" and
    G: "dwu_gens t' =
          (dwu_gens t)(g \<mapsto> UArmed (stamped_at (length (dwu_journal t)) g (u_sink_delta f t)))"
    by auto
  show ?thesis
    unfolding u_floor_section_def
  proof (intro allI impI)
    fix g' B
    assume gB: "dwu_gens t' g' = Some (UArmed B)" and el: "dwu_fence t' \<le> g'"
    show "g' = dwu_fence t'"
    proof (cases "g' = g")
      case True
      with F show ?thesis by simp
    next
      case False
      with gB G have "dwu_gens t g' = Some (UArmed B)" by (auto split: if_split_asm)
      with abf have "g' \<le> dwu_fence t" unfolding u_arm_below_fence_def by blast
      with fle F el show ?thesis by simp
    qed
  qed
qed


section \<open>7. The landed U8 safety headliner, re-derived through the factorization\<close>

text \<open>Statement-identical to the landed principal
  @{thm [source] u_fenced_multiwriter_discipline_safe} (which stays pinned);
  the route here exhibits the order condition's exact role: the landed
  preservation induction maintains the invariant, the factorization splits it
  into section + content, and the content alone discharges safety at the end
  state.  The discipline maintains the section along the way
  (@{text u_disciplined_floor_section} below) --- that is what survives every
  fire (the C4 appeal inside the landed @{thm [source] pres_fire}).\<close>

theorem u_fenced_discipline_safe_via_floor:
  assumes "u_disciplined_trace (dwu_init b K fin) acts t"
  shows "\<not> u_effect_unsafe t"
proof -
  have "u_disc_inv t" by (rule u_disc_inv_pres[OF assms u_disc_inv_init])
  then have "u_disc_content t"
    by (simp add: u_disc_inv_floor_factorization)
  then show ?thesis by (rule u_disc_content_safe)
qed

corollary u_disciplined_floor_section:
  assumes "u_disciplined_trace (dwu_init b K fin) acts t"
  shows "u_floor_section t"
  using u_disc_inv_pres[OF assms u_disc_inv_init]
  by (simp add: u_disc_inv_floor_factorization)

lemma u_floor_section_init: "u_floor_section (dwu_init b K fin)"
  by (auto simp: u_floor_section_def dwu_init_def split: if_split_asm)


section \<open>8. The boundary anchor: the section is a guard, not a consequence of safety\<close>

text \<open>The characterization stops at the guard clause, and provably must: the
  machine reaches SAFE states in which the section fails.  The witness is the
  landed U10 mid-state @{const rf_t2} (both generations armed while the fence
  still stands at 0, so slot 1 is armed strictly ABOVE the floor) --- reachable
  by the landed steps
  @{thm [source] rf_step_arm1} / @{thm [source] rf_step_arm2} from the landed
  witness @{const rf_W}, safe because its ledger, journal, and store are
  @{const rf_W}'s own, and section-violating at slot 1.  From exactly this
  state the landed defeat run duplicates two fires later
  (@{thm [source] rf_dup_t5}) --- the landed evidence, cited not restated, that
  the guard is load-bearing.  Polarity: a positive existence statement over the
  machine's own reachable states; it bounds the characterization (the iff of
  section 5 is of C4, not of the safety conclusion) and claims nothing beyond
  the machine.\<close>

lemma rf_t2_reachable: "dwu_reachable_w rf_t2"
proof -
  have r1: "dwu_reachable_w rf_t1"
    by (rule dwu_reach_other[OF rf_reach_W _ _ rf_step_arm1]) simp_all
  show ?thesis
    by (rule dwu_reach_other[OF r1 _ _ rf_step_arm2]) simp_all
qed

lemma rf_t2_safe: "\<not> u_effect_unsafe rf_t2"
  by (simp add: u_effect_unsafe_def u_premature_def u_duplicate_def u_justified_def
                rf_t2_def rf_t1_def rf_W_def mkU_def rf_sto6_def mkC_def rf_x1_def
                log_payloads_def map_filter_simps e1_def ec_defs)

lemma rf_t2_not_floor_section: "\<not> u_floor_section rf_t2"
proof -
  have g1: "dwu_gens rf_t2 1 = Some (UArmed rf_B2)"
    by (simp add: rf_t2_def rf_t1_def rf_W_def mkU_def)
  have f0: "dwu_fence rf_t2 = 0"
    by (simp add: rf_t2_def rf_t1_def rf_W_def mkU_def)
  show ?thesis
  proof
    assume "u_floor_section rf_t2"
    from this[unfolded u_floor_section_def, rule_format, OF g1] f0
    show False by simp
  qed
qed

theorem u_safe_state_without_floor_section:
  "\<exists>t. dwu_reachable_w t \<and> \<not> u_effect_unsafe t \<and> \<not> u_floor_section t"
  using rf_t2_reachable rf_t2_safe rf_t2_not_floor_section by blast

end
