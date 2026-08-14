(*  Title:       DWU_Conservativity.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Purpose: Road-2 I1 — THE CONSERVATIVITY BLOCK (the admissibility value).

    The landed cyclic effect machine is recovered as the fence-identically-0,
    single-incarnation, permanent-source, log-only SOLO FRAGMENT under the
    projection Pi / embedding iota.  Five pinned principals (statements copied
    VERBATIM from the Stage-3 probe seed DWU_Statement_Probe.thy):

      U1  u_landed_embedding      (dwe trace embeds as a solo_trace at iota)
      U1  u_reachable_pullback    (corollary: dwe_reachable pulls back)
      U2  u_solo_projection       (solo_trace projects to a dwe trace; solo_inv)
      U3  u_hazards_once          (the hazard commutes under Pi)
      U3  u_sink_delta_commutes   (sink-delta / loss / at-least-once commute)

    The FUSED-TRIPLE INVERSION PACKAGE (arm/heal/fire adjacency: endpoints,
    stamp agreement via journal-frozen-through-the-triple, the m <= length
    replay pin) is built first as named lemmas — I3's U8 reuses them wholesale.

    Honesty regime: quick_and_dirty = false (ROOT-pinned), ZERO sorry, ZERO
    oops, no axiomatization, no consts, no oracles.  Every principal PROVED.
*)

theory DWU_Conservativity
  imports DWU_Machine
begin

section \<open>0. Bridge lemmas: the projected emission ledger\<close>

text \<open>@{const log_payloads} keeps exactly the ULog payloads, in order; this is
  the same list @{const \<Pi>} produces (which filters @{const is_ulog} then reads
  @{const ulog_of} via the payload projection).\<close>

lemma log_payloads_eq_map_ulog_filter:
  "log_payloads xs = map ulog_of (filter is_ulog xs)"
  by (induction xs)
     (auto simp: log_payloads_def is_ulog_def ulog_of_def map_filter_simps
           split: upayload.splits)

text \<open>The payload projection @{term "\<lambda>x. (ue_stamp x, ue_gen x, fst (ulog_of x),
  snd (ulog_of x))"} that @{const \<Pi>} applies reads back, under the landed
  emission accessors, to exactly the unified stamp / gen / payload.\<close>

lemma e_payload_proj [simp]:
  "e_payload (ue_stamp x, ue_gen x, fst (ulog_of x), snd (ulog_of x)) = ulog_of x"
  by (simp add: e_payload_def)

lemma e_stamp_proj [simp]:
  "e_stamp (ue_stamp x, ue_gen x, fst (ulog_of x), snd (ulog_of x)) = ue_stamp x"
  by (simp add: e_stamp_def)

lemma e_epoch_proj [simp]:
  "e_epoch (ue_stamp x, ue_gen x, fst (ulog_of x), snd (ulog_of x)) = ue_gen x"
  by (simp add: e_epoch_def)

text \<open>The load-bearing ledger bridge: the payloads @{const \<Pi>} exports equal the
  unified @{const log_payloads} of the sent ledger, AS A LIST.\<close>

lemma map_e_payload_\<Pi>_emitted:
  "map e_payload (dwe_emitted (\<Pi> t)) = log_payloads (dwu_sent t)"
  by (simp add: \<Pi>_def log_payloads_eq_map_ulog_filter o_def)

lemma set_\<Pi>_emitted_payloads:
  "e_payload ` set (dwe_emitted (\<Pi> t)) = set (log_payloads (dwu_sent t))"
  by (metis map_e_payload_\<Pi>_emitted set_map)


section \<open>1. The embedding @{term \<iota>} and projection @{term \<Pi>}: field accessors\<close>

lemma \<iota>_store [simp]:   "dwu_store (\<iota> t) = dwe_core t" by (simp add: \<iota>_def)
lemma \<iota>_journal [simp]: "dwu_journal (\<iota> t) = exec_src_hist (dwe_core t)" by (simp add: \<iota>_def)
lemma \<iota>_sent [simp]:    "dwu_sent (\<iota> t) = map ulift (dwe_emitted t)" by (simp add: \<iota>_def)
lemma \<iota>_accepted [simp]: "dwu_accepted (\<iota> t) = map ulift (dwe_emitted t)" by (simp add: \<iota>_def)
lemma \<iota>_fence [simp]:   "dwu_fence (\<iota> t) = 0" by (simp add: \<iota>_def)
lemma \<iota>_gens [simp]:    "dwu_gens (\<iota> t) = (\<lambda>g. if g \<le> dwe_epoch t then Some UProd else None)"
  by (simp add: \<iota>_def)
lemma \<iota>_hwm [simp]:     "dwu_hwm (\<iota> t) = dwe_epoch t" by (simp add: \<iota>_def)
lemma \<iota>_floor [simp]:   "dwu_floor (\<iota> t) = 0" by (simp add: \<iota>_def)

lemma \<Pi>_core [simp]:  "dwe_core (\<Pi> t) = dwu_store t" by (simp add: \<Pi>_def)
lemma \<Pi>_epoch [simp]: "dwe_epoch (\<Pi> t) = dwu_hwm t" by (simp add: \<Pi>_def)

text \<open>The incumbent actor @{term "dwe_epoch t"} is a live UProd producer at
  @{term "\<iota> t"} (S1 shape, discharged on the nose by the pinned gens field).\<close>

lemma \<iota>_incumbent_dom [simp]: "dwe_epoch t \<in> dom (dwu_gens (\<iota> t))"
  by (simp add: dom_def)

lemma \<iota>_incumbent_prod [simp]: "dwu_gens (\<iota> t) (dwe_epoch t) = Some UProd"
  by simp


section \<open>2. U1 lift simulation: a dwe label step is an incumbent unified ULift\<close>

text \<open>Every landed @{const dwe_step} label step is simulated on the nose by the
  unified @{const ULift} at the incumbent actor @{term "dwe_epoch t"}, landing
  exactly at @{term "\<iota> t'"}.  The case split is DoSource / publish / other
  (P2 route).\<close>

lemma \<iota>_dwe_label_sim:
  assumes "dwe_step t a t'"
  shows "dwu_step (\<iota> t) (ULift (dwe_epoch t) a) (\<iota> t')"
  using assms
proof (cases rule: dwe_step.cases)
  case (lift_nonpub c')
  \<comment> \<open>@{term "t' = t\<lparr>dwe_core := c'\<rparr>"}; @{term a} is not a publish\<close>
  from lift_nonpub(2) show ?thesis
  proof (cases rule: dw_exec_step.cases)
    case (do_source c e)
    have step': "dw_exec_step (dwu_store (\<iota> t)) (DoSource c e) c'"
      using lift_nonpub(2) do_source(1) by simp
    have base: "dwu_step (\<iota> t) (ULift (dwe_epoch t) (DoSource c e))
                  ((\<iota> t)\<lparr>dwu_store := c', dwu_journal := dwu_journal (\<iota> t) @ [(c, e)]\<rparr>)"
      by (rule dwu_step.ulift_source[OF \<iota>_incumbent_dom \<iota>_incumbent_prod step'])
    have steq: "(\<iota> t)\<lparr>dwu_store := c', dwu_journal := dwu_journal (\<iota> t) @ [(c, e)]\<rparr> = \<iota> t'"
      using lift_nonpub(1) do_source by (simp add: \<iota>_def)
    show ?thesis using base steq do_source by simp
  next
    case (enqueue_downstream c e)
    have step': "dw_exec_step (dwu_store (\<iota> t)) (EnqueueDownstream c e) c'"
      using lift_nonpub(2) enqueue_downstream(1) by simp
    have base: "dwu_step (\<iota> t) (ULift (dwe_epoch t) (EnqueueDownstream c e))
                  ((\<iota> t)\<lparr>dwu_store := c'\<rparr>)"
      by (rule dwu_step.ulift_enqueue[OF \<iota>_incumbent_dom \<iota>_incumbent_prod step'])
    have steq: "(\<iota> t)\<lparr>dwu_store := c'\<rparr> = \<iota> t'"
      using lift_nonpub(1) enqueue_downstream by (simp add: \<iota>_def)
    show ?thesis using base steq enqueue_downstream by simp
  next
    case (ack c e)
    have step': "dw_exec_step (dwu_store (\<iota> t)) (Ack c e) c'"
      using lift_nonpub(2) ack(1) by simp
    have base: "dwu_step (\<iota> t) (ULift (dwe_epoch t) (Ack c e)) ((\<iota> t)\<lparr>dwu_store := c'\<rparr>)"
      by (rule dwu_step.ulift_ack[OF \<iota>_incumbent_dom \<iota>_incumbent_prod step'])
    have steq: "(\<iota> t)\<lparr>dwu_store := c'\<rparr> = \<iota> t'"
      using lift_nonpub(1) ack by (simp add: \<iota>_def)
    show ?thesis using base steq ack by simp
  next
    case (do_downstream c e)
    \<comment> \<open>excluded: lift_nonpub's own guard forbids a publish\<close>
    from lift_nonpub(3) do_downstream show ?thesis by blast
  next
    case (crash c)
    have step': "dw_exec_step (dwu_store (\<iota> t)) (Crash c) c'"
      using lift_nonpub(2) crash(1) by simp
    have base: "dwu_step (\<iota> t) (ULift (dwe_epoch t) (Crash c)) ((\<iota> t)\<lparr>dwu_store := c'\<rparr>)"
      by (rule dwu_step.ulift_nonprod[OF \<iota>_incumbent_dom _ step']) simp
    have steq: "(\<iota> t)\<lparr>dwu_store := c'\<rparr> = \<iota> t'"
      using lift_nonpub(1) crash by (simp add: \<iota>_def)
    show ?thesis using base steq crash by simp
  next
    case (recover c)
    have step': "dw_exec_step (dwu_store (\<iota> t)) Recover c'"
      using lift_nonpub(2) recover(1) by simp
    have base: "dwu_step (\<iota> t) (ULift (dwe_epoch t) Recover) ((\<iota> t)\<lparr>dwu_store := c'\<rparr>)"
      by (rule dwu_step.ulift_nonprod[OF \<iota>_incumbent_dom _ step']) simp
    have steq: "(\<iota> t)\<lparr>dwu_store := c'\<rparr> = \<iota> t'"
      using lift_nonpub(1) recover by (simp add: \<iota>_def)
    show ?thesis using base steq recover by simp
  next
    case (observe f)
    have step': "dw_exec_step (dwu_store (\<iota> t)) (Observe f) c'"
      using lift_nonpub(2) observe(1) by simp
    have base: "dwu_step (\<iota> t) (ULift (dwe_epoch t) (Observe f)) ((\<iota> t)\<lparr>dwu_store := c'\<rparr>)"
      by (rule dwu_step.ulift_nonprod[OF \<iota>_incumbent_dom _ step']) simp
    have steq: "(\<iota> t)\<lparr>dwu_store := c'\<rparr> = \<iota> t'"
      using lift_nonpub(1) observe by (simp add: \<iota>_def)
    show ?thesis using base steq observe by simp
  qed
next
  case (publish_emit c e c')
  \<comment> \<open>@{term "a = DoDownstream c e"}; ledger gets one emission at (LSN, epoch)\<close>
  define x where "x = \<lparr> ue_stamp = length (dwu_journal (\<iota> t)), ue_gen = dwe_epoch t,
                        ue_pay = ULog (c, e) \<rparr>"
  have step': "dw_exec_step (dwu_store (\<iota> t)) (DoDownstream c e) c'"
    using publish_emit by simp
  have base: "dwu_step (\<iota> t) (ULift (dwe_epoch t) (DoDownstream c e))
                ((\<iota> t)\<lparr>dwu_store := c',
                       dwu_sent := dwu_sent (\<iota> t) @ [x],
                       dwu_accepted := dwu_accepted (\<iota> t)
                         @ (if dwu_fence (\<iota> t) \<le> ue_gen x then [x] else [])\<rparr>)"
    by (rule dwu_step.ulift_publish[OF \<iota>_incumbent_dom \<iota>_incumbent_prod step' x_def])
  have srch: "exec_src_hist c' = exec_src_hist (dwe_core t)"
    using step' by (cases rule: dw_exec_step.cases) simp_all
  have steq: "(\<iota> t)\<lparr>dwu_store := c',
              dwu_sent := dwu_sent (\<iota> t) @ [x],
              dwu_accepted := dwu_accepted (\<iota> t)
                @ (if dwu_fence (\<iota> t) \<le> ue_gen x then [x] else [])\<rparr> = \<iota> t'"
    using publish_emit srch by (simp add: \<iota>_def x_def ulift_def)
  show ?thesis using base steq publish_emit by simp
qed


section \<open>3. THE FUSED-TRIPLE INVERSION PACKAGE (arm / heal / fire adjacency)\<close>

text \<open>These named lemmas invert the recovery triple @{term "UArm g B f"},
  @{term "UHeal g f"}, @{term "UFire g"} at a state, exposing endpoints, the
  ledger stamp agreement (the fired batch is the frozen armed batch), and the
  arm's enabling conditions.  They are STATEMENT-STABLE and reused wholesale by
  I3's U8 multi-writer discipline (both @{text u_disciplined_trace}'s
  @{text ud_cursor_recovery} and @{text solo_disciplined_trace}'s
  @{text sd_reconcile} carry the same triple).\<close>

subsection \<open>3.1 Single-step inversions\<close>

text \<open>@{const UArm}'s enabling conditions: the store is crashed, the frontier is
  within finish, the actor is live, and the batch is gen-tagged and LSN-bounded.\<close>

lemma dwu_step_arm_precond:
  assumes "dwu_step u (UArm g B f) u1"
  shows "(\<exists>c. exec_status (dwu_store u) = Crashed c) \<and> f \<le> exec_finish (dwu_store u)
       \<and> g \<in> dom (dwu_gens u)
       \<and> (\<forall>x \<in> set B. ue_gen x = g \<and> ue_stamp x \<le> length (dwu_journal u))"
  using assms by (cases rule: dwu_step.cases) auto

text \<open>@{const UHeal} moves the store by the relay reconcile image (definitional):
  down-history becomes the frontier-bounded replay, pending clears, status
  recovers; source and base are frozen.\<close>

lemma dwu_step_heal_reconcile:
  assumes "dwu_step u (UHeal g f) u1"
  shows "relay_bounded_replay_reconcile (dwu_store u) f (dwu_store u1)"
  using assms by (cases rule: dwu_step.cases) auto

lemma dwu_step_heal_store_eq:
  assumes "dwu_step u (UHeal g f) u1"
  shows "dwu_store u1 = (dwu_store u)
           \<lparr>exec_down_hist := replay_down_hist (exec_src_hist (dwu_store u))
                                (exec_scope (dwu_store u)) f,
            exec_pending := {}, exec_status := Recovered\<rparr>"
  using dwu_step_heal_reconcile[OF assms]
  by (simp add: relay_bounded_replay_reconcile_def)

text \<open>@{const UFire} appends the FROZEN armed batch (STAMP AGREEMENT: the fired
  batch is exactly the batch the incarnation table names, so a batch armed at
  the pre-crash LSN fires at that same LSN --- journal-frozen through the
  triple), fence-resolved into accepted.\<close>

lemma dwu_step_fire_ledger:
  assumes "dwu_step u (UFire g) u1"
      and "dwu_gens u g = Some (UArmed B)"
  shows "dwu_sent u1 = dwu_sent u @ B
       \<and> dwu_accepted u1 = dwu_accepted u @ (if dwu_fence u \<le> g then B else [])"
  using assms by (cases rule: dwu_step.cases) auto

subsection \<open>3.2 The composite endpoint\<close>

text \<open>The fused triple's endpoint: journal / fence / floor / hwm frozen, the
  incarnation table round-trips to @{const UProd}, the store is the heal image,
  and both ledgers append the batch @{term B} (fence-resolved in accepted).\<close>

lemma fused_triple_endpoint:
  assumes arm: "dwu_step u (UArm g B f) u1"
      and heal: "dwu_step u1 (UHeal g f) u2"
      and fire: "dwu_step u2 (UFire g) u3"
  shows "dwu_journal u3 = dwu_journal u
       \<and> dwu_sent u3 = dwu_sent u @ B
       \<and> dwu_accepted u3 = dwu_accepted u @ (if dwu_fence u \<le> g then B else [])
       \<and> dwu_fence u3 = dwu_fence u
       \<and> dwu_floor u3 = dwu_floor u
       \<and> dwu_hwm u3 = dwu_hwm u
       \<and> dwu_gens u3 = (dwu_gens u)(g \<mapsto> UProd)
       \<and> dwu_store u3 = (dwu_store u)
           \<lparr>exec_down_hist := replay_down_hist (exec_src_hist (dwu_store u))
                                (exec_scope (dwu_store u)) f,
            exec_pending := {}, exec_status := Recovered\<rparr>"
proof -
  note A = dwu_step_arm_inv[OF arm]
  note H = dwu_step_heal_frame[OF heal]
  note Hs = dwu_step_heal_store_eq[OF heal]
  note F = dwu_step_fire_inv[OF fire]
  have g2: "dwu_gens u2 g = Some (UArmed B)"
    using A H by simp
  note Fl = dwu_step_fire_ledger[OF fire g2]
  have store3: "dwu_store u3
      = (dwu_store u)\<lparr>exec_down_hist := replay_down_hist (exec_src_hist (dwu_store u))
                          (exec_scope (dwu_store u)) f,
                      exec_pending := {}, exec_status := Recovered\<rparr>"
    using A H F Hs by simp
  have gens3: "dwu_gens u3 = (dwu_gens u)(g \<mapsto> UProd)"
    using A H F by simp
  show ?thesis
    using A H F Fl store3 gens3 by simp
qed

subsection \<open>3.3 The @{const stamped_at} / @{const ulift} bridge\<close>

text \<open>The cursor-armed batch is the @{const ulift} image of the landed reconcile
  suffix: a payload @{term "(c, e)"} stamped at LSN @{term n}, generation
  @{term g}, embeds as the same @{const ULog} emission the landed
  @{const emitting_reconcile} appends.\<close>

lemma stamped_at_eq_map_ulift:
  "stamped_at n g ps = map ulift (map (\<lambda>(c, e). (n, g, c, e)) ps)"
  by (induction ps)
     (auto simp: stamped_at_def ulift_def e_stamp_def e_epoch_def e_payload_def)


section \<open>4. U1: the landed embedding and reachability pullback\<close>

subsection \<open>4.1 The reconcile and resume construction steps\<close>

text \<open>A landed @{const emitting_reconcile} is simulated, at @{term "\<iota> t"}, by the
  cursor-shaped fused triple, extending any solo tail --- floor 0 makes the
  retained replay the full replay, journal-freeze fixes the stamp, fence 0 makes
  accepted = sent, actor = hwm = epoch.\<close>

lemma \<iota>_emitting_reconcile_solo:
  assumes er: "emitting_reconcile m t f t'"
      and tail: "solo_trace (\<iota> t') ys zs u'"
  shows "\<exists>ws. solo_trace (\<iota> t) ws (DWE_Reconcile m f # zs) u'"
proof -
  define g where "g = dwe_epoch t"
  define R where "R = replay_down_hist (exec_src_hist (dwe_core t)) (exec_scope (dwe_core t)) f"
  define B where "B = stamped_at (length (exec_src_hist (dwe_core t))) g (drop m R)"
  define s0 where "s0 = (dwe_core t)\<lparr>exec_down_hist := R, exec_pending := {}, exec_status := Recovered\<rparr>"
  define u1 where "u1 = (\<iota> t)\<lparr>dwu_gens := (dwu_gens (\<iota> t))(g \<mapsto> UArmed B)\<rparr>"
  define u2 where "u2 = u1\<lparr>dwu_store := s0\<rparr>"
  from er have crashed: "\<exists>c. exec_status (dwe_core t) = Crashed c"
    by (simp add: emitting_reconcile_def)
  from er have fle: "f \<le> exec_finish (dwe_core t)"
    by (simp add: emitting_reconcile_def)
  from er have mle: "m \<le> length R"
    by (simp add: emitting_reconcile_def R_def)
  from er have t'eq:
    "t' = t\<lparr>dwe_core := s0,
            dwe_emitted := dwe_emitted t
              @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core t)), dwe_epoch t, c, e))
                  (drop m R)\<rparr>"
    by (simp add: emitting_reconcile_def R_def s0_def)
  \<comment> \<open>grammar-shape premises\<close>
  have g_eq: "g = dwu_hwm (\<iota> t)" by (simp add: g_def)
  have R_eq: "R = replay_down_hist (retained_hist (\<iota> t)) (exec_scope (dwu_store (\<iota> t))) f"
    by (simp add: R_def retained_hist_def)
  have B_eq: "B = stamped_at (length (dwu_journal (\<iota> t))) g (drop m R)"
    by (simp add: B_def)
  \<comment> \<open>the arm\<close>
  have Bguard: "\<forall>x \<in> set B. ue_gen x = g \<and> ue_stamp x \<le> length (dwu_journal (\<iota> t))"
    by (auto simp: B_def stamped_at_def)
  have arm: "dwu_step (\<iota> t) (UArm g B f) u1"
    unfolding u1_def
    by (rule dwu_step.uarm)
       (use crashed fle Bguard in \<open>simp_all add: g_def domIff\<close>)
  \<comment> \<open>the heal\<close>
  have relay: "relay_bounded_replay_reconcile (dwu_store u1) f s0"
    using crashed fle by (simp add: relay_bounded_replay_reconcile_def u1_def s0_def R_def)
  have heal: "dwu_step u1 (UHeal g f) u2"
    unfolding u2_def by (rule dwu_step.uheal[OF relay])
  \<comment> \<open>the fire, landing on the nose at @{term "\<iota> t'"}\<close>
  have g2: "dwu_gens u2 g = Some (UArmed B)"
    by (simp add: u2_def u1_def)
  have fire0: "dwu_step u2 (UFire g)
        (u2\<lparr>dwu_sent := dwu_sent u2 @ B,
             dwu_accepted := dwu_accepted u2 @ (if dwu_fence u2 \<le> g then B else []),
             dwu_gens := (dwu_gens u2)(g \<mapsto> UProd)\<rparr>)"
    by (rule dwu_step.ufire[OF g2])
  have fireeq:
    "u2\<lparr>dwu_sent := dwu_sent u2 @ B,
        dwu_accepted := dwu_accepted u2 @ (if dwu_fence u2 \<le> g then B else []),
        dwu_gens := (dwu_gens u2)(g \<mapsto> UProd)\<rparr> = \<iota> t'"
    by (simp add: u2_def u1_def s0_def \<iota>_def t'eq g_def B_def
                  stamped_at_eq_map_ulift fun_upd_idem)
  have fire: "dwu_step u2 (UFire g) (\<iota> t')"
    using fire0 fireeq by simp
  \<comment> \<open>assemble the solo reconcile production\<close>
  have "solo_trace (\<iota> t) (UArm g B f # UHeal g f # UFire g # ys)
          (DWE_Reconcile m f # zs) u'"
    by (rule solo_trace.solo_reconcile[OF g_eq R_eq mle B_eq arm heal fire tail])
  then show ?thesis by blast
qed

text \<open>A landed @{const dwe_resume} is simulated, at @{term "\<iota> t"}, by the adjacent
  spawn / release turnover pair, extending any solo tail.\<close>

lemma \<iota>_dwe_resume_solo:
  assumes dr: "dwe_resume t t'"
      and tail: "solo_trace (\<iota> t') ys zs u'"
  shows "\<exists>ws. solo_trace (\<iota> t) ws (DWE_Resume # zs) u'"
proof -
  define u1 where "u1 = (\<iota> t)\<lparr>dwu_gens := (dwu_gens (\<iota> t))(Suc (dwu_hwm (\<iota> t)) \<mapsto> UProd),
                              dwu_hwm := Suc (dwu_hwm (\<iota> t))\<rparr>"
  from dr have rec: "exec_status (dwe_core t) = Recovered"
    by (simp add: dwe_resume_def)
  from dr have t'eq: "t' = t\<lparr>dwe_core := (dwe_core t)\<lparr>exec_status := Running\<rparr>,
                            dwe_epoch := Suc (dwe_epoch t)\<rparr>"
    by (simp add: dwe_resume_def)
  have spawn: "dwu_step (\<iota> t) USpawn u1"
    unfolding u1_def by (rule dwu_step.uspawn)
  have store_u1: "dwu_store u1 = dwe_core t" by (simp add: u1_def)
  have rel0: "dwu_step u1 (URelease (dwu_hwm u1))
        (u1\<lparr>dwu_store := (dwu_store u1)\<lparr>exec_status := Running\<rparr>\<rparr>)"
    by (rule dwu_step.urelease) (simp add: store_u1 rec)
  have releq: "u1\<lparr>dwu_store := (dwu_store u1)\<lparr>exec_status := Running\<rparr>\<rparr> = \<iota> t'"
    by (simp add: u1_def \<iota>_def t'eq fun_eq_iff le_Suc_eq)
  have rel: "dwu_step u1 (URelease (dwu_hwm u1)) (\<iota> t')"
    using rel0 releq by simp
  have "solo_trace (\<iota> t) (USpawn # URelease (dwu_hwm u1) # ys) (DWE_Resume # zs) u'"
    by (rule solo_trace.solo_turnover[OF spawn rel tail])
  then show ?thesis by blast
qed

subsection \<open>4.2 The principals\<close>

text \<open>U1 (P2 amended pin, VERBATIM): every landed temporal trace embeds as a solo
  trace of @{term "\<iota> t"} carrying the SAME dwe action list and landing on the nose
  at @{term "\<iota> t'"}.\<close>

theorem u_landed_embedding:
  assumes "dwe_temporal_trace t xs t'"
  shows "\<exists>ys. solo_trace (\<iota> t) ys xs (\<iota> t')"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  show ?case by (intro exI[of _ "[]"] solo_trace.solo_refl)
next
  case (dwe_label_step t a t' as t'')
  from dwe_label_step.IH obtain ys where ys: "solo_trace (\<iota> t') ys as (\<iota> t'')" ..
  have wf: "wellformed_exec_state (dwu_store (\<iota> t))"
    using dwe_label_step.hyps(1) by simp
  have wfh: "exec_label_preserves_history_wf (dwu_store (\<iota> t)) a"
    using dwe_label_step.hyps(2) by simp
  have step: "dwu_step (\<iota> t) (ULift (dwu_hwm (\<iota> t)) a) (\<iota> t')"
    using \<iota>_dwe_label_sim[OF dwe_label_step.hyps(3)] by simp
  have "solo_trace (\<iota> t) (ULift (dwu_hwm (\<iota> t)) a # ys) (DWE_Label a # as) (\<iota> t'')"
    by (rule solo_trace.solo_lift[OF wf wfh step ys])
  then show ?case by blast
next
  case (dwe_reconcile_step m t f t' as t'')
  from dwe_reconcile_step.IH obtain ys where ys: "solo_trace (\<iota> t') ys as (\<iota> t'')" ..
  from \<iota>_emitting_reconcile_solo[OF dwe_reconcile_step.hyps(1) ys]
  show ?case by blast
next
  case (dwe_resume_step t t' as t'')
  from dwe_resume_step.IH obtain ys where ys: "solo_trace (\<iota> t') ys as (\<iota> t'')" ..
  from \<iota>_dwe_resume_solo[OF dwe_resume_step.hyps(1) ys]
  show ?case by blast
qed

text \<open>U1 corollary (P2 pin, VERBATIM): reachability pulls back along @{term \<iota>}
  --- the landed reachable set embeds in the unified machine's.\<close>

corollary u_reachable_pullback:
  assumes "dwe_reachable t"
  shows "dwu_reachable_w (\<iota> t)"
proof -
  from assms obtain xs
    where xs: "dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2) xs t"
    by (auto simp: dwe_reachable_def)
  from u_landed_embedding[OF xs] obtain ys
    where "solo_trace (\<iota> (dwe_init Map.empty {0, 1} ec2)) ys xs (\<iota> t)" ..
  then have "dwu_temporal_trace (\<iota> (dwe_init Map.empty {0, 1} ec2)) ys (\<iota> t)"
    by (rule solo_trace_imp_dwu_trace)
  then have "dwu_temporal_trace (dwu_init Map.empty {0, 1} ec2) ys (\<iota> t)"
    by (simp add: \<iota>_init)
  then show ?thesis by (auto simp: dwu_reachable_def)
qed


section \<open>5. U2: the solo projection (the block's hardest --- MED)\<close>

lemma \<Pi>_emitted_eq:
  "dwe_emitted (\<Pi> u)
     = map (\<lambda>x. (ue_stamp x, ue_gen x, fst (ulog_of x), snd (ulog_of x)))
         (filter is_ulog (dwu_sent u))"
  by (simp add: \<Pi>_def)

text \<open>Convenience destructor for the fragment invariant.\<close>

lemma solo_invD:
  assumes "solo_inv u"
  shows "dwu_fence u = 0" "dwu_floor u = 0"
    and "dwu_journal u = exec_src_hist (dwu_store u)"
    and "dwu_sent u = dwu_accepted u"
    and "\<forall>x \<in> set (dwu_sent u). is_ulog x"
    and "dwu_gens u = (\<lambda>g. if g \<le> dwu_hwm u then Some UProd else None)"
  using assms by (simp_all add: solo_inv_def)

subsection \<open>5.1 The lift step projects and preserves the invariant\<close>

text \<open>The incumbent unified @{const ULift} projects to the SAME landed
  @{const dwe_step} label (the lift splits DoSource / publish / other), and
  preserves the 6-conjunct @{const solo_inv}: no writer forges the journal /
  source agreement, ledger equality, all-ULog shape, or the gens determination.\<close>

lemma solo_lift_project:
  assumes step: "dwu_step u (ULift (dwu_hwm u) a) u1"
      and inv: "solo_inv u"
  shows "dwe_step (\<Pi> u) a (\<Pi> u1) \<and> solo_inv u1"
  using step
proof (cases rule: dwu_step.cases)
  case (ulift_source c e s')
  have hs: "dw_exec_step (dwu_store u) (DoSource c e) s'" using ulift_source by simp
  have s'eq: "s' = (dwu_store u)\<lparr>exec_src_hist := exec_src_hist (dwu_store u) @ [(c, e)]\<rparr>"
    using hs by (cases rule: dw_exec_step.cases) auto
  have u1eq: "u1 = u\<lparr>dwu_store := s', dwu_journal := dwu_journal u @ [(c, e)]\<rparr>"
    using ulift_source by simp
  have pieq: "\<Pi> u1 = (\<Pi> u)\<lparr>dwe_core := s'\<rparr>" by (simp add: \<Pi>_def u1eq)
  have proj: "dwe_step (\<Pi> u) (DoSource c e) (\<Pi> u1)"
    by (rule dwe_lift_nonpubI[OF _ _ pieq]) (use hs in simp_all)
  have inv1: "solo_inv u1"
    using inv by (simp add: solo_inv_def u1eq s'eq)
  show ?thesis using proj inv1 ulift_source by simp
next
  case (ulift_enqueue c e s')
  have hs: "dw_exec_step (dwu_store u) (EnqueueDownstream c e) s'" using ulift_enqueue by simp
  have s'eq: "exec_src_hist s' = exec_src_hist (dwu_store u)"
    using hs by (cases rule: dw_exec_step.cases) auto
  have u1eq: "u1 = u\<lparr>dwu_store := s'\<rparr>" using ulift_enqueue by simp
  have pieq: "\<Pi> u1 = (\<Pi> u)\<lparr>dwe_core := s'\<rparr>" by (simp add: \<Pi>_def u1eq)
  have proj: "dwe_step (\<Pi> u) (EnqueueDownstream c e) (\<Pi> u1)"
    by (rule dwe_lift_nonpubI[OF _ _ pieq]) (use hs in simp_all)
  have inv1: "solo_inv u1"
    using inv by (simp add: solo_inv_def u1eq s'eq)
  show ?thesis using proj inv1 ulift_enqueue by simp
next
  case (ulift_ack c e s')
  have hs: "dw_exec_step (dwu_store u) (Ack c e) s'" using ulift_ack by simp
  have s'eq: "exec_src_hist s' = exec_src_hist (dwu_store u)"
    using hs by (cases rule: dw_exec_step.cases) auto
  have u1eq: "u1 = u\<lparr>dwu_store := s'\<rparr>" using ulift_ack by simp
  have pieq: "\<Pi> u1 = (\<Pi> u)\<lparr>dwe_core := s'\<rparr>" by (simp add: \<Pi>_def u1eq)
  have proj: "dwe_step (\<Pi> u) (Ack c e) (\<Pi> u1)"
    by (rule dwe_lift_nonpubI[OF _ _ pieq]) (use hs in simp_all)
  have inv1: "solo_inv u1"
    using inv by (simp add: solo_inv_def u1eq s'eq)
  show ?thesis using proj inv1 ulift_ack by simp
next
  case (ulift_publish c e s' x)
  have hs: "dw_exec_step (dwu_store u) (DoDownstream c e) s'" using ulift_publish by simp
  have s'eq: "exec_src_hist s' = exec_src_hist (dwu_store u)"
    using hs by (cases rule: dw_exec_step.cases) auto
  have xeq: "x = \<lparr>ue_stamp = length (dwu_journal u), ue_gen = dwu_hwm u, ue_pay = ULog (c, e)\<rparr>"
    using ulift_publish by simp
  have fence0: "dwu_fence u = 0" and jsrc: "dwu_journal u = exec_src_hist (dwu_store u)"
    using inv by (simp_all add: solo_inv_def)
  have u1eq: "u1 = u\<lparr>dwu_store := s', dwu_sent := dwu_sent u @ [x],
                     dwu_accepted := dwu_accepted u @ [x]\<rparr>"
    using ulift_publish xeq fence0 by simp
  \<comment> \<open>the projected emission agrees with the landed publish stamp\<close>
  have hs': "dw_exec_step (dwe_core (\<Pi> u)) (DoDownstream c e) s'" using hs by simp
  have pieq: "\<Pi> u1 = (\<Pi> u)\<lparr>dwe_core := s',
            dwe_emitted := dwe_emitted (\<Pi> u)
              @ [(length (exec_src_hist (dwe_core (\<Pi> u))), dwe_epoch (\<Pi> u), c, e)]\<rparr>"
    using u1eq xeq jsrc by (simp add: \<Pi>_def is_ulog_def ulog_of_def)
  have proj: "dwe_step (\<Pi> u) (DoDownstream c e) (\<Pi> u1)"
    by (rule dwe_publish_emitI[OF hs' pieq])
  have inv1: "solo_inv u1"
    using inv by (auto simp: solo_inv_def u1eq s'eq xeq is_ulog_def)
  show ?thesis using proj inv1 ulift_publish by simp
next
  case (ulift_nonprod s')
  have hs: "dw_exec_step (dwu_store u) a s'" using ulift_nonprod by simp
  have nprod: "\<not> u_production_label a" using ulift_nonprod by simp
  have s'eq: "exec_src_hist s' = exec_src_hist (dwu_store u)"
    using hs nprod by (cases rule: dw_exec_step.cases) auto
  have u1eq: "u1 = u\<lparr>dwu_store := s'\<rparr>" using ulift_nonprod by simp
  have nodown: "\<forall>c e. a \<noteq> DoDownstream c e" using nprod by auto
  have pieq: "\<Pi> u1 = (\<Pi> u)\<lparr>dwe_core := s'\<rparr>" by (simp add: \<Pi>_def u1eq)
  have proj: "dwe_step (\<Pi> u) a (\<Pi> u1)"
    by (rule dwe_lift_nonpubI[OF _ nodown pieq]) (use hs in simp)
  have inv1: "solo_inv u1"
    using inv by (simp add: solo_inv_def u1eq s'eq)
  show ?thesis using proj inv1 by simp
qed

subsection \<open>5.2 The fused triple projects to a landed reconcile\<close>

text \<open>A cursor-armed batch is all-ULog and projects to the landed reconcile
  suffix.\<close>

lemma filter_is_ulog_stamped_at [simp]:
  "filter is_ulog (stamped_at n g ps) = stamped_at n g ps"
  by (induction ps) (auto simp: stamped_at_def is_ulog_def)

lemma map_proj_stamped_at [simp]:
  "map (\<lambda>x. (ue_stamp x, ue_gen x, ulog_of x)) (stamped_at n g ps)
     = map (\<lambda>p. (n, g, p)) ps"
  by (induction ps) (auto simp: stamped_at_def ulog_of_def)

text \<open>U2's central case: on a solo state, the fused recovery triple projects to
  exactly the landed @{const emitting_reconcile} (floor 0 makes the retained
  replay the full replay; journal-inv + actor fix the stamp; fence 0 makes
  accepted = sent), and preserves @{const solo_inv}.\<close>

lemma solo_reconcile_project:
  assumes inv: "solo_inv u"
      and g_eq: "g = dwu_hwm u"
      and R_eq: "R = replay_down_hist (retained_hist u) (exec_scope (dwu_store u)) f"
      and mle: "m \<le> length R"
      and B_eq: "B = stamped_at (length (dwu_journal u)) g (drop m R)"
      and arm: "dwu_step u (UArm g B f) u1"
      and heal: "dwu_step u1 (UHeal g f) u2"
      and fire: "dwu_step u2 (UFire g) u3"
  shows "emitting_reconcile m (\<Pi> u) f (\<Pi> u3) \<and> solo_inv u3"
proof -
  \<comment> \<open>fragment invariant fields\<close>
  have fence0: "dwu_fence u = 0" and floor0: "dwu_floor u = 0"
    and jsrc: "dwu_journal u = exec_src_hist (dwu_store u)"
    and sent_acc: "dwu_sent u = dwu_accepted u"
    and allulog: "\<forall>x \<in> set (dwu_sent u). is_ulog x"
    and gensu: "dwu_gens u = (\<lambda>g'. if g' \<le> dwu_hwm u then Some UProd else None)"
    using inv by (simp_all add: solo_inv_def)
  \<comment> \<open>arm enabling conditions\<close>
  have crashed: "\<exists>c. exec_status (dwu_store u) = Crashed c"
    and fle: "f \<le> exec_finish (dwu_store u)"
    using dwu_step_arm_precond[OF arm] by simp_all
  \<comment> \<open>the retained replay is the full replay (floor 0)\<close>
  have Rfull: "R = replay_down_hist (exec_src_hist (dwu_store u)) (exec_scope (dwu_store u)) f"
    using R_eq floor0 by (simp add: retained_hist_def)
  \<comment> \<open>fused triple endpoint\<close>
  note ep = fused_triple_endpoint[OF arm heal fire]
  have store3: "dwu_store u3 = (dwu_store u)
      \<lparr>exec_down_hist := replay_down_hist (exec_src_hist (dwu_store u))
                            (exec_scope (dwu_store u)) f,
       exec_pending := {}, exec_status := Recovered\<rparr>"
    using ep by simp
  have sent3: "dwu_sent u3 = dwu_sent u @ B" using ep by simp
  have acc3: "dwu_accepted u3 = dwu_accepted u @ B"
    using ep fence0 g_eq by simp
  have hwm3: "dwu_hwm u3 = dwu_hwm u" using ep by simp
  have gens3: "dwu_gens u3 = dwu_gens u"
    using ep g_eq gensu by (simp add: fun_upd_idem)
  have jour3: "dwu_journal u3 = dwu_journal u" using ep by simp
  \<comment> \<open>Pi u3 is the landed reconcile image (batch projects to the reconcile suffix)\<close>
  have Perm: "\<Pi> u3 = (\<Pi> u)
      \<lparr>dwe_core := (dwu_store u)
          \<lparr>exec_down_hist := replay_down_hist (exec_src_hist (dwu_store u))
                                (exec_scope (dwu_store u)) f,
           exec_pending := {}, exec_status := Recovered\<rparr>,
       dwe_emitted := dwe_emitted (\<Pi> u)
         @ map (\<lambda>(c, e). (length (exec_src_hist (dwu_store u)), dwu_hwm u, c, e)) (drop m R)\<rparr>"
    using store3 sent3 hwm3
    by (simp add: \<Pi>_def B_eq jsrc g_eq)
  have ER: "emitting_reconcile m (\<Pi> u) f (\<Pi> u3)"
    unfolding emitting_reconcile_def
  proof (intro conjI)
    show "\<exists>c. exec_status (dwe_core (\<Pi> u)) = Crashed c" using crashed by simp
  next
    show "f \<le> exec_finish (dwe_core (\<Pi> u))" using fle by simp
  next
    show "m \<le> length (replay_down_hist (exec_src_hist (dwe_core (\<Pi> u)))
                        (exec_scope (dwe_core (\<Pi> u))) f)"
      using mle Rfull by simp
  next
    show "\<Pi> u3 = (\<Pi> u)
        \<lparr>dwe_core := (dwe_core (\<Pi> u))
            \<lparr>exec_down_hist := replay_down_hist (exec_src_hist (dwe_core (\<Pi> u)))
                                  (exec_scope (dwe_core (\<Pi> u))) f,
             exec_pending := {}, exec_status := Recovered\<rparr>,
         dwe_emitted := dwe_emitted (\<Pi> u)
           @ map (\<lambda>(c, e). (length (exec_src_hist (dwe_core (\<Pi> u))), dwe_epoch (\<Pi> u), c, e))
               (drop m (replay_down_hist (exec_src_hist (dwe_core (\<Pi> u)))
                          (exec_scope (dwe_core (\<Pi> u))) f))\<rparr>"
      using Perm Rfull by simp
  qed
  \<comment> \<open>solo_inv preserved\<close>
  have inv3: "solo_inv u3"
    unfolding solo_inv_def
  proof (intro conjI)
    show "dwu_fence u3 = 0" using ep fence0 by simp
    show "dwu_floor u3 = 0" using ep floor0 by simp
    show "dwu_journal u3 = exec_src_hist (dwu_store u3)"
      using jour3 jsrc store3 by simp
    show "dwu_sent u3 = dwu_accepted u3" using sent3 acc3 sent_acc by simp
    show "\<forall>x \<in> set (dwu_sent u3). is_ulog x"
      using sent3 allulog by (auto simp: B_eq stamped_at_def is_ulog_def)
    show "dwu_gens u3 = (\<lambda>g'. if g' \<le> dwu_hwm u3 then Some UProd else None)"
      using gens3 hwm3 gensu by simp
  qed
  show ?thesis using ER inv3 by blast
qed

subsection \<open>5.3 The turnover pair projects to a landed resume\<close>

text \<open>On a solo state, the adjacent spawn / release pair projects to exactly the
  landed @{const dwe_resume} (hwm counts what epoch counts) and preserves
  @{const solo_inv} (the gens table extends to @{term "Suc (dwu_hwm u)"}).\<close>

lemma solo_turnover_project:
  assumes inv: "solo_inv u"
      and spawn: "dwu_step u USpawn u1"
      and rel: "dwu_step u1 (URelease (dwu_hwm u1)) u2"
  shows "dwe_resume (\<Pi> u) (\<Pi> u2) \<and> solo_inv u2"
proof -
  have fence0: "dwu_fence u = 0" and floor0: "dwu_floor u = 0"
    and jsrc: "dwu_journal u = exec_src_hist (dwu_store u)"
    and sent_acc: "dwu_sent u = dwu_accepted u"
    and allulog: "\<forall>x \<in> set (dwu_sent u). is_ulog x"
    and gensu: "dwu_gens u = (\<lambda>g'. if g' \<le> dwu_hwm u then Some UProd else None)"
    using inv by (simp_all add: solo_inv_def)
  note S = dwu_step_spawn_inv[OF spawn]
  note Rf = dwu_step_release_frame[OF rel]
  have rec: "exec_status (dwu_store u1) = Recovered"
    using rel by (cases rule: dwu_step.cases) auto
  have rel_store: "dwu_store u2 = (dwu_store u1)\<lparr>exec_status := Running\<rparr>"
    using rel by (cases rule: dwu_step.cases) auto
  \<comment> \<open>the landed resume\<close>
  have DR: "dwe_resume (\<Pi> u) (\<Pi> u2)"
    unfolding dwe_resume_def
  proof (intro conjI)
    show "exec_status (dwe_core (\<Pi> u)) = Recovered" using rec S by simp
  next
    show "\<Pi> u2 = (\<Pi> u)\<lparr>dwe_core := (dwe_core (\<Pi> u))\<lparr>exec_status := Running\<rparr>,
                        dwe_epoch := Suc (dwe_epoch (\<Pi> u))\<rparr>"
      using rel_store S Rf by (simp add: \<Pi>_def)
  qed
  \<comment> \<open>solo_inv preserved\<close>
  have gens2: "dwu_gens u2 = (\<lambda>g'. if g' \<le> dwu_hwm u2 then Some UProd else None)"
    using S Rf gensu by (auto simp: fun_eq_iff le_Suc_eq)
  have inv2: "solo_inv u2"
    unfolding solo_inv_def
  proof (intro conjI)
    show "dwu_fence u2 = 0" using S Rf fence0 by simp
    show "dwu_floor u2 = 0" using S Rf floor0 by simp
    show "dwu_journal u2 = exec_src_hist (dwu_store u2)"
      using S Rf jsrc rel_store by simp
    show "dwu_sent u2 = dwu_accepted u2" using S Rf sent_acc by simp
    show "\<forall>x \<in> set (dwu_sent u2). is_ulog x" using S Rf allulog by simp
    show "dwu_gens u2 = (\<lambda>g'. if g' \<le> dwu_hwm u2 then Some UProd else None)" by (rule gens2)
  qed
  show ?thesis using DR inv2 by blast
qed

subsection \<open>5.4 The principal\<close>

text \<open>U2 (P2 amended pin, VERBATIM): a solo trace of a solo-invariant state
  projects to a landed temporal trace carrying the SAME dwe action list, and the
  invariant is preserved throughout.  Induction over the four grammar productions
  threading the 6-conjunct @{const solo_inv}.\<close>

theorem u_solo_projection:
  assumes "solo_trace u ys zs u'"
      and "solo_inv u"
  shows "dwe_temporal_trace (\<Pi> u) zs (\<Pi> u') \<and> solo_inv u'"
  using assms
proof (induction rule: solo_trace.induct)
  case (solo_refl u)
  show ?case using solo_refl.prems by (simp add: dwe_temporal_trace.dwe_refl)
next
  case (solo_lift u a u1 ys zs u')
  from solo_lift_project[OF solo_lift.hyps(3) solo_lift.prems]
  have proj: "dwe_step (\<Pi> u) a (\<Pi> u1)" and inv1: "solo_inv u1" by simp_all
  from solo_lift.IH[OF inv1]
  have tr: "dwe_temporal_trace (\<Pi> u1) zs (\<Pi> u')" and inv': "solo_inv u'" by simp_all
  have wf: "wellformed_exec_state (dwe_core (\<Pi> u))"
    using solo_lift.hyps(1) by simp
  have wfh: "exec_label_preserves_history_wf (dwe_core (\<Pi> u)) a"
    using solo_lift.hyps(2) by simp
  have "dwe_temporal_trace (\<Pi> u) (DWE_Label a # zs) (\<Pi> u')"
    by (rule dwe_temporal_trace.dwe_label_step[OF wf wfh proj tr])
  then show ?case using inv' by blast
next
  case (solo_reconcile g u R f m B u1 u2 u3 ys zs u')
  from solo_reconcile_project[OF solo_reconcile.prems solo_reconcile.hyps(1-7)]
  have er: "emitting_reconcile m (\<Pi> u) f (\<Pi> u3)" and inv3: "solo_inv u3" by simp_all
  from solo_reconcile.IH[OF inv3]
  have tr: "dwe_temporal_trace (\<Pi> u3) zs (\<Pi> u')" and inv': "solo_inv u'" by simp_all
  have "dwe_temporal_trace (\<Pi> u) (DWE_Reconcile m f # zs) (\<Pi> u')"
    by (rule dwe_temporal_trace.dwe_reconcile_step[OF er tr])
  then show ?case using inv' by blast
next
  case (solo_turnover u u1 u2 ys zs u')
  from solo_turnover_project[OF solo_turnover.prems solo_turnover.hyps(1,2)]
  have dr: "dwe_resume (\<Pi> u) (\<Pi> u2)" and inv2: "solo_inv u2" by simp_all
  from solo_turnover.IH[OF inv2]
  have tr: "dwe_temporal_trace (\<Pi> u2) zs (\<Pi> u')" and inv': "solo_inv u'" by simp_all
  have "dwe_temporal_trace (\<Pi> u) (DWE_Resume # zs) (\<Pi> u')"
    by (rule dwe_temporal_trace.dwe_resume_step[OF dr tr])
  then show ?case using inv' by blast
qed


section \<open>6. U3: the hazard and sink-delta commutes\<close>

text \<open>U3 @{text u_hazards_once} (P2 amended pin, VERBATIM): on an all-ULog state
  with the ledgers equal and the journal = source, every unified effect hazard is
  its landed counterpart under @{term \<Pi>}.  The amended assumes-bundle is
  load-bearing: without all-ULog, @{term \<Pi>} filters non-log entries and the
  premature commute fails.\<close>

theorem u_hazards_once:
  assumes "dwu_sent t = dwu_accepted t"
      and "dwu_journal t = exec_src_hist (dwu_store t)"
      and "\<forall>x \<in> set (dwu_sent t). is_ulog x"
  shows "(u_premature t \<longleftrightarrow> premature (\<Pi> t))
       \<and> (u_duplicate t \<longleftrightarrow> duplicate (\<Pi> t))
       \<and> (u_effect_unsafe t \<longleftrightarrow> effect_unsafe (\<Pi> t))"
proof -
  note se = assms(1) and js = assms(2) and ul = assms(3)
  have flt: "filter is_ulog (dwu_sent t) = dwu_sent t"
    using ul by (simp add: filter_id_conv)
  have emit: "dwe_emitted (\<Pi> t)
      = map (\<lambda>x. (ue_stamp x, ue_gen x, fst (ulog_of x), snd (ulog_of x))) (dwu_sent t)"
    by (simp add: \<Pi>_def flt)
  \<comment> \<open>duplicate: the two views read the same payload list\<close>
  have dup: "u_duplicate t \<longleftrightarrow> duplicate (\<Pi> t)"
    by (simp add: u_duplicate_def duplicate_def map_e_payload_\<Pi>_emitted se)
  \<comment> \<open>per-emission justification bridge (all-ULog + journal = source)\<close>
  have bridge: "\<And>x. x \<in> set (dwu_sent t) \<Longrightarrow>
      (u_justified t x \<longleftrightarrow>
        justified_at (exec_src_hist (dwu_store t))
          (ue_stamp x, ue_gen x, fst (ulog_of x), snd (ulog_of x)))"
  proof -
    fix x assume "x \<in> set (dwu_sent t)"
    then have "is_ulog x" using ul by blast
    then obtain p where p: "ue_pay x = ULog p"
      by (auto simp: is_ulog_def split: upayload.splits)
    show "u_justified t x \<longleftrightarrow>
        justified_at (exec_src_hist (dwu_store t))
          (ue_stamp x, ue_gen x, fst (ulog_of x), snd (ulog_of x))"
      using js p
      by (simp add: u_justified_def justified_at_def ulog_of_def e_stamp_def e_payload_def)
  qed
  have prem: "u_premature t \<longleftrightarrow> premature (\<Pi> t)"
  proof -
    have "premature (\<Pi> t) \<longleftrightarrow>
        (\<exists>x \<in> set (dwu_sent t). \<not> justified_at (exec_src_hist (dwu_store t))
           (ue_stamp x, ue_gen x, fst (ulog_of x), snd (ulog_of x)))"
      by (simp add: premature_def emit)
    also have "... \<longleftrightarrow> (\<exists>x \<in> set (dwu_sent t). \<not> u_justified t x)"
      using bridge by blast
    also have "... \<longleftrightarrow> u_premature t"
      by (simp add: u_premature_def se)
    finally show ?thesis ..
  qed
  have "u_effect_unsafe t \<longleftrightarrow> effect_unsafe (\<Pi> t)"
    using prem dup by (simp add: u_effect_unsafe_def effect_unsafe_def)
  then show ?thesis using prem dup by blast
qed

text \<open>U3 @{text u_sink_delta_commutes} (P2 amended pin, VERBATIM): on a ledger-equal
  floor-0 state, the sink-delta, the loss predicate and at-least-once all commute
  with @{term \<Pi>}.  Floor 0 is load-bearing: at a positive floor the retained
  replay differs from the landed full replay.\<close>

theorem u_sink_delta_commutes:
  fixes t :: "(nat, nat) dwu_state"
  assumes "dwu_sent t = dwu_accepted t"
      and "dwu_floor t = 0"
  shows "u_sink_delta f t = sink_delta f (\<Pi> t)
       \<and> (u_lost f t \<longleftrightarrow> lost_effect f (\<Pi> t))
       \<and> (u_at_least_once_at f t \<longleftrightarrow> at_least_once_at f (\<Pi> t))"
proof -
  note se = assms(1) and fl = assms(2)
  have retf: "retained_hist t = exec_src_hist (dwu_store t)"
    using fl by (simp add: retained_hist_def)
  have pay: "set (log_payloads (dwu_accepted t)) = e_payload ` set (dwe_emitted (\<Pi> t))"
    using se by (simp add: set_\<Pi>_emitted_payloads)
  have sd: "u_sink_delta f t = sink_delta f (\<Pi> t)"
    by (simp add: u_sink_delta_def sink_delta_def retf pay)
  have lost: "u_lost f t \<longleftrightarrow> lost_effect f (\<Pi> t)"
    by (simp add: u_lost_def lost_effect_def retf pay)
  have alo: "u_at_least_once_at f t \<longleftrightarrow> at_least_once_at f (\<Pi> t)"
    by (simp add: u_at_least_once_at_def at_least_once_at_def retf pay)
  show ?thesis using sd lost alo by blast
qed

end
