(*  Title:       Dual_Write_Effect_Channel_Blind.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    NO CHANNEL-BLIND RE-DRIVE POLICY ESCAPES: the class-level for-all
    law of the D-091 channel/fencing wave (ladder section 35) --- the
    wave's OPTIONAL stretch slice, built under the design gate's
    under-budget authorization, additive post-freeze under the freeze's
    own protocol (no landed statement, proof, definition, name, import,
    or session-DAG change).

    FROM ONE POLICY TO THE WHOLE CLASS.  The zombie slice (ladder
    section 33) defeated one recovery: the honest sink-reading escape,
    the very policy that escapes the landed dilemma.  This theory
    defeats every recovery of its kind at once.  A re-drive policy is
    CHANNEL-BLIND when its batch factors through everything EXCEPT the
    wire: the whole inner state (the durable store, the sent ledger,
    the epoch), the sink's accepted record, and the fence --- formally,
    through the (inner, accepted, fence) projection triple, every
    record surface of the machine except dwc_channel.  The landed
    sink-reading delta is IN the class (reading the SINK'S RECORD is
    not seeing the WIRE), and the unfenced escape composite is
    literally the class relation instantiated at it --- so the law
    strictly generalizes the zombie defeat, and its content is: on this
    machine the channel is the new hidden state.  Reading the sink
    remains necessary (the landed dilemma, untouched); no channel-blind
    read whatsoever is sufficient.

    THE LAW AND ITS PROOF PLAN (gate amendment MF-5, the ratified
    two-case membership split; the original three-case sketch is
    retired).  The designed pair: y1 is the zombie run's crash state
    (one superseded copy in flight), y2 its loss successor by
    DWC_Lose 0 --- the same state with an empty wire.  Equal inner,
    equal accepted record, equal fence, both reachable, so every
    channel-blind policy emits the SAME batch B on both members.
    Split on whether the crash-straddling payload is in B.  If it is
    NOT, the empty-wire member loses: the re-drive's accepted record
    carries only the first effect and B's payloads, its wire holds
    nothing, and at-least-once fails at the crash frontier.  If it IS,
    the in-flight member duplicates POST-ARRIVAL: the policy's own
    batch copy is synchronously accepted, and the wire's superseded
    copy then arrives at the never-raised fence zero --- the zombie
    completes the defeat one wire event after the recovery.  The horn
    crossing is deliberate and visible in the statement itself: the
    duplicate horn is an arrival successor, the loss horn the
    composite's own result.  The accepted-unsafe-persists-under-arrive
    helper pins the hazard algebra the split rides on: an arrival can
    append to the record but never heal it.

    WHAT THE FENCE HAS TO DO WITH IT.  The policy-generic relation is
    the UNFENCED composite's shape --- batch synchronously accepted,
    fence unchanged --- so the law quantifies over recoveries that
    change what is READ, never what the wire may DO.  The fenced
    composite is deliberately NOT an instance (it moves the fence
    field): the fence escapes the defeat not by reading more but by
    changing ACCEPTANCE.  This theory is thereby the necessity
    companion of the fence family: within the whole channel-blind
    reading class there is no escape hatch; the slice-3 positive shows
    the acceptance side has one.

    NOT CLAIMED.  No weakening of any landed B-side result: the landed
    escape stays correct on its own machine (where send and receive
    are one atomic event and the wire cannot outrun the read), the
    landed dilemma keeps its polarity, and the defeat here is the
    wave's designed pair --- no new machine, no new premise class.
    The loss horn is the state-level at-least-once reading at the
    composite's own frontier (boundary row 4's terminal-state stand-in
    status, inherited verbatim); nothing temporal is claimed.

    IMPORTS: Dual_Write_Effect_Fencing alone --- through it the zombie
    witness kit (the crash state, its inner, the slice-3 guard facts),
    the channel machine, and the landed policy vocabulary.  The
    terminal branch enters no cone of this theory.

    PROVENANCE: owner decision D-091; the channel-wave design gate
    (paper/dual_write/theory_backlog/channel_wave/CHANNEL_WAVE_DESIGN.md
    section 4.12, ratified COHERENT-GO with amendments MF-1..MF-10 by
    channel_wave/GATE_REPORT.md, 2026-07-07; this slice = the gate
    report's section-3 tail OPTIONAL item, gate P3_EGate35, proof plan
    amendment MF-5).

    In-source ML oracle gates are STRIPPED at landing: oracle-freedom
    is certified by scratch-side per-slice gate sessions with
    confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Channel_Blind
  imports Dual_Write_Effect_Fencing
begin

section \<open>The channel-blind policy class and the policy-generic re-drive\<close>

text \<open>
  The class, mirroring the landed @{const store_measured} pattern one
  observation rung up: a policy is channel-blind when its batch
  factors through the (inner, accepted, fence) projection triple ---
  it may read the WHOLE inner state (the durable store, the sent
  ledger, the epoch), the sink's durable accepted record, and the
  fence; the one field outside the triple is the wire itself.  The
  landed sink-reading delta is a member (below), which is the point:
  the class contains the strongest reader the landed corpus has.
\<close>

type_synonym dwc_redrive_policy =
  "(nat, nat) dwc_state \<Rightarrow> (src_coord \<times> (nat, nat) source_event) list"

definition dwc_channel_blind :: "dwc_redrive_policy \<Rightarrow> bool" where
  "dwc_channel_blind P \<longleftrightarrow>
     (\<exists>g. \<forall>t. P t = g (dwc_inner t, dwc_accepted t, dwc_fence t))"

text \<open>
  The policy-generic re-drive: the unfenced composite's exact shape
  with the policy's batch --- from a crashed inner, the landed heal,
  the batch stamped at the crash-time epoch and appended to the sent
  ledger AND synchronously into the accepted record, the fence
  UNCHANGED.  A relation, never a machine action --- exactly the
  landed treatment of @{const policy_redrive}.  Because the fence
  field is untouched, the fenced composite is deliberately NOT an
  instance: the class quantifies over what recovery READS, never over
  what the wire may DO.
\<close>

definition dwc_policy_redrive
  :: "dwc_redrive_policy \<Rightarrow> frontier \<Rightarrow> (nat, nat) dwc_state
      \<Rightarrow> (nat, nat) dwc_state \<Rightarrow> bool"
where
  "dwc_policy_redrive P f t t' \<longleftrightarrow>
     (\<exists>c. exec_status (dwe_core (dwc_inner t)) = Crashed c)
   \<and> f \<le> exec_finish (dwe_core (dwc_inner t))
   \<and> t' = t\<lparr>dwc_inner := (dwc_inner t)
              \<lparr>dwe_core := (dwe_core (dwc_inner t))
                 \<lparr>exec_down_hist := dwc_replay f t,
                  exec_pending := {},
                  exec_status := Recovered\<rparr>,
               dwe_emitted := dwe_emitted (dwc_inner t)
                 @ map (dwc_stamp t) (P t)\<rparr>,
            dwc_accepted := dwc_accepted t @ map (dwc_stamp t) (P t)\<rparr>"

text \<open>The unique result state, as a function (witness construction).\<close>

definition dwc_policy_result
  :: "dwc_redrive_policy \<Rightarrow> frontier \<Rightarrow> (nat, nat) dwc_state
      \<Rightarrow> (nat, nat) dwc_state"
where
  "dwc_policy_result P f t =
     t\<lparr>dwc_inner := (dwc_inner t)
         \<lparr>dwe_core := (dwe_core (dwc_inner t))
            \<lparr>exec_down_hist := dwc_replay f t,
             exec_pending := {},
             exec_status := Recovered\<rparr>,
          dwe_emitted := dwe_emitted (dwc_inner t)
            @ map (dwc_stamp t) (P t)\<rparr>,
       dwc_accepted := dwc_accepted t @ map (dwc_stamp t) (P t)\<rparr>"

lemma dwc_policy_redriveI:
  assumes "\<exists>c. exec_status (dwe_core (dwc_inner t)) = Crashed c"
      and "f \<le> exec_finish (dwe_core (dwc_inner t))"
  shows "dwc_policy_redrive P f t (dwc_policy_result P f t)"
  using assms by (simp add: dwc_policy_redrive_def dwc_policy_result_def)

lemma dwc_policy_redrive_result:
  assumes "dwc_policy_redrive P f t t'"
  shows "t' = dwc_policy_result P f t"
  using assms by (simp add: dwc_policy_redrive_def dwc_policy_result_def)

lemma dwc_policy_result_components:
  "dwc_channel (dwc_policy_result P f t) = dwc_channel t"
  "dwc_accepted (dwc_policy_result P f t)
     = dwc_accepted t @ map (dwc_stamp t) (P t)"
  "dwc_fence (dwc_policy_result P f t) = dwc_fence t"
  "dwe_epoch (dwc_inner (dwc_policy_result P f t)) = dwe_epoch (dwc_inner t)"
  "dwe_emitted (dwc_inner (dwc_policy_result P f t))
     = dwe_emitted (dwc_inner t) @ map (dwc_stamp t) (P t)"
  "dwc_src (dwc_policy_result P f t) = dwc_src t"
  "dwc_scope (dwc_policy_result P f t) = dwc_scope t"
  "exec_status (dwe_core (dwc_inner (dwc_policy_result P f t))) = Recovered"
  by (simp_all add: dwc_policy_result_def dwc_src_def dwc_scope_def)

lemma dwc_policy_result_replay:
  "dwc_replay f' (dwc_policy_result P f t) = dwc_replay f' t"
  by (simp add: dwc_replay_def dwc_policy_result_components)

text \<open>
  The constant-batch projection onto the landed relation --- the same
  transfer engine as the slice-1 composites --- and its heal corollary
  by citation: every re-drive of the class relation heals every scoped
  store mismatch at its own frontier.  The law below therefore defeats
  the class WITH the store healed on both members: the store heals,
  the effect does not, at class level.
\<close>

lemma dwc_policy_redrive_inner_projects:
  assumes "dwc_policy_redrive P f t t'"
  shows "policy_redrive (\<lambda>_. P t) (dwc_inner t) f (dwc_inner t')"
  using assms
  by (simp add: dwc_policy_redrive_def policy_redrive_def dwc_stamp_unfold
                dwc_replay_def dwc_src_def dwc_scope_def)

lemma dwc_policy_redrive_heals:
  assumes "dwc_policy_redrive P f t t'"
  shows "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core (dwc_inner t')) f) f k"
  by (rule policy_redrive_heals[OF dwc_policy_redrive_inner_projects[OF assms]])

text \<open>
  Non-vacuity at both levels, and the point of the class.  The
  unfenced escape composite IS the class relation instantiated at the
  accepted-record delta; and that delta is channel-blind --- it reads
  the inner (for the committed replay) and the accepted record (for
  the freshness filter), never the wire.  The landed escape recipe is
  therefore INSIDE the defeated class: the zombie slice defeated it as
  one policy; the law below defeats everything it exemplifies.
\<close>

lemma dwc_escape_redrive_is_policy_instance:
  fixes t :: "(nat, nat) dwc_state"
  shows "dwc_escape_redrive f t t' \<longleftrightarrow>
           dwc_policy_redrive (dwc_sink_delta f) f t t'"
  by (simp add: dwc_escape_redrive_def dwc_policy_redrive_def)

lemma sink_delta_channel_blind: "dwc_channel_blind (dwc_sink_delta f)"
  unfolding dwc_channel_blind_def
  by (intro exI[of _ "\<lambda>(i, a, fn).
        filter (\<lambda>p. p \<notin> e_payload ` set a)
          (replay_down_hist (exec_src_hist (dwe_core i))
             (exec_scope (dwe_core i)) f)"])
     (simp add: dwc_sink_delta_def dwc_replay_def dwc_src_def dwc_scope_def)

section \<open>The designed pair: equal everything but the wire\<close>

text \<open>
  The y-pair.  Member one is the zombie run's crash state itself
  (@{const z8}: the superseded copy @{term "(2, 0, ec2, e2)"} in
  flight, the first effect accepted, fence never raised); member two
  is its loss successor by @{term "DWC_Lose 0"} --- the SAME state
  with an empty wire.  Equal inner, equal accepted record, equal
  fence, both reachable: to every channel-blind policy the two are
  one state, and the wire difference is precisely what the policy
  cannot see.

  The pair exists BECAUSE the machine has a loss rule (fold-in (a) of
  the wave design, its load-bearing use): at the never-raised fence
  zero the arrive rule's drop guard is unsatisfiable --- an arrival
  at fence zero is always accepted, writing the record --- so below
  the fence era the only rule that removes an in-flight entry without
  touching the accepted record is @{const dwc_lose}.  The loss
  successor coincides, field for field, with the wipe twin's
  post-crash state (@{const w8}, the slice-2 control): losing a
  singleton wire IS the wipe, reached here by an ordinary action of
  the REAL machine rather than by the twin's altered crash rule.
\<close>

definition y1 :: "(nat, nat) dwc_state" where "y1 = z8"

definition y2 :: "(nat, nat) dwc_state" where
  "y2 = mkZ zi8 [] [(1, 0, ec1, e1)] 0"

lemma y_lose: "dwc_lose y1 0 y2"
  by (rule dwc_loseI) (simp_all add: y1_def y2_def z8_def mkZ_def)

lemma reach_y1: "dwc_reachable y1"
  unfolding y1_def by (rule reach_z8)

lemma reach_y2: "dwc_reachable y2"
  by (rule dwc_reachable_lose_ext[OF reach_y1 y_lose])

lemma y2_eq_w8: "y2 = w8"
  by (simp add: y2_def w8_def)

text \<open>The pair certificate: both members reachable, the three
  blind-visible projections literally equal, the wire divergent.\<close>

lemma y_pair_certificate:
  "dwc_reachable y1 \<and> dwc_reachable y2
 \<and> dwc_inner y1 = dwc_inner y2
 \<and> dwc_accepted y1 = dwc_accepted y2
 \<and> dwc_fence y1 = dwc_fence y2
 \<and> dwc_channel y1 = [(2, 0, ec2, e2)]
 \<and> dwc_channel y2 = []"
  by (intro conjI reach_y1 reach_y2) (simp_all add: y1_def y2_def z8_def)

text \<open>The batch-agreement kernel, one machine up: channel-blindness
  forces literal batch agreement on the pair.\<close>

lemma channel_blind_agrees_on_y_pair:
  assumes "dwc_channel_blind P"
  shows "P y1 = P y2"
proof -
  obtain g where g: "\<forall>t. P t = g (dwc_inner t, dwc_accepted t, dwc_fence t)"
    using assms unfolding dwc_channel_blind_def by blast
  from g have "P y1 = g (dwc_inner y1, dwc_accepted y1, dwc_fence y1)"
         and "P y2 = g (dwc_inner y2, dwc_accepted y2, dwc_fence y2)"
    by blast+
  moreover have "(dwc_inner y1, dwc_accepted y1, dwc_fence y1)
               = (dwc_inner y2, dwc_accepted y2, dwc_fence y2)"
    by (simp add: y1_def y2_def z8_def)
  ultimately show ?thesis by simp
qed

section \<open>The helper: accepted hazards persist through arrivals\<close>

text \<open>
  An arrival can only APPEND to the accepted record (or, dropped,
  leave it alone), and it never touches the committed source --- so
  both accepted-record hazards persist through it: the wire cannot
  heal the record.  This is the hazard algebra the membership split
  below rides on --- in particular it covers the already-duplicate
  batch reading of the duplicate horn (a batch that duplicates BEFORE
  the straggler lands stays duplicated after it), and it makes the
  defeat permanent under any continued delivery.
\<close>

lemma accepted_unsafe_persists_under_arrive:
  assumes arr: "dwc_arrive t i t'"
      and un: "dwc_accepted_unsafe t"
  shows "dwc_accepted_unsafe t'"
proof -
  have src: "dwc_src t' = dwc_src t"
    using dwc_arrive_inner_stutter[OF arr] by (simp add: dwc_src_def)
  from dwc_arrive_shape[OF arr]
  have shape: "dwc_accepted t' = dwc_accepted t @ [dwc_channel t ! i]
             \<or> dwc_accepted t' = dwc_accepted t"
    by blast
  from un shape show ?thesis
    by (auto simp add: dwc_accepted_unsafe_def dwc_accepted_premature_def
                       dwc_accepted_duplicate_def src)
qed

section \<open>The for-all law: no channel-blind re-drive policy escapes\<close>

text \<open>
  THE STRETCH LAW (wave design section 4.12; proof plan = gate
  amendment MF-5, the two-case membership split).  For EVERY
  channel-blind policy: both members of the pair admit the policy's
  re-drive, and on the agreed batch either the batch misses the
  crash-straddling payload --- then the empty-wire member loses it at
  the crash frontier (its accepted record carries only the first
  effect and the batch payloads; its wire is empty) --- or the batch
  carries it --- then on the in-flight member the wire's superseded
  copy arrives at the never-raised fence zero and the accepted record
  duplicates.  The duplicate horn is stated POST-ARRIVAL, one wire
  event after the composite, the loss horn at the composite's own
  result: on this machine the wire is part of the adversary, and a
  defeat it completes is still the policy's defeat, because the
  policy chose its batch blind to the very copy that lands.

  Read with the wave's ladder: the landed dilemma says recovery must
  READ THE SINK; the zombie slice says the honest sink read is not
  enough; this law says NO read that stops short of the wire is
  enough; the fence (slice 3) escapes by changing ACCEPTANCE, not by
  reading more.  NOT claimed: any weakening of the landed B-side
  results --- the landed escape stays correct on its own machine,
  where send and receive are one atomic event and the wire cannot
  outrun the read.
\<close>

theorem no_channel_blind_policy_escapes:
  "\<forall>P. dwc_channel_blind P \<longrightarrow>
     (\<exists>u1 u2. dwc_policy_redrive P ec2 y1 u1 \<and> dwc_policy_redrive P ec2 y2 u2
        \<and> ((\<exists>v. dwc_arrive u1 0 v \<and> dwc_accepted_unsafe v)   \<comment> \<open>zombie member, POST-ARRIVAL\<close>
           \<or> \<not> dwc_alo_at ec2 u2))                            \<comment> \<open>empty-wire member loses\<close>"
proof (intro allI impI)
  fix P :: dwc_redrive_policy
  assume cb: "dwc_channel_blind P"

  \<comment> \<open>the agreed batch: channel-blindness collapses the pair\<close>
  define B where "B = P y1"
  have agree: "P y2 = B"
    unfolding B_def by (rule channel_blind_agrees_on_y_pair[OF cb, symmetric])

  \<comment> \<open>both composites are enabled: the shared inner is crashed at the finish\<close>
  have c1: "\<exists>c. exec_status (dwe_core (dwc_inner y1)) = Crashed c"
    using z8_satisfies_P_premises unfolding y1_def by blast
  have f1: "ec2 \<le> exec_finish (dwe_core (dwc_inner y1))"
    using z8_satisfies_P_premises unfolding y1_def by blast
  have inner_eq: "dwc_inner y2 = dwc_inner y1"
    by (simp add: y1_def y2_def z8_def)
  have c2: "\<exists>c. exec_status (dwe_core (dwc_inner y2)) = Crashed c"
    using c1 by (simp add: inner_eq)
  have f2: "ec2 \<le> exec_finish (dwe_core (dwc_inner y2))"
    using f1 by (simp add: inner_eq)

  define u1 where "u1 = dwc_policy_result P ec2 y1"
  define u2 where "u2 = dwc_policy_result P ec2 y2"
  have pr1: "dwc_policy_redrive P ec2 y1 u1"
    unfolding u1_def by (rule dwc_policy_redriveI[OF c1 f1])
  have pr2: "dwc_policy_redrive P ec2 y2 u2"
    unfolding u2_def by (rule dwc_policy_redriveI[OF c2 f2])

  \<comment> \<open>the record shapes at the two results\<close>
  have u1_acc: "dwc_accepted u1 = [(1, 0, ec1, e1)] @ map (dwc_stamp y1) B"
    by (simp add: u1_def dwc_policy_result_components B_def y1_def z8_def)
  have u1_ch: "dwc_channel u1 = [(2, 0, ec2, e2)]"
    by (simp add: u1_def dwc_policy_result_components y1_def z8_def)
  have u1_fn: "dwc_fence u1 = 0"
    by (simp add: u1_def dwc_policy_result_components y1_def z8_def)
  have u2_acc: "dwc_accepted u2 = [(1, 0, ec1, e1)] @ map (dwc_stamp y2) B"
  proof -
    have "dwc_accepted u2 = dwc_accepted y2 @ map (dwc_stamp y2) (P y2)"
      by (simp add: u2_def dwc_policy_result_components)
    also have "\<dots> = dwc_accepted y2 @ map (dwc_stamp y2) B"
      by (simp add: agree)
    also have "dwc_accepted y2 @ map (dwc_stamp y2) B
             = [(1, 0, ec1, e1)] @ map (dwc_stamp y2) B"
      by (simp add: y2_def)
    finally show ?thesis .
  qed

  show "\<exists>u1 u2.
          dwc_policy_redrive P ec2 y1 u1 \<and> dwc_policy_redrive P ec2 y2 u2
        \<and> ((\<exists>v. dwc_arrive u1 0 v \<and> dwc_accepted_unsafe v)
           \<or> \<not> dwc_alo_at ec2 u2)"
  proof (cases "(ec2, e2) \<in> set B")
    case True
    \<comment> \<open>the batch carries the payload: the straggler's arrival duplicates\<close>
    define v where
      "v = u1\<lparr>dwc_channel := [],
              dwc_accepted := dwc_accepted u1 @ [(2, 0, ec2, e2)]\<rparr>"
    have arr: "dwc_arrive u1 0 v"
      by (rule dwc_arrive_acceptI) (simp_all add: u1_ch u1_fn v_def)
    have v_pay: "map e_payload (dwc_accepted v)
        = (ec1, e1) # B @ [(ec2, e2)]"
      by (simp add: v_def u1_acc o_def)
    have dup: "dwc_accepted_duplicate v"
      using True by (auto simp add: dwc_accepted_duplicate_def v_pay)
    have unsafe: "dwc_accepted_unsafe v"
      using dup by (simp add: dwc_accepted_unsafe_def)
    have horn: "\<exists>v. dwc_arrive u1 0 v \<and> dwc_accepted_unsafe v"
      using arr unsafe by blast
    show ?thesis using pr1 pr2 horn by blast
  next
    case False
    \<comment> \<open>the batch misses the payload: the empty-wire member loses it\<close>
    have mem: "(ec2, e2) \<in> set (dwc_replay ec2 u2)"
      unfolding u2_def dwc_policy_result_replay
      by (simp add: dwc_replay_def dwc_src_def dwc_scope_def
                    replay_down_hist_def y2_def zi8_def mkT_def mkC_def
                    e1_def e2_def ec_defs)
    have pay: "e_payload ` set (dwc_accepted u2) = {(ec1, e1)} \<union> set B"
      by (simp add: u2_acc image_Un image_image)
    have nmem: "(ec2, e2) \<notin> e_payload ` set (dwc_accepted u2)"
      unfolding pay using False by (simp add: e1_def e2_def ec_defs)
    have not_alo: "\<not> dwc_alo_at ec2 u2"
      unfolding dwc_alo_at_def using mem nmem by blast
    show ?thesis using pr1 pr2 not_alo by blast
  qed
qed

end
