(*  Title:       Dual_Write_Effect_Channel.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE CHANNEL VARIANT MACHINE (dwc): delayed delivery + generation
    fencing over the landed cyclic effect machine --- an additive
    post-freeze slice under the freeze's own protocol (no landed
    statement, proof, definition, name, import, or session-DAG change),
    the first slice of the D-091 channel/fencing wave (ladder section 32).

    THE SPLIT.  The landed cyclic machine collapses "sent to the sink"
    and "received by the sink" into one atomic event: dwe_emitted is
    written at fire time and the landed sink_delta filters against it,
    so recovery's sink read enjoys silent wire-omniscience.  The dwc
    machine splits the event: a publish goes IN FLIGHT (dwc_channel),
    the sink's durable record is what has ARRIVED and been accepted
    (dwc_accepted), and acceptance is guarded by a sink-side generation
    fence (dwc_fence) consuming the epoch tag every emission already
    carries.  The landed dwe_emitted (dwc_inner t) is re-read as the
    append-only SENT log; the sent-side verdicts (effect_unsafe on the
    inner) remain true, stated facts of dwc_inner; the machine's own
    hazard and exactly-once verdicts read the ACCEPTED record.  Crash
    acts through the inner only, so the wire and the sink's record
    survive it by construction (dwc_crash_wire_survives) --- the design
    choice that makes the zombie expressible (slice 2).

    THE RULES.  Seven: the label lift/send pair (a publish pushes its
    stamped emission onto the channel, not into accepted), the fenced
    arrive pair (pop by index; accept iff the entry's epoch clears the
    fence, drop otherwise --- NO status guard on the inner: the wire
    outlives the process), wire loss, the resume lift, the channeled
    cursor re-drive lift (the landed emitting_reconcile on the inner,
    its re-driven suffix pushed in flight --- a recovery's re-sends are
    sends), THE ATOMIC FENCED RE-DRIVE (the one new disclosed model
    boundary, contracts row 11: landed heal + accepted-record sink
    delta appended to the sent ledger AND synchronously into the
    accepted record + fence raised to Suc of the crash-time epoch, ONE
    rule), and its unfenced escape sibling differing in EXACTLY the
    fence field --- the N/P contrast pair of the wave.

    THE EMBEDDING.  Every landed cyclic trace embeds as a dwc trace in
    which each send is immediately followed by its own arrival and each
    cursor re-drive by the arrivals of its whole batch --- the
    instant-delivery reading.  On embedded states the accepted record
    IS the landed ledger and the accepted-record verdicts coincide with
    the landed verdicts (the verdict bridges).  The honest transfer
    scope is stated verbatim at the embedding (E-3): the landed corpus
    transfers to the embedded fragment and the structural invariants
    lift along ALL dwc traces; the escape, the discipline, and
    exactly-once on the accepted record are re-litigated subjects.

    THE FENCE PACKAGE.  The inductive invariant is epoch-boundedness of
    both records plus fence-boundedness (dwc_fence_inv) --- NOT the
    refuted payload-freshness candidate (a post-resume application may
    legally re-publish an already-accepted payload; finding F-2 of the
    wave design).  On top: fence monotonicity per step and per trace,
    the guard-level inventory fact (arrive_accept_respects_fence), the
    redrive-free growth bound (accepted_growth_fenced: along any
    redrive-free continuation the accepted record grows only by entries
    at or above the fence --- a sub-fence entry is PERMANENTLY
    excluded), and the status-indexed companion bound
    (dwc_fence_status_bound, gate amendment MF-6): Running/Crashed
    states have fence <= epoch, Recovered states fence <= Suc epoch ---
    strictly stronger than the pinned invariant's fence half and the
    exact reason ordinary publishes are BORN ACCEPTABLE
    (publish_born_acceptable).

    WHAT THIS SLICE DOES NOT BUILD (the A4 boundary, named here as the
    next rung): the acceptance discipline is deliberately
    writer-agnostic --- the arrive guard is a pure token comparison
    between the entry's stamped generation and the sink's fence, never
    an inner status, identity, or history read --- so a future
    multi-writer machine reuses the channel/accepted/fence fields and
    the arrive rules verbatim; but generating a live zombie's FRESH
    sends and true concurrent recoverers are inexpressible on any
    wrapper over one inner and are NOT built or claimed here.

    IMPORTS: Dual_Write_Effect_Exactly_Once alone --- the exactly-once
    vocabulary this theory twins onto the accepted record, and through
    it the Dilemma policy vocabulary, the Discipline, the cyclic
    machine, and the locked core.  The terminal branch is deliberately
    NOT imported (namespace rule: the two branches share hazard names
    by design).

    PROVENANCE: owner decision D-091; the channel-wave design gate
    (paper/dual_write/theory_backlog/channel_wave/CHANNEL_WAVE_DESIGN.md,
    ratified COHERENT-GO with amendments MF-1..MF-10 by
    channel_wave/GATE_REPORT.md, 2026-07-07); fence soundness
    independently re-derived in channel_wave/FENCE_VERIFICATION.md.

    In-source ML oracle gates are STRIPPED at landing: oracle-freedom is
    certified by scratch-side per-slice gate sessions with
    confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Channel
  imports Dual_Write_Effect_Exactly_Once
begin

section \<open>The channel variant state: inner machine, wire, accepted record, fence\<close>

text \<open>
  The record wraps the WHOLE landed cyclic wrapper state as
  @{text dwc_inner} --- no frozen type is touched --- and adds the wire
  (@{text dwc_channel}: sent, not yet resolved), the sink's durable
  accepted record (@{text dwc_accepted}), and the sink-side generation
  fence (@{text dwc_fence}; @{term "0::nat"} = never raised).
\<close>

record ('k, 'v) dwc_state =
  dwc_inner    :: "('k, 'v) dwe_state"
  dwc_channel  :: "('k, 'v) emission list"
  dwc_accepted :: "('k, 'v) emission list"
  dwc_fence    :: nat

definition dwc_init
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'k set \<Rightarrow> frontier \<Rightarrow> ('k, 'v) dwc_state"
where
  "dwc_init b K fin =
     \<lparr> dwc_inner = dwe_init b K fin, dwc_channel = [], dwc_accepted = [],
       dwc_fence = 0 \<rparr>"

text \<open>Readability projections used by every rule below.\<close>

definition dwc_src :: "('k, 'v) dwc_state \<Rightarrow> ('k, 'v) src_history" where
  "dwc_src t = exec_src_hist (dwe_core (dwc_inner t))"

definition dwc_scope :: "('k, 'v) dwc_state \<Rightarrow> 'k set" where
  "dwc_scope t = exec_scope (dwe_core (dwc_inner t))"

definition dwc_replay
  :: "frontier \<Rightarrow> ('k, 'v) dwc_state \<Rightarrow> ('k, 'v) src_history"
where
  "dwc_replay f t = replay_down_hist (dwc_src t) (dwc_scope t) f"

definition dwc_stamp
  :: "('k, 'v) dwc_state \<Rightarrow> (src_coord \<times> ('k, 'v) source_event)
      \<Rightarrow> ('k, 'v) emission"
where
  "dwc_stamp t = (\<lambda>(c, e). (length (dwc_src t), dwe_epoch (dwc_inner t), c, e))"

text \<open>
  @{const dwc_stamp} is literally the landed stamping (the
  @{text publish_emit} and @{const emitting_reconcile} ledger entries):
  committed-prefix length plus the CURRENT epoch.  Re-drives therefore
  stamp at the OLD (crash-time) epoch --- the landed
  @{thm [source] emitting_reconcile_epoch_const} fact that forces the
  atomic fence site below.
\<close>

lemma e_stamp_triple [simp]: "e_stamp (n, ep, p) = n"
  by (simp add: e_stamp_def)

lemma e_epoch_triple [simp]: "e_epoch (n, ep, p) = ep"
  by (simp add: e_epoch_def)

lemma dwc_stamp_eval [simp]:
  "dwc_stamp t p = (length (dwc_src t), dwe_epoch (dwc_inner t), p)"
  by (simp add: dwc_stamp_def)

text \<open>The function-level unfolding (NOT a global simp rule, per the
  house proof discipline): used exactly where a stamped batch must be
  compared against the landed stamping lambda.\<close>

lemma dwc_stamp_unfold:
  "dwc_stamp t = (\<lambda>p. (length (dwc_src t), dwe_epoch (dwc_inner t), p))"
  by (simp add: dwc_stamp_def)

lemma e_stamp_dwc_stamp [simp]:
  "e_stamp (dwc_stamp t p) = length (dwc_src t)"
  by simp

lemma e_epoch_dwc_stamp [simp]:
  "e_epoch (dwc_stamp t p) = dwe_epoch (dwc_inner t)"
  by simp

lemma e_payload_dwc_stamp [simp]: "e_payload (dwc_stamp t p) = p"
  by simp

lemma map_payload_dwc_stamp [simp]:
  "map e_payload (map (dwc_stamp t) B) = B"
  by (induction B) simp_all

lemma dwc_stamp_payload_set [simp]:
  "e_payload ` set (map (dwc_stamp t) B) = set B"
  by (induction B) simp_all

lemma dwc_stamped_elem:
  assumes "x \<in> set (map (dwc_stamp t) B)"
  shows "e_stamp x = length (dwc_src t)
       \<and> e_epoch x = dwe_epoch (dwc_inner t)
       \<and> e_payload x \<in> set B"
  using assms by auto

section \<open>The accepted-record sink read\<close>

text \<open>
  The landed @{const sink_delta} with ONE change: the filter reads
  @{const dwc_accepted}, not the sent ledger --- the honest repair of
  the landed escape's silent wire-omniscience.  The sent-side reading
  remains a true, stated fact of the inner (the lifted
  @{const effect_unsafe} monotonicity below); the accepted-side reading
  is the machine's own verdict; the divergence of the two is itself a
  theorem of the wave (slice 3).
\<close>

definition dwc_sink_delta
  :: "frontier \<Rightarrow> ('k, 'v) dwc_state
      \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list"
where
  "dwc_sink_delta f t =
     filter (\<lambda>p. p \<notin> e_payload ` set (dwc_accepted t)) (dwc_replay f t)"

section \<open>The transition rules\<close>

subsection \<open>R1 --- label lift and send: a publish goes in flight\<close>

text \<open>
  Two mirrored rules keyed on the label, the landed relation as premise
  (the Small-Step house pattern).  A non-publish label lifts through the
  inner untouched --- INCLUDING @{text Crash}: the wire and the sink's
  record live outside the producer's failure domain.  A publish pushes
  its emission ONTO THE CHANNEL, not into the accepted record: send and
  receive are now separate events.
\<close>

inductive dwc_step
  :: "('k, 'v) dwc_state \<Rightarrow> ('k, 'v) dw_exec_label \<Rightarrow> ('k, 'v) dwc_state
      \<Rightarrow> bool"
where
  lift_nonpub:
    "dwe_step (dwc_inner t) a i' \<Longrightarrow>
     \<forall>c e. a \<noteq> DoDownstream c e \<Longrightarrow>
     dwc_step t a (t\<lparr>dwc_inner := i'\<rparr>)"
| send_pub:
    "dwe_step (dwc_inner t) (DoDownstream c e) i' \<Longrightarrow>
     dwc_step t (DoDownstream c e)
       (t\<lparr>dwc_inner := i',
          dwc_channel := dwc_channel t @ [dwc_stamp t (c, e)]\<rparr>)"

lemma dwc_lift_nonpubI:
  assumes "dwe_step (dwc_inner t) a i'"
      and "\<forall>c e. a \<noteq> DoDownstream c e"
      and "t' = t\<lparr>dwc_inner := i'\<rparr>"
  shows "dwc_step t a t'"
  unfolding assms(3) by (rule dwc_step.lift_nonpub[OF assms(1) assms(2)])

lemma dwc_send_pubI:
  assumes "dwe_step (dwc_inner t) (DoDownstream c e) i'"
      and "t' = t\<lparr>dwc_inner := i',
                 dwc_channel := dwc_channel t @ [dwc_stamp t (c, e)]\<rparr>"
  shows "dwc_step t (DoDownstream c e) t'"
  unfolding assms(2) by (rule dwc_step.send_pub[OF assms(1)])

text \<open>
  The named inversion accompanying the send rule: the channel entry a
  publish pushes in flight is BYTE-IDENTICAL to the entry the landed
  @{text publish_emit} appends to the inner sent ledger --- one
  emission, two records.
\<close>

lemma dwc_step_inner:
  assumes "dwc_step t a t'"
  shows "dwe_step (dwc_inner t) a (dwc_inner t')"
  using assms by (cases rule: dwc_step.cases) simp_all

lemma dwe_step_pub_emitted:
  assumes "dwe_step t (DoDownstream c e) t'"
  shows "dwe_emitted t' = dwe_emitted t
           @ [(length (exec_src_hist (dwe_core t)), dwe_epoch t, c, e)]"
  using assms by (cases rule: dwe_step.cases) auto

lemma dwc_step_pub_channel:
  assumes "dwc_step t (DoDownstream c e) t'"
  shows "dwc_channel t' = dwc_channel t @ [dwc_stamp t (c, e)]"
  using assms by (cases rule: dwc_step.cases) auto

lemma dwc_send_entry_eq:
  assumes "dwc_step t (DoDownstream c e) t'"
  shows "dwc_channel t' = dwc_channel t @ [dwc_stamp t (c, e)]
       \<and> dwe_emitted (dwc_inner t')
           = dwe_emitted (dwc_inner t) @ [dwc_stamp t (c, e)]"
proof -
  have ch: "dwc_channel t' = dwc_channel t @ [dwc_stamp t (c, e)]"
    by (rule dwc_step_pub_channel[OF assms])
  have em: "dwe_emitted (dwc_inner t')
      = dwe_emitted (dwc_inner t)
        @ [(length (exec_src_hist (dwe_core (dwc_inner t))),
            dwe_epoch (dwc_inner t), c, e)]"
    by (rule dwe_step_pub_emitted[OF dwc_step_inner[OF assms]])
  show ?thesis
    using ch em by (simp add: dwc_src_def)
qed

text \<open>Crash survival, theorem-visible: a crash moves the inner status
  only --- the wire, the accepted record, and the fence all SURVIVE.
  This is the design choice that makes the zombie of slice 2
  expressible; its wipe-twin control lands beside the zombie there.\<close>

theorem dwc_crash_wire_survives:
  assumes "dwc_step t (Crash c) t'"
  shows "dwc_channel t' = dwc_channel t \<and> dwc_accepted t' = dwc_accepted t
       \<and> dwc_fence t' = dwc_fence t"
  using assms by (cases rule: dwc_step.cases) auto

subsection \<open>R2 --- the fenced arrive: pop by index, accept or drop\<close>

text \<open>
  NO status guard on the inner and NO inner update --- an arrival fires
  while the producer is Running, Crashed, or Recovered, at any later
  epoch: the wire does not know the producer's status.  Pop-by-index
  gives single-arrival semantics (each in-flight copy resolves exactly
  once) and free reordering.  The guard is the corpus's FIRST
  epoch-reading guard --- sink-side AUTHORITY over acceptance, wrapper
  level only; no landed (store-side) guard reads the tag, and the
  landed row-8 claim and GAP-2 stand unchanged.
\<close>

inductive dwc_arrive
  :: "('k, 'v) dwc_state \<Rightarrow> nat \<Rightarrow> ('k, 'v) dwc_state \<Rightarrow> bool"
where
  arrive_accept:
    "i < length (dwc_channel t) \<Longrightarrow>
     dwc_fence t \<le> e_epoch (dwc_channel t ! i) \<Longrightarrow>
     dwc_arrive t i
       (t\<lparr>dwc_channel := take i (dwc_channel t) @ drop (Suc i) (dwc_channel t),
          dwc_accepted := dwc_accepted t @ [dwc_channel t ! i]\<rparr>)"
| arrive_drop:
    "i < length (dwc_channel t) \<Longrightarrow>
     e_epoch (dwc_channel t ! i) < dwc_fence t \<Longrightarrow>
     dwc_arrive t i
       (t\<lparr>dwc_channel := take i (dwc_channel t) @ drop (Suc i) (dwc_channel t)\<rparr>)"

lemma dwc_arrive_acceptI:
  assumes "i < length (dwc_channel t)"
      and "dwc_fence t \<le> e_epoch (dwc_channel t ! i)"
      and "t' = t\<lparr>dwc_channel := take i (dwc_channel t)
                    @ drop (Suc i) (dwc_channel t),
                 dwc_accepted := dwc_accepted t @ [dwc_channel t ! i]\<rparr>"
  shows "dwc_arrive t i t'"
  unfolding assms(3) by (rule dwc_arrive.arrive_accept[OF assms(1) assms(2)])

lemma dwc_arrive_dropI:
  assumes "i < length (dwc_channel t)"
      and "e_epoch (dwc_channel t ! i) < dwc_fence t"
      and "t' = t\<lparr>dwc_channel := take i (dwc_channel t)
                    @ drop (Suc i) (dwc_channel t)\<rparr>"
  shows "dwc_arrive t i t'"
  unfolding assms(3) by (rule dwc_arrive.arrive_drop[OF assms(1) assms(2)])

subsection \<open>R3 --- wire loss\<close>

text \<open>
  An in-flight entry may vanish (fold-in (a) of the wave design,
  adopted): loss and fence-drop are visibly different rule paths, an
  unresolved in-flight entry is first-class state (the model's rendering
  of the ambiguous-outcome window), and the accepted-record delta is
  loss-oblivious by construction --- it filters replay against
  @{const dwc_accepted} only, so a lost send is re-driven at the next
  recovery exactly like a never-arrived one (the slice-3 bonus theorem).
\<close>

definition dwc_lose :: "('k, 'v) dwc_state \<Rightarrow> nat \<Rightarrow> ('k, 'v) dwc_state \<Rightarrow> bool"
where
  "dwc_lose t i t' \<longleftrightarrow>
     i < length (dwc_channel t)
   \<and> t' = t\<lparr>dwc_channel := take i (dwc_channel t) @ drop (Suc i) (dwc_channel t)\<rparr>"

lemma dwc_loseI:
  assumes "i < length (dwc_channel t)"
      and "t' = t\<lparr>dwc_channel := take i (dwc_channel t)
                    @ drop (Suc i) (dwc_channel t)\<rparr>"
  shows "dwc_lose t i t'"
  using assms by (simp add: dwc_lose_def)

subsection \<open>R4 --- resume lift\<close>

definition dwc_resume_lift :: "('k, 'v) dwc_state \<Rightarrow> ('k, 'v) dwc_state \<Rightarrow> bool"
where
  "dwc_resume_lift t t' \<longleftrightarrow>
     (\<exists>i'. dwe_resume (dwc_inner t) i' \<and> t' = t\<lparr>dwc_inner := i'\<rparr>)"

lemma dwc_resume_liftI:
  assumes "dwe_resume (dwc_inner t) i'"
      and "t' = t\<lparr>dwc_inner := i'\<rparr>"
  shows "dwc_resume_lift t t'"
  using assms by (auto simp: dwc_resume_lift_def)

subsection \<open>R5 --- the channeled cursor re-drive lift\<close>

text \<open>
  The landed @{const emitting_reconcile} on the inner, its re-driven
  suffix pushed IN FLIGHT --- a recovery's re-sends are sends (finding
  F-1 of the wave design: the instant-delivery embedding must replay
  landed cursor re-drives, including the cold-cursor @{term "m = (0::nat)"}
  whose batch duplicates the sent ledger, which no delta-based rule can
  emit).  Inherits the landed atomic big-step reconcile boundary
  (contracts row 1) and adds nothing to it.
\<close>

definition dwc_reconcile_send
  :: "nat \<Rightarrow> ('k, 'v) dwc_state \<Rightarrow> frontier \<Rightarrow> ('k, 'v) dwc_state \<Rightarrow> bool"
where
  "dwc_reconcile_send m t f t' \<longleftrightarrow>
     (\<exists>i'. emitting_reconcile m (dwc_inner t) f i'
         \<and> t' = t\<lparr>dwc_inner := i',
                  dwc_channel := dwc_channel t
                    @ map (dwc_stamp t) (drop m (dwc_replay f t))\<rparr>)"

lemma dwc_reconcile_sendI:
  assumes "emitting_reconcile m (dwc_inner t) f i'"
      and "t' = t\<lparr>dwc_inner := i',
                 dwc_channel := dwc_channel t
                   @ map (dwc_stamp t) (drop m (dwc_replay f t))\<rparr>"
  shows "dwc_reconcile_send m t f t'"
  using assms by (auto simp: dwc_reconcile_send_def)

subsection \<open>R6 --- THE ATOMIC FENCED RE-DRIVE (disclosed boundary, contracts row 11)\<close>

text \<open>
  THE ATOMIC FENCED RE-DRIVE, a disclosed model boundary (contracts row
  11, same family as the atomic big-step reconcile of row 1).  This
  composite performs, in ONE rule: the landed scoped heal, the
  accepted-record sink delta appended to the sent ledger and
  SYNCHRONOUSLY into the accepted record (the recovery's own re-sends
  never traverse the fenced channel), and the fence raised to the
  successor of the crash-time epoch.  Excluded: a crash DURING the
  fenced re-drive, and any wire delay on the recovery's own re-sends.
  Causal split, for honest citation: the result-state exactly-once
  verdict (@{text dwc_eo_at} at the redrive's own result) is carried by
  the SYNCHRONOUS sink-delta acceptance --- the unfenced escape sibling
  @{text dwc_escape_redrive} differs only in the fence field, which
  @{text dwc_eo_at} never reads, so that conjunct holds for it equally.
  What the fence itself buys is the residual-wire pair: every surviving
  channel entry stale below the new fence, and the accepted record
  preserved under arrive/lose-only wire resolution.
  It does NOT stand in for delivery liveness of ordinary publishes ---
  those stay channeled and may be lost (@{const dwc_lose}) or fenced
  out.

  The site of the fence rise is FORCED, not stylistic, GIVEN the landed
  old-epoch stamp discipline.  Re-drives stamp at the OLD epoch (the
  landed stamping; the reconcile is epoch-constant and Resume bumps
  only afterwards), so a superseded generation's in-flight emission and
  the recovery's own re-drive carry the SAME epoch --- no fence value
  separates them on the wire.  Raising the fence at Resume admits the
  straggler in the reconcile-to-resume window (and the bare
  @{text Recover} path fences generations that never re-drove); raising
  it in a separate step before the re-drive rejects the recovery's own
  sends if they are channeled.  Synchronous acceptance plus an atomic
  rise is the landed rule's design point in this family (soundness of
  the point is what the theorems establish; uniqueness of the placement
  is not a landed fact); a crash DURING
  the composite is inexpressible here, exactly as row 1 disclosed for
  the landed reconcile.  A variant machine that re-stamped its
  re-drives at the successor epoch would evade the wire
  indistinguishability, but it breaks mirror fidelity with the landed
  reconcile and policy stamping and the channel epoch bound --- out of
  scope under the D-091 fidelity requirement; the necessity claim is
  stated with exactly this hypothesis.

  The fence governs the WIRE (which arrivals are accepted), never the
  POLICY (which batch is re-driven): the positive results ride the
  accepted-record delta batch plus @{const strictly_ascending_source}
  (boundary row 6); the SAME composite family with a store-measured or
  cursor batch retains BOTH landed horns on the accepted record
  (boundary row 2), and the fence converts the wire's late-arrival
  rescue into a certain drop when the recovery under-scopes (the
  @{text fence_rescue_conversion} control of slice 3).

  What this boundary buys, and only this: the fenced positive results.
  The zombie defeat (the unfenced sibling below differs from this rule
  in the fence field alone) needs none of it, and splitting the
  composite only ADDS behaviors to a for-all-policy defeat.  Non-stale
  duplicate-freedom still rides @{const strictly_ascending_source}:
  the fence is necessary, never magic.
\<close>

definition dwc_fenced_redrive
  :: "frontier \<Rightarrow> ('k, 'v) dwc_state \<Rightarrow> ('k, 'v) dwc_state \<Rightarrow> bool"
where
  "dwc_fenced_redrive f t t' \<longleftrightarrow>
     (\<exists>c. exec_status (dwe_core (dwc_inner t)) = Crashed c)
   \<and> f \<le> exec_finish (dwe_core (dwc_inner t))
   \<and> t' = t\<lparr>dwc_inner := (dwc_inner t)
              \<lparr>dwe_core := (dwe_core (dwc_inner t))
                 \<lparr>exec_down_hist := dwc_replay f t,
                  exec_pending := {},
                  exec_status := Recovered\<rparr>,
               dwe_emitted := dwe_emitted (dwc_inner t)
                 @ map (dwc_stamp t) (dwc_sink_delta f t)\<rparr>,
            dwc_accepted := dwc_accepted t @ map (dwc_stamp t) (dwc_sink_delta f t),
            dwc_fence := Suc (dwe_epoch (dwc_inner t))\<rparr>"

lemma dwc_fenced_redriveI:
  assumes "\<exists>c. exec_status (dwe_core (dwc_inner t)) = Crashed c"
      and "f \<le> exec_finish (dwe_core (dwc_inner t))"
      and "t' = t\<lparr>dwc_inner := (dwc_inner t)
                    \<lparr>dwe_core := (dwe_core (dwc_inner t))
                       \<lparr>exec_down_hist := dwc_replay f t,
                        exec_pending := {},
                        exec_status := Recovered\<rparr>,
                     dwe_emitted := dwe_emitted (dwc_inner t)
                       @ map (dwc_stamp t) (dwc_sink_delta f t)\<rparr>,
                  dwc_accepted := dwc_accepted t
                    @ map (dwc_stamp t) (dwc_sink_delta f t),
                  dwc_fence := Suc (dwe_epoch (dwc_inner t))\<rparr>"
  shows "dwc_fenced_redrive f t t'"
  using assms by (simp add: dwc_fenced_redrive_def)

subsection \<open>R7 --- the unfenced escape sibling (the biting-control hygiene)\<close>

text \<open>
  Identical to the atomic fenced re-drive MINUS the fence update --- the
  honest sink-reading escape, channel-era, WITHOUT fencing.  The two
  rules differ in EXACTLY the fence field: the fence is the only delta
  of the N/P contrast pair (slices 2 and 3).  Both siblings share the
  synchronous-acceptance idealization and are disclosed together as the
  one new boundary (contracts row 11).
\<close>

definition dwc_escape_redrive
  :: "frontier \<Rightarrow> ('k, 'v) dwc_state \<Rightarrow> ('k, 'v) dwc_state \<Rightarrow> bool"
where
  "dwc_escape_redrive f t t' \<longleftrightarrow>
     (\<exists>c. exec_status (dwe_core (dwc_inner t)) = Crashed c)
   \<and> f \<le> exec_finish (dwe_core (dwc_inner t))
   \<and> t' = t\<lparr>dwc_inner := (dwc_inner t)
              \<lparr>dwe_core := (dwe_core (dwc_inner t))
                 \<lparr>exec_down_hist := dwc_replay f t,
                  exec_pending := {},
                  exec_status := Recovered\<rparr>,
               dwe_emitted := dwe_emitted (dwc_inner t)
                 @ map (dwc_stamp t) (dwc_sink_delta f t)\<rparr>,
            dwc_accepted := dwc_accepted t @ map (dwc_stamp t) (dwc_sink_delta f t)\<rparr>"

lemma dwc_escape_redriveI:
  assumes "\<exists>c. exec_status (dwe_core (dwc_inner t)) = Crashed c"
      and "f \<le> exec_finish (dwe_core (dwc_inner t))"
      and "t' = t\<lparr>dwc_inner := (dwc_inner t)
                    \<lparr>dwe_core := (dwe_core (dwc_inner t))
                       \<lparr>exec_down_hist := dwc_replay f t,
                        exec_pending := {},
                        exec_status := Recovered\<rparr>,
                     dwe_emitted := dwe_emitted (dwc_inner t)
                       @ map (dwc_stamp t) (dwc_sink_delta f t)\<rparr>,
                  dwc_accepted := dwc_accepted t
                    @ map (dwc_stamp t) (dwc_sink_delta f t)\<rparr>"
  shows "dwc_escape_redrive f t t'"
  using assms by (simp add: dwc_escape_redrive_def)

section \<open>Per-rule field equations\<close>

text \<open>One-line component lemmas per rule, the plumbing every invariant
  induction below consumes.\<close>

lemma dwc_step_accepted_same:
  assumes "dwc_step t a t'"
  shows "dwc_accepted t' = dwc_accepted t"
  using assms by (cases rule: dwc_step.cases) simp_all

lemma dwc_step_fence_same:
  assumes "dwc_step t a t'"
  shows "dwc_fence t' = dwc_fence t"
  using assms by (cases rule: dwc_step.cases) simp_all

lemma dwc_step_channel_shape:
  assumes "dwc_step t a t'"
  shows "dwc_channel t' = dwc_channel t
       \<or> (\<exists>c e. a = DoDownstream c e
            \<and> dwc_channel t' = dwc_channel t @ [dwc_stamp t (c, e)])"
  using assms by (cases rule: dwc_step.cases) auto

lemma dwe_step_nonpub_emitted:
  assumes "dwe_step t a t'"
      and "\<forall>c e. a \<noteq> DoDownstream c e"
  shows "dwe_emitted t' = dwe_emitted t"
  using assms by (cases rule: dwe_step.cases) auto

lemma dwc_arrive_inner_stutter:
  assumes "dwc_arrive t i t'"
  shows "dwc_inner t' = dwc_inner t"
  using assms by (cases rule: dwc_arrive.cases) simp_all

lemma dwc_arrive_fence_same:
  assumes "dwc_arrive t i t'"
  shows "dwc_fence t' = dwc_fence t"
  using assms by (cases rule: dwc_arrive.cases) simp_all

lemma dwc_arrive_channel_subset:
  assumes "dwc_arrive t i t'"
  shows "set (dwc_channel t') \<subseteq> set (dwc_channel t)"
  using assms
  by (cases rule: dwc_arrive.cases)
     (auto dest: in_set_takeD in_set_dropD)

lemma dwc_arrive_shape:
  assumes "dwc_arrive t i t'"
  shows "i < length (dwc_channel t)
       \<and> dwc_channel t' = take i (dwc_channel t) @ drop (Suc i) (dwc_channel t)
       \<and> (dwc_accepted t' = dwc_accepted t @ [dwc_channel t ! i]
          \<or> dwc_accepted t' = dwc_accepted t)"
  using assms by (cases rule: dwc_arrive.cases) auto

lemma dwc_lose_inner_stutter:
  assumes "dwc_lose t i t'"
  shows "dwc_inner t' = dwc_inner t"
  using assms by (simp add: dwc_lose_def)

lemma dwc_lose_accepted_same:
  assumes "dwc_lose t i t'"
  shows "dwc_accepted t' = dwc_accepted t"
  using assms by (simp add: dwc_lose_def)

lemma dwc_lose_fence_same:
  assumes "dwc_lose t i t'"
  shows "dwc_fence t' = dwc_fence t"
  using assms by (simp add: dwc_lose_def)

lemma dwc_lose_channel_subset:
  assumes "dwc_lose t i t'"
  shows "set (dwc_channel t') \<subseteq> set (dwc_channel t)"
  using assms
  by (auto simp: dwc_lose_def dest: in_set_takeD in_set_dropD)

lemma dwc_resume_lift_inner:
  assumes "dwc_resume_lift t t'"
  shows "dwe_resume (dwc_inner t) (dwc_inner t')"
  using assms by (auto simp: dwc_resume_lift_def)

lemma dwc_resume_lift_wire_same:
  assumes "dwc_resume_lift t t'"
  shows "dwc_channel t' = dwc_channel t \<and> dwc_accepted t' = dwc_accepted t
       \<and> dwc_fence t' = dwc_fence t"
  using assms by (auto simp: dwc_resume_lift_def)

lemma dwc_reconcile_send_inner:
  assumes "dwc_reconcile_send m t f t'"
  shows "emitting_reconcile m (dwc_inner t) f (dwc_inner t')"
  using assms by (auto simp: dwc_reconcile_send_def)

lemma dwc_reconcile_send_channel:
  assumes "dwc_reconcile_send m t f t'"
  shows "dwc_channel t' = dwc_channel t
           @ map (dwc_stamp t) (drop m (dwc_replay f t))"
  using assms by (auto simp: dwc_reconcile_send_def)

lemma dwc_reconcile_send_accepted_same:
  assumes "dwc_reconcile_send m t f t'"
  shows "dwc_accepted t' = dwc_accepted t"
  using assms by (auto simp: dwc_reconcile_send_def)

lemma dwc_reconcile_send_fence_same:
  assumes "dwc_reconcile_send m t f t'"
  shows "dwc_fence t' = dwc_fence t"
  using assms by (auto simp: dwc_reconcile_send_def)

lemma dwc_fenced_redrive_components:
  assumes "dwc_fenced_redrive f t t'"
  shows "dwc_channel t' = dwc_channel t"
    and "dwc_accepted t' = dwc_accepted t @ map (dwc_stamp t) (dwc_sink_delta f t)"
    and "dwc_fence t' = Suc (dwe_epoch (dwc_inner t))"
    and "dwe_epoch (dwc_inner t') = dwe_epoch (dwc_inner t)"
    and "dwe_emitted (dwc_inner t') = dwe_emitted (dwc_inner t)
           @ map (dwc_stamp t) (dwc_sink_delta f t)"
    and "exec_src_hist (dwe_core (dwc_inner t'))
           = exec_src_hist (dwe_core (dwc_inner t))"
    and "exec_status (dwe_core (dwc_inner t')) = Recovered"
  using assms by (simp_all add: dwc_fenced_redrive_def)

lemma dwc_escape_redrive_components:
  assumes "dwc_escape_redrive f t t'"
  shows "dwc_channel t' = dwc_channel t"
    and "dwc_accepted t' = dwc_accepted t @ map (dwc_stamp t) (dwc_sink_delta f t)"
    and "dwc_fence t' = dwc_fence t"
    and "dwe_epoch (dwc_inner t') = dwe_epoch (dwc_inner t)"
    and "dwe_emitted (dwc_inner t') = dwe_emitted (dwc_inner t)
           @ map (dwc_stamp t) (dwc_sink_delta f t)"
    and "exec_src_hist (dwe_core (dwc_inner t'))
           = exec_src_hist (dwe_core (dwc_inner t))"
    and "exec_status (dwe_core (dwc_inner t')) = Recovered"
  using assms by (simp_all add: dwc_escape_redrive_def)

text \<open>
  The two composites project to the landed CONSTANT-batch policy redrive
  on the inner (at the landed pinned type), so every landed generic
  redrive fact --- heal, src-same, scope-same, emitted shape,
  justification --- transfers with zero new proofs; and the channeled
  cursor lift projects to the landed @{const emitting_reconcile}
  itself.  This is the transfer engine of the inner-projection lifts.
\<close>

lemma dwc_fenced_redrive_inner_projects:
  fixes t :: "(nat, nat) dwc_state"
  assumes "dwc_fenced_redrive f t t'"
  shows "policy_redrive (\<lambda>_. dwc_sink_delta f t) (dwc_inner t) f (dwc_inner t')"
  using assms
  by (simp add: dwc_fenced_redrive_def policy_redrive_def dwc_stamp_unfold
                dwc_replay_def dwc_src_def dwc_scope_def)

lemma dwc_escape_redrive_inner_projects:
  fixes t :: "(nat, nat) dwc_state"
  assumes "dwc_escape_redrive f t t'"
  shows "policy_redrive (\<lambda>_. dwc_sink_delta f t) (dwc_inner t) f (dwc_inner t')"
  using assms
  by (simp add: dwc_escape_redrive_def policy_redrive_def dwc_stamp_unfold
                dwc_replay_def dwc_src_def dwc_scope_def)

section \<open>Action datatype, trace relation, reachability\<close>

datatype ('k, 'v) dwc_action =
    DWC_Label "('k, 'v) dw_exec_label"
  | DWC_Reconcile nat frontier
  | DWC_Resume
  | DWC_Arrive nat
  | DWC_Lose nat
  | DWC_Escape frontier
  | DWC_Fenced frontier

inductive dwc_temporal_trace
  :: "('k, 'v) dwc_state \<Rightarrow> ('k, 'v) dwc_action list \<Rightarrow> ('k, 'v) dwc_state
      \<Rightarrow> bool"
where
  dwc_refl: "dwc_temporal_trace t [] t"
| dwc_label_step:
    "\<lbrakk>wellformed_exec_state (dwe_core (dwc_inner t));
      exec_label_preserves_history_wf (dwe_core (dwc_inner t)) a;
      dwc_step t a t';  dwc_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwc_temporal_trace t (DWC_Label a # as) t''"
| dwc_reconcile_step:
    "\<lbrakk>dwc_reconcile_send m t f t';  dwc_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwc_temporal_trace t (DWC_Reconcile m f # as) t''"
| dwc_resume_step:
    "\<lbrakk>dwc_resume_lift t t';  dwc_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwc_temporal_trace t (DWC_Resume # as) t''"
| dwc_arrive_step:
    "\<lbrakk>dwc_arrive t i t';  dwc_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwc_temporal_trace t (DWC_Arrive i # as) t''"
| dwc_lose_step:
    "\<lbrakk>dwc_lose t i t';  dwc_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwc_temporal_trace t (DWC_Lose i # as) t''"
| dwc_escape_step:
    "\<lbrakk>dwc_escape_redrive f t t';  dwc_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwc_temporal_trace t (DWC_Escape f # as) t''"
| dwc_fenced_step:
    "\<lbrakk>dwc_fenced_redrive f t t';  dwc_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwc_temporal_trace t (DWC_Fenced f # as) t''"

lemma dwc_temporal_trace_append:
  assumes "dwc_temporal_trace s as s'"
      and "dwc_temporal_trace s' bs s''"
  shows "dwc_temporal_trace s (as @ bs) s''"
  using assms
  by (induction rule: dwc_temporal_trace.induct)
     (auto intro: dwc_temporal_trace.intros)

text \<open>Reachability, from the SAME pinned init as the landed
  @{const dwe_reachable}: type @{typ "(nat, nat) dwc_state"}, empty
  base, scope @{term "{0, 1} :: nat set"}, finish frontier
  @{const ec2} --- boundary row 5 carries over unchanged.\<close>

definition dwc_reachable :: "(nat, nat) dwc_state \<Rightarrow> bool" where
  "dwc_reachable t \<longleftrightarrow>
     (\<exists>xs. dwc_temporal_trace (dwc_init Map.empty {0, 1} ec2) xs t)"

lemma dwc_reachable_init: "dwc_reachable (dwc_init Map.empty {0, 1} ec2)"
  unfolding dwc_reachable_def
  by (intro exI[of _ "[]"] dwc_temporal_trace.dwc_refl)

lemma dwc_reachable_label_ext:
  assumes "dwc_reachable t"
      and "wellformed_exec_state (dwe_core (dwc_inner t))"
      and "exec_label_preserves_history_wf (dwe_core (dwc_inner t)) a"
      and "dwc_step t a t'"
  shows "dwc_reachable t'"
proof -
  obtain xs where xs: "dwc_temporal_trace (dwc_init Map.empty {0, 1} ec2) xs t"
    using assms(1) unfolding dwc_reachable_def by blast
  have one: "dwc_temporal_trace t [DWC_Label a] t'"
    by (rule dwc_temporal_trace.dwc_label_step[OF assms(2) assms(3) assms(4)
          dwc_temporal_trace.dwc_refl])
  show ?thesis
    unfolding dwc_reachable_def
    using dwc_temporal_trace_append[OF xs one] by blast
qed

lemma dwc_reachable_reconcile_ext:
  assumes "dwc_reachable t"
      and "dwc_reconcile_send m t f t'"
  shows "dwc_reachable t'"
proof -
  obtain xs where xs: "dwc_temporal_trace (dwc_init Map.empty {0, 1} ec2) xs t"
    using assms(1) unfolding dwc_reachable_def by blast
  have one: "dwc_temporal_trace t [DWC_Reconcile m f] t'"
    by (rule dwc_temporal_trace.dwc_reconcile_step[OF assms(2)
          dwc_temporal_trace.dwc_refl])
  show ?thesis
    unfolding dwc_reachable_def
    using dwc_temporal_trace_append[OF xs one] by blast
qed

lemma dwc_reachable_resume_ext:
  assumes "dwc_reachable t"
      and "dwc_resume_lift t t'"
  shows "dwc_reachable t'"
proof -
  obtain xs where xs: "dwc_temporal_trace (dwc_init Map.empty {0, 1} ec2) xs t"
    using assms(1) unfolding dwc_reachable_def by blast
  have one: "dwc_temporal_trace t [DWC_Resume] t'"
    by (rule dwc_temporal_trace.dwc_resume_step[OF assms(2)
          dwc_temporal_trace.dwc_refl])
  show ?thesis
    unfolding dwc_reachable_def
    using dwc_temporal_trace_append[OF xs one] by blast
qed

lemma dwc_reachable_arrive_ext:
  assumes "dwc_reachable t"
      and "dwc_arrive t i t'"
  shows "dwc_reachable t'"
proof -
  obtain xs where xs: "dwc_temporal_trace (dwc_init Map.empty {0, 1} ec2) xs t"
    using assms(1) unfolding dwc_reachable_def by blast
  have one: "dwc_temporal_trace t [DWC_Arrive i] t'"
    by (rule dwc_temporal_trace.dwc_arrive_step[OF assms(2)
          dwc_temporal_trace.dwc_refl])
  show ?thesis
    unfolding dwc_reachable_def
    using dwc_temporal_trace_append[OF xs one] by blast
qed

lemma dwc_reachable_lose_ext:
  assumes "dwc_reachable t"
      and "dwc_lose t i t'"
  shows "dwc_reachable t'"
proof -
  obtain xs where xs: "dwc_temporal_trace (dwc_init Map.empty {0, 1} ec2) xs t"
    using assms(1) unfolding dwc_reachable_def by blast
  have one: "dwc_temporal_trace t [DWC_Lose i] t'"
    by (rule dwc_temporal_trace.dwc_lose_step[OF assms(2)
          dwc_temporal_trace.dwc_refl])
  show ?thesis
    unfolding dwc_reachable_def
    using dwc_temporal_trace_append[OF xs one] by blast
qed

lemma dwc_reachable_escape_ext:
  assumes "dwc_reachable t"
      and "dwc_escape_redrive f t t'"
  shows "dwc_reachable t'"
proof -
  obtain xs where xs: "dwc_temporal_trace (dwc_init Map.empty {0, 1} ec2) xs t"
    using assms(1) unfolding dwc_reachable_def by blast
  have one: "dwc_temporal_trace t [DWC_Escape f] t'"
    by (rule dwc_temporal_trace.dwc_escape_step[OF assms(2)
          dwc_temporal_trace.dwc_refl])
  show ?thesis
    unfolding dwc_reachable_def
    using dwc_temporal_trace_append[OF xs one] by blast
qed

lemma dwc_reachable_fenced_ext:
  assumes "dwc_reachable t"
      and "dwc_fenced_redrive f t t'"
  shows "dwc_reachable t'"
proof -
  obtain xs where xs: "dwc_temporal_trace (dwc_init Map.empty {0, 1} ec2) xs t"
    using assms(1) unfolding dwc_reachable_def by blast
  have one: "dwc_temporal_trace t [DWC_Fenced f] t'"
    by (rule dwc_temporal_trace.dwc_fenced_step[OF assms(2)
          dwc_temporal_trace.dwc_refl])
  show ?thesis
    unfolding dwc_reachable_def
    using dwc_temporal_trace_append[OF xs one] by blast
qed

section \<open>Hazards and exactly-once on the ACCEPTED record\<close>

text \<open>
  Literal accepted-record twins of the landed @{const premature} /
  @{const duplicate} / @{const effect_unsafe} /
  @{const at_least_once_at} / @{const exactly_once_at}: the same
  predicate pair, read on @{const dwc_accepted} instead of the sent
  ledger.  The verdict bridges at the embedding below justify the twin
  naming: on embedded states the two readings literally coincide.
\<close>

definition dwc_accepted_premature :: "('k, 'v) dwc_state \<Rightarrow> bool" where
  "dwc_accepted_premature t \<longleftrightarrow>
     (\<exists>x \<in> set (dwc_accepted t). \<not> justified_at (dwc_src t) x)"

definition dwc_accepted_duplicate :: "('k, 'v) dwc_state \<Rightarrow> bool" where
  "dwc_accepted_duplicate t \<longleftrightarrow> \<not> distinct (map e_payload (dwc_accepted t))"

definition dwc_accepted_unsafe :: "('k, 'v) dwc_state \<Rightarrow> bool" where
  "dwc_accepted_unsafe t \<longleftrightarrow> dwc_accepted_premature t \<or> dwc_accepted_duplicate t"

text \<open>
  @{text dwc_alo_at} inherits boundary row 4's TERMINAL-STATE STAND-IN
  status VERBATIM: a state-level reading at the given frontier --- a
  stand-in for delivery liveness of the same kind as the landed
  acknowledgement-durability boundary, not a temporal eventually.
  Between recoveries an in-flight entry is UNRESOLVED (neither
  delivered nor lost); the predicate reads what has been ACCEPTED, and
  emissions of a later Running segment are new application work, not
  the recovery's redrive.
\<close>

definition dwc_alo_at :: "frontier \<Rightarrow> ('k, 'v) dwc_state \<Rightarrow> bool" where
  "dwc_alo_at f t \<longleftrightarrow> set (dwc_replay f t) \<subseteq> e_payload ` set (dwc_accepted t)"

definition dwc_eo_at :: "frontier \<Rightarrow> ('k, 'v) dwc_state \<Rightarrow> bool" where
  "dwc_eo_at f t \<longleftrightarrow> \<not> dwc_accepted_unsafe t \<and> dwc_alo_at f t"

section \<open>The instant-delivery embedding\<close>

definition dwc_embed :: "('k, 'v) dwe_state \<Rightarrow> ('k, 'v) dwc_state" where
  "dwc_embed t =
     \<lparr> dwc_inner = t, dwc_channel = [], dwc_accepted = dwe_emitted t,
       dwc_fence = 0 \<rparr>"

definition dwc_at_rest :: "('k, 'v) dwc_state \<Rightarrow> bool" where
  "dwc_at_rest s \<longleftrightarrow>
     dwc_channel s = [] \<and> dwc_accepted s = dwe_emitted (dwc_inner s)
   \<and> dwc_fence s = 0"

text \<open>E-2, the project-back identities: the embedded inner IS the landed
  state, and on embedded states the accepted record IS the landed
  ledger.  Any landed predicate or theorem about @{term t} is verbatim a
  fact about @{term "dwc_inner (dwc_embed t)"}.\<close>

lemma dwc_embed_inner [simp]: "dwc_inner (dwc_embed t) = t"
  by (simp add: dwc_embed_def)

lemma dwc_embed_channel [simp]: "dwc_channel (dwc_embed t) = []"
  by (simp add: dwc_embed_def)

lemma dwc_embed_accepted [simp]: "dwc_accepted (dwc_embed t) = dwe_emitted t"
  by (simp add: dwc_embed_def)

lemma dwc_embed_fence [simp]: "dwc_fence (dwc_embed t) = 0"
  by (simp add: dwc_embed_def)

lemma dwc_at_rest_embed: "dwc_at_rest (dwc_embed t)"
  by (simp add: dwc_at_rest_def)

lemma dwc_embed_init: "dwc_embed (dwe_init b K fin) = dwc_init b K fin"
  by (simp add: dwc_embed_def dwc_init_def dwe_init_def)

text \<open>The verdict bridges: on embedded states the accepted-record
  verdicts COINCIDE with the landed sent-ledger verdicts --- pure
  definitional unfolding, no new content.  This is what licenses the
  twin naming of the accepted-record hazard family.\<close>

lemma dwc_accepted_unsafe_embed:
  "dwc_accepted_unsafe (dwc_embed t) \<longleftrightarrow> effect_unsafe t"
  by (simp add: dwc_accepted_unsafe_def dwc_accepted_premature_def
                dwc_accepted_duplicate_def effect_unsafe_def premature_def
                duplicate_def dwc_src_def)

lemma dwc_alo_at_embed:
  "dwc_alo_at f (dwc_embed t) \<longleftrightarrow> at_least_once_at f t"
  by (simp add: dwc_alo_at_def at_least_once_at_def dwc_replay_def
                dwc_src_def dwc_scope_def)

lemma dwc_eo_at_embed:
  "dwc_eo_at f (dwc_embed t) \<longleftrightarrow> exactly_once_at f t"
  by (simp add: dwc_eo_at_def exactly_once_at_def dwc_accepted_unsafe_embed
                dwc_alo_at_embed)

subsection \<open>Draining the wire at fence zero\<close>

text \<open>The drain helper: from any state whose fence is zero, arriving
  index 0 repeatedly resolves the whole wire in order, appending it to
  the accepted record --- the engine of the instant-delivery embedding.\<close>

lemma dwc_drain_channel:
  assumes "dwc_channel u = ch"
      and "dwc_fence u = 0"
  shows "dwc_temporal_trace u (replicate (length ch) (DWC_Arrive 0))
           (u\<lparr>dwc_channel := [], dwc_accepted := dwc_accepted u @ ch\<rparr>)"
  using assms
proof (induction ch arbitrary: u)
  case Nil
  have "u\<lparr>dwc_channel := [], dwc_accepted := dwc_accepted u @ []\<rparr> = u"
    using Nil.prems(1) by (cases u) simp
  then show ?case
    using dwc_temporal_trace.dwc_refl by fastforce
next
  case (Cons x ch)
  define u1 where
    "u1 = u\<lparr>dwc_channel := ch, dwc_accepted := dwc_accepted u @ [x]\<rparr>"
  have arr: "dwc_arrive u 0 u1"
    by (rule dwc_arrive_acceptI[of 0 u u1])
       (simp_all add: Cons.prems u1_def)
  have ch1: "dwc_channel u1 = ch" and fn1: "dwc_fence u1 = 0"
    by (simp_all add: u1_def Cons.prems(2))
  have rest: "dwc_temporal_trace u1 (replicate (length ch) (DWC_Arrive 0))
                (u1\<lparr>dwc_channel := [], dwc_accepted := dwc_accepted u1 @ ch\<rparr>)"
    by (rule Cons.IH[OF ch1 fn1])
  have end_eq: "u1\<lparr>dwc_channel := [], dwc_accepted := dwc_accepted u1 @ ch\<rparr>
              = u\<lparr>dwc_channel := [], dwc_accepted := dwc_accepted u @ (x # ch)\<rparr>"
    by (simp add: u1_def)
  have "dwc_temporal_trace u (DWC_Arrive 0 # replicate (length ch) (DWC_Arrive 0))
          (u\<lparr>dwc_channel := [], dwc_accepted := dwc_accepted u @ (x # ch)\<rparr>)"
    by (rule dwc_temporal_trace.dwc_arrive_step[OF arr])
       (use rest end_eq in simp)
  then show ?case by simp
qed

subsection \<open>E-1: every cyclic trace embeds, instant delivery\<close>

text \<open>
  Per landed action group: a non-publish label maps to its own lift; a
  publish maps to the lift followed by its own arrival (fence 0 accepts
  everything); a cursor re-drive maps to the channeled re-drive
  followed by the arrivals of its whole batch in order (index 0 each
  time); Resume maps to the resume lift.  The run is at rest at every
  group boundary.  The existential form is pinned: the action list is
  state-dependent through the batch length, so no pure action map
  exists --- the honest difference from the Small-Step datatype-map
  embedding.
\<close>

theorem cyclic_embeds_instant_delivery:
  assumes "dwe_temporal_trace t xs t'"
  shows "\<exists>ys. dwc_temporal_trace (dwc_embed t) ys (dwc_embed t')"
  using assms
proof (induction rule: dwe_temporal_trace.induct)
  case (dwe_refl t)
  show ?case
    by (intro exI[of _ "[]"] dwc_temporal_trace.dwc_refl)
next
  case (dwe_label_step t a t' as t'')
  obtain ys where ys: "dwc_temporal_trace (dwc_embed t') ys (dwc_embed t'')"
    using dwe_label_step.IH by blast
  have wf: "wellformed_exec_state (dwe_core (dwc_inner (dwc_embed t)))"
    using dwe_label_step.hyps(1) by simp
  have g: "exec_label_preserves_history_wf
             (dwe_core (dwc_inner (dwc_embed t))) a"
    using dwe_label_step.hyps(2) by simp
  have istep: "dwe_step (dwc_inner (dwc_embed t)) a t'"
    using dwe_label_step.hyps(3) by simp
  show ?case
  proof (cases "\<exists>c e. a = DoDownstream c e")
    case False
    then have nonpub: "\<forall>c e. a \<noteq> DoDownstream c e" by blast
    have em_eq: "dwe_emitted t' = dwe_emitted t"
      by (rule dwe_step_nonpub_emitted[OF dwe_label_step.hyps(3) nonpub])
    have step1: "dwc_step (dwc_embed t) a (dwc_embed t')"
      by (rule dwc_lift_nonpubI[OF istep nonpub])
         (simp add: dwc_embed_def em_eq)
    have head: "dwc_temporal_trace (dwc_embed t) [DWC_Label a] (dwc_embed t')"
      by (rule dwc_temporal_trace.dwc_label_step[OF wf g step1
            dwc_temporal_trace.dwc_refl])
    show ?thesis
      by (intro exI[of _ "DWC_Label a # ys"])
         (use dwc_temporal_trace_append[OF head ys] in simp)
  next
    case True
    then obtain c e where a_eq: "a = DoDownstream c e" by blast
    have em_eq: "dwe_emitted t' = dwe_emitted t @ [dwc_stamp (dwc_embed t) (c, e)]"
      using dwe_step_pub_emitted[OF dwe_label_step.hyps(3)[unfolded a_eq]]
      by (simp add: dwc_src_def)
    define u where
      "u = (dwc_embed t)\<lparr>dwc_inner := t',
             dwc_channel := [dwc_stamp (dwc_embed t) (c, e)]\<rparr>"
    have step1: "dwc_step (dwc_embed t) (DoDownstream c e) u"
      by (rule dwc_send_pubI[OF istep[unfolded a_eq]])
         (simp add: u_def)
    have arr: "dwc_arrive u 0 (dwc_embed t')"
      by (rule dwc_arrive_acceptI[of 0 u])
         (simp_all add: u_def dwc_embed_def em_eq)
    have head: "dwc_temporal_trace (dwc_embed t)
                  [DWC_Label a, DWC_Arrive 0] (dwc_embed t')"
      unfolding a_eq
      by (rule dwc_temporal_trace.dwc_label_step[OF wf[unfolded a_eq] g[unfolded a_eq]
            step1 dwc_temporal_trace.dwc_arrive_step[OF arr
              dwc_temporal_trace.dwc_refl]])
    show ?thesis
      by (intro exI[of _ "[DWC_Label a, DWC_Arrive 0] @ ys"])
         (rule dwc_temporal_trace_append[OF head ys])
  qed
next
  case (dwe_reconcile_step m t f t' as t'')
  obtain ys where ys: "dwc_temporal_trace (dwc_embed t') ys (dwc_embed t'')"
    using dwe_reconcile_step.IH by blast
  define B where "B = map (dwc_stamp (dwc_embed t))
                        (drop m (dwc_replay f (dwc_embed t)))"
  have em_eq: "dwe_emitted t' = dwe_emitted t @ B"
    using dwe_reconcile_step.hyps(1)
    by (simp add: emitting_reconcile_def B_def dwc_stamp_unfold
                  dwc_replay_def dwc_src_def dwc_scope_def)
  define u where
    "u = (dwc_embed t)\<lparr>dwc_inner := t', dwc_channel := B\<rparr>"
  have rec: "emitting_reconcile m (dwc_inner (dwc_embed t)) f t'"
    using dwe_reconcile_step.hyps(1) by simp
  have step1: "dwc_reconcile_send m (dwc_embed t) f u"
    by (rule dwc_reconcile_sendI[OF rec]) (simp add: u_def B_def)
  have drain: "dwc_temporal_trace u (replicate (length B) (DWC_Arrive 0))
                 (u\<lparr>dwc_channel := [], dwc_accepted := dwc_accepted u @ B\<rparr>)"
    by (rule dwc_drain_channel) (simp_all add: u_def)
  have end_eq: "u\<lparr>dwc_channel := [], dwc_accepted := dwc_accepted u @ B\<rparr>
              = dwc_embed t'"
    by (simp add: u_def dwc_embed_def em_eq)
  have head: "dwc_temporal_trace (dwc_embed t)
                (DWC_Reconcile m f # replicate (length B) (DWC_Arrive 0))
                (dwc_embed t')"
    by (rule dwc_temporal_trace.dwc_reconcile_step[OF step1])
       (use drain end_eq in simp)
  show ?case
    by (intro exI[of _ "(DWC_Reconcile m f
            # replicate (length B) (DWC_Arrive 0)) @ ys"])
       (use dwc_temporal_trace_append[OF head ys] in simp)
next
  case (dwe_resume_step t t' as t'')
  obtain ys where ys: "dwc_temporal_trace (dwc_embed t') ys (dwc_embed t'')"
    using dwe_resume_step.IH by blast
  have em_eq: "dwe_emitted t' = dwe_emitted t"
    by (rule dwe_resume_emitted_same[OF dwe_resume_step.hyps(1)])
  have res: "dwe_resume (dwc_inner (dwc_embed t)) t'"
    using dwe_resume_step.hyps(1) by simp
  have step1: "dwc_resume_lift (dwc_embed t) (dwc_embed t')"
    by (rule dwc_resume_liftI[OF res]) (simp add: dwc_embed_def em_eq)
  have head: "dwc_temporal_trace (dwc_embed t) [DWC_Resume] (dwc_embed t')"
    by (rule dwc_temporal_trace.dwc_resume_step[OF step1
          dwc_temporal_trace.dwc_refl])
  show ?case
    by (intro exI[of _ "DWC_Resume # ys"])
       (use dwc_temporal_trace_append[OF head ys] in simp)
qed

corollary dwc_reachable_of_reachable:
  assumes "dwe_reachable t"
  shows "dwc_reachable (dwc_embed t)"
proof -
  obtain xs where "dwe_temporal_trace (dwe_init Map.empty {0, 1} ec2) xs t"
    using assms unfolding dwe_reachable_def by blast
  then obtain ys where
    "dwc_temporal_trace (dwc_embed (dwe_init Map.empty {0, 1} ec2)) ys (dwc_embed t)"
    using cyclic_embeds_instant_delivery by blast
  then show ?thesis
    unfolding dwc_reachable_def dwc_embed_init by blast
qed

text \<open>
  E-3, THE HONEST TRANSFER SCOPE (binding wording).  "The landed corpus
  transfers verbatim" is true EXACTLY of: (i) the embedded
  instant-delivery fragment (E-1/E-2: every landed theorem holds of the
  embedded run's inner, and the accepted-record notions coincide with
  the landed ones there), and (ii) the inner-projection structural
  invariants below, along ALL dwc traces.  It is FALSE of, and never
  claimed for: the Dilemma family, the escape (B1/B2), the discipline,
  and exactly-once on the accepted record --- those are re-litigated
  subjects (the zombie defeat and the fenced positive are genuinely new
  theorems), and the S4d wave, the Decider, the Dichotomy, the
  Small-Step variant, and the terminal branch are out of scope exactly
  as the Small-Step slice scoped them.  Also NOT claimed: a general
  projection of dwc traces back into cyclic traces --- the two
  composites project to @{const policy_redrive} instances, which are
  relations the landed machine studies but not landed trace actions;
  the inner of a dwc-reachable state is NOT claimed
  @{const dwe_reachable}.
\<close>

section \<open>Inner-projection lifts: the landed structural invariants along dwc traces\<close>

text \<open>
  Proved by dwc-trace induction using the landed PER-RULE preservation
  lemmas (never the landed end-to-end reachability facts, which do not
  apply --- E-3), with the arrive/lose cases trivial by inner-inertness
  and the composite cases via their explicit ledger shape (the
  constant-batch @{const policy_redrive} projection at the pinned
  type carries the heal; the stamp and append bookkeeping is direct and
  polymorphic).
\<close>

lemma dwc_fenced_redrive_inner_stamps_bounded:
  assumes fr: "dwc_fenced_redrive f t t'"
      and sb: "stamps_bounded (dwc_inner t)"
  shows "stamps_bounded (dwc_inner t')"
proof -
  have em: "dwe_emitted (dwc_inner t') = dwe_emitted (dwc_inner t)
              @ map (dwc_stamp t) (dwc_sink_delta f t)"
    by (rule dwc_fenced_redrive_components(5)[OF fr])
  have src: "exec_src_hist (dwe_core (dwc_inner t'))
               = exec_src_hist (dwe_core (dwc_inner t))"
    by (rule dwc_fenced_redrive_components(6)[OF fr])
  show ?thesis
    using sb unfolding stamps_bounded_def em src
    by (auto simp: dwc_src_def)
qed

lemma dwc_escape_redrive_inner_stamps_bounded:
  assumes fr: "dwc_escape_redrive f t t'"
      and sb: "stamps_bounded (dwc_inner t)"
  shows "stamps_bounded (dwc_inner t')"
proof -
  have em: "dwe_emitted (dwc_inner t') = dwe_emitted (dwc_inner t)
              @ map (dwc_stamp t) (dwc_sink_delta f t)"
    by (rule dwc_escape_redrive_components(5)[OF fr])
  have src: "exec_src_hist (dwe_core (dwc_inner t'))
               = exec_src_hist (dwe_core (dwc_inner t))"
    by (rule dwc_escape_redrive_components(6)[OF fr])
  show ?thesis
    using sb unfolding stamps_bounded_def em src
    by (auto simp: dwc_src_def)
qed

lemma dwc_trace_stamps_bounded:
  assumes "dwc_temporal_trace t xs t'"
      and "stamps_bounded (dwc_inner t)"
  shows "stamps_bounded (dwc_inner t')"
  using assms
proof (induction rule: dwc_temporal_trace.induct)
  case (dwc_refl t)
  then show ?case by simp
next
  case (dwc_label_step t a t' as t'')
  then show ?case
    using dwe_step_stamps_bounded dwc_step_inner by blast
next
  case (dwc_reconcile_step m t f t' as t'')
  then show ?case
    using emitting_reconcile_stamps_bounded dwc_reconcile_send_inner by blast
next
  case (dwc_resume_step t t' as t'')
  then show ?case
    using dwe_resume_stamps_bounded dwc_resume_lift_inner by blast
next
  case (dwc_arrive_step t i t' as t'')
  then show ?case using dwc_arrive_inner_stutter by fastforce
next
  case (dwc_lose_step t i t' as t'')
  then show ?case using dwc_lose_inner_stutter by fastforce
next
  case (dwc_escape_step f t t' as t'')
  then show ?case using dwc_escape_redrive_inner_stamps_bounded by blast
next
  case (dwc_fenced_step f t t' as t'')
  then show ?case using dwc_fenced_redrive_inner_stamps_bounded by blast
qed

theorem dwc_reachable_stamps_bounded:
  assumes "dwc_reachable t"
  shows "stamps_bounded (dwc_inner t)"
proof -
  obtain xs where "dwc_temporal_trace (dwc_init Map.empty {0, 1} ec2) xs t"
    using assms unfolding dwc_reachable_def by blast
  moreover have "stamps_bounded (dwc_inner (dwc_init Map.empty {0, 1} ec2))"
    by (simp add: dwc_init_def dwe_init_stamps_bounded)
  ultimately show ?thesis using dwc_trace_stamps_bounded by blast
qed

text \<open>The epoch-factorization pair on the inner: only the resume lift
  bumps the inner epoch; every other dwc rule is epoch-constant.\<close>

lemma dwc_trace_epoch_mono:
  assumes "dwc_temporal_trace t xs t'"
  shows "dwe_epoch (dwc_inner t) \<le> dwe_epoch (dwc_inner t')"
  using assms
proof (induction rule: dwc_temporal_trace.induct)
  case (dwc_refl t)
  then show ?case by simp
next
  case (dwc_label_step t a t' as t'')
  then show ?case using dwe_step_epoch_const dwc_step_inner by fastforce
next
  case (dwc_reconcile_step m t f t' as t'')
  then show ?case
    using emitting_reconcile_epoch_const dwc_reconcile_send_inner by fastforce
next
  case (dwc_resume_step t t' as t'')
  then show ?case using dwe_resume_epoch_Suc dwc_resume_lift_inner by fastforce
next
  case (dwc_arrive_step t i t' as t'')
  then show ?case using dwc_arrive_inner_stutter by fastforce
next
  case (dwc_lose_step t i t' as t'')
  then show ?case using dwc_lose_inner_stutter by fastforce
next
  case (dwc_escape_step f t t' as t'')
  then show ?case using dwc_escape_redrive_components(4) by fastforce
next
  case (dwc_fenced_step f t t' as t'')
  then show ?case using dwc_fenced_redrive_components(4) by fastforce
qed

lemma dwc_trace_no_resume_epoch_const:
  assumes "dwc_temporal_trace t xs t'"
      and "DWC_Resume \<notin> set xs"
  shows "dwe_epoch (dwc_inner t') = dwe_epoch (dwc_inner t)"
  using assms
proof (induction rule: dwc_temporal_trace.induct)
  case (dwc_refl t)
  then show ?case by simp
next
  case (dwc_label_step t a t' as t'')
  then show ?case using dwe_step_epoch_const dwc_step_inner by fastforce
next
  case (dwc_reconcile_step m t f t' as t'')
  then show ?case
    using emitting_reconcile_epoch_const dwc_reconcile_send_inner by fastforce
next
  case (dwc_resume_step t t' as t'')
  then show ?case by simp
next
  case (dwc_arrive_step t i t' as t'')
  then show ?case using dwc_arrive_inner_stutter by fastforce
next
  case (dwc_lose_step t i t' as t'')
  then show ?case using dwc_lose_inner_stutter by fastforce
next
  case (dwc_escape_step f t t' as t'')
  then show ?case using dwc_escape_redrive_components(4) by fastforce
next
  case (dwc_fenced_step f t t' as t'')
  then show ?case using dwc_fenced_redrive_components(4) by fastforce
qed

text \<open>Sent ledger and committed prefix are append-only through EVERY dwc
  rule --- the shape premises of the landed hazard-persistence engines.\<close>

lemma dwc_trace_emitted_ext:
  assumes "dwc_temporal_trace t xs t'"
  shows "\<exists>es. dwe_emitted (dwc_inner t') = dwe_emitted (dwc_inner t) @ es"
  using assms
proof (induction rule: dwc_temporal_trace.induct)
  case (dwc_refl t)
  then show ?case by (intro exI[of _ "[]"]) simp
next
  case (dwc_label_step t a t' as t'')
  then show ?case
    using dwe_step_emitted_ext[OF dwc_step_inner[OF dwc_label_step.hyps(3)]]
    by (metis append.assoc)
next
  case (dwc_reconcile_step m t f t' as t'')
  then show ?case
    using emitting_reconcile_emitted_ext[OF dwc_reconcile_send_inner[OF
            dwc_reconcile_step.hyps(1)]]
    by (metis append.assoc)
next
  case (dwc_resume_step t t' as t'')
  then show ?case
    using dwe_resume_emitted_same[OF dwc_resume_lift_inner[OF
            dwc_resume_step.hyps(1)]]
    by simp
next
  case (dwc_arrive_step t i t' as t'')
  then show ?case using dwc_arrive_inner_stutter by fastforce
next
  case (dwc_lose_step t i t' as t'')
  then show ?case using dwc_lose_inner_stutter by fastforce
next
  case (dwc_escape_step f t t' as t'')
  then show ?case
    using dwc_escape_redrive_components(5)[OF dwc_escape_step.hyps(1)]
    by (metis append.assoc)
next
  case (dwc_fenced_step f t t' as t'')
  then show ?case
    using dwc_fenced_redrive_components(5)[OF dwc_fenced_step.hyps(1)]
    by (metis append.assoc)
qed

lemma dwc_trace_src_ext:
  assumes "dwc_temporal_trace t xs t'"
  shows "\<exists>ext. exec_src_hist (dwe_core (dwc_inner t'))
                 = exec_src_hist (dwe_core (dwc_inner t)) @ ext"
  using assms
proof (induction rule: dwc_temporal_trace.induct)
  case (dwc_refl t)
  then show ?case by (intro exI[of _ "[]"]) simp
next
  case (dwc_label_step t a t' as t'')
  then show ?case
    using dw_exec_step_src_ext[OF dwe_step_core[OF dwc_step_inner[OF
            dwc_label_step.hyps(3)]]]
    by (metis append.assoc)
next
  case (dwc_reconcile_step m t f t' as t'')
  then show ?case
    using emitting_reconcile_src_same[OF dwc_reconcile_send_inner[OF
            dwc_reconcile_step.hyps(1)]]
    by simp
next
  case (dwc_resume_step t t' as t'')
  then show ?case
    using dwe_resume_src_same[OF dwc_resume_lift_inner[OF
            dwc_resume_step.hyps(1)]]
    by simp
next
  case (dwc_arrive_step t i t' as t'')
  then show ?case using dwc_arrive_inner_stutter by fastforce
next
  case (dwc_lose_step t i t' as t'')
  then show ?case using dwc_lose_inner_stutter by fastforce
next
  case (dwc_escape_step f t t' as t'')
  then show ?case
    using dwc_escape_redrive_components(6)[OF dwc_escape_step.hyps(1)] by simp
next
  case (dwc_fenced_step f t t' as t'')
  then show ?case
    using dwc_fenced_redrive_components(6)[OF dwc_fenced_step.hyps(1)] by simp
qed

text \<open>
  Anti-healing on the SENT ledger, lifted: the landed sent-side verdict
  @{const effect_unsafe} persists along every dwc trace --- keeping the
  sent-side reading a true, stated fact of the variant.  As landed, the
  @{const stamps_bounded} premise is load-bearing, not decorative, and
  reachability discharges it at every @{const dwc_reachable} state.
\<close>

theorem dwc_effect_unsafe_trace_monotone:
  assumes "dwc_temporal_trace t xs t'"
      and "stamps_bounded (dwc_inner t)"
      and "effect_unsafe (dwc_inner t)"
  shows "effect_unsafe (dwc_inner t')"
  using assms
proof (induction rule: dwc_temporal_trace.induct)
  case (dwc_refl t)
  then show ?case by simp
next
  case (dwc_label_step t a t' as t'')
  have step: "dwe_step (dwc_inner t) a (dwc_inner t')"
    by (rule dwc_step_inner[OF dwc_label_step.hyps(3)])
  have sb': "stamps_bounded (dwc_inner t')"
    by (rule dwe_step_stamps_bounded[OF step dwc_label_step.prems(1)])
  have un': "effect_unsafe (dwc_inner t')"
    using effect_unsafe_monotone[OF dwc_label_step.prems(1)
            dwc_label_step.prems(2)] step
    by blast
  show ?case by (rule dwc_label_step.IH[OF sb' un'])
next
  case (dwc_reconcile_step m t f t' as t'')
  have step: "emitting_reconcile m (dwc_inner t) f (dwc_inner t')"
    by (rule dwc_reconcile_send_inner[OF dwc_reconcile_step.hyps(1)])
  have sb': "stamps_bounded (dwc_inner t')"
    by (rule emitting_reconcile_stamps_bounded[OF step
          dwc_reconcile_step.prems(1)])
  have un': "effect_unsafe (dwc_inner t')"
    using effect_unsafe_monotone[OF dwc_reconcile_step.prems(1)
            dwc_reconcile_step.prems(2)] step
    by blast
  show ?case by (rule dwc_reconcile_step.IH[OF sb' un'])
next
  case (dwc_resume_step t t' as t'')
  have step: "dwe_resume (dwc_inner t) (dwc_inner t')"
    by (rule dwc_resume_lift_inner[OF dwc_resume_step.hyps(1)])
  have sb': "stamps_bounded (dwc_inner t')"
    by (rule dwe_resume_stamps_bounded[OF step dwc_resume_step.prems(1)])
  have un': "effect_unsafe (dwc_inner t')"
    using effect_unsafe_monotone[OF dwc_resume_step.prems(1)
            dwc_resume_step.prems(2)] step
    by blast
  show ?case by (rule dwc_resume_step.IH[OF sb' un'])
next
  case (dwc_arrive_step t i t' as t'')
  then show ?case using dwc_arrive_inner_stutter by fastforce
next
  case (dwc_lose_step t i t' as t'')
  then show ?case using dwc_lose_inner_stutter by fastforce
next
  case (dwc_escape_step f t t' as t'')
  have em: "\<exists>es. dwe_emitted (dwc_inner t') = dwe_emitted (dwc_inner t) @ es"
    using dwc_escape_redrive_components(5)[OF dwc_escape_step.hyps(1)] by blast
  have src: "\<exists>ext. exec_src_hist (dwe_core (dwc_inner t'))
                     = exec_src_hist (dwe_core (dwc_inner t)) @ ext"
    using dwc_escape_redrive_components(6)[OF dwc_escape_step.hyps(1)]
    by (metis append_Nil2)
  have sb': "stamps_bounded (dwc_inner t')"
    by (rule dwc_escape_redrive_inner_stamps_bounded[OF
          dwc_escape_step.hyps(1) dwc_escape_step.prems(1)])
  have un': "effect_unsafe (dwc_inner t')"
    using dwc_escape_step.prems(2)
    unfolding effect_unsafe_def
    using premature_preserved[OF dwc_escape_step.prems(1) _ em src]
          duplicate_preserved[OF _ em]
    by blast
  show ?case by (rule dwc_escape_step.IH[OF sb' un'])
next
  case (dwc_fenced_step f t t' as t'')
  have em: "\<exists>es. dwe_emitted (dwc_inner t') = dwe_emitted (dwc_inner t) @ es"
    using dwc_fenced_redrive_components(5)[OF dwc_fenced_step.hyps(1)] by blast
  have src: "\<exists>ext. exec_src_hist (dwe_core (dwc_inner t'))
                     = exec_src_hist (dwe_core (dwc_inner t)) @ ext"
    using dwc_fenced_redrive_components(6)[OF dwc_fenced_step.hyps(1)]
    by (metis append_Nil2)
  have sb': "stamps_bounded (dwc_inner t')"
    by (rule dwc_fenced_redrive_inner_stamps_bounded[OF
          dwc_fenced_step.hyps(1) dwc_fenced_step.prems(1)])
  have un': "effect_unsafe (dwc_inner t')"
    using dwc_fenced_step.prems(2)
    unfolding effect_unsafe_def
    using premature_preserved[OF dwc_fenced_step.prems(1) _ em src]
          duplicate_preserved[OF _ em]
    by blast
  show ?case by (rule dwc_fenced_step.IH[OF sb' un'])
qed

text \<open>The heal, by projection: the channeled cursor re-drive and both
  atomic composites heal every scoped store mismatch at their own
  frontier --- cited through the landed relay heal (the cursor lift IS
  the landed reconcile on the inner) and the landed
  @{thm [source] policy_redrive_heals} at the constant-batch instances.
  No re-proof.\<close>

theorem dwc_heal_via_projection:
  fixes t :: "(nat, nat) dwc_state"
  assumes "dwc_reconcile_send m t f t' \<or> dwc_escape_redrive f t t'
           \<or> dwc_fenced_redrive f t t'"
  shows "\<forall>k. \<not> mismatch_at (proto_of_exec_at (dwe_core (dwc_inner t')) f) f k"
  using assms
proof (elim disjE)
  assume "dwc_reconcile_send m t f t'"
  then show ?thesis
    by (rule emitting_reconcile_heals[OF dwc_reconcile_send_inner])
next
  assume "dwc_escape_redrive f t t'"
  then show ?thesis
    by (rule policy_redrive_heals[OF dwc_escape_redrive_inner_projects])
next
  assume "dwc_fenced_redrive f t t'"
  then show ?thesis
    by (rule policy_redrive_heals[OF dwc_fenced_redrive_inner_projects])
qed

section \<open>The ledger accounting: sent = in flight + accepted + dropped-or-lost\<close>

text \<open>
  Every occurrence in flight or accepted is backed by a sent occurrence;
  the deficit is exactly the dropped-or-lost mass (fence drops and wire
  losses) --- stated as a @{const count_list} sub-partition inequality
  because drops and losses are not separately recorded (a ghost field
  was considered and rejected: extra state, no consumer).  Send rules
  append equally to a side and to the sent ledger; the composites
  append the SAME stamped batch to accepted and to the sent ledger; an
  accepting arrival moves one occurrence across the partition; drops
  and losses shrink the left side.
\<close>

definition dwc_ledger_accounting :: "('k, 'v) dwc_state \<Rightarrow> bool" where
  "dwc_ledger_accounting t \<longleftrightarrow>
     (\<forall>x. count_list (dwc_channel t) x + count_list (dwc_accepted t) x
          \<le> count_list (dwe_emitted (dwc_inner t)) x)"

lemma count_list_nth_split:
  assumes "i < length xs"
  shows "count_list xs x
       = count_list (take i xs) x + count_list (drop (Suc i) xs) x
         + (if xs ! i = x then 1 else 0)"
proof -
  have "count_list (take i xs @ xs ! i # drop (Suc i) xs) x
      = count_list (take i xs) x + count_list (drop (Suc i) xs) x
        + (if xs ! i = x then 1 else 0)"
    by simp
  then show ?thesis
    by (metis id_take_nth_drop[OF assms])
qed

lemma dwc_step_ledger_accounting:
  assumes step: "dwc_step t a t'"
      and acc: "dwc_ledger_accounting t"
  shows "dwc_ledger_accounting t'"
proof (cases "\<exists>c e. a = DoDownstream c e")
  case False
  then have nonpub: "\<forall>c e. a \<noteq> DoDownstream c e" by blast
  have em: "dwe_emitted (dwc_inner t') = dwe_emitted (dwc_inner t)"
    by (rule dwe_step_nonpub_emitted[OF dwc_step_inner[OF step] nonpub])
  have ch: "dwc_channel t' = dwc_channel t"
    using dwc_step_channel_shape[OF step] nonpub by blast
  show ?thesis
    using acc
    unfolding dwc_ledger_accounting_def em ch dwc_step_accepted_same[OF step]
    by simp
next
  case True
  then obtain c e where a_eq: "a = DoDownstream c e" by blast
  have both: "dwc_channel t' = dwc_channel t @ [dwc_stamp t (c, e)]
            \<and> dwe_emitted (dwc_inner t')
                = dwe_emitted (dwc_inner t) @ [dwc_stamp t (c, e)]"
    by (rule dwc_send_entry_eq[OF step[unfolded a_eq]])
  show ?thesis
    unfolding dwc_ledger_accounting_def
  proof
    fix x
    have "count_list (dwc_channel t) x + count_list (dwc_accepted t) x
        \<le> count_list (dwe_emitted (dwc_inner t)) x"
      using acc unfolding dwc_ledger_accounting_def by blast
    then show "count_list (dwc_channel t') x + count_list (dwc_accepted t') x
        \<le> count_list (dwe_emitted (dwc_inner t')) x"
      unfolding conjunct1[OF both] conjunct2[OF both]
        dwc_step_accepted_same[OF step]
      by simp
  qed
qed

lemma dwc_arrive_ledger_accounting:
  assumes step: "dwc_arrive t i t'"
      and acc: "dwc_ledger_accounting t"
  shows "dwc_ledger_accounting t'"
proof -
  have len: "i < length (dwc_channel t)"
   and ch': "dwc_channel t' = take i (dwc_channel t)
               @ drop (Suc i) (dwc_channel t)"
   and accs: "dwc_accepted t' = dwc_accepted t @ [dwc_channel t ! i]
              \<or> dwc_accepted t' = dwc_accepted t"
    using dwc_arrive_shape[OF step] by blast+
  have inner: "dwc_inner t' = dwc_inner t"
    by (rule dwc_arrive_inner_stutter[OF step])
  show ?thesis
    unfolding dwc_ledger_accounting_def
  proof
    fix x
    have split: "count_list (dwc_channel t) x
        = count_list (take i (dwc_channel t)) x
          + count_list (drop (Suc i) (dwc_channel t)) x
          + (if dwc_channel t ! i = x then 1 else 0)"
      by (rule count_list_nth_split[OF len])
    have base: "count_list (dwc_channel t) x + count_list (dwc_accepted t) x
        \<le> count_list (dwe_emitted (dwc_inner t)) x"
      using acc unfolding dwc_ledger_accounting_def by blast
    have chapp: "count_list (dwc_channel t') x
        = count_list (take i (dwc_channel t)) x
          + count_list (drop (Suc i) (dwc_channel t)) x"
      unfolding ch' by simp
    from accs show "count_list (dwc_channel t') x + count_list (dwc_accepted t') x
        \<le> count_list (dwe_emitted (dwc_inner t')) x"
    proof
      assume A: "dwc_accepted t' = dwc_accepted t @ [dwc_channel t ! i]"
      have app: "count_list (dwc_accepted t') x
          = count_list (dwc_accepted t) x
            + (if dwc_channel t ! i = x then 1 else 0)"
        unfolding A by simp
      show "count_list (dwc_channel t') x + count_list (dwc_accepted t') x
          \<le> count_list (dwe_emitted (dwc_inner t')) x"
        unfolding inner using base split chapp app by linarith
    next
      assume A: "dwc_accepted t' = dwc_accepted t"
      show "count_list (dwc_channel t') x + count_list (dwc_accepted t') x
          \<le> count_list (dwe_emitted (dwc_inner t')) x"
        unfolding inner A using base split chapp by linarith
    qed
  qed
qed

lemma dwc_lose_ledger_accounting:
  assumes step: "dwc_lose t i t'"
      and acc: "dwc_ledger_accounting t"
  shows "dwc_ledger_accounting t'"
proof -
  have len: "i < length (dwc_channel t)"
   and t': "t' = t\<lparr>dwc_channel := take i (dwc_channel t)
                     @ drop (Suc i) (dwc_channel t)\<rparr>"
    using step by (simp_all add: dwc_lose_def)
  show ?thesis
    unfolding dwc_ledger_accounting_def
  proof
    fix x
    have split: "count_list (dwc_channel t) x
        = count_list (take i (dwc_channel t)) x
          + count_list (drop (Suc i) (dwc_channel t)) x
          + (if dwc_channel t ! i = x then 1 else 0)"
      by (rule count_list_nth_split[OF len])
    have base: "count_list (dwc_channel t) x + count_list (dwc_accepted t) x
        \<le> count_list (dwe_emitted (dwc_inner t)) x"
      using acc unfolding dwc_ledger_accounting_def by blast
    have chapp: "count_list (dwc_channel t') x
        = count_list (take i (dwc_channel t)) x
          + count_list (drop (Suc i) (dwc_channel t)) x"
      unfolding t' by simp
    have same: "dwc_accepted t' = dwc_accepted t"
      and inner: "dwc_inner t' = dwc_inner t"
      unfolding t' by simp_all
    show "count_list (dwc_channel t') x + count_list (dwc_accepted t') x
        \<le> count_list (dwe_emitted (dwc_inner t')) x"
      unfolding same inner using base split chapp by linarith
  qed
qed

lemma dwc_resume_lift_ledger_accounting:
  assumes step: "dwc_resume_lift t t'"
      and acc: "dwc_ledger_accounting t"
  shows "dwc_ledger_accounting t'"
proof -
  have em: "dwe_emitted (dwc_inner t') = dwe_emitted (dwc_inner t)"
    by (rule dwe_resume_emitted_same[OF dwc_resume_lift_inner[OF step]])
  show ?thesis
    using acc dwc_resume_lift_wire_same[OF step]
    unfolding dwc_ledger_accounting_def em by simp
qed

lemma dwc_reconcile_send_ledger_accounting:
  assumes step: "dwc_reconcile_send m t f t'"
      and acc: "dwc_ledger_accounting t"
  shows "dwc_ledger_accounting t'"
proof -
  have em: "dwe_emitted (dwc_inner t') = dwe_emitted (dwc_inner t)
              @ map (dwc_stamp t) (drop m (dwc_replay f t))"
    using dwc_reconcile_send_inner[OF step]
    by (simp add: emitting_reconcile_def dwc_stamp_unfold dwc_replay_def
                  dwc_src_def dwc_scope_def)
  show ?thesis
    using acc
    unfolding dwc_ledger_accounting_def em
      dwc_reconcile_send_channel[OF step]
      dwc_reconcile_send_accepted_same[OF step]
    by simp
qed

lemma dwc_fenced_redrive_ledger_accounting:
  assumes step: "dwc_fenced_redrive f t t'"
      and acc: "dwc_ledger_accounting t"
  shows "dwc_ledger_accounting t'"
  using acc
  unfolding dwc_ledger_accounting_def
    dwc_fenced_redrive_components(1)[OF step]
    dwc_fenced_redrive_components(2)[OF step]
    dwc_fenced_redrive_components(5)[OF step]
  by simp

lemma dwc_escape_redrive_ledger_accounting:
  assumes step: "dwc_escape_redrive f t t'"
      and acc: "dwc_ledger_accounting t"
  shows "dwc_ledger_accounting t'"
  using acc
  unfolding dwc_ledger_accounting_def
    dwc_escape_redrive_components(1)[OF step]
    dwc_escape_redrive_components(2)[OF step]
    dwc_escape_redrive_components(5)[OF step]
  by simp

lemma dwc_trace_ledger_accounting:
  assumes "dwc_temporal_trace t xs t'"
      and "dwc_ledger_accounting t"
  shows "dwc_ledger_accounting t'"
  using assms
proof (induction rule: dwc_temporal_trace.induct)
  case (dwc_refl t)
  then show ?case by simp
next
  case (dwc_label_step t a t' as t'')
  then show ?case using dwc_step_ledger_accounting by blast
next
  case (dwc_reconcile_step m t f t' as t'')
  then show ?case using dwc_reconcile_send_ledger_accounting by blast
next
  case (dwc_resume_step t t' as t'')
  then show ?case using dwc_resume_lift_ledger_accounting by blast
next
  case (dwc_arrive_step t i t' as t'')
  then show ?case using dwc_arrive_ledger_accounting by blast
next
  case (dwc_lose_step t i t' as t'')
  then show ?case using dwc_lose_ledger_accounting by blast
next
  case (dwc_escape_step f t t' as t'')
  then show ?case using dwc_escape_redrive_ledger_accounting by blast
next
  case (dwc_fenced_step f t t' as t'')
  then show ?case using dwc_fenced_redrive_ledger_accounting by blast
qed

theorem dwc_reachable_ledger_accounting:
  assumes "dwc_reachable t"
  shows "dwc_ledger_accounting t"
proof -
  obtain xs where "dwc_temporal_trace (dwc_init Map.empty {0, 1} ec2) xs t"
    using assms unfolding dwc_reachable_def by blast
  moreover have "dwc_ledger_accounting (dwc_init Map.empty {0, 1} ec2)"
    by (simp add: dwc_ledger_accounting_def dwc_init_def dwe_init_def)
  ultimately show ?thesis using dwc_trace_ledger_accounting by blast
qed

text \<open>Set-level consequences consumed downstream: both records are
  backed by the sent ledger, which transports the landed stamp bound to
  accepted and in-flight entries.\<close>

corollary dwc_accounting_subsets:
  assumes "dwc_ledger_accounting t"
  shows "set (dwc_accepted t) \<subseteq> set (dwe_emitted (dwc_inner t))"
    and "set (dwc_channel t) \<subseteq> set (dwe_emitted (dwc_inner t))"
proof -
  show "set (dwc_accepted t) \<subseteq> set (dwe_emitted (dwc_inner t))"
  proof
    fix x assume "x \<in> set (dwc_accepted t)"
    then have "count_list (dwc_accepted t) x \<noteq> 0"
      by (simp add: count_list_0_iff)
    then have "count_list (dwe_emitted (dwc_inner t)) x \<noteq> 0"
      using assms unfolding dwc_ledger_accounting_def
      by (metis add_eq_0_iff_both_eq_0 le_zero_eq)
    then show "x \<in> set (dwe_emitted (dwc_inner t))"
      by (simp add: count_list_0_iff)
  qed
  show "set (dwc_channel t) \<subseteq> set (dwe_emitted (dwc_inner t))"
  proof
    fix x assume "x \<in> set (dwc_channel t)"
    then have "count_list (dwc_channel t) x \<noteq> 0"
      by (simp add: count_list_0_iff)
    then have "count_list (dwe_emitted (dwc_inner t)) x \<noteq> 0"
      using assms unfolding dwc_ledger_accounting_def
      by (metis add_eq_0_iff_both_eq_0 le_zero_eq)
    then show "x \<in> set (dwe_emitted (dwc_inner t))"
      by (simp add: count_list_0_iff)
  qed
qed

theorem dwc_accepted_stamps_bounded:
  assumes "dwc_reachable t"
  shows "(\<forall>x \<in> set (dwc_accepted t).
            e_stamp x \<le> length (exec_src_hist (dwe_core (dwc_inner t))))
       \<and> (\<forall>x \<in> set (dwc_channel t).
            e_stamp x \<le> length (exec_src_hist (dwe_core (dwc_inner t))))"
proof -
  have sb: "stamps_bounded (dwc_inner t)"
    by (rule dwc_reachable_stamps_bounded[OF assms])
  have subs: "set (dwc_accepted t) \<subseteq> set (dwe_emitted (dwc_inner t))"
    "set (dwc_channel t) \<subseteq> set (dwe_emitted (dwc_inner t))"
    using dwc_accounting_subsets[OF dwc_reachable_ledger_accounting[OF assms]]
    by blast+
  show ?thesis
    using sb subs unfolding stamps_bounded_def by blast
qed

section \<open>The fence invariant package\<close>

text \<open>
  THE EXACT INDUCTIVE STRENGTHENING (wave-design finding F-2 applied):
  epoch-boundedness of both records plus fence-boundedness.  The naive
  payload-freshness candidate ("every channel entry at or above the
  fence is payload-fresh w.r.t.\ accepted") is FALSE at a reachable
  state --- post-resume the application may legally re-enqueue and
  re-publish an already-accepted payload (the landed core carries no
  freshness guard) --- so no pinned statement consumes it; the positive
  side of the wave routes through "all residual channel entries are
  sub-fence at the composite's result" instead (slice 3).
\<close>

definition dwc_epoch_bounds :: "('k, 'v) dwc_state \<Rightarrow> bool" where
  "dwc_epoch_bounds t \<longleftrightarrow>
     (\<forall>x \<in> set (dwc_channel t).  e_epoch x \<le> dwe_epoch (dwc_inner t))
   \<and> (\<forall>x \<in> set (dwc_accepted t). e_epoch x \<le> dwe_epoch (dwc_inner t))"

definition dwc_fence_inv :: "('k, 'v) dwc_state \<Rightarrow> bool" where
  "dwc_fence_inv t \<longleftrightarrow>
     dwc_epoch_bounds t \<and> dwc_fence t \<le> Suc (dwe_epoch (dwc_inner t))"

lemma dwc_step_fence_inv:
  assumes step: "dwc_step t a t'"
      and inv: "dwc_fence_inv t"
  shows "dwc_fence_inv t'"
proof -
  have ep: "dwe_epoch (dwc_inner t') = dwe_epoch (dwc_inner t)"
    by (rule dwe_step_epoch_const[OF dwc_step_inner[OF step]])
  from dwc_step_channel_shape[OF step] show ?thesis
  proof
    assume "dwc_channel t' = dwc_channel t"
    then show ?thesis
      using inv dwc_step_accepted_same[OF step] dwc_step_fence_same[OF step]
      unfolding dwc_fence_inv_def dwc_epoch_bounds_def ep by simp
  next
    assume "\<exists>c e. a = DoDownstream c e
              \<and> dwc_channel t' = dwc_channel t @ [dwc_stamp t (c, e)]"
    then obtain c e where
      ch: "dwc_channel t' = dwc_channel t @ [dwc_stamp t (c, e)]" by blast
    show ?thesis
      using inv dwc_step_accepted_same[OF step] dwc_step_fence_same[OF step]
      unfolding dwc_fence_inv_def dwc_epoch_bounds_def ep ch by simp
  qed
qed

lemma dwc_arrive_fence_inv:
  assumes step: "dwc_arrive t i t'"
      and inv: "dwc_fence_inv t"
  shows "dwc_fence_inv t'"
proof -
  have ep: "dwe_epoch (dwc_inner t') = dwe_epoch (dwc_inner t)"
    using dwc_arrive_inner_stutter[OF step] by simp
  have len: "i < length (dwc_channel t)"
   and accs: "dwc_accepted t' = dwc_accepted t @ [dwc_channel t ! i]
              \<or> dwc_accepted t' = dwc_accepted t"
    using dwc_arrive_shape[OF step] by blast+
  have mem: "dwc_channel t ! i \<in> set (dwc_channel t)"
    by (rule nth_mem[OF len])
  from accs show ?thesis
  proof
    assume A: "dwc_accepted t' = dwc_accepted t @ [dwc_channel t ! i]"
    show ?thesis
      using inv mem dwc_arrive_channel_subset[OF step]
            dwc_arrive_fence_same[OF step]
      unfolding dwc_fence_inv_def dwc_epoch_bounds_def ep A
      by auto
  next
    assume A: "dwc_accepted t' = dwc_accepted t"
    show ?thesis
      using inv dwc_arrive_channel_subset[OF step]
            dwc_arrive_fence_same[OF step]
      unfolding dwc_fence_inv_def dwc_epoch_bounds_def ep A
      by auto
  qed
qed

lemma dwc_lose_fence_inv:
  assumes step: "dwc_lose t i t'"
      and inv: "dwc_fence_inv t"
  shows "dwc_fence_inv t'"
proof -
  have ep: "dwe_epoch (dwc_inner t') = dwe_epoch (dwc_inner t)"
    using dwc_lose_inner_stutter[OF step] by simp
  have t': "t' = t\<lparr>dwc_channel := take i (dwc_channel t)
                     @ drop (Suc i) (dwc_channel t)\<rparr>"
    using step by (simp add: dwc_lose_def)
  show ?thesis
    using inv
    unfolding dwc_fence_inv_def dwc_epoch_bounds_def ep t'
    by (auto dest: in_set_takeD in_set_dropD)
qed

lemma dwc_resume_lift_fence_inv:
  assumes step: "dwc_resume_lift t t'"
      and inv: "dwc_fence_inv t"
  shows "dwc_fence_inv t'"
proof -
  have ep: "dwe_epoch (dwc_inner t') = Suc (dwe_epoch (dwc_inner t))"
    by (rule dwe_resume_epoch_Suc[OF dwc_resume_lift_inner[OF step]])
  show ?thesis
    using inv dwc_resume_lift_wire_same[OF step]
    unfolding dwc_fence_inv_def dwc_epoch_bounds_def ep
    by (auto intro: le_SucI)
qed

lemma dwc_reconcile_send_fence_inv:
  assumes step: "dwc_reconcile_send m t f t'"
      and inv: "dwc_fence_inv t"
  shows "dwc_fence_inv t'"
proof -
  have ep: "dwe_epoch (dwc_inner t') = dwe_epoch (dwc_inner t)"
    by (rule emitting_reconcile_epoch_const[OF dwc_reconcile_send_inner[OF step]])
  show ?thesis
    using inv
    unfolding dwc_fence_inv_def dwc_epoch_bounds_def ep
      dwc_reconcile_send_channel[OF step]
      dwc_reconcile_send_accepted_same[OF step]
      dwc_reconcile_send_fence_same[OF step]
    by auto
qed

lemma dwc_fenced_redrive_fence_inv:
  assumes step: "dwc_fenced_redrive f t t'"
      and inv: "dwc_fence_inv t"
  shows "dwc_fence_inv t'"
  using inv
  unfolding dwc_fence_inv_def dwc_epoch_bounds_def
    dwc_fenced_redrive_components(1)[OF step]
    dwc_fenced_redrive_components(2)[OF step]
    dwc_fenced_redrive_components(3)[OF step]
    dwc_fenced_redrive_components(4)[OF step]
  by auto

lemma dwc_escape_redrive_fence_inv:
  assumes step: "dwc_escape_redrive f t t'"
      and inv: "dwc_fence_inv t"
  shows "dwc_fence_inv t'"
  using inv
  unfolding dwc_fence_inv_def dwc_epoch_bounds_def
    dwc_escape_redrive_components(1)[OF step]
    dwc_escape_redrive_components(2)[OF step]
    dwc_escape_redrive_components(3)[OF step]
    dwc_escape_redrive_components(4)[OF step]
  by auto

lemma dwc_trace_fence_inv:
  assumes "dwc_temporal_trace t xs t'"
      and "dwc_fence_inv t"
  shows "dwc_fence_inv t'"
  using assms
proof (induction rule: dwc_temporal_trace.induct)
  case (dwc_refl t)
  then show ?case by simp
next
  case (dwc_label_step t a t' as t'')
  then show ?case using dwc_step_fence_inv by blast
next
  case (dwc_reconcile_step m t f t' as t'')
  then show ?case using dwc_reconcile_send_fence_inv by blast
next
  case (dwc_resume_step t t' as t'')
  then show ?case using dwc_resume_lift_fence_inv by blast
next
  case (dwc_arrive_step t i t' as t'')
  then show ?case using dwc_arrive_fence_inv by blast
next
  case (dwc_lose_step t i t' as t'')
  then show ?case using dwc_lose_fence_inv by blast
next
  case (dwc_escape_step f t t' as t'')
  then show ?case using dwc_escape_redrive_fence_inv by blast
next
  case (dwc_fenced_step f t t' as t'')
  then show ?case using dwc_fenced_redrive_fence_inv by blast
qed

lemma dwc_init_fence_inv: "dwc_fence_inv (dwc_init b K fin)"
  by (simp add: dwc_fence_inv_def dwc_epoch_bounds_def dwc_init_def
                dwe_init_def)

theorem dwc_reachable_fence_inv:
  assumes "dwc_reachable t"
  shows "dwc_fence_inv t"
proof -
  obtain xs where "dwc_temporal_trace (dwc_init Map.empty {0, 1} ec2) xs t"
    using assms unfolding dwc_reachable_def by blast
  from dwc_trace_fence_inv[OF this dwc_init_fence_inv]
  show ?thesis .
qed

subsection \<open>Fence monotonicity: per step, per trace\<close>

text \<open>Only the atomic fenced re-drive writes the fence, and it can only
  raise it: at its pre-state the invariant gives
  @{term "dwc_fence t \<le> Suc (dwe_epoch (dwc_inner t))"}, and the rule
  sets exactly that successor.  No rule lowers or resets the fence ---
  what upgrades per-step rejection to PERMANENT rejection: an entry
  sub-fence now is sub-fence at every later state.\<close>

lemma dwc_step_fence_mono:
  assumes inv: "dwc_fence_inv t"
      and step: "dwc_step t a t' \<or> dwc_arrive t i t' \<or> dwc_lose t i t'
                 \<or> dwc_resume_lift t t' \<or> dwc_reconcile_send m t f t'
                 \<or> dwc_escape_redrive f t t' \<or> dwc_fenced_redrive f t t'"
  shows "dwc_fence t \<le> dwc_fence t'"
  using step
proof (elim disjE)
  assume "dwc_step t a t'"
  then show ?thesis using dwc_step_fence_same by fastforce
next
  assume "dwc_arrive t i t'"
  then show ?thesis using dwc_arrive_fence_same by fastforce
next
  assume "dwc_lose t i t'"
  then show ?thesis using dwc_lose_fence_same by fastforce
next
  assume "dwc_resume_lift t t'"
  then show ?thesis using dwc_resume_lift_wire_same by fastforce
next
  assume "dwc_reconcile_send m t f t'"
  then show ?thesis using dwc_reconcile_send_fence_same by fastforce
next
  assume "dwc_escape_redrive f t t'"
  then show ?thesis using dwc_escape_redrive_components(3) by fastforce
next
  assume "dwc_fenced_redrive f t t'"
  then show ?thesis
    using inv dwc_fenced_redrive_components(3)
    unfolding dwc_fence_inv_def by fastforce
qed

theorem dwc_trace_fence_mono:
  assumes "dwc_temporal_trace t xs t'"
      and "dwc_fence_inv t"
  shows "dwc_fence t \<le> dwc_fence t'"
  using assms
proof (induction rule: dwc_temporal_trace.induct)
  case (dwc_refl t)
  then show ?case by simp
next
  case (dwc_label_step t a t' as t'')
  have inv': "dwc_fence_inv t'"
    by (rule dwc_step_fence_inv[OF dwc_label_step.hyps(3)
          dwc_label_step.prems])
  have "dwc_fence t \<le> dwc_fence t'"
    using dwc_step_fence_same[OF dwc_label_step.hyps(3)] by simp
  then show ?case using dwc_label_step.IH[OF inv'] by simp
next
  case (dwc_reconcile_step m t f t' as t'')
  have inv': "dwc_fence_inv t'"
    by (rule dwc_reconcile_send_fence_inv[OF dwc_reconcile_step.hyps(1)
          dwc_reconcile_step.prems])
  have "dwc_fence t \<le> dwc_fence t'"
    using dwc_reconcile_send_fence_same[OF dwc_reconcile_step.hyps(1)] by simp
  then show ?case using dwc_reconcile_step.IH[OF inv'] by simp
next
  case (dwc_resume_step t t' as t'')
  have inv': "dwc_fence_inv t'"
    by (rule dwc_resume_lift_fence_inv[OF dwc_resume_step.hyps(1)
          dwc_resume_step.prems])
  have "dwc_fence t \<le> dwc_fence t'"
    using dwc_resume_lift_wire_same[OF dwc_resume_step.hyps(1)] by simp
  then show ?case using dwc_resume_step.IH[OF inv'] by simp
next
  case (dwc_arrive_step t i t' as t'')
  have inv': "dwc_fence_inv t'"
    by (rule dwc_arrive_fence_inv[OF dwc_arrive_step.hyps(1)
          dwc_arrive_step.prems])
  have "dwc_fence t \<le> dwc_fence t'"
    using dwc_arrive_fence_same[OF dwc_arrive_step.hyps(1)] by simp
  then show ?case using dwc_arrive_step.IH[OF inv'] by simp
next
  case (dwc_lose_step t i t' as t'')
  have inv': "dwc_fence_inv t'"
    by (rule dwc_lose_fence_inv[OF dwc_lose_step.hyps(1) dwc_lose_step.prems])
  have "dwc_fence t \<le> dwc_fence t'"
    using dwc_lose_fence_same[OF dwc_lose_step.hyps(1)] by simp
  then show ?case using dwc_lose_step.IH[OF inv'] by simp
next
  case (dwc_escape_step f t t' as t'')
  have inv': "dwc_fence_inv t'"
    by (rule dwc_escape_redrive_fence_inv[OF dwc_escape_step.hyps(1)
          dwc_escape_step.prems])
  have "dwc_fence t \<le> dwc_fence t'"
    using dwc_escape_redrive_components(3)[OF dwc_escape_step.hyps(1)] by simp
  then show ?case using dwc_escape_step.IH[OF inv'] by simp
next
  case (dwc_fenced_step f t t' as t'')
  have inv': "dwc_fence_inv t'"
    by (rule dwc_fenced_redrive_fence_inv[OF dwc_fenced_step.hyps(1)
          dwc_fenced_step.prems])
  have "dwc_fence t \<le> dwc_fence t'"
    using dwc_fenced_step.prems dwc_fenced_redrive_components(3)[OF
            dwc_fenced_step.hyps(1)]
    unfolding dwc_fence_inv_def by simp
  then show ?case using dwc_fenced_step.IH[OF inv'] by simp
qed

subsection \<open>The guard-level inventory fact\<close>

text \<open>Immediate from the arrive rule pair: an arrival either leaves the
  accepted record untouched (the drop path) or the arrived entry
  cleared the fence --- no stale entry is ever written by an arrival.\<close>

theorem arrive_accept_respects_fence:
  assumes "dwc_arrive t i t'"
  shows "dwc_accepted t' = dwc_accepted t
       \<or> (dwc_fence t \<le> e_epoch (dwc_channel t ! i)
          \<and> dwc_accepted t' = dwc_accepted t @ [dwc_channel t ! i])"
  using assms by (cases rule: dwc_arrive.cases) simp_all

subsection \<open>The redrive-free growth bound: sub-fence entries are permanently excluded\<close>

text \<open>
  Along ANY redrive-free continuation, the accepted record grows only
  by entries at or above the starting fence --- an entry sub-fence at
  @{term u} (every zombie) is PERMANENTLY excluded, however long the
  run, whatever arrives, in whatever order.  The redrive actions are
  excluded from the action list only because the composites'
  batches are synchronously accepted BY DESIGN --- their acceptances are
  governed by the positive theorem applied at that crash (slice 3),
  not by the arrive guard; the side condition is an action-class
  scoping of a preservation law, not a new premise on states.
\<close>

theorem accepted_growth_fenced:
  assumes "dwc_temporal_trace u xs v"
      and "dwc_fence_inv u"
      and "\<forall>f. DWC_Escape f \<notin> set xs \<and> DWC_Fenced f \<notin> set xs"
  shows "\<forall>x \<in> set (dwc_accepted v).
           x \<in> set (dwc_accepted u) \<or> dwc_fence u \<le> e_epoch x"
  using assms
proof (induction rule: dwc_temporal_trace.induct)
  case (dwc_refl t)
  then show ?case by simp
next
  case (dwc_label_step t a t' as t'')
  have inv': "dwc_fence_inv t'"
    by (rule dwc_step_fence_inv[OF dwc_label_step.hyps(3)
          dwc_label_step.prems(1)])
  have cls': "\<forall>f. DWC_Escape f \<notin> set as \<and> DWC_Fenced f \<notin> set as"
    using dwc_label_step.prems(2) by simp
  show ?case
    using dwc_label_step.IH[OF inv' cls']
          dwc_step_accepted_same[OF dwc_label_step.hyps(3)]
          dwc_step_fence_same[OF dwc_label_step.hyps(3)]
    by simp
next
  case (dwc_reconcile_step m t f t' as t'')
  have inv': "dwc_fence_inv t'"
    by (rule dwc_reconcile_send_fence_inv[OF dwc_reconcile_step.hyps(1)
          dwc_reconcile_step.prems(1)])
  have cls': "\<forall>f. DWC_Escape f \<notin> set as \<and> DWC_Fenced f \<notin> set as"
    using dwc_reconcile_step.prems(2) by simp
  show ?case
    using dwc_reconcile_step.IH[OF inv' cls']
          dwc_reconcile_send_accepted_same[OF dwc_reconcile_step.hyps(1)]
          dwc_reconcile_send_fence_same[OF dwc_reconcile_step.hyps(1)]
    by simp
next
  case (dwc_resume_step t t' as t'')
  have inv': "dwc_fence_inv t'"
    by (rule dwc_resume_lift_fence_inv[OF dwc_resume_step.hyps(1)
          dwc_resume_step.prems(1)])
  have cls': "\<forall>f. DWC_Escape f \<notin> set as \<and> DWC_Fenced f \<notin> set as"
    using dwc_resume_step.prems(2) by simp
  show ?case
    using dwc_resume_step.IH[OF inv' cls']
          dwc_resume_lift_wire_same[OF dwc_resume_step.hyps(1)]
    by simp
next
  case (dwc_arrive_step t i t' as t'')
  have inv': "dwc_fence_inv t'"
    by (rule dwc_arrive_fence_inv[OF dwc_arrive_step.hyps(1)
          dwc_arrive_step.prems(1)])
  have cls': "\<forall>f. DWC_Escape f \<notin> set as \<and> DWC_Fenced f \<notin> set as"
    using dwc_arrive_step.prems(2) by simp
  have ih: "\<forall>x \<in> set (dwc_accepted t'').
              x \<in> set (dwc_accepted t') \<or> dwc_fence t' \<le> e_epoch x"
    by (rule dwc_arrive_step.IH[OF inv' cls'])
  have fn: "dwc_fence t' = dwc_fence t"
    by (rule dwc_arrive_fence_same[OF dwc_arrive_step.hyps(1)])
  show ?case
  proof
    fix x assume "x \<in> set (dwc_accepted t'')"
    then have "x \<in> set (dwc_accepted t') \<or> dwc_fence t \<le> e_epoch x"
      using ih fn by auto
    moreover have "x \<in> set (dwc_accepted t')
        \<Longrightarrow> x \<in> set (dwc_accepted t) \<or> dwc_fence t \<le> e_epoch x"
      using arrive_accept_respects_fence[OF dwc_arrive_step.hyps(1)] by auto
    ultimately show "x \<in> set (dwc_accepted t) \<or> dwc_fence t \<le> e_epoch x"
      by blast
  qed
next
  case (dwc_lose_step t i t' as t'')
  have inv': "dwc_fence_inv t'"
    by (rule dwc_lose_fence_inv[OF dwc_lose_step.hyps(1)
          dwc_lose_step.prems(1)])
  have cls': "\<forall>f. DWC_Escape f \<notin> set as \<and> DWC_Fenced f \<notin> set as"
    using dwc_lose_step.prems(2) by simp
  show ?case
    using dwc_lose_step.IH[OF inv' cls']
          dwc_lose_accepted_same[OF dwc_lose_step.hyps(1)]
          dwc_lose_fence_same[OF dwc_lose_step.hyps(1)]
    by simp
next
  case (dwc_escape_step f t t' as t'')
  have "DWC_Escape f \<in> set (DWC_Escape f # as)" by simp
  then have False using dwc_escape_step.prems(2) by blast
  then show ?case ..
next
  case (dwc_fenced_step f t t' as t'')
  have "DWC_Fenced f \<in> set (DWC_Fenced f # as)" by simp
  then have False using dwc_fenced_step.prems(2) by blast
  then show ?case ..
qed

section \<open>The status-indexed fence bound (gate amendment MF-6)\<close>

text \<open>
  The ADDITIVE companion to the pinned invariant, strictly stronger on
  its fence half and NOT derivable from it: at Running or Crashed
  states the fence never exceeds the CURRENT epoch (only Recovered
  states --- the reconcile-to-resume window --- may carry the successor
  fence).  Full-space inductive: the fenced composite fires from
  Crashed where the fence is at most the epoch and sets the successor
  at Recovered; Resume restores the bound at Running by bumping the
  epoch; the bare landed @{text Recover} label reaches Recovered
  without any re-drive and keeps the fence at most the epoch.  Its
  payoff is the born-acceptable sanity fact below: ordinary publishes
  stamp the current epoch at Running, so a fresh send always clears the
  fence of its own generation --- the fence rejects only SUPERSEDED
  generations, never live work.
\<close>

definition dwc_fence_status_bound :: "('k, 'v) dwc_state \<Rightarrow> bool" where
  "dwc_fence_status_bound t \<longleftrightarrow>
     (if exec_status (dwe_core (dwc_inner t)) = Recovered
      then dwc_fence t \<le> Suc (dwe_epoch (dwc_inner t))
      else dwc_fence t \<le> dwe_epoch (dwc_inner t))"

lemma dwc_fence_status_bound_fence_le_Suc:
  assumes "dwc_fence_status_bound t"
  shows "dwc_fence t \<le> Suc (dwe_epoch (dwc_inner t))"
  using assms unfolding dwc_fence_status_bound_def
  by (cases "exec_status (dwe_core (dwc_inner t)) = Recovered") auto

lemma dwc_step_fence_status_bound:
  assumes step: "dwc_step t a t'"
      and inv: "dwc_fence_status_bound t"
  shows "dwc_fence_status_bound t'"
proof -
  have core: "dw_exec_step (dwe_core (dwc_inner t)) a (dwe_core (dwc_inner t'))"
    by (rule dwe_step_core[OF dwc_step_inner[OF step]])
  have ep: "dwe_epoch (dwc_inner t') = dwe_epoch (dwc_inner t)"
    by (rule dwe_step_epoch_const[OF dwc_step_inner[OF step]])
  have fn: "dwc_fence t' = dwc_fence t"
    by (rule dwc_step_fence_same[OF step])
  show ?thesis
  proof (cases "exec_status (dwe_core (dwc_inner t')) = Recovered")
    case True
    have "dwc_fence t \<le> Suc (dwe_epoch (dwc_inner t))"
      by (rule dwc_fence_status_bound_fence_le_Suc[OF inv])
    then show ?thesis
      unfolding dwc_fence_status_bound_def using True ep fn by simp
  next
    case False
    have pre: "exec_status (dwe_core (dwc_inner t)) \<noteq> Recovered"
      using recovered_stays_recovered[OF core] False by blast
    then have "dwc_fence t \<le> dwe_epoch (dwc_inner t)"
      using inv unfolding dwc_fence_status_bound_def by simp
    then show ?thesis
      unfolding dwc_fence_status_bound_def using False ep fn by simp
  qed
qed

lemma dwc_arrive_fence_status_bound:
  assumes step: "dwc_arrive t i t'"
      and inv: "dwc_fence_status_bound t"
  shows "dwc_fence_status_bound t'"
  using inv dwc_arrive_inner_stutter[OF step] dwc_arrive_fence_same[OF step]
  unfolding dwc_fence_status_bound_def by simp

lemma dwc_lose_fence_status_bound:
  assumes step: "dwc_lose t i t'"
      and inv: "dwc_fence_status_bound t"
  shows "dwc_fence_status_bound t'"
  using inv dwc_lose_inner_stutter[OF step] dwc_lose_fence_same[OF step]
  unfolding dwc_fence_status_bound_def by simp

lemma dwc_resume_lift_fence_status_bound:
  assumes step: "dwc_resume_lift t t'"
      and inv: "dwc_fence_status_bound t"
  shows "dwc_fence_status_bound t'"
proof -
  have res: "dwe_resume (dwc_inner t) (dwc_inner t')"
    by (rule dwc_resume_lift_inner[OF step])
  have pre_rec: "exec_status (dwe_core (dwc_inner t)) = Recovered"
    using res by (simp add: dwe_resume_def)
  have post: "exec_status (dwe_core (dwc_inner t')) = Running"
    using res by (simp add: dwe_resume_def)
  have ep: "dwe_epoch (dwc_inner t') = Suc (dwe_epoch (dwc_inner t))"
    by (rule dwe_resume_epoch_Suc[OF res])
  have "dwc_fence t \<le> Suc (dwe_epoch (dwc_inner t))"
    using inv pre_rec unfolding dwc_fence_status_bound_def by simp
  then show ?thesis
    unfolding dwc_fence_status_bound_def
    using post ep dwc_resume_lift_wire_same[OF step] by simp
qed

lemma dwc_reconcile_send_fence_status_bound:
  assumes step: "dwc_reconcile_send m t f t'"
      and inv: "dwc_fence_status_bound t"
  shows "dwc_fence_status_bound t'"
proof -
  have rec: "emitting_reconcile m (dwc_inner t) f (dwc_inner t')"
    by (rule dwc_reconcile_send_inner[OF step])
  have pre_crashed: "\<exists>c. exec_status (dwe_core (dwc_inner t)) = Crashed c"
    using rec by (simp add: emitting_reconcile_def)
  have post: "exec_status (dwe_core (dwc_inner t')) = Recovered"
    using rec by (auto simp: emitting_reconcile_def)
  have ep: "dwe_epoch (dwc_inner t') = dwe_epoch (dwc_inner t)"
    by (rule emitting_reconcile_epoch_const[OF rec])
  have "dwc_fence t \<le> dwe_epoch (dwc_inner t)"
    using inv pre_crashed unfolding dwc_fence_status_bound_def by auto
  then show ?thesis
    unfolding dwc_fence_status_bound_def
    using post ep dwc_reconcile_send_fence_same[OF step] by simp
qed

lemma dwc_fenced_redrive_fence_status_bound:
  assumes step: "dwc_fenced_redrive f t t'"
      and inv: "dwc_fence_status_bound t"
  shows "dwc_fence_status_bound t'"
  unfolding dwc_fence_status_bound_def
  using dwc_fenced_redrive_components(3)[OF step]
        dwc_fenced_redrive_components(4)[OF step]
        dwc_fenced_redrive_components(7)[OF step]
  by simp

lemma dwc_escape_redrive_fence_status_bound:
  assumes step: "dwc_escape_redrive f t t'"
      and inv: "dwc_fence_status_bound t"
  shows "dwc_fence_status_bound t'"
proof -
  have pre_crashed: "\<exists>c. exec_status (dwe_core (dwc_inner t)) = Crashed c"
    using step by (simp add: dwc_escape_redrive_def)
  have "dwc_fence t \<le> dwe_epoch (dwc_inner t)"
    using inv pre_crashed unfolding dwc_fence_status_bound_def by auto
  then show ?thesis
    unfolding dwc_fence_status_bound_def
    using dwc_escape_redrive_components(3)[OF step]
          dwc_escape_redrive_components(4)[OF step]
          dwc_escape_redrive_components(7)[OF step]
    by simp
qed

lemma dwc_trace_fence_status_bound:
  assumes "dwc_temporal_trace t xs t'"
      and "dwc_fence_status_bound t"
  shows "dwc_fence_status_bound t'"
  using assms
proof (induction rule: dwc_temporal_trace.induct)
  case (dwc_refl t)
  then show ?case by simp
next
  case (dwc_label_step t a t' as t'')
  then show ?case using dwc_step_fence_status_bound by blast
next
  case (dwc_reconcile_step m t f t' as t'')
  then show ?case using dwc_reconcile_send_fence_status_bound by blast
next
  case (dwc_resume_step t t' as t'')
  then show ?case using dwc_resume_lift_fence_status_bound by blast
next
  case (dwc_arrive_step t i t' as t'')
  then show ?case using dwc_arrive_fence_status_bound by blast
next
  case (dwc_lose_step t i t' as t'')
  then show ?case using dwc_lose_fence_status_bound by blast
next
  case (dwc_escape_step f t t' as t'')
  then show ?case using dwc_escape_redrive_fence_status_bound by blast
next
  case (dwc_fenced_step f t t' as t'')
  then show ?case using dwc_fenced_redrive_fence_status_bound by blast
qed

theorem dwc_reachable_fence_status_bound:
  assumes "dwc_reachable t"
  shows "dwc_fence_status_bound t"
proof -
  obtain xs where "dwc_temporal_trace (dwc_init Map.empty {0, 1} ec2) xs t"
    using assms unfolding dwc_reachable_def by blast
  moreover have "dwc_fence_status_bound (dwc_init Map.empty {0, 1} ec2)"
    by (simp add: dwc_fence_status_bound_def dwc_init_def dwe_init_def
                  initial_exec_state_def)
  ultimately show ?thesis using dwc_trace_fence_status_bound by blast
qed

corollary publish_born_acceptable:
  assumes reach: "dwc_reachable t"
      and run: "exec_status (dwe_core (dwc_inner t)) = Running"
  shows "dwc_fence t \<le> dwe_epoch (dwc_inner t)
       \<and> dwc_fence t \<le> e_epoch (dwc_stamp t p)"
proof -
  have "dwc_fence t \<le> dwe_epoch (dwc_inner t)"
    using dwc_reachable_fence_status_bound[OF reach] run
    unfolding dwc_fence_status_bound_def by simp
  then show ?thesis by simp
qed

section \<open>The accepted-writes inventory\<close>

text \<open>
  The publish atom, anchored by construction (fold-in (b) of the wave
  design): the accepted record lives in the sink's failure domain ---
  no application or store rule writes it; it changes ONLY by the sink's
  own acceptance act (@{text arrive_accept}: one entry, the arrived
  one) or by the two disclosed atomic re-drive composites (the stamped
  delta batch); and it survives producer crashes untouched
  (@{thm [source] dwc_crash_wire_survives}).  "The system's own durable
  record" of delivery is exactly this field --- recovery reads it and
  nothing else about delivery.
\<close>

theorem accepted_writes_inventory:
  "(dwc_step t a t' \<longrightarrow> dwc_accepted t' = dwc_accepted t)
 \<and> (dwc_reconcile_send m t f t' \<longrightarrow> dwc_accepted t' = dwc_accepted t)
 \<and> (dwc_resume_lift t t' \<longrightarrow> dwc_accepted t' = dwc_accepted t)
 \<and> (dwc_lose t i t' \<longrightarrow> dwc_accepted t' = dwc_accepted t)
 \<and> (dwc_arrive t i t' \<longrightarrow>
      dwc_accepted t' = dwc_accepted t
    \<or> dwc_accepted t' = dwc_accepted t @ [dwc_channel t ! i])
 \<and> (dwc_escape_redrive f t t' \<longrightarrow>
      dwc_accepted t' = dwc_accepted t @ map (dwc_stamp t) (dwc_sink_delta f t))
 \<and> (dwc_fenced_redrive f t t' \<longrightarrow>
      dwc_accepted t' = dwc_accepted t @ map (dwc_stamp t) (dwc_sink_delta f t))"
proof (intro conjI impI)
  assume "dwc_step t a t'"
  then show "dwc_accepted t' = dwc_accepted t"
    by (rule dwc_step_accepted_same)
next
  assume "dwc_reconcile_send m t f t'"
  then show "dwc_accepted t' = dwc_accepted t"
    by (rule dwc_reconcile_send_accepted_same)
next
  assume "dwc_resume_lift t t'"
  then show "dwc_accepted t' = dwc_accepted t"
    using dwc_resume_lift_wire_same by blast
next
  assume "dwc_lose t i t'"
  then show "dwc_accepted t' = dwc_accepted t"
    by (rule dwc_lose_accepted_same)
next
  assume "dwc_arrive t i t'"
  then show "dwc_accepted t' = dwc_accepted t
           \<or> dwc_accepted t' = dwc_accepted t @ [dwc_channel t ! i]"
    using arrive_accept_respects_fence by blast
next
  assume "dwc_escape_redrive f t t'"
  then show "dwc_accepted t' = dwc_accepted t
               @ map (dwc_stamp t) (dwc_sink_delta f t)"
    by (rule dwc_escape_redrive_components(2))
next
  assume "dwc_fenced_redrive f t t'"
  then show "dwc_accepted t' = dwc_accepted t
               @ map (dwc_stamp t) (dwc_sink_delta f t)"
    by (rule dwc_fenced_redrive_components(2))
qed

end
