(*  Title:       Dual_Write_Effect_Zombie.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    THE ZOMBIE: the negative payload of the D-091 channel/fencing wave
    (ladder section 33) --- an additive post-freeze slice under the
    freeze's own protocol (no landed statement, proof, definition,
    name, import, or session-DAG change), the second slice of the wave,
    on top of the channel variant machine of ladder section 32.

    THE DEFEAT, SAID HONESTLY.  The landed sink-reading escape (B1) is
    correct on its own machine: the landed model grants recovery a
    silent free premise --- the recovery-time sink read is STABLE for
    every fire that will ever arrive, because "sent" and "received"
    are one atomic event there.  The channel variant revokes exactly
    that premise and nothing else.  This theory exhibits the designed
    zombie run: a publish goes in flight, the producer crashes, the
    wire SURVIVES the crash (dwc_crash_wire_survives, slice 1), the
    honest escape reads the TRUE durable accepted record and re-drives
    exactly the missing effect --- state-measurably exactly-once at its
    own result --- and then the superseded generation's in-flight copy
    arrives from the surviving channel at fence zero: the accepted
    record now carries the payload TWICE, with every entry still
    justified.  The escape did everything right against the record it
    read; the wire alone defeats it.  Duplication is orthogonal to
    justification, the landed dilemma is untouched, and the defeat
    REINFORCES the landed headline a fortiori: reading the sink is
    necessary (landed) and, on this machine, no longer sufficient.

    ROBUSTNESS TO THE DISCLOSED BOUNDARY.  The one new boundary of the
    wave (contracts row 11, the atomic composite with synchronous
    acceptance) is leaned on ONLY by the fenced positive results
    (slice 3).  The defeat below uses the UNFENCED sibling
    dwc_escape_redrive and is robust to the boundary: splitting the
    composite only ADDS behaviors to the run set, and the zombie
    arrival needs none of the idealization --- it is an ordinary
    fenced-arrive step at the never-raised fence zero.

    THE SEPARATION.  The zombie end state is not a re-dressed landed
    state: its accepted record carries the epoch signature [0, 0, 1, 0]
    --- an arrival-order signature --- while every landed cyclic
    reachable ledger has a SORTED epoch sequence (the cited landed
    completeness invariant).  So the hazard state's observable record
    lies outside the instant-delivery embedded fragment AND outside
    every landed reachable ledger: new behavior, machine-checked.

    THE CALIBRATION.  The defeat consumes read-STABILITY, not
    read-completeness: a straggler that lands BEFORE the recovery
    reads is harmless (crashed_arrival_benign --- the arrival fires
    while the producer is still Crashed, exercising the wire-outlives-
    the-process design choice, and the escape's delta is then empty).
    The hazard is arrival AFTER the read, nothing weaker.

    THE CONTROL.  The crash-survives-wire design choice is witnessed
    LOAD-BEARING by a wipe twin: a twin trace relation identical to
    the channel machine's except that its Crash rule CLEARS the
    channel (dwc_wipe_crash --- the wire dies with the process).  On
    the twin, the same action schedule runs the same recovery --- the
    escape re-drives the same missing effect --- but the zombie
    arrival has no carrier (the arrive rule needs an in-range index on
    an empty wire), and the run stays exactly-once.  Same labels, same
    recovery rule, opposite verdict, one rule-body difference: the
    biting-control discipline of the house.  The control is a
    SCHEDULE-level witness, deliberately not a machine-wide twin
    safety law --- machine-wide accepted-distinctness is false on the
    twin too, since the application may legally duplicate itself
    without any crash.

    IMPORTS: Dual_Write_Effect_Channel (the variant machine, its
    intro-equation kit, and the fence package) and
    Dual_Write_Effect_Completeness (cyclic-lane only; solely for the
    cited landed epoch-sortedness invariant
    dwe_reachable_ledger_epochs_sorted that carries the separation
    witness).  The terminal branch enters no cone of this theory.

    PROVENANCE: owner decision D-091; the channel-wave design gate
    (paper/dual_write/theory_backlog/channel_wave/CHANNEL_WAVE_DESIGN.md,
    ratified COHERENT-GO with amendments MF-1..MF-10 by
    channel_wave/GATE_REPORT.md, 2026-07-07).  This slice executes the
    design section 4.1/4.2/4.3/4.11 content with gate amendments MF-1
    (the pinned wipe-twin action list), MF-2 (the fresh event constant
    ev3 --- e3 is a Discipline constant and Discipline IS in this
    import cone), and MF-3 (witness-kit provenance labels) applied.

    In-source ML oracle gates are STRIPPED at landing: oracle-freedom
    is certified by scratch-side per-slice gate sessions with
    confirmed-biting negative controls, kept outside landed sources.
*)

theory Dual_Write_Effect_Zombie
  imports Dual_Write_Effect_Channel Dual_Write_Effect_Completeness
begin

section \<open>The witness kit and the designed states\<close>

text \<open>
  Witness-kit provenance (gate amendment MF-3): the coordinates
  @{const ec1}, @{const ec2}, @{const ec3} and the @{thm [source]
  ec_defs} bundle are LAYER-0 constants (the shared coordinate
  theory); the state constructors @{const mkC} / @{const mkT} and the
  committed business events @{const e1} / @{const e2} are the cyclic
  machine's witness kit.  This theory adds ONE new event constant and
  ONE state builder of its own.

  The fresh name (gate amendment MF-2): the third business event is
  @{text ev3}, NOT @{text e3} --- @{text e3} is defined by the
  discipline theory, which IS in this import cone (through the
  exactly-once theory), so a plain @{text e3} here would silently
  denote the discipline's constant @{term "Insert 2 3"}.  The zombie
  run's third event is a fresh key-0 insert.
\<close>

definition ev3 :: "(nat, nat) source_event" where "ev3 = Insert 0 3"

definition mkZ
  :: "(nat, nat) dwe_state \<Rightarrow> (nat, nat) emission list
      \<Rightarrow> (nat, nat) emission list \<Rightarrow> nat \<Rightarrow> (nat, nat) dwc_state"
where
  "mkZ i ch acc fn =
     \<lparr> dwc_inner = i, dwc_channel = ch, dwc_accepted = acc, dwc_fence = fn \<rparr>"

lemma mkZ_inner [simp]: "dwc_inner (mkZ i ch acc fn) = i"
  by (simp add: mkZ_def)

lemma mkZ_channel [simp]: "dwc_channel (mkZ i ch acc fn) = ch"
  by (simp add: mkZ_def)

lemma mkZ_accepted [simp]: "dwc_accepted (mkZ i ch acc fn) = acc"
  by (simp add: mkZ_def)

lemma mkZ_fence [simp]: "dwc_fence (mkZ i ch acc fn) = fn"
  by (simp add: mkZ_def)

text \<open>Three-event committed histories are wellformed --- derived from
  the landed pair helper through the landed core append lemma, at the
  concrete chain @{const ec1}, @{const ec2}, @{const ec3}.  The name
  carries the @{const ev3} suffix because the discipline theory (in
  this import cone) already owns a triple helper at ITS third event;
  a fresh name keeps both citable unqualified.\<close>

lemma wfh_triple_ev3:
  "wellformed_src_history [(ec1, e1), (ec2, e2), (ec3, ev3)]"
proof -
  have "wellformed_src_history ([(ec1, e1), (ec2, e2)] @ [(ec3, ev3)])"
    by (rule wellformed_src_history_append_one[OF wfh_pair])
       (simp add: history_can_append_def ec_defs)
  then show ?thesis by simp
qed

subsection \<open>The inner states of the zombie run\<close>

text \<open>
  The zombie run's inner (cyclic wrapper) states.  Its first six inner
  states ARE the landed loaded-window chain @{const W0} ...
  @{const W5}; the run then delivers the second publish before the
  crash (the landed chain crashed with that delivery still pending),
  so the remaining inner states are new closed literals: the crash,
  the escape's heal-and-append result, the resume into epoch one, and
  the epoch-one publish of the third event.
\<close>

definition zi7 :: "(nat, nat) dwe_state" where
  "zi7 = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)]
                [(ec1, e1), (ec2, e2)] {} Running)
             [(1, 0, ec1, e1), (2, 0, ec2, e2)] 0"

definition zi8 :: "(nat, nat) dwe_state" where
  "zi8 = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)]
                [(ec1, e1), (ec2, e2)] {} (Crashed ec2))
             [(1, 0, ec1, e1), (2, 0, ec2, e2)] 0"

definition zi9 :: "(nat, nat) dwe_state" where
  "zi9 = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)]
                [(ec1, e1), (ec2, e2)] {} Recovered)
             [(1, 0, ec1, e1), (2, 0, ec2, e2), (2, 0, ec2, e2)] 0"

definition zi10 :: "(nat, nat) dwe_state" where
  "zi10 = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)]
                 [(ec1, e1), (ec2, e2)] {} Running)
              [(1, 0, ec1, e1), (2, 0, ec2, e2), (2, 0, ec2, e2)] 1"

definition zi11 :: "(nat, nat) dwe_state" where
  "zi11 = mkT (mkC [(ec1, e1), (ec2, e2), (ec3, ev3)] [(ec1, e1), (ec2, e2)]
                 [(ec1, e1), (ec2, e2)] {} Running)
              [(1, 0, ec1, e1), (2, 0, ec2, e2), (2, 0, ec2, e2)] 1"

definition zi12 :: "(nat, nat) dwe_state" where
  "zi12 = mkT (mkC [(ec1, e1), (ec2, e2), (ec3, ev3)] [(ec1, e1), (ec2, e2)]
                 [(ec1, e1), (ec2, e2), (ec3, ev3)] {(ec3, ev3)} Running)
              [(1, 0, ec1, e1), (2, 0, ec2, e2), (2, 0, ec2, e2)] 1"

definition zi13 :: "(nat, nat) dwe_state" where
  "zi13 = mkT (mkC [(ec1, e1), (ec2, e2), (ec3, ev3)]
                 [(ec1, e1), (ec2, e2), (ec3, ev3)]
                 [(ec1, e1), (ec2, e2), (ec3, ev3)] {} Running)
              [(1, 0, ec1, e1), (2, 0, ec2, e2), (2, 0, ec2, e2),
               (3, 1, ec3, ev3)] 1"

text \<open>The calibration branch's inner states: the escape fired at a
  state whose in-flight copy had ALREADY arrived appends nothing (its
  delta is empty), then resumes.\<close>

definition bi10 :: "(nat, nat) dwe_state" where
  "bi10 = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)]
                 [(ec1, e1), (ec2, e2)] {} Recovered)
              [(1, 0, ec1, e1), (2, 0, ec2, e2)] 0"

definition bif :: "(nat, nat) dwe_state" where
  "bif = mkT (mkC [(ec1, e1), (ec2, e2)] [(ec1, e1), (ec2, e2)]
                [(ec1, e1), (ec2, e2)] {} Running)
             [(1, 0, ec1, e1), (2, 0, ec2, e2)] 1"

subsection \<open>The zombie run's channel states\<close>

text \<open>
  The designed zombie run, state by state (the z-chain of the wave
  design, section 4.1).  Reading of the schedule: commit and deliver
  event one, its arrival is accepted at fence zero; commit and publish
  event two --- the emission @{term "(2, 0, ec2, e2)"} goes IN FLIGHT;
  crash --- the wire and the accepted record SURVIVE; the honest
  escape reads the accepted record, computes the delta
  @{term "[(ec2, e2)]"} (exactly the missing effect), re-drives it
  synchronously, and is exactly-once at its own result; Resume opens
  epoch one; the application commits and publishes a third event; the
  fresh epoch-one emission arrives first (free reordering: pop by
  index); THEN the superseded generation's in-flight copy arrives at
  the never-raised fence zero --- the ZOMBIE --- and the accepted
  record carries the payload @{term "(ec2, e2)"} twice.
\<close>

definition z0 :: "(nat, nat) dwc_state" where "z0 = mkZ W0 [] [] 0"

definition z1 :: "(nat, nat) dwc_state" where "z1 = mkZ W1 [] [] 0"

definition z2 :: "(nat, nat) dwc_state" where "z2 = mkZ W2 [] [] 0"

definition z3 :: "(nat, nat) dwc_state" where
  "z3 = mkZ W3 [(1, 0, ec1, e1)] [] 0"

definition z4 :: "(nat, nat) dwc_state" where
  "z4 = mkZ W3 [] [(1, 0, ec1, e1)] 0"

definition z5 :: "(nat, nat) dwc_state" where
  "z5 = mkZ W4 [] [(1, 0, ec1, e1)] 0"

definition z6 :: "(nat, nat) dwc_state" where
  "z6 = mkZ W5 [] [(1, 0, ec1, e1)] 0"

definition z7 :: "(nat, nat) dwc_state" where
  "z7 = mkZ zi7 [(2, 0, ec2, e2)] [(1, 0, ec1, e1)] 0"

definition z8 :: "(nat, nat) dwc_state" where
  "z8 = mkZ zi8 [(2, 0, ec2, e2)] [(1, 0, ec1, e1)] 0"

definition z9 :: "(nat, nat) dwc_state" where
  "z9 = mkZ zi9 [(2, 0, ec2, e2)] [(1, 0, ec1, e1), (2, 0, ec2, e2)] 0"

definition z10 :: "(nat, nat) dwc_state" where
  "z10 = mkZ zi10 [(2, 0, ec2, e2)] [(1, 0, ec1, e1), (2, 0, ec2, e2)] 0"

definition z11 :: "(nat, nat) dwc_state" where
  "z11 = mkZ zi11 [(2, 0, ec2, e2)] [(1, 0, ec1, e1), (2, 0, ec2, e2)] 0"

definition z12 :: "(nat, nat) dwc_state" where
  "z12 = mkZ zi12 [(2, 0, ec2, e2)] [(1, 0, ec1, e1), (2, 0, ec2, e2)] 0"

definition z13 :: "(nat, nat) dwc_state" where
  "z13 = mkZ zi13 [(2, 0, ec2, e2), (3, 1, ec3, ev3)]
           [(1, 0, ec1, e1), (2, 0, ec2, e2)] 0"

definition z14 :: "(nat, nat) dwc_state" where
  "z14 = mkZ zi13 [(2, 0, ec2, e2)]
           [(1, 0, ec1, e1), (2, 0, ec2, e2), (3, 1, ec3, ev3)] 0"

definition z15 :: "(nat, nat) dwc_state" where
  "z15 = mkZ zi13 []
           [(1, 0, ec1, e1), (2, 0, ec2, e2), (3, 1, ec3, ev3),
            (2, 0, ec2, e2)] 0"

text \<open>The calibration branch: from the crash state, the in-flight copy
  arrives WHILE the producer is still Crashed, then the escape fires
  (empty delta) and the run resumes.\<close>

definition b9 :: "(nat, nat) dwc_state" where
  "b9 = mkZ zi8 [] [(1, 0, ec1, e1), (2, 0, ec2, e2)] 0"

definition b10 :: "(nat, nat) dwc_state" where
  "b10 = mkZ bi10 [] [(1, 0, ec1, e1), (2, 0, ec2, e2)] 0"

definition bf :: "(nat, nat) dwc_state" where
  "bf = mkZ bif [] [(1, 0, ec1, e1), (2, 0, ec2, e2)] 0"

text \<open>The wipe-twin's states (the w-chain; its first eight states are
  the z-chain's own @{const z0} ... @{const z7}): the twin crash
  CLEARS the channel, the same escape re-drives the same missing
  effect, the same third event publishes into the wiped wire, and its
  single arrival is the only arrival the twin admits.\<close>

definition w8 :: "(nat, nat) dwc_state" where
  "w8 = mkZ zi8 [] [(1, 0, ec1, e1)] 0"

definition w9 :: "(nat, nat) dwc_state" where
  "w9 = mkZ zi9 [] [(1, 0, ec1, e1), (2, 0, ec2, e2)] 0"

definition w10 :: "(nat, nat) dwc_state" where
  "w10 = mkZ zi10 [] [(1, 0, ec1, e1), (2, 0, ec2, e2)] 0"

definition w11 :: "(nat, nat) dwc_state" where
  "w11 = mkZ zi11 [] [(1, 0, ec1, e1), (2, 0, ec2, e2)] 0"

definition w12 :: "(nat, nat) dwc_state" where
  "w12 = mkZ zi12 [] [(1, 0, ec1, e1), (2, 0, ec2, e2)] 0"

definition w13 :: "(nat, nat) dwc_state" where
  "w13 = mkZ zi13 [(3, 1, ec3, ev3)] [(1, 0, ec1, e1), (2, 0, ec2, e2)] 0"

definition w_fin :: "(nat, nat) dwc_state" where
  "w_fin = mkZ zi13 []
             [(1, 0, ec1, e1), (2, 0, ec2, e2), (3, 1, ec3, ev3)] 0"

lemma z0_init: "z0 = dwc_init Map.empty {0, 1} ec2"
  by (simp add: z0_def mkZ_def dwc_init_def W0_init)

section \<open>Wellformedness and admissibility guards along the chains\<close>

text \<open>The landed guards @{thm [source] wf_W0} ... @{thm [source] wf_W5}
  and @{thm [source] g_W0_src1} ... @{thm [source] g_W4_enq2} cover the
  shared prefix; the new inner states need their own, in the landed
  discharge style.\<close>

lemma wf_zi7: "wellformed_exec_state (dwe_core zi7)"
  by (simp add: zi7_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_pair)

lemma wf_zi10: "wellformed_exec_state (dwe_core zi10)"
  by (simp add: zi10_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_pair)

lemma wf_zi11: "wellformed_exec_state (dwe_core zi11)"
  by (simp add: zi11_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_pair
                wfh_triple_ev3)

lemma wf_zi12: "wellformed_exec_state (dwe_core zi12)"
  by (simp add: zi12_def mkT_def mkC_def ws_defs wf_hist_Nil wfh_pair
                wfh_triple_ev3)

lemma g_W5_down2: "exec_label_preserves_history_wf (dwe_core W5)
                     (DoDownstream ec2 e2)"
  by (simp add: W5_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_zi7_crash: "exec_label_preserves_history_wf (dwe_core zi7) (Crash ec2)"
  by (simp add: exec_label_preserves_history_wf_def)

lemma g_zi10_src3: "exec_label_preserves_history_wf (dwe_core zi10)
                      (DoSource ec3 ev3)"
  by (simp add: zi10_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_zi11_enq3: "exec_label_preserves_history_wf (dwe_core zi11)
                      (EnqueueDownstream ec3 ev3)"
  by (simp add: zi11_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

lemma g_zi12_down3: "exec_label_preserves_history_wf (dwe_core zi12)
                       (DoDownstream ec3 ev3)"
  by (simp add: zi12_def mkT_def mkC_def exec_label_preserves_history_wf_def
                history_can_append_def ec_defs)

section \<open>The inner witness steps\<close>

text \<open>The inner transitions the two chains share, in the landed
  equation-form intro style: the delivery of event two before the
  crash, the crash itself, the epoch-one resume, and the epoch-one
  commit/enqueue/publish of the third event.\<close>

lemma zi_down2: "dwe_step W5 (DoDownstream ec2 e2) zi7"
proof -
  have c: "dw_exec_step (dwe_core W5) (DoDownstream ec2 e2) (dwe_core zi7)"
    by (rule do_downstreamI) (simp_all add: W5_def zi7_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_publish_emitI[OF c])
       (simp add: W5_def zi7_def mkT_def mkC_def eval_nat_numeral)
qed

lemma zi_crash: "dwe_step zi7 (Crash ec2) zi8"
proof -
  have c: "dw_exec_step (dwe_core zi7) (Crash ec2) (dwe_core zi8)"
    by (rule crashI) (simp_all add: zi7_def zi8_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: zi7_def zi8_def mkT_def)
qed

lemma zi_resume: "dwe_resume zi9 zi10"
  by (simp add: dwe_resume_def zi9_def zi10_def mkT_def mkC_def
                eval_nat_numeral)

lemma zi_src3: "dwe_step zi10 (DoSource ec3 ev3) zi11"
proof -
  have c: "dw_exec_step (dwe_core zi10) (DoSource ec3 ev3) (dwe_core zi11)"
    by (rule do_sourceI) (simp_all add: zi10_def zi11_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: zi10_def zi11_def mkT_def)
qed

lemma zi_enq3: "dwe_step zi11 (EnqueueDownstream ec3 ev3) zi12"
proof -
  have c: "dw_exec_step (dwe_core zi11) (EnqueueDownstream ec3 ev3)
             (dwe_core zi12)"
    by (rule enqueue_downstreamI)
       (simp_all add: zi11_def zi12_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_lift_nonpubI[OF c]) (simp_all add: zi11_def zi12_def mkT_def)
qed

lemma zi_down3: "dwe_step zi12 (DoDownstream ec3 ev3) zi13"
proof -
  have c: "dw_exec_step (dwe_core zi12) (DoDownstream ec3 ev3) (dwe_core zi13)"
    by (rule do_downstreamI) (simp_all add: zi12_def zi13_def mkT_def mkC_def)
  show ?thesis
    by (rule dwe_publish_emitI[OF c])
       (simp add: zi12_def zi13_def mkT_def mkC_def eval_nat_numeral)
qed

lemma bi_resume: "dwe_resume bi10 bif"
  by (simp add: dwe_resume_def bi10_def bif_def mkT_def mkC_def
                eval_nat_numeral)

section \<open>The zombie run, step by step\<close>

text \<open>Every step of the z-chain is an actual rule application of the
  channel machine --- machine-checked reachability, never an asserted
  state.  The label steps lift the landed inner steps; the publishes
  push their stamped emissions IN FLIGHT; the arrivals pop by index at
  the never-raised fence zero; the escape is the unfenced sink-reading
  composite; Resume is the landed epoch bump.\<close>

lemma zs1: "dwc_step z0 (DoSource ec1 e1) z1"
proof -
  have i: "dwe_step (dwc_inner z0) (DoSource ec1 e1) W1"
    using ws1 by (simp add: z0_def)
  show ?thesis
    by (rule dwc_lift_nonpubI[OF i]) (simp_all add: z0_def z1_def mkZ_def)
qed

lemma zs2: "dwc_step z1 (EnqueueDownstream ec1 e1) z2"
proof -
  have i: "dwe_step (dwc_inner z1) (EnqueueDownstream ec1 e1) W2"
    using ws2 by (simp add: z1_def)
  show ?thesis
    by (rule dwc_lift_nonpubI[OF i]) (simp_all add: z1_def z2_def mkZ_def)
qed

lemma zs3: "dwc_step z2 (DoDownstream ec1 e1) z3"
proof -
  have i: "dwe_step (dwc_inner z2) (DoDownstream ec1 e1) W3"
    using ws3 by (simp add: z2_def)
  show ?thesis
    by (rule dwc_send_pubI[OF i])
       (simp add: z2_def z3_def mkZ_def W2_def mkT_def mkC_def dwc_src_def
                  eval_nat_numeral)
qed

lemma zs4: "dwc_arrive z3 0 z4"
  by (rule dwc_arrive_acceptI) (simp_all add: z3_def z4_def mkZ_def)

lemma zs5: "dwc_step z4 (DoSource ec2 e2) z5"
proof -
  have i: "dwe_step (dwc_inner z4) (DoSource ec2 e2) W4"
    using ws4 by (simp add: z4_def)
  show ?thesis
    by (rule dwc_lift_nonpubI[OF i]) (simp_all add: z4_def z5_def mkZ_def)
qed

lemma zs6: "dwc_step z5 (EnqueueDownstream ec2 e2) z6"
proof -
  have i: "dwe_step (dwc_inner z5) (EnqueueDownstream ec2 e2) W5"
    using ws5 by (simp add: z5_def)
  show ?thesis
    by (rule dwc_lift_nonpubI[OF i]) (simp_all add: z5_def z6_def mkZ_def)
qed

lemma zs7: "dwc_step z6 (DoDownstream ec2 e2) z7"
proof -
  have i: "dwe_step (dwc_inner z6) (DoDownstream ec2 e2) zi7"
    using zi_down2 by (simp add: z6_def)
  show ?thesis
    by (rule dwc_send_pubI[OF i])
       (simp add: z6_def z7_def mkZ_def W5_def mkT_def mkC_def dwc_src_def
                  eval_nat_numeral)
qed

text \<open>The crash: a plain non-publish label lift --- the wire, the
  accepted record, and the fence all SURVIVE (the slice-1 survival
  theorem, exercised here at the designed run).\<close>

lemma zs8: "dwc_step z7 (Crash ec2) z8"
proof -
  have i: "dwe_step (dwc_inner z7) (Crash ec2) zi8"
    using zi_crash by (simp add: z7_def)
  show ?thesis
    by (rule dwc_lift_nonpubI[OF i]) (simp_all add: z7_def z8_def mkZ_def)
qed

text \<open>
  What the recovery reads, computed: the replay at the crash frontier
  is the two committed events; the accepted record holds event one
  only; so the accepted-record delta is EXACTLY the missing effect
  @{term "[(ec2, e2)]"}.  The escape re-drives it, stamped at the
  crash-time epoch --- byte-identical to the in-flight copy on the
  surviving wire, the fact that forces the fence design (slice 3) and
  that the zombie below exploits.
\<close>

lemma z8_delta: "dwc_sink_delta ec2 z8 = [(ec2, e2)]"
  by (simp add: dwc_sink_delta_def dwc_replay_def dwc_src_def dwc_scope_def
                replay_down_hist_def z8_def mkZ_def zi8_def mkT_def mkC_def
                e1_def e2_def ec_defs)

lemma zesc9: "dwc_escape_redrive ec2 z8 z9"
  by (rule dwc_escape_redriveI)
     (simp_all add: z8_def z9_def mkZ_def zi8_def zi9_def mkT_def mkC_def
                    dwc_sink_delta_def dwc_replay_def dwc_src_def
                    dwc_scope_def replay_down_hist_def e1_def e2_def ec_defs
                    eval_nat_numeral)

text \<open>The escape's result is exactly-once at its own frontier,
  state-measurably: the recovery did everything right against the
  record it read.\<close>

lemma z9_eo: "dwc_eo_at ec2 z9"
  by (simp add: dwc_eo_at_def dwc_accepted_unsafe_def
                dwc_accepted_premature_def dwc_accepted_duplicate_def
                dwc_alo_at_def justified_at_def dwc_replay_def dwc_src_def
                dwc_scope_def replay_down_hist_def z9_def mkZ_def zi9_def
                mkT_def mkC_def e1_def e2_def ec_defs eval_nat_numeral)

lemma zres10: "dwc_resume_lift z9 z10"
proof -
  have i: "dwe_resume (dwc_inner z9) zi10"
    using zi_resume by (simp add: z9_def)
  show ?thesis
    by (rule dwc_resume_liftI[OF i]) (simp add: z9_def z10_def mkZ_def)
qed

lemma zs11: "dwc_step z10 (DoSource ec3 ev3) z11"
proof -
  have i: "dwe_step (dwc_inner z10) (DoSource ec3 ev3) zi11"
    using zi_src3 by (simp add: z10_def)
  show ?thesis
    by (rule dwc_lift_nonpubI[OF i]) (simp_all add: z10_def z11_def mkZ_def)
qed

lemma zs12: "dwc_step z11 (EnqueueDownstream ec3 ev3) z12"
proof -
  have i: "dwe_step (dwc_inner z11) (EnqueueDownstream ec3 ev3) zi12"
    using zi_enq3 by (simp add: z11_def)
  show ?thesis
    by (rule dwc_lift_nonpubI[OF i]) (simp_all add: z11_def z12_def mkZ_def)
qed

lemma zs13: "dwc_step z12 (DoDownstream ec3 ev3) z13"
proof -
  have i: "dwe_step (dwc_inner z12) (DoDownstream ec3 ev3) zi13"
    using zi_down3 by (simp add: z12_def)
  show ?thesis
    by (rule dwc_send_pubI[OF i])
       (simp add: z12_def z13_def mkZ_def zi12_def mkT_def mkC_def
                  dwc_src_def eval_nat_numeral)
qed

text \<open>Free reordering on the wire: the FRESH epoch-one emission
  (index one) arrives before the stale epoch-zero straggler.\<close>

lemma zs14: "dwc_arrive z13 1 z14"
  by (rule dwc_arrive_acceptI)
     (simp_all add: z13_def z14_def mkZ_def eval_nat_numeral)

text \<open>THE ZOMBIE ARRIVAL: the superseded generation's in-flight copy
  lands at the never-raised fence zero and is accepted --- an ordinary
  accepting arrive step; nothing exotic fires.\<close>

lemma zs15: "dwc_arrive z14 0 z15"
  by (rule dwc_arrive_acceptI)
     (simp_all add: z14_def z15_def mkZ_def)

section \<open>Reachability of the zombie run\<close>

lemma reach_z0: "dwc_reachable z0"
  unfolding z0_init by (rule dwc_reachable_init)

lemma reach_z1: "dwc_reachable z1"
  by (rule dwc_reachable_label_ext[OF reach_z0 _ _ zs1])
     (simp_all add: z0_def wf_W0 g_W0_src1)

lemma reach_z2: "dwc_reachable z2"
  by (rule dwc_reachable_label_ext[OF reach_z1 _ _ zs2])
     (simp_all add: z1_def wf_W1 g_W1_enq1)

lemma reach_z3: "dwc_reachable z3"
  by (rule dwc_reachable_label_ext[OF reach_z2 _ _ zs3])
     (simp_all add: z2_def wf_W2 g_W2_down1)

lemma reach_z4: "dwc_reachable z4"
  by (rule dwc_reachable_arrive_ext[OF reach_z3 zs4])

lemma reach_z5: "dwc_reachable z5"
  by (rule dwc_reachable_label_ext[OF reach_z4 _ _ zs5])
     (simp_all add: z4_def wf_W3 g_W3_src2)

lemma reach_z6: "dwc_reachable z6"
  by (rule dwc_reachable_label_ext[OF reach_z5 _ _ zs6])
     (simp_all add: z5_def wf_W4 g_W4_enq2)

lemma reach_z7: "dwc_reachable z7"
  by (rule dwc_reachable_label_ext[OF reach_z6 _ _ zs7])
     (simp_all add: z6_def wf_W5 g_W5_down2)

lemma reach_z8: "dwc_reachable z8"
  by (rule dwc_reachable_label_ext[OF reach_z7 _ _ zs8])
     (simp_all add: z7_def wf_zi7 g_zi7_crash)

lemma reach_z9: "dwc_reachable z9"
  by (rule dwc_reachable_escape_ext[OF reach_z8 zesc9])

lemma reach_z10: "dwc_reachable z10"
  by (rule dwc_reachable_resume_ext[OF reach_z9 zres10])

lemma reach_z11: "dwc_reachable z11"
  by (rule dwc_reachable_label_ext[OF reach_z10 _ _ zs11])
     (simp_all add: z10_def wf_zi10 g_zi10_src3)

lemma reach_z12: "dwc_reachable z12"
  by (rule dwc_reachable_label_ext[OF reach_z11 _ _ zs12])
     (simp_all add: z11_def wf_zi11 g_zi11_enq3)

lemma reach_z13: "dwc_reachable z13"
  by (rule dwc_reachable_label_ext[OF reach_z12 _ _ zs13])
     (simp_all add: z12_def wf_zi12 g_zi12_down3)

lemma reach_z14: "dwc_reachable z14"
  by (rule dwc_reachable_arrive_ext[OF reach_z13 zs14])

lemma reach_z15: "dwc_reachable z15"
  by (rule dwc_reachable_arrive_ext[OF reach_z14 zs15])

text \<open>The post-recovery tail as ONE trace fact --- the exact action
  list the defeat theorem pins: everything after the escape's
  exactly-once result is ordinary machine life (Resume, fresh work,
  two arrivals), and it alone converts the correct recovery into a
  duplicated record.\<close>

lemma trace_z9_z15:
  "dwc_temporal_trace z9
     [DWC_Resume, DWC_Label (DoSource ec3 ev3),
      DWC_Label (EnqueueDownstream ec3 ev3),
      DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 1, DWC_Arrive 0] z15"
proof -
  have s6: "dwc_temporal_trace z14 [DWC_Arrive 0] z15"
    by (rule dwc_temporal_trace.dwc_arrive_step[OF zs15
          dwc_temporal_trace.dwc_refl])
  have s5: "dwc_temporal_trace z13 [DWC_Arrive 1, DWC_Arrive 0] z15"
    by (rule dwc_temporal_trace.dwc_arrive_step[OF zs14 s6])
  have s4: "dwc_temporal_trace z12
              [DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 1, DWC_Arrive 0]
              z15"
    by (rule dwc_temporal_trace.dwc_label_step[OF _ _ zs13 s5])
       (simp_all add: z12_def wf_zi12 g_zi12_down3)
  have s3: "dwc_temporal_trace z11
              [DWC_Label (EnqueueDownstream ec3 ev3),
               DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 1, DWC_Arrive 0]
              z15"
    by (rule dwc_temporal_trace.dwc_label_step[OF _ _ zs12 s4])
       (simp_all add: z11_def wf_zi11 g_zi11_enq3)
  have s2: "dwc_temporal_trace z10
              [DWC_Label (DoSource ec3 ev3),
               DWC_Label (EnqueueDownstream ec3 ev3),
               DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 1, DWC_Arrive 0]
              z15"
    by (rule dwc_temporal_trace.dwc_label_step[OF _ _ zs11 s3])
       (simp_all add: z10_def wf_zi10 g_zi10_src3)
  show ?thesis
    by (rule dwc_temporal_trace.dwc_resume_step[OF zres10 s2])
qed

text \<open>The COMPLETE zombie schedule as one trace fact, from the pinned
  init to the hazard state --- the action list the wipe twin below
  re-runs (its first thirteen actions verbatim; the twin's wire then
  carries one entry, so the twin's tail is the single fresh arrival
  and the zombie arrival is unfireable there).\<close>

lemma zombie_run_action_list:
  "dwc_temporal_trace (dwc_init Map.empty {0, 1} ec2)
     [DWC_Label (DoSource ec1 e1), DWC_Label (EnqueueDownstream ec1 e1),
      DWC_Label (DoDownstream ec1 e1), DWC_Arrive 0,
      DWC_Label (DoSource ec2 e2), DWC_Label (EnqueueDownstream ec2 e2),
      DWC_Label (DoDownstream ec2 e2), DWC_Label (Crash ec2),
      DWC_Escape ec2, DWC_Resume,
      DWC_Label (DoSource ec3 ev3), DWC_Label (EnqueueDownstream ec3 ev3),
      DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 1, DWC_Arrive 0] z15"
proof -
  have a9: "dwc_temporal_trace z8
              [DWC_Escape ec2, DWC_Resume, DWC_Label (DoSource ec3 ev3),
               DWC_Label (EnqueueDownstream ec3 ev3),
               DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 1, DWC_Arrive 0]
              z15"
    by (rule dwc_temporal_trace.dwc_escape_step[OF zesc9 trace_z9_z15])
  have a8: "dwc_temporal_trace z7
              (DWC_Label (Crash ec2)
               # [DWC_Escape ec2, DWC_Resume, DWC_Label (DoSource ec3 ev3),
                  DWC_Label (EnqueueDownstream ec3 ev3),
                  DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 1,
                  DWC_Arrive 0])
              z15"
    by (rule dwc_temporal_trace.dwc_label_step[OF _ _ zs8 a9])
       (simp_all add: z7_def wf_zi7 g_zi7_crash)
  have a7: "dwc_temporal_trace z6
              (DWC_Label (DoDownstream ec2 e2) # DWC_Label (Crash ec2)
               # [DWC_Escape ec2, DWC_Resume, DWC_Label (DoSource ec3 ev3),
                  DWC_Label (EnqueueDownstream ec3 ev3),
                  DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 1,
                  DWC_Arrive 0])
              z15"
    by (rule dwc_temporal_trace.dwc_label_step[OF _ _ zs7 a8])
       (simp_all add: z6_def wf_W5 g_W5_down2)
  have a6: "dwc_temporal_trace z5
              (DWC_Label (EnqueueDownstream ec2 e2)
               # DWC_Label (DoDownstream ec2 e2) # DWC_Label (Crash ec2)
               # [DWC_Escape ec2, DWC_Resume, DWC_Label (DoSource ec3 ev3),
                  DWC_Label (EnqueueDownstream ec3 ev3),
                  DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 1,
                  DWC_Arrive 0])
              z15"
    by (rule dwc_temporal_trace.dwc_label_step[OF _ _ zs6 a7])
       (simp_all add: z5_def wf_W4 g_W4_enq2)
  have a5: "dwc_temporal_trace z4
              (DWC_Label (DoSource ec2 e2)
               # DWC_Label (EnqueueDownstream ec2 e2)
               # DWC_Label (DoDownstream ec2 e2) # DWC_Label (Crash ec2)
               # [DWC_Escape ec2, DWC_Resume, DWC_Label (DoSource ec3 ev3),
                  DWC_Label (EnqueueDownstream ec3 ev3),
                  DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 1,
                  DWC_Arrive 0])
              z15"
    by (rule dwc_temporal_trace.dwc_label_step[OF _ _ zs5 a6])
       (simp_all add: z4_def wf_W3 g_W3_src2)
  have a4: "dwc_temporal_trace z3
              (DWC_Arrive 0 # DWC_Label (DoSource ec2 e2)
               # DWC_Label (EnqueueDownstream ec2 e2)
               # DWC_Label (DoDownstream ec2 e2) # DWC_Label (Crash ec2)
               # [DWC_Escape ec2, DWC_Resume, DWC_Label (DoSource ec3 ev3),
                  DWC_Label (EnqueueDownstream ec3 ev3),
                  DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 1,
                  DWC_Arrive 0])
              z15"
    by (rule dwc_temporal_trace.dwc_arrive_step[OF zs4 a5])
  have a3: "dwc_temporal_trace z2
              (DWC_Label (DoDownstream ec1 e1) # DWC_Arrive 0
               # DWC_Label (DoSource ec2 e2)
               # DWC_Label (EnqueueDownstream ec2 e2)
               # DWC_Label (DoDownstream ec2 e2) # DWC_Label (Crash ec2)
               # [DWC_Escape ec2, DWC_Resume, DWC_Label (DoSource ec3 ev3),
                  DWC_Label (EnqueueDownstream ec3 ev3),
                  DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 1,
                  DWC_Arrive 0])
              z15"
    by (rule dwc_temporal_trace.dwc_label_step[OF _ _ zs3 a4])
       (simp_all add: z2_def wf_W2 g_W2_down1)
  have a2: "dwc_temporal_trace z1
              (DWC_Label (EnqueueDownstream ec1 e1)
               # DWC_Label (DoDownstream ec1 e1) # DWC_Arrive 0
               # DWC_Label (DoSource ec2 e2)
               # DWC_Label (EnqueueDownstream ec2 e2)
               # DWC_Label (DoDownstream ec2 e2) # DWC_Label (Crash ec2)
               # [DWC_Escape ec2, DWC_Resume, DWC_Label (DoSource ec3 ev3),
                  DWC_Label (EnqueueDownstream ec3 ev3),
                  DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 1,
                  DWC_Arrive 0])
              z15"
    by (rule dwc_temporal_trace.dwc_label_step[OF _ _ zs2 a3])
       (simp_all add: z1_def wf_W1 g_W1_enq1)
  have a1: "dwc_temporal_trace z0
              (DWC_Label (DoSource ec1 e1)
               # DWC_Label (EnqueueDownstream ec1 e1)
               # DWC_Label (DoDownstream ec1 e1) # DWC_Arrive 0
               # DWC_Label (DoSource ec2 e2)
               # DWC_Label (EnqueueDownstream ec2 e2)
               # DWC_Label (DoDownstream ec2 e2) # DWC_Label (Crash ec2)
               # [DWC_Escape ec2, DWC_Resume, DWC_Label (DoSource ec3 ev3),
                  DWC_Label (EnqueueDownstream ec3 ev3),
                  DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 1,
                  DWC_Arrive 0])
              z15"
    by (rule dwc_temporal_trace.dwc_label_step[OF _ _ zs1 a2])
       (simp_all add: z0_def wf_W0 g_W0_src1)
  show ?thesis using a1 by (simp add: z0_init)
qed

section \<open>N --- the zombie defeats the sink-reading escape\<close>

text \<open>The end-state verdicts, each computed on the closed record.\<close>

lemma z15_duplicate: "dwc_accepted_duplicate z15"
  by (simp add: dwc_accepted_duplicate_def z15_def mkZ_def e1_def e2_def
                ev3_def ec_defs)

lemma z15_count:
  "2 \<le> count_list (map e_payload (dwc_accepted z15)) (ec2, e2)"
  by (simp add: z15_def mkZ_def e1_def e2_def ev3_def ec_defs)

lemma z15_all_justified:
  "\<forall>x \<in> set (dwc_accepted z15). justified_at (dwc_src z15) x"
  by (simp add: z15_def mkZ_def zi13_def mkT_def mkC_def dwc_src_def
                justified_at_def e1_def e2_def ev3_def ec_defs
                eval_nat_numeral)

lemma z15_fence: "dwc_fence z15 = 0"
  by (simp add: z15_def)

text \<open>
  THE DEFEAT THEOREM, named form: a premise-free closed designed run.
  Its nine conjuncts, in order: the end state is reachable on the
  channel machine; the recovery step is the honest unfenced
  sink-reading escape; the delta it computed was EXACTLY the missing
  effect (the read was honest and correct); the escape's result was
  exactly-once at its own frontier (the recovery did everything right,
  state-measurably so); the pinned post-recovery tail is ordinary
  machine life; the end state's accepted record is DUPLICATED; the
  payload of the re-driven effect is carried at least twice; every
  accepted entry is still justified (duplication is orthogonal to
  justification --- the hazard is not a phantom); and the fence was
  never raised --- the zombie walked in at fence zero.

  Honest headline, calibrated: the landed escape's implicit premise
  --- the recovery-time sink read is STABLE for every fire that will
  ever arrive --- is granted free by the landed model (where sending
  and receiving are one atomic event) and revoked here.  The landed
  dilemma and the landed escape theorems are untouched: reading the
  sink remains necessary; on the channel machine it is no longer
  sufficient.
\<close>

theorem zombie_defeats_sink_reading_named:
  "dwc_reachable z15
 \<and> dwc_escape_redrive ec2 z8 z9
 \<and> dwc_sink_delta ec2 z8 = [(ec2, e2)]
 \<and> dwc_eo_at ec2 z9
 \<and> dwc_temporal_trace z9
     [DWC_Resume, DWC_Label (DoSource ec3 ev3),
      DWC_Label (EnqueueDownstream ec3 ev3),
      DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 1, DWC_Arrive 0] z15
 \<and> dwc_accepted_duplicate z15
 \<and> 2 \<le> count_list (map e_payload (dwc_accepted z15)) (ec2, e2)
 \<and> (\<forall>x \<in> set (dwc_accepted z15). justified_at (dwc_src z15) x)
 \<and> dwc_fence z15 = 0"
  by (intro conjI reach_z15 zesc9 z8_delta z9_eo trace_z9_z15 z15_duplicate
            z15_count z15_all_justified z15_fence)

text \<open>The packaged form: the same certificate with the witness states
  existentially bound, in the shape of the landed bridge certificates.\<close>

theorem zombie_defeats_sink_reading:
  "\<exists>t8 t9 t15.
     dwc_reachable t15
   \<and> dwc_escape_redrive ec2 t8 t9
   \<and> dwc_sink_delta ec2 t8 = [(ec2, e2)]
   \<and> dwc_eo_at ec2 t9
   \<and> dwc_temporal_trace t9
       [DWC_Resume, DWC_Label (DoSource ec3 ev3),
        DWC_Label (EnqueueDownstream ec3 ev3),
        DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 1, DWC_Arrive 0] t15
   \<and> dwc_accepted_duplicate t15
   \<and> 2 \<le> count_list (map e_payload (dwc_accepted t15)) (ec2, e2)
   \<and> (\<forall>x \<in> set (dwc_accepted t15). justified_at (dwc_src t15) x)
   \<and> dwc_fence t15 = 0"
  by (rule exI[of _ z8], rule exI[of _ z9], rule exI[of _ z15])
     (rule zombie_defeats_sink_reading_named)

section \<open>The separation witness: no cyclic ledger carries the signature\<close>

text \<open>
  The zombie end state is NEW BEHAVIOR, not a re-dressed landed state.
  The separating observable is the accepted record's epoch sequence:
  the zombie's is @{term "[0, 0, 1, 0] :: nat list"} --- the stale
  epoch-zero straggler landed AFTER an epoch-one acceptance --- which
  is not sorted.  Every landed cyclic reachable state's ledger has a
  SORTED epoch sequence (the cited landed completeness invariant,
  consumed here by citation and never re-proved), and on embedded
  states the accepted record IS the landed ledger.  So no landed
  reachable state embeds to the zombie's record, and no landed
  reachable ledger even equals it: the hazard lives strictly outside
  the instant-delivery fragment.  (The record-level claim is
  deliberately signature-based: a duplicate-carrying accepted record
  CAN equal an embedded one --- the landed machine has its own
  duplicates --- so plain non-membership of the record value would be
  the wrong claim; the epoch signature is the robust one.)
\<close>

theorem zombie_signature_cyclic_unreachable:
  "\<not> sorted (map e_epoch (dwc_accepted z15))
 \<and> (\<forall>t. dwe_reachable t \<longrightarrow> dwc_accepted (dwc_embed t) \<noteq> dwc_accepted z15)
 \<and> (\<nexists>t. dwe_reachable t \<and> dwe_emitted t = dwc_accepted z15)"
proof -
  have sig: "\<not> sorted (map e_epoch (dwc_accepted z15))"
    by (simp add: z15_def mkZ_def)
  have no_ledger: "dwe_emitted t \<noteq> dwc_accepted z15"
    if r: "dwe_reachable t" for t
  proof
    assume eq: "dwe_emitted t = dwc_accepted z15"
    have "sorted (map e_epoch (dwe_emitted t))"
      by (rule dwe_reachable_ledger_epochs_sorted[OF r])
    with eq sig show False by simp
  qed
  have emb: "\<forall>t. dwe_reachable t
               \<longrightarrow> dwc_accepted (dwc_embed t) \<noteq> dwc_accepted z15"
    using no_ledger by simp
  have nex: "\<nexists>t. dwe_reachable t \<and> dwe_emitted t = dwc_accepted z15"
    using no_ledger by blast
  show ?thesis by (intro conjI sig emb nex)
qed

section \<open>The calibration witness: an early arrival is benign\<close>

text \<open>
  Read-STABILITY, not read-completeness.  The same crash state, one
  reordering earlier: the in-flight copy arrives WHILE the producer is
  still Crashed --- the arrive rule carries no status guard on the
  inner; the wire outlives the process --- so the recovery's read then
  SEES the delivery: its delta is empty, it appends nothing, and the
  resumed run is exactly-once with a duplicate-free record.  The
  straggler that lands BEFORE the read is harmless; the defeat above
  is arrival AFTER the read, nothing weaker.  This is also the
  non-vacuity witness for the arrive rule's status-guard freedom.
\<close>

lemma bs9: "dwc_arrive z8 0 b9"
  by (rule dwc_arrive_acceptI) (simp_all add: z8_def b9_def mkZ_def)

lemma b9_delta: "dwc_sink_delta ec2 b9 = []"
  by (simp add: dwc_sink_delta_def dwc_replay_def dwc_src_def dwc_scope_def
                replay_down_hist_def b9_def mkZ_def zi8_def mkT_def mkC_def
                e1_def e2_def ec_defs)

lemma besc10: "dwc_escape_redrive ec2 b9 b10"
  by (rule dwc_escape_redriveI)
     (simp_all add: b9_def b10_def mkZ_def zi8_def bi10_def mkT_def mkC_def
                    dwc_sink_delta_def dwc_replay_def dwc_src_def
                    dwc_scope_def replay_down_hist_def e1_def e2_def ec_defs
                    eval_nat_numeral)

lemma bres_f: "dwc_resume_lift b10 bf"
proof -
  have i: "dwe_resume (dwc_inner b10) bif"
    using bi_resume by (simp add: b10_def)
  show ?thesis
    by (rule dwc_resume_liftI[OF i]) (simp add: b10_def bf_def mkZ_def)
qed

lemma reach_b9: "dwc_reachable b9"
  by (rule dwc_reachable_arrive_ext[OF reach_z8 bs9])

lemma reach_b10: "dwc_reachable b10"
  by (rule dwc_reachable_escape_ext[OF reach_b9 besc10])

lemma reach_bf: "dwc_reachable bf"
  by (rule dwc_reachable_resume_ext[OF reach_b10 bres_f])

lemma bf_eo: "dwc_eo_at ec2 bf"
  by (simp add: dwc_eo_at_def dwc_accepted_unsafe_def
                dwc_accepted_premature_def dwc_accepted_duplicate_def
                dwc_alo_at_def justified_at_def dwc_replay_def dwc_src_def
                dwc_scope_def replay_down_hist_def bf_def mkZ_def bif_def
                mkT_def mkC_def e1_def e2_def ec_defs eval_nat_numeral)

lemma bf_no_duplicate: "\<not> dwc_accepted_duplicate bf"
  by (simp add: dwc_accepted_duplicate_def bf_def mkZ_def e1_def e2_def
                ec_defs)

theorem crashed_arrival_benign:
  "dwc_reachable bf \<and> dwc_eo_at ec2 bf \<and> \<not> dwc_accepted_duplicate bf
 \<and> dwc_sink_delta ec2 b9 = []"
  by (intro conjI reach_bf bf_eo bf_no_duplicate b9_delta)

section \<open>The wipe twin: crash clears the wire\<close>

text \<open>
  The survival control's mechanism: a twin TRACE RELATION on the SAME
  record --- no new record, no parameterized machine.  Its rules are
  the channel machine's rules verbatim, except that the Crash label is
  interpreted by the one twin rule below: the inner crashes exactly as
  landed, and the channel is CLEARED --- the wire dies with the
  process.  Everything else (sends, arrivals, losses, both re-drive
  composites, the cursor re-drive, Resume) is untouched.
\<close>

definition dwc_wipe_crash
  :: "('k, 'v) dwc_state \<Rightarrow> src_coord \<Rightarrow> ('k, 'v) dwc_state \<Rightarrow> bool"
where
  "dwc_wipe_crash t c t' \<longleftrightarrow>
     (\<exists>i'. dwe_step (dwc_inner t) (Crash c) i'
         \<and> t' = t\<lparr>dwc_inner := i', dwc_channel := []\<rparr>)"

lemma dwc_wipe_crashI:
  assumes "dwe_step (dwc_inner t) (Crash c) i'"
      and "t' = t\<lparr>dwc_inner := i', dwc_channel := []\<rparr>"
  shows "dwc_wipe_crash t c t'"
  using assms by (auto simp: dwc_wipe_crash_def)

inductive dwc0_temporal_trace
  :: "('k, 'v) dwc_state \<Rightarrow> ('k, 'v) dwc_action list \<Rightarrow> ('k, 'v) dwc_state
      \<Rightarrow> bool"
where
  dwc0_refl: "dwc0_temporal_trace t [] t"
| dwc0_label_step:
    "\<lbrakk>wellformed_exec_state (dwe_core (dwc_inner t));
      exec_label_preserves_history_wf (dwe_core (dwc_inner t)) a;
      \<forall>c. a \<noteq> Crash c;
      dwc_step t a t';  dwc0_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwc0_temporal_trace t (DWC_Label a # as) t''"
| dwc0_wipe_step:
    "\<lbrakk>wellformed_exec_state (dwe_core (dwc_inner t));
      exec_label_preserves_history_wf (dwe_core (dwc_inner t)) (Crash c);
      dwc_wipe_crash t c t';  dwc0_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwc0_temporal_trace t (DWC_Label (Crash c) # as) t''"
| dwc0_reconcile_step:
    "\<lbrakk>dwc_reconcile_send m t f t';  dwc0_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwc0_temporal_trace t (DWC_Reconcile m f # as) t''"
| dwc0_resume_step:
    "\<lbrakk>dwc_resume_lift t t';  dwc0_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwc0_temporal_trace t (DWC_Resume # as) t''"
| dwc0_arrive_step:
    "\<lbrakk>dwc_arrive t i t';  dwc0_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwc0_temporal_trace t (DWC_Arrive i # as) t''"
| dwc0_lose_step:
    "\<lbrakk>dwc_lose t i t';  dwc0_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwc0_temporal_trace t (DWC_Lose i # as) t''"
| dwc0_escape_step:
    "\<lbrakk>dwc_escape_redrive f t t';  dwc0_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwc0_temporal_trace t (DWC_Escape f # as) t''"
| dwc0_fenced_step:
    "\<lbrakk>dwc_fenced_redrive f t t';  dwc0_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwc0_temporal_trace t (DWC_Fenced f # as) t''"

lemma dwc0_temporal_trace_append:
  assumes "dwc0_temporal_trace s as s'"
      and "dwc0_temporal_trace s' bs s''"
  shows "dwc0_temporal_trace s (as @ bs) s''"
  using assms
  by (induction rule: dwc0_temporal_trace.induct)
     (auto intro: dwc0_temporal_trace.intros)

definition dwc0_reachable :: "(nat, nat) dwc_state \<Rightarrow> bool" where
  "dwc0_reachable t \<longleftrightarrow>
     (\<exists>xs. dwc0_temporal_trace (dwc_init Map.empty {0, 1} ec2) xs t)"

lemma dwc0_reachable_init: "dwc0_reachable (dwc_init Map.empty {0, 1} ec2)"
  unfolding dwc0_reachable_def
  by (intro exI[of _ "[]"] dwc0_temporal_trace.dwc0_refl)

lemma dwc0_reachable_label_ext:
  assumes "dwc0_reachable t"
      and "wellformed_exec_state (dwe_core (dwc_inner t))"
      and "exec_label_preserves_history_wf (dwe_core (dwc_inner t)) a"
      and "\<forall>c. a \<noteq> Crash c"
      and "dwc_step t a t'"
  shows "dwc0_reachable t'"
proof -
  obtain xs where xs: "dwc0_temporal_trace (dwc_init Map.empty {0, 1} ec2) xs t"
    using assms(1) unfolding dwc0_reachable_def by blast
  have one: "dwc0_temporal_trace t [DWC_Label a] t'"
    by (rule dwc0_temporal_trace.dwc0_label_step[OF assms(2) assms(3) assms(4)
          assms(5) dwc0_temporal_trace.dwc0_refl])
  show ?thesis
    unfolding dwc0_reachable_def
    using dwc0_temporal_trace_append[OF xs one] by blast
qed

lemma dwc0_reachable_wipe_ext:
  assumes "dwc0_reachable t"
      and "wellformed_exec_state (dwe_core (dwc_inner t))"
      and "dwc_wipe_crash t c t'"
  shows "dwc0_reachable t'"
proof -
  obtain xs where xs: "dwc0_temporal_trace (dwc_init Map.empty {0, 1} ec2) xs t"
    using assms(1) unfolding dwc0_reachable_def by blast
  have g: "exec_label_preserves_history_wf (dwe_core (dwc_inner t)) (Crash c)"
    by (simp add: exec_label_preserves_history_wf_def)
  have one: "dwc0_temporal_trace t [DWC_Label (Crash c)] t'"
    by (rule dwc0_temporal_trace.dwc0_wipe_step[OF assms(2) g assms(3)
          dwc0_temporal_trace.dwc0_refl])
  show ?thesis
    unfolding dwc0_reachable_def
    using dwc0_temporal_trace_append[OF xs one] by blast
qed

lemma dwc0_reachable_arrive_ext:
  assumes "dwc0_reachable t"
      and "dwc_arrive t i t'"
  shows "dwc0_reachable t'"
proof -
  obtain xs where xs: "dwc0_temporal_trace (dwc_init Map.empty {0, 1} ec2) xs t"
    using assms(1) unfolding dwc0_reachable_def by blast
  have one: "dwc0_temporal_trace t [DWC_Arrive i] t'"
    by (rule dwc0_temporal_trace.dwc0_arrive_step[OF assms(2)
          dwc0_temporal_trace.dwc0_refl])
  show ?thesis
    unfolding dwc0_reachable_def
    using dwc0_temporal_trace_append[OF xs one] by blast
qed

lemma dwc0_reachable_resume_ext:
  assumes "dwc0_reachable t"
      and "dwc_resume_lift t t'"
  shows "dwc0_reachable t'"
proof -
  obtain xs where xs: "dwc0_temporal_trace (dwc_init Map.empty {0, 1} ec2) xs t"
    using assms(1) unfolding dwc0_reachable_def by blast
  have one: "dwc0_temporal_trace t [DWC_Resume] t'"
    by (rule dwc0_temporal_trace.dwc0_resume_step[OF assms(2)
          dwc0_temporal_trace.dwc0_refl])
  show ?thesis
    unfolding dwc0_reachable_def
    using dwc0_temporal_trace_append[OF xs one] by blast
qed

lemma dwc0_reachable_escape_ext:
  assumes "dwc0_reachable t"
      and "dwc_escape_redrive f t t'"
  shows "dwc0_reachable t'"
proof -
  obtain xs where xs: "dwc0_temporal_trace (dwc_init Map.empty {0, 1} ec2) xs t"
    using assms(1) unfolding dwc0_reachable_def by blast
  have one: "dwc0_temporal_trace t [DWC_Escape f] t'"
    by (rule dwc0_temporal_trace.dwc0_escape_step[OF assms(2)
          dwc0_temporal_trace.dwc0_refl])
  show ?thesis
    unfolding dwc0_reachable_def
    using dwc0_temporal_trace_append[OF xs one] by blast
qed

subsection \<open>The twin runs the same schedule\<close>

text \<open>
  The w-chain (gate amendment MF-1's pinned action list): the
  z-chain's first eight actions verbatim --- the twin's first eight
  states ARE @{const z0} ... @{const z7}, since no rule before the
  crash differs --- with the Crash interpreted by
  @{const dwc_wipe_crash}; then the same escape at the same frontier,
  the same Resume, the same three epoch-one labels for the third
  event, and then a SINGLE arrival: index zero, the fresh epoch-one
  emission, the only entry the wiped wire carries.
\<close>

lemma reach0_z0: "dwc0_reachable z0"
  unfolding z0_init by (rule dwc0_reachable_init)

lemma reach0_z1: "dwc0_reachable z1"
  by (rule dwc0_reachable_label_ext[OF reach0_z0 _ _ _ zs1])
     (simp_all add: z0_def wf_W0 g_W0_src1)

lemma reach0_z2: "dwc0_reachable z2"
  by (rule dwc0_reachable_label_ext[OF reach0_z1 _ _ _ zs2])
     (simp_all add: z1_def wf_W1 g_W1_enq1)

lemma reach0_z3: "dwc0_reachable z3"
  by (rule dwc0_reachable_label_ext[OF reach0_z2 _ _ _ zs3])
     (simp_all add: z2_def wf_W2 g_W2_down1)

lemma reach0_z4: "dwc0_reachable z4"
  by (rule dwc0_reachable_arrive_ext[OF reach0_z3 zs4])

lemma reach0_z5: "dwc0_reachable z5"
  by (rule dwc0_reachable_label_ext[OF reach0_z4 _ _ _ zs5])
     (simp_all add: z4_def wf_W3 g_W3_src2)

lemma reach0_z6: "dwc0_reachable z6"
  by (rule dwc0_reachable_label_ext[OF reach0_z5 _ _ _ zs6])
     (simp_all add: z5_def wf_W4 g_W4_enq2)

lemma reach0_z7: "dwc0_reachable z7"
  by (rule dwc0_reachable_label_ext[OF reach0_z6 _ _ _ zs7])
     (simp_all add: z6_def wf_W5 g_W5_down2)

text \<open>The twin crash: the inner crashes exactly as on the channel
  machine (the SAME landed inner step), and the wire is wiped ---
  the in-flight @{term "(2, 0, ec2, e2)"} is gone.\<close>

lemma wwipe8: "dwc_wipe_crash z7 ec2 w8"
proof -
  have i: "dwe_step (dwc_inner z7) (Crash ec2) zi8"
    using zi_crash by (simp add: z7_def)
  show ?thesis
    by (rule dwc_wipe_crashI[OF i]) (simp add: z7_def w8_def mkZ_def)
qed

lemma reach0_w8: "dwc0_reachable w8"
  by (rule dwc0_reachable_wipe_ext[OF reach0_z7 _ wwipe8])
     (simp add: z7_def wf_zi7)

text \<open>The twin's recovery reads the same accepted record and computes
  the SAME delta --- the missing effect is re-driven identically; the
  read cannot and need not distinguish a wiped send from an in-flight
  one.\<close>

lemma w8_delta: "dwc_sink_delta ec2 w8 = [(ec2, e2)]"
  by (simp add: dwc_sink_delta_def dwc_replay_def dwc_src_def dwc_scope_def
                replay_down_hist_def w8_def mkZ_def zi8_def mkT_def mkC_def
                e1_def e2_def ec_defs)

lemma wesc9: "dwc_escape_redrive ec2 w8 w9"
  by (rule dwc_escape_redriveI)
     (simp_all add: w8_def w9_def mkZ_def zi8_def zi9_def mkT_def mkC_def
                    dwc_sink_delta_def dwc_replay_def dwc_src_def
                    dwc_scope_def replay_down_hist_def e1_def e2_def ec_defs
                    eval_nat_numeral)

lemma reach0_w9: "dwc0_reachable w9"
  by (rule dwc0_reachable_escape_ext[OF reach0_w8 wesc9])

lemma wres10: "dwc_resume_lift w9 w10"
proof -
  have i: "dwe_resume (dwc_inner w9) zi10"
    using zi_resume by (simp add: w9_def)
  show ?thesis
    by (rule dwc_resume_liftI[OF i]) (simp add: w9_def w10_def mkZ_def)
qed

lemma reach0_w10: "dwc0_reachable w10"
  by (rule dwc0_reachable_resume_ext[OF reach0_w9 wres10])

lemma ws11: "dwc_step w10 (DoSource ec3 ev3) w11"
proof -
  have i: "dwe_step (dwc_inner w10) (DoSource ec3 ev3) zi11"
    using zi_src3 by (simp add: w10_def)
  show ?thesis
    by (rule dwc_lift_nonpubI[OF i]) (simp_all add: w10_def w11_def mkZ_def)
qed

lemma reach0_w11: "dwc0_reachable w11"
  by (rule dwc0_reachable_label_ext[OF reach0_w10 _ _ _ ws11])
     (simp_all add: w10_def wf_zi10 g_zi10_src3)

lemma ws12: "dwc_step w11 (EnqueueDownstream ec3 ev3) w12"
proof -
  have i: "dwe_step (dwc_inner w11) (EnqueueDownstream ec3 ev3) zi12"
    using zi_enq3 by (simp add: w11_def)
  show ?thesis
    by (rule dwc_lift_nonpubI[OF i]) (simp_all add: w11_def w12_def mkZ_def)
qed

lemma reach0_w12: "dwc0_reachable w12"
  by (rule dwc0_reachable_label_ext[OF reach0_w11 _ _ _ ws12])
     (simp_all add: w11_def wf_zi11 g_zi11_enq3)

lemma ws13: "dwc_step w12 (DoDownstream ec3 ev3) w13"
proof -
  have i: "dwe_step (dwc_inner w12) (DoDownstream ec3 ev3) zi13"
    using zi_down3 by (simp add: w12_def)
  show ?thesis
    by (rule dwc_send_pubI[OF i])
       (simp add: w12_def w13_def mkZ_def zi12_def mkT_def mkC_def
                  dwc_src_def eval_nat_numeral)
qed

lemma reach0_w13: "dwc0_reachable w13"
  by (rule dwc0_reachable_label_ext[OF reach0_w12 _ _ _ ws13])
     (simp_all add: w12_def wf_zi12 g_zi12_down3)

lemma ws_fin: "dwc_arrive w13 0 w_fin"
  by (rule dwc_arrive_acceptI)
     (simp_all add: w13_def w_fin_def mkZ_def)

lemma reach0_w_fin: "dwc0_reachable w_fin"
  by (rule dwc0_reachable_arrive_ext[OF reach0_w13 ws_fin])

text \<open>The COMPLETE twin schedule as one trace fact: the zombie
  schedule's first thirteen actions VERBATIM --- same labels, same
  crash label (interpreted by the wipe rule), same escape at the same
  frontier, same resume, same epoch-one work --- closed by the single
  fresh arrival.  The two pinned action lists differ only in the
  zombie run's extra final arrivals, and the twin's wire cannot
  carry them (the unfireability lemmas below).\<close>

lemma twin_run_action_list:
  "dwc0_temporal_trace (dwc_init Map.empty {0, 1} ec2)
     [DWC_Label (DoSource ec1 e1), DWC_Label (EnqueueDownstream ec1 e1),
      DWC_Label (DoDownstream ec1 e1), DWC_Arrive 0,
      DWC_Label (DoSource ec2 e2), DWC_Label (EnqueueDownstream ec2 e2),
      DWC_Label (DoDownstream ec2 e2), DWC_Label (Crash ec2),
      DWC_Escape ec2, DWC_Resume,
      DWC_Label (DoSource ec3 ev3), DWC_Label (EnqueueDownstream ec3 ev3),
      DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 0] w_fin"
proof -
  have b14: "dwc0_temporal_trace w13 [DWC_Arrive 0] w_fin"
    by (rule dwc0_temporal_trace.dwc0_arrive_step[OF ws_fin
          dwc0_temporal_trace.dwc0_refl])
  have b13: "dwc0_temporal_trace w12
               [DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 0] w_fin"
    by (rule dwc0_temporal_trace.dwc0_label_step[OF _ _ _ ws13 b14])
       (simp_all add: w12_def wf_zi12 g_zi12_down3)
  have b12: "dwc0_temporal_trace w11
               [DWC_Label (EnqueueDownstream ec3 ev3),
                DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 0] w_fin"
    by (rule dwc0_temporal_trace.dwc0_label_step[OF _ _ _ ws12 b13])
       (simp_all add: w11_def wf_zi11 g_zi11_enq3)
  have b11: "dwc0_temporal_trace w10
               [DWC_Label (DoSource ec3 ev3),
                DWC_Label (EnqueueDownstream ec3 ev3),
                DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 0] w_fin"
    by (rule dwc0_temporal_trace.dwc0_label_step[OF _ _ _ ws11 b12])
       (simp_all add: w10_def wf_zi10 g_zi10_src3)
  have b10: "dwc0_temporal_trace w9
               (DWC_Resume
                # [DWC_Label (DoSource ec3 ev3),
                   DWC_Label (EnqueueDownstream ec3 ev3),
                   DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 0]) w_fin"
    by (rule dwc0_temporal_trace.dwc0_resume_step[OF wres10 b11])
  have b9: "dwc0_temporal_trace w8
              (DWC_Escape ec2 # DWC_Resume
               # [DWC_Label (DoSource ec3 ev3),
                  DWC_Label (EnqueueDownstream ec3 ev3),
                  DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 0]) w_fin"
    by (rule dwc0_temporal_trace.dwc0_escape_step[OF wesc9 b10])
  have b8: "dwc0_temporal_trace z7
              (DWC_Label (Crash ec2) # DWC_Escape ec2 # DWC_Resume
               # [DWC_Label (DoSource ec3 ev3),
                  DWC_Label (EnqueueDownstream ec3 ev3),
                  DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 0]) w_fin"
    by (rule dwc0_temporal_trace.dwc0_wipe_step[OF _ _ wwipe8 b9])
       (simp_all add: z7_def wf_zi7 g_zi7_crash)
  have b7: "dwc0_temporal_trace z6
              (DWC_Label (DoDownstream ec2 e2) # DWC_Label (Crash ec2)
               # DWC_Escape ec2 # DWC_Resume
               # [DWC_Label (DoSource ec3 ev3),
                  DWC_Label (EnqueueDownstream ec3 ev3),
                  DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 0]) w_fin"
    by (rule dwc0_temporal_trace.dwc0_label_step[OF _ _ _ zs7 b8])
       (simp_all add: z6_def wf_W5 g_W5_down2)
  have b6: "dwc0_temporal_trace z5
              (DWC_Label (EnqueueDownstream ec2 e2)
               # DWC_Label (DoDownstream ec2 e2) # DWC_Label (Crash ec2)
               # DWC_Escape ec2 # DWC_Resume
               # [DWC_Label (DoSource ec3 ev3),
                  DWC_Label (EnqueueDownstream ec3 ev3),
                  DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 0]) w_fin"
    by (rule dwc0_temporal_trace.dwc0_label_step[OF _ _ _ zs6 b7])
       (simp_all add: z5_def wf_W4 g_W4_enq2)
  have b5: "dwc0_temporal_trace z4
              (DWC_Label (DoSource ec2 e2)
               # DWC_Label (EnqueueDownstream ec2 e2)
               # DWC_Label (DoDownstream ec2 e2) # DWC_Label (Crash ec2)
               # DWC_Escape ec2 # DWC_Resume
               # [DWC_Label (DoSource ec3 ev3),
                  DWC_Label (EnqueueDownstream ec3 ev3),
                  DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 0]) w_fin"
    by (rule dwc0_temporal_trace.dwc0_label_step[OF _ _ _ zs5 b6])
       (simp_all add: z4_def wf_W3 g_W3_src2)
  have b4: "dwc0_temporal_trace z3
              (DWC_Arrive 0 # DWC_Label (DoSource ec2 e2)
               # DWC_Label (EnqueueDownstream ec2 e2)
               # DWC_Label (DoDownstream ec2 e2) # DWC_Label (Crash ec2)
               # DWC_Escape ec2 # DWC_Resume
               # [DWC_Label (DoSource ec3 ev3),
                  DWC_Label (EnqueueDownstream ec3 ev3),
                  DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 0]) w_fin"
    by (rule dwc0_temporal_trace.dwc0_arrive_step[OF zs4 b5])
  have b3: "dwc0_temporal_trace z2
              (DWC_Label (DoDownstream ec1 e1) # DWC_Arrive 0
               # DWC_Label (DoSource ec2 e2)
               # DWC_Label (EnqueueDownstream ec2 e2)
               # DWC_Label (DoDownstream ec2 e2) # DWC_Label (Crash ec2)
               # DWC_Escape ec2 # DWC_Resume
               # [DWC_Label (DoSource ec3 ev3),
                  DWC_Label (EnqueueDownstream ec3 ev3),
                  DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 0]) w_fin"
    by (rule dwc0_temporal_trace.dwc0_label_step[OF _ _ _ zs3 b4])
       (simp_all add: z2_def wf_W2 g_W2_down1)
  have b2: "dwc0_temporal_trace z1
              (DWC_Label (EnqueueDownstream ec1 e1)
               # DWC_Label (DoDownstream ec1 e1) # DWC_Arrive 0
               # DWC_Label (DoSource ec2 e2)
               # DWC_Label (EnqueueDownstream ec2 e2)
               # DWC_Label (DoDownstream ec2 e2) # DWC_Label (Crash ec2)
               # DWC_Escape ec2 # DWC_Resume
               # [DWC_Label (DoSource ec3 ev3),
                  DWC_Label (EnqueueDownstream ec3 ev3),
                  DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 0]) w_fin"
    by (rule dwc0_temporal_trace.dwc0_label_step[OF _ _ _ zs2 b3])
       (simp_all add: z1_def wf_W1 g_W1_enq1)
  have b1: "dwc0_temporal_trace z0
              (DWC_Label (DoSource ec1 e1)
               # DWC_Label (EnqueueDownstream ec1 e1)
               # DWC_Label (DoDownstream ec1 e1) # DWC_Arrive 0
               # DWC_Label (DoSource ec2 e2)
               # DWC_Label (EnqueueDownstream ec2 e2)
               # DWC_Label (DoDownstream ec2 e2) # DWC_Label (Crash ec2)
               # DWC_Escape ec2 # DWC_Resume
               # [DWC_Label (DoSource ec3 ev3),
                  DWC_Label (EnqueueDownstream ec3 ev3),
                  DWC_Label (DoDownstream ec3 ev3), DWC_Arrive 0]) w_fin"
    by (rule dwc0_temporal_trace.dwc0_label_step[OF _ _ _ zs1 b2])
       (simp_all add: z0_def wf_W0 g_W0_src1)
  show ?thesis using b1 by (simp add: z0_init)
qed

subsection \<open>The zombie arrival has no carrier on the twin\<close>

text \<open>The z-chain's zombie step was @{term "DWC_Arrive 1"} at the
  two-entry wire followed by @{term "DWC_Arrive 0"}.  On the twin the
  wiped wire carries ONE entry, so index one is out of range --- the
  arrive rule cannot fire at all --- and after the single fresh
  arrival the wire is empty: no arrival of any index exists.  The
  zombie is not dropped on the twin; it is INEXPRESSIBLE.\<close>

lemma twin_zombie_arrival_unfireable: "\<not> dwc_arrive w13 1 v"
proof
  assume "dwc_arrive w13 1 v"
  from dwc_arrive_shape[OF this] have "1 < length (dwc_channel w13)"
    by blast
  then show False by (simp add: w13_def eval_nat_numeral)
qed

lemma twin_wire_empty_after_delivery: "\<not> dwc_arrive w_fin i v"
proof
  assume "dwc_arrive w_fin i v"
  from dwc_arrive_shape[OF this] have "i < length (dwc_channel w_fin)"
    by blast
  then show False by (simp add: w_fin_def)
qed

subsection \<open>The survival control\<close>

lemma w_fin_eo: "dwc_eo_at ec2 w_fin"
  by (simp add: dwc_eo_at_def dwc_accepted_unsafe_def
                dwc_accepted_premature_def dwc_accepted_duplicate_def
                dwc_alo_at_def justified_at_def dwc_replay_def dwc_src_def
                dwc_scope_def replay_down_hist_def w_fin_def mkZ_def
                zi13_def mkT_def mkC_def e1_def e2_def ev3_def ec_defs
                eval_nat_numeral)

lemma w_fin_no_duplicate: "\<not> dwc_accepted_duplicate w_fin"
  by (simp add: dwc_accepted_duplicate_def w_fin_def mkZ_def e1_def e2_def
                ev3_def ec_defs)

lemma w8_wire_wiped: "dwc_channel w8 = []"
  by (simp add: w8_def)

text \<open>
  THE CONTROL BITES: on the wipe twin the same action schedule ---
  same labels, same recovery rule at the same frontier, same resume,
  same fresh epoch-one work --- ends exactly-once with a
  duplicate-free record, because the crash cleared the wire and the
  zombie arrival has no carrier.  One rule-body difference (crash
  wipes the channel instead of leaving it) flips the verdict of the
  defeat theorem above: the crash-survives-wire design choice of the
  channel machine is witnessed LOAD-BEARING for the zombie.

  Honest scope: this is a SCHEDULE-level witness, not a machine-wide
  twin safety law --- machine-wide accepted-distinctness is false on
  the twin too (a post-resume application may legally re-publish an
  already-accepted payload and deliver it; the landed core carries no
  freshness guard).  The claim is exactly: wipe the wire at the crash
  and THIS schedule stays exactly-once.
\<close>

theorem channel_survival_control:
  "dwc0_reachable w_fin
 \<and> dwc_eo_at ec2 w_fin \<and> \<not> dwc_accepted_duplicate w_fin
 \<and> dwc_channel w8 = []"
  by (intro conjI reach0_w_fin w_fin_eo w_fin_no_duplicate w8_wire_wiped)

end
