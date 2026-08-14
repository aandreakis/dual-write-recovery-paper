(*  Title:       DWU_Machine.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Purpose: Road-2 I0 scaffold — THE UNIFIED MACHINE plus the shared obligations.

    Assembled from the Stage-4 mechanization probe (DWU_Statement_Probe.thy): the
    machine (design sections 2-6 as amended by the Stage-3 pins P1-P8) and the
    shared obligations S1-S6, with the three obligations that were oops'd in the
    probe (S4 stamps invariant, S5a/S5b crashed-episode inventory) CLOSED with real
    proofs.  The later-increment battery apparatus (U1-U16 theorems, disciplined /
    solo-disciplined traces, gate/pair/window vocabulary) is deferred to I1-I8.

    Honesty regime: quick_and_dirty = false (ROOT-pinned), ZERO sorry, ZERO oops,
    no axiomatization, no consts, no oracles.  Every statement is PROVED.
*)

theory DWU_Machine
  imports
    "Dual_Write_Effect.Dual_Write_Effect_Exactly_Once"
    "Dual_Write_Core.Dual_Write_Crash_Truncation"
begin

section \<open>1. THE MACHINE\<close>

subsection \<open>1.1 State (design section 2)\<close>

datatype ('k, 'v) upayload =
    ULog "src_coord \<times> ('k, 'v) source_event"
  | USnap src_coord 'k "'v option"

record ('k, 'v) uemission =
  ue_stamp :: nat
  ue_gen   :: nat
  ue_pay   :: "('k, 'v) upayload"

text \<open>Register the fresh named record as a BNF so it may occur inside the
  @{text ustage} and @{text dwu_action} datatypes below (record types are not
  BNFs by default; this is a standard registration, not an axiom).\<close>

copy_bnf ('k, 'v, 'z) uemission_ext

datatype ('k, 'v) ustage = UProd | UArmed "('k, 'v) uemission list"

record ('k, 'v) dwu_state =
  dwu_store    :: "('k, 'v) dw_exec_state"
  dwu_journal  :: "('k, 'v) src_history"
  dwu_sent     :: "('k, 'v) uemission list"
  dwu_accepted :: "('k, 'v) uemission list"
  dwu_fence    :: nat
  dwu_gens     :: "nat \<rightharpoonup> ('k, 'v) ustage"
  dwu_hwm      :: nat
  dwu_floor    :: nat

definition dwu_init :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'k set \<Rightarrow> frontier \<Rightarrow> ('k, 'v) dwu_state" where
  "dwu_init b K fin =
     \<lparr> dwu_store = initial_exec_state b K fin,
       dwu_journal = [],
       dwu_sent = [],
       dwu_accepted = [],
       dwu_fence = 0,
       dwu_gens = [0 \<mapsto> UProd],
       dwu_hwm = 0,
       dwu_floor = 0 \<rparr>"

subsection \<open>1.2 Derived vocabulary (design section 3, S7 live auxiliaries, R4/U5 scope predicate)\<close>

definition retained_hist :: "('k, 'v) dwu_state \<Rightarrow> ('k, 'v) src_history" where
  "retained_hist t = drop (dwu_floor t) (exec_src_hist (dwu_store t))"

definition u_justified :: "('k, 'v) dwu_state \<Rightarrow> ('k, 'v) uemission \<Rightarrow> bool" where
  "u_justified t x \<longleftrightarrow>
     ue_stamp x \<le> length (dwu_journal t) \<and>
     (case ue_pay x of
        ULog p \<Rightarrow> p \<in> set (take (ue_stamp x) (dwu_journal t))
      | USnap c k v \<Rightarrow> v = Src (exec_base (dwu_store t)) (take (ue_stamp x) (dwu_journal t)) c k)"

definition log_payloads :: "('k, 'v) uemission list \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list" where
  "log_payloads xs =
     List.map_filter (\<lambda>x. case ue_pay x of ULog p \<Rightarrow> Some p | _ \<Rightarrow> None) xs"

definition u_premature :: "('k, 'v) dwu_state \<Rightarrow> bool" where
  "u_premature t \<longleftrightarrow> (\<exists>x \<in> set (dwu_accepted t). \<not> u_justified t x)"

definition u_duplicate :: "('k, 'v) dwu_state \<Rightarrow> bool" where
  "u_duplicate t \<longleftrightarrow> \<not> distinct (log_payloads (dwu_accepted t))"

definition u_effect_unsafe :: "('k, 'v) dwu_state \<Rightarrow> bool" where
  "u_effect_unsafe t \<longleftrightarrow> u_premature t \<or> u_duplicate t"

definition u_lost :: "frontier \<Rightarrow> ('k, 'v) dwu_state \<Rightarrow> bool" where
  "u_lost f t \<longleftrightarrow>
     (\<exists>p \<in> set (replay_down_hist (retained_hist t) (exec_scope (dwu_store t)) f).
        p \<notin> set (log_payloads (dwu_accepted t)))"

definition u_lost_journal :: "frontier \<Rightarrow> ('k, 'v) dwu_state \<Rightarrow> bool" where
  "u_lost_journal f t \<longleftrightarrow>
     (\<exists>p \<in> set (replay_down_hist (dwu_journal t) (exec_scope (dwu_store t)) f).
        p \<notin> set (log_payloads (dwu_accepted t)))"

definition u_sink_delta
  :: "frontier \<Rightarrow> ('k, 'v) dwu_state \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list"
where
  "u_sink_delta f t =
     filter (\<lambda>p. p \<notin> set (log_payloads (dwu_accepted t)))
       (replay_down_hist (retained_hist t) (exec_scope (dwu_store t)) f)"

definition u_at_least_once_at :: "frontier \<Rightarrow> ('k, 'v) dwu_state \<Rightarrow> bool" where
  "u_at_least_once_at f t \<longleftrightarrow>
     set (replay_down_hist (retained_hist t) (exec_scope (dwu_store t)) f)
       \<subseteq> set (log_payloads (dwu_accepted t))"

definition u_exactly_once_at :: "frontier \<Rightarrow> ('k, 'v) dwu_state \<Rightarrow> bool" where
  "u_exactly_once_at f t \<longleftrightarrow> \<not> u_effect_unsafe t \<and> u_at_least_once_at f t"

definition u_genuinely_emitting :: "('k, 'v) dwu_state \<Rightarrow> bool" where
  "u_genuinely_emitting t \<longleftrightarrow> dwu_accepted t \<noteq> []"

definition u_dedup_view
  :: "('k, 'v) dwu_state \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list"
where
  "u_dedup_view t = remdups (log_payloads (dwu_accepted t))"

text \<open>S7 live-justification auxiliaries (pinned amendment for U14c/U14d: the design's
  section 3 has the live/journal split for LOSS but not for prematurity).\<close>

definition u_justified_live :: "('k, 'v) dwu_state \<Rightarrow> ('k, 'v) uemission \<Rightarrow> bool" where
  "u_justified_live t x \<longleftrightarrow>
     ue_stamp x \<le> length (exec_src_hist (dwu_store t)) \<and>
     (case ue_pay x of
        ULog p \<Rightarrow> p \<in> set (take (ue_stamp x) (exec_src_hist (dwu_store t)))
      | USnap c k v \<Rightarrow>
          v = Src (exec_base (dwu_store t)) (take (ue_stamp x) (exec_src_hist (dwu_store t))) c k)"

definition u_premature_live :: "('k, 'v) dwu_state \<Rightarrow> bool" where
  "u_premature_live t \<longleftrightarrow> (\<exists>x \<in> set (dwu_accepted t). \<not> u_justified_live t x)"

text \<open>R4/U5 pinned scope predicate (P2 and P4 pins agree on this form).\<close>

definition u_permanent_source :: "('k, 'v) dwu_state \<Rightarrow> bool" where
  "u_permanent_source W \<longleftrightarrow>
     dwu_journal W = exec_src_hist (dwu_store W) \<and> dwu_floor W = 0"

text \<open>ULog stamping of payload batches (U1 pin: the cursor-arm/reconcile batch shape).\<close>

definition stamped_at
  :: "nat \<Rightarrow> nat \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list \<Rightarrow> ('k, 'v) uemission list"
where
  "stamped_at n g ps = map (\<lambda>p. \<lparr> ue_stamp = n, ue_gen = g, ue_pay = ULog p \<rparr>) ps"

text \<open>General recovery-batch helper (probe section 1.8, KEPT here at I0: U10/U9 consume
  it in later increments).\<close>

definition u_stamped_batch
  :: "nat \<Rightarrow> nat \<Rightarrow> (nat, nat) upayload list \<Rightarrow> (nat, nat) uemission list"
where
  "u_stamped_batch n g qs = map (\<lambda>q. \<lparr> ue_stamp = n, ue_gen = g, ue_pay = q \<rparr>) qs"

text \<open>Cheap definitional bridges and list infrastructure (proved).\<close>

lemma u_at_least_once_iff_not_lost:
  "u_at_least_once_at f t \<longleftrightarrow> \<not> u_lost f t"
  by (auto simp: u_at_least_once_at_def u_lost_def)

lemma log_payloads_append:
  "log_payloads (xs @ ys) = log_payloads xs @ log_payloads ys"
  by (induction xs)
     (auto simp: log_payloads_def map_filter_simps split: upayload.splits option.splits)

lemma log_payloads_stamped_at [simp]:
  "log_payloads (stamped_at n g ps) = ps"
  by (induction ps) (auto simp: log_payloads_def stamped_at_def map_filter_simps)

lemma log_payloads_snap [simp]:
  "log_payloads [\<lparr> ue_stamp = n, ue_gen = g, ue_pay = USnap c k v \<rparr>] = []"
  by (simp add: log_payloads_def map_filter_simps)

subsection \<open>1.3 Actions and transition rules (design section 4, as amended by S3)\<close>

datatype ('k, 'v) dwu_action =
    ULift nat "('k, 'v) dw_exec_label"
  | UPubLost nat src_coord "('k, 'v) source_event"
  | USnapE nat src_coord 'k "'v option"
  | USpawn
  | UArm nat "('k, 'v) uemission list" frontier
  | UArmF nat frontier
  | UHeal nat frontier
  | UFire nat
  | URelease nat
  | UFenceRaise nat
  | UTruncCrash frontier frontier
  | URetain nat

fun u_production_label :: "('k, 'v) dw_exec_label \<Rightarrow> bool" where
  "u_production_label (DoSource c e) = True"
| "u_production_label (EnqueueDownstream c e) = True"
| "u_production_label (DoDownstream c e) = True"
| "u_production_label (Ack c e) = True"
| "u_production_label (Crash f) = False"
| "u_production_label Recover = False"
| "u_production_label (Observe f) = False"

inductive dwu_step
  :: "('k, 'v) dwu_state \<Rightarrow> ('k, 'v) dwu_action \<Rightarrow> ('k, 'v) dwu_state \<Rightarrow> bool"
where
  ulift_source:
    "\<lbrakk>g \<in> dom (dwu_gens t); dwu_gens t g = Some UProd;
      dw_exec_step (dwu_store t) (DoSource c e) s'\<rbrakk> \<Longrightarrow>
     dwu_step t (ULift g (DoSource c e))
       (t\<lparr>dwu_store := s', dwu_journal := dwu_journal t @ [(c, e)]\<rparr>)"
| ulift_enqueue:
    "\<lbrakk>g \<in> dom (dwu_gens t); dwu_gens t g = Some UProd;
      dw_exec_step (dwu_store t) (EnqueueDownstream c e) s'\<rbrakk> \<Longrightarrow>
     dwu_step t (ULift g (EnqueueDownstream c e)) (t\<lparr>dwu_store := s'\<rparr>)"
| ulift_ack:
    "\<lbrakk>g \<in> dom (dwu_gens t); dwu_gens t g = Some UProd;
      dw_exec_step (dwu_store t) (Ack c e) s'\<rbrakk> \<Longrightarrow>
     dwu_step t (ULift g (Ack c e)) (t\<lparr>dwu_store := s'\<rparr>)"
| ulift_publish:
    "\<lbrakk>g \<in> dom (dwu_gens t); dwu_gens t g = Some UProd;
      dw_exec_step (dwu_store t) (DoDownstream c e) s';
      x = \<lparr> ue_stamp = length (dwu_journal t), ue_gen = g, ue_pay = ULog (c, e) \<rparr>\<rbrakk> \<Longrightarrow>
     dwu_step t (ULift g (DoDownstream c e))
       (t\<lparr>dwu_store := s',
          dwu_sent := dwu_sent t @ [x],
          dwu_accepted := dwu_accepted t @ (if dwu_fence t \<le> ue_gen x then [x] else [])\<rparr>)"
| ulift_nonprod:
    "\<lbrakk>g \<in> dom (dwu_gens t); \<not> u_production_label a;
      dw_exec_step (dwu_store t) a s'\<rbrakk> \<Longrightarrow>
     dwu_step t (ULift g a) (t\<lparr>dwu_store := s'\<rparr>)"
| upublost:
    "\<lbrakk>g \<in> dom (dwu_gens t); dwu_gens t g = Some UProd;
      dw_exec_step (dwu_store t) (DoDownstream c e) s';
      x = \<lparr> ue_stamp = length (dwu_journal t), ue_gen = g, ue_pay = ULog (c, e) \<rparr>\<rbrakk> \<Longrightarrow>
     dwu_step t (UPubLost g c e)
       (t\<lparr>dwu_store := s', dwu_sent := dwu_sent t @ [x]\<rparr>)"
| usnap:
    "\<lbrakk>dwu_gens t g = Some UProd; exec_status (dwu_store t) = Running;
      x = \<lparr> ue_stamp = length (dwu_journal t), ue_gen = g, ue_pay = USnap c k v \<rparr>\<rbrakk> \<Longrightarrow>
     dwu_step t (USnapE g c k v)
       (t\<lparr>dwu_sent := dwu_sent t @ [x],
          dwu_accepted := dwu_accepted t @ (if dwu_fence t \<le> ue_gen x then [x] else [])\<rparr>)"
| uspawn:
    "dwu_step t USpawn
       (t\<lparr>dwu_gens := (dwu_gens t)(Suc (dwu_hwm t) \<mapsto> UProd),
          dwu_hwm := Suc (dwu_hwm t)\<rparr>)"
| uarm:
    "\<lbrakk>g \<in> dom (dwu_gens t);
      \<exists>c. exec_status (dwu_store t) = Crashed c;
      f \<le> exec_finish (dwu_store t);
      \<forall>x \<in> set B. ue_gen x = g \<and> ue_stamp x \<le> length (dwu_journal t)\<rbrakk> \<Longrightarrow>
     dwu_step t (UArm g B f) (t\<lparr>dwu_gens := (dwu_gens t)(g \<mapsto> UArmed B)\<rparr>)"
| uarmf:
    "\<lbrakk>g \<in> dom (dwu_gens t);
      \<exists>c. exec_status (dwu_store t) = Crashed c;
      f \<le> exec_finish (dwu_store t);
      dwu_fence t \<le> g\<rbrakk> \<Longrightarrow>
     dwu_step t (UArmF g f)
       (t\<lparr>dwu_fence := g,
          dwu_gens := (dwu_gens t)
            (g \<mapsto> UArmed (stamped_at (length (dwu_journal t)) g (u_sink_delta f t)))\<rparr>)"
| uheal:
    "relay_bounded_replay_reconcile (dwu_store t) f s' \<Longrightarrow>
     dwu_step t (UHeal g f) (t\<lparr>dwu_store := s'\<rparr>)"
| ufire:
    "dwu_gens t g = Some (UArmed B) \<Longrightarrow>
     dwu_step t (UFire g)
       (t\<lparr>dwu_sent := dwu_sent t @ B,
          dwu_accepted := dwu_accepted t @ (if dwu_fence t \<le> g then B else []),
          dwu_gens := (dwu_gens t)(g \<mapsto> UProd)\<rparr>)"
| urelease:
    "exec_status (dwu_store t) = Recovered \<Longrightarrow>
     dwu_step t (URelease g)
       (t\<lparr>dwu_store := (dwu_store t)\<lparr>exec_status := Running\<rparr>\<rparr>)"
| ufenceraise:
    "dwu_step t (UFenceRaise n) (t\<lparr>dwu_fence := max (dwu_fence t) n\<rparr>)"
| utrunccrash:
    "\<lbrakk>wellformed_exec_state (dwu_store t); exec_status (dwu_store t) = Running;
      d \<le> exec_finish (dwu_store t)\<rbrakk> \<Longrightarrow>
     dwu_step t (UTruncCrash d c)
       (t\<lparr>dwu_store := truncating_crash_state (dwu_store t) d c,
          dwu_floor := min (dwu_floor t)
            (length (exec_src_hist (truncating_crash_state (dwu_store t) d c)))\<rparr>)"
| uretain:
    "\<lbrakk>exec_status (dwu_store t) = Running;
      dwu_floor t \<le> n; n \<le> length (exec_src_hist (dwu_store t))\<rbrakk> \<Longrightarrow>
     dwu_step t (URetain n) (t\<lparr>dwu_floor := n\<rparr>)"

subsection \<open>1.4 Temporal traces and reachability (landed list-recursion idiom)\<close>

inductive dwu_temporal_trace
  :: "('k, 'v) dwu_state \<Rightarrow> ('k, 'v) dwu_action list \<Rightarrow> ('k, 'v) dwu_state \<Rightarrow> bool"
where
  dwu_refl:
    "dwu_temporal_trace t [] t"
| dwu_lift_step:
    "\<lbrakk>wellformed_exec_state (dwu_store t);
      exec_label_preserves_history_wf (dwu_store t) a;
      dwu_step t (ULift g a) t';
      dwu_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwu_temporal_trace t (ULift g a # as) t''"
| dwu_publost_step:
    "\<lbrakk>wellformed_exec_state (dwu_store t);
      exec_label_preserves_history_wf (dwu_store t) (DoDownstream c e);
      dwu_step t (UPubLost g c e) t';
      dwu_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwu_temporal_trace t (UPubLost g c e # as) t''"
| dwu_other_step:
    "\<lbrakk>\<forall>g a. \<alpha> \<noteq> ULift g a; \<forall>g c e. \<alpha> \<noteq> UPubLost g c e;
      dwu_step t \<alpha> t';
      dwu_temporal_trace t' as t''\<rbrakk> \<Longrightarrow>
     dwu_temporal_trace t (\<alpha> # as) t''"

lemma dwu_temporal_trace_append:
  assumes "dwu_temporal_trace s as s'"
      and "dwu_temporal_trace s' bs s''"
  shows "dwu_temporal_trace s (as @ bs) s''"
  using assms
  by (induction rule: dwu_temporal_trace.induct)
     (auto intro: dwu_temporal_trace.intros)

definition dwu_reachable
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'k set \<Rightarrow> frontier \<Rightarrow> ('k, 'v) dwu_state \<Rightarrow> bool"
where
  "dwu_reachable b K fin t \<longleftrightarrow> (\<exists>xs. dwu_temporal_trace (dwu_init b K fin) xs t)"

text \<open>The pinned witness alias (boundary row 5 discipline; landed
  @{const dwe_reachable} idiom, monomorphic).\<close>

abbreviation dwu_reachable_w :: "(nat, nat) dwu_state \<Rightarrow> bool" where
  "dwu_reachable_w \<equiv> dwu_reachable Map.empty {0, 1} ec2"

lemma dwu_reachable_init: "dwu_reachable b K fin (dwu_init b K fin)"
  unfolding dwu_reachable_def
  by (intro exI[of _ "[]"] dwu_temporal_trace.dwu_refl)

subsection \<open>1.5 Policy vocabulary (design section 4; u_policy_redrive pinned by P8)\<close>

type_synonym u_redrive_policy =
  "(nat, nat) dwu_state \<Rightarrow> (src_coord \<times> (nat, nat) source_event) list"

text \<open>P8 pin: guards verbatim landed (Crashed + frontier-within-finish, NO watermark,
  NO fence, NO floor); effect = the relay heal image with exec_src_hist AND exec_base
  untouched, journal EXPLICITLY untouched (S3), batch stamped
  @{text "(length (dwu_journal t), dwu_hwm t)"} appended to sent and fence-resolved
  accepted.\<close>

definition u_policy_redrive
  :: "u_redrive_policy \<Rightarrow> (nat, nat) dwu_state \<Rightarrow> frontier \<Rightarrow> (nat, nat) dwu_state \<Rightarrow> bool"
where
  "u_policy_redrive P t f t' \<longleftrightarrow>
     (\<exists>c. exec_status (dwu_store t) = Crashed c)
   \<and> f \<le> exec_finish (dwu_store t)
   \<and> t' = t\<lparr> dwu_store := (dwu_store t)
               \<lparr>exec_down_hist :=
                  replay_down_hist (exec_src_hist (dwu_store t))
                    (exec_scope (dwu_store t)) f,
                exec_pending := {},
                exec_status := Recovered\<rparr>,
             dwu_journal := dwu_journal t,
             dwu_sent := dwu_sent t
               @ stamped_at (length (dwu_journal t)) (dwu_hwm t) (P t),
             dwu_accepted := dwu_accepted t
               @ filter (\<lambda>x. dwu_fence t \<le> ue_gen x)
                   (stamped_at (length (dwu_journal t)) (dwu_hwm t) (P t)) \<rparr>"

text \<open>The four measurability classes (design section 4).  The retained view is the
  canonical 8-tuple pinned by P6; journal CONTENT is the only excluded coordinate
  (its LENGTH --- the LSN --- is in every view).  @{text u_retention_respecting} is
  concretized as factoring through the above-floor (retained) source view: the
  design leaves "the above-floor view" informal and no battery statement consumes
  it (the U15 companion is demoted), so this is recorded as a deviation.\<close>

definition u_store_measured :: "u_redrive_policy \<Rightarrow> bool" where
  "u_store_measured P \<longleftrightarrow> (\<exists>g. \<forall>t. P t = g (dwu_store t))"

definition u_control_plane_view
  :: "('k, 'v) dwu_state \<Rightarrow>
      ('k, 'v) dw_exec_state \<times> nat \<times> nat \<times> (nat \<rightharpoonup> ('k, 'v) ustage) \<times> nat \<times> nat"
where
  "u_control_plane_view t =
     (dwu_store t, length (dwu_journal t), dwu_fence t, dwu_gens t, dwu_hwm t, dwu_floor t)"

definition u_control_plane_measured :: "u_redrive_policy \<Rightarrow> bool" where
  "u_control_plane_measured P \<longleftrightarrow> (\<exists>g. \<forall>t. P t = g (u_control_plane_view t))"

definition u_retained_view
  :: "('k, 'v) dwu_state \<Rightarrow>
      ('k, 'v) dw_exec_state \<times> nat \<times> nat \<times> (nat \<rightharpoonup> ('k, 'v) ustage) \<times> nat \<times> nat
        \<times> ('k, 'v) uemission list \<times> ('k, 'v) uemission list"
where
  "u_retained_view t =
     (dwu_store t, length (dwu_journal t), dwu_fence t, dwu_gens t, dwu_hwm t,
      dwu_floor t, dwu_sent t, dwu_accepted t)"

definition u_retained_measured :: "u_redrive_policy \<Rightarrow> bool" where
  "u_retained_measured P \<longleftrightarrow> (\<exists>g. \<forall>t. P t = g (u_retained_view t))"

definition u_retention_view
  :: "('k, 'v) dwu_state \<Rightarrow>
      ('k, 'v) dw_exec_state \<times> nat \<times> nat \<times> (nat \<rightharpoonup> ('k, 'v) ustage) \<times> nat \<times> nat
        \<times> ('k, 'v) uemission list \<times> ('k, 'v) uemission list"
where
  "u_retention_view t =
     ((dwu_store t)\<lparr>exec_src_hist := retained_hist t\<rparr>, length (dwu_journal t),
      dwu_fence t, dwu_gens t, dwu_hwm t, dwu_floor t, dwu_sent t, dwu_accepted t)"

definition u_retention_respecting :: "u_redrive_policy \<Rightarrow> bool" where
  "u_retention_respecting P \<longleftrightarrow> (\<exists>g. \<forall>t. P t = g (u_retention_view t))"

subsection \<open>1.6 Projection and embedding (design section 6, U1 pin)\<close>

definition is_ulog :: "('k, 'v) uemission \<Rightarrow> bool" where
  "is_ulog x \<longleftrightarrow> (case ue_pay x of ULog p \<Rightarrow> True | _ \<Rightarrow> False)"

definition ulog_of :: "('k, 'v) uemission \<Rightarrow> src_coord \<times> ('k, 'v) source_event" where
  "ulog_of x = (case ue_pay x of ULog p \<Rightarrow> p)"

definition \<Pi> :: "('k, 'v) dwu_state \<Rightarrow> ('k, 'v) dwe_state" where
  "\<Pi> t = \<lparr> dwe_core = dwu_store t,
           dwe_emitted =
             map (\<lambda>x. (ue_stamp x, ue_gen x, fst (ulog_of x), snd (ulog_of x)))
               (filter is_ulog (dwu_sent t)),
           dwe_epoch = dwu_hwm t \<rparr>"

definition ulift :: "('k, 'v) emission \<Rightarrow> ('k, 'v) uemission" where
  "ulift z = \<lparr> ue_stamp = e_stamp z, ue_gen = e_epoch z, ue_pay = ULog (e_payload z) \<rparr>"

definition \<iota> :: "('k, 'v) dwe_state \<Rightarrow> ('k, 'v) dwu_state" where
  "\<iota> t = \<lparr> dwu_store = dwe_core t,
          dwu_journal = exec_src_hist (dwe_core t),
          dwu_sent = map ulift (dwe_emitted t),
          dwu_accepted = map ulift (dwe_emitted t),
          dwu_fence = 0,
          dwu_gens = (\<lambda>g. if g \<le> dwe_epoch t then Some UProd else None),
          dwu_hwm = dwe_epoch t,
          dwu_floor = 0 \<rparr>"

lemma is_ulog_ulift [simp]: "is_ulog (ulift z)"
  by (simp add: is_ulog_def ulift_def)

lemma ulog_of_ulift [simp]: "ulog_of (ulift z) = e_payload z"
  by (simp add: ulog_of_def ulift_def)

lemma ue_stamp_ulift [simp]: "ue_stamp (ulift z) = e_stamp z"
  by (simp add: ulift_def)

lemma ue_gen_ulift [simp]: "ue_gen (ulift z) = e_epoch z"
  by (simp add: ulift_def)

lemma emission_tuple_collapse [simp]: "(e_stamp z, e_epoch z, e_payload z) = z"
  by (simp add: e_stamp_def e_epoch_def e_payload_def)

lemma \<Pi>_emitted_ulift:
  "map (\<lambda>x. (ue_stamp x, ue_gen x, fst (ulog_of x), snd (ulog_of x)))
     (filter is_ulog (map ulift es)) = es"
  by (induction es) (simp_all add: e_stamp_def e_epoch_def e_payload_def)

text \<open>U1: the section law (stretch goal --- proved).\<close>

lemma \<Pi>_section: "\<Pi> (\<iota> t) = t"
  by (cases t) (simp add: \<Pi>_def \<iota>_def o_def)

text \<open>U1: init alignment (proved).\<close>

lemma \<iota>_init: "\<iota> (dwe_init b K fin) = dwu_init b K fin"
  by (simp add: \<iota>_def dwe_init_def dwu_init_def initial_exec_state_def fun_eq_iff)

subsection \<open>1.7 The solo fragment (design section 6 restriction; U1/U2 amended pins)\<close>

text \<open>P2's pinned 4-place form: the state-indexed grammar derivation OUTPUTS the
  landed action list (the "total strip" is not a ys-only function --- P2 amendment).
  Incumbent actor (= hwm), cursor-shaped arm batches, fused recovery triples,
  adjacent turnover pairs, bare Recover admitted as a plain lift; no UArmF /
  UFenceRaise / USnapE / UPubLost / UTruncCrash / URetain.  The triple carries the
  landed cursor guard @{text "m \<le> length R"} (P3 spillover pin).\<close>

inductive solo_trace
  :: "('k, 'v) dwu_state \<Rightarrow> ('k, 'v) dwu_action list \<Rightarrow> ('k, 'v) dwe_action list
      \<Rightarrow> ('k, 'v) dwu_state \<Rightarrow> bool"
where
  solo_refl:
    "solo_trace u [] [] u"
| solo_lift:
    "\<lbrakk>wellformed_exec_state (dwu_store u);
      exec_label_preserves_history_wf (dwu_store u) a;
      dwu_step u (ULift (dwu_hwm u) a) u1;
      solo_trace u1 ys zs u'\<rbrakk> \<Longrightarrow>
     solo_trace u (ULift (dwu_hwm u) a # ys) (DWE_Label a # zs) u'"
| solo_reconcile:
    "\<lbrakk>g = dwu_hwm u;
      R = replay_down_hist (retained_hist u) (exec_scope (dwu_store u)) f;
      m \<le> length R;
      B = stamped_at (length (dwu_journal u)) g (drop m R);
      dwu_step u (UArm g B f) u1;
      dwu_step u1 (UHeal g f) u2;
      dwu_step u2 (UFire g) u3;
      solo_trace u3 ys zs u'\<rbrakk> \<Longrightarrow>
     solo_trace u (UArm g B f # UHeal g f # UFire g # ys) (DWE_Reconcile m f # zs) u'"
| solo_turnover:
    "\<lbrakk>dwu_step u USpawn u1;
      dwu_step u1 (URelease (dwu_hwm u1)) u2;
      solo_trace u2 ys zs u'\<rbrakk> \<Longrightarrow>
     solo_trace u (USpawn # URelease (dwu_hwm u1) # ys) (DWE_Resume # zs) u'"

text \<open>U2's pinned fragment-invariant bundle, EXTENDED with the gens determination
  (P2/P4's load-bearing shared fix, S1).\<close>

definition solo_inv :: "('k, 'v) dwu_state \<Rightarrow> bool" where
  "solo_inv u \<longleftrightarrow>
     dwu_fence u = 0
   \<and> dwu_floor u = 0
   \<and> dwu_journal u = exec_src_hist (dwu_store u)
   \<and> dwu_sent u = dwu_accepted u
   \<and> (\<forall>x \<in> set (dwu_sent u). is_ulog x)
   \<and> dwu_gens u = (\<lambda>g. if g \<le> dwu_hwm u then Some UProd else None)"

lemma solo_inv_init: "solo_inv (dwu_init b K fin)"
  by (simp add: solo_inv_def dwu_init_def initial_exec_state_def fun_eq_iff)

lemma solo_inv_\<iota>: "solo_inv (\<iota> t)"
  by (auto simp: solo_inv_def \<iota>_def)

subsection \<open>1.8 Named-predicate helpers carried at I0 (S1 shape; S4 invariant)\<close>

text \<open>S1's invariant shape as a named predicate (fragment gens determination).\<close>

definition solo_gens_ok :: "('k, 'v) dwu_state \<Rightarrow> bool" where
  "solo_gens_ok u \<longleftrightarrow>
     dwu_gens u = (\<lambda>g. if g \<le> dwu_hwm u then Some UProd else None)"

text \<open>The strengthened stamps invariant (P7): the naive accepted-only form is NOT
  inductive (UFire's case cannot close); the pinned form covers accepted, sent, and
  every armed batch in the incarnation table.\<close>

definition u_journal_stamps_bounded :: "('k, 'v) dwu_state \<Rightarrow> bool" where
  "u_journal_stamps_bounded t \<longleftrightarrow>
     (\<forall>x \<in> set (dwu_sent t). ue_stamp x \<le> length (dwu_journal t))
   \<and> (\<forall>x \<in> set (dwu_accepted t). ue_stamp x \<le> length (dwu_journal t))
   \<and> (\<forall>g B. dwu_gens t g = Some (UArmed B) \<longrightarrow>
        (\<forall>x \<in> set B. ue_stamp x \<le> length (dwu_journal t)))"


section \<open>2. SHARED OBLIGATIONS S1-S6\<close>

subsection \<open>2.0 Step-inversion frame lemmas (proved; consumed by S1/S2/S3/S6)\<close>

lemma dwu_step_lift_frame:
  assumes "dwu_step t (ULift g a) t'"
  shows "dwu_gens t' = dwu_gens t \<and> dwu_hwm t' = dwu_hwm t
       \<and> dwu_fence t' = dwu_fence t \<and> dwu_floor t' = dwu_floor t"
  using assms by cases auto

lemma dwu_step_arm_inv:
  assumes "dwu_step t (UArm g B f) t'"
  shows "dwu_gens t' = (dwu_gens t)(g \<mapsto> UArmed B) \<and> dwu_hwm t' = dwu_hwm t
       \<and> dwu_store t' = dwu_store t \<and> dwu_journal t' = dwu_journal t
       \<and> dwu_sent t' = dwu_sent t \<and> dwu_accepted t' = dwu_accepted t
       \<and> dwu_fence t' = dwu_fence t \<and> dwu_floor t' = dwu_floor t"
  using assms by cases auto

lemma dwu_step_heal_frame:
  assumes "dwu_step t (UHeal g f) t'"
  shows "dwu_gens t' = dwu_gens t \<and> dwu_hwm t' = dwu_hwm t
       \<and> dwu_journal t' = dwu_journal t \<and> dwu_sent t' = dwu_sent t
       \<and> dwu_accepted t' = dwu_accepted t \<and> dwu_fence t' = dwu_fence t
       \<and> dwu_floor t' = dwu_floor t"
  using assms by cases auto

lemma dwu_step_fire_inv:
  assumes "dwu_step t (UFire g) t'"
  shows "\<exists>B. dwu_gens t g = Some (UArmed B)
       \<and> dwu_gens t' = (dwu_gens t)(g \<mapsto> UProd)
       \<and> dwu_hwm t' = dwu_hwm t \<and> dwu_store t' = dwu_store t
       \<and> dwu_journal t' = dwu_journal t \<and> dwu_fence t' = dwu_fence t
       \<and> dwu_floor t' = dwu_floor t"
  using assms by cases auto

lemma dwu_step_spawn_inv:
  assumes "dwu_step t USpawn t'"
  shows "dwu_gens t' = (dwu_gens t)(Suc (dwu_hwm t) \<mapsto> UProd)
       \<and> dwu_hwm t' = Suc (dwu_hwm t) \<and> dwu_store t' = dwu_store t
       \<and> dwu_journal t' = dwu_journal t \<and> dwu_sent t' = dwu_sent t
       \<and> dwu_accepted t' = dwu_accepted t \<and> dwu_fence t' = dwu_fence t
       \<and> dwu_floor t' = dwu_floor t"
  using assms by cases auto

lemma dwu_step_release_frame:
  assumes "dwu_step t (URelease g) t'"
  shows "dwu_gens t' = dwu_gens t \<and> dwu_hwm t' = dwu_hwm t
       \<and> dwu_journal t' = dwu_journal t \<and> dwu_sent t' = dwu_sent t
       \<and> dwu_accepted t' = dwu_accepted t \<and> dwu_fence t' = dwu_fence t
       \<and> dwu_floor t' = dwu_floor t"
  using assms by cases auto

subsection \<open>2.1 S2 --- the store-frame bank: exec_base / exec_scope / exec_finish constancy, machine-wide\<close>

lemma u_dw_exec_step_finish:
  assumes "dw_exec_step s a s'"
  shows "exec_finish s' = exec_finish s"
  using assms by (induction rule: dw_exec_step.induct) simp_all

lemma u_exec_base_const:
  assumes "dwu_step t \<alpha> t'"
  shows "exec_base (dwu_store t') = exec_base (dwu_store t)"
  using assms
  by (induction rule: dwu_step.induct)
     (auto simp: relay_bounded_replay_reconcile_def truncating_crash_state_def
                 truncating_crash_state_at_boundary_def durable_exec_state_at_boundary_def
           dest: dw_exec_step_base)

lemma u_exec_scope_const:
  assumes "dwu_step t \<alpha> t'"
  shows "exec_scope (dwu_store t') = exec_scope (dwu_store t)"
  using assms
  by (induction rule: dwu_step.induct)
     (auto simp: relay_bounded_replay_reconcile_def truncating_crash_state_def
                 truncating_crash_state_at_boundary_def durable_exec_state_at_boundary_def
           dest: dw_exec_step_scope)

lemma u_exec_finish_const:
  assumes "dwu_step t \<alpha> t'"
  shows "exec_finish (dwu_store t') = exec_finish (dwu_store t)"
  using assms
  by (induction rule: dwu_step.induct)
     (auto simp: relay_bounded_replay_reconcile_def truncating_crash_state_def
                 truncating_crash_state_at_boundary_def durable_exec_state_at_boundary_def
           dest: u_dw_exec_step_finish)

subsection \<open>2.2 S3 --- journal hygiene: single writer, append-only (proved)\<close>

lemma u_journal_single_writer:
  assumes "dwu_step t \<alpha> t'"
  shows "dwu_journal t' = dwu_journal t
       \<or> (\<exists>g c e. \<alpha> = ULift g (DoSource c e)
            \<and> dwu_journal t' = dwu_journal t @ [(c, e)])"
  using assms by (induction rule: dwu_step.induct) auto

lemma u_journal_append_only:
  assumes "dwu_step t \<alpha> t'"
  shows "\<exists>js. dwu_journal t' = dwu_journal t @ js"
  using u_journal_single_writer[OF assms] by (metis append_Nil2)

text \<open>S3's u_policy_redrive clause (journal and source untouched) is definitional
  in the pinned form; named here for the record.\<close>

lemma u_policy_redrive_journal_src_same:
  assumes "u_policy_redrive P t f t'"
  shows "dwu_journal t' = dwu_journal t
       \<and> exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t)
       \<and> exec_base (dwu_store t') = exec_base (dwu_store t)"
  using assms by (simp add: u_policy_redrive_def)

subsection \<open>2.3 S6 --- dom(dwu_gens) is bounded by the high-water mark (proved)\<close>

lemma u_gens_dom_step:
  assumes "dwu_step t \<alpha> t'"
      and "dom (dwu_gens t) \<subseteq> {0..dwu_hwm t}"
  shows "dom (dwu_gens t') \<subseteq> {0..dwu_hwm t'}"
  using assms by (induction rule: dwu_step.induct) (auto split: if_splits)

lemma u_gens_dom_trace:
  assumes "dwu_temporal_trace u xs u'"
      and "dom (dwu_gens u) \<subseteq> {0..dwu_hwm u}"
  shows "dom (dwu_gens u') \<subseteq> {0..dwu_hwm u'}"
  using assms
  by (induction rule: dwu_temporal_trace.induct) (meson u_gens_dom_step)+

theorem u_gens_dom_bounded:   \<comment> \<open>S6\<close>
  assumes "dwu_reachable b K fin t"
  shows "dom (dwu_gens t) \<subseteq> {0..dwu_hwm t}"
proof -
  from assms obtain xs where xs: "dwu_temporal_trace (dwu_init b K fin) xs t"
    unfolding dwu_reachable_def by blast
  have init: "dom (dwu_gens (dwu_init b K fin)) \<subseteq> {0..dwu_hwm (dwu_init b K fin)}"
    by (simp add: dwu_init_def)
  show ?thesis by (rule u_gens_dom_trace[OF xs init])
qed

subsection \<open>2.4 S1 --- the gens fragment invariant (proved)\<close>

lemma solo_trace_gens_ok:
  assumes "solo_trace u ys zs u'"
      and "solo_gens_ok u"
  shows "solo_gens_ok u'"
  using assms
proof (induction rule: solo_trace.induct)
  case (solo_refl u)
  then show ?case .
next
  case (solo_lift u a u1 ys zs u')
  from dwu_step_lift_frame[OF solo_lift.hyps(3)] solo_lift.prems
  have "solo_gens_ok u1" by (simp add: solo_gens_ok_def)
  with solo_lift.IH show ?case by blast
next
  case (solo_reconcile g u R f m B u1 u2 u3 ys zs u')
  have arm_gens: "dwu_gens u1 = (dwu_gens u)(g \<mapsto> UArmed B)"
   and arm_hwm: "dwu_hwm u1 = dwu_hwm u"
    using dwu_step_arm_inv[OF solo_reconcile.hyps(5)] by blast+
  have heal_gens: "dwu_gens u2 = dwu_gens u1" and heal_hwm: "dwu_hwm u2 = dwu_hwm u1"
    using dwu_step_heal_frame[OF solo_reconcile.hyps(6)] by blast+
  obtain B' where fire_gens: "dwu_gens u3 = (dwu_gens u2)(g \<mapsto> UProd)"
      and fire_hwm: "dwu_hwm u3 = dwu_hwm u2"
    using dwu_step_fire_inv[OF solo_reconcile.hyps(7)] by blast
  have gu: "dwu_gens u g = Some UProd"
    using solo_reconcile.prems solo_reconcile.hyps(1)
    by (simp add: solo_gens_ok_def)
  have "dwu_gens u3 = (dwu_gens u)(g \<mapsto> UProd)"
    by (simp add: fire_gens heal_gens arm_gens)
  also have "... = dwu_gens u"
    using gu by (simp add: fun_upd_idem)
  finally have "solo_gens_ok u3"
    using solo_reconcile.prems arm_hwm heal_hwm fire_hwm
    by (simp add: solo_gens_ok_def)
  with solo_reconcile.IH show ?case by blast
next
  case (solo_turnover u u1 u2 ys zs u')
  have sp_gens: "dwu_gens u1 = (dwu_gens u)(Suc (dwu_hwm u) \<mapsto> UProd)"
   and sp_hwm: "dwu_hwm u1 = Suc (dwu_hwm u)"
    using dwu_step_spawn_inv[OF solo_turnover.hyps(1)] by blast+
  have rel_gens: "dwu_gens u2 = dwu_gens u1" and rel_hwm: "dwu_hwm u2 = dwu_hwm u1"
    using dwu_step_release_frame[OF solo_turnover.hyps(2)] by blast+
  have "solo_gens_ok u1"
    using solo_turnover.prems
    by (auto simp: solo_gens_ok_def sp_gens sp_hwm fun_eq_iff)
  then have "solo_gens_ok u2"
    by (simp add: solo_gens_ok_def rel_gens rel_hwm)
  with solo_turnover.IH show ?case by blast
qed

theorem solo_fragment_gens_invariant:   \<comment> \<open>S1\<close>
  assumes "solo_trace (dwu_init b K fin) ys zs u"
  shows "dwu_gens u = (\<lambda>g. if g \<le> dwu_hwm u then Some UProd else None)"
proof -
  have "solo_gens_ok (dwu_init b K fin)"
    by (simp add: solo_gens_ok_def dwu_init_def fun_eq_iff)
  from solo_trace_gens_ok[OF assms this] show ?thesis
    by (simp add: solo_gens_ok_def)
qed

subsection \<open>2.5 S4 --- the strengthened stamps invariant (CLOSED: per-step +
  trace + reachability, mirroring the S6 route)\<close>

text \<open>Monotonicity spine: when the ledgers and the incarnation table are frozen and
  the journal only grows, the stamps bound relaxes.\<close>

lemma u_journal_stamps_bounded_mono:
  assumes inv: "u_journal_stamps_bounded t"
      and se: "dwu_sent t' = dwu_sent t"
      and ac: "dwu_accepted t' = dwu_accepted t"
      and ge: "dwu_gens t' = dwu_gens t"
      and jl: "length (dwu_journal t) \<le> length (dwu_journal t')"
  shows "u_journal_stamps_bounded t'"
proof (unfold u_journal_stamps_bounded_def, intro conjI ballI allI impI)
  fix x assume "x \<in> set (dwu_sent t')"
  then have "x \<in> set (dwu_sent t)" by (simp add: se)
  then have "ue_stamp x \<le> length (dwu_journal t)"
    using inv by (simp add: u_journal_stamps_bounded_def)
  then show "ue_stamp x \<le> length (dwu_journal t')" using jl by (rule order_trans)
next
  fix x assume "x \<in> set (dwu_accepted t')"
  then have "x \<in> set (dwu_accepted t)" by (simp add: ac)
  then have "ue_stamp x \<le> length (dwu_journal t)"
    using inv by (simp add: u_journal_stamps_bounded_def)
  then show "ue_stamp x \<le> length (dwu_journal t')" using jl by (rule order_trans)
next
  fix g B x
  assume "dwu_gens t' g = Some (UArmed B)" and "x \<in> set B"
  then have "dwu_gens t g = Some (UArmed B)" by (simp add: ge)
  with \<open>x \<in> set B\<close> have "ue_stamp x \<le> length (dwu_journal t)"
    using inv by (simp add: u_journal_stamps_bounded_def)
  then show "ue_stamp x \<le> length (dwu_journal t')" using jl by (rule order_trans)
qed

lemma u_journal_stamps_bounded_step:
  assumes "dwu_step t \<alpha> t'"
      and "u_journal_stamps_bounded t"
  shows "u_journal_stamps_bounded t'"
  using assms
proof (induction rule: dwu_step.induct)
  case (ulift_source g t c e s')
  show ?case
    by (rule u_journal_stamps_bounded_mono[OF ulift_source.prems]) simp_all
next
  case ulift_enqueue
  then show ?case by (auto simp: u_journal_stamps_bounded_def)
next
  case ulift_ack
  then show ?case by (auto simp: u_journal_stamps_bounded_def)
next
  case ulift_publish
  then show ?case
    by (auto simp: u_journal_stamps_bounded_def split: if_splits)
next
  case ulift_nonprod
  then show ?case by (auto simp: u_journal_stamps_bounded_def)
next
  case upublost
  then show ?case
    by (auto simp: u_journal_stamps_bounded_def split: if_splits)
next
  case usnap
  then show ?case
    by (auto simp: u_journal_stamps_bounded_def split: if_splits)
next
  case uspawn
  then show ?case
    by (auto simp: u_journal_stamps_bounded_def split: if_splits)
next
  case uarm
  then show ?case
    by (auto simp: u_journal_stamps_bounded_def split: if_splits)
next
  case uarmf
  then show ?case
    by (auto simp: u_journal_stamps_bounded_def stamped_at_def split: if_splits)
next
  case uheal
  then show ?case by (auto simp: u_journal_stamps_bounded_def)
next
  case (ufire t g B)
  have B_le: "\<forall>x \<in> set B. ue_stamp x \<le> length (dwu_journal t)"
    using ufire.prems[unfolded u_journal_stamps_bounded_def] ufire.hyps by blast
  from ufire.prems B_le show ?case
    by (auto simp: u_journal_stamps_bounded_def split: if_splits)
next
  case urelease
  then show ?case by (auto simp: u_journal_stamps_bounded_def)
next
  case ufenceraise
  then show ?case by (auto simp: u_journal_stamps_bounded_def)
next
  case utrunccrash
  then show ?case by (auto simp: u_journal_stamps_bounded_def)
next
  case uretain
  then show ?case by (auto simp: u_journal_stamps_bounded_def)
qed

lemma u_journal_stamps_bounded_trace:
  assumes "dwu_temporal_trace u xs u'"
      and "u_journal_stamps_bounded u"
  shows "u_journal_stamps_bounded u'"
  using assms
  by (induction rule: dwu_temporal_trace.induct)
     (meson u_journal_stamps_bounded_step)+

theorem u_journal_stamps_bounded_invariant:   \<comment> \<open>S4\<close>
  assumes "dwu_reachable b K fin t"
  shows "u_journal_stamps_bounded t"
proof -
  from assms obtain xs where xs: "dwu_temporal_trace (dwu_init b K fin) xs t"
    unfolding dwu_reachable_def by blast
  have init: "u_journal_stamps_bounded (dwu_init b K fin)"
    by (auto simp: u_journal_stamps_bounded_def dwu_init_def)
  show ?thesis by (rule u_journal_stamps_bounded_trace[OF xs init])
qed

subsection \<open>2.6 The solo fragment embeds in the machine (U1's transport lemma, proved)\<close>

lemma solo_trace_imp_dwu_trace:
  assumes "solo_trace u ys zs u'"
  shows "dwu_temporal_trace u ys u'"
  using assms
proof (induction rule: solo_trace.induct)
  case (solo_refl u)
  show ?case by (rule dwu_temporal_trace.dwu_refl)
next
  case (solo_lift u a u1 ys zs u')
  then show ?case by (auto intro: dwu_temporal_trace.dwu_lift_step)
next
  case (solo_reconcile g u R f m B u1 u2 u3 ys zs u')
  have t3: "dwu_temporal_trace u2 (UFire g # ys) u'"
    by (rule dwu_temporal_trace.dwu_other_step
              [OF _ _ solo_reconcile.hyps(7) solo_reconcile.IH]) auto
  have t2: "dwu_temporal_trace u1 (UHeal g f # UFire g # ys) u'"
    by (rule dwu_temporal_trace.dwu_other_step[OF _ _ solo_reconcile.hyps(6) t3]) auto
  show ?case
    by (rule dwu_temporal_trace.dwu_other_step[OF _ _ solo_reconcile.hyps(5) t2]) auto
next
  case (solo_turnover u u1 u2 ys zs u')
  have t2: "dwu_temporal_trace u1 (URelease (dwu_hwm u1) # ys) u'"
    by (rule dwu_temporal_trace.dwu_other_step
              [OF _ _ solo_turnover.hyps(2) solo_turnover.IH]) auto
  show ?case
    by (rule dwu_temporal_trace.dwu_other_step[OF _ _ solo_turnover.hyps(1) t2]) auto
qed

subsection \<open>2.7 S5 --- the crashed-episode inventory (CLOSED: store/journal/base/floor
  freeze; the enumerated ledger and status motion)\<close>

text \<open>Core-step lemmas: from a Crashed store, the ONLY enabled @{const dw_exec_step}
  labels are @{term Recover} (Crashed \<rightarrow> Recovered) and @{term "Observe f"} (a no-op);
  the production/crash labels are Running-guarded and hence impossible.\<close>

lemma dwu_crashed_step_label:
  assumes "dw_exec_step s a s'"
      and "exec_status s = Crashed c"
  shows "a = Recover \<or> (\<exists>f. a = Observe f)"
  using assms by (cases rule: dw_exec_step.cases) auto

lemma dwu_crashed_step_label':
  assumes "dw_exec_step s a s'"
      and "\<exists>c. exec_status s = Crashed c"
  shows "a = Recover \<or> (\<exists>f. a = Observe f)"
  using assms by (cases rule: dw_exec_step.cases) auto

lemma dwu_crashed_core_frame':
  assumes "dw_exec_step (dwu_store t) a s'"
      and "\<exists>c. exec_status (dwu_store t) = Crashed c"
  shows "exec_src_hist s' = exec_src_hist (dwu_store t)
       \<and> exec_base s' = exec_base (dwu_store t)"
  using assms by (cases rule: dw_exec_step.cases) auto

text \<open>The @{const UHeal} relay frame: the reconcile image freezes source and base and
  moves the store to Recovered (definitional).\<close>

lemma dwu_relay_reconcile_frame:
  assumes "relay_bounded_replay_reconcile s f s'"
  shows "exec_src_hist s' = exec_src_hist s
       \<and> exec_base s' = exec_base s
       \<and> exec_status s' = Recovered"
  using assms by (simp add: relay_bounded_replay_reconcile_def)

text \<open>The non-production @{const ULift} step out of a Crashed store, packaged in the
  post-state shape of the S5a conclusion (actor @{text ga} left free; the concrete
  frontier witness @{const ec2} discharges the vacuous @{const UHeal} branch).\<close>

lemma dwu_crashed_nonprod_case:
  assumes "dw_exec_step (dwu_store t) a s'"
      and "exec_status (dwu_store t) = Crashed c"
  shows "dwu_journal (t\<lparr>dwu_store := s'\<rparr>) = dwu_journal t
       \<and> exec_src_hist (dwu_store (t\<lparr>dwu_store := s'\<rparr>)) = exec_src_hist (dwu_store t)
       \<and> exec_base (dwu_store (t\<lparr>dwu_store := s'\<rparr>)) = exec_base (dwu_store t)
       \<and> dwu_floor (t\<lparr>dwu_store := s'\<rparr>) = dwu_floor t
       \<and> (exec_status (dwu_store (t\<lparr>dwu_store := s'\<rparr>)) = Crashed c
          \<or> (\<exists>g f. (ULift ga a = UHeal g f \<or> ULift ga a = ULift g Recover)
               \<and> exec_status (dwu_store (t\<lparr>dwu_store := s'\<rparr>)) = Recovered))"
  using assms(1)
proof (cases rule: dw_exec_step.cases)
  case (recover c')
  have "\<exists>g f. (ULift ga a = UHeal g f \<or> ULift ga a = ULift g Recover)
          \<and> exec_status s' = Recovered"
    using recover by (intro exI[of _ ga] exI[of _ ec2]) simp
  then show ?thesis using recover by simp
qed (use assms(2) in simp_all)

theorem u_crashed_episode_constancy:   \<comment> \<open>S5a, P2 pin form\<close>
  assumes "exec_status (dwu_store u) = Crashed c"
      and "dwu_step u \<alpha> u'"
  shows "dwu_journal u' = dwu_journal u
       \<and> exec_src_hist (dwu_store u') = exec_src_hist (dwu_store u)
       \<and> exec_base (dwu_store u') = exec_base (dwu_store u)
       \<and> dwu_floor u' = dwu_floor u
       \<and> (exec_status (dwu_store u') = Crashed c
          \<or> (\<exists>g f. (\<alpha> = UHeal g f \<or> \<alpha> = ULift g Recover)
               \<and> exec_status (dwu_store u') = Recovered))"
  using assms(2,1)
proof (induction rule: dwu_step.induct)
  case ulift_source
  from ulift_source.hyps ulift_source.prems show ?case
    by (auto dest: dwu_crashed_step_label)
next
  case ulift_enqueue
  from ulift_enqueue.hyps ulift_enqueue.prems show ?case
    by (auto dest: dwu_crashed_step_label)
next
  case ulift_ack
  from ulift_ack.hyps ulift_ack.prems show ?case
    by (auto dest: dwu_crashed_step_label)
next
  case ulift_publish
  from ulift_publish.hyps ulift_publish.prems show ?case
    by (auto dest: dwu_crashed_step_label)
next
  case ulift_nonprod
  from dwu_crashed_nonprod_case[OF ulift_nonprod.hyps(3) ulift_nonprod.prems]
  show ?case by blast
next
  case upublost
  from upublost.hyps upublost.prems show ?case
    by (auto dest: dwu_crashed_step_label)
next
  case usnap
  from usnap.hyps usnap.prems show ?case by auto
next
  case uspawn
  from uspawn.prems show ?case by simp
next
  case uarm
  from uarm.prems show ?case by simp
next
  case uarmf
  from uarmf.prems show ?case by simp
next
  case uheal
  from dwu_relay_reconcile_frame[OF uheal.hyps] show ?case by auto
next
  case ufire
  from ufire.prems show ?case by simp
next
  case urelease
  from urelease.hyps urelease.prems show ?case by auto
next
  case ufenceraise
  from ufenceraise.prems show ?case by simp
next
  case utrunccrash
  from utrunccrash.hyps utrunccrash.prems show ?case by auto
next
  case uretain
  from uretain.hyps uretain.prems show ?case by auto
qed

theorem u_crashed_episode_ledger_motion:   \<comment> \<open>S5b, P8 amended form: NOT the landed
  full ledger freeze (UFire moves the ledgers during Crashed); store+base+journal
  frozen, ledgers append-only\<close>
  assumes "\<exists>c. exec_status (dwu_store t) = Crashed c"
      and "dwu_step t a t'"
  shows "exec_src_hist (dwu_store t') = exec_src_hist (dwu_store t)
       \<and> exec_base (dwu_store t') = exec_base (dwu_store t)
       \<and> dwu_journal t' = dwu_journal t
       \<and> (\<exists>ss. dwu_sent t' = dwu_sent t @ ss)
       \<and> (\<exists>aa. dwu_accepted t' = dwu_accepted t @ aa)"
  using assms(2,1)
proof (induction rule: dwu_step.induct)
  case ulift_source
  from ulift_source.hyps ulift_source.prems show ?case
    by (auto dest: dwu_crashed_step_label')
next
  case ulift_enqueue
  from ulift_enqueue.hyps ulift_enqueue.prems show ?case
    by (auto dest: dwu_crashed_step_label')
next
  case ulift_ack
  from ulift_ack.hyps ulift_ack.prems show ?case
    by (auto dest: dwu_crashed_step_label')
next
  case ulift_publish
  from ulift_publish.hyps ulift_publish.prems show ?case
    by (auto dest: dwu_crashed_step_label')
next
  case ulift_nonprod
  from dwu_crashed_core_frame'[OF ulift_nonprod.hyps(3) ulift_nonprod.prems]
  show ?case by (auto intro: exI[of _ "[]"])
next
  case upublost
  from upublost.hyps upublost.prems show ?case
    by (auto dest: dwu_crashed_step_label')
next
  case usnap
  from usnap.hyps usnap.prems show ?case by auto
next
  case uspawn
  show ?case by (auto intro: exI[of _ "[]"])
next
  case uarm
  show ?case by (auto intro: exI[of _ "[]"])
next
  case uarmf
  show ?case by (auto intro: exI[of _ "[]"])
next
  case uheal
  from dwu_relay_reconcile_frame[OF uheal.hyps] show ?case
    by (auto intro: exI[of _ "[]"])
next
  case (ufire t g B)
  show ?case
    by (auto intro: exI[of _ B] exI[of _ "if dwu_fence t \<le> g then B else []"])
next
  case urelease
  from urelease.hyps urelease.prems show ?case by auto
next
  case ufenceraise
  show ?case by (auto intro: exI[of _ "[]"])
next
  case utrunccrash
  from utrunccrash.hyps utrunccrash.prems show ?case by auto
next
  case uretain
  from uretain.hyps uretain.prems show ?case by auto
qed


section \<open>3. RETAINED PROVED LEMMAS (U13 snap-blindness; U16 seam/frame/turnover bank)\<close>

lemma u_duplicate_snap_blind:   \<comment> \<open>snaps are outside the raw duplicate BY CONSTRUCTOR\<close>
  "u_duplicate (t\<lparr>dwu_accepted := dwu_accepted t
                    @ [\<lparr> ue_stamp = n, ue_gen = g, ue_pay = USnap c k v \<rparr>]\<rparr>)
   \<longleftrightarrow> u_duplicate t"
  by (simp add: u_duplicate_def log_payloads_append)

text \<open>The two HARD seams (no core witness), pinned as machine-checkable statements;
  UArmF is a fence-segment boundary but expressible, so the honest hard-seam count
  is 2 (URelease inherited + UTruncCrash new).\<close>

lemma u_release_hard_seam:   \<comment> \<open>no Recovered-to-Running dw_exec_step exists\<close>
  assumes "exec_status s = Recovered"
  shows "\<not> (\<exists>a s'. dw_exec_step s a s' \<and> exec_status s' = Running)"
  using assms by (auto elim: dw_exec_step.cases)

lemma u_core_step_src_hist:
  assumes "dw_exec_step s a s'"
  shows "exec_src_hist s' = exec_src_hist s
       \<or> (\<exists>x. exec_src_hist s' = exec_src_hist s @ [x])"
  using assms by (induction rule: dw_exec_step.induct) auto

lemma u_trunccrash_hard_seam:   \<comment> \<open>a genuinely-truncating step has NO core witness\<close>
  assumes neq: "exec_src_hist (truncating_crash_state s d c) \<noteq> exec_src_hist s"
  shows "\<not> (\<exists>a. dw_exec_step s a (truncating_crash_state s d c))"
proof
  assume "\<exists>a. dw_exec_step s a (truncating_crash_state s d c)"
  then obtain a where a: "dw_exec_step s a (truncating_crash_state s d c)" by blast
  have le: "length (exec_src_hist (truncating_crash_state s d c))
              \<le> length (exec_src_hist s)"
    by (simp add: truncating_crash_state_def truncating_crash_state_at_boundary_def
                  durable_exec_state_at_boundary_def durable_history_prefix_at_def
                  length_takeWhile_le)
  from u_core_step_src_hist[OF a] neq le show False by auto
qed

text \<open>The three UTruncCrash frame lemmas the U6 machine-wide monotone consumes
  (P8's pinned truncation-segment residual: cheap frame facts, NOT live-history
  re-landing).\<close>

lemma u_trunc_ledger_frame:
  assumes "dwu_step t (UTruncCrash d c) t'"
  shows "dwu_journal t' = dwu_journal t \<and> dwu_sent t' = dwu_sent t
       \<and> dwu_accepted t' = dwu_accepted t \<and> dwu_gens t' = dwu_gens t"
  using assms by cases auto

lemma u_trunc_base_frame:
  "exec_base (truncating_crash_state s d c) = exec_base s"
  by (simp add: truncating_crash_state_def truncating_crash_state_at_boundary_def
                durable_exec_state_at_boundary_def)

lemma u_trunc_stamps_frame:
  assumes "u_journal_stamps_bounded t"
      and "dwu_step t (UTruncCrash d c) t'"
  shows "u_journal_stamps_bounded t'"
  using assms(1) u_trunc_ledger_frame[OF assms(2)]
  by (simp add: u_journal_stamps_bounded_def)

text \<open>Epoch-segment counting via the turnover pair: hwm counts exactly what
  dwe_epoch counts (B-math verified; stated as the projection-level fact).\<close>

lemma u_turnover_counts_epoch:
  assumes "dwu_step t USpawn t1"
      and "dwu_step t1 (URelease (dwu_hwm t1)) t2"
  shows "dwu_hwm t2 = Suc (dwu_hwm t) \<and> dwe_epoch (\<Pi> t2) = Suc (dwe_epoch (\<Pi> t))"
  using dwu_step_spawn_inv[OF assms(1)] dwu_step_release_frame[OF assms(2)]
  by (simp add: \<Pi>_def)

end
