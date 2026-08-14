(*  Title:       DWU_Modality.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Purpose: Road-2 I6 --- U13 THE MODALITY BANK: three theorems that ride the
             already-landed facts of the unified machine (no new vocabulary).

    "Honest snap justification survives every later step; adding honest snaps to a
     disciplined run cannot break effect-safety; and the log-only fragment recovers
     the landed duplicate reading EXACTLY."

    Three principals, byte-identical to the Stage-4 seed
    (ref/road2_clean_slate/probe/DWU_Statement_Probe.thy, section U13):

      (U13a) u_snap_honesty_append_stable  --- machine-wide justification
             append-stability.  Both justification modes (ULog / USnap) are frozen
             by journal-append-only (S3, u_journal_append_only) together with
             exec_base constancy (S2, u_exec_base_const): the stamped journal prefix
             and the execution base survive every rule, so u_justified transports
             verbatim.  This is the landed justified_at_append_stable pattern lifted
             to the unified u_justified surface.

      (U13b) u_mixed_stream_discipline_safe  --- a direct corollary of the U8 safety
             headliner u_fenced_multiwriter_discipline_safe, whose discipline grammar
             already admits USnapE steps (the ud_snap case).  The USnapE-present
             premise names the "mixed streams" scenario and is not consumed: adding
             honest snaps to a disciplined run cannot make it effect-unsafe.
             Scope, explicit: effect-safety's duplicate reading is log-only
             by constructor (u_duplicate_snap_blind at I0) --- repeated
             identical honest snapshots are accepted and are not graded as
             duplicates.  The theorem prices snapshot HONESTY under
             interference, not snapshot multiplicity.

      (U13c) u_log_only_projection_no_weakening  --- on a log-only, ledger-equal state
             the unified duplicate reading and the landed duplicate reading of the
             projection Pi coincide, as an exact list-equality via
             map_e_payload_Pi_emitted.  The premises are STRICTLY WEAKER than
             u_hazards_once (no journal = source premise): the duplicate reading never
             needed it.

    DEFINES NOTHING: all vocabulary is landed (u_duplicate_snap_blind is already at I0
    and is NOT re-declared here).

    Honesty regime: quick_and_dirty = false (ROOT-pinned); no unfinished-proof
    markers, no new axioms, no free-standing constant declarations, no external
    trust appeals.  Every principal fully PROVED.
*)

theory DWU_Modality
  imports DWU_Fenced_Discipline
begin

section \<open>U13 --- the modality bank (seed section U13, VERBATIM statements)\<close>

text \<open>U13a (P7): machine-wide justification append-stability.  @{const u_justified}
  reads the stamped journal prefix @{term "take (ue_stamp x) (dwu_journal t)"} and,
  in the USnap mode, the execution base @{term "exec_base (dwu_store t)"}.  Every rule
  either leaves the journal or appends to it (S3) and none touches @{const exec_base}
  (S2), so with @{term "ue_stamp x \<le> length (dwu_journal t)"} the prefix and the base
  are frozen and both justification clauses transport unchanged.\<close>

theorem u_snap_honesty_append_stable:   \<comment> \<open>U13a, upgraded MACHINE-WIDE (P7): both
  justification modes are frozen by journal-append-only + exec_base constancy\<close>
  assumes "u_justified t x"
      and "dwu_step t \<alpha> t'"
  shows "u_justified t' x"
proof -
  from u_journal_append_only[OF assms(2)]
  obtain js where js: "dwu_journal t' = dwu_journal t @ js" ..
  from assms(1) have stamp: "ue_stamp x \<le> length (dwu_journal t)"
    by (simp add: u_justified_def)
  have take_eq: "take (ue_stamp x) (dwu_journal t') = take (ue_stamp x) (dwu_journal t)"
    using stamp by (simp add: js)
  have len': "ue_stamp x \<le> length (dwu_journal t')"
    using stamp by (simp add: js)
  have base: "exec_base (dwu_store t') = exec_base (dwu_store t)"
    by (rule u_exec_base_const[OF assms(2)])
  show "u_justified t' x"
  proof (cases "ue_pay x")
    case (ULog p)
    with assms(1) show ?thesis
      by (simp add: u_justified_def take_eq len' base)
  next
    case (USnap c k v)
    with assms(1) show ?thesis
      by (simp add: u_justified_def take_eq len' base)
  qed
qed

text \<open>U13b (P7): the U8 discipline with honest snaps present stays effect-safe.  This
  is the U8 safety headliner @{thm [source] u_fenced_multiwriter_discipline_safe}
  applied to the same disciplined trace; the discipline grammar's @{text ud_snap} case
  already admits @{term "USnapE g c k v"} steps, so the USnapE-present premise
  @{term "\<exists>g c k v. USnapE g c k v \<in> set acts"} is narrative (it names the mixed-stream
  scenario) and is not needed for the conclusion.\<close>

theorem u_mixed_stream_discipline_safe:   \<comment> \<open>U13b: the U8 discipline with honest
  snaps present stays effect-safe (the scope rides D5 in the bundle)\<close>
  assumes "u_disciplined_trace (dwu_init b K fin) acts t"
      and "\<exists>g c k v. USnapE g c k v \<in> set acts"
  shows "\<not> u_effect_unsafe t"
  by (rule u_fenced_multiwriter_discipline_safe[OF assms(1)])

text \<open>U13c (P7): the log-only fragment recovers the landed duplicate reading EXACTLY.
  @{const u_duplicate} reads @{term "log_payloads (dwu_accepted t)"}; @{const duplicate}
  of @{term "\<Pi> t"} reads @{term "map e_payload (dwe_emitted (\<Pi> t))"}, which is
  UNCONDITIONALLY @{term "log_payloads (dwu_sent t)"} (@{thm [source] map_e_payload_\<Pi>_emitted});
  the ledger-equality @{term "dwu_sent t = dwu_accepted t"} closes the gap.  This is the
  internal @{text dup} sub-proof of @{thm [source] u_hazards_once} at its WEAKER premises:
  the duplicate reading needs only @{term "dwu_sent t = dwu_accepted t"} --- neither the
  journal = source premise nor even the all-ULog premise is consumed.\<close>

theorem u_log_only_projection_no_weakening:   \<comment> \<open>U13c: the log-only fragment recovers
  the landed duplicate reading EXACTLY\<close>
  assumes "dwu_sent t = dwu_accepted t"
      and "\<forall>x \<in> set (dwu_sent t). is_ulog x"
  shows "u_duplicate t \<longleftrightarrow> duplicate (\<Pi> t)"
  by (simp add: u_duplicate_def duplicate_def map_e_payload_\<Pi>_emitted assms(1))

end
