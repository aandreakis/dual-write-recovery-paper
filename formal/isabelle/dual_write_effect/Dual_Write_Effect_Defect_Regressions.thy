(*  Title:       Dual_Write_Effect_Defect_Regressions.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Permanent kernel-checked regressions for retained effect-tier defects.
    The witness below deliberately uses the forbidden base coordinate c0:
    the raw step exists, while the guarded wrapper trace must reject it.

    The external report defining the D-numbering is archived verbatim in
    the development repository at
    sink_and_fence/reviews/incoming/R07_isabelle_defect_report.md.
*)

theory Dual_Write_Effect_Defect_Regressions
  imports
    Dual_Write_Effect_Converse
    Dual_Write_Effect_Segment_Boundaries
begin

section \<open>D8 regression: canonical implementation rejects a wrapper-invalid label\<close>

definition d8_t0 :: "(nat, nat) dwe_state" where
  "d8_t0 = dwe_init Map.empty {0} ec1"

definition d8_t1 :: "(nat, nat) dwe_state" where
  "d8_t1 =
     d8_t0\<lparr>dwe_core :=
       (dwe_core d8_t0)\<lparr>exec_src_hist :=
         exec_src_hist (dwe_core d8_t0) @ [(c0, Insert 0 7)]\<rparr>\<rparr>"

lemma d8_raw_wrapper_step:
  "dwe_step d8_t0 (DoSource c0 (Insert 0 7)) d8_t1"
  unfolding d8_t1_def
  apply (rule dwe_step.lift_nonpub)
   apply (rule dw_exec_step.do_source)
   apply (simp add: d8_t0_def dwe_init_def initial_exec_state_def)
  apply simp
  done

lemma d8_guard_rejects:
  "\<not> exec_label_preserves_history_wf
       (dwe_core d8_t0) (DoSource c0 (Insert 0 7))"
  by (simp add: d8_t0_def dwe_init_def initial_exec_state_def
                exec_label_preserves_history_wf_def history_can_append_def)

lemma d8_canonical_rejects_invalid_label:
  "\<not> dwei_step (canonical_dwe_implementation d8_t0) d8_t0
     (DWE_Label (DoSource c0 (Insert 0 7))) d8_t1"
  using d8_guard_rejects
  by (simp add: canonical_dwe_implementation_def)

lemma d8_segment_carrier_rejects_invalid_label:
  "\<not> dwi_step (guarded_segment_implementation d8_t0) d8_t0
     (DoSource c0 (Insert 0 7)) d8_t1"
  using d8_guard_rejects
  by (simp add: guarded_segment_implementation_def)

lemma d8_guarded_trace_rejects:
  "\<not> dwe_temporal_trace d8_t0
       [DWE_Label (DoSource c0 (Insert 0 7))] d8_t1"
proof
  assume tr:
    "dwe_temporal_trace d8_t0
       [DWE_Label (DoSource c0 (Insert 0 7))] d8_t1"
  from tr d8_guard_rejects show False
    by (cases rule: dwe_temporal_trace.cases) auto
qed

text \<open>The underlying raw core implementation accepts the same step.  This
  is the strict overapproximation that a wrapper-segment characterization
  must not package as its operational implementation.\<close>

lemma d8_raw_core_overapproximation:
  "dwi_trace (canonical_dw_implementation (dwe_core d8_t0))
     (dwi_initial (canonical_dw_implementation (dwe_core d8_t0)))
     [DoSource c0 (Insert 0 7)] (dwe_core d8_t1)"
proof -
  have raw:
    "dw_exec_step (dwe_core d8_t0) (DoSource c0 (Insert 0 7))
       (dwe_core d8_t1)"
    using d8_raw_wrapper_step by (rule dwe_step_core)
  have step:
    "dwi_step (canonical_dw_implementation (dwe_core d8_t0))
       (dwe_core d8_t0) (DoSource c0 (Insert 0 7)) (dwe_core d8_t1)"
    using raw by (simp add: canonical_dw_implementation_def)
  have init:
    "dwi_initial (canonical_dw_implementation (dwe_core d8_t0))
       = dwe_core d8_t0"
    by (simp add: canonical_dw_implementation_def)
  show ?thesis
    unfolding init
    by (rule dwi_trace.dwi_trace_step[OF step
              dwi_trace.dwi_trace_refl])
qed

end
