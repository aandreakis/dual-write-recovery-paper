(*  Title:       Layer3_Defect_Regressions.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Permanent kernel-checked regressions for retained Layer-3 fixture
    defects.  The same-evidence fixture must reach accessor comparison;
    failure of materialization is a confounder, not an accessor test.

    The external report defining the D-numbering is archived verbatim in
    the development repository at
    sink_and_fence/reviews/incoming/R07_isabelle_defect_report.md.
*)

theory Layer3_Defect_Regressions
  imports Layer3_Fixtures_Inst
begin

section \<open>D15 regression: the accessor fixture reaches comparison\<close>

lemma d15_accessor_mismatch_is_present:
  "\<not> cf.cert_accessors_agree CAcc ()"
  unfolding cf.cert_accessors_agree_def
  by (simp add: cf_clean_prefix_empty)

lemma d15_materializes_then_fails_accessor_agreement:
  "l3f_verify CAcc EAcc = Accept
   \<and> l3f_materializes CAcc EAcc ()
   \<and> \<not> cf.cert_accessors_agree CAcc ()
   \<and> \<not> cf.cert_run_coherent CAcc EAcc ()"
  unfolding cf.cert_run_coherent_def
  using d15_accessor_mismatch_is_present by simp

end
