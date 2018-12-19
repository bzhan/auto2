(*
  File: Auto2_HOL.thy
  Author: Bohua Zhan

  Main file for auto2 setup in HOL.
*)

theory Auto2_HOL
  imports HOL_Base
  keywords "@proof" :: prf_block % "proof"
    and "@have" "@case" "@obtain" "@let" "@contradiction" "@strong_induct" :: prf_decl % "proof"
    and "@unfold" :: prf_decl % "proof"
    and "@induct" "@fun_induct" "@case_induct" "@prop_induct" "@cases" :: prf_decl % "proof"
    and "@apply_induct_hyp" :: prf_decl % "proof"
    and "@subgoal" "@endgoal" "@end" :: prf_decl % "proof"
    and "@qed" :: prf_decl % "proof"
    and "@with" "where" "arbitrary" "@rule" :: quasi_command
begin

ML_file "../util.ML"
ML_file "../util_base.ML"
ML_file "auto2_hol.ML"
ML_file "../util_logic.ML"
ML_file "../box_id.ML"
ML_file "../consts.ML"
ML_file "../property.ML"
ML_file "../wellform.ML"
ML_file "../wfterm.ML"
ML_file "../rewrite.ML"
ML_file "../propertydata.ML"
ML_file "../matcher.ML"
ML_file "../items.ML"
ML_file "../wfdata.ML"
ML_file "../auto2_data.ML"
ML_file "../status.ML"
ML_file "../normalize.ML"
ML_file "../proofsteps.ML"
ML_file "../auto2_state.ML"
ML_file "../logic_steps.ML"
ML_file "../auto2.ML"
ML_file "../auto2_outer.ML"

ML_file "acdata.ML"
ML_file "ac_steps.ML"
ML_file "unfolding.ML"
ML_file "induct_outer.ML"
ML_file "extra_hol.ML"

method_setup auto2 = \<open>Scan.succeed (SIMPLE_METHOD o Auto2.auto2_tac)\<close> "auto2 prover"

attribute_setup forward = \<open>setup_attrib add_forward_prfstep\<close>
attribute_setup backward = \<open>setup_attrib add_backward_prfstep\<close>
attribute_setup backward1 = \<open>setup_attrib add_backward1_prfstep\<close>
attribute_setup backward2 = \<open>setup_attrib add_backward2_prfstep\<close>
attribute_setup resolve = \<open>setup_attrib add_resolve_prfstep\<close>
attribute_setup rewrite = \<open>setup_attrib add_rewrite_rule\<close>
attribute_setup rewrite_back = \<open>setup_attrib add_rewrite_rule_back\<close>
attribute_setup rewrite_bidir = \<open>setup_attrib add_rewrite_rule_bidir\<close>
attribute_setup forward_arg1 = \<open>setup_attrib add_forward_arg1_prfstep\<close>
attribute_setup forward_arg = \<open>setup_attrib add_forward_arg_prfstep\<close>
attribute_setup rewrite_arg = \<open>setup_attrib add_rewrite_arg_rule\<close>

end
