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

method_setup auto2 = {* Scan.succeed (SIMPLE_METHOD o Auto2.auto2_tac) *} "auto2 prover"

attribute_setup forward = {* setup_attrib add_forward_prfstep *}
attribute_setup backward = {* setup_attrib add_backward_prfstep *}
attribute_setup backward1 = {* setup_attrib add_backward1_prfstep *}
attribute_setup backward2 = {* setup_attrib add_backward2_prfstep *}
attribute_setup resolve = {* setup_attrib add_resolve_prfstep *}
attribute_setup rewrite = {* setup_attrib add_rewrite_rule *}
attribute_setup rewrite_back = {* setup_attrib add_rewrite_rule_back *}
attribute_setup rewrite_bidir = {* setup_attrib add_rewrite_rule_bidir *}
attribute_setup forward_arg1 = {* setup_attrib add_forward_arg1_prfstep *}
attribute_setup forward_arg = {* setup_attrib add_forward_arg_prfstep *}
attribute_setup rewrite_arg = {* setup_attrib add_rewrite_arg_rule *}

end
