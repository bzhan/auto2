(* Auto2 tactic. *)

theory Auto2_Base
imports Logic_Base
begin

(* Theorem lists for auto2. *)
named_theorems property_rewrites "Auto2: rewriting theorems to properties"

ML_file "util.ML"
ML_file "util_logic.ML"
ML_file "box_id.ML"
ML_file "acdata.ML"
ML_file "subterms.ML"
ML_file "property.ML"
ML_file "rewrite.ML"
ML_file "matcher.ML"
ML_file "status.ML"
ML_file "normalize.ML"
ML_file "proofsteps.ML"
ML_file "script.ML"
ML_file "auto2.ML"
ML_file "induction.ML"
ML_file "ac_steps.ML"
ML_file "logic_steps.ML"

ML_file "auto2_hol.ML"

method_setup auto2 = {* Scan.succeed (SIMPLE_METHOD o auto2_tac) *} "auto2 prover"

attribute_setup forward = {* setup_attrib add_forward_prfstep_gnrc *}
attribute_setup backward = {* setup_attrib add_backward_prfstep_gnrc *}
attribute_setup backward1 = {* setup_attrib add_backward1_prfstep_gnrc *}
attribute_setup backward2 = {* setup_attrib add_backward2_prfstep_gnrc *}
attribute_setup resolve = {* setup_attrib add_resolve_prfstep_gnrc *}
attribute_setup rewrite = {* setup_attrib add_rewrite_rule_gnrc *}
attribute_setup rewrite_back = {* setup_attrib add_rewrite_rule_back_gnrc *}
attribute_setup rewrite_bidir = {* setup_attrib add_rewrite_rule_bidir_gnrc *}

end
