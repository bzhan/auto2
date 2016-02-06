theory Auto2_Base
imports Main Logic_Base
begin

ML_file "util.ML"
ML_file "box_id.ML"
ML_file "acdata.ML"
ML_file "subterms.ML"
ML_file "rewrite.ML"
ML_file "status.ML"
ML_file "normalize.ML"
ML_file "proofsteps.ML"
ML_file "script.ML"
ML_file "auto2.ML"
ML_file "induction.ML"

method_setup auto2 = {* Scan.succeed (SIMPLE_METHOD o auto2_tac) *} "auto2 prover"

text {* First add proofstep converting any PROP equality to EQ. Then use EQ to match
  equality in all proofsteps. *}
theorem trivial_eq: "A = B \<Longrightarrow> A = B" by simp
setup {* add_gen_prfstep ("trivial_eq",
  [WithItem (TY_PROP, @{term_pat "(?A::?'a) = ?B"}),
   GetFact (@{term_pat "(?A::?'a) = ?B"}, @{thm trivial_eq})]) *}

attribute_setup known_fact = {* setup_attrib add_known_fact_ctxt *}
attribute_setup forward = {* setup_attrib add_forward_prfstep_ctxt *}
attribute_setup backward = {* setup_attrib add_backward_prfstep_ctxt *}
attribute_setup backward1 = {* setup_attrib add_backward1_prfstep_ctxt *}
attribute_setup backward2 = {* setup_attrib add_backward2_prfstep_ctxt *}
attribute_setup resolve = {* setup_attrib add_resolve_prfstep_ctxt *}
attribute_setup rewrite = {* setup_attrib add_rewrite_rule_ctxt *}
attribute_setup rewrite_back = {* setup_attrib add_rewrite_rule_back_ctxt *}
attribute_setup rewrite_bidir = {* setup_attrib add_rewrite_rule_bidir_ctxt *}

end
