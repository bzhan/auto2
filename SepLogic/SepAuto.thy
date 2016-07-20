theory SepAuto
imports Hoare_Triple
begin

subsection {* Assertions *}

theorem mod_ex_distrib_star [rewrite]: "(h \<Turnstile> (\<exists>\<^sub>Ax. P x) * Q) = (h \<Turnstile> (\<exists>\<^sub>Ax. P x * Q))"
  by (simp add: ex_distrib_star)

theorem ex_distrib_star_l:
  "(\<exists>\<^sub>Ax. (Q * P x)) = (Q * (\<exists>\<^sub>Ax. P x))" by auto2

theorem pure_assn_eq_same [resolve]: "P * \<up>(x = x) = P" by auto2
theorem mod_false' [resolve]: "\<not> (h \<Turnstile> false * Ru)" by auto2
theorem mod_star_true [resolve]: "h \<Turnstile> P * Ru \<Longrightarrow> h \<Turnstile> P * true"
  by (tactic {* auto2s_tac @{context} (OBTAIN "Ru \<Longrightarrow>\<^sub>A true") *})
theorem mod_star_true' [resolve]: "h \<Turnstile> R \<Longrightarrow> h \<Turnstile> true" by auto2

subsection {* Clear unused proofsteps *}

setup {* fold del_prfstep_thm [
  @{thm ex_assn_def}, @{thm pure_assn_rule}, @{thm top_assn_rule},
  @{thm star_false_left}, @{thm entailsD'}, @{thm mod_ex_distrib_star}] *}
setup {* fold del_prfstep [
  "Assertions.mod_pure_star_dist", "Assertions.mod_pure'"] *}

subsection {* Definition of procedures *}

named_theorems sep_proc_defs "Seplogic: definitions of procedures"
named_theorems sep_prec_thms "Seplogic: precision theorems"
named_theorems sep_heap_presv_thms "Seplogic: heap preservation theorems"

declare ref_prec [sep_prec_thms]
declare array_ref_prec [sep_prec_thms]

(* ASCII abbreviations for ML files. *)
abbreviation ex_assn_ascii :: "('a \<Rightarrow> assn) \<Rightarrow> assn" (binder "EXA" 11)
  where "ex_assn_ascii \<equiv> ex_assn"

abbreviation models_ascii :: "pheap \<Rightarrow> assn \<Rightarrow> bool" (infix "|=" 50)
  where "h |= P \<equiv> h \<Turnstile> P"

ML_file "sep_steps.ML"
ML_file "sep_steps_test.ML"

attribute_setup heap_presv_thms = {* setup_attrib Sep_Logic.add_heap_preserving_thm *}
attribute_setup forward_ent = {* setup_attrib Sep_Logic.add_forward_ent_prfstep_ctxt *}
attribute_setup match_code_pos_emp = {* setup_attrib Sep_Logic.add_match_code_pos_emp_prfstep_ctxt *}
attribute_setup code_pos_create_case = {* setup_attrib Sep_Logic.add_match_code_pos_create_case_ctxt *}
attribute_setup next_code_pos = {* setup_attrib Sep_Logic.add_next_code_pos_prfstep_ctxt *}
attribute_setup next_code_pos_direct = {* setup_attrib Sep_Logic.add_next_code_pos_direct_prfstep_ctxt *}

theorem basic_heap_preserving_thms [sep_heap_presv_thms, heap_presv_thms]:
  "heap_preserving (!p)"
  "heap_preserving (return x)"
  "heap_preserving (Array.nth a i)"
  "heap_preserving (Array.len a)"
by (smt effect_lookupE effect_returnE effect_nthE effect_lengthE heap_preserving_def)+

setup {* add_next_code_pos_direct_prfstep @{thm return_rule} *}
setup {* add_next_code_pos_prfstep @{thm ref_rule} *}
setup {* add_next_code_pos_direct_prfstep @{thm lookup_rule} *}
setup {* add_next_code_pos_prfstep @{thm update_rule} *}
setup {* add_next_code_pos_prfstep @{thm new_rule} *}
setup {* add_next_code_pos_prfstep @{thm nth_rule} *}
declare nth_rule [code_pos_create_case]
setup {* add_next_code_pos_prfstep @{thm upd_rule} *}
declare upd_rule [code_pos_create_case]
setup {* add_next_code_pos_direct_prfstep @{thm length_rule} *}

(* Some simple tests *)

theorem "<emp> ref x <\<lambda>r. r \<mapsto>\<^sub>r x>" by auto2
theorem "<a \<mapsto>\<^sub>r x> ref x <\<lambda>r. a \<mapsto>\<^sub>r x * r \<mapsto>\<^sub>r x>" by auto2
theorem "<a \<mapsto>\<^sub>r x> (!a) <\<lambda>r. a \<mapsto>\<^sub>r x * \<up>(r = x)>" by auto2
theorem "<a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y> (!a) <\<lambda>r. a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y * \<up>(r = x)>" by auto2
theorem "<a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y> (!b) <\<lambda>r. a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y * \<up>(r = y)>" by auto2
theorem "<a \<mapsto>\<^sub>r x> do { a := y; !a } <\<lambda>r. a \<mapsto>\<^sub>r y * \<up>(r = y)>" by auto2
theorem "<a \<mapsto>\<^sub>r x> do { a := y; a := z; !a } <\<lambda>r. a \<mapsto>\<^sub>r z * \<up>(r = z)>" by auto2
theorem "<a \<mapsto>\<^sub>r x> do { y \<leftarrow> !a; ref y} <\<lambda>r. a \<mapsto>\<^sub>r x * r \<mapsto>\<^sub>r x>" by auto2
theorem "<emp> return x <\<lambda>r. \<up>(r = x)>" by auto2

end
