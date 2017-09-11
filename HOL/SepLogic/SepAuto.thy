theory SepAuto
imports Hoare_Triple
keywords "@hoare_induct" :: prf_decl % "proof"
begin

subsection {* Assertions *}

theorem pure_conj:  "\<up>(P \<and> Q) = \<up>P * \<up>Q" by auto2
theorem mod_false' [resolve]: "\<not> (h \<Turnstile> false * Ru)" by auto2

subsection {* Entailment *}

theorem entails_true: "A \<Longrightarrow>\<^sub>A true" by auto2
theorem entail_equiv_forward: "P = Q \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q" by auto2
theorem entail_equiv_backward: "P = Q \<Longrightarrow> Q \<Longrightarrow>\<^sub>A P" by auto2
theorem entailsD_back: "P \<Longrightarrow>\<^sub>A Q \<Longrightarrow> \<not>h \<Turnstile> Q * R \<Longrightarrow> \<not>h \<Turnstile> P * R" by auto2
theorem entails_triv: "A \<Longrightarrow>\<^sub>A A" by auto2
theorem entail_trans2: "A \<Longrightarrow>\<^sub>A D * B \<Longrightarrow> B \<Longrightarrow>\<^sub>A C \<Longrightarrow> A \<Longrightarrow>\<^sub>A D * C"
  by (simp add: assn_times_comm entailsD' entails_def)
theorem entail_trans2': "D * B \<Longrightarrow>\<^sub>A A \<Longrightarrow> C \<Longrightarrow>\<^sub>A B \<Longrightarrow> D * C \<Longrightarrow>\<^sub>A A"
  by (simp add: assn_times_comm entailsD' entails_def)
theorem entails_invD: "A \<Longrightarrow>\<^sub>A B \<Longrightarrow> \<not>(h \<Turnstile> B) \<Longrightarrow> \<not>(h \<Turnstile> A)"
  using entailsD by blast

theorem mod_array_eq [backward1]: "xs = xs' \<Longrightarrow> h \<Turnstile> p \<mapsto>\<^sub>a xs \<Longrightarrow> h \<Turnstile> p \<mapsto>\<^sub>a xs'" by simp

subsection {* outer_remains for Arrays *}

definition outer_remains :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "outer_remains xs xs' l r = (length xs = length xs' \<and> (\<forall>i. i < l \<or> r < i \<longrightarrow> xs ! i = xs' ! i))"
setup {* add_rewrite_rule @{thm outer_remains_def} *}

subsection {* Clear unused proofsteps *}

setup {* fold del_prfstep_thm [
  @{thm mod_ex_dist}, @{thm ex_assn_def}, @{thm pure_assn_rule}, @{thm top_assn_rule},
  @{thm star_false_left}, @{thm entailsD'}, @{thm mod_pure_star_dist}, @{thm mod_pure'}] *}

subsection {* Definition of procedures *}

named_theorems sep_proc_defs "Seplogic: definitions of procedures"
named_theorems sep_prec_thms "Seplogic: precision theorems"
(* Note adding to sep_heap_presv_thms is taken care of by heap_presv_thms attribute. *)
named_theorems sep_heap_presv_thms "Seplogic: heap preservation theorems"

declare ref_prec [sep_prec_thms]
declare array_ref_prec [sep_prec_thms]

(* ASCII abbreviations for ML files. *)
abbreviation (input) ex_assn_ascii :: "('a \<Rightarrow> assn) \<Rightarrow> assn" (binder "EXA" 11)
  where "ex_assn_ascii \<equiv> ex_assn"

abbreviation (input) models_ascii :: "pheap \<Rightarrow> assn \<Rightarrow> bool" (infix "|=" 50)
  where "h |= P \<equiv> h \<Turnstile> P"

ML_file "sep_util.ML"
ML_file "assn_matcher.ML"
ML_file "sep_steps.ML"
ML_file "sep_steps_test.ML"
ML_file "sep_induct.ML"

attribute_setup heap_presv_thms = {* setup_attrib add_heap_preserving_thm *}
attribute_setup forward_ent = {* setup_attrib add_forward_ent_prfstep *}
attribute_setup forward_ent_shadow = {* setup_attrib add_forward_ent_shadowing_prfstep *}
attribute_setup rewrite_ent = {* setup_attrib add_rewrite_ent_rule *}
attribute_setup hoare_create_case = {* setup_attrib add_match_hoare_create_case *}
attribute_setup hoare_triple = {* setup_attrib add_hoare_triple_prfstep *}
attribute_setup hoare_triple_direct = {* setup_attrib add_hoare_triple_direct_prfstep *}

lemma heap_preserving_lookup [heap_presv_thms]: "heap_preserving (!p)"
  using effect_lookupE heap_preserving_def by fastforce

lemma heap_preserving_return [heap_presv_thms]: "heap_preserving (return x)"
  using effect_returnE heap_preserving_def by fastforce

lemma heap_preserving_nth [heap_presv_thms]: "heap_preserving (Array.nth a i)"
  using effect_nthE heap_preserving_def by fastforce

lemma heap_preserving_len [heap_presv_thms]: "heap_preserving (Array.len a)"
  using effect_lengthE heap_preserving_def by fastforce

lemma heap_preserve_assert [heap_presv_thms]: "heap_preserving (assert P x)"
  using effect_assertE heap_preserving_def by fastforce

setup {* fold add_hoare_triple_prfstep [
  @{thm assert_rule}, @{thm update_rule}, @{thm nth_rule}, @{thm upd_rule}] *}

setup {* fold add_match_hoare_create_case [
  @{thm assert_rule}, @{thm nth_rule}, @{thm upd_rule}] *}

setup {* fold add_hoare_triple_direct_prfstep [
  @{thm return_rule}, @{thm ref_rule}, @{thm lookup_rule}, @{thm new_rule},
  @{thm of_list_rule}, @{thm length_rule}] *}

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
