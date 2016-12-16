theory SepAuto
imports Hoare_Triple
begin

subsection {* Assertions *}

theorem mod_ex_distrib_star [rewrite]: "(h \<Turnstile> (\<exists>\<^sub>Ax. P x) * Q) = (h \<Turnstile> (\<exists>\<^sub>Ax. P x * Q))"
  by (simp add: ex_distrib_star)

theorem ex_distrib_star_l:  "(\<exists>\<^sub>Ax. (Q * P x)) = (Q * (\<exists>\<^sub>Ax. P x))" by auto2

theorem pure_conj:  "\<up>(P \<and> Q) = \<up>P * \<up>Q" by auto2

theorem pure_assn_eq_same [resolve]: "P * \<up>(x = x) = P" by auto2
theorem mod_false' [resolve]: "\<not> (h \<Turnstile> false * Ru)" by auto2
theorem mod_star_true [resolve]: "h \<Turnstile> P * Ru \<Longrightarrow> h \<Turnstile> P * true"
  by (tactic {* auto2s_tac @{context} (HAVE "Ru \<Longrightarrow>\<^sub>A true") *})
theorem mod_star_true' [resolve]: "h \<Turnstile> R \<Longrightarrow> h \<Turnstile> true" by auto2
theorem mod_star_true2 [backward2]: "h \<Turnstile> P x * R \<Longrightarrow> Q x \<Longrightarrow> \<exists>x. (h \<Turnstile> P x * true) \<and> Q x"
  by (tactic {* auto2s_tac @{context} (HAVE "h \<Turnstile> P x * true") *})

subsection {* Entailment *}

theorem entails_triv: "A \<Longrightarrow>\<^sub>A A" by auto2
theorem entail_trans: "A \<Longrightarrow>\<^sub>A B \<Longrightarrow> B \<Longrightarrow>\<^sub>A C \<Longrightarrow> A \<Longrightarrow>\<^sub>A C" by auto2
theorem entail_trans2: "A \<Longrightarrow>\<^sub>A D * B \<Longrightarrow> B \<Longrightarrow>\<^sub>A C \<Longrightarrow> A \<Longrightarrow>\<^sub>A D * C"
  by (simp add: assn_times_comm entailsD' entails_def)
theorem entail_trans3: "A \<Longrightarrow>\<^sub>A B * C \<Longrightarrow> B \<Longrightarrow>\<^sub>A D \<Longrightarrow> A \<Longrightarrow>\<^sub>A D * C"
  by (simp add: entailsD' entails_def)

theorem mod_array_eq [backward1]: "xs = xs' \<Longrightarrow> h \<Turnstile> p \<mapsto>\<^sub>a xs \<Longrightarrow> h \<Turnstile> p \<mapsto>\<^sub>a xs'" by simp

subsection {* outer_remains for Arrays *}

definition outer_remains :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "outer_remains xs xs' l r = (length xs = length xs' \<and> (\<forall>i. i < l \<or> r < i \<longrightarrow> xs ! i = xs' ! i))"
setup {* add_rewrite_rule @{thm outer_remains_def} *}

subsection {* Clear unused proofsteps *}

setup {* fold del_prfstep_thm [
  @{thm ex_assn_def}, @{thm pure_assn_rule}, @{thm top_assn_rule},
  @{thm star_false_left}, @{thm entailsD'}, @{thm mod_ex_distrib_star},
  @{thm mod_pure_star_dist}, @{thm mod_pure'}] *}

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

ML_file "sep_steps.ML"
ML_file "sep_steps_test.ML"
ML_file "assn_matcher.ML"
ML_file "sep_induct.ML"

setup {* Logic_ProofSteps.add_priority_term @{const_name models} *}
attribute_setup heap_presv_thms = {* setup_attrib Sep_Logic.add_heap_preserving_thm_gnrc *}
attribute_setup forward_ent = {* setup_attrib Sep_Logic.add_forward_ent_prfstep_gnrc *}
attribute_setup hoare_create_case = {* setup_attrib Sep_Logic.add_match_hoare_create_case_gnrc *}
attribute_setup hoare_triple = {* setup_attrib Sep_Logic.add_hoare_triple_prfstep_gnrc *}
attribute_setup hoare_triple_direct = {* setup_attrib Sep_Logic.add_hoare_triple_direct_prfstep_gnrc *}

theorem basic_heap_preserving_thms [heap_presv_thms]:
  "heap_preserving (!p)"
  "heap_preserving (return x)"
  "heap_preserving (Array.nth a i)"
  "heap_preserving (Array.len a)"
by (smt effect_lookupE effect_returnE effect_nthE effect_lengthE heap_preserving_def)+

theorem heap_preserve_comment [heap_presv_thms]: "heap_preserving (comment P)"
  by (simp add: comment_def effect_def heap_preserving_def)

theorem heap_preserve_assert [heap_presv_thms]: "heap_preserving (assert P x)"
  using effect_assertE heap_preserving_def by fastforce

declare comment_rule [hoare_triple]
declare comment_rule2 [hoare_triple, hoare_create_case]
declare assert_rule [hoare_triple, hoare_create_case]
declare return_rule [hoare_triple_direct]
declare ref_rule [hoare_triple_direct]
declare lookup_rule [hoare_triple_direct]
declare update_rule [hoare_triple]
declare new_rule [hoare_triple_direct]
declare nth_rule [hoare_triple, hoare_create_case]
declare upd_rule [hoare_triple, hoare_create_case]
declare length_rule [hoare_triple_direct]

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
theorem "<a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y> comment (a \<mapsto>\<^sub>r x) <\<lambda>r. a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y>" by auto2

end
