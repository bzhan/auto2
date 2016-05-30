theory Prelim_Thms
imports "~~/src/HOL/Library/FuncSet" "../Auto2"
begin

(* Membership *)
setup {* fold add_forward_prfstep [@{thm Set.IntD1}, @{thm Set.IntD2}] *}

(* Subset *)
setup {* add_forward_prfstep @{thm Set.subsetI} *}
theorem set_order_antisym [backward2]: "(A::('a set)) \<subseteq> B \<Longrightarrow> B \<subseteq> A \<Longrightarrow> A = B" by auto2
theorem subset_Union [backward]: "\<forall>t\<in>T. \<exists>s\<in>S. t \<in> s \<Longrightarrow> T \<subseteq> (\<Union>S)" by auto
theorem Union_subset [backward]: "\<forall>s\<in>S. s \<subseteq> T \<Longrightarrow> (\<Union>S) \<subseteq> T" by auto
theorem BUnion_subset [backward]: "\<forall>x\<in>A. f x \<in> T \<Longrightarrow> (\<Union>x\<in>A. {f x}) \<subseteq> T" by auto

(* Set comprehension *)
theorem set_comprehensionI [backward]: "x \<in> A \<Longrightarrow> f x \<in> (\<Union>x\<in>A. {f x})" by auto
theorem set_comprehensionD [resolve]: "y \<in> (\<Union>x\<in>A. {f x}) \<Longrightarrow> \<exists>x\<in>A. y = f x" by auto
theorem set_comprehensionI2 [backward2]: "x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> f x y \<in> (\<Union>x\<in>A. \<Union>y\<in>B. {f x y})" by auto
theorem set_comprehensionD2 [resolve]: "z \<in> (\<Union>x\<in>A. \<Union>y\<in>B. {f x y}) \<Longrightarrow> \<exists>x\<in>A. \<exists>y\<in>B. z = f x y" by auto

(* THE and \<exists>! *)
setup {* add_forward_prfstep_cond @{thm theI'} [with_term "THE x. ?P x"] *}
setup {* add_backward_prfstep @{thm HOL.ex_ex1I} *}

(* Property of bijection *)
setup {* add_forward_prfstep @{thm Fun.bij_betw_imp_inj_on} *}
setup {* add_forward_prfstep @{thm bij_betw_imp_surj_on} *}
setup {* add_backward2_prfstep @{thm bij_betw_imageI} *}
setup {* add_backward_prfstep (equiv_backward_th @{thm inj_on_def}) *}
theorem surj_onI [backward1]: "\<forall>x\<in>A. f x \<in> B \<Longrightarrow> \<forall>y\<in>B. \<exists>x\<in>A. f x = y \<Longrightarrow> f ` A = B" by auto

theorem bij_betw_identity [resolve]: "bij_betw (\<lambda>x. x) X X" by (simp add: bij_betw_def)
setup {* add_backward_prfstep @{thm bij_betw_inv_into} *}
setup {* add_backward2_prfstep @{thm bij_betw_compose} *}

(* Finite sets *)
setup {* add_rewrite_rule @{thm finite_Pow_iff} *}
setup {* add_backward2_prfstep @{thm finite_subset} *}
setup {* add_backward2_prfstep @{thm finite_UN_I} *}

(* Cardinality of sets *)
setup {* add_resolve_prfstep @{thm bij_betw_same_card} *}
setup {* add_backward1_prfstep @{thm card_partition} *}

end
