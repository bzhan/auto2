(* Setup of proof steps related to sets. *)

theory Set_Thms
imports Auto2_Base "~~/src/HOL/Library/Multiset"
begin

section {* Set *}

subsection {* AC property of intersection and union *}

ML {*
val add_set_ac_data =
  fold ACUtil.add_ac_data [
    {fname = @{const_name inf}, assoc_r = false,
     assoc_th = @{thm Int_ac(1)}, comm_th = @{thm Int_ac(3)},
     unit_val = @{term UNIV}, unit_th = @{thm Set.Int_UNIV_left}, unitr_th = true_th,
     uinv_name = "", inv_name = "", double_inv_th = true_th,
     distr_inv_th = true_th, binop_inv_th = true_th, unit_inv_th = true_th},

    {fname = @{const_name sup}, assoc_r = false,
     assoc_th = @{thm Un_ac(1)}, comm_th = @{thm Un_ac(3)},
     unit_val = @{term "{}"}, unit_th = @{thm Set.Un_empty_left}, unitr_th = true_th,
     uinv_name = "", inv_name = "", double_inv_th = true_th,
     distr_inv_th = true_th, binop_inv_th = true_th, unit_inv_th = true_th}]
*}
setup {* add_set_ac_data *}

subsection {* Collection and bounded quantification *}
setup {* add_rewrite_rule @{thm Set.mem_Collect_eq} *}
setup {* add_forward_prfstep (equiv_forward_th @{thm Ball_def}) *}
setup {* add_backward_prfstep (equiv_backward_th @{thm Ball_def}) *}
theorem ball_subset [forward]: "\<forall>x\<in>s. P x \<Longrightarrow> t \<subseteq> s \<Longrightarrow> \<forall>x\<in>t. P x" by auto
setup {* add_forward_prfstep_cond (equiv_forward_th @{thm Set.ball_Un})
  [with_filt (canonical_split_filter @{const_name sup} "A" "B")] *}
theorem set_ball_Un_backward [forward]: "\<forall>x\<in>A. P x \<Longrightarrow> \<not>(\<forall>x\<in>A\<union>B. P x) \<Longrightarrow> \<not>(\<forall>x\<in>B. P x)" by auto
setup {* add_rewrite_rule @{thm Set.ball_empty} *}
theorem ball_single [rewrite]: "(\<forall>x\<in>{x}. P x) = P x" by auto

subsection {* Membership *}
setup {* add_forward_prfstep @{thm Set.singletonD} *}
theorem set_notin_singleton [forward]: "x \<notin> {v} \<Longrightarrow> x \<noteq> v" by simp
setup {* add_forward_prfstep (equiv_forward_th @{thm Set.empty_iff}) *}
theorem set_membership_distinct [forward]: "x \<in> s \<Longrightarrow> y \<notin> s \<Longrightarrow> x \<noteq> y" by auto
theorem non_empty_exist_elt [backward]: "U \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> U" by blast
theorem non_univ_exist_compl [backward]: "U \<noteq> UNIV \<Longrightarrow> \<exists>x. x \<notin> U" by blast
theorem univ_member_all [resolve]: "U = UNIV \<Longrightarrow> x \<in> U" by simp

subsection {* Union *}
theorem set_not_in_union: "x \<notin> A \<union> B \<Longrightarrow> x \<notin> A \<and> x \<notin> B" by auto
setup {* add_forward_prfstep_cond @{thm set_not_in_union}
  [with_filt (canonical_split_filter @{const_name sup} "A" "B")] *}
theorem set_in_union_mp: "x \<in> A \<union> B \<Longrightarrow> x \<notin> A \<Longrightarrow> x \<in> B" by auto
setup {* add_forward_prfstep_cond @{thm set_in_union_mp} [with_cond "?A \<noteq> {?y}"] *}
theorem set_in_union_mp_single [forward]: "x \<in> {y} \<union> B \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<in> B" by auto
theorem union_single_eq [rewrite, backward]: "x \<in> p \<Longrightarrow> {x} \<union> p = p" by auto
theorem set_eq_union_same [backward]: "A = B \<Longrightarrow> C \<union> A = C \<union> B" by simp

subsection {* Disjointness *}
theorem set_disjoint_mp: "A \<inter> B = {} \<Longrightarrow> p \<in> A \<Longrightarrow> p \<notin> B" by auto
setup {* add_forward_prfstep_cond @{thm set_disjoint_mp} [with_cond "?A \<noteq> {?y}"] *}
theorem set_disjoint_single [rewrite]: "{x} \<inter> ys = {} \<longleftrightarrow> x \<notin> ys" by simp
theorem set_disjoint_intro [resolve]: "\<forall>x. x \<in> xs \<longrightarrow> x \<notin> ys \<Longrightarrow> xs \<inter> ys = {}" by auto

subsection {* subset *}
theorem subset_single [rewrite]: "{a} \<subseteq> B \<longleftrightarrow> a \<in> B" by simp
setup {* add_forward_prfstep @{thm set_mp} *}
setup {* add_resolve_prfstep @{thm Set.basic_monos(1)} *}
setup {* add_resolve_prfstep @{thm Set.Un_upper1} *}
theorem subset_union_same [backward]: "B \<subseteq> C \<Longrightarrow> A \<union> B \<subseteq> A \<union> C" by auto

subsection {* Diff *}
setup {* add_rewrite_rule @{thm Set.empty_Diff} *}
theorem set_union_minus_same [rewrite]: "(A \<union> B) - B = A - B" by auto
theorem set_union_minus_distinct [rewrite]: "a \<noteq> c \<Longrightarrow> {a} \<union> (B - {c}) = {a} \<union> B - {c}" by auto
setup {* add_forward_prfstep_cond @{thm Set.Diff_subset} [with_term "?A - ?B"] *}
theorem union_subtract_elt [rewrite]: "x \<notin> B \<Longrightarrow> (B \<union> {x}) - {x} = B" by simp
theorem subset_sub1 [backward]: "x \<in> A \<Longrightarrow> A - {x} \<subset> A" by auto

subsection {* Results on finite sets *}
setup {* add_resolve_prfstep @{thm Finite_Set.finite.emptyI} *}
theorem set_finite_single [resolve]: "finite {x}" by simp
setup {* add_rewrite_rule_cond @{thm Finite_Set.finite_Un}
  [with_filt (canonical_split_filter @{const_name sup} "F" "G")] *}
setup {* add_resolve_prfstep @{thm List.finite_set} *}
theorem Min_eqI' [backward1]: "finite A \<and> (\<forall>y\<in>A. y \<ge> x) \<Longrightarrow> x \<in> A \<Longrightarrow> Min A = x" using Min_eqI by auto
theorem Max_ge' [forward]: "finite A \<Longrightarrow> x > Max A \<Longrightarrow> \<not>(x \<in> A)" using Max_ge leD by auto

subsection {* Induction for finite sets *}

theorem finite_less_induct: "finite A \<Longrightarrow> (\<And>A. (\<And>B. B \<subset> A \<Longrightarrow> P B) \<Longrightarrow> P A) \<Longrightarrow> P A"
  apply (induct rule: finite_psubset_induct) by blast
ML_file "set_steps.ML"

section {* Multiset *}

subsection {* set_mset *}
setup {* add_rewrite_rule @{thm set_mset_empty} *}
setup {* add_rewrite_rule @{thm set_mset_single} *}
setup {* add_rewrite_rule @{thm set_mset_union} *}

subsection {* image_mset *}
setup {* add_rewrite_rule @{thm image_mset_empty} *}
setup {* add_rewrite_rule @{thm image_mset_single} *}
setup {* add_rewrite_rule @{thm image_mset_union} *}

subsection {* mset_prod *}
setup {* add_rewrite_rule @{thm msetprod_empty} *}
setup {* add_rewrite_rule @{thm msetprod_singleton} *}
setup {* add_rewrite_rule @{thm msetprod_Un} *}

subsection {* mset *}
theorem mset_single [rewrite]: "mset [x] = {#x#}" by simp
setup {* add_rewrite_rule @{thm mset.simps(1)} #> add_rewrite_rule_cond @{thm mset.simps(2)} [with_cond "?x \<noteq> []"] *} 
setup {* add_rewrite_rule @{thm mset_eq_setD} *}

subsection {* Case checking *}
setup {* add_resolve_prfstep @{thm multi_nonempty_split} *}

subsection {* Membership and ordering *}
theorem multiset_eq_union_same [backward]: "(A::'a multiset) = B \<Longrightarrow> C + A = C + B" by simp
setup {* add_backward2_prfstep @{thm subset_mset.antisym} *}
setup {* add_resolve_prfstep @{thm Multiset.empty_le} *}
setup {* add_forward_prfstep @{thm mset_lessD} *}
setup {* add_backward_prfstep @{thm Multiset.multi_member_split} *}
setup {* add_forward_prfstep_cond @{thm multi_psub_of_add_self} [with_term "?A + {#?x#}"] *}
theorem multi_contain_add_self: "x \<in># A + {#x#}" by simp
setup {* add_forward_prfstep_cond @{thm multi_contain_add_self} [with_term "?A + {#?x#}"] *}
theorem multi_add_right [resolve]: "M \<subseteq># N \<Longrightarrow> M + {#x#} \<subseteq># N + {#x#}" by simp
theorem multi_Ball_mono' [forward]:
  "M \<subset># N \<Longrightarrow> \<forall>x\<in>set_mset N. P x \<Longrightarrow> \<forall>x\<in>set_mset M. P x" by (meson mem_set_mset_iff mset_lessD)
setup {* add_rewrite_rule @{thm ball_set_mset_iff} *}

subsection {* swap *}
setup {* add_backward2_prfstep @{thm mset_swap} *}

subsection {* induction *}
setup {* add_prfstep_strong_induction @{thm full_multiset_induct} *}

end
