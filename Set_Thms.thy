theory Set_Thms
imports Auto2_Base "~~/src/HOL/Library/Multiset"
begin

section {* Set *}

subsection {* AC property of intersection and union *}

ML {*
val add_set_ac_data =
  fold add_ac_data [
    {fname = @{const_name inf}, assoc_r = false,
     unit_val = @{term UNIV}, comm_th = @{thm Int_ac(3)},
     assoc_th = @{thm Int_ac(1)}, unit_th = @{thm Set.Int_UNIV_left}},

    {fname = @{const_name sup}, assoc_r = false,
     unit_val = @{term "{}"}, comm_th = @{thm Un_ac(3)},
     assoc_th = @{thm Un_ac(1)}, unit_th = @{thm Set.Un_empty_left}}]
*}
setup {* add_set_ac_data *}

subsection {* Collection and bounded quantification *}
setup {* add_rewrite_rule @{thm Set.mem_Collect_eq} *}
setup {* add_forward_prfstep (equiv_forward_th @{thm Ball_def}) *}
setup {* add_backward_prfstep (equiv_backward_th @{thm Ball_def}) *}
theorem ball_subset: "\<forall>x\<in>s. P x \<Longrightarrow> t \<subseteq> s \<Longrightarrow> \<forall>x\<in>t. P x" by auto
setup {* add_forward_prfstep @{thm ball_subset} *}
setup {* add_forward_prfstep_cond (equiv_forward_th @{thm Set.ball_Un})
  [with_filt (canonical_split_filter @{const_name sup} "A" "B")] *}
theorem set_ball_Un_backward: "\<forall>x\<in>A. P x \<Longrightarrow> \<not>(\<forall>x\<in>A\<union>B. P x) \<Longrightarrow> \<not>(\<forall>x\<in>B. P x)" by auto
setup {* add_forward_prfstep @{thm set_ball_Un_backward} *}
setup {* add_rewrite_rule @{thm Set.ball_empty} *}
theorem ball_single: "(\<forall>x\<in>{x}. P x) = P x" by auto
setup {* add_rewrite_rule @{thm ball_single} *}

subsection {* Membership *}
setup {* add_forward_prfstep @{thm Set.singletonD} *}
theorem set_notin_singleton: "x \<notin> {v} \<Longrightarrow> x \<noteq> v" by simp
setup {* add_forward_prfstep @{thm set_notin_singleton} *}
setup {* add_forward_prfstep (equiv_forward_th @{thm Set.empty_iff}) *}
theorem set_membership_distinct: "x \<in> s \<Longrightarrow> y \<notin> s \<Longrightarrow> x \<noteq> y" by auto
setup {* add_forward_prfstep @{thm set_membership_distinct} *}

subsection {* Union *}
theorem set_not_in_union: "x \<notin> A \<union> B \<Longrightarrow> x \<notin> A \<and> x \<notin> B" by auto
setup {* add_forward_prfstep_cond @{thm set_not_in_union}
  [with_filt (canonical_split_filter @{const_name sup} "A" "B")] *}
theorem set_in_union_mp: "x \<in> A \<union> B \<Longrightarrow> x \<notin> A \<Longrightarrow> x \<in> B" by auto
setup {* add_forward_prfstep_cond @{thm set_in_union_mp} [with_cond "?A \<noteq> {?y}"] *}
theorem set_in_union_mp_single: "x \<in> {y} \<union> B \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<in> B" by auto
setup {* add_forward_prfstep @{thm set_in_union_mp_single} *}
theorem union_single_eq: "x \<in> p \<Longrightarrow> {x} \<union> p = p" by auto
setup {* add_rewrite_rule @{thm union_single_eq} #> add_backward_prfstep @{thm union_single_eq} *}
theorem set_eq_union_same: "A = B \<Longrightarrow> C \<union> A = C \<union> B" by simp
setup {* add_backward_prfstep @{thm set_eq_union_same} *}

subsection {* Disjointness *}
theorem set_disjoint_mp: "A \<inter> B = {} \<Longrightarrow> p \<in> A \<Longrightarrow> p \<notin> B" by auto
setup {* add_forward_prfstep_cond @{thm set_disjoint_mp} [with_cond "?A \<noteq> {?y}"] *}
theorem set_disjoint_single: "{x} \<inter> ys = {} \<longleftrightarrow> x \<notin> ys" by simp
setup {* add_rewrite_rule @{thm set_disjoint_single} *}
theorem set_disjoint_intro: "\<forall>x. x \<in> xs \<longrightarrow> x \<notin> ys \<Longrightarrow> xs \<inter> ys = {}" by auto
setup {* add_resolve_prfstep @{thm set_disjoint_intro} *}

subsection {* subset *}
theorem subset_single: "{a} \<subseteq> B \<longleftrightarrow> a \<in> B" by simp
setup {* add_rewrite_rule @{thm subset_single} *}
setup {* add_forward_prfstep @{thm set_mp} *}
setup {* add_resolve_prfstep @{thm Set.basic_monos(1)} *}
setup {* add_resolve_prfstep @{thm Set.Un_upper1} *}
theorem subset_union_same: "B \<subseteq> C \<Longrightarrow> A \<union> B \<subseteq> A \<union> C" by auto
setup {* add_backward_prfstep @{thm subset_union_same} *}

subsection {* Diff *}
setup {* add_rewrite_rule @{thm Set.empty_Diff} *}
theorem set_union_minus_same: "(A \<union> B) - B = A - B" by auto
setup {* add_rewrite_rule @{thm set_union_minus_same} *}
theorem set_union_minus_distinct: "a \<noteq> c \<Longrightarrow> {a} \<union> (B - {c}) = {a} \<union> B - {c}" by auto
setup {* add_rewrite_rule @{thm set_union_minus_distinct} *}
setup {* add_forward_prfstep_cond @{thm Set.Diff_subset} [with_term "?A - ?B"] *}
theorem union_subtract_elt: "x \<notin> B \<Longrightarrow> (B \<union> {x}) - {x} = B" by simp
setup {* add_rewrite_rule @{thm union_subtract_elt} *}

subsection {* Maximum value of a set *}
theorem Max_ge': "finite A \<Longrightarrow> x > Max A \<Longrightarrow> \<not>(x \<in> A)" using Max_ge leD by auto
setup {* add_forward_prfstep @{thm Max_ge'} *}

section {* Multiset *}

subsection {* set_of *}
setup {* add_rewrite_rule @{thm set_of_empty} *}
setup {* add_rewrite_rule @{thm set_of_single} *}
setup {* add_rewrite_rule @{thm set_of_union} *}

subsection {* image_mset *}
setup {* add_rewrite_rule @{thm image_mset_empty} *}
setup {* add_rewrite_rule @{thm image_mset_single} *}
setup {* add_rewrite_rule @{thm image_mset_union} *}

subsection {* mset_prod *}
setup {* add_rewrite_rule @{thm msetprod_empty} *}
setup {* add_rewrite_rule @{thm msetprod_singleton} *}
setup {* add_rewrite_rule @{thm msetprod_Un} *}

subsection {* multiset_of *}
theorem multiset_of_single: "multiset_of [x] = {#x#}" by simp
setup {* fold add_rewrite_rule [@{thm multiset_of.simps(1)}, @{thm multiset_of_single}]
  #> add_rewrite_rule_cond @{thm multiset_of.simps(2)} [with_cond "?x \<noteq> []"] *} 
setup {* add_rewrite_rule @{thm multiset_of_eq_setD} *}

subsection {* Case checking *}
setup {* add_resolve_prfstep @{thm multi_nonempty_split} *}

subsection {* Membership and ordering *}
theorem multiset_eq_union_same: "A = B \<Longrightarrow> C + A = C + B" by simp
setup {* add_backward_prfstep @{thm multiset_eq_union_same} *}
theorem multiset_antisym: "M \<subseteq># N \<Longrightarrow> N \<subseteq># M \<Longrightarrow> M = N" by simp
setup {* add_backward2_prfstep @{thm multiset_antisym} *}
setup {* add_resolve_prfstep @{thm Multiset.empty_le} *}
setup {* add_forward_prfstep @{thm mset_lessD} *}
setup {* add_backward_prfstep @{thm Multiset.multi_member_split} *}
setup {* add_forward_prfstep_cond @{thm multi_psub_of_add_self} [with_term "?A + {#?x#}"] *}
theorem multi_contain_add_self: "x \<in># A + {#x#}" by simp
setup {* add_forward_prfstep_cond @{thm multi_contain_add_self} [with_term "?A + {#?x#}"] *}
theorem multi_add_right: "M \<subseteq># N \<Longrightarrow> M + {#x#} \<subseteq># N + {#x#}" by simp
setup {* add_resolve_prfstep @{thm multi_add_right} *}
theorem multi_Ball_mono': "M \<subset># N \<Longrightarrow> \<forall>x\<in>set_of N. P x \<Longrightarrow> \<forall>x\<in>set_of M. P x" by (meson mem_set_of_iff mset_lessD)
setup {* add_forward_prfstep @{thm multi_Ball_mono'} *}
setup {* add_rewrite_rule @{thm ball_set_of_iff} *}

subsection {* swap *}
setup {* add_backward2_prfstep @{thm multiset_of_swap} *}

subsection {* induction *}
setup {* add_prfstep_strong_induction @{thm full_multiset_induct} *}

end
