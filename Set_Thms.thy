(* Setup of proof steps related to sets. *)

theory Set_Thms
imports Auto2_Base "~~/src/HOL/Library/Multiset"
begin

section {* Set *}

subsection {* AC property of intersection and union *}

theorem Int_is_assoc: "is_assoc_fn (op \<inter>)" by (simp add: inf.semigroup_axioms is_assoc_fn_def semigroup.assoc)
theorem Int_is_comm: "is_comm_fn (op \<inter>)" by (simp add: inf_commute is_comm_fn_def)
theorem Int_has_unit: "is_unit_fn UNIV (op \<inter>)" by (simp add: is_unit_fn_def)

theorem Un_is_assoc: "is_assoc_fn (op \<union>)" by (simp add: is_assoc_fn_def semigroup.assoc sup.semigroup_axioms)
theorem Un_is_comm: "is_comm_fn (op \<union>)" by (simp add: is_comm_fn_def sup_commute)
theorem Un_has_unit: "is_unit_fn {} (op \<union>)" by (simp add: is_unit_fn_def)

ML {*
val add_set_ac_data =
  fold ACUtil.add_ac_data [
    {fname = @{const_name inf},
     assoc_th = @{thm Int_is_assoc}, comm_th = @{thm Int_is_comm},
     unit_th = @{thm Int_has_unit}, uinv_th = true_th, inv_th = true_th},

    {fname = @{const_name sup},
     assoc_th = @{thm Un_is_assoc}, comm_th = @{thm Un_is_comm},
     unit_th = @{thm Un_has_unit}, uinv_th = true_th, inv_th = true_th}]
*}
setup {* add_set_ac_data *}

subsection {* Collection and bounded quantification *}
setup {* add_rewrite_rule @{thm Set.mem_Collect_eq} *}
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
theorem set_not_in_union [forward]: "x \<notin> A \<union> B \<Longrightarrow> x \<notin> A \<and> x \<notin> B" by auto
theorem set_in_union_mp: "x \<in> A \<union> B \<Longrightarrow> x \<notin> A \<Longrightarrow> x \<in> B" by auto
setup {* add_forward_prfstep_cond @{thm set_in_union_mp} [with_cond "?A \<noteq> {?y}"] *}
theorem set_in_union_mp_single [forward]: "x \<in> {y} \<union> B \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<in> B" by auto
theorem union_single_eq [rewrite, backward]: "x \<in> p \<Longrightarrow> {x} \<union> p = p" by auto
setup {* add_prfstep (AC_ProofSteps.ac_equiv_strong (
  "ac_equiv_strong_union", @{term_pat "?A \<union> ?B \<noteq> ?C \<union> ?D"})) *}

subsection {* Intersection *}
setup {* add_rewrite_rule @{thm Set.Int_absorb} *}

subsection {* Disjointness *}
definition set_disjoint :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "set_disjoint U V = (U \<inter> V = {})"
setup {* add_forward_prfstep (equiv_backward_th @{thm set_disjoint_def}) *}
setup {* add_backward_prfstep (equiv_forward_th @{thm set_disjoint_def}) *}

theorem set_disjoint_comm: "set_disjoint A B = set_disjoint B A" by (simp add: inf_commute set_disjoint_def)
setup {* add_forward_prfstep (equiv_forward_th @{thm set_disjoint_comm}) *}
setup {* add_backward_prfstep (equiv_backward_th @{thm set_disjoint_comm}) *}

theorem set_disjoint_empty [resolve]: "set_disjoint {} A" by (simp add: set_disjoint_def)
theorem set_disjoint_mp: "set_disjoint A B \<Longrightarrow> p \<in> A \<Longrightarrow> p \<notin> B" by (metis IntI empty_iff set_disjoint_def)
setup {* add_forward_prfstep_cond @{thm set_disjoint_mp} [with_cond "?A \<noteq> {?y}"] *}
theorem set_disjoint_single [rewrite]: "set_disjoint {x} ys \<longleftrightarrow> x \<notin> ys" by (simp add: set_disjoint_def)
theorem set_disjoint_intro [resolve]: "\<forall>x. x \<in> xs \<longrightarrow> x \<notin> ys \<Longrightarrow> set_disjoint xs ys" using set_disjoint_def by force
theorem disjoint_with_union [forward]: "set_disjoint A (B \<union> C) \<Longrightarrow> set_disjoint A B \<and> set_disjoint A C"
  by (simp add: Int_Un_distrib set_disjoint_def)
theorem disjoint_with_union' [backward2]: "set_disjoint A B \<Longrightarrow> set_disjoint A C \<Longrightarrow> set_disjoint A (B \<union> C)"
  by (meson set_disjoint_intro set_disjoint_mp set_in_union_mp)

subsection {* subset *}
theorem subset_single [rewrite]: "{a} \<subseteq> B \<longleftrightarrow> a \<in> B" by simp
setup {* add_forward_prfstep @{thm set_mp} *}
setup {* add_resolve_prfstep @{thm Set.basic_monos(1)} *}
setup {* add_resolve_prfstep @{thm Set.Un_upper1} *}
theorem subset_union_same: "B \<subseteq> C \<Longrightarrow> A \<union> B \<subseteq> A \<union> C" by auto
setup {* add_backward_prfstep_cond @{thm subset_union_same} [with_term "?A"] *}

subsection {* Diff *}
setup {* add_rewrite_rule @{thm Set.empty_Diff} *}
theorem set_union_minus_same [rewrite]: "(A \<union> B) - B = A - B" by auto
theorem set_union_minus_same' [rewrite]: "(B \<union> A) - B = A - B" by auto
theorem set_union_minus_distinct [rewrite]: "a \<noteq> c \<Longrightarrow> {a} \<union> (B - {c}) = {a} \<union> B - {c}" by auto
setup {* add_forward_prfstep_cond @{thm Set.Diff_subset} [with_term "?A - ?B"] *}
theorem union_subtract_elt [rewrite]: "x \<notin> B \<Longrightarrow> (B \<union> {x}) - {x} = B" by simp
theorem subset_sub1 [backward]: "x \<in> A \<Longrightarrow> A - {x} \<subset> A" by auto
theorem member_notin [forward]: "x \<in> S - {y} \<Longrightarrow> x \<noteq> y" by simp
theorem member_notin_contra: "x \<in> S \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<in> S - {y}" by simp
setup {* add_forward_prfstep_cond @{thm member_notin_contra} [with_term "?S - {?y}"] *}

subsection {* Results on finite sets *}
setup {* add_resolve_prfstep @{thm Set.insert_not_empty} *}
setup {* add_resolve_prfstep @{thm Finite_Set.finite.emptyI} *}
theorem set_finite_single [resolve]: "finite {x}" by simp
setup {* add_rewrite_rule @{thm Finite_Set.finite_Un} *}
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
theorem mset_member_empty [resolve]: "\<not>p \<in># {#}" by simp
theorem mset_single [rewrite]: "mset [x] = {#x#}" by simp
setup {* add_rewrite_rule @{thm mset.simps(1)} #> add_rewrite_rule_cond @{thm mset.simps(2)} [with_cond "?x \<noteq> []"] *} 
setup {* add_rewrite_rule @{thm mset_eq_setD} *}
theorem mset_append_one [rewrite]: "mset (xs @ [x]) = mset xs + {#x#}" by simp
setup {* add_backward_prfstep @{thm Multiset.nth_mem_mset} *}
theorem in_mset_append [forward]: "m \<in># mset (xs @ [x]) \<Longrightarrow> m \<in># mset xs \<or> m = x" by auto
theorem in_multiset_single [forward]: "x \<in># {#y#} \<Longrightarrow> x = y" using not_gr0 by fastforce
theorem mset_butlast [forward]: "p \<in># mset (butlast xs) \<Longrightarrow> p \<in># mset xs"
  by (meson in_set_butlastD mem_set_multiset_eq)

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
setup {* add_forward_prfstep (equiv_forward_th @{thm ball_set_mset_iff}) *}

subsection {* swap *}
setup {* add_backward2_prfstep @{thm mset_swap} *}

subsection {* induction *}
setup {* add_prfstep_strong_induction @{thm full_multiset_induct} *}

end
