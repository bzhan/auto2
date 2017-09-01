(* Setup of proof steps related to sets. *)

theory Set_Thms
imports Logic_Thms "~~/src/HOL/Library/Multiset"
begin

section {* Set *}

subsection {* AC property of intersection and union *}

setup {* fold ACUtil.add_ac_data [
  {cfhead = @{cterm inf}, assoc_th = @{thm inf_assoc}, comm_th = @{thm inf_commute},
   unitl_th = @{thm inf_top_left}, unitr_th = @{thm inf_top_right}},

  {cfhead = @{cterm sup}, assoc_th = @{thm sup_assoc}, comm_th = @{thm sup_commute},
   unitl_th = @{thm sup_bot_left}, unitr_th = @{thm sup_bot_right}}]
*}

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

setup {* add_rewrite_rule @{thm Set.Un_iff} *}
setup {* add_fixed_sc ("Set.Un_iff@eqforward", 500) *}

lemma UnD1 [forward]: "c \<in> A \<union> B \<Longrightarrow> c \<notin> A \<Longrightarrow> c \<in> B" by auto
lemma UnD2 [forward]: "c \<in> A \<union> B \<Longrightarrow> c \<notin> B \<Longrightarrow> c \<in> A" by auto
lemma UnD1_single [forward]: "c \<in> {a} \<union> B \<Longrightarrow> c \<noteq> a \<Longrightarrow> c \<in> B" by auto
lemma UnD2_single [forward]: "c \<in> A \<union> {b} \<Longrightarrow> c \<noteq> b \<Longrightarrow> c \<in> A" by auto
setup {* add_forward_prfstep_cond @{thm Set.UnI1} [with_term "?A \<union> ?B"] *}
setup {* add_forward_prfstep_cond @{thm Set.UnI2} [with_term "?A \<union> ?B"] *}
lemma UnI1_single: "a \<in> {a} \<union> B" by auto
lemma UnI2_single: "b \<in> A \<union> {b}" by auto
setup {* add_forward_prfstep_cond @{thm UnI1_single} [with_term "{?a} \<union> ?B"] *}
setup {* add_forward_prfstep_cond @{thm UnI2_single} [with_term "?A \<union> {?b}"] *}
  
theorem union_single_eq [rewrite, backward]: "x \<in> p \<Longrightarrow> {x} \<union> p = p" by auto

subsection {* Intersection *}
setup {* add_rewrite_rule @{thm Set.Int_absorb} *}

subsection {* Disjointness *}

definition set_disjoint :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "set_disjoint U V = (U \<inter> V = {})"
setup {* add_rewrite_rule_back @{thm set_disjoint_def} *}

theorem set_disjoint_comm [rewrite]:
  "set_disjoint A B = set_disjoint B A" by (simp add: inf_commute set_disjoint_def)

theorem set_disjoint_empty [resolve]: "set_disjoint {} A" by (simp add: set_disjoint_def)
theorem set_disjoint_mp: "set_disjoint A B \<Longrightarrow> p \<in> A \<Longrightarrow> p \<notin> B" by (metis IntI empty_iff set_disjoint_def)
setup {* add_forward_prfstep_cond @{thm set_disjoint_mp} [with_cond "?A \<noteq> {?y}"] *}
theorem set_disjoint_single [rewrite]: "set_disjoint {x} ys \<longleftrightarrow> x \<notin> ys" by (simp add: set_disjoint_def)
theorem set_disjoint_intro [resolve]: "\<forall>x. x \<in> xs \<longrightarrow> x \<notin> ys \<Longrightarrow> set_disjoint xs ys" using set_disjoint_def by force
theorem disjoint_with_union [forward]: "set_disjoint A (B \<union> C) \<Longrightarrow> set_disjoint A B \<and> set_disjoint A C"
  by (simp add: Int_Un_distrib set_disjoint_def)
theorem disjoint_with_union' [backward2]: "set_disjoint A B \<Longrightarrow> set_disjoint A C \<Longrightarrow> set_disjoint A (B \<union> C)"
  by (meson UnD1 set_disjoint_intro set_disjoint_mp)

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
theorem union_subtract_elt [rewrite]:
  "x \<notin> B \<Longrightarrow> ({x} \<union> B) - {x} = B"
  "x \<notin> B \<Longrightarrow> (B \<union> {x}) - {x} = B" by simp+
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
setup {* add_rewrite_rule @{thm prod_mset_empty} *}
setup {* add_rewrite_rule @{thm prod_mset_singleton} *}
setup {* add_rewrite_rule @{thm prod_mset_Un} *}

subsection {* mset *}
theorem mset_member_empty [resolve]: "\<not>p \<in># {#}" by simp
theorem mset_single [rewrite]: "mset [x] = {#x#}" by simp
theorem mset_simps_2: "mset (a # x) = mset x + {#a#}" by simp
setup {* add_rewrite_rule @{thm mset.simps(1)} #>
  add_rewrite_rule_cond @{thm mset_simps_2} [with_cond "?x \<noteq> []"] *} 
setup {* add_rewrite_rule @{thm mset_eq_setD} *}
theorem mset_append_one [rewrite]: "mset (xs @ [x]) = mset xs + {#x#}" by simp
setup {* add_backward_prfstep @{thm Multiset.nth_mem_mset} *}
theorem in_mset_append [forward]: "m \<in># mset (xs @ [x]) \<Longrightarrow> m \<in># mset xs \<or> m = x" by auto
theorem in_multiset_single [forward]: "x \<in># {#y#} \<Longrightarrow> x = y" using not_gr0 by fastforce
theorem mset_butlast [forward]: "p \<in># mset (butlast xs) \<Longrightarrow> p \<in># mset xs"
  by (simp add: in_set_butlastD)
setup {* add_rewrite_rule_cond @{thm in_multiset_in_set} [with_term "set ?xs"] *}
setup {* add_rewrite_rule_back_cond @{thm in_multiset_in_set} [with_term "mset ?xs"] *}

subsection {* Case checking *}
theorem multi_nonempty_split' [resolve]: "M \<noteq> {#} \<Longrightarrow> \<exists>M' m. M = M' + {#m#}"
  using multi_nonempty_split by auto

subsection {* Membership and ordering *}
theorem multiset_eq_union_same [backward]: "(A::'a multiset) = B \<Longrightarrow> C + A = C + B" by simp
setup {* add_backward2_prfstep @{thm subset_mset.antisym} *}
setup {* add_resolve_prfstep @{thm Multiset.empty_le} *}
setup {* add_forward_prfstep @{thm mset_subsetD} *}
theorem multi_member_split' [backward]: "x \<in># M \<Longrightarrow> \<exists>M'. M = M' + {#x#}" by (metis insert_DiffM2)
theorem multi_contain_add_self: "A \<subset># {#x#} + A \<and> x \<in># {#x#} + A" by simp
setup {* add_forward_prfstep_cond @{thm multi_contain_add_self} [with_term "{#?x#} + ?A"] *}
theorem multi_contain_add_self': "A \<subset># A + {#x#} \<and> x \<in># A + {#x#}" by simp
setup {* add_forward_prfstep_cond @{thm multi_contain_add_self'} [with_term "?A + {#?x#}"] *}
theorem multi_add_right [resolve]: "M \<subseteq># N \<Longrightarrow> M + {#x#} \<subseteq># N + {#x#}" by simp
theorem multi_Ball_mono' [forward]: "M \<subset># N \<Longrightarrow> \<forall>x\<in>#N. P x \<Longrightarrow> \<forall>x\<in>#M. P x" by (simp add: mset_subsetD)

subsection {* swap *}
setup {* add_backward2_prfstep @{thm mset_swap} *}

subsection {* induction *}
setup {* add_strong_induct_rule @{thm full_multiset_induct} *}

end
