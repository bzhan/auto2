(* Setup of proof steps related to sets. *)

theory Set_Thms
imports Logic_Thms "~~/src/HOL/Library/Multiset"
begin

section {* Functions *}

setup {* add_backward_prfstep @{thm injI} *}

section {* Set *}

subsection {* AC property of intersection and union *}

setup {* fold ACUtil.add_ac_data [
  {cfhead = @{cterm inf}, unit = SOME @{cterm inf},
   assoc_th = @{thm inf_assoc}, comm_th = @{thm inf_commute},
   unitl_th = @{thm inf_top_left}, unitr_th = @{thm inf_top_right}},

  {cfhead = @{cterm sup}, unit = SOME @{cterm bot},
   assoc_th = @{thm sup_assoc}, comm_th = @{thm sup_commute},
   unitl_th = @{thm sup_bot_left}, unitr_th = @{thm sup_bot_right}}]
*}

subsection {* Collection and bounded quantification *}

setup {* add_rewrite_rule @{thm Set.mem_Collect_eq} *}
lemma ball_single [rewrite]: "(\<forall>x\<in>{x}. P x) = P x" by auto

subsection {* Membership *}

setup {* add_rewrite_rule @{thm Set.singleton_iff} *} 
lemma set_two_mem [rewrite]: "{u, v} \<subseteq> S \<longleftrightarrow> u \<in> S \<and> v \<in> S" by simp
setup {* add_forward_prfstep (equiv_forward_th @{thm Set.empty_iff}) *}
lemma set_membership_distinct [forward]: "x \<in> s \<Longrightarrow> y \<notin> s \<Longrightarrow> x \<noteq> y" by auto
lemma non_empty_exist_elt [backward]: "U \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> U" by blast
lemma non_univ_exist_compl [backward]: "U \<noteq> UNIV \<Longrightarrow> \<exists>x. x \<notin> U" by blast
lemma univ_member_all [resolve]: "U = UNIV \<Longrightarrow> x \<in> U" by simp

subsection {* Extensionality *}

lemma set_ext [forward]: "\<forall>a. a \<in> S \<longleftrightarrow> a \<in> T \<Longrightarrow> S = T" by auto
setup {* add_backward_prfstep_cond @{thm set_ext} [with_filt (order_filter "S" "T")] *}
setup {* add_fixed_sc ("Set_Thms.set_ext@back", 500) *}

lemma set_pair_ext [forward]: "\<forall>a b. (a, b) \<in> S \<longleftrightarrow> (a, b) \<in> T \<Longrightarrow> S = T" by auto

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
  
lemma union_single_eq [rewrite, backward]: "x \<in> p \<Longrightarrow> {x} \<union> p = p" by auto

subsection {* Intersection *}

setup {* add_rewrite_rule @{thm Set.Int_iff} *}
setup {* add_fixed_sc ("Set.Int_iff@invbackward", 500) *}

setup {* add_rewrite_rule @{thm Set.Int_empty_left} *}
setup {* add_rewrite_rule @{thm Set.Int_empty_right} *}
setup {* add_rewrite_rule @{thm Set.Int_absorb} *}
lemma set_disjoint_mp [forward, backward2]: "A \<inter> B = {} \<Longrightarrow> p \<in> A \<Longrightarrow> p \<notin> B" by auto
lemma set_disjoint_single [rewrite]: "{x} \<inter> B = {} \<longleftrightarrow> x \<notin> B" by simp

subsection {* subset *}

setup {* add_forward_prfstep @{thm subsetI} *}
setup {* add_forward_prfstep @{thm set_mp} *}
theorem subset_single [rewrite]: "{a} \<subseteq> B \<longleftrightarrow> a \<in> B" by simp
setup {* add_resolve_prfstep @{thm Set.basic_monos(1)} *}
setup {* add_resolve_prfstep @{thm Set.Un_upper1} *}
setup {* add_resolve_prfstep @{thm Set.Un_upper2} *}
lemma union_is_subset [forward]: "A \<union> B \<subseteq> C \<Longrightarrow> A \<subseteq> C \<and> B \<subseteq> C" by simp
setup {* add_backward1_prfstep @{thm Set.Un_least} *}
setup {* add_backward2_prfstep @{thm Set.Un_least} *}
lemma subset_union_same1 [backward]: "B \<subseteq> C \<Longrightarrow> A \<union> B \<subseteq> A \<union> C" by auto
lemma subset_union_same2 [backward]: "A \<subseteq> B \<Longrightarrow> A \<union> C \<subseteq> B \<union> C" by auto

subsection {* Diff *}

setup {* add_rewrite_rule @{thm Set.Diff_iff} *}
setup {* add_fixed_sc ("Set.Diff_iff@invbackward", 500) *}

setup {* add_rewrite_rule @{thm Set.empty_Diff} *}
lemma mem_diff [rewrite]: "x \<in> A - B \<longleftrightarrow> x \<in> A \<and> x \<notin> B" by simp
lemma set_union_minus_same1 [rewrite]: "(A \<union> B) - B = A - B" by auto
lemma set_union_minus_same2 [rewrite]: "(B \<union> A) - B = A - B" by auto
lemma set_union_minus_distinct [rewrite]: "a \<noteq> c \<Longrightarrow> {a} \<union> (B - {c}) = {a} \<union> B - {c}" by auto
setup {* add_forward_prfstep_cond @{thm Set.Diff_subset} [with_term "?A - ?B"] *}
lemma union_subtract_elt1 [rewrite]: "x \<notin> B \<Longrightarrow> ({x} \<union> B) - {x} = B" by simp
lemma union_subtract_elt2 [rewrite]: "x \<notin> B \<Longrightarrow> (B \<union> {x}) - {x} = B" by simp
lemma subset_sub1 [backward]: "x \<in> A \<Longrightarrow> A - {x} \<subset> A" by auto
lemma member_notin [forward]: "x \<in> S - {y} \<Longrightarrow> x \<noteq> y" by simp
lemma member_notin_contra: "x \<in> S \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<in> S - {y}" by simp
setup {* add_forward_prfstep_cond @{thm member_notin_contra} [with_term "?S - {?y}"] *}

subsection {* Results on finite sets *}

setup {* add_property_const @{term finite} *}
setup {* add_resolve_prfstep @{thm Finite_Set.finite.emptyI} *}
lemma set_finite_single [resolve]: "finite {x}" by simp
setup {* add_rewrite_rule @{thm Finite_Set.finite_Un} *}
lemma Max_ge' [forward]: "finite A \<Longrightarrow> x > Max A \<Longrightarrow> \<not>(x \<in> A)" using Max_ge leD by auto

subsection {* Cardinality *}

setup {* add_rewrite_rule @{thm card_empty} *}
lemma card_emptyD [rewrite]: "finite S \<Longrightarrow> card S = 0 \<Longrightarrow> S = {}" by simp
lemma card_minus1 [rewrite]:
  "x \<in> S \<Longrightarrow> card (S - {x}) = card S - 1" by (simp add: card_Diff_subset)
setup {* add_forward_prfstep @{thm finite_Diff} *}

subsection {* image_set *}

setup {* add_rewrite_rule @{thm Set.image_Un} *}
setup {* add_rewrite_rule @{thm image_set_diff} *}

section {* Multiset *}

subsection {* Basic properties *}

lemma mset_member_empty [resolve]: "\<not>p \<in># {#}" by simp
lemma mem_multiset_single [rewrite]: "x \<in># {#y#} \<longleftrightarrow> x = y" by simp
setup {* add_backward2_prfstep @{thm subset_mset.antisym} *}
setup {* add_resolve_prfstep @{thm Multiset.empty_le} *}
setup {* add_forward_prfstep @{thm mset_subsetD} *}

lemma multi_contain_add_self1 [resolve]: "A \<subset># {#x#} + A" by simp
lemma multi_contain_add_self2 [resolve]: "A \<subset># A + {#x#}" by simp
setup {* add_forward_prfstep_cond @{thm Multiset.multi_member_this} [with_term "{#?x#} + ?XS"] *}
lemma multi_member_this2: "x \<in># XS + {#x#}" by simp
setup {* add_forward_prfstep_cond @{thm multi_member_this2} [with_term "?XS + {#?x#}"] *}
setup {* add_backward_prfstep @{thm Multiset.subset_mset.add_left_mono} *}
setup {* add_backward_prfstep @{thm Multiset.subset_mset.add_right_mono} *}

subsection {* Case checking and induction *}

lemma multi_nonempty_split' [resolve]: "M \<noteq> {#} \<Longrightarrow> \<exists>M' m. M = M' + {#m#}"
  using multi_nonempty_split by auto

lemma multi_member_split' [backward]: "x \<in># M \<Longrightarrow> \<exists>M'. M = M' + {#x#}"
  by (metis insert_DiffM2)

setup {* add_strong_induct_rule @{thm full_multiset_induct} *}

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

subsection {* Set interval *}

setup {* add_rewrite_rule @{thm Set_Interval.ord_class.lessThan_iff} *}

end
