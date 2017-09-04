theory More_Lists
  imports "../DataStrs/Arrays_Ex"
begin

section {* hd and last *}

lemma hd_conv_nth [rewrite_back]: "length xs > 0 \<Longrightarrow> hd xs = xs ! 0"
  by (simp add: hd_conv_nth)

lemma last_conv_nth' [rewrite]: "length xs > 0 \<Longrightarrow> last xs = xs ! (length xs - 1)"
  by (simp add: last_conv_nth)

lemma hd_in_set: "length xs > 0 \<Longrightarrow> hd xs \<in> set xs" by simp
setup {* add_forward_prfstep_cond @{thm hd_in_set} [with_term "hd ?xs", with_term "set ?xs"] *}

lemma hd_in_mset: "length xs > 0 \<Longrightarrow> hd xs \<in># mset xs" by simp
setup {* add_forward_prfstep_cond @{thm hd_in_mset} [with_term "hd ?xs", with_term "mset ?xs"] *}

lemma last_in_set: "length xs > 0 \<Longrightarrow> last xs \<in> set xs" by simp
setup {* add_forward_prfstep_cond @{thm last_in_set} [with_term "last ?xs", with_term "set ?xs"] *}

lemma last_in_mset: "length xs > 0 \<Longrightarrow> last xs \<in># mset xs" by simp
setup {* add_forward_prfstep_cond @{thm last_in_mset} [with_term "last ?xs", with_term "mset ?xs"] *}

section {* Relationship between mset and set of lists *}

theorem mset_butlast [rewrite]: "length xs > 0 \<Longrightarrow> mset (butlast xs) = mset xs - {# last xs #}"
  by (metis add_diff_cancel_right' append_butlast_last_id length_greater_0_conv list.size(3)
      mset.simps(2) size_eq_0_iff_empty size_mset union_code)

theorem insert_mset_to_set [rewrite]: "mset xs' = mset xs + {# x #} \<Longrightarrow> set xs' = set xs \<union> {x}"
  by (metis set_mset_mset set_mset_single set_mset_union)

theorem delete_mset_to_set [rewrite]:
  "distinct xs \<Longrightarrow> mset xs' = mset xs - {# x #} \<Longrightarrow> set xs' = set xs - {x}"
  by (metis mset_eq_setD mset_remove1 set_remove1_eq)

theorem update_mset_to_set [rewrite]:
  "distinct xs \<Longrightarrow> mset xs' = {# y #} + (mset xs - {# x #}) \<Longrightarrow> set xs' = (set xs - {x}) \<union> {y}"
  by (metis insert_mset_to_set mset_remove1 set_remove1_eq union_commute)

end
