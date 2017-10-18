theory More_Lists
imports "../DataStrs/Arrays_Ex"
begin

section {* Relationship between mset and set of lists *}

lemma set_butlast [resolve]: "set (butlast xs) \<subseteq> set xs"
  by (simp add: in_set_butlastD subsetI)

lemma mset_butlast [rewrite]: "xs \<noteq> [] \<Longrightarrow> mset (butlast xs) = mset xs - {# last xs #}"
  by (metis add_diff_cancel_right' append_butlast_last_id list.size(3)
      mset.simps(2) size_eq_0_iff_empty size_mset union_code)

lemma insert_mset_to_set [rewrite]: "mset xs' = mset xs + {# x #} \<Longrightarrow> set xs' = set xs \<union> {x}"
  by (metis set_mset_mset set_mset_single set_mset_union)

lemma delete_mset_to_set [rewrite]:
  "distinct xs \<Longrightarrow> mset xs' = mset xs - {# x #} \<Longrightarrow> set xs' = set xs - {x}"
  by (metis mset_eq_setD mset_remove1 set_remove1_eq)

lemma update_mset_to_set [rewrite]:
  "distinct xs \<Longrightarrow> mset xs' = {# y #} + (mset xs - {# x #}) \<Longrightarrow> set xs' = (set xs - {x}) \<union> {y}"
  by (metis insert_mset_to_set mset_remove1 set_remove1_eq union_commute)

lemma mset_update' [rewrite]:
  "i < length ls \<Longrightarrow> mset (list_update ls i v) = {#v#} + (mset ls - {# ls ! i #})"
  using mset_update by fastforce

end
