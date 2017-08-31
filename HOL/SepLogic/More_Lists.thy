theory More_Lists
imports "../DataStrs/Lists_Ex"
begin

section {* More on take, drop, and update *}

theorem take_update [rewrite]: "i < length l \<Longrightarrow> take (i + 1) (list_update l i x) = take i l @ [x]"
  by (simp add: take_Suc_conv_app_nth)

setup {* add_rewrite_rule @{thm butlast_take} *}

(* From Sep_Misc in AFP *)
lemma last_take_nth_conv [rewrite]:
  "n \<le> length l \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> last (take n l) = l!(n - 1)"
  apply (induction l arbitrary: n)
  by (auto simp: take_Cons split: nat.split)

setup {* add_rewrite_rule @{thm take_update_swap} *}

section {* hd and last *}

theorem hd_conv_nth [rewrite_back]: "length xs > 0 \<Longrightarrow> hd xs = xs ! 0"
  by (simp add: hd_conv_nth)

theorem last_conv_nth' [rewrite_back]: "length xs > 0 \<Longrightarrow> last xs = xs ! (length xs - 1)"
  by (simp add: last_conv_nth)

theorem hd_in_set: "length xs > 0 \<Longrightarrow> hd xs \<in> set xs" by simp
setup {* add_forward_prfstep_cond @{thm hd_in_set} [with_term "hd ?xs", with_term "set ?xs"] *}

theorem hd_in_mset: "length xs > 0 \<Longrightarrow> hd xs \<in># mset xs" by simp
setup {* add_forward_prfstep_cond @{thm hd_in_mset} [with_term "hd ?xs", with_term "mset ?xs"] *}

theorem last_in_set: "length xs > 0 \<Longrightarrow> last xs \<in> set xs" by simp
setup {* add_forward_prfstep_cond @{thm last_in_set} [with_term "last ?xs", with_term "set ?xs"] *}

theorem last_in_mset: "length xs > 0 \<Longrightarrow> last xs \<in># mset xs" by simp
setup {* add_forward_prfstep_cond @{thm last_in_mset} [with_term "last ?xs", with_term "mset ?xs"] *}

section {* Relationship between mset and set of lists *}

setup {* add_rewrite_rule_cond @{thm in_multiset_in_set} [with_term "set ?xs"] *}
setup {* add_rewrite_rule_back_cond @{thm in_multiset_in_set} [with_term "mset ?xs"] *}

theorem in_mset_conv_nth [resolve]: "x \<in># mset xs \<Longrightarrow> \<exists>i<length xs. x = xs ! i"
  by (simp add: in_set_conv_nth')

theorem insert_mset_to_set [rewrite]: "mset xs' = mset xs + {# x #} \<Longrightarrow> set xs' = set xs \<union> {x}"
  by (metis set_mset_mset set_mset_single set_mset_union)

theorem delete_mset_to_set [rewrite]:
  "mset xs' = mset xs - {# x #} \<Longrightarrow> distinct xs \<Longrightarrow> set xs' = set xs - {x}"
  by (metis mset_eq_setD mset_remove1 set_remove1_eq)

theorem update_mset_to_set [rewrite]:
  "mset xs' = {# y #} + (mset xs - {# x #}) \<Longrightarrow> distinct xs \<Longrightarrow> set xs' = (set xs - {x}) \<union> {y}"
  by (metis insert_mset_to_set mset_remove1 set_remove1_eq union_commute)

end
