theory More_Lists
imports "../DataStrs/Lists_Ex" "~~/src/HOL/Imperative_HOL/ex/Subarray"
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

theorem in_set_conv_nth' [resolve]: "x \<in> set xs \<Longrightarrow> \<exists>i<length xs. x = xs ! i"
  by (metis in_set_conv_nth)

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

section {* Subarray and sublists. *}

setup {* add_backward2_prfstep (equiv_backward_th @{thm sublist'_eq_samelength_iff}) *}
setup {* add_rewrite_rule @{thm length_sublist'} *}
setup {* add_rewrite_rule @{thm nth_sublist'} *}
theorem nth_rev_sublist'_use [rewrite]:
  "k < j - i \<Longrightarrow> j \<le> length xs \<Longrightarrow> sublist' i j xs ! (length (sublist' i j xs) - 1 - k) = xs ! (j - 1 - k)"
  by (simp add: length_sublist' nth_sublist')

theorem sublist_as_Cons [backward]:
  "l < r \<Longrightarrow> r \<le> length xs \<Longrightarrow> sublist' l r xs = xs ! l # sublist' (l + 1) r xs"
  by (metis One_nat_def add.right_neutral add_Suc_right order_less_trans sublist'_front le_neq_implies_less)
theorem sublist_as_Cons1 [backward]:
  "0 < r \<Longrightarrow> r \<le> length xs \<Longrightarrow> sublist' 0 r xs = xs ! 0 # sublist' 1 r xs"
  by (metis One_nat_def order_less_trans sublist'_front le_neq_implies_less)
theorem sublist_as_append [backward]:
  "l \<le> m \<Longrightarrow> m \<le> r \<Longrightarrow> sublist' l r xs = sublist' l m xs @ sublist' m r xs"
  by (simp add: sublist'_append)

(* An result about sortedness of trivial sublists. *)
theorem sublist'_single' [rewrite]:
  "n < length xs \<Longrightarrow> sublist' n (n + 1) xs = [xs ! n]" using sublist'_single by simp
setup {* fold add_rewrite_rule [@{thm sublist'_Nil'}, @{thm sublist'_Nil2}] *}

(* Some results about sets and multisets of sublists. *)
setup {* add_rewrite_rule @{thm set_sublist'} *}

theorem mset_sublist' [backward1]:
  "r \<le> List.length xs \<Longrightarrow> \<forall>i. i < l \<longrightarrow> xs ! i = ys ! i \<Longrightarrow> \<forall>i. i \<ge> r \<longrightarrow> xs ! i = ys ! i \<Longrightarrow>
   mset xs = mset ys \<Longrightarrow> mset (sublist' l r xs) = mset (sublist' l r ys)"
  by (smt le_less_trans mset_eq_length mset_sublist nat_less_le sublist'_eq_samelength_iff)

end
