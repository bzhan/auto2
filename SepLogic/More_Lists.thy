theory More_Lists
imports "../Auto2"
begin

section {* More on take, drop, and update *}

theorem take_update [rewrite]: "i < length l \<Longrightarrow> take (1 + i) (list_update l i x) = take i l @ [x]"
  by (simp add: take_Suc_conv_app_nth)

theorem drop_update [rewrite]: "drop (1 + i + n) (list_update l i x) = drop (1 + i + n) l" by simp

theorem take_drop_shift_one [rewrite]:
  "i + len \<le> length l \<Longrightarrow> len \<noteq> 0 \<Longrightarrow> l ! i # take (len - 1) (drop (i + 1) l) = take len (drop i l)"
  by (metis Cons_nth_drop_Suc One_nat_def add.right_neutral add_Suc_right add_diff_inverse_nat
      add_eq_self_zero add_lessD1 diff_add_zero le_neq_implies_less take_Cons')

setup {* add_rewrite_rule @{thm butlast_take} *}

(* From Sep_Misc in AFP *)
lemma last_take_nth_conv [rewrite]:
  "n \<le> length l \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> last (take n l) = l!(n - 1)"
  apply (induction l arbitrary: n)
  by (auto simp: take_Cons split: nat.split)

section {* list_update_range *}

fun list_update_range :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "list_update_range l i [] = l"
| "list_update_range l i (x # xs) = list_update_range (list_update l i x) (1 + i) xs"
setup {* fold add_rewrite_rule @{thms list_update_range.simps} *}
setup {* add_rewrite_rule_back @{thm list_update_range.simps(2)} *}

theorem length_list_update_range [rewrite]:
  "length (list_update_range l i l') = length l"
  by (tactic {* auto2s_tac @{context} (INDUCT ("l'", Arbitraries ["i", "l"])) *})

theorem list_update_range_rule:
  "length l' + i \<le> length l \<Longrightarrow> list_update_range l i l' = take i l @ l' @ drop (i + length l') l"
  by (tactic {* auto2s_tac @{context} (
    INDUCT ("l'", Arbitraries ["i", "l"]) THEN
    OBTAIN "length (tl l') + 1 + i \<le> length l" THEN
    OBTAIN "i < length l") *})

theorem list_update_range_rule_zero [rewrite]:
  "length l' \<le> length l \<Longrightarrow> list_update_range l 0 l' = l' @ drop (length l') l"
  by (metis add.right_neutral append_Nil gen_length_def length_code list_update_range_rule take_0)

theorem take_n_list_update_range [rewrite]:
  "n \<le> length l \<Longrightarrow> n \<le> length l' \<Longrightarrow> take n (list_update_range l' 0 (take n l)) = take n l"
  by (simp add: list_update_range_rule_zero)

section {* Swap *}

definition list_swap :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "list_swap xs i j = list_update (list_update xs i (xs!j)) j (xs!i)"
setup {* add_rewrite_rule @{thm list_swap_def} *}

theorem list_swap_eval [rewrite]:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> (list_swap xs i j) ! i = xs ! j"
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> (list_swap xs i j) ! j = xs ! i"
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> k \<noteq> i \<Longrightarrow> k \<noteq> j \<Longrightarrow> (list_swap xs i j) ! k = xs ! k"
  by (simp add: list_swap_def nth_list_update)+

theorem length_swap [rewrite]: "length (list_swap xs i j) = length xs" by auto2

theorem mset_swap [rewrite]:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> mset (list_swap xs i j) = mset xs" by auto2

section {* hd and last *}

theorem hd_conv_nth [rewrite_back]: "length xs > 0 \<Longrightarrow> hd xs = xs ! 0"
  by (simp add: hd_conv_nth)

theorem last_conv_nth' [rewrite_back]: "length xs > 0 \<Longrightarrow> last xs = xs ! (length xs - 1)"
  by (simp add: last_conv_nth)

theorem hd_in_set: "length xs > 0 \<Longrightarrow> hd xs \<in> set xs" by simp
setup {* add_forward_prfstep_cond @{thm hd_in_set} [with_term "hd ?xs", with_term "set ?xs"] *}

theorem hd_in_mset: "length xs > 0 \<Longrightarrow> hd xs \<in># mset xs" by (meson More_Lists.hd_in_set mem_set_multiset_eq)
setup {* add_forward_prfstep_cond @{thm hd_in_mset} [with_term "hd ?xs", with_term "mset ?xs"] *}

theorem last_in_set: "length xs > 0 \<Longrightarrow> last xs \<in> set xs" by simp
setup {* add_forward_prfstep_cond @{thm last_in_set} [with_term "last ?xs", with_term "set ?xs"] *}

theorem last_in_mset: "length xs > 0 \<Longrightarrow> last xs \<in># mset xs" using mem_set_multiset_eq by fastforce
setup {* add_forward_prfstep_cond @{thm last_in_mset} [with_term "last ?xs", with_term "mset ?xs"] *}

section {* Relationship between mset and set of lists *}

setup {* add_resolve_prfstep (equiv_forward_th @{thm in_multiset_in_set}) *}
setup {* add_resolve_prfstep (equiv_backward_th @{thm in_multiset_in_set}) *}

theorem in_set_conv_nth' [resolve]: "x \<in> set xs \<Longrightarrow> \<exists>i<length xs. x = xs ! i"
  by (metis in_set_conv_nth)

theorem in_mset_conv_nth [resolve]: "x \<in># mset xs \<Longrightarrow> \<exists>i<length xs. x = xs ! i"
  by (metis in_set_conv_nth mem_set_multiset_eq)

theorem insert_mset_to_set [rewrite]: "mset xs' = mset xs + {# x #} \<Longrightarrow> set xs' = set xs \<union> {x}"
  by (metis set_mset_mset set_mset_single set_mset_union)

theorem delete_mset_to_set [rewrite]:
  "mset xs' = mset xs - {# x #} \<Longrightarrow> distinct xs \<Longrightarrow> set xs' = set xs - {x}"
  by (metis mset_eq_setD mset_remove1 set_remove1_eq)

theorem update_mset_to_set [rewrite]:
  "mset xs' = (mset xs - {# x #}) + {# y #} \<Longrightarrow> distinct xs \<Longrightarrow> set xs' = (set xs - {x}) \<union> {y}"
  by (metis insert_mset_to_set mset_remove1 set_remove1_eq)

end
