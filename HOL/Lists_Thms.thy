(* Setup for proof steps related to lists. *)

theory Lists_Thms
imports Set_Thms
begin

section {* Definition of lists *}

setup {* add_resolve_prfstep @{thm list.distinct(2)} *}
setup {* add_forward_prfstep (equiv_forward_th @{thm list.simps(1)}) *}
setup {* fold add_rewrite_rule @{thms List.list.sel(1,3)} *}
setup {* add_forward_prfstep @{thm list.collapse} *}
setup {* add_var_induct_rule @{thm list.induct} *}

section {* Append *}

setup {* add_rewrite_rule @{thm List.append.simps(2)} *}
setup {* add_rewrite_rule @{thm List.hd_append2} *}

setup {* ACUtil.add_ac_data {
  cfhead = @{cterm "op @"}, unit = SOME @{cterm "[]"},
  assoc_th = @{thm List.append_assoc}, comm_th = true_th,
  unitl_th = @{thm List.append.append_Nil}, unitr_th = @{thm List.append_Nil2}}
*}

lemma append_is_empty [forward]: "xs @ ys = [] \<Longrightarrow> xs = [] \<and> ys = []" by simp

section {* Showing two lists are equal *}

setup {* add_backward2_prfstep_cond @{thm nth_equalityI} [with_filt (order_filter "xs" "ys")] *}

section {* nth *}

setup {* register_wellform_data ("xs ! i", ["i < length xs"]) *}
setup {* add_rewrite_rule_back @{thm hd_conv_nth} *}
setup {* add_rewrite_rule @{thm List.nth_Cons'} *}
setup {* add_rewrite_rule @{thm List.nth_append} *}

section {* Set of elements of a list *}

setup {* add_rewrite_rule @{thm List.set_simps(1)} *}
lemma set_simps2 [rewrite]: "set (x # xs) = {x} \<union> set xs" by simp
setup {* add_rewrite_rule @{thm List.set_append} *}
setup {* add_resolve_prfstep @{thm List.finite_set} *}

setup {* add_resolve_prfstep (equiv_forward_th @{thm in_set_conv_nth}) *}

section {* sorted *}

setup {* add_property_const @{term sorted} *}
setup {* fold add_resolve_prfstep [@{thm sorted.Nil}, @{thm sorted_single}] *}
setup {* add_backward_prfstep (equiv_backward_th @{thm sorted_Cons}) *}

lemma sorted_ConsD1 [forward]: "sorted (x # xs) \<Longrightarrow> sorted xs" using sorted_Cons by blast
lemma sorted_ConsD2 [forward, backward2]: "sorted (x # xs) \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<le> y"
  using sorted_Cons by blast  

lemma sorted_appendI [backward]:
  "sorted xs \<Longrightarrow> sorted ys \<Longrightarrow> \<forall>x\<in>set xs. \<forall>y\<in>set ys. x \<le> y \<Longrightarrow> sorted (xs @ ys)"
  by (simp add: sorted_append)

section {* distinct *}

setup {* add_property_const @{term distinct} *}
  
lemma distinct_Nil [resolve]: "distinct []" by simp
setup {* add_resolve_prfstep @{thm List.distinct_singleton} *}

lemma distinct_ConsI [backward]: "distinct xs \<Longrightarrow> \<forall>y\<in>set xs. x \<noteq> y \<Longrightarrow> distinct (x # xs)" by auto

lemma distinct_ConsD1 [forward]: "distinct (x # xs) \<Longrightarrow> distinct xs" by auto
lemma distinct_ConsD2 [forward]: "distinct (x # xs) \<Longrightarrow> x \<notin> set xs" by auto

section {* map function *}

setup {* fold add_rewrite_rule @{thms List.list.map} *}
setup {* add_rewrite_rule @{thm List.map_append} *}

section {* Replicate *}

setup {* add_rewrite_rule @{thm length_replicate} *}
setup {* add_rewrite_rule @{thm List.nth_replicate} *}

section {* last *}

setup {* add_rewrite_rule @{thm List.last_snoc} *}

section {* butlast *}

setup {* add_rewrite_rule @{thm length_butlast} *}
setup {* add_rewrite_rule @{thm nth_butlast} *}
setup {* add_rewrite_rule @{thm List.butlast_conv_take} *}
setup {* add_rewrite_rule @{thm List.butlast_snoc} *}

section {* List update *}

setup {* register_wellform_data ("xs[i := x]", ["i < length xs"]) *}
setup {* add_forward_prfstep_cond @{thm List.length_list_update} [with_term "?xs[?i := ?x]"] *}
setup {* add_rewrite_rule @{thm List.nth_list_update_eq} *}
setup {* add_rewrite_rule @{thm List.nth_list_update_neq} *}
setup {* add_rewrite_rule @{thm List.nth_list_update} *}

section {* take *}

setup {* register_wellform_data ("take n xs", ["n \<le> length xs"]) *}
setup {* add_prfstep_check_req ("take n xs", "n \<le> length xs") *}

lemma length_take: "n \<le> length xs \<Longrightarrow> length (take n xs) = n" by simp
setup {* add_forward_prfstep_cond @{thm length_take} [with_term "take ?n ?xs"] *}

lemma nth_take [rewrite]: "i < length (take n xs) \<Longrightarrow> take n xs ! i = xs ! i" by simp

setup {* add_rewrite_rule @{thm List.take_0} *}

section {* drop *}

setup {* add_forward_prfstep_cond @{thm List.length_drop} [with_term "drop ?n ?xs"] *}

lemma nth_drop [rewrite]: "i < length (drop n xs) \<Longrightarrow> drop n xs ! i = xs ! (n + i)" by simp

setup {* add_rewrite_rule @{thm List.drop_0} *}
setup {* add_rewrite_rule @{thm List.drop_all} *}

section {* rev *}

setup {* add_forward_prfstep_cond @{thm List.length_rev} [with_term "rev ?xs"] *}
setup {* fold add_rewrite_rule @{thms List.rev.simps} *}
setup {* add_rewrite_rule @{thm List.rev_append} *}

section {* mset *}

setup {* add_rewrite_rule @{thm mset.simps(1)} *}
lemma mset_simps_2 [rewrite]: "mset (a # x) = mset x + {#a#}" by simp
setup {* add_rewrite_rule @{thm mset_append} *}
setup {* add_backward2_prfstep @{thm mset_swap} *}

setup {* add_rewrite_rule @{thm mset_eq_setD} *}
lemma mset_butlast [forward]: "p \<in># mset (butlast xs) \<Longrightarrow> p \<in># mset xs" by (simp add: in_set_butlastD)
setup {* add_rewrite_rule_cond @{thm in_multiset_in_set} [with_term "set ?xs"] *}
setup {* add_rewrite_rule_back_cond @{thm in_multiset_in_set} [with_term "mset ?xs"] *}
setup {* add_backward_prfstep @{thm Multiset.nth_mem_mset} *}

lemma in_mset_conv_nth [resolve]: "x \<in># mset xs \<Longrightarrow> \<exists>i<length xs. x = xs ! i"
  by (metis in_multiset_in_set in_set_conv_nth)

section {* upto lists *}

lemma upt_zero_length [rewrite]: "length [0..<n] = n" by simp
lemma nth_upt_zero [rewrite]: "i < length [0..<n] \<Longrightarrow> [0..<n] ! i = i" by simp

section {* Lambda lists *}

definition list :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a list" where
  "list s n = map s [0 ..< n]"

lemma list_length: "length (list s n) = n" by (simp add: list_def)
setup {* add_forward_prfstep_cond @{thm list_length} [with_term "list ?s ?n"] *}
lemma list_nth [rewrite]: "i < length (list s n) \<Longrightarrow> (list s n) ! i = s i" by (simp add: list_def)

end
