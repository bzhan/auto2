(* Setup for proof steps related to lists. *)

theory Lists_Thms
imports Auto2_Base
begin

section {* Case checking and induction *}

setup {* add_resolve_prfstep @{thm list.distinct(2)} *}
theorem list_constr: "x # xs = y # ys \<Longrightarrow> x = y \<and> xs = ys" by simp
setup {* add_forward_prfstep_cond (conj_left_th @{thm list_constr}) [with_cond "?x \<noteq> ?y"]
  #> add_forward_prfstep_cond (conj_right_th @{thm list_constr}) [with_cond "?xs \<noteq> ?ys"] *}

theorem list_eq_hd [backward]: "xs = ys \<Longrightarrow> x # xs = x # ys" by simp
theorem list_eq_tl [backward]: "x = y \<Longrightarrow> x # xs = y # xs" by simp
setup {* fold add_rewrite_rule @{thms List.list.sel(1,3)} *}
setup {* add_rewrite_rule @{thm List.hd_append2} *}

text {* Case checking for lists: first verify the [] case, then split into hd :: tl. *}

setup {* add_gen_prfstep ("list_case_intro",
  [WithTerm @{term_pat "?x::?'a list"},
   Filter (unique_free_filter "x"),
   CreateCase @{term_pat "(?x::?'a list) = []"}]) *}
setup {* add_forward_prfstep @{thm list.collapse} *}

text {* Induction. After proving a property P holds for [], can assume P holds
  for tl l when trying to show P l. *}

theorem list_induct': "P [] \<Longrightarrow> (\<forall>l. P (tl l) \<longrightarrow> P l) \<Longrightarrow> P l"
  by (metis list.sel(3) list_nonempty_induct)
setup {* add_prfstep_induction @{thm list_induct'} *}

section {* Other functions *}

subsection {* append *}

lemma append_eq_first: "b = c \<Longrightarrow> a @ b = a @ c" by simp
lemma append_eq_second: "a = b \<Longrightarrow> a @ c = b @ c" by simp
setup {* add_backward_prfstep_cond @{thm append_eq_first} [with_term "?a"] *}
setup {* add_backward_prfstep_cond @{thm append_eq_second} [with_term "?c"] *}
theorem list_append_one [rewrite]: "[a] @ b = a # b" by simp
setup {* add_rewrite_rule_cond @{thm List.append.simps(2)} [with_cond "?xs \<noteq> []"] *}
theorem append_eq_empty [forward]: "xs @ ys = [] \<Longrightarrow> xs = [] \<and> ys = []" by simp

theorem append_is_assoc: "is_assoc_fn (op @)" by (simp add: is_assoc_fn_def)
theorem append_has_unit: "is_unit_fn [] (op @)" by (simp add: is_unit_fn_def)
ML {*
val add_list_ac_data =
  fold ACUtil.add_ac_data [
    {fname = @{const_name append},
     assoc_th = @{thm append_is_assoc}, comm_th = true_th,
     unit_th = @{thm append_has_unit}, uinv_th = true_th, inv_th = true_th}]
*}
setup {* add_list_ac_data *}

subsection {* length *}

theorem length_non_empty [resolve]: "length (x # xs) > 0" by simp
setup {* add_rewrite_rule @{thm length_replicate} *}
setup {* add_rewrite_rule @{thm List.list.size(3)} *}
setup {* add_rewrite_rule @{thm List.length_append} *}
theorem length_one [rewrite]: "length [x] = 1" by simp
theorem length_tl' [rewrite]: "l' \<noteq> [] \<Longrightarrow> length (tl l') + 1 = length l'" by simp
setup {* add_rewrite_rule_back_cond @{thm List.length_list_update} [with_term "list_update ?xs ?i ?x"] *}
setup {* add_rewrite_rule @{thm length_butlast} *}
theorem length_butlast': "xs \<noteq> [] \<Longrightarrow> length xs = length (butlast xs) + 1" by simp
setup {* add_forward_prfstep_cond @{thm length_butlast'} [with_term "length (butlast ?xs)"] *}

theorem list_last_singleton [rewrite]: "length xs = 1 \<Longrightarrow> last xs = hd xs"
  by (metis diff_is_0_eq hd_conv_nth last_conv_nth le_numeral_extra(4) length_greater_0_conv zero_less_one)

subsection {* nth *}

theorem nth_append1 [rewrite]: "i < length xs \<Longrightarrow> (xs @ ys) ! i = xs ! i" by (simp add: nth_append)
setup {* add_rewrite_rule_back @{thm hd_conv_nth} *}
setup {* add_rewrite_rule @{thm List.nth_take} *}
setup {* add_rewrite_rule @{thm nth_butlast} *}
setup {* add_rewrite_rule @{thm List.nth_list_update_neq} *}
setup {* add_rewrite_rule @{thm List.nth_list_update_eq} *}
setup {* add_rewrite_rule @{thm List.nth_append_length} *}
setup {* add_rewrite_rule @{thm List.nth_replicate} *}

subsection {* take and drop *}

setup {* add_rewrite_rule @{thm List.take_0} *}
setup {* add_rewrite_rule @{thm List.drop_0} *}
setup {* add_rewrite_rule @{thm List.append_take_drop_id} *}
theorem length_take' [rewrite]: "n \<le> length l \<Longrightarrow> length (take n l) = n" by simp
setup {* add_rewrite_rule @{thm take_update_swap} *}

subsection {* rev *}

theorem rev_one [rewrite]: "rev [x] = [x]" by simp
setup {* add_rewrite_rule @{thm List.rev.simps(1)} #>
  add_rewrite_rule_cond @{thm List.rev.simps(2)} [with_cond "?xs \<noteq> []"] #>
  add_rewrite_rule @{thm List.rev_append} *}
theorem rev_nth' [rewrite]:
  "n < length xs \<Longrightarrow> List.rev xs ! n = xs ! (length xs - 1 - n)" using rev_nth by auto
setup {* add_rewrite_rule @{thm length_rev} *}

subsection {* sorted *}

setup {* fold add_resolve_prfstep [@{thm sorted.Nil}, @{thm sorted_single}] *}
setup {* add_rewrite_rule_cond @{thm sorted_Cons} [with_cond "?xs \<noteq> []"]*}

subsection {* distinct *}

theorem distinct2 [rewrite]: "distinct [a, b] = (a \<noteq> b)" by simp
theorem distinct3 [rewrite]: "distinct [a, b, c] = (a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c)" by simp
setup {* add_rewrite_rule @{thm distinct.simps(1)} #>
  add_resolve_prfstep @{thm distinct_singleton} #>
  add_rewrite_rule_cond @{thm distinct.simps(2)} (
    with_conds ["?xs \<noteq> []", "?xs \<noteq> [?a]", "?xs \<noteq> [?a, ?b]"]) *}

section {* Set of elements of a list *}

setup {* add_rewrite_rule @{thm List.set_simps(1)} *}
theorem set_list_single [rewrite]: "set [x] = {x}" by simp
theorem set_list_simp2: "set (x # xs) = {x} \<union> set xs" by simp
setup {* add_rewrite_rule_cond @{thm set_list_simp2} [with_cond "?xs \<noteq> []"] *}
setup {* add_forward_prfstep_cond @{thm List.list.set_intros(1)} [with_term "set (?a1.0 # ?a2.0)"] *}
setup {* add_forward_prfstep_cond @{thm List.list.set_intros(2)} [with_term "set (?a1.0 # ?a2.0)"] *}
setup {* add_backward_prfstep @{thm List.list.set_intros(2)} *}
setup {* add_rewrite_rule @{thm List.set_append} *}

(* Apply just to the set of elements of a list for now. *)
setup {* add_gen_prfstep ("Un_single_case_list",
  [WithFact @{term_pat "?x \<in> {?a} \<union> set ?B"},
   Filter (neq_filter "x" "a"),
   CreateCase @{term_pat "?x = ?a"}]) *}

section {* Splitting of lists *}

setup {* add_resolve_prfstep @{thm split_list} *}
theorem list_split_neq_second [resolve]: "xs \<noteq> as @ x # xs" by simp

section {* Showing two lists are equal *}
setup {* add_backward2_prfstep @{thm nth_equalityI} *}

section {* Other operations *}

setup {* fold add_rewrite_rule @{thms removeAll.simps} *}
setup {* fold add_rewrite_rule @{thms listsum_simps} *}

end
