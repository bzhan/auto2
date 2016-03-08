(* Setup for proof steps related to lists. *)

theory Lists_Thms
imports Auto2_Base
begin

section {* Case checking and induction *}

setup {* add_rew_const @{term "[]"} *}
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

lemma append_eq_first [backward]: "b = c \<Longrightarrow> a @ b = a @ c" by simp
lemma append_eq_second [backward]: "a = b \<Longrightarrow> a @ c = b @ c" by simp
theorem list_append_one [rewrite]: "[a] @ b = a # b" by simp
setup {* add_rewrite_rule_cond @{thm List.append.simps(2)} [with_cond "?xs \<noteq> []"] *}
theorem append_eq_empty [forward]: "xs @ ys = [] \<Longrightarrow> xs = [] \<and> ys = []" by simp

ML {*
val add_list_ac_data =
  fold ACUtil.add_ac_data [
    {fname = @{const_name append}, assoc_r = true,
     assoc_th = @{thm List.append_assoc}, comm_th = true_th,
     unit_val = @{term "[]"}, unit_th = @{thm List.append.simps(1)}, unitr_th = @{thm List.append_Nil2},
     uinv_name = "", inv_name = "", double_inv_th = true_th,
     distr_inv_th = true_th, binop_inv_th = true_th, unit_inv_th = true_th}]
*}
setup {* add_list_ac_data *}

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

end
