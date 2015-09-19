theory Lists_Thms
imports Auto2
begin

section {* Case checking and induction *}

setup {* add_rew_const @{term "[]"} *}
setup {* add_resolve_prfstep @{thm list.distinct(2)} *}
theorem list_constr: "x # xs = y # ys \<Longrightarrow> x = y \<and> xs = ys" by simp
setup {* add_forward_prfstep_cond (conj_left_th @{thm list_constr}) [with_cond "?x \<noteq> ?y"]
  #> add_forward_prfstep_cond (conj_right_th @{thm list_constr}) [with_cond "?xs \<noteq> ?ys"] *}

theorem list_eq_hd: "xs = ys \<Longrightarrow> x # xs = x # ys" by simp
theorem list_eq_tl: "x = y \<Longrightarrow> x # xs = y # xs" by simp
setup {* fold add_backward_prfstep [@{thm list_eq_hd}, @{thm list_eq_tl}] *}
setup {* fold add_rewrite_rule @{thms List.list.sel(1,3)} *}
setup {* add_rewrite_rule @{thm List.hd_append2} *}

text {* Case checking for lists: first verify the [] case, then split into hd :: tl. *}

setup {* add_gen_prfstep ("list_case_intro",
  [WithTerm @{term_pat "?x::?'a list"},
   Filter (unique_free_filter "x"),
   CreateCase ([@{term_pat "(?x::?'a list) = []"}], [])]) *}
setup {* add_forward_prfstep @{thm list.collapse} *}

text {* Induction. After proving a property P holds for [], can assume P holds
  for tl l when trying to show P l. *}

theorem list_induct': "P [] \<Longrightarrow> (\<forall>l. P (tl l) \<longrightarrow> P l) \<Longrightarrow> P l" by (metis list.sel(3) list_nonempty_induct)
setup {* add_prfstep_induction @{thm list_induct'} *}

text {* Simplified writing of induction on lists. Note expanded version still
  need to be used when there are WITH forms. *}
ML {*
fun LIST_INDUCT (var, extra_vars) =
  CASE (var ^ " = []") THEN INDUCT (var, OnFact (var ^ " \<noteq> []") :: Arbitraries extra_vars)
fun LIST_INDUCT_NEWVAR (exp, var, extra_vars) =
  CASE (exp ^ " = []") THEN
  INDUCT (var ^ " = " ^ exp, OnFact (exp ^ " \<noteq> []") :: Arbitraries extra_vars)
*}

text {* Induction on two lists. *}

theorem list_double_induct: "\<forall>ys. P [] ys \<Longrightarrow> \<forall>xs. P xs [] \<Longrightarrow> \<forall>xs ys. P (tl xs) ys \<and> P xs (tl ys) \<longrightarrow> P xs ys \<Longrightarrow> P xs ys"
  by (tactic {* auto2s_tac @{context} (LIST_INDUCT ("xs", []) THEN LIST_INDUCT ("ys", ["xs"])) *})
setup {* add_prfstep_double_induction @{thm list_double_induct} *}

ML {*
fun LIST_DOUBLE_INDUCT (var1, var2, extra_vars) =
  CASE (var1 ^ " = []") THEN CASE (var2 ^ " = []") THEN
  DOUBLE_INDUCT ((var1, var2), [OnFact (var1 ^ " \<noteq> []"), OnFact (var2 ^ " \<noteq> []")] @ Arbitraries extra_vars)
fun LIST_DOUBLE_INDUCT_NEWVAR (exp1, var1, exp2, var2, extra_vars) =
  CASE (exp1 ^ " = []") THEN CASE (exp2 ^ " = []") THEN
  DOUBLE_INDUCT (
    (var1 ^ " = " ^ exp1, var2 ^ " = " ^ exp2),
    [OnFact (exp1 ^ " \<noteq> []"), OnFact (exp2 ^ " \<noteq> []")] @ Arbitraries extra_vars)
*}

section {* Other functions *}

subsection {* append *}

theorem list_append_one: "[a] @ b = a # b" by simp
setup {* fold add_rewrite_rule [@{thm List.append.simps(1)}, @{thm List.append_Nil2}] #>
  add_rewrite_rule @{thm list_append_one} #>
  add_rewrite_rule_cond @{thm List.append.simps(2)} [with_cond "?xs \<noteq> []"] #>
  add_rewrite_rule_bidir_cond @{thm List.append_assoc} (with_conds ["?xs \<noteq> []", "?ys \<noteq> []", "?zs \<noteq> []"]) *}
theorem append_eq_empty: "xs @ ys = [] \<Longrightarrow> xs = [] \<and> ys = []" by simp
setup {* add_forward_prfstep @{thm append_eq_empty} *}

subsection {* rev *}

theorem rev_one: "rev [x] = [x]" by simp
setup {* add_rewrite_rule @{thm List.rev.simps(1)} #>
  add_rewrite_rule_cond @{thm List.rev.simps(2)} [with_cond "?xs \<noteq> []"] #>
  add_rewrite_rule @{thm rev_one} *}
setup {* add_rewrite_rule_cond @{thm List.rev_append} (with_conds ["?xs \<noteq> []", "?ys \<noteq> []"]) *}
theorem rev_nth': "n < length xs \<Longrightarrow> List.rev xs ! n = xs ! (length xs - 1 - n)" using rev_nth by auto
setup {* fold add_rewrite_rule [@{thm length_rev}, @{thm rev_nth'}] *}

subsection {* sorted *}

setup {* fold add_resolve_prfstep [@{thm sorted.Nil}, @{thm sorted_single}] *}
setup {* add_rewrite_rule_cond @{thm sorted_Cons} [with_cond "?xs \<noteq> []"]*}

subsection {* distinct *}

setup {* add_rewrite_rule @{thm distinct.simps(1)} #>
  add_known_fact @{thm distinct_singleton} #>
  add_rewrite_rule_cond @{thm distinct.simps(2)} [with_cond "?xs \<noteq> []"] *}

section {* Set of elements of a list *}

setup {* add_rewrite_rule @{thm List.set_simps(1)} *}
theorem set_list_single: "set [x] = {x}" by simp
setup {* add_rewrite_rule @{thm set_list_single} *}
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
   CreateCase ([@{term_pat "?x = ?a"}], [])]) *}

section {* Splitting of lists *}

setup {* add_resolve_prfstep @{thm split_list} *}
theorem list_split_neq_second: "xs \<noteq> as @ x # xs" by simp
setup {* add_resolve_prfstep @{thm list_split_neq_second} *}

section {* Showing two lists are equal *}
setup {* add_backward2_prfstep @{thm nth_equalityI} *}

end
