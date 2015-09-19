theory Lists_Ex
imports Auto2 Lists_Thms
begin

section {* Linear time version of rev *}

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev []       ys = ys" |
  "itrev (x # xs) ys = itrev xs (x # ys)"
setup {* fold add_rewrite_rule @{thms itrev.simps} *}

lemma itrev_prop: "itrev x y = rev x @ y"
  by (tactic {* auto2s_tac @{context} (LIST_INDUCT ("x", ["y"])) *})
setup {* add_rewrite_rule @{thm itrev_prop} *}

lemma itrev_eq_rev: "itrev x [] = rev x" by auto2

section {* sorted function on lists *}

fun strict_sorted :: "'a::linorder list \<Rightarrow> bool" where
  "strict_sorted [] = True"
| "strict_sorted (x # ys) = ((\<forall>y\<in>set ys. x < y) \<and> strict_sorted ys)"
setup {* fold add_rewrite_rule @{thms strict_sorted.simps} *}

theorem strict_sorted_single: "strict_sorted [x]" by auto2
setup {* add_resolve_prfstep @{thm strict_sorted_single} #>
  del_prfstep_thm @{thm strict_sorted.simps(2)} #>
  add_rewrite_rule_cond @{thm strict_sorted.simps(2)} [with_cond "?ys \<noteq> []"] *}

theorem strict_sorted_append:
  "strict_sorted (xs @ ys) =
    ((\<forall>x y. x \<in> set xs \<longrightarrow> y \<in> set ys \<longrightarrow> x < y) \<and> strict_sorted xs \<and> strict_sorted ys)"
  by (tactic {* auto2s_tac @{context} (LIST_INDUCT ("xs", [])) *})
setup {* add_rewrite_rule @{thm strict_sorted_append} *}

theorem strict_sorted_append_one:
  "strict_sorted (xs @ [y]) = (\<forall>x\<in>set xs. x < y \<and> strict_sorted xs)" by auto2

section {* Insertion sort *}

fun ordered_insert :: "'a::ord \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "ordered_insert x [] = [x]"
| "ordered_insert x (y # ys) = (
    if x < y then x # (y # ys)
    else y # ordered_insert x ys)"
setup {* fold add_rewrite_rule @{thms ordered_insert.simps} *}

theorem ordered_insert_multiset: "multiset_of (ordered_insert x ys) = {#x#} + multiset_of ys" by auto2
setup {* add_rewrite_rule @{thm ordered_insert_multiset} *}
theorem ordered_insert_set: "set (ordered_insert x ys) = {x} \<union> set ys" by auto2
setup {* add_rewrite_rule @{thm ordered_insert_set} *}

theorem ordered_insert_sorted: "sorted ys \<Longrightarrow> sorted (ordered_insert x ys)" by auto2
setup {* add_backward_prfstep @{thm ordered_insert_sorted} *}

section {* Deleting an element *}

fun remove_elt_list :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remove_elt_list x [] = []"
| "remove_elt_list x (y # ys) = (if y = x then remove_elt_list x ys else y # remove_elt_list x ys)"
setup {* fold add_rewrite_rule @{thms remove_elt_list.simps} *}

theorem remove_elt_list_correct: "set (remove_elt_list x ys) = set ys - {x}" by auto2
setup {* add_rewrite_rule @{thm remove_elt_list_correct} *}

theorem remove_elt_list_sorted: "sorted ys \<Longrightarrow> sorted (remove_elt_list x ys)" by auto2
theorem remove_elt_list_strict_sorted: "strict_sorted ys \<Longrightarrow> strict_sorted (remove_elt_list x ys)" by auto2
setup {* fold add_backward_prfstep [@{thm remove_elt_list_sorted}, @{thm remove_elt_list_strict_sorted}] *}

section {* Merge sort *}

fun merge_list :: "('a::ord) list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "merge_list xs [] = xs"
| "merge_list [] ys = ys"
| "merge_list (x # xs) (y # ys) = (
    if x \<le> y then x # (merge_list xs (y # ys))
    else y # (merge_list (x # xs) ys))"
setup {* fold add_rewrite_rule @{thms merge_list.simps} *}
theorem merge_list_simp2': "merge_list [] ys = ys" by auto2
setup {* del_prfstep_thm @{thm merge_list.simps(2)} #> add_rewrite_rule @{thm merge_list_simp2'} *}

theorem merge_list_correct: "set (merge_list xs ys) = set xs \<union> set ys"
  by (tactic {* auto2s_tac @{context} (LIST_DOUBLE_INDUCT ("xs", "ys", [])) *})
setup {* add_rewrite_rule @{thm merge_list_correct} *}

theorem merge_list_sorted: "sorted xs \<Longrightarrow> sorted ys \<Longrightarrow> sorted (merge_list xs ys)"
  by (tactic {* auto2s_tac @{context} (LIST_DOUBLE_INDUCT ("xs", "ys", [])) *})
setup {* add_backward2_prfstep @{thm merge_list_sorted} *}

section {* Definition and setup for trees *}

datatype 'a tree =
    Tip
  | Node (lsub: "'a tree") (nval: 'a) (rsub: "'a tree")

setup {* add_rew_const @{term "Tip"} *}
setup {* add_resolve_prfstep @{thm tree.distinct(2)} *}
setup {* add_forward_prfstep (equiv_forward_th (@{thm tree.simps(1)})) *}
theorem if_not_Tip: "(if Node l v r = Tip then a else b) = b" by simp
setup {* add_rewrite_rule @{thm if_not_Tip} *}

text {* Case checking for trees: first verify the Tip case, then can assume t is
  in the form Node l n r. *}

setup {* add_gen_prfstep ("tree_case_intro",
  [WithTerm @{term_pat "?t::?'a tree"},
   Filter (unique_free_filter "t"),
   CreateCase ([@{term_pat "(?t::?'a tree) = Tip"}], [])]) *}
setup {* add_forward_prfstep_cond @{thm tree.collapse} [with_cond "?tree \<noteq> Node ?l ?v ?r"] *}

text {* Induction on trees: after checking Tip case, can assume P (lsub t)
  and P (rsub t) holds when trying to prove P t. *}

theorem tree_induct': "P Tip \<Longrightarrow> (\<forall>t. P (lsub t) \<and> P (rsub t) \<longrightarrow> P t) \<Longrightarrow> P t"
  apply (induction t) apply blast by (metis tree.sel(1) tree.sel(3))
setup {* add_prfstep_induction @{thm tree_induct'} *}

ML {*
fun TREE_INDUCT (var, extra_vars) =
  CASE (var ^ " = Tip") THEN INDUCT (var, (OnFact (var ^ " \<noteq> Tip") :: Arbitraries extra_vars))
fun TREE_INDUCT_NEWVAR (exp, var, extra_vars) =
  CASE (exp ^ " = Tip") THEN
  INDUCT (var ^ " = " ^ exp, (OnFact (exp ^ " \<noteq> Tip") :: Arbitraries extra_vars))
*}

section {* Inorder traversal, and set of elements of a tree *}

fun in_traverse :: "'a tree \<Rightarrow> 'a list" where
  "in_traverse Tip = []"
| "in_traverse (Node l a r) = (in_traverse l) @ [a] @ (in_traverse r)"

fun tree_set :: "'a tree \<Rightarrow> 'a set" where
  "tree_set Tip = {}"
| "tree_set (Node l y r) = {y} \<union> tree_set l \<union> tree_set r"
setup {* fold add_rewrite_rule (@{thms in_traverse.simps} @ @{thms tree_set.simps}) *}

theorem in_traverse_non_empty: "t \<noteq> Tip \<Longrightarrow> in_traverse t \<noteq> []" by auto2
setup {* add_forward_prfstep_cond @{thm in_traverse_non_empty} [with_term "in_traverse ?t"] *}

theorem inorder_preserve_set: "set (in_traverse t) = tree_set t" by auto2
setup {* add_rewrite_rule_bidir @{thm inorder_preserve_set} *}

section {* Sortedness on trees *}

fun tree_sorted :: "'a::linorder tree \<Rightarrow> bool" where
  "tree_sorted Tip = True"
| "tree_sorted (Node l a r) = ((\<forall>x\<in>tree_set l. x < a) \<and> (\<forall>x\<in>tree_set r. a < x)
                              \<and> tree_sorted l \<and> tree_sorted r)"
setup {* fold add_rewrite_rule @{thms tree_sorted.simps} *}

theorem inorder_sorted: "strict_sorted (in_traverse t) = tree_sorted t" by auto2
setup {* add_rewrite_rule_bidir @{thm inorder_sorted} *}

section {* Rotation on trees *}

fun rotateL :: "'a tree \<Rightarrow> 'a tree" where
  "rotateL Tip = Tip"
| "rotateL (Node a x Tip) = Node a x Tip"
| "rotateL (Node a x (Node b y c)) = Node (Node a x b) y c"

fun rotateR :: "'a tree \<Rightarrow> 'a tree" where
  "rotateR Tip = Tip"
| "rotateR (Node Tip x a) = Node Tip x a"
| "rotateR (Node (Node a x b) y c) = Node a x (Node b y c)"
setup {* fold add_rewrite_rule (@{thms rotateL.simps} @ @{thms rotateR.simps}) *}

ML {* val rotateL_cases = CASE "t = Tip" THEN CASE "rsub t = Tip"
      val rotateR_cases = CASE "t = Tip" THEN CASE "lsub t = Tip" *}

theorem rotateL_in_trav: "in_traverse (rotateL t) = in_traverse t"
  by (tactic {* auto2s_tac @{context} rotateL_cases *})
theorem rotateR_in_trav: "in_traverse (rotateR t) = in_traverse t"
  by (tactic {* auto2s_tac @{context} rotateR_cases *})
setup {* fold add_rewrite_rule [@{thm rotateL_in_trav}, @{thm rotateR_in_trav}] *}

theorem rotateL_sorted: "tree_sorted (rotateL t) = tree_sorted t" by auto2
theorem rotateR_sorted: "tree_sorted (rotateR t) = tree_sorted t" by auto2
setup {* fold add_rewrite_rule [@{thm rotateL_sorted}, @{thm rotateR_sorted}] *}

section {* Search on sorted trees *}

fun tree_search :: "'a::ord tree \<Rightarrow> 'a \<Rightarrow> bool" where
  "tree_search Tip x = False"
| "tree_search (Node l y r) x =
  (if x = y then True
   else if x < y then tree_search l x
   else tree_search r x)"
setup {* fold add_rewrite_rule @{thms tree_search.simps} *}

theorem tree_search_correct: "tree_sorted t \<Longrightarrow> (tree_search t x \<longleftrightarrow> x \<in> tree_set t)" by auto2

section {* Insertion on trees *}

fun tree_insert :: "'a::ord \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "tree_insert x Tip = Node Tip x Tip"
| "tree_insert x (Node l y r) =
    (if x = y then Node l y r
     else if x < y then Node (tree_insert x l) y r
     else Node l y (tree_insert x r))"
setup {* fold add_rewrite_rule @{thms tree_insert.simps} *}

theorem insert_present: "tree_set (tree_insert x t) = {x} \<union> tree_set t" by auto2
setup {* add_rewrite_rule @{thm insert_present} *}

theorem insert_sorted: "tree_sorted t \<Longrightarrow> tree_sorted (tree_insert x t)" by auto2
setup {* add_backward_prfstep @{thm insert_sorted} *}

section {* Deletion on trees *}

fun min_tree :: "'a tree \<Rightarrow> 'a" where
  "min_tree Tip = undefined"
| "min_tree (Node Tip y rt) = y"
| "min_tree (Node lt y rt) = min_tree lt"
setup {* fold add_rewrite_rule @{thms min_tree.simps(2-3)} *}

theorem min_tree_is_hd: "t \<noteq> Tip \<Longrightarrow> min_tree t = hd (in_traverse t)"
  by (tactic {* auto2s_tac @{context} (CASE "lsub t = Tip") *})
setup {* add_rewrite_rule @{thm min_tree_is_hd} *}

fun delete_min_tree :: "'a tree \<Rightarrow> 'a tree" where
  "delete_min_tree Tip = undefined"
| "delete_min_tree (Node Tip y rt) = rt"
| "delete_min_tree (Node lt y rt) = Node (delete_min_tree lt) y rt"
setup {* fold add_rewrite_rule @{thms delete_min_tree.simps(2-3)} *}

theorem delete_min_del_hd: "t \<noteq> Tip \<Longrightarrow> in_traverse (delete_min_tree t) = tl (in_traverse t)"
  by (tactic {* auto2s_tac @{context} (CASE "lsub t = Tip") *})
setup {* add_rewrite_rule @{thm delete_min_del_hd} *}

fun delete_elt_tree :: "'a tree \<Rightarrow> 'a tree" where
  "delete_elt_tree Tip = undefined"
| "delete_elt_tree (Node Tip v rt) = rt"
| "delete_elt_tree (Node lt v Tip) = lt"
| "delete_elt_tree (Node lt v rt) = Node lt (min_tree rt) (delete_min_tree rt)"
setup {* fold add_rewrite_rule @{thms delete_elt_tree.simps(2-4)} *}

theorem delete_elt_in_traverse:
  "in_traverse (delete_elt_tree (Node lt v rt)) = in_traverse lt @ in_traverse rt"
  by (tactic {* auto2s_tac @{context} (CASE "lt = Tip" THEN CASE "rt = Tip") *})
setup {* add_rewrite_rule @{thm delete_elt_in_traverse} *}

theorem delete_elt_on_set:
  "tree_sorted (Node lt v rt) \<Longrightarrow> tree_set (delete_elt_tree (Node lt v rt)) = tree_set (Node lt v rt) - {v}"
  by (tactic {* auto2s_tac @{context}
    (OBTAIN "tree_set (delete_elt_tree (Node lt v rt)) = tree_set lt \<union> tree_set rt" THEN
     OBTAIN "v \<notin> tree_set lt \<union> tree_set rt" WITH OBTAIN "v \<notin> tree_set lt") *})
setup {* add_rewrite_rule @{thm delete_elt_on_set} *}

theorem delete_elt_sorted:
  "tree_sorted (Node lt v rt) \<Longrightarrow> tree_sorted (delete_elt_tree (Node lt v rt))" by auto2
setup {* add_backward_prfstep @{thm delete_elt_sorted} *}

setup {* del_prfstep_thm @{thm min_tree_is_hd} *}

section {* More on rotation functions, to be used in RBT_Ex *}

fun rotateL_at_L :: "'a tree \<Rightarrow> 'a tree" where
  "rotateL_at_L Tip = Tip"
| "rotateL_at_L (Node l a r) = Node (rotateL l) a r"

fun rotateR_at_R :: "'a tree \<Rightarrow> 'a tree" where
  "rotateR_at_R Tip = Tip"
| "rotateR_at_R (Node l a r) = Node l a (rotateR r)"
setup {* fold add_rewrite_rule (@{thms rotateL_at_L.simps} @ @{thms rotateR_at_R.simps}) *}

theorem rotateL_at_L_def': "rotateL_at_L (Node (Node a z (Node b y c)) x d) = Node (Node (Node a z b) y c) x d" by auto2
theorem rotateR_at_R_def': "rotateR_at_R (Node a x (Node (Node b y c) z d)) = Node a x (Node b y (Node c z d))" by auto2
setup {* fold add_rewrite_rule [@{thm rotateL_at_L_def'}, @{thm rotateR_at_R_def'}] *}

theorem rotateL_at_L_sorted: "tree_sorted (rotateL_at_L t) = tree_sorted t" by auto2
theorem rotateR_at_R_sorted: "tree_sorted (rotateR_at_R t) = tree_sorted t" by auto2

setup {* fold add_rewrite_rule
  [@{thm rotateL_sorted}, @{thm rotateR_sorted}, @{thm rotateL_at_L_sorted}, @{thm rotateR_at_R_sorted}] *}

(* Forbid the introduction of in_traverse in future proofs. *)
setup {* fold del_prfstep ["inorder_preserve_set@sym", "inorder_sorted@sym"] *}

end
