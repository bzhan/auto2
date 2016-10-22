(* Base of binary search trees, to be used in verification of both
   functional and imperative programs. *)

theory BST_Base
imports "../Lists_Ex" "../Mapping"
begin

section {* Definition and setup for trees *}

datatype ('a, 'b) tree =
    Tip | Node (lsub: "('a, 'b) tree") (key: 'a) (nval: 'b) (rsub: "('a, 'b) tree")

setup {* add_resolve_prfstep @{thm tree.distinct(2)} *}
setup {* add_forward_prfstep (equiv_forward_th (@{thm tree.simps(1)})) *}

text {* Case checking for trees: first verify the Tip case, then can assume t is
  in the form Node l n r. *}

setup {* add_gen_prfstep ("tree_case_intro",
  [WithTerm @{term_pat "?t::(?'a, ?'b) tree"},
   Filter (unique_free_filter "t"),
   CreateCase @{term_pat "(?t::(?'a, ?'b) tree) = Tip"}]) *}
setup {* add_forward_prfstep_cond @{thm tree.collapse} [with_cond "?tree \<noteq> Node ?l ?k ?v ?r"] *}

text {* Induction on trees: after checking Tip case, can assume P (lsub t)
  and P (rsub t) holds when trying to prove P t. *}

theorem tree_induct': "P Tip \<Longrightarrow> (\<forall>t. P (lsub t) \<and> P (rsub t) \<longrightarrow> P t) \<Longrightarrow> P t"
  apply (induct t) apply blast by (metis tree.sel(1) tree.sel(4))
setup {* add_prfstep_induction @{thm tree_induct'} *}

section {* Inorder traversal, and set of elements of a tree *}

fun in_traverse :: "('a, 'b) tree \<Rightarrow> 'a list" where
  "in_traverse Tip = []"
| "in_traverse (Node l k v r) = (in_traverse l) @ [k] @ (in_traverse r)"
setup {* fold add_rewrite_rule @{thms in_traverse.simps} *}

fun tree_set :: "('a, 'b) tree \<Rightarrow> 'a set" where
  "tree_set Tip = {}"
| "tree_set (Node l k v r) = {k} \<union> tree_set l \<union> tree_set r"
setup {* fold add_rewrite_rule @{thms tree_set.simps} *}

fun in_traverse_pairs :: "('a, 'b) tree \<Rightarrow> ('a \<times> 'b) list" where
  "in_traverse_pairs Tip = []"
| "in_traverse_pairs (Node l k v r) = (in_traverse_pairs l) @ [(k, v)] @ (in_traverse_pairs r)"
setup {* fold add_rewrite_rule @{thms in_traverse_pairs.simps} *}

theorem in_traverse_fst [rewrite]:
  "map fst (in_traverse_pairs t) = in_traverse t" by auto2
setup {* add_rewrite_rule_back_cond @{thm in_traverse_fst} [with_filt (size1_filter "t")] *}

definition tree_map :: "('a, 'b) tree \<Rightarrow> ('a, 'b) map" where
  "tree_map t = map_of_alist (in_traverse_pairs t)"
setup {* add_rewrite_rule @{thm tree_map_def} *}

theorem in_traverse_non_empty: "in_traverse (Node lt k v rt) \<noteq> []" by auto2
setup {* add_forward_prfstep_cond @{thm in_traverse_non_empty}
  [with_term "in_traverse (Node ?lt ?k ?v ?rt)"] *}

theorem in_traverse_pair_non_empty: "in_traverse_pairs (Node lt k v rt) \<noteq> []" by auto2
setup {* add_forward_prfstep_cond @{thm in_traverse_pair_non_empty}
  [with_term "in_traverse_pairs (Node ?lt ?k ?v ?rt)"] *}

section {* Sortedness on trees *}

fun tree_sorted :: "('a::linorder, 'b) tree \<Rightarrow> bool" where
  "tree_sorted Tip = True"
| "tree_sorted (Node l k v r) = ((\<forall>x\<in>tree_set l. x < k) \<and> (\<forall>x\<in>tree_set r. k < x)
                              \<and> tree_sorted l \<and> tree_sorted r)"
setup {* fold add_rewrite_rule @{thms tree_sorted.simps} *}

theorem inorder_preserve_set [rewrite_back]:
  "set (in_traverse t) = tree_set t" by auto2

theorem inorder_sorted [rewrite_back]:
  "strict_sorted (in_traverse t) = tree_sorted t" by auto2

(* Use definition in terms of in_traverse from now on. *)
setup {* fold del_prfstep_thm (@{thms tree_set.simps} @ @{thms tree_sorted.simps}) *}

section {* Rotation on trees *}

fun rotateL :: "('a, 'b) tree \<Rightarrow> ('a, 'b) tree" where
  "rotateL Tip = Tip"
| "rotateL (Node a k v Tip) = Node a k v Tip"
| "rotateL (Node a k1 v1 (Node b k2 v2 c)) = Node (Node a k1 v1 b) k2 v2 c"

fun rotateR :: "('a, 'b) tree \<Rightarrow> ('a, 'b) tree" where
  "rotateR Tip = Tip"
| "rotateR (Node Tip k v a) = Node Tip k v a"
| "rotateR (Node (Node a k1 v1 b) k2 v2 c) = Node a k1 v1 (Node b k2 v2 c)"
setup {* fold add_rewrite_rule (@{thms rotateL.simps} @ @{thms rotateR.simps}) *}

theorem rotateL_in_trav [rewrite]: "in_traverse (rotateL t) = in_traverse t"
  by (tactic {* auto2s_tac @{context} (CASE "t = Tip" THEN CASE "rsub t = Tip") *})
theorem rotateR_in_trav [rewrite]: "in_traverse (rotateR t) = in_traverse t"
  by (tactic {* auto2s_tac @{context} (CASE "t = Tip" THEN CASE "lsub t = Tip") *})

theorem rotateL_sorted [rewrite]: "tree_sorted (rotateL t) = tree_sorted t" by auto2
theorem rotateR_sorted [rewrite]: "tree_sorted (rotateR t) = tree_sorted t" by auto2

end
