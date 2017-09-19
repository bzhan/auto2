(* Base of binary search trees, to be used in verification of both
   functional and imperative programs. *)

theory BST_Base
imports Lists_Ex
begin

section {* Definition and setup for trees *}

datatype ('a, 'b) tree =
    Tip | Node (lsub: "('a, 'b) tree") (key: 'a) (nval: 'b) (rsub: "('a, 'b) tree")

setup {* add_resolve_prfstep @{thm tree.distinct(2)} *}
setup {* add_forward_prfstep (equiv_forward_th (@{thm tree.simps(1)})) *}
setup {* fold add_rewrite_rule @{thms tree.sel} *}
setup {* add_forward_prfstep_cond @{thm tree.collapse} [with_cond "?tree \<noteq> Node ?l ?k ?v ?r"] *}
setup {* add_var_induct_rule @{thm tree.induct} *}

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
  "map fst (in_traverse_pairs t) = in_traverse t"
@proof @induct t @qed

definition tree_map :: "('a, 'b) tree \<Rightarrow> ('a, 'b) map" where
  "tree_map t = map_of_alist (in_traverse_pairs t)"
setup {* add_rewrite_rule @{thm tree_map_def} *}

section {* Sortedness on trees *}

fun tree_sorted :: "('a::linorder, 'b) tree \<Rightarrow> bool" where
  "tree_sorted Tip = True"
| "tree_sorted (Node l k v r) = ((\<forall>x\<in>tree_set l. x < k) \<and> (\<forall>x\<in>tree_set r. k < x)
                              \<and> tree_sorted l \<and> tree_sorted r)"
setup {* fold add_rewrite_rule @{thms tree_sorted.simps} *}
setup {* add_property_const @{term tree_sorted} *}

theorem tree_sorted_lr [forward]:
  "tree_sorted (Node l k v r) \<Longrightarrow> tree_sorted l \<and> tree_sorted r" by auto2

theorem inorder_preserve_set [rewrite_back]:
  "set (in_traverse t) = tree_set t"
@proof @induct t @qed

theorem inorder_sorted [rewrite_back]:
  "strict_sorted (in_traverse t) = tree_sorted t"
@proof @induct t @qed

theorem inorder_pairs_sorted:
  "tree_sorted t \<Longrightarrow> strict_sorted (map fst (in_traverse_pairs t))" by auto2
setup {* add_forward_prfstep_cond @{thm inorder_pairs_sorted} [with_term "in_traverse_pairs ?t"] *}

(* Use definition in terms of in_traverse from now on. *)
setup {* fold del_prfstep_thm (@{thms tree_set.simps} @ @{thms tree_sorted.simps}) *}

section {* Rotation on trees *}

definition rotateL :: "('a, 'b) tree \<Rightarrow> ('a, 'b) tree" where [rewrite]:
  "rotateL t = (if t = Tip then t else if rsub t = Tip then t else
    (let rt = rsub t in
     Node (Node (lsub t) (key t) (nval t) (lsub rt)) (key rt) (nval rt) (rsub rt)))"

definition rotateR :: "('a, 'b) tree \<Rightarrow> ('a, 'b) tree" where [rewrite]:
  "rotateR t = (if t = Tip then t else if lsub t = Tip then t else
    (let lt = lsub t in
     Node (lsub lt) (key lt) (nval lt) (Node (rsub lt) (key t) (nval t) (rsub t))))"

lemma rotateL_in_trav [rewrite]: "in_traverse (rotateL t) = in_traverse t" by auto2
lemma rotateR_in_trav [rewrite]: "in_traverse (rotateR t) = in_traverse t" by auto2

lemma rotateL_sorted [forward]: "tree_sorted t \<Longrightarrow> tree_sorted (rotateL t)" by auto2
lemma rotateR_sorted [forward]: "tree_sorted t \<Longrightarrow> tree_sorted (rotateR t)" by auto2

end
