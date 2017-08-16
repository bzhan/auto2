(* Verification of functional programs on binary search trees. *)

theory BST_Func
imports BST_Base
begin

section {* Insertion on trees *}

fun tree_insert :: "'a::ord \<Rightarrow> 'b \<Rightarrow> ('a, 'b) tree \<Rightarrow> ('a, 'b) tree" where
  "tree_insert x v Tip = Node Tip x v Tip"
| "tree_insert x v (Node l y w r) =
    (if x = y then Node l x v r
     else if x < y then Node (tree_insert x v l) y w r
     else Node l y w (tree_insert x v r))"
setup {* fold add_rewrite_rule @{thms tree_insert.simps} *}

theorem insert_in_traverse [rewrite]:
  "tree_sorted t \<Longrightarrow> in_traverse (tree_insert x v t) = ordered_insert x (in_traverse t)"
@proof @induct t @qed
 
theorem insert_in_traverse_pairs [rewrite]:
  "tree_sorted t \<Longrightarrow> in_traverse_pairs (tree_insert x v t) = ordered_insert_pairs x v (in_traverse_pairs t)"
@proof @induct t @qed

theorem insert_on_set [rewrite]:
  "tree_sorted t \<Longrightarrow> tree_set (tree_insert x v t) = {x} \<union> tree_set t" by auto2

theorem insert_sorted [backward]:
  "tree_sorted t \<Longrightarrow> tree_sorted (tree_insert x v t)" by auto2

theorem insert_on_map:
  "tree_sorted t \<Longrightarrow> tree_map (tree_insert x v t) = (tree_map t) {x \<rightarrow> v}" by auto2

section {* Deletion on trees *}

fun del_min :: "('a, 'b) tree \<Rightarrow> ('a \<times> 'b) \<times> ('a, 'b) tree" where
  "del_min Tip = undefined"
| "del_min (Node Tip x v rt) = ((x, v), rt)"
| "del_min (Node lt x v rt) = (fst (del_min lt), Node (snd (del_min lt)) x v rt)"
setup {* fold add_rewrite_rule @{thms del_min.simps(2-3)} *}

theorem delete_min_del_hd [rewrite]:
  "t \<noteq> Tip \<Longrightarrow> fst (fst (del_min t)) # in_traverse (snd (del_min t)) = in_traverse t"
@proof
  @induct t @with
    @subgoal "t = Node l x v r" @case "l = Tip" @endgoal
  @end
@qed

theorem delete_min_del_hd_pairs [rewrite]:
  "t \<noteq> Tip \<Longrightarrow> fst (del_min t) # in_traverse_pairs (snd (del_min t)) = in_traverse_pairs t"
@proof
  @induct t @with
    @subgoal "t = Node l x v r" @case "l = Tip" @endgoal
  @end
@qed

fun delete_elt_tree :: "('a, 'b) tree \<Rightarrow> ('a, 'b) tree" where
  "delete_elt_tree Tip = undefined"
| "delete_elt_tree (Node Tip x v rt) = rt"
| "delete_elt_tree (Node lt x v Tip) = lt"
| "delete_elt_tree (Node lt x v rt) = Node lt (fst (fst (del_min rt))) (snd (fst (del_min rt))) (snd (del_min rt))"
setup {* fold add_rewrite_rule @{thms delete_elt_tree.simps(2-4)} *}

theorem delete_elt_in_traverse [rewrite]:
  "in_traverse (delete_elt_tree (Node lt x v rt)) = in_traverse lt @ in_traverse rt"
@proof @case "lt = Tip" @then @case "rt = Tip" @qed

theorem delete_elt_in_traverse_pairs [rewrite]:
  "in_traverse_pairs (delete_elt_tree (Node lt x v rt)) = in_traverse_pairs lt @ in_traverse_pairs rt"
@proof @case "lt = Tip" @then @case "rt = Tip" @qed

fun tree_delete :: "'a::ord \<Rightarrow> ('a, 'b) tree \<Rightarrow> ('a, 'b) tree" where
  "tree_delete x Tip = Tip"
| "tree_delete x (Node l y w r) =
    (if x = y then delete_elt_tree (Node l y w r)
     else if x < y then Node (tree_delete x l) y w r
     else Node l y w (tree_delete x r))"
setup {* fold add_rewrite_rule @{thms tree_delete.simps} *}

theorem tree_delete_in_traverse [rewrite]:
  "tree_sorted t \<Longrightarrow> in_traverse (tree_delete x t) = remove_elt_list x (in_traverse t)"
@proof @induct t @qed

theorem tree_delete_in_traverse_pairs [rewrite]:
  "tree_sorted t \<Longrightarrow> in_traverse_pairs (tree_delete x t) = remove_elt_pairs x (in_traverse_pairs t)"
@proof @induct t @qed

theorem tree_delete_sorted [backward]:
  "tree_sorted t \<Longrightarrow> tree_sorted (tree_delete x t)" by auto2

theorem tree_delete_map [rewrite]:
  "tree_sorted t \<Longrightarrow> tree_map (tree_delete x t) = delete_map x (tree_map t)" by auto2

section {* Search on sorted trees *}

fun tree_search :: "('a::ord, 'b) tree \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "tree_search Tip x = None"
| "tree_search (Node l k v r) x =
  (if x = k then Some v
   else if x < k then tree_search l x
   else tree_search r x)"
setup {* fold add_rewrite_rule @{thms tree_search.simps} *}

theorem tree_search_correct:
  "tree_sorted t \<Longrightarrow> tree_search t x = (tree_map t)\<langle>x\<rangle>"
@proof @induct t @qed

end
