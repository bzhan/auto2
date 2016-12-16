(* Verification of functional red-black trees. See RBT_Base for sources. *)

theory RBT_Func
imports RBT_Base
begin

section {* Balancing function on RBT *}

fun balanceR :: "('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt" where
  "balanceR (Node a B k1 v1 (Node (Node b R k3 v3 c) R k2 v2 d)) = Node (Node a B k1 v1 b) R k3 v3 (Node c B k2 v2 d)"
| "balanceR (Node a B k1 v1 (Node b R k2 v2 (Node c R k3 v3 d))) = Node (Node a B k1 v1 b) R k2 v2 (Node c B k3 v3 d)"
| "balanceR t = t"
setup {* fold add_rewrite_rule @{thms balanceR.simps(1,4-5)} *}

theorem balanceR_def' [rewrite]:
  "cl b = B \<Longrightarrow> balanceR (Node a B k1 v1 (Node b R k2 v2 (Node c R k3 v3 d))) = Node (Node a B k1 v1 b) R k2 v2 (Node c B k3 v3 d)"
  "cl r = B \<Longrightarrow> balanceR (Node l B k v r) = Node l B k v r"
  "cl r = R \<Longrightarrow> cl (lsub r) = B \<Longrightarrow> cl (rsub r) = B \<Longrightarrow> balanceR (Node l B k v r) = Node l B k v r"
  apply (metis balanceR.simps(2) balanceR.simps(3) pre_rbt.collapse)
  apply (metis balanceR.simps(15) balanceR.simps(6) pre_rbt.collapse)
  by (smt balanceR.simps(10) balanceR.simps(13) balanceR.simps(14) balanceR.simps(9) pre_rbt.collapse red_not_leaf)

fun balance :: "('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt" where
  "balance (Node (Node (Node a R k3 v3 b) R k2 v2 c) B k1 v1 d) = Node (Node a B k3 v3 b) R k2 v2 (Node c B k1 v1 d)"
| "balance (Node (Node a R k2 v2 (Node b R k3 v3 c)) B k1 v1 d) = Node (Node a B k2 v2 b) R k3 v3 (Node c B k1 v1 d)"
| "balance t = balanceR t"
setup {* fold add_rewrite_rule @{thms balance.simps(1,4)} *}

theorem balance_def' [rewrite]:
  "balance (Node l R k v r) = Node l R k v r"
  "cl a = B \<Longrightarrow> balance (Node (Node a R k2 v2 (Node b R k3 v3 c)) B k1 v1 d) = Node (Node a B k2 v2 b) R k3 v3 (Node c B k1 v1 d)"
  "cl l = B \<Longrightarrow> balance (Node l B k v r) = balanceR (Node l B k v r)"
  "cl l = R \<Longrightarrow> cl (lsub l) = B \<Longrightarrow> cl (rsub l) = B \<Longrightarrow> balance (Node l B k v r) = balanceR (Node l B k v r)"
  apply simp apply (metis balance.simps(2) balance.simps(3) pre_rbt.collapse)
  apply (metis balance.simps(14) balance.simps(5) pre_rbt.collapse)
  by (smt balance.simps(11) balance.simps(12) balance.simps(4) balance.simps(7) balance.simps(8) pre_rbt.collapse red_not_leaf)

text {*
  Script specifying the case checking needed when proving theorems involving
  balanceR t / balance t.
*}

ML {*
(* For balanceR t *)
val balanceR_cases =
CASE "t = Leaf"
THEN CASE "cl t = B" WITH
  CASE "cl (rsub t) = R" WITH
    (CASE "cl (lsub (rsub t)) = R" THEN CASE "cl (rsub (rsub t)) = R")

(* For balance t *)
val balance_cases =
CASE "t = Leaf"
THEN CASE "cl t = B" WITH
  CASE "cl (lsub t) = R" WITH
    (CASE "cl (lsub (lsub t)) = R" THEN CASE "cl (rsub (lsub t)) = R")

(* For balanceR (Node l B x r) *)
val balanceR_node_cases =
  CASE "cl r = R" WITH (CASE "cl (lsub r) = R" THEN CASE "cl (rsub r) = R")

(* For balance (Node l B x r) *)
val balance_node_cases =
  CASE "cl l = R" WITH (CASE "cl (lsub l) = R" THEN CASE "cl (rsub l) = R")
*}

subsection {* balance function preserves bd_inv *}

theorem balance_bd': "bd_inv t \<Longrightarrow> bd_inv (balanceR t) \<and> black_depth t = black_depth (balanceR t)"
  by (tactic {* auto2s_tac @{context} balanceR_cases *})
setup {* fold add_backward_prfstep [conj_left_th @{thm balance_bd'}, conj_right_th @{thm balance_bd'}] *}

theorem balance_bd: "bd_inv t \<Longrightarrow> bd_inv (balance t) \<and> black_depth (balance t) = black_depth t"
  by (tactic {* auto2s_tac @{context} balance_cases *})
setup {* add_backward_prfstep (conj_left_th @{thm balance_bd}) #> add_rewrite_rule (conj_right_th @{thm balance_bd}) *}

subsection {* balance function preserves cl_inv *}

theorem balanceR [backward1, backward2]:
  "cl_inv l \<Longrightarrow> cl_inv' r \<Longrightarrow> cl_inv (balanceR (Node l B k v r))"
  by (tactic {* auto2s_tac @{context} balanceR_node_cases *})

theorem balance1 [backward1, backward2]:
  "cl_inv' l \<Longrightarrow> cl_inv r \<Longrightarrow> cl_inv (balance (Node l B k v r))"
  by (tactic {* auto2s_tac @{context} balance_node_cases *})
theorem balance2 [backward1, backward2]:
  "cl_inv l \<Longrightarrow> cl_inv' r \<Longrightarrow> cl_inv (balance (Node l B k v r))"
  by (tactic {* auto2s_tac @{context} balance_node_cases *})
setup {* del_prfstep_thm @{thm balanceR} *}

subsection {* Balance function takes non-leafs to non-leafs *}

theorem balanceR_non_Leaf [resolve]: "balanceR (Node l c k v r) \<noteq> Leaf"
  by (tactic {* auto2s_tac @{context} (CASE "c = R" THEN balanceR_node_cases) *})
theorem balance_non_Leaf: "balance (Node l c k v r) \<noteq> Leaf"
  by (tactic {* auto2s_tac @{context} (CASE "c = R" THEN balance_node_cases) *})
setup {* add_forward_prfstep_cond @{thm balance_non_Leaf} [with_term "balance (Node ?l ?c ?k ?v ?r)"] *}

section {* ins function *}

fun ins :: "'a::order \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt" where
  "ins x v Leaf = Node Leaf R x v Leaf"
| "ins x v (Node l c y w r) =
    (if x = y then Node l c x v r
     else if x < y then balance (Node (ins x v l) c y w r)
     else balance (Node l c y w (ins x v r)))"
setup {* fold add_rewrite_rule @{thms ins.simps} *}

subsection {* ins function takes non-leaf to non-leafs *}

theorem ins_non_Leaf: "ins x v t \<noteq> Leaf" by auto2
setup {* add_forward_prfstep_cond @{thm ins_non_Leaf} [with_term "ins ?x ?v ?t"] *}

subsection {* Properties of ins function on cl_inv, bd_inv, and set of keys *}

theorem cl_inv_ins:
  "cl_inv t \<Longrightarrow> if cl t = B then cl_inv (ins x v t) else cl (ins x v t) = R \<and> cl_inv' (ins x v t)" by auto2

setup {* add_forward_prfstep_cond @{thm cl_inv_ins} [with_term "ins ?x ?v ?t"] *}
theorem cl_inv_ins_l [backward]: "cl_inv t \<Longrightarrow> cl_inv (lsub (ins x v t))" by auto2
theorem cl_inv_ins_r [backward]: "cl_inv t \<Longrightarrow> cl_inv (rsub (ins x v t))" by auto2
setup {* del_prfstep_thm @{thm cl_inv_ins} *}

theorem bd_inv_ins: "bd_inv t \<Longrightarrow> bd_inv (ins x v t) \<and> black_depth t = black_depth (ins x v t)"
  by (tactic {* auto2s_tac @{context} (CASE "cl t = R") *})
setup {* add_forward_prfstep_cond (conj_left_th @{thm bd_inv_ins}) [with_term "ins ?x ?v ?t"] *}

section {* Insert function *}

fun makeBlack :: "('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt" where
  "makeBlack Leaf = Leaf"
| "makeBlack (Node l c x v r) = Node l B x v r"

definition rbt_insert :: "'a::order \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt" where
  "rbt_insert x v t = makeBlack (ins x v t)"

setup {* fold add_rewrite_rule (@{thms makeBlack.simps} @ [@{thm rbt_insert_def}]) *}

theorem rbt_set_makeBlack [rewrite]: "rbt_set (makeBlack t) = rbt_set t" by auto2

theorem cl_inv_insert [backward]: "cl_inv t \<Longrightarrow> cl_inv (rbt_insert x v t)" by auto2
theorem bd_inv_insert [backward]: "bd_inv t \<Longrightarrow> bd_inv (rbt_insert x v t)" by auto2

theorem is_rbt_insert: "is_rbt t \<Longrightarrow> is_rbt (rbt_insert x v t)" by auto2

section {* Sortedness, sets, and maps *}

theorem balanceR_inorder_pairs [rewrite]: "rbt_in_traverse_pairs (balanceR t) = rbt_in_traverse_pairs t"
  by (tactic {* auto2s_tac @{context} balanceR_cases *})

theorem balance_inorder_pairs [rewrite]: "rbt_in_traverse_pairs (balance t) = rbt_in_traverse_pairs t"
  by (tactic {* auto2s_tac @{context} balance_cases *})

theorem balance_inorder [rewrite]: "rbt_in_traverse (balance t) = rbt_in_traverse t"
  by (tactic {* auto2s_tac @{context}
    (HAVE "rbt_in_traverse_pairs (balance t) = rbt_in_traverse_pairs t") *})

theorem ins_inorder [rewrite]:
  "rbt_sorted t \<Longrightarrow> rbt_in_traverse (ins x v t) = ordered_insert x (rbt_in_traverse t)" by auto2

theorem ins_inorder_pairs [rewrite]:
  "rbt_sorted t \<Longrightarrow> rbt_in_traverse_pairs (ins x v t) = ordered_insert_pairs x v (rbt_in_traverse_pairs t)" by auto2

theorem insert_inorder [rewrite]:
  "rbt_sorted t \<Longrightarrow> rbt_in_traverse (rbt_insert x v t) = ordered_insert x (rbt_in_traverse t)"
  by (tactic {* auto2s_tac @{context}
    (HAVE "rbt_in_traverse (rbt_insert x v t) = rbt_in_traverse (ins x v t)") *})

theorem insert_inorder_pairs [rewrite]:
  "rbt_sorted t \<Longrightarrow> rbt_in_traverse_pairs (rbt_insert x v t) = ordered_insert_pairs x v (rbt_in_traverse_pairs t)"
  by (tactic {* auto2s_tac @{context}
    (HAVE "rbt_in_traverse_pairs (rbt_insert x v t) = rbt_in_traverse_pairs (ins x v t)") *})

theorem insert_rbt_set: "rbt_sorted t \<Longrightarrow> rbt_set (rbt_insert x v t) = {x} \<union> rbt_set t" by auto2

theorem insert_sorted: "rbt_sorted t \<Longrightarrow> rbt_sorted (rbt_insert x v t)" by auto2

theorem insert_rbt_map: "rbt_sorted t \<Longrightarrow> rbt_map (rbt_insert x v t) = (rbt_map t) {x \<rightarrow> v}" by auto2

section {* Search on sorted trees and its correctness *}

fun rbt_search :: "('a::ord, 'b) pre_rbt \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "rbt_search Leaf x = None"
| "rbt_search (Node l c y w r) x =
  (if x = y then Some w
   else if x < y then rbt_search l x
   else rbt_search r x)"
setup {* fold add_rewrite_rule @{thms rbt_search.simps} *}

theorem rbt_search_correct: "rbt_sorted t \<Longrightarrow> rbt_search t x = (rbt_map t)\<langle>x\<rangle>" by auto2

end
