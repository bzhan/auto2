(* Verification of functional red-black trees. See RBT_Base for sources. *)

theory RBT_Func
imports RBT_Base
begin

section {* Balancing function on RBT *}

fun balanceR :: "('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt" where
  "balanceR Leaf = Leaf"
| "balanceR (Node l c k v r) =
   (if c = R then Node l c k v r
    else if cl r = R then
      let lr = lsub r; rr = rsub r in
      if cl lr = R then Node (Node l B k v (lsub lr)) R (key lr) (val lr) (Node (rsub lr) B (key r) (val r) rr)
      else if cl rr = R then Node (Node l B k v lr) R (key r) (val r) (Node (lsub rr) B (key rr) (val rr) (rsub rr))
      else Node l c k v r
    else Node l c k v r)"
setup {* fold add_rewrite_rule @{thms balanceR.simps} *}
  
fun balance :: "('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt" where
  "balance Leaf = Leaf"
| "balance (Node l c k v r) =
   (if c = R then Node l c k v r
    else if cl l = R then
      let ll = lsub l; rl = rsub l in
      if cl ll = R then Node (Node (lsub ll) B (key ll) (val ll) (rsub ll)) R (key l) (val l) (Node (rsub l) B k v r)
      else if cl rl = R then Node (Node (lsub l) B (key l) (val l) (lsub rl)) R (key rl) (val rl) (Node (rsub rl) B k v r)
      else balanceR (Node l c k v r)
    else balanceR (Node l c k v r))"
setup {* fold add_rewrite_rule @{thms balance.simps} *}

subsection {* balance function preserves bd_inv *}

lemma balanceR_bd: "bd_inv t \<Longrightarrow> bd_inv (balanceR t) \<and> black_depth t = black_depth (balanceR t)"
@proof @case "t = Leaf" @qed

setup {* fold add_backward_prfstep [conj_left_th @{thm balanceR_bd}, conj_right_th @{thm balanceR_bd}] *}

theorem balance_bd: "bd_inv t \<Longrightarrow> bd_inv (balance t) \<and> black_depth (balance t) = black_depth t"
@proof @case "t = Leaf" @qed
setup {* add_backward_prfstep (conj_left_th @{thm balance_bd}) #> add_rewrite_rule (conj_right_th @{thm balance_bd}) *}

subsection {* balance function preserves cl_inv *}

lemma balanceR_cl [backward1, backward2]:
  "cl_inv l \<Longrightarrow> cl_inv' r \<Longrightarrow> cl_inv (balanceR (Node l B k v r))" by auto2

lemma balance1 [backward1, backward2]:
  "cl_inv' l \<Longrightarrow> cl_inv r \<Longrightarrow> cl_inv (balance (Node l B k v r))" by auto2

lemma balance2 [backward1, backward2]:
  "cl_inv l \<Longrightarrow> cl_inv' r \<Longrightarrow> cl_inv (balance (Node l B k v r))" by auto2
setup {* del_prfstep_thm @{thm balanceR_cl} *}

subsection {* Balance function takes non-leafs to non-leafs *}

lemma balanceR_non_Leaf [resolve]: "balanceR (Node l c k v r) \<noteq> Leaf" by auto2

lemma balance_non_Leaf: "balance (Node l c k v r) \<noteq> Leaf" by auto2
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

theorem ins_non_Leaf: "ins x v t \<noteq> Leaf" @proof @case "t = Leaf" @qed
setup {* add_forward_prfstep_cond @{thm ins_non_Leaf} [with_term "ins ?x ?v ?t"] *}

subsection {* Properties of ins function on cl_inv, bd_inv, and set of keys *}

theorem cl_inv_ins:
  "cl_inv t \<Longrightarrow> if cl t = B then cl_inv (ins x v t) else cl (ins x v t) = R \<and> cl_inv' (ins x v t)"
@proof @induct t @qed

setup {* add_forward_prfstep_cond @{thm cl_inv_ins} [with_term "ins ?x ?v ?t"] *}
theorem cl_inv_ins_l [backward]: "cl_inv t \<Longrightarrow> cl_inv (lsub (ins x v t))" by auto2
theorem cl_inv_ins_r [backward]: "cl_inv t \<Longrightarrow> cl_inv (rsub (ins x v t))" by auto2
setup {* del_prfstep_thm @{thm cl_inv_ins} *}

theorem bd_inv_ins:
  "bd_inv t \<Longrightarrow> bd_inv (ins x v t) \<and> black_depth t = black_depth (ins x v t)"
@proof
  @induct t @with
    @subgoal "t = Node l c y w r" @case "c = R" @endgoal
  @end
@qed
setup {* add_forward_prfstep_cond (conj_left_th @{thm bd_inv_ins}) [with_term "ins ?x ?v ?t"] *}

section {* Insert function *}

fun makeBlack :: "('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt" where
  "makeBlack Leaf = Leaf"
| "makeBlack (Node l c x v r) = Node l B x v r"

definition rbt_insert :: "'a::order \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt" where
  "rbt_insert x v t = makeBlack (ins x v t)"

setup {* fold add_rewrite_rule (@{thms makeBlack.simps} @ [@{thm rbt_insert_def}]) *}

theorem rbt_set_makeBlack [rewrite]: "rbt_set (makeBlack t) = rbt_set t"
  @proof @case "t = Leaf" @qed

theorem cl_inv_insert [backward]: "cl_inv t \<Longrightarrow> cl_inv (rbt_insert x v t)" by auto2
theorem bd_inv_insert [backward]: "bd_inv t \<Longrightarrow> bd_inv (rbt_insert x v t)" by auto2

theorem is_rbt_insert: "is_rbt t \<Longrightarrow> is_rbt (rbt_insert x v t)" by auto2

section {* Sortedness, sets, and maps *}

theorem balanceR_inorder_pairs [rewrite]: "rbt_in_traverse_pairs (balanceR t) = rbt_in_traverse_pairs t"
@proof @case "t = Leaf" @qed

theorem balance_inorder_pairs [rewrite]: "rbt_in_traverse_pairs (balance t) = rbt_in_traverse_pairs t"
@proof @case "t = Leaf" @qed

theorem balance_inorder [rewrite]: "rbt_in_traverse (balance t) = rbt_in_traverse t"
@proof @have "rbt_in_traverse_pairs (balance t) = rbt_in_traverse_pairs t" @qed

theorem ins_inorder [rewrite]:
  "rbt_sorted t \<Longrightarrow> rbt_in_traverse (ins x v t) = ordered_insert x (rbt_in_traverse t)"
@proof @induct t @qed

theorem ins_inorder_pairs [rewrite]:
  "rbt_sorted t \<Longrightarrow> rbt_in_traverse_pairs (ins x v t) = ordered_insert_pairs x v (rbt_in_traverse_pairs t)"
@proof @induct t @qed

theorem insert_inorder [rewrite]:
  "rbt_sorted t \<Longrightarrow> rbt_in_traverse (rbt_insert x v t) = ordered_insert x (rbt_in_traverse t)"
@proof @have "rbt_in_traverse (rbt_insert x v t) = rbt_in_traverse (ins x v t)" @qed

theorem insert_inorder_pairs [rewrite]:
  "rbt_sorted t \<Longrightarrow> rbt_in_traverse_pairs (rbt_insert x v t) = ordered_insert_pairs x v (rbt_in_traverse_pairs t)"
@proof @have "rbt_in_traverse_pairs (rbt_insert x v t) = rbt_in_traverse_pairs (ins x v t)" @qed

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

theorem rbt_search_correct [rewrite]:
  "rbt_sorted t \<Longrightarrow> rbt_search t x = (rbt_map t)\<langle>x\<rangle>"
@proof @induct t @qed

end
