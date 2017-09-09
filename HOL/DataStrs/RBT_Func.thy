(* Verification of functional red-black trees. See RBT_Base for sources. *)

theory RBT_Func
imports RBT_Base
begin

section {* Balancing function on RBT *}

definition balanceR :: "('a, 'b) pre_rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt" where
  "balanceR l k v r =
   (if cl r = R then
      let lr = lsub r; rr = rsub r in
      if cl lr = R then Node (Node l B k v (lsub lr)) R (key lr) (val lr) (Node (rsub lr) B (key r) (val r) rr)
      else if cl rr = R then Node (Node l B k v lr) R (key r) (val r) (Node (lsub rr) B (key rr) (val rr) (rsub rr))
      else Node l B k v r
    else Node l B k v r)"
setup {* add_rewrite_rule @{thm balanceR_def} *}
  
definition balance :: "('a, 'b) pre_rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt" where
  "balance l k v r =
   (if cl l = R then
      let ll = lsub l; rl = rsub l in
      if cl ll = R then Node (Node (lsub ll) B (key ll) (val ll) (rsub ll)) R (key l) (val l) (Node (rsub l) B k v r)
      else if cl rl = R then Node (Node (lsub l) B (key l) (val l) (lsub rl)) R (key rl) (val rl) (Node (rsub rl) B k v r)
      else balanceR l k v r
    else balanceR l k v r)"
setup {* add_rewrite_rule @{thm balance_def} *}

subsection {* balance function preserves bd_inv *}

lemma balanceR_bd [rewrite]:
  "bd_inv l \<Longrightarrow> bd_inv r \<Longrightarrow> black_depth l = black_depth r \<Longrightarrow>
   black_depth (balanceR l k v r) = black_depth l + 1" by auto2

lemma balanceR_bdinv:
  "bd_inv l \<Longrightarrow> bd_inv r \<Longrightarrow> black_depth l = black_depth r \<Longrightarrow> bd_inv (balanceR l k v r)" by auto2
setup {* add_forward_prfstep_cond @{thm balanceR_bdinv} [with_term "balanceR ?l ?k ?v ?r"] *}

lemma balance_bd [rewrite]:
  "bd_inv l \<Longrightarrow> bd_inv r \<Longrightarrow> black_depth l = black_depth r \<Longrightarrow>
   black_depth (balance l k v r) = black_depth l + 1" by auto2

lemma balance_bdinv:
  "bd_inv l \<Longrightarrow> bd_inv r \<Longrightarrow> black_depth l = black_depth r \<Longrightarrow> bd_inv (balance l k v r)" by auto2
setup {* add_forward_prfstep_cond @{thm balance_bdinv} [with_term "balance ?l ?k ?v ?r"] *}

subsection {* balance function preserves cl_inv *}

lemma balanceR_cl [backward1, backward2]:
  "cl_inv l \<Longrightarrow> cl_inv' r \<Longrightarrow> cl_inv (balanceR l k v r)" by auto2

lemma balance1 [backward1, backward2]:
  "cl_inv' l \<Longrightarrow> cl_inv r \<Longrightarrow> cl_inv (balance l k v r)" by auto2

lemma balance2 [backward1, backward2]:
  "cl_inv l \<Longrightarrow> cl_inv' r \<Longrightarrow> cl_inv (balance l k v r)" by auto2
setup {* del_prfstep_thm @{thm balanceR_cl} *}

section {* ins function *}

fun ins :: "'a::order \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt" where
  "ins x v Leaf = Node Leaf R x v Leaf"
| "ins x v (Node l c y w r) =
   (if c = B then
     (if x = y then Node l B x v r
      else if x < y then balance (ins x v l) y w r
      else balance l y w (ins x v r))
    else
     (if x = y then Node l R x v r
      else if x < y then Node (ins x v l) R y w r
      else Node l R y w (ins x v r)))"
setup {* fold add_rewrite_rule @{thms ins.simps} *}

subsection {* ins function takes non-leaf to non-leafs *}

lemma balanceR_non_Leaf [resolve]: "balanceR l k v r \<noteq> Leaf" by auto2

lemma balance_non_Leaf: "balance l k v r \<noteq> Leaf" by auto2
setup {* add_forward_prfstep_cond @{thm balance_non_Leaf} [with_term "balance (Node ?l ?c ?k ?v ?r)"] *}

lemma ins_non_Leaf: "ins x v t \<noteq> Leaf" @proof @case "t = Leaf" @qed
setup {* add_forward_prfstep_cond @{thm ins_non_Leaf} [with_term "ins ?x ?v ?t"] *}

subsection {* Properties of ins function on cl_inv and bd_inv *}

lemma cl_inv_ins [forward]:
  "cl_inv t \<Longrightarrow> cl_inv' (ins x v t)"
@proof
  @have "if cl t = B then cl_inv (ins x v t) else cl (ins x v t) = R \<and> cl_inv' (ins x v t)" @with
    @induct t
  @end
@qed

lemma bd_inv_ins:
  "bd_inv t \<Longrightarrow> bd_inv (ins x v t) \<and> black_depth t = black_depth (ins x v t)"
@proof @induct t @qed
setup {* add_forward_prfstep_cond (conj_left_th @{thm bd_inv_ins}) [with_term "ins ?x ?v ?t"] *}

section {* Insert function *}

fun makeBlack :: "('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt" where
  "makeBlack Leaf = Leaf"
| "makeBlack (Node l c x v r) = Node l B x v r"

definition rbt_insert :: "'a::order \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt" where
  "rbt_insert x v t = makeBlack (ins x v t)"

setup {* fold add_rewrite_rule (@{thms makeBlack.simps} @ [@{thm rbt_insert_def}]) *}

lemma rbt_set_makeBlack [rewrite]: "rbt_set (makeBlack t) = rbt_set t"
@proof @case "t = Leaf" @qed

lemma is_rbt_insert [forward]: "is_rbt t \<Longrightarrow> is_rbt (rbt_insert x v t)" by auto2

section {* Sortedness, sets, and maps *}

lemma balanceR_inorder_pairs [rewrite]:
  "rbt_in_traverse_pairs (balanceR l k v r) = rbt_in_traverse_pairs l @ [(k, v)] @ rbt_in_traverse_pairs r" by auto2

lemma balance_inorder_pairs [rewrite]:
  "rbt_in_traverse_pairs (balance l k v r) = rbt_in_traverse_pairs l @ [(k, v)] @ rbt_in_traverse_pairs r" by auto2

lemma balance_inorder [rewrite]:
  "rbt_in_traverse (balance l k v r) = rbt_in_traverse l @ [k] @ rbt_in_traverse r"
@proof
  @have "rbt_in_traverse_pairs (balance l k v r) = rbt_in_traverse_pairs l @ [(k, v)] @ rbt_in_traverse_pairs r"
@qed

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
