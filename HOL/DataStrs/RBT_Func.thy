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
setup {* register_wellform_data ("balance l k v r", ["black_depth l = black_depth r"]) *}
setup {* add_prfstep_check_req ("balance l k v r", "black_depth l = black_depth r") *}

subsection {* balance function preserves bd_inv *}

lemma balance_bdinv:
  "bd_inv l \<Longrightarrow> bd_inv r \<Longrightarrow> black_depth l = black_depth r \<Longrightarrow> bd_inv (balance l k v r)"
@proof @have "bd_inv (balanceR l k v r)" @qed
setup {* add_forward_prfstep_cond @{thm balance_bdinv} [with_term "balance ?l ?k ?v ?r"] *}

lemma balance_bd [rewrite]:
  "bd_inv l \<Longrightarrow> bd_inv r \<Longrightarrow> black_depth l = black_depth r \<Longrightarrow>
   black_depth (balance l k v r) = black_depth l + 1"
@proof @have "black_depth (balanceR l k v r) = black_depth l + 1" @qed

subsection {* balance function preserves cl_inv *}

lemma balance1 [forward]:
  "cl_inv' l \<Longrightarrow> cl_inv r \<Longrightarrow> cl_inv (balance l k v r)" by auto2

lemma balance2 [forward]:
  "cl_inv l \<Longrightarrow> cl_inv' r \<Longrightarrow> cl_inv (balance l k v r)" by auto2

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

lemma balance_non_Leaf [resolve]: "balance l k v r \<noteq> Leaf" by auto2

lemma ins_non_Leaf [resolve]: "ins x v t \<noteq> Leaf"
@proof @case "t = Leaf" @qed

subsection {* Properties of ins function on cl_inv and bd_inv *}

lemma cl_inv_ins [forward]:
  "cl_inv t \<Longrightarrow> cl_inv' (ins x v t)"
@proof
  @have "if cl t = B then cl_inv (ins x v t) else cl_inv' (ins x v t)" @with
    @induct t
  @end
@qed

lemma bd_inv_ins:
  "bd_inv t \<Longrightarrow> bd_inv (ins x v t) \<and> black_depth t = black_depth (ins x v t)"
@proof @induct t @qed
setup {* add_forward_prfstep_cond (conj_left_th @{thm bd_inv_ins}) [with_term "ins ?x ?v ?t"] *}

section {* Paint function *}

fun paint :: "color \<Rightarrow> ('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt" where
  "paint c Leaf = Leaf"
| "paint c (Node l c' x v r) = Node l c x v r"
setup {* fold add_rewrite_rule @{thms paint.simps} *}
setup {* register_wellform_data ("paint c t", ["t \<noteq> Leaf"]) *}
setup {* add_prfstep_check_req ("paint c t", "t \<noteq> Leaf") *}

lemma paint_cl_inv' [forward]: "cl_inv' t \<Longrightarrow> cl_inv' (paint c t)" by auto2

lemma paint_bd_inv [forward]: "bd_inv t \<Longrightarrow> bd_inv (paint c t)" by auto2

lemma paint_bd [rewrite]:
  "bd_inv t \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> cl t = B \<Longrightarrow> black_depth (paint R t) = black_depth t - 1" by auto2
    
lemma paint_in_traverse [rewrite]:
  "rbt_in_traverse (paint c t) = rbt_in_traverse t" by auto2

lemma paint_in_traverse_pairs [rewrite]:
  "rbt_in_traverse_pairs (paint c t) = rbt_in_traverse_pairs t" by auto2

section {* Insert function *}

definition rbt_insert :: "'a::order \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt" where [rewrite]:
  "rbt_insert x v t = paint B (ins x v t)"

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
    
section {* Deletion *}
    
definition balL :: "('a, 'b) pre_rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt" where
  "balL l k v r = (let lr = lsub r in
   if cl l = R then Node (Node (lsub l) B (key l) (val l) (rsub l)) R k v r
   else if r = Leaf then Node l R k v r
   else if cl r = B then balance l k v (Node (lsub r) R (key r) (val r) (rsub r))
   else if lr = Leaf then Node l R k v r
   else if cl lr = B then
     Node (Node l B k v (lsub lr)) R (key lr) (val lr) (balance (rsub lr) (key r) (val r) (paint R (rsub r)))
   else Node l R k v r)"
setup {* add_rewrite_rule @{thm balL_def} *}
setup {* register_wellform_data ("balL l k v r", ["black_depth l + 1 = black_depth r"]) *}
setup {* add_prfstep_check_req ("balL l k v r", "black_depth l + 1 = black_depth r") *}
  
definition balR :: "('a, 'b) pre_rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt" where
  "balR l k v r = (let rl = rsub l in
   if cl r = R then Node l R k v (Node (lsub r) B (key r) (val r) (rsub r))
   else if l = Leaf then Node l R k v r
   else if cl l = B then balance (Node (lsub l) R (key l) (val l) (rsub l)) k v r
   else if rl = Leaf then Node l R k v r
   else if cl rl = B then
     Node (balance (paint R (lsub l)) (key l) (val l) (lsub rl)) R (key rl) (val rl) (Node (rsub rl) B k v r)
   else Node l R k v r)"
setup {* add_rewrite_rule @{thm balR_def} *}
setup {* register_wellform_data ("balR l k v r", ["black_depth l = black_depth r + 1"]) *}
setup {* add_prfstep_check_req ("balR l k v r", "black_depth l = black_depth r + 1") *}

lemma balL_bd:
  "bd_inv l \<Longrightarrow> bd_inv r \<Longrightarrow> cl_inv r \<Longrightarrow> black_depth l + 1 = black_depth r \<Longrightarrow>
   bd_inv (balL l k v r) \<and> black_depth (balL l k v r) = black_depth l + 1" by auto2
setup {* add_forward_prfstep_cond @{thm balL_bd} [with_term "balL ?l ?k ?v ?r"] *}

lemma balL_bd':
  "bd_inv l \<Longrightarrow> r = Node r1 B k1 v1 r2 \<Longrightarrow> black_depth l + 1 = black_depth r \<Longrightarrow> bd_inv r \<Longrightarrow>
   bd_inv (balL l k v r) \<and> black_depth (balL l k v r) = black_depth r" by auto2
setup {* add_forward_prfstep_cond @{thm balL_bd'} [with_term "balL ?l ?k ?v ?r"] *}

lemma balL_cl:
  "cl_inv' l \<Longrightarrow> r = Node r1 B k1 v1 r2 \<Longrightarrow> cl_inv r \<Longrightarrow> cl_inv (balL l k v r)" by auto2
setup {* add_forward_prfstep_cond @{thm balL_cl} [with_term "balL ?l ?k ?v ?r"] *}

lemma balL_cl' [forward]:
  "cl_inv' l \<Longrightarrow> cl_inv r \<Longrightarrow> cl_inv' (balL l k v r)" by auto2

lemma balR_bd:
  "bd_inv l \<Longrightarrow> bd_inv r \<Longrightarrow> cl_inv l \<Longrightarrow> black_depth l = black_depth r + 1 \<Longrightarrow>
   bd_inv (balR l k v r) \<and> black_depth (balR l k v r) = black_depth l" by auto2
setup {* add_forward_prfstep_cond @{thm balR_bd} [with_term "balR ?l ?k ?v ?r"] *}

lemma balR_cl:
  "cl_inv l \<Longrightarrow> cl_inv' r \<Longrightarrow> cl l = B \<Longrightarrow> cl_inv (balR l k v r)" by auto2
setup {* add_forward_prfstep_cond @{thm balR_cl} [with_term "balR ?l ?k ?v ?r"] *}

lemma balR_cl' [forward]:
  "cl_inv l \<Longrightarrow> cl_inv' r \<Longrightarrow> cl_inv' (balR l k v r)" by auto2

lemma balL_in_traverse [rewrite]:
  "rbt_in_traverse (balL l k v r) = rbt_in_traverse l @ [k] @ rbt_in_traverse r" by auto2

lemma balR_in_traverse [rewrite]:
  "rbt_in_traverse (balR l k v r) = rbt_in_traverse l @ [k] @ rbt_in_traverse r" by auto2

lemma balL_in_traverse_pairs [rewrite]:
  "rbt_in_traverse_pairs (balL l k v r) = rbt_in_traverse_pairs l @ [(k, v)] @ rbt_in_traverse_pairs r" by auto2

lemma balR_in_traverse_pairs [rewrite]:
  "rbt_in_traverse_pairs (balR l k v r) = rbt_in_traverse_pairs l @ [(k, v)] @ rbt_in_traverse_pairs r" by auto2

fun combine :: "('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt" where
  "combine Leaf t = t"
| "combine t Leaf = t"
| "combine (Node l1 c1 k1 v1 r1) (Node l2 c2 k2 v2 r2) = (
   if c1 = R then
     if c2 = R then
       let tm = combine r1 l2 in
         if cl tm = R then
           Node (Node l1 R k1 v1 (lsub tm)) R (key tm) (val tm) (Node (rsub tm) R k2 v2 r2)
         else
           Node l1 R k1 v1 (Node tm R k2 v2 r2)
     else
       Node l1 R k1 v1 (combine r1 (Node l2 c2 k2 v2 r2))
   else
     if c2 = B then
       let tm = combine r1 l2 in
         if cl tm = R then
           Node (Node l1 B k1 v1 (lsub tm)) R (key tm) (val tm) (Node (rsub tm) B k2 v2 r2)
         else
           balL l1 k1 v1 (Node tm B k2 v2 r2)
     else
       Node (combine (Node l1 c1 k1 v1 r1) l2) R k2 v2 r2)"
setup {* fold add_rewrite_rule @{thms combine.simps} *}
setup {* add_fun_induct_rule (@{term_pat "combine (?a0.0::(?'a,?'b) pre_rbt) ?a1.0"}, @{thm combine.induct}) *}

lemma combine_bd:
  "bd_inv lt \<Longrightarrow> bd_inv rt \<Longrightarrow> black_depth lt = black_depth rt \<Longrightarrow>
   bd_inv (combine lt rt) \<and> black_depth (combine lt rt) = black_depth lt"
@proof @fun_induct "combine lt rt" @qed
setup {* add_forward_prfstep_cond @{thm combine_bd} [with_term "combine ?lt ?rt"] *}

lemma combine_cl:
  "cl_inv lt \<Longrightarrow> cl_inv rt \<Longrightarrow>
   (cl lt = B \<longrightarrow> cl rt = B \<longrightarrow> cl_inv (combine lt rt)) \<and> cl_inv' (combine lt rt)"
@proof @fun_induct "combine lt rt" @qed
setup {* add_forward_prfstep_cond @{thm combine_cl} [with_term "combine ?lt ?rt"] *}

lemma combine_in_traverse_pairs [rewrite]:
  "rbt_in_traverse_pairs (combine lt rt) = rbt_in_traverse_pairs lt @ rbt_in_traverse_pairs rt"
@proof @fun_induct "combine lt rt" @with
  @subgoal "(lt = Node l1 c1 k1 v1 r1, rt = Node l2 c2 k2 v2 r2)"
    @case "c1 = R" @with @case "c2 = R" @with @case "cl (combine r1 l2) = R" @with
      @have "rbt_in_traverse_pairs (combine (Node l1 c1 k1 v1 r1) (Node l2 c2 k2 v2 r2)) =
             rbt_in_traverse_pairs l1 @ [(k1, v1)] @ rbt_in_traverse_pairs (combine r1 l2) @ [(k2, v2)] @ rbt_in_traverse_pairs r2"
    @end @end @end
    @case "c1 = B" @with @case "c2 = B" @with @case "cl (combine r1 l2) = R" @with
      @have "rbt_in_traverse_pairs (combine (Node l1 c1 k1 v1 r1) (Node l2 c2 k2 v2 r2)) =
             rbt_in_traverse_pairs l1 @ [(k1, v1)] @ rbt_in_traverse_pairs (combine r1 l2) @ [(k2, v2)] @ rbt_in_traverse_pairs r2"
    @end @end @end
  @endgoal @end
@qed

lemma combine_in_traverse [rewrite]:
  "rbt_in_traverse (combine lt rt) = rbt_in_traverse lt @ rbt_in_traverse rt"
@proof
  @have "rbt_in_traverse_pairs (combine lt rt) = rbt_in_traverse_pairs lt @ rbt_in_traverse_pairs rt"
@qed

fun del :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt" where
  "del x y Leaf = Leaf"
| "del x y (Node l _ k v r) =
    (if x = k then combine l r
     else if x < k then
       if l = Leaf then Node Leaf R k v r
       else if cl l = B then balL (del x y l) k v r
       else Node (del x y l) R k v r
     else
       if r = Leaf then Node l R k v Leaf
       else if cl r = B then balR l k v (del x y r)
       else Node l R k v (del x y r))"
setup {* fold add_rewrite_rule @{thms del.simps} *}

lemma del_bd:
  "bd_inv t \<Longrightarrow> cl_inv t \<Longrightarrow> bd_inv (del x y t) \<and> (
    if cl t = R then black_depth (del x y t) = black_depth t
    else black_depth (del x y t) = black_depth t - 1)"
@proof @induct t @with @subgoal "t = Node l c k v r"
  @case "x = k" @case "x < k" @with
    @case "l = Leaf" @case "cl l = B" @end
  @case "x > k" @with
    @case "r = Leaf" @case "cl r = B" @end
  @endgoal @end
@qed

lemma del_cl:
  "cl_inv t \<Longrightarrow> if cl t = R then cl_inv (del x y t) else cl_inv' (del x y t)"
@proof @induct t @with @subgoal "t = Node l c k v r"
  @case "x = k" @case "x < k" @with
    @case "l = Leaf" @case "cl l = B" @end
  @endgoal @end
@qed

setup {* add_forward_prfstep_cond @{thm del_bd} [with_term "del ?x ?y ?t"] *}
setup {* add_forward_prfstep_cond @{thm del_cl} [with_term "del ?x ?y ?t"] *}
  
lemma del_in_traverse [rewrite]:
  "rbt_sorted t \<Longrightarrow> rbt_in_traverse (del x y t) = remove_elt_list x (rbt_in_traverse t)"
@proof @induct t @qed

lemma del_in_traverse_pairs [rewrite]:
  "rbt_sorted t \<Longrightarrow> rbt_in_traverse_pairs (del x y t) = remove_elt_pairs x (rbt_in_traverse_pairs t)"
@proof @induct t @qed

definition delete :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) pre_rbt" where [rewrite]:
  "delete x y t = paint B (del x y t)"

lemma rbt_delete [forward]: "is_rbt t \<Longrightarrow> is_rbt (delete x y t)" by auto2

lemma delete_in_traverse [rewrite]:
  "rbt_sorted t \<Longrightarrow> rbt_in_traverse (delete x y t) = remove_elt_list x (rbt_in_traverse t)" by auto2

lemma delete_in_traverse_pairs [rewrite]:
  "rbt_sorted t \<Longrightarrow> rbt_in_traverse_pairs (delete x y t) = remove_elt_pairs x (rbt_in_traverse_pairs t)" by auto2

lemma delete_rbt_set: "rbt_sorted t \<Longrightarrow> rbt_set (delete x v t) = rbt_set t - {x}" by auto2

lemma delete_sorted: "rbt_sorted t \<Longrightarrow> rbt_sorted (delete x v t)" by auto2

lemma delete_rbt_map: "rbt_sorted t \<Longrightarrow> rbt_map (delete x v t) = delete_map x (rbt_map t)" by auto2

end
