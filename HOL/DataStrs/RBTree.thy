(* Verification of functional red-black trees. *)

theory RBTree
imports Lists_Ex
begin

section {* Definition of RBT *}

datatype color = R | B
datatype ('a, 'b) rbt =
    Leaf
  | Node (lsub: "('a, 'b) rbt") (cl: color) (key: 'a) (val: 'b) (rsub: "('a, 'b) rbt")
where
  "cl Leaf = B"

setup {* add_resolve_prfstep @{thm color.distinct(1)} *}
setup {* add_resolve_prfstep @{thm rbt.distinct(1)} *}
setup {* fold add_rewrite_rule @{thms rbt.sel} *}
setup {* add_forward_prfstep @{thm rbt.collapse} *}
setup {* add_var_induct_rule @{thm rbt.induct} *}

lemma not_R [forward]: "c \<noteq> R \<Longrightarrow> c = B" using color.exhaust by blast
lemma not_B [forward]: "c \<noteq> B \<Longrightarrow> c = R" using color.exhaust by blast
lemma red_not_leaf [forward]: "cl t = R \<Longrightarrow> t \<noteq> Leaf" by auto

section {* RBT invariants *}

fun black_depth :: "('a, 'b) rbt \<Rightarrow> nat" where
  "black_depth Leaf = 0"
| "black_depth (Node l R k v r) = black_depth l"
| "black_depth (Node l B k v r) = black_depth l + 1"
setup {* fold add_rewrite_rule @{thms black_depth.simps} *}

fun cl_inv :: "('a, 'b) rbt \<Rightarrow> bool" where
  "cl_inv Leaf = True"
| "cl_inv (Node l R k v r) = (cl_inv l \<and> cl_inv r \<and> cl l = B \<and> cl r = B)"
| "cl_inv (Node l B k v r) = (cl_inv l \<and> cl_inv r)"
setup {* fold add_rewrite_rule @{thms cl_inv.simps} *}
setup {* add_property_const @{term cl_inv} *}

fun bd_inv :: "('a, 'b) rbt \<Rightarrow> bool" where
  "bd_inv Leaf = True"
| "bd_inv (Node l c k v r) = (bd_inv l \<and> bd_inv r \<and> black_depth l = black_depth r)"
setup {* fold add_rewrite_rule @{thms bd_inv.simps} *}
setup {* add_property_const @{term bd_inv} *}

definition is_rbt :: "('a, 'b) rbt \<Rightarrow> bool" where [rewrite]:
  "is_rbt t = (cl_inv t \<and> bd_inv t)"
setup {* add_property_const @{term is_rbt} *}

lemma cl_invI: "cl_inv l \<Longrightarrow> cl_inv r \<Longrightarrow> cl_inv (Node l B k v r)" by auto2
setup {* add_forward_prfstep_cond @{thm cl_invI} [with_term "Node ?l B ?k ?v ?r"] *}

lemma bd_invI: "bd_inv l \<Longrightarrow> bd_inv r \<Longrightarrow> black_depth l = black_depth r \<Longrightarrow> bd_inv (Node l c k v r)" by auto2
setup {* add_forward_prfstep_cond @{thm bd_invI} [with_term "Node ?l ?c ?k ?v ?r"] *}

lemma is_rbt_rec [forward]: "is_rbt (Node l c k v r) \<Longrightarrow> is_rbt l \<and> is_rbt r"
@proof @case "c = R" @qed

section {* Balancedness of RBT *}

(* Remove after having general normalization procedure for nats. *)
lemma two_distrib [rewrite]: "(2::nat) * (a + 1) = 2 * a + 2" by simp

fun min_depth :: "('a, 'b) rbt \<Rightarrow> nat" where
  "min_depth Leaf = 0"
| "min_depth (Node l c k v r) = min (min_depth l) (min_depth r) + 1"
setup {* fold add_rewrite_rule @{thms min_depth.simps} *}

fun max_depth :: "('a, 'b) rbt \<Rightarrow> nat" where
  "max_depth Leaf = 0"
| "max_depth (Node l c k v r) = max (max_depth l) (max_depth r) + 1"
setup {* fold add_rewrite_rule @{thms max_depth.simps} *}

theorem rbt_balanced: "is_rbt t \<Longrightarrow> max_depth t \<le> 2 * min_depth t + 1"
@proof
  @induct t for "is_rbt t \<longrightarrow> black_depth t \<le> min_depth t" @with
    @subgoal "t = Node l c k v r" @case "c = R" @endgoal
  @end
  @induct t for "is_rbt t \<longrightarrow> (if cl t = R then max_depth t \<le> 2 * black_depth t + 1
                               else max_depth t \<le> 2 * black_depth t)" @with
    @subgoal "t = Node l c k v r" @case "c = R" @endgoal
  @end
  @have "max_depth t \<le> 2 * black_depth t + 1"
@qed

section {* Definition and basic properties of cl_inv' *}

fun cl_inv' :: "('a, 'b) rbt \<Rightarrow> bool" where
  "cl_inv' Leaf = True"
| "cl_inv' (Node l c k v r) = (cl_inv l \<and> cl_inv r)"
setup {* fold add_rewrite_rule @{thms cl_inv'.simps} *}
setup {* add_property_const @{term cl_inv'} *}

lemma cl_inv'B [forward, backward1]:
  "cl_inv' t \<Longrightarrow> cl t = B \<Longrightarrow> cl_inv t"
@proof @case "t = Leaf" @qed

lemma cl_inv'R [forward]:
  "cl_inv' (Node l R k v r) \<Longrightarrow> cl l = B \<Longrightarrow> cl r = B \<Longrightarrow> cl_inv (Node l R k v r)" by auto2

lemma cl_inv_to_cl_inv' [forward]: "cl_inv t \<Longrightarrow> cl_inv' t"
@proof @case "t = Leaf" @then @case "cl t = R" @qed

lemma cl_inv'I: "cl_inv l \<Longrightarrow> cl_inv r \<Longrightarrow> cl_inv' (Node l c k v r)" by auto
setup {* add_forward_prfstep_cond @{thm cl_inv'I} [with_term "Node ?l ?c ?k ?v ?r"] *}

subsection {* Set of keys, sortedness *}

fun rbt_in_traverse :: "('a, 'b) rbt \<Rightarrow> 'a list" where
  "rbt_in_traverse Leaf = []"
| "rbt_in_traverse (Node l c k v r) = rbt_in_traverse l @ k # rbt_in_traverse r"
setup {* fold add_rewrite_rule @{thms rbt_in_traverse.simps} *}

fun rbt_set :: "('a, 'b) rbt \<Rightarrow> 'a set" where
  "rbt_set Leaf = {}"
| "rbt_set (Node l c k v r) = {k} \<union> rbt_set l \<union> rbt_set r"
setup {* fold add_rewrite_rule @{thms rbt_set.simps} *}

fun rbt_in_traverse_pairs :: "('a, 'b) rbt \<Rightarrow> ('a \<times> 'b) list" where
  "rbt_in_traverse_pairs Leaf = []"
| "rbt_in_traverse_pairs (Node l c k v r) = rbt_in_traverse_pairs l @ (k, v) # rbt_in_traverse_pairs r"
setup {* fold add_rewrite_rule @{thms rbt_in_traverse_pairs.simps} *}

lemma rbt_in_traverse_fst [rewrite]: "map fst (rbt_in_traverse_pairs t) = rbt_in_traverse t"
@proof @induct t @qed

definition rbt_map :: "('a, 'b) rbt \<Rightarrow> ('a, 'b) map" where
  "rbt_map t = map_of_alist (rbt_in_traverse_pairs t)"
setup {* add_rewrite_rule @{thm rbt_map_def} *}

fun rbt_sorted :: "('a::linorder, 'b) rbt \<Rightarrow> bool" where
  "rbt_sorted Leaf = True"
| "rbt_sorted (Node l c k v r) = ((\<forall>x\<in>rbt_set l. x < k) \<and> (\<forall>x\<in>rbt_set r. k < x) \<and> rbt_sorted l \<and> rbt_sorted r)"
setup {* fold add_rewrite_rule @{thms rbt_sorted.simps} *}
setup {* add_property_const @{term rbt_sorted} *}

lemma rbt_sorted_lr [forward]:
  "rbt_sorted (Node l c k v r) \<Longrightarrow> rbt_sorted l \<and> rbt_sorted r" by auto2

lemma rbt_inorder_preserve_set [rewrite]:
  "rbt_set t = set (rbt_in_traverse t)"
@proof @induct t @qed

lemma rbt_inorder_sorted [rewrite]:
  "rbt_sorted t \<longleftrightarrow> strict_sorted (map fst (rbt_in_traverse_pairs t))"
@proof @induct t @qed

setup {* fold del_prfstep_thm (@{thms rbt_set.simps} @ @{thms rbt_sorted.simps}) *}

section {* Balance function *}

definition balanceR :: "('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where [rewrite,unfold]:
  "balanceR l k v r =
   (if cl r = R then
      let lr = lsub r; rr = rsub r in
      if cl lr = R then Node (Node l B k v (lsub lr)) R (key lr) (val lr) (Node (rsub lr) B (key r) (val r) rr)
      else if cl rr = R then Node (Node l B k v lr) R (key r) (val r) (Node (lsub rr) B (key rr) (val rr) (rsub rr))
      else Node l B k v r
    else Node l B k v r)"
  
definition balance :: "('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where [rewrite,unfold]:
  "balance l k v r =
   (if cl l = R then
      let ll = lsub l; rl = rsub l in
      if cl ll = R then Node (Node (lsub ll) B (key ll) (val ll) (rsub ll)) R (key l) (val l) (Node (rsub l) B k v r)
      else if cl rl = R then Node (Node (lsub l) B (key l) (val l) (lsub rl)) R (key rl) (val rl) (Node (rsub rl) B k v r)
      else balanceR l k v r
    else balanceR l k v r)"
setup {* register_wellform_data ("balance l k v r", ["black_depth l = black_depth r"]) *}
setup {* add_prfstep_check_req ("balance l k v r", "black_depth l = black_depth r") *}

lemma balance_non_Leaf [resolve]: "balance l k v r \<noteq> Leaf" by auto2

lemma balance_bdinv:
  "bd_inv l \<Longrightarrow> bd_inv r \<Longrightarrow> black_depth l = black_depth r \<Longrightarrow> bd_inv (balance l k v r)"
@proof @have "bd_inv (balanceR l k v r)" @qed
setup {* add_forward_prfstep_cond @{thm balance_bdinv} [with_term "balance ?l ?k ?v ?r"] *}

lemma balance_bd [rewrite]:
  "bd_inv l \<Longrightarrow> bd_inv r \<Longrightarrow> black_depth l = black_depth r \<Longrightarrow>
   black_depth (balance l k v r) = black_depth l + 1"
@proof @have "black_depth (balanceR l k v r) = black_depth l + 1" @qed

lemma balance_cl1 [forward]:
  "cl_inv' l \<Longrightarrow> cl_inv r \<Longrightarrow> cl_inv (balance l k v r)" by auto2

lemma balance_cl2 [forward]:
  "cl_inv l \<Longrightarrow> cl_inv' r \<Longrightarrow> cl_inv (balance l k v r)" by auto2

lemma balanceR_inorder_pairs [rewrite]:
  "rbt_in_traverse_pairs (balanceR l k v r) = rbt_in_traverse_pairs l @ (k, v) # rbt_in_traverse_pairs r" by auto2

lemma balance_inorder_pairs [rewrite]:
  "rbt_in_traverse_pairs (balance l k v r) = rbt_in_traverse_pairs l @ (k, v) # rbt_in_traverse_pairs r" by auto2

setup {* fold del_prfstep_thm [@{thm balanceR_def}, @{thm balance_def}] *}

section {* ins function *}

fun ins :: "'a::order \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
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

lemma ins_non_Leaf [resolve]: "ins x v t \<noteq> Leaf"
@proof @case "t = Leaf" @qed

lemma cl_inv_ins [forward]:
  "cl_inv t \<Longrightarrow> cl_inv' (ins x v t)"
@proof
  @induct t for "cl_inv t \<longrightarrow> (if cl t = B then cl_inv (ins x v t) else cl_inv' (ins x v t))"
@qed

lemma bd_inv_ins:
  "bd_inv t \<Longrightarrow> bd_inv (ins x v t) \<and> black_depth t = black_depth (ins x v t)"
@proof @induct t @qed
setup {* add_forward_prfstep_cond (conj_left_th @{thm bd_inv_ins}) [with_term "ins ?x ?v ?t"] *}

lemma ins_inorder_pairs [rewrite]:
  "rbt_sorted t \<Longrightarrow> rbt_in_traverse_pairs (ins x v t) = ordered_insert_pairs x v (rbt_in_traverse_pairs t)"
@proof @induct t @qed

section {* Paint function *}

fun paint :: "color \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "paint c Leaf = Leaf"
| "paint c (Node l c' x v r) = Node l c x v r"
setup {* fold add_rewrite_rule @{thms paint.simps} *}
setup {* register_wellform_data ("paint c t", ["t \<noteq> Leaf"]) *}
setup {* add_prfstep_check_req ("paint c t", "t \<noteq> Leaf") *}

lemma paint_cl_inv' [forward]: "cl_inv' t \<Longrightarrow> cl_inv' (paint c t)" by auto2

lemma paint_bd_inv [forward]: "bd_inv t \<Longrightarrow> bd_inv (paint c t)" by auto2

lemma paint_bd [rewrite]:
  "bd_inv t \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> cl t = B \<Longrightarrow> black_depth (paint R t) = black_depth t - 1" by auto2

lemma paint_in_traverse_pairs [rewrite]:
  "rbt_in_traverse_pairs (paint c t) = rbt_in_traverse_pairs t" by auto2

section {* Insert function *}

definition rbt_insert :: "'a::order \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where [rewrite]:
  "rbt_insert x v t = paint B (ins x v t)"

theorem insert_is_rbt [forward]:
  "is_rbt t \<Longrightarrow> is_rbt (rbt_insert x v t)" by auto2

theorem insert_sorted [forward]:
  "rbt_sorted t \<Longrightarrow> rbt_sorted (rbt_insert x v t)" by auto2

theorem insert_rbt_map [rewrite]:
  "rbt_sorted t \<Longrightarrow> rbt_map (rbt_insert x v t) = (rbt_map t) {x \<rightarrow> v}" by auto2

section {* Search on sorted trees and its correctness *}

fun rbt_search :: "('a::ord, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "rbt_search Leaf x = None"
| "rbt_search (Node l c y w r) x =
  (if x = y then Some w
   else if x < y then rbt_search l x
   else rbt_search r x)"
setup {* fold add_rewrite_rule @{thms rbt_search.simps} *}

theorem rbt_search_correct [rewrite]:
  "rbt_sorted t \<Longrightarrow> rbt_search t x = (rbt_map t)\<langle>x\<rangle>"
@proof @induct t @qed
    
section {* balL and balR *}

definition balL :: "('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where [rewrite,unfold]:
  "balL l k v r = (let lr = lsub r in
   if cl l = R then Node (Node (lsub l) B (key l) (val l) (rsub l)) R k v r
   else if r = Leaf then Node l R k v r
   else if cl r = B then balance l k v (Node (lsub r) R (key r) (val r) (rsub r))
   else if lr = Leaf then Node l R k v r
   else if cl lr = B then
     Node (Node l B k v (lsub lr)) R (key lr) (val lr) (balance (rsub lr) (key r) (val r) (paint R (rsub r)))
   else Node l R k v r)"
setup {* register_wellform_data ("balL l k v r", ["black_depth l + 1 = black_depth r"]) *}
setup {* add_prfstep_check_req ("balL l k v r", "black_depth l + 1 = black_depth r") *}
  
definition balR :: "('a, 'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where [rewrite,unfold]:
  "balR l k v r = (let rl = rsub l in
   if cl r = R then Node l R k v (Node (lsub r) B (key r) (val r) (rsub r))
   else if l = Leaf then Node l R k v r
   else if cl l = B then balance (Node (lsub l) R (key l) (val l) (rsub l)) k v r
   else if rl = Leaf then Node l R k v r
   else if cl rl = B then
     Node (balance (paint R (lsub l)) (key l) (val l) (lsub rl)) R (key rl) (val rl) (Node (rsub rl) B k v r)
   else Node l R k v r)"
setup {* register_wellform_data ("balR l k v r", ["black_depth l = black_depth r + 1"]) *}
setup {* add_prfstep_check_req ("balR l k v r", "black_depth l = black_depth r + 1") *}

lemma balL_bd:
  "bd_inv l \<Longrightarrow> bd_inv r \<Longrightarrow> cl r = B \<Longrightarrow> black_depth l + 1 = black_depth r \<Longrightarrow>
   bd_inv (balL l k v r) \<and> black_depth (balL l k v r) = black_depth l + 1" by auto2
setup {* add_forward_prfstep_cond @{thm balL_bd} [with_term "balL ?l ?k ?v ?r"] *}

lemma balL_bd':
  "bd_inv l \<Longrightarrow> bd_inv r \<Longrightarrow> cl_inv r \<Longrightarrow> black_depth l + 1 = black_depth r \<Longrightarrow>
   bd_inv (balL l k v r) \<and> black_depth (balL l k v r) = black_depth l + 1" by auto2
setup {* add_forward_prfstep_cond @{thm balL_bd'} [with_term "balL ?l ?k ?v ?r"] *}

lemma balL_cl:
  "cl_inv' l \<Longrightarrow> cl_inv r \<Longrightarrow> cl r = B \<Longrightarrow> cl_inv (balL l k v r)" by auto2
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

lemma balL_in_traverse_pairs [rewrite]:
  "rbt_in_traverse_pairs (balL l k v r) = rbt_in_traverse_pairs l @ (k, v) # rbt_in_traverse_pairs r" by auto2

lemma balR_in_traverse_pairs [rewrite]:
  "rbt_in_traverse_pairs (balR l k v r) = rbt_in_traverse_pairs l @ (k, v) # rbt_in_traverse_pairs r" by auto2

setup {* fold del_prfstep_thm [@{thm balL_def}, @{thm balR_def}] *}

section {* Combine *}

fun combine :: "('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
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
setup {* fold add_rewrite_rule @{thms combine.simps(1,2)} *}
setup {* add_unfolding_rule @{thm combine.simps(3)} *}
setup {* add_fun_induct_rule (@{term combine}, @{thm combine.induct}) *}

lemma combine_bd:
  "bd_inv lt \<Longrightarrow> bd_inv rt \<Longrightarrow> black_depth lt = black_depth rt \<Longrightarrow>
   bd_inv (combine lt rt) \<and> black_depth (combine lt rt) = black_depth lt"
@proof @fun_induct "combine lt rt" @with
  @subgoal "(lt = Node l1 c1 k1 v1 r1, rt = Node l2 c2 k2 v2 r2)"
    @unfold "combine (Node l1 c1 k1 v1 r1) (Node l2 c2 k2 v2 r2)"
    @case "c1 = B" @with @case "c2 = B" @with @case "cl (combine r1 l2) = B" @with
      @have "cl (Node (combine r1 l2) B k2 v2 r2) = B" @end @end @end
  @endgoal @end
@qed
setup {* add_forward_prfstep_cond @{thm combine_bd} [with_term "combine ?lt ?rt"] *}

lemma combine_cl:
  "cl_inv lt \<Longrightarrow> cl_inv rt \<Longrightarrow>
   (cl lt = B \<longrightarrow> cl rt = B \<longrightarrow> cl_inv (combine lt rt)) \<and> cl_inv' (combine lt rt)"
@proof @fun_induct "combine lt rt" @with
  @subgoal "(lt = Node l1 c1 k1 v1 r1, rt = Node l2 c2 k2 v2 r2)"
    @unfold "combine (Node l1 c1 k1 v1 r1) (Node l2 c2 k2 v2 r2)"
    @case "c1 = B" @with @case "c2 = B" @with @case "cl (combine r1 l2) = B" @with
      @have "cl (Node (combine r1 l2) B k2 v2 r2) = B" @end @end @end
  @endgoal @end
@qed
setup {* add_forward_prfstep_cond @{thm combine_cl} [with_term "combine ?lt ?rt"] *}

lemma combine_in_traverse_pairs [rewrite]:
  "rbt_in_traverse_pairs (combine lt rt) = rbt_in_traverse_pairs lt @ rbt_in_traverse_pairs rt"
@proof @fun_induct "combine lt rt" @with
  @subgoal "(lt = Node l1 c1 k1 v1 r1, rt = Node l2 c2 k2 v2 r2)"
    @unfold "combine (Node l1 c1 k1 v1 r1) (Node l2 c2 k2 v2 r2)"
    @case "c1 = R" @with @case "c2 = R" @with @case "cl (combine r1 l2) = R" @with
      @have "rbt_in_traverse_pairs (combine (Node l1 c1 k1 v1 r1) (Node l2 c2 k2 v2 r2)) =
             rbt_in_traverse_pairs l1 @ (k1, v1) # rbt_in_traverse_pairs (combine r1 l2) @ (k2, v2) # rbt_in_traverse_pairs r2"
    @end @end @end
    @case "c1 = B" @with @case "c2 = B" @with @case "cl (combine r1 l2) = R" @with
      @have "rbt_in_traverse_pairs (combine (Node l1 c1 k1 v1 r1) (Node l2 c2 k2 v2 r2)) =
             rbt_in_traverse_pairs l1 @ (k1, v1) # rbt_in_traverse_pairs (combine r1 l2) @ (k2, v2) # rbt_in_traverse_pairs r2"
    @end @end @end
  @endgoal @end
@qed

section {* Deletion *}

fun del :: "'a::linorder \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "del x Leaf = Leaf"
| "del x (Node l _ k v r) =
    (if x = k then combine l r
     else if x < k then
       if l = Leaf then Node Leaf R k v r
       else if cl l = B then balL (del x l) k v r
       else Node (del x l) R k v r
     else
       if r = Leaf then Node l R k v Leaf
       else if cl r = B then balR l k v (del x r)
       else Node l R k v (del x r))"
setup {* add_rewrite_rule @{thm del.simps(1)} *}
setup {* add_unfolding_rule @{thm del.simps(2)} *}

lemma del_bd:
  "bd_inv t \<Longrightarrow> cl_inv t \<Longrightarrow> bd_inv (del x t) \<and> (
    if cl t = R then black_depth (del x t) = black_depth t
    else black_depth (del x t) = black_depth t - 1)"
@proof @induct t @with
  @subgoal "t = Node l c k v r"
    @unfold "del x (Node l c k v r)"
    @case "x = k" @case "x < k" @with
      @case "l = Leaf" @case "cl l = B" @end
    @case "x > k" @with
      @case "r = Leaf" @case "cl r = B" @end
  @endgoal @end
@qed
setup {* add_forward_prfstep_cond @{thm del_bd} [with_term "del ?x ?t"] *}

lemma del_cl:
  "cl_inv t \<Longrightarrow> if cl t = R then cl_inv (del x t) else cl_inv' (del x t)"
@proof @induct t @with
  @subgoal "t = Node l c k v r"
    @unfold "del x (Node l c k v r)"
    @case "x = k" @case "x < k"
  @endgoal @end
@qed
setup {* add_forward_prfstep_cond @{thm del_cl} [with_term "del ?x ?t"] *}

lemma del_in_traverse_pairs [rewrite]:
  "rbt_sorted t \<Longrightarrow> rbt_in_traverse_pairs (del x t) = remove_elt_pairs x (rbt_in_traverse_pairs t)"
@proof @induct t @with
  @subgoal "t = Node l c k v r"
    @unfold "del x (Node l c k v r)"
  @endgoal @end
@qed

definition delete :: "'a::linorder \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where [rewrite]:
  "delete x t = paint B (del x t)"

theorem delete_is_rbt [forward]:
  "is_rbt t \<Longrightarrow> is_rbt (delete x t)" by auto2

theorem delete_sorted [forward]:
  "rbt_sorted t \<Longrightarrow> rbt_sorted (delete x t)" by auto2

theorem delete_rbt_map [rewrite]:
  "rbt_sorted t \<Longrightarrow> rbt_map (delete x t) = delete_map x (rbt_map t)" by auto2

setup {* del_prfstep "RBTree.balance_case" *}
setup {* del_prfstep "RBTree.balL_case" *}
setup {* del_prfstep "RBTree.balR_case" *}
setup {* del_prfstep "RBTree.paint_case" *}

end
