theory Interval_Tree
imports Lists_Ex
begin
  
definition max3 :: "('a::ord) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where [rewrite]:
  "max3 a b c = max a (max b c)"

section {* Definition of an interval tree *}

(* low is the key, high is the value, max is additional info  *)
datatype interval_tree =
   Tip
 | Node (lsub: interval_tree) (val: "nat \<times> nat") (tmax: nat) (rsub: interval_tree)
where
  "tmax Tip = 0"

setup {* add_resolve_prfstep @{thm interval_tree.distinct(2)} *}
setup {* add_forward_prfstep (equiv_forward_th (@{thm interval_tree.simps(1)})) *}
setup {* fold add_rewrite_rule @{thms interval_tree.sel} *}
setup {* add_forward_prfstep_cond @{thm interval_tree.collapse} [with_cond "?tree \<noteq> Node ?l ?k ?v ?r"] *}
setup {* add_var_induct_rule @{thm interval_tree.induct} *}

section {* Inorder traversal, and set of elements of a tree *}

fun in_traverse_keys :: "interval_tree \<Rightarrow> nat list" where
  "in_traverse_keys Tip = []"
| "in_traverse_keys (Node l it m r) = (in_traverse_keys l) @ [fst it] @ (in_traverse_keys r)"
setup {* fold add_rewrite_rule @{thms in_traverse_keys.simps} *}

fun in_traverse :: "interval_tree \<Rightarrow> (nat \<times> nat) list" where
  "in_traverse Tip = []"
| "in_traverse (Node l it m r) = (in_traverse l) @ [it] @ (in_traverse r)"
setup {* fold add_rewrite_rule @{thms in_traverse.simps} *}

fun tree_set_keys :: "interval_tree \<Rightarrow> nat set" where
  "tree_set_keys Tip = {}"
| "tree_set_keys (Node l it m r) = {fst it} \<union> tree_set_keys l \<union> tree_set_keys r"
setup {* fold add_rewrite_rule @{thms tree_set_keys.simps} *}

fun tree_sorted :: "interval_tree \<Rightarrow> bool" where
  "tree_sorted Tip = True"
| "tree_sorted (Node l it m r) = ((\<forall>x\<in>tree_set_keys l. x < fst it) \<and> (\<forall>x\<in>tree_set_keys r. fst it < x)
                                   \<and> tree_sorted l \<and> tree_sorted r)"
setup {* add_property_const @{term tree_sorted} *}
setup {* fold add_rewrite_rule @{thms tree_sorted.simps} *}

lemma tree_sorted_lr [forward]:
  "tree_sorted (Node l it m r) \<Longrightarrow> tree_sorted l \<and> tree_sorted r" by auto2

lemma inorder_preserve_set [rewrite_back]:
  "set (in_traverse_keys t) = tree_set_keys t"
@proof @induct t @qed

lemma inorder_keys_sorted [rewrite_back]:
  "strict_sorted (in_traverse_keys t) \<longleftrightarrow> tree_sorted t"
@proof @induct t @qed

lemma in_traverse_fst [rewrite]:
  "map fst (in_traverse t) = in_traverse_keys t"
@proof @induct t @qed

(* Use definition in terms of in_traverse from now on. *)
setup {* fold del_prfstep_thm (@{thms tree_set_keys.simps} @ @{thms tree_sorted.simps}) *}

section {* Invariant on the maximum *}

fun tree_set :: "interval_tree \<Rightarrow> (nat \<times> nat) set" where
  "tree_set Tip = {}"
| "tree_set (Node l it m r) = {it} \<union> tree_set l \<union> tree_set r"
setup {* fold add_rewrite_rule @{thms tree_set.simps} *}

lemma tree_set_fst [backward]:
  "p \<in> tree_set t \<Longrightarrow> fst p \<in> tree_set_keys t"
@proof @induct t @qed

fun tree_max_inv :: "interval_tree \<Rightarrow> bool" where
  "tree_max_inv Tip = True"
| "tree_max_inv (Node l it m r) \<longleftrightarrow> (tree_max_inv l \<and> tree_max_inv r \<and> m = max3 (snd it) (tmax l) (tmax r))"
setup {* fold add_rewrite_rule @{thms tree_max_inv.simps} *}
setup {* add_property_const @{term tree_max_inv} *}

lemma tree_max_is_max [resolve]:
  "tree_max_inv t \<Longrightarrow> it \<in> tree_set t \<Longrightarrow> snd it \<le> tmax t"
@proof @induct t @qed

lemma tmax_exists [backward]:
  "tree_max_inv t \<Longrightarrow> t \<noteq> Tip \<Longrightarrow> \<exists>p\<in>tree_set t. snd p = tmax t"
@proof @induct t @with
  @subgoal "t = Node l it m r"
    @case "l = Tip" @with @case "r = Tip" @end
    @case "r = Tip"
  @endgoal @end
@qed

section {* Rotation on trees *}
  
fun rotateL :: "interval_tree \<Rightarrow> interval_tree" where
  "rotateL Tip = Tip"
| "rotateL (Node l it m Tip) = Node l it m Tip"
| "rotateL (Node l it m (Node lr itr mr rr)) =
  (let ml = max3 (snd it) (tmax l) (tmax lr) in
   Node (Node l it ml lr) itr (max3 (snd itr) ml (tmax rr)) rr)"
setup {* fold add_rewrite_rule @{thms rotateL.simps} *}

lemma rotateL_in_trav_keys [rewrite]: "in_traverse_keys (rotateL t) = in_traverse_keys t"
@proof @case "t = Tip" @then @case "rsub t = Tip" @qed

lemma rotateL_in_trav [rewrite]: "in_traverse (rotateL t) = in_traverse t"
@proof @case "t = Tip" @then @case "rsub t = Tip" @qed

lemma rotateL_sorted [forward]: "tree_sorted t \<Longrightarrow> tree_sorted (rotateL t)" by auto2

lemma rotateL_max_inv [forward]: "tree_max_inv t \<Longrightarrow> tree_max_inv (rotateL t)"
@proof @case "t = Tip" @then @case "rsub t = Tip" @qed

fun rotateR :: "interval_tree \<Rightarrow> interval_tree" where
  "rotateR Tip = Tip"
| "rotateR (Node Tip it m r) = Node Tip it m r"
| "rotateR (Node (Node ll itl ml rl) it m r) =
   (let mr = max3 (snd it) (tmax rl) (tmax r) in
    Node ll itl (max3 (snd itl) (tmax ll) mr) (Node rl it mr r))"
setup {* fold add_rewrite_rule @{thms rotateR.simps} *}

lemma rotateR_in_trav_keys [rewrite]: "in_traverse_keys (rotateR t) = in_traverse_keys t"
@proof @case "t = Tip" @then @case "lsub t = Tip" @qed

lemma rotateR_in_trav [rewrite]: "in_traverse (rotateR t) = in_traverse t"
@proof @case "t = Tip" @then @case "lsub t = Tip" @qed

lemma rotateR_sorted [forward]: "tree_sorted t \<Longrightarrow> tree_sorted (rotateR t)" by auto2

lemma rotateR_max_inv [forward]: "tree_max_inv t \<Longrightarrow> tree_max_inv (rotateR t)"
@proof @case "t = Tip" @then @case "lsub t = Tip" @qed

section {* Insertion on trees *}

fun tree_insert :: "nat \<times> nat \<Rightarrow> interval_tree \<Rightarrow> interval_tree" where
  "tree_insert (a, b) Tip = Node Tip (a, b) b Tip"
| "tree_insert (a, b) (Node l (c, d) m r) =
    (if a = c then Node l (c, d) m r
     else if a < c then
       let l' = tree_insert (a, b) l in
           Node l' (c, d) (max3 d (tmax l') (tmax r)) r
     else
       let r' = tree_insert (a, b) r in
           Node l (c, d) (max3 d (tmax l) (tmax r')) r')"
setup {* fold add_rewrite_rule @{thms tree_insert.simps} *}

lemma tree_insert_in_traverse_keys [rewrite]:
  "tree_sorted t \<Longrightarrow> in_traverse_keys (tree_insert (a, b) t) = ordered_insert a (in_traverse_keys t)"
@proof @induct t @qed

lemma tree_insert_on_set [rewrite]:
  "tree_sorted t \<Longrightarrow> tree_set_keys (tree_insert (a, b) t) = {a} \<union> tree_set_keys t" by auto2

lemma tree_insert_sorted [backward]:
  "tree_sorted t \<Longrightarrow> tree_sorted (tree_insert (a, b) t)" by auto2

lemma tree_insert_max_inv:
  "tree_max_inv t \<Longrightarrow> tree_max_inv (tree_insert (a, b) t)"
@proof @induct t @qed

section {* Search on interval trees *}

fun is_overlap :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "is_overlap (a, b) (c, d) \<longleftrightarrow> (b \<ge> c \<or> d \<ge> a)"
setup {* add_rewrite_rule @{thm is_overlap.simps} *}

fun tree_search :: "interval_tree \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "tree_search Tip (a, b) = False"
| "tree_search (Node l (c, d) m r) (a, b) =
   (if is_overlap (a, b) (c, d) then True
    else if l \<noteq> Tip \<and> tmax l \<ge> a then tree_search l (a, b)
    else tree_search r (a, b))"
setup {* fold add_rewrite_rule @{thms tree_search.simps} *}

fun tree_interval_inv :: "interval_tree \<Rightarrow> bool" where
  "tree_interval_inv Tip = True"
| "tree_interval_inv (Node l (a, b) m r) = (a \<le> b \<and> tree_interval_inv l \<and> tree_interval_inv r)"
setup {* fold add_rewrite_rule @{thms tree_interval_inv.simps} *}

lemma tree_search_correct [rewrite]:
  "tree_sorted t \<Longrightarrow> tree_interval_inv t \<Longrightarrow> tree_max_inv t \<Longrightarrow> a \<le> b \<Longrightarrow>
   tree_search t (a, b) \<longleftrightarrow> (\<exists>p\<in>tree_set t. is_overlap (a, b) p)"
@proof @induct t @qed

end
