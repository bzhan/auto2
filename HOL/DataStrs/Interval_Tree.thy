theory Interval_Tree
imports Lists_Ex
begin
  
definition max3 :: "('a::ord) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where [rewrite]:
  "max3 a b c = max a (max b c)"

section {* Definition of interval *}

datatype 'a interval = Interval (low: 'a) (high: 'a)
setup {* add_rewrite_rule_back @{thm interval.collapse} *}
setup {* add_rewrite_rule @{thm interval.case} *}
setup {* fold add_rewrite_rule @{thms interval.sel} *}

instantiation interval :: (linorder) linorder begin

definition less: "(a < b) = (low a < low b | (low a = low b \<and> high a < high b))"
definition less_eq: "(a \<le> b) = (low a < low b | (low a = low b \<and> high a \<le> high b))"

instance proof
  fix x y z :: "'a interval"
  show a: "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    using less local.less_eq by force
  show b: "x \<le> x"
    by (simp add: local.less_eq)
  show c: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (smt Interval_Tree.less_eq dual_order.trans less_trans)
  show d: "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    using Interval_Tree.less_eq a interval.expand less by fastforce
  show e: "x \<le> y \<or> y \<le> x"
    by (meson Interval_Tree.less_eq leI not_less_iff_gr_or_eq)
qed end

section {* Definition of an interval tree *}

datatype interval_tree =
   Tip
 | Node (lsub: interval_tree) (val: "nat interval") (tmax: nat) (rsub: interval_tree)
where
  "tmax Tip = 0"

setup {* add_resolve_prfstep @{thm interval_tree.distinct(2)} *}
setup {* add_forward_prfstep (equiv_forward_th (@{thm interval_tree.simps(1)})) *}
setup {* fold add_rewrite_rule @{thms interval_tree.sel} *}
setup {* add_forward_prfstep_cond @{thm interval_tree.collapse} [with_cond "?tree \<noteq> Node ?l ?k ?v ?r"] *}
setup {* add_var_induct_rule @{thm interval_tree.induct} *}

section {* Inorder traversal, and set of elements of a tree *}

fun in_traverse :: "interval_tree \<Rightarrow> nat interval list" where
  "in_traverse Tip = []"
| "in_traverse (Node l it m r) = (in_traverse l) @ [it] @ (in_traverse r)"
setup {* fold add_rewrite_rule @{thms in_traverse.simps} *}

fun tree_set :: "interval_tree \<Rightarrow> nat interval set" where
  "tree_set Tip = {}"
| "tree_set (Node l it m r) = {it} \<union> tree_set l \<union> tree_set r"
setup {* fold add_rewrite_rule @{thms tree_set.simps} *}

fun tree_sorted :: "interval_tree \<Rightarrow> bool" where
  "tree_sorted Tip = True"
| "tree_sorted (Node l it m r) = ((\<forall>x\<in>tree_set l. x < it) \<and> (\<forall>x\<in>tree_set r. it < x)
                                   \<and> tree_sorted l \<and> tree_sorted r)"
setup {* add_property_const @{term tree_sorted} *}
setup {* fold add_rewrite_rule @{thms tree_sorted.simps} *}

lemma tree_sorted_lr [forward]:
  "tree_sorted (Node l it m r) \<Longrightarrow> tree_sorted l \<and> tree_sorted r" by auto2

lemma inorder_preserve_set [rewrite_back]:
  "set (in_traverse t) = tree_set t"
@proof @induct t @qed

lemma inorder_sorted [rewrite_back]:
  "strict_sorted (in_traverse t) \<longleftrightarrow> tree_sorted t"
@proof @induct t @qed

(* Use definition in terms of in_traverse from now on. *)
setup {* fold del_prfstep_thm (@{thms tree_set.simps} @ @{thms tree_sorted.simps}) *}

section {* Invariant on the maximum *}

fun tree_max_inv :: "interval_tree \<Rightarrow> bool" where
  "tree_max_inv Tip = True"
| "tree_max_inv (Node l it m r) \<longleftrightarrow> (tree_max_inv l \<and> tree_max_inv r \<and> m = max3 (high it) (tmax l) (tmax r))"
setup {* fold add_rewrite_rule @{thms tree_max_inv.simps} *}
setup {* add_property_const @{term tree_max_inv} *}

lemma tree_max_is_max [resolve]:
  "tree_max_inv t \<Longrightarrow> it \<in> tree_set t \<Longrightarrow> high it \<le> tmax t"
@proof @induct t @qed

lemma tmax_exists [backward]:
  "tree_max_inv t \<Longrightarrow> t \<noteq> Tip \<Longrightarrow> \<exists>p\<in>tree_set t. high p = tmax t"
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
  (let ml = max3 (high it) (tmax l) (tmax lr) in
   Node (Node l it ml lr) itr (max3 (high itr) ml (tmax rr)) rr)"
setup {* fold add_rewrite_rule @{thms rotateL.simps} *}

lemma rotateL_in_trav [rewrite]: "in_traverse (rotateL t) = in_traverse t"
@proof @case "t = Tip" @then @case "rsub t = Tip" @qed

lemma rotateL_sorted [forward]: "tree_sorted t \<Longrightarrow> tree_sorted (rotateL t)" by auto2

lemma rotateL_max_inv [forward]: "tree_max_inv t \<Longrightarrow> tree_max_inv (rotateL t)"
@proof @case "t = Tip" @then @case "rsub t = Tip" @qed

fun rotateR :: "interval_tree \<Rightarrow> interval_tree" where
  "rotateR Tip = Tip"
| "rotateR (Node Tip it m r) = Node Tip it m r"
| "rotateR (Node (Node ll itl ml rl) it m r) =
   (let mr = max3 (high it) (tmax rl) (tmax r) in
    Node ll itl (max3 (high itl) (tmax ll) mr) (Node rl it mr r))"
setup {* fold add_rewrite_rule @{thms rotateR.simps} *}

lemma rotateR_in_trav [rewrite]: "in_traverse (rotateR t) = in_traverse t"
@proof @case "t = Tip" @then @case "lsub t = Tip" @qed

lemma rotateR_sorted [forward]: "tree_sorted t \<Longrightarrow> tree_sorted (rotateR t)" by auto2

lemma rotateR_max_inv [forward]: "tree_max_inv t \<Longrightarrow> tree_max_inv (rotateR t)"
@proof @case "t = Tip" @then @case "lsub t = Tip" @qed

section {* Insertion on trees *}

fun tree_insert :: "nat interval \<Rightarrow> interval_tree \<Rightarrow> interval_tree" where
  "tree_insert x Tip = Node Tip x (high x) Tip"
| "tree_insert x (Node l y m r) =
    (if x = y then Node l y m r
     else if x < y then
       let l' = tree_insert x l in
           Node l' y (max3 (high y) (tmax l') (tmax r)) r
     else
       let r' = tree_insert x r in
           Node l y (max3 (high y) (tmax l) (tmax r')) r')"
setup {* fold add_rewrite_rule @{thms tree_insert.simps} *}

lemma tree_insert_in_traverse [rewrite]:
  "tree_sorted t \<Longrightarrow> in_traverse (tree_insert x t) = ordered_insert x (in_traverse t)"
@proof @induct t @qed

lemma tree_insert_on_set [rewrite]:
  "tree_sorted t \<Longrightarrow> tree_set (tree_insert it t) = {it} \<union> tree_set t" by auto2

lemma tree_insert_sorted [backward]:
  "tree_sorted t \<Longrightarrow> tree_sorted (tree_insert x t)" by auto2

lemma tree_insert_max_inv:
  "tree_max_inv t \<Longrightarrow> tree_max_inv (tree_insert x t)"
@proof @induct t @qed

section {* Search on interval trees *}

fun is_overlap :: "nat interval \<Rightarrow> nat interval \<Rightarrow> bool" where
  "is_overlap (Interval a b) (Interval c d) \<longleftrightarrow> (b \<ge> c \<or> d \<ge> a)"
setup {* add_rewrite_rule @{thm is_overlap.simps} *}

fun tree_search :: "interval_tree \<Rightarrow> nat interval \<Rightarrow> bool" where
  "tree_search Tip x = False"
| "tree_search (Node l y m r) x =
   (if is_overlap x y then True
    else if l \<noteq> Tip \<and> tmax l \<ge> low x then tree_search l x
    else tree_search r x)"
setup {* fold add_rewrite_rule @{thms tree_search.simps} *}

fun tree_interval_inv :: "interval_tree \<Rightarrow> bool" where
  "tree_interval_inv Tip = True"
| "tree_interval_inv (Node l (Interval a b) m r) = (a \<le> b \<and> tree_interval_inv l \<and> tree_interval_inv r)"
setup {* fold add_rewrite_rule @{thms tree_interval_inv.simps} *}

lemma tree_search_correct [rewrite]:
  "tree_sorted t \<Longrightarrow> tree_interval_inv t \<Longrightarrow> tree_max_inv t \<Longrightarrow> a \<le> b \<Longrightarrow>
   tree_search t (Interval a b) \<longleftrightarrow> (\<exists>p\<in>tree_set t. is_overlap (Interval a b) p)"
@proof @induct t @qed

end
