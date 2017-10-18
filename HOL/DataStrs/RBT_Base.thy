(* Basic definition of red-black trees. This is the shared portion
   for the verification of functional and imperative programs.

   Proofs follow Section 8.4 of "Certified Programming with Dependent
   types", and RBT_Impl in HOL/Library. The algorithms ultimately come
   from "Red-black trees in a functional setting" by Okasaki.
 *)

theory RBT_Base
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
setup {* add_resolve_prfstep @{thm rbt.distinct(2)} *}
setup {* fold add_rewrite_rule @{thms rbt.sel} *}
setup {* add_forward_prfstep (equiv_forward_th (@{thm rbt.simps(1)})) *}
setup {* add_forward_prfstep_cond @{thm rbt.collapse} [with_cond "?tree \<noteq> Node ?l ?c ?k ?v ?r"] *}
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
| "rbt_in_traverse (Node l c k v r) = (rbt_in_traverse l) @ [k] @ (rbt_in_traverse r)"
setup {* fold add_rewrite_rule @{thms rbt_in_traverse.simps} *}

fun rbt_set :: "('a, 'b) rbt \<Rightarrow> 'a set" where
  "rbt_set Leaf = {}"
| "rbt_set (Node l c k v r) = {k} \<union> rbt_set l \<union> rbt_set r"
setup {* fold add_rewrite_rule @{thms rbt_set.simps} *}

fun rbt_in_traverse_pairs :: "('a, 'b) rbt \<Rightarrow> ('a \<times> 'b) list" where
  "rbt_in_traverse_pairs Leaf = []"
| "rbt_in_traverse_pairs (Node l c k v r) = (rbt_in_traverse_pairs l) @ [(k, v)] @ (rbt_in_traverse_pairs r)"
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

end
