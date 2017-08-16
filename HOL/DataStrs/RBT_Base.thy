(* Basic definition of red-black trees. This is the shared portion
   for the verification of functional and imperative programs.

   Proofs follow Section 8.4 of "Certified Programming with Dependent
   types", and RBT_Impl in HOL/Library. The algorithms ultimately come
   from "Red-black trees in a functional setting" by Okasaki.
 *)

theory RBT_Base
imports Lists_Ex
begin

section {* Definition of RBT, and basic setup *}

datatype color = R | B
datatype ('a, 'b) pre_rbt =
    Leaf
  | Node (lsub: "('a, 'b) pre_rbt") (cl: color) (key: 'a) (val: 'b) (rsub: "('a, 'b) pre_rbt")
where
  "cl Leaf = B"

setup {* add_resolve_prfstep @{thm color.distinct(1)} *}
setup {* add_resolve_prfstep @{thm pre_rbt.distinct(2)} *}
setup {* fold add_rewrite_rule @{thms pre_rbt.sel} *}
setup {* add_forward_prfstep (equiv_forward_th (@{thm pre_rbt.simps(1)})) *}
setup {* add_forward_prfstep @{thm pre_rbt.collapse} *}
setup {* add_var_induct_rule @{thm pre_rbt.induct} *}

subsection {* Some trivial lemmas *}

theorem not_R [forward]: "c \<noteq> R \<Longrightarrow> c = B" using color.exhaust by blast
theorem not_B [forward]: "c \<noteq> B \<Longrightarrow> c = R" using color.exhaust by blast
theorem red_not_leaf [forward]: "cl t = R \<Longrightarrow> t \<noteq> Leaf" by auto

section {* Definition of main functions and invariants *}

fun min_depth :: "('a, 'b) pre_rbt \<Rightarrow> nat" where
  "min_depth Leaf = 0"
| "min_depth (Node l c k v r) = min (min_depth l) (min_depth r) + 1"

fun max_depth :: "('a, 'b) pre_rbt \<Rightarrow> nat" where
  "max_depth Leaf = 0"
| "max_depth (Node l c k v r) = max (max_depth l) (max_depth r) + 1"

fun black_depth :: "('a, 'b) pre_rbt \<Rightarrow> nat" where
  "black_depth Leaf = 0"
| "black_depth (Node l R k v r) = min (black_depth l) (black_depth r)"
| "black_depth (Node l B k v r) = min (black_depth l) (black_depth r) + 1"

fun cl_inv :: "('a, 'b) pre_rbt \<Rightarrow> bool" where
  "cl_inv Leaf = True"
| "cl_inv (Node l R k v r) = (cl_inv l \<and> cl_inv r \<and> cl l = B \<and> cl r = B)"
| "cl_inv (Node l B k v r) = (cl_inv l \<and> cl_inv r)"
setup {* add_property_const @{term cl_inv} *}

fun bd_inv :: "('a, 'b) pre_rbt \<Rightarrow> bool" where
  "bd_inv Leaf = True"
| "bd_inv (Node l c k v r) = (bd_inv l \<and> bd_inv r \<and> black_depth l = black_depth r)"
setup {* add_property_const @{term bd_inv} *}

definition is_rbt :: "('a, 'b) pre_rbt \<Rightarrow> bool" where
  "is_rbt t = (cl_inv t \<and> bd_inv t)"
setup {* add_property_const @{term is_rbt} *}

setup {* fold add_rewrite_rule (
  @{thms min_depth.simps} @ @{thms max_depth.simps} @ @{thms black_depth.simps} @
  @{thms cl_inv.simps} @ @{thms bd_inv.simps} @ [@{thm is_rbt_def}]) *}
theorem cl_invI: "cl_inv l \<Longrightarrow> cl_inv r \<Longrightarrow> cl_inv (Node l B k v r)" by auto2
setup {* add_forward_prfstep_cond @{thm cl_invI} [with_term "cl_inv (Node ?l B ?k ?v ?r)"] *}

subsection {* Properties of bd_inv *}

theorem bd_inv_elimR [rewrite]:
  "bd_inv (Node l R k v r) \<Longrightarrow> black_depth (Node l R k v r) = black_depth l" by auto2
theorem bd_inv_elimB [rewrite]:
  "bd_inv (Node l B k v r) \<Longrightarrow> black_depth (Node l B k v r) = black_depth l + 1" by auto2
theorem bd_inv_intro: "bd_inv l \<Longrightarrow> bd_inv r \<Longrightarrow> black_depth l = black_depth r \<Longrightarrow> bd_inv (Node l c k v r)" by auto2
setup {* add_forward_prfstep_cond @{thm bd_inv_intro} [with_term "Node ?l ?c ?k ?v ?r"] *}

subsection {* is_rbt is recursive *}

theorem is_rbt_rec [forward]: "is_rbt (Node l c k v r) \<Longrightarrow> is_rbt l \<and> is_rbt r"
@proof @case "c = R" @qed

section {* Balancedness of is_rbt *}

theorem depth_min: "is_rbt t \<Longrightarrow> black_depth t \<le> min_depth t"
@proof
  @var_induct t @with
    @subgoal "t = Node l c k v r"
      @case "c = R" @with
      @have "black_depth (Node l c k v r) \<le> min (min_depth l) (min_depth r)" @end
    @endgoal
  @end
@qed

theorem two_distrib [rewrite]: "(2::nat) * (a + 1) = 2 * a + 2" by simp
theorem depth_max: "is_rbt t \<Longrightarrow> if cl t = R then max_depth t \<le> 2 * black_depth t + 1
                                 else max_depth t \<le> 2 * black_depth t"
@proof
  @var_induct t @with
    @subgoal "t = Node l c k v r"
      @case "c = R" @then
      @have "max_depth l \<le> 2 * black_depth l + 1" @then
      @have "max_depth r \<le> 2 * black_depth r + 1"
    @endgoal
  @end
@qed

setup {* fold add_forward_prfstep [@{thm depth_min}, @{thm depth_max}] *}
  
setup {* add_backward_prfstep @{thm Nat.add_le_mono1} *}
setup {* add_backward_prfstep @{thm Nat.mult_le_mono2} *}

theorem balanced: "is_rbt t \<Longrightarrow> max_depth t \<le> 2 * min_depth t + 1"
@proof @have "max_depth t \<le> 2 * black_depth t + 1" @qed
setup {* fold del_prfstep_thm [@{thm depth_min}, @{thm depth_max}] *}

subsection {* Definition and basic properties of cl_inv' *}

fun cl_inv' :: "('a, 'b) pre_rbt \<Rightarrow> bool" where
  "cl_inv' Leaf = True"
| "cl_inv' (Node l c k v r) = (cl_inv l \<and> cl_inv r)"
setup {* fold add_rewrite_rule @{thms cl_inv'.simps} *}
setup {* add_property_const @{term cl_inv'} *}

theorem cl_inv_B [forward, backward1]:
  "cl_inv' t \<Longrightarrow> cl t = B \<Longrightarrow> cl_inv t"
@proof @case "t = Leaf" @qed

theorem cl_inv_R [forward]:
  "cl_inv' (Node l R k v r) \<Longrightarrow> cl l = B \<Longrightarrow> cl r = B \<Longrightarrow> cl_inv (Node l R k v r)" by auto2

theorem cl_inv_imp [forward]: "cl_inv t \<Longrightarrow> cl_inv' t"
@proof @case "t = Leaf" @then @case "cl t = R" @qed

theorem cl_inv'I: "cl_inv l \<Longrightarrow> cl_inv r \<Longrightarrow> cl_inv' (Node l c k v r)" by auto
setup {* add_forward_prfstep_cond @{thm cl_inv'I} [with_term "cl_inv' (Node ?l ?c ?k ?v ?r)"] *}

subsection {* Set of keys, sortedness *}

fun rbt_in_traverse :: "('a, 'b) pre_rbt \<Rightarrow> 'a list" where
  "rbt_in_traverse Leaf = []"
| "rbt_in_traverse (Node l c k v r) = (rbt_in_traverse l) @ [k] @ (rbt_in_traverse r)"
setup {* fold add_rewrite_rule @{thms rbt_in_traverse.simps} *}

fun rbt_set :: "('a, 'b) pre_rbt \<Rightarrow> 'a set" where
  "rbt_set Leaf = {}"
| "rbt_set (Node l c k v r) = {k} \<union> rbt_set l \<union> rbt_set r"
setup {* fold add_rewrite_rule @{thms rbt_set.simps} *}

fun rbt_in_traverse_pairs :: "('a, 'b) pre_rbt \<Rightarrow> ('a \<times> 'b) list" where
  "rbt_in_traverse_pairs Leaf = []"
| "rbt_in_traverse_pairs (Node l c k v r) = (rbt_in_traverse_pairs l) @ [(k, v)] @ (rbt_in_traverse_pairs r)"
setup {* fold add_rewrite_rule @{thms rbt_in_traverse_pairs.simps} *}

theorem rbt_in_traverse_fst:
  "map fst (rbt_in_traverse_pairs t) = rbt_in_traverse t"
@proof @var_induct t @qed
setup {* add_forward_prfstep_cond @{thm rbt_in_traverse_fst} [with_term "rbt_in_traverse_pairs ?t"] *}

definition rbt_map :: "('a, 'b) pre_rbt \<Rightarrow> ('a, 'b) map" where
  "rbt_map t = map_of_alist (rbt_in_traverse_pairs t)"
setup {* add_rewrite_rule @{thm rbt_map_def} *}

theorem rbt_in_traverse_non_empty: "rbt_in_traverse (Node l c k v r) \<noteq> []" by auto2
setup {* add_forward_prfstep_cond @{thm rbt_in_traverse_non_empty}
  [with_term "rbt_in_traverse (Node ?l ?c ?k ?v ?r)"] *}

theorem rbt_in_traverse_pairs_non_empty: "rbt_in_traverse_pairs (Node l c k v r) \<noteq> []" by auto2
setup {* add_forward_prfstep_cond @{thm rbt_in_traverse_pairs_non_empty}
  [with_term "rbt_in_traverse_pairs (Node ?l ?c ?k ?v ?r)"] *}

fun rbt_sorted :: "('a::linorder, 'b) pre_rbt \<Rightarrow> bool" where
  "rbt_sorted Leaf = True"
| "rbt_sorted (Node l c k v r) = ((\<forall>x\<in>rbt_set l. x < k) \<and> (\<forall>x\<in>rbt_set r. k < x)
                                  \<and> rbt_sorted l \<and> rbt_sorted r)"
setup {* fold add_rewrite_rule @{thms rbt_sorted.simps} *}

theorem rbt_sorted_lr [forward]:
  "rbt_sorted (Node l c k v r) \<Longrightarrow> rbt_sorted l \<and> rbt_sorted r" by auto2

theorem rbt_inorder_preserve_set [rewrite_back]:
  "set (rbt_in_traverse t) = rbt_set t"
@proof @var_induct t @qed

theorem rbt_inorder_sorted [rewrite_back]:
  "strict_sorted (rbt_in_traverse t) = rbt_sorted t"
@proof @var_induct t @qed

setup {* fold del_prfstep_thm (@{thms rbt_set.simps} @ @{thms rbt_sorted.simps}) *}

end
