(* Red-black trees, following Section 8.4 of "Certified Programming
   with Dependent Types", and RBT_Impl in HOL/Library. *)

theory RBT_Ex
imports Auto2 Lists_Ex
begin

section {* Definition of RBT, and basic setup *}

datatype color = R | B
datatype 'a pre_rbt =
    Leaf
  | Node (lsub: "'a pre_rbt") (cl: color) (nval: 'a) (rsub: "'a pre_rbt")
where
  "cl Leaf = B"

setup {* add_resolve_prfstep @{thm color.distinct(1)} *}
setup {* add_resolve_prfstep @{thm pre_rbt.distinct(2)} *}
setup {* fold add_rewrite_rule @{thms pre_rbt.sel} *}

text {* Case checking: after checking the Leaf case, can assume t is in the
  form Node l c n r. *}

setup {* add_gen_prfstep ("rbt_case_intro",
     [WithTerm @{term_pat "?t::?'a pre_rbt"},
      Filter (unique_free_filter "t"),
      CreateCase @{term_pat "(?t::?'a pre_rbt) = Leaf"}]) *}
setup {* add_forward_prfstep @{thm pre_rbt.collapse} *}

text {* Induction: after checking the Leaf case, can assume P (lsub t) and
  P (rsub t) holds when proving P t. *}

theorem pre_rbt_induct': "P Leaf \<Longrightarrow> (\<forall>t. P (lsub t) \<and> P (rsub t) \<longrightarrow> P t) \<Longrightarrow> P t"
  apply (induction t) apply blast by (metis pre_rbt.sel(1) pre_rbt.sel(5))
setup {* add_prfstep_induction @{thm pre_rbt_induct'} *}

subsection {* Some trivial lemmas *}

theorem not_R [forward]: "c \<noteq> R \<Longrightarrow> c = B" using color.exhaust by blast
theorem not_B [forward]: "c \<noteq> B \<Longrightarrow> c = R" using color.exhaust by blast
theorem red_not_leaf [forward]: "cl t = R \<Longrightarrow> t \<noteq> Leaf" by auto
theorem if_not_Leaf [rewrite]: "(if Node l c v r = Leaf then a else b) = b" by simp
theorem if_R [rewrite]: "(if R = B then a else b) = b" by simp
theorem if_B [rewrite]: "(if B = R then a else b) = b" by simp

section {* Definition of main functions and invariants *}

fun min_depth :: "'a pre_rbt \<Rightarrow> nat" where
  "min_depth Leaf = 0"
| "min_depth (Node l c a r) = min (min_depth l) (min_depth r) + 1"

fun max_depth :: "'a pre_rbt \<Rightarrow> nat" where
  "max_depth Leaf = 0"
| "max_depth (Node l c a r) = max (max_depth l) (max_depth r) + 1"

fun black_depth :: "'a pre_rbt \<Rightarrow> nat" where
  "black_depth Leaf = 0"
| "black_depth (Node l R a r) = min (black_depth l) (black_depth r)"
| "black_depth (Node l B a r) = min (black_depth l) (black_depth r) + 1"

fun cl_inv :: "'a pre_rbt \<Rightarrow> bool" where
  "cl_inv Leaf = True"
| "cl_inv (Node l R a r) = (cl_inv l \<and> cl_inv r \<and> cl l = B \<and> cl r = B)"
| "cl_inv (Node l B a r) = (cl_inv l \<and> cl_inv r)"

fun bd_inv :: "'a pre_rbt \<Rightarrow> bool" where
  "bd_inv Leaf = True"
| "bd_inv (Node l c a r) = (bd_inv l \<and> bd_inv r \<and> black_depth l = black_depth r)"

definition is_rbt :: "'a pre_rbt \<Rightarrow> bool" where
  "is_rbt t = (cl_inv t \<and> bd_inv t)"

setup {* fold add_rewrite_rule (
  @{thms min_depth.simps} @ @{thms max_depth.simps} @ @{thms black_depth.simps} @
  @{thms cl_inv.simps} @ @{thms bd_inv.simps} @ [@{thm is_rbt_def}]) *}
theorem cl_invI: "cl_inv l \<Longrightarrow> cl_inv r \<Longrightarrow> cl_inv (Node l B a r)" by auto
setup {* add_forward_prfstep_cond @{thm cl_invI} [with_term "cl_inv (Node ?l B ?a ?r)"] *}

subsection {* Properties of bd_inv *}

theorem bd_inv_elimR [rewrite]:
  "bd_inv (Node l R a r) \<Longrightarrow> black_depth (Node l R a r) = black_depth l" by auto2
theorem bd_inv_elimB [rewrite]:
  "bd_inv (Node l B a r) \<Longrightarrow> black_depth (Node l B a r) = black_depth l + 1" by auto2
theorem bd_inv_intro: "black_depth l = black_depth r \<Longrightarrow> bd_inv l \<Longrightarrow> bd_inv r \<Longrightarrow> bd_inv (Node l c a r)" by auto2
setup {* add_forward_prfstep_cond @{thm bd_inv_intro} [with_term "Node ?l ?c ?a ?r"] *}

subsection {* is_rbt is recursive *}

theorem is_rbt_rec [forward]: "is_rbt (Node l c a r) \<Longrightarrow> is_rbt l \<and> is_rbt r"
  by (tactic {* auto2s_tac @{context} (CASE "c = R") *})

section {* Balancedness of is_rbt *}

theorem depth_min: "is_rbt t \<Longrightarrow> black_depth t \<le> min_depth t"
  by (tactic {* auto2s_tac @{context}
    (CASE "t = Leaf" THEN
     CASE "cl t = R" WITH
        OBTAIN "black_depth t \<le> min (min_depth (lsub t)) (min_depth (rsub t))") *} )

theorem depth_max: "is_rbt t \<Longrightarrow> if cl t = R then max_depth t \<le> 2 * black_depth t + 1
                                 else max_depth t \<le> 2 * black_depth t"
  by (tactic {* auto2s_tac @{context}
    (CASE "t = Leaf" THEN CASE "cl t = R" THEN
     OBTAIN "max_depth (lsub t) \<le> 2 * black_depth (lsub t) + 1" THEN
     OBTAIN "max_depth (rsub t) \<le> 2 * black_depth (rsub t) + 1") *} )

setup {* fold add_forward_prfstep [@{thm depth_min}, @{thm depth_max}] *}
theorem balanced: "is_rbt t \<Longrightarrow> max_depth t \<le> 2 * min_depth t + 1"
  by (tactic {* auto2s_tac @{context}
    (OBTAIN "max_depth t \<le> 2 * black_depth t + 1") *})
setup {* fold del_prfstep_thm [@{thm depth_min}, @{thm depth_max}] *}

section {* Balancing function on RBT *}

fun balanceR :: "'a pre_rbt \<Rightarrow> 'a pre_rbt" where
  "balanceR (Node a B x (Node (Node b R z c) R y d)) = Node (Node a B x b) R z (Node c B y d)"
| "balanceR (Node a B x (Node b R y (Node c R z d))) = Node (Node a B x b) R y (Node c B z d)"
| "balanceR t = t"
setup {* fold add_rewrite_rule @{thms balanceR.simps(1,4-5)} *}

theorem balanceR_def' [rewrite]:
  "cl b = B \<Longrightarrow> balanceR (Node a B x (Node b R y (Node c R z d))) = Node (Node a B x b) R y (Node c B z d)"
  "cl r = B \<Longrightarrow> balanceR (Node l B x r) = Node l B x r"
  "cl r = R \<Longrightarrow> cl (lsub r) = B \<Longrightarrow> cl (rsub r) = B \<Longrightarrow> balanceR (Node l B x r) = Node l B x r"
  apply (metis balanceR.simps(2) balanceR.simps(3) pre_rbt.collapse)
  apply (metis balanceR.simps(15) balanceR.simps(6) pre_rbt.collapse)
  by (smt balanceR.simps(10) balanceR.simps(13) balanceR.simps(14) balanceR.simps(9) pre_rbt.collapse red_not_leaf)

fun balance :: "'a pre_rbt \<Rightarrow> 'a pre_rbt" where
  "balance (Node (Node (Node a R z b) R y c) B x d) = Node (Node a B z b) R y (Node c B x d)"
| "balance (Node (Node a R y (Node b R z c)) B x d) = Node (Node a B y b) R z (Node c B x d)"
| "balance t = balanceR t"
setup {* fold add_rewrite_rule @{thms balance.simps(1,4)} *}

theorem balance_def' [rewrite]:
  "balance (Node l R x r) = Node l R x r"
  "cl a = B \<Longrightarrow> balance (Node (Node a R y (Node b R z c)) B x d) = Node (Node a B y b) R z (Node c B x d)"
  "cl l = B \<Longrightarrow> balance (Node l B x r) = balanceR (Node l B x r)"
  "cl l = R \<Longrightarrow> cl (lsub l) = B \<Longrightarrow> cl (rsub l) = B \<Longrightarrow> balance (Node l B x r) = balanceR (Node l B x r)"
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

subsection {* Balance function preserves set of keys *}

fun rbt_set :: "'a pre_rbt \<Rightarrow> 'a set" where
  "rbt_set Leaf = {}"
| "rbt_set (Node l c y r) = {y} \<union> rbt_set l \<union> rbt_set r"
setup {* fold add_rewrite_rule @{thms rbt_set.simps} *}

theorem rbt_set_balanceR [rewrite]: "rbt_set (balanceR t) = rbt_set t"
  by (tactic {* auto2s_tac @{context} balanceR_cases *})
theorem rbt_set_balance [rewrite]: "rbt_set (balance t) = rbt_set t"
  by (tactic {* auto2s_tac @{context} balance_cases *})

subsection {* balance function preserves bd_inv *}

theorem balance_bd': "bd_inv t \<Longrightarrow> bd_inv (balanceR t) \<and> black_depth t = black_depth (balanceR t)"
  by (tactic {* auto2s_tac @{context} balanceR_cases *})
setup {* fold add_backward_prfstep [conj_left_th @{thm balance_bd'}, conj_right_th @{thm balance_bd'}] *}

theorem balance_bd: "bd_inv t \<Longrightarrow> bd_inv (balance t) \<and> black_depth (balance t) = black_depth t"
  by (tactic {* auto2s_tac @{context} balance_cases *})
setup {* add_backward_prfstep (conj_left_th @{thm balance_bd}) #> add_rewrite_rule (conj_right_th @{thm balance_bd}) *}

subsection {* Definition and basic properties of cl_inv' *}

fun cl_inv' :: "'a pre_rbt \<Rightarrow> bool" where
  "cl_inv' Leaf = True"
| "cl_inv' (Node l c a r) = (cl_inv l \<and> cl_inv r)"
setup {* fold add_rewrite_rule @{thms cl_inv'.simps} *}

theorem cl_inv_B [forward, backward2]: "cl t = B \<Longrightarrow> cl_inv' t \<Longrightarrow> cl_inv t" by auto2
theorem cl_inv_R [forward]: "cl_inv' (Node l R x r) \<Longrightarrow> cl l = B \<Longrightarrow> cl r = B \<Longrightarrow> cl_inv (Node l R x r)" by auto2
theorem cl_inv_imp [forward]: "cl_inv t \<Longrightarrow> cl_inv' t"
  by (tactic {* auto2s_tac @{context} (CASE "cl t = R") *})
theorem cl_inv'I: "cl_inv l \<Longrightarrow> cl_inv r \<Longrightarrow> cl_inv' (Node l c a r)" by auto
setup {* add_forward_prfstep_cond @{thm cl_inv'I} [with_term "cl_inv' (Node ?l ?c ?a ?r)"] *}

subsection {* balance function preserves cl_inv *}

theorem balanceR [backward1, backward2]:
  "cl_inv l \<Longrightarrow> cl_inv' r \<Longrightarrow> cl_inv (balanceR (Node l B a r))"
  by (tactic {* auto2s_tac @{context} balanceR_node_cases *})

theorem balance1 [backward1, backward2]:
  "cl_inv' l \<Longrightarrow> cl_inv r \<Longrightarrow> cl_inv (balance (Node l B a r))"
  by (tactic {* auto2s_tac @{context} balance_node_cases *})
theorem balance2 [backward1, backward2]:
  "cl_inv l \<Longrightarrow> cl_inv' r \<Longrightarrow> cl_inv (balance (Node l B a r))"
  by (tactic {* auto2s_tac @{context} balance_node_cases *})
setup {* del_prfstep_thm @{thm balanceR} *}

subsection {* Balance function takes non-leafs to non-leafs *}

theorem balanceR_non_Leaf [resolve]: "balanceR (Node l c a r) \<noteq> Leaf"
  by (tactic {* auto2s_tac @{context} (CASE "c = R" THEN balanceR_node_cases) *})
theorem balance_non_Leaf: "balance (Node l c a r) \<noteq> Leaf"
  by (tactic {* auto2s_tac @{context} (CASE "c = R" THEN balance_node_cases) *})
setup {* add_forward_prfstep_cond @{thm balance_non_Leaf} [with_term "balance (Node ?l ?c ?a ?r)"] *}

section {* ins function *}

fun ins :: "'a::order \<Rightarrow> 'a pre_rbt \<Rightarrow> 'a pre_rbt" where
  "ins x Leaf = Node Leaf R x Leaf"
| "ins x (Node l c y r) =
    (if x = y then Node l c y r
     else if x < y then balance (Node (ins x l) c y r)
     else balance (Node l c y (ins x r)))"
setup {* fold add_rewrite_rule @{thms ins.simps} *}

subsection {* ins function takes non-leaf to non-leafs *}

theorem ins_non_Leaf: "ins x t \<noteq> Leaf" by auto2
setup {* add_forward_prfstep_cond @{thm ins_non_Leaf} [with_term "ins ?x ?t"] *}

subsection {* Properties of ins function on cl_inv, bd_inv, and set of keys *}

theorem cl_inv_ins: "cl_inv t \<Longrightarrow> if cl t = B then cl_inv (ins x t) else cl (ins x t) = R \<and> cl_inv' (ins x t)" by auto2

setup {* add_forward_prfstep_cond @{thm cl_inv_ins} [with_term "ins ?x ?t"] *}
theorem cl_inv_ins_l [backward]: "cl_inv t \<Longrightarrow> cl_inv (lsub (ins x t))" by auto2
theorem cl_inv_ins_r [backward]: "cl_inv t \<Longrightarrow> cl_inv (rsub (ins x t))" by auto2
setup {* del_prfstep_thm @{thm cl_inv_ins} *}

theorem bd_inv_ins: "bd_inv t \<Longrightarrow> bd_inv (ins x t) \<and> black_depth t = black_depth (ins x t)"
  by (tactic {* auto2s_tac @{context} (CASE "cl t = R") *})
setup {* add_forward_prfstep_cond (conj_left_th @{thm bd_inv_ins}) [with_term "ins ?x ?t"] *}

theorem rbt_set_ins [rewrite]: "rbt_set (ins x t) = {x} \<union> rbt_set t" by auto2

section {* Insert function *}

fun makeBlack :: "'a pre_rbt \<Rightarrow> 'a pre_rbt" where
  "makeBlack Leaf = Leaf"
| "makeBlack (Node l c a r) = Node l B a r"

definition rbt_insert :: "'a::order \<Rightarrow> 'a pre_rbt \<Rightarrow> 'a pre_rbt" where
  "rbt_insert x t = makeBlack (ins x t)"

setup {* fold add_rewrite_rule (@{thms makeBlack.simps} @ [@{thm rbt_insert_def}]) *}

theorem rbt_set_makeBlack [rewrite]: "rbt_set (makeBlack t) = rbt_set t" by auto2

theorem cl_inv_insert [backward]: "cl_inv t \<Longrightarrow> cl_inv (rbt_insert x t)" by auto2
theorem bd_inv_insert [backward]: "bd_inv t \<Longrightarrow> bd_inv (rbt_insert x t)" by auto2

theorem is_rbt_insert: "is_rbt t \<Longrightarrow> is_rbt (rbt_insert x t)" by auto2

theorem rbt_set_insert: "rbt_set (rbt_insert x t) = {x} \<union> rbt_set t" by auto2

section {* Sortedness on trees *}

fun base_tree :: "'a pre_rbt \<Rightarrow> 'a tree" where
  "base_tree Leaf = Tip"
| "base_tree (Node l c a r) = Lists_Ex.Node (base_tree l) a (base_tree r)"
setup {* fold add_rewrite_rule @{thms base_tree.simps} *}

theorem balanceR_as_rotate1 [rewrite]: "cl r = R \<Longrightarrow> cl (lsub r) = R \<Longrightarrow>
  base_tree (balanceR (Node l B x r)) = rotateL (rotateR_at_R (base_tree (Node l B x r)))" by auto2
theorem balanceR_as_rotate2 [rewrite]: "cl r = R \<Longrightarrow> cl (lsub r) = B \<Longrightarrow> cl (rsub r) = R \<Longrightarrow>
  base_tree (balanceR (Node l B x r)) = rotateL (base_tree (Node l B x r))" by auto2
theorem balance_as_rotate1 [rewrite]: "cl l = R \<Longrightarrow> cl (lsub l) = R \<Longrightarrow>
  base_tree (balance (Node l B x r)) = rotateR (base_tree (Node l B x r))" by auto2
theorem balance_as_rotate2 [rewrite]: "cl l = R \<Longrightarrow> cl (lsub l) = B \<Longrightarrow> cl (rsub l) = R \<Longrightarrow>
  base_tree (balance (Node l B x r)) = rotateR (rotateL_at_L (base_tree (Node l B x r)))" by auto2

definition rbt_sorted :: "'a::linorder pre_rbt \<Rightarrow> bool" where
  "rbt_sorted t = tree_sorted (base_tree t)"
setup {* add_rewrite_rule_bidir @{thm rbt_sorted_def} *}

theorem rbt_set_base [rewrite_bidir]: "rbt_set t = tree_set (base_tree t)" by auto2

theorem balanceR_sorted [backward]: "rbt_sorted t \<Longrightarrow> rbt_sorted (balanceR t)"
  by (tactic {* auto2s_tac @{context} balanceR_cases *})
theorem balance_sorted [backward]: "rbt_sorted t \<Longrightarrow> rbt_sorted (balance t)"
  by (tactic {* auto2s_tac @{context} balance_cases *})

theorem ins_sorted [backward]: "rbt_sorted t \<Longrightarrow> rbt_sorted (ins x t)"
  by (tactic {* auto2s_tac @{context}
    (CASE "t = Leaf" THEN CASE "x = nval t" THEN CASE "x < nval t") *})

theorem insert_sorted: "rbt_sorted t \<Longrightarrow> rbt_sorted (rbt_insert x t)"
  by (tactic {* auto2s_tac @{context}
    (OBTAIN "rbt_sorted (ins x t) = rbt_sorted (rbt_insert x t)") *})

section {* Search on sorted trees and its correctness *}

fun rbt_search :: "'a::ord pre_rbt \<Rightarrow> 'a \<Rightarrow> bool" where
  "rbt_search Leaf x = False"
| "rbt_search (Node l c y r) x =
  (if x = y then True
   else if x < y then rbt_search l x
   else rbt_search r x)"
setup {* fold add_rewrite_rule @{thms rbt_search.simps} *}

theorem rbt_search_correct: "rbt_sorted t \<Longrightarrow> (rbt_search t x \<longleftrightarrow> x \<in> rbt_set t)" by auto2

end
