theory RBT_Ex
imports Auto2 Lists_Ex
begin

datatype color = R | B
datatype 'a pre_rbt =
    Leaf
  | Node (lsub: "'a pre_rbt") (cl: color) (nval: 'a) (rsub: "'a pre_rbt")
where
  "cl Leaf = B"

setup {* fold add_rew_const [@{term "R"}, @{term "B"}, @{term "Leaf"}] *}
setup {* fold add_rewrite_rule [@{thm pre_rbt.sel(2)}, @{thm pre_rbt.sel(3)}] *}
setup {* add_simp_rule_cond @{thm pre_rbt.sel(1)} [with_cond "?x21.0 \<noteq> lsub ?t"] *}
setup {* add_simp_rule_cond @{thm pre_rbt.sel(5)} [with_cond "?x24.0 \<noteq> rsub ?t"] *}

(* Case checking. *)
setup {* add_gen_prfstep ("rbt_case_intro",
     [WithTerm @{term_pat "?t::?'a pre_rbt"},
      Filter (unique_free_filter "t"),
      CreateCase ([@{term_pat "(?t::?'a pre_rbt) = Leaf"}], [])]) *}

setup {* add_forward_prfstep @{thm pre_rbt.collapse} *}  (* Case checking after Leaf case. *)
setup {* add_resolve_prfstep @{thm color.distinct(1)} *}
setup {* add_resolve_prfstep @{thm pre_rbt.distinct(2)} *}

abbreviation LL :: "'a pre_rbt \<Rightarrow> 'a pre_rbt" where "LL t \<equiv> lsub (lsub t)"
abbreviation LR :: "'a pre_rbt \<Rightarrow> 'a pre_rbt" where "LR t \<equiv> rsub (lsub t)"
abbreviation RL :: "'a pre_rbt \<Rightarrow> 'a pre_rbt" where "RL t \<equiv> lsub (rsub t)"
abbreviation RR :: "'a pre_rbt \<Rightarrow> 'a pre_rbt" where "RR t \<equiv> rsub (rsub t)"
abbreviation LLL :: "'a pre_rbt \<Rightarrow> 'a pre_rbt" where "LLL t \<equiv> LL (lsub t)"
abbreviation LLR :: "'a pre_rbt \<Rightarrow> 'a pre_rbt" where "LLR t \<equiv> LR (lsub t)"
abbreviation LRL :: "'a pre_rbt \<Rightarrow> 'a pre_rbt" where "LRL t \<equiv> RL (lsub t)"
abbreviation LRR :: "'a pre_rbt \<Rightarrow> 'a pre_rbt" where "LRR t \<equiv> RR (lsub t)"
abbreviation RLL :: "'a pre_rbt \<Rightarrow> 'a pre_rbt" where "RLL t \<equiv> LL (rsub t)"
abbreviation RLR :: "'a pre_rbt \<Rightarrow> 'a pre_rbt" where "RLR t \<equiv> LR (rsub t)"
abbreviation RRL :: "'a pre_rbt \<Rightarrow> 'a pre_rbt" where "RRL t \<equiv> RL (rsub t)"
abbreviation RRR :: "'a pre_rbt \<Rightarrow> 'a pre_rbt" where "RRR t \<equiv> RR (rsub t)"
abbreviation LV :: "'a pre_rbt \<Rightarrow> 'a" where "LV t \<equiv> nval (lsub t)"
abbreviation RV :: "'a pre_rbt \<Rightarrow> 'a" where "RV t \<equiv> nval (rsub t)"
abbreviation LLV :: "'a pre_rbt \<Rightarrow> 'a" where "LLV t \<equiv> nval (LL t)"
abbreviation LRV :: "'a pre_rbt \<Rightarrow> 'a" where "LRV t \<equiv> nval (LR t)"
abbreviation RLV :: "'a pre_rbt \<Rightarrow> 'a" where "RLV t \<equiv> nval (RL t)"
abbreviation RRV :: "'a pre_rbt \<Rightarrow> 'a" where "RRV t \<equiv> nval (RR t)"

(* Some trivial lemmas. *)
theorem not_R: "c \<noteq> R \<Longrightarrow> c = B" using color.exhaust by blast
theorem not_B: "c \<noteq> B \<Longrightarrow> c = R" using color.exhaust by blast
theorem red_not_leaf: "cl t = R \<Longrightarrow> t \<noteq> Leaf" by auto
theorem if_not_Leaf: "(if Node l c v r = Leaf then a else b) = b" by simp
theorem if_R: "(if R = B then a else b) = b" by simp
theorem if_B: "(if B = R then a else b) = b" by simp
setup {* fold add_forward_prfstep [@{thm not_R}, @{thm not_B}, @{thm red_not_leaf}] *}
setup {* fold add_simp_rule [@{thm if_not_Leaf}, @{thm if_R}, @{thm if_B}] *}

(* Induction. *)
theorem pre_rbt_induct': "P Leaf \<Longrightarrow> (\<forall>t. P (lsub t) \<and> P (rsub t) \<longrightarrow> P t) \<Longrightarrow> P t"
  apply (induction t) apply blast by (metis pre_rbt.sel(1) pre_rbt.sel(5))
setup {* add_prfstep_induction @{thm pre_rbt_induct'} *}

(* Definition of main functions and invariants. *)
fun min_depth :: "'a pre_rbt \<Rightarrow> nat" where
  "min_depth Leaf = 0"
| "min_depth (Node l c a r) = min (min_depth l) (min_depth r) + 1"
setup {* fold add_rewrite_rule @{thms min_depth.simps} *}

fun max_depth :: "'a pre_rbt \<Rightarrow> nat" where
  "max_depth Leaf = 0"
| "max_depth (Node l c a r) = max (max_depth l) (max_depth r) + 1"
setup {* fold add_rewrite_rule @{thms max_depth.simps} *}

fun black_depth :: "'a pre_rbt \<Rightarrow> nat" where
  "black_depth Leaf = 0"
| "black_depth (Node l c a r) =
    (if c = R then min (black_depth l) (black_depth r)
     else min (black_depth l) (black_depth r) + 1)"
setup {* fold add_rewrite_rule @{thms black_depth.simps} *}

fun cl_inv :: "'a pre_rbt \<Rightarrow> bool" where
  "cl_inv Leaf = True"
| "cl_inv (Node l c a r) = (cl_inv l \<and> cl_inv r \<and> (if c = R then cl l = B \<and> cl r = B else True))"
setup {* fold add_rewrite_rule @{thms cl_inv.simps} *}

fun bd_inv :: "'a pre_rbt \<Rightarrow> bool" where
  "bd_inv Leaf = True"
| "bd_inv (Node l c a r) = (bd_inv l \<and> bd_inv r \<and> black_depth l = black_depth r)"
setup {* fold add_rewrite_rule @{thms bd_inv.simps} *}

definition is_rbt :: "'a pre_rbt \<Rightarrow> bool" where
  "is_rbt t = (cl_inv t \<and> bd_inv t)"
setup {* add_rewrite_rule @{thm is_rbt_def} *}

(* More on bd_inv. *)
theorem bd_inv_elim': "bd_inv (Node l c a r) \<Longrightarrow> black_depth (Node l c a r) =
    (if c = R then black_depth l else black_depth l + 1)" by auto2
theorem bd_inv_intro: "black_depth l = black_depth r \<Longrightarrow> (bd_inv l \<longrightarrow> bd_inv r \<longrightarrow> bd_inv (Node l c a r))" by auto2

setup {* add_forward_prfstep @{thm bd_inv_elim'} *}
setup {* add_forward_prfstep_cond @{thm bd_inv_intro} [with_term "Node ?l ?c ?a ?r"] *}

(* is_rbt is recursive. *)
theorem is_rbt_rec: "is_rbt (Node l c a r) \<Longrightarrow> is_rbt l \<and> is_rbt r" by auto2
setup {* add_forward_prfstep @{thm is_rbt_rec} *}

(* is_rbt condition implies that the tree is roughly balanced. *)
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
    (OBTAIN "max_depth t \<le> 2 * black_depth t + 1"
     THEN OBTAIN "2 * black_depth t + 1 \<le> 2 * min_depth t + 1") *})
setup {* fold del_prfstep_thm [@{thm depth_min}, @{thm depth_max}] *}

(* Balance function. *)
definition balanceR :: "'a pre_rbt \<Rightarrow> 'a pre_rbt" where
  "balanceR t =
    (if t = Leaf then Leaf else
     if cl t = B then
       if cl (rsub t) = R then
         if cl (RL t) = R then
           Node (Node (lsub t) B (nval t) (RLL t)) R (RLV t) (Node (RLR t) B (RV t) (RR t))
         else if cl (RR t) = R then
           Node (Node (lsub t) B (nval t) (RL t)) R (RV t) (Node (RRL t) B (RRV t) (RRR t))
         else t
       else t
     else t)"
definition balance :: "'a pre_rbt \<Rightarrow> 'a pre_rbt" where
  "balance t =
    (if t = Leaf then Leaf else
     if cl t = B then
       if cl (lsub t) = R then
         if cl (LL t) = R then
           Node (Node (LLL t) B (LLV t) (LLR t)) R (LV t) (Node (LR t) B (nval t) (rsub t))
         else if cl (LR t) = R then
           Node (Node (LL t) B (LV t) (LRL t)) R (LRV t) (Node (LRR t) B (nval t) (rsub t))
         else balanceR t
       else balanceR t
     else t)"
theorem balance_on_R: "balance (Node l R a r) = Node l R a r" by (simp add: balance_def)

setup {*
  add_rewrite_rule_cond @{thm balance_def} (with_conds ["?t \<noteq> lsub ?s", "?t \<noteq> rsub ?s"]) #>
  add_rewrite_rule_cond @{thm balanceR_def} (with_conds ["?t \<noteq> lsub ?s", "?t \<noteq> rsub ?s"]) #>
  add_rewrite_rule @{thm balance_on_R} *}

(* Case checking when proving theorems involving balanceR t / balance t. *)
ML {*
val balanceR_scrpt =
CASE "t = Leaf"
THEN CASE "cl t = B" WITH
  CASE "cl (rsub t) = R" WITH
    (CASE "cl (RL t) = R" THEN CASE "cl (RR t) = R")

val balance_scrpt =
CASE "t = Leaf"
THEN CASE "cl t = B" WITH
  CASE "cl (lsub t) = R" WITH
    (CASE "cl (LL t) = R" THEN CASE "cl (LR t) = R")
*}

(* Present function on RBT. Balance function preserves present. *)
fun present :: "'a pre_rbt \<Rightarrow> 'a \<Rightarrow> bool" where
  "present Leaf x = False"
| "present (Node l c y r) x = (present l x \<or> x = y \<or> present r x)"
setup {* fold add_rewrite_rule @{thms present.simps} *}

theorem present_balanceR: "present (balanceR t) y = present t y"
  by (tactic {* auto2s_tac @{context} balanceR_scrpt *})
setup {* add_rewrite_rule @{thm present_balanceR} *}
theorem present_balance: "present (balance t) y = present t y"
  by (tactic {* auto2s_tac @{context} balance_scrpt *})
setup {* add_rewrite_rule @{thm present_balance} *}

(* balance function preserves bd_inv. *)
theorem balance_bd': "bd_inv t \<Longrightarrow> bd_inv (balanceR t) \<and> black_depth t = black_depth (balanceR t)"
  by (tactic {* auto2s_tac @{context} balanceR_scrpt *})
setup {* fold add_backward_prfstep [conj_left_th @{thm balance_bd'}, conj_right_th @{thm balance_bd'}] *}

theorem balance_bd: "bd_inv t \<Longrightarrow> bd_inv (balance t) \<and> black_depth t = black_depth (balance t)"
  by (tactic {* auto2s_tac @{context} balance_scrpt *})
setup {* add_backward_prfstep (conj_left_th @{thm balance_bd}) #>
         add_forward_prfstep_cond (conj_right_th @{thm balance_bd}) [with_term "black_depth (balance ?t)"] *}

(* cl_inv', and some trivial lemmas. *)
fun cl_inv' :: "'a pre_rbt \<Rightarrow> bool" where
  "cl_inv' Leaf = True"
| "cl_inv' (Node l c a r) = (cl_inv l \<and> cl_inv r)"

theorem cl_inv_def': "cl_inv (Node l c a r) \<Longrightarrow> cl_inv l \<and> cl_inv r" by simp
theorem cl_inv_def1: "cl_inv (Node l B a r) = (cl_inv l \<and> cl_inv r)" by simp
theorem cl_inv_def2: "cl_inv (Node l R a r) = (cl_inv l \<and> cl_inv r \<and> cl l = B \<and> cl r = B)" by simp
setup {* fold add_rewrite_rule (@{thms cl_inv'.simps} @ [@{thm cl_inv_def1}, @{thm cl_inv_def2}]) *}
setup {* add_forward_prfstep @{thm cl_inv_def'} *}
setup {* del_prfstep_thm @{thm cl_inv.simps(2)} *}

theorem cl_inv_B: "cl_inv' t \<Longrightarrow> cl t = B \<Longrightarrow> cl_inv t" by auto2
theorem cl_inv_imp: "cl_inv t \<Longrightarrow> cl_inv' t" by auto2
setup {* add_backward1_prfstep @{thm cl_inv_B} #> add_resolve_prfstep @{thm cl_inv_imp} *}

(* balance function preserves cl_inv. *)
theorem balanceR: "cl_inv l \<Longrightarrow> cl_inv' r \<Longrightarrow> cl_inv (balanceR (Node l B a r))" by auto2
setup {* add_backward1_prfstep @{thm balanceR} #> add_backward2_prfstep @{thm balanceR} *}

theorem balance1: "cl_inv' l \<Longrightarrow> cl_inv r \<Longrightarrow> cl_inv (balance (Node l B a r))" by auto2
theorem balance2: "cl_inv l \<Longrightarrow> cl_inv' r \<Longrightarrow> cl_inv (balance (Node l B a r))" by auto2
setup {* del_prfstep_thm @{thm balanceR} *}
setup {* fold (fn th => add_backward1_prfstep th o add_backward2_prfstep th)
              [@{thm balance1}, @{thm balance2}] *}

(* Insert function. *)
fun ins :: "nat \<Rightarrow> nat pre_rbt \<Rightarrow> nat pre_rbt" where
  "ins x Leaf = Node Leaf R x Leaf"
| "ins x (Node l c y r) =
    (if x = y then Node l c y r
     else if x < y then balance (Node (ins x l) c y r)
     else balance (Node l c y (ins x r)))"
setup {* fold add_rewrite_rule @{thms ins.simps} *}

theorem balanceR_non_Leaf: "balanceR (Node l c a r) \<noteq> Leaf" by auto2
setup {* add_resolve_prfstep @{thm balanceR_non_Leaf} *}
theorem balance_non_Leaf: "balance (Node l c a r) \<noteq> Leaf" by auto2
setup {* add_forward_prfstep_cond @{thm balance_non_Leaf} [with_term "balance (Node ?l ?c ?a ?r)"] *}

theorem ins_non_Leaf: "ins x t \<noteq> Leaf" by auto2
setup {* add_forward_prfstep_cond @{thm ins_non_Leaf} [with_term "ins ?x ?t"] *}

theorem cl_inv_ins: "cl_inv t \<Longrightarrow> if cl t = B then cl_inv (ins x t) else cl (ins x t) = R \<and> cl_inv' (ins x t)" by auto2

setup {* add_forward_prfstep_cond @{thm cl_inv_ins} [with_term "ins ?x ?t"] *}
theorem cl_inv_ins_l: "cl_inv t \<Longrightarrow> cl_inv (lsub (ins x t))" by auto2
theorem cl_inv_ins_r: "cl_inv t \<Longrightarrow> cl_inv (rsub (ins x t))" by auto2
setup {* del_prfstep_thm @{thm cl_inv_ins} *}
setup {* fold add_backward_prfstep [@{thm cl_inv_ins_l}, @{thm cl_inv_ins_r}] *}

theorem bd_inv_ins: "bd_inv t \<Longrightarrow> bd_inv (ins x t) \<and> black_depth t = black_depth (ins x t)" by auto2
setup {* add_forward_prfstep_cond (conj_left_th @{thm bd_inv_ins}) [with_term "ins ?x ?t"] *}

theorem present_ins: "present (ins x t) y = (x = y \<or> present t y)" by auto2
setup {* add_rewrite_rule @{thm present_ins} *}

fun makeBlack :: "'a pre_rbt \<Rightarrow> 'a pre_rbt" where
  "makeBlack Leaf = Leaf"
| "makeBlack (Node l c a r) = Node l B a r"
definition rbt_insert :: "nat \<Rightarrow> nat pre_rbt \<Rightarrow> nat pre_rbt" where
  "rbt_insert x t = makeBlack (ins x t)"

setup {* fold add_rewrite_rule (@{thms makeBlack.simps} @ [@{thm rbt_insert_def}]) *}

theorem present_makeBlack: "present (makeBlack t) y = present t y" by auto2
setup {* add_rewrite_rule @{thm present_makeBlack} *}

theorem cl_inv_insert: "cl_inv t \<Longrightarrow> cl_inv (rbt_insert x t)" by auto2
theorem bd_inv_insert: "bd_inv t \<Longrightarrow> bd_inv (rbt_insert x t)" by auto2
setup {* fold add_backward_prfstep [@{thm cl_inv_insert}, @{thm bd_inv_insert}] *}

theorem is_rbt_insert: "is_rbt t \<Longrightarrow> is_rbt (rbt_insert x t)" by auto2

theorem present_insert: "present (rbt_insert x t) y = (x = y \<or> present t y)" by auto2

(* Sortedness on trees. *)
fun base_tree :: "'a pre_rbt \<Rightarrow> 'a tree" where
  "base_tree Leaf = Tip"
| "base_tree (Node l c a r) = Lists_Ex.Node (base_tree l) a (base_tree r)"
setup {* fold add_rewrite_rule @{thms base_tree.simps} *}

theorem balanceR_as_rotate: "base_tree (balanceR t) =
  (if t = Leaf then Tip else
   if cl t = B then
     if cl (rsub t) = R then
       if cl (RL t) = R then rotateL (rotateR_at_R (base_tree t))
       else if cl (RR t) = R then rotateL (base_tree t)
       else base_tree t
     else base_tree t
   else base_tree t)"
  by (tactic {* auto2s_tac @{context} balanceR_scrpt *})

theorem balance_as_rotate: "base_tree (balance t) =
  (if t = Leaf then Tip else
   if cl t = B then
     if cl (lsub t) = R then
       if cl (LL t) = R then rotateR (base_tree t)
       else if cl (LR t) = R then rotateR (rotateL_at_L (base_tree t))
       else base_tree (balanceR t)
     else base_tree (balanceR t)
   else base_tree t)"
  by (tactic {* auto2s_tac @{context} balance_scrpt *})

setup {* fold add_rewrite_rule [@{thm balanceR_as_rotate}, @{thm balance_as_rotate}] *}

definition rbt_sorted :: "nat pre_rbt \<Rightarrow> bool" where
  "rbt_sorted t = tree_sorted (base_tree t)"
setup {* add_rewrite_rule_bidir @{thm rbt_sorted_def} *}

theorem rbt_present: "present t x = tree_present (base_tree t) x" by auto2
setup {* add_rewrite_rule_bidir @{thm rbt_present} *}

theorem balanceR_sorted: "rbt_sorted t \<Longrightarrow> rbt_sorted (balanceR t)"
  by (tactic {* auto2s_tac @{context} balanceR_scrpt *})
setup {* add_backward_prfstep @{thm balanceR_sorted} *}

theorem balance_sorted: "rbt_sorted t \<Longrightarrow> rbt_sorted (balance t)"
  by (tactic {* auto2s_tac @{context} balance_scrpt *})
setup {* add_backward_prfstep @{thm balance_sorted} *}

theorem rbt_sorted_def': "rbt_sorted (Node l c a r) =
  ((\<forall>x. present l x \<longrightarrow> x < a) \<and> (\<forall>x. present r x \<longrightarrow> a < x) \<and>
   rbt_sorted l \<and> rbt_sorted r)" by auto2
setup {* add_rewrite_rule @{thm rbt_sorted_def'} *}
setup {* del_prfstep_thm @{thm rbt_sorted_def} *}

theorem ins_sorted: "rbt_sorted t \<Longrightarrow> rbt_sorted (ins x t)"
  by (tactic {* auto2s_tac @{context}
    (CASE "t = Leaf" THEN CASE "x = nval t" THEN CASE "x < nval t") *})
setup {* add_backward_prfstep @{thm ins_sorted} *}

theorem insert_sorted: "rbt_sorted t \<Longrightarrow> rbt_sorted (rbt_insert x t)"
  by (tactic {* auto2s_tac @{context}
    (OBTAIN "rbt_sorted (ins x t) = rbt_sorted (rbt_insert x t)") *})

(* Search on sorted trees and its correctness. *)
fun rbt_search :: "nat pre_rbt \<Rightarrow> nat \<Rightarrow> bool" where
  "rbt_search Leaf x = False"
| "rbt_search (Node l c y r) x =
  (if x = y then True
   else if x < y then rbt_search l x
   else rbt_search r x)"
setup {* fold add_rewrite_rule @{thms rbt_search.simps} *}

theorem rbt_search_correct: "rbt_sorted t \<Longrightarrow> (rbt_search t x = present t x)" by auto2

end
