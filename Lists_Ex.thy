theory Lists_Ex
imports Auto2
begin

setup {* add_rew_const @{term "[]"} *}

(* Case checking. *)
setup {* add_gen_prfstep ("list_case_intro",
  [WithTerm @{term_pat "?x::?'a list"},
   Filter (unique_free_filter "x"),
   CreateCase ([@{term_pat "(?x::?'a list) = []"}], [])]) *}

setup {* add_forward_prfstep @{thm list.collapse} *}  (* Case checking after [] case. *)
setup {* add_resolve_prfstep @{thm list.distinct(2)} *}

(* Definition of append and rev. *)
setup {* fold add_simp_rule (@{thms List.append.simps} @ @{thms List.rev.simps}) *}

(* Induction. *)
theorem list_induct': "P [] \<Longrightarrow> (\<forall>l. P (tl l) \<longrightarrow> P l) \<Longrightarrow> P l" by (metis list.sel(3) list_nonempty_induct)
setup {* add_prfstep_induction @{thm list_induct'} *}

(* Some results on append and rev. *)
theorem app_simp1: "[x] @ y = x # y" by auto2
setup {* add_simp_rule @{thm app_simp1} *}

theorem rev_simp1: "rev [x] = [x]" by auto2
setup {* add_simp_rule @{thm rev_simp1} *}

theorem app_nil2: "x @ [] = x" by auto2
setup {* add_simp_rule @{thm app_nil2} *}

theorem app_assoc: "(x @ y) @ z = x @ y @ z"
  by (tactic {* auto2s_tac @{context} (CASE "x = []" THEN INDUCT ("x", [OnFact "x \<noteq> []"])) *})
setup {* add_rewrite_rule_bidir_cond @{thm app_assoc} (with_conds ["?x ~= []", "?y ~= []", "?z ~= []"]) *}

theorem rev_app: "rev (x @ y) = (rev y) @ (rev x)"
  by (tactic {* auto2s_tac @{context} (CASE "x = []" THEN INDUCT ("x", [OnFact "x \<noteq> []"])) *})
setup {* add_rewrite_rule_cond @{thm rev_app} (with_conds ["?x ~= []", "?y ~= []"]) *}

theorem rev_rev: "rev (rev x) = x" by auto2

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev []       ys = ys" |
  "itrev (x # xs) ys = itrev xs (x # ys)"
setup {* add_simp_rule @{thm itrev.simps(1)} #> add_rewrite_rule @{thm itrev.simps(2)} *}

lemma itrev_prop: "itrev x y = rev x @ y"
  by (tactic {* auto2s_tac @{context} (
    CASE "x = []" THEN INDUCT ("x", [OnFact "x \<noteq> []", Arbitrary "y"])) *})
setup {* add_simp_rule @{thm itrev_prop} *}

lemma itrev_eq_rev: "itrev x [] = rev x" by auto2

(* Present function on lists. *)
fun list_present :: "'a list \<Rightarrow> 'a \<Rightarrow> bool" where
  "list_present [] x = False"
| "list_present (y # ya) x = (if x = y then True else list_present ya x)"

setup {* fold add_rewrite_rule @{thms list_present.simps} *}

theorem list_present_app: "list_present (l1 @ l2) x = (list_present l1 x \<or> list_present l2 x)"
  by (tactic {* auto2s_tac @{context} (CASE "l1 = []" THEN INDUCT ("l1", [OnFact "l1 \<noteq> []"])) *})
setup {* add_rewrite_rule @{thm list_present_app} *}

setup {* add_rewrite_rule_back @{thm list_present_app} *}
theorem list_present_app':
  "(\<forall>x. list_present (l1 @ l2) x \<longrightarrow> C x) = (\<forall>x. (list_present l1 x \<or> list_present l2 x) \<longrightarrow> C x)" by auto2
setup {* del_prfstep "list_present_app@sym" *}

setup {* add_prfstep_conv ("list_present_app'",
  [WithTerm @{term_pat "\<forall>x. list_present (?l1.0 @ ?l2.0) x \<longrightarrow> ?C"}],
  (rewr_obj_eq @{thm list_present_app'})) *}

theorem list_present1: "list_present [x] y = (x = y)" by auto2
setup {* add_rewrite_rule @{thm list_present1} *}

theorem list_present1': "list_present [x] x" by auto2
setup {* add_prfstep_two_stage ("list_present1'",
  [WithFact @{term_pat "\<forall>x. list_present [?x::?'a] x \<longrightarrow> ?C"},
   GetFact (@{term_pat "list_present [?x::?'a] ?x"}, @{thm list_present1'})],
  @{thm forall_resolve}) *}

(* Sortedness on lists. *)
fun list_sorted :: "nat list \<Rightarrow> bool" where
  "list_sorted [] = True"
| "list_sorted (y # ys) = ((\<forall>x. list_present ys x \<longrightarrow> y < x) \<and> list_sorted ys)"

setup {* fold add_rewrite_rule @{thms list_sorted.simps} *}

theorem list_sorted1: "list_sorted [x]" by auto2
setup {* add_known_fact @{thm list_sorted1} *}

definition elt_less_list :: "nat \<Rightarrow> nat list \<Rightarrow> bool" (infix "<<" 60) where
  "elt_less_list y ys = (\<forall>x. list_present ys x \<longrightarrow> y < x)"
definition elt_greater_list :: "nat \<Rightarrow> nat list \<Rightarrow> bool" (infix ">>" 60) where
  "elt_greater_list y ys = (\<forall>x. list_present ys x \<longrightarrow> x < y)"
definition list_less :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" (infix "<<<" 60) where
  "list_less xs ys = (\<forall>x y. list_present xs x \<and> list_present ys y \<longrightarrow> x < y)"

setup {* fold add_rewrite_rule
  [@{thm list_less_def}, @{thm elt_less_list_def}, @{thm elt_greater_list_def}] *}

theorem list_less_trans: "y >> xs \<Longrightarrow> y << zs \<Longrightarrow> xs <<< zs" by auto2
setup {* add_forward_prfstep @{thm list_less_trans} *}

theorem list_less_simp1: "([x] <<< ys) = (x << ys)" by auto2
theorem list_less_simp2: "(ys <<< [x]) = (x >> ys)" by auto2
theorem list_less_empty: "[] <<< ys" by auto2
setup {* fold add_rewrite_rule [@{thm list_less_simp1}, @{thm list_less_simp2}] *}
setup {* add_known_fact @{thm list_less_empty} *}

theorem list_less_distrib1: "(x << (ys @ zs)) = (x << ys \<and> x << zs)" by auto2
theorem list_less_distrib2: "(xs @ ys) <<< zs = (xs <<< zs \<and> ys <<< zs)" by auto2
theorem list_less_distrib3: "xs <<< (ys @ zs) = (xs <<< ys \<and> xs <<< zs)" by auto2
setup {* fold add_rewrite_rule
  [@{thm list_less_distrib1}, @{thm list_less_distrib2}, @{thm list_less_distrib3}] *}

theorem list_less_distrib4: "(x # ys) <<< zs = (x << zs \<and> ys <<< zs)"
  by (tactic {* auto2s_tac @{context} (OBTAIN "x # ys = [x] @ ys") *})
setup {* add_rewrite_rule @{thm list_less_distrib4} *}

setup {* del_prfstep_thm @{thm list_less_def} *}

theorem sorted_dom': "list_sorted (x # xs) = ((x << xs) \<and> list_sorted xs)" by auto2
setup {* add_rewrite_rule @{thm sorted_dom'} *}

theorem sorted_dom: "list_sorted (xs @ ys) = (xs <<< ys \<and> list_sorted xs \<and> list_sorted ys)"
  by (tactic {* auto2s_tac @{context} (CASE "xs = []" THEN INDUCT ("xs", [OnFact "xs \<noteq> []"])) *})
setup {* add_rewrite_rule_cond @{thm sorted_dom} [with_cond "?xs \<noteq> ?xs1 @ ?xs2"] *}

theorem sorted_dom2: "list_sorted (xs @ [y]) = ((y >> xs) \<and> list_sorted xs)" by auto2

(* Definition of trees. *)
datatype 'a tree =
    Tip
  | Node (lsub: "'a tree") (nval: 'a) (rsub: "'a tree")

setup {* add_rew_const @{term "Tip"} *}

setup {* add_gen_prfstep ("tree_case_intro",
  [WithTerm @{term_pat "?t::?'a tree"},
   Filter (unique_free_filter "t"),
   CreateCase ([@{term_pat "(?t::?'a tree) = Tip"}], [])]) *}

setup {* add_forward_prfstep @{thm tree.collapse} *}  (* Case checking after Tip case. *)
setup {* add_resolve_prfstep @{thm tree.distinct(2)} *}

theorem if_not_Tip: "(if Node l v r = Tip then a else b) = b" by simp
setup {* add_simp_rule @{thm if_not_Tip} *}

(* Induction on trees. *)
theorem tree_induct': "P Tip \<Longrightarrow> (\<forall>t. P (lsub t) \<and> P (rsub t) \<longrightarrow> P t) \<Longrightarrow> P t"
  apply (induction t) apply blast by (metis tree.sel(1) tree.sel(3))
setup {* add_prfstep_induction @{thm tree_induct'} *}

(* mirror function. *)
fun mirror :: "'a tree \<Rightarrow> 'a tree" where
  "mirror Tip = Tip" |
  "mirror (Node l a r) = Node (mirror r) a (mirror l)"

setup {* fold add_rewrite_rule @{thms mirror.simps} *}

lemma "mirror (mirror (t::nat tree)) = t" by auto2

(* Inorder traversal, and present function on trees. *)
fun in_traverse :: "'a tree \<Rightarrow> 'a list" where
  "in_traverse Tip = []"
| "in_traverse (Node l a r) = (in_traverse l) @ [a] @ (in_traverse r)"

fun tree_present :: "nat tree \<Rightarrow> nat \<Rightarrow> bool" where
  "tree_present Tip x = False"
| "tree_present (Node l y r) x = (tree_present l x \<or> x = y \<or> tree_present r x)"

setup {* fold add_rewrite_rule (@{thms in_traverse.simps} @ @{thms tree_present.simps}) *}

theorem inorder_prop: "list_present (in_traverse t) x = tree_present t x" by auto2
theorem inorder_prop': "(\<forall>x. list_present (in_traverse t) x \<longrightarrow> C x) = (\<forall>x. tree_present t x \<longrightarrow> C x)"
  by (simp add: inorder_prop)
setup {* add_prfstep_conv ("inorder_prop'",
  [WithTerm @{term_pat "\<forall>x. list_present (in_traverse ?t) x \<longrightarrow> ?C"}],
  (rewr_obj_eq @{thm inorder_prop'})) *}

(* Sortedness on trees. *)
fun tree_sorted :: "nat tree \<Rightarrow> bool" where
  "tree_sorted Tip = True"
| "tree_sorted (Node l a r) = ((\<forall>x. tree_present l x \<longrightarrow> x < a) \<and> (\<forall>x. tree_present r x \<longrightarrow> a < x)
                              \<and> tree_sorted l \<and> tree_sorted r)"

setup {* fold add_rewrite_rule @{thms tree_sorted.simps} *}

theorem inorder_sorted: "list_sorted (in_traverse t) = tree_sorted t" by auto2
setup {* add_rewrite_rule_bidir @{thm inorder_sorted} *}

(* Rotate function. *)
abbreviation LL :: "'a tree \<Rightarrow> 'a tree" where "LL t \<equiv> lsub (lsub t)"
abbreviation LR :: "'a tree \<Rightarrow> 'a tree" where "LR t \<equiv> rsub (lsub t)"
abbreviation RL :: "'a tree \<Rightarrow> 'a tree" where "RL t \<equiv> lsub (rsub t)"
abbreviation RR :: "'a tree \<Rightarrow> 'a tree" where "RR t \<equiv> rsub (rsub t)"
abbreviation LV :: "'a tree \<Rightarrow> 'a" where "LV t \<equiv> nval (lsub t)"
abbreviation RV :: "'a tree \<Rightarrow> 'a" where "RV t \<equiv> nval (rsub t)"

definition rotateL :: "'a tree \<Rightarrow> 'a tree" where
  "rotateL t = (if t = Tip then t else if rsub t = Tip then t
                else Node (Node (lsub t) (nval t) (RL t)) (RV t) (RR t))"
definition rotateR :: "'a tree \<Rightarrow> 'a tree" where
  "rotateR t = (if t = Tip then t else if lsub t = Tip then t
                else Node (LL t) (LV t) (Node (LR t) (nval t) (rsub t)))"

setup {*
  add_rewrite_rule_cond @{thm rotateL_def} (with_conds ["?t \<noteq> lsub ?s", "?t \<noteq> rsub ?s"]) #>
  add_rewrite_rule_cond @{thm rotateR_def} (with_conds ["?t \<noteq> lsub ?s", "?t \<noteq> rsub ?s"]) *}

theorem rotateL_in_trav: "in_traverse (rotateL t) = in_traverse t" by auto2
theorem rotateR_in_trav: "in_traverse (rotateR t) = in_traverse t" by auto2
setup {* fold add_rewrite_rule [@{thm rotateL_in_trav}, @{thm rotateR_in_trav}] *}

theorem rotateL_sorted: "tree_sorted (rotateL t) = tree_sorted t" by auto2
theorem rotateR_sorted: "tree_sorted (rotateR t) = tree_sorted t" by auto2

(* Search on sorted trees. *)
fun tree_search :: "nat tree \<Rightarrow> nat \<Rightarrow> bool" where
  "tree_search Tip x = False"
| "tree_search (Node l y r) x =
  (if x = y then True
   else if x < y then tree_search l x
   else tree_search r x)"
setup {* fold add_rewrite_rule @{thms tree_search.simps} *}

theorem tree_search_correct: "tree_sorted t \<Longrightarrow> (tree_search t x = tree_present t x)" by auto2

(* Insertion on trees. *)
fun tree_insert :: "nat \<Rightarrow> nat tree \<Rightarrow> nat tree" where
  "tree_insert x Tip = Node Tip x Tip"
| "tree_insert x (Node l y r) =
    (if x = y then Node l y r
     else if x < y then Node (tree_insert x l) y r
     else Node l y (tree_insert x r))"
setup {* fold add_rewrite_rule @{thms tree_insert.simps} *}

theorem insert_present: "tree_present (tree_insert x t) y = (x = y \<or> tree_present t y)" by auto2
setup {* add_rewrite_rule @{thm insert_present} *}

theorem insert_sorted: "tree_sorted t \<Longrightarrow> tree_sorted (tree_insert x t)"
  by (tactic {* auto2s_tac @{context}
    (CASE "t = Tip" THEN CASE "x = nval t" THEN CASE "x < nval t") *})

(* More on rotation functions, to be used in rbt. *)
theorem rotateL_def': "rotateL (Node a x (Node b y c)) = Node (Node a x b) y c" by (simp add: rotateL_def)
theorem rotateR_def': "rotateR (Node (Node a x b) y c) = Node a x (Node b y c)" by (simp add: rotateR_def)

fun rotateL_at_L :: "'a tree \<Rightarrow> 'a tree" where
  "rotateL_at_L Tip = Tip"
| "rotateL_at_L (Node l a r) = Node (rotateL l) a r"

fun rotateR_at_R :: "'a tree \<Rightarrow> 'a tree" where
  "rotateR_at_R Tip = Tip"
| "rotateR_at_R (Node l a r) = Node l a (rotateR r)"

setup {* fold add_rewrite_rule
  ([@{thm rotateL_def'}, @{thm rotateR_def'}] @ @{thms rotateL_at_L.simps} @ @{thms rotateR_at_R.simps}) *}

theorem rotateL_at_L_def': "rotateL_at_L (Node (Node a z (Node b y c)) x d) = Node (Node (Node a z b) y c) x d" by (simp add: rotateL_def)
theorem rotateR_at_R_def': "rotateR_at_R (Node a x (Node (Node b y c) z d)) = Node a x (Node b y (Node c z d))" by (simp add: rotateR_def)
setup {* fold add_rewrite_rule [@{thm rotateL_at_L_def'}, @{thm rotateR_at_R_def'}] *}

theorem rotateL_at_L_sorted: "tree_sorted (rotateL_at_L t) = tree_sorted t" by auto2
theorem rotateR_at_R_sorted: "tree_sorted (rotateR_at_R t) = tree_sorted t" by auto2

setup {* fold add_rewrite_rule
  [@{thm rotateL_sorted}, @{thm rotateR_sorted}, @{thm rotateL_at_L_sorted}, @{thm rotateR_at_R_sorted}] *}

end
