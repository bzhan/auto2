theory Imp_Ex_Binary_Trees
imports Imp_Thms Lists_Ex
begin

section {* Definition of Binary trees *}

setup {* Sign.add_const_constraint (@{const_name Ref}, SOME @{typ "nat \<Rightarrow> 'a\<Colon>type ref"}) *}
datatype 'a node = Empty | Node (lnxt: "'a node ref") (val: 'a) (rnxt: "'a node ref")

setup {* add_forward_prfstep (equiv_forward_th @{thm node.simps(1)}) *}
setup {* add_rew_const @{term "Empty"} *}
setup {* add_resolve_prfstep @{thm node.distinct(2)} *}
setup {* add_forward_prfstep_cond @{thm node.collapse} [with_cond "?node \<noteq> Node ?lp ?v ?rp"] *}
setup {* fold add_rewrite_rule @{thms node.case} *}

primrec
  node_encode :: "'a\<Colon>countable node \<Rightarrow> nat"
where
  "node_encode Empty = 0"
| "node_encode (Node x l r) = Suc (to_nat (x, l, r))"

instance node :: (countable) countable
proof (rule countable_classI [of "node_encode"])
  fix x y :: "'a\<Colon>countable node"
  show "node_encode x = node_encode y \<Longrightarrow> x = y"
  by (induct x, auto, induct y, auto, induct y, auto)
qed

instance node :: (heap) heap ..

subsection {* Definition and properties of the predicates *}

inductive tree_ofR :: "heap \<Rightarrow> ('a::heap) node ref \<Rightarrow> 'a tree \<Rightarrow> bool" where
  "Ref.get h p = Empty \<Longrightarrow> tree_ofR h p Tip"
| "Ref.get h p = Node lp v rp \<Longrightarrow> tree_ofR h lp lt \<and> tree_ofR h rp rt \<Longrightarrow>
   tree_ofR h p (tree.Node lt v rt)"
setup {* add_forward_prfstep @{thm tree_ofR.intros(1)} *}
setup {* add_backward2_prfstep @{thm tree_ofR.intros(2)} *}
setup {* add_prfstep_prop_induction @{thm tree_ofR.induct} *}

theorem tree_ofR_non_Tip: "tree_ofR h p t \<Longrightarrow> Ref.get h p = Node lp n rp \<Longrightarrow> t \<noteq> Tip" by auto2
setup {* add_forward_prfstep @{thm tree_ofR_non_Tip} *}
theorem tree_ofR_non_Empty: "tree_ofR h p (tree.Node l v r) \<Longrightarrow> Ref.get h p \<noteq> Empty" 
  by (tactic {* auto2s_tac @{context} (PROP_INDUCT ("tree_ofR h p (tree.Node l v r)", [])) *})
setup {* add_forward_prfstep @{thm tree_ofR_non_Empty} *}

theorem tree_ofR_Node: "Ref.get h p = Node lp v' rp \<Longrightarrow> tree_ofR h p (tree.Node l v r) \<Longrightarrow>
  v = v' \<and> tree_ofR h lp l \<and> tree_ofR h rp r"
  by (tactic {* auto2s_tac @{context} (PROP_INDUCT ("tree_ofR h p (tree.Node l v r)", [])) *})
setup {* add_forward_prfstep @{thm tree_ofR_Node} *}

theorem tree_ofR_Node': "Ref.get h p = Node lp v rp \<Longrightarrow> tree_ofR h lp lt \<Longrightarrow>
  \<forall>rt. tree_ofR h rp rt \<longrightarrow> tree_ofR h p (tree.Node lt v rt)" by auto2
setup {* add_forward_prfstep @{thm tree_ofR_Node'} *}

inductive refs_ofR :: "heap \<Rightarrow> ('a::heap) node ref \<Rightarrow> 'a node ref set \<Rightarrow> bool" where
  "Ref.get h p = Empty \<Longrightarrow> refs_ofR h p {p}"
| "Ref.get h p = Node lp v rp \<Longrightarrow> refs_ofR h lp lps \<and> refs_ofR h rp rps
  \<and> lps \<inter> rps = {} \<and> p \<notin> lps \<and> p \<notin> rps \<Longrightarrow> refs_ofR h p ({p} \<union> lps \<union> rps)"
setup {* add_known_fact @{thm refs_ofR.intros(1)} *}
setup {* add_backward2_prfstep @{thm refs_ofR.intros(2)} *}
setup {* add_prfstep_prop_induction @{thm refs_ofR.induct} *}

theorem refs_ofR_Empty: "Ref.get h p = Empty \<Longrightarrow> refs_ofR h p ps \<Longrightarrow> ps = {p}" by auto2
theorem refs_ofR_Node: "Ref.get h p = Node lp v rp \<Longrightarrow> refs_ofR h p ps \<Longrightarrow>
  \<exists>lps rps. refs_ofR h lp lps \<and> refs_ofR h rp rps \<and> lps \<inter> rps = {} \<and> p \<notin> lps \<and> p \<notin> rps \<and> ps = {p} \<union> lps \<union> rps" by auto2
setup {* fold add_forward_prfstep [@{thm refs_ofR_Empty}, @{thm refs_ofR_Node}] *}

theorem exists_tree_of: "refs_ofR h p ps \<Longrightarrow> \<exists>t. tree_ofR h p t" by auto2
setup {* add_resolve_prfstep @{thm exists_tree_of} *}

lemma refs_ofR_is_fun: "\<lbrakk> refs_ofR h p xt; refs_ofR h p yt \<rbrakk> \<Longrightarrow> xt = yt"
  by (tactic {* auto2s_tac @{context} (PROP_INDUCT ("refs_ofR h p xt", [Arbitrary "yt"])) *})
setup {* add_forward_prfstep_cond @{thm refs_ofR_is_fun} [with_cond "?xt \<noteq> ?yt"] *}

lemma tree_ofR_is_fun: "\<lbrakk> tree_ofR h p xt; tree_ofR h p yt \<rbrakk> \<Longrightarrow> xt = yt"
  by (tactic {* auto2s_tac @{context} (PROP_INDUCT ("tree_ofR h p xt", [Arbitrary "yt"])) *})
setup {* add_forward_prfstep_cond @{thm tree_ofR_is_fun} [with_cond "?xt \<noteq> ?yt"] *}

subsection {* Partial function version of predicates *}

definition proper_ref :: "heap \<Rightarrow> ('a::heap) node ref \<Rightarrow> bool" where
  "proper_ref h p = (\<exists>ps. refs_ofR h p ps \<and> present_on_set h ps)"
setup {* add_rewrite_rule @{thm proper_ref_def} *}
theorem proper_ref_empty: "Ref.present h p \<Longrightarrow> Ref.get h p = Empty \<Longrightarrow> proper_ref h p"
  by (tactic {* auto2s_tac @{context} (OBTAIN "refs_ofR h p {p}") *})
setup {* add_forward_prfstep @{thm proper_ref_empty} *}

theorem proper_ref_next1:
  "Ref.get h p = Node lp v rp \<Longrightarrow> proper_ref h p \<Longrightarrow> proper_ref h lp \<and> proper_ref h rp" by auto2
setup {* add_forward_prfstep @{thm proper_ref_next1} *}

theorem proper_ref_tree_of: "proper_ref h p \<Longrightarrow> \<exists>t. tree_ofR h p t" by auto2
setup {* add_resolve_prfstep @{thm proper_ref_tree_of} *}

definition tree_of :: "heap \<Rightarrow> ('a::heap) node ref \<Rightarrow> 'a tree" where
  "tree_of h p = (THE t. tree_ofR h p t)"
theorem tree_ofI: "tree_ofR h p t \<Longrightarrow> tree_of h p = t" by (metis the1_equality tree_of_def tree_ofR_is_fun)
theorem tree_ofE: "proper_ref h p \<Longrightarrow> tree_ofR h p (tree_of h p)" using proper_ref_tree_of tree_ofI by blast
setup {* add_forward_prfstep @{thm tree_ofI} #> add_forward_prfstep_cond @{thm tree_ofE} [with_term "tree_of ?h ?p"] *}

theorem tree_of_Empty: "Ref.get h r = Empty \<Longrightarrow> tree_of h r = Tip" by auto2
theorem tree_of_Empty': "proper_ref h r \<Longrightarrow> tree_of h r = Tip \<Longrightarrow> Ref.get h r = Empty" by auto2
theorem tree_of_Node: "Ref.get h p = Node lp v rp \<Longrightarrow> proper_ref h p \<Longrightarrow>
  tree_of h p = tree.Node (tree_of h lp) v (tree_of h rp)" by auto2
theorem tree_of_Node': "tree_of h p = tree.Node l v r \<Longrightarrow> Ref.get h p \<noteq> Empty" by auto2
setup {* add_rewrite_rule @{thm tree_of_Empty} *}
setup {* fold add_forward_prfstep [@{thm tree_of_Empty'}, @{thm tree_of_Node}, @{thm tree_of_Node'}] *}

definition refs_of :: "heap \<Rightarrow> ('a::heap) node ref \<Rightarrow> 'a node ref set" where
  "refs_of h p = (THE ps. refs_ofR h p ps)"
theorem refs_ofI: "refs_ofR h p ps \<Longrightarrow> present_on_set h ps \<Longrightarrow> proper_ref h p \<and> refs_of h p = ps"
  by (metis proper_ref_def refs_of_def refs_ofR_is_fun the1_equality)
theorem refs_ofE: "proper_ref h p \<Longrightarrow> refs_ofR h p (refs_of h p)" using proper_ref_def refs_ofI by blast
setup {* add_forward_prfstep @{thm refs_ofI} #> add_forward_prfstep_cond @{thm refs_ofE} [with_term "refs_of ?h ?p"] *}

theorem refs_of_Empty: "Ref.present h p \<Longrightarrow> Ref.get h p = Empty \<Longrightarrow> refs_of h p = {p}" by auto2
setup {* add_forward_prfstep @{thm refs_of_Empty} *}

theorem proper_ref_next1':
  "Ref.get h p = Node lp v rp \<Longrightarrow> proper_ref h p \<Longrightarrow> refs_of h lp \<inter> refs_of h rp = {} \<and>
   p \<notin> refs_of h lp \<and> p \<notin> refs_of h rp \<and> refs_of h p = {p} \<union> refs_of h lp \<union> refs_of h rp" by auto2
setup {* add_forward_prfstep @{thm proper_ref_next1'} *}

theorem proper_ref_next2:
  "Ref.get h p = Node lp v rp \<Longrightarrow> Ref.present h p \<and> proper_ref h lp \<and> proper_ref h rp \<and> p \<notin> refs_of h lp \<and>
   p \<notin> refs_of h rp \<and> refs_of h lp \<inter> refs_of h rp = {} \<Longrightarrow> proper_ref h p"
  by (tactic {* auto2s_tac @{context} (OBTAIN "refs_ofR h p ({p} \<union> refs_of h lp \<union> refs_of h rp)") *})
setup {* add_backward2_prfstep @{thm proper_ref_next2} *}

theorem proper_ref_present: "proper_ref h p \<Longrightarrow> Ref.present h p \<and> present_on_set h (refs_of h p)"
  by (tactic {* auto2s_tac @{context} (CASE "Ref.get h p = Empty") *})
setup {* add_forward_prfstep @{thm proper_ref_present} *}

setup {* fold del_prfstep_thm [@{thm tree_ofR.intros(1)}, @{thm refs_ofR.intros(1)},
  @{thm proper_ref_def}, @{thm tree_ofE}, @{thm refs_ofE}] *}

subsection {* Interaction of partial functions with heap transitions *}

lemma refs_of_set_ref: "p \<notin> refs_of h q \<Longrightarrow> proper_ref h q \<Longrightarrow>
  proper_ref (Ref.set p v h) q \<and> refs_of (Ref.set p v h) q = refs_of h q"
  by (tactic {* auto2s_tac @{context} (TREE_INDUCT_NEWVAR ("tree_of h q", "ts", ["q"])) *})
setup {* add_forward_prfstep_cond @{thm refs_of_set_ref} [with_term "Ref.set ?p ?v ?h"] *}

lemma tree_of_set_ref: "p \<notin> refs_of h q \<Longrightarrow> proper_ref h q \<Longrightarrow> tree_of (Ref.set p v h) q = tree_of h q"
  by (tactic {* auto2s_tac @{context} (TREE_INDUCT_NEWVAR ("tree_of h q", "ts", ["q"])) *})
setup {* add_rewrite_rule @{thm tree_of_set_ref} *}

lemma refs_of_set_next_ref: "proper_ref h lp \<Longrightarrow> proper_ref h rp \<Longrightarrow>
  p \<notin> refs_of h lp \<Longrightarrow> p \<notin> refs_of h rp \<Longrightarrow> refs_of h lp \<inter> refs_of h rp = {} \<Longrightarrow>
  Ref.present h p \<Longrightarrow> proper_ref (Ref.set p (Node lp v rp) h) p \<and>
  refs_of (Ref.set p (Node lp v rp) h) p = {p} \<union> refs_of h lp \<union> refs_of h rp \<and>
  tree_of (Ref.set p (Node lp v rp) h) p = tree.Node (tree_of h lp) v (tree_of h rp)" by auto2
setup {* add_forward_prfstep_cond @{thm refs_of_set_next_ref} [with_term "Ref.set ?p (Node ?lp ?v ?rp) ?h"] *}

lemma refs_of_set_get: "p \<notin> refs_of h q \<Longrightarrow> proper_ref h q \<Longrightarrow> Ref.present h p \<Longrightarrow>
  proper_ref (Ref.set p (Ref.get h q) h) p \<and> tree_of (Ref.set p (Ref.get h q) h) p = tree_of h q \<and>
  refs_of (Ref.set p (Ref.get h q) h) p \<subseteq> {p} \<union> refs_of h q"
  by (tactic {* auto2s_tac @{context} (CASE "Ref.get h q = Empty") *})
setup {* add_forward_prfstep_cond @{thm refs_of_set_get} [with_term "Ref.set ?p (Ref.get ?h ?q) ?h"] *}

subsection {* Invariance of partial functions *}

lemma eq_on_set_head: "eq_on_set h h' (refs_of h r) \<Longrightarrow> proper_ref h r \<Longrightarrow> Ref.get h r = Ref.get h' r"
  by (tactic {* auto2s_tac @{context} (CASE "Ref.get h r = Empty") *})

lemma eq_on_set_next_refs: "Ref.get h r = Node lp v rp \<Longrightarrow> eq_on_set h h' (refs_of h r) \<Longrightarrow> proper_ref h r \<Longrightarrow>
  eq_on_set h h' (refs_of h lp) \<and> eq_on_set h h' (refs_of h rp)" by auto2
setup {* fold add_forward_prfstep [@{thm eq_on_set_head}, @{thm eq_on_set_next_refs}] *}

lemma refs_of_invariant: "proper_ref h r \<Longrightarrow> eq_on_set h h' (refs_of h r) \<Longrightarrow>
  proper_ref h' r \<and> refs_of h r = refs_of h' r"
  by (tactic {* auto2s_tac @{context} (TREE_INDUCT_NEWVAR ("tree_of h r", "ts", ["r"])) *})
setup {* add_forward_prfstep @{thm refs_of_invariant} *}

lemma tree_of_invariant: "proper_ref h r \<Longrightarrow> eq_on_set h h' (refs_of h r) \<Longrightarrow> tree_of h r = tree_of h' r"
  by (tactic {* auto2s_tac @{context} (TREE_INDUCT_NEWVAR ("tree_of h r", "ts", ["r"])) *})
setup {* add_forward_prfstep @{thm tree_of_invariant} *}

lemma effect_update_ref:
  "effect (p := q) h h' v \<Longrightarrow> Ref.get h p = Node lp v rp \<Longrightarrow> proper_ref h p \<Longrightarrow>
   eq_on_set h h' (refs_of h lp) \<and> eq_on_set h h' (refs_of h rp)" by auto2
setup {* add_forward_prfstep @{thm effect_update_ref} *}

lemma effect_ref_tree:
  "effect (ref (Node lp v rp)) h h' r \<Longrightarrow> proper_ref h lp \<Longrightarrow> proper_ref h rp \<Longrightarrow>
  refs_of h lp \<inter> refs_of h rp = {} \<Longrightarrow> proper_ref h' r \<and>
  tree_of h' r = tree.Node (tree_of h lp) v (tree_of h rp) \<and>
  refs_of h' r = {r} \<union> refs_of h lp \<union> refs_of h rp" by auto2
setup {* add_forward_prfstep @{thm effect_ref_tree} *}

section {* make_btree, traverse, and proof of correctness *}

primrec make_btree :: "'a::heap tree \<Rightarrow> 'a node ref Heap" where
  "make_btree Tip = do { p \<leftarrow> ref Empty; return p }"
| "make_btree (tree.Node lt v rt) =
  do { lp \<leftarrow> make_btree lt;
       rp \<leftarrow> make_btree rt;
       p \<leftarrow> ref (Node lp v rp);
       return p
     }"
setup {* fold add_rewrite_rule @{thms make_btree.simps} *}

lemma make_btree_unchanged:
  "effect (make_btree t) h h' r \<Longrightarrow> Ref.present h r' \<Longrightarrow> Ref.present h' r' \<and> Ref.get h r' = Ref.get h' r'"
  by (tactic {* auto2s_tac @{context} (TREE_INDUCT ("t", ["h", "h'", "r"])) *})
setup {* add_forward_prfstep @{thm make_btree_unchanged} *}

lemma make_btree_unchanged_set:
  "effect (make_btree t) h h' r \<Longrightarrow> present_on_set h rs \<Longrightarrow> eq_on_set h h' rs" by auto2
lemma make_btree_unchanged_set':
  "effect (make_btree t) h h' r \<Longrightarrow> not_present_on_set h' rs \<Longrightarrow> not_present_on_set h rs" by auto2
setup {* fold add_forward_prfstep [@{thm make_btree_unchanged_set}, @{thm make_btree_unchanged_set'}] *}
  
lemma make_btree:
  "effect (make_btree t) h h' r \<Longrightarrow> proper_ref h' r \<and> tree_of h' r = t \<and> not_present_on_set h (refs_of h' r)"
  by (tactic {* auto2s_tac @{context} (TREE_INDUCT ("t", ["h", "h'", "r"])) *})

partial_function (heap) traverse :: "'a::heap node ref \<Rightarrow> 'a tree Heap" where
  "traverse p = do { t \<leftarrow> !p;
    case t of Empty \<Rightarrow> return Tip
     | Node lp v rp \<Rightarrow> do { lt \<leftarrow> traverse lp;
                            rt \<leftarrow> traverse rp;
                            return (tree.Node lt v rt) } }"
setup {* add_rewrite_rule_cond @{thm traverse.simps} [with_filt (size1_filter "p")] *}

lemma traverse: "proper_ref h p \<Longrightarrow> tree_of h p = t \<Longrightarrow> effect (traverse p) h h t"
  by (tactic {* auto2s_tac @{context} (TREE_INDUCT ("t", ["p"])) *})

setup {* fold add_forward_prfstep [@{thm make_btree}, @{thm traverse}] *}
lemma traverse_make_btree: "effect (make_btree t \<guillemotright>= traverse) h h' r \<Longrightarrow> r = t" by auto2
setup {* del_prfstep_thm @{thm traverse} *}

section {* Insertion on binary trees *}

partial_function (heap) insert :: "'a::{heap,ord} \<Rightarrow> 'a node ref \<Rightarrow> unit Heap" where
  "insert x p = do { t \<leftarrow> !p;
    case t of Empty \<Rightarrow> do { lp \<leftarrow> ref Empty; rp \<leftarrow> ref Empty; p := Node lp x rp }
     | Node lp y rp \<Rightarrow> if x = y then return ()
                       else if x < y then insert x lp
                       else insert x rp } "
setup {* add_rewrite_rule_cond @{thm insert.simps} [with_filt (size1_filter "p")] *}

lemma insert_unchanged:
  "effect (insert x p) h h' r' \<Longrightarrow> proper_ref h p \<Longrightarrow> unchanged_outer h h' (refs_of h p)"
  by (tactic {* auto2s_tac @{context} (TREE_INDUCT_NEWVAR ("tree_of h p", "t", ["p", "h", "h'"])) *})
setup {* add_forward_prfstep @{thm insert_unchanged} *}

lemma insert_local: "effect (insert x p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow>
  proper_ref h' p \<and> refs_of_extension h (refs_of h p) (refs_of h' p)"
  by (tactic {* auto2s_tac @{context} (TREE_INDUCT_NEWVAR ("tree_of h p", "t", ["p", "h", "h'"])) *})
setup {* add_forward_prfstep @{thm insert_local} *}

theorem insert_correct:
  "effect (insert x p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> tree_of h' p = tree_insert x (tree_of h p)"
  by (tactic {* auto2s_tac @{context} (TREE_INDUCT_NEWVAR ("tree_of h p", "t", ["p", "h", "h'"])) *})
setup {* add_forward_prfstep @{thm insert_correct} #> del_prfstep_thm @{thm insert.simps} *}

theorem imp_insert_present:
  "effect (insert x p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> tree_set (tree_of h' p) = {x} \<union> tree_set (tree_of h p)" by auto2

theorem imp_insert_sorted:
  "effect (insert x p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> tree_sorted (tree_of h p) \<Longrightarrow> tree_sorted (tree_of h' p)" by auto2

section {* Deletion on binary trees *}

partial_function (heap) delete_min :: "'a::{heap,ord} node ref \<Rightarrow> 'a Heap" where
  "delete_min p = do { t \<leftarrow> !p;
    case t of Empty \<Rightarrow> raise ''delete_min: empty_node''
     | Node lp v rp \<Rightarrow> do { lt \<leftarrow> !lp; if lt = Empty then do { rt \<leftarrow> !rp; p := rt; return v }
                                       else do { w \<leftarrow> delete_min lp; return w } } }"
setup {* add_rewrite_rule_cond @{thm delete_min.simps} [with_filt (size1_filter "p")] *}

lemma delete_min_non_empty: "effect (delete_min p) h h' r \<Longrightarrow> Ref.get h p \<noteq> Empty" by auto2
setup {* add_forward_prfstep @{thm delete_min_non_empty} *}

lemma delete_min_unchanged:
  "effect (delete_min p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> unchanged_outer h h' (refs_of h p)"
  by (tactic {* auto2s_tac @{context} (TREE_INDUCT_NEWVAR ("tree_of h p", "t", ["p", "h", "h'", "r"])) *})
setup {* add_forward_prfstep @{thm delete_min_unchanged} *}

lemma delete_min_local: "effect (delete_min p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow>
  proper_ref h' p \<and> refs_of_extension h (refs_of h p) (refs_of h' p)"
  by (tactic {* auto2s_tac @{context} (TREE_INDUCT_NEWVAR ("tree_of h p", "t", ["p", "h", "h'", "r"])) *})
setup {* add_forward_prfstep @{thm delete_min_local} *}

lemma delete_min_correct:
  "effect (delete_min p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow>
   tree_of h' p = delete_min_tree (tree_of h p) \<and> r = min_tree (tree_of h p)"
  by (tactic {* auto2s_tac @{context} (TREE_INDUCT_NEWVAR ("tree_of h p", "t", ["p", "h", "h'", "r"])) *})
setup {* add_forward_prfstep @{thm delete_min_correct} *}

lemma delete_min_succeed: "proper_ref h p \<Longrightarrow> Ref.get h p \<noteq> Empty \<Longrightarrow> success (delete_min p) h"
  by (tactic {* auto2s_tac @{context} (TREE_INDUCT_NEWVAR ("tree_of h p", "t", ["p", "h"])) *})
setup {* add_backward2_prfstep @{thm delete_min_succeed} *}
setup {* del_prfstep_thm @{thm delete_min.simps} *}

partial_function (heap) delete :: "'a::{heap,ord} node ref \<Rightarrow> unit Heap" where
  "delete p = do { t \<leftarrow> !p;
    case t of Empty \<Rightarrow> raise ''delete: empty node''
     | Node lp v rp \<Rightarrow> do { lt \<leftarrow> !lp; rt \<leftarrow> !rp;
                            if lt = Empty then p := rt
                            else if rt = Empty then p := lt
                            else do { w \<leftarrow> delete_min rp; p := Node lp w rp } } }"
setup {* add_rewrite_rule @{thm delete.simps} *}

lemma delete_succeed: "proper_ref h p \<Longrightarrow> Ref.get h p \<noteq> Empty \<Longrightarrow> success (delete p) h" by auto2

lemma delete_correct:
  "effect (delete p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> Ref.get h p \<noteq> Empty \<Longrightarrow>
   proper_ref h' p \<and> tree_of h' p = delete_elt_tree (tree_of h p)" by auto2
setup {* add_forward_prfstep @{thm delete_correct} #> del_prfstep_thm @{thm delete.simps} *}

theorem delete_data_str:
  "effect (delete p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> Ref.get h p \<noteq> Empty \<Longrightarrow> tree_sorted (tree_of h p) \<Longrightarrow>
   tree_set (tree_of h' p) = tree_set (tree_of h p) - {val (Ref.get h p)} \<and> tree_sorted (tree_of h' p)" by auto2

end
