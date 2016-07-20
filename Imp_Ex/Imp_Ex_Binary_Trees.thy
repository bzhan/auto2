(* Imperative binary search trees. *)

theory Imp_Ex_Binary_Trees
imports Imp_Thms "../Lists_Ex"
begin

section {* Definition of Binary trees *}

setup {* Sign.add_const_constraint (@{const_name Ref}, SOME @{typ "nat \<Rightarrow> 'a::type ref"}) *}
datatype 'a node = Empty | Node (lnxt: "'a node ref") (val: 'a) (rnxt: "'a node ref")

setup {* add_forward_prfstep (equiv_forward_th @{thm node.simps(1)}) *}
setup {* add_resolve_prfstep @{thm node.distinct(2)} *}
setup {* add_forward_prfstep_cond @{thm node.collapse} [with_cond "?node \<noteq> Node ?lp ?v ?rp"] *}
setup {* fold add_rewrite_rule @{thms node.case} *}

primrec
  node_encode :: "'a::countable node \<Rightarrow> nat"
where
  "node_encode Empty = 0"
| "node_encode (Node x l r) = Suc (to_nat (x, l, r))"

instance node :: (countable) countable
proof (rule countable_classI [of "node_encode"])
  fix x y :: "'a::countable node"
  show "node_encode x = node_encode y \<Longrightarrow> x = y"
  by (induct x, auto, induct y, auto, induct y, auto)
qed

instance node :: (heap) heap ..

subsection {* Definition and properties of the predicates *}

inductive tree_ofR :: "heap \<Rightarrow> ('a::heap) node ref \<Rightarrow> 'a tree \<Rightarrow> bool" where
  "Ref.get h p = Empty \<Longrightarrow> tree_ofR h p Tip"
| "Ref.get h p = Node lp v rp \<Longrightarrow> tree_ofR h lp lt \<Longrightarrow> tree_ofR h rp rt \<Longrightarrow>
   tree_ofR h p (tree.Node lt v rt)"
setup {* add_forward_prfstep @{thm tree_ofR.intros(1)} *}
setup {* add_backward2_prfstep @{thm tree_ofR.intros(2)} *}
setup {* add_prfstep_prop_induction @{thm tree_ofR.induct} *}

theorem tree_ofR_non_Tip [forward]: "tree_ofR h p t \<Longrightarrow> Ref.get h p = Node lp n rp \<Longrightarrow> t \<noteq> Tip" by auto2
theorem tree_ofR_non_Empty [forward]: "tree_ofR h p (tree.Node l v r) \<Longrightarrow> Ref.get h p \<noteq> Empty" 
  by (tactic {* auto2s_tac @{context} (PROP_INDUCT ("tree_ofR h p (tree.Node l v r)", [])) *})

theorem tree_ofR_Node [forward]: "Ref.get h p = Node lp v' rp \<Longrightarrow> tree_ofR h p (tree.Node l v r) \<Longrightarrow>
  v = v' \<and> tree_ofR h lp l \<and> tree_ofR h rp r"
  by (tactic {* auto2s_tac @{context} (PROP_INDUCT ("tree_ofR h p (tree.Node l v r)", [])) *})

theorem tree_ofR_Node' [forward]: "Ref.get h p = Node lp v rp \<Longrightarrow> tree_ofR h lp lt \<Longrightarrow>
  \<forall>rt. tree_ofR h rp rt \<longrightarrow> tree_ofR h p (tree.Node lt v rt)" by auto2

inductive refs_ofR :: "heap \<Rightarrow> ('a::heap) node ref \<Rightarrow> 'a node ref set \<Rightarrow> bool" where
  "Ref.get h p = Empty \<Longrightarrow> refs_ofR h p {p}"
| "Ref.get h p = Node lp v rp \<Longrightarrow> refs_ofR h lp lps \<Longrightarrow> refs_ofR h rp rps \<Longrightarrow>
   lps \<inter> rps = {} \<Longrightarrow> p \<notin> lps \<Longrightarrow> p \<notin> rps \<Longrightarrow> refs_ofR h p ({p} \<union> lps \<union> rps)"
setup {* add_resolve_prfstep @{thm refs_ofR.intros(1)} *}
setup {* add_backward2_prfstep @{thm refs_ofR.intros(2)} *}
setup {* add_prfstep_prop_induction @{thm refs_ofR.induct} *}

theorem refs_ofR_Empty [forward]: "Ref.get h p = Empty \<Longrightarrow> refs_ofR h p ps \<Longrightarrow> ps = {p}" by auto2
theorem refs_ofR_Node [forward]: "Ref.get h p = Node lp v rp \<Longrightarrow> refs_ofR h p ps \<Longrightarrow>
  \<exists>lps rps. refs_ofR h lp lps \<and> refs_ofR h rp rps \<and> lps \<inter> rps = {} \<and> p \<notin> lps \<and> p \<notin> rps \<and> ps = {p} \<union> lps \<union> rps" by auto2

theorem exists_tree_of [resolve]: "refs_ofR h p ps \<Longrightarrow> \<exists>t. tree_ofR h p t" by auto2

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
theorem proper_ref_empty [forward]: "Ref.present h p \<Longrightarrow> Ref.get h p = Empty \<Longrightarrow> proper_ref h p"
  by (tactic {* auto2s_tac @{context} (OBTAIN "refs_ofR h p {p}") *})

theorem proper_ref_next1 [forward]:
  "Ref.get h p = Node lp v rp \<Longrightarrow> proper_ref h p \<Longrightarrow> proper_ref h lp \<and> proper_ref h rp" by auto2

theorem proper_ref_tree_of [resolve]: "proper_ref h p \<Longrightarrow> \<exists>t. tree_ofR h p t" by auto2

definition tree_of :: "heap \<Rightarrow> ('a::heap) node ref \<Rightarrow> 'a tree" where
  "tree_of h p = (THE t. tree_ofR h p t)"
setup {* add_rewrite_rule @{thm tree_of_def} *}
theorem tree_ofI [forward]: "tree_ofR h p t \<Longrightarrow> tree_of h p = t" by auto2
theorem tree_ofE: "proper_ref h p \<Longrightarrow> tree_ofR h p (tree_of h p)"
  by (tactic {* auto2s_tac @{context} (OBTAIN "\<exists>!t. tree_ofR h p t") *})
setup {* del_prfstep_thm @{thm tree_of_def} *}
setup {* add_forward_prfstep_cond @{thm tree_ofE} [with_term "tree_of ?h ?p"] *}

theorem tree_of_Empty [rewrite]: "Ref.get h r = Empty \<Longrightarrow> tree_of h r = Tip" by auto2
theorem tree_of_Empty' [forward]: "proper_ref h r \<Longrightarrow> tree_of h r = Tip \<Longrightarrow> Ref.get h r = Empty" by auto2
theorem tree_of_Node [forward]: "Ref.get h p = Node lp v rp \<Longrightarrow> proper_ref h p \<Longrightarrow>
  tree_of h p = tree.Node (tree_of h lp) v (tree_of h rp)" by auto2
theorem tree_of_Node' [forward]: "tree_of h p = tree.Node l v r \<Longrightarrow> Ref.get h p \<noteq> Empty" by auto2

definition refs_of :: "heap \<Rightarrow> ('a::heap) node ref \<Rightarrow> 'a node ref set" where
  "refs_of h p = (THE ps. refs_ofR h p ps)"
setup {* add_rewrite_rule @{thm refs_of_def} *}
theorem refs_ofI [forward]: "refs_ofR h p ps \<Longrightarrow> present_on_set h ps \<Longrightarrow> proper_ref h p \<and> refs_of h p = ps" by auto2
theorem refs_ofE: "proper_ref h p \<Longrightarrow> refs_ofR h p (refs_of h p)" by auto2
setup {* del_prfstep_thm @{thm refs_of_def} *}
setup {* add_forward_prfstep_cond @{thm refs_ofE} [with_term "refs_of ?h ?p"] *}

theorem refs_of_Empty [forward]:
  "Ref.present h p \<Longrightarrow> Ref.get h p = Empty \<Longrightarrow> refs_of h p = {p}" by auto2

theorem proper_ref_next1' [forward]:
  "Ref.get h p = Node lp v rp \<Longrightarrow> proper_ref h p \<Longrightarrow> refs_of h lp \<inter> refs_of h rp = {} \<and>
   p \<notin> refs_of h lp \<and> p \<notin> refs_of h rp \<and> refs_of h p = {p} \<union> refs_of h lp \<union> refs_of h rp" by auto2

theorem proper_ref_next2 [backward2]:
  "Ref.get h p = Node lp v rp \<Longrightarrow> Ref.present h p \<Longrightarrow> proper_ref h lp \<Longrightarrow> proper_ref h rp \<Longrightarrow>
   p \<notin> refs_of h lp \<Longrightarrow> p \<notin> refs_of h rp \<Longrightarrow> refs_of h lp \<inter> refs_of h rp = {} \<Longrightarrow> proper_ref h p"
  by (tactic {* auto2s_tac @{context} (OBTAIN "refs_ofR h p ({p} \<union> refs_of h lp \<union> refs_of h rp)") *})

theorem proper_ref_present [forward]:
  "proper_ref h p \<Longrightarrow> Ref.present h p \<and> present_on_set h (refs_of h p)"
  by (tactic {* auto2s_tac @{context} (CASE "Ref.get h p = Empty") *})

setup {* fold del_prfstep_thm [@{thm tree_ofR.intros(1)}, @{thm refs_ofR.intros(1)},
  @{thm proper_ref_def}, @{thm tree_ofE}, @{thm refs_ofE}] *}

subsection {* Interaction of partial functions with heap transitions *}

lemma refs_of_set_ref: "p \<notin> refs_of h q \<Longrightarrow> proper_ref h q \<Longrightarrow>
  proper_ref (Ref.set p v h) q \<and> refs_of (Ref.set p v h) q = refs_of h q"
  by (tactic {* auto2s_tac @{context} (INDUCT ("ts = tree_of h q", [Arbitrary "q"])) *})
setup {* add_forward_prfstep_cond @{thm refs_of_set_ref} [with_term "Ref.set ?p ?v ?h"] *}

lemma tree_of_set_ref [rewrite]:
  "p \<notin> refs_of h q \<Longrightarrow> proper_ref h q \<Longrightarrow> tree_of (Ref.set p v h) q = tree_of h q"
  by (tactic {* auto2s_tac @{context} (INDUCT ("ts = tree_of h q", [Arbitrary "q"])) *})

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

lemma eq_on_set_head [forward]:
  "eq_on_set h h' (refs_of h r) \<Longrightarrow> proper_ref h r \<Longrightarrow> Ref.get h r = Ref.get h' r"
  by (tactic {* auto2s_tac @{context} (CASE "Ref.get h r = Empty") *})

lemma eq_on_set_next_refs [forward]:
  "Ref.get h r = Node lp v rp \<Longrightarrow> eq_on_set h h' (refs_of h r) \<Longrightarrow> proper_ref h r \<Longrightarrow>
  eq_on_set h h' (refs_of h lp) \<and> eq_on_set h h' (refs_of h rp)" by auto2

lemma refs_of_invariant [forward]: "proper_ref h r \<Longrightarrow> eq_on_set h h' (refs_of h r) \<Longrightarrow>
  proper_ref h' r \<and> refs_of h r = refs_of h' r"
  by (tactic {* auto2s_tac @{context} (INDUCT ("ts = tree_of h r", [Arbitrary "r"])) *})

lemma tree_of_invariant [forward]:
  "proper_ref h r \<Longrightarrow> eq_on_set h h' (refs_of h r) \<Longrightarrow> tree_of h r = tree_of h' r"
  by (tactic {* auto2s_tac @{context} (INDUCT ("ts = tree_of h r", [Arbitrary "r"])) *})

lemma effect_update_ref [forward]:
  "effect (p := q) h h' v \<Longrightarrow> Ref.get h p = Node lp v rp \<Longrightarrow> proper_ref h p \<Longrightarrow>
   eq_on_set h h' (refs_of h lp) \<and> eq_on_set h h' (refs_of h rp)" by auto2

lemma effect_ref_tree [forward]:
  "effect (ref (Node lp v rp)) h h' r \<Longrightarrow> proper_ref h lp \<Longrightarrow> proper_ref h rp \<Longrightarrow>
  refs_of h lp \<inter> refs_of h rp = {} \<Longrightarrow> proper_ref h' r \<and>
  tree_of h' r = tree.Node (tree_of h lp) v (tree_of h rp) \<and>
  refs_of h' r = {r} \<union> refs_of h lp \<union> refs_of h rp" by auto2

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

lemma make_btree_unchanged [forward]:
  "effect (make_btree t) h h' r \<Longrightarrow> Ref.present h r' \<Longrightarrow> Ref.present h' r' \<and> Ref.get h r' = Ref.get h' r'"
  by (tactic {* auto2s_tac @{context} (INDUCT ("t", Arbitraries ["h", "h'", "r"])) *})

lemma make_btree_unchanged_set [forward]:
  "effect (make_btree t) h h' r \<Longrightarrow> present_on_set h rs \<Longrightarrow> eq_on_set h h' rs" by auto2
lemma make_btree_unchanged_set' [forward]:
  "effect (make_btree t) h h' r \<Longrightarrow> not_present_on_set h' rs \<Longrightarrow> not_present_on_set h rs" by auto2
  
lemma make_btree [forward]:
  "effect (make_btree t) h h' r \<Longrightarrow> proper_ref h' r \<and> tree_of h' r = t \<and> not_present_on_set h (refs_of h' r)"
  by (tactic {* auto2s_tac @{context} (INDUCT ("t", Arbitraries ["h", "h'", "r"])) *})

partial_function (heap) traverse :: "'a::heap node ref \<Rightarrow> 'a tree Heap" where
  "traverse p = do { t \<leftarrow> !p;
    case t of Empty \<Rightarrow> return Tip
     | Node lp v rp \<Rightarrow> do { lt \<leftarrow> traverse lp;
                            rt \<leftarrow> traverse rp;
                            return (tree.Node lt v rt) } }"
setup {* add_rewrite_rule_cond @{thm traverse.simps} [with_filt (size1_filter "p")] *}

lemma traverse [forward]: "proper_ref h p \<Longrightarrow> tree_of h p = t \<Longrightarrow> effect (traverse p) h h t"
  by (tactic {* auto2s_tac @{context} (INDUCT ("t", [Arbitrary "p"])) *})

lemma traverse_make_btree: "effect (make_btree t \<bind> traverse) h h' r \<Longrightarrow> r = t" by auto2
setup {* del_prfstep_thm @{thm traverse} *}

section {* Sorted binary trees *}

definition proper_sorted_ref :: "heap \<Rightarrow> ('a::{heap,linorder}) node ref \<Rightarrow> bool" where
  "proper_sorted_ref h p \<longleftrightarrow> proper_ref h p \<and> tree_sorted (tree_of h p)"
setup {* add_rewrite_rule @{thm proper_sorted_ref_def} *}

theorem proper_sorted_ref_empty [forward]:
  "Ref.present h p \<Longrightarrow> Ref.get h p = Empty \<Longrightarrow> proper_sorted_ref h p" by auto2

section {* Insertion on binary trees *}

partial_function (heap) insert :: "'a::{heap,ord} \<Rightarrow> 'a node ref \<Rightarrow> unit Heap" where
  "insert x p = do { t \<leftarrow> !p;
    case t of Empty \<Rightarrow> do { lp \<leftarrow> ref Empty; rp \<leftarrow> ref Empty; p := Node lp x rp }
     | Node lp y rp \<Rightarrow> if x = y then return ()
                       else if x < y then insert x lp
                       else insert x rp } "
setup {* add_rewrite_rule_cond @{thm insert.simps} [with_filt (size1_filter "p")] *}

lemma insert_unchanged [forward]:
  "effect (insert x p) h h' r' \<Longrightarrow> proper_ref h p \<Longrightarrow> unchanged_outer h h' (refs_of h p)"
  by (tactic {* auto2s_tac @{context} (INDUCT ("t = tree_of h p", [Arbitrary "p"])) *})

lemma insert_local [forward]: "effect (insert x p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow>
  proper_ref h' p \<and> refs_of_extension h (refs_of h p) (refs_of h' p)"
  by (tactic {* auto2s_tac @{context} (INDUCT ("t = tree_of h p", [Arbitrary "p"])) *})

theorem insert_correct [forward]:
  "effect (insert x p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> tree_of h' p = tree_insert x (tree_of h p)"
  by (tactic {* auto2s_tac @{context} (INDUCT ("t = tree_of h p", [Arbitrary "p"])) *})
setup {* del_prfstep_thm @{thm insert.simps} *}

theorem imp_insert_present [forward]:
  "effect (insert x p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> tree_set (tree_of h' p) = {x} \<union> tree_set (tree_of h p)" by auto2

theorem imp_insert_sorted [forward]:
  "effect (insert x p) h h' r \<Longrightarrow> proper_sorted_ref h p \<Longrightarrow> proper_sorted_ref h' p" by auto2

section {* Deletion on binary trees *}

partial_function (heap) delete_min :: "'a::{heap,ord} node ref \<Rightarrow> 'a Heap" where
  "delete_min p = do { t \<leftarrow> !p;
    case t of Empty \<Rightarrow> raise ''delete_min: empty_node''
     | Node lp v rp \<Rightarrow> do { lt \<leftarrow> !lp; if lt = Empty then do { rt \<leftarrow> !rp; p := rt; return v }
                                       else do { w \<leftarrow> delete_min lp; return w } } }"
setup {* add_rewrite_rule_cond @{thm delete_min.simps} [with_filt (size1_filter "p")] *}

lemma delete_min_non_empty [forward]:
  "effect (delete_min p) h h' r \<Longrightarrow> Ref.get h p \<noteq> Empty" by auto2

lemma delete_min_unchanged [forward]:
  "effect (delete_min p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> unchanged_outer h h' (refs_of h p)"
  by (tactic {* auto2s_tac @{context} (INDUCT ("t = tree_of h p", Arbitraries ["p", "h", "h'", "r"])) *})

lemma delete_min_local [forward]: "effect (delete_min p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow>
  proper_ref h' p \<and> refs_of_extension h (refs_of h p) (refs_of h' p)"
  by (tactic {* auto2s_tac @{context} (INDUCT ("t = tree_of h p", Arbitraries ["p", "h", "h'", "r"])) *})

lemma delete_min_correct [forward]:
  "effect (delete_min p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow>
   tree_of h' p = delete_min_tree (tree_of h p) \<and> r = min_tree (tree_of h p)"
  by (tactic {* auto2s_tac @{context} (INDUCT ("t = tree_of h p", Arbitraries ["p", "h", "h'", "r"])) *})

lemma delete_min_data_str [forward]:
  "effect (delete_min p) h h' r \<Longrightarrow> proper_sorted_ref h p \<Longrightarrow> tree_of h p \<noteq> Tip \<Longrightarrow>
   proper_sorted_ref h' p \<and> tree_set (tree_of h' p) \<subset> tree_set (tree_of h p) \<and>
   tree_set (tree_of h' p) = tree_set (tree_of h p) - {min_tree (tree_of h p)}" by auto2

lemma delete_min_data_str2 [rewrite_back]:
  "effect (delete_min p) h h' r \<Longrightarrow> proper_sorted_ref h p \<Longrightarrow> tree_of h p \<noteq> Tip \<Longrightarrow>
   tree_set (tree_of h p) = tree_set (tree_of h' p) \<union> {min_tree (tree_of h p)}" by auto2

lemma delete_min_succeed [backward2]:
  "proper_ref h p \<Longrightarrow> Ref.get h p \<noteq> Empty \<Longrightarrow> success (delete_min p) h"
  by (tactic {* auto2s_tac @{context} (INDUCT ("t = tree_of h p", Arbitraries ["p", "h"])) *})
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

lemma delete_correct [forward]:
  "effect (delete p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> Ref.get h p \<noteq> Empty \<Longrightarrow>
   proper_ref h' p \<and> tree_of h' p = delete_elt_tree (tree_of h p)" by auto2
setup {* del_prfstep_thm @{thm delete.simps} *}

theorem delete_data_str:
  "effect (delete p) h h' r \<Longrightarrow> proper_sorted_ref h p \<Longrightarrow> Ref.get h p \<noteq> Empty \<Longrightarrow> proper_sorted_ref h' p \<and>
   tree_set (tree_of h' p) = tree_set (tree_of h p) - {val (Ref.get h p)} \<and> tree_sorted (tree_of h' p)" by auto2

section {* Example: tree sort *}

primrec insert_list :: "'a::{heap,ord} list \<Rightarrow> 'a node ref \<Rightarrow> unit Heap" where
  "insert_list [] p = return ()"
| "insert_list (x # xs) p = do { insert x p; insert_list xs p; return () }"
setup {* fold add_rewrite_rule @{thms insert_list.simps} *}

lemma insert_list_unchanged [forward]:
  "effect (insert_list xs p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> unchanged_outer h h' (refs_of h p)"
  by (tactic {* auto2s_tac @{context} (INDUCT ("xs", [Arbitrary "h"])) *})

lemma insert_list_local [forward]: "effect (insert_list xs p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow>
  proper_ref h' p \<and> refs_of_extension h (refs_of h p) (refs_of h' p)"
  by (tactic {* auto2s_tac @{context} (INDUCT ("xs", [Arbitrary "h"])) *})

lemma insert_list_present [forward]: "effect (insert_list xs p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow>
  tree_set (tree_of h' p) = set xs \<union> tree_set (tree_of h p)"
  by (tactic {* auto2s_tac @{context} (INDUCT ("xs", [Arbitrary "h"])) *})

lemma insert_list_sorted [forward]:
  "effect (insert_list xs p) h h' r \<Longrightarrow> proper_sorted_ref h p \<Longrightarrow> proper_sorted_ref h' p"
  by (tactic {* auto2s_tac @{context} (INDUCT ("xs", [Arbitrary "h"])) *})

partial_function (heap) extract_sorted_list :: "'a::{heap,ord} node ref \<Rightarrow> 'a list Heap" where
  "extract_sorted_list p = do { t \<leftarrow> !p;
    case t of Empty \<Rightarrow> return []
     | Node lt v rt \<Rightarrow> do { x \<leftarrow> delete_min p; xs \<leftarrow> extract_sorted_list p; return (x # xs) } }"
setup {* add_rewrite_rule @{thm extract_sorted_list.simps} *}

ML {*
(* For effect (extract_sorted_list p) h h' r *)
val extract_sorted_list_script =
  OBTAIN "tree_of h p \<noteq> Tip" THEN
  FINSET_INDUCT ("A = tree_set (tree_of h p)", Arbitraries ["h", "h'", "r"])
*}

lemma extract_sorted_list_unchanged [forward]:
  "effect (extract_sorted_list p) h h' r \<Longrightarrow> proper_sorted_ref h p \<Longrightarrow> unchanged_outer h h' (refs_of h p)"
  by (tactic {* auto2s_tac @{context} extract_sorted_list_script *})

lemma extract_sorted_list_on_set [forward]:
  "effect (extract_sorted_list p) h h' r \<Longrightarrow> proper_sorted_ref h p \<Longrightarrow> set r = tree_set (tree_of h p) \<and> strict_sorted r"
   by (tactic {* auto2s_tac @{context} extract_sorted_list_script *})

definition tree_sort :: "'a::{heap,linorder} list \<Rightarrow> 'a list Heap" where
  "tree_sort xs = do { p \<leftarrow> ref Empty; insert_list xs p;
                       ys \<leftarrow> extract_sorted_list p; return ys}"
setup {* add_rewrite_rule @{thm tree_sort_def} *}

theorem tree_sort_correct: "effect (tree_sort xs) h h' ys \<Longrightarrow> set xs = set ys \<and> strict_sorted ys" by auto2

end
