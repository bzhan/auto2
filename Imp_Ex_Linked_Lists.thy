theory Imp_Ex_Linked_Lists
imports Imp_Thms Lists_Ex
begin

section {* Definition of Linked Lists *}

setup {* Sign.add_const_constraint (@{const_name Ref}, SOME @{typ "nat \<Rightarrow> 'a\<Colon>type ref"}) *}
datatype 'a node = Empty | Node (val: 'a) (nxt: "'a node ref")

setup {* add_forward_prfstep (equiv_forward_th @{thm node.simps(1)}) *}
setup {* add_rew_const @{term "Empty"} *}
setup {* add_resolve_prfstep @{thm node.distinct(2)} *}
setup {* add_forward_prfstep @{thm node.collapse} *}

primrec
  node_encode :: "'a\<Colon>countable node \<Rightarrow> nat"
where
  "node_encode Empty = 0"
| "node_encode (Node x r) = Suc (to_nat (x, r))"

instance node :: (countable) countable
proof (rule countable_classI [of "node_encode"])
  fix x y :: "'a\<Colon>countable node"
  show "node_encode x = node_encode y \<Longrightarrow> x = y"
  by (induct x, auto, induct y, auto, induct y, auto)
qed

instance node :: (heap) heap ..

subsection {* Definition and properties of the predicates *}

inductive list_ofR :: "heap \<Rightarrow> ('a::heap) node ref \<Rightarrow> 'a list \<Rightarrow> bool" where
  "Ref.get h p = Empty \<Longrightarrow> list_ofR h p []"
| "Ref.get h p = Node b n \<Longrightarrow> list_ofR h n ns \<Longrightarrow> list_ofR h p (b # ns)"
setup {* fold add_forward_prfstep @{thms list_ofR.intros} *}
setup {* add_prfstep_prop_induction @{thm list_ofR.induct} *}

theorem list_ofR_non_Nil: "list_ofR h p xs \<Longrightarrow> Ref.get h p = Node b n \<Longrightarrow> xs \<noteq> []" by auto2
setup {* add_forward_prfstep @{thm list_ofR_non_Nil} *}
theorem list_ofR_non_Empty: "list_ofR h p (b # xs) \<Longrightarrow> Ref.get h p \<noteq> Empty"
  by (tactic {* auto2s_tac @{context} (PROP_INDUCT ("list_ofR h p (b # xs)", [])) *})
setup {* add_forward_prfstep @{thm list_ofR_non_Empty} *}

theorem list_ofR_Node: "Ref.get h p = Node b n \<Longrightarrow> list_ofR h p (x # xs) \<Longrightarrow>
  x = b \<and> list_ofR h n xs"
  by (tactic {* auto2s_tac @{context} (PROP_INDUCT ("list_ofR h p (x # xs)", [])) *})
setup {* add_forward_prfstep @{thm list_ofR_Node} *}

inductive refs_ofR :: "heap \<Rightarrow> ('a::heap) node ref \<Rightarrow> 'a node ref set \<Rightarrow> bool" where
  "Ref.get h p = Empty \<Longrightarrow> refs_ofR h p {p}"
| "Ref.get h p = Node b n \<Longrightarrow> refs_ofR h n ps \<and> p \<notin> ps \<Longrightarrow> refs_ofR h p ({p} \<union> ps)"
setup {* add_known_fact @{thm refs_ofR.intros(1)} *}
setup {* add_backward2_prfstep @{thm refs_ofR.intros(2)} *}
setup {* add_prfstep_prop_induction @{thm refs_ofR.induct} *}

theorem refs_ofR_Empty: "Ref.get h p = Empty \<Longrightarrow> refs_ofR h p ps \<Longrightarrow> ps = {p}" by auto2
theorem refs_ofR_Node: "Ref.get h p = Node b n \<Longrightarrow> refs_ofR h p ps \<Longrightarrow>
  \<exists>ns. refs_ofR h n ns \<and> p \<notin> ns \<and> ps = {p} \<union> ns" by auto2
setup {* fold add_forward_prfstep [@{thm refs_ofR_Empty}, @{thm refs_ofR_Node}] *}

theorem exists_list_of: "refs_ofR h p ps \<Longrightarrow> \<exists>xs. list_ofR h p xs" by auto2
setup {* add_resolve_prfstep @{thm exists_list_of} *}

lemma refs_ofR_is_fun: "\<lbrakk> refs_ofR h p xs; refs_ofR h p ys \<rbrakk> \<Longrightarrow> xs = ys"
  by (tactic {* auto2s_tac @{context} (PROP_INDUCT ("refs_ofR h p xs", [Arbitrary "ys"])) *})
setup {* add_forward_prfstep_cond @{thm refs_ofR_is_fun} [with_cond "?xs \<noteq> ?ys"] *}

lemma list_ofR_is_fun: "\<lbrakk> list_ofR h p xs; list_ofR h p ys \<rbrakk> \<Longrightarrow> xs = ys"
  by (tactic {* auto2s_tac @{context} (PROP_INDUCT ("list_ofR h p xs", [Arbitrary "ys"])) *})
setup {* add_forward_prfstep_cond @{thm list_ofR_is_fun} [with_cond "?xs \<noteq> ?ys"] *}

subsection {* Partial function version of predicates *}

definition proper_ref :: "heap \<Rightarrow> ('a::heap) node ref \<Rightarrow> bool" where
  "proper_ref h p = (\<exists>ps. refs_ofR h p ps \<and> present_on_set h ps)"
setup {* add_rewrite_rule @{thm proper_ref_def} *}
theorem proper_ref_empty: "Ref.present h p \<Longrightarrow> Ref.get h p = Empty \<Longrightarrow> proper_ref h p"
  by (tactic {* auto2s_tac @{context} (OBTAIN "refs_ofR h p {p}") *})
setup {* add_forward_prfstep @{thm proper_ref_empty} *}

theorem proper_ref_next1: "Ref.get h p = Node b n \<Longrightarrow> proper_ref h p \<Longrightarrow> proper_ref h n" by auto2
setup {* add_forward_prfstep @{thm proper_ref_next1} *}

theorem proper_ref_list_of: "proper_ref h p \<Longrightarrow> \<exists>ps. list_ofR h p ps" by auto2
setup {* add_resolve_prfstep @{thm proper_ref_list_of} *}

definition list_of :: "heap \<Rightarrow> ('a::heap) node ref \<Rightarrow> 'a list" where
  "list_of h p = (THE xs. list_ofR h p xs)"
theorem list_ofI: "list_ofR h p xs \<Longrightarrow> list_of h p = xs" by (metis list_ofR_is_fun list_of_def the1_equality)
theorem list_ofE: "proper_ref h p \<Longrightarrow> list_ofR h p (list_of h p)" using list_ofI proper_ref_list_of by blast
setup {* add_forward_prfstep @{thm list_ofI} #> add_forward_prfstep_cond @{thm list_ofE} [with_term "list_of ?h ?p"] *}

theorem list_of_Empty: "Ref.get h p = Empty \<Longrightarrow> list_of h p = []" by auto2
theorem list_of_Empty': "proper_ref h p \<Longrightarrow> list_of h p = [] \<Longrightarrow> Ref.get h p = Empty" by auto2
theorem list_of_Node: "Ref.get h p = Node b n \<Longrightarrow> proper_ref h p \<Longrightarrow> list_of h p = b # list_of h n" by auto2
theorem list_of_Node': "list_of h p = b # xn \<Longrightarrow> Ref.get h p \<noteq> Empty" by auto2
setup {* add_rewrite_rule @{thm list_of_Empty} *}
setup {* fold add_forward_prfstep [@{thm list_of_Empty'}, @{thm list_of_Node}, @{thm list_of_Node'}] *}

definition refs_of :: "heap \<Rightarrow> ('a::heap) node ref \<Rightarrow> 'a node ref set" where
  "refs_of h p = (THE rs. refs_ofR h p rs)"
theorem refs_ofI: "refs_ofR h p ps \<Longrightarrow> present_on_set h ps \<Longrightarrow> proper_ref h p \<and> refs_of h p = ps"
  by (metis proper_ref_def refs_ofR_is_fun refs_of_def the1_equality)
theorem refs_ofE: "proper_ref h p \<Longrightarrow> refs_ofR h p (refs_of h p)" using proper_ref_def refs_ofI by blast
setup {* add_forward_prfstep @{thm refs_ofI} #> add_forward_prfstep_cond @{thm refs_ofE} [with_term "refs_of ?h ?p"] *}

theorem refs_of_Empty: "Ref.present h p \<Longrightarrow> Ref.get h p = Empty \<Longrightarrow> refs_of h p = {p}" by auto2
setup {* add_forward_prfstep @{thm refs_of_Empty} *}

theorem proper_ref_next1':
  "Ref.get h p = Node b n \<Longrightarrow> proper_ref h p \<Longrightarrow> p \<notin> refs_of h n \<and> refs_of h p = {p} \<union> refs_of h n" by auto2
setup {* add_forward_prfstep @{thm proper_ref_next1'} *}

theorem proper_ref_next2:
  "Ref.get h p = Node b n \<Longrightarrow> Ref.present h p \<and> proper_ref h n \<and> p \<notin> refs_of h n \<Longrightarrow> proper_ref h p"
  by (tactic {* auto2s_tac @{context} (OBTAIN "refs_ofR h p ({p} \<union> refs_of h n)") *})
setup {* add_backward2_prfstep @{thm proper_ref_next2} *}

theorem proper_ref_present: "proper_ref h p \<Longrightarrow> Ref.present h p \<and> present_on_set h (refs_of h p)"
  by (tactic {* auto2s_tac @{context} (CASE "Ref.get h p = Empty") *})
setup {* add_forward_prfstep @{thm proper_ref_present} *}

setup {* fold del_prfstep_thm [@{thm list_ofR.intros(1)}, @{thm refs_ofR.intros(1)},
  @{thm proper_ref_def}, @{thm list_ofE}, @{thm refs_ofE}] *}

subsection {* Interaction of partial functions with heap transitions *}

lemma refs_of_set_ref: "p \<notin> refs_of h q \<Longrightarrow> proper_ref h q \<Longrightarrow>
  proper_ref (Ref.set p v h) q \<and> refs_of (Ref.set p v h) q = refs_of h q"
  by (tactic {* auto2s_tac @{context} (LIST_INDUCT_NEWVAR ("list_of h q", "qs", ["q"])) *})
setup {* add_forward_prfstep_cond @{thm refs_of_set_ref} [with_term "Ref.set ?p ?v ?h"] *}

lemma list_of_set_ref: "p \<notin> refs_of h q \<Longrightarrow> proper_ref h q \<Longrightarrow>
  list_of (Ref.set p v h) q = list_of h q"
  by (tactic {* auto2s_tac @{context} (LIST_INDUCT_NEWVAR ("list_of h q", "xs", ["q"])) *})
setup {* add_rewrite_rule @{thm list_of_set_ref} *}

lemma refs_of_set_next_ref: "proper_ref h n \<Longrightarrow> p \<notin> refs_of h n \<Longrightarrow>
  Ref.present h p \<Longrightarrow> proper_ref (Ref.set p (Node b n) h) p \<and>
  refs_of (Ref.set p (Node b n) h) p = {p} \<union> refs_of h n \<and>
  list_of (Ref.set p (Node b n) h) p = b # list_of h n" by auto2
setup {* add_forward_prfstep_cond @{thm refs_of_set_next_ref} [with_term "Ref.set ?p (Node ?b ?n) ?h"] *}

setup {* add_gen_prfstep ("set_next_ref_case_intro",
  [WithTerm @{term_pat "Ref.set ?p (Node ?b ?n) ?h"},
   CreateCase ([], [@{term_pat "?p \<notin> refs_of ?h ?n"}])]) *}

subsection {* Invariance of partial functions *}

lemma eq_on_set_head: "eq_on_set h h' (refs_of h r) \<Longrightarrow> proper_ref h r \<Longrightarrow> Ref.get h r = Ref.get h' r"
  by (tactic {* auto2s_tac @{context} (CASE "Ref.get h r = Empty") *})

lemma eq_on_set_next_refs: "Ref.get h r = Node b n \<Longrightarrow> eq_on_set h h' (refs_of h r) \<Longrightarrow> proper_ref h r \<Longrightarrow>
  eq_on_set h h' (refs_of h n)" by auto2
setup {* fold add_forward_prfstep [@{thm eq_on_set_head}, @{thm eq_on_set_next_refs}] *}

lemma refs_of_invariant: "proper_ref h r \<Longrightarrow> eq_on_set h h' (refs_of h r) \<Longrightarrow>
  proper_ref h' r \<and> refs_of h r = refs_of h' r"
  by (tactic {* auto2s_tac @{context} (LIST_INDUCT_NEWVAR ("list_of h r", "rs", ["r"])) *})
setup {* add_forward_prfstep @{thm refs_of_invariant} *}

lemma list_of_invariant: "proper_ref h r \<Longrightarrow> eq_on_set h h' (refs_of h r) \<Longrightarrow> list_of h r = list_of h' r"
  by (tactic {* auto2s_tac @{context} (LIST_INDUCT_NEWVAR ("list_of h r", "xs", ["r"])) *})
setup {* add_forward_prfstep @{thm list_of_invariant} *}

lemma effect_update_ref:
  "effect (p := q) h h' v \<Longrightarrow> Ref.get h p = Node x n \<Longrightarrow> proper_ref h p \<Longrightarrow>
   eq_on_set h h' (refs_of h n)" by auto2
setup {* add_forward_prfstep @{thm effect_update_ref} *}

theorem effect_ref_llist:
  "effect (ref (Node x n)) h h' r \<Longrightarrow> proper_ref h n \<Longrightarrow>
   proper_ref h' r \<and> list_of h' r = x # list_of h n \<and> refs_of h' r = {r} \<union> refs_of h n" by auto2
setup {* add_forward_prfstep @{thm effect_ref_llist} *}

section {* make_llist, traverse, and proof of correctness *}

primrec make_llist :: "'a\<Colon>heap list \<Rightarrow> 'a node ref Heap" where
  "make_llist []     = do { r \<leftarrow> ref Empty; return r }"
| "make_llist (x#xs) =
   do { tl \<leftarrow> make_llist xs;
        r \<leftarrow> ref (Node x tl);
        return r
      }"

partial_function (heap) traverse :: "'a\<Colon>heap node ref \<Rightarrow> 'a list Heap" where [code del]:
  "traverse r = do { v \<leftarrow> !r;
    if v = Empty then return []
    else do { xs \<leftarrow> traverse (nxt v);
              return (val v # xs)
            } }"
setup {* fold add_rewrite_rule @{thms make_llist.simps} #> add_rewrite_rule @{thm traverse.simps} *}

lemma make_llist: "effect (make_llist xs) h h' r \<Longrightarrow> proper_ref h' r \<and> list_of h' r = xs"
  by (tactic {* auto2s_tac @{context} (LIST_INDUCT ("xs", ["h", "h'", "r"])) *})

lemma traverse: "proper_ref h n \<Longrightarrow> list_of h n = r \<Longrightarrow> effect (traverse n) h h r"
  by (tactic {* auto2s_tac @{context} (LIST_INDUCT ("r", ["n"])) *})

setup {* fold add_forward_prfstep [@{thm make_llist}, @{thm traverse}] *}
lemma traverse_make_llist: "effect (make_llist xs \<guillemotright>= traverse) h h' r \<Longrightarrow> r = xs" by auto2
setup {* del_prfstep_thm @{thm traverse} *}

section {* Insertion and deletion on lists *}

text {* Insert x after p, which should not be Empty. *}

definition insert_after :: "'a::heap \<Rightarrow> 'a node ref \<Rightarrow> unit Heap" where
  "insert_after x p = do { v \<leftarrow> !p; if v = Empty then return () else do { r \<leftarrow> ref (Node x (nxt v)); p := Node (val v) r } }"
setup {* add_rewrite_rule @{thm insert_after_def} *}

theorem insert_after_correct:
  "effect (insert_after x p) h h' r' \<Longrightarrow> Ref.get h p \<noteq> Empty \<Longrightarrow> proper_ref h p \<Longrightarrow>
   unchanged_outer h h' (refs_of h p) \<and> proper_ref h' p \<and>
   list_of h' p = hd (list_of h p) # x # tl (list_of h p)" by auto2

text {* Insert at head of linked list. Return reference to new list. *}

definition insert_head :: "'a::heap \<Rightarrow> 'a node ref \<Rightarrow> 'a node ref Heap" where
  "insert_head x p = do { r \<leftarrow> ref (Node x p); return r }"
setup {* add_rewrite_rule @{thm insert_head_def} *}

theorem insert_head_correct:
  "effect (insert_head x p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow>
   proper_ref h' r \<and> list_of h' r = x # list_of h p \<and> refs_of h' r = {r} \<union> refs_of h p \<and>
   \<not> Ref.present h r \<and> unchanged_outer h h' (refs_of h p) \<and> refs_of_extension h (refs_of h p) (refs_of h' r)" by auto2
setup {* add_forward_prfstep @{thm insert_head_correct} *}
setup {* del_prfstep_thm @{thm insert_head_def} *}

text {* Insert x before the first node in p whose value is at least x. If p is sorted,
  this is ordered insertion. *}

partial_function (heap) insert_in_order :: "'a::{heap, ord} \<Rightarrow> 'a node ref \<Rightarrow> 'a node ref Heap" where
  "insert_in_order x p = do {
    v \<leftarrow> !p;
    if v = Empty then insert_head x p
    else if x < val v then insert_head x p
    else do { q \<leftarrow> insert_in_order x (nxt v); p := Node (val v) q; return p }
  }"
setup {* add_rewrite_rule_cond @{thm insert_in_order.simps} [with_filt (size1_filter "p")] *}

theorem insert_in_order_unchanged:
  "effect (insert_in_order x p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> unchanged_outer h h' (refs_of h p)"
  by (tactic {* auto2s_tac @{context} (LIST_INDUCT_NEWVAR ("list_of h p", "l", ["p", "h", "h'", "r"])) *})
setup {* add_forward_prfstep @{thm insert_in_order_unchanged} *}

theorem insert_in_order_local:
  "effect (insert_in_order x p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow>
   proper_ref h' r \<and> refs_of_extension h (refs_of h p) (refs_of h' r)"
  by (tactic {* auto2s_tac @{context} (LIST_INDUCT_NEWVAR ("list_of h p", "l", ["p", "h", "h'", "r"])) *})
setup {* add_forward_prfstep @{thm insert_in_order_local} *}

theorem insert_in_order_correct:
  "effect (insert_in_order x p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> list_of h' r = ordered_insert x (list_of h p)"
  by (tactic {* auto2s_tac @{context} (LIST_INDUCT_NEWVAR ("list_of h p", "l", ["p", "h", "h'", "r"])) *})
setup {* add_forward_prfstep @{thm insert_in_order_correct} #> del_prfstep_thm @{thm insert_in_order.simps} *}

theorem insert_in_order_multiset_of:
  "effect (insert_in_order x p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow>
   multiset_of (list_of h' r) = {#x#} + multiset_of (list_of h p)" by auto2

theorem insert_in_order_sorted:
  "effect (insert_in_order x p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> sorted (list_of h p) \<Longrightarrow> sorted (list_of h' r)" by auto2

text {* Remove a particular element. *}

partial_function (heap) remove_element :: "'a::heap \<Rightarrow> 'a node ref \<Rightarrow> 'a node ref Heap" where
  "remove_element x p = do {
    v \<leftarrow> !p;
    if v = Empty then return p
    else do { q \<leftarrow> remove_element x (nxt v);
              if val v = x then return q
              else do { p := Node (val v) q; return p } }
  }"
setup {* add_rewrite_rule_cond @{thm remove_element.simps} [with_filt (size1_filter "p")] *}

theorem remove_element_unchanged:
  "effect (remove_element x p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> unchanged_outer h h' (refs_of h p)"
  by (tactic {* auto2s_tac @{context} (LIST_INDUCT_NEWVAR ("list_of h p", "l", ["p", "h", "h'", "r"])) *})
setup {* add_forward_prfstep @{thm remove_element_unchanged} *}

theorem remove_element_local: "effect (remove_element x p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow>
   proper_ref h' r \<and> refs_of_extension h (refs_of h p) (refs_of h' r)" 
  by (tactic {* auto2s_tac @{context} (LIST_INDUCT_NEWVAR ("list_of h p", "l", ["p", "h", "h'", "r"])) *})
setup {* add_forward_prfstep @{thm remove_element_local} *}

theorem remove_element_correct:
  "effect (remove_element x p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> list_of h' r = remove_elt_list x (list_of h p)"
  by (tactic {* auto2s_tac @{context} (LIST_INDUCT_NEWVAR ("list_of h p", "l", ["p", "h", "h'", "r"])) *})
setup {* add_forward_prfstep @{thm remove_element_correct} #> del_prfstep_thm @{thm remove_element.simps} *}

theorem remove_element_set_of:
  "effect (remove_element x p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> set (list_of h' r) = set (list_of h p) - {x}" by auto2

theorem remove_element_sorted:
  "effect (remove_element x p) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> sorted (list_of h p) \<Longrightarrow> sorted (list_of h' r)" by auto2

section {* Proving correctness of in-place reversal *}

partial_function (heap) rev' :: "('a::heap) node ref \<Rightarrow> 'a node ref \<Rightarrow> 'a node ref Heap"
where
  [code]: "rev' q p =
   do { v \<leftarrow> !p;
        if v = Empty then return q
        else do { p := Node (val v) q;
                  rev' p (nxt v)
                }
      }"
setup {* add_rewrite_rule_cond @{thm rev'.simps} [with_filt (size1_filter "p")] *}

definition rev :: "('a::heap) node ref \<Rightarrow> 'a node ref Heap" where
  "rev p = do { v \<leftarrow> !p;
    if v = Empty then return p
    else do { q \<leftarrow> ref Empty;
              comment (\<lambda>h. refs_of h p \<inter> refs_of h q = {});
              v \<leftarrow> rev' q p;
              return v
            } }"
setup {* add_rewrite_rule @{thm rev_def} *}

theorem set_disjoint_exchange:
  "({p} \<union> A) \<inter> B = {} \<Longrightarrow> p \<notin> A \<Longrightarrow> ({p} \<union> B) \<inter> A = {}" by (simp add: Int_ac(3))
setup {* add_forward_prfstep_cond @{thm set_disjoint_exchange} [with_term "({?p} \<union> ?B) \<inter> ?A"] *}

lemma rev'_unchanged:
  "effect (rev' q p) h h' v' \<Longrightarrow> proper_ref h p \<Longrightarrow> proper_ref h q \<Longrightarrow> refs_of h p \<inter> refs_of h q = {} \<Longrightarrow>
   unchanged_outer h h' (refs_of h p)"
   by (tactic {* auto2s_tac @{context} (LIST_INDUCT_NEWVAR ("list_of h p", "ps", ["p", "q", "h"])) *})
setup {* add_forward_prfstep @{thm rev'_unchanged} *}

lemma rev'_invariant:
  "effect (rev' q p) h h' v' \<Longrightarrow> proper_ref h p \<Longrightarrow> proper_ref h q \<Longrightarrow> refs_of h p \<inter> refs_of h q = {} \<Longrightarrow>
   proper_ref h' v' \<and> list_of h' v' = (List.rev (list_of h p) @ list_of h q)"
   by (tactic {* auto2s_tac @{context} (LIST_INDUCT_NEWVAR ("list_of h p", "ps", ["p", "q", "h"])) *})
setup {* add_forward_prfstep @{thm rev'_invariant} *}

lemma rev'_succeed: "proper_ref h p \<Longrightarrow> success (rev' q p) h"
  by (tactic {* auto2s_tac @{context} (LIST_INDUCT_NEWVAR ("list_of h p", "ps", ["p", "q", "h"])) *})
setup {* del_prfstep_thm @{thm rev'.simps} #> add_backward_prfstep @{thm rev'_succeed} *}

lemma rev_correct: "effect (rev r) h h' r' \<Longrightarrow> proper_ref h r \<Longrightarrow>
  proper_ref h' r' \<and> list_of h' r' = List.rev (list_of h r)" by auto2

lemma rev_succeed: "proper_ref h r \<Longrightarrow> success (rev r) h" by auto2

section {* The merge function on Linked Lists *}

partial_function (heap) merge :: "('a::{heap, ord}) node ref \<Rightarrow> 'a node ref \<Rightarrow> 'a node ref Heap" where
[code]: "merge p q =
  do { np \<leftarrow> !p; nq \<leftarrow> !q;
       if np = Empty then return q
       else if nq = Empty then return p
       else if val np \<le> val nq then
         do { npq \<leftarrow> merge (nxt np) q;
              p := Node (val np) npq;
              return p
            }
       else
         do { pnq \<leftarrow> merge p (nxt nq);
              q := Node (val nq) pnq;
              return q
            }
     }"
setup {* add_rewrite_rule_cond @{thm merge.simps} [with_filt (size1_filter "p"), with_filt (size1_filter "q")] *}

theorem set_intersection_list: "(x \<union> xs) \<inter> ys = {} \<Longrightarrow> xs \<inter> ys = {}" by auto
setup {* add_forward_prfstep_cond @{thm set_intersection_list} [with_term "?xs \<inter> ?ys"] *}

theorem unchanged_outer_union_ref:
  "unchanged_outer h h' (refs_of h p \<union> refs_of h q) \<Longrightarrow> r \<notin> refs_of h p \<Longrightarrow> r \<notin> refs_of h q \<Longrightarrow>
   Ref.present h r \<Longrightarrow> Ref.get h r = Ref.get h' r" by (simp add: unchanged_outer_ref)
setup {* add_forward_prfstep @{thm unchanged_outer_union_ref} *}

theorem merge_unchanged:
  "effect (merge p q) h h' r' \<Longrightarrow> proper_ref h p \<Longrightarrow> proper_ref h q \<Longrightarrow> unchanged_outer h h' (refs_of h p \<union> refs_of h q)"
  by (tactic {* auto2s_tac @{context} (
    LIST_DOUBLE_INDUCT_NEWVAR ("list_of h p", "pl", "list_of h q", "ql", ["p", "q", "h'", "r'"])) *})
setup {* add_forward_prfstep @{thm merge_unchanged} *}

theorem merge_local:
  "effect (merge p q) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> proper_ref h q \<Longrightarrow> refs_of h p \<inter> refs_of h q = {} \<Longrightarrow>
   proper_ref h' r \<and> refs_of h' r \<subseteq> refs_of h p \<union> refs_of h q"
  by (tactic {* auto2s_tac @{context} (
    LIST_DOUBLE_INDUCT_NEWVAR ("list_of h p", "pl", "list_of h q", "ql", ["p", "q", "h'", "r"])) *})
setup {* add_forward_prfstep @{thm merge_local} *}

theorem merge_correct:
  "effect (merge p q) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> proper_ref h q \<Longrightarrow> refs_of h p \<inter> refs_of h q = {} \<Longrightarrow>
   list_of h' r = merge_list (list_of h p) (list_of h q)"
  by (tactic {* auto2s_tac @{context} (
    LIST_DOUBLE_INDUCT_NEWVAR ("list_of h p", "pl", "list_of h q", "ql", ["p", "q", "h'", "r"])) *})
setup {* add_forward_prfstep @{thm merge_correct} #> del_prfstep_thm @{thm merge.simps} *}

theorem merge_set_of:
  "effect (merge p q) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> proper_ref h q \<Longrightarrow> refs_of h p \<inter> refs_of h q = {} \<Longrightarrow>
   set (list_of h' r) = set (list_of h p) \<union> set (list_of h q)" by auto2

theorem merge_sorted:
  "effect (merge p q) h h' r \<Longrightarrow> proper_ref h p \<Longrightarrow> proper_ref h q \<Longrightarrow> refs_of h p \<inter> refs_of h q = {} \<Longrightarrow>
   sorted (list_of h p) \<Longrightarrow> sorted (list_of h q) \<Longrightarrow> sorted (list_of h' r)" by auto2

end
