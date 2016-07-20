(* Binary search trees. *)

theory BinaryTree
imports SepAuto Mapping
begin

section {* Abstract trees *}

datatype ('a, 'b) tree =
  Tip | Node (lsub: "('a, 'b) tree") (key: 'a) (val: 'b) (rsub: "('a, 'b) tree")
setup {* add_resolve_prfstep @{thm tree.distinct(2)} *}
setup {* add_forward_prfstep (equiv_forward_th (@{thm tree.simps(1)})) *}
theorem if_not_Tip [rewrite]: "(if Node l k v r = Tip then a else b) = b" by simp

text {* Case checking for trees: first verify the Tip case, then can assume t is
  in the form Node l k v r. *}

setup {* add_gen_prfstep ("tree_case_intro",
  [WithTerm @{term_pat "?t::(?'a, ?'b) tree"},
   Filter (unique_free_filter "t"),
   CreateCase @{term_pat "(?t::(?'a, ?'b) tree) = Tip"}]) *}
setup {* add_forward_prfstep_cond @{thm tree.collapse} [with_cond "?tree \<noteq> Node ?l ?k ?v ?r"] *}

text {* Induction on trees: after checking Tip case, can assume P (lsub t)
  and P (rsub t) holds when trying to prove P t. *}

theorem tree_induct': "P Tip \<Longrightarrow> (\<forall>t. P (lsub t) \<and> P (rsub t) \<longrightarrow> P t) \<Longrightarrow> P t"
  apply (induct t) apply blast by (metis tree.sel(1) tree.sel(4))
setup {* add_prfstep_induction @{thm tree_induct'} *}

section {* Tree nodes *}

datatype ('a, 'b) node =
  Node (lsub: "('a, 'b) node ref option") (key: 'a) (val: 'b) (rsub: "('a, 'b) node ref option")

fun node_encode :: "('a::heap, 'b::heap) node \<Rightarrow> nat" where
  "node_encode (Node l k v r) = to_nat (l, k, v, r)"

instance node :: (heap, heap) heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "node_encode"])
  apply (case_tac x, simp_all, case_tac y, simp_all)
  ..

setup {* fold add_rewrite_rule @{thms node.sel} *}
theorem node_constr:
  "Node l k v r = Node l' k' v' r' \<Longrightarrow> l = l' \<and> k = k' \<and> v = v' \<and> r = r'" by simp
setup {* add_forward_prfstep @{thm node_constr} *}

fun btree :: "('a::heap, 'b::heap) tree \<Rightarrow> ('a, 'b) node ref option \<Rightarrow> assn" where
  "btree Tip p = \<up>(p = None)"
| "btree (tree.Node lt k v rt) (Some p) = (\<exists>\<^sub>Alp rp. p \<mapsto>\<^sub>r Node lp k v rp * btree lt lp * btree rt rp)"
| "btree (tree.Node lt k v rt) None = false"
setup {* fold add_rewrite_rule @{thms btree.simps} *}

lemma btree_split_iff1 [rewrite]: "btree t None = \<up>(t = Tip)" by auto2

lemma btree_split_iff2 [forward_ent]:
  "btree (tree.Node lt k v rt) (Some p) \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Alp rp. p \<mapsto>\<^sub>r Node lp k v rp * btree lt lp * btree rt rp)" by auto2

lemma btree_split_elim:
  "\<exists>lp rp. h \<Turnstile> p \<mapsto>\<^sub>r Node lp k v rp * Ql lp rp \<Longrightarrow> h \<Turnstile> p \<mapsto>\<^sub>r Node lp k v rp * Q \<Longrightarrow>
   h \<Turnstile> p \<mapsto>\<^sub>r Node lp k v rp * Ql lp rp" by auto2
setup {* add_gen_prfstep ("btree_split_elim", forward_descs @{thm btree_split_elim} @ [ShadowFirst]) *}

lemma btree_is_some: "h \<Turnstile> btree (tree.Node lt k v rt) q * Qu \<Longrightarrow> q \<noteq> None" by auto2
setup {* add_forward_prfstep_cond @{thm btree_is_some} [with_cond "?q \<noteq> None"] *}

lemma btree_constr_ent [forward_ent]:
  "p \<mapsto>\<^sub>r Node lp k v rp * btree lt lp * btree rt rp \<Longrightarrow>\<^sub>A btree (tree.Node lt k v rt) (Some p)" by auto2
setup {* del_prfstep_thm @{thm btree.simps(2)} *}

lemma btree_prec [sep_prec_thms]:
  "h \<Turnstile> btree t p * F1 \<Longrightarrow> h \<Turnstile> btree t' p * F2 \<Longrightarrow> t = t'"
  by (tactic {* auto2s_tac @{context}
    (INDUCT ("t", Arbitraries ["p", "t'", "F1", "F2"]) THEN CASE "t' = Tip") *})

theorem btree_some [resolve]: "\<not>h \<Turnstile> btree Tip (Some p) * Ru" by auto2
theorem btree_none [match_code_pos_emp]: "btree Tip None = emp" by auto2

type_synonym ('a, 'b) btree = "('a, 'b) node ref option"

subsection {* Operations *}

subsubsection {* Basic operations *}

definition tree_empty :: "('a, 'b) btree Heap" where
  "tree_empty \<equiv> return None"
declare tree_empty_def [sep_proc_defs]

lemma tree_empty_rule [next_code_pos]:
  "<emp> tree_empty <btree Tip>" by auto2

definition tree_is_empty :: "('a, 'b) btree \<Rightarrow> bool Heap" where
  "tree_is_empty b \<equiv> return (b = None)"
declare tree_is_empty_def [sep_proc_defs]

lemma tree_is_empty_rule:
  "<btree t b> tree_is_empty b <\<lambda>r. btree t b * \<up>(r \<longleftrightarrow> t = Tip)>" by auto2

definition btree_constr :: "('a::heap, 'b::heap) btree \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_constr lp k v rp = do { p \<leftarrow> ref (Node lp k v rp); return (Some p) }"
declare btree_constr_def [sep_proc_defs]

lemma btree_constr_rule [next_code_pos, resolve]:
  "<btree lt lp * btree rt rp> btree_constr lp k v rp <btree (tree.Node lt k v rt)>" by auto2

subsubsection {* Insertion *}

partial_function (heap) btree_insert ::
  "'a::{heap,ord} \<Rightarrow> 'b::heap \<Rightarrow> ('a, 'b) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_insert k v b = (case b of
     None \<Rightarrow> btree_constr None k v None
   | Some p \<Rightarrow> do {
      t \<leftarrow> !p;
      (if k = key t then do {
         p := Node (lsub t) k v (rsub t);
         return (Some p) }
       else if k < key t then do {
         q \<leftarrow> btree_insert k v (lsub t);
         p := Node q (key t) (val t) (rsub t);  
         return (Some p) }
       else do {
         q \<leftarrow> btree_insert k v (rsub t);
         p := Node (lsub t) (key t) (val t) q;
         return (Some p)}) })"
declare btree_insert.simps [sep_proc_defs]

fun tree_set :: "('a, 'b) tree \<Rightarrow> 'a set" where
  "tree_set Tip = {}"
| "tree_set (tree.Node lt k v rt) = {k} \<union> tree_set lt \<union> tree_set rt"
setup {* fold add_rewrite_rule @{thms tree_set.simps} *}

fun tree_sorted :: "('a::linorder, 'b) tree \<Rightarrow> bool" where
  "tree_sorted Tip = True"
| "tree_sorted (tree.Node lt k v rt) = ((\<forall>x\<in>tree_set lt. x < k) \<and> (\<forall>x\<in>tree_set rt. k < x)
                              \<and> tree_sorted lt \<and> tree_sorted rt)"
setup {* fold add_rewrite_rule @{thms tree_sorted.simps} *}

fun tree_map :: "('a::linorder, 'b) tree \<Rightarrow> ('a, 'b) map" where
  "tree_map Tip = Map (\<lambda>x. None)"
| "tree_map (tree.Node lt k v rt) = binary_map k v (tree_map lt) (tree_map rt)"
setup {* fold add_rewrite_rule @{thms tree_map.simps} *}

lemma btree_insert_set_rule [next_code_pos]:
  "<btree t b> btree_insert k v b <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(tree_set t' = {k} \<union> tree_set t)>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("t", Arbitraries ["b"])) *})

lemma btree_insert_map_rule [next_code_pos]:
  "<btree t b> btree_insert k v b <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(tree_map t' = (tree_map t) {k \<rightarrow> v})>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("t", Arbitraries ["b"])) *})

lemma btree_insert_sorted_rule [next_code_pos]:
  "<btree t b * \<up>(tree_sorted t)> btree_insert k v b <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(tree_sorted t')>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("t", Arbitraries ["b"])) *})

section {* Outer interface *}

definition btree_set :: "'a set \<Rightarrow> ('a::{heap,linorder}, 'b::heap) node ref option \<Rightarrow> assn" where
  "btree_set S p = (\<exists>\<^sub>At. btree t p * \<up>(tree_sorted t) * \<up>(S = tree_set t))"
setup {* add_rewrite_rule @{thm btree_set_def} *}

definition btree_map :: "('a, 'b) map \<Rightarrow> ('a::{heap,linorder}, 'b::heap) node ref option \<Rightarrow> assn" where
  "btree_map M p = (\<exists>\<^sub>At. btree t p * \<up>(tree_sorted t) * \<up>(M = tree_map t))"
setup {* add_rewrite_rule @{thm btree_map_def} *}

declare tree_empty_def [sep_proc_defs del]

lemma btree_empty_rule1:
  "<emp> tree_empty <btree_set {}>" by auto2

lemma btree_empty_rule2:
  "<emp> tree_empty <btree_map empty_map>" by auto2

declare btree_insert.simps [sep_proc_defs del]

lemma btree_insert_rule1:
  "<btree_set S b> btree_insert k v b <btree_set ({k} \<union> S)>" by auto2

lemma btree_insert_rule2:
  "<btree_map M b> btree_insert k v b <btree_map (M {k \<rightarrow> v})>" by auto2

end
