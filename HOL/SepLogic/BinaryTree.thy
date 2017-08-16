(* Binary search trees. *)

theory BinaryTree
imports SepAuto "../DataStrs/BST_Base"
begin

section {* Tree nodes *}

datatype ('a, 'b) node =
  Node (lsub: "('a, 'b) node ref option") (key: 'a) (val: 'b) (rsub: "('a, 'b) node ref option")
setup {* fold add_rewrite_rule @{thms node.sel} *}
setup {* add_forward_prfstep (equiv_forward_th @{thm node.simps(1)}) *}

fun node_encode :: "('a::heap, 'b::heap) node \<Rightarrow> nat" where
  "node_encode (Node l k v r) = to_nat (l, k, v, r)"

instance node :: (heap, heap) heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "node_encode"])
  apply (case_tac x, simp_all, case_tac y, simp_all)
  ..

fun btree :: "('a::heap, 'b::heap) tree \<Rightarrow> ('a, 'b) node ref option \<Rightarrow> assn" where
  "btree Tip p = \<up>(p = None)"
| "btree (tree.Node lt k v rt) (Some p) = (\<exists>\<^sub>Alp rp. p \<mapsto>\<^sub>r Node lp k v rp * btree lt lp * btree rt rp)"
| "btree (tree.Node lt k v rt) None = false"
setup {* fold add_rewrite_ent_rule @{thms btree.simps} *}

lemma btree_Tip [forward_ent_shadow]: "btree Tip p \<Longrightarrow>\<^sub>A \<up>(p = None)" by auto2

lemma btree_Node [forward_ent_shadow]:
  "btree (tree.Node lt k v rt) (Some p) \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Alp rp. p \<mapsto>\<^sub>r Node lp k v rp * btree lt lp * btree rt rp)"
  by auto2

lemma btree_Node_none [forward_ent]: "btree (tree.Node lt k v rt) None \<Longrightarrow>\<^sub>A false" by auto2

lemma btree_Tip_some [forward_ent]: "btree Tip (Some p) \<Longrightarrow>\<^sub>A false" by auto2

lemma btree_is_some [forward_ent]: "btree (tree.Node lt k v rt) p \<Longrightarrow>\<^sub>A true * \<up>(p \<noteq> None)" by auto2

lemma btree_none: "emp \<Longrightarrow>\<^sub>A btree tree.Tip None" by auto2

lemma btree_constr_ent:
  "p \<mapsto>\<^sub>r Node lp k v rp * btree lt lp * btree rt rp \<Longrightarrow>\<^sub>A btree (tree.Node lt k v rt) (Some p)" by auto2

setup {* fold add_entail_matcher [@{thm btree_none}, @{thm btree_constr_ent}] *}

lemma btree_prec [sep_prec_thms]:
  "h \<Turnstile> btree t p * F1 \<Longrightarrow> h \<Turnstile> btree t' p * F2 \<Longrightarrow> t = t'"
@proof
  @induct t arbitrary p t' F1 F2 @with
    @subgoal "t = tree.Node l x v r" @case "t' = Tip" @endgoal
  @end
@qed

setup {* fold del_prfstep_thm @{thms btree.simps} *}

type_synonym ('a, 'b) btree = "('a, 'b) node ref option"

subsection {* Operations *}

subsubsection {* Basic operations *}

definition tree_empty :: "('a, 'b) btree Heap" where
  "tree_empty \<equiv> return None"
declare tree_empty_def [sep_proc_defs]

lemma tree_empty_rule [hoare_triple]:
  "<emp> tree_empty <btree Tip>" by auto2

definition tree_is_empty :: "('a, 'b) btree \<Rightarrow> bool Heap" where
  "tree_is_empty b \<equiv> return (b = None)"
declare tree_is_empty_def [sep_proc_defs]

lemma tree_is_empty_rule:
  "<btree t b> tree_is_empty b <\<lambda>r. btree t b * \<up>(r \<longleftrightarrow> t = Tip)>" by auto2

definition btree_constr :: "('a::heap, 'b::heap) btree \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_constr lp k v rp = do { p \<leftarrow> ref (Node lp k v rp); return (Some p) }"
declare btree_constr_def [sep_proc_defs]

lemma btree_constr_rule [hoare_triple, resolve]:
  "<btree lt lp * btree rt rp> btree_constr lp k v rp <btree (tree.Node lt k v rt)>" by auto2

subsubsection {* Insertion *}

partial_function (heap) btree_insert ::
  "'a::{heap,linorder} \<Rightarrow> 'b::heap \<Rightarrow> ('a, 'b) btree \<Rightarrow> ('a, 'b) btree Heap" where
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

lemma btree_insert_in_traverse [hoare_triple]:
  "<btree t b * \<up>(tree_sorted t)>
   btree_insert k v b
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(in_traverse t' = ordered_insert k (in_traverse t))>"
@proof @induct t arbitrary b @qed

lemma btree_insert_in_traverse_pairs [hoare_triple]:
  "<btree t b * \<up>(tree_sorted t)>
   btree_insert k v b
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(in_traverse_pairs t' = ordered_insert_pairs k v (in_traverse_pairs t))>"
@proof @induct t arbitrary b @qed

declare btree_insert.simps [sep_proc_defs del]
lemma btree_insert_sorted_rule [hoare_triple]:
  "<btree t b * \<up>(tree_sorted t)>
   btree_insert k v b
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(tree_sorted t')>" by auto2

lemma btree_insert_set_rule [hoare_triple]:
  "<btree t b * \<up>(tree_sorted t)>
   btree_insert k v b
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(tree_set t' = {k} \<union> tree_set t)>" by auto2

lemma btree_insert_map_rule [hoare_triple]:
  "<btree t b * \<up>(tree_sorted t)>
   btree_insert k v b
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(tree_map t' = (tree_map t) {k \<rightarrow> v})>" by auto2

partial_function (heap) btree_del_min :: "('a::heap, 'b::heap) btree \<Rightarrow> (('a \<times> 'b) \<times> ('a, 'b) btree) Heap" where
  "btree_del_min b = (case b of
     None \<Rightarrow> raise ''del_min: empty tree''
   | Some p \<Rightarrow> do {
      t \<leftarrow> !p;
      (if lsub t = None then
         return ((key t, val t), rsub t)
       else do {
         r \<leftarrow> btree_del_min (lsub t);
         p := Node (snd r) (key t) (val t) (rsub t);
         return (fst r, Some p) }) })"
declare btree_del_min.simps [sep_proc_defs]

lemma btree_del_min_in_traverse [hoare_triple]:
  "<btree t b * \<up>(b \<noteq> None)>
   btree_del_min b
   <\<lambda>r. \<exists>\<^sub>At'. btree t' (snd r) * true * \<up>(fst (fst r) # in_traverse t' = in_traverse t)>"
@proof
  @induct t arbitrary b @with
    @subgoal "t = tree.Node l x v r" @case "l = Tip" @endgoal
  @end
@qed

lemma btree_del_min_in_traverse_pairs [hoare_triple]:
  "<btree t b * \<up>(b \<noteq> None)>
   btree_del_min b
   <\<lambda>r. \<exists>\<^sub>At'. btree t' (snd r) * true * \<up>(fst r # in_traverse_pairs t' = in_traverse_pairs t)>"
@proof
  @induct t arbitrary b @with
    @subgoal "t = tree.Node l x v r" @case "l = Tip" @endgoal
  @end
@qed

definition btree_del_elt :: "('a::heap, 'b::heap) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_del_elt b = (case b of
     None \<Rightarrow> raise ''del_elt: empty tree''
   | Some p \<Rightarrow> do {
       t \<leftarrow> !p;
       (if lsub t = None then return (rsub t)
        else if rsub t = None then return (lsub t)
        else do {
          r \<leftarrow> btree_del_min (rsub t);
          p := Node (lsub t) (fst (fst r)) (snd (fst r)) (snd r);
          return (Some p) }) })"
declare btree_del_elt_def [sep_proc_defs]

lemma btree_del_elt_in_traverse [hoare_triple]:
  "<btree (tree.Node lt x v rt) b>
   btree_del_elt b
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * true * \<up>(in_traverse t' = in_traverse lt @ in_traverse rt)>"
@proof @case "lt = Tip" @then @case "rt = Tip" @qed

lemma btree_del_elt_in_traverse_pairs [hoare_triple]:
  "<btree (tree.Node lt x v rt) b>
   btree_del_elt b
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * true * \<up>(in_traverse_pairs t' = in_traverse_pairs lt @ in_traverse_pairs rt)>"
@proof @case "lt = Tip" @then @case "rt = Tip" @qed

partial_function (heap) btree_delete ::
  "'a::{heap,linorder} \<Rightarrow> ('a, 'b::heap) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_delete x b = (case b of
     None \<Rightarrow> return None
   | Some p \<Rightarrow> do {
      t \<leftarrow> !p;
      (if x = key t then do {
         r \<leftarrow> btree_del_elt b;
         return r }
       else if x < key t then do {
         q \<leftarrow> btree_delete x (lsub t);
         p := Node q (key t) (val t) (rsub t);
         return (Some p) }
       else do {
         q \<leftarrow> btree_delete x (rsub t);
         p := Node (lsub t) (key t) (val t) q;
         return (Some p)}) })"
declare btree_delete.simps [sep_proc_defs]

lemma btree_delete_in_traverse [hoare_triple]:
  "<btree t b * \<up>(tree_sorted t)>
   btree_delete x b
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * true * \<up>(in_traverse t' = remove_elt_list x (in_traverse t))>"
@proof @induct t arbitrary b @qed

lemma btree_delete_in_traverse_pairs [hoare_triple]:
  "<btree t b * \<up>(tree_sorted t)>
   btree_delete x b
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * true * \<up>(in_traverse_pairs t' = remove_elt_pairs x (in_traverse_pairs t))>"
@proof @induct t arbitrary b @qed

declare btree_delete.simps [sep_proc_defs del]
lemma btree_delete_sorted_rule [hoare_triple]:
  "<btree t b * \<up>(tree_sorted t)>
   btree_delete x b
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * true * \<up>(tree_sorted t')>" by auto2

lemma btree_delete_set_rule [hoare_triple]:
  "<btree t b * \<up>(tree_sorted t)>
   btree_delete x b
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * true * \<up>(tree_set t' = tree_set t - {x})>" by auto2

lemma btree_delete_map_rule [hoare_triple]:
  "<btree t b * \<up>(tree_sorted t)>
   btree_delete x b
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * true * \<up>(tree_map t' = delete_map x (tree_map t))>" by auto2

partial_function (heap) btree_search ::
  "'a::{heap,linorder} \<Rightarrow> ('a, 'b::heap) btree \<Rightarrow> 'b option Heap" where
  "btree_search x b = (case b of
     None \<Rightarrow> return None
   | Some p \<Rightarrow> do {
      t \<leftarrow> !p;
      (if x = key t then return (Some (val t))
       else if x < key t then btree_search x (lsub t)
       else btree_search x (rsub t)) })"
declare btree_search.simps [sep_proc_defs]

lemma btree_search_correct [hoare_triple]:
  "<btree t b * \<up>(tree_sorted t)>
   btree_search x b
   <\<lambda>r. btree t b * \<up>(r = (tree_map t)\<langle>x\<rangle>)>"
@proof @induct t arbitrary b @qed
declare btree_search.simps [sep_proc_defs del]

section {* Outer interface *}

definition btree_set :: "'a set \<Rightarrow> ('a::{heap,linorder}, 'b::heap) node ref option \<Rightarrow> assn" where
  "btree_set S p = (\<exists>\<^sub>At. btree t p * \<up>(tree_sorted t) * \<up>(S = tree_set t))"
setup {* add_rewrite_ent_rule @{thm btree_set_def} *}

definition btree_map :: "('a, 'b) map \<Rightarrow> ('a::{heap,linorder}, 'b::heap) node ref option \<Rightarrow> assn" where
  "btree_map M p = (\<exists>\<^sub>At. btree t p * \<up>(tree_sorted t) * \<up>(M = tree_map t))"
setup {* add_rewrite_ent_rule @{thm btree_map_def} *}

declare tree_empty_def [sep_proc_defs del]

lemma btree_empty_rule1:
  "<emp> tree_empty <btree_set {}>" by auto2

lemma btree_empty_rule2:
  "<emp> tree_empty <btree_map empty_map>" by auto2

lemma btree_insert_rule1:
  "<btree_set S b> btree_insert k v b <btree_set ({k} \<union> S)>" by auto2

lemma btree_insert_rule2:
  "<btree_map M b> btree_insert k v b <btree_map (M {k \<rightarrow> v})>" by auto2

lemma btree_delete_rule1:
  "<btree_set S b> btree_delete x b <btree_set (S - {x})>\<^sub>t" by auto2

lemma btree_delete_rule2:
  "<btree_map M b> btree_delete x b <btree_map (delete_map x M)>\<^sub>t" by auto2

lemma btree_search_rule:
  "<btree_map M b> btree_search x b <\<lambda>r. btree_map M b * \<up>(r = M\<langle>x\<rangle>)>" by auto2

end
