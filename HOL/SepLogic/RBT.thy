(* Red-black trees. *)

theory RBT
imports SepAuto "../DataStrs/RBT_Base"
begin

section {* Tree nodes *}

datatype ('a, 'b) rbt_node =
  Node (lsub: "('a, 'b) rbt_node ref option") (cl: color) (key: 'a) (val: 'b) (rsub: "('a, 'b) rbt_node ref option")
setup {* fold add_rewrite_rule @{thms rbt_node.sel} *}
setup {* add_forward_prfstep (equiv_forward_th @{thm rbt_node.simps(1)}) *}

fun color_encode :: "color \<Rightarrow> nat" where
  "color_encode B = 0"
| "color_encode R = 1"

instance color :: heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "color_encode"])
  apply (metis color_encode.simps(1) color_encode.simps(2) not_B zero_neq_one)
  ..

fun rbt_node_encode :: "('a::heap, 'b::heap) rbt_node \<Rightarrow> nat" where
  "rbt_node_encode (Node l c k v r) = to_nat (l, c, k, v, r)"

instance rbt_node :: (heap, heap) heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "rbt_node_encode"])
  apply (case_tac x, simp_all, case_tac y, simp_all)
  ..

fun btree :: "('a::heap, 'b::heap) pre_rbt \<Rightarrow> ('a, 'b) rbt_node ref option \<Rightarrow> assn" where
  "btree Leaf p = \<up>(p = None)"
| "btree (pre_rbt.Node lt c k v rt) (Some p) = (\<exists>\<^sub>Alp rp. p \<mapsto>\<^sub>r Node lp c k v rp * btree lt lp * btree rt rp)"
| "btree (pre_rbt.Node lt c k v rt) None = false"
setup {* fold add_rewrite_ent_rule @{thms btree.simps} *}

lemma btree_Leaf [forward_ent_shadow]: "btree Leaf p \<Longrightarrow>\<^sub>A \<up>(p = None)" by auto2

lemma btree_Node [forward_ent_shadow]:
  "btree (pre_rbt.Node lt c k v rt) (Some p) \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Alp rp. p \<mapsto>\<^sub>r Node lp c k v rp * btree lt lp * btree rt rp)" by auto2

lemma btree_Leaf_some [forward_ent]: "btree Leaf (Some p) \<Longrightarrow>\<^sub>A false" by auto2

lemma btree_Node_none [forward_ent]: "btree (pre_rbt.Node lt c k v rt) None \<Longrightarrow>\<^sub>A false" by auto2

lemma btree_is_some [forward_ent]: "btree (pre_rbt.Node lt c k v rt) q \<Longrightarrow>\<^sub>A true * \<up>(q \<noteq> None)" by auto2

lemma btree_is_not_leaf [forward_ent]: "btree t (Some p) \<Longrightarrow>\<^sub>A true * \<up>(t \<noteq> Leaf)" by auto2

lemma btree_none: "emp \<Longrightarrow>\<^sub>A btree Leaf None" by auto2

lemma btree_constr_ent:
  "p \<mapsto>\<^sub>r Node lp c k v rp * btree lt lp * btree rt rp \<Longrightarrow>\<^sub>A btree (pre_rbt.Node lt c k v rt) (Some p)" by auto2

setup {* fold add_entail_matcher [@{thm btree_none}, @{thm btree_constr_ent}] *}

lemma btree_prec [sep_prec_thms]:
  "h \<Turnstile> btree t p * F1 \<Longrightarrow> h \<Turnstile> btree t' p * F2 \<Longrightarrow> t = t'"
  by (tactic {* auto2s_tac @{context}
    (INDUCT ("t", Arbitraries ["p", "t'", "F1", "F2"]) THEN CASE "t' = Leaf") *})

setup {* fold del_prfstep_thm @{thms btree.simps} *}

type_synonym ('a, 'b) btree = "('a, 'b) rbt_node ref option"

section {* Operations *}

subsection {* Basic operations *}

definition tree_empty :: "('a, 'b) btree Heap" where
  "tree_empty \<equiv> return None"
declare tree_empty_def [sep_proc_defs]

lemma tree_empty_rule [hoare_triple]:
  "<emp> tree_empty <btree Leaf>" by auto2

definition tree_is_empty :: "('a, 'b) btree \<Rightarrow> bool Heap" where
  "tree_is_empty b \<equiv> return (b = None)"
declare tree_is_empty_def [sep_proc_defs]

lemma tree_is_empty_rule:
  "<btree t b> tree_is_empty b <\<lambda>r. btree t b * \<up>(r \<longleftrightarrow> t = Leaf)>" by auto2

definition btree_constr :: "('a::heap, 'b::heap) btree \<Rightarrow> color \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_constr lp c k v rp = do { p \<leftarrow> ref (Node lp c k v rp); return (Some p) }"
declare btree_constr_def [sep_proc_defs]

lemma btree_constr_rule [hoare_triple, resolve]:
  "<btree lt lp * btree rt rp> btree_constr lp c k v rp <btree (pre_rbt.Node lt c k v rt)>" by auto2

partial_function (heap) extract_tree ::
  "('a::heap, 'b::heap) btree \<Rightarrow> ('a, 'b) pre_rbt Heap" where
  "extract_tree p = (case p of
     None \<Rightarrow> return Leaf
   | Some pp \<Rightarrow> do {
      t \<leftarrow> !pp;
      lt \<leftarrow> extract_tree (lsub t);
      rt \<leftarrow> extract_tree (rsub t);
      return (pre_rbt.Node lt (cl t) (key t) (val t) rt)
    })"
declare extract_tree.simps [sep_proc_defs]

theorem extract_tree_rule [hoare_triple_direct]:
  "<btree t p> extract_tree p <\<lambda>r. btree t p * \<up>(r = t)>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("t", Arbitraries ["p"])) *})

definition set_color :: "color \<Rightarrow> ('a::heap, 'b::heap) btree \<Rightarrow> unit Heap" where
  "set_color c p = (case p of
    None \<Rightarrow> raise ''set_color''
  | Some pp \<Rightarrow> do {
      t \<leftarrow> !pp;
      pp := Node (lsub t) c (key t) (val t) (rsub t)
    })"
declare set_color_def [sep_proc_defs]

theorem set_color_rule [hoare_triple]:
  "<btree (pre_rbt.Node a c x v b) p>
   set_color c' p
   <\<lambda>r. btree (pre_rbt.Node a c' x v b) p>" by auto2

subsection {* Rotation *}

definition btree_rotate_l :: "('a::heap, 'b::heap) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_rotate_l p = (case p of
    None \<Rightarrow> raise ''Empty btree''
  | Some pp \<Rightarrow> do {
     t \<leftarrow> !pp;
     (case rsub t of
        None \<Rightarrow> raise ''Empty rsub''
      | Some rp \<Rightarrow> do {
          rt \<leftarrow> !rp;
          pp := Node (lsub t) (cl t) (key t) (val t) (lsub rt);
          rp := Node p (cl rt) (key rt) (val rt) (rsub rt);
          return (rsub t) })})"
declare btree_rotate_l_def [sep_proc_defs]

lemma btree_rotate_l_rule [hoare_triple]:
  "<btree (pre_rbt.Node a c1 x v (pre_rbt.Node b c2 y w c)) p>
   btree_rotate_l p
   <btree (pre_rbt.Node (pre_rbt.Node a c1 x v b) c2 y w c)>" by auto2

definition btree_rotate_r :: "('a::heap, 'b::heap) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_rotate_r p = (case p of
    None \<Rightarrow> raise ''Empty btree''
  | Some pp \<Rightarrow> do {
     t \<leftarrow> !pp;
     (case lsub t of
        None \<Rightarrow> raise ''Empty lsub''
      | Some lp \<Rightarrow> do {
          lt \<leftarrow> !lp;
          pp := Node (rsub lt) (cl t) (key t) (val t) (rsub t);
          lp := Node (lsub lt) (cl lt) (key lt) (val lt) p;
          return (lsub t) })})"
declare btree_rotate_r_def [sep_proc_defs]

lemma btree_rotate_r_rule [hoare_triple]:
  "<btree (pre_rbt.Node (pre_rbt.Node a c1 x v b) c2 y w c) p>
   btree_rotate_r p
   <btree (pre_rbt.Node a c1 x v (pre_rbt.Node b c2 y w c))>" by auto2

section {* Definition of functions *}

definition get_cl :: "('a::heap, 'b::heap) btree \<Rightarrow> color Heap" where
  "get_cl p = (case p of
     None \<Rightarrow> return B
   | Some pp \<Rightarrow> do {
       t \<leftarrow> !pp;
       return (cl t)
     })"
declare get_cl_def [sep_proc_defs]

theorem get_cl_heap_preserving [heap_presv_thms]:
  "heap_preserving (get_cl p)"
  by (tactic {* auto2s_tac @{context} (CASE "p = None") *})

theorem get_cl_rule [hoare_triple_direct]:
  "<btree t p> get_cl p <\<lambda>r. btree t p * \<up>(r = pre_rbt.cl t)>" by auto2

definition btree_balanceR :: "('a::heap, 'b::heap) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_balanceR p = (case p of None \<Rightarrow> return None | Some pp \<Rightarrow> do {
     t \<leftarrow> !pp;
     if cl t = R then return p
     else do {
       cl_r \<leftarrow> get_cl (rsub t);
       if cl_r = R then do {
          rt \<leftarrow> !(the (rsub t));
          cl_lr \<leftarrow> get_cl (lsub rt);
          cl_rr \<leftarrow> get_cl (rsub rt);
          if cl_lr = R then do {
            rp' \<leftarrow> btree_rotate_r (rsub t);
            pp := Node (lsub t) (cl t) (key t) (val t) rp';
            p' \<leftarrow> btree_rotate_l p;
            t' \<leftarrow> !(the p');
            set_color B (rsub t');
            return p'
          } else if cl_rr = R then do {
            p' \<leftarrow> btree_rotate_l p;
            t' \<leftarrow> !(the p');
            set_color B (rsub t');
            return p'
          } else return p }
       else return p
     }})"
declare btree_balanceR_def [sep_proc_defs]

definition btree_balance :: "('a::heap, 'b::heap) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_balance p = (case p of None \<Rightarrow> return None | Some pp \<Rightarrow> do {
     t \<leftarrow> !pp;
     if cl t = R then return p
     else do {
       cl_l \<leftarrow> get_cl (lsub t);
       if cl_l = R then do {
          lt \<leftarrow> !(the (lsub t));
          cl_rl \<leftarrow> get_cl (rsub lt);
          cl_ll \<leftarrow> get_cl (lsub lt);
          if cl_rl = R then do {
            lp' \<leftarrow> btree_rotate_l (lsub t);
            pp := Node lp' (cl t) (key t) (val t) (rsub t);
            p' \<leftarrow> btree_rotate_r p;
            t' \<leftarrow> !(the p');
            set_color B (lsub t');
            return p'
          } else if cl_ll = R then do {
            p' \<leftarrow> btree_rotate_r p;
            t' \<leftarrow> !(the p');
            set_color B (lsub t');
            return p'
          } else btree_balanceR p }
       else do {
         p' \<leftarrow> btree_balanceR p;
         return p'
       }
     }})"
declare btree_balance_def [sep_proc_defs]

partial_function (heap) rbt_ins ::
  "'a::{heap,ord} \<Rightarrow> 'b::heap \<Rightarrow> ('a, 'b) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "rbt_ins k v p = (case p of
     None \<Rightarrow> btree_constr None R k v None
   | Some pp \<Rightarrow> do {
      t \<leftarrow> !pp;
      (if k = key t then do {
         pp := Node (lsub t) (cl t) k v (rsub t);
         return (Some pp) }
       else if k < key t then do {
         q \<leftarrow> rbt_ins k v (lsub t);
         pp := Node q (cl t) (key t) (val t) (rsub t);
         btree_balance p }
       else do {
         q \<leftarrow> rbt_ins k v (rsub t);
         pp := Node (lsub t) (cl t) (key t) (val t) q;
         btree_balance p })} )"
declare rbt_ins.simps [sep_proc_defs]

definition rbt_insert :: "'a::{heap,ord} \<Rightarrow> 'b::heap \<Rightarrow> ('a, 'b) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "rbt_insert k v p = do {
    p' \<leftarrow> rbt_ins k v p;
    set_color B p';
    return p' }"
declare rbt_insert_def [sep_proc_defs]

section {* Preservation of black-depth *}

theorem balanceR_bd [hoare_triple]:
  "<btree t p * \<up>(bd_inv t)>
   btree_balanceR p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(bd_inv t') * \<up>(black_depth t' = black_depth t)>"
  by auto2

theorem balance_bd [hoare_triple]:
  "<btree t p * \<up>(bd_inv t)>
   btree_balance p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(bd_inv t') * \<up>(black_depth t' = black_depth t)>"
  by auto2

theorem ins_bd [hoare_triple]:
  "<btree t p * \<up>(bd_inv t)>
   rbt_ins k v p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(bd_inv t') * \<up>(black_depth t' = black_depth t)>"
  by (tactic {* auto2s_tac @{context} (
    INDUCT ("t", Arbitraries ["p"]) THEN CASE "pre_rbt.cl t = R") *})

setup {* fold del_prfstep_thm [@{thm balanceR_bd}, @{thm balance_bd}] *}

section {* Preservation of cl invariant *}

theorem balanceR_cl [hoare_triple]:
  "<btree (pre_rbt.Node lt B k v rt) p * \<up>(cl_inv lt) * \<up>(cl_inv' rt)>
   btree_balanceR p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(cl_inv t')>"
  by auto2

theorem balance_cl1 [hoare_triple]:
  "<btree (pre_rbt.Node lt B k v rt) p * \<up>(cl_inv' lt) * \<up>(cl_inv rt)>
   btree_balance p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(cl_inv t')>"
  by auto2

theorem balance_cl2 [hoare_triple]:
  "<btree (pre_rbt.Node lt B k v rt) p * \<up>(cl_inv lt) * \<up>(cl_inv' rt)>
   btree_balance p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(cl_inv t')>"
  by auto2

theorem balanceR_non_leaf [hoare_triple]:
  "<btree (pre_rbt.Node lt c k v rt) p>
    btree_balanceR p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(t' \<noteq> Leaf)>"
  by auto2

theorem balance_non_leaf [hoare_triple]:
  "<btree (pre_rbt.Node lt c k v rt) p>
    btree_balance p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(t' \<noteq> Leaf)>"
  by auto2

theorem balance_on_R [hoare_triple]:
  "<btree (pre_rbt.Node lt R k v rt) p>
   btree_balance p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(t' = pre_rbt.Node lt R k v rt)>"
  by auto2

theorem ins_non_leaf [hoare_triple]:
  "<btree t p> rbt_ins k v p <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(t' \<noteq> Leaf)>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("t", Arbitraries ["p"])) *})

theorem ins_cl [hoare_triple]:
  "<btree t p * \<up>(cl_inv t)>
   rbt_ins k v p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(if pre_rbt.cl t = B then cl_inv t' else pre_rbt.cl t' = R \<and> cl_inv' t')>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("t", Arbitraries ["p"])) *})

section {* Insert function *}

theorem insert_is_rbt [hoare_triple]:
  "<btree t p * \<up>(is_rbt t)>
   rbt_insert k v p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(is_rbt t')>" by auto2

(* insert_is_rbt is all we need, so we can clear out bd and cl properties. *)
setup {* fold del_prfstep_thm [
  @{thm balanceR_cl}, @{thm balance_cl1}, @{thm balance_cl2}, @{thm ins_bd}, @{thm ins_cl}] *}

section {* sortedness on RBT, mapping associated to RBT *}

theorem balanceR_in_traverse_pairs [hoare_triple]:
  "<btree t p>
   btree_balanceR p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(rbt_in_traverse_pairs t' = rbt_in_traverse_pairs t)>"
  by auto2

theorem balance_in_traverse_pairs [hoare_triple]:
  "<btree t p>
   btree_balance p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(rbt_in_traverse_pairs t' = rbt_in_traverse_pairs t)>"
  by auto2

declare btree_balance_def [sep_proc_defs del]

theorem ins_inorder_pairs [hoare_triple]:
  "<btree t p * \<up>(rbt_sorted t)>
   rbt_ins k v p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(rbt_in_traverse_pairs t' = ordered_insert_pairs k v (rbt_in_traverse_pairs t))>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("t", Arbitraries ["p"])) *})

theorem insert_inorder_pairs [hoare_triple]:
  "<btree t p * \<up>(rbt_sorted t)>
   rbt_insert k v p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(rbt_in_traverse_pairs t' = ordered_insert_pairs k v (rbt_in_traverse_pairs t))>"
  by auto2

declare rbt_insert_def [sep_proc_defs del]

theorem insert_sorted [hoare_triple]:
  "<btree t p * \<up>(rbt_sorted t)>
   rbt_insert k v p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(rbt_sorted t')>" by auto2

theorem insert_tree_map [hoare_triple]:
  "<btree t p * \<up>(rbt_sorted t)>
   rbt_insert k v p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(rbt_map t' = (rbt_map t) {k \<rightarrow> v})>" by auto2

section {* Search function *}

partial_function (heap) rbt_search ::
  "'a::{heap,linorder} \<Rightarrow> ('a, 'b::heap) btree \<Rightarrow> 'b option Heap" where
  "rbt_search x b = (case b of
     None \<Rightarrow> return None
   | Some p \<Rightarrow> do {
      t \<leftarrow> !p;
      (if x = key t then return (Some (val t))
       else if x < key t then rbt_search x (lsub t)
       else rbt_search x (rsub t)) })"
declare rbt_search.simps [sep_proc_defs]

lemma btree_search_correct [hoare_triple]:
  "<btree t b * \<up>(rbt_sorted t)>
   rbt_search x b
   <\<lambda>r. btree t b * \<up>(r = (rbt_map t)\<langle>x\<rangle>)>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("t", Arbitraries ["b"])) *})
declare rbt_search.simps [sep_proc_defs del]

section {* Outer interface *}

definition rbt_set_assn :: "'a set \<Rightarrow> ('a::{heap,linorder}, 'b::heap) rbt_node ref option \<Rightarrow> assn" where
  "rbt_set_assn S p = (\<exists>\<^sub>At. btree t p * \<up>(is_rbt t) * \<up>(rbt_sorted t) * \<up>(S = rbt_set t))"
setup {* add_rewrite_ent_rule @{thm rbt_set_assn_def} *}

definition rbt_map_assn :: "('a, 'b) map \<Rightarrow> ('a::{heap,linorder}, 'b::heap) rbt_node ref option \<Rightarrow> assn" where
  "rbt_map_assn M p = (\<exists>\<^sub>At. btree t p * \<up>(is_rbt t) * \<up>(rbt_sorted t) * \<up>(M = rbt_map t))"
setup {* add_rewrite_ent_rule @{thm rbt_map_assn_def} *}

declare tree_empty_def [sep_proc_defs del]

lemma rbt_empty_rule1:
  "<emp> tree_empty <rbt_set_assn {}>" by auto2

lemma rbt_empty_rule2:
  "<emp> tree_empty <rbt_map_assn empty_map>" by auto2

declare rbt_insert_def [sep_proc_defs del]

lemma rbt_insert_rule1:
  "<rbt_set_assn S b> rbt_insert k v b <rbt_set_assn ({k} \<union> S)>" by auto2

lemma rbt_insert_rule2:
  "<rbt_map_assn M b> rbt_insert k v b <rbt_map_assn (M {k \<rightarrow> v})>" by auto2

lemma rbt_search:
  "<rbt_map_assn M b> rbt_search x b <\<lambda>r. rbt_map_assn M b * \<up>(r = M\<langle>x\<rangle>)>" by auto2

end
