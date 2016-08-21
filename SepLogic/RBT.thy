(* Red-black trees. *)

theory RBT
imports SepAuto Mapping
begin

section {* Abstract red-black trees *}

datatype color = R | B

datatype ('a, 'b) rbt =
  Leaf | Node (lsub: "('a, 'b) rbt") (cl: color) (key: 'a) (val: 'b) (rsub: "('a, 'b) rbt")
where
  "cl Leaf = B"

setup {* add_resolve_prfstep @{thm color.distinct(1)} *}
setup {* add_resolve_prfstep @{thm rbt.distinct(2)} *}
setup {* fold add_rewrite_rule @{thms rbt.sel} *}
setup {* add_forward_prfstep (equiv_forward_th (@{thm rbt.simps(1)})) *}

text {* Case checking for trees: first verify the Tip case, then can assume t is
  in the form Node l c k v r. *}

setup {* add_gen_prfstep ("rbt_case_intro",
  [WithTerm @{term_pat "?t::(?'a, ?'b) rbt"},
   Filter (unique_free_filter "t"),
   CreateCase @{term_pat "(?t::(?'a, ?'b) rbt) = Leaf"}]) *}
setup {* add_forward_prfstep_cond @{thm rbt.collapse} [with_cond "?rbt \<noteq> Node ?l ?c ?k ?v ?r"] *}

text {* Induction on trees: after checking Tip case, can assume P (lsub t)
  and P (rsub t) holds when trying to prove P t. *}

theorem rbt_induct': "P Leaf \<Longrightarrow> (\<forall>t. P (lsub t) \<and> P (rsub t) \<longrightarrow> P t) \<Longrightarrow> P t"
  apply (induction t) apply blast by (metis rbt.sel(1) rbt.sel(6))
setup {* add_prfstep_induction @{thm rbt_induct'} *}

subsection {* Some trivial lemmas *}

theorem not_R [forward]: "c \<noteq> R \<Longrightarrow> c = B" using color.exhaust by blast
theorem not_B [forward]: "c \<noteq> B \<Longrightarrow> c = R" using color.exhaust by blast
theorem red_not_leaf [forward]: "cl t = R \<Longrightarrow> t \<noteq> Leaf" by auto

subsection {* Definition of main functions and invariants *}

fun min_depth :: "('a, 'b) rbt \<Rightarrow> nat" where
  "min_depth Leaf = 0"
| "min_depth (Node l c k v r) = min (min_depth l) (min_depth r) + 1"

fun max_depth :: "('a, 'b) rbt \<Rightarrow> nat" where
  "max_depth Leaf = 0"
| "max_depth (Node l c k v r) = max (max_depth l) (max_depth r) + 1"

fun black_depth :: "('a, 'b) rbt \<Rightarrow> nat" where
  "black_depth Leaf = 0"
| "black_depth (Node l R k v r) = min (black_depth l) (black_depth r)"
| "black_depth (Node l B k v r) = min (black_depth l) (black_depth r) + 1"

fun cl_inv :: "('a, 'b) rbt \<Rightarrow> bool" where
  "cl_inv Leaf = True"
| "cl_inv (Node l R k v r) = (cl_inv l \<and> cl_inv r \<and> cl l = B \<and> cl r = B)"
| "cl_inv (Node l B k v r) = (cl_inv l \<and> cl_inv r)"

fun bd_inv :: "('a, 'b) rbt \<Rightarrow> bool" where
  "bd_inv Leaf = True"
| "bd_inv (Node l c k v r) = (bd_inv l \<and> bd_inv r \<and> black_depth l = black_depth r)"

definition is_rbt :: "('a, 'b) rbt \<Rightarrow> bool" where
  "is_rbt t = (cl_inv t \<and> bd_inv t)"

setup {* fold add_rewrite_rule (
  @{thms min_depth.simps} @ @{thms max_depth.simps} @ @{thms black_depth.simps} @
  @{thms cl_inv.simps} @ @{thms bd_inv.simps} @ [@{thm is_rbt_def}]) *}
theorem cl_invI: "cl_inv l \<Longrightarrow> cl_inv r \<Longrightarrow> cl_inv (Node l B k v r)" by auto
setup {* add_forward_prfstep_cond @{thm cl_invI} [with_term "cl_inv (Node ?l B ?k ?v ?r)"] *}

subsection {* Properties of bd_inv *}

theorem bd_inv_elimR [rewrite]:
  "bd_inv (Node l R k v r) \<Longrightarrow> black_depth (Node l R k v r) = black_depth l" by auto2
theorem bd_inv_elimB [rewrite]:
  "bd_inv (Node l B k v r) \<Longrightarrow> black_depth (Node l B k v r) = black_depth l + 1" by auto2
theorem bd_inv_intro: "black_depth l = black_depth r \<Longrightarrow> bd_inv l \<Longrightarrow> bd_inv r \<Longrightarrow> bd_inv (Node l c k v r)" by auto2
setup {* add_forward_prfstep_cond @{thm bd_inv_intro} [with_term "Node ?l ?c ?k ?v ?r"] *}

subsection {* is_rbt is recursive *}

theorem is_rbt_rec [forward]: "is_rbt (Node l c k v r) \<Longrightarrow> is_rbt l \<and> is_rbt r"
  by (tactic {* auto2s_tac @{context} (CASE "c = R") *})

subsection {* Balancedness of is_rbt *}

theorem depth_min: "is_rbt t \<Longrightarrow> black_depth t \<le> min_depth t"
  by (tactic {* auto2s_tac @{context}
    (CASE "t = Leaf" THEN
     CASE "cl t = R" WITH
        OBTAIN "black_depth t \<le> min (min_depth (lsub t)) (min_depth (rsub t))") *} )
theorem two_distrib [rewrite]: "(2::nat) * (a + 1) = 2 * a + 2" by simp
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

subsection {* Definition and basic properties of cl_inv' *}

fun cl_inv' :: "('a, 'b) rbt \<Rightarrow> bool" where
  "cl_inv' Leaf = True"
| "cl_inv' (rbt.Node l c k v r) = (cl_inv l \<and> cl_inv r)"
setup {* fold add_rewrite_rule @{thms cl_inv'.simps} *}

theorem cl_inv_B [forward, backward2]: "rbt.cl t = B \<Longrightarrow> cl_inv' t \<Longrightarrow> cl_inv t" by auto2
theorem cl_inv_R [forward]:
  "cl_inv' (rbt.Node l R k v r) \<Longrightarrow> rbt.cl l = B \<Longrightarrow> rbt.cl r = B \<Longrightarrow> cl_inv (rbt.Node l R k v r)" by auto2
theorem cl_inv_imp [forward]: "cl_inv t \<Longrightarrow> cl_inv' t"
  by (tactic {* auto2s_tac @{context} (CASE "rbt.cl t = R") *})
theorem cl_inv'I: "cl_inv l \<Longrightarrow> cl_inv r \<Longrightarrow> cl_inv' (rbt.Node l c k v r)" by auto
setup {* add_forward_prfstep_cond @{thm cl_inv'I} [with_term "cl_inv' (rbt.Node ?l ?c ?k ?v ?r)"] *}

section {* Tree nodes *}

datatype ('a, 'b) rbt_node =
  Node (lsub: "('a, 'b) rbt_node ref option") (cl: color) (key: 'a) (val: 'b) (rsub: "('a, 'b) rbt_node ref option")

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

setup {* fold add_rewrite_rule @{thms rbt_node.sel} *}
theorem rbt_node_constr:
  "Node l c k v r = Node l' c' k' v' r' \<Longrightarrow> l = l' \<and> c = c' \<and> k = k' \<and> v = v' \<and> r = r'" by simp
setup {* add_forward_prfstep @{thm rbt_node_constr} *}

fun btree :: "('a::heap, 'b::heap) rbt \<Rightarrow> ('a, 'b) rbt_node ref option \<Rightarrow> assn" where
  "btree Leaf p = \<up>(p = None)"
| "btree (rbt.Node lt c k v rt) (Some p) = (\<exists>\<^sub>Alp rp. p \<mapsto>\<^sub>r Node lp c k v rp * btree lt lp * btree rt rp)"
| "btree (rbt.Node lt c k v rt) None = false"
setup {* fold add_rewrite_rule @{thms btree.simps} *}

lemma btree_split_iff1 [rewrite]: "btree t None = \<up>(t = Leaf)" by auto2

lemma btree_split_iff2 [forward_ent]:
  "btree (rbt.Node lt c k v rt) (Some p) \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Alp rp. p \<mapsto>\<^sub>r Node lp c k v rp * btree lt lp * btree rt rp)" by auto2

lemma btree_split_elim:
  "\<exists>lp rp. h \<Turnstile> p \<mapsto>\<^sub>r Node lp c k v rp * Ql lp rp \<Longrightarrow> h \<Turnstile> p \<mapsto>\<^sub>r Node lp c k v rp * Q \<Longrightarrow>
   h \<Turnstile> p \<mapsto>\<^sub>r Node lp c k v rp * Ql lp rp" by auto2
setup {* add_gen_prfstep ("btree_split_elim", forward_descs @{thm btree_split_elim} @ [ShadowFirst]) *}

lemma btree_is_some: "h \<Turnstile> btree (rbt.Node lt c k v rt) q * Qu \<Longrightarrow> q \<noteq> None" by auto2
setup {* add_forward_prfstep_cond @{thm btree_is_some} [with_cond "?q \<noteq> None"] *}

lemma btree_constr_ent [forward_ent]:
  "p \<mapsto>\<^sub>r Node lp c k v rp * btree lt lp * btree rt rp \<Longrightarrow>\<^sub>A btree (rbt.Node lt c k v rt) (Some p)" by auto2
setup {* del_prfstep_thm @{thm btree.simps(2)} *}

lemma btree_prec [sep_prec_thms]:
  "h \<Turnstile> btree t p * F1 \<Longrightarrow> h \<Turnstile> btree t' p * F2 \<Longrightarrow> t = t'"
  by (tactic {* auto2s_tac @{context}
    (INDUCT ("t", Arbitraries ["p", "t'", "F1", "F2"]) THEN CASE "t' = Leaf") *})

theorem btree_some [resolve]: "\<not>h \<Turnstile> btree Leaf (Some p) * Ru" by auto2
theorem btree_none [match_code_pos_emp]: "btree Leaf None = emp" by auto2

lemma rbt_is_not_leaf:
  "h \<Turnstile> btree t (Some p) * Qu \<Longrightarrow> t \<noteq> Leaf" by auto2
setup {* add_forward_prfstep_cond @{thm rbt_is_not_leaf} [with_cond "?t \<noteq> rbt.Node ?lt ?c ?k ?v ?rt"] *}

type_synonym ('a, 'b) btree = "('a, 'b) rbt_node ref option"

section {* Operations *}

subsection {* Basic operations *}

definition tree_empty :: "('a, 'b) btree Heap" where
  "tree_empty \<equiv> return None"
declare tree_empty_def [sep_proc_defs]

lemma tree_empty_rule [next_code_pos]:
  "<emp> tree_empty <btree Leaf>" by auto2

definition tree_is_empty :: "('a, 'b) btree \<Rightarrow> bool Heap" where
  "tree_is_empty b \<equiv> return (b = None)"
declare tree_is_empty_def [sep_proc_defs]

lemma tree_is_empty_rule:
  "<btree t b> tree_is_empty b <\<lambda>r. btree t b * \<up>(r \<longleftrightarrow> t = Leaf)>" by auto2

definition btree_constr :: "('a::heap, 'b::heap) btree \<Rightarrow> color \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "btree_constr lp c k v rp = do { p \<leftarrow> ref (Node lp c k v rp); return (Some p) }"
declare btree_constr_def [sep_proc_defs]

lemma btree_constr_rule [next_code_pos, resolve]:
  "<btree lt lp * btree rt rp> btree_constr lp c k v rp <btree (rbt.Node lt c k v rt)>" by auto2

partial_function (heap) extract_tree ::
  "('a::heap, 'b::heap) btree \<Rightarrow> ('a, 'b) rbt Heap" where
  "extract_tree p = (case p of
     None \<Rightarrow> return Leaf
   | Some pp \<Rightarrow> do {
      t \<leftarrow> !pp;
      lt \<leftarrow> extract_tree (lsub t);
      rt \<leftarrow> extract_tree (rsub t);
      return (rbt.Node lt (cl t) (key t) (val t) rt)
    })"
declare extract_tree.simps [sep_proc_defs]

theorem extract_tree_rule [next_code_pos_direct]:
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

theorem set_color_rule [next_code_pos]:
  "<btree (rbt.Node a c x v b) p>
   set_color c' p
   <\<lambda>r. btree (rbt.Node a c' x v b) p>" by auto2

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

lemma btree_rotate_l_rule [next_code_pos]:
  "<btree (rbt.Node a c1 x v (rbt.Node b c2 y w c)) p>
   btree_rotate_l p
   <btree (rbt.Node (rbt.Node a c1 x v b) c2 y w c)>" by auto2

definition btree_rotate_l_at_l :: "('a::heap, 'b::heap) btree \<Rightarrow> unit Heap" where
  "btree_rotate_l_at_l p = (case p of
    None \<Rightarrow> raise ''rotate_l_at_l''
  | Some pp \<Rightarrow> do {
      t \<leftarrow> !pp;
      p' \<leftarrow> btree_rotate_l (lsub t);
      pp := Node p' (cl t) (key t) (val t) (rsub t)
    })"
declare btree_rotate_l_at_l_def [sep_proc_defs]

lemma btree_rotate_l_at_l_rule [next_code_pos]:
  "<btree (rbt.Node (rbt.Node a c2 k2 v2 (rbt.Node b c3 k3 v3 c)) c1 k1 v1 d) p>
   btree_rotate_l_at_l p
   <\<lambda>_. btree (rbt.Node (rbt.Node (rbt.Node a c2 k2 v2 b) c3 k3 v3 c) c1 k1 v1 d) p>" by auto2

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

lemma btree_rotate_r_rule [next_code_pos]:
  "<btree (rbt.Node (rbt.Node a c1 x v b) c2 y w c) p>
   btree_rotate_r p
   <btree (rbt.Node a c1 x v (rbt.Node b c2 y w c))>" by auto2

definition btree_rotate_r_at_r :: "('a::heap, 'b::heap) btree \<Rightarrow> unit Heap" where
  "btree_rotate_r_at_r p = (case p of
    None \<Rightarrow> raise ''rotate_r_at_r''
  | Some pp \<Rightarrow> do {
      t \<leftarrow> !pp;
      p' \<leftarrow> btree_rotate_r (rsub t);
      pp := Node (lsub t) (cl t) (key t) (val t) p'
    })"
declare btree_rotate_r_at_r_def [sep_proc_defs]

lemma btree_rotate_r_at_r_rule [next_code_pos]:
  "<btree (rbt.Node a c1 k1 v1 (rbt.Node (rbt.Node b c2 k2 v2 c) c3 k3 v3 d)) p>
   btree_rotate_r_at_r p
   <\<lambda>_. btree (rbt.Node a c1 k1 v1 (rbt.Node b c2 k2 v2 (rbt.Node c c3 k3 v3 d))) p>" by auto2

section {* Balancing *}

definition get_cl :: "('a::heap, 'b::heap) btree \<Rightarrow> color Heap" where
  "get_cl p = (case p of
     None \<Rightarrow> return B
   | Some pp \<Rightarrow> do {
       t \<leftarrow> !pp;
       return (cl t)
     })"
declare get_cl_def [sep_proc_defs]

theorem get_cl_heap_preserving [sep_heap_presv_thms, heap_presv_thms]:
  "heap_preserving (get_cl p)"
  by (tactic {* auto2s_tac @{context} (CASE "p = None") *})

theorem get_cl_rule [next_code_pos_direct]:
  "<btree t p> get_cl p <\<lambda>r. btree t p * \<up>(r = rbt.cl t)>" by auto2

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
            btree_rotate_r_at_r p;
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

theorem balanceR_bd [next_code_pos]:
  "<btree t p * \<up>(bd_inv t)>
   btree_balanceR p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(bd_inv t') * \<up>(black_depth t' = black_depth t)>"
  by auto2

theorem balanceR_cl [next_code_pos]:
  "<btree (rbt.Node lt B k v rt) p * \<up>(cl_inv lt) * \<up>(cl_inv' rt)>
   btree_balanceR p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(cl_inv t')>"
  by auto2

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
            btree_rotate_l_at_l p;
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

theorem balance_bd [next_code_pos]:
  "<btree t p * \<up>(bd_inv t)>
   btree_balance p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(bd_inv t') * \<up>(black_depth t' = black_depth t)>"
   by auto2

theorem balance_cl1 [next_code_pos]:
  "<btree (rbt.Node lt B k v rt) p * \<up>(cl_inv' lt) * \<up>(cl_inv rt)>
   btree_balance p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(cl_inv t')>"
   by auto2

theorem balance_cl2 [next_code_pos]:
  "<btree (rbt.Node lt B k v rt) p * \<up>(cl_inv lt) * \<up>(cl_inv' rt)>
   btree_balance p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(cl_inv t')>"
   by auto2

theorem balanceR_non_leaf [next_code_pos]:
  "<btree (rbt.Node lt c k v rt) p>
    btree_balanceR p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(t' \<noteq> Leaf)>"
   by auto2

theorem balance_non_leaf [next_code_pos]:
  "<btree (rbt.Node lt c k v rt) p>
    btree_balance p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(t' \<noteq> Leaf)>"
   by auto2

theorem balance_on_R [next_code_pos]:
  "<btree (rbt.Node lt R k v rt) p>
   btree_balance p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(t' = rbt.Node lt R k v rt)>" by auto2

section {* ins function *}

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

theorem ins_non_leaf [next_code_pos]:
  "<btree t p> rbt_ins k v p <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(t' \<noteq> Leaf)>"
   by (tactic {* auto2s_tac @{context} (INDUCT ("t", Arbitraries ["p"])) *})

theorem ins_bd [next_code_pos]:
  "<btree t p * \<up>(bd_inv t)>
   rbt_ins k v p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(bd_inv t') * \<up>(black_depth t' = black_depth t)>"
   by (tactic {* auto2s_tac @{context} (
     INDUCT ("t", Arbitraries ["p"]) THEN CASE "rbt.cl t = R") *})

theorem ins_cl [next_code_pos]:
  "<btree t p * \<up>(cl_inv t)>
   rbt_ins k v p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(if rbt.cl t = B then cl_inv t' else rbt.cl t' = R \<and> cl_inv' t')>"
   by (tactic {* auto2s_tac @{context} (INDUCT ("t", Arbitraries ["p"])) *})

section {* Insert function *}

definition rbt_insert :: "'a::{heap,ord} \<Rightarrow> 'b::heap \<Rightarrow> ('a, 'b) btree \<Rightarrow> ('a, 'b) btree Heap" where
  "rbt_insert k v p = do {
    p' \<leftarrow> rbt_ins k v p;
    set_color B p';
    return p' }"
declare rbt_insert_def [sep_proc_defs]

theorem insert_is_rbt [next_code_pos]:
  "<btree t p * \<up>(is_rbt t)>
   rbt_insert k v p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(is_rbt t')>" by auto2

(* insert_is_rbt is all we need, so we can clear out bd and cl properties. *)
setup {* fold del_prfstep_thm [
  @{thm balanceR_bd}, @{thm balanceR_cl}, @{thm balance_bd},
  @{thm balance_cl1}, @{thm balance_cl2}, @{thm ins_bd}, @{thm ins_cl}] *}

section {* Set of keys and mapping associated to an RBT, sortedness on RBT *}

fun rbt_key_set :: "('a, 'b) rbt \<Rightarrow> 'a set" where
  "rbt_key_set Leaf = {}"
| "rbt_key_set (rbt.Node lt c k v rt) = {k} \<union> rbt_key_set lt \<union> rbt_key_set rt"
setup {* fold add_rewrite_rule @{thms rbt_key_set.simps} *}

fun rbt_sorted :: "('a::linorder, 'b) rbt \<Rightarrow> bool" where
  "rbt_sorted Leaf = True"
| "rbt_sorted (rbt.Node lt c k v rt) =
   ((\<forall>x\<in>rbt_key_set lt. x < k) \<and> (\<forall>x\<in>rbt_key_set rt. k < x) \<and> rbt_sorted lt \<and> rbt_sorted rt)"
setup {* fold add_rewrite_rule @{thms rbt_sorted.simps} *}

lemma rbt_sorted_on_left [forward]:
  "rbt_sorted (rbt.Node (rbt.Node a c1 x v b) c2 y w c) \<Longrightarrow> x < y" by auto2 

lemma rbt_sorted_on_right [forward]:
  "rbt_sorted (rbt.Node a c1 x v (rbt.Node b c2 y w c)) \<Longrightarrow> x < y" by auto2

fun tree_map :: "('a::linorder, 'b) rbt \<Rightarrow> ('a, 'b) map" where
  "tree_map Leaf = Map (\<lambda>x. None)"
| "tree_map (rbt.Node lt c k v rt) = binary_map k v (tree_map lt) (tree_map rt)"
setup {* fold add_rewrite_rule @{thms tree_map.simps} *}

(* Sortedness and preservation of set of keys is best proved by
   introducing in-order traversal. *)
fun rbt_in_traverse :: "('a, 'b) rbt \<Rightarrow> 'a list" where
  "rbt_in_traverse Leaf = []"
| "rbt_in_traverse (rbt.Node lt c k v rt) = (rbt_in_traverse lt) @ [k] @ (rbt_in_traverse rt)"
setup {* fold add_rewrite_rule @{thms rbt_in_traverse.simps} *}

theorem rbt_in_traverse_non_empty:
  "rbt_in_traverse (rbt.Node lt c k v rt) \<noteq> []" by auto2

theorem inorder_preserve_set [rewrite_bidir]:
  "set (rbt_in_traverse t) = rbt_key_set t" by auto2

fun strict_sorted :: "'a::linorder list \<Rightarrow> bool" where
  "strict_sorted [] = True"
| "strict_sorted (x # ys) = ((\<forall>y\<in>set ys. x < y) \<and> strict_sorted ys)"
setup {* fold add_rewrite_rule @{thms strict_sorted.simps} *}

theorem strict_sorted_single [resolve]: "strict_sorted [x]" by auto2
setup {* del_prfstep_thm @{thm strict_sorted.simps(2)} #>
  add_rewrite_rule_cond @{thm strict_sorted.simps(2)} [with_cond "?ys \<noteq> []"] *}

theorem strict_sorted_append [rewrite]:
  "strict_sorted (xs @ ys) =
    ((\<forall>x y. x \<in> set xs \<longrightarrow> y \<in> set ys \<longrightarrow> x < y) \<and> strict_sorted xs \<and> strict_sorted ys)"
  by (tactic {* auto2s_tac @{context} (INDUCT ("xs", [])) *})

theorem inorder_sorted [rewrite_bidir]:
  "strict_sorted (rbt_in_traverse t) = rbt_sorted t" by auto2
setup {* del_prfstep_thm @{thm strict_sorted_append} *}

theorem balanceR_in_traverse [next_code_pos]:
  "<btree t p>
   btree_balanceR p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(rbt_in_traverse t' = rbt_in_traverse t)>"
  by auto2

theorem balance_in_traverse [next_code_pos]:
  "<btree t p>
   btree_balance p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(rbt_in_traverse t' = rbt_in_traverse t)>"
  by auto2

declare btree_balance_def [sep_proc_defs del]
theorem balance_sorted [next_code_pos]:
  "<btree t p * \<up>(rbt_sorted t)>
   btree_balance p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(rbt_sorted t')>"
  by auto2

theorem balance_key_set [next_code_pos]:
  "<btree t p>
   btree_balance p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(rbt_key_set t' = rbt_key_set t)>"
  by auto2
declare btree_balance_def [sep_proc_defs]

theorem ins_key_set [next_code_pos]:
  "<btree t p>
   rbt_ins k v p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(rbt_key_set t' = {k} \<union> rbt_key_set t)>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("t", Arbitraries ["p"])) *})

theorem ins_sorted [next_code_pos]:
  "<btree t p * \<up>(rbt_sorted t)>
   rbt_ins k v p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(rbt_sorted t')>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("t", Arbitraries ["p"])) *})

theorem insert_key_set [next_code_pos]:
  "<btree t p>
   rbt_insert k v p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(rbt_key_set t' = {k} \<union> rbt_key_set t)>"
  by auto2

theorem insert_sorted [next_code_pos]:
  "<btree t p * \<up>(rbt_sorted t)>
   rbt_insert k v p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(rbt_sorted t')>"
  by auto2

(* Finally, we prove effect of operations on mapping *)

lemma btree_rotate_preserves_map:
  "x < y \<Longrightarrow> tree_map (rbt.Node a c1 x v (rbt.Node b c2 y w c)) =
   tree_map (rbt.Node (rbt.Node a c3 x v b) c4 y w c)" by auto2
setup {* add_forward_prfstep_cond @{thm btree_rotate_preserves_map}
  [with_term "rbt.Node ?a ?c1.0 ?x ?v (rbt.Node ?b ?c2.0 ?y ?w ?c)",
   with_term "rbt.Node (rbt.Node ?a ?c3.0 ?x ?v ?b) ?c4.0 ?y ?w ?c"] *}

theorem balanceR_map [next_code_pos]:
  "<btree t p * \<up>(rbt_sorted t)>
   btree_balanceR p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(tree_map t' = tree_map t)>"
  by auto2

theorem balance_map [next_code_pos, code_pos_create_case]:
  "<btree t p * \<up>(rbt_sorted t)>
   btree_balance p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(tree_map t' = tree_map t)>"
  by auto2

theorem ins_map [next_code_pos]:
  "<btree t p * \<up>(rbt_sorted t)>
   rbt_ins k v p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(tree_map t' = (tree_map t) {k \<rightarrow> v})>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("t", Arbitraries ["p"])) *})

theorem insert_map [next_code_pos]:
  "<btree t p * \<up>(rbt_sorted t)>
   rbt_insert k v p
   <\<lambda>r. \<exists>\<^sub>At'. btree t' r * \<up>(tree_map t' = (tree_map t) {k \<rightarrow> v})>"
  by auto2

section {* Outer interface *}

definition rbt_set :: "'a set \<Rightarrow> ('a::{heap,linorder}, 'b::heap) rbt_node ref option \<Rightarrow> assn" where
  "rbt_set S p = (\<exists>\<^sub>At. btree t p * \<up>(is_rbt t) * \<up>(rbt_sorted t) * \<up>(S = rbt_key_set t))"
setup {* add_rewrite_rule @{thm rbt_set_def} *}

definition rbt_map :: "('a, 'b) map \<Rightarrow> ('a::{heap,linorder}, 'b::heap) rbt_node ref option \<Rightarrow> assn" where
  "rbt_map M p = (\<exists>\<^sub>At. btree t p * \<up>(is_rbt t) * \<up>(rbt_sorted t) * \<up>(M = tree_map t))"
setup {* add_rewrite_rule @{thm rbt_map_def} *}

declare tree_empty_def [sep_proc_defs del]

lemma rbt_empty_rule1:
  "<emp> tree_empty <rbt_set {}>" by auto2

lemma rbt_empty_rule2:
  "<emp> tree_empty <rbt_map empty_map>" by auto2

declare rbt_insert_def [sep_proc_defs del]

lemma rbt_insert_rule1:
  "<rbt_set S b> rbt_insert k v b <rbt_set ({k} \<union> S)>" by auto2

lemma rbt_insert_rule2:
  "<rbt_map M b> rbt_insert k v b <rbt_map (M {k \<rightarrow> v})>" by auto2

end
