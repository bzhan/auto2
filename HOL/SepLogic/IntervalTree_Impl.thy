theory IntervalTree_Impl
imports SepAuto "../DataStrs/Interval_Tree"
begin

section {* Interval and IdxInterval *}

fun interval_encode :: "('a::heap) interval \<Rightarrow> nat" where
  "interval_encode (Interval l h) = to_nat (l, h)"

instance interval :: (heap) heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "interval_encode"])
  apply (case_tac x, simp_all, case_tac y, simp_all)
  ..

fun idx_interval_encode :: "('a::heap) idx_interval \<Rightarrow> nat" where
  "idx_interval_encode (IdxInterval it i) = to_nat (it, i)"

instance idx_interval :: (heap) heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "idx_interval_encode"])
  apply (case_tac x, simp_all, case_tac y, simp_all)
  ..

section {* Tree nodes *}

datatype 'a node =
  Node (lsub: "'a node ref option") (val: "'a idx_interval") (tmax: nat) (rsub: "'a node ref option")
setup {* fold add_rewrite_rule @{thms node.sel} *}
setup {* add_forward_prfstep (equiv_forward_th @{thm node.simps(1)}) *}

fun node_encode :: "('a::heap) node \<Rightarrow> nat" where
  "node_encode (Node l v m r) = to_nat (l, v, m, r)"

instance node :: (heap) heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "node_encode"])
  apply (case_tac x, simp_all, case_tac y, simp_all)
  ..

fun int_tree :: "interval_tree \<Rightarrow> nat node ref option \<Rightarrow> assn" where
  "int_tree Tip p = \<up>(p = None)"
| "int_tree (interval_tree.Node lt v m rt) (Some p) = (\<exists>\<^sub>Alp rp. p \<mapsto>\<^sub>r Node lp v m rp * int_tree lt lp * int_tree rt rp)"
| "int_tree (interval_tree.Node lt v m rt) None = false"
setup {* fold add_rewrite_ent_rule @{thms int_tree.simps} *}

lemma int_tree_Tip [forward_ent_shadow]: "int_tree Tip p \<Longrightarrow>\<^sub>A \<up>(p = None)" by auto2

lemma int_tree_Node [forward_ent_shadow]:
  "int_tree (interval_tree.Node lt v m rt) (Some p) \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Alp rp. p \<mapsto>\<^sub>r Node lp v m rp * int_tree lt lp * int_tree rt rp)"
  by auto2

lemma int_tree_Node_none [forward_ent]:
  "int_tree (interval_tree.Node lt v m rt) None \<Longrightarrow>\<^sub>A false" by auto2

lemma int_tree_Tip_some [forward_ent]:
  "int_tree Tip (Some p) \<Longrightarrow>\<^sub>A false" by auto2

lemma int_tree_is_some [forward_ent]:
  "int_tree (interval_tree.Node lt v m rt) p \<Longrightarrow>\<^sub>A true * \<up>(p \<noteq> None)" by auto2

lemma int_tree_is_not_leaf [forward_ent]:
  "int_tree t (Some p) \<Longrightarrow>\<^sub>A true * \<up>(t \<noteq> Tip)" by auto2

lemma int_tree_none: "emp \<Longrightarrow>\<^sub>A int_tree interval_tree.Tip None" by auto2

lemma int_tree_constr_ent:
  "p \<mapsto>\<^sub>r Node lp v m rp * int_tree lt lp * int_tree rt rp \<Longrightarrow>\<^sub>A int_tree (interval_tree.Node lt v m rt) (Some p)" by auto2

setup {* fold add_entail_matcher [@{thm int_tree_none}, @{thm int_tree_constr_ent}] *}

lemma int_tree_prec [sep_prec_thms]:
  "h \<Turnstile> int_tree t p * F1 \<Longrightarrow> h \<Turnstile> int_tree t' p * F2 \<Longrightarrow> t = t'"
@proof @induct t arbitrary p t' F1 F2 @qed

setup {* fold del_prfstep_thm @{thms int_tree.simps} *}

type_synonym int_tree = "nat node ref option"

section {* Operations *}

subsection {* Basic operation *}

definition int_tree_empty :: "int_tree Heap" where
  "int_tree_empty \<equiv> return None"
declare int_tree_empty_def [sep_proc_defs]

lemma int_tree_empty_to_fun [hoare_triple]:
  "<emp> int_tree_empty <int_tree Tip>" by auto2
declare int_tree_empty_def [sep_proc_defs del]

definition int_tree_is_empty :: "int_tree \<Rightarrow> bool Heap" where
  "int_tree_is_empty b \<equiv> return (b = None)"
declare int_tree_is_empty_def [sep_proc_defs]

lemma int_tree_is_empty_rule:
  "<int_tree t b>
   int_tree_is_empty b
   <\<lambda>r. int_tree t b * \<up>(r \<longleftrightarrow> t = Tip)>" by auto2
declare int_tree_is_empty_def [sep_proc_defs del]

definition get_tmax :: "int_tree \<Rightarrow> nat Heap" where
  "get_tmax b = (case b of
     None \<Rightarrow> return 0
   | Some p \<Rightarrow> do {
      t \<leftarrow> !p;
      return (tmax t) })"
declare get_tmax_def [sep_proc_defs]

lemma get_tmax_rule [hoare_triple]:
  "<int_tree t b> get_tmax b <\<lambda>r. int_tree t b * \<up>(r = interval_tree.tmax t)>"
@proof @case "t = Tip" @qed
declare get_tmax_def [sep_proc_defs del]

definition compute_tmax :: "nat idx_interval \<Rightarrow> int_tree \<Rightarrow> int_tree \<Rightarrow> nat Heap" where
  "compute_tmax it l r = do {
    lm \<leftarrow> get_tmax l;
    rm \<leftarrow> get_tmax r;
    return (max3 it lm rm)
  }"
declare compute_tmax_def [sep_proc_defs]

lemma compute_tmax_rule [hoare_triple]:
  "<int_tree t1 b1 * int_tree t2 b2>
   compute_tmax it b1 b2
   <\<lambda>r. int_tree t1 b1 * int_tree t2 b2 * \<up>(r = max3 it (interval_tree.tmax t1) (interval_tree.tmax t2))>"
  by auto2
declare compute_tmax_def [sep_proc_defs del]

definition int_tree_constr :: "int_tree \<Rightarrow> nat idx_interval \<Rightarrow> int_tree \<Rightarrow> int_tree Heap" where
  "int_tree_constr lp v rp = do {
    m \<leftarrow> compute_tmax v lp rp;
    p \<leftarrow> ref (Node lp v m rp);
    return (Some p) }"
declare int_tree_constr_def [sep_proc_defs]

lemma int_tree_constr_rule [hoare_triple]:
  "<int_tree lt lp * int_tree rt rp>
   int_tree_constr lp v rp
   <\<lambda>r. int_tree (interval_tree.Node lt v (max3 v (interval_tree.tmax lt) (interval_tree.tmax rt)) rt) r>"
  by auto2
declare int_tree_constr_def [sep_proc_defs del]

subsection {* Insertion *}
  
partial_function (heap) int_tree_insert :: "nat idx_interval \<Rightarrow> int_tree \<Rightarrow> int_tree Heap" where
  "int_tree_insert v b = (case b of
    None \<Rightarrow> int_tree_constr None v None
  | Some p \<Rightarrow> do {
    t \<leftarrow> !p;
    (if v = val t then do {
       return (Some p) }
     else if v < val t then do {
       q \<leftarrow> int_tree_insert v (lsub t);
       m \<leftarrow> compute_tmax (val t) q (rsub t);
       p := Node q (val t) m (rsub t);
       return (Some p) }
     else do {
       q \<leftarrow> int_tree_insert v (rsub t);
       m \<leftarrow> compute_tmax (val t) (lsub t) q;
       p := Node (lsub t) (val t) m q;
       return (Some p) })})"
declare int_tree_insert.simps [sep_proc_defs]

lemma int_tree_insert_to_fun [hoare_triple]:
  "<int_tree t b>
   int_tree_insert v b
   <\<lambda>r. int_tree (tree_insert v t) r>"
@proof @induct t arbitrary b @qed
declare int_tree_insert.simps [sep_proc_defs del]

subsection {* Deletion *}

partial_function (heap) int_tree_del_min :: "int_tree \<Rightarrow> (nat idx_interval \<times> int_tree) Heap" where
  "int_tree_del_min b = (case b of
     None \<Rightarrow> raise ''del_min: empty tree''
   | Some p \<Rightarrow> do {
      t \<leftarrow> !p;
      (if lsub t = None then
         return (val t, rsub t)
       else do {
         r \<leftarrow> int_tree_del_min (lsub t);
         m \<leftarrow> compute_tmax (val t) (snd r) (rsub t);
         p := Node (snd r) (val t) m (rsub t);
         return (fst r, Some p) })})"
declare int_tree_del_min.simps [sep_proc_defs]

lemma int_tree_del_min_to_fun [hoare_triple]:
  "<int_tree t b * \<up>(b \<noteq> None)>
   int_tree_del_min b
   <\<lambda>r. int_tree (snd (del_min t)) (snd r) * true * \<up>(fst(r) = fst (del_min t))>"
@proof @induct t arbitrary b @qed
declare int_tree_del_min.simps [sep_proc_defs del]

definition int_tree_del_elt :: "int_tree \<Rightarrow> int_tree Heap" where
  "int_tree_del_elt b = (case b of
     None \<Rightarrow> raise ''del_elt: empty tree''
   | Some p \<Rightarrow> do {
       t \<leftarrow> !p;
       (if lsub t = None then return (rsub t)
        else if rsub t = None then return (lsub t)
        else do {
          r \<leftarrow> int_tree_del_min (rsub t);
          m \<leftarrow> compute_tmax (fst r) (lsub t) (snd r);
          p := Node (lsub t) (fst r) m (snd r);
          return (Some p) }) })"
declare int_tree_del_elt_def [sep_proc_defs]

lemma int_tree_del_elt_to_fun [hoare_triple]:
  "<int_tree (interval_tree.Node lt v m rt) b>
   int_tree_del_elt b
   <\<lambda>r. int_tree (delete_elt_tree (interval_tree.Node lt v m rt)) r * true>" by auto2
declare int_tree_del_elt_def [sep_proc_defs del]

partial_function (heap) int_tree_delete ::
  "nat idx_interval \<Rightarrow> int_tree \<Rightarrow> int_tree Heap" where
  "int_tree_delete x b = (case b of
     None \<Rightarrow> return None
   | Some p \<Rightarrow> do {
      t \<leftarrow> !p;
      (if x = val t then do {
         r \<leftarrow> int_tree_del_elt b;
         return r }
       else if x < val t then do {
         q \<leftarrow> int_tree_delete x (lsub t);
         m \<leftarrow> compute_tmax (val t) q (rsub t);
         p := Node q (val t) m (rsub t);
         return (Some p) }
       else do {
         q \<leftarrow> int_tree_delete x (rsub t);
         m \<leftarrow> compute_tmax (val t) (lsub t) q;
         p := Node (lsub t) (val t) m q;
         return (Some p) })})"
declare int_tree_delete.simps [sep_proc_defs]

lemma int_tree_delete_to_fun [hoare_triple]:
  "<int_tree t b>
   int_tree_delete x b
   <\<lambda>r. int_tree (tree_delete x t) r * true>"
@proof @induct t arbitrary b @qed
declare int_tree_delete.simps [sep_proc_defs del]

subsection {* Search *}

partial_function (heap) int_tree_search :: "nat interval \<Rightarrow> int_tree \<Rightarrow> bool Heap" where
  "int_tree_search x b = (case b of
     None \<Rightarrow> return False
   | Some p \<Rightarrow> do {
      t \<leftarrow> !p;
      (if is_overlap (int (val t)) x then return True
       else case lsub t of
           None \<Rightarrow> do { b \<leftarrow> int_tree_search x (rsub t); return b }
         | Some lp \<Rightarrow> do {
            lt \<leftarrow> !lp;
            if tmax lt \<ge> low x then
              do { b \<leftarrow> int_tree_search x (lsub t); return b }
            else
              do { b \<leftarrow> int_tree_search x (rsub t); return b }})})"
declare int_tree_search.simps [sep_proc_defs]

lemma int_tree_search_correct [hoare_triple]:
  "<int_tree t b>
   int_tree_search x b
   <\<lambda>r. int_tree t b * \<up>(r \<longleftrightarrow> tree_search t x)>"
@proof @induct t arbitrary b @with
  @subgoal "t = interval_tree.Node l v m r"
    @case "is_overlap (int v) x"
    @case "l \<noteq> Tip \<and> interval_tree.tmax l \<ge> low x"
  @endgoal @end
@qed
declare int_tree_search.simps [sep_proc_defs del]

section {* Outer interface *}

definition int_tree_set :: "nat idx_interval set \<Rightarrow> int_tree \<Rightarrow> assn" where
  "int_tree_set S p = (\<exists>\<^sub>At. int_tree t p * \<up>(is_interval_tree t) * \<up>(S = tree_set t))"
setup {* add_rewrite_ent_rule @{thm int_tree_set_def} *}

lemma int_tree_empty_rule [hoare_triple]:
  "<emp> int_tree_empty <int_tree_set {}>" by auto2

lemma int_tree_insert_rule [hoare_triple]:
  "<int_tree_set S b * \<up>(is_interval (int x))>
   int_tree_insert x b
   <int_tree_set (S \<union> {x})>" by auto2

lemma int_tree_delete_rule [hoare_triple]:
  "<int_tree_set S b * \<up>(is_interval (int x))>
   int_tree_delete x b
   <int_tree_set (S - {x})>\<^sub>t" by auto2

lemma int_tree_search_rule [hoare_triple]:
  "<int_tree_set S b * \<up>(is_interval x)>
   int_tree_search x b
   <\<lambda>r. int_tree_set S b * \<up>(r \<longleftrightarrow> has_overlap S x)>" by auto2
setup {* del_prfstep_thm @{thm int_tree_set_def} *}

end