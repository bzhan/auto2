(* Examples in linked lists. Definitions and some of the examples are
   based on List_Seg and Open_List theories in Separation_Logic_Imperative_HOL/Examples. *)

theory LinkedList
imports SepAuto
begin

subsection {* Nodes *}

datatype 'a node = Node (val: "'a") (nxt: "'a node ref option")
setup {* fold add_rewrite_rule @{thms node.sel} *}
setup {* add_forward_prfstep (equiv_forward_th @{thm node.simps(1)}) *}

fun node_encode :: "'a::heap node \<Rightarrow> nat" where
  "node_encode (Node x r) = to_nat (x, r)"

instance node :: (heap) heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "node_encode"])
  apply (case_tac x, simp_all, case_tac y, simp_all)
  ..

subsection {* List Assertion *}

fun os_list :: "'a::heap list \<Rightarrow> 'a node ref option \<Rightarrow> assn" where
  "os_list [] p = \<up>(p = None)"
| "os_list (x # l) (Some p) = (\<exists>\<^sub>Aq. p \<mapsto>\<^sub>r Node x q * os_list l q)"
| "os_list (x # l) None = false"
setup {* fold add_rewrite_ent_rule @{thms os_list.simps} *}

lemma os_list_empty [forward_ent_shadow]:
  "os_list [] p \<Longrightarrow>\<^sub>A \<up>(p = None)" by auto2

lemma os_list_Cons [forward_ent_shadow]:
  "os_list (x # l) (Some p) \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Aq. p \<mapsto>\<^sub>r Node x q * os_list l q)" by auto2

lemma os_list_empty_none [forward_ent]:
  "os_list (x # l) None \<Longrightarrow>\<^sub>A false" by auto2

lemma os_list_Cons_some [forward_ent]:
  "os_list [] (Some p) \<Longrightarrow>\<^sub>A false" by auto2

lemma os_list_is_some [forward_ent]:
  "os_list (x # l) p \<Longrightarrow>\<^sub>A true * \<up>(p \<noteq> None)" by auto2

lemma os_list_is_not_empty [forward_ent]:
  "os_list xs (Some p) \<Longrightarrow>\<^sub>A true * \<up>(xs \<noteq> [])" by auto2

lemma os_list_none: "emp \<Longrightarrow>\<^sub>A os_list [] None" by auto2

lemma os_list_constr_ent:
  "p \<mapsto>\<^sub>r Node x q * os_list l q \<Longrightarrow>\<^sub>A os_list (x # l) (Some p)" by auto2

setup {* fold add_entail_matcher [@{thm os_list_none}, @{thm os_list_constr_ent}] *}
setup {* fold del_prfstep_thm @{thms os_list.simps} *}

ML_file "list_matcher_test.ML"

type_synonym 'a os_list = "'a node ref option"

subsection {* List assertion *}

lemma mod_os_list_eq [backward1]:
  "l1 = l2 \<Longrightarrow> h \<Turnstile> os_list l1 r \<Longrightarrow> h \<Turnstile> os_list l2 r" by simp

subsection {* Operations *}

subsubsection {* Basic operations *}

definition os_empty :: "'a::heap os_list Heap" where [sep_proc_defs]:
  "os_empty = return None"

lemma os_empty_rule [hoare_triple]:
  "<emp> os_empty <os_list []>" by auto2

definition os_is_empty :: "'a::heap os_list \<Rightarrow> bool Heap" where [sep_proc_defs]:
  "os_is_empty b = return (b = None)"

lemma os_is_empty_rule [hoare_triple]:
  "<os_list xs b> os_is_empty b <\<lambda>r. os_list xs b * \<up>(r \<longleftrightarrow> xs = [])>"
@proof @case "xs = []" @have "xs = hd xs # tl xs" @qed

definition os_prepend :: "'a \<Rightarrow> 'a::heap os_list \<Rightarrow> 'a os_list Heap" where [sep_proc_defs]:
  "os_prepend a n = do { p \<leftarrow> ref (Node a n); return (Some p) }"

lemma os_prepend_rule [hoare_triple]:
  "<os_list xs n> os_prepend x n <os_list (x # xs)>" by auto2

definition os_pop :: "'a::heap os_list \<Rightarrow> ('a \<times> 'a os_list) Heap" where [sep_proc_defs]:
  "os_pop r = (case r of
    None \<Rightarrow> raise ''Empty Os_list'' |
    Some p \<Rightarrow> do {m \<leftarrow> !p; return (val m, nxt m)})"

lemma os_pop_rule [hoare_triple]:
  "<os_list xs (Some p)>
   os_pop (Some p)
   <\<lambda>(x,r'). os_list (tl xs) r' * p \<mapsto>\<^sub>r (Node x r') * \<up>(x = hd xs)>"
@proof @case "xs = []" @have "xs = hd xs # tl xs" @qed

subsubsection {* Reverse *}

partial_function (heap) os_reverse_aux :: "'a::heap os_list \<Rightarrow> 'a os_list \<Rightarrow> 'a os_list Heap" where
  "os_reverse_aux q p = (case p of
    None \<Rightarrow> return q |
    Some r \<Rightarrow> do {
      v \<leftarrow> !r;
      r := Node (val v) q;
      os_reverse_aux p (nxt v) })"
declare os_reverse_aux.simps [sep_proc_defs]

lemma os_reverse_aux_rule [hoare_triple]:
  "<os_list xs p * os_list ys q> 
    os_reverse_aux q p 
   <os_list ((rev xs) @ ys)>"
@proof @induct xs arbitrary p q ys @qed

definition os_reverse :: "'a::heap os_list \<Rightarrow> 'a os_list Heap" where [sep_proc_defs]:
  "os_reverse p = os_reverse_aux None p"

lemma os_reverse_rule:
  "<os_list xs p> os_reverse p <os_list (rev xs)>" by auto2

subsubsection {* Remove *}

setup {* fold add_rewrite_rule @{thms removeAll.simps} *}

partial_function (heap) os_rem :: "'a::heap \<Rightarrow> 'a node ref option \<Rightarrow> 'a node ref option Heap" where
  "os_rem x b = (case b of 
     None \<Rightarrow> return None |
     Some p \<Rightarrow> do { 
       n \<leftarrow> !p;
       q \<leftarrow> os_rem x (nxt n);
       (if (val n = x) 
         then return q
         else do {
           p := Node (val n) q; 
           return (Some p) }) })"
declare os_rem.simps [sep_proc_defs]

lemma os_rem_rule [hoare_triple]:
  "<os_list xs b> os_rem x b <\<lambda>r. os_list (removeAll x xs) r>\<^sub>t"
@proof @induct xs arbitrary b @qed

subsubsection {* Insert in order *}

fun list_insert :: "'a::ord \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "list_insert x [] = [x]"
| "list_insert x (y # ys) = (
    if x \<le> y then x # (y # ys) else y # list_insert x ys)"
setup {* fold add_rewrite_rule @{thms list_insert.simps} *}

lemma list_insert_mset [rewrite]:
  "mset (list_insert x xs) = {#x#} + mset xs"
@proof @induct xs @qed

lemma list_insert_set [rewrite]:
  "set (list_insert x xs) = {x} \<union> set xs"
@proof @induct xs @qed

lemma list_insert_sorted [forward]:
  "sorted xs \<Longrightarrow> sorted (list_insert x xs)"
@proof @induct xs @qed

partial_function (heap) os_insert :: "'a::{ord,heap} \<Rightarrow> 'a os_list \<Rightarrow> 'a os_list Heap" where
  "os_insert x b = (case b of
      None \<Rightarrow> os_prepend x None
    | Some p \<Rightarrow> do {
        v \<leftarrow> !p;
        (if x \<le> val v then os_prepend x b
         else do {
           q \<leftarrow> os_insert x (nxt v);
           p := Node (val v) q;
           return (Some p) }) })"
declare os_insert.simps [sep_proc_defs]

lemma os_insert_to_fun [hoare_triple]:
  "<os_list xs b> os_insert x b <os_list (list_insert x xs)>"
@proof @induct xs arbitrary b @qed

subsection {* Application: insertion sort *}

partial_function (heap) extract_list :: "'a::heap os_list \<Rightarrow> 'a list Heap" where
  "extract_list p = (case p of
    None \<Rightarrow> return []
  | Some pp \<Rightarrow> do {
      v \<leftarrow> !pp;
      ls \<leftarrow> extract_list (nxt v);
      return (val v # ls)
    })"
declare extract_list.simps [sep_proc_defs]

lemma extract_list_rule [hoare_triple]:
  "<os_list l p> extract_list p <\<lambda>r. os_list l p * \<up>(r = l)>"
@proof @induct l arbitrary p @qed

fun os_insert_list :: "'a::{ord,heap} list \<Rightarrow> 'a os_list \<Rightarrow> 'a os_list Heap" where
  "os_insert_list xs b = (
    if xs = [] then return b
    else do {
      b' \<leftarrow> os_insert (hd xs) b;
      b'' \<leftarrow> os_insert_list (tl xs) b';
      return b''
    })"
declare os_insert_list.simps [sep_proc_defs]

lemma os_insert_list_correct [hoare_triple]:
  "<os_list xs b * \<up>(sorted xs)>
   os_insert_list ys b
   <\<lambda>r. \<exists>\<^sub>Axs'. os_list xs' r * \<up>(sorted xs') * \<up>(mset xs' = mset ys + mset xs)>"
@proof @induct ys arbitrary b xs @qed

definition insertion_sort :: "'a::{ord,heap} list \<Rightarrow> 'a list Heap" where [sep_proc_defs]:
  "insertion_sort xs = do {
    p \<leftarrow> os_insert_list xs None;
    l \<leftarrow> extract_list p;
    return l
  }"

lemma insertion_sort_rule:
  "<emp> insertion_sort xs <\<lambda>ys. \<up>(ys = sort xs)>\<^sub>t" by auto2

subsection {* Merging two lists *}

fun merge_list :: "('a::ord) list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "merge_list xs [] = xs"
| "merge_list [] ys = ys"
| "merge_list (x # xs) (y # ys) = (
    if x \<le> y then x # (merge_list xs (y # ys))
    else y # (merge_list (x # xs) ys))"
setup {* fold add_rewrite_rule @{thms merge_list.simps} *}
setup {* add_fun_induct_rule (@{term_pat "merge_list (?a0.0::?'a::ord list) ?a1.0"}, @{thm merge_list.induct}) *}

lemma merge_list_correct [rewrite]:
  "set (merge_list xs ys) = set xs \<union> set ys"
@proof @fun_induct "merge_list xs ys" @qed

lemma merge_list_sorted [forward]:
  "sorted xs \<Longrightarrow> sorted ys \<Longrightarrow> sorted (merge_list xs ys)"
@proof @fun_induct "merge_list xs ys" @qed

partial_function (heap) merge_os_list :: "('a::{heap, ord}) os_list \<Rightarrow> 'a os_list \<Rightarrow> 'a os_list Heap" where
  "merge_os_list p q = (
    if p = None then return q
    else if q = None then return p
    else do {
      np \<leftarrow> !(the p); nq \<leftarrow> !(the q);
      if val np \<le> val nq then
        do { npq \<leftarrow> merge_os_list (nxt np) q;
             (the p) := Node (val np) npq;
             return p }
      else
        do { pnq \<leftarrow> merge_os_list p (nxt nq);
             (the q) := Node (val nq) pnq;
             return q } })"
declare merge_os_list.simps [sep_proc_defs]

lemma merge_os_list_to_fun [hoare_triple]:
  "<os_list xs p * os_list ys q>
  merge_os_list p q
  <\<lambda>r. os_list (merge_list xs ys) r>"
@proof @fun_induct "merge_list xs ys" arbitrary p q @qed

subsection {* List copy *}

partial_function (heap) copy_os_list :: "'a::heap os_list \<Rightarrow> 'a os_list Heap" where
  "copy_os_list b = (case b of
      None \<Rightarrow> return None
    | Some p \<Rightarrow> do {
        v \<leftarrow> !p;
        q \<leftarrow> copy_os_list (nxt v);
        os_prepend (val v) q })"
declare copy_os_list.simps [sep_proc_defs]

lemma copy_os_list_rule [hoare_triple]:
  "<os_list xs b> copy_os_list b <\<lambda>r. os_list xs b * os_list xs r>"
@proof @induct xs arbitrary b @qed

subsection {* Higher-order functions *}

partial_function (heap) map_os_list :: "('a::heap \<Rightarrow> 'a) \<Rightarrow> 'a os_list \<Rightarrow> 'a os_list Heap" where
  "map_os_list f b = (case b of
      None \<Rightarrow> return None
    | Some p \<Rightarrow> do {
        v \<leftarrow> !p;
        q \<leftarrow> map_os_list f (nxt v);
        p := Node (f (val v)) q;
        return (Some p) })"
declare map_os_list.simps [sep_proc_defs]

lemma map_os_list_rule [hoare_triple]:
  "<os_list xs b> map_os_list f b <os_list (map f xs)>"
@proof @induct xs arbitrary b @qed

partial_function (heap) filter_os_list :: "('a::heap \<Rightarrow> bool) \<Rightarrow> 'a os_list \<Rightarrow> 'a os_list Heap" where
  "filter_os_list f b = (case b of
      None \<Rightarrow> return None
    | Some p \<Rightarrow> do {
        v \<leftarrow> !p;
        q \<leftarrow> filter_os_list f (nxt v);
        (if (f (val v)) then do {
           p := Node (val v) q;
           return (Some p) }
         else return q) })"
declare filter_os_list.simps [sep_proc_defs]

lemma filter_os_list_rule [hoare_triple]:
  "<os_list xs b> filter_os_list f b <\<lambda>r. os_list (filter f xs) r * true>"
@proof @induct xs arbitrary b @qed

partial_function (heap) filter_os_list2 :: "('a::heap \<Rightarrow> bool) \<Rightarrow> 'a os_list \<Rightarrow> 'a os_list Heap" where
  "filter_os_list2 f b = (case b of
      None \<Rightarrow> return None
    | Some p \<Rightarrow> do {
        v \<leftarrow> !p;
        q \<leftarrow> filter_os_list2 f (nxt v);
        (if (f (val v)) then os_prepend (val v) q
         else return q) })"
declare filter_os_list2.simps [sep_proc_defs]

lemma filter_os_list2_rule [hoare_triple]:
  "<os_list xs b> filter_os_list2 f b <\<lambda>r. os_list xs b * os_list (filter f xs) r>"
@proof @induct xs arbitrary b @qed

setup {* fold add_rewrite_rule @{thms List.fold_simps} *}

partial_function (heap) fold_os_list :: "('a::heap \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a os_list \<Rightarrow> 'b \<Rightarrow> 'b Heap" where
  "fold_os_list f b x = (case b of
      None \<Rightarrow> return x
    | Some p \<Rightarrow> do {
       v \<leftarrow> !p;
       r \<leftarrow> fold_os_list f (nxt v) (f (val v) x);
       return r})"
declare fold_os_list.simps [sep_proc_defs]

lemma fold_os_list_rule [hoare_triple]:
  "<os_list xs b> fold_os_list f b x <\<lambda>r. os_list xs b * \<up>(r = fold f xs x)>"
@proof @induct xs arbitrary b x @qed

end
