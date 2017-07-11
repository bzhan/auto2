(* Examples in linked lists. Definitions and some of the examples are
   based on List_Seg and Open_List theories in Separation_Logic_Imperative_HOL/Examples. *)

theory LinkedList
imports SepAuto More_Lists
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

subsection {* List Segment Assertion *}

fun lseg :: "'a::heap list \<Rightarrow> 'a node ref option \<Rightarrow> 'a node ref option \<Rightarrow> assn" where
  "lseg [] p s = \<up>(p = s)"
| "lseg (x # l) (Some p) s = (\<exists>\<^sub>Aq. p \<mapsto>\<^sub>r Node x q * lseg l q s)"
| "lseg (x # l) None s = false"
setup {* fold add_rewrite_ent_rule @{thms lseg.simps} *}

lemma lseg_empty: "emp \<Longrightarrow>\<^sub>A lseg [] p p" by auto2
ML_file "lseg_matcher.ML"

(* Folding and expanding the recursive definition of lseg. *)
lemma lseg_is_some [forward_ent]: "lseg (x # l) p s \<Longrightarrow>\<^sub>A true * \<up>(p \<noteq> None)" by auto2

lemma lseg_prepend [forward_ent]:
  "p \<mapsto>\<^sub>r Node x q * lseg l q s \<Longrightarrow>\<^sub>A lseg (x # l) (Some p) s" by auto2

(* Several examples for using induction. *)
lemma lseg_append [forward_ent]:
  "lseg l p (Some s) * s \<mapsto>\<^sub>r Node x q \<Longrightarrow>\<^sub>A lseg (l @ [x]) p q"
  by (tactic {* auto2s_tac @{context} (INDUCT ("l", [Arbitrary "p"])) *})

lemma lseg_conc [forward_ent]:
  "lseg l1 p q * lseg l2 q r \<Longrightarrow>\<^sub>A lseg (l1 @ l2) p r"
  by (tactic {* auto2s_tac @{context} (INDUCT ("l1", [Arbitrary "p"])) *})

lemma lseg_split:
  "lseg (l1 @ l2) p r \<Longrightarrow>\<^sub>A \<exists>\<^sub>Aq. lseg l1 p q * lseg l2 q r"
  by (tactic {* auto2s_tac @{context} (INDUCT ("l1", [Arbitrary "p"])) *})

lemma lseg_prec [forward]:
  "h \<Turnstile> lseg l p None * F1 \<Longrightarrow> h \<Turnstile> lseg l' p None * F2 \<Longrightarrow> l = l'"
  by (tactic {* auto2s_tac @{context}
    (INDUCT ("l", Arbitraries ["p", "l'", "F1", "F2"]) THEN CASE "l' = []") *})

subsection {* List assertion *}

type_synonym 'a os_list = "'a node ref option"

definition os_list :: "'a list \<Rightarrow> ('a::heap) os_list \<Rightarrow> assn" where
  "os_list l p = lseg l p None"
setup {* add_rewrite_ent_rule @{thm os_list_def} *}
setup {* add_rewrite_ent_rule (obj_sym_th @{thm os_list_def}) *}

theorem os_line_none_rewr [forward_ent]:
  "os_list [] b \<Longrightarrow>\<^sub>A \<up>(b = None)" by auto2

theorem mod_os_list_eq [backward1]:
  "l1 = l2 \<Longrightarrow> h \<Turnstile> os_list l1 r \<Longrightarrow> h \<Turnstile> os_list l2 r" by simp

lemma os_list_prec [sep_prec_thms]:
  "h \<Turnstile> os_list l p * F1 \<Longrightarrow> h \<Turnstile> os_list l' p * F2 \<Longrightarrow> l = l'" by auto2

lemma os_list_none: "emp \<Longrightarrow>\<^sub>A os_list [] None" by auto2

(* Folding and expanding the recursive definition of os_list. *)
lemma os_list_is_some [forward_ent]:
  "os_list (x # l) p \<Longrightarrow>\<^sub>A true * \<up>(p \<noteq> None)" by auto2

lemma os_list_prepend [forward_ent]:
  "p \<mapsto>\<^sub>r Node x q * os_list xs q \<Longrightarrow>\<^sub>A os_list (x # xs) (Some p)" by auto2

lemma os_list_prepend_rev [forward_ent]:
  "os_list (x # xs) (Some p) \<Longrightarrow>\<^sub>A (\<exists>\<^sub>An. p \<mapsto>\<^sub>r (Node x n) * os_list xs n)" by auto2

setup {* fold add_entail_matcher [@{thm os_list_none}, @{thm os_list_prepend}] *}
ML_file "list_matcher_test.ML"

subsection {* Operations *}

subsubsection {* Basic operations *}

definition os_empty :: "'a::heap os_list Heap" where
  "os_empty \<equiv> return None"
declare os_empty_def [sep_proc_defs]

lemma os_empty_rule: "<emp> os_empty <os_list []>" by auto2

definition os_is_empty :: "'a::heap os_list \<Rightarrow> bool Heap" where
  "os_is_empty b \<equiv> return (b = None)"
declare os_is_empty_def [sep_proc_defs]

lemma os_is_empty_rule:
  "<os_list xs b> os_is_empty b <\<lambda>r. os_list xs b * \<up>(r \<longleftrightarrow> xs = [])>" by auto2

definition os_prepend :: "'a \<Rightarrow> 'a::heap os_list \<Rightarrow> 'a os_list Heap" where
  "os_prepend a n = do { p \<leftarrow> ref (Node a n); return (Some p) }"
declare os_prepend_def [sep_proc_defs]

lemma os_prepend_rule [hoare_triple]:
  "<os_list xs n> os_prepend x n <os_list (x # xs)>" by auto2

definition os_pop :: "'a::heap os_list \<Rightarrow> ('a \<times> 'a os_list) Heap" where
  "os_pop r = (case r of
    None \<Rightarrow> raise ''Empty Os_list'' |
    Some p \<Rightarrow> do {m \<leftarrow> !p; return (val m, nxt m)})"
declare os_pop_def [sep_proc_defs]

lemma os_pop_rule [hoare_triple]:
  "<os_list xs (Some p)>
   os_pop (Some p)
   <\<lambda>(x,r'). os_list (tl xs) r' * p \<mapsto>\<^sub>r (Node x r') * \<up>(x = hd xs)>" by auto2

subsubsection {* Iterator *}

type_synonym 'a os_list_it = "'a os_list"

definition os_is_it :: "('a::heap) list \<Rightarrow> 'a node ref option \<Rightarrow> 'a list \<Rightarrow> 'a node ref option \<Rightarrow> assn" where
  "os_is_it l p l2 it = (\<exists>\<^sub>Al1. lseg l1 p it * os_list l2 it * \<up>(l = l1 @ l2))"
setup {* add_rewrite_ent_rule @{thm os_is_it_def} *}

theorem os_is_it_empty [backward]: "h \<Turnstile> os_list l p \<Longrightarrow> h \<Turnstile> os_is_it l p l p"
  by (tactic {* auto2s_tac @{context} (HAVE "h \<Turnstile> lseg [] p p * os_list l p") *})

definition os_it_init :: "'a os_list \<Rightarrow> ('a os_list_it) Heap" where
  "os_it_init l = return l"
declare os_it_init_def [sep_proc_defs]

definition os_it_next :: "'a::heap os_list \<Rightarrow> ('a \<times> 'a os_list) Heap" where
  "os_it_next it = os_pop it"
declare os_it_next_def [sep_proc_defs]

definition os_it_has_next :: "'a os_list_it \<Rightarrow> bool Heap" where
  "os_it_has_next it = return (it \<noteq> None)"
declare os_it_has_next_def [sep_proc_defs]

theorem os_it_init_rule [hoare_triple]:
  "<os_list l p> os_it_init p <os_is_it l p l>" by auto2

theorem os_is_it_rule [forward_ent]: "os_is_it l p l' it \<Longrightarrow>\<^sub>A os_list l p" by auto2

theorem os_is_has_next_rule [hoare_triple]:
  "<os_is_it l p l' it> os_it_has_next it <\<lambda>r. os_is_it l p l' it * \<up>(r = (l' \<noteq> []))>"
  by auto2

theorem os_is_has_next_rule' [forward_ent]:
  "os_is_it l p (x # xs) it \<Longrightarrow>\<^sub>A true * \<up>(it \<noteq> None)" by auto2

theorem os_it_next_rule [hoare_triple]:
  "<os_is_it l p l' (Some q)> os_it_next (Some q) <\<lambda>(a, it'). os_is_it l p (tl l') it' * \<up>(a = hd l')>"
  by (tactic {* auto2s_tac @{context} (CASE "l' = []") *})

setup {* del_prfstep_thm @{thm os_list_def} *}
setup {* del_prfstep_thm @{thm os_is_it_def} *}

subsubsection {* List-Sum *}

partial_function (heap) os_sum' :: "int os_list_it \<Rightarrow> int \<Rightarrow> int Heap"
  where [code]:
  "os_sum' it s = do {
    b \<leftarrow> os_it_has_next it;
    if b then do {
      (x,it') \<leftarrow> os_it_next it;
      os_sum' it' (s+x)
    } else return s
  }"
declare os_sum'.simps [sep_proc_defs]

lemma os_sum'_rule [hoare_triple]:
  "<os_is_it l p l' it>
    os_sum' it s
  <\<lambda>r. os_list l p * \<up>(r = s + sum_list l')>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("l'", Arbitraries ["it", "s"])) *})

definition os_sum :: "int node ref option \<Rightarrow> int Heap" where
  "os_sum p \<equiv> do {
    it \<leftarrow> os_it_init p;
    os_sum' it 0
  }"
declare os_sum_def [sep_proc_defs]

lemma os_sum_rule:
  "<os_list l p> os_sum p <\<lambda>r. os_list l p * \<up>(r = sum_list l)>" by auto2

subsubsection {* Reverse *}

partial_function (heap) os_reverse_aux 
  :: "'a::heap os_list \<Rightarrow> 'a os_list \<Rightarrow> 'a os_list Heap" where [code]:
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
  by (tactic {* auto2s_tac @{context} (
    INDUCT ("xs", Arbitraries ["p", "q", "ys"]) THEN
    HAVE "[hd xs] @ ys = hd xs # ys") *})

definition os_reverse :: "'a::heap os_list \<Rightarrow> 'a os_list Heap" where
  "os_reverse p = os_reverse_aux None p"
declare os_reverse_def [sep_proc_defs]

lemma os_reverse_rule: "<os_list xs p> os_reverse p <os_list (rev xs)>" by auto2

subsubsection {* Remove *}

partial_function (heap) os_rem
  :: "'a::heap \<Rightarrow> 'a node ref option \<Rightarrow> 'a node ref option Heap" 
  where [code]:
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
  by (tactic {* auto2s_tac @{context} (INDUCT ("xs", Arbitraries ["b"])) *})

subsubsection {* Insert in order *}

partial_function (heap) os_insert
  :: "'a::{ord,heap} \<Rightarrow> 'a os_list \<Rightarrow> 'a os_list Heap" where
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

lemma os_insert_mset_rule [hoare_triple]:
  "<os_list xs b> os_insert x b <\<lambda>r. \<exists>\<^sub>Axs'. os_list xs' r * \<up>(mset xs' = {#x#} + mset xs)>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("xs", Arbitraries ["b"])) *})

lemma os_insert_set_rule [hoare_triple]:
  "<os_list xs b> os_insert x b <\<lambda>r. \<exists>\<^sub>Axs'. os_list xs' r * \<up>(set xs' = {x} \<union> set xs)>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("xs", Arbitraries ["b"])) *})

lemma os_insert_sorted [hoare_triple]:
  "<os_list xs b * \<up>(sorted xs)> os_insert x b <\<lambda>r. \<exists>\<^sub>Axs'. os_list xs' r * \<up>(sorted xs')>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("xs", Arbitraries ["b"])) *})

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

theorem extract_list_rule [hoare_triple_direct]:
  "<os_list l p> extract_list p <\<lambda>r. os_list l p * \<up>(r = l)>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("l", Arbitraries ["p"])) *})

fun os_insert_list :: "'a::{ord,heap} list \<Rightarrow> 'a os_list \<Rightarrow> 'a os_list Heap" where
  "os_insert_list xs b = (
    if xs = [] then return b
    else do {
      b' \<leftarrow> os_insert (hd xs) b;
      b'' \<leftarrow> os_insert_list (tl xs) b';
      return b''
    })"
declare os_insert_list.simps [sep_proc_defs]

lemma os_insert_list_sorted [hoare_triple]:
  "<os_list xs b * \<up>(sorted xs)> os_insert_list ys b <\<lambda>r. \<exists>\<^sub>Axs'. os_list xs' r * \<up>(sorted xs')>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("ys", Arbitraries ["b", "xs"])) *})

lemma os_insert_list_mset [hoare_triple]:
  "<os_list xs b> os_insert_list ys b <\<lambda>r. \<exists>\<^sub>Axs'. os_list xs' r * \<up>(mset xs' = mset ys + mset xs)>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("ys", Arbitraries ["b", "xs"])) *})

definition insertion_sort :: "'a::{ord,heap} list \<Rightarrow> 'a list Heap" where
  "insertion_sort xs = do {
    p \<leftarrow> os_insert_list xs None;
    l \<leftarrow> extract_list p;
    return l
  }"
declare insertion_sort_def [sep_proc_defs]

setup {* add_backward2_prfstep @{thm properties_for_sort} *}
lemma insertion_sort_rule:
  "<emp> insertion_sort (xs::'a::{heap,linorder} list) <\<lambda>ys. \<up>(ys = sort xs) * true>"
  by (tactic {* auto2s_tac @{context} (HAVE "sorted ([]::'a list)") *})

subsection {* Merging two lists *}

partial_function (heap) merge_os_list ::
  "('a::{heap, ord}) os_list \<Rightarrow> 'a os_list \<Rightarrow> 'a os_list Heap" where
"merge_os_list p q = (
  if p = None then return q
  else if q = None then return p
  else do {
    np \<leftarrow> !(the p); nq \<leftarrow> !(the q);
    if val np \<le> val nq then
      do { npq \<leftarrow> merge_os_list (nxt np) q;
           (the p) := Node (val np) npq;
           return p
         }
    else
      do { pnq \<leftarrow> merge_os_list p (nxt nq);
           (the q) := Node (val nq) pnq;
           return q
         }
     })"
declare merge_os_list.simps [sep_proc_defs]

theorem list_double_induct: "\<forall>ys. P [] ys \<Longrightarrow> \<forall>xs. P xs [] \<Longrightarrow> \<forall>xs ys. P (tl xs) ys \<and> P xs (tl ys) \<longrightarrow> P xs ys \<Longrightarrow> P xs ys"
  by (tactic {* auto2s_tac @{context} (INDUCT ("xs", []) THEN INDUCT ("ys", [Arbitrary "xs"])) *})
setup {* add_prfstep_double_induction @{thm list_double_induct} *}

lemma merge_list_keys [hoare_triple]:
  "<os_list xs p * os_list ys q>
  merge_os_list p q
  <\<lambda>r. \<exists>\<^sub>Azs. os_list zs r * \<up>(set zs = set xs \<union> set ys)>"
  by (tactic {* auto2s_tac @{context} (
    DOUBLE_INDUCT (("xs", "ys"), Arbitraries ["p", "q"])) *})

lemma merge_list_sorted [hoare_triple]:
  "<os_list xs p * os_list ys q * \<up>(sorted xs) * \<up>(sorted ys)>
  merge_os_list p q
  <\<lambda>r. \<exists>\<^sub>Azs. os_list zs r * \<up>(sorted zs)>"
  by (tactic {* auto2s_tac @{context} (
    DOUBLE_INDUCT (("xs", "ys"), Arbitraries ["p", "q"])) *})

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
  by (tactic {* auto2s_tac @{context} (INDUCT ("xs", Arbitraries ["b"])) *})

subsection {* Higher-order functions *}

partial_function (heap) map_os_list ::
  "('a::heap \<Rightarrow> 'a) \<Rightarrow> 'a os_list \<Rightarrow> 'a os_list Heap" where
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
  by (tactic {* auto2s_tac @{context} (INDUCT ("xs", Arbitraries ["b"])) *})

partial_function (heap) filter_os_list ::
  "('a::heap \<Rightarrow> bool) \<Rightarrow> 'a os_list \<Rightarrow> 'a os_list Heap" where
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
  by (tactic {* auto2s_tac @{context} (INDUCT ("xs", Arbitraries ["b"])) *})

partial_function (heap) filter_os_list2 ::
  "('a::heap \<Rightarrow> bool) \<Rightarrow> 'a os_list \<Rightarrow> 'a os_list Heap" where
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
  by (tactic {* auto2s_tac @{context} (INDUCT ("xs", Arbitraries ["b"])) *})

partial_function (heap) fold_os_list ::
  "('a::heap \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a os_list \<Rightarrow> 'b \<Rightarrow> 'b Heap" where
"fold_os_list f b x = (case b of
    None \<Rightarrow> return x
  | Some p \<Rightarrow> do {
     v \<leftarrow> !p;
     r \<leftarrow> fold_os_list f (nxt v) (f (val v) x);
     return r})"
declare fold_os_list.simps [sep_proc_defs]

theorem fold_os_list_rule [hoare_triple]:
  "<os_list xs b> fold_os_list f b x <\<lambda>r. os_list xs b * \<up>(r = fold f xs x)>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("xs", Arbitraries ["b", "x"])) *})

end
