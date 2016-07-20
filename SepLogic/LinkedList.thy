(* Linked lists, based on ListSeg in Separation_Logic_Imperative_HOL/Examples. *)

theory LinkedList
imports SepAuto
begin

subsection {* Nodes *}
text {*
  We define a node of a list to contain a data value and a next pointer.
  As Imperative HOL does not support null-pointers, we make the next-pointer
  an optional value, @{text "None"} representing a null pointer.

  Unfortunately, Imperative HOL requires some boilerplate code to define 
  a datatype.
*}
datatype 'a node = Node (val: "'a") (nxt: "'a node ref option")

text {* Encoding to natural numbers, as required by Imperative/HOL *}

fun node_encode :: "'a::heap node \<Rightarrow> nat" where
  "node_encode (Node x r) = to_nat (x, r)"

instance node :: (heap) heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "node_encode"])
  apply (case_tac x, simp_all, case_tac y, simp_all)
  ..

setup {* fold add_rewrite_rule @{thms node.sel} *}
theorem node_constr: "Node a n = Node a' n' \<Longrightarrow> a = a' \<and> n = n'" by simp
setup {* add_forward_prfstep_cond (conj_left_th @{thm node_constr}) [with_cond "?a \<noteq> ?a'"]
  #> add_forward_prfstep_cond (conj_right_th @{thm node_constr}) [with_cond "?n \<noteq> ?n'"] *}

subsection {* List Segment Assertion *}
text {*
  Intuitively, @{text "lseg l p s"} describes a list starting at @{text "p"} and
  ending with a pointer @{text "s"}. The content of the list are @{text "l"}.
  Note that the pointer @{text "s"} may also occur earlier in the list, in which
  case it is handled as a usual next-pointer.
*}
fun lseg :: "'a::heap list \<Rightarrow> 'a node ref option \<Rightarrow> 'a node ref option \<Rightarrow> assn" where
  "lseg [] p s = \<up>(p = s)"
| "lseg (x # l) (Some p) s = (\<exists>\<^sub>Aq. p \<mapsto>\<^sub>r Node x q * lseg l q s)"
| "lseg (x # l) None s = false"
setup {* fold add_rewrite_rule @{thms lseg.simps} *}

(* Make use of lseg [] p s = \<up>(p=s) in \<exists> goals. *)
theorem ex_lseg_empty [backward]:
  "h \<Turnstile> Q y \<Longrightarrow> \<exists>x. h \<Turnstile> lseg [] x y * Q x"
  "h \<Turnstile> Q x \<Longrightarrow> \<exists>y. h \<Turnstile> lseg [] x y * Q y" by (simp add: mod_pure_star_dist mult.commute)+

lemma lseg_split_iff1 [rewrite]: "lseg l None None = \<up>(l = [])" by auto2

theorem lseg_is_some: "h \<Turnstile> lseg (x # l) p s * Qu \<Longrightarrow> p \<noteq> None" by auto2
setup {* add_forward_prfstep_cond @{thm lseg_is_some} [with_cond "?p \<noteq> Some ?q"] *}

lemma lseg_split_iff2 [forward_ent]:
  "lseg (x # xs) (Some p) q \<Longrightarrow>\<^sub>A (\<exists>\<^sub>An. p \<mapsto>\<^sub>r (Node x n) * lseg xs n q)" by auto2

lemma lseg_split_elim:
  "\<exists>n. h \<Turnstile> p \<mapsto>\<^sub>r Node x n * Ql n \<Longrightarrow> h \<Turnstile> p \<mapsto>\<^sub>r Node x n * Q \<Longrightarrow>
   h \<Turnstile> p \<mapsto>\<^sub>r Node x n * Ql n" by auto2
setup {* add_gen_prfstep ("lseg_split_elim", forward_descs @{thm lseg_split_elim} @ [ShadowFirst]) *}

lemma lseg_prepend [forward_ent]:
  "p \<mapsto>\<^sub>r Node x q * lseg l q s \<Longrightarrow>\<^sub>A lseg (x # l) (Some p) s" by auto2

lemma lseg_append [forward_ent]:
  "lseg l p (Some s) * s \<mapsto>\<^sub>r Node x q \<Longrightarrow>\<^sub>A lseg (l @ [x]) p q"
  by (tactic {* auto2s_tac @{context} (INDUCT ("l", [Arbitrary "p"])) *})
setup {* del_prfstep_thm @{thm lseg.simps(2)} *}

lemma lseg_conc [forward_ent]:
  "lseg l1 p q * lseg l2 q r \<Longrightarrow>\<^sub>A lseg (l1 @ l2) p r"
  by (tactic {* auto2s_tac @{context} (INDUCT ("l1", [Arbitrary "p"])) *})

lemma lseg_split [resolve]:
  "lseg (l1 @ l2) p r \<Longrightarrow>\<^sub>A \<exists>\<^sub>Aq. lseg l1 p q * lseg l2 q r"
  by (tactic {* auto2s_tac @{context} (INDUCT ("l1", [Arbitrary "p"])) *})

lemma lseg_prec1:
  "h \<Turnstile> lseg l p (Some q) * q \<mapsto>\<^sub>r x * F1 \<Longrightarrow> h \<Turnstile> lseg l' p (Some q) * q \<mapsto>\<^sub>r x * F2 \<Longrightarrow> l = l'"
  by (tactic {* auto2s_tac @{context}
    (INDUCT ("l", Arbitraries ["p", "l'", "F1", "F2"]) THEN CASE "l' = []") *})

lemma lseg_prec2 [sep_prec_thms]:
  "h \<Turnstile> lseg l p None * F1 \<Longrightarrow> h \<Turnstile> lseg l' p None * F2 \<Longrightarrow> l = l'"
  by (tactic {* auto2s_tac @{context}
    (INDUCT ("l", Arbitraries ["p", "l'", "F1", "F2"]) THEN CASE "l' = []") *})

lemma lseg_prec3:
  "h \<Turnstile> lseg l p q * F1 \<Longrightarrow> h \<Turnstile> lseg l p q' * F2 \<Longrightarrow> q = q'"
  by (tactic {* auto2s_tac @{context} (INDUCT ("l", Arbitraries ["p", "F1", "F2"])) *})

(* Linked lists with null at end. *)
type_synonym 'a os_list = "'a node ref option"

abbreviation os_list :: "'a list \<Rightarrow> ('a::heap) os_list \<Rightarrow> assn" where
  "os_list l p \<equiv> lseg l p None"

theorem os_list_some [resolve]: "\<not>h \<Turnstile> os_list [] (Some p) * Ru" by auto2
theorem mod_os_list_eq [backward1]: "l1 = l2 \<Longrightarrow> h \<Turnstile> os_list l1 r \<Longrightarrow> h \<Turnstile> os_list l2 r" by simp
theorem os_list_none [match_code_pos_emp]: "os_list [] None = emp" by auto2

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

lemma os_prepend_rule [next_code_pos]:
  "<os_list xs n> os_prepend x n <os_list (x # xs)>" by auto2

definition os_pop :: "'a::heap os_list \<Rightarrow> ('a \<times> 'a os_list) Heap" where
  "os_pop r = (case r of
    None \<Rightarrow> raise ''Empty Os_list'' |
    Some p \<Rightarrow> do {m \<leftarrow> !p; return (val m, nxt m)})"
declare os_pop_def [sep_proc_defs]

lemma os_pop_rule [next_code_pos]:
  "<os_list xs (Some p)>
   os_pop (Some p)
   <\<lambda>(x,r'). os_list (tl xs) r' * p \<mapsto>\<^sub>r (Node x r') * \<up>(x = hd xs)>" by auto2

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

lemma os_reverse_aux_rule [next_code_pos]:
  "<os_list xs p * os_list ys q> 
    os_reverse_aux q p 
  <os_list ((rev xs) @ ys)>"
  by (tactic {* auto2s_tac @{context}
    (INDUCT ("xs", Arbitraries ["p", "q", "ys"])) *})

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

lemma os_rem_rule [next_code_pos]:
  "<os_list xs b> os_rem x b <\<lambda>r. os_list (removeAll x xs) r>\<^sub>t"
  by (tactic {* auto2s_tac @{context} (INDUCT ("xs", Arbitraries ["b"])) *})

subsubsection {* Iterator *}

type_synonym 'a os_list_it = "'a os_list"

definition os_is_it :: "('a::heap) list \<Rightarrow> 'a node ref option \<Rightarrow> 'a list \<Rightarrow> 'a node ref option \<Rightarrow> assn" where
  "os_is_it l p l2 it = (\<exists>\<^sub>Al1. lseg l1 p it * os_list l2 it * \<up>(l = l1 @ l2))"
setup {* add_rewrite_rule @{thm os_is_it_def} *}

theorem os_is_it_empty [backward]: "h \<Turnstile> os_list l p \<Longrightarrow> h \<Turnstile> os_is_it l p l p"
  by (tactic {* auto2s_tac @{context} (OBTAIN "h \<Turnstile> lseg [] p p * os_list l p") *})

definition os_it_init :: "'a os_list \<Rightarrow> ('a os_list_it) Heap" where
  "os_it_init l = return l"
declare os_it_init_def [sep_proc_defs]

definition os_it_next :: "'a::heap os_list \<Rightarrow> ('a \<times> 'a os_list) Heap" where
  "os_it_next it = os_pop it"
declare os_it_next_def [sep_proc_defs]

definition os_it_has_next :: "'a os_list_it \<Rightarrow> bool Heap" where
  "os_it_has_next it = return (it \<noteq> None)"
declare os_it_has_next_def [sep_proc_defs]

theorem os_it_init_rule [next_code_pos]:
  "<os_list l p> os_it_init p <os_is_it l p l>" by auto2

theorem os_is_it_rule [forward_ent]: "os_is_it l p l' it \<Longrightarrow>\<^sub>A os_list l p" by auto2

theorem os_is_has_next_rule [next_code_pos]:
  "<os_is_it l p l' it> os_it_has_next it <\<lambda>r. os_is_it l p l' it * \<up>(r = (l' \<noteq> []))>"
  by auto2

theorem os_is_has_next_rule' [forward]:
  "h \<Turnstile> os_is_it l p (x # xs) it * Ru \<Longrightarrow> it \<noteq> None" by auto2

theorem os_it_next_rule [next_code_pos]:
  "<os_is_it l p l' (Some q)> os_it_next (Some q) <\<lambda>(a, it'). os_is_it l p (tl l') it' * \<up>(a = hd l')>"
  by (tactic {* auto2s_tac @{context} (OBTAIN "l' \<noteq> []") *})

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

lemma os_sum'_rule [next_code_pos]:
  "<os_is_it l p l' it>
    os_sum' it s
  <\<lambda>r. os_list l p * \<up>(r = s + listsum l')>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("l'", Arbitraries ["it", "s"])) *})

definition os_sum :: "int node ref option \<Rightarrow> int Heap" where
  "os_sum p \<equiv> do {
    it \<leftarrow> os_it_init p;
    os_sum' it 0
  }"
declare os_sum_def [sep_proc_defs]

lemma os_sum_rule:
  "<os_list l p> os_sum p <\<lambda>r. os_list l p * \<up>(r = listsum l)>" by auto2

subsubsection {* Insert in order *}

partial_function (heap) os_insert
  :: "'a::{ord,heap} \<Rightarrow> 'a os_list \<Rightarrow> 'a os_list Heap" where
  "os_insert x b = (case b of
      None \<Rightarrow> os_prepend x None
    | Some p \<Rightarrow> do {
        v \<leftarrow> !p;
        (if x < val v then os_prepend x b
         else do {
           q \<leftarrow> os_insert x (nxt v);
           p := Node (val v) q;
           return (Some p) }) })"
declare os_insert.simps [sep_proc_defs]

lemma os_insert_mset_rule [next_code_pos]:
  "<os_list xs b> os_insert x b <\<lambda>r. \<exists>\<^sub>Axs'. os_list xs' r * \<up>(mset xs' = {#x#} + mset xs)>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("xs", Arbitraries ["b"])) *})

lemma os_insert_set_rule [next_code_pos]:
  "<os_list xs b> os_insert x b <\<lambda>r. \<exists>\<^sub>Axs'. os_list xs' r * \<up>(set xs' = {x} \<union> set xs)>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("xs", Arbitraries ["b"])) *})

lemma os_insert_sorted [next_code_pos]:
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

theorem extract_list_rule [next_code_pos_direct]:
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

lemma os_insert_list_sorted [next_code_pos]:
  "<os_list xs b * \<up>(sorted xs)> os_insert_list ys b <\<lambda>r. \<exists>\<^sub>Axs'. os_list xs' r * \<up>(sorted xs')>"
  by (tactic {* auto2s_tac @{context} (INDUCT ("ys", Arbitraries ["b", "xs"])) *})

lemma os_insert_list_mset [next_code_pos]:
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
  by (tactic {* auto2s_tac @{context} (OBTAIN "sorted ([]::'a list)") *})

end
