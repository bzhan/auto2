theory PriorityQueue
imports DynamicArray
begin

section {* Successor functions, eq-predecessor predicate *}

definition s1 :: "nat \<Rightarrow> nat" where "s1 m = 2 * m + 1"
definition s2 :: "nat \<Rightarrow> nat" where "s2 m = 2 * m + 2"

theorem s_inj [forward]:
  "s1 m = s1 m' \<Longrightarrow> m = m'" "s2 m = s2 m' \<Longrightarrow> m = m'" using s1_def s2_def by auto
theorem s_neq [resolve]:
  "s1 m \<noteq> s2 m'" "s1 m > m" "s2 m > m" "s2 m > s1 m" using s1_def s2_def by presburger+
setup {* add_forward_prfstep_cond @{thm s_neq(2)} [with_term "s1 ?m"] *}
setup {* add_forward_prfstep_cond @{thm s_neq(3)} [with_term "s2 ?m"] *}
setup {* add_forward_prfstep_cond @{thm s_neq(4)} [with_term "s2 ?m", with_term "s1 ?m"] *}

inductive eq_pred :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "eq_pred n n"
| "eq_pred n m \<Longrightarrow> eq_pred n (s1 m)"
| "eq_pred n m \<Longrightarrow> eq_pred n (s2 m)"
setup {* add_case_induct_rule @{thm eq_pred.cases} *}
setup {* add_prop_induct_rule @{thm eq_pred.induct} *}
setup {* add_resolve_prfstep @{thm eq_pred.intros(1)} *}
setup {* fold add_backward_prfstep @{thms eq_pred.intros(2,3)} *}
theorem eq_pred_parent1 [forward]: "eq_pred i (s1 k) \<Longrightarrow> i \<noteq> s1 k \<Longrightarrow> eq_pred i k"
  by (tactic {* auto2s_tac @{context} (
    LET "v = s1 k" THEN
    PROP_INDUCT ("eq_pred i v", "v = s1 k \<longrightarrow> i \<noteq> s1 k \<longrightarrow> eq_pred i k")) *})
theorem eq_pred_parent2 [forward]: "eq_pred i (s2 k) \<Longrightarrow> i \<noteq> s2 k \<Longrightarrow> eq_pred i k"
  by (tactic {* auto2s_tac @{context} (
    LET "v = s2 k" THEN
    PROP_INDUCT ("eq_pred i v", "v = s2 k \<longrightarrow> i \<noteq> s2 k \<longrightarrow> eq_pred i k")) *})
theorem eq_pred_cases [forward]:
  "eq_pred i j \<Longrightarrow> \<not>eq_pred (s1 i) j \<Longrightarrow> \<not>eq_pred (s2 i) j \<Longrightarrow> j = i \<or> j = s1 i \<or> j = s2 i"
  by (tactic {* auto2s_tac @{context} (
    PROP_INDUCT ("eq_pred i j", "\<not>eq_pred (s1 i) j \<longrightarrow> \<not>eq_pred (s2 i) j \<longrightarrow> j = i \<or> j = s1 i \<or> j = s2 i")) *})
theorem eq_pred_le [forward]: "eq_pred i j \<Longrightarrow> i \<le> j"
  by (tactic {* auto2s_tac @{context} (PROP_INDUCT ("eq_pred i j", "i \<le> j")) *})

section {* Heap property *}

(* The corresponding tree is a heap. *)
definition is_heap :: "'a::linorder list \<Rightarrow> bool" where
  "is_heap xs = (\<forall>i j. eq_pred i j \<longrightarrow> i < length xs \<longrightarrow> j < length xs \<longrightarrow> xs ! i \<le> xs ! j)"
setup {* add_rewrite_rule @{thm is_heap_def} *}

theorem is_heap_butlast: "is_heap xs \<Longrightarrow> is_heap (butlast xs)" by auto2
setup {* add_forward_prfstep_cond @{thm is_heap_butlast} [with_term "butlast ?xs"] *}

section {* Bubble-down *}

(* The corresponding tree is a heap, except k is not necessarily smaller than its descendents. *)
definition is_heap_partial1 :: "'a::linorder list \<Rightarrow> nat \<Rightarrow> bool" where
  "is_heap_partial1 xs k = (\<forall>i j. eq_pred i j \<longrightarrow> i < length xs \<longrightarrow> i \<noteq> k \<longrightarrow> j < length xs \<longrightarrow> xs ! i \<le> xs ! j)"
setup {* add_rewrite_rule @{thm is_heap_partial1_def} *}

theorem swap_zero_is_heap_partial1:
  "is_heap xs \<Longrightarrow> length xs > 0 \<Longrightarrow> is_heap_partial1 (butlast (list_swap xs 0 (length xs - 1))) 0"
  by (tactic {* auto2s_tac @{context}
    (LET "xs' = list_swap xs 0 (length xs - 1)" THEN
     HAVE_RULE "\<forall>i j. eq_pred i j \<longrightarrow> i < length xs - 1 \<longrightarrow> i \<noteq> 0 \<longrightarrow> j < length xs - 1 \<longrightarrow> xs' ! i \<le> xs' ! j" WITH
       CASE "j = 0") *})
setup {* add_forward_prfstep_cond @{thm swap_zero_is_heap_partial1}
  [with_term "butlast (list_swap ?xs 0 (length ?xs - 1))"] *}

theorem incr_is_heap_partial1:
  "is_heap xs \<Longrightarrow> k < length xs \<Longrightarrow> v \<ge> xs ! k \<Longrightarrow> is_heap_partial1 (list_update xs k v) k"
  by (tactic {* auto2s_tac @{context}
    (LET "xs' = list_update xs k v" THEN
     HAVE "\<forall>i j. eq_pred i j \<longrightarrow> i < length xs' \<longrightarrow> i \<noteq> k \<longrightarrow> j < length xs' \<longrightarrow> xs' ! i \<le> xs' ! j" WITH
       CASE "j = k") *})
setup {* add_forward_prfstep_cond @{thm incr_is_heap_partial1} [with_term "list_update ?xs ?k ?v"] *}

ML {*
val CASES_J =
  CASE "j = i" THEN CASE "j = s1 i" THEN CASE "j = s2 i" THEN
  CASE "eq_pred (s1 i) j"
*}

(* Two cases of switching with s1 k. *)
theorem bubble_down1:
  "is_heap_partial1 xs k \<Longrightarrow> s2 k < length xs \<Longrightarrow> xs ! (s1 k) \<le> xs ! (s2 k) \<Longrightarrow> xs ! k > xs ! (s1 k) \<Longrightarrow>
   is_heap_partial1 (list_swap xs k (s1 k)) (s1 k)"
  "is_heap_partial1 xs k \<Longrightarrow> s2 k \<ge> length xs \<Longrightarrow> s1 k < length xs \<Longrightarrow> xs ! k > xs ! (s1 k) \<Longrightarrow>
   is_heap_partial1 (list_swap xs k (s1 k)) (s1 k)"
  by (tactic {* auto2s_tac @{context}
    (LET "xs' = list_swap xs k (s1 k)" THEN
     HAVE "\<forall>i j. eq_pred i j \<longrightarrow> i < length xs \<longrightarrow> i \<noteq> s1 k \<longrightarrow> j < length xs \<longrightarrow> xs' ! i \<le> xs' ! j" WITH
      (CASE "i = k" WITH CASES_J THEN CASE "j = k" THEN CASE "j = s1 k")) *})+
setup {* add_forward_prfstep_cond @{thm bubble_down1(1)} [with_term "list_swap ?xs ?k (s1 ?k)"] *}
setup {* add_forward_prfstep_cond @{thm bubble_down1(2)} [with_term "list_swap ?xs ?k (s1 ?k)"] *}

(* One case of switching with s2 k. *)
theorem bubble_down2: "s2 k < length xs \<Longrightarrow> xs ! (s1 k) > xs ! (s2 k) \<Longrightarrow> xs ! k > xs ! (s2 k) \<Longrightarrow>
  is_heap_partial1 xs k \<Longrightarrow> is_heap_partial1 (list_swap xs k (s2 k)) (s2 k)"
  by (tactic {* auto2s_tac @{context}
    (LET "xs' = list_swap xs k (s2 k)" THEN
     HAVE "\<forall>i j. eq_pred i j \<longrightarrow> i < length xs \<longrightarrow> i \<noteq> s2 k \<longrightarrow> j < length xs \<longrightarrow> xs' ! i \<le> xs' ! j" WITH
      (CASE "i = k" WITH CASES_J THEN CASE "j = k" THEN CASE "j = s2 k")) *})
setup {* add_forward_prfstep_cond @{thm bubble_down2} [with_term "list_swap ?xs ?k (s2 ?k)"] *}

(* Four trivial cases. *)
theorem bubble_down3 [forward]:
  "is_heap_partial1 xs k \<Longrightarrow> xs ! k \<le> xs ! (s1 k) \<Longrightarrow> s2 k < length xs \<Longrightarrow> xs ! (s1 k) \<le> xs ! (s2 k) \<Longrightarrow> is_heap xs"
  "is_heap_partial1 xs k \<Longrightarrow> xs ! k \<le> xs ! (s2 k) \<Longrightarrow> s2 k < length xs \<Longrightarrow> xs ! (s1 k) > xs ! (s2 k) \<Longrightarrow> is_heap xs"
  "is_heap_partial1 xs k \<Longrightarrow> xs ! k \<le> xs ! (s1 k) \<Longrightarrow> s2 k \<ge> length xs \<Longrightarrow> s1 k < length xs \<Longrightarrow> is_heap xs"
  "is_heap_partial1 xs k \<Longrightarrow> s1 k \<ge> length xs \<Longrightarrow> is_heap xs"
  by (tactic {* auto2s_tac @{context}
   (HAVE "\<forall>i j. eq_pred i j \<longrightarrow> i < length xs \<longrightarrow> j < length xs \<longrightarrow> xs ! i \<le> xs ! j" WITH CASES_J) *})+
setup {* del_prfstep_thm @{thm is_heap_partial1_def} *}

partial_function (heap) bubble_down :: "'a::{heap,linorder} dynamic_array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "bubble_down a k = do {
    len \<leftarrow> array_length a;
    (if s2 k < len then do {
      vk \<leftarrow> array_nth a k;
      vs1k \<leftarrow> array_nth a (s1 k);
      vs2k \<leftarrow> array_nth a (s2 k);
      (if vs1k \<le> vs2k then
         if vk > vs1k then
           do { array_swap a k (s1 k); bubble_down a (s1 k) }
         else return ()
       else
         if vk > vs2k then
           do { array_swap a k (s2 k); bubble_down a (s2 k) }
         else return ()) }
     else if s1 k < len then do {
       vk \<leftarrow> array_nth a k;
       vs1k \<leftarrow> array_nth a (s1 k);
       (if vk > vs1k then
          do { array_swap a k (s1 k); bubble_down a (s1 k) }
        else return ()) }
     else return ()) }"
declare bubble_down.simps [sep_proc_defs]

theorem bubble_down_rule [hoare_triple]:
  "<dyn_array xs a * \<up>(is_heap_partial1 xs k)>
   bubble_down a k
   <\<lambda>_. \<exists>\<^sub>Axs'. dyn_array xs' a * \<up>(is_heap xs') * \<up>(length xs' = length xs) * \<up>(mset xs' = mset xs)>"
  by (tactic {* auto2s_tac @{context} (
    UPPER_STRONG_INDUCT ("k", "k < length xs", Arbitrary "xs" :: ApplyOns ["s1 k", "s2 k"])) *})

section {* Bubble-up *}

definition par :: "nat \<Rightarrow> nat" where "par m = (m - 1) div 2"

theorem ps_inverse [rewrite]:
  "par (s1 k) = k" "par (s2 k) = k" by (simp add: par_def s1_def s2_def)+

theorem p_neq: "(m::nat) \<noteq> 0 \<Longrightarrow> par m < m" using par_def by auto
setup {* add_forward_prfstep_cond @{thm p_neq} [with_term "par ?m"] *}

theorem p_cases: "i \<noteq> 0 \<Longrightarrow> i = s1 (par i) \<or> i = s2 (par i)" using par_def s1_def s2_def by auto
setup {* add_forward_prfstep_cond @{thm p_cases} [with_term "par ?m"] *}

theorem eq_pred_p1: "eq_pred i j \<Longrightarrow> i \<noteq> j \<Longrightarrow> eq_pred i (par j)"
  by (tactic {* auto2s_tac @{context} (CASE_INDUCT ("eq_pred i j")) *})
theorem eq_pred_p2: "eq_pred i j \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> eq_pred (par i) j"
  by (tactic {* auto2s_tac @{context} (
    PROP_INDUCT ("eq_pred i j", "i \<noteq> 0 \<longrightarrow> eq_pred (par i) j")) *})
theorem eq_pred_p3: "i \<noteq> 0 \<Longrightarrow> eq_pred (par i) i" by auto2
setup {* fold add_forward_prfstep [@{thm eq_pred_p1}, @{thm eq_pred_p2}] *}
setup {* add_forward_prfstep_cond @{thm eq_pred_p3} [with_term "par ?i"] *}

theorem heap_implies_hd_min [backward2]:
  "is_heap xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> i < length xs \<Longrightarrow> hd xs \<le> xs ! i"
  by (tactic {* auto2s_tac @{context}
    (CASE "i = 0" THEN STRONG_INDUCT ("i", [ApplyOn "par i"])) *})

(* The corresponding tree is a heap, except k is not necessarily greater than its ancestors. *)
definition is_heap_partial2 :: "'a::linorder list \<Rightarrow> nat \<Rightarrow> bool" where
  "is_heap_partial2 xs k = (\<forall>i j. eq_pred i j \<longrightarrow> i < length xs \<longrightarrow> j < length xs \<longrightarrow> j \<noteq> k \<longrightarrow> xs ! i \<le> xs ! j)"
setup {* add_rewrite_rule @{thm is_heap_partial2_def} *}

theorem bubble_up1 [forward]:
  "is_heap_partial2 xs k \<Longrightarrow> xs ! k < xs ! (par k) \<Longrightarrow> k \<noteq> 0 \<Longrightarrow> k < length xs \<Longrightarrow>
   is_heap_partial2 (list_swap xs k (par k)) (par k)"
  by (tactic {* auto2s_tac @{context}
    (LET "xs' = list_swap xs k (par k)" THEN
     HAVE "\<forall>i j. eq_pred i j \<longrightarrow> i < length xs \<longrightarrow> j < length xs \<longrightarrow> j \<noteq> par k \<longrightarrow> xs' ! i \<le> xs' ! j" WITH
       (CASE "j = k" WITH (CASE "i = k" THEN CASE "i = par k") THEN
        CASE "i = k" THEN CASE "i = par k")) *})

theorem bubble_up2 [forward]:
  "is_heap_partial2 xs k \<Longrightarrow> xs ! k \<ge> xs ! (par k) \<Longrightarrow> k \<noteq> 0 \<Longrightarrow> k < length xs \<Longrightarrow> is_heap xs"
  by (tactic {* auto2s_tac @{context}
   (HAVE "\<forall>i j. eq_pred i j \<longrightarrow> i < length xs \<longrightarrow> j < length xs \<longrightarrow> xs ! i \<le> xs ! j" WITH
    (CASE "j = k" WITH CASE "i = k")) *})

theorem bubble_up3 [forward]: "is_heap_partial2 xs 0 \<Longrightarrow> is_heap xs" by auto2
theorem bubble_up4 [forward]: "is_heap_partial2 xs k \<Longrightarrow> k \<ge> length xs \<Longrightarrow> is_heap xs" by auto2

theorem append_is_heap_partial2:
  "is_heap xs \<Longrightarrow> is_heap_partial2 (xs @ [x]) (length xs)" by auto2
setup {* add_forward_prfstep_cond @{thm append_is_heap_partial2} [with_term "?xs @ [?x]"] *}

theorem desc_is_heap_partial2:
  "is_heap xs \<Longrightarrow> k < length xs \<Longrightarrow> v < xs ! k \<Longrightarrow> is_heap_partial2 (list_update xs k v) k"
  by (tactic {* auto2s_tac @{context}
   (LET "xs' = list_update xs k v" THEN
    HAVE "\<forall>i j. eq_pred i j \<longrightarrow> i < length xs' \<longrightarrow> j < length xs' \<longrightarrow> j \<noteq> k \<longrightarrow> xs' ! i \<le> xs' ! j" WITH
      CASE "i = k") *})
setup {* add_forward_prfstep_cond @{thm desc_is_heap_partial2} [with_term "list_update ?xs ?k ?v"] *}

setup {* fold del_prfstep_thm [@{thm eq_pred_p1}, @{thm eq_pred_p2}, @{thm eq_pred_p3}] *}
setup {* del_prfstep_thm @{thm p_cases} *}
setup {* del_prfstep_thm @{thm is_heap_partial2_def} *}

partial_function (heap) bubble_up :: "'a::{heap,linorder} dynamic_array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "bubble_up a k =
    (if k = 0 then return () else do {
       len \<leftarrow> array_length a;
       (if k < len then do {
          vk \<leftarrow> array_nth a k;
          vpk \<leftarrow> array_nth a (par k);
          (if vk < vpk then
             do { array_swap a k (par k); bubble_up a (par k) }
           else return ()) }
        else return ())})"
declare bubble_up.simps [sep_proc_defs]

theorem bubble_up_rule [hoare_triple]:
  "<dyn_array xs a * \<up>(is_heap_partial2 xs k)>
   bubble_up a k
   <\<lambda>_. \<exists>\<^sub>Axs'. dyn_array xs' a * \<up>(is_heap xs') * \<up>(length xs' = length xs) * \<up>(mset xs' = mset xs)>"
  by (tactic {* auto2s_tac @{context} (
    STRONG_INDUCT ("k", [Arbitrary "xs", ApplyOn "par k"])) *})

section {* Insertion *}

definition insert_pqueue :: "'a::{heap,linorder} \<Rightarrow> 'a dynamic_array \<Rightarrow> 'a dynamic_array Heap" where
  "insert_pqueue x d = do {
     d' \<leftarrow> push_array x d;
     len \<leftarrow> array_length d';
     bubble_up d' (len - 1);
     return d'
   }"
declare insert_pqueue_def [sep_proc_defs]

theorem insert_pqueue_rule:
  "<dyn_array xs p * \<up>(is_heap xs)>
   insert_pqueue x p
   <\<lambda>r. \<exists>\<^sub>Axs'. dyn_array xs' r * \<up>(is_heap xs') * \<up>(mset xs' = mset xs + {#x#})>\<^sub>t" by auto2

section {* Delete-min *}

theorem mset_butlast [rewrite]: "length xs > 0 \<Longrightarrow> mset (butlast xs) = mset xs - {# last xs #}"
  by (metis add_diff_cancel_right' append_butlast_last_id length_greater_0_conv list.size(3)
      mset.simps(2) size_eq_0_iff_empty size_mset union_code)

theorem last_swap: "length xs > 0 \<Longrightarrow> (list_swap xs 0 (length xs - 1)) ! (length xs - 1) = xs ! 0"
  by (simp add: list_swap_eval(2))

theorem last_swap' [rewrite]: "length xs > 0 \<Longrightarrow> last (list_swap xs 0 (length xs - 1)) = hd xs"
  by (metis hd_conv_nth last_conv_nth last_swap length_swap list.size(3) not_gr0)

definition delete_min_pqueue ::
  "'a::{heap,linorder} dynamic_array \<Rightarrow> ('a \<times> 'a dynamic_array) Heap" where
  "delete_min_pqueue p = do {
    len \<leftarrow> array_length p;
    (if len = 0 then raise ''delete_min''
     else do {
       array_swap p 0 (len - 1);
       (x', r) \<leftarrow> pop_array p;
       bubble_down r 0;
       return (x', r)
     })}"
declare delete_min_pqueue_def [sep_proc_defs]

theorem delete_min_pqueue_rule:
  "<dyn_array xs p * \<up>(is_heap xs) * \<up>(length xs > 0)>
   delete_min_pqueue p
   <\<lambda>(x, r). \<exists>\<^sub>Axs'. dyn_array xs' r * \<up>(is_heap xs') * \<up>(x = hd xs) * \<up>(mset xs' = mset xs - {#x#})>"
  by auto2

end
