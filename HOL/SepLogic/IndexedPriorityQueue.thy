theory IndexedPriorityQueue
imports DynamicArray ArrayMap
begin

section {* Successor functions, eq-pred predicate *}

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
@proof
  @let "v = s1 k" @then
  @prop_induct "eq_pred i v" "v = s1 k \<longrightarrow> i \<noteq> s1 k \<longrightarrow> eq_pred i k"
@qed

theorem eq_pred_parent2 [forward]: "eq_pred i (s2 k) \<Longrightarrow> i \<noteq> s2 k \<Longrightarrow> eq_pred i k"
@proof
  @let "v = s2 k" @then
  @prop_induct "eq_pred i v" "v = s2 k \<longrightarrow> i \<noteq> s2 k \<longrightarrow> eq_pred i k"
@qed

theorem eq_pred_cases [forward]:
  "eq_pred i j \<Longrightarrow> \<not>eq_pred (s1 i) j \<Longrightarrow> \<not>eq_pred (s2 i) j \<Longrightarrow> j = i \<or> j = s1 i \<or> j = s2 i"
@proof
  @prop_induct "eq_pred i j" "\<not>eq_pred (s1 i) j \<longrightarrow> \<not>eq_pred (s2 i) j \<longrightarrow> j = i \<or> j = s1 i \<or> j = s2 i"
@qed

theorem eq_pred_le [forward]: "eq_pred i j \<Longrightarrow> i \<le> j"
@proof @prop_induct "eq_pred i j" "i \<le> j" @qed

section {* Heap property *}

(* The corresponding tree is a heap. *)
definition is_heap :: "('a \<times> 'b::linorder) list \<Rightarrow> bool" where [rewrite]:
  "is_heap xs = (\<forall>i j. eq_pred i j \<longrightarrow> j < length xs \<longrightarrow> snd (xs ! i) \<le> snd (xs ! j))"
setup {* add_property_const @{term is_heap} *}

lemma is_heapD:
  "is_heap xs \<Longrightarrow> eq_pred i j \<Longrightarrow> j < length xs \<Longrightarrow> snd (xs ! i) \<le> snd (xs ! j)" by auto2
setup {* add_forward_prfstep_cond @{thm is_heapD} [with_term "?xs ! ?j"] *}
setup {* del_prfstep_thm_eqforward @{thm is_heap_def} *}

theorem is_heap_butlast: "is_heap xs \<Longrightarrow> is_heap (butlast xs)" by auto2
setup {* add_forward_prfstep_cond @{thm is_heap_butlast} [with_term "butlast ?xs"] *}

section {* Bubble-down *}

(* The corresponding tree is a heap, except k is not necessarily smaller than its descendents. *)
definition is_heap_partial1 :: "('a \<times> 'b::linorder) list \<Rightarrow> nat \<Rightarrow> bool" where [rewrite]:
  "is_heap_partial1 xs k = (\<forall>i j. eq_pred i j \<longrightarrow> i \<noteq> k \<longrightarrow> j < length xs \<longrightarrow> snd (xs ! i) \<le> snd (xs ! j))"

theorem swap_zero_is_heap_partial1:
  "is_heap xs \<Longrightarrow> length xs > 0 \<Longrightarrow> xs' = list_swap xs 0 (length xs - 1) \<Longrightarrow> is_heap_partial1 (butlast xs') 0"
@proof
  @have "\<forall>i j. eq_pred i j \<longrightarrow> i \<noteq> 0 \<longrightarrow> j < length xs - 1 \<longrightarrow> snd (xs' ! i) \<le> snd (xs' ! j)" @with
    @case "j = 0"
  @end
@qed
setup {* add_forward_prfstep_cond @{thm swap_zero_is_heap_partial1} [with_term "butlast ?xs'"] *}

theorem incr_is_heap_partial1:
  "is_heap xs \<Longrightarrow> k < length xs \<Longrightarrow> v \<ge> snd (xs ! k) \<Longrightarrow> xs' = list_update xs k (fst (xs ! k), v) \<Longrightarrow>
   is_heap_partial1 xs' k"
@proof
  @have "\<forall>i j. eq_pred i j \<longrightarrow> i \<noteq> k \<longrightarrow> j < length xs' \<longrightarrow> snd (xs' ! i) \<le> snd (xs' ! j)" @with
    @case "j = k"
  @end
@qed
setup {* add_forward_prfstep_cond @{thm incr_is_heap_partial1} [with_term "?xs'"] *}

(* Two cases of switching with s1 k. *)
theorem bubble_down1:
  "is_heap_partial1 xs k \<Longrightarrow> s2 k < length xs \<Longrightarrow> snd (xs ! (s1 k)) \<le> snd (xs ! (s2 k)) \<Longrightarrow>
   snd (xs ! k) > snd (xs ! (s1 k)) \<Longrightarrow> is_heap_partial1 (list_swap xs k (s1 k)) (s1 k)" by auto2
setup {* add_forward_prfstep_cond @{thm bubble_down1} [with_term "list_swap ?xs ?k (s1 ?k)"] *}

theorem bubble_down2:
  "is_heap_partial1 xs k \<Longrightarrow> s2 k \<ge> length xs \<Longrightarrow> s1 k < length xs \<Longrightarrow> snd (xs ! k) > snd (xs ! (s1 k)) \<Longrightarrow>
   is_heap_partial1 (list_swap xs k (s1 k)) (s1 k)" by auto2
setup {* add_forward_prfstep_cond @{thm bubble_down2} [with_term "list_swap ?xs ?k (s1 ?k)"] *}

(* One case of switching with s2 k. *)
theorem bubble_down3:
  "s2 k < length xs \<Longrightarrow> snd (xs ! (s1 k)) > snd (xs ! (s2 k)) \<Longrightarrow> snd (xs ! k) > snd (xs ! (s2 k)) \<Longrightarrow>
   is_heap_partial1 xs k \<Longrightarrow> xs' = list_swap xs k (s2 k) \<Longrightarrow> is_heap_partial1 xs' (s2 k)"
@proof
  @have "\<forall>i j. eq_pred i j \<longrightarrow> i \<noteq> s2 k \<longrightarrow> j < length xs \<longrightarrow> snd (xs' ! i) \<le> snd (xs' ! j)" @with
    @case "i = k" @with @case "eq_pred (s1 i) j" @end
  @end
@qed
setup {* add_forward_prfstep_cond @{thm bubble_down3} [with_term "?xs'"] *}

(* Four trivial cases. *)
theorem bubble_down4 [forward]:
  "is_heap_partial1 xs k \<Longrightarrow> snd (xs ! k) \<le> snd (xs ! (s1 k)) \<Longrightarrow> s2 k < length xs \<Longrightarrow>
   snd (xs ! (s1 k)) \<le> snd (xs ! (s2 k)) \<Longrightarrow> is_heap xs"
@proof
  @have "\<forall>i j. eq_pred i j \<longrightarrow> j < length xs \<longrightarrow> snd (xs ! i) \<le> snd (xs ! j)" @with
    @case "eq_pred (s1 i) j"
  @end
@qed

theorem bubble_down5 [forward]:
  "is_heap_partial1 xs k \<Longrightarrow> snd (xs ! k) \<le> snd (xs ! (s2 k)) \<Longrightarrow> s2 k < length xs \<Longrightarrow>
   snd (xs ! (s1 k)) > snd (xs ! (s2 k)) \<Longrightarrow> is_heap xs"
@proof
  @have "\<forall>i j. eq_pred i j \<longrightarrow> j < length xs \<longrightarrow> snd (xs ! i) \<le> snd (xs ! j)" @with
    @case "eq_pred (s1 i) j"
  @end
@qed

theorem bubble_down6 [forward]:
  "is_heap_partial1 xs k \<Longrightarrow> snd (xs ! k) \<le> snd (xs ! (s1 k)) \<Longrightarrow> s2 k \<ge> length xs \<Longrightarrow>
   s1 k < length xs \<Longrightarrow> is_heap xs"
@proof
  @have "\<forall>i j. eq_pred i j \<longrightarrow> j < length xs \<longrightarrow> snd (xs ! i) \<le> snd (xs ! j)" @with
    @case "eq_pred (s1 i) j"
  @end
@qed

theorem bubble_down7 [forward]:
  "is_heap_partial1 xs k \<Longrightarrow> s1 k \<ge> length xs \<Longrightarrow> is_heap xs"
@proof
  @have "\<forall>i j. eq_pred i j \<longrightarrow> j < length xs \<longrightarrow> snd (xs ! i) \<le> snd (xs ! j)" @with
    @case "eq_pred (s1 i) j"
  @end
@qed

setup {* del_prfstep_thm @{thm is_heap_partial1_def} *}

section {* Bubble-up *}

definition par :: "nat \<Rightarrow> nat" where "par m = (m - 1) div 2"

theorem ps_inverse [rewrite]:
  "par (s1 k) = k" "par (s2 k) = k" by (simp add: par_def s1_def s2_def)+

theorem p_neq: "m \<noteq> 0 \<Longrightarrow> par m < m" using par_def by auto
setup {* add_forward_prfstep_cond @{thm p_neq} [with_term "par ?m"] *}

theorem p_cases: "m \<noteq> 0 \<Longrightarrow> m = s1 (par m) \<or> m = s2 (par m)" using par_def s1_def s2_def by auto
setup {* add_forward_prfstep_cond @{thm p_cases} [with_term "par ?m"] *}

theorem eq_pred_p1 [forward]: "eq_pred i j \<Longrightarrow> i \<noteq> j \<Longrightarrow> eq_pred i (par j)"
@proof @case_induct "eq_pred i j" @qed

theorem eq_pred_p2 [forward]: "eq_pred i j \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> eq_pred (par i) j"
@proof @prop_induct "eq_pred i j" "i \<noteq> 0 \<longrightarrow> eq_pred (par i) j" @qed

theorem eq_pred_p3: "i \<noteq> 0 \<Longrightarrow> eq_pred (par i) i" by auto2
setup {* add_forward_prfstep_cond @{thm eq_pred_p3} [with_term "par ?i"] *}

theorem heap_implies_hd_min [backward2]:
  "is_heap xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> i < length xs \<Longrightarrow> snd (hd xs) \<le> snd (xs ! i)"
@proof
  @strong_induct i
  @case "i = 0" @then @apply_induct_hyp "par i"
@qed

(* The corresponding tree is a heap, except k is not necessarily greater than its ancestors. *)
definition is_heap_partial2 :: "('a \<times> 'b::linorder) list \<Rightarrow> nat \<Rightarrow> bool" where
  "is_heap_partial2 xs k = (\<forall>i j. eq_pred i j \<longrightarrow> j < length xs \<longrightarrow> j \<noteq> k \<longrightarrow> snd (xs ! i) \<le> snd (xs ! j))"
setup {* add_rewrite_rule @{thm is_heap_partial2_def} *}

theorem bubble_up1 [forward]:
  "is_heap_partial2 xs k \<Longrightarrow> snd (xs ! k) < snd (xs ! (par k)) \<Longrightarrow> k \<noteq> 0 \<Longrightarrow> k < length xs \<Longrightarrow>
   is_heap_partial2 (list_swap xs k (par k)) (par k)" by auto2

theorem bubble_up2 [forward]:
  "is_heap_partial2 xs k \<Longrightarrow> snd (xs ! k) \<ge> snd (xs ! (par k)) \<Longrightarrow> k \<noteq> 0 \<Longrightarrow> k < length xs \<Longrightarrow> is_heap xs"
@proof
  @have "\<forall>i j. eq_pred i j \<longrightarrow> j < length xs \<longrightarrow> snd (xs ! i) \<le> snd (xs ! j)" @with
    @case "j = k" @with @case "i = k" @end
  @end
@qed

theorem bubble_up3 [forward]: "is_heap_partial2 xs 0 \<Longrightarrow> is_heap xs" by auto2
theorem bubble_up4 [forward]: "is_heap_partial2 xs k \<Longrightarrow> k \<ge> length xs \<Longrightarrow> is_heap xs" by auto2

theorem append_is_heap_partial2:
  "is_heap xs \<Longrightarrow> is_heap_partial2 (xs @ [x]) (length xs)" by auto2
setup {* add_forward_prfstep_cond @{thm append_is_heap_partial2} [with_term "?xs @ [?x]"] *}

theorem desc_is_heap_partial2:
  "is_heap xs \<Longrightarrow> k < length xs \<Longrightarrow> v < snd (xs ! k) \<Longrightarrow>
   xs' = list_update xs k (fst (xs ! k), v) \<Longrightarrow> is_heap_partial2 xs' k" by auto2
setup {* add_forward_prfstep_cond @{thm desc_is_heap_partial2} [with_term "?xs'"] *}

setup {* fold del_prfstep_thm [@{thm eq_pred_p1}, @{thm eq_pred_p2}, @{thm eq_pred_p3}] *}
setup {* del_prfstep_thm @{thm p_cases} *}
setup {* del_prfstep_thm @{thm is_heap_partial2_def} *}

section {* Delete-min *}

theorem mset_butlast [rewrite]: "length xs > 0 \<Longrightarrow> mset (butlast xs) = mset xs - {# last xs #}"
  by (metis add_diff_cancel_right' append_butlast_last_id length_greater_0_conv list.size(3)
      mset.simps(2) size_eq_0_iff_empty size_mset union_code)

lemma last_swap' [rewrite]:
  "length xs > 0 \<Longrightarrow> last (list_swap xs 0 (length xs - 1)) = hd xs"
@proof
  @let "xs' = list_swap xs 0 (length xs - 1)"
  @have "last xs' = xs' ! (length xs - 1)"
  @have "hd xs = xs ! 0"
@qed

section {* Indexed priority queue *}

datatype 'a indexed_pqueue =
  Indexed_PQueue (pqueue: "(nat \<times> 'a) dynamic_array") (index: "nat array_map")
setup {* add_rewrite_rule_back @{thm indexed_pqueue.collapse} *}
setup {* add_rewrite_rule @{thm indexed_pqueue.case} *}
setup {* fold add_rewrite_rule @{thms indexed_pqueue.sel} *}

definition index_of_pqueue :: "(nat \<times> 'a) list \<Rightarrow> (nat, nat) map \<Rightarrow> bool" where [rewrite]:
  "index_of_pqueue xs m = (
    (\<forall>i<length xs. m\<langle>fst (xs ! i)\<rangle> = Some i) \<and>
    (\<forall>i k. m\<langle>k\<rangle> = Some i \<longrightarrow> i < length xs \<and> fst (xs ! i) = k))"

lemma index_of_pqueueD1 [forward]:
  "index_of_pqueue xs m \<Longrightarrow> \<forall>i. i < length xs \<longrightarrow> m \<langle>fst (xs ! i)\<rangle> = Some i" by auto2

lemma index_of_pqueueD2 [forward]:
  "index_of_pqueue xs m \<Longrightarrow> m\<langle>k\<rangle> = Some i \<Longrightarrow> i < length xs \<and> fst (xs ! i) = k" by auto2
setup {* del_prfstep_thm_eqforward @{thm index_of_pqueue_def} *}

definition unique_keys :: "(nat \<times> 'a) list \<Rightarrow> bool" where [rewrite]:
  "unique_keys xs = (\<forall>m n. m < length xs \<longrightarrow> n < length xs \<longrightarrow> m \<noteq> n \<longrightarrow> fst (xs ! m) \<noteq> fst (xs ! n))"
setup {* add_property_const @{term unique_keys} *}

lemma unique_keysD:
  "unique_keys xs \<Longrightarrow> m < length xs \<Longrightarrow> n < length xs \<Longrightarrow> m \<noteq> n \<Longrightarrow> fst (xs ! m) \<noteq> fst (xs ! n)" by auto2
setup {* add_forward_prfstep_cond @{thm unique_keysD} [with_term "?xs ! ?m", with_term "?xs ! ?n"] *}
setup {* del_prfstep_thm_eqforward @{thm unique_keys_def} *}
  
theorem has_index_unique_key [forward]:
  "index_of_pqueue xs m \<Longrightarrow> unique_keys xs" by auto2

definition key_within_range :: "(nat \<times> 'a) list \<Rightarrow> nat \<Rightarrow> bool" where
  "key_within_range xs n = (\<forall>p. p \<in># mset xs \<longrightarrow> fst p < n)"
setup {* add_rewrite_rule @{thm key_within_range_def} *}

theorem key_within_range_on_index:
  "i < length xs \<Longrightarrow> key_within_range xs n \<Longrightarrow> fst (xs ! i) < n" by auto2
setup {* add_forward_prfstep_cond @{thm key_within_range_on_index} [with_term "?xs ! ?i"] *}

fun idx_pqueue :: "(nat \<times> 'a::{heap,linorder}) list \<Rightarrow> 'a indexed_pqueue \<Rightarrow> assn" where
  "idx_pqueue xs (Indexed_PQueue pq idx) =
    (\<exists>\<^sub>Am. dyn_array xs pq * amap m idx * \<up>(index_of_pqueue xs m) * \<up>(key_within_range xs (alen idx)))"
setup {* add_rewrite_ent_rule @{thm idx_pqueue.simps} *}

setup {* add_forward_prfstep @{thm dyn_array_prec} *}
theorem idx_pqueue_prec [sep_prec_thms]:
  "h \<Turnstile> idx_pqueue xs p * F1 \<Longrightarrow> h \<Turnstile> idx_pqueue ys p * F2 \<Longrightarrow> xs = ys" by auto2
setup {* del_prfstep_thm @{thm dyn_array_prec} *}

section {* Basic operations on indexed_queue *}

definition idx_pqueue_empty :: "nat \<Rightarrow> 'a::heap \<Rightarrow> 'a indexed_pqueue Heap" where
  "idx_pqueue_empty k x = do {
    pq \<leftarrow> dyn_array_new (0, x);
    idx \<leftarrow> amap_new k;
    return (Indexed_PQueue pq idx) }"
declare idx_pqueue_empty_def [sep_proc_defs]

theorem index_of_pqueue_empty [resolve]:
  "index_of_pqueue [] empty_map" by auto2

theorem idx_pqueue_empty_rule [hoare_triple]:
  "<emp> idx_pqueue_empty k x <\<lambda>r. idx_pqueue [] r * \<up>(alen (index r) = k)>" by auto2

definition idx_pqueue_nth :: "'a::heap indexed_pqueue \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a) Heap" where
  "idx_pqueue_nth p i = array_nth (pqueue p) i"
declare idx_pqueue_nth_def [sep_proc_defs]

theorem idx_pqueue_nth_rule [hoare_triple, hoare_create_case]:
  "<idx_pqueue xs p * \<up>(i < length xs)>
   idx_pqueue_nth p i
   <\<lambda>r. idx_pqueue xs p * \<up>(r = xs ! i)>" by auto2

theorem idx_pqueue_nth_heap_preserving [heap_presv_thms]:
  "heap_preserving (idx_pqueue_nth p i)" by auto2

definition idx_pqueue_length :: "'a indexed_pqueue \<Rightarrow> nat Heap" where
  "idx_pqueue_length a = array_length (pqueue a)"
declare idx_pqueue_length_def [sep_proc_defs]

theorem idx_pqueue_length_rule [hoare_triple_direct]:
  "<idx_pqueue xs p>
   idx_pqueue_length p
   <\<lambda>r. idx_pqueue xs p * \<up>(r = length xs)>" by auto2

theorem idx_pqueue_length_heap_preserving [heap_presv_thms]:
  "heap_preserving (idx_pqueue_length a)" by auto2

definition idx_pqueue_swap :: "'a::{heap,linorder} indexed_pqueue \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "idx_pqueue_swap p i j =
   (case p of Indexed_PQueue pq idx \<Rightarrow> do {
      pr_i \<leftarrow> array_nth pq i;
      pr_j \<leftarrow> array_nth pq j;
      amap_update (fst pr_i) j idx;
      amap_update (fst pr_j) i idx;
      array_swap pq i j
    })"
declare idx_pqueue_swap_def [sep_proc_defs]

theorem index_of_pqueue_swap [backward]:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> index_of_pqueue xs m \<Longrightarrow>
   index_of_pqueue (list_swap xs i j) (m {fst (xs ! i) \<rightarrow> j} {fst (xs ! j) \<rightarrow> i})" by auto2

theorem idx_pqueue_swap_rule [hoare_triple, hoare_create_case]:
  "<idx_pqueue xs p * \<up>(i < length xs) * \<up>(j < length xs)>
   idx_pqueue_swap p i j
   <\<lambda>_. idx_pqueue (list_swap xs i j) p>" by auto2

definition idx_pqueue_push :: "nat \<Rightarrow> 'a::heap \<Rightarrow> 'a indexed_pqueue \<Rightarrow> 'a indexed_pqueue Heap" where
  "idx_pqueue_push k v p = do {
    len \<leftarrow> array_length (pqueue p);
    d' \<leftarrow> push_array (k, v) (pqueue p);
    amap_update k len (index p);
    return (Indexed_PQueue d' (index p))
   }"
declare idx_pqueue_push_def [sep_proc_defs]

definition has_key :: "(nat \<times> 'a) list \<Rightarrow> nat \<Rightarrow> bool" where
  "has_key xs k = (\<exists>v'. (k, v') \<in># mset xs)"
setup {* add_rewrite_rule @{thm has_key_def} *}

theorem not_has_key [forward, backward2]:
  "\<not>(has_key xs k) \<Longrightarrow> p \<in># mset xs \<Longrightarrow> k \<noteq> fst p" by auto2

theorem index_of_pqueue_push [backward2]:
  "index_of_pqueue xs m \<Longrightarrow> \<not>has_key xs k \<Longrightarrow> index_of_pqueue (xs @ [(k, v)]) (m{k \<rightarrow> length xs})" by auto2

theorem idx_pqueue_push_rule [hoare_triple]:
  "<idx_pqueue xs p * \<up>(k < alen (index p)) * \<up>(\<not>has_key xs k)>
   idx_pqueue_push k v p
   <\<lambda>r. idx_pqueue (xs @ [(k, v)]) r>\<^sub>t" by auto2

definition idx_pqueue_pop :: "'a::heap indexed_pqueue \<Rightarrow> ((nat \<times> 'a) \<times> 'a indexed_pqueue) Heap" where
  "idx_pqueue_pop p = do {
     (x, d') \<leftarrow> pop_array (pqueue p);
     amap_delete (fst x) (index p);
     return (x, Indexed_PQueue d' (index p))
   }"
declare idx_pqueue_pop_def [sep_proc_defs]

theorem idx_pqueue_pop_rule [hoare_triple]:
  "<idx_pqueue xs p * \<up>(length xs > 0)>
   idx_pqueue_pop p
   <\<lambda>(x, r). idx_pqueue (butlast xs) r * \<up>(x = last xs)>"
@proof @case "xs = []" @qed

theorem index_of_pqueue_update:
  "index_of_pqueue xs m \<Longrightarrow> m\<langle>k\<rangle> = Some i \<Longrightarrow> index_of_pqueue (list_update xs i (k, v)) m" by auto2
setup {* add_forward_prfstep_cond @{thm index_of_pqueue_update} [with_term "list_update ?xs ?i (?k, ?v)"] *}

theorem key_within_range_update [backward2]:
  "key_within_range xs n \<Longrightarrow> i < length xs \<Longrightarrow> k < n \<Longrightarrow> key_within_range (list_update xs i (k, v)) n"
@proof
  @let "xs' = list_update xs i (k, v)" @then
  @have "\<forall>p. p \<in># mset xs' \<longrightarrow> fst p < n" @with
    @obtain j where "j < length xs' \<and> p = xs' ! j" @then @case "j = i"
  @end
@qed

theorem array_upd_idx_pqueue_rule [hoare_triple]:
  "<idx_pqueue xs p * \<up>(i < length xs) * \<up>(k = fst (xs ! i))>
   array_upd i (k, v) (pqueue p)
   <\<lambda>_. idx_pqueue (list_update xs i (k, v)) p>" by auto2

setup {* del_prfstep_thm @{thm indexed_pqueue.collapse} *}

section {* Mapping from list of kv-pairs. *}

definition map_of_kv_set :: "('a \<times> 'b) set \<Rightarrow> ('a, 'b) map" where
  "map_of_kv_set S = Map (\<lambda>a. THE_unique (\<lambda>b. (a, b) \<in> S))"
setup {* add_rewrite_rule @{thm map_of_kv_set_def} *}

setup {* add_gen_prfstep ("THE_unique_case",
  [WithTerm @{term_pat "THE_unique (\<lambda>b. (?a, b) \<in> ?S)"},
   CreateCase @{term_pat "\<exists>!b. (?a, b) \<in> ?S"}]) *}

definition unique_keys_set :: "(nat \<times> 'a) set \<Rightarrow> bool" where
  "unique_keys_set S = (\<forall>i x y. (i, x) \<in> S \<longrightarrow> (i, y) \<in> S \<longrightarrow> x = y)"
setup {* add_rewrite_rule @{thm unique_keys_set_def} *}

theorem unique_keys_imp [forward]:
  "unique_keys_set S \<Longrightarrow> (i, x) \<in> S \<Longrightarrow> \<exists>!x. (i, x) \<in> S" by auto2

theorem in_set_union_single: "x \<in> A \<union> {y} \<Longrightarrow> x = y \<or> x \<in> A" by auto
setup {* add_forward_prfstep_cond @{thm in_set_union_single} [with_cond "?x \<noteq> ?y"] *}
theorem member_union_single: "x \<in> A \<union> {x}" by simp
setup {* add_forward_prfstep_cond @{thm member_union_single} [with_term "?A \<union> {?x}"] *}

theorem map_of_kv_set_insert [rewrite]:
  "unique_keys_set T \<Longrightarrow> \<forall>v. (k, v) \<notin> T \<Longrightarrow> map_of_kv_set (T \<union> { (k, v) }) = (map_of_kv_set T) {k \<rightarrow> v}"
@proof
  @let "S = T \<union> { (k, v) }" @then
  @have "T \<subseteq> S" @then @have "unique_keys_set S"
@qed

theorem map_of_kv_set_delete [rewrite]:
  "unique_keys_set T \<Longrightarrow> (k, v) \<in> T \<Longrightarrow> map_of_kv_set (T - { (k, v) }) = delete_map k (map_of_kv_set T)"
@proof
  @let "S = T - { (k, v) }" @then
  @have "S \<subseteq> T" @then @have "unique_keys_set S"
@qed

theorem map_of_kv_set_update [rewrite]:
  "unique_keys_set T \<Longrightarrow> (k, v) \<in> T \<Longrightarrow>
   map_of_kv_set ((T - { (k, v) }) \<union> { (k, v') }) = (map_of_kv_set T) {k \<rightarrow> v'}"
@proof
  @have "unique_keys_set (T - { (k, v) })" @then
  @have "\<forall>x. (k, x) \<notin> T - { (k, v) }"
@qed

setup {* fold del_prfstep_thm [@{thm in_set_union_single}, @{thm member_union_single}] *}

definition map_of_kv_list :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) map" where
  "map_of_kv_list xs = map_of_kv_set (set xs)"
setup {* add_rewrite_rule @{thm map_of_kv_list_def} *}

setup {* add_forward_prfstep_cond @{thm in_set_conv_nth'} [with_cond "?x \<noteq> ?xs ! ?i"] *}
theorem unique_keys_to_set [forward]: "unique_keys xs \<Longrightarrow> unique_keys_set (set xs)" by auto2
setup {* del_prfstep_thm_str "" @{thm in_set_conv_nth'} *}

theorem unique_key_to_distinct [forward]: "unique_keys xs \<Longrightarrow> distinct xs"
  using distinct_conv_nth unique_keys_def by fastforce

lemma map_of_kv_list_empty [backward]:
  "[] = xs \<Longrightarrow> map_of_kv_list xs = empty_map" by auto2

section {* Heap operations on indexed_queue *}

partial_function (heap) idx_bubble_down ::
  "'a::{heap,linorder} indexed_pqueue \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "idx_bubble_down a k = do {
    len \<leftarrow> idx_pqueue_length a;
    (if s2 k < len then do {
      vk \<leftarrow> idx_pqueue_nth a k;
      vs1k \<leftarrow> idx_pqueue_nth a (s1 k);
      vs2k \<leftarrow> idx_pqueue_nth a (s2 k);
      (if snd vs1k \<le> snd vs2k then
         if snd vk > snd vs1k then
           do { idx_pqueue_swap a k (s1 k); idx_bubble_down a (s1 k) }
         else return ()
       else
         if snd vk > snd vs2k then
           do { idx_pqueue_swap a k (s2 k); idx_bubble_down a (s2 k) }
         else return ()) }
     else if s1 k < len then do {
       vk \<leftarrow> idx_pqueue_nth a k;
       vs1k \<leftarrow> idx_pqueue_nth a (s1 k);
       (if snd vk > snd vs1k then
          do { idx_pqueue_swap a k (s1 k); idx_bubble_down a (s1 k) }
        else return ()) }
     else return ()) }"
declare idx_bubble_down.simps [sep_proc_defs]

theorem idx_bubble_down_rule [hoare_triple]:
  "<idx_pqueue xs a * \<up>(is_heap_partial1 xs k)>
   idx_bubble_down a k
   <\<lambda>_. \<exists>\<^sub>Axs'. idx_pqueue xs' a * \<up>(is_heap xs') * \<up>(mset xs' = mset xs) * \<up>(map_of_kv_list xs' = map_of_kv_list xs)>"
@proof
  @let "d = length xs - k"
  @strong_induct d arbitrary k xs
  @contradiction
  @apply_induct_hyp "length xs - s1 k" @have "length xs - s1 k < d"
  @apply_induct_hyp "length xs - s2 k" @have "length xs - s2 k < d"
@qed

partial_function (heap) idx_bubble_up ::
  "'a::{heap,linorder} indexed_pqueue \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "idx_bubble_up a k =
    (if k = 0 then return () else do {
       len \<leftarrow> idx_pqueue_length a;
       (if k < len then do {
          vk \<leftarrow> idx_pqueue_nth a k;
          vpk \<leftarrow> idx_pqueue_nth a (par k);
          (if snd vk < snd vpk then
             do { idx_pqueue_swap a k (par k); idx_bubble_up a (par k) }
           else return ()) }
        else return ())})"
declare idx_bubble_up.simps [sep_proc_defs]

theorem idx_bubble_up_rule [hoare_triple]:
  "<idx_pqueue xs a * \<up>(is_heap_partial2 xs k)>
   idx_bubble_up a k
   <\<lambda>_. \<exists>\<^sub>Axs'. idx_pqueue xs' a * \<up>(is_heap xs') * \<up>(mset xs' = mset xs) * \<up>(map_of_kv_list xs' = map_of_kv_list xs)>"
@proof
  @strong_induct k arbitrary xs
  @apply_induct_hyp "par k"
@qed

definition delete_min_idx_pqueue ::
  "'a::{heap,linorder} indexed_pqueue \<Rightarrow> ((nat \<times> 'a) \<times> 'a indexed_pqueue) Heap" where
  "delete_min_idx_pqueue p = do {
    len \<leftarrow> idx_pqueue_length p;
    (if len = 0 then raise ''delete_min''
     else do {
       idx_pqueue_swap p 0 (len - 1);
       (x', r) \<leftarrow> idx_pqueue_pop p;
       idx_bubble_down r 0;
       return (x', r)
     })}"
declare delete_min_idx_pqueue_def [sep_proc_defs]

theorem delete_min_idx_pqueue_rule [hoare_triple]:
  "<idx_pqueue xs p * \<up>(is_heap xs) * \<up>(length xs > 0)>
   delete_min_idx_pqueue p
   <\<lambda>(x, r). \<exists>\<^sub>Axs'. idx_pqueue xs' r * \<up>(is_heap xs') * \<up>(x = hd xs) * \<up>(mset xs' = mset xs - {#x#})>"
  by auto2
declare delete_min_idx_pqueue_def [sep_proc_defs del]

setup {* add_rewrite_rule_back @{thm indexed_pqueue.collapse} *}

theorem delete_min_idx_pqueue_map' [hoare_triple, hoare_create_case]:
  "<idx_pqueue xs p * \<up>(is_heap xs) * \<up>(length xs > 0)>
   delete_min_idx_pqueue p
   <\<lambda>(x, r). \<exists>\<^sub>Axs'. idx_pqueue xs' r * \<up>(map_of_kv_list xs' = delete_map (fst x) (map_of_kv_list xs))>"
  by auto2

definition insert_idx_pqueue ::
  "nat \<Rightarrow> 'a::{heap,linorder} \<Rightarrow> 'a indexed_pqueue \<Rightarrow> 'a indexed_pqueue Heap" where
  "insert_idx_pqueue k v p = do {
     p' \<leftarrow> idx_pqueue_push k v p;
     len \<leftarrow> idx_pqueue_length p';
     idx_bubble_up p' (len - 1);
     return p'
   }"
declare insert_idx_pqueue_def [sep_proc_defs]

theorem insert_idx_pqueue_rule [hoare_triple]:
  "<idx_pqueue xs p * \<up>(is_heap xs) * \<up>(k < alen (index p)) * \<up>(\<not>has_key xs k)>
   insert_idx_pqueue k v p
   <\<lambda>r. \<exists>\<^sub>Axs'. idx_pqueue xs' r * \<up>(is_heap xs') * \<up>(map_of_kv_list xs' = map_of_kv_list xs {k \<rightarrow> v})>\<^sub>t" by auto2

definition update_idx_pqueue ::
  "nat \<Rightarrow> 'a::{heap,linorder} \<Rightarrow> 'a indexed_pqueue \<Rightarrow> unit Heap" where
  "update_idx_pqueue k v p = do {
    i_opt \<leftarrow> amap_lookup (index p) k;
    (case i_opt of
      None \<Rightarrow> raise ''update_idx_pqueue''
    | Some i \<Rightarrow> do {
        x \<leftarrow> array_nth (pqueue p) i;
        array_upd i (k, v) (pqueue p);
        (if snd x \<le> v then idx_bubble_down p i
         else idx_bubble_up p i) })
   }"
declare update_idx_pqueue_def [sep_proc_defs]

theorem mset_update' [rewrite]:
  "i < length ls \<Longrightarrow> mset (list_update ls i v) = {#v#} + (mset ls - {# ls ! i #})"
  using mset_update by fastforce

theorem update_idx_pqueue_rule [hoare_triple]:
  "<idx_pqueue xs p * \<up>(is_heap xs) * \<up>(has_key xs k)>
   update_idx_pqueue k v p
   <\<lambda>_. \<exists>\<^sub>Axs'. idx_pqueue xs' p * \<up>(is_heap xs') * \<up>(map_of_kv_list xs' = map_of_kv_list xs {k \<rightarrow> v})>"
@proof
  @contradiction
  @obtain v' where "(k, v') \<in># mset xs" @then
  @obtain i where "i < length xs \<and> (k, v') = xs ! i"
@qed
setup {* del_prfstep_thm @{thm mset_update'} *}

section {* Outer interface *}

definition idx_pqueue_map :: "(nat, 'a::{heap,linorder}) map \<Rightarrow> 'a indexed_pqueue \<Rightarrow> assn" where
  "idx_pqueue_map M p = (\<exists>\<^sub>Axs. idx_pqueue xs p * \<up>(is_heap xs) * \<up>(M = map_of_kv_list xs))"
setup {* add_rewrite_ent_rule @{thm idx_pqueue_map_def} *}

theorem has_key_set [rewrite]:
  "has_key xs k \<longleftrightarrow> (\<exists>v. (k, v) \<in> set xs)"
@proof
  @case "has_key xs k" @with
    @obtain v where "(k, v) \<in># mset xs" @then @have "(k, v) \<in> set xs"
  @end
@qed

theorem has_key_to_map_none [rewrite_bidir]:
  "unique_keys xs \<Longrightarrow> has_key xs k \<longleftrightarrow> (map_of_kv_list xs) \<langle>k\<rangle> \<noteq> None" by auto2
setup {* del_prfstep_thm @{thm has_key_set} *}

theorem heap_implies_hd_min2 [backward1]:
  "is_heap xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> (map_of_kv_list xs)\<langle>k\<rangle> = Some v \<Longrightarrow> snd (hd xs) \<le> v"
@proof
  @obtain i where "i < length xs \<and> (k, v) = xs ! i" @with @have "(k, v) \<in> set xs" @end
  @have "v = snd (k, v)"
@qed

theorem empty_list_to_empty_map [rewrite]:
  "map_of_kv_list ([]::('a \<times> 'b) list) = empty_map" by auto2

declare idx_pqueue_empty_def [sep_proc_defs del]
theorem idx_pqueue_empty_map:
  "<emp> idx_pqueue_empty k x <\<lambda>r. idx_pqueue_map empty_map r * \<up>(alen (index r) = k)>"
  by auto2

declare delete_min_idx_pqueue_def [sep_proc_defs del]

theorem delete_min_idx_pqueue_map:
  "<idx_pqueue_map M p * \<up>(M \<noteq> empty_map)>
   delete_min_idx_pqueue p
   <\<lambda>(x, r). idx_pqueue_map (delete_map (fst x) M) r * \<up>(\<forall>k v. M\<langle>k\<rangle> = Some v \<longrightarrow> snd x \<le> v)>"
  by auto2

declare insert_idx_pqueue_def [sep_proc_defs del]
theorem insert_idx_pqueue_map:
  "<idx_pqueue_map M p * \<up>(k < alen (index p)) * \<up>(M\<langle>k\<rangle> = None)>  
   insert_idx_pqueue k v p
   <idx_pqueue_map (M {k \<rightarrow> v})>\<^sub>t" by auto2

declare update_idx_pqueue_def [sep_proc_defs del]
theorem update_idx_pqueue_map:
  "<idx_pqueue_map M p * \<up>(M\<langle>k\<rangle> \<noteq> None)>
   update_idx_pqueue k v p
   <\<lambda>_. idx_pqueue_map (M {k \<rightarrow> v}) p>" by auto2

end
