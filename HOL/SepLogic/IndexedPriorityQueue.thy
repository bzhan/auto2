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

lemma is_heap_butlast [forward]: "is_heap xs \<Longrightarrow> is_heap (butlast xs)"
@proof @let "xs' = butlast xs" @have (@rule) "\<forall>i<length xs'. xs' ! i = xs ! i" @qed

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
  @let "xs'' = butlast xs'" @have (@rule) "\<forall>i<length xs''. xs'' ! i = xs' ! i"
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
  "is_heap xs \<Longrightarrow> is_heap_partial2 (xs @ [x]) (length xs)"
@proof
  @let "xs' = xs @ [x]"
  @have "\<forall>i j. eq_pred i j \<longrightarrow> j < length xs' \<longrightarrow> j \<noteq> length xs \<longrightarrow> snd (xs' ! i) \<le> snd (xs' ! j)" @with
    (* Need to make explicit rewriting into x + n form, where n is a constant. *)
    @have "length xs' = length xs + 1"
  @end  
@qed
setup {* add_forward_prfstep_cond @{thm append_is_heap_partial2} [with_term "?xs @ [?x]"] *}

theorem desc_is_heap_partial2:
  "is_heap xs \<Longrightarrow> k < length xs \<Longrightarrow> v < snd (xs ! k) \<Longrightarrow>
   xs' = list_update xs k (fst (xs ! k), v) \<Longrightarrow> is_heap_partial2 xs' k" by auto2
setup {* add_forward_prfstep_cond @{thm desc_is_heap_partial2} [with_term "?xs'"] *}

setup {* fold del_prfstep_thm [@{thm eq_pred_p1}, @{thm eq_pred_p2}, @{thm eq_pred_p3}] *}
setup {* del_prfstep_thm @{thm p_cases} *}
setup {* del_prfstep_thm @{thm is_heap_partial2_def} *}

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
  
theorem has_index_unique_key [forward]:
  "index_of_pqueue xs m \<Longrightarrow> unique_keys_set (set xs)"
@proof
  @have "\<forall>a x y. (a, x) \<in> set xs \<longrightarrow> (a, y) \<in> set xs \<longrightarrow> x = y" @with
    @obtain i where "i < length xs" "xs ! i = (a, x)"
    @obtain j where "j < length xs" "xs ! j = (a, y)"
  @end
@qed

lemma has_index_keys_of [rewrite_bidir]:
  "index_of_pqueue xs m \<Longrightarrow> has_key_alist xs k \<longleftrightarrow> k \<in> keys_of m"
@proof
  @case "has_key_alist xs k" @with
    @obtain v' where "(k, v') \<in> set xs" @then
    @obtain i where "i < length xs \<and> xs ! i = (k, v')"
  @end
@qed

lemma has_index_distinct [forward]:
  "index_of_pqueue xs m \<Longrightarrow> distinct xs"
@proof
  @have "\<forall>i<length xs. \<forall>j<length xs. i \<noteq> j \<longrightarrow> xs ! i \<noteq> xs ! j"
@qed

definition key_within_range :: "(nat \<times> 'a) list \<Rightarrow> nat \<Rightarrow> bool" where
  "key_within_range xs n = (\<forall>p\<in>set xs. fst p < n)"
setup {* add_rewrite_rule @{thm key_within_range_def} *}

theorem key_within_range_on_index:
  "i < length xs \<Longrightarrow> key_within_range xs n \<Longrightarrow> fst (xs ! i) < n" by auto2
setup {* add_forward_prfstep_cond @{thm key_within_range_on_index} [with_term "?xs ! ?i"] *}

fun idx_pqueue :: "(nat \<times> 'a::{heap,linorder}) list \<Rightarrow> nat \<Rightarrow> 'a indexed_pqueue \<Rightarrow> assn" where
  "idx_pqueue xs n (Indexed_PQueue pq idx) =
    (\<exists>\<^sub>Am. dyn_array xs pq * amap m idx * \<up>(n = alen idx) * \<up>(index_of_pqueue xs m) * \<up>(key_within_range xs n))"
setup {* add_rewrite_ent_rule @{thm idx_pqueue.simps} *}

setup {* add_forward_prfstep @{thm dyn_array_prec} *}
theorem idx_pqueue_prec [sep_prec_thms]:
  "h \<Turnstile> idx_pqueue xs m p * F1 \<Longrightarrow> h \<Turnstile> idx_pqueue ys n p * F2 \<Longrightarrow> xs = ys \<and> m = n" by auto2
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
  "<emp> idx_pqueue_empty n x <\<lambda>r. idx_pqueue [] n r>" by auto2
declare idx_pqueue_empty_def [sep_proc_defs del]

definition idx_pqueue_nth :: "'a::heap indexed_pqueue \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a) Heap" where
  "idx_pqueue_nth p i = array_nth (pqueue p) i"
declare idx_pqueue_nth_def [sep_proc_defs]

theorem idx_pqueue_nth_rule [hoare_triple, hoare_create_case]:
  "<idx_pqueue xs n p * \<up>(i < length xs)>
   idx_pqueue_nth p i
   <\<lambda>r. idx_pqueue xs n p * \<up>(r = xs ! i)>" by auto2

theorem idx_pqueue_nth_heap_preserving [heap_presv_thms]:
  "heap_preserving (idx_pqueue_nth p i)" by auto2

definition idx_pqueue_length :: "'a indexed_pqueue \<Rightarrow> nat Heap" where
  "idx_pqueue_length a = array_length (pqueue a)"
declare idx_pqueue_length_def [sep_proc_defs]

theorem idx_pqueue_length_rule [hoare_triple_direct]:
  "<idx_pqueue xs n p>
   idx_pqueue_length p
   <\<lambda>r. idx_pqueue xs n p * \<up>(r = length xs)>" by auto2

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
  "<idx_pqueue xs n p * \<up>(i < length xs) * \<up>(j < length xs)>
   idx_pqueue_swap p i j
   <\<lambda>_. idx_pqueue (list_swap xs i j) n p>"
@proof @contradiction
  @have "mset xs = mset (list_swap xs i j)"
  @have "set xs = set (list_swap xs i j)"
@qed

definition idx_pqueue_push :: "nat \<Rightarrow> 'a::heap \<Rightarrow> 'a indexed_pqueue \<Rightarrow> 'a indexed_pqueue Heap" where
  "idx_pqueue_push k v p = do {
    len \<leftarrow> array_length (pqueue p);
    d' \<leftarrow> push_array (k, v) (pqueue p);
    amap_update k len (index p);
    return (Indexed_PQueue d' (index p))
   }"
declare idx_pqueue_push_def [sep_proc_defs]

theorem index_of_pqueue_push [backward2]:
  "index_of_pqueue xs m \<Longrightarrow> \<not>has_key_alist xs k \<Longrightarrow> index_of_pqueue (xs @ [(k, v)]) (m{k \<rightarrow> length xs})"
(* Again, need to make rewriting into x + n form explicit. *)
@proof @have "length (xs @ [(k, v)]) = length xs + 1" @qed

theorem idx_pqueue_push_rule [hoare_triple]:
  "<idx_pqueue xs n p * \<up>(k < n) * \<up>(\<not>has_key_alist xs k)>
   idx_pqueue_push k v p
   <\<lambda>r. idx_pqueue (xs @ [(k, v)]) n r>\<^sub>t" by auto2

definition idx_pqueue_pop :: "'a::heap indexed_pqueue \<Rightarrow> ((nat \<times> 'a) \<times> 'a indexed_pqueue) Heap" where
  "idx_pqueue_pop p = do {
     (x, d') \<leftarrow> pop_array (pqueue p);
     amap_delete (fst x) (index p);
     return (x, Indexed_PQueue d' (index p))
   }"
declare idx_pqueue_pop_def [sep_proc_defs]

theorem index_of_pqueue_pop [backward2]:
  "index_of_pqueue xs m \<Longrightarrow> length xs > 0 \<Longrightarrow>
   index_of_pqueue (butlast xs) (delete_map (fst (last xs)) m)"
(* Again, need to make rewriting into x + n form explicit. *)
@proof @have "length xs = length (butlast xs) + 1" @qed

theorem idx_pqueue_pop_rule [hoare_triple]:
  "<idx_pqueue xs n p * \<up>(length xs > 0)>
   idx_pqueue_pop p
   <\<lambda>(x, r). idx_pqueue (butlast xs) n r * \<up>(x = last xs)>"
@proof @have "set (butlast xs) \<subseteq> set xs" @qed

theorem index_of_pqueue_update:
  "index_of_pqueue xs m \<Longrightarrow> m\<langle>k\<rangle> = Some i \<Longrightarrow> index_of_pqueue (list_update xs i (k, v)) m" by auto2
setup {* add_forward_prfstep_cond @{thm index_of_pqueue_update} [with_term "list_update ?xs ?i (?k, ?v)"] *}

theorem key_within_range_update [backward2]:
  "key_within_range xs n \<Longrightarrow> i < length xs \<Longrightarrow> k < n \<Longrightarrow> key_within_range (list_update xs i (k, v)) n"
@proof
  @let "xs' = list_update xs i (k, v)" @then
  @have "\<forall>p\<in>set xs'. fst p < n" @with
    @obtain j where "j < length xs' \<and> xs' ! j = p" @then @case "j = i"
  @end
@qed

theorem array_upd_idx_pqueue_rule [hoare_triple]:
  "<idx_pqueue xs n p * \<up>(i < length xs) * \<up>(k = fst (xs ! i))>
   array_upd i (k, v) (pqueue p)
   <\<lambda>_. idx_pqueue (list_update xs i (k, v)) n p>" by auto2

setup {* del_prfstep_thm @{thm indexed_pqueue.collapse} *}

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
  "<idx_pqueue xs n a * \<up>(is_heap_partial1 xs k)>
   idx_bubble_down a k
   <\<lambda>_. \<exists>\<^sub>Axs'. idx_pqueue xs' n a * \<up>(is_heap xs') * \<up>(mset xs' = mset xs)>"
@proof
  @let "d = length xs - k"
  @strong_induct d arbitrary k xs
  @case "s2 k < length xs" @with
    @case "snd (xs ! s1 k) \<le> snd (xs ! s2 k)" @with
      @apply_induct_hyp "length xs - s1 k" "s1 k" "list_swap xs k (s1 k)"
    @end
    @apply_induct_hyp "length xs - s2 k" "s2 k" "list_swap xs k (s2 k)"
  @end
  @case "s1 k < length xs" @with
    @apply_induct_hyp "length xs - s1 k" "s1 k" "list_swap xs k (s1 k)"
  @end
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
  "<idx_pqueue xs n a * \<up>(is_heap_partial2 xs k)>
   idx_bubble_up a k
   <\<lambda>_. \<exists>\<^sub>Axs'. idx_pqueue xs' n a * \<up>(is_heap xs') * \<up>(mset xs' = mset xs)>"
@proof
  @strong_induct k arbitrary xs
  @case "k = 0" @then
  @case "k < length xs" @with
    @apply_induct_hyp "par k" "list_swap xs k (par k)"
  @end
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

lemma hd_last_swap_eval_last [rewrite]:
  "length xs > 0 \<Longrightarrow> last (list_swap xs 0 (length xs - 1)) = hd xs"
@proof
  @let "xs' = list_swap xs 0 (length xs - 1)"
  @have "last xs' = xs' ! (length xs - 1)"
  @have "hd xs = xs ! 0"
@qed

setup {* add_rewrite_rule_back @{thm indexed_pqueue.collapse} *}

theorem delete_min_idx_pqueue_rule [hoare_triple, hoare_create_case]:
  "<idx_pqueue xs n p * \<up>(is_heap xs) * \<up>(length xs > 0)>
   delete_min_idx_pqueue p
   <\<lambda>(x, r). \<exists>\<^sub>Axs'. idx_pqueue xs' n r * \<up>(is_heap xs') * \<up>(x = hd xs) *
                    \<up>(map_of_alist xs' = delete_map (fst x) (map_of_alist xs))>" by auto2
declare delete_min_idx_pqueue_def [sep_proc_defs del]

definition insert_idx_pqueue ::
  "nat \<Rightarrow> 'a::{heap,linorder} \<Rightarrow> 'a indexed_pqueue \<Rightarrow> 'a indexed_pqueue Heap" where
  "insert_idx_pqueue k v p = do {
     p' \<leftarrow> idx_pqueue_push k v p;
     len \<leftarrow> idx_pqueue_length p';
     idx_bubble_up p' (len - 1);
     return p' }"
declare insert_idx_pqueue_def [sep_proc_defs]

theorem insert_idx_pqueue_rule [hoare_triple]:
  "<idx_pqueue xs n p * \<up>(is_heap xs) * \<up>(k < n) * \<up>(\<not>has_key_alist xs k)>
   insert_idx_pqueue k v p
   <\<lambda>r. \<exists>\<^sub>Axs'. idx_pqueue xs' n r * \<up>(is_heap xs') * \<up>(map_of_alist xs' = map_of_alist xs {k \<rightarrow> v})>\<^sub>t" by auto2
declare insert_idx_pqueue_def [sep_proc_defs del]

definition has_key_idx_pqueue ::
  "nat \<Rightarrow> 'a::{heap,linorder} indexed_pqueue \<Rightarrow> bool Heap" where
  "has_key_idx_pqueue k p = do {
    i_opt \<leftarrow> amap_lookup (index p) k;
    return (i_opt \<noteq> None) }"
declare has_key_idx_pqueue_def [sep_proc_defs]

lemma has_key_idx_pqueue_rule [hoare_triple]:
  "<idx_pqueue xs n p * \<up>(is_heap xs)>
   has_key_idx_pqueue k p
   <\<lambda>r. idx_pqueue xs n p * \<up>(r \<longleftrightarrow> has_key_alist xs k)>" by auto2

lemma has_key_idx_heap_preserving [heap_presv_thms]:
  "heap_preserving (has_key_idx_pqueue k p)" by auto2

declare has_key_idx_pqueue_def [sep_proc_defs del]

definition update_idx_pqueue ::
  "nat \<Rightarrow> 'a::{heap,linorder} \<Rightarrow> 'a indexed_pqueue \<Rightarrow> 'a indexed_pqueue Heap" where
  "update_idx_pqueue k v p = do {
    i_opt \<leftarrow> amap_lookup (index p) k;
    if i_opt = None then
      insert_idx_pqueue k v p
    else do {
      x \<leftarrow> array_nth (pqueue p) (the i_opt);
      array_upd (the i_opt) (k, v) (pqueue p);
      (if snd x \<le> v then do {idx_bubble_down p (the i_opt); return p}
       else do {idx_bubble_up p (the i_opt); return p}) }}"
declare update_idx_pqueue_def [sep_proc_defs]

theorem update_idx_pqueue_rule [hoare_triple]:
  "<idx_pqueue xs n p * \<up>(is_heap xs) * \<up>(k < n)>
   update_idx_pqueue k v p
   <\<lambda>r. \<exists>\<^sub>Axs'. idx_pqueue xs' n r * \<up>(is_heap xs') * \<up>(map_of_alist xs' = map_of_alist xs {k \<rightarrow> v})>\<^sub>t" by auto2
declare update_idx_pqueue_def [sep_proc_defs del]

section {* Outer interface *}

definition idx_pqueue_map :: "(nat, 'a::{heap,linorder}) map \<Rightarrow> nat \<Rightarrow> 'a indexed_pqueue \<Rightarrow> assn" where
  "idx_pqueue_map M n p = (\<exists>\<^sub>Axs. idx_pqueue xs n p * \<up>(is_heap xs) * \<up>(M = map_of_alist xs))"
setup {* add_rewrite_ent_rule @{thm idx_pqueue_map_def} *}

lemma heap_implies_hd_min2 [backward1]:
  "is_heap xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> (map_of_alist xs)\<langle>k\<rangle> = Some v \<Longrightarrow> snd (hd xs) \<le> v"
@proof
  @obtain i where "i < length xs" "xs ! i = (k, v)"
  @have "snd (hd xs) \<le> snd (xs ! i)"
@qed

lemma idx_pqueue_empty_map [hoare_triple]:
  "<emp> idx_pqueue_empty n x <\<lambda>r. idx_pqueue_map empty_map n r>" by auto2

lemma delete_min_idx_pqueue_map [hoare_triple]:
  "<idx_pqueue_map M n p * \<up>(M \<noteq> empty_map)>
   delete_min_idx_pqueue p
   <\<lambda>(x, r). idx_pqueue_map (delete_map (fst x) M) n r * \<up>(fst x \<in> keys_of M) * \<up>(M\<langle>fst x\<rangle> = Some (snd x)) *
             \<up>(\<forall>k\<in>keys_of M. snd x \<le> the (M\<langle>k\<rangle>))>" by auto2

lemma insert_idx_pqueue_map [hoare_triple]:
  "<idx_pqueue_map M n p * \<up>(k < n) * \<up>(k \<notin> keys_of M)>
   insert_idx_pqueue k v p
   <idx_pqueue_map (M {k \<rightarrow> v}) n>\<^sub>t" by auto2

lemma has_key_idx_pqueue_map [hoare_triple]:
  "<idx_pqueue_map M n p>
   has_key_idx_pqueue k p
   <\<lambda>r. idx_pqueue_map M n p * \<up>(r \<longleftrightarrow> k \<in> keys_of M)>" by auto2

lemma update_idx_pqueue_map [hoare_triple]:
  "<idx_pqueue_map M n p * \<up>(k < n)>
   update_idx_pqueue k v p
   <idx_pqueue_map (M {k \<rightarrow> v}) n>\<^sub>t" by auto2

end
