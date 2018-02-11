theory IndexedPriorityQueue
  imports "../DataStrs/Arrays_Ex" "../DataStrs/Mapping_Str"
begin

section {* Successor functions, eq-pred predicate *}

fun s1 :: "nat \<Rightarrow> nat" where "s1 m = 2 * m + 1"
fun s2 :: "nat \<Rightarrow> nat" where "s2 m = 2 * m + 2"

lemma s_inj [forward]:
  "s1 m = s1 m' \<Longrightarrow> m = m'" "s2 m = s2 m' \<Longrightarrow> m = m'" by auto
lemma s_neq [resolve]:
  "s1 m \<noteq> s2 m'" "s1 m > m" "s2 m > m" "s2 m > s1 m" using s1.simps s2.simps by presburger+
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

lemma eq_pred_parent1 [forward]:
  "eq_pred i (s1 k) \<Longrightarrow> i \<noteq> s1 k \<Longrightarrow> eq_pred i k"
@proof @let "v = s1 k" @then @prop_induct "eq_pred i v" @qed

lemma eq_pred_parent2 [forward]:
  "eq_pred i (s2 k) \<Longrightarrow> i \<noteq> s2 k \<Longrightarrow> eq_pred i k"
@proof @let "v = s2 k" @then @prop_induct "eq_pred i v" @qed

lemma eq_pred_cases:
  "eq_pred i j \<Longrightarrow> eq_pred (s1 i) j \<or> eq_pred (s2 i) j \<or> j = i \<or> j = s1 i \<or> j = s2 i"
@proof @prop_induct "eq_pred i j" @qed
setup {* add_forward_prfstep_cond @{thm eq_pred_cases} [with_cond "?i \<noteq> s1 ?k", with_cond "?i \<noteq> s2 ?k"] *}

lemma eq_pred_le [forward]: "eq_pred i j \<Longrightarrow> i \<le> j"
@proof @prop_induct "eq_pred i j" @qed

section {* Heap property *}

(* The corresponding tree is a heap. *)
definition is_heap :: "('a \<times> 'b::linorder) list \<Rightarrow> bool" where [rewrite]:
  "is_heap xs = (\<forall>i j. eq_pred i j \<longrightarrow> j < length xs \<longrightarrow> snd (xs ! i) \<le> snd (xs ! j))"
setup {* add_property_const @{term is_heap} *}

lemma is_heapD:
  "is_heap xs \<Longrightarrow> j < length xs \<Longrightarrow> eq_pred i j \<Longrightarrow> snd (xs ! i) \<le> snd (xs ! j)" by auto2
setup {* add_forward_prfstep_cond @{thm is_heapD} [with_term "?xs ! ?j"] *}
setup {* del_prfstep_thm_eqforward @{thm is_heap_def} *}

lemma is_heap_butlast [forward]:
  "is_heap xs \<Longrightarrow> is_heap (butlast xs)" by auto2

section {* Bubble-down *}

(* The corresponding tree is a heap, except k is not necessarily smaller than its descendents. *)
definition is_heap_partial1 :: "('a \<times> 'b::linorder) list \<Rightarrow> nat \<Rightarrow> bool" where [rewrite]:
  "is_heap_partial1 xs k = (\<forall>i j. eq_pred i j \<longrightarrow> i \<noteq> k \<longrightarrow> j < length xs \<longrightarrow> snd (xs ! i) \<le> snd (xs ! j))"

lemma swap_zero_is_heap_partial1:
  "is_heap xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> xs' = list_swap xs 0 (length xs - 1) \<Longrightarrow>
   is_heap_partial1 (butlast xs') 0" by auto2
setup {* add_forward_prfstep_cond @{thm swap_zero_is_heap_partial1} [with_term "butlast ?xs'"] *}

lemma incr_is_heap_partial1:
  "is_heap xs \<Longrightarrow> k < length xs \<Longrightarrow> v \<ge> snd (xs ! k) \<Longrightarrow> xs' = list_update xs k (fst (xs ! k), v) \<Longrightarrow>
   is_heap_partial1 xs' k" by auto2
setup {* add_forward_prfstep_cond @{thm incr_is_heap_partial1} [with_term "?xs'"] *}

(* Two cases of switching with s1 k. *)
lemma bubble_down1:
  "s1 k < length xs \<Longrightarrow> is_heap_partial1 xs k \<Longrightarrow> snd (xs ! k) > snd (xs ! s1 k) \<Longrightarrow>
   snd (xs ! s1 k) \<le> snd (xs ! s2 k) \<Longrightarrow> is_heap_partial1 (list_swap xs k (s1 k)) (s1 k)" by auto2
setup {* add_forward_prfstep_cond @{thm bubble_down1} [with_term "list_swap ?xs ?k (s1 ?k)"] *}

lemma bubble_down2:
  "s1 k < length xs \<Longrightarrow> is_heap_partial1 xs k \<Longrightarrow> snd (xs ! k) > snd (xs ! s1 k) \<Longrightarrow>
   s2 k \<ge> length xs \<Longrightarrow> is_heap_partial1 (list_swap xs k (s1 k)) (s1 k)" by auto2
setup {* add_forward_prfstep_cond @{thm bubble_down2} [with_term "list_swap ?xs ?k (s1 ?k)"] *}

(* One case of switching with s2 k. *)
lemma bubble_down3:
  "s2 k < length xs \<Longrightarrow> is_heap_partial1 xs k \<Longrightarrow> snd (xs ! s1 k) > snd (xs ! s2 k) \<Longrightarrow>
   snd (xs ! k) > snd (xs ! s2 k) \<Longrightarrow> xs' = list_swap xs k (s2 k) \<Longrightarrow> is_heap_partial1 xs' (s2 k)" by auto2
setup {* add_forward_prfstep_cond @{thm bubble_down3} [with_term "?xs'"] *}

section {* Bubble-up *}

fun par :: "nat \<Rightarrow> nat" where
  "par m = (m - 1) div 2"
setup {* register_wellform_data ("par m", ["m \<noteq> 0"]) *}

lemma ps_inverse [rewrite]: "par (s1 k) = k" "par (s2 k) = k" by simp+

lemma p_basic: "m \<noteq> 0 \<Longrightarrow> par m < m" by auto
setup {* add_forward_prfstep_cond @{thm p_basic} [with_term "par ?m"] *}

lemma p_cases: "m \<noteq> 0 \<Longrightarrow> m = s1 (par m) \<or> m = s2 (par m)" by auto
setup {* add_forward_prfstep_cond @{thm p_cases} [with_term "par ?m"] *}

lemma eq_pred_p_next:
  "i \<noteq> 0 \<Longrightarrow> eq_pred i j \<Longrightarrow> eq_pred (par i) j"
@proof @prop_induct "eq_pred i j" @qed
setup {* add_forward_prfstep_cond @{thm eq_pred_p_next} [with_term "par ?i"] *}

lemma heap_implies_hd_min [resolve]:
  "is_heap xs \<Longrightarrow> i < length xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> snd (hd xs) \<le> snd (xs ! i)"
@proof
  @strong_induct i
  @case "i = 0" @then @apply_induct_hyp "par i"
  @have "eq_pred (par i) i"
@qed

(* The corresponding tree is a heap, except k is not necessarily greater than its ancestors. *)
definition is_heap_partial2 :: "('a \<times> 'b::linorder) list \<Rightarrow> nat \<Rightarrow> bool" where [rewrite]:
  "is_heap_partial2 xs k = (\<forall>i j. eq_pred i j \<longrightarrow> j < length xs \<longrightarrow> j \<noteq> k \<longrightarrow> snd (xs ! i) \<le> snd (xs ! j))"

lemma bubble_up1 [forward]:
  "k < length xs \<Longrightarrow> is_heap_partial2 xs k \<Longrightarrow> snd (xs ! k) < snd (xs ! par k) \<Longrightarrow> k \<noteq> 0 \<Longrightarrow>
   is_heap_partial2 (list_swap xs k (par k)) (par k)" by auto2

lemma bubble_up2 [forward]:
  "k < length xs \<Longrightarrow> is_heap_partial2 xs k \<Longrightarrow> snd (xs ! k) \<ge> snd (xs ! par k) \<Longrightarrow> k \<noteq> 0 \<Longrightarrow>
   is_heap xs" by auto2
setup {* del_prfstep_thm @{thm p_cases} *}

lemma append_is_heap_partial2:
  "is_heap xs \<Longrightarrow> is_heap_partial2 (xs @ [x]) (length xs)" by auto2
setup {* add_forward_prfstep_cond @{thm append_is_heap_partial2} [with_term "?xs @ [?x]"] *}

lemma desc_is_heap_partial2:
  "is_heap xs \<Longrightarrow> k < length xs \<Longrightarrow> v < snd (xs ! k) \<Longrightarrow>
   xs' = list_update xs k (fst (xs ! k), v) \<Longrightarrow> is_heap_partial2 xs' k" by auto2
setup {* add_forward_prfstep_cond @{thm desc_is_heap_partial2} [with_term "?xs'"] *}

section {* Indexed priority queue *}

type_synonym 'a idx_pqueue = "(nat \<times> 'a) list \<times> nat option list"

fun index_of_pqueue :: "'a idx_pqueue \<Rightarrow> bool" where
  "index_of_pqueue (xs, m) = (
    (\<forall>i<length xs. fst (xs ! i) < length m \<and> m ! (fst (xs ! i)) = Some i) \<and>
    (\<forall>i. \<forall>k<length m. m ! k = Some i \<longrightarrow> i < length xs \<and> fst (xs ! i) = k) \<and>
    (\<forall>p\<in>set xs. fst p < length m))"
setup {* add_rewrite_rule @{thm index_of_pqueue.simps} *}

lemma has_index_unique_key [forward]:
  "index_of_pqueue (xs, m) \<Longrightarrow> unique_keys_set (set xs)"
@proof
  @have "\<forall>a x y. (a, x) \<in> set xs \<longrightarrow> (a, y) \<in> set xs \<longrightarrow> x = y" @with
    @obtain i where "i < length xs" "xs ! i = (a, x)"
    @obtain j where "j < length xs" "xs ! j = (a, y)"
  @end
@qed

lemma has_index_keys_of [rewrite]:
  "index_of_pqueue (xs, m) \<Longrightarrow> has_key_alist xs k \<longleftrightarrow> (k < length m \<and> m ! k \<noteq> None)"
@proof
  @case "has_key_alist xs k" @with
    @obtain v' where "(k, v') \<in> set xs" @then
    @obtain i where "i < length xs \<and> xs ! i = (k, v')"
  @end
@qed

lemma has_index_distinct [forward]:
  "index_of_pqueue (xs, m) \<Longrightarrow> distinct xs"
@proof
  @have "\<forall>i<length xs. \<forall>j<length xs. i \<noteq> j \<longrightarrow> xs ! i \<noteq> xs ! j"
@qed

section {* Basic operations on indexed_queue *}

fun idx_pqueue_swap_fun :: "(nat \<times> 'a) list \<times> nat option list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a) list \<times> nat option list" where
  "idx_pqueue_swap_fun (xs, m) i j = (
    list_swap xs i j, (m [fst (xs ! i) := Some j] [fst (xs ! j) := Some i]))"
setup {* add_unfolding_rule @{thm idx_pqueue_swap_fun.simps} *}

lemma index_of_pqueue_swap [forward_arg]:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> index_of_pqueue (xs, m) \<Longrightarrow>
   index_of_pqueue (idx_pqueue_swap_fun (xs, m) i j)"
@proof @unfold "idx_pqueue_swap_fun (xs, m) i j" @qed

lemma fst_idx_pqueue_swap [rewrite]:
  "fst (idx_pqueue_swap_fun (xs, m) i j) = list_swap xs i j"
@proof @unfold "idx_pqueue_swap_fun (xs, m) i j" @qed

lemma snd_idx_pqueue_swap [rewrite]:
  "length (snd (idx_pqueue_swap_fun (xs, m) i j)) = length m"
@proof @unfold "idx_pqueue_swap_fun (xs, m) i j" @qed

fun idx_pqueue_push_fun :: "nat \<Rightarrow> 'a \<Rightarrow> 'a idx_pqueue \<Rightarrow> 'a idx_pqueue" where
  "idx_pqueue_push_fun k v (xs, m) = (xs @ [(k, v)], list_update m k (Some (length xs)))"
declare idx_pqueue_push_fun.simps [unfold]

lemma idx_pqueue_push_correct [forward_arg]:
  "index_of_pqueue (xs, m) \<Longrightarrow> k < length m \<Longrightarrow> \<not>has_key_alist xs k \<Longrightarrow>
   index_of_pqueue (idx_pqueue_push_fun k v (xs, m))"
@proof
  @unfold "idx_pqueue_push_fun k v (xs, m)"
  @let "res = idx_pqueue_push_fun k v (xs, m)"
  @let "xs' = fst res" "m' = snd res"
  @have "\<forall>i<length xs'. fst (xs' ! i) < length m' \<and> m' ! (fst (xs' ! i)) = Some i"
  @have "\<forall>i. \<forall>k'<length m'. m' ! k' = Some i \<longrightarrow> i < length xs' \<and> fst (xs' ! i) = k'"
  @have "\<forall>p\<in>set xs'. fst p < length m'"
@qed

lemma idx_pqueue_push_correct2:
  "is_heap xs \<Longrightarrow> k < length m \<Longrightarrow> \<not>has_key_alist xs k \<Longrightarrow>
   r = idx_pqueue_push_fun k v (xs, m) \<Longrightarrow>
   fst r = xs @ [(k, v)] \<and> length (snd r) = length m"
@proof
  @unfold "idx_pqueue_push_fun k v (xs, m)"
@qed
setup {* add_forward_prfstep_cond @{thm idx_pqueue_push_correct2} [with_term "?r"] *}

fun idx_pqueue_pop_fun :: "'a idx_pqueue \<Rightarrow> 'a idx_pqueue" where
  "idx_pqueue_pop_fun (xs, m) = (butlast xs, list_update m (fst (last xs)) None)"
declare idx_pqueue_pop_fun.simps [unfold]

lemma idx_pqueue_pop_correct [forward_arg]:
  "index_of_pqueue (xs, m) \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> index_of_pqueue (idx_pqueue_pop_fun (xs, m))"
@proof
  @unfold "idx_pqueue_pop_fun (xs, m)"
  @have "length xs = length (butlast xs) + 1"
@qed

lemma idx_pqueue_pop_correct2:
  "r = idx_pqueue_pop_fun (xs, m) \<Longrightarrow> fst r = butlast xs \<and> length (snd r) = length m"
@proof @unfold "idx_pqueue_pop_fun (xs, m)" @qed
setup {* add_forward_prfstep_cond @{thm idx_pqueue_pop_correct2} [with_term "?r"] *}

lemma index_of_pqueue_update [forward_arg]:
  "index_of_pqueue (xs, m) \<Longrightarrow> i < length xs \<Longrightarrow> k = fst (xs ! i) \<Longrightarrow> k < length m \<Longrightarrow>
   index_of_pqueue (list_update xs i (k, v), m)"
@proof
  @let "xs' = list_update xs i (k, v)" @then
  @have "\<forall>p\<in>set xs'. fst p < length m" @with
    @obtain j where "j < length xs' \<and> xs' ! j = p"
  @end
@qed

section {* Bubble up and down *}

function idx_bubble_down_fun :: "'a::linorder idx_pqueue \<Rightarrow> nat \<Rightarrow> 'a idx_pqueue" where
  "idx_bubble_down_fun (xs, m) k = (
    if s2 k < length xs then
      if snd (xs ! s1 k) \<le> snd (xs ! s2 k) then
        if snd (xs ! k) > snd (xs ! s1 k) then
          idx_bubble_down_fun (idx_pqueue_swap_fun (xs, m) k (s1 k)) (s1 k)
        else (xs, m)
      else
        if snd (xs ! k) > snd (xs ! s2 k) then
          idx_bubble_down_fun (idx_pqueue_swap_fun (xs, m) k (s2 k)) (s2 k)
        else (xs, m)
    else if s1 k < length xs then
      if snd (xs ! k) > snd (xs ! s1 k) then
        idx_bubble_down_fun (idx_pqueue_swap_fun (xs, m) k (s1 k)) (s1 k)
      else (xs, m)
    else (xs, m))"
  by pat_completeness auto
  termination by (relation "measure (\<lambda>((xs,_),k). (length xs - k))") (simp_all, auto2+)
setup {* add_unfolding_rule @{thm idx_bubble_down_fun.simps} *}
setup {* add_fun_induct_rule (@{term idx_bubble_down_fun}, @{thm idx_bubble_down_fun.induct}) *}

lemma idx_bubble_down_fun_correct:
  "r = idx_bubble_down_fun x k \<Longrightarrow> is_heap_partial1 (fst x) k \<Longrightarrow>
   is_heap (fst r) \<and> mset (fst r) = mset (fst x) \<and> length (snd r) = length (snd x)"
@proof @fun_induct "idx_bubble_down_fun x k" @with
  @subgoal "(x = (xs, m), k = k)"
  @unfold "idx_bubble_down_fun (xs, m) k"
  @case "s2 k < length xs" @with
    @case "snd (xs ! s1 k) \<le> snd (xs ! s2 k)"
  @end
  @case "s1 k < length xs" @end
@qed
setup {* add_forward_prfstep_cond @{thm idx_bubble_down_fun_correct} [with_term "?r"] *}

lemma idx_bubble_down_fun_correct2 [forward_arg]:
  "index_of_pqueue x \<Longrightarrow> index_of_pqueue (idx_bubble_down_fun x k)"
@proof @fun_induct "idx_bubble_down_fun x k" @with
  @subgoal "(x = (xs, m), k = k)"
  @unfold "idx_bubble_down_fun (xs, m) k"
  @case "s2 k < length xs" @with
    @case "snd (xs ! s1 k) \<le> snd (xs ! s2 k)"
  @end
  @case "s1 k < length xs" @end
@qed

fun idx_bubble_up_fun :: "'a::linorder idx_pqueue \<Rightarrow> nat \<Rightarrow> 'a idx_pqueue" where
  "idx_bubble_up_fun (xs, m) k = (
    if k = 0 then (xs, m)
    else if k < length xs then
      if snd (xs ! k) < snd (xs ! par k) then
        idx_bubble_up_fun (idx_pqueue_swap_fun (xs, m) k (par k)) (par k)
      else (xs, m)
    else (xs, m))"
setup {* add_unfolding_rule @{thm idx_bubble_up_fun.simps} *}
setup {* add_fun_induct_rule (@{term idx_bubble_up_fun}, @{thm idx_bubble_up_fun.induct}) *}

lemma idx_bubble_up_fun_correct:
  "r = idx_bubble_up_fun x k \<Longrightarrow> is_heap_partial2 (fst x) k \<Longrightarrow>
   is_heap (fst r) \<and> mset (fst r) = mset (fst x) \<and> length (snd r) = length (snd x)"
@proof @fun_induct "idx_bubble_up_fun x k" @with
  @subgoal "(x = (xs, m), k = k)"
  @unfold "idx_bubble_up_fun (xs, m) k" @end
@qed
setup {* add_forward_prfstep_cond @{thm idx_bubble_up_fun_correct} [with_term "?r"] *}

lemma idx_bubble_up_fun_correct2 [forward_arg]:
  "index_of_pqueue x \<Longrightarrow> index_of_pqueue (idx_bubble_up_fun x k)"
@proof @fun_induct "idx_bubble_up_fun x k" @with
  @subgoal "(x = (xs, m), k = k)"
  @unfold "idx_bubble_up_fun (xs, m) k" @end
@qed

section {* Main operations *}

fun delete_min_idx_pqueue_fun :: "'a::linorder idx_pqueue \<Rightarrow> (nat \<times> 'a) \<times> 'a idx_pqueue" where
  "delete_min_idx_pqueue_fun (xs, m) = (
    let (xs', m') = idx_pqueue_swap_fun (xs, m) 0 (length xs - 1);
        a'' = idx_pqueue_pop_fun (xs', m')
     in (last xs', idx_bubble_down_fun a'' 0))"
setup {* add_unfolding_rule @{thm delete_min_idx_pqueue_fun.simps} *}

lemma delete_min_idx_pqueue_correct:
  "index_of_pqueue (xs, m) \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> res = delete_min_idx_pqueue_fun (xs, m) \<Longrightarrow>
   index_of_pqueue (snd res)"
@proof @unfold "delete_min_idx_pqueue_fun (xs, m)" @qed
setup {* add_forward_prfstep_cond @{thm delete_min_idx_pqueue_correct} [with_term "?res"] *}

lemma delete_min_idx_pqueue_correct2:
  "is_heap xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> res = delete_min_idx_pqueue_fun (xs, m) \<Longrightarrow> index_of_pqueue (xs, m) \<Longrightarrow>
   is_heap (fst (snd res)) \<and> fst res = hd xs \<and> length (snd (snd res)) = length m \<and>
   map_of_alist (fst (snd res)) = delete_map (fst (fst res)) (map_of_alist xs)"
@proof @unfold "delete_min_idx_pqueue_fun (xs, m)" @qed
setup {* add_forward_prfstep_cond @{thm delete_min_idx_pqueue_correct2} [with_term "?res"] *}

fun insert_idx_pqueue_fun :: "nat \<Rightarrow> 'a::linorder \<Rightarrow> 'a idx_pqueue \<Rightarrow> 'a idx_pqueue" where
  "insert_idx_pqueue_fun k v x = (
    let x' = idx_pqueue_push_fun k v x in
      idx_bubble_up_fun x' (length (fst x') - 1))"
setup {* add_unfolding_rule @{thm insert_idx_pqueue_fun.simps} *}

lemma insert_idx_pqueue_correct [forward_arg]:
  "index_of_pqueue (xs, m) \<Longrightarrow> k < length m \<Longrightarrow> \<not>has_key_alist xs k \<Longrightarrow>
   index_of_pqueue (insert_idx_pqueue_fun k v (xs, m))"
@proof @unfold "insert_idx_pqueue_fun k v (xs, m)" @qed

lemma insert_idx_pqueue_correct2:
  "index_of_pqueue (xs, m) \<Longrightarrow> is_heap xs \<Longrightarrow> k < length m \<Longrightarrow> \<not>has_key_alist xs k \<Longrightarrow>
   r = insert_idx_pqueue_fun k v (xs, m) \<Longrightarrow>
   is_heap (fst r) \<and> length (snd r) = length m \<and>
   map_of_alist (fst r) = map_of_alist xs { k \<rightarrow> v }"
@proof @unfold "insert_idx_pqueue_fun k v (xs, m)" @qed
setup {* add_forward_prfstep_cond @{thm insert_idx_pqueue_correct2} [with_term "?r"] *}

fun update_idx_pqueue_fun :: "nat \<Rightarrow> 'a::linorder \<Rightarrow> 'a idx_pqueue \<Rightarrow> 'a idx_pqueue" where
  "update_idx_pqueue_fun k v (xs, m) = (
    if m ! k = None then
      insert_idx_pqueue_fun k v (xs, m)
    else let
      i = the (m ! k);
      xs' = list_update xs i (k, v)
    in
      if snd (xs ! i) \<le> v then idx_bubble_down_fun (xs', m) i
      else idx_bubble_up_fun (xs', m) i)"
setup {* add_unfolding_rule @{thm update_idx_pqueue_fun.simps} *}

lemma update_idx_pqueue_correct [forward_arg]:
  "index_of_pqueue (xs, m) \<Longrightarrow> k < length m \<Longrightarrow>
   index_of_pqueue (update_idx_pqueue_fun k v (xs, m))"
@proof @unfold "update_idx_pqueue_fun k v (xs, m)" @qed

lemma update_idx_pqueue_correct2:
  "index_of_pqueue (xs, m) \<Longrightarrow> is_heap xs \<Longrightarrow> k < length m \<Longrightarrow>
   r = update_idx_pqueue_fun k v (xs, m) \<Longrightarrow>
   is_heap (fst r) \<and> length (snd r) = length m \<and>
   map_of_alist (fst r) = map_of_alist xs { k \<rightarrow> v }"
@proof @unfold "update_idx_pqueue_fun k v (xs, m)"
  @let "i = the (m ! k)"
  @let "xs' = list_update xs i (k, v)"
  @have "xs' = fst (xs', m)" (* TODO: remove *)
  @case "m ! k = None"
  @case "snd (xs ! the (m ! k)) \<le> v"
@qed
setup {* add_forward_prfstep_cond @{thm update_idx_pqueue_correct2} [with_term "?r"] *}

end
