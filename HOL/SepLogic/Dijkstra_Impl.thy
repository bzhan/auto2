theory Dijkstra_Impl
imports IndexedPriorityQueue "../DataStrs/Dijkstra"
begin

datatype dijkstra_state = Dijkstra_State (est_a: "nat array") (heap_pq: "nat indexed_pqueue")
setup {* add_rewrite_rule_back_cond @{thm dijkstra_state.collapse}
  [with_cond "?dijkstra_state \<noteq> Dijkstra_State ?e ?h"] *}
setup {* add_rewrite_rule @{thm dijkstra_state.case} *}
setup {* fold add_rewrite_rule @{thms dijkstra_state.sel} *}

fun dstate :: "state \<Rightarrow> dijkstra_state \<Rightarrow> assn" where
  "dstate (State e M) (Dijkstra_State a pq) = a \<mapsto>\<^sub>a e * idx_pqueue_map M (length e) pq"
setup {* add_rewrite_ent_rule @{thm dstate.simps} *}

fun dstate_pq_init :: "graph \<Rightarrow> nat \<Rightarrow> nat indexed_pqueue Heap" where
  "dstate_pq_init G 0 = idx_pqueue_empty (size G) 0"
| "dstate_pq_init G (Suc k) = do {
    p \<leftarrow> dstate_pq_init G k;
    if k > 0 then update_idx_pqueue k (weight G 0 k) p
    else return p }"
declare dstate_pq_init.simps [sep_proc_defs]

lemma dstate_pq_init_to_fun [hoare_triple]:
  "<\<up>(k \<le> size G)>
   dstate_pq_init G k
   <idx_pqueue_map (map_constr (\<lambda>i. i > 0) (\<lambda>i. weight G 0 i) k) (size G)>\<^sub>t"
@proof @induct k @qed
 
definition dstate_init :: "graph \<Rightarrow> dijkstra_state Heap" where
  "dstate_init G = do {
     a \<leftarrow> Array.of_list (list (\<lambda>i. if i = 0 then 0 else weight G 0 i) (size G));
     pq \<leftarrow> dstate_pq_init G (size G);
     return (Dijkstra_State a pq)
   }"
declare dstate_init_def [sep_proc_defs]

lemma dstate_init_to_fun [hoare_triple]:
  "<emp>
   dstate_init G
   <dstate (dijkstra_start_state G)>\<^sub>t" by auto2

fun dstate_update_est :: "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat indexed_pqueue \<Rightarrow> nat array \<Rightarrow> nat array Heap" where
  "dstate_update_est G m 0 pq a = (return a)"
| "dstate_update_est G m (Suc k) pq a = do {
     b \<leftarrow> has_key_idx_pqueue k pq;
     if b then do {
       ek \<leftarrow> Array.nth a k;
       em \<leftarrow> Array.nth a m;
       a' \<leftarrow> dstate_update_est G m k pq a;
       a'' \<leftarrow> Array.upd k (min (em + weight G m k) ek) a';
       return a'' }
     else dstate_update_est G m k pq a }"
declare dstate_update_est.simps [sep_proc_defs]

lemma dstate_update_est_ind [hoare_triple]:
  "<dstate (State e M) (Dijkstra_State a pq) * \<up>(k \<le> length e) * \<up>(m < length e)>
   dstate_update_est G m k pq a
   <let e' = list_update_set_impl (\<lambda>i. i \<in> keys_of M)
               (\<lambda>i. min (e ! m + weight G m i) (e ! i)) e k
    in (\<lambda>r. dstate (State e' M) (Dijkstra_State r pq))>\<^sub>t"
@proof @induct k @qed
declare dstate_update_est.simps [sep_proc_defs del]

lemma dstate_update_est_to_fun [hoare_triple]:
  "<dstate (State e M) (Dijkstra_State a pq) * \<up>(m < length e)>
   dstate_update_est G m (length e) pq a
   <let e' = list_update_set (\<lambda>i. i \<in> keys_of M)
               (\<lambda>i. min (e ! m + weight G m i) (e ! i)) e
    in (\<lambda>r. dstate (State e' M) (Dijkstra_State r pq))>\<^sub>t" by auto2
setup {* del_prfstep_thm @{thm dstate_update_est_ind} *}

fun dstate_update_heap ::
  "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat indexed_pqueue \<Rightarrow> nat indexed_pqueue Heap" where
  "dstate_update_heap G m 0 a pq = return pq"
| "dstate_update_heap G m (Suc k) a pq = do {
     b \<leftarrow> has_key_idx_pqueue k pq;
     if b then do {
       ek \<leftarrow> Array.nth a k;
       pq' \<leftarrow> dstate_update_heap G m k a pq;
       update_idx_pqueue k ek pq' }
     else dstate_update_heap G m k a pq }"
declare dstate_update_heap.simps [sep_proc_defs]

lemma dstate_update_heap_ind [hoare_triple]:
  "<dstate (State e M) (Dijkstra_State a pq) * \<up>(k \<le> length e) * \<up>(m < length e)>
   dstate_update_heap G m k a pq
   <let M' = map_update_all_impl (\<lambda>i. e ! i) M k
    in (\<lambda>r. dstate (State e M') (Dijkstra_State a r))>\<^sub>t"
@proof @induct k @qed
declare dstate_update_heap.simps [sep_proc_defs]

lemma dstate_update_heap_to_fun [hoare_triple, hoare_create_case]:
  "<dstate (State e M) (Dijkstra_State a pq) * \<up>(m < length e) * \<up>(\<forall>i\<in>keys_of M. i < length e)>
   dstate_update_heap G m (length e) a pq
   <let M' = map_update_all (\<lambda>i. e ! i) M
    in (\<lambda>r. dstate (State e M') (Dijkstra_State a r))>\<^sub>t" by auto2
setup {* del_prfstep_thm @{thm dstate_update_heap_ind} *}

fun dijkstra_extract_min :: "dijkstra_state \<Rightarrow> (nat \<times> dijkstra_state) Heap" where
  "dijkstra_extract_min (Dijkstra_State a pq) = do {
     (x, pq') \<leftarrow> delete_min_idx_pqueue pq;
     return (fst x, Dijkstra_State a pq') }"
declare dijkstra_extract_min.simps [sep_proc_defs]
  
lemma dijkstra_extract_min_rule [hoare_triple]:
  "<dstate (State e M) (Dijkstra_State a pq) * \<up>(M \<noteq> empty_map)>
   dijkstra_extract_min (Dijkstra_State a pq)
   <\<lambda>(m, r). dstate (State e (delete_map m M)) r * \<up>(m < length e) * \<up>(is_heap_min m M)>\<^sub>t" by auto2
declare dijkstra_extract_min.simps [sep_proc_defs del]

fun dijkstra_step_impl :: "graph \<Rightarrow> dijkstra_state \<Rightarrow> dijkstra_state Heap" where
  "dijkstra_step_impl G (Dijkstra_State a pq) = do {
     (x, S') \<leftarrow> dijkstra_extract_min (Dijkstra_State a pq);
     a' \<leftarrow> dstate_update_est G x (size G) (heap_pq S') (est_a S');
     pq'' \<leftarrow> dstate_update_heap G x (size G) a' (heap_pq S');
     return (Dijkstra_State a' pq'') }"
declare dijkstra_step_impl.simps [sep_proc_defs]

lemma dijkstra_step_impl_to_fun [hoare_triple]:
  "<dstate S (Dijkstra_State a pq) * \<up>(heap S \<noteq> empty_map) * \<up>(inv G S)>
   dijkstra_step_impl G (Dijkstra_State a pq)
   <\<lambda>r. \<exists>\<^sub>AS'. dstate S' r * \<up>(is_dijkstra_step G S S')>\<^sub>t" by auto2
declare dijkstra_step_impl.simps [sep_proc_defs del]

lemma dijkstra_step_impl_correct [hoare_triple, hoare_create_case]:
  "<dstate S p * \<up>(heap S \<noteq> empty_map) * \<up>(inv G S)>
   dijkstra_step_impl G p
   <\<lambda>r. \<exists>\<^sub>AS'. dstate S' r * \<up>(inv G S') * \<up>(card (unknown_set S') = card (unknown_set S) - 1)>\<^sub>t" by auto2

fun dijkstra_loop :: "graph \<Rightarrow> nat \<Rightarrow> dijkstra_state \<Rightarrow> dijkstra_state Heap" where
  "dijkstra_loop G 0 p = (return p)"
| "dijkstra_loop G (Suc k) p = do {
    p' \<leftarrow> dijkstra_step_impl G p;
    p'' \<leftarrow> dijkstra_loop G k p';
    return p'' }"
declare dijkstra_loop.simps [sep_proc_defs]

(* Should not need this *)
setup {* add_rewrite_rule @{thm Nat.diff_Suc_eq_diff_pred} *}

lemma dijkstra_loop_correct [hoare_triple, hoare_create_case]:
  "<dstate S p * \<up>(n \<le> card (unknown_set S)) * \<up>(inv G S)>
   dijkstra_loop G n p
   <\<lambda>r. \<exists>\<^sub>AS'. dstate S' r * \<up>(inv G S') * \<up>(card (unknown_set S') = card (unknown_set S) - n)>\<^sub>t"
@proof @contradiction
  @induct n arbitrary S p @with
  @subgoal "n = Suc m"
    @have "m \<le> card (unknown_set S) - 1"
  @endgoal @end
@qed
declare dijkstra_loop.simps [sep_proc_defs del]

definition dijkstra :: "graph \<Rightarrow> dijkstra_state Heap" where
  "dijkstra G = do {
    p \<leftarrow> dstate_init G;
    dijkstra_loop G (size G - 1) p }"
declare dijkstra_def [sep_proc_defs]

lemma dijkstra_correct [hoare_triple]:
  "<\<up>(size G > 0)>
   dijkstra G
   <\<lambda>r. \<exists>\<^sub>AS. dstate S r * \<up>(inv G S) * \<up>(unknown_set S = {}) *
        \<up>(\<forall>i\<in>verts G. has_dist G 0 i \<and> est S ! i = dist G 0 i)>\<^sub>t" by auto2
declare dijkstra_def [sep_proc_defs del]

end
