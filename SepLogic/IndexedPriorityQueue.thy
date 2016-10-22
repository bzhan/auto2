theory IndexedPriorityQueue
imports PriorityQueue ArrayMap
begin

section {* Definitions of kv_pair and indexed_queue *}

datatype ('a, 'b) kv_pair = KVPair (key: 'a) (val: 'b)
setup {* add_rewrite_rule_back @{thm kv_pair.collapse} *}
setup {* add_rewrite_rule @{thm kv_pair.case} *}
setup {* fold add_rewrite_rule @{thms kv_pair.sel} *}

fun kv_pair_encode :: "('a::heap, 'b::heap) kv_pair \<Rightarrow> nat" where
  "kv_pair_encode (KVPair k v) = to_nat (k, v)"

instance kv_pair :: (heap, heap) heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "kv_pair_encode"])
  apply (case_tac x, simp_all, case_tac y, simp_all)
  ..

instantiation kv_pair :: (linorder, linorder) linorder begin

definition less: "(a < b) = (val a < val b | (val a = val b \<and> key a < key b))"
definition less_eq: "(a \<le> b) = (val a < val b | (val a = val b \<and> key a \<le> key b))"

instance proof
  fix x y z :: "('a, 'b) kv_pair"
  show a: "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    using less local.less_eq by force
  show b: "x \<le> x"
    by (simp add: local.less_eq)
  show c: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (smt IndexedPriorityQueue.less_eq less_trans order_trans)
  show d: "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    using IndexedPriorityQueue.less_eq a kv_pair.expand less by fastforce
  show e: "x \<le> y \<or> y \<le> x"
    by (meson IndexedPriorityQueue.less_eq leI not_less_iff_gr_or_eq)
qed end

theorem kv_pair_less [resolve]: "KVPair k v \<le> KVPair k' v' \<Longrightarrow> v \<le> v'"
  by (metis IndexedPriorityQueue.less_eq eq_iff kv_pair.sel(2) less_imp_le)

datatype 'a indexed_pqueue =
  Indexed_PQueue (pqueue: "(nat, 'a) kv_pair dynamic_array") (index: "nat array_map")
setup {* add_rewrite_rule_back @{thm indexed_pqueue.collapse} *}
setup {* add_rewrite_rule @{thm indexed_pqueue.case} *}
setup {* fold add_rewrite_rule @{thms indexed_pqueue.sel} *}

definition index_of_pqueue :: "(nat, 'a) kv_pair list \<Rightarrow> (nat, nat) map \<Rightarrow> bool" where
  "index_of_pqueue xs m = (
    (\<forall>i<length xs. m\<langle>key (xs ! i)\<rangle> = Some i) \<and>
    (\<forall>i k. m\<langle>k\<rangle> = Some i \<longrightarrow> i < length xs \<and> key (xs ! i) = k))"
setup {* add_rewrite_rule @{thm index_of_pqueue_def} *}

definition unique_keys :: "(nat, 'a) kv_pair list \<Rightarrow> bool" where
  "unique_keys xs = (\<forall>m n. m < length xs \<longrightarrow> n < length xs \<longrightarrow> m \<noteq> n \<longrightarrow> key (xs ! m) \<noteq> key (xs ! n))"
setup {* add_rewrite_rule @{thm unique_keys_def} *}

theorem has_index_unique_key [forward]:
  "index_of_pqueue xs m \<Longrightarrow> unique_keys xs" by auto2

definition key_within_range :: "(nat, 'a) kv_pair list \<Rightarrow> nat \<Rightarrow> bool" where
  "key_within_range xs n = (\<forall>p. p \<in># mset xs \<longrightarrow> key p < n)"
setup {* add_rewrite_rule @{thm key_within_range_def} *}

theorem key_within_range_on_index:
  "key_within_range xs n \<Longrightarrow> i < length xs \<Longrightarrow> key (xs ! i) < n" by auto2
setup {* add_forward_prfstep_cond @{thm key_within_range_on_index} [with_term "key (?xs ! ?i)"] *}

fun idx_pqueue :: "(nat, 'a::{heap,linorder}) kv_pair list \<Rightarrow> 'a indexed_pqueue \<Rightarrow> assn" where
  "idx_pqueue xs (Indexed_PQueue pq idx) =
    (\<exists>\<^sub>Am. dyn_array xs pq * amap m idx * \<up>(index_of_pqueue xs m) * \<up>(key_within_range xs (alen idx)))"
setup {* add_rewrite_rule @{thm idx_pqueue.simps} *}

theorem idx_pqueueE [forward_ent]:
  "idx_pqueue xs (Indexed_PQueue pq idx) \<Longrightarrow>\<^sub>A
    (\<exists>\<^sub>Am. dyn_array xs pq * amap m idx * \<up>(index_of_pqueue xs m) * \<up>(key_within_range xs (alen idx)))" by auto2

theorem idx_pqueueI:
  "h \<Turnstile> dyn_array xs pq * amap m idx * \<up>(index_of_pqueue xs m) * \<up>(key_within_range xs (alen idx)) * Qu \<Longrightarrow>
   h \<Turnstile> idx_pqueue xs (Indexed_PQueue pq idx) * Qu" by auto2
setup {* del_prfstep_thm @{thm idx_pqueue.simps} *}

setup {* add_prfstep_custom ("idx_pqueueI",
  [WithGoal @{term_pat "?h \<Turnstile> idx_pqueue (?xs::((nat, ?'a::{heap,linorder}) kv_pair list)) (Indexed_PQueue ?pq (?idx::nat array_map)) * ?Qu"},
   WithFact @{term_pat "?h \<Turnstile> dyn_array (?xs::((nat, ?'a::{heap,linorder}) kv_pair list)) ?pq * amap ?m (?idx::nat array_map) * ?Qu"}],
  PRIORITY_SHADOW,
  (fn ((id, inst), ths) => fn items => fn {ctxt, ...} =>
    let
      val th = ([hd ths] MRS (backward_th @{thm idx_pqueueI}))
                 |> subst_thm ctxt inst
                 |> apply_to_thm' (Conv.arg_conv (Sep_Logic.normalize_mod_cv ctxt))
    in
      [Update.thm_update (id, th),
       Update.ShadowItem {id = id, item = hd items}]
    end)) *}

setup {* add_forward_prfstep @{thm dyn_array_prec} *}
theorem idx_pqueue_prec [sep_prec_thms]:
  "h \<Turnstile> idx_pqueue xs p * F1 \<Longrightarrow> h \<Turnstile> idx_pqueue ys p * F2 \<Longrightarrow> xs = ys" by auto2
setup {* del_prfstep "DynamicArray.dyn_array_prec" *}

section {* Basic operations on indexed_queue *}

definition idx_pqueue_empty :: "nat \<Rightarrow> 'a::heap \<Rightarrow> 'a indexed_pqueue Heap" where
  "idx_pqueue_empty k x = do {
    pq \<leftarrow> dyn_array_new (KVPair 0 x);
    idx \<leftarrow> amap_new k;
    return (Indexed_PQueue pq idx) }"
declare idx_pqueue_empty_def [sep_proc_defs]

theorem index_of_pqueue_empty [resolve]:
  "index_of_pqueue [] empty_map" by auto2

theorem idx_pqueue_empty_rule [hoare_triple]:
  "<emp> idx_pqueue_empty k x <\<lambda>r. idx_pqueue [] r * \<up>(alen (index r) = k)>" by auto2

definition idx_pqueue_nth :: "'a::heap indexed_pqueue \<Rightarrow> nat \<Rightarrow> (nat, 'a) kv_pair Heap" where
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
      amap_update (key pr_i) j idx;
      amap_update (key pr_j) i idx;
      array_swap pq i j
    })"
declare idx_pqueue_swap_def [sep_proc_defs]

theorem index_of_pqueue_swap [backward2]:
  "index_of_pqueue xs m \<Longrightarrow> i < length xs \<Longrightarrow> j < length xs \<Longrightarrow>
   index_of_pqueue (list_swap xs i j) (m {key (xs ! i) \<rightarrow> j} {key (xs ! j) \<rightarrow> i})"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "m', m' = m {key (xs ! i) \<rightarrow> j} {key (xs ! j) \<rightarrow> i}" THEN
     OBTAIN "\<forall>k<length xs. m'\<langle>key (list_swap xs i j ! k)\<rangle> = Some k" WITH
      (CASE "k = i" THEN CASE "k = j")) *})

theorem idx_pqueue_swap_rule [hoare_triple, hoare_create_case]:
  "<idx_pqueue xs p * \<up>(i < length xs) * \<up>(j < length xs)>
   idx_pqueue_swap p i j
   <\<lambda>_. idx_pqueue (list_swap xs i j) p>" by auto2

definition idx_pqueue_push :: "nat \<Rightarrow> 'a::heap \<Rightarrow> 'a indexed_pqueue \<Rightarrow> 'a indexed_pqueue Heap" where
  "idx_pqueue_push k v p = do {
    len \<leftarrow> array_length (pqueue p);
    d' \<leftarrow> push_array (KVPair k v) (pqueue p);
    amap_update k len (index p);
    return (Indexed_PQueue d' (index p))
   }"
declare idx_pqueue_push_def [sep_proc_defs]

definition has_key :: "(nat, 'a) kv_pair list \<Rightarrow> nat \<Rightarrow> bool" where
  "has_key xs k = (\<exists>v'. KVPair k v' \<in># mset xs)"
setup {* add_rewrite_rule @{thm has_key_def} *}

theorem not_has_key [forward, backward2]:
  "\<not>(has_key xs k) \<Longrightarrow> p \<in># mset xs \<Longrightarrow> k \<noteq> key p" by auto2

theorem index_of_pqueue_push [backward2]:
  "index_of_pqueue xs m \<Longrightarrow> \<not>has_key xs k \<Longrightarrow> index_of_pqueue (xs @ [KVPair k v]) (m{k \<rightarrow> length xs})"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "xs', xs' = xs @ [KVPair k v]" THEN
     CHOOSE "m', m' = m{k \<rightarrow> length xs}" THEN
     OBTAIN "\<forall>j<length xs'. m'\<langle>key (xs' ! j)\<rangle> = Some j" WITH CASE "j = length xs") *})

theorem idx_pqueue_push_rule [hoare_triple]:
  "<idx_pqueue xs p * \<up>(k < alen (index p)) * \<up>(\<not>has_key xs k)>
   idx_pqueue_push k v p
   <\<lambda>r. idx_pqueue (xs @ [KVPair k v]) r>\<^sub>t" by auto2

definition idx_pqueue_pop :: "'a::heap indexed_pqueue \<Rightarrow> ((nat, 'a) kv_pair \<times> 'a indexed_pqueue) Heap" where
  "idx_pqueue_pop p = do {
     (x, d') \<leftarrow> pop_array (pqueue p);
     amap_delete (key x) (index p);
     return (x, Indexed_PQueue d' (index p))
   }"
declare idx_pqueue_pop_def [sep_proc_defs]

theorem idx_pqueue_pop_rule [hoare_triple]:
  "<idx_pqueue xs p * \<up>(length xs > 0)>
   idx_pqueue_pop p
   <\<lambda>(x, r). idx_pqueue (butlast xs) r * \<up>(x = last xs)>" by auto2

theorem index_of_pqueue_update:
  "index_of_pqueue xs m \<Longrightarrow> m\<langle>k\<rangle> = Some i \<Longrightarrow> index_of_pqueue (list_update xs i (KVPair k v)) m"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "xs', xs' = list_update xs i (KVPair k v)" THEN
     OBTAIN "\<forall>j<length xs'. m\<langle>key (xs' ! j)\<rangle> = Some j" WITH CASE "j = i") *})
setup {* add_forward_prfstep_cond @{thm index_of_pqueue_update} [with_term "list_update ?xs ?i (KVPair ?k ?v)"] *}

theorem key_within_range_update [backward2]:
  "key_within_range xs n \<Longrightarrow> i < length xs \<Longrightarrow> k < n \<Longrightarrow> key_within_range (list_update xs i (KVPair k v)) n"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "xs', xs' = list_update xs i (KVPair k v)" THEN
     OBTAIN "\<forall>p. p \<in># mset xs' \<longrightarrow> key p < n" WITH
      (CHOOSE "j, j < length xs' \<and> p = xs' ! j" THEN CASE "j = i")) *})

theorem array_upd_idx_pqueue_rule [hoare_triple]:
  "<idx_pqueue xs p * \<up>(i < length xs) * \<up>(k = key (xs ! i))>
   array_upd i (KVPair k v) (pqueue p)
   <\<lambda>_. idx_pqueue (list_update xs i (KVPair k v)) p>" by auto2

setup {* del_prfstep_thm @{thm indexed_pqueue.collapse} *}

section {* Mapping from list of kv-pairs. *}

definition map_of_kv_set :: "('a, 'b) kv_pair set \<Rightarrow> ('a, 'b) map" where
  "map_of_kv_set S = Map (\<lambda>a. THE_unique (\<lambda>b. KVPair a b \<in> S))"
setup {* add_rewrite_rule @{thm map_of_kv_set_def} *}

setup {* add_gen_prfstep ("THE_unique_case",
  [WithTerm @{term_pat "THE_unique (\<lambda>b. KVPair ?a b \<in> ?S)"},
   CreateCase @{term_pat "\<exists>!b. KVPair ?a b \<in> ?S"}]) *}

definition unique_keys_set :: "(nat, 'a) kv_pair set \<Rightarrow> bool" where
  "unique_keys_set S = (\<forall>i x y. KVPair i x \<in> S \<longrightarrow> KVPair i y \<in> S \<longrightarrow> x = y)"
setup {* add_rewrite_rule @{thm unique_keys_set_def} *}

theorem unique_keys_imp [forward]:
  "unique_keys_set S \<Longrightarrow> KVPair i x \<in> S \<Longrightarrow> \<exists>!x. KVPair i x \<in> S" by auto2

theorem in_set_union_single: "x \<in> A \<union> {y} \<Longrightarrow> x = y \<or> x \<in> A" by auto
setup {* add_forward_prfstep_cond @{thm in_set_union_single} [with_cond "?x \<noteq> ?y"] *}
theorem member_union_single: "x \<in> A \<union> {x}" by simp
setup {* add_forward_prfstep_cond @{thm member_union_single} [with_term "?A \<union> {?x}"] *}

theorem map_of_kv_set_insert [rewrite]:
  "unique_keys_set T \<Longrightarrow> \<forall>v. KVPair k v \<notin> T \<Longrightarrow> map_of_kv_set (T \<union> { KVPair k v }) = (map_of_kv_set T) {k \<rightarrow> v}"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "S, S = T \<union> { KVPair k v }" THEN
     OBTAIN "T \<subseteq> S" THEN OBTAIN "unique_keys_set S") *})

theorem map_of_kv_set_delete [rewrite]:
  "unique_keys_set T \<Longrightarrow> KVPair k v \<in> T \<Longrightarrow> map_of_kv_set (T - { KVPair k v }) = delete_map k (map_of_kv_set T)"
  by (tactic {* auto2s_tac @{context}
     (CHOOSE "S, S = T - { KVPair k v }" THEN
      OBTAIN "S \<subseteq> T" THEN OBTAIN "unique_keys_set S") *})

theorem map_of_kv_set_update [rewrite]:
  "unique_keys_set T \<Longrightarrow> KVPair k v \<in> T \<Longrightarrow>
   map_of_kv_set ((T - { KVPair k v }) \<union> { KVPair k v' }) = (map_of_kv_set T) {k \<rightarrow> v'}"
  by (tactic {* auto2s_tac @{context}
    (OBTAIN "unique_keys_set (T - { KVPair k v })" THEN
     OBTAIN "\<forall>x. KVPair k x \<notin> T - { KVPair k v }") *})

setup {* fold del_prfstep_thm [@{thm in_set_union_single}, @{thm member_union_single}] *}

definition map_of_kv_list :: "('a, 'b) kv_pair list \<Rightarrow> ('a, 'b) map" where
  "map_of_kv_list xs = map_of_kv_set (set xs)"
setup {* add_rewrite_rule @{thm map_of_kv_list_def} *}

setup {* add_forward_prfstep_cond @{thm in_set_conv_nth'} [with_cond "?x \<noteq> ?xs ! ?i"] *}
theorem unique_keys_to_set [forward]: "unique_keys xs \<Longrightarrow> unique_keys_set (set xs)" by auto2
setup {* del_prfstep "More_Lists.in_set_conv_nth'" *}

theorem unique_key_to_distinct [forward]: "unique_keys xs \<Longrightarrow> distinct xs"
  using distinct_conv_nth unique_keys_def by fastforce

section {* Heap operations on indexed_queue *}

partial_function (heap) idx_bubble_down ::
  "'a::{heap,linorder} indexed_pqueue \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "idx_bubble_down a k = do {
    len \<leftarrow> idx_pqueue_length a;
    (if s2 k < len then do {
      vk \<leftarrow> idx_pqueue_nth a k;
      vs1k \<leftarrow> idx_pqueue_nth a (s1 k);
      vs2k \<leftarrow> idx_pqueue_nth a (s2 k);
      (if vs1k \<le> vs2k then
         if vk > vs1k then
           do { idx_pqueue_swap a k (s1 k); idx_bubble_down a (s1 k) }
         else return ()
       else
         if vk > vs2k then
           do { idx_pqueue_swap a k (s2 k); idx_bubble_down a (s2 k) }
         else return ()) }
     else if s1 k < len then do {
       vk \<leftarrow> idx_pqueue_nth a k;
       vs1k \<leftarrow> idx_pqueue_nth a (s1 k);
       (if vk > vs1k then
          do { idx_pqueue_swap a k (s1 k); idx_bubble_down a (s1 k) }
        else return ()) }
     else return ()) }"
declare idx_bubble_down.simps [sep_proc_defs]

theorem idx_bubble_down_rule [hoare_triple]:
  "<idx_pqueue xs a * \<up>(is_heap_partial1 xs k)>
   idx_bubble_down a k
   <\<lambda>_. \<exists>\<^sub>Axs'. idx_pqueue xs' a * \<up>(is_heap xs') * \<up>(mset xs' = mset xs) * \<up>(map_of_kv_list xs' = map_of_kv_list xs)>"
  by (tactic {* auto2s_tac @{context} (
    UPPER_STRONG_INDUCT ("k", "k < length xs", Arbitrary "xs" :: ApplyOns ["s1 k", "s2 k"])) *})

partial_function (heap) idx_bubble_up :: "'a::{heap,linorder} indexed_pqueue \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "idx_bubble_up a k =
    (if k = 0 then return () else do {
       len \<leftarrow> idx_pqueue_length a;
       (if k < len then do {
          vk \<leftarrow> idx_pqueue_nth a k;
          vpk \<leftarrow> idx_pqueue_nth a (par k);
          (if vk < vpk then
             do { idx_pqueue_swap a k (par k); idx_bubble_up a (par k) }
           else return ()) }
        else return ())})"
declare idx_bubble_up.simps [sep_proc_defs]

theorem idx_bubble_up_rule [hoare_triple]:
  "<idx_pqueue xs a * \<up>(is_heap_partial2 xs k)>
   idx_bubble_up a k
   <\<lambda>_. \<exists>\<^sub>Axs'. idx_pqueue xs' a * \<up>(is_heap xs') * \<up>(mset xs' = mset xs) * \<up>(map_of_kv_list xs' = map_of_kv_list xs)>"
  by (tactic {* auto2s_tac @{context} (
    STRONG_INDUCT ("k", [Arbitrary "xs", ApplyOn "par k"])) *})

definition delete_min_idx_pqueue ::
  "'a::{heap,linorder} indexed_pqueue \<Rightarrow> ((nat, 'a) kv_pair \<times> 'a indexed_pqueue) Heap" where
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
   <\<lambda>(x, r). \<exists>\<^sub>Axs'. idx_pqueue xs' r * \<up>(map_of_kv_list xs' = delete_map (key x) (map_of_kv_list xs))>"
  by auto2

definition insert_idx_pqueue :: "nat \<Rightarrow> 'a::{heap,linorder} \<Rightarrow> 'a indexed_pqueue \<Rightarrow> 'a indexed_pqueue Heap" where
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

definition update_idx_pqueue :: "nat \<Rightarrow> 'a::{heap,linorder} \<Rightarrow> 'a indexed_pqueue \<Rightarrow> unit Heap" where
  "update_idx_pqueue k v p = do {
    i_opt \<leftarrow> amap_lookup (index p) k;
    (case i_opt of
      None \<Rightarrow> raise ''update_idx_pqueue''
    | Some i \<Rightarrow> do {
        x \<leftarrow> array_nth (pqueue p) i;
        array_upd i (KVPair k v) (pqueue p);
        (if x \<le> KVPair k v then idx_bubble_down p i
         else idx_bubble_up p i) })
   }"
declare update_idx_pqueue_def [sep_proc_defs]

setup {* add_rewrite_rule @{thm Multiset.mset_update} *}
theorem update_idx_pqueue_rule [hoare_triple]:
  "<idx_pqueue xs p * \<up>(is_heap xs) * \<up>(has_key xs k)>
   update_idx_pqueue k v p
   <\<lambda>_. \<exists>\<^sub>Axs'. idx_pqueue xs' p * \<up>(is_heap xs') * \<up>(map_of_kv_list xs' = map_of_kv_list xs {k \<rightarrow> v})>"
   by (tactic {* auto2s_tac @{context}
     (CHOOSE "v', KVPair k v' \<in># mset xs" THEN
      CHOOSE "i, i < length xs \<and> KVPair k v' = xs ! i") *})
setup {* del_prfstep_thm @{thm Multiset.mset_update} *}

section {* Outer interface *}

definition idx_pqueue_map :: "(nat, 'a::{heap,linorder}) map \<Rightarrow> 'a indexed_pqueue \<Rightarrow> assn" where
  "idx_pqueue_map M p = (\<exists>\<^sub>Axs. idx_pqueue xs p * \<up>(is_heap xs) * \<up>(M = map_of_kv_list xs))"
setup {* add_rewrite_rule @{thm idx_pqueue_map_def} *}

theorem has_key_set [rewrite]:
  "has_key xs k \<longleftrightarrow> (\<exists>v. KVPair k v \<in> set xs)"
  by (tactic {* auto2s_tac @{context}
    (CASE "has_key xs k" WITH
      (CHOOSE "v, KVPair k v \<in># mset xs" THEN OBTAIN "KVPair k v \<in> set xs")) *})

theorem has_key_to_map_none [rewrite]:
  "unique_keys xs \<Longrightarrow> has_key xs k \<longleftrightarrow> (map_of_kv_list xs) \<langle>k\<rangle> \<noteq> None" by auto2
setup {* del_prfstep_thm @{thm has_key_set} *}

theorem heap_implies_hd_min2 [backward1]:
  "is_heap xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> (map_of_kv_list xs)\<langle>k\<rangle> = Some v \<Longrightarrow> val (hd xs) \<le> v"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "i, i < length xs \<and> KVPair k v = xs ! i" WITH OBTAIN "KVPair k v \<in> set xs" THEN
     OBTAIN "hd xs \<le> KVPair k v") *})

theorem empty_list_to_empty_map [rewrite]:
  "map_of_kv_list ([]::('a, 'b) kv_pair list) = empty_map"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "x, (map_of_kv_list ([]::('a, 'b) kv_pair list))\<langle>x\<rangle> \<noteq> None" THEN
     CHOOSE "v, KVPair x v \<in> set ([]::('a, 'b) kv_pair list)") *})

declare idx_pqueue_empty_def [sep_proc_defs del]
theorem idx_pqueue_empty_map:
  "<emp> idx_pqueue_empty k x <\<lambda>r. idx_pqueue_map empty_map r * \<up>(alen (index r) = k)>"
  by auto2

declare delete_min_idx_pqueue_def [sep_proc_defs del]
theorem delete_min_idx_pqueue_map:
  "<idx_pqueue_map M p * \<up>(M \<noteq> empty_map)>
   delete_min_idx_pqueue p
   <\<lambda>(x, r). idx_pqueue_map (delete_map (key x) M) r * \<up>(\<forall>k v. M\<langle>k\<rangle> = Some v \<longrightarrow> val x \<le> v)>"
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
