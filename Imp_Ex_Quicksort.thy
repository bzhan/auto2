theory Imp_Ex_Quicksort
imports Imp_Thms
begin

fun swap :: "'a\<Colon>heap array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "swap a i j = do {
     x \<leftarrow> Array.nth a i;
     y \<leftarrow> Array.nth a j;
     Array.upd i y a;
     Array.upd j x a;
     return ()
   }"

function part1 :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap"
where
  "part1 a left right p = (
     if (right \<le> left) then return right
     else do {
       v \<leftarrow> Array.nth a left;
       (if v \<le> p
        then (part1 a (left + 1) right p)
        else (do { swap a left right;
                   part1 a left (right - 1) p }))
     })"
by pat_completeness auto termination by (relation "measure (\<lambda>(_,l,r,_). r - l )") auto

(* Properties of swap. *)
setup {* add_rewrite_rule @{thm swap.simps} *}
lemma swap_pointwise: "effect (swap a i j) h h' r \<Longrightarrow>
  Array.get h' a ! k = (if k = i then Array.get h a ! j else if k = j then Array.get h a ! i else Array.get h a ! k)" by auto2
lemma swap_permutes: "effect (swap a i j) h h' rs \<Longrightarrow>
  multiset_of (Array.get h' a) = multiset_of (Array.get h a)" by auto2
lemma swap_length: "effect (swap a i j) h h' r \<Longrightarrow> Array.length h' a = Array.length h a" by auto2
lemma swap_succeed: "i < Array.length h a \<and> j < Array.length h a \<Longrightarrow> success (swap a i j) h" by auto2
setup {* del_prfstep_thm @{thm swap.simps}
      #> fold add_rewrite_rule [@{thm swap_pointwise}, @{thm swap_permutes}, @{thm swap_length}]
      #> add_backward_prfstep @{thm swap_succeed} *}

(* Induction rule for part1. *)
setup {* add_rewrite_rule_cond @{thm part1.simps} (with_filts [size1_filter "left", size1_filter "right"]) *}
theorem part1_induct': "(\<forall>a left right p.
    ((\<not> right \<le> left \<longrightarrow> (\<forall>v.  v \<le> p \<longrightarrow> P a (left + 1) right p)) \<and>
     (\<not> right \<le> left \<longrightarrow> (\<forall>v. \<not>v \<le> p \<longrightarrow> P a left (right - 1) p))) \<longrightarrow> P a left right p) \<Longrightarrow>
    P (a::nat array) (left::nat) (right::nat) (p::nat)"
  apply (induct rule: part1.induct) by blast
setup {* add_prfstep_imp_induction @{term_pat "part1 ?a ?l ?r ?p"} @{thm part1_induct'} *}

(* Properties of part1. *)
lemma part1_permutes: "effect (part1 a l r p) h h' rs \<Longrightarrow>
  multiset_of (Array.get h' a) = multiset_of (Array.get h a)" by auto2
setup {* add_rewrite_rule @{thm part1_permutes} *}

lemma part1_returns_index_in_bounds': "effect (part1 a l r p) h h' rs \<Longrightarrow>
  if r \<le> l then rs = r else l \<le> rs \<and> rs \<le> r" by auto2
lemma part1_returns_index_in_bounds: "effect (part1 a l r p) h h' rs \<Longrightarrow>
  l \<le> r \<Longrightarrow> l \<le> rs \<and> rs \<le> r" by (metis order_refl part1_returns_index_in_bounds')
setup {* add_forward_prfstep @{thm part1_returns_index_in_bounds} *}

lemma part1_outer_remains: "effect (part1 a l r p) h h' rs \<Longrightarrow> outer_remains h h' a l r" by auto2
setup {* add_forward_prfstep @{thm part1_outer_remains} *}

lemma part1_partitions1: "effect (part1 a l r p) h h' rs \<Longrightarrow> l \<le> i \<and> i < rs \<Longrightarrow> Array.get h' a ! i \<le> p" by auto2
lemma part1_partitions2: "effect (part1 a l r p) h h' rs \<Longrightarrow> rs < i \<and> i \<le> r \<Longrightarrow> Array.get h' a ! i \<ge> p" by auto2
setup {* fold add_backward2_prfstep [@{thm part1_partitions1}, @{thm part1_partitions2}] *}

lemma part1_succeed: "l < Array.length h a \<and> r < Array.length h a \<Longrightarrow> success (part1 a l r p) h" by auto2
setup {* add_backward_prfstep @{thm part1_succeed} *}

setup {* fold del_prfstep_thm [@{thm part1.simps}, @{thm part1_induct'}] *}

(* Partition function. *)
fun partition :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap"
where
  "partition a left right = do {
     pivot \<leftarrow> Array.nth a right;
     middle \<leftarrow> part1 a left (right - 1) pivot;
     v \<leftarrow> Array.nth a middle;
     m \<leftarrow> return (if (v \<le> pivot) then (middle + 1) else middle);
     comment (\<lambda>h. (\<forall>i. left \<le> i \<and> i < m \<longrightarrow> Array.get h a ! i \<le> pivot) \<and>
                  (\<forall>i. m \<le> i \<and> i < right - 1 \<longrightarrow> Array.get h a ! i \<ge> pivot) \<and>
                  Array.get h a ! right = pivot);
     swap a m right;
     return m
   }"

(* Properties of partition. *)
setup {* add_rewrite_rule @{thm partition.simps} *}
lemma partition_succeed: "l < r \<and> r < Array.length h a \<Longrightarrow> success (partition a l r) h" by auto2
setup {* add_backward_prfstep @{thm partition_succeed} *}

lemma partition_permutes: "effect (partition a l r) h h' rs \<Longrightarrow>
  multiset_of (Array.get h' a) = multiset_of (Array.get h a)" by auto2
setup {* add_rewrite_rule @{thm partition_permutes} *}

lemma partition_outer_remains: "effect (partition a l r) h h' rs \<Longrightarrow>
  l < r \<Longrightarrow> outer_remains h h' a l r" by auto2
setup {* add_forward_prfstep @{thm partition_outer_remains} *}

lemma partition_returns_index_in_bounds: "effect (partition a l r) h h' rs \<Longrightarrow>
  l < r \<Longrightarrow> l \<le> rs \<le> r" by auto2
setup {* add_forward_prfstep @{thm partition_returns_index_in_bounds} *}

lemma partition_partitions1: "effect (partition a l r) h h' rs \<Longrightarrow> l < r \<Longrightarrow>
  (\<forall>x\<in>set (subarray l rs a h'). x \<le> Array.get h' a ! rs)" by auto2
lemma partition_partitions2: "effect (partition a l r) h h' rs \<Longrightarrow> l < r \<Longrightarrow>
  (\<forall>y\<in>set (subarray (rs + 1) (r + 1) a h'). Array.get h' a ! rs \<le> y)" by auto2
setup {* del_prfstep_thm @{thm partition.simps}
  #> fold add_forward_prfstep [@{thm partition_partitions1}, @{thm partition_partitions2}] *}

(* Quicksort function *)
function quicksort :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap"
where
  "quicksort a left right =
     (if left < right then
        do {
          pivot \<leftarrow> partition a left right;
          pivot \<leftarrow> assert (\<lambda>x. left \<le> x \<and> x \<le> right) pivot;
          comment (\<lambda>h. if pivot > 0 then pivot = 1 + (pivot - 1) else pivot = 0);
          quicksort a left (pivot - 1);
          quicksort a (pivot + 1) right
        }
     else return ())"
by pat_completeness auto termination by (relation "measure (\<lambda>(a, l, r). (r - l))") auto

(* Induction rule for quicksort. *)
setup {* add_rewrite_rule_cond @{thm quicksort.simps} (with_filts [size1_filter "left", size1_filter "right"]) *}
theorem quicksort_induct': "(\<forall>arr left right.
    ((left < right \<longrightarrow> (\<forall>p. left \<le> p \<le> right \<longrightarrow> P arr left (p - 1))) \<and>
     (left < right \<longrightarrow> (\<forall>p. left \<le> p \<le> right \<longrightarrow> P arr (p + 1) right))) \<longrightarrow> P arr left right) \<Longrightarrow>
    P (arr::nat array) (left::nat) (right::nat)"
  apply (induct rule: quicksort.induct) by (metis closed_interval_def)
setup {* add_prfstep_imp_induction @{term_pat "quicksort ?a ?left ?right"} @{thm quicksort_induct'} *}

lemma quicksort_outer_remains: "effect (quicksort a l r) h h' rs \<Longrightarrow> outer_remains h h' a l r" by auto2
setup {* add_forward_prfstep @{thm quicksort_outer_remains} *}

lemma quicksort_permutes: "effect (quicksort a l r) h h' rs \<Longrightarrow>
  multiset_of (Array.get h' a) = multiset_of (Array.get h a)" by auto2
setup {* add_forward_prfstep @{thm quicksort_permutes} *}

theorem quicksort_permutes': "effect (quicksort a l r) h h' rs \<Longrightarrow>
  r < Array.length h a \<Longrightarrow> multiset_of (subarray l (r + 1) a h) = multiset_of (subarray l (r + 1) a h')"
  by (tactic {* auto2s_tac @{context} (OBTAIN "multiset_of (Array.get h' a) = multiset_of (Array.get h a)") *})
setup {* del_prfstep_thm @{thm quicksort_permutes} #> add_forward_prfstep @{thm quicksort_permutes'} *}

lemma quicksort_is_skip: "effect (quicksort a l r) h h' rs \<Longrightarrow> r \<le> l \<Longrightarrow> h' = h" by auto2
setup {* add_forward_prfstep @{thm quicksort_is_skip} *}

lemma quicksort_success_skip: "\<not>r > l \<Longrightarrow> success (quicksort a l r) h" by auto2
setup {* add_backward_prfstep @{thm quicksort_success_skip} *}

lemma quicksort_success: "l < Array.length h a \<and> r < Array.length h a \<Longrightarrow>
  success (quicksort a l r) h" by auto2

(* Now for the final theorem. *)
setup {* add_gen_prfstep ("quicksort_case",
  [WithFact @{term_pat "effect (quicksort ?a ?l ?r) ?h ?h' ?rs"},
   CreateCase ([@{term_pat "(?l::nat) < ?r"}], [])]) *}

(* Outer remains theorems particular to quicksort. *)
theorem outer_remains_qs1: "outer_remains h h' a (l+1) r \<Longrightarrow>
  Array.get h a ! l = Array.get h' a ! l \<and> subarray x l a h = subarray x l a h'" by auto2
theorem outer_remains_qs2: "outer_remains h h' a l r \<Longrightarrow>
  Array.get h a ! (r+1) = Array.get h' a ! (r+1) \<and> subarray (r+2) y a h = subarray (r+2) y a h'" by auto2
setup {* fold (add_rewrite_rule o conj_left_th) [@{thm outer_remains_qs1}, @{thm outer_remains_qs2}] *}
setup {* fold (add_rewrite_rule o conj_right_th) [@{thm outer_remains_qs1}, @{thm outer_remains_qs2}] *}

(* Sortedness of lists of form x @ [pivot] @ y. *)
setup {* add_rewrite_rule @{thm sorted_append} *}
theorem sorted_pivoted_list: "sorted (sublist' l pivot xs) \<Longrightarrow> sorted (sublist' (pivot + 1) r xs) \<Longrightarrow>
  \<forall>x\<in>set (sublist' l pivot xs). x \<le> xs ! pivot \<Longrightarrow> \<forall>y\<in>set (sublist' (pivot + 1) r xs). xs ! pivot \<le> y \<Longrightarrow>
  l \<le> pivot \<Longrightarrow> pivot < r \<Longrightarrow> r \<le> length xs \<Longrightarrow> sorted (sublist' l r xs)"
  by (tactic {* auto2s_tac @{context} (
      OBTAIN "sublist' pivot r xs = xs ! pivot # sublist' (pivot + 1) r xs" THEN
      CASE "pivot = 0" THEN OBTAIN "sublist' l r xs = sublist' l pivot xs @ sublist' pivot r xs") *})
setup {* del_prfstep_thm @{thm sorted_append} #> add_forward_prfstep @{thm sorted_pivoted_list} *}

theorem sorted_pivoted_list': "sorted (sublist' 1 r xs) \<Longrightarrow>
  \<forall>y\<in>set (sublist' 1 r xs). xs ! 0 \<le> y \<Longrightarrow> r \<le> length xs \<Longrightarrow> sorted (sublist' 0 r xs)"
  by (tactic {* auto2s_tac @{context} (OBTAIN "sublist' 0 r xs = xs ! 0 # sublist' 1 r xs") *})
setup {* add_forward_prfstep @{thm sorted_pivoted_list'} *}

lemma quicksort_sorts: "effect (quicksort a l r) h h' rs \<Longrightarrow>
  l < Array.length h a \<Longrightarrow> r < Array.length h a \<Longrightarrow>
  sorted (subarray l (r + 1) a h')" by auto2

end
