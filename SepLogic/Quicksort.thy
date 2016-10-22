theory Quicksort
imports Reverse More_Lists
  "~~/src/HOL/Imperative_HOL/ex/Subarray"
begin

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

declare part1.simps [sep_proc_defs]

theorem part1_induct': "(\<forall>a left right p.
    ((\<not> right \<le> left \<longrightarrow> (\<forall>v.  v \<le> p \<longrightarrow> P a (left + 1) right p)) \<and>
     (\<not> right \<le> left \<longrightarrow> (\<forall>v. \<not>v \<le> p \<longrightarrow> P a left (right - 1) p))) \<longrightarrow> P a left right p) \<Longrightarrow>
    P (a::nat array) (left::nat) (right::nat) (p::nat)"
  apply (induct rule: part1.induct) by blast
setup {* add_prfstep_imp_induction @{term_pat "part1 ?a ?l ?r ?p"} @{thm part1_induct'} *}

theorem part1_permutes [hoare_triple]:
  "<p \<mapsto>\<^sub>a xs * \<up>(r < length xs)>
   part1 p l r a
   <\<lambda>rs. \<exists>\<^sub>Axs'. p \<mapsto>\<^sub>a xs' * \<up>(mset xs' = mset xs)>" by auto2

theorem part1_returns_index_in_bounds' [hoare_triple]:
  "<p \<mapsto>\<^sub>a xs * \<up>(r < length xs)>
   part1 p l r a
   <\<lambda>rs. \<exists>\<^sub>Axs'. p \<mapsto>\<^sub>a xs' * \<up>(if r \<le> l then rs = r else l \<le> rs \<and> rs \<le> r)>" by auto2

theorem part1_outer_remains [hoare_triple]:
  "<p \<mapsto>\<^sub>a xs * \<up>(r < length xs)>
   part1 p l r a
   <\<lambda>_. \<exists>\<^sub>Axs'. p \<mapsto>\<^sub>a xs' * \<up>(outer_remains xs xs' l r)>" by auto2

theorem part1_partitions1 [hoare_triple]:
  "<p \<mapsto>\<^sub>a xs * \<up>(r < length xs)>
   part1 p l r a
   <\<lambda>rs. \<exists>\<^sub>Axs'. p \<mapsto>\<^sub>a xs' * \<up>(\<forall>i. l \<le> i \<longrightarrow> i < rs \<longrightarrow> xs' ! i \<le> a)>" by auto2

theorem part1_partitions2 [hoare_triple]:
  "<p \<mapsto>\<^sub>a xs * \<up>(r < length xs)>
   part1 p l r a
   <\<lambda>rs. \<exists>\<^sub>Axs'. p \<mapsto>\<^sub>a xs' * \<up>(\<forall>i. rs < i \<longrightarrow> i \<le> r \<longrightarrow> xs' ! i \<ge> a)>" by auto2

declare part1.simps [sep_proc_defs del]

theorem part1_returns_index_in_bounds [hoare_triple]:
  "<p \<mapsto>\<^sub>a xs * \<up>(r < length xs) * \<up>(l \<le> r)>
   part1 p l r a
   <\<lambda>rs. \<exists>\<^sub>Axs'. p \<mapsto>\<^sub>a xs' * \<up>(l \<le> rs) * \<up>(rs \<le> r)>" by auto2
setup {* del_prfstep_thm @{thm part1_returns_index_in_bounds'} *}

(* Partition function. *)
definition partition :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "partition a left right = do {
     pivot \<leftarrow> Array.nth a right;
     middle \<leftarrow> part1 a left (right - 1) pivot;
     v \<leftarrow> Array.nth a middle;
     m \<leftarrow> return (if (v \<le> pivot) then (middle + 1) else middle);
     comment (\<exists>\<^sub>Axs. a \<mapsto>\<^sub>a xs *
              \<up>(\<forall>i. left \<le> i \<and> i < m \<longrightarrow> xs ! i \<le> pivot) *
              \<up>(\<forall>i. m \<le> i \<and> i < right - 1 \<longrightarrow> xs ! i \<ge> pivot) *
              \<up>(xs ! right = pivot));
     swap a m right;
     return m
   }"
declare partition_def [sep_proc_defs]

theorem partition_basics [hoare_triple]:
  "<a \<mapsto>\<^sub>a xs * \<up>(l < r) * \<up>(r < length xs)>
   partition a l r
   <\<lambda>rs. \<exists>\<^sub>Axs'. a \<mapsto>\<^sub>a xs' * \<up>(outer_remains xs xs' l r) * \<up>(mset xs' = mset xs) * \<up>(l \<le> rs \<le> r)>" by auto2

theorem partition_partitions [hoare_triple]:
  "<a \<mapsto>\<^sub>a xs * \<up>(l < r) * \<up>(r < length xs)>
   partition a l r
   <\<lambda>rs. \<exists>\<^sub>Axs'. a \<mapsto>\<^sub>a xs' * \<up>(\<forall>x\<in>set (sublist' l rs xs'). x \<le> xs' ! rs) *
              \<up>(\<forall>x\<in>set (sublist' (rs + 1) (r + 1) xs'). xs' ! rs \<le> x)>" by auto2

(* Quicksort function *)
function quicksort :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "quicksort a left right =
     (if left < right then
        do {
          pivot \<leftarrow> partition a left right;
          pivot \<leftarrow> assert (\<lambda>x. left \<le> x \<and> x \<le> right) pivot;
          comment (\<up>(if pivot > 0 then pivot = 1 + (pivot - 1) else pivot = 0));
          comment (\<exists>\<^sub>Axs. a \<mapsto>\<^sub>a xs * \<up>(left < length xs) * \<up>(pivot - 1 < length xs));
          quicksort a left (pivot - 1);
          comment (\<exists>\<^sub>Axs. a \<mapsto>\<^sub>a xs * \<up>(pivot + 1 \<ge> right \<or> pivot + 1 < length xs));
          quicksort a (pivot + 1) right
        }
     else return ())"
  by pat_completeness auto
  termination by (relation "measure (\<lambda>(a, l, r). (r - l))") auto

declare quicksort.simps [sep_proc_defs]

theorem quicksort_induct': "(\<forall>arr left right.
    ((left < right \<longrightarrow> (\<forall>p. left \<le> p \<le> right \<longrightarrow> P arr left (p - 1))) \<and>
     (left < right \<longrightarrow> (\<forall>p. left \<le> p \<le> right \<longrightarrow> P arr (p + 1) right))) \<longrightarrow> P arr left right) \<Longrightarrow>
    P (arr::nat array) (left::nat) (right::nat)"
  apply (induct rule: quicksort.induct) by (metis closed_interval_def)
setup {* add_prfstep_imp_induction @{term_pat "quicksort ?a ?left ?right"} @{thm quicksort_induct'} *}

theorem quicksort_trivial [hoare_triple]:
  "<a \<mapsto>\<^sub>a xs * \<up>(l \<ge> r)>
   quicksort a l r
   <\<lambda>_. \<exists>\<^sub>Axs'. a \<mapsto>\<^sub>a xs' * \<up>(xs' = xs)>" by auto2

theorem quicksort_outer_remains [hoare_triple]:
  "<a \<mapsto>\<^sub>a xs * \<up>(l < length xs) * \<up>(r < length xs)>
   quicksort a l r
   <\<lambda>rs. \<exists>\<^sub>Axs'. a \<mapsto>\<^sub>a xs' * \<up>(outer_remains xs xs' l r)>" by auto2

theorem quicksort_permutes' [hoare_triple]:
  "<a \<mapsto>\<^sub>a xs * \<up>(l < length xs) * \<up>(r < length xs)>
   quicksort a l r
   <\<lambda>rs. \<exists>\<^sub>Axs'. a \<mapsto>\<^sub>a xs' * \<up>(mset xs' = mset xs)>" by auto2

declare quicksort.simps [sep_proc_defs del]
theorem quicksort_permutes [hoare_triple]:
  "<a \<mapsto>\<^sub>a xs * \<up>(l < length xs) * \<up>(r < length xs)>
   quicksort a l r
   <\<lambda>rs. \<exists>\<^sub>Axs'. a \<mapsto>\<^sub>a xs' * \<up>(mset (sublist' l (r+1) xs') = mset (sublist' l (r+1) xs))>" by auto2
setup {* del_prfstep_thm @{thm quicksort_permutes'} *}

(* Outer remains theorems particular to quicksort. *)
theorem outer_remains_eqs1: "outer_remains xs xs' (l+1) r \<Longrightarrow>
  xs' ! l = xs ! l \<and> sublist' x l xs' = sublist' x l xs" by auto2

theorem outer_remains_eqs2: "outer_remains xs xs' l r \<Longrightarrow>
  xs' ! (r+1) = xs ! (r+1) \<and> sublist' (r+2) y xs' = sublist' (r+2) y xs" by auto2

setup {* fold (add_rewrite_rule_bidir o conj_left_th) [@{thm outer_remains_eqs1}, @{thm outer_remains_eqs2}] *}
setup {* fold (add_rewrite_rule_bidir o conj_right_th) [@{thm outer_remains_eqs1}, @{thm outer_remains_eqs2}] *}

(* Sortedness of lists of form x @ [pivot] @ y. *)
setup {* add_rewrite_rule @{thm sorted_append} *}
theorem sorted_pivoted_list [forward]: "sorted (sublist' (pivot + 1) r xs) \<Longrightarrow> sorted (sublist' l pivot xs) \<Longrightarrow>
  \<forall>x\<in>set (sublist' l pivot xs). x \<le> xs ! pivot \<Longrightarrow> \<forall>y\<in>set (sublist' (pivot + 1) r xs). xs ! pivot \<le> y \<Longrightarrow>
  l \<le> pivot \<Longrightarrow> pivot < r \<Longrightarrow> r \<le> length xs \<Longrightarrow> sorted (sublist' l r xs)"
  by (tactic {* auto2s_tac @{context} (
      OBTAIN "sublist' pivot r xs = xs ! pivot # sublist' (pivot + 1) r xs" THEN
      CASE "pivot = 0" THEN OBTAIN "sublist' l r xs = sublist' l pivot xs @ sublist' pivot r xs") *})
setup {* del_prfstep_thm @{thm sorted_append} *}

theorem sorted_pivoted_list' [forward]: "sorted (sublist' 1 r xs) \<Longrightarrow>
  \<forall>y\<in>set (sublist' 1 r xs). xs ! 0 \<le> y \<Longrightarrow> r \<le> length xs \<Longrightarrow> sorted (sublist' 0 r xs)"
  by (tactic {* auto2s_tac @{context} (OBTAIN "sublist' 0 r xs = xs ! 0 # sublist' 1 r xs") *})

declare quicksort.simps [sep_proc_defs]

setup {* add_gen_prfstep ("quicksort_case",
  [WithTerm @{term_pat "quicksort ?a ?l ?r"},
   CreateCase @{term_pat "(?l::nat) < ?r"}]) *}

theorem sorted_triv_list:
  "l \<ge> r \<Longrightarrow> sorted (sublist' l (1 + r) xs)"
  by (tactic {* auto2s_tac @{context} (CASE "l \<ge> length xs" THEN CASE "l = r" THEN OBTAIN "l > r") *})
setup {* add_forward_prfstep_cond @{thm sorted_triv_list} [with_term "sublist' ?l (1 + ?r) ?xs"] *}

theorem quicksort_sorts:
  "<a \<mapsto>\<^sub>a xs * \<up>(l < length xs) * \<up>(r < length xs)>
   quicksort a l r
   <\<lambda>rs. \<exists>\<^sub>Axs'. a \<mapsto>\<^sub>a xs' * \<up>(sorted (sublist' l (r + 1) xs'))>" by auto2

end
