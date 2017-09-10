theory Quicksort
imports Reverse "../DataStrs/Quicksort_Func"
begin

function part1 :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "part1 a left right p = (
     if (right \<le> left) then return right
     else do {
       v \<leftarrow> Array.nth a left;
       (if v \<le> p
        then (part1 a (left + 1) right p)
        else (do { swap a left right;
                   part1 a left (right - 1) p }))
     })"
  by auto
  termination by (relation "measure (\<lambda>(_,l,r,_). r - l )") auto
declare part1.simps [sep_proc_defs]
setup {* add_hoare_induct_rule (@{term part1}, @{thm part1.induct}) *}

setup {* add_rewrite_rule_cond @{thm Quicksort_Func.part1.simps}
  [with_filt (size1_filter "l"), with_filt (size1_filter "r")] *}
lemma part1_to_fun [hoare_triple]:
  "<p \<mapsto>\<^sub>a xs * \<up>(r < length xs)>
   part1 p l r a
   <\<lambda>rs. p \<mapsto>\<^sub>a snd (Quicksort_Func.part1 xs l r a) * \<up>(rs = fst (Quicksort_Func.part1 xs l r a))>"
@proof @hoare_induct @qed
declare part1.simps [sep_proc_defs del]
setup {* del_prfstep_thm @{thm Quicksort_Func.part1.simps} *}

(* Partition function. *)
definition partition :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "partition a left right = do {
     pivot \<leftarrow> Array.nth a right;
     middle \<leftarrow> part1 a left (right - 1) pivot;
     v \<leftarrow> Array.nth a middle;
     m \<leftarrow> return (if (v \<le> pivot) then (middle + 1) else middle);
     swap a m right;
     return m
   }"

declare partition_def [sep_proc_defs]
setup {* add_rewrite_rule @{thm Quicksort_Func.partition_def} *}
lemma partition_to_fun [hoare_triple]:
  "<a \<mapsto>\<^sub>a xs * \<up>(l < r) * \<up>(r < length xs)>
   partition a l r
   <\<lambda>rs. a \<mapsto>\<^sub>a snd (Quicksort_Func.partition xs l r) * \<up>(rs = fst (Quicksort_Func.partition xs l r))>" by auto2
declare partition_def [sep_proc_defs del]
setup {* del_prfstep_thm @{thm Quicksort_Func.partition_def} *}

(* Quicksort function *)
function quicksort :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "quicksort a left right =
     (if left < right then do {
        pivot \<leftarrow> partition a left right;
        pivot \<leftarrow> assert (\<lambda>x. left \<le> x \<and> x \<le> right) pivot;
        quicksort a left (pivot - 1);
        quicksort a (pivot + 1) right
      }
     else return ())"
  by auto
  termination by (relation "measure (\<lambda>(a, l, r). (r - l))") auto
declare quicksort.simps [sep_proc_defs]
setup {* add_hoare_induct_rule (@{term quicksort}, @{thm quicksort.induct}) *}

setup {* add_rewrite_rule_cond @{thm Quicksort_Func.quicksort.simps}
  [with_filt (size1_filter "l"), with_filt (size1_filter "r")] *}
theorem quicksort_trivial [hoare_triple]:
  "<a \<mapsto>\<^sub>a xs * \<up>(l \<ge> r)>
   quicksort a l r
   <\<lambda>_. a \<mapsto>\<^sub>a Quicksort_Func.quicksort xs l r>" by auto2

theorem quicksort_to_fun [hoare_triple]:
  "<a \<mapsto>\<^sub>a xs * \<up>(l < length xs) * \<up>(r < length xs)>
   quicksort a l r
   <\<lambda>_. a \<mapsto>\<^sub>a Quicksort_Func.quicksort xs l r>"
@proof @hoare_induct
  @contradiction
  @case "l < r" @with
    @have "l < r \<and> r < length xs"
    @let "p = fst (Quicksort_Func.partition xs l r)"
    @have "p \<ge> l \<and> p \<le> r"
    @case "p + 1 \<ge> r"
    @case "l \<ge> p - 1"
  @end
@qed

declare quicksort.simps [sep_proc_defs del]
setup {* del_prfstep_thm @{thm Quicksort_Func.quicksort.simps} *}

theorem quicksort_sorts:
  "<a \<mapsto>\<^sub>a xs * \<up>(l < length xs) * \<up>(r < length xs)>
   quicksort a l r
   <\<lambda>rs. \<exists>\<^sub>Axs'. a \<mapsto>\<^sub>a xs' * \<up>(sorted (sublist l (r + 1) xs'))>" by auto2

end
