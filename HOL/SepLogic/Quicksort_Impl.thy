theory Quicksort_Impl
imports Reverse "../DataStrs/Quicksort"
begin

function part1 :: "'a::{heap,linorder} array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat Heap" where
  "part1 a l r p = (
     if r \<le> l then return r
     else do {
       v \<leftarrow> Array.nth a l;
       if v \<le> p then
         part1 a (l + 1) r p
       else do {
         swap a l r;
         part1 a l (r - 1) p }})"
  by auto
  termination by (relation "measure (\<lambda>(_,l,r,_). r - l )") auto
declare part1.simps [sep_proc_defs]

setup {* add_rewrite_rule_cond @{thm Quicksort.part1.simps} (map (with_filt o size1_filter) ["l", "r"]) *}
lemma part1_to_fun [hoare_triple]:
  "<p \<mapsto>\<^sub>a xs * \<up>(r < length xs)>
   part1 p l r a
   <\<lambda>rs. p \<mapsto>\<^sub>a snd (Quicksort.part1 xs l r a) * \<up>(rs = fst (Quicksort.part1 xs l r a))>"
@proof
  @let "d = r - l"
  @strong_induct d arbitrary l r xs
  @case "r \<le> l"
  @case "xs ! l \<le> a" @with @apply_induct_hyp "d - 1" "l + 1" r xs @end
  @apply_induct_hyp "d - 1" l "r - 1" "list_swap xs l r"
@qed
declare part1.simps [sep_proc_defs del]
setup {* del_prfstep_thm @{thm Quicksort.part1.simps} *}

(* Partition function. *)
definition partition :: "'a::{heap,linorder} array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where [sep_proc_defs]:
  "partition a l r = do {
     p \<leftarrow> Array.nth a r;
     m \<leftarrow> part1 a l (r - 1) p;
     v \<leftarrow> Array.nth a m;
     m' \<leftarrow> return (if v \<le> p then m + 1 else m);
     swap a m' r;
     return m' }"

setup {* add_rewrite_rule @{thm Quicksort.partition_def} *}
lemma partition_to_fun [hoare_triple]:
  "<a \<mapsto>\<^sub>a xs * \<up>(l < r) * \<up>(r < length xs)>
   partition a l r
   <\<lambda>rs. a \<mapsto>\<^sub>a snd (Quicksort.partition xs l r) * \<up>(rs = fst (Quicksort.partition xs l r))>" by auto2
declare partition_def [sep_proc_defs del]
setup {* del_prfstep_thm @{thm Quicksort.partition_def} *}

(* Quicksort function *)
function quicksort :: "'a::{heap,linorder} array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "quicksort a l r =
     (if l < r then do {
        p \<leftarrow> partition a l r;
        p \<leftarrow> assert (\<lambda>x. l \<le> x \<and> x \<le> r) p;
        (if l < p - 1 then quicksort a l (p - 1) else return ());
        (if p + 1 < r then quicksort a (p + 1) r else return ())
      }
     else return ())"
  by auto
  termination by (relation "measure (\<lambda>(a, l, r). (r - l))") auto
declare quicksort.simps [sep_proc_defs]

setup {* add_rewrite_rule_cond @{thm Quicksort.quicksort.simps} (map (with_filt o size1_filter) ["l", "r"]) *}
lemma quicksort_to_fun [hoare_triple]:
  "r < length xs \<Longrightarrow> <a \<mapsto>\<^sub>a xs>
   quicksort a l r
   <\<lambda>_. a \<mapsto>\<^sub>a Quicksort.quicksort xs l r>"
@proof
  @let "d = r - l"
  @strong_induct d arbitrary l r xs
  @case "l < r" @with
    @let "p = fst (Quicksort.partition xs l r)"
    @let "xs1 = snd (Quicksort.partition xs l r)"
    @let "xs2 = Quicksort.quicksort xs1 l (p - 1)"
    @have "p \<ge> l \<and> p \<le> r"
    @case "p + 1 \<ge> r" @with
      @case "l \<ge> p - 1" @then
      @apply_induct_hyp "(p-1)-l" l "p-1" xs1
    @end
    @apply_induct_hyp "r-(p+1)" "p+1" r xs2
    @case "l \<ge> p - 1"
    @apply_induct_hyp "(p-1)-l" l "p-1" xs1
  @end
@qed
declare quicksort.simps [sep_proc_defs del]
setup {* del_prfstep_thm @{thm Quicksort.quicksort.simps} *}

definition quicksort_all :: "('a::{heap,linorder}) array \<Rightarrow> unit Heap" where [sep_proc_defs]:
  "quicksort_all a = do {
     n \<leftarrow> Array.len a;
     if n = 0 then return ()
     else quicksort a 0 (n - 1) }"

theorem quicksort_sorts_basic [hoare_triple]:
  "<a \<mapsto>\<^sub>a xs>
   quicksort_all a
   <\<lambda>_. a \<mapsto>\<^sub>a sort xs>"
@proof
  @case "xs = []"
  @have "Quicksort.quicksort xs 0 (length xs - 1) = sort xs"
@qed
declare quicksort_all_def [sep_proc_defs del]

end
