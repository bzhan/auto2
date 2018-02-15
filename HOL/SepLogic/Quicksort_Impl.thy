theory Quicksort_Impl
imports Arrays_Impl "../DataStrs/Quicksort"
begin

partial_function (heap) part1 :: "'a::{heap,linorder} array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat Heap" where
  "part1 a l r p = (
     if r \<le> l then return r
     else do {
       v \<leftarrow> Array.nth a l;
       if v \<le> p then
         part1 a (l + 1) r p
       else do {
         swap a l r;
         part1 a l (r - 1) p }})"
declare part1.simps [sep_proc]

lemma part1_to_fun [hoare_triple]:
  "r < length xs \<Longrightarrow> <p \<mapsto>\<^sub>a xs>
   part1 p l r a
   <\<lambda>rs. p \<mapsto>\<^sub>a snd (Quicksort.part1 xs l r a) * \<up>(rs = fst (Quicksort.part1 xs l r a))>"
@proof @fun_induct "Quicksort.part1 xs l r a" @with
  @subgoal "(xs = xs, l = l, r = r, a = a)" @unfold "Quicksort.part1 xs l r a" @end
@qed

(* Partition function. *)
definition partition :: "'a::{heap,linorder} array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where [sep_proc]:
  "partition a l r = do {
     p \<leftarrow> Array.nth a r;
     m \<leftarrow> part1 a l (r - 1) p;
     v \<leftarrow> Array.nth a m;
     m' \<leftarrow> return (if v \<le> p then m + 1 else m);
     swap a m' r;
     return m' }"

lemma partition_to_fun [hoare_triple]:
  "l < r \<Longrightarrow> r < length xs \<Longrightarrow> <a \<mapsto>\<^sub>a xs>
   partition a l r
   <\<lambda>rs. a \<mapsto>\<^sub>a snd (Quicksort.partition xs l r) * \<up>(rs = fst (Quicksort.partition xs l r))>"
@proof @unfold "Quicksort.partition xs l r" @qed

(* Quicksort function *)
partial_function (heap) quicksort :: "'a::{heap,linorder} array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "quicksort a l r = (
     if l \<ge> r then return ()
     else do {
       p \<leftarrow> partition a l r;
       (if l < p - 1 then quicksort a l (p - 1) else return ());
       (if p + 1 < r then quicksort a (p + 1) r else return ())
     })"
declare quicksort.simps [sep_proc]

lemma quicksort_to_fun [hoare_triple]:
  "r < length xs \<Longrightarrow> <a \<mapsto>\<^sub>a xs>
   quicksort a l r
   <\<lambda>_. a \<mapsto>\<^sub>a Quicksort.quicksort xs l r>"
@proof
  @let "d = r - l"
  @strong_induct d arbitrary l r xs
  @unfold "Quicksort.quicksort xs l r"
  @case "l \<ge> r"
  @let "p = fst (Quicksort.partition xs l r)"
  @let "xs1 = snd (Quicksort.partition xs l r)"
  @let "xs2 = Quicksort.quicksort xs1 l (p - 1)"
  @case "p + 1 \<ge> r" @with
    @case "l \<ge> p - 1" @then
    @apply_induct_hyp "(p-1)-l" l "p-1" xs1
  @end
  @apply_induct_hyp "r-(p+1)" "p+1" r xs2
  @case "l \<ge> p - 1"
  @apply_induct_hyp "(p-1)-l" l "p-1" xs1
@qed

definition quicksort_all :: "('a::{heap,linorder}) array \<Rightarrow> unit Heap" where [sep_proc]:
  "quicksort_all a = do {
     n \<leftarrow> Array.len a;
     if n = 0 then return ()
     else quicksort a 0 (n - 1) }"

theorem quicksort_sorts_basic [hoare_triple]:
  "<a \<mapsto>\<^sub>a xs>
   quicksort_all a
   <\<lambda>_. a \<mapsto>\<^sub>a sort xs>" by auto2

end
