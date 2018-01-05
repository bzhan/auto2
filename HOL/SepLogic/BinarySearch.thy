(* Binary search example.
   Author: Max P.L. Haslbeck, Bohua Zhan *)

theory BinarySearch
imports SepAuto "../DataStrs/DiscreteLog_Thms"
begin

function binarysearch_fun :: "nat \<Rightarrow> nat \<Rightarrow> 'a::linorder \<Rightarrow> 'a list \<Rightarrow> bool" where
  "binarysearch_fun l r x xs =
   (if l \<ge> r then False
    else if l + 1 \<ge> r then xs ! l = x
    else let m = avg l r in
      if xs ! m = x then True
      else if xs ! m < x then binarysearch_fun (m + 1) r x xs
      else binarysearch_fun l m x xs)"
by pat_completeness auto
termination by (relation "measure (\<lambda>(l,r,a,f). r-l)") auto

setup {* add_unfolding_rule @{thm binarysearch_fun.simps} *}
setup {* register_wellform_data ("binarysearch_fun l r x xs", ["l \<le> r", "r \<le> length xs"]) *}
setup {* add_prfstep_check_req ("binarysearch_fun l r x xs", "l \<le> r \<and> r \<le> length xs") *}
setup {* add_fun_induct_rule (@{term binarysearch_fun}, @{thm binarysearch_fun.induct}) *}

lemma binarysearch_fun_correct [rewrite]:
  "sorted xs \<Longrightarrow> l \<le> r \<Longrightarrow> r \<le> length xs \<Longrightarrow>
   binarysearch_fun l r x xs \<longleftrightarrow> (\<exists>i. l \<le> i \<and> i < r \<and> xs ! i = x)"
@proof @fun_induct "binarysearch_fun l r x xs" @with
  @subgoal "(l = l, r = r, x = x, xs = xs)"
  @unfold "binarysearch_fun l r x xs"
  @case "l \<ge> r" @case "l + 1 \<ge> r"
  @let "m = avg l r"
  @case "xs ! m = x"
  @case "xs ! m < x" @with
    @case "\<exists>i. l \<le> i \<and> i < r \<and> xs ! i = x" @with
      @obtain i where "l \<le> i \<and> i < r \<and> xs ! i = x"
      @have "m < length xs"
    @end
  @end @end
@qed

partial_function (heap) binarysearch :: "nat \<Rightarrow> nat \<Rightarrow> 'a::{heap,linorder} \<Rightarrow> 'a array \<Rightarrow> bool Heap" where
  "binarysearch l r x a = (
    if l \<ge> r then return False
    else if l + 1 \<ge> r then do {
      v \<leftarrow> Array.nth a l;
      return (v = x) }
    else let m = avg l r in do {
      v \<leftarrow> Array.nth a m;
      (if v = x then return True
       else if v < x then binarysearch (m + 1) r x a
       else binarysearch l m x a)
    })"
declare binarysearch.simps [sep_proc]

lemma binarysearch_correct [hoare_triple]:
  "<a \<mapsto>\<^sub>a xs * \<up>(r \<le> length xs) * \<up>(l \<le> r)>
   binarysearch l r x a
   <\<lambda>res. a \<mapsto>\<^sub>a xs * \<up>(res \<longleftrightarrow> binarysearch_fun l r x xs)>\<^sub>t"
@proof @fun_induct "binarysearch_fun l r x xs" @with
  @subgoal "(l = l, r = r, x = x, xs = xs)"
    @unfold "binarysearch_fun l r x xs"
    @case "l \<ge> r" @case "l + 1 \<ge> r"
  @end
@qed

lemma binarysearch_correct' [hoare_triple]:
  "sorted xs \<Longrightarrow> r \<le> length xs \<Longrightarrow> l \<le> r \<Longrightarrow> <a \<mapsto>\<^sub>a xs>
   binarysearch l r x a
   <\<lambda>res. a \<mapsto>\<^sub>a xs * \<up>(res \<longleftrightarrow> (\<exists>i. l \<le> i \<and> i < r \<and> xs ! i = x))>\<^sub>t"
  by auto2

end
