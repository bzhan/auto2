(* Author: Max P.L. Haslbeck, Bohua Zhan
*)

theory MergeSort
  imports SepAuto "../DataStrs/DiscreteLog_Thms"
begin

section \<open>Simple functional version\<close>

fun merge_list :: "('a::linorder) list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "merge_list xs ys = (
     if xs = [] then ys else if ys = [] then xs
     else if last xs \<ge> last ys then merge_list (butlast xs) ys @ [last xs]
     else merge_list xs (butlast ys) @ [last ys])"
setup {* add_rewrite_rule @{thm merge_list.simps} *}
setup {* add_fun_induct_rule (@{term merge_list}, @{thm merge_list.induct}) *}

lemma merge_list_simps' [rewrite]:
  "merge_list [] ys = ys"
  "merge_list xs [] = xs"
  "merge_list (xs @ [x]) (ys @ [y]) =
    (if x \<ge> y then merge_list xs (ys @ [y]) @ [x]
               else merge_list (xs @ [x]) ys @ [y])" by auto2+
setup {* del_prfstep_thm @{thm merge_list.simps} *}

lemma merge_list_length [rewrite]:
  "length (merge_list xs ys) = length xs + length ys"
@proof @fun_induct "merge_list xs ys" @with
  @subgoal "(xs = xs, ys = ys)"
    @case "xs = []" @case "ys = []"
    @have "xs = butlast xs @ [last xs]"
    @have "ys = butlast ys @ [last ys]"
  @end
@qed

lemma merge_list_correct_mset [rewrite]:
  "mset (merge_list xs ys) = mset xs + mset ys"
@proof @fun_induct "merge_list xs ys" @with
  @subgoal "(xs = xs, ys = ys)"
    @case "xs = []" @case "ys = []"
    @have "xs = butlast xs @ [last xs]"
    @have "ys = butlast ys @ [last ys]"
  @end
@qed

lemma merge_list_correct_set [rewrite]:
  "set (merge_list xs ys) = set xs \<union> set ys"
@proof
  @have "set (merge_list xs ys) = set_mset (mset (merge_list xs ys))"
@qed

lemma merge_list_sorted [forward]:
  "sorted xs \<Longrightarrow> sorted ys \<Longrightarrow> sorted (merge_list xs ys)"
@proof @fun_induct "merge_list xs ys" @with
  @subgoal "(xs = xs, ys = ys)"
    @case "xs = []" @case "ys = []"
    @have "xs = butlast xs @ [last xs]"
    @have "ys = butlast ys @ [last ys]"
  @end
@qed

section \<open>Actual functional version\<close>

function mergeinto_fun :: "nat \<Rightarrow> nat \<Rightarrow> 'a::{heap,linorder} list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "mergeinto_fun 0 0 a b c = c"
| "mergeinto_fun (Suc la) 0 a b c =
    (let c' = mergeinto_fun la 0 a b c;
         e  = nth a la in
      list_update c' la e)"
| "mergeinto_fun 0 (Suc lb) a b c =
    (let c' = mergeinto_fun 0 lb a b c;
         e  = nth b lb in
      list_update c' lb e)"
| "mergeinto_fun (Suc la) (Suc lb) a b c =
    (let ha = nth a la; hb = nth b lb in
      if ha \<ge> hb then
        let c' = mergeinto_fun la (Suc lb) a b c in
          list_update c' (Suc (la+lb)) ha
      else 
        let c' = mergeinto_fun (Suc la) lb a b c in
          list_update c' (Suc (la+lb)) hb)"
by pat_completeness auto
termination by (relation "measure (\<lambda>(la, lb, a, b, c). la + lb)") auto

setup {* fold add_rewrite_rule @{thms mergeinto_fun.simps} *}
setup {* add_fun_induct_rule (@{term mergeinto_fun}, @{thm mergeinto_fun.induct}) *}

lemma mergeinto_fun_length [rewrite]:
  "length (mergeinto_fun la lb a b c) = length c"
@proof @fun_induct "mergeinto_fun la lb a b c" @qed

lemma mergeinto_fun_to_merge_list_induct [backward]:
  "length c = length a + length b \<Longrightarrow>
  la \<le> length a \<Longrightarrow> lb \<le> length b \<Longrightarrow>
  take (la + lb) (mergeinto_fun la lb a b c) = merge_list (take la a) (take lb b)"
@proof @fun_induct "mergeinto_fun la lb a b c" @with
  @subgoal "(la = Suc la, lb = Suc lb, a = a, b = b, c = c)"
    @case "nth a la \<ge> nth b lb" @with
      @have "Suc (la + Suc lb) \<le> length c"
      @let "res = mergeinto_fun (Suc la) (Suc lb) a b c"
      @have "nth a la = nth res (Suc (la + lb))"
    @end
    @case "nth a la < nth b lb" @with
      @have "Suc (Suc la + lb) \<le> length c"
      @let "res = mergeinto_fun (Suc la) (Suc lb) a b c"
      @have "nth b lb = nth res (Suc (la + lb))"
    @end
  @endgoal @end
@qed

lemma mergeinto_fun_to_merge_list [rewrite]:
  "length c = length a + length b \<Longrightarrow>
   mergeinto_fun (length a) (length b) a b c = merge_list a b"
@proof
  @let "res = mergeinto_fun (length a) (length b) a b c"
  @have "take (length c) res = res"
  @have "take (length a) a = a" @have "take (length b) b = b"
@qed

section {* Imperative version *}

function mergeinto :: "nat \<Rightarrow> nat \<Rightarrow> 'a::{heap,linorder} array \<Rightarrow> 'a array \<Rightarrow> 'a array \<Rightarrow> unit Heap" where
  "mergeinto 0 0 a b c = return ()"
| "mergeinto (Suc la) 0 a b c = do {
     mergeinto la 0 a b c;
     e \<leftarrow> Array.nth a la;
     Array.upd la e c;
     return ()
   }"
| "mergeinto 0 (Suc lb) a b c = do {
     mergeinto 0 lb a b c;
     e \<leftarrow> Array.nth b lb;
     Array.upd lb e c;
     return ()
   }"
| "mergeinto (Suc la) (Suc lb) a b c = do {
     ha \<leftarrow> Array.nth a la;
     hb \<leftarrow> Array.nth b lb;
     if ha \<ge> hb then do {
       mergeinto la (Suc lb) a b c;
       Array.upd (Suc (la+lb)) ha c;
       return ()
     }
     else do {
       mergeinto (Suc la) lb a b c;
       Array.upd (Suc (la+lb)) hb c;
       return ()
     }
   }"
by pat_completeness auto
termination by (relation "measure (\<lambda>(la, lb, a, b, c). la + lb)") auto

declare mergeinto.simps [sep_proc]

lemma mergeinto_to_fun [hoare_triple]:
  "la \<le> length as \<Longrightarrow> lb \<le> length bs \<Longrightarrow> length cs = length as + length bs \<Longrightarrow>
    <a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs * c \<mapsto>\<^sub>a cs>
    mergeinto la lb a b c
    <\<lambda>_. a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs * c \<mapsto>\<^sub>a mergeinto_fun la lb as bs cs>"
@proof @fun_induct "mergeinto_fun la lb as bs cs" @with
  @subgoal "(la = Suc la, lb = Suc lb, as = as, bs = bs, cs = cs)"
    @have "Suc la + Suc lb = Suc (la + lb) + 1"
    @case "bs ! lb \<le> as ! la"
  @endgoal @end
@qed

lemma mergeinto_correct [hoare_triple]:
  "la = length as \<Longrightarrow> lb = length bs \<Longrightarrow> length cs = la + lb \<Longrightarrow>
    <a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs * c \<mapsto>\<^sub>a cs>
    mergeinto la lb a b c
    <\<lambda>_. a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs * c \<mapsto>\<^sub>a merge_list as bs>"
  by auto2

definition atake :: "'a::heap array \<Rightarrow> nat \<Rightarrow> 'a array Heap" where [sep_proc]:
  "atake xs n = do {
     XS \<leftarrow> Array.freeze xs;
     Array.of_list (take n XS)
   }"

lemma atake_copies [hoare_triple]:
  "n \<le> length as \<Longrightarrow>
   <xs \<mapsto>\<^sub>a as> atake xs n <\<lambda>r. r \<mapsto>\<^sub>a take n as * xs \<mapsto>\<^sub>a as>" by auto2

definition adrop :: "'a::heap array \<Rightarrow> nat \<Rightarrow> 'a array Heap" where [sep_proc]:
  "adrop xs n = do {
     XS \<leftarrow> Array.freeze xs;
     Array.of_list (drop n XS)
   }"

lemma adrop_copies [hoare_triple]:
  "n \<le> length as \<Longrightarrow>
   <xs \<mapsto>\<^sub>a as> adrop xs n <\<lambda>r. r \<mapsto>\<^sub>a drop n as * xs \<mapsto>\<^sub>a as>" by auto2

partial_function (heap) mergeSort :: "'a::{heap,linorder} array \<Rightarrow> unit Heap" where
  "mergeSort p = do {
    len \<leftarrow> Array.len p;
    if len \<le> 1 then return ()
    else do { 
      a \<leftarrow> atake p (len div 2);
      b \<leftarrow> adrop p (len div 2);
      mergeSort a;
      mergeSort b;
      mergeinto (len div 2) (len - len div 2) a b p;
      return ()
    }
  }"
declare mergeSort.simps [sep_proc]

fun mergesort_fun :: "'a::linorder list \<Rightarrow> 'a list" where
  "mergesort_fun xs =
    (if length xs \<le> 1 then xs else
     merge_list (mergesort_fun (take (length xs div 2) xs)) (mergesort_fun (drop (length xs div 2) xs)))"
setup {* add_rewrite_rule @{thm mergesort_fun.simps} *}
setup {* add_fun_induct_rule (@{term mergesort_fun}, @{thm mergesort_fun.induct}) *}

lemma sort_length_le1 [rewrite]: "length xs \<le> 1 \<Longrightarrow> sort xs = xs"
@proof
  @case "xs = []" @have "xs = hd xs # tl xs" @case "tl xs = []"
@qed

lemma mergesort_fun_correct [rewrite]:
  "mergesort_fun xs = sort xs"
@proof @fun_induct "mergesort_fun xs" @with
  @subgoal "xs = xs"
    @case "length xs \<le> 1"
    @let "l1 = length xs div 2"
    @have "mset (take l1 xs) + mset (drop l1 xs) = mset xs" @with
      @have "take l1 xs @ drop l1 xs = xs"
    @end
  @end
@qed

lemma mergeSort_to_fun [hoare_triple]:
  "<p \<mapsto>\<^sub>a xs>
   mergeSort p
   <\<lambda>_. p \<mapsto>\<^sub>a mergesort_fun xs>\<^sub>t"
@proof @fun_induct "mergesort_fun xs" arbitrary p @qed

lemma mergeSort_correct [hoare_triple]:
  "<p \<mapsto>\<^sub>a xs> mergeSort p <\<lambda>_. p \<mapsto>\<^sub>a sort xs>\<^sub>t" by auto2

end
