theory Arrays_Impl
  imports SepAuto "../DataStrs/Arrays_Ex"
begin

section {* Array copy *}

fun array_copy :: "'a::heap array \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "array_copy a b 0 = (return ())"
| "array_copy a b (Suc n) = do {
      array_copy a b n;
      x \<leftarrow> Array.nth a n;
      Array.upd n x b;
      return () }"
declare array_copy.simps [sep_proc]

lemma array_copy_rule [hoare_triple]:
  "n \<le> length as \<Longrightarrow> n \<le> length bs \<Longrightarrow>
   <a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs>
    array_copy a b n
   <\<lambda>_. a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a Arrays_Ex.array_copy as bs n>"
@proof @induct n @qed

section {* Swap *}

definition swap :: "'a::heap array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where [sep_proc]:
  "swap a i j = do {
     x \<leftarrow> Array.nth a i;
     y \<leftarrow> Array.nth a j;
     Array.upd i y a;
     Array.upd j x a;
     return ()
   }"

lemma swap_rule [hoare_triple]:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow>
   <p \<mapsto>\<^sub>a xs>
   swap p i j
   <\<lambda>_. p \<mapsto>\<^sub>a list_swap xs i j>" by auto2

section {* Reverse *}

fun rev :: "'a::heap array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "rev a i j = (if i < j then do {
     swap a i j;
     rev a (i + 1) (j - 1)
   }
   else return ())"
declare rev.simps [sep_proc]

lemma rev_to_fun [hoare_triple]:
  "j < length xs \<Longrightarrow>
   <p \<mapsto>\<^sub>a xs>
   rev p i j
   <\<lambda>_. p \<mapsto>\<^sub>a rev_swap xs i j>"
@proof @fun_induct "rev_swap xs i j" @with
  @subgoal "(xs = xs, i = i, j = j)"
    @unfold "rev_swap xs i j"
  @end
@qed

lemma rev_is_rev [hoare_triple]:
  "xs \<noteq> [] \<Longrightarrow>
   <p \<mapsto>\<^sub>a xs>
   rev p 0 (length xs - 1)
   <\<lambda>_. p \<mapsto>\<^sub>a List.rev xs>" by auto2

end
