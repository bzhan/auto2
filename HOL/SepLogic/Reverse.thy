theory Reverse
imports SepAuto "../DataStrs/Arrays_Ex"
begin

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
