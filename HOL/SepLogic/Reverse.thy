theory Reverse
imports SepAuto "../DataStrs/Arrays_Ex"
begin

definition swap :: "'a::heap array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "swap a i j = do {
     x \<leftarrow> Array.nth a i;
     y \<leftarrow> Array.nth a j;
     Array.upd i y a;
     Array.upd j x a;
     return ()
   }"
declare swap_def [sep_proc_defs]

lemma swap_rule [hoare_triple]:
  "<p \<mapsto>\<^sub>a xs * \<up>(i < length xs) * \<up>(j < length xs)>
   swap p i j
   <\<lambda>_. p \<mapsto>\<^sub>a list_swap xs i j>" by auto2

fun rev :: "'a::heap array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "rev a i j = (if i < j then do {
     swap a i j;
     rev a (i + 1) (j - 1)
   }
   else return ())"
declare rev.simps [sep_proc_defs]
setup {* add_hoare_induct_rule (@{term_pat Reverse.rev}, @{thm rev.induct}) *}

lemma rev_to_fun [hoare_triple]:
  "<p \<mapsto>\<^sub>a xs * \<up>(j < length xs)>
   rev p i j
   <\<lambda>_. p \<mapsto>\<^sub>a rev_swap xs i j>"
@proof @hoare_induct @qed
declare rev.simps [sep_proc_defs del]

lemma rev_is_rev:
  "<p \<mapsto>\<^sub>a xs * \<up>(xs \<noteq> [])>
   rev p 0 (length xs - 1)
   <\<lambda>_. p \<mapsto>\<^sub>a List.rev xs>" by auto2

end
