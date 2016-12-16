theory Reverse
imports SepAuto More_Lists
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

lemma swap_rule [hoare_triple, hoare_create_case]:
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

theorem rev_induct': "(\<forall>a i j. (i < j \<longrightarrow> P a (i + 1) (j - 1)) \<longrightarrow> P a i j) \<Longrightarrow> P (a::'a::heap array) (i::nat) (j::nat)"
  apply (induct rule: rev.induct) by blast
setup {* add_prfstep_imp_induction @{term_pat "rev ?a ?i ?j"} @{thm rev_induct'} *}

theorem reduce_minus_1 [rewrite]: "(k::nat) \<ge> i + 1 \<Longrightarrow> j - 1 - (k - (1 + i)) = j - (k - i)" by simp

lemma rev_rule_length [hoare_triple]:
  "<p \<mapsto>\<^sub>a xs * \<up>(j < length xs)>
   rev p i j
   <\<lambda>_. \<exists>\<^sub>Axs'. p \<mapsto>\<^sub>a xs' * \<up>(length xs' = length xs)>" by auto2

theorem list_swap_eval' [rewrite]:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> (list_swap xs i j) ! k =
    (if k = i then xs ! j else if k = j then xs ! i else xs ! k)" by auto2

lemma rev_rule [hoare_triple]:
  "<p \<mapsto>\<^sub>a xs * \<up>(j < length xs)>
   rev p i j
   <\<lambda>_. \<exists>\<^sub>Axs'. p \<mapsto>\<^sub>a xs' * \<up>(\<forall>k. xs' ! k =
    (if k < i then xs ! k else if j < k then xs ! k
     else xs ! (j - (k - i))))>" by auto2

declare rev.simps [sep_proc_defs del]
lemma rev_is_rev:
  "<p \<mapsto>\<^sub>a xs * \<up>(length xs > 0)> rev p 0 (length xs - 1) <\<lambda>_. p \<mapsto>\<^sub>a List.rev xs>"
  by (tactic {* auto2s_tac @{context} (HAVE "length xs = length (List.rev xs)") *})

end
