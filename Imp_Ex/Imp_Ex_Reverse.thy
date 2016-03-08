(* Reversal of an array, following Imperative_Reverse in
   HOL/Imperative_HOL/ex. *)

theory Imp_Ex_Reverse
imports Imp_Thms
begin

fun swap :: "'a::heap array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "swap a i j = do {
     x \<leftarrow> Array.nth a i;
     y \<leftarrow> Array.nth a j;
     Array.upd i y a;
     Array.upd j x a;
     return ()
   }"

fun rev :: "'a::heap array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "rev a i j = (if i < j then do {
     swap a i j;
     rev a (i + 1) (j - 1)
   }
   else return ())"

(* Properties of swap. *)
setup {* add_rewrite_rule @{thm swap.simps} *}
lemma swap_pointwise [rewrite]: "effect (swap a i j) h h' r \<Longrightarrow> Array.get h' a ! k =
  (if k = i then Array.get h a ! j else if k = j then Array.get h a ! i else Array.get h a ! k)" by auto2
lemma swap_length [rewrite]: "effect (swap a i j) h h' r \<Longrightarrow> Array.length h a = Array.length h' a" by auto2
lemma swap_succeed [backward]: "i < Array.length h a \<and> j < Array.length h a \<Longrightarrow> success (swap a i j) h" by auto2
setup {* del_prfstep_thm @{thm swap.simps} *}

(* Induction rule for rev. *)
setup {* add_rewrite_rule_cond @{thm rev.simps} [with_filt (size1_filter "i")] *}
theorem rev_induct': "(\<forall>a i j. (i < j \<longrightarrow> P a (i + 1) (j - 1)) \<longrightarrow> P a i j) \<Longrightarrow> P (a::'a::heap array) (i::nat) (j::nat)"
  apply (induct rule: rev.induct) by blast
setup {* add_prfstep_imp_induction @{term_pat "rev ?a ?i ?j"} @{thm rev_induct'} *}

(* Properties of rev. *)
lemma rev_length [rewrite]:
  "effect (rev a i j) h h' r \<Longrightarrow> Array.length h a = Array.length h' a" by auto2

theorem reduce_minus_1 [rewrite]: "(k::nat) \<ge> i + 1 \<Longrightarrow> j - 1 - (k - (1 + i)) = j - (k - i)" by simp

lemma rev_pointwise [rewrite]: "effect (rev a i j) h h' r \<Longrightarrow> Array.get h' a ! k =
  (if k < i then Array.get h a ! k else if j < k then Array.get h a ! k
   else Array.get h a ! (j - (k - i)))" by auto2

lemma rev_succeed' [backward]: "i < Array.length h a \<and> j < Array.length h a \<Longrightarrow> success (rev a i j) h" by auto2
lemma rev_succeed: "success (rev a 0 (Array.length h a - 1)) h" by auto2

setup {* fold del_prfstep_thm [@{thm rev.simps}, @{thm rev_induct'}] *}

lemma rev2_rev': "effect (rev a i j) h h' u \<Longrightarrow> j < Array.length h a \<Longrightarrow>
  subarray i (j + 1) a h' = List.rev (subarray i (j + 1) a h)"
  by (tactic {* auto2s_tac @{context}
    (OBTAIN "length (subarray i (1 + j) a h') = length (List.rev (subarray i (1 + j) a h))") *})

(* Just a special case of previous proof. *)
lemma rev2_rev: "effect (rev a 0 (Array.length h a - 1)) h h' u \<Longrightarrow>
  Array.get h' a = List.rev (Array.get h a)"
  by (tactic {* auto2s_tac @{context}
    (OBTAIN "length (Array.get h' a) = length (List.rev (Array.get h a))") *})

end
