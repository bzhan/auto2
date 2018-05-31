(* Setup for proof steps related to logic. *)

theory Logic_FOL
imports Auto2_FOL
begin

section \<open>Trivial contradictions\<close>

setup {* add_resolve_prfstep @{thm refl} *}
setup {* add_forward_prfstep @{thm contra_triv} *}
setup {* add_resolve_prfstep @{thm TrueI} *}
theorem FalseD [resolve]: "\<not>False" by simp
lemma exists_triv_eq [resolve]: "\<exists>x. x = x" by auto

section \<open>If and only iff\<close>

setup {* add_gen_prfstep ("iff_intro1",
  [WithGoal @{term_pat "?A \<longleftrightarrow> ?B"}, CreateCase @{term_pat "?A::o"}, WithScore 25]) *}
theorem iff_goal:
  "\<not>(A \<longleftrightarrow> B) \<Longrightarrow> A \<Longrightarrow> \<not>B" "\<not>(A \<longleftrightarrow> B) \<Longrightarrow> B \<Longrightarrow> \<not>A"
  "\<not>(A \<longleftrightarrow> B) \<Longrightarrow> \<not>A \<Longrightarrow> B" "\<not>(A \<longleftrightarrow> B) \<Longrightarrow> \<not>B \<Longrightarrow> A"
  "\<not>(\<not>A \<longleftrightarrow> B) \<Longrightarrow> A \<Longrightarrow> B" "\<not>(A \<longleftrightarrow> \<not>B) \<Longrightarrow> B \<Longrightarrow> A" by auto
setup {* fold (fn th => add_forward_prfstep_cond th [with_score 1]) @{thms iff_goal} *}

section \<open>Unique existence\<close>

setup {* add_rewrite_rule @{thm ex1_def} *}

(* To show \<exists>!x. P(x), first show \<exists>x. P(x), then name a variable x satisfying P.
   Finally show \<forall>y. P(y) \<longrightarrow> x = y. *)
setup {* add_gen_prfstep ("ex1_case",
  [WithGoal @{term_pat "\<exists>!x. ?P(x)"}, CreateConcl @{term_pat "\<exists>x. ?P(x)"}]) *}
setup {* add_backward2_prfstep @{thm ex_ex1I} *}
theorem ex_ex1I' [backward1]:
  "(\<forall>y. P(y) \<longrightarrow> x = y) \<Longrightarrow> P(x) \<Longrightarrow> \<exists>!x. P(x)" by auto
theorem ex_ex1D [forward]:
  "\<exists>!x. P(x) \<Longrightarrow> \<exists>x. P(x)"
  "\<exists>!x. P(x) \<Longrightarrow> P(x) \<Longrightarrow> \<forall>y. P(y) \<longrightarrow> y = x" by auto
setup {* del_prfstep_thm @{thm ex1_def} *}

section \<open>Let\<close>

setup {* Normalizer.add_rewr_normalizer ("rewr_let", @{thm Let_def}) *}

end
