(* Setup for proof steps related to logic. *)

theory Logic_FOL
imports Auto2_FOL
begin

section \<open>Trivial contradictions\<close>

setup {* add_resolve_prfstep @{thm refl} *}
setup {* add_forward_prfstep @{thm contra_triv} *}
setup {* add_resolve_prfstep @{thm TrueI} *}
setup {* add_forward_prfstep_cond @{thm TrueI} [with_term "True"] *}
theorem FalseD [resolve]: "\<not>False" by simp
setup {* add_forward_prfstep_cond @{thm FalseD} [with_term "False"] *}

section \<open>If and only iff\<close>

setup {* add_gen_prfstep ("iff_intro1",
  [WithGoal @{term_pat "?A \<longleftrightarrow> ?B"}, CreateCase @{term_pat "?A::o"}]) *}
setup {* add_fixed_sc ("iff_intro1", 25) *}  (* includes the cost of creating a case. *)
theorem iff_goal [forward]:
  "\<not>(A \<longleftrightarrow> B) \<Longrightarrow> A \<Longrightarrow> \<not>B" "\<not>(A \<longleftrightarrow> B) \<Longrightarrow> B \<Longrightarrow> \<not>A"
  "\<not>(A \<longleftrightarrow> B) \<Longrightarrow> \<not>A \<Longrightarrow> B" "\<not>(A \<longleftrightarrow> B) \<Longrightarrow> \<not>B \<Longrightarrow> A"
  "\<not>(\<not>A \<longleftrightarrow> B) \<Longrightarrow> A \<Longrightarrow> B" "\<not>(A \<longleftrightarrow> \<not>B) \<Longrightarrow> B \<Longrightarrow> A" by auto
setup {* fold add_fixed_sc (map (rpair 1) [
  "Logic_FOL.iff_goal_1", "Logic_FOL.iff_goal_3",
  "Logic_FOL.iff_goal_2", "Logic_FOL.iff_goal_4",
  "Logic_FOL.iff_goal_5", "Logic_FOL.iff_goal_6"]) *}

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

section \<open>Signature of meta-functions\<close>

definition unary_fun :: "i \<Rightarrow> [i \<Rightarrow> i] \<Rightarrow> o" where [rewrite]:
  "unary_fun(S,f) \<longleftrightarrow> (\<forall>x\<in>S. f(x) \<in> S)"

lemma unary_funD [typing]: "unary_fun(S,f) \<Longrightarrow> x \<in> S \<Longrightarrow> f(x) \<in> S" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm unary_fun_def} *}

definition binary_fun :: "i \<Rightarrow> [i \<Rightarrow> i \<Rightarrow> i] \<Rightarrow> o" where [rewrite]:
  "binary_fun(S,f) \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. f(x,y) \<in> S)"

lemma binary_funD [typing]: "binary_fun(S,f) \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> f(x,y) \<in> S" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm binary_fun_def} *}

end
