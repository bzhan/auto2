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

section \<open>Negation\<close>

setup {* add_forward_prfstep_cond @{thm not_sym} [with_filt (not_type_filter "a" boolT)] *}

section \<open>If and only iff\<close>

setup {* add_gen_prfstep ("iff_intro1",
  [WithGoal @{term_pat "?A \<longleftrightarrow> ?B"}, CreateCase @{term_pat "?A::o"}]) *}
setup {* add_fixed_sc ("iff_intro1", 25) *}  (* includes the cost of creating a case. *)
theorem iff_two_dirs [forward]: "\<not>(A \<longleftrightarrow> B) \<Longrightarrow> (A \<longrightarrow> \<not>B) \<and> (\<not>A \<longrightarrow> B)" by auto
setup {* add_fixed_sc ("Logic_FOL.iff_two_dirs", 1) *}

section \<open>Unique existence\<close>

setup {* add_rewrite_rule (to_obj_eq_th @{thm ex1_def}) *}

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

end
