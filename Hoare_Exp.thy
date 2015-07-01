theory Hoare_Exp
imports Auto2
begin

datatype aexp =
  ANum nat
| APlus aexp aexp
| AMinus aexp aexp
| AMult aexp aexp

thm aexp.induct

datatype bexp =
  BTrue
| BFalse
| BEq aexp aexp
| BLe aexp aexp
| BNot bexp
| BAnd bexp bexp

fun aeval :: "aexp \<Rightarrow> nat" where
  "aeval (ANum n) = n"
| "aeval (APlus m n) = aeval m + aeval n"
| "aeval (AMinus m n) = aeval m - aeval n"
| "aeval (AMult m n) = aeval m * aeval n"
setup {* fold add_simp_rule @{thms aeval.simps} *}

theorem test_aeval1: "aeval (APlus (ANum 2) (ANum 2)) = 4" by auto2

fun beval :: "bexp \<Rightarrow> bool" where
  "beval BTrue = True"
| "beval BFalse = False"
| "beval (BEq a1 a2) = (aeval a1 = aeval a2)"
| "beval (BLe a1 a2) = (aeval a1 \<le> aeval a2)"
| "beval (BNot b) = (\<not> beval b)"
| "beval (BAnd b1 b2) = (beval b1 \<and> beval b2)"
setup {* fold add_simp_rule @{thms beval.simps} *}

theorem test_beval1: "beval (BEq (ANum 2) (ANum 3)) = False" by auto2

inductive aevalR :: "aexp \<Rightarrow> nat \<Rightarrow> bool" (infix "\<Down>" 50) where
  "(ANum n) \<Down> n"
| "e1 \<Down> n1 \<Longrightarrow> e2 \<Down> n2 \<Longrightarrow> (APlus e1 e2) \<Down> (n1 + n2)"
| "e1 \<Down> n1 \<Longrightarrow> e2 \<Down> n2 \<Longrightarrow> (AMinus e1 e2) \<Down> (n1 - n2)"
| "e1 \<Down> n1 \<Longrightarrow> e2 \<Down> n2 \<Longrightarrow> (AMult e1 e2) \<Down> (n1 * n2)"
setup {* add_known_fact @{thm aevalR.intros(1)} *}
setup {* fold add_backward2_prfstep
  [@{thm aevalR.intros(2)}, @{thm aevalR.intros(3)}, @{thm aevalR.intros(4)}] *}
setup {* add_prfstep_prop_induction @{thm aevalR.induct} *}

theorem test_aevalR1: "(APlus (ANum 2) (ANum 2)) \<Down> 4"
by (metis aeval.simps(1) aeval.simps(2) aevalR.intros(1) aevalR.intros(2) test_aeval1)

inductive bevalR :: "bexp \<Rightarrow> bool \<Rightarrow> bool" where
  "bevalR BTrue True"
| "bevalR BFalse False"
| "a1 \<Down> n1 \<Longrightarrow> a2 \<Down> n2 \<Longrightarrow> bevalR (BEq a1 a2) (n1 = n2)"
| "a1 \<Down> n1 \<Longrightarrow> a2 \<Down> n2 \<Longrightarrow> bevalR (BLe a1 a2) (n1 \<le> n2)"
| "bevalR b v \<Longrightarrow> bevalR (BNot b) (\<not> v)"
| "bevalR b1 v1 \<Longrightarrow> bevalR b2 v2 \<Longrightarrow> bevalR (BAnd b1 b2) (v1 \<and> v2)"
theorem bevalR_intros1': "v \<Longrightarrow> bevalR BTrue v" by (simp add: bevalR.intros(1))
theorem bevalR_intros2': "\<not>v \<Longrightarrow> bevalR BFalse v" by (simp add: bevalR.intros(2))
setup {* add_prfstep_prop_induction @{thm bevalR.induct} *}
setup {* fold add_backward_prfstep [@{thm bevalR_intros1'}, @{thm bevalR_intros2'}, @{thm bevalR.intros(5)}] *}
setup {* fold add_backward2_prfstep [@{thm bevalR.intros(3)}, @{thm bevalR.intros(4)}, @{thm bevalR.intros(6)}] *}

theorem test_bevalR1: "bevalR (BEq (ANum 2) (ANum 3)) False"
by (metis (full_types) aevalR.intros(1) bevalR.intros(3) numeral_eq_iff semiring_norm(88))

setup {* add_prfstep_var_induction @{thm aexp.induct} *}
setup {* add_prfstep_var_induction @{thm bexp.induct} *}

(* Equivalence of definitions. *)
theorem aevalR_to_aeval: "a \<Down> n \<Longrightarrow> aeval a = n" by auto2
theorem aeval_to_aevalR: "aeval a = n \<Longrightarrow> a \<Down> n"
  by (tactic {* auto2s_tac @{context} (VAR_INDUCT ("a", [Arbitrary "n"])) *})
theorem aeval_to_aevalR': "a \<Down> aeval a" by (simp add: aeval_to_aevalR)
setup {* add_forward_prfstep @{thm aevalR_to_aeval} *}
setup {* add_forward_prfstep_cond @{thm aeval_to_aevalR'} [with_term "aeval ?a"] *}
theorem aeval_iff_aevalR: "a \<Down> n \<longleftrightarrow> aeval a = n" by auto2

theorem bevalR_to_beval: "bevalR b v \<Longrightarrow> (beval b = v)" by auto2
theorem beval_to_bevalR: "(beval b = v) \<Longrightarrow> bevalR b v"
  by (tactic {* auto2s_tac @{context} (VAR_INDUCT ("b", [Arbitrary "v"])) *})
theorem beval_to_bevalR': "bevalR b (beval b)" by (simp add: beval_to_bevalR)
setup {* add_forward_prfstep @{thm bevalR_to_beval} *}
setup {* add_forward_prfstep_cond @{thm beval_to_bevalR'} [with_term "beval ?b"] *}
theorem beval_iff_bevalR: "bevalR b v \<longleftrightarrow> (beval b = v)" by auto2

end
