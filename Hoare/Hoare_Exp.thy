(* Expressions as functions and relations, following chapter Imp in
   "Software Foundations". *)

theory Hoare_Exp
imports "../Auto2"
begin

datatype aexp =
  ANum nat
| APlus aexp aexp
| AMinus aexp aexp
| AMult aexp aexp

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
setup {* add_eval_fun_prfsteps @{thms aeval.simps} *}

theorem test_aeval1: "aeval (APlus (ANum 2) (ANum 2)) = 4" by auto2

fun beval :: "bexp \<Rightarrow> bool" where
  "beval BTrue = True"
| "beval BFalse = False"
| "beval (BEq a1 a2) = (aeval a1 = aeval a2)"
| "beval (BLe a1 a2) = (aeval a1 \<le> aeval a2)"
| "beval (BNot b) = (\<not> beval b)"
| "beval (BAnd b1 b2) = (beval b1 \<and> beval b2)"
setup {* add_eval_fun_prfsteps' @{thms beval.simps} (@{thms aeval.simps} @ @{thms beval.simps}) *}

theorem test_beval1: "beval (BEq (ANum 2) (ANum 3)) = False" by auto2

inductive aevalR :: "aexp \<Rightarrow> nat \<Rightarrow> bool" (infix "\<Down>" 50) where
  "(ANum n) \<Down> n"
| "e1 \<Down> n1 \<Longrightarrow> e2 \<Down> n2 \<Longrightarrow> (APlus e1 e2) \<Down> (n1 + n2)"
| "e1 \<Down> n1 \<Longrightarrow> e2 \<Down> n2 \<Longrightarrow> (AMinus e1 e2) \<Down> (n1 - n2)"
| "e1 \<Down> n1 \<Longrightarrow> e2 \<Down> n2 \<Longrightarrow> (AMult e1 e2) \<Down> (n1 * n2)"
setup {* add_resolve_prfstep @{thm aevalR.intros(1)} *}
setup {* fold add_backward2_prfstep
  [@{thm aevalR.intros(2)}, @{thm aevalR.intros(3)}, @{thm aevalR.intros(4)}] *}
setup {* add_prfstep_prop_induction @{thm aevalR.induct} *}

inductive bevalR :: "bexp \<Rightarrow> bool \<Rightarrow> bool" where
  "bevalR BTrue True"
| "bevalR BFalse False"
| "a1 \<Down> n1 \<Longrightarrow> a2 \<Down> n2 \<Longrightarrow> bevalR (BEq a1 a2) (n1 = n2)"
| "a1 \<Down> n1 \<Longrightarrow> a2 \<Down> n2 \<Longrightarrow> bevalR (BLe a1 a2) (n1 \<le> n2)"
| "bevalR b v \<Longrightarrow> bevalR (BNot b) (\<not> v)"
| "bevalR b1 v1 \<Longrightarrow> bevalR b2 v2 \<Longrightarrow> bevalR (BAnd b1 b2) (v1 \<and> v2)"
theorem bevalR_intros1': "v \<Longrightarrow> bevalR BTrue v" by (simp add: bevalR.intros(1))
theorem bevalR_intros2': "\<not>v \<Longrightarrow> bevalR BFalse v" by (simp add: bevalR.intros(2))
setup {* fold add_backward_prfstep [@{thm bevalR_intros1'}, @{thm bevalR_intros2'}, @{thm bevalR.intros(5)}] *}
setup {* fold add_backward2_prfstep [@{thm bevalR.intros(3)}, @{thm bevalR.intros(4)}, @{thm bevalR.intros(6)}] *}
setup {* add_prfstep_prop_induction @{thm bevalR.induct} *}

setup {* add_prfstep_var_induction @{thm aexp.induct} *}
setup {* add_prfstep_var_induction @{thm bexp.induct} *}

(* Equivalence of definitions. *)
theorem aeval_iff_aevalR [rewrite]: "a \<Down> n \<longleftrightarrow> aeval a = n"
  by (tactic {* auto2s_tac @{context}
    (HAVE "\<forall>a' n'. a' \<Down> n' \<longrightarrow> aeval a' = n'" WITH PROP_INDUCT ("a' \<Down> n'", []) THEN
     HAVE "\<forall>a' n'. aeval a' = n' \<longrightarrow> a' \<Down> n'" WITH VAR_INDUCT ("a'", [Arbitrary "n'"])) *})
theorem aevalR_triv: "a \<Down> aeval a" by auto2
setup {* add_forward_prfstep_cond @{thm aevalR_triv} [with_term "aeval ?a"] *}
theorem test_aevalR1: "(APlus (ANum 2) (ANum 2)) \<Down> 4" by auto2

theorem beval_iff_bevalR [rewrite]: "bevalR b v \<longleftrightarrow> beval b = v"
  by (tactic {* auto2s_tac @{context}
    (HAVE "\<forall>b' v'. bevalR b' v' \<longrightarrow> beval b' = v'" WITH PROP_INDUCT ("bevalR b' v'", []) THEN
     HAVE "\<forall>b' v'. beval b' = v' \<longrightarrow> bevalR b' v'" WITH VAR_INDUCT ("b'", [Arbitrary "v'"])) *})
theorem bevalR_triv: "bevalR b (beval b)" by auto2
theorem test_bevalR1: "bevalR (BEq (ANum 2) (ANum 3)) False" by auto2

end
