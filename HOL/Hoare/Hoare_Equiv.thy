(* Equivalence of commands, following chapter Equiv in "Software
   Foundations". *)

theory Hoare_Equiv
imports Hoare_States
begin

definition aequiv :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" where
  "aequiv a1 a2 = (\<forall>st. aeval st a1 = aeval st a2)"

definition bequiv :: "bexp \<Rightarrow> bexp \<Rightarrow> bool" where
  "bequiv b1 b2 = (\<forall>st. beval st b1 = beval st b2)"

definition cequiv :: "com \<Rightarrow> com \<Rightarrow> bool" where
  "cequiv c1 c2 = (\<forall>st st'. ceval c1 st st' \<longleftrightarrow> ceval c2 st st')"

setup {* fold add_rewrite_rule [@{thm aequiv_def}, @{thm bequiv_def}, @{thm cequiv_def}] *}
theorem aequiv_example: "aequiv (AMinus (AId X) (AId X)) (ANum 0)" by auto2
theorem bequiv_example: "bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue" by auto2

theorem skip_left: "cequiv (SKIP; c) c" by auto2
theorem skip_right: "cequiv (c; SKIP) c" by auto2
theorem IF_true_simple: "cequiv (IF BTrue THEN c1 ELSE c2 FI) c1" by auto2
theorem IF_true: "bequiv b BTrue \<Longrightarrow> cequiv (IF b THEN c1 ELSE c2 FI) c1" by auto2
theorem IF_false: "bequiv b BFalse \<Longrightarrow> cequiv (IF b THEN c1 ELSE c2 FI) c2" by auto2
theorem swap_if_branches: "cequiv (IF b THEN e1 ELSE e2 FI)
                                  (IF BNot b THEN e2 ELSE e1 FI)" by auto2

theorem WHILE_false: "bequiv b BFalse \<Longrightarrow> cequiv (WHILE b DO c OD) SKIP" by auto2
theorem seq_assoc: "cequiv ((c1;c2);c3) (c1;(c2;c3))" by auto2

(* Using functional equivalence. *)
theorem identity_assignment: "cequiv (X := AId X) SKIP" by auto2
theorem assign_equiv: "aequiv (AId X) e \<Longrightarrow> cequiv (X := e) SKIP" by auto2

(* Behavioral equivalence is an equivalence. *)
theorem refl_aequiv: "aequiv a a" by auto2
theorem sym_aequiv: "aequiv a1 a2 \<Longrightarrow> aequiv a2 a1" by auto2
theorem trans_aequiv: "aequiv a1 a2 \<Longrightarrow> aequiv a2 a3 \<Longrightarrow> aequiv a1 a3" by auto2
theorem refl_bequiv: "bequiv b b" by auto2
theorem sym_bequiv [backward]: "bequiv b1 b2 \<Longrightarrow> bequiv b2 b1" by auto2
theorem trans_bequiv: "bequiv b1 b2 \<Longrightarrow> bequiv b2 b3 \<Longrightarrow> bequiv b1 b3" by auto2
theorem refl_cequiv: "cequiv c c" by auto2
theorem sym_cequiv [backward]: "cequiv c1 c2 \<Longrightarrow> cequiv c2 c1" by auto2
theorem trans_equiv: "cequiv c1 c2 \<Longrightarrow> cequiv c2 c3 \<Longrightarrow> cequiv c1 c3" by auto2

(* Behavior equivalence is a congruence. *)
theorem assign_cong: "aequiv a a' \<Longrightarrow> cequiv (x := a) (x := a')" by auto2
theorem seq_cong: "cequiv c1 c1' \<Longrightarrow> cequiv c2 c2' \<Longrightarrow> cequiv (c1;c2) (c1';c2')" by auto2
theorem if_cong: "bequiv b b' \<Longrightarrow> cequiv c1 c1' \<Longrightarrow> cequiv c2 c2' \<Longrightarrow>
  cequiv (IF b THEN c1 ELSE c2 FI) (IF b' THEN c1' ELSE c2' FI)" by auto2

(* Prove lemma by induction separately *)
theorem while_cong1 [backward1]:
  "bequiv b b' \<Longrightarrow> cequiv c c' \<Longrightarrow> ceval (WHILE b DO c OD) st st' \<Longrightarrow> ceval (WHILE b' DO c' OD) st st'"
  by (tactic {* auto2s_tac @{context} (
    LET "v = WHILE b DO c OD" THEN
    PROP_INDUCT ("ceval v st st'", "v = WHILE b DO c OD \<longrightarrow> ceval (WHILE b' DO c' OD) st st'")) *})

(* This lemma is then used twice in the proof below *)
theorem while_cong: "bequiv b b' \<Longrightarrow> cequiv c c' \<Longrightarrow> cequiv (WHILE b DO c OD) (WHILE b' DO c' OD)" by auto2
setup {* del_prfstep_thm @{thm while_cong1} *}

end
