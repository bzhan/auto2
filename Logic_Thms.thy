theory Logic_Thms
imports Main
begin

thm TrueI
thm conjunct1
thm mp
thm exE
thm HOL.atomize_imp
thm ex_comm

theorem contra1: "A \<Longrightarrow> (\<not>A \<Longrightarrow> False)" by simp
theorem contra2: "(\<not>A \<Longrightarrow> False) \<Longrightarrow> A" by blast
theorem contra3: "\<not>A \<Longrightarrow> (A \<Longrightarrow> False)" by simp
theorem contra4: "(A \<Longrightarrow> False) \<Longrightarrow> \<not>A" by blast
ML {*
  val contra_eq1_th = Thm.equal_intr @{thm contra1} @{thm contra2}
  val contra_eq1_th_sym = contra_eq1_th RS @{thm symmetric}
  val contra_eq2_th = Thm.equal_intr @{thm contra3} @{thm contra4}
  val contra_eq2_th_sym = contra_eq2_th RS @{thm symmetric}
*}

theorem conj_true_neutral: "(True \<and> A) = A" by simp
theorem disj_false_neutral: "(False \<or> A) = A" by simp
theorem and_intro2: "A \<Longrightarrow> \<not>(A \<and> B) \<Longrightarrow> ~ B" by simp
theorem or_elim: "A | B \<Longrightarrow> \<not>A \<Longrightarrow> \<not>B \<Longrightarrow> False" by simp
theorem or_elim': "\<not>A | B \<Longrightarrow> A \<Longrightarrow> B" by simp
theorem imp_triv: "A \<Longrightarrow> A" by simp
theorem iff_intro2A: "A \<longrightarrow> B \<Longrightarrow> \<not>(A = B) \<Longrightarrow> \<not>A" by simp
theorem iff_intro2B: "A \<longrightarrow> B \<Longrightarrow> \<not>(A = B) \<Longrightarrow> B" by simp
theorem imp_introA: "\<not>(A \<longrightarrow> B) \<Longrightarrow> A" by simp
theorem imp_introB: "\<not>(A \<longrightarrow> B) \<Longrightarrow> \<not>B" by simp
theorem eq_triv: "A = A" by simp

theorem forall_resolve: "\<forall>x. P x \<longrightarrow> Q x \<Longrightarrow> P x \<Longrightarrow> Q x" by simp
theorem forall_resolve_opp: "\<forall>x. P x \<longrightarrow> \<not>(Q x) \<Longrightarrow> Q x \<Longrightarrow> \<not>(P x)" by blast
theorem forall_resolve2: "\<forall>x y. P x y \<longrightarrow> Q x y \<Longrightarrow> P x y \<Longrightarrow> Q x y" by blast
theorem exists_intro: "\<not> (\<exists>x. P x \<and> Q x) \<Longrightarrow> P x \<Longrightarrow> \<not> (Q x)" by simp
theorem exists_intro2: "\<not> (\<exists>x y. P x y \<and> Q x y) \<Longrightarrow> P x y \<Longrightarrow> \<not> (Q x y)" by simp
theorem exists_resolve: "\<not> (\<exists>x. P x) \<Longrightarrow> P x \<Longrightarrow> False" by simp
theorem exists_split: "(\<exists>x y. P x \<and> Q y) \<equiv> ((\<exists>x. P x) \<and> (\<exists>y. Q y))" by simp
theorem exists_split': "(\<exists>y x. P x \<and> Q y) \<equiv> ((\<exists>x. P x) \<and> (\<exists>y. Q y))" by simp

theorem if_true: "cond \<Longrightarrow> (if cond then yes else no) = yes" by simp
theorem if_false: "\<not>cond \<Longrightarrow> (if cond then yes else no) = no" by simp
theorem if_false': "cond \<Longrightarrow> (if \<not>cond then yes else no) = no" by simp

end

