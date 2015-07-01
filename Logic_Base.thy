theory Logic_Base
imports Main
begin

definition simp_eq :: "['a, 'a] \<Rightarrow> bool" (infix "simp=" 1) where
  "simp_eq \<equiv> op ="
theorem simp_eq_rewr: "(x simp= y) \<equiv> (x = y)" by (simp add: simp_eq_def)

theorem contra1: "A \<Longrightarrow> (\<not>A \<Longrightarrow> False)" by simp
theorem contra2: "(\<not>A \<Longrightarrow> False) \<Longrightarrow> A" by blast
theorem contra3: "\<not>A \<Longrightarrow> (A \<Longrightarrow> False)" by simp
theorem contra4: "(A \<Longrightarrow> False) \<Longrightarrow> \<not>A" by blast
ML {*
  val contra_eq1_th = Thm.equal_intr @{thm contra1} @{thm contra2}
  val contra_eq2_th = Thm.equal_intr @{thm contra3} @{thm contra4}
*}

theorem or_intro1: "\<not> (P \<or> Q) \<Longrightarrow> \<not> P" by simp
theorem or_intro2: "\<not> (P \<or> Q) \<Longrightarrow> \<not> Q" by simp
theorem exE': "(\<And>x. P x \<Longrightarrow> False) \<Longrightarrow> \<exists>x. P x \<Longrightarrow> False" by auto

ML {* val use_vardef_th = @{thm HOL.simp_thms(42)} *}

end
