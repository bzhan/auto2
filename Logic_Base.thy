theory Logic_Base
imports Main
begin

theorem to_contra_form: "Trueprop A \<equiv> (\<not>A \<Longrightarrow> False)" by (rule equal_intr_rule) auto
theorem to_contra_form': "Trueprop (\<not>A) \<equiv> (A \<Longrightarrow> False)" by (rule equal_intr_rule) auto

theorem contra_triv: "\<not>A \<Longrightarrow> A \<Longrightarrow> False" by simp
theorem or_intro1: "\<not> (P \<or> Q) \<Longrightarrow> \<not> P" by simp
theorem or_intro2: "\<not> (P \<or> Q) \<Longrightarrow> \<not> Q" by simp
theorem exE': "(\<And>x. P x \<Longrightarrow> Q) \<Longrightarrow> \<exists>x. P x \<Longrightarrow> Q" by auto
theorem eq_False': "((\<not>A) = False) = A" by simp

theorem use_vardef: "(\<forall>x. x = t \<longrightarrow> P x) = P t" by simp

theorem obj_sym: "Trueprop (t = s) \<equiv> Trueprop (s = t)" by (rule equal_intr_rule) auto
theorem meta_sym: "(y \<equiv> x) \<equiv> (x \<equiv> y)" by (rule equal_intr_rule) auto
theorem to_meta_eq: "Trueprop (t = s) \<equiv> (t \<equiv> s)" by (rule equal_intr_rule) auto
theorem to_obj_eq: "(t \<equiv> s) \<equiv> Trueprop (t = s)" by (rule equal_intr_rule) auto

theorem backward_conv: "(A \<Longrightarrow> B) \<equiv> (\<not>B \<Longrightarrow> \<not>A)" by (rule equal_intr_rule) auto
theorem backward1_conv: "(A \<Longrightarrow> B \<Longrightarrow> C) \<equiv> (\<not>C \<Longrightarrow> B \<Longrightarrow> \<not>A)" by (rule equal_intr_rule) auto
theorem backward2_conv: "(A \<Longrightarrow> B \<Longrightarrow> C) \<equiv> (\<not>C \<Longrightarrow> A \<Longrightarrow> \<not>B)" by (rule equal_intr_rule) auto
ML {* val nn_cancel_th = @{thm HOL.nnf_simps(6)} *}

end
