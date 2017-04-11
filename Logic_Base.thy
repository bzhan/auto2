(* Theorems in logic used in the auto2 tactic. *)

theory Logic_Base
imports Main Rat
begin

theorem to_contra_form: "Trueprop A \<equiv> (\<not>A \<Longrightarrow> False)" by (rule equal_intr_rule) auto
theorem to_contra_form': "Trueprop (\<not>A) \<equiv> (A \<Longrightarrow> False)" by (rule equal_intr_rule) auto

theorem contra_triv: "\<not>A \<Longrightarrow> A \<Longrightarrow> False" by simp
theorem or_intro1: "\<not> (P \<or> Q) \<Longrightarrow> \<not> P" by simp
theorem or_intro2: "\<not> (P \<or> Q) \<Longrightarrow> \<not> Q" by simp
theorem exE': "(\<And>x. P x \<Longrightarrow> Q) \<Longrightarrow> \<exists>x. P x \<Longrightarrow> Q" by auto
theorem eq_False: "\<not>A \<Longrightarrow> A = False" by simp
theorem eq_False': "A \<Longrightarrow> (\<not>A) = False" by simp

theorem obj_sym: "Trueprop (t = s) \<equiv> Trueprop (s = t)" by (rule equal_intr_rule) auto
theorem to_meta_eq: "Trueprop (t = s) \<equiv> (t \<equiv> s)" by (rule equal_intr_rule) auto

theorem inv_backward: "A \<longleftrightarrow> B \<Longrightarrow> \<not>A \<Longrightarrow> \<not>B" by auto
theorem backward_conv: "(A \<Longrightarrow> B) \<equiv> (\<not>B \<Longrightarrow> \<not>A)" by (rule equal_intr_rule) auto
theorem backward1_conv: "(A \<Longrightarrow> B \<Longrightarrow> C) \<equiv> (\<not>C \<Longrightarrow> B \<Longrightarrow> \<not>A)" by (rule equal_intr_rule) auto
theorem backward2_conv: "(A \<Longrightarrow> B \<Longrightarrow> C) \<equiv> (\<not>C \<Longrightarrow> A \<Longrightarrow> \<not>B)" by (rule equal_intr_rule) auto
theorem resolve_conv: "(A \<Longrightarrow> B) \<equiv> (\<not>B \<Longrightarrow> A \<Longrightarrow> False)" by (rule equal_intr_rule) auto

(* Quantifiers: swapping out of ALL or EX *)
theorem swap_ex_conj: "(P \<and> (\<exists>x. Q x)) \<longleftrightarrow> (\<exists>x. P \<and> Q x)" by auto
theorem swap_all_implies: "(P \<longrightarrow> (\<forall>x. Q x)) \<longleftrightarrow> (\<forall>x. P \<longrightarrow> Q x)" by auto

(* Use these instead of original versions to keep names in abstractions. *)
theorem Bex_def': "(\<exists>x\<in>S. P x) \<longleftrightarrow> (\<exists>x. x \<in> S \<and> P x)" by auto
theorem Ball_def': "(\<forall>x\<in>S. P x) \<longleftrightarrow> (\<forall>x. x \<in> S \<longrightarrow> P x)" by auto

(* Taking conjunction of assumptions *)
theorem atomize_conjL2: "(A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D) \<equiv> (A \<and> B \<Longrightarrow> C \<Longrightarrow> D)" by (rule equal_intr_rule) auto

end
