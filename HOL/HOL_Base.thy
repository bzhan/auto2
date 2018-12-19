(*
  File: HOL_Base.thy
  Author: Bohua Zhan

  Extra theorems in logic used by auto2.
*)

theory HOL_Base
  imports Main
begin

lemma to_contra_form: "Trueprop A \<equiv> (\<not>A \<Longrightarrow> False)" by (rule equal_intr_rule) auto
lemma to_contra_form': "Trueprop (\<not>A) \<equiv> (A \<Longrightarrow> False)" by (rule equal_intr_rule) auto

lemma contra_triv: "\<not>A \<Longrightarrow> A \<Longrightarrow> False" by simp
lemma or_intro1: "\<not> (P \<or> Q) \<Longrightarrow> \<not> P" by simp
lemma or_intro2: "\<not> (P \<or> Q) \<Longrightarrow> \<not> Q" by simp
lemma or_cancel1: "\<not>Q \<Longrightarrow> (P \<or> Q) = P" by auto
lemma or_cancel2: "\<not>P \<Longrightarrow> (P \<or> Q) = Q" by auto
lemma exE': "(\<And>x. P x \<Longrightarrow> Q) \<Longrightarrow> \<exists>x. P x \<Longrightarrow> Q" by auto
lemma nn_create: "A \<Longrightarrow> \<not>\<not>A" by auto
lemma iffD: "A \<longleftrightarrow> B \<Longrightarrow> (A \<longrightarrow> B) \<and> (B \<longrightarrow> A)" by auto

lemma obj_sym: "Trueprop (t = s) \<equiv> Trueprop (s = t)" by (rule equal_intr_rule) auto
lemma to_meta_eq: "Trueprop (t = s) \<equiv> (t \<equiv> s)" by (rule equal_intr_rule) auto

lemma inv_backward: "A \<longleftrightarrow> B \<Longrightarrow> \<not>A \<Longrightarrow> \<not>B" by auto
lemma backward_conv: "(A \<Longrightarrow> B) \<equiv> (\<not>B \<Longrightarrow> \<not>A)" by (rule equal_intr_rule) auto
lemma backward1_conv: "(A \<Longrightarrow> B \<Longrightarrow> C) \<equiv> (\<not>C \<Longrightarrow> B \<Longrightarrow> \<not>A)" by (rule equal_intr_rule) auto
lemma backward2_conv: "(A \<Longrightarrow> B \<Longrightarrow> C) \<equiv> (\<not>C \<Longrightarrow> A \<Longrightarrow> \<not>B)" by (rule equal_intr_rule) auto
lemma resolve_conv: "(A \<Longrightarrow> B) \<equiv> (\<not>B \<Longrightarrow> A \<Longrightarrow> False)" by (rule equal_intr_rule) auto

text \<open>Quantifiers: swapping out of ALL or EX.\<close>
lemma swap_ex_conj: "(P \<and> (\<exists>x. Q x)) \<longleftrightarrow> (\<exists>x. P \<and> Q x)" by auto
lemma swap_all_disj: "(P \<or> (\<forall>x. Q x)) \<longleftrightarrow> (\<forall>x. P \<or> Q x)" by auto

text \<open>Use these instead of original versions to keep names in abstractions.\<close>
lemma Bex_def': "(\<exists>x\<in>S. P x) \<longleftrightarrow> (\<exists>x. x \<in> S \<and> P x)" by auto
lemma Ball_def': "(\<forall>x\<in>S. P x) \<longleftrightarrow> (\<forall>x. x \<in> S \<longrightarrow> P x)" by auto

text \<open>Taking conjunction of assumptions.\<close>
lemma atomize_conjL: "(A \<Longrightarrow> B \<Longrightarrow> PROP C) \<equiv> (A \<and> B \<Longrightarrow> PROP C)" by (rule equal_intr_rule) auto

end
