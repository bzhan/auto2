(* Theorems in logic needed for FOL. *)

theory FOL_Base
imports FOL
begin

section \<open>Declare type of sets\<close>

declare [[eta_contract = false]]

(* Type of sets *)
typedecl i
instance i :: "term" ..

(* Membership relation *)
axiomatization mem :: "[i, i] \<Rightarrow> o"  (infixl "\<in>" 50)

(* Bounded quantifiers *)
definition Ball :: "[i, i \<Rightarrow> o] \<Rightarrow> o" where
  "Ball(A, P) \<longleftrightarrow> (\<forall>x. x\<in>A \<longrightarrow> P(x))"

definition Bex :: "[i, i \<Rightarrow> o] \<Rightarrow> o" where
  "Bex(A, P) \<longleftrightarrow> (\<exists>x. x\<in>A \<and> P(x))"

syntax
  "_Ball" :: "[pttrn, i, o] \<Rightarrow> o"  ("(3\<forall>_\<in>_./ _)" 10)
  "_Bex" :: "[pttrn, i, o] \<Rightarrow> o"  ("(3\<exists>_\<in>_./ _)" 10)
translations
  "\<forall>x\<in>A. P" \<rightleftharpoons> "CONST Ball(A, \<lambda>x. P)"
  "\<exists>x\<in>A. P" \<rightleftharpoons> "CONST Bex(A, \<lambda>x. P)"

abbreviation not_mem :: "[i, i] \<Rightarrow> o"  (infixl "\<notin>" 50) where
  "x \<notin> y \<equiv> \<not> (x \<in> y)"

section \<open>Theorems in logic used in auto2\<close>

theorem to_contra_form: "Trueprop (A) \<equiv> (\<not>A \<Longrightarrow> False)" by (rule equal_intr_rule) auto
theorem to_contra_form': "Trueprop (\<not>A) \<equiv> (A \<Longrightarrow> False)" by (rule equal_intr_rule) auto

theorem contra_triv: "\<not>A \<Longrightarrow> A \<Longrightarrow> False" by simp
theorem or_intro1: "\<not> (P \<or> Q) \<Longrightarrow> \<not> P" by simp
theorem or_intro2: "\<not> (P \<or> Q) \<Longrightarrow> \<not> Q" by simp
theorem not_imp: "\<not>(P \<longrightarrow> Q) \<longleftrightarrow> P \<and> \<not>Q" by auto
theorem exE': "(\<And>x. P(x) \<Longrightarrow> Q) \<Longrightarrow> \<exists>x. P(x) \<Longrightarrow> Q" by auto
theorem eq_True: "A \<Longrightarrow> A \<longleftrightarrow> True" by simp
theorem eq_True_inv: "A \<longleftrightarrow> True \<Longrightarrow> A" by simp
theorem eq_False: "\<not>A \<Longrightarrow> A \<longleftrightarrow> False" by simp
theorem eq_False': "A \<Longrightarrow> \<not>A \<longleftrightarrow> False" by simp
theorem disj_True1: "(True \<or> A) \<longleftrightarrow> True" by simp
theorem disj_True2: "(A \<or> True) \<longleftrightarrow> True" by simp
theorem use_vardef: "(\<forall>x. x = t \<longrightarrow> P(x)) \<longleftrightarrow> P(t)" by simp
theorem ex_vardef: "\<exists>x. x = a" by simp

theorem obj_sym: "Trueprop (t = s) \<equiv> Trueprop (s = t)" by (rule equal_intr_rule) auto
theorem obj_sym_iff: "Trueprop (t \<longleftrightarrow> s) \<equiv> Trueprop (s \<longleftrightarrow> t)" by (rule equal_intr_rule) auto
theorem to_meta_eq: "Trueprop (t = s) \<equiv> (t \<equiv> s)" by (rule equal_intr_rule) auto
theorem to_meta_eq_iff: "Trueprop (t \<longleftrightarrow> s) \<equiv> (t \<equiv> s)" by (rule equal_intr_rule) auto

theorem inv_backward: "P \<longleftrightarrow> Q \<Longrightarrow> \<not>P \<Longrightarrow> \<not>Q" by simp
theorem backward_conv: "(A \<Longrightarrow> B) \<equiv> (\<not>B \<Longrightarrow> \<not>A)" by (rule equal_intr_rule) auto
theorem backward1_conv: "(A \<Longrightarrow> B \<Longrightarrow> C) \<equiv> (\<not>C \<Longrightarrow> B \<Longrightarrow> \<not>A)" by (rule equal_intr_rule) auto
theorem backward2_conv: "(A \<Longrightarrow> B \<Longrightarrow> C) \<equiv> (\<not>C \<Longrightarrow> A \<Longrightarrow> \<not>B)" by (rule equal_intr_rule) auto
theorem resolve_conv: "(A \<Longrightarrow> B) \<equiv> (\<not>B \<Longrightarrow> A \<Longrightarrow> False)" by (rule equal_intr_rule) auto

(* Quantifiers: swapping out of ALL or EX *)
theorem swap_ex_conj: "(P \<and> (\<exists>x. Q(x))) \<longleftrightarrow> (\<exists>x. P \<and> Q(x))" by auto
theorem swap_all_implies: "(P \<longrightarrow> (\<forall>x. Q(x))) \<longleftrightarrow> (\<forall>x. P \<longrightarrow> Q(x))" by auto

(* Use these instead of original versions to keep names in abstractions. *)
theorem Bex_def': "(\<exists>x\<in>S. P(x)) \<longleftrightarrow> (\<exists>x. x \<in> S \<and> P(x))" using Bex_def by auto
theorem Ball_def': "(\<forall>x\<in>S. P(x)) \<longleftrightarrow> (\<forall>x. x \<in> S \<longrightarrow> P(x))" using Ball_def by auto

(* Taking conjunction of assumptions *)
theorem atomize_conjL2: "(A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D) \<equiv> (A \<and> B \<Longrightarrow> C \<Longrightarrow> D)" by (rule equal_intr_rule) auto

(* Other rules *)
theorem imp_conv_disj: "(P \<longrightarrow> Q) \<longleftrightarrow> (\<not>P \<or> Q)" by auto
theorem not_ex: "\<not>(\<exists>x. P(x)) \<longleftrightarrow> (\<forall>x. \<not>P(x))" by simp
theorem not_all: "\<not>(\<forall>x. P(x)) \<longleftrightarrow> (\<exists>x. \<not>P(x))" by simp

(* AC for conj and disj *)
theorem conj_assoc: "(P \<and> Q) \<and> R \<longleftrightarrow> P \<and> Q \<and> R" by simp
theorem conj_unitL: "True \<and> A \<longleftrightarrow> A" by simp
theorem disj_assoc: "(P \<or> Q) \<or> R \<longleftrightarrow> P \<or> Q \<or> R" by simp
theorem disj_unitL: "False \<or> A \<longleftrightarrow> A" by simp

end
