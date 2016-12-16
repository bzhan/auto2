(* Sum of two sets *)

theory SetSum
imports Set
begin

section {* Booleans *}

definition succ :: "i \<Rightarrow> i" where succ_def [rewrite]:
  "succ(i) = cons(i, i)"

definition zero ("0") where "0 = \<emptyset>"
definition one ("1") where "1 = succ(\<emptyset>)"

definition bool :: "i" where
  "bool = {0,1}"

(* Conditional on the first argument, which is a boolean. *)
definition cond :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where
  "cond(b,c,d) = (if b = 1 then c else d)"

definition not :: "i \<Rightarrow> i" where
  "not(b) = cond(b,0,1)"

definition "and" :: "i \<Rightarrow> i \<Rightarrow> i"  (infixl "and" 70) where
  "a and b = cond(a,b,0)"

definition "or"  :: "i \<Rightarrow> i \<Rightarrow> i" (infixl "or" 65) where
  "a or b  = cond(a,1,b)"

definition "xor" :: "i \<Rightarrow> i \<Rightarrow> i" (infixl "xor" 65) where
  "a xor b = cond(a,not(b),b)"

setup {* add_rewrite_rule @{thm bool_def} *}
lemma bool_1I [resolve]: "1 \<in> bool" by auto2
lemma bool_0I [resolve]: "0 \<in> bool" by auto2
setup {* add_rewrite_rule @{thm zero_def} *}
setup {* add_rewrite_rule @{thm one_def} *}
lemma one_not_0 [resolve]: "1 \<noteq> 0" by auto2
setup {* del_prfstep_thm @{thm one_def} *}

lemma boolE [forward]: "a \<in> bool \<Longrightarrow> a = 0 \<or> a = 1" by auto2
setup {* del_prfstep_thm @{thm bool_def} *}

setup {* add_rewrite_rule @{thm cond_def} *}
lemma cond_1 [rewrite]: "cond(1,c,d) = c" by auto2
lemma cond_0 [rewrite]: "cond(0,c,d) = d" by auto2
lemma cond_simple_type: "b \<in> bool \<Longrightarrow> c \<in> A \<Longrightarrow> d \<in> A \<Longrightarrow> cond(b,c,d) \<in> A" by auto2
setup {* del_prfstep_thm @{thm cond_def} *}

setup {* add_rewrite_rule @{thm not_def} *}
lemma not_type: "a \<in> bool \<Longrightarrow> not(a) \<in> bool" by auto2

setup {* add_rewrite_rule @{thm and_def} *}
lemma and_type: "a \<in> bool \<Longrightarrow> b \<in> bool \<Longrightarrow> a and b \<in> bool" by auto2

setup {* add_rewrite_rule @{thm or_def} *}
lemma or_type: "a \<in> bool \<Longrightarrow> b \<in> bool \<Longrightarrow> a or b \<in> bool" by auto2

setup {* add_rewrite_rule @{thm xor_def} *}
lemma xor_type: "a \<in> bool \<Longrightarrow> b \<in> bool \<Longrightarrow> a xor b \<in> bool" by auto2

definition bool_of_o :: "o \<Rightarrow> i" where
  "bool_of_o(P) = (if P then 1 else 0)"
setup {* add_rewrite_rule @{thm bool_of_o_def} *}

lemma bool_of_True [rewrite]: "bool_of_o(True) = 1" by auto2
lemma bool_of_False [rewrite]: "bool_of_o(False) = 0" by auto2
lemma bool_of_o_type [resolve]: "bool_of_o(P) \<in> bool" by auto2
lemma bool_of_P_is_1 [rewrite]: "(bool_of_o(P) = 1) \<longleftrightarrow> P" by auto2
lemma bool_of_P_is_0 [rewrite]: "(bool_of_o(P) = 0) \<longleftrightarrow> \<not>P" by auto2

section {* Disjoint sum *}

definition sum :: "i \<Rightarrow> i \<Rightarrow> i" (infixr "+" 65) where
  "A + B = {0} \<times> A \<union> {1} \<times> B"

definition Inl :: "i \<Rightarrow> i" where
  "Inl(a) = \<langle>0,a\<rangle>"

definition Inr :: "i \<Rightarrow> i" where
  "Inr(b) = \<langle>1,b\<rangle>"

definition "case" :: "[i\<Rightarrow>i, i\<Rightarrow>i, i] \<Rightarrow> i" where
  "case(c,d,p) = cond(fst(p), d(snd(p)), c(snd(p)))"

subsection {* Rules for disjoint sums *}

setup {* add_rewrite_rule @{thm sum_def} *}
setup {* add_rewrite_rule @{thm Inl_def} *}
setup {* add_rewrite_rule @{thm Inr_def} *}

lemma Sigma_bool: "Sigma(bool,C) = C(0) + C(1)" by auto2
lemma InlI_type [rewrite]: "Inl(a) \<in> A + B \<longleftrightarrow> a \<in> A" by auto2
lemma InrI_type [rewrite]: "Inr(b) \<in> A + B \<longleftrightarrow> b \<in> B" by auto2

lemma sum_iff [forward]:
  "u \<in> A + B \<Longrightarrow> (\<exists>x\<in>A. u = Inl(x)) \<or> (\<exists>y\<in>B. u = Inr(y))" by auto2

lemma Inl_inj [forward]: "Inl(a) = Inl(b) \<Longrightarrow> a = b" by auto2
lemma Inr_inj [forward]: "Inr(a) = Inr(b) \<Longrightarrow> a = b" by auto2
lemma Inl_Inr_neq [resolve]: "Inl(a) \<noteq> Inr(b)" by auto2
lemma sum_empty: "0 + 0 = 0" by auto2

lemma sum_subset_iff [rewrite]: "A + B \<subseteq> C + D \<longleftrightarrow> A \<subseteq> C \<and> B \<subseteq> D"
  by (tactic {* auto2s_tac @{context}
    (CASE "A + B \<subseteq> C + D" WITH (
      HAVE "\<forall>x\<in>A. x \<in> C" WITH HAVE "Inl(x) \<in> A + B" THEN
      HAVE "\<forall>y\<in>B. y \<in> D" WITH HAVE "Inr(y) \<in> A + B")) *})

lemma sum_equal [forward]: "A + B = C + D \<Longrightarrow> A = C \<and> B = D"
  by (tactic {* auto2s_tac @{context}
    (HAVE "A + B \<subseteq> C + D" THEN HAVE "C + D \<subseteq> A + B") *})

section {* Case *}

setup {* add_rewrite_rule @{thm case_def} *}

lemma case_Inl [rewrite]: "case(c, d, Inl(a)) = c(a)" by auto2
lemma case_Inr [rewrite]: "case(c, d, Inr(b)) = d(b)" by auto2

setup {* del_prfstep_thm @{thm case_def} *}

end
