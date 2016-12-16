(* Fixed point theorems *)

theory FixedPt
imports Set
begin

(* h is a function from Pow(D) to itself, satisfying a monotone property. *)
definition bnd_mono :: "i \<Rightarrow> (i \<Rightarrow> i) \<Rightarrow> o" where
  "bnd_mono(D,h) \<longleftrightarrow> (h(D) \<subseteq> D \<and> (\<forall>W X. W \<subseteq> X \<longrightarrow> X \<subseteq> D \<longrightarrow> h(W) \<subseteq> h(X)))"

(* Least fixed point of h. *)
definition lfp :: "i \<Rightarrow> (i \<Rightarrow> i) \<Rightarrow> i" where
  "lfp(D,h) = \<Inter>({X \<in> Pow(D). h(X) \<subseteq> X})"

(* Greatest fixed point of h. *)
definition gfp :: "i \<Rightarrow> (i \<Rightarrow> i) \<Rightarrow> i" where
  "gfp(D,h) = \<Union>({X \<in> Pow(D). X \<subseteq> h(X)})"

section {* Monotone operators *}

setup {* add_rewrite_rule @{thm bnd_mono_def} *}
lemma bnd_monoD1 [forward]: "bnd_mono(D,h) \<Longrightarrow> h(D) \<subseteq> D" by auto2
lemma bnd_monoD2 [backward2]: "bnd_mono(D,h) \<Longrightarrow> W \<subseteq> X \<Longrightarrow> X \<subseteq> D \<Longrightarrow> h(W) \<subseteq> h(X)" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm bnd_mono_def} *}

lemma bnd_mono_subset:
  "bnd_mono(D,h) \<Longrightarrow> X \<subseteq> D \<Longrightarrow> h(X) \<subseteq> D"
  by (tactic {* auto2s_tac @{context} (HAVE "h(X) \<subseteq> h(D)") *})

lemma bnd_mono_Un:
  "bnd_mono(D,h) \<Longrightarrow> A \<subseteq> D \<Longrightarrow> B \<subseteq> D \<Longrightarrow> h(A) \<union> h(B) \<subseteq> h(A \<union> B)" by auto2

section {* Knaster-Tarski Theorem using lfp *}

setup {* add_rewrite_rule @{thm lfp_def} *}

lemma lfp_set_nonempty [backward2]: "h(A) \<subseteq> A \<Longrightarrow> A \<subseteq> D \<Longrightarrow> {X \<in> Pow(D). h(X) \<subseteq> X} \<noteq> \<emptyset>"
  by (tactic {* auto2s_tac @{context} (
    HAVE "A \<in> {X \<in> Pow(D). h(X) \<subseteq> X}") *})

lemma lfp_lowerbound [backward]:
  "h(A) \<subseteq> A \<Longrightarrow> A \<subseteq> D \<Longrightarrow> lfp(D,h) \<subseteq> A" by auto2

lemma lfp_subset [backward]:
  "h(D) \<subseteq> D \<Longrightarrow> lfp(D,h) \<subseteq> D" by auto2

lemma lfp_greatest [backward2]:
  "h(D) \<subseteq> D \<Longrightarrow> \<forall>X. h(X) \<subseteq> X \<longrightarrow> X \<subseteq> D \<longrightarrow> A \<subseteq> X \<Longrightarrow> A \<subseteq> lfp(D,h)" by auto2

lemma lfp_unfold [rewrite]:
  "bnd_mono(D,h) \<Longrightarrow> h(lfp(D,h)) = lfp(D,h)"
  by (tactic {* auto2s_tac @{context} (HAVE "h(lfp(D,h)) \<subseteq> lfp(D,h)") *})

section {* General induction rule for least fixed points *}

lemma induct:
  "bnd_mono(D,h) \<Longrightarrow> a \<in> lfp(D,h) \<Longrightarrow> \<forall>x\<in>h(Collect(lfp(D,h),P)). P(x) \<Longrightarrow> P(a)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "h(Collect(lfp(D,h),P)) \<subseteq> lfp(D,h)") *})

lemma lfp_Int_lowerbound [backward1]:
  "bnd_mono(D,h) \<Longrightarrow> h(D \<inter> A) \<subseteq> A \<Longrightarrow> lfp(D,h) \<subseteq> A" by auto2

lemma lfp_mono:
  "bnd_mono(D,h) \<Longrightarrow> bnd_mono(E,i) \<Longrightarrow> \<forall>X. X \<subseteq> D \<longrightarrow> h(X) \<subseteq> i(X) \<Longrightarrow>
   lfp(D,h) \<subseteq> lfp(E,i)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>X. i(X) \<subseteq> X \<longrightarrow> X \<subseteq> E \<longrightarrow> lfp(D,h) \<subseteq> X" WITH
      (HAVE "h(D \<inter> X) \<subseteq> X" WITH HAVE "h(D \<inter> X) \<subseteq> i(D \<inter> X)")) *})

lemma lfp_cong:
  "\<forall>X. X \<subseteq> D \<longrightarrow> h(X) = h'(X) \<Longrightarrow> lfp(D,h) = lfp(D,h')" by auto2

setup {* del_prfstep_thm @{thm lfp_def} *}

section {* Knaster-Tarski Theorem using gfp *}

setup {* add_rewrite_rule @{thm gfp_def} *}

lemma gfp_upperbound [backward]:
  "A \<subseteq> h(A) \<Longrightarrow> A \<subseteq> D \<Longrightarrow> A \<subseteq> gfp(D,h)" by auto2

lemma gfp_subset [resolve]: "gfp(D,h) \<subseteq> D" by auto2

lemma gfp_least [backward2]:
  "h(D) \<subseteq> D \<Longrightarrow> \<forall>X. X \<subseteq> h(X) \<longrightarrow> X \<subseteq> D \<longrightarrow> X \<subseteq> A \<Longrightarrow> gfp(D,h) \<subseteq> A" by auto2

lemma gfp_unfold [rewrite]:
  "bnd_mono(D,h) \<Longrightarrow> h(gfp(D,h)) = gfp(D,h)"
  by (tactic {* auto2s_tac @{context} (HAVE "gfp(D,h) \<subseteq> h(gfp(D,h))") *})

section {* General induction rule for greatest fixed points *}

lemma weak_coinduct:
  "a \<in> X \<Longrightarrow> X \<subseteq> h(X) \<Longrightarrow> X \<subseteq> D \<Longrightarrow> a \<in> gfp(D,h)" by auto2

lemma coinduct_lemma [backward1]:
  "X \<subseteq> D \<Longrightarrow> bnd_mono(D,h) \<Longrightarrow> X \<subseteq> h(X \<union> gfp(D,h)) \<Longrightarrow> X \<union> gfp(D,h) \<subseteq> h(X \<union> gfp(D,h))" by auto2

lemma coinduct:
  "bnd_mono(D,h) \<Longrightarrow> a \<in> X \<Longrightarrow> X \<subseteq> h(X \<union> gfp(D,h)) \<Longrightarrow> X \<subseteq> D \<Longrightarrow> a \<in> gfp(D,h)" by auto2

lemma gfp_mono:
  "bnd_mono(D,h) \<Longrightarrow> D \<subseteq> E \<Longrightarrow> \<forall>X. X \<subseteq> D \<longrightarrow> h(X) \<subseteq> i(X) \<Longrightarrow> gfp(D,h) \<subseteq> gfp(E,i)" by auto2

setup {* del_prfstep_thm @{thm gfp_def} *}

end
