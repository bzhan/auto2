theory BigSet
imports Functions
begin

section {* Big union *}

lemma Union_mem_D: "x \<in> A \<Longrightarrow> A \<in> S \<Longrightarrow> x \<in> \<Union>(S)" by auto2

lemma Union_subset_iff: "\<Union>(A) \<subseteq> C \<longleftrightarrow> (\<forall>x\<in>A. x \<subseteq> C)" by auto2

lemma Union_upper: "B \<in> A \<Longrightarrow> B \<subseteq> \<Union>(A)" by auto2

lemma Union_Un_distrib: "\<Union>(A \<union> B) = \<Union>(A) \<union> \<Union>(B)" by auto2

lemma Union_Int_subset: "\<Union>(A \<inter> B) \<subseteq> \<Union>(A) \<inter> \<Union>(B)" by auto2

lemma Union_disjoint: "\<Union>(C) \<inter> A = \<emptyset> \<longleftrightarrow> (\<forall>B\<in>C. B \<inter> A = \<emptyset>)" by auto2

section {* Big intersection *}

lemma Inter_Un_distrib:
  "A \<noteq> \<emptyset> \<Longrightarrow> B \<noteq> \<emptyset> \<Longrightarrow> \<Inter>(A \<union> B) = \<Inter>(A) \<inter> \<Inter>(B)" by auto2

section {* Parametrized union and intersection *}  (* Bourbaki II.4.1 -- II.4.4 *)

lemma UN_surj [rewrite]:
  "surjective(f) \<Longrightarrow> is_function(B) \<Longrightarrow> f \<in> K \<rightarrow> I \<Longrightarrow> (\<Union>x\<in>K. B`(f`x)) = (\<Union>x\<in>I. B`x)"
@proof @have (@rule) "\<forall>y\<in>I. \<exists>x\<in>K. f`x = y" @qed

lemma INT_surj [rewrite]:
  "surjective(f) \<Longrightarrow> is_function(B) \<Longrightarrow> f \<in> K \<rightarrow> I \<Longrightarrow> I \<noteq> \<emptyset> \<Longrightarrow> (\<Inter>x\<in>K. B`(f`x)) = (\<Inter>x\<in>I. B`x)"
@proof @have (@rule) "\<forall>y\<in>I. \<exists>x\<in>K. f`x = y" @qed

lemma UN_image_subset [resolve]:
  "\<forall>x\<in>I. X(x) \<subseteq> Y(x) \<Longrightarrow> (\<Union>x\<in>I. X(x)) \<subseteq> (\<Union>x\<in>I. Y(x))" by auto2

lemma INT_image_subset [backward2]:
  "\<forall>x\<in>I. X(x) \<subseteq> Y(x) \<Longrightarrow> I \<noteq> \<emptyset> \<Longrightarrow> (\<Inter>x\<in>I. X(x)) \<subseteq> (\<Inter>x\<in>I. Y(x))" by auto2

lemma UN_source_subset [backward]:
  "J \<subseteq> I \<Longrightarrow> (\<Union>x\<in>J. X(x)) \<subseteq> (\<Union>x\<in>I. X(x))" by auto2

lemma INT_source_subset [backward2]:
  "J \<subseteq> I \<Longrightarrow> J \<noteq> \<emptyset> \<Longrightarrow> (\<Inter>x\<in>I. X(x)) \<subseteq> (\<Inter>x\<in>J. X(x))" by auto2

lemma UN_double_eq [rewrite_back]:
  "(\<Union>a\<in>(\<Union>x\<in>L. J(x)). X(a)) = (\<Union>x\<in>L. \<Union>a\<in>J(x). X(a))" by auto2

lemma UN_nonempty [backward]:
  "I \<noteq> \<emptyset> \<Longrightarrow> \<forall>a\<in>I. X(a) \<noteq> \<emptyset> \<Longrightarrow> (\<Union>a\<in>I. X(a)) \<noteq> \<emptyset>" by auto2

lemma INT_double_eq [rewrite_back]:
  "\<forall>x\<in>L. J(x) \<noteq> \<emptyset> \<Longrightarrow> L \<noteq> \<emptyset> \<Longrightarrow> (\<Inter>a\<in>(\<Union>x\<in>L. J(x)). X(a)) = (\<Inter>x\<in>L. \<Inter>a\<in>J(x). X(a))" by auto2

lemma INT_image_eq [rewrite]:
  "injective(f) \<Longrightarrow> I \<noteq> \<emptyset> \<Longrightarrow> f `` (\<Inter>a\<in>I. X(a)) = (\<Inter>a\<in>I. f `` X(a))" by auto2

lemma INT_vImage [backward]:
  "is_function(\<Gamma>) \<Longrightarrow> I \<noteq> \<emptyset> \<Longrightarrow> \<Gamma> -`` (\<Inter>a\<in>I. X(a)) = (\<Inter>a\<in>I. \<Gamma> -`` X(a))" by auto2

lemma UN_complement:
  "I \<noteq> \<emptyset> \<Longrightarrow> E \<midarrow> (\<Union>a\<in>I. X(a)) = (\<Inter>a\<in>I. E \<midarrow> X(a))" by auto2

lemma INT_complement [rewrite]:
  "I \<noteq> \<emptyset> \<Longrightarrow> E \<midarrow> (\<Inter>a\<in>I. X(a)) = (\<Union>a\<in>I. E \<midarrow> X(a))" by auto2

section {* Union and intersection of two sets *}  (* Bourbaki II.4.5 *)

lemma Un_to_UN [rewrite_back]:
  "A \<union> B = (\<Union>{A, B})" by auto2

lemma Int_to_INT [rewrite_back]:
  "A \<inter> B = (\<Inter>{A, B})" by auto2

lemma Un_distrib [resolve]:
  "A \<union> (B \<inter> C) = (A \<union> B) \<inter> (A \<union> C)" by auto2

lemma Int_distrib [resolve]:
  "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)" by auto2

lemma Un_complement [rewrite]:
  "E \<midarrow> (A \<union> B) = (E \<midarrow> A) \<inter> (E \<midarrow> B)" by auto2

lemma Int_complement [rewrite]:
  "E \<midarrow> (A \<inter> B) = (E \<midarrow> A) \<union> (E \<midarrow> B)" by auto2

lemma Un_with_complement [rewrite]:
  "A \<subseteq> E \<Longrightarrow> A \<union> (E \<midarrow> A) = E" by auto2

lemma Int_with_complement [rewrite]:
  "A \<inter> (E \<midarrow> A) = \<emptyset>" by auto2

lemma Int_vImage [rewrite]:
  "is_function(f) \<Longrightarrow> f -`` (A \<inter> B) = (f -`` A) \<inter> (f -`` B)" by auto2

lemma Diff_vImage [rewrite]:
  "is_function(f) \<Longrightarrow> X \<subseteq> E \<Longrightarrow> f -`` (E \<midarrow> X) = (f -`` E) \<midarrow> (f -`` X)" by auto2

lemma Int_image_eq [rewrite]:
  "injective(f) \<Longrightarrow> X \<subseteq> source(f) \<Longrightarrow> f `` (source(f) \<midarrow> X) = image(f) \<midarrow> f `` X" by auto2

section {* Finite roducts *}
  
lemma prod_inter [rewrite]:
  "(A \<times> B) \<inter> (C \<times> D) = (A \<inter> C) \<times> (B \<inter> D)" by auto2

end
