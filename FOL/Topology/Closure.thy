(*
  File: Closure.thy
  Author: Bohua Zhan

  Closure in topological spaces.
*)

theory Closure
  imports ProductTopology
begin

definition interior :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "interior(X,A) = \<Union>{U\<in>open_sets(X). U \<subseteq> A}"
setup {* register_wellform_data ("interior(X,A)", ["A \<subseteq> carrier(X)"]) *}
  
lemma interior_subset [resolve]: "interior(X,A) \<subseteq> A" by auto2
lemma interior_open [resolve]: "is_top_space(X) \<Longrightarrow> is_open(X,interior(X,A))" by auto2

definition closure :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "closure(X,A) = \<Inter>{C\<in>closed_sets(X). A \<subseteq> C}"
setup {* register_wellform_data ("closure(X,A)", ["A \<subseteq> carrier(X)"]) *}

lemma closure_prop:
  "is_top_space(X) \<Longrightarrow> A \<subseteq> carrier(X) \<Longrightarrow> A \<subseteq> closure(X,A) \<and> is_closed(X,closure(X,A))"
@proof @have "carrier(X) \<in> {C\<in>closed_sets(X). A \<subseteq> C}" @qed
setup {* add_forward_prfstep_cond @{thm closure_prop} [with_term "closure(?X,?A)"] *}
      
lemma closure_subset' [backward2]:
  "is_top_space(X) \<Longrightarrow> A \<subseteq> carrier(X) \<Longrightarrow> is_closed(X,B) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> closure(X,A) \<subseteq> B"
@proof @have "carrier(X) \<in> {C\<in>closed_sets(X). A \<subseteq> C}" @qed

lemma closure_subspace:
  "is_top_space(X) \<Longrightarrow> Y \<subseteq> carrier(X) \<Longrightarrow> A \<subseteq> Y \<Longrightarrow> closure(subspace(X,Y),A) = Y \<inter> closure(X,A)"
@proof
  @let "B = closure(subspace(X,Y), A)"
  @have "B \<subseteq> Y \<inter> closure(X,A)" @with
    @have "is_closed(subspace(X,Y), Y \<inter> closure(X,A))" @end
  @obtain "C\<in>closed_sets(X)" where "B = Y \<inter> C"
  @have "closure(X,A) \<subseteq> C"
  @have "Y \<inter> closure(X,A) \<subseteq> Y \<inter> C"
@qed

lemma closure_mem1 [backward1]:
  "is_top_space(X) \<Longrightarrow> A \<subseteq> carrier(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> x \<notin> closure(X,A) \<Longrightarrow> \<exists>U\<in>neighs(X,x). U \<inter> A = \<emptyset>"
@proof @have "carrier(X) \<midarrow> closure(X,A) \<in> neighs(X,x)" @qed

lemma closure_mem2 [forward]:
  "is_top_space(X) \<Longrightarrow> A \<subseteq> carrier(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> x \<in> closure(X,A) \<Longrightarrow> U \<in> neighs(X,x) \<Longrightarrow> U \<inter> A \<noteq> \<emptyset>"
@proof
  @contradiction
  @have "is_closed(X, carrier(X) \<midarrow> U)"
  @have "closure(X,A) \<subseteq> carrier(X) \<midarrow> U"
@qed

definition hausdorff :: "i \<Rightarrow> o" where [rewrite]:
  "hausdorff(X) \<longleftrightarrow> (is_top_space(X) \<and> (\<forall>x\<in>.X. \<forall>y\<in>.X. x \<noteq> y \<longrightarrow> (\<exists>U\<in>neighs(X,x). \<exists>V\<in>neighs(X,y). U \<inter> V = \<emptyset>)))"

lemma hausdorffD1 [forward]: "hausdorff(X) \<Longrightarrow> is_top_space(X)" by auto2
lemma hausdorffD2 [backward]: "hausdorff(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> y \<in>. X \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<exists>U\<in>neighs(X,x). \<exists>V\<in>neighs(X,y). U \<inter> V = \<emptyset>" by auto2
setup {* del_prfstep_thm_eqforward @{thm hausdorff_def} *}

definition T1_space :: "i \<Rightarrow> o" where [rewrite]:
  "T1_space(X) \<longleftrightarrow> (is_top_space(X) \<and> (\<forall>x\<in>.X. is_closed(X,{x})))"

lemma T1_spaceD1 [forward]: "T1_space(X) \<Longrightarrow> is_top_space(X)" by auto2
lemma T1_spaceD2: "T1_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> is_closed(X,{x})" by auto2
setup {* add_forward_prfstep_cond @{thm T1_spaceD2} [with_term "{?x}"] *}
setup {* del_prfstep_thm_eqforward @{thm T1_space_def} *}

lemma hausdorff_is_T1 [forward]: "hausdorff(X) \<Longrightarrow> T1_space(X)"
@proof
  @have "\<forall>x\<in>.X. is_closed(X,{x})" @with
    @contradiction
    @have "\<forall>y\<in>closure(X,{x}). y \<in> {x}" @with
      @contradiction
      @obtain "U\<in>neighs(X,x)" "V\<in>neighs(X,y)" where "U \<inter> V = \<emptyset>" @end @end
@qed

lemma subspace_hausdorff: "hausdorff(X) \<Longrightarrow> A \<subseteq> carrier(X) \<Longrightarrow> hausdorff(subspace(X,A))"
@proof 
  @let "Y = subspace(X,A)"
  @have "\<forall>x\<in>.Y. \<forall>y\<in>.Y. x \<noteq> y \<longrightarrow> (\<exists>U\<in>neighs(Y,x). \<exists>V\<in>neighs(Y,y). U \<inter> V = \<emptyset>)" @with
    @obtain "U\<in>neighs(X,x)" "V\<in>neighs(X,y)" where "U \<inter> V = \<emptyset>"
    @have "(A \<inter> U) \<inter> (A \<inter> V) = \<emptyset>" @end
@qed
setup {* add_forward_prfstep_cond @{thm subspace_hausdorff} [with_term "subspace(?X,?A)"] *}

lemma product_hausdorff [forward]: "hausdorff(X) \<Longrightarrow> hausdorff(Y) \<Longrightarrow> hausdorff(X \<times>\<^sub>T Y)"
@proof 
  @let "Z = X \<times>\<^sub>T Y"
  @have "\<forall>x\<in>.Z. \<forall>y\<in>.Z. x \<noteq> y \<longrightarrow> (\<exists>U\<in>neighs(Z,x). \<exists>V\<in>neighs(Z,y). U \<inter> V = \<emptyset>)" @with
    @case "fst(x) \<noteq> fst(y)" @with
      @obtain "U\<in>neighs(X,fst(x))" "V\<in>neighs(X,fst(y))" where "U \<inter> V = \<emptyset>"
      @have "(U \<times> carrier(Y)) \<inter> (V \<times> carrier(Y)) = \<emptyset>" @end
    @case "snd(x) \<noteq> snd(y)" @with
      @obtain "U\<in>neighs(Y,snd(x))" "V\<in>neighs(Y,snd(y))" where "U \<inter> V = \<emptyset>"
      @have "(carrier(X) \<times> U) \<inter> (carrier(X) \<times> V) = \<emptyset>" @end
  @end
@qed

end
