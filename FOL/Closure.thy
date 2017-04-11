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
  by (tactic {* auto2s_tac @{context} (HAVE "carrier(X) \<in> {C\<in>closed_sets(X). A \<subseteq> C}") *})
setup {* add_forward_prfstep_cond @{thm closure_prop} [with_term "closure(?X,?A)"] *}
      
lemma closure_subset' [backward2]:
  "is_top_space(X) \<Longrightarrow> A \<subseteq> carrier(X) \<Longrightarrow> is_closed(X,B) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> closure(X,A) \<subseteq> B"
  by (tactic {* auto2s_tac @{context} (HAVE "carrier(X) \<in> {C\<in>closed_sets(X). A \<subseteq> C}") *})

lemma closure_subspace:
  "is_top_space(X) \<Longrightarrow> Y \<subseteq> carrier(X) \<Longrightarrow> A \<subseteq> Y \<Longrightarrow> closure(subspace(X,Y),A) = Y \<inter> closure(X,A)"
  by (tactic {* auto2s_tac @{context} (
    LET "B = closure(subspace(X,Y), A)" THEN
    HAVE "B \<subseteq> Y \<inter> closure(X,A)" WITH
      HAVE "is_closed(subspace(X,Y), Y \<inter> closure(X,A))" THEN
    CHOOSE "C\<in>closed_sets(X), B = Y \<inter> C" THEN
    HAVE "closure(X,A) \<subseteq> C" THEN
    HAVE "Y \<inter> closure(X,A) \<subseteq> Y \<inter> C") *})

lemma closure_mem1 [backward1]:
  "is_top_space(X) \<Longrightarrow> A \<subseteq> carrier(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> x \<notin> closure(X,A) \<Longrightarrow> \<exists>U\<in>neighs(X,x). U \<inter> A = \<emptyset>"
  by (tactic {* auto2s_tac @{context} (HAVE "carrier(X) \<midarrow> closure(X,A) \<in> neighs(X,x)") *})

lemma closure_mem2 [forward]:
  "is_top_space(X) \<Longrightarrow> A \<subseteq> carrier(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> x \<in> closure(X,A) \<Longrightarrow> U \<in> neighs(X,x) \<Longrightarrow> U \<inter> A \<noteq> \<emptyset>"
  by (tactic {* auto2s_tac @{context} (
    HAVE "is_closed(X, carrier(X) \<midarrow> U)" THEN
    HAVE "closure(X,A) \<subseteq> carrier(X) \<midarrow> U") *})

definition hausdorff :: "i \<Rightarrow> o" where [rewrite]:
  "hausdorff(X) \<longleftrightarrow> (is_top_space(X) \<and> (\<forall>x\<in>.X. \<forall>y\<in>.X. x \<noteq> y \<longrightarrow> (\<exists>U\<in>neighs(X,x). \<exists>V\<in>neighs(X,y). U \<inter> V = \<emptyset>)))"
setup {* add_property_const @{term hausdorff} *}

lemma hausdorffD1 [forward]: "hausdorff(X) \<Longrightarrow> is_top_space(X)" by auto2
lemma hausdorffD2 [backward]: "hausdorff(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> y \<in>. X \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<exists>U\<in>neighs(X,x). \<exists>V\<in>neighs(X,y). U \<inter> V = \<emptyset>" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm hausdorff_def} *}

definition T1_space :: "i \<Rightarrow> o" where [rewrite]:
  "T1_space(X) \<longleftrightarrow> (is_top_space(X) \<and> (\<forall>x\<in>.X. is_closed(X,{x})))"
setup {* add_property_const @{term T1_space} *}

lemma T1_spaceD1 [forward]: "T1_space(X) \<Longrightarrow> is_top_space(X)" by auto2
lemma T1_spaceD2: "T1_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> is_closed(X,{x})" by auto2
setup {* add_forward_prfstep_cond @{thm T1_spaceD2} [with_term "{?x}"] *}
setup {* del_prfstep_thm_str "@eqforward" @{thm T1_space_def} *}

lemma hausdorff_is_T1 [forward]: "hausdorff(X) \<Longrightarrow> T1_space(X)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x\<in>.X. is_closed(X,{x})" WITH (
      HAVE "\<forall>y\<in>closure(X,{x}). y \<in> {x}" WITH (
        CHOOSE "U\<in>neighs(X,x), V\<in>neighs(X,y), U \<inter> V = \<emptyset>"))) *})

lemma subspace_hausdorff: "hausdorff(X) \<Longrightarrow> A \<subseteq> carrier(X) \<Longrightarrow> hausdorff(subspace(X,A))"
  by (tactic {* auto2s_tac @{context} (
    LET "Y = subspace(X,A)" THEN
    HAVE "\<forall>x\<in>.Y. \<forall>y\<in>.Y. x \<noteq> y \<longrightarrow> (\<exists>U\<in>neighs(Y,x). \<exists>V\<in>neighs(Y,y). U \<inter> V = \<emptyset>)" WITH (
      CHOOSE "U\<in>neighs(X,x), V\<in>neighs(X,y), U \<inter> V = \<emptyset>" THEN
      HAVE "(A \<inter> U) \<inter> (A \<inter> V) = \<emptyset>")) *})
setup {* add_forward_prfstep_cond @{thm subspace_hausdorff} [with_term "subspace(?X,?A)"] *}

lemma product_hausdorff [forward]: "hausdorff(X) \<Longrightarrow> hausdorff(Y) \<Longrightarrow> hausdorff(X \<times>\<^sub>T Y)"
  by (tactic {* auto2s_tac @{context} (
    LET "Z = X \<times>\<^sub>T Y" THEN
    HAVE "\<forall>x\<in>.Z. \<forall>y\<in>.Z. x \<noteq> y \<longrightarrow> (\<exists>U\<in>neighs(Z,x). \<exists>V\<in>neighs(Z,y). U \<inter> V = \<emptyset>)" WITH (
      CASE "fst(x) \<noteq> fst(y)" WITH (
        CHOOSE "U\<in>neighs(X,fst(x)), V\<in>neighs(X,fst(y)), U \<inter> V = \<emptyset>" THEN
        HAVE "(U \<times> carrier(Y)) \<inter> (V \<times> carrier(Y)) = \<emptyset>") THEN
      CASE "snd(x) \<noteq> snd(y)" WITH (
        CHOOSE "U\<in>neighs(Y,snd(x)), V\<in>neighs(Y,snd(y)), U \<inter> V = \<emptyset>" THEN
        HAVE "(carrier(X) \<times> U) \<inter> (carrier(X) \<times> V) = \<emptyset>"))) *})

end
