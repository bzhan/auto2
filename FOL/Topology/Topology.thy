(*
  File: Topology.thy
  Author: Bohua Zhan

  Basics of topological spaces.
*)

theory Topology
  imports Auto2_FOL.Morphism Auto2_FOL.BigSet
begin

section \<open>Topological structure\<close>

definition "open_sets_name = succ(\<emptyset>)"
definition "open_sets(X) = graph_eval(X, open_sets_name)"
setup {* add_field_data (@{term open_sets_name}, @{term open_sets}) *}
  
definition is_open :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite_bidir]:
  "is_open(X,A) \<longleftrightarrow> A \<in> open_sets(X)"

definition is_top_space_raw :: "i \<Rightarrow> o" where [rewrite]:
  "is_top_space_raw(X) \<longleftrightarrow> open_sets(X) \<subseteq> Pow(carrier(X))"
    
lemma is_top_space_rawD [forward]: "is_top_space_raw(X) \<Longrightarrow> is_open(X,A) \<Longrightarrow> A \<subseteq> carrier(X)" by auto2
setup {* del_prfstep_thm_eqforward @{thm is_top_space_raw_def} *}

definition top_space_form :: "i \<Rightarrow> o" where [rewrite]:
  "top_space_form(X) \<longleftrightarrow> is_top_space_raw(X) \<and> is_func_graph(X,{carrier_name,open_sets_name})"

lemma top_space_form_to_raw [forward]: "top_space_form(X) \<Longrightarrow> is_top_space_raw(X)" by auto2

(* Space of all topological structures on S *)
definition raw_top_spaces :: "i \<Rightarrow> i" where [rewrite]:
  "raw_top_spaces(S) = {Struct({\<langle>carrier_name,S\<rangle>, \<langle>open_sets_name,T\<rangle>}). T\<in>Pow(Pow(S))}"
  
lemma raw_top_spacesD [forward]:
  "X \<in> raw_top_spaces(S) \<Longrightarrow> top_space_form(X) \<and> carrier(X) = S" by auto2
    
lemma raw_top_spacesI [resolve]:
  "top_space_form(X) \<Longrightarrow> X \<in> raw_top_spaces(carrier(X))"
@proof @have "X = Struct({\<langle>carrier_name,carrier(X)\<rangle>, \<langle>open_sets_name,open_sets(X)\<rangle>})" @qed

definition Top :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "Top(S,T) = Struct({\<langle>carrier_name,S\<rangle>, \<langle>open_sets_name,T\<rangle>})"
setup {* add_prfstep_check_req ("Top(S,T)", "T \<subseteq> Pow(S)") *}

lemma Top_is_top_space_raw [typing]: "T \<subseteq> Pow(S) \<Longrightarrow> Top(S,T) \<in> raw_top_spaces(S)" by auto2

lemma eval_Top [rewrite]: "is_open(Top(S,T),A) \<longleftrightarrow> A \<in> T" by auto2
lemma open_sets_Top: "open_sets(Top(S,T)) = T" by auto2
setup {* add_forward_prfstep_cond @{thm open_sets_Top} [with_term "Top(?S,?T)"] *}
    
lemma top_space_form_eq [backward]:
  "top_space_form(X) \<Longrightarrow> top_space_form(Y) \<Longrightarrow> carrier(X) = carrier(Y) \<Longrightarrow>
   \<forall>U. is_open(X,U) \<longleftrightarrow> is_open(Y,U) \<Longrightarrow> X = Y" by auto2

setup {* fold del_prfstep_thm [
  @{thm top_space_form_def}, @{thm raw_top_spaces_def}, @{thm Top_def}, @{thm is_open_def}] *}
setup {* add_rewrite_rule_back @{thm is_open_def} *}
setup {* add_rewrite_rule_cond @{thm is_open_def} [with_term "open_sets(?X)"] *}

section {* Definition of a topological space *}

definition union_closed :: "i \<Rightarrow> o" where [rewrite]:
  "union_closed(X) \<longleftrightarrow> (\<forall>C. (\<forall>x\<in>source(C). is_open(X,C`x)) \<longrightarrow> is_open(X,\<Union>x\<in>source(C).C`x))"
  
lemma union_closedD1 [backward]:
  "union_closed(X) \<Longrightarrow> \<forall>U\<in>C. is_open(X,U) \<Longrightarrow> is_open(X,\<Union>C)"
@proof
  @let "F = Tup(C, \<lambda>x. x)" @have "(\<Union>C) = (\<Union>x\<in>source(F). F`x)"
@qed
    
lemma union_closedD2 [backward]:
  "union_closed(X) \<Longrightarrow> \<forall>a\<in>I. is_open(X,C(a)) \<Longrightarrow> is_open(X,\<Union>a\<in>I. C(a))"
@proof @have "(\<Union>a\<in>I. C(a)) = \<Union>{C(a). a\<in>I}" @qed
      
lemma union_closedI [backward]:
  "\<forall>C. (\<forall>x\<in>source(C). is_open(X,C`x)) \<longrightarrow> is_open(X,\<Union>x\<in>source(C).C`x) \<Longrightarrow> union_closed(X)" by auto2
setup {* del_prfstep_thm @{thm union_closed_def} *}

definition finite_inter_closed :: "i \<Rightarrow> o" where [rewrite]:
  "finite_inter_closed(X) \<longleftrightarrow> (\<forall>U V. is_open(X,U) \<longrightarrow> is_open(X,V) \<longrightarrow> is_open(X,U \<inter> V))"
  
lemma finite_inter_closedD [backward1,backward2]:
  "finite_inter_closed(X) \<Longrightarrow> is_open(X,U) \<Longrightarrow> is_open(X,V) \<Longrightarrow> is_open(X,U \<inter> V)" by auto2
setup {* del_prfstep_thm_eqforward @{thm finite_inter_closed_def} *}

definition is_top_space :: "i \<Rightarrow> o" where [rewrite]:
  "is_top_space(X) \<longleftrightarrow> (is_top_space_raw(X) \<and> is_open(X,\<emptyset>) \<and> is_open(X,carrier(X)) \<and>
                        union_closed(X) \<and> finite_inter_closed(X))"

lemma is_top_spaceD1 [forward]:
  "is_top_space(X) \<Longrightarrow> is_top_space_raw(X)"
  "is_top_space(X) \<Longrightarrow> union_closed(X)"
  "is_top_space(X) \<Longrightarrow> finite_inter_closed(X)" by auto2+

lemma is_top_spaceD2 [resolve]:
  "is_top_space(X) \<Longrightarrow> is_open(X,\<emptyset>)"
  "is_top_space(X) \<Longrightarrow> is_open(X,carrier(X))" by auto2+
setup {* del_prfstep_thm_eqforward @{thm is_top_space_def} *}
  
section {* Finer topologies *}
  
definition top_space_finer :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "top_space_finer(X,Y) \<longleftrightarrow> is_top_space_raw(X) \<and> is_top_space_raw(Y) \<and>
     carrier(X) = carrier(Y) \<and> open_sets(Y) \<subseteq> open_sets(X)"
setup {* register_wellform_data ("top_space_finer(X,Y)", ["carrier(X) = carrier(Y)"]) *}
  
definition eq_str_top :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "eq_str_top(X,Y) \<longleftrightarrow> is_top_space_raw(X) \<and> is_top_space_raw(Y) \<and>
     carrier(X) = carrier(Y) \<and> open_sets(X) = open_sets(Y)"
setup {* register_wellform_data ("eq_str_top(X,Y)", ["carrier(X) = carrier(Y)"]) *}

lemma eq_str_top_from_finer [forward]:
  "top_space_finer(X,Y) \<Longrightarrow> top_space_finer(Y,X) \<Longrightarrow> eq_str_top(X,Y)" by auto2
    
lemma topoloogy_eq_from_eq_str [forward]:
  "top_space_form(X) \<Longrightarrow> top_space_form(Y) \<Longrightarrow> eq_str_top(X,Y) \<Longrightarrow> X = Y" by auto2
    
lemma eq_str_top_is_top_space [forward]:
  "is_top_space(X) \<Longrightarrow> eq_str_top(X,Y) \<Longrightarrow> is_top_space(Y)" by auto2
    
lemma eq_str_top_sym [forward]:
  "eq_str_top(X,Y) \<Longrightarrow> eq_str_top(Y,X)" by auto2

section {* Constructing a topological space from a basis *}
  
definition collection_is_basis :: "i \<Rightarrow> o" where [rewrite]:
  "collection_is_basis(\<B>) \<longleftrightarrow> (\<forall>U\<in>\<B>. \<forall>V\<in>\<B>. \<forall>x\<in>U\<inter>V. \<exists>W\<in>\<B>. x\<in>W \<and> W\<subseteq>U\<inter>V)"
  
lemma collection_is_basisD [backward2]:
  "collection_is_basis(\<B>) \<Longrightarrow> x \<in> U \<inter> V \<Longrightarrow> U \<in> \<B> \<Longrightarrow> V \<in> \<B> \<Longrightarrow> \<exists>W\<in>\<B>. x \<in> W \<and> W \<subseteq> U \<inter> V" by auto2
    
lemma collection_is_basisI [forward]:
  "\<forall>U\<in>\<B>. \<forall>V\<in>\<B>. \<forall>x\<in>U\<inter>V. \<exists>W\<in>\<B>. x\<in>W \<and> W\<subseteq>U\<inter>V \<Longrightarrow> collection_is_basis(\<B>)" by auto2
    
lemma collection_is_basisI2 [forward]:
  "\<forall>U\<in>\<B>. \<forall>V\<in>\<B>. U \<inter> V \<in> \<B> \<Longrightarrow> collection_is_basis(\<B>)" by auto2
    
lemma top_all_open_sets_is_basis [forward]:
  "is_top_space(X) \<Longrightarrow> collection_is_basis(open_sets(X))" by auto2

setup {* del_prfstep_thm @{thm collection_is_basis_def} *}

definition top_from_basis :: "i \<Rightarrow> i" where [rewrite]:
  "top_from_basis(\<B>) = {\<Union>S. S\<in>Pow(\<B>)}"

definition top_has_basis :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "top_has_basis(X,\<B>) \<longleftrightarrow> (collection_is_basis(\<B>) \<and> carrier(X) = \<Union>\<B> \<and> open_sets(X) = top_from_basis(\<B>))"

lemma top_from_basis_type [backward]:
  "carrier(X) = \<Union>\<B> \<Longrightarrow> top_from_basis(\<B>) \<subseteq> Pow(carrier(X))" by auto2

lemma top_has_basisI [backward1]:
  "collection_is_basis(\<B>) \<Longrightarrow> carrier(X) = \<Union>\<B> \<Longrightarrow> open_sets(X) = top_from_basis(\<B>) \<Longrightarrow>
   top_has_basis(X,\<B>)" by auto2

lemma top_has_basisD1 [forward]:
  "top_has_basis(X,\<B>) \<Longrightarrow> collection_is_basis(\<B>)" by auto2
    
lemma top_has_basisD2 [rewrite_back]:
  "top_has_basis(X,\<B>) \<Longrightarrow> carrier(X) = \<Union>\<B>" by auto2

lemma top_has_basis_is_openE [backward2]:
  "top_has_basis(X,\<B>) \<Longrightarrow> is_open(X,U) \<Longrightarrow> \<exists>S\<in>Pow(\<B>). U = \<Union>S" by auto2
    
lemma top_has_basis_is_openI [forward]:
  "top_has_basis(X,\<B>) \<Longrightarrow> S \<in> Pow(\<B>) \<Longrightarrow> is_open(X, \<Union>S)" by auto2

lemma top_has_basis_is_openE' [forward]:
  "top_has_basis(X,\<B>) \<Longrightarrow> is_open(X,U) \<Longrightarrow> \<forall>x\<in>U. \<exists>B\<in>\<B>. x \<in> B \<and> B \<subseteq> U" by auto2
    
lemma top_has_basis_is_openI' [backward2]:
  "top_has_basis(X,\<B>) \<Longrightarrow> \<forall>x\<in>U. \<exists>B\<in>\<B>. x \<in> B \<and> B \<subseteq> U \<Longrightarrow> is_open(X,U)"
@proof
  @case "\<forall>x\<in>U. \<exists>B\<in>\<B>. x \<in> B \<and> B \<subseteq> U" @with
    @let "S = {(SOME B\<in>\<B>. x \<in> B \<and> B \<subseteq> U). x\<in>U}" @have "\<Union>S = U" @end
@qed

lemma top_has_basis_id [resolve]:
  "is_top_space(X) \<Longrightarrow> top_has_basis(X, open_sets(X))"
@proof @have (@rule) "\<forall>U\<in>open_sets(X). U = \<Union>{U}" @qed
    
lemma top_has_basis_eq_str_top [rewrite]:
  "eq_str_top(X,Y) \<Longrightarrow> top_has_basis(X,\<B>) \<longleftrightarrow> top_has_basis(Y,\<B>)" by auto2

lemma top_has_basisI' [backward1]:
  "is_top_space(X) \<Longrightarrow> \<B> \<subseteq> open_sets(X) \<Longrightarrow> \<forall>U\<in>open_sets(X). \<forall>x\<in>U. \<exists>C\<in>\<B>. x \<in> C \<and> C \<subseteq> U \<Longrightarrow>
   top_has_basis(X,\<B>)"
@proof
  @have "collection_is_basis(\<B>)" @with
    @have "\<forall>U\<in>\<B>. \<forall>V\<in>\<B>. \<forall>x\<in>U\<inter>V. \<exists>W\<in>\<B>. x\<in>W \<and> W\<subseteq>U\<inter>V" @with
      @have "is_open(X,U \<inter> V)" @end @end
  @have "carrier(X) = \<Union>\<B>" @with @have "is_open(X,carrier(X))" @end
  @have "\<forall>U\<in>open_sets(X). U \<in> {\<Union>S. S\<in>Pow(\<B>)}" @with
    @let "S = {(SOME B\<in>\<B>. x \<in> B \<and> B \<subseteq> U). x\<in>U}" @have "\<Union>S = U" @end
@qed

lemma topology_basis_eq [forward]:
  "top_space_form(X) \<Longrightarrow> top_space_form(Y) \<Longrightarrow> top_has_basis(X,\<B>) \<Longrightarrow> top_has_basis(Y,\<B>) \<Longrightarrow> X = Y"
  by auto2

lemma topology_basis_finer [backward1]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> carrier(X) = carrier(Y) \<Longrightarrow> top_has_basis(Y,\<B>) \<Longrightarrow>
   \<forall>U\<in>\<B>. is_open(X,U) \<Longrightarrow> top_space_finer(X,Y)" by auto2

setup {* del_prfstep_thm @{thm top_has_basis_def} *}

lemma top_has_basis_finite_inter_closed [forward]:
  "top_has_basis(X,\<B>) \<Longrightarrow> finite_inter_closed(X)"
@proof
  @have "\<forall>U V. is_open(X,U) \<longrightarrow> is_open(X,V) \<longrightarrow> is_open(X,U \<inter> V)" @with
    @have "\<forall>x\<in>U\<inter>V. \<exists>B\<in>\<B>. x \<in> B \<and> B \<subseteq> U\<inter>V" @with
      @obtain "B1\<in>\<B>" where "x \<in> B1 \<and> B1 \<subseteq> U"
      @obtain "B2\<in>\<B>" where "x \<in> B2 \<and> B2 \<subseteq> V"
      @have "x \<in> B1 \<inter> B2"
      @obtain "W\<in>\<B>" where "x \<in> W \<and> W \<subseteq> B1 \<inter> B2" @end @end
@qed

lemma top_has_basis_is_topology [forward]:
  "is_top_space_raw(X) \<Longrightarrow> top_has_basis(X,\<B>) \<Longrightarrow> is_top_space(X)"
@proof @have "carrier(X) = \<Union>\<B>" @qed

lemma top_has_basis_is_open_trivial [forward]:
  "top_has_basis(X,\<B>) \<Longrightarrow> S \<in> \<B> \<Longrightarrow> is_open(X,S)" by auto2
    
setup {* add_gen_prfstep ("Top_from_basis_case",
  [WithTerm @{term_pat "Top(?S,top_from_basis(?B))"},
   CreateConcl @{term_pat "top_has_basis(Top(?S,top_from_basis(?B)),?B)"}]) *}

section {* Open and closed sets *}
  
lemma open_union_pair [backward1,backward2]:
  "is_top_space(X) \<Longrightarrow> is_open(X,U) \<Longrightarrow> is_open(X,V) \<Longrightarrow> is_open(X,U \<union> V)"
@proof @have "U \<union> V = \<Union>{U,V}" @qed
    
definition is_closed :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "is_closed(X,A) \<longleftrightarrow> (A \<subseteq> carrier(X) \<and> is_open(X, carrier(X) \<midarrow> A))"

definition closed_sets :: "i \<Rightarrow> i" where [rewrite]:
  "closed_sets(X) = {A \<in> Pow(carrier(X)). is_closed(X,A)}"
  
lemma closed_sets_iff [rewrite_back]: "is_closed(X,A) \<longleftrightarrow> A \<in> closed_sets(X)" by auto2
setup {* add_rewrite_rule_cond @{thm closed_sets_iff} [with_term "closed_sets(?X)"] *}
setup {* del_prfstep_thm @{thm closed_sets_def} *}

lemma is_closed_empty [resolve]:
  "is_top_space(X) \<Longrightarrow> is_closed(X,\<emptyset>)"
@proof  @have "\<emptyset> = carrier(X) \<midarrow> carrier(X)" @qed
    
lemma is_closed_full [resolve]:
  "is_top_space(X) \<Longrightarrow> is_closed(X,carrier(X))"
@proof  @have "\<emptyset> = carrier(X) \<midarrow> carrier(X)" @qed

lemma is_open_compl [rewrite]:
  "is_top_space(X) \<Longrightarrow> A \<subseteq> carrier(X) \<Longrightarrow> is_open(X, carrier(X) \<midarrow> A) \<longleftrightarrow> is_closed(X,A)" by auto2

lemma is_closed_compl [rewrite]:
  "is_top_space(X) \<Longrightarrow> A \<subseteq> carrier(X) \<Longrightarrow> is_closed(X, carrier(X) \<midarrow> A) \<longleftrightarrow> is_open(X,A)" by auto2

lemma closed_union_pair [backward1,backward2]:
  "is_top_space(X) \<Longrightarrow> is_closed(X,A) \<Longrightarrow> is_closed(X,B) \<Longrightarrow> is_closed(X,A \<union> B)" by auto2

lemma closed_inter_pair [backward1,backward2]:
  "is_top_space(X) \<Longrightarrow> is_closed(X,A) \<Longrightarrow> is_closed(X,B) \<Longrightarrow> is_closed(X,A \<inter> B)" by auto2

lemma closed_inter1 [backward]:
  "is_top_space(X) \<Longrightarrow> I \<noteq> \<emptyset> \<Longrightarrow> \<forall>a\<in>I. is_closed(X,C(a)) \<Longrightarrow> is_closed(X,\<Inter>a\<in>I. C(a))" by auto2

lemma closed_inter2 [backward]:
  "is_top_space(X) \<Longrightarrow> C \<noteq> \<emptyset> \<Longrightarrow> \<forall>A\<in>C. is_closed(X,A) \<Longrightarrow> is_closed(X,\<Inter>C)"
@proof
  @let "F = Tup(C, \<lambda>x. x)" @have "(\<Inter>C) = (\<Inter>x\<in>source(F). F`x)"
@qed

section {* Empty topological space *}

definition empty_top_space :: i where [rewrite]:
  "empty_top_space = Top(\<emptyset>,{\<emptyset>})"

lemma empty_top_space_type [typing]: "empty_top_space \<in> raw_top_spaces(\<emptyset>)" by auto2
lemma empty_is_top_space [forward]: "is_top_space(empty_top_space)" by auto2
lemma top_space_on_empty [forward]:
  "top_space_form(X) \<Longrightarrow> is_top_space(X) \<Longrightarrow> carrier(X) = \<emptyset> \<Longrightarrow> X = empty_top_space" by auto2
setup {* del_prfstep_thm @{thm empty_top_space_def} *}

section {* Subspace topology *}
  
definition subspace :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "subspace(X,Y) = Top(Y, {Y \<inter> U. U \<in> open_sets(X)})"
setup {* register_wellform_data ("subspace(X,Y)", ["Y \<subseteq> carrier(X)"]) *}
setup {* add_prfstep_check_req ("subspace(X,Y)", "Y \<subseteq> carrier(X)") *}

lemma subspace_type [typing]: "subspace(X,Y) \<in> raw_top_spaces(Y)" by auto2

lemma subspace_is_openD [resolve]:
  "is_open(subspace(X,Y),U) \<Longrightarrow> \<exists>V\<in>open_sets(X). U = Y \<inter> V" by auto2
    
lemma subspace_is_openI [backward]:
  "is_open(X,U) \<Longrightarrow> is_open(subspace(X,Y), Y \<inter> U)" by auto2
setup {* del_prfstep_thm @{thm subspace_def} *}

lemma subspace_is_top_space:
  "is_top_space(\<X>) \<Longrightarrow> Y \<subseteq> carrier(\<X>) \<Longrightarrow> is_top_space(subspace(\<X>,Y))"
@proof
  @let "\<Y> = subspace(\<X>,Y)"
  @have "\<emptyset> = Y \<inter> \<emptyset>" @have "Y = Y \<inter> carrier(\<X>)"
  @have "\<forall>C. (\<forall>x\<in>source(C). is_open(\<Y>,C`x)) \<longrightarrow> is_open(\<Y>,\<Union>x\<in>source(C). C`x)" @with
    @let "C' = Tup(source(C), \<lambda>x. (SOME V\<in>open_sets(\<X>). C`x = Y \<inter> V))"
    @have "\<forall>x\<in>source(C). C`x = Y \<inter> C'`x"
    @have "(Y \<inter> (\<Union>x\<in>source(C).C'`x)) = (\<Union>x\<in>source(C). C`x)" @end
  @have "\<forall>U V. is_open(\<Y>,U) \<longrightarrow> is_open(\<Y>,V) \<longrightarrow> is_open(\<Y>,U \<inter> V)" @with
    @obtain "U'\<in>open_sets(\<X>)" where "U = Y \<inter> U'"
    @obtain "V'\<in>open_sets(\<X>)" where "V = Y \<inter> V'"
    @have "Y \<inter> (U' \<inter> V') = U \<inter> V" @end
@qed
setup {* add_forward_prfstep_cond @{thm subspace_is_top_space} [with_term "subspace(?\<X>,?Y)"] *}

lemma subspace_is_closedD [resolve]:
  "is_top_space(\<X>) \<Longrightarrow> X = carrier(\<X>) \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> is_closed(subspace(\<X>,Y),A) \<Longrightarrow>
   \<exists>B\<in>closed_sets(\<X>). A = Y \<inter> B"
@proof
  @obtain "U\<in>open_sets(\<X>)" where "Y \<midarrow> A = Y \<inter> U"
  @have "A = Y \<inter> (X \<midarrow> U)" @with
    @have "Y \<inter> (X \<midarrow> U) = Y \<inter> X \<midarrow> Y \<inter> U" @end
@qed

lemma subspace_is_closedI [backward]:
  "is_top_space(\<X>) \<Longrightarrow> X = carrier(\<X>) \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> is_closed(\<X>,C) \<Longrightarrow> is_closed(subspace(\<X>,Y), Y \<inter> C)"
@proof
  @have "is_open(subspace(\<X>,Y), Y \<inter> (X \<midarrow> C))"
  @have "Y \<inter> (X \<midarrow> C) = Y \<midarrow> (Y \<inter> C)"
@qed
      
(* Open subspaces *)
lemma open_subspace_is_open [rewrite]:
  "is_top_space(X) \<Longrightarrow> is_open(X,Y) \<Longrightarrow> U \<subseteq> carrier(subspace(X,Y)) \<Longrightarrow>
   is_open(subspace(X,Y),U) \<longleftrightarrow> is_open(X,U)"
@proof @contradiction @obtain "V\<in>open_sets(X)" where "U = Y \<inter> V" @qed

(* Closed subspaces *)
lemma closed_subspace_is_closed [rewrite]:
  "is_top_space(X) \<Longrightarrow> is_closed(X,Y) \<Longrightarrow> A \<subseteq> carrier(subspace(X,Y)) \<Longrightarrow>
   is_closed(subspace(X,Y),A) \<longleftrightarrow> is_closed(X,A)"
@proof @contradiction @obtain "B\<in>closed_sets(X)" where "A = Y \<inter> B" @qed

lemma subspace_basis [backward]:
  "is_top_space(X) \<Longrightarrow> A \<subseteq> carrier(X) \<Longrightarrow> top_has_basis(X,\<B>) \<Longrightarrow> top_has_basis(subspace(X,A), {A \<inter> U. U \<in> \<B>})"
@proof
  @let "\<C> = {A \<inter> U. U \<in> \<B>}"
  @have "\<forall>U\<in>open_sets(subspace(X,A)). \<forall>x\<in>U. \<exists>C\<in>\<C>. x \<in> C \<and> C \<subseteq> U" @with
    @obtain "V\<in>open_sets(X)" where "U = A \<inter> V"
    @obtain "B\<in>\<B>" where "x \<in> B \<and> B \<subseteq> V"
    @have "x \<in> A \<inter> B \<and> A \<inter> B \<subseteq> U" @end
@qed

lemma subspace_id [rewrite]:
  "top_space_form(X) \<Longrightarrow> is_top_space(X) \<Longrightarrow> subspace(X,carrier(X)) = X"
@proof
  @have "top_has_basis(X, open_sets(X))"
  @have "top_has_basis(subspace(X,carrier(X)), {carrier(X) \<inter> U. U \<in> open_sets(X)})"
@qed

lemma subspace_trans [rewrite]:
  "is_top_space(X) \<Longrightarrow> A \<subseteq> carrier(X) \<Longrightarrow> B \<subseteq> carrier(subspace(X,A)) \<Longrightarrow>
   subspace(subspace(X,A),B) = subspace(X,B)"
@proof
  @let "\<A> = {A \<inter> U. U \<in> open_sets(X)}"
  @let "\<B> = {B \<inter> U. U \<in> open_sets(X)}"
  @have "top_has_basis(subspace(X,A), \<A>)"
  @have "top_has_basis(subspace(X,B), \<B>)"
  @have "top_has_basis(subspace(subspace(X,A),B), {B \<inter> U. U \<in> \<A>})"
  @have "\<B> = {B \<inter> U. U \<in> \<A>}" @with
    @have (@rule) "\<forall>U\<in>open_sets(X). B \<inter> U = B \<inter> (A \<inter> U)" @end
@qed

section {* Neighborhoods *}
  
definition neighs :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "neighs(X,x) = {U \<in> open_sets(X). x \<in> U}"
setup {* register_wellform_data ("neighs(X,x)", ["x \<in>. X"]) *}

lemma neighsI [typing2,backward]: "x \<in> U \<Longrightarrow> is_open(X,U) \<Longrightarrow> U \<in> neighs(X,x)" by auto2
lemma neighsE [forward]: "U \<in> neighs(X,x) \<Longrightarrow> x \<in> U \<and> is_open(X,U)" by auto2
setup {* del_prfstep_thm @{thm neighs_def} *}
  
lemma top_space_is_open_local [backward1]:
  "is_top_space(X) \<Longrightarrow> V \<subseteq> carrier(X) \<Longrightarrow> \<forall>x\<in>V. \<exists>U\<in>neighs(X,x). U \<subseteq> V \<Longrightarrow> is_open(X,V)"
@proof
  @let "C = Tup(V, \<lambda>x. SOME U\<in>neighs(X,x). U \<subseteq> V)"
  @have "V = (\<Union>x\<in>V. C`x)"
@qed

section {* Continuous functions *}

definition is_morphism_top :: "i \<Rightarrow> o" where [rewrite]:
  "is_morphism_top(f) \<longleftrightarrow> (is_morphism(f) \<and> is_top_space(source_str(f)) \<and> is_top_space(target_str(f)))"

lemma is_morphism_topD [forward]:
  "is_morphism_top(f) \<Longrightarrow> is_morphism(f)"
  "is_morphism_top(f) \<Longrightarrow> is_top_space(source_str(f))"
  "is_morphism_top(f) \<Longrightarrow> is_top_space(target_str(f))" by auto2+
    
lemma is_morphism_topI [forward]:
  "is_morphism(f) \<Longrightarrow> is_top_space(source_str(f)) \<Longrightarrow> is_top_space(target_str(f)) \<Longrightarrow> is_morphism_top(f)" by auto2
setup {* del_prfstep_thm @{thm is_morphism_top_def} *}

definition continuous :: "i \<Rightarrow> o" where [rewrite]:
  "continuous(f) \<longleftrightarrow> (is_morphism_top(f) \<and>
                      (\<forall>V\<in>open_sets(target_str(f)). is_open(source_str(f), f -`` V)))"

lemma continuousD1 [forward]:
  "continuous(f) \<Longrightarrow> is_morphism_top(f)" by auto2

lemma continuousD2 [backward]:
  "continuous(f) \<Longrightarrow> is_open(target_str(f),V) \<Longrightarrow> is_open(source_str(f),f-``V)" by auto2
setup {* add_forward_prfstep_cond @{thm continuousD2} [with_term "?f -`` ?V"] *}

lemma continuousI [forward]:
  "is_morphism_top(f) \<Longrightarrow> X = source_str(f) \<Longrightarrow> Y = target_str(f) \<Longrightarrow>
   \<forall>V\<in>open_sets(Y). is_open(X, f -`` V) \<Longrightarrow> continuous(f)" by auto2

definition continuous_fun_space :: "i \<Rightarrow> i \<Rightarrow> i" (infix "\<rightharpoonup>\<^sub>T" 60) where [rewrite]:
  "X \<rightharpoonup>\<^sub>T Y = {f \<in> X \<rightharpoonup> Y. continuous(f)}"

lemma continuous_fun_spaceD [forward]:
  "f \<in> X \<rightharpoonup>\<^sub>T Y \<Longrightarrow> f \<in> X \<rightharpoonup> Y \<and> continuous(f)" by auto2

lemma continuous_fun_spaceI [typing, backward]:
  "mor_form(f) \<Longrightarrow> continuous(f) \<Longrightarrow> f \<in> source_str(f) \<rightharpoonup>\<^sub>T target_str(f)" by auto2
setup {* del_prfstep_thm @{thm continuous_fun_space_def} *}

lemma id_continuous [typing]: "is_top_space(X) \<Longrightarrow> id_mor(X) \<in> X \<rightharpoonup>\<^sub>T X" by auto2

lemma inj_continuous [typing]:
  "is_top_space(X) \<Longrightarrow> Y \<subseteq> carrier(X) \<Longrightarrow> inj_mor(subspace(X,Y),X) \<in> subspace(X,Y) \<rightharpoonup>\<^sub>T X" by auto2

lemma comp_continuous:
  "continuous(f) \<Longrightarrow> continuous(g) \<Longrightarrow> target_str(f) = source_str(g) \<Longrightarrow> continuous(g \<circ>\<^sub>m f)" by auto2
setup {* add_forward_prfstep_cond @{thm comp_continuous} [with_term "?g \<circ>\<^sub>m ?f"] *}
    
lemma comp_continuous' [backward]:
  "Y = source_str(G) \<Longrightarrow> G \<in> Y \<rightharpoonup>\<^sub>T target_str(G) \<Longrightarrow> F = Mor(X,Y,\<lambda>x. f(x)) \<Longrightarrow> F \<in> X \<rightharpoonup>\<^sub>T Y \<Longrightarrow>
   continuous(Mor(X,target_str(G),\<lambda>x. G`(f(x))))"
@proof
  @have (@rule) "\<forall>x\<in>.X. F`x = f(x)"
  @have "Mor(X,target_str(G),\<lambda>x. G`(f(x))) = G \<circ>\<^sub>m F"
@qed

lemma comp_continuous'' [backward2]:
  "is_top_space(Z) \<Longrightarrow> A \<subseteq> carrier(Z) \<Longrightarrow> Y = source_str(G) \<Longrightarrow> target_str(G) = subspace(Z,A) \<Longrightarrow>
   F = Mor(X,Y,\<lambda>x. f(x)) \<Longrightarrow> G \<in> Y \<rightharpoonup>\<^sub>T subspace(Z,A) \<Longrightarrow> F \<in> X \<rightharpoonup>\<^sub>T Y \<Longrightarrow>
   continuous(Mor(X,Z,\<lambda>x. G`(f(x))))"
@proof
  @have (@rule) "\<forall>x\<in>.X. F`x = f(x)"
  @have "Mor(X,Z,\<lambda>x. G`(f(x))) = inj_mor(subspace(Z,A),Z) \<circ>\<^sub>m G \<circ>\<^sub>m F"
@qed
setup {* del_prfstep_thm @{thm continuous_def} *}

lemma continuousD_neighs [backward]:
  "continuous(f) \<Longrightarrow> X = source_str(f) \<Longrightarrow> x \<in>. X \<Longrightarrow> V \<in> neighs(target_str(f),f`x) \<Longrightarrow>
   \<exists>U\<in>neighs(X,x). f``U \<subseteq> V"
@proof @have "is_open(source_str(f), f -`` V)" @qed

lemma continuousI_neighs [forward]:
  "is_morphism_top(f) \<Longrightarrow> X = source_str(f) \<Longrightarrow> Y = target_str(f) \<Longrightarrow>
   \<forall>x\<in>.X. \<forall>V\<in>neighs(Y,f`x). \<exists>U\<in>neighs(X,x). f``U \<subseteq> V \<Longrightarrow> continuous(f)"
@proof
  @have "\<forall>V\<in>open_sets(Y). is_open(X,f-``V)" @with
    @have "\<forall>x\<in>f-``V. \<exists>U\<in>neighs(X,x). U \<subseteq> f-``V"
  @end
@qed

lemma continuousI_basis [forward]:
  "is_morphism_top(f) \<Longrightarrow> X = source_str(f) \<Longrightarrow> Y = target_str(f) \<Longrightarrow>
   top_has_basis(Y,\<B>) \<Longrightarrow> \<forall>V\<in>\<B>. is_open(X, f -`` V) \<Longrightarrow> continuous(f)"
@proof @have "\<forall>x\<in>.X. \<forall>V\<in>neighs(Y,f`x). \<exists>U\<in>neighs(X,x). f``U \<subseteq> V" @qed
    
lemma continuousD_closed [backward]:
  "continuous(f) \<Longrightarrow> is_closed(target_str(f),B) \<Longrightarrow> is_closed(source_str(f),f-``B)"
@proof @have "is_open(source_str(f), f -`` (target(f) \<midarrow> B))" @qed
setup {* add_forward_prfstep_cond @{thm continuousD_closed} [with_term "?f -`` ?B"] *}
    
lemma continuousI_closed [forward]:
  "is_morphism_top(f) \<Longrightarrow> X = source_str(f) \<Longrightarrow> Y = target_str(f) \<Longrightarrow>
   \<forall>B\<in>closed_sets(Y). is_closed(X, f -`` B) \<Longrightarrow> continuous(f)"
@proof
  @have "\<forall>V\<in>open_sets(Y). is_open(X,f-``V)" @with
    @have "is_closed(Y,target(f)\<midarrow>V)" @end
@qed

lemma const_continuous:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> y \<in>. Y \<Longrightarrow> const_mor(X,Y,y) \<in> X \<rightharpoonup>\<^sub>T Y"
@proof
  @have "\<forall>V\<in>open_sets(Y). is_open(X,const_mor(X,Y,y)-``V)" @with @case "y \<in> V" @end
@qed
setup {* add_forward_prfstep_cond @{thm const_continuous} [with_term "const_mor(?X,?Y,?y)"] *}
  
definition mor_restrict_top :: "i \<Rightarrow> i \<Rightarrow> i"  (infix "|\<^sub>T" 55) where [rewrite]:
  "f |\<^sub>T A = Mor(subspace(source_str(f),A),target_str(f),\<lambda>x. f`x)"
setup {* register_wellform_data ("f |\<^sub>T A", ["A \<subseteq> source(f)"]) *}
setup {* add_prfstep_check_req ("f |\<^sub>T A", "A \<subseteq> source(f)") *}

lemma mor_restrict_top_is_morphism [typing]:
  "is_morphism(f) \<Longrightarrow> X = source_str(f) \<Longrightarrow> A \<subseteq> source(f) \<Longrightarrow> f |\<^sub>T A \<in> subspace(X,A) \<rightharpoonup> target_str(f)" by auto2

lemma mor_restrict_top_is_continuous [typing]:
  "continuous(f) \<Longrightarrow> X = source_str(f) \<Longrightarrow> A \<subseteq> source(f) \<Longrightarrow> f |\<^sub>T A \<in> subspace(X,A) \<rightharpoonup>\<^sub>T target_str(f)"
@proof @have "f |\<^sub>T A = f \<circ>\<^sub>m inj_mor(subspace(X,A),X)" @qed

lemma mor_restrict_top_eval [rewrite]:
  "is_morphism(f) \<Longrightarrow> A \<subseteq> source(f) \<Longrightarrow> x \<in> source(f |\<^sub>T A) \<Longrightarrow> (f |\<^sub>T A) ` x = f ` x" by auto2
setup {* del_prfstep_thm @{thm mor_restrict_top_def} *}
  
lemma mor_restrict_top_vImage [rewrite]:
  "is_morphism(f) \<Longrightarrow> A \<subseteq> source(f) \<Longrightarrow> B \<subseteq> target(f) \<Longrightarrow> (f |\<^sub>T A) -`` B = A \<inter> (f -`` B)" by auto2

lemma mor_restrict_top_image [rewrite]:
  "is_morphism(f) \<Longrightarrow> A \<subseteq> source(f) \<Longrightarrow> image(f |\<^sub>T A) = f `` A"
@proof
  @have "\<forall>x\<in>f``A. x \<in> image(f |\<^sub>T A)" @with
    @obtain "y \<in> A" where "f`y = x"
    @have "(f |\<^sub>T A) ` y = x"
  @end
@qed
  
definition mor_restrict_image_top :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "mor_restrict_image_top(f,A) = Mor(source_str(f),subspace(target_str(f),A),\<lambda>x. f`x)"
setup {* register_wellform_data ("mor_restrict_image_top(f,A)", ["image(f) \<subseteq> A", "A \<subseteq> target(f)"]) *}
setup {* add_prfstep_check_req ("mor_restrict_image_top(f,A)", "image(f) \<subseteq> A \<and> A \<subseteq> target(f)") *}

lemma mor_restrict_image_top_is_continuous [typing]:
  "continuous(f) \<Longrightarrow> X = source_str(f) \<Longrightarrow> Y = target_str(f) \<Longrightarrow> image(f) \<subseteq> A \<Longrightarrow> A \<subseteq> target(f) \<Longrightarrow>
   Z = subspace(Y,A) \<Longrightarrow> mor_restrict_image_top(f,A) \<in> X \<rightharpoonup>\<^sub>T Z"
@proof
  @let "g = mor_restrict_image_top(f,A)"
  @have "\<forall>V\<in>open_sets(Z). is_open(X, g -`` V)" @with
    @obtain "U\<in>open_sets(Y)" where "V = A \<inter> U"
    @have "g -`` V = f -`` U" @end
@qed

lemma mor_restrict_image_top_eval [rewrite]:
  "is_morphism(f) \<Longrightarrow> g = mor_restrict_image_top(f,A) \<Longrightarrow> image(f) \<subseteq> A \<Longrightarrow>
   x \<in> source(g) \<Longrightarrow> g`x = f`x" by auto2
setup {* del_prfstep_thm @{thm mor_restrict_image_top_def} *}
  
lemma continuous_paste_open:
  "is_morphism_top(f) \<Longrightarrow> X = source_str(f) \<Longrightarrow> Y = target_str(f) \<Longrightarrow>
   carrier(X) = A \<union> B \<Longrightarrow> is_open(X,A) \<Longrightarrow> is_open(X,B) \<Longrightarrow>
   continuous(f |\<^sub>T A) \<Longrightarrow> continuous(f |\<^sub>T B) \<Longrightarrow> continuous(f)"
@proof
  @have "\<forall>V\<in>open_sets(Y). is_open(X, f -`` V)" @with
    @have "f -`` V = ((f |\<^sub>T A) -`` V) \<union> ((f |\<^sub>T B) -`` V)" @end
@qed

(* Pasting lemma *)
lemma continuous_paste_closed [backward2]:
  "is_morphism_top(f) \<Longrightarrow> X = source_str(f) \<Longrightarrow> Y = target_str(f) \<Longrightarrow>
   carrier(X) = A \<union> B \<Longrightarrow> is_closed(X,A) \<Longrightarrow> is_closed(X,B) \<Longrightarrow>
   continuous(f |\<^sub>T A) \<Longrightarrow> continuous(f |\<^sub>T B) \<Longrightarrow> continuous(f)"
@proof
  @have "\<forall>D\<in>closed_sets(Y). is_closed(X, f -`` D)" @with
    @have "f -`` D = ((f |\<^sub>T A) -`` D) \<union> ((f |\<^sub>T B) -`` D)" @end
@qed

definition glue_morphism :: "[i, i, i] \<Rightarrow> i" where [rewrite]:
  "glue_morphism(X,g,h) = Mor(X,target_str(g),\<lambda>x. if x\<in>source(g) then g`x else h`x)"
setup {* register_wellform_data ("glue_morphism(X,g,h)",
  ["carrier(X) = source(g) \<union> source(h)", "target_str(g) = target_str(h)"]) *}
setup {* add_prfstep_check_req ("glue_morphism(X,g,h)", "carrier(X) = source(g) \<union> source(h)") *}

lemma glue_is_morphism [typing]:
  "is_top_space(X) \<Longrightarrow> is_morphism(g) \<Longrightarrow> is_morphism(h) \<Longrightarrow>
   carrier(X) = source(g) \<union> source(h) \<Longrightarrow> target_str(g) = target_str(h) \<Longrightarrow>
   glue_morphism(X,g,h) \<in> X \<rightharpoonup> target_str(g)" by auto2

lemma glue_morphism_top_eval [rewrite]:
  "is_top_space(X) \<Longrightarrow> is_morphism(g) \<Longrightarrow> is_morphism(h) \<Longrightarrow>
   carrier(X) = source(g) \<union> source(h) \<Longrightarrow> target_str(g) = target_str(h) \<Longrightarrow>
   x \<in> source(glue_morphism(X,g,h)) \<Longrightarrow>
   glue_morphism(X,g,h)`x = (if x \<in> source(g) then g`x else h`x)" by auto2
setup {* del_prfstep_thm @{thm glue_morphism_def} *}

lemma continuous_paste_closed2 [backward]:
  "is_top_space(X) \<Longrightarrow> A = source(g) \<Longrightarrow> B = source(h) \<Longrightarrow> carrier(X) = A \<union> B \<Longrightarrow>
   g \<in> subspace(X,A) \<rightharpoonup>\<^sub>T Y \<Longrightarrow> h \<in> subspace(X,B) \<rightharpoonup>\<^sub>T Y \<Longrightarrow> is_closed(X,A) \<Longrightarrow> is_closed(X,B) \<Longrightarrow>
   \<forall>x\<in>source(g)\<inter>source(h). g`x = h`x \<Longrightarrow> glue_morphism(X,g,h) \<in> X \<rightharpoonup>\<^sub>T Y"
@proof
  @let "f = glue_morphism(X,g,h)"
  @have "f |\<^sub>T source(g) = g" @have "f |\<^sub>T source(h) = h"
@qed
setup {* del_prfstep_thm @{thm continuous_paste_closed} *}

section {* Homeomorphisms *}
  
definition homeomorphism :: "i \<Rightarrow> o" where [rewrite]:
  "homeomorphism(f) \<longleftrightarrow> (is_morphism_top(f) \<and> bijective(f) \<and> continuous(f) \<and> continuous(inverse_mor(f)))"

lemma top_inverse_pair_homeomorphism [forward]:
  "mor_form(g) \<Longrightarrow> mor_form(f) \<Longrightarrow> continuous(f) \<Longrightarrow> continuous(g) \<Longrightarrow> inverse_mor_pair(f,g) \<Longrightarrow>
   homeomorphism(f) \<and> homeomorphism(g)" by auto2

lemma homeomorphismD [backward]:
  "homeomorphism(f) \<Longrightarrow> is_open(source_str(f),U) \<Longrightarrow> is_open(target_str(f),f``U)"
@proof
  @have (@rule) "\<forall>y\<in>target(f). \<exists>x\<in>source(f). f`x = y"
  @have "inverse_mor(f) -`` U = f``U"
@qed

definition top_iso_space :: "i \<Rightarrow> i \<Rightarrow> i"  (infix "\<cong>\<^sub>T" 60) where [rewrite]:
  "top_iso_space(X,Y) = {f \<in> mor_space(X,Y). homeomorphism(f)}"

lemma top_iso_spaceD [forward]:
  "f \<in> X \<cong>\<^sub>T Y \<Longrightarrow> f \<in> X \<rightharpoonup> Y \<and> homeomorphism(f)" by auto2

lemma top_iso_spaceI [backward]:
  "mor_form(f) \<Longrightarrow> homeomorphism(f) \<Longrightarrow> f \<in> source_str(f) \<cong>\<^sub>T target_str(f)" by auto2
setup {* del_prfstep_thm @{thm top_iso_space_def} *}

definition homeomorphic :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "homeomorphic(X,Y) \<longleftrightarrow> (\<exists>f. f \<in> X \<cong>\<^sub>T Y)"

lemma homeomorphicI [forward]: "f \<in> X \<cong>\<^sub>T Y \<Longrightarrow> homeomorphic(X,Y)" by auto2
lemma homeomorphicD [resolve]: "homeomorphic(X,Y) \<Longrightarrow> \<exists>f. f \<in> X \<cong>\<^sub>T Y" by auto2
setup {* del_prfstep_thm @{thm homeomorphic_def} *}

lemma eq_str_top_to_homeomorphic [resolve]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> eq_str_top(X,Y) \<Longrightarrow> homeomorphic(X,Y)"
@proof
  @let "f = Mor(X,Y,\<lambda>x. x)" @have "continuous(f)" @with
    @have "\<forall>U\<in>open_sets(Y). is_open(X,f-``U)" @with @have "f-``U = U" @end @end
  @let "g = Mor(Y,X,\<lambda>x. x)" @have "continuous(g)" @with
    @have "\<forall>U\<in>open_sets(X). is_open(Y,g-``U)" @with @have "g-``U = U" @end @end
  @have "inverse_mor_pair(f,g)" @have "f \<in> X \<cong>\<^sub>T Y"
@qed

end
