(*
  File: ProductTopology.thy
  Author: Bohua Zhan

  Basic results about product topology.
*)

theory ProductTopology
  imports Topology
begin

section \<open>Product topology\<close>
  
definition prod_basis :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "prod_basis(X,Y) = (\<Union>U\<in>X. \<Union>V\<in>Y. {U \<times> V})"
  
lemma prod_basis_iff [rewrite]:
  "W \<in> prod_basis(X,Y) \<longleftrightarrow> (\<exists>U\<in>X. \<exists>V\<in>Y. W = U \<times> V)" by auto2
setup {* del_prfstep_thm @{thm prod_basis_def} *}

lemma prod_basis_is_basis:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> collection_is_basis(prod_basis(open_sets(X),open_sets(Y)))"
@proof
  @let "\<B> = prod_basis(open_sets(X),open_sets(Y))"
  @have "\<forall>U\<in>\<B>. \<forall>V\<in>\<B>. U \<inter> V \<in> \<B>"
@qed
setup {* add_forward_prfstep_cond @{thm prod_basis_is_basis}
  [with_term "prod_basis(open_sets(?X),open_sets(?Y))"] *}
      
definition product_space :: "i \<Rightarrow> i \<Rightarrow> i"  (infixr "\<times>\<^sub>T" 80) where [rewrite]:
  "product_space(X,Y) = Top(carrier(X)\<times>carrier(Y), top_from_basis(prod_basis(open_sets(X),open_sets(Y))))"
  
lemma product_space_type [typing]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> product_space(X,Y) \<in> raw_top_spaces(carrier(X)\<times>carrier(Y))" by auto2

lemma product_space_is_top_space [forward]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> is_top_space(X \<times>\<^sub>T Y)" by auto2
    
lemma product_space_is_openD [backward2]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> is_open(X \<times>\<^sub>T Y, U) \<Longrightarrow> x \<in> U \<Longrightarrow>
   \<exists>V W. is_open(X,V) \<and> is_open(Y,W) \<and> x \<in> V\<times>W \<and> V\<times>W \<subseteq> U" by auto2
  
lemma product_space_is_openI [forward]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow>
   \<forall>x\<in>U. \<exists>V W. is_open(X,V) \<and> is_open(Y,W) \<and> x \<in> V\<times>W \<and> V\<times>W \<subseteq> U \<Longrightarrow> is_open(X \<times>\<^sub>T Y, U)" by auto2
  
lemma product_space_is_open_prod [backward]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> is_open(X,U) \<Longrightarrow> is_open(Y,V) \<Longrightarrow> is_open(X \<times>\<^sub>T Y, U \<times> V)" by auto2

setup {* del_prfstep_thm @{thm product_space_def} *}

lemma product_space_is_closed_prod [backward]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> is_closed(X,A) \<Longrightarrow> is_closed(Y,B) \<Longrightarrow> is_closed(X \<times>\<^sub>T Y, A \<times> B)"
@proof
  @have "is_closed(X \<times>\<^sub>T Y, carrier(X) \<times> B)"
  @have "is_closed(X \<times>\<^sub>T Y, A \<times> carrier(Y))"
  @have "A \<times> B = carrier(X) \<times> B \<inter> A \<times> carrier(Y)"
@qed

lemma product_space_is_closed_prod1 [backward]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> is_closed(Y,B) \<Longrightarrow> is_closed(X \<times>\<^sub>T Y, carrier(X) \<times> B)" by auto2

lemma product_space_is_closed_prod2 [backward]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> is_closed(X,A) \<Longrightarrow> is_closed(X \<times>\<^sub>T Y, A \<times> carrier(Y))" by auto2

lemma product_space_has_basis [backward]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> top_has_basis(X,\<B>) \<Longrightarrow> top_has_basis(Y,\<C>) \<Longrightarrow>
   top_has_basis(X \<times>\<^sub>T Y, prod_basis(\<B>,\<C>))"
@proof
  @have "\<forall>W\<in>open_sets(X\<times>\<^sub>TY). \<forall>x\<in>W. \<exists>C\<in>prod_basis(\<B>,\<C>). x \<in> C \<and> C \<subseteq> W" @with
    @obtain U V where "is_open(X,U)" "is_open(Y,V)" "x \<in> U\<times>V \<and> U\<times>V \<subseteq> W"
    @obtain "B\<in>\<B>" where "fst(x)\<in>B" "B \<subseteq> U"
    @obtain "C\<in>\<C>" where "snd(x)\<in>C" "C \<subseteq> V"
    @have "B \<times> C \<subseteq> U \<times> V" @end
@qed

(* Commutativity between subspace and product space *)
lemma product_sub_spaces [rewrite]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> A \<subseteq> carrier(X) \<Longrightarrow> B \<subseteq> carrier(Y) \<Longrightarrow>
   subspace(X \<times>\<^sub>T Y, A \<times> B) = subspace(X,A) \<times>\<^sub>T subspace(Y,B)"
@proof
  @let "\<A> = {A \<inter> U. U \<in> open_sets(X)}"
  @let "\<B> = {B \<inter> U. U \<in> open_sets(Y)}"
  @have "top_has_basis(subspace(X,A), \<A>)"
  @have "top_has_basis(subspace(Y,B), \<B>)"
  @have "top_has_basis(subspace(X,A) \<times>\<^sub>T subspace(Y,B), prod_basis(\<A>,\<B>))"
  @let "\<C> = prod_basis(open_sets(X), open_sets(Y))"
  @have "top_has_basis(X \<times>\<^sub>T Y, \<C>)"
  @have "top_has_basis(subspace(X \<times>\<^sub>T Y, A \<times> B), {(A\<times>B) \<inter> U. U \<in> \<C>})"
@qed

lemma product_sub_spaces1 [rewrite]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> B \<subseteq> carrier(Y) \<Longrightarrow>
   subspace(X \<times>\<^sub>T Y, carrier(X) \<times> B) = X \<times>\<^sub>T subspace(Y,B)"
@proof
  @let "\<B> = {B \<inter> U. U \<in> open_sets(Y)}"
  @have "top_has_basis(subspace(Y,B), \<B>)"
  @have "top_has_basis(X \<times>\<^sub>T subspace(Y,B), prod_basis(open_sets(X),\<B>))"
  @let "\<C> = prod_basis(open_sets(X), open_sets(Y))"
  @have "top_has_basis(X \<times>\<^sub>T Y, \<C>)"
  @have "top_has_basis(subspace(X \<times>\<^sub>T Y, carrier(X) \<times> B), {(carrier(X)\<times>B) \<inter> U. U \<in> \<C>})"
  @have "prod_basis(open_sets(X),\<B>) = {(carrier(X)\<times>B)\<inter>U. U \<in> \<C>}" @with
    @have "\<forall>U\<in>prod_basis(open_sets(X),\<B>). U \<in> {(carrier(X)\<times>B)\<inter>U. U \<in> \<C>}" @with
      @obtain "V\<in>open_sets(X)" "W\<in>\<B>" where "U = V \<times> W"
      @obtain "W'\<in>open_sets(Y)" where "W = B \<inter> W'"
      @have "U = carrier(X)\<times>B \<inter> V\<times>W'" @end @end
@qed

lemma product_sub_spaces2 [rewrite]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> A \<subseteq> carrier(X) \<Longrightarrow>
   subspace(X \<times>\<^sub>T Y, A \<times> carrier(Y)) = subspace(X,A) \<times>\<^sub>T Y"
@proof
  @let "\<A> = {A \<inter> U. U \<in> open_sets(X)}"
  @have "top_has_basis(subspace(X,A), \<A>)"
  @have "top_has_basis(subspace(X,A) \<times>\<^sub>T Y, prod_basis(\<A>,open_sets(Y)))"
  @let "\<C> = prod_basis(open_sets(X), open_sets(Y))"
  @have "top_has_basis(X \<times>\<^sub>T Y, \<C>)"
  @have "top_has_basis(subspace(X \<times>\<^sub>T Y, A \<times> carrier(Y)), {(A\<times>carrier(Y)) \<inter> U. U \<in> \<C>})"
  @have "prod_basis(\<A>,open_sets(Y)) = {(A\<times>carrier(Y))\<inter>U. U \<in> \<C>}" @with
    @have "\<forall>U\<in>prod_basis(\<A>,open_sets(Y)). U \<in> {(A\<times>carrier(Y))\<inter>U. U \<in> \<C>}" @with
      @obtain "V\<in>\<A>" "W\<in>open_sets(Y)" where "U = V \<times> W"
      @obtain "V'\<in>open_sets(X)" where "V = A \<inter> V'"
      @have "U = A\<times>carrier(Y) \<inter> V'\<times>W" @end @end
@qed

section \<open>Continuous functions on product spaces\<close>

definition proj1_top :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "proj1_top(A,B) = Mor(A \<times>\<^sub>T B, A, \<lambda>p. fst(p))"

lemma proj1_top_is_morphism [typing]:
  "is_top_space(A) \<Longrightarrow> is_top_space(B) \<Longrightarrow> proj1_top(A,B) \<in> A \<times>\<^sub>T B \<rightharpoonup> A" by auto2
lemma proj1_top_eval [rewrite]:
  "is_top_space(A) \<Longrightarrow> is_top_space(B) \<Longrightarrow> p \<in> source(proj1_top(A,B)) \<Longrightarrow> proj1_top(A,B)`p = fst(p)" by auto2
setup {* del_prfstep_thm @{thm proj1_top_def} *}
setup {* add_rewrite_rule_back @{thm proj1_top_def} *}
  
lemma proj1_top_continuous [forward]:
  "is_top_space(A) \<Longrightarrow> is_top_space(B) \<Longrightarrow> continuous(proj1_top(A,B))"
@proof
  @let "f = proj1_top(A,B)"
  @have "\<forall>V\<in>open_sets(A). is_open(A\<times>\<^sub>TB, f -`` V)" @with
    @have "f -`` V = V \<times> carrier(B)" @end
@qed

lemma proj1_top_continuous' [backward]:
  "is_top_space(A) \<Longrightarrow> is_top_space(B) \<Longrightarrow> C \<subseteq> carrier(A) \<Longrightarrow>
   f = Mor(subspace(A,C) \<times>\<^sub>T B, A, \<lambda>p. fst(p)) \<Longrightarrow> continuous(f)"
@proof @have "f = inj_mor(subspace(A,C),A) \<circ>\<^sub>m proj1_top(subspace(A,C),B)" @qed

definition proj2_top :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "proj2_top(A,B) = Mor(A \<times>\<^sub>T B, B, \<lambda>p. snd(p))"

lemma proj2_top_is_morphism [typing]:
  "is_top_space(A) \<Longrightarrow> is_top_space(B) \<Longrightarrow> proj2_top(A,B) \<in> A \<times>\<^sub>T B \<rightharpoonup> B" by auto2
lemma proj2_top_eval [rewrite]:
  "is_top_space(A) \<Longrightarrow> is_top_space(B) \<Longrightarrow> p \<in> source(proj2_top(A,B)) \<Longrightarrow> proj2_top(A,B)`p = snd(p)" by auto2
setup {* del_prfstep_thm @{thm proj2_top_def} *}
setup {* add_rewrite_rule_back @{thm proj2_top_def} *}
  
lemma proj2_top_continuous [forward]:
  "is_top_space(A) \<Longrightarrow> is_top_space(B) \<Longrightarrow> continuous(proj2_top(A,B))"
@proof
  @let "f = proj2_top(A,B)"
  @have "\<forall>V\<in>open_sets(B). is_open(A\<times>\<^sub>TB, f -`` V)" @with
    @have "f -`` V = carrier(A) \<times> V" @end
@qed

lemma proj2_top_continuous' [backward]:
  "is_top_space(A) \<Longrightarrow> is_top_space(B) \<Longrightarrow> C \<subseteq> carrier(B) \<Longrightarrow>
   f = Mor(A \<times>\<^sub>T subspace(B,C), B, \<lambda>p. snd(p)) \<Longrightarrow> continuous(f)"
@proof @have "f = inj_mor(subspace(B,C),B) \<circ>\<^sub>m proj2_top(A,subspace(B,C))" @qed

definition diag_top_map :: "i \<Rightarrow> i" where [rewrite]:
  "diag_top_map(A) = Mor(A, A \<times>\<^sub>T A, \<lambda>x. \<langle>x,x\<rangle>)"
  
lemma diag_top_map_is_morphism [typing]:
  "is_top_space(A) \<Longrightarrow> diag_top_map(A) \<in> A \<rightharpoonup> A \<times>\<^sub>T A" by auto2
lemma diag_top_map_eval [rewrite]:
  "is_top_space(A) \<Longrightarrow> x \<in> source(diag_top_map(A)) \<Longrightarrow> diag_top_map(A)`x = \<langle>x,x\<rangle>" by auto2
setup {* del_prfstep_thm @{thm diag_top_map_def} *}
  
lemma diag_top_map_continuous [forward]:
  "is_top_space(A) \<Longrightarrow> continuous(diag_top_map(A))"
@proof
  @let "f = diag_top_map(A)"
  @let "\<B> = prod_basis(open_sets(A),open_sets(A))"
  @have "top_has_basis(A \<times>\<^sub>T A, \<B>)"
  @have "\<forall>V\<in>\<B>. is_open(A, f -`` V)" @with
    @obtain "U1\<in>open_sets(A)" "U2\<in>open_sets(A)" where "V = U1 \<times> U2"
    @have "f -`` V = U1 \<inter> U2" @end
@qed

definition prod_top_map :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "prod_top_map(u,v) = Mor(source_str(u) \<times>\<^sub>T source_str(v), target_str(u) \<times>\<^sub>T target_str(v), \<lambda>\<langle>x,y\<rangle>. \<langle>u`x, v`y\<rangle>)"

lemma prod_top_map_is_morphism [typing]:
  "is_morphism_top(u) \<Longrightarrow> is_morphism_top(v) \<Longrightarrow>
   prod_top_map(u,v) \<in> source_str(u) \<times>\<^sub>T source_str(v) \<rightharpoonup> target_str(u) \<times>\<^sub>T target_str(v)" by auto2
  
lemma prod_top_map_eval [rewrite]:
  "is_morphism_top(u) \<Longrightarrow> is_morphism_top(v) \<Longrightarrow>
   \<langle>x,y\<rangle> \<in> source(prod_top_map(u,v)) \<Longrightarrow> prod_top_map(u,v)`\<langle>x,y\<rangle> = \<langle>u`x, v`y\<rangle>" by auto2
setup {* del_prfstep_thm @{thm prod_top_map_def} *}
  
lemma prod_top_map_continuous [forward]:
  "continuous(u) \<Longrightarrow> continuous(v) \<Longrightarrow> continuous(prod_top_map(u,v))"
@proof
  @let "f = prod_top_map(u,v)"
  @let "A = source_str(u)" "B = source_str(v)"
  @let "C = target_str(u)" "D = target_str(v)"
  @let "\<B> = prod_basis(open_sets(C), open_sets(D))"
  @have "top_has_basis(C \<times>\<^sub>T D, \<B>)"
  @have "\<forall>V\<in>\<B>. is_open(A \<times>\<^sub>T B, f -`` V)" @with
    @obtain "U1\<in>open_sets(C)" "U2\<in>open_sets(D)" where "V = U1 \<times> U2"
    @have "f -`` V = (u -`` U1) \<times> (v -`` U2)" @end
@qed

definition incl1_top :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "incl1_top(X,Y,x) = Mor(Y, X \<times>\<^sub>T Y, \<lambda>y. \<langle>x,y\<rangle>)"
setup {* register_wellform_data ("incl1_top(X,Y,x)", ["x \<in>. X"]) *}
  
lemma incl1_top_eval [rewrite]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> x \<in>. X \<Longrightarrow> y \<in> source(incl1_top(X,Y,x)) \<Longrightarrow>
   incl1_top(X,Y,x)`y = \<langle>x,y\<rangle>" by auto2

lemma incl1_top_continuous [typing]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> x \<in>. X \<Longrightarrow> incl1_top(X,Y,x) \<in> Y \<rightharpoonup>\<^sub>T X \<times>\<^sub>T Y"
@proof
  @let "f = incl1_top(X,Y,x)"
  @let "B = prod_basis(open_sets(X),open_sets(Y))"
  @have "top_has_basis(X \<times>\<^sub>T Y, B)"
  @have "\<forall>W\<in>B. is_open(Y, f -`` W)" @with
    @obtain "U\<in>open_sets(X)" "V\<in>open_sets(Y)" where "W = U \<times> V"
    @case "x \<in> U" @with @have "f -`` W = V" @end
    @case "x \<notin> U" @with @have "f -`` W = \<emptyset>" @end
  @end
@qed
setup {* del_prfstep_thm @{thm incl1_top_def} *}
  
definition incl2_top :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "incl2_top(X,Y,y) = Mor(X, X \<times>\<^sub>T Y, \<lambda>x. \<langle>x,y\<rangle>)"
setup {* register_wellform_data ("incl2_top(X,Y,y)", ["y \<in>. Y"]) *}
  
lemma incl2_top_eval [rewrite]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> y \<in>. Y \<Longrightarrow> x \<in> source(incl2_top(X,Y,y)) \<Longrightarrow>
   incl2_top(X,Y,y)`x = \<langle>x,y\<rangle>" by auto2
  
lemma incl2_top_continuous [typing]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> y \<in>. Y \<Longrightarrow> incl2_top(X,Y,y) \<in> X \<rightharpoonup>\<^sub>T X \<times>\<^sub>T Y"
@proof
  @let "f = incl2_top(X,Y,y)"
  @let "B = prod_basis(open_sets(X),open_sets(Y))"
  @have "top_has_basis(X \<times>\<^sub>T Y, B)"
  @have "\<forall>W\<in>B. is_open(X, f -`` W)" @with
    @obtain "U\<in>open_sets(X)" "V\<in>open_sets(Y)" where "W = U \<times> V"
    @case "y \<in> V" @with @have "f -`` W = U" @end
    @case "y \<notin> V" @with @have "f -`` W = \<emptyset>" @end
  @end
@qed
setup {* del_prfstep_thm @{thm incl2_top_def} *}

(* Homeomorphisms on product spaces *)
lemma product_slice1 [typing]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> x \<in>. X \<Longrightarrow> A = {x} \<times> carrier(Y) \<Longrightarrow>
   f = mor_restrict_image_top(incl1_top(X,Y,x),A) \<Longrightarrow> f \<in> Y \<cong>\<^sub>T subspace(X \<times>\<^sub>T Y, A)"
@proof
  @let "g = proj2_top(X,Y) \<circ>\<^sub>m inj_mor(subspace(X \<times>\<^sub>T Y, A), X \<times>\<^sub>T Y)"
  @have "inverse_mor_pair(f,g)"
@qed
      
lemma product_slice1' [backward]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> x \<in>. X \<Longrightarrow> A = {x} \<times> carrier(Y) \<Longrightarrow>
   homeomorphic(Y, subspace(X \<times>\<^sub>T Y, A))"
@proof
  @have "mor_restrict_image_top(incl1_top(X,Y,x),A) \<in> Y \<cong>\<^sub>T subspace(X \<times>\<^sub>T Y, A)"
@qed

lemma product_slice2 [typing]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> y \<in>. Y \<Longrightarrow> A = carrier(X) \<times> {y} \<Longrightarrow>
   f = mor_restrict_image_top(incl2_top(X,Y,y),A) \<Longrightarrow> f \<in> X \<cong>\<^sub>T subspace(X \<times>\<^sub>T Y, A)"
@proof
  @let "g = proj1_top(X,Y) \<circ>\<^sub>m inj_mor(subspace(X \<times>\<^sub>T Y, A), X \<times>\<^sub>T Y)"
  @have "inverse_mor_pair(f,g)"
@qed
      
lemma product_slice2' [backward]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> y \<in>. Y \<Longrightarrow> A = carrier(X) \<times> {y} \<Longrightarrow>
   homeomorphic(X, subspace(X \<times>\<^sub>T Y, A))"
@proof
  @have "mor_restrict_image_top(incl2_top(X,Y,y),A) \<in> X \<cong>\<^sub>T subspace(X \<times>\<^sub>T Y, A)"
@qed

end
