(*
  File: Connected.thy
  Author: Bohua Zhan

  Connected topological spaces.
*)

theory Connected
  imports ProductTopology OrderTopology
begin

section \<open>Connected spaces\<close>

definition separation :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "separation(X,U,V) \<longleftrightarrow> (is_open(X,U) \<and> is_open(X,V) \<and> U \<noteq> \<emptyset> \<and> V \<noteq> \<emptyset> \<and> U \<inter> V = \<emptyset> \<and> U \<union> V = carrier(X))"

lemma separation_eq_str_top [rewrite]:
  "eq_str_top(X,Y) \<Longrightarrow> separation(X,A,B) \<longleftrightarrow> separation(Y,A,B)" by auto2

lemma separation_sym [resolve]: "separation(X,A,B) \<Longrightarrow> separation(X,B,A)" by auto2

definition connected :: "i \<Rightarrow> o" where [rewrite]:
  "connected(X) \<longleftrightarrow> (is_top_space(X) \<and> \<not>(\<exists>U V. separation(X,U,V)))"
  
lemma connectedD1 [forward]: "connected(X) \<Longrightarrow> is_top_space(X)" by auto2
lemma connectedD2 [resolve]: "connected(X) \<Longrightarrow> \<not>separation(X,U,V)" by auto2
lemma connectedI [resolve]: "is_top_space(X) \<Longrightarrow> \<not>connected(X) \<Longrightarrow> \<exists>U V. separation(X,U,V)" by auto2

lemma connected_empty [resolve]: "is_top_space(X) \<Longrightarrow> carrier(X) = \<emptyset> \<Longrightarrow> connected(X)" by auto2
setup {* del_prfstep_thm @{thm connected_def} *}

lemma connectedD':
  "connected(X) \<Longrightarrow> is_open(X,A) \<Longrightarrow> is_closed(X,A) \<Longrightarrow> A = \<emptyset> \<or> A = carrier(X)"
@proof @contradiction @have "separation(X,A,carrier(X) \<midarrow> A)" @qed

lemma connectedI':
  "is_top_space(X) \<Longrightarrow> \<forall>A\<in>open_sets(X). is_closed(X,A) \<longrightarrow> A = \<emptyset> \<or> A = carrier(X) \<Longrightarrow> connected(X)"
@proof
  @contradiction
  @obtain U V where "separation(X,U,V)" @have "U = carrier(X) \<midarrow> V"
@qed

definition connected_subset :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "connected_subset(X,Y) \<longleftrightarrow> (Y \<subseteq> carrier(X) \<and> connected(subspace(X,Y)))"

lemma connected_subset_sep [forward]:
  "is_top_space(X) \<Longrightarrow> separation(X,C,D) \<Longrightarrow> connected_subset(X,Y) \<Longrightarrow> Y \<subseteq> C \<or> Y \<subseteq> D"
@proof 
  @case "Y \<inter> C \<noteq> \<emptyset> \<and> Y \<inter> D \<noteq> \<emptyset>" @with
    @have "separation(subspace(X,Y),Y \<inter> C,Y \<inter> D)" @end
@qed

lemma connected_subset_full [forward]:
  "is_top_space(X) \<Longrightarrow> connected_subset(X,carrier(X)) \<Longrightarrow> connected(X)"
@proof @contradiction @obtain U V where "separation(X,U,V)" @qed
    
lemma connected_union [backward1]:
  "is_top_space(X) \<Longrightarrow> \<forall>a\<in>A. connected_subset(X,a) \<Longrightarrow> (\<Inter>A) \<noteq> \<emptyset> \<Longrightarrow> connected_subset(X, \<Union>A)"
@proof
  @contradiction
  @let "Y = (\<Union>A)"
  @obtain p where "p \<in> (\<Inter>A)"
  @have (@rule) "\<forall>a\<in>A. connected_subset(subspace(X,Y),a)"
  @obtain C D where "separation(subspace(X,Y), C, D)"
  @case "p \<in> C" @with @have "\<forall>a\<in>A. a \<subseteq> C" @end
@qed
      
lemma connected_union' [backward1]:
  "is_top_space(X) \<Longrightarrow> \<forall>a\<in>A. connected_subset(X,a) \<Longrightarrow> carrier(X) \<subseteq> (\<Union>A) \<Longrightarrow> (\<Inter>A) \<noteq> \<emptyset> \<Longrightarrow> connected(X)"
@proof 
  @have "carrier(X) = (\<Union>A)"
  @have "connected_subset(X, carrier(X))"
@qed

lemma connected_union2 [backward1]:
  "is_top_space(X) \<Longrightarrow> connected_subset(X,A) \<Longrightarrow> connected_subset(X,B) \<Longrightarrow>
   A \<inter> B \<noteq> \<emptyset> \<Longrightarrow> connected_subset(X, A \<union> B)"
@proof @have "A \<union> B = \<Union>{A,B}" @have "A \<inter> B = \<Inter>{A,B}" @qed

lemma connected_continuous_surj [forward,resolve]:
  "continuous(f) \<Longrightarrow> surjective(f) \<Longrightarrow> connected(source_str(f)) \<Longrightarrow> connected(target_str(f))"
@proof
  @contradiction
  @obtain U V where "separation(target_str(f),U,V)"
  @have "separation(source_str(f), f-``U, f-``V)"
@qed

lemma connected_continuous [backward]:
  "continuous(f) \<Longrightarrow> connected(source_str(f)) \<Longrightarrow> connected_subset(target_str(f),image(f))"
@proof 
  @let "f' = mor_restrict_image_top(f,image(f))" @have "surjective(f')"
@qed

lemma connected_continuous_subspace [backward]:
  "continuous(f) \<Longrightarrow> connected_subset(source_str(f),A) \<Longrightarrow> connected_subset(target_str(f),f``A)"
@proof @contradiction @have "connected_subset(source(f),image(f |\<^sub>T A))" @qed

lemma connected_is_top_prop [forward]:
  "connected(X) \<Longrightarrow> homeomorphic(X,Y) \<Longrightarrow> connected(Y)"
@proof @obtain "f \<in> X \<cong>\<^sub>T Y" @qed
    
lemma connected_is_top_prop2 [forward]:
  "connected(X) \<Longrightarrow> eq_str_top(X,Y) \<Longrightarrow> connected(Y)"
@proof @have "homeomorphic(X,Y)" @qed

section \<open>Connected-ness on product spaces\<close>
 
lemma product_connected [forward]:
  "connected(X) \<Longrightarrow> connected(Y) \<Longrightarrow> connected(X \<times>\<^sub>T Y)"
@proof
  @case "carrier(X) = \<emptyset>" @case "carrier(Y) = \<emptyset>"
  @obtain "x \<in>. X"
  @let "A = {{x} \<times> carrier(Y) \<union> carrier(X) \<times> {y}. y\<in>.Y}"
  @have "(\<Inter>A) \<noteq> \<emptyset>" @with
    @obtain "y \<in>. Y" @have "\<langle>x,y\<rangle> \<in> (\<Inter>A)" @end
  @have "carrier(X \<times>\<^sub>T Y) \<subseteq> (\<Union>A)" @with
    @have "\<forall>p\<in>carrier(X \<times>\<^sub>T Y). p \<in> (\<Union>A)" @with
      @have "p \<in> {x} \<times> carrier(Y) \<union> carrier(X) \<times> {snd(p)}" @end @end
  @have "\<forall>a\<in>A. connected_subset(X \<times>\<^sub>T Y,a)" @with
    @obtain "y\<in>.Y" where "a = {x} \<times> carrier(Y) \<union> carrier(X) \<times> {y}"
    @have "{x} \<times> carrier(Y) \<inter> carrier(X) \<times> {y} \<noteq> \<emptyset>" @with
      @have "\<langle>x,y\<rangle> \<in> {x} \<times> carrier(Y) \<inter> carrier(X) \<times> {y}" @end
    @have "connected_subset(X \<times>\<^sub>T Y, {x} \<times> carrier(Y))" @with
      @have "homeomorphic(Y, subspace(X \<times>\<^sub>T Y, {x} \<times> carrier(Y)))" @end
    @have "connected_subset(X \<times>\<^sub>T Y, carrier(X) \<times> {y})" @with
      @have "homeomorphic(X, subspace(X \<times>\<^sub>T Y, carrier(X) \<times> {y}))" @end
  @end
@qed

section \<open>Connected-ness on order topology\<close>

lemma connected_convex [resolve]:
  "order_topology(X) \<Longrightarrow> connected_subset(X,A) \<Longrightarrow> order_convex(X,A)"
@proof 
  @have "\<forall>a\<in>A. \<forall>b\<in>A. closed_interval(X,a,b) \<subseteq> A" @with
    @have "\<forall>c\<in>closed_interval(X,a,b). c \<in> A" @with
      @contradiction
      @let "U = A \<inter> less_interval(X,c)"
      @let "V = A \<inter> greater_interval(X,c)"
      @have "U \<inter> V = \<emptyset>" @have "U \<union> V = A"
      @have "separation(subspace(X,A),U,V)" @end @end
@qed

lemma continuum_connected_aux [backward1]:
  "order_topology(X) \<Longrightarrow> linear_continuum(X) \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow>
   carrier(X) = closed_interval(X,a,b) \<Longrightarrow> \<not>separation(X,A,B)"
@proof
  @contradiction
  @have "has_sup(X,A)" @with @have "b \<in> upper_bound(X,A)" @end
  @let "c = sup(X,A)"
  @case "c \<in> A" @with
    @have "c \<noteq> b"
    @obtain e where "e >\<^sub>X c" "closed_open_interval(X,c,e) \<subseteq> A"
    @obtain z where "c <\<^sub>X z \<and> z <\<^sub>X e"
    @have "z \<in> closed_open_interval(X,c,e)" @end
  @case "c \<in> B" @with
    @have "c \<noteq> a"
    @obtain d where "d <\<^sub>X c" "open_closed_interval(X,d,c) \<subseteq> B"
    @have "d \<in> upper_bound(X,A)" @with
      @have "\<forall>x\<in>A. d \<ge>\<^sub>X x" @with
        @have "x \<notin> open_closed_interval(X,d,c)" @end @end @end
@qed

lemma separation_subspace [backward2]:
  "C \<subseteq> carrier(X) \<Longrightarrow> separation(X,A,B) \<Longrightarrow> C \<inter> A \<noteq> \<emptyset> \<Longrightarrow> C \<inter> B \<noteq> \<emptyset> \<Longrightarrow>
   separation(subspace(X,C), C \<inter> A, C \<inter> B)" by auto2
  
lemma continuum_connected [forward]:
  "order_topology(X) \<Longrightarrow> linear_continuum(X) \<Longrightarrow> connected(X)"
@proof
  @contradiction
  @obtain A B where "separation(X,A,B)"
  @obtain "a \<in> A" @obtain "b \<in> B"
  @case "a <\<^sub>X b" @with
    @let "I = closed_interval(X,a,b)"
    @let "Y = ord_subspace(X,I)"
    @have "linear_continuum(Y)" @with @have "eq_str_order(suborder(X,I),Y)" @end
    @have "carrier(Y) = closed_interval(Y,a,b)"
    @have "separation(Y,I \<inter> A,I \<inter> B)" @with @have "eq_str_top(subspace(X,I),Y)" @end @end
  @case "b <\<^sub>X a" @with
    @let "I = closed_interval(X,b,a)"
    @let "Y = ord_subspace(X,I)"
    @have "linear_continuum(Y)" @with @have "eq_str_order(suborder(X,I),Y)" @end
    @have "carrier(Y) = closed_interval(Y,b,a)"
    @have "separation(X,B,A)"
    @have "separation(Y,I \<inter> B,I \<inter> A)" @with @have "eq_str_top(subspace(X,I),Y)" @end @end
@qed

end
