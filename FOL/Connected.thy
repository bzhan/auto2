theory Connected
imports ProductTopology OrderTopology
begin

section {* Connected spaces *}

definition separation :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "separation(X,U,V) \<longleftrightarrow> (is_open(X,U) \<and> is_open(X,V) \<and> U \<noteq> \<emptyset> \<and> V \<noteq> \<emptyset> \<and> U \<inter> V = \<emptyset> \<and> U \<union> V = carrier(X))"

lemma separation_eq_str_top [rewrite]:
  "eq_str_top(X,Y) \<Longrightarrow> separation(X,A,B) \<longleftrightarrow> separation(Y,A,B)" by auto2

lemma separation_sym [resolve]: "separation(X,A,B) \<Longrightarrow> separation(X,B,A)" by auto2

definition connected :: "i \<Rightarrow> o" where [rewrite]:
  "connected(X) \<longleftrightarrow> (is_top_space(X) \<and> \<not>(\<exists>U V. separation(X,U,V)))"
setup {* add_property_const @{term connected} *}
  
lemma connectedD1 [forward]: "connected(X) \<Longrightarrow> is_top_space(X)" by auto2
lemma connectedD2 [resolve]: "connected(X) \<Longrightarrow> \<not>separation(X,U,V)" by auto2
lemma connectedI [resolve]: "is_top_space(X) \<Longrightarrow> \<not>connected(X) \<Longrightarrow> \<exists>U V. separation(X,U,V)" by auto2

lemma connected_empty [resolve]: "is_top_space(X) \<Longrightarrow> carrier(X) = \<emptyset> \<Longrightarrow> connected(X)" by auto2
setup {* del_prfstep_thm @{thm connected_def} *}

lemma connectedD':
  "connected(X) \<Longrightarrow> is_open(X,A) \<Longrightarrow> is_closed(X,A) \<Longrightarrow> A = \<emptyset> \<or> A = carrier(X)"
  by (tactic {* auto2s_tac @{context} (HAVE "separation(X,A,carrier(X) \<midarrow> A)") *})

lemma connectedI':
  "is_top_space(X) \<Longrightarrow> \<forall>A\<in>open_sets(X). is_closed(X,A) \<longrightarrow> A = \<emptyset> \<or> A = carrier(X) \<Longrightarrow> connected(X)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "U, V, separation(X,U,V)" THEN HAVE "U = carrier(X) \<midarrow> V") *})

definition connected_subset :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "connected_subset(X,Y) \<longleftrightarrow> (Y \<subseteq> carrier(X) \<and> connected(subspace(X,Y)))"

lemma connected_subset_sep [forward]:
  "is_top_space(X) \<Longrightarrow> separation(X,C,D) \<Longrightarrow> connected_subset(X,Y) \<Longrightarrow> Y \<subseteq> C \<or> Y \<subseteq> D"
  by (tactic {* auto2s_tac @{context} (
    CASE "Y \<inter> C \<noteq> \<emptyset> \<and> Y \<inter> D \<noteq> \<emptyset>" WITH
      HAVE "separation(subspace(X,Y),Y \<inter> C,Y \<inter> D)") *})

lemma connected_subset_full [forward]:
  "is_top_space(X) \<Longrightarrow> connected_subset(X,carrier(X)) \<Longrightarrow> connected(X)"
  by (tactic {* auto2s_tac @{context} (CHOOSE "U,V,separation(X,U,V)") *})
    
lemma connected_union [backward1]:
  "is_top_space(X) \<Longrightarrow> \<forall>a\<in>A. connected_subset(X,a) \<Longrightarrow> (\<Inter>A) \<noteq> \<emptyset> \<Longrightarrow> connected_subset(X, \<Union>A)"
  by (tactic {* auto2s_tac @{context} (
    LET "Y = (\<Union>A)" THEN
    CHOOSE "p, p \<in> (\<Inter>A)" THEN
    HAVE "\<forall>a\<in>A. connected_subset(subspace(X,Y),a)" THEN
    CHOOSE "C, D, separation(subspace(X,Y), C, D)" THEN
    CASE "p \<in> C" WITH HAVE "\<forall>a\<in>A. a \<subseteq> C" THEN
    CASE "p \<in> D" WITH HAVE "\<forall>a\<in>A. a \<subseteq> D") *})
      
lemma connected_union' [backward1]:
  "is_top_space(X) \<Longrightarrow> \<forall>a\<in>A. connected_subset(X,a) \<Longrightarrow> carrier(X) \<subseteq> (\<Union>A) \<Longrightarrow> (\<Inter>A) \<noteq> \<emptyset> \<Longrightarrow> connected(X)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "carrier(X) = (\<Union>A)" THEN
    HAVE "connected_subset(X, carrier(X))") *})

lemma connected_union2 [backward1]:
  "is_top_space(X) \<Longrightarrow> connected_subset(X,A) \<Longrightarrow> connected_subset(X,B) \<Longrightarrow>
   A \<inter> B \<noteq> \<emptyset> \<Longrightarrow> connected_subset(X, A \<union> B)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "A \<union> B = \<Union>{A,B}" THEN HAVE "A \<inter> B = \<Inter>{A,B}") *})

lemma connected_continuous_surj [forward,resolve]:
  "continuous(f) \<Longrightarrow> surjective(f) \<Longrightarrow> connected(source_str(f)) \<Longrightarrow> connected(target_str(f))"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "U, V, separation(target_str(f),U,V)" THEN
    HAVE "separation(source_str(f), f-``U, f-``V)") *})

lemma connected_continuous [backward]:
  "continuous(f) \<Longrightarrow> connected(source_str(f)) \<Longrightarrow> connected_subset(target_str(f),image(f))"
  by (tactic {* auto2s_tac @{context} (
    LET "f' = mor_restrict_image_top(f,image(f))" THEN HAVE "surjective(f')") *})

lemma connected_continuous_subspace [backward]:
  "continuous(f) \<Longrightarrow> connected_subset(source_str(f),A) \<Longrightarrow> connected_subset(target_str(f),f``A)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "connected_subset(source(f),image(f |\<^sub>T A))") *})

lemma connected_is_top_prop [forward]:
  "connected(X) \<Longrightarrow> homeomorphic(X,Y) \<Longrightarrow> connected(Y)"
  by (tactic {* auto2s_tac @{context} (CHOOSE "f, f \<in> X \<cong>\<^sub>T Y") *})
    
lemma connected_is_top_prop2 [forward]:
  "connected(X) \<Longrightarrow> eq_str_top(X,Y) \<Longrightarrow> connected(Y)"
  by (tactic {* auto2s_tac @{context} (HAVE "homeomorphic(X,Y)") *})

section {* Connected-ness on product spaces *}
 
lemma product_connected [forward]:
  "connected(X) \<Longrightarrow> connected(Y) \<Longrightarrow> connected(X \<times>\<^sub>T Y)"
  by (tactic {* auto2s_tac @{context} (
    CASE "carrier(X) = \<emptyset>" THEN CASE "carrier(Y) = \<emptyset>" THEN
    CHOOSE "x, x \<in>. X" THEN
    LET "A = {{x} \<times> carrier(Y) \<union> carrier(X) \<times> {y}. y\<in>.Y}" THEN
    HAVE "(\<Inter>A) \<noteq> \<emptyset>" WITH (
      CHOOSE "y, y \<in>. Y" THEN HAVE "\<langle>x,y\<rangle> \<in> (\<Inter>A)") THEN
    HAVE "carrier(X \<times>\<^sub>T Y) \<subseteq> (\<Union>A)" WITH
      HAVE "\<forall>p\<in>carrier(X \<times>\<^sub>T Y). p \<in> (\<Union>A)" WITH (
        HAVE "p \<in> {x} \<times> carrier(Y) \<union> carrier(X) \<times> {snd(p)}") THEN
    HAVE "\<forall>a\<in>A. connected_subset(X \<times>\<^sub>T Y,a)" WITH (
      CHOOSE "y\<in>.Y, a = {x} \<times> carrier(Y) \<union> carrier(X) \<times> {y}" THEN
      HAVE "{x} \<times> carrier(Y) \<inter> carrier(X) \<times> {y} \<noteq> \<emptyset>" WITH
        HAVE "\<langle>x,y\<rangle> \<in> {x} \<times> carrier(Y) \<inter> carrier(X) \<times> {y}" THEN
      HAVE "connected_subset(X \<times>\<^sub>T Y, {x} \<times> carrier(Y))" WITH
        HAVE "homeomorphic(Y, subspace(X \<times>\<^sub>T Y, {x} \<times> carrier(Y)))" THEN
      HAVE "connected_subset(X \<times>\<^sub>T Y, carrier(X) \<times> {y})" WITH
        HAVE "homeomorphic(X, subspace(X \<times>\<^sub>T Y, carrier(X) \<times> {y}))")) *})

section {* Connected-ness on order topology *}

lemma connected_convex [resolve]:
  "order_topology(X) \<Longrightarrow> connected_subset(X,A) \<Longrightarrow> order_convex(X,A)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "a \<in> A, b \<in> A, \<not>closed_interval(X,a,b) \<subseteq> A" THEN
    CHOOSE "c \<in> closed_interval(X,a,b), c \<notin> A" THEN
    LET "U = A \<inter> less_interval(X,c)" THEN
    LET "V = A \<inter> greater_interval(X,c)" THEN
    HAVE "U \<inter> V = \<emptyset>" THEN HAVE "U \<union> V = A" THEN
    HAVE "separation(subspace(X,A),U,V)") *})

lemma continuum_connected_aux [backward1]:
  "order_topology(X) \<Longrightarrow> linear_continuum(X) \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow>
   carrier(X) = closed_interval(X,a,b) \<Longrightarrow> \<not>separation(X,A,B)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "has_sup(X,A)" WITH HAVE "b \<in> upper_bound(X,A)" THEN
    LET "c = sup(X,A)" THEN
    CASE "c \<in> A" WITH (HAVE "c \<noteq> b" THEN
      CHOOSE "e >\<^sub>X c, closed_open_interval(X,c,e) \<subseteq> A" THEN
      CHOOSE "z, c <\<^sub>X z \<and> z <\<^sub>X e" THEN
      HAVE "z \<in> closed_open_interval(X,c,e)") THEN
    CASE "c \<in> B" WITH (HAVE "c \<noteq> a" THEN
      CHOOSE "d <\<^sub>X c, open_closed_interval(X,d,c) \<subseteq> B" THEN
      HAVE "d \<in> upper_bound(X,A)" WITH (
        HAVE "\<forall>x\<in>A. d \<ge>\<^sub>X x" WITH (
          HAVE "x \<in> open_closed_interval(X,d,c)")))) *})

lemma separation_subspace [backward2]:
  "C \<subseteq> carrier(X) \<Longrightarrow> separation(X,A,B) \<Longrightarrow> C \<inter> A \<noteq> \<emptyset> \<Longrightarrow> C \<inter> B \<noteq> \<emptyset> \<Longrightarrow>
   separation(subspace(X,C), C \<inter> A, C \<inter> B)" by auto2
  
lemma continuum_connected [forward]:
  "order_topology(X) \<Longrightarrow> linear_continuum(X) \<Longrightarrow> connected(X)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "A,B,separation(X,A,B)" THEN
    CHOOSE "a, a \<in> A" THEN CHOOSE "b, b \<in> B" THEN
    CASE "a <\<^sub>X b" WITH (
      LET "I = closed_interval(X,a,b)" THEN
      LET "Y = ord_subspace(X,I)" THEN
      HAVE "linear_continuum(Y)" WITH HAVE "eq_str_order(suborder(X,I),Y)" THEN
      HAVE "carrier(Y) = closed_interval(Y,a,b)" THEN
      HAVE "separation(Y,I \<inter> A,I \<inter> B)" WITH HAVE "eq_str_top(subspace(X,I),Y)") THEN
    CASE "b <\<^sub>X a" WITH (
      LET "I = closed_interval(X,b,a)" THEN
      LET "Y = ord_subspace(X,I)" THEN
      HAVE "linear_continuum(Y)" WITH HAVE "eq_str_order(suborder(X,I),Y)" THEN
      HAVE "carrier(Y) = closed_interval(Y,b,a)" THEN
      HAVE "separation(X,B,A)" THEN
      HAVE "separation(Y,I \<inter> B,I \<inter> A)" WITH HAVE "eq_str_top(subspace(X,I),Y)")) *})

end
