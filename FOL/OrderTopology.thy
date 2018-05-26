theory OrderTopology
imports Topology Interval AlgStructure
begin

section {* Set with at least two element *}
  
definition card_ge2 :: "i \<Rightarrow> o" where [rewrite]:
  "card_ge2(X) \<longleftrightarrow> (\<exists>a\<in>X. \<exists>b\<in>X. a \<noteq> b)"
  
lemma card_ge2I [backward2]: "{a,b} \<subseteq> X \<Longrightarrow> a \<noteq> b \<Longrightarrow> card_ge2(X)" by auto2
lemma card_ge2_D1 [resolve]: "card_ge2(X) \<Longrightarrow> \<exists>a\<in>X. \<exists>b\<in>X. a \<noteq> b" by auto2
lemma card_ge2_D2 [resolve]: "card_ge2(X) \<Longrightarrow> a \<in> X \<Longrightarrow> \<exists>b\<in>X. b \<noteq> a" by auto2
setup {* del_prfstep_thm @{thm card_ge2_def} *}
  
section {* Order topology *}

definition ord_basis :: "i \<Rightarrow> i" where [rewrite]:
  "ord_basis(X) = ((\<Union>a\<in>.X. \<Union>b\<in>.X. {open_interval(X,a,b)}) \<union>
     (\<Union>a\<in>.X. {less_interval(X,a)}) \<union> (\<Union>a\<in>.X. {greater_interval(X,a)}))"
  
lemma ord_basisE [forward]:
  "W \<in> ord_basis(X) \<Longrightarrow> (\<exists>a\<in>.X. \<exists>b\<in>.X. W = open_interval(X,a,b)) \<or>
     (\<exists>a\<in>.X. W = less_interval(X,a)) \<or> (\<exists>a\<in>.X. W = greater_interval(X,a))" by auto2
  
lemma ord_basisI [resolve]:
  "a \<in>. X \<Longrightarrow> b \<in>. X \<Longrightarrow> open_interval(X,a,b) \<in> ord_basis(X)"
  "a \<in>. X \<Longrightarrow> less_interval(X,a) \<in> ord_basis(X)"
  "a \<in>. X \<Longrightarrow> greater_interval(X,a) \<in> ord_basis(X)" by auto2+
setup {* del_prfstep_thm @{thm ord_basis_def} *}

lemma ord_basis_eq_str [rewrite]:
  "eq_str_order(X,Y) \<Longrightarrow> ord_basis(X) = ord_basis(Y)" by auto2

lemma ord_basis_is_basis [forward]:
  "linorder(X) \<Longrightarrow> collection_is_basis(ord_basis(X))"
@proof @let "\<B> = ord_basis(X)" @have "\<forall>U\<in>\<B>. \<forall>V\<in>\<B>. U \<inter> V \<in> \<B>" @qed

lemma ord_basis_union [rewrite]:
  "linorder(X) \<Longrightarrow> card_ge2(carrier(X)) \<Longrightarrow> \<Union>ord_basis(X) = carrier(X)"
@proof
  @have "\<forall>x\<in>.X. x \<in> \<Union>ord_basis(X)" @with
    @obtain "y\<in>.X" where "y \<noteq> x"
    @case "y <\<^sub>X x" @with @have "x \<in> greater_interval(X,y)" @end
    @case "y >\<^sub>X x" @with @have "x \<in> less_interval(X,y)" @end
  @end
@qed

definition order_topology :: "i \<Rightarrow> o" where [rewrite]:
  "order_topology(X) \<longleftrightarrow> (linorder(X) \<and> is_top_space_raw(X) \<and> card_ge2(carrier(X)) \<and>
    open_sets(X) = top_from_basis(ord_basis(X)))"

lemma order_topology_has_basis [forward]:
  "order_topology(X) \<Longrightarrow> top_has_basis(X,ord_basis(X))" by auto2

lemma order_topologyD [forward]:
  "order_topology(X) \<Longrightarrow> linorder(X)"
  "order_topology(X) \<Longrightarrow> is_top_space(X)"
  "order_topology(X) \<Longrightarrow> card_ge2(carrier(X))" by auto2+
    
lemma order_topologyI [backward]:
  "linorder(X) \<Longrightarrow> is_top_space_raw(X) \<Longrightarrow> card_ge2(carrier(X)) \<Longrightarrow>
   open_sets(X) = top_from_basis(ord_basis(X)) \<Longrightarrow> order_topology(X)" by auto2

lemma order_topology_open_interval [resolve]:
  "order_topology(X) \<Longrightarrow> a \<in>. X \<Longrightarrow> b \<in>. X \<Longrightarrow> is_open(X,open_interval(X,a,b))" by auto2
    
lemma order_topology_less_interval [resolve]:
  "order_topology(X) \<Longrightarrow> a \<in>. X \<Longrightarrow> is_open(X,less_interval(X,a))" by auto2
    
lemma order_topology_greater_interval [resolve]:
  "order_topology(X) \<Longrightarrow> a \<in>. X \<Longrightarrow> is_open(X,greater_interval(X,a))" by auto2
    
lemma order_topology_le_interval [resolve]:
  "order_topology(X) \<Longrightarrow> a \<in>. X \<Longrightarrow> is_closed(X,le_interval(X,a))" by auto2
      
lemma order_topology_ge_interval [resolve]:
  "order_topology(X) \<Longrightarrow> a \<in>. X \<Longrightarrow> is_closed(X,ge_interval(X,a))" by auto2
    
lemma order_topology_closed_interval [resolve]:
  "order_topology(X) \<Longrightarrow> a \<in>. X \<Longrightarrow> b \<in>. X \<Longrightarrow> is_closed(X,closed_interval(X,a,b))"
@proof
  @have "closed_interval(X,a,b) = le_interval(X,b) \<inter> ge_interval(X,a)"
@qed

lemma order_top_is_openI [forward]:
  "order_topology(X) \<Longrightarrow> \<forall>x\<in>U. \<exists>a b. x \<in> open_interval(X,a,b) \<and> open_interval(X,a,b) \<subseteq> U \<Longrightarrow> is_open(X,U)" by auto2
  
lemma order_top_is_openD_gt [backward2]:
  "order_topology(X) \<Longrightarrow> is_open(X,U) \<Longrightarrow> a \<in> U \<Longrightarrow> \<exists>M. M >\<^sub>X a \<Longrightarrow> \<exists>c >\<^sub>X a. closed_open_interval(X,a,c) \<subseteq> U"
@proof
  @obtain "W\<in>ord_basis(X)" where "a \<in> W \<and> W \<subseteq> U"
  @case "\<exists>p\<in>.X. \<exists>q\<in>.X. W = open_interval(X,p,q)"
@qed

lemma order_top_is_openD_lt [backward2]:
  "order_topology(X) \<Longrightarrow> is_open(X,U) \<Longrightarrow> a \<in> U \<Longrightarrow> \<exists>M. M <\<^sub>X a \<Longrightarrow> \<exists>c <\<^sub>X a. open_closed_interval(X,c,a) \<subseteq> U"
@proof
  @obtain "W\<in>ord_basis(X)" where "a \<in> W \<and> W \<subseteq> U"
  @case "\<exists>p\<in>.X. \<exists>q\<in>.X. W = open_interval(X,p,q)"
@qed

lemma order_top_is_openD_unbounded [backward2]:
  "order_topology(X) \<Longrightarrow> order_unbounded(X) \<Longrightarrow>
   is_open(X,U) \<Longrightarrow> x \<in> U \<Longrightarrow> \<exists>a b. x \<in> open_interval(X,a,b) \<and> open_interval(X,a,b) \<subseteq> U"
@proof
  @obtain b where "b >\<^sub>X x" "closed_open_interval(X,x,b) \<subseteq> U"
  @obtain a where "a <\<^sub>X x" "open_closed_interval(X,a,x) \<subseteq> U"
  @have "x \<in> open_interval(X,a,b)"
  @have "open_interval(X,a,b) = open_closed_interval(X,a,x) \<union> closed_open_interval(X,x,b)"
@qed

setup {* fold del_prfstep_thm [@{thm order_topology_has_basis}, @{thm order_topology_def}] *}
setup {* add_resolve_prfstep @{thm order_topology_has_basis} *}
  
section {* Data structure for order topology *}
  
definition is_ord_top_raw :: "i \<Rightarrow> o" where [rewrite]:
  "is_ord_top_raw(R) \<longleftrightarrow> is_top_space_raw(R) \<and> raworder(R)"

lemma is_ord_top_rawD [forward]:
  "is_ord_top_raw(R) \<Longrightarrow> is_top_space_raw(R)"
  "is_ord_top_raw(R) \<Longrightarrow> raworder(R)" by auto2+
setup {* del_prfstep_thm_eqforward @{thm is_ord_top_raw_def} *}
  
definition ord_top_form :: "i \<Rightarrow> o" where [rewrite]:
  "ord_top_form(R) \<longleftrightarrow> is_ord_top_raw(R) \<and> is_func_graph(R,{carrier_name,open_sets_name,order_graph_name})"
  
lemma ord_top_form_to_raw [forward]: "ord_top_form(R) \<Longrightarrow> is_ord_top_raw(R)" by auto2

definition OrderTop :: "[i, i, i \<Rightarrow> i \<Rightarrow> o] \<Rightarrow> i" where [rewrite]:
  "OrderTop(S,T,r) = Struct({\<langle>carrier_name,S\<rangle>, \<langle>open_sets_name,T\<rangle>, \<langle>order_graph_name, rel_graph(S,r)\<rangle>})"

lemma OrderTop_is_ord_top_raw [backward]:
  "T \<subseteq> Pow(S) \<Longrightarrow> R = OrderTop(S,T,r) \<Longrightarrow> ord_top_form(R)"
@proof @have "raworder(R)" @qed

lemma OrderTop_eval [rewrite]:
  "carrier(OrderTop(S,T,r)) = S"
  "open_sets(OrderTop(S,T,r)) = T"
  "X = OrderTop(S,T,r) \<Longrightarrow> x \<in>. X \<Longrightarrow> y \<in>. X \<Longrightarrow> x \<le>\<^sub>X y \<longleftrightarrow> r(x,y)" by auto2+

lemma ord_top_eq [backward]:
  "ord_top_form(X) \<Longrightarrow> ord_top_form(Y) \<Longrightarrow> eq_str_order(X,Y) \<Longrightarrow> eq_str_top(X,Y) \<Longrightarrow> X = Y" by auto2

setup {* fold del_prfstep_thm [@{thm ord_top_form_def}, @{thm OrderTop_def}] *}

definition order_top_from_order :: "i \<Rightarrow> i" where [rewrite]:
  "order_top_from_order(X) = OrderTop(carrier(X),top_from_basis(ord_basis(X)),\<lambda>x y. x \<le>\<^sub>X y)"
  
lemma order_top_from_order_ord_top_form [forward]:
  "raworder(X) \<Longrightarrow> ord_top_form(order_top_from_order(X))" by auto2

lemma order_top_from_order_eq_str:
  "raworder(X) \<Longrightarrow> eq_str_order(X,order_top_from_order(X))" by auto2
setup {* add_forward_prfstep_cond @{thm order_top_from_order_eq_str} [with_term "order_top_from_order(?X)"] *}

lemma order_top_from_order_is_ord_top [backward]:
  "linorder(X) \<Longrightarrow> card_ge2(carrier(X)) \<Longrightarrow> order_topology(order_top_from_order(X))" by auto2
setup {* add_prfstep_check_req ("order_top_from_order(X)", "order_topology(order_top_from_order(X))") *}

section {* Defining topology on an ordered ring *}

definition OrdRingTop :: "[i, i, i \<Rightarrow> i \<Rightarrow> i, i, i \<Rightarrow> i \<Rightarrow> i, i \<Rightarrow> i \<Rightarrow> o, i] \<Rightarrow> i" where [rewrite]:
  "OrdRingTop(S,z,f,u,g,r,T) = Struct({\<langle>carrier_name,S\<rangle>, \<langle>open_sets_name,T\<rangle>,
      \<langle>order_graph_name, rel_graph(S,r)\<rangle>,
      \<langle>zero_name, z\<rangle>, \<langle>plus_fun_name, binary_fun_of(S,f)\<rangle>,
      \<langle>one_name, u\<rangle>, \<langle>times_fun_name, binary_fun_of(S,g)\<rangle>})"

lemma OrdRingTop_is_ord_ring_raw [backward]:
  "z \<in> S \<Longrightarrow> binary_fun(S,f) \<Longrightarrow> u \<in> S \<Longrightarrow> binary_fun(S,g) \<Longrightarrow>
   R = OrdRingTop(S,z,f,u,g,r,T) \<Longrightarrow> is_ord_ring_raw(R)"
@proof
  @have "is_abgroup_raw(R)"
  @have "is_group_raw(R)"
  @have "is_ring_raw(R)"  
  @have "raworder(R)"
@qed
    
lemma ord_top_ring_eval [rewrite]:
  "carrier(OrdRingTop(S,z,f,u,g,r,T)) = S"
  "zero(OrdRingTop(S,z,f,u,g,r,T)) = z"
  "one(OrdRingTop(S,z,f,u,g,r,T)) = u"
  "open_sets(OrdRingTop(S,z,f,u,g,r,T)) = T"
  "R = OrdRingTop(S,z,f,u,g,r,T) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> is_abgroup_raw(R) \<Longrightarrow> x +\<^sub>R y = f(x,y)"
  "R = OrdRingTop(S,z,f,u,g,r,T) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> is_group_raw(R) \<Longrightarrow> x *\<^sub>R y = g(x,y)"
  "R = OrdRingTop(S,z,f,u,g,r,T) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x \<le>\<^sub>R y \<longleftrightarrow> r(x,y)" by auto2+
setup {* del_prfstep_thm @{thm OrdRingTop_def} *}

section {* Order topology from an ordered ring *}
  
definition ord_ring_top_from_ord_ring :: "i \<Rightarrow> i" where [rewrite]:
  "ord_ring_top_from_ord_ring(R) =
    OrdRingTop(carrier(R), \<zero>\<^sub>R, \<lambda>x y. x +\<^sub>R y, \<one>\<^sub>R, \<lambda>x y. x *\<^sub>R y, \<lambda>x y. x \<le>\<^sub>R y, top_from_basis(ord_basis(R)))"

lemma ord_ring_top_from_ord_ring_is_ord_ring [forward]:
  "is_ord_ring_raw(R) \<Longrightarrow> is_ord_ring_raw(ord_ring_top_from_ord_ring(R))" by auto2

lemma ord_ring_top_from_ord_ring_eq_str:
  "is_ord_ring_raw(R) \<Longrightarrow> A = ord_ring_top_from_ord_ring(R) \<Longrightarrow> eq_str_ord_ring(R,A)" by auto2
setup {* add_forward_prfstep_cond @{thm ord_ring_top_from_ord_ring_eq_str} [with_term "?A"] *}

lemma ord_ring_top_from_ord_ring_is_top_space_raw [forward]:
  "is_ord_ring_raw(R) \<Longrightarrow> linorder(R) \<Longrightarrow> is_ord_top_raw(ord_ring_top_from_ord_ring(R))" by auto2

lemma ord_ring_top_from_ord_ring_is_ord_top [backward]:
  "is_ord_ring_raw(R) \<Longrightarrow> linorder(R) \<Longrightarrow> card_ge2(carrier(R)) \<Longrightarrow>
   order_topology(ord_ring_top_from_ord_ring(R))" by auto2

section {* Subspace on order topology *}
  
definition order_convex :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "order_convex(X,A) \<longleftrightarrow> (A \<subseteq> carrier(X) \<and> (\<forall>a\<in>A. \<forall>b\<in>A. closed_interval(X,a,b) \<subseteq> A))"
  
lemma order_convexD1 [forward]: "order_convex(X,A) \<Longrightarrow> A \<subseteq> carrier(X)" by auto2

lemma order_convexD2a [backward2]:
  "order_convex(X,A) \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> closed_interval(X,a,b) \<subseteq> A" by auto2
    
lemma order_convexD2b [backward2]:
  "linorder(X) \<Longrightarrow> order_convex(X,A) \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> open_interval(X,a,b) \<subseteq> A" by auto2
setup {* del_prfstep_thm_eqforward @{thm order_convex_def} *}
  
lemma closed_interval_convex [resolve]:
  "linorder(X) \<Longrightarrow> order_convex(X,closed_interval(X,a,b))" by auto2

definition ord_subspace :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "ord_subspace(X,A) = OrderTop(A, {A \<inter> U. U \<in> open_sets(X)}, \<lambda>x y. x \<le>\<^sub>X y)"

lemma ord_subspace_ord_top_form [forward]: "ord_top_form(ord_subspace(X,A))" by auto2
lemma ord_subspace_carrier: "carrier(ord_subspace(X,A)) = A" by auto2
setup {* add_forward_prfstep_cond @{thm ord_subspace_carrier} [with_term "ord_subspace(?X,?A)"] *}

lemma ord_subspace_eq_str [resolve]:
  "is_top_space(X) \<Longrightarrow> A \<subseteq> carrier(X) \<Longrightarrow> eq_str_top(subspace(X,A),ord_subspace(X,A))"
@proof @have "open_sets(subspace(X,A)) = open_sets(ord_subspace(X,A))" @qed
  
lemma ord_subspace_is_top_space:
  "is_top_space(X) \<Longrightarrow> A \<subseteq> carrier(X) \<Longrightarrow> is_top_space(ord_subspace(X,A))"
@proof @have "eq_str_top(subspace(X,A),ord_subspace(X,A))" @qed
setup {* add_forward_prfstep_cond @{thm ord_subspace_is_top_space} [with_term "ord_subspace(?X,?A)"] *}

lemma order_top_from_order_finer1 [resolve]:
  "order_topology(X) \<Longrightarrow> card_ge2(A) \<Longrightarrow> order_convex(X,A) \<Longrightarrow>
   Y = order_top_from_order(suborder(X,A)) \<Longrightarrow> is_open(Y, A \<inter> less_interval(X,x))"
@proof
  @case "x \<in> A" @with @have "A \<inter> less_interval(X,x) = less_interval(suborder(X,A),x)" @end
  @have (@rule) "A \<inter> less_interval(X,x) = \<emptyset> \<or> A \<subseteq> less_interval(X,x)" @with
    @contradiction
    @obtain "b \<in> A" where "b \<in> less_interval(X,x)"
    @obtain "c \<in> A" where "c \<notin> less_interval(X,x)"
    @have "closed_interval(X,b,c) \<subseteq> A"
    @have "x \<in> closed_interval(X,b,c)" @end
@qed

lemma order_top_from_order_finer2 [resolve]:
  "order_topology(X) \<Longrightarrow> card_ge2(A) \<Longrightarrow> order_convex(X,A) \<Longrightarrow>
   Y = order_top_from_order(suborder(X,A)) \<Longrightarrow> is_open(Y, A \<inter> greater_interval(X,x))"
@proof
  @case "x \<in> A" @with @have "A \<inter> greater_interval(X,x) = greater_interval(suborder(X,A),x)" @end
  @have (@rule) "A \<inter> greater_interval(X,x) = \<emptyset> \<or> A \<subseteq> greater_interval(X,x)" @with
    @contradiction
    @obtain "b \<in> A" where "b \<in> greater_interval(X,x)"
    @obtain "c \<in> A" where "c \<notin> greater_interval(X,x)"
    @have "closed_interval(X,c,b) \<subseteq> A"
    @have "x \<in> closed_interval(X,c,b)" @end
@qed

lemma order_top_from_order_finer3 [resolve]:
  "order_topology(X) \<Longrightarrow> card_ge2(A) \<Longrightarrow> order_convex(X,A) \<Longrightarrow>
   Y = order_top_from_order(suborder(X,A)) \<Longrightarrow> is_open(Y, A \<inter> open_interval(X,x,y))"
@proof
  @have "open_interval(X,x,y) = less_interval(X,y) \<inter> greater_interval(X,x)"
  @have "A \<inter> open_interval(X,x,y) = (A \<inter> less_interval(X,y)) \<inter> (A \<inter> greater_interval(X,x))"
  @have "is_open(Y, A \<inter> less_interval(X,y))"
@qed

lemma order_top_from_order_eq_sub [backward]:
  "order_topology(X) \<Longrightarrow> card_ge2(A) \<Longrightarrow> order_convex(X,A) \<Longrightarrow>
   eq_str_top(ord_subspace(X,A),order_top_from_order(suborder(X,A)))"
@proof
  @let "Y = order_top_from_order(suborder(X,A))"
  @let "Z = ord_subspace(X,A)"
  @have "top_space_finer(Z,Y)"
  @let "\<B> = {A \<inter> U. U \<in> ord_basis(X)}"
  @have "top_has_basis(Z,\<B>)" @with @have "eq_str_top(subspace(X,A),Z)" @end
  @have "top_space_finer(Y,Z)" @with @have "\<forall>U\<in>\<B>. is_open(Y,U)" @end
@qed

lemma ord_subspace_is_order_top:
  "order_topology(X) \<Longrightarrow> card_ge2(A) \<Longrightarrow> order_convex(X,A) \<Longrightarrow> order_topology(ord_subspace(X,A))"
@proof @have "ord_subspace(X,A) = order_top_from_order(suborder(X,A))"@qed
setup {* add_forward_prfstep_cond @{thm ord_subspace_is_order_top} [with_term "ord_subspace(?X,?A)"] *}

lemma closed_interval_order_topology:
  "order_topology(X) \<Longrightarrow> a <\<^sub>X b \<Longrightarrow> I = closed_interval(X,a,b) \<Longrightarrow> order_topology(ord_subspace(X,I))"
@proof
  @have "card_ge2(I)" @with @have "{a,b} \<subseteq> I" @end
  @have "order_convex(X,I)"
@qed
setup {* add_forward_prfstep_cond @{thm closed_interval_order_topology} [with_term "ord_subspace(?X,?I)"] *}

end
