theory Interval
imports OrderRel
begin
  
section {* Intervals *}  (* Bourbaki III.1.13 *)

definition closed_interval :: "[i, i, i] \<Rightarrow> i" where [rewrite]:
  "closed_interval(R,a,b) = {x \<in>. R. a \<le>\<^sub>R x \<and> x \<le>\<^sub>R b}"
setup {* register_wellform_data ("closed_interval(R,a,b)", ["a \<in>. R", "b \<in>. R"]) *}

lemma closed_interval_subset [resolve]: "closed_interval(R,a,b) \<subseteq> carrier(R)" by auto2
lemma closed_interval_iff [rewrite]: "raworder(R) \<Longrightarrow> x \<in> closed_interval(R,a,b) \<longleftrightarrow> (a \<le>\<^sub>R x \<and> x \<le>\<^sub>R b)" by auto2
lemma closed_interval_I1 [typing2]: "preorder(R) \<Longrightarrow> a \<le>\<^sub>R b \<Longrightarrow> a \<in> closed_interval(R,a,b)" by auto2
lemma closed_interval_I2 [typing2]: "preorder(R) \<Longrightarrow> a \<le>\<^sub>R b \<Longrightarrow> b \<in> closed_interval(R,a,b)" by auto2
setup {* del_prfstep_thm @{thm closed_interval_def} *}

definition open_interval :: "[i, i, i] \<Rightarrow> i" where [rewrite]:
  "open_interval(R,a,b) = {x \<in>. R. a <\<^sub>R x \<and> x <\<^sub>R b}"
setup {* register_wellform_data ("open_interval(R,a,b)", ["a \<in>. R", "b \<in>. R"]) *}

lemma open_interval_subset [resolve]: "open_interval(R,a,b) \<subseteq> carrier(R)" by auto2
lemma open_interval_iff [rewrite]: "raworder(R) \<Longrightarrow> x \<in> open_interval(R,a,b) \<longleftrightarrow> (a <\<^sub>R x \<and> x <\<^sub>R b)" by auto2
lemma open_interval_eq_str [rewrite]:
  "eq_str_order(X,Y) \<Longrightarrow> a \<in>. X \<Longrightarrow> b \<in>. X \<Longrightarrow> open_interval(X,a,b) = open_interval(Y,a,b)" by auto2
setup {* del_prfstep_thm @{thm open_interval_def} *}

definition closed_open_interval :: "[i, i, i] \<Rightarrow> i" where [rewrite]:
  "closed_open_interval(R,a,b) = {x \<in>. R. a \<le>\<^sub>R x \<and> x <\<^sub>R b}"
setup {* register_wellform_data ("closed_open_interval(R,a,b)", ["a \<in>. R", "b \<in>. R"]) *}
  
lemma closed_open_interval_subset [resolve]: "closed_open_interval(R,a,b) \<subseteq> carrier(R)" by auto2
lemma closed_open_interval_iff [rewrite]: "raworder(R) \<Longrightarrow> x \<in> closed_open_interval(R,a,b) \<longleftrightarrow> (a \<le>\<^sub>R x \<and> x <\<^sub>R b)" by auto2
setup {* del_prfstep_thm @{thm closed_open_interval_def} *}

definition open_closed_interval :: "[i, i, i] \<Rightarrow> i" where [rewrite]:
  "open_closed_interval(R,a,b) = {x \<in>. R. a <\<^sub>R x \<and> x \<le>\<^sub>R b}"
setup {* register_wellform_data ("open_closed_interval(R,a,b)", ["a \<in>. R", "b \<in>. R"]) *}
  
lemma open_closed_interval_subset [resolve]: "open_closed_interval(R,a,b) \<subseteq> carrier(R)" by auto2
lemma open_closed_interval_iff [rewrite]: "raworder(R) \<Longrightarrow> x \<in> open_closed_interval(R,a,b) \<longleftrightarrow> (a <\<^sub>R x \<and> x \<le>\<^sub>R b)" by auto2
setup {* del_prfstep_thm @{thm open_closed_interval_def} *}

definition le_interval :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "le_interval(R,a) = {x \<in>. R. x \<le>\<^sub>R a}"
setup {* register_wellform_data ("le_interval(R,a)", ["a \<in>. R"]) *}
  
lemma le_interval_subset [resolve]: "le_interval(R,a) \<subseteq> carrier(R)" by auto2
lemma le_intervalI [typing2]: "raworder(R) \<Longrightarrow> x \<le>\<^sub>R a \<Longrightarrow> x \<in> le_interval(R,a)" by auto2
lemma le_interval_iff [rewrite]: "raworder(R) \<Longrightarrow> x \<in> le_interval(R,a) \<longleftrightarrow> x \<le>\<^sub>R a" by auto2
setup {* del_prfstep_thm @{thm le_interval_iff} *}

definition less_interval :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "less_interval(R,a) = {x \<in>. R. x <\<^sub>R a}"
setup {* register_wellform_data ("less_interval(R,a)", ["a \<in>. R"]) *}

lemma less_interval_subset [resolve]: "less_interval(R,a) \<subseteq> carrier(R)" by auto2
lemma less_intervalI [typing2]: "raworder(R) \<Longrightarrow> x <\<^sub>R a \<Longrightarrow> x \<in> less_interval(R,a)" by auto2
lemma less_interval_iff [rewrite]: "raworder(R) \<Longrightarrow> x \<in> less_interval(R,a) \<longleftrightarrow> x <\<^sub>R a" by auto2
lemma less_interval_eq_str [rewrite]:
  "eq_str_order(X,Y) \<Longrightarrow> a \<in>. X \<Longrightarrow> less_interval(X,a) = less_interval(Y,a)" by auto2
setup {* del_prfstep_thm @{thm less_interval_def} *}

definition ge_interval :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "ge_interval(R,a) = {x \<in>. R. x \<ge>\<^sub>R a}"
setup {* register_wellform_data ("ge_interval(R,a)", ["a \<in>. R"]) *}

lemma ge_interval_subset [resolve]: "ge_interval(R,a) \<subseteq> carrier(R)" by auto2
lemma ge_intervalI [typing2]: "raworder(R) \<Longrightarrow> x \<ge>\<^sub>R a \<Longrightarrow> x \<in> ge_interval(R,a)" by auto2
lemma ge_interval_iff [rewrite]: "raworder(R) \<Longrightarrow> x \<in> ge_interval(R,a) \<longleftrightarrow> x \<ge>\<^sub>R a" by auto2
setup {* del_prfstep_thm @{thm ge_interval_def} *}

definition greater_interval :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "greater_interval(R,a) = {x \<in>. R. x >\<^sub>R a}"
setup {* register_wellform_data ("greater_interval(R,a)", ["a \<in>. R"]) *}
  
lemma greater_interval_subset [resolve]: "greater_interval(R,a) \<subseteq> carrier(R)" by auto2
lemma greater_intervalI [typing2]: "raworder(R) \<Longrightarrow> x >\<^sub>R a \<Longrightarrow> x \<in> greater_interval(R,a)" by auto2
lemma greater_interval_iff [rewrite]: "raworder(R) \<Longrightarrow> x \<in> greater_interval(R,a) \<longleftrightarrow> x >\<^sub>R a" by auto2
lemma greater_interval_eq_str [rewrite]:
  "eq_str_order(X,Y) \<Longrightarrow> a \<in>. X \<Longrightarrow> greater_interval(X,a) = greater_interval(Y,a)" by auto2
setup {* del_prfstep_thm @{thm greater_interval_def} *}

section {* Intersection of intervals *}
  
lemma open_interval_inter [rewrite]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> c \<in>. R \<Longrightarrow> d \<in>. R \<Longrightarrow>
   open_interval(R,a,b) \<inter> open_interval(R,c,d) = open_interval(R,max(R,a,c),min(R,b,d))" by auto2

lemma open_less_interval_inter [rewrite]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> c \<in>. R \<Longrightarrow>
   open_interval(R,a,b) \<inter> less_interval(R,c) = open_interval(R,a,min(R,b,c))" by auto2

lemma open_greater_interval_inter [rewrite]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> c \<in>. R \<Longrightarrow>
   open_interval(R,a,b) \<inter> greater_interval(R,c) = open_interval(R,max(R,a,c),b)" by auto2
  
lemma less_open_interval_inter [rewrite]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> c \<in>. R \<Longrightarrow>
   less_interval(R,c) \<inter> open_interval(R,a,b) = open_interval(R,a,min(R,b,c))" by auto2
  
lemma less_less_interval_inter [rewrite]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow>
   less_interval(R,a) \<inter> less_interval(R,b) = less_interval(R,min(R,a,b))" by auto2
  
lemma lesss_greater_interval_inter [rewrite]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow>
   less_interval(R,a) \<inter> greater_interval(R,b) = open_interval(R,b,a)" by auto2

lemma greater_open_interval_inter [rewrite]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> c \<in>. R \<Longrightarrow>
   greater_interval(R,c) \<inter> open_interval(R,a,b) = open_interval(R,max(R,a,c),b)" by auto2
  
lemma greater_less_interval_inter [rewrite]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow>
   greater_interval(R,b) \<inter> less_interval(R,a) = open_interval(R,b,a)" by auto2

lemma greater_greater_interval_inter [rewrite]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow>
   greater_interval(R,a) \<inter> greater_interval(R,b) = greater_interval(R,max(R,a,b))" by auto2
  
section {* Union of intervals *}
  
lemma open_closed_open_union [rewrite]:
  "linorder(X) \<Longrightarrow> a <\<^sub>X b \<Longrightarrow> b <\<^sub>X c \<Longrightarrow>
   open_closed_interval(X,a,b) \<union> closed_open_interval(X,b,c) = open_interval(X,a,c)" by auto2

section {* Complement of intervals *}

lemma order_ge_compl [rewrite]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> carrier(R) \<midarrow> ge_interval(R,a) = less_interval(R,a)" by auto2

lemma order_greater_compl [rewrite]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> carrier(R) \<midarrow> greater_interval(R,a) = le_interval(R,a)" by auto2

lemma order_less_compl [rewrite]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> carrier(R) \<midarrow> less_interval(R,a) = ge_interval(R,a)" by auto2

lemma order_le_compl [rewrite]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> carrier(R) \<midarrow> le_interval(R,a) = greater_interval(R,a)" by auto2

lemma ge_compl_is_less' [forward]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> S \<subseteq> carrier(R) \<Longrightarrow> carrier(R) \<midarrow> S = ge_interval(R,a) \<Longrightarrow>
   S = less_interval(R,a)"
@proof @have "S = carrier(R) \<midarrow> (carrier(R) \<midarrow> S)" @qed
    
section {* Inclusion results on intervals *}

lemma open_interval_contain [backward]:
  "order(R) \<Longrightarrow> a \<ge>\<^sub>R c \<Longrightarrow> b \<le>\<^sub>R d \<Longrightarrow> open_interval(R,a,b) \<subseteq> open_interval(R,c,d)" by auto2

lemma closed_open_sub_open [backward]:
  "linorder(X) \<Longrightarrow> p <\<^sub>X a \<Longrightarrow> closed_open_interval(X,a,q) \<subseteq> open_interval(X,p,q)" by auto2

lemma closed_open_sub_less [resolve]:
  "linorder(X) \<Longrightarrow> closed_open_interval(X,a,p) \<subseteq> less_interval(X,p)" by auto2

lemma closed_open_sub_greater [backward]:
  "linorder(X) \<Longrightarrow> q <\<^sub>X a \<Longrightarrow> closed_open_interval(X,a,p) \<subseteq> greater_interval(X,q)" by auto2
    
lemma open_closed_sub_open [backward]:
  "linorder(X) \<Longrightarrow> a <\<^sub>X q \<Longrightarrow> open_closed_interval(X,p,a) \<subseteq> open_interval(X,p,q)" by auto2
    
lemma open_closed_sub_greater [resolve]:
  "linorder(X) \<Longrightarrow> open_closed_interval(X,p,a) \<subseteq> greater_interval(X,p)" by auto2
    
lemma open_closed_sub_less [backward]:
  "linorder(X) \<Longrightarrow> a <\<^sub>X q \<Longrightarrow> open_closed_interval(X,p,a) \<subseteq> less_interval(X,q)" by auto2

section {* Intervals on suborder *}
  
lemma less_interval_suborder [rewrite]:
  "linorder(X) \<Longrightarrow> A \<subseteq> carrier(X) \<Longrightarrow> x \<in> A \<Longrightarrow>
   less_interval(suborder(X,A),x) = A \<inter> less_interval(X,x)" by auto2

lemma greater_interval_suborder [rewrite]:
  "linorder(X) \<Longrightarrow> A \<subseteq> carrier(X) \<Longrightarrow> x \<in> A \<Longrightarrow>
   greater_interval(suborder(X,A),x) = A \<inter> greater_interval(X,x)" by auto2

lemma open_interval_suborder [rewrite]:
  "linorder(X) \<Longrightarrow> A \<subseteq> carrier(X) \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow>
   open_interval(suborder(X,A),x,y) = A \<inter> open_interval(X,x,y)" by auto2

section {* Other results *}

(* Intervals with one boundary are distinct *)
lemma less_interval_neq [backward]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> a \<noteq> b \<Longrightarrow> less_interval(R,a) \<noteq> less_interval(R,b)"
@proof @case "a <\<^sub>R b" @qed

(* Ordering on less_interval. *)
definition less_interval_rel :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "less_interval_rel(R,x) = suborder(R,less_interval(R,x))"
setup {* register_wellform_data ("less_interval_rel(R,x)", ["x \<in>. R"]) *}

lemma less_interval_rel_trans [rewrite]:
  "linorder(R) \<Longrightarrow> y <\<^sub>R x \<Longrightarrow> less_interval_rel(less_interval_rel(R,x),y) = less_interval_rel(R,y)" by auto2

lemma less_interval_rel_eq_trans [forward]:
  "linorder(R) \<Longrightarrow> linorder(S) \<Longrightarrow> x \<in>. S \<Longrightarrow> y \<le>\<^sub>R x \<Longrightarrow>
   less_interval_rel(R,x) = less_interval_rel(S,x) \<Longrightarrow>
   y\<in>.S \<and> less_interval_rel(R,y) = less_interval_rel(S,y)"
@proof
  @case "y \<noteq> x" @with
    @have "less_interval_rel(less_interval_rel(R,x),y) = less_interval_rel(R,y)" @end
@qed

section {* Intervals inherit a number of order properties *}
  
lemma dense_order_closed_interval:
  "linorder(R) \<Longrightarrow> dense_order(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> S = suborder(R,closed_interval(R,a,b)) \<Longrightarrow> 
   dense_order(S)"
@proof
  @have "\<forall>x y. x <\<^sub>S y \<longrightarrow> (\<exists>z. x <\<^sub>S z \<and> z <\<^sub>S y)" @with
    @obtain z where "x <\<^sub>R z \<and> z <\<^sub>R y" @then @have "x <\<^sub>S z" @end
@qed
setup {* add_forward_prfstep_cond @{thm dense_order_closed_interval} [with_term "?S"] *}

lemma linear_continuum_closed_interval:
  "linear_continuum(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> S = suborder(R,closed_interval(R,a,b)) \<Longrightarrow> 
   linear_continuum(S)"
@proof
  @have "\<forall>T. T \<noteq> \<emptyset> \<longrightarrow> upper_bound(S,T) \<noteq> \<emptyset> \<longrightarrow> has_sup(S,T)" @with
    @have "has_sup(R,T)" @then
    @have "has_sup(S,T) \<and> sup(S,T) = sup(R,T)"
  @end
@qed

setup {* add_forward_prfstep_cond @{thm linear_continuum_closed_interval} [with_term "?S"] *}
  
end
