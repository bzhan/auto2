(*
  File: MetricSpaces.thy
  Author: Bohua Zhan

  Metric spaces.
*)

theory MetricSpaces
  imports RealTopology
begin

section \<open>Metric spaces\<close>

definition "metric_fun_name = succ(succ(\<emptyset>))"
definition "metric_fun(X) = graph_eval(X, metric_fun_name)"
setup {* add_field_data (@{term metric_fun_name}, @{term metric_fun}) *}
  
definition dist :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "dist(X,x,y) = metric_fun(X)`\<langle>x,y\<rangle>"
setup {* register_wellform_data ("dist(X,x,y)", ["x \<in>. X", "y \<in>. X"]) *}
  
definition is_metric_space_raw :: "i \<Rightarrow> o" where [rewrite]:
  "is_metric_space_raw(X) \<longleftrightarrow> (\<forall>x\<in>.X. \<forall>y\<in>.X. dist(X,x,y) \<in> real)"
  
lemma is_metric_space_rawI [backward]:
  "\<forall>x\<in>.X. \<forall>y\<in>.X. dist(X,x,y) \<in> real \<Longrightarrow> is_metric_space_raw(X)" by auto2

lemma is_metric_space_rawD [typing]:
  "is_metric_space_raw(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> y \<in>. X \<Longrightarrow> dist(X,x,y) \<in> real" by auto2
setup {* del_prfstep_thm @{thm is_metric_space_raw_def} *}

definition is_metric_space :: "i \<Rightarrow> o" where [rewrite]:
  "is_metric_space(X) \<longleftrightarrow>
    is_metric_space_raw(X) \<and>
    (\<forall>x\<in>.X. \<forall>y\<in>.X. dist(X,x,y) = 0\<^sub>\<real> \<longleftrightarrow> x = y) \<and>
    (\<forall>x\<in>.X. \<forall>y\<in>.X. dist(X,x,y) = dist(X,y,x)) \<and>
    (\<forall>x\<in>.X. \<forall>y\<in>.X. \<forall>z\<in>.X. dist(X,x,y) +\<^sub>\<real> dist(X,y,z) \<ge>\<^sub>\<real> dist(X,x,z))"

lemma is_metric_spaceD [forward]:
  "is_metric_space(X) \<Longrightarrow> is_metric_space_raw(X)" by auto2

lemma is_metric_spaceD1 [forward]:
  "is_metric_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> y \<in>. X \<Longrightarrow> dist(X,x,y) = 0\<^sub>\<real> \<Longrightarrow> x = y"
@proof @have "dist(X,x,y) = 0\<^sub>\<real> \<longleftrightarrow> x = y" @qed
    
lemma is_metric_spaceD2 [rewrite]:
  "is_metric_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> dist(X,x,x) = 0\<^sub>\<real>"
@proof @have "dist(X,x,x) = 0\<^sub>\<real> \<longleftrightarrow> x = x" @qed

lemma is_metric_spaceD3 [rewrite]:
  "is_metric_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> y \<in>. X \<Longrightarrow> dist(X,x,y) = dist(X,y,x)" by auto2
    
lemma is_metric_spaceD4 [backward]:
  "is_metric_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> y \<in>. X \<Longrightarrow> z \<in>. X \<Longrightarrow>
   dist(X,x,y) +\<^sub>\<real> dist(X,y,z) \<ge>\<^sub>\<real> dist(X,x,z)" by auto2

lemma is_metric_spaceD5:
  "is_metric_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> y \<in>. X \<Longrightarrow> dist(X,x,y) \<ge>\<^sub>\<real> 0\<^sub>\<real>"
@proof 
  @have "dist(X,x,y) +\<^sub>\<real> dist(X,y,x) \<ge>\<^sub>\<real> 0\<^sub>\<real>" @with @have "dist(X,x,x) = 0\<^sub>\<real>" @end
  @case "dist(X,x,y) <\<^sub>\<real> 0\<^sub>\<real>" @with @have "dist(X,y,x) <\<^sub>\<real> 0\<^sub>\<real>" @end
@qed
setup {* add_forward_prfstep_cond @{thm is_metric_spaceD5} [with_term "dist(?X,?x,?y)"] *}
setup {* del_prfstep_thm_str "@eqforward" @{thm is_metric_space_def} *}

lemma metric_space_dist_bound [backward1, backward2]:
  "is_metric_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> y \<in>. X \<Longrightarrow> z \<in>. X \<Longrightarrow>
   dist(X,x,y) <\<^sub>\<real> s \<Longrightarrow> dist(X,y,z) <\<^sub>\<real> t \<Longrightarrow> dist(X,x,z) <\<^sub>\<real> s +\<^sub>\<real> t"
@proof @have "dist(X,x,z) \<le>\<^sub>\<real> dist(X,x,y) +\<^sub>\<real> dist(X,y,z)" @qed

definition open_ball :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "open_ball(X,x,a) = {y\<in>.X. dist(X,x,y) <\<^sub>\<real> a}"
setup {* register_wellform_data ("open_ball(X,x,a)", ["x \<in>. X", "a \<in>. \<real>"]) *}

lemma open_ballD [forward]: "y \<in> open_ball(X,x,a) \<Longrightarrow> dist(X,x,y) <\<^sub>\<real> a" by auto2
lemma open_ballI [typing2]: "y \<in>. X \<Longrightarrow> dist(X,x,y) <\<^sub>\<real> a \<Longrightarrow> y \<in> open_ball(X,x,a)" by auto2
lemma open_ball_sub_carrier: "open_ball(X,x,a) \<subseteq> carrier(X)" by auto2
setup {* add_forward_prfstep_cond @{thm open_ball_sub_carrier} [with_term "open_ball(?X,?x,?a)"] *}
lemma open_ball_mem_self [backward]:
  "is_metric_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> a >\<^sub>\<real> 0\<^sub>\<real> \<Longrightarrow> x \<in> open_ball(X,x,a)" by auto2
lemma open_ball_eq [rewrite]:
  "carrier(X) = carrier(Y) \<Longrightarrow> metric_fun(X) = metric_fun(Y) \<Longrightarrow>
   open_ball(X,x,a) = open_ball(Y,x,a)" by auto2
setup {* del_prfstep_thm @{thm open_ball_def} *}
  
(* Subset relation on open balls *)
lemma open_ball_subset [backward]:
  "is_metric_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> y \<in>. X \<Longrightarrow> a +\<^sub>\<real> dist(X,x,y) \<le>\<^sub>\<real> b \<Longrightarrow> open_ball(X,x,a) \<subseteq> open_ball(X,y,b)"
@proof
  @have "\<forall>z\<in>open_ball(X,x,a). z \<in> open_ball(X,y,b)" @with
    @have "dist(X,y,z) \<le>\<^sub>\<real> dist(X,y,x) +\<^sub>\<real> dist(X,x,z)"
    @have "dist(X,y,z) <\<^sub>\<real> a +\<^sub>\<real> dist(X,y,x)" @end
@qed

section \<open>Metric topology\<close>
  
definition metric_basis :: "i \<Rightarrow> i" where [rewrite]:
  "metric_basis(X) = (\<Union>x\<in>.X. \<Union>a\<in>.\<real>. {open_ball(X,x,a)})"

lemma metric_basisE [backward]:
  "U \<in> metric_basis(X) \<Longrightarrow> \<exists>x\<in>.X. \<exists>a\<in>.\<real>. U = open_ball(X,x,a)" by auto2

lemma metric_basisI [resolve]:
  "x \<in>. X \<Longrightarrow> a \<in>. \<real> \<Longrightarrow> open_ball(X,x,a) \<in> metric_basis(X)" by auto2

lemma metric_basis_eq [rewrite]:
  "carrier(X) = carrier(Y) \<Longrightarrow> metric_fun(X) = metric_fun(Y) \<Longrightarrow>
   metric_basis(X) = metric_basis(Y)" by auto2

lemma metric_basis_union [rewrite]:
  "is_metric_space(X) \<Longrightarrow> \<Union>metric_basis(X) = carrier(X)"
@proof
  @have "\<forall>x\<in>.X. x \<in> \<Union>metric_basis(X)" @with
    @have "x \<in> open_ball(X,x,1\<^sub>\<real>)" @end
@qed
setup {* del_prfstep_thm @{thm metric_basis_def} *}

lemma metric_basis_is_basis [forward]:
  "is_metric_space(X) \<Longrightarrow> collection_is_basis(metric_basis(X))"
@proof
  @let "B = metric_basis(X)"
  @have "\<forall>U\<in>B. \<forall>V\<in>B. \<forall>w\<in>U\<inter>V. \<exists>W\<in>B. w\<in>W \<and> W\<subseteq>U\<inter>V" @with
    @obtain "x\<in>.X" "a\<in>.\<real>" where "U = open_ball(X,x,a)"
    @obtain "y\<in>.X" "b\<in>.\<real>" where "V = open_ball(X,y,b)"
    @have "dist(X,w,x) <\<^sub>\<real> a"
    @have "dist(X,w,y) <\<^sub>\<real> b"
    @let "c = min(\<real>, a -\<^sub>\<real> dist(X,w,x), b -\<^sub>\<real> dist(X,w,y))"
    @have "c >\<^sub>\<real> 0\<^sub>\<real>" @with @have "a -\<^sub>\<real> dist(X,w,x) >\<^sub>\<real> 0\<^sub>\<real>" @end
    @let "W = open_ball(X,w,c)"
    @have "w \<in> W"
    @have "W \<subseteq> U" @with @have "c \<le>\<^sub>\<real> a -\<^sub>\<real> dist(X,w,x)" @end
    @have "W \<subseteq> V" @with @have "c \<le>\<^sub>\<real> b -\<^sub>\<real> dist(X,w,y)" @end
  @end
@qed

definition metric_top_space :: "i \<Rightarrow> i" where [rewrite]:
  "metric_top_space(X) = Struct({\<langle>carrier_name,carrier(X)\<rangle>,
    \<langle>open_sets_name,top_from_basis(metric_basis(X))\<rangle>, \<langle>metric_fun_name,metric_fun(X)\<rangle>})"

lemma metric_top_spaceD [rewrite]:
  "carrier(metric_top_space(X)) = carrier(X)"
  "open_sets(metric_top_space(X)) = top_from_basis(metric_basis(X))"
  "metric_fun(metric_top_space(X)) = metric_fun(X)"
  "A = metric_top_space(X) \<Longrightarrow> x \<in>. A \<Longrightarrow> y \<in>. A \<Longrightarrow> dist(A,x,y) = dist(X,x,y)" by auto2+
setup {* del_prfstep_thm @{thm metric_top_space_def} *}

lemma metric_top_space_is_metric [forward]:
  "is_metric_space(A) \<Longrightarrow> is_metric_space(metric_top_space(A))" by auto2

lemma metric_top_space_is_topology [forward]:
  "is_metric_space(A) \<Longrightarrow> is_top_space(metric_top_space(A))"
@proof
  @let "B = metric_basis(A)" "X = metric_top_space(A)"
  @have "collection_is_basis(B)"
  @have "open_sets(X) = top_from_basis(B)"
  @have "top_has_basis(X,B)"
@qed

definition is_metric_top_space :: "i \<Rightarrow> o" where [rewrite]:
  "is_metric_top_space(X) \<longleftrightarrow> (is_metric_space(X) \<and> is_top_space(X) \<and>
    open_sets(X) = top_from_basis(metric_basis(X)))"

lemma metric_top_space_is_metric_top [forward]:
  "is_metric_space(A) \<Longrightarrow> is_metric_top_space(metric_top_space(A))"
@proof @have "carrier(A) = carrier(metric_top_space(A))" @qed

lemma metric_top_space_open:
  "is_metric_top_space(X) \<Longrightarrow> U \<subseteq> carrier(X) \<Longrightarrow>
   is_open(X,U) \<longleftrightarrow> (\<forall>x\<in>U. \<exists>a>\<^sub>\<real>0\<^sub>\<real>. open_ball(X,x,a) \<subseteq> U)"
@proof
  @have "top_has_basis(X,metric_basis(X))"
  @case "is_open(X,U)" @with
    @have "\<forall>x\<in>U. \<exists>a>\<^sub>\<real>0\<^sub>\<real>. open_ball(X,x,a) \<subseteq> U" @with
      @obtain "B\<in>metric_basis(X)" where "x \<in> B" "B \<subseteq> U"
      @obtain "y\<in>.X" "a\<in>.\<real>" where "B = open_ball(X,y,a)"
      @have "dist(X,x,y) <\<^sub>\<real> a"
      @have "open_ball(X,x,a -\<^sub>\<real> dist(X,x,y)) \<subseteq> open_ball(X,y,a)"
    @end
  @end
@qed

end
