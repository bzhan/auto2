theory AbGroup
imports AlgStructure
begin

section {* Monoids *}

definition is_ab_monoid :: "i \<Rightarrow> o" where [rewrite]:
  "is_ab_monoid(G) \<longleftrightarrow> (is_abgroup_raw(G) \<and> is_add_id(G) \<and> is_plus_comm(G) \<and> is_plus_assoc(G))"
setup {* add_property_const @{term is_ab_monoid} *}
  
lemma is_ab_monoidD [forward]:
  "is_ab_monoid(G) \<Longrightarrow> is_abgroup_raw(G)"
  "is_ab_monoid(G) \<Longrightarrow> is_add_id(G)"
  "is_ab_monoid(G) \<Longrightarrow> is_plus_comm(G)"
  "is_ab_monoid(G) \<Longrightarrow> is_plus_assoc(G)" by auto2+
setup {* del_prfstep_thm_eqforward @{thm is_ab_monoid_def} *}
  
lemma is_ab_monoid_abgroup_prop [forward]:
  "is_abgroup_raw(H) \<Longrightarrow> is_ab_monoid(G) \<Longrightarrow> eq_str_abgroup(G,H) \<Longrightarrow> is_ab_monoid(H)" by auto2

section {* Abelian groups *}
  
definition has_add_inverse :: "i \<Rightarrow> o" where [rewrite]:
  "has_add_inverse(G) \<longleftrightarrow> (\<forall>x\<in>.G. \<exists>y\<in>.G. x +\<^sub>G y = \<zero>\<^sub>G)"
setup {* add_property_const @{term "has_add_inverse"} *}
  
lemma has_add_inverseD [backward]:
  "has_add_inverse(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> \<exists>y\<in>.G. x +\<^sub>G y = \<zero>\<^sub>G" by auto2

lemma has_add_inverseI [backward1]:
  "unary_fun(carrier(G),f) \<Longrightarrow> \<forall>x\<in>.G. x +\<^sub>G f(x) = \<zero>\<^sub>G \<Longrightarrow> has_add_inverse(G)" by auto2    
setup {* del_prfstep_thm @{thm has_add_inverse_def} *}

lemma has_add_inverse_abgroup_prop [forward]:
  "is_abgroup_raw(H) \<Longrightarrow> has_add_inverse(G) \<Longrightarrow> eq_str_abgroup(G,H) \<Longrightarrow> has_add_inverse(H)"
@proof @have "\<forall>x\<in>.H. x +\<^sub>H (SOME y\<in>.G. x +\<^sub>G y = \<zero>\<^sub>G) = \<zero>\<^sub>H" @qed

definition is_abgroup :: "i \<Rightarrow> o" where [rewrite]:
  "is_abgroup(G) \<longleftrightarrow> (is_ab_monoid(G) \<and> has_add_inverse(G))"
setup {* add_property_const @{term is_abgroup} *}

lemma is_abgroupD [forward]:
  "is_abgroup(G) \<Longrightarrow> is_ab_monoid(G)"
  "is_abgroup(G) \<Longrightarrow> has_add_inverse(G)" by auto2+
setup {* del_prfstep_thm_eqforward @{thm is_abgroup_def} *}
  
lemma is_abgroup_abgroup_prop [forward]:
  "is_abgroup_raw(H) \<Longrightarrow> is_abgroup(G) \<Longrightarrow> eq_str_abgroup(G,H) \<Longrightarrow> is_abgroup(H)" by auto2

section {* Negation and subtraction *}

setup {* fold add_rewrite_rule [@{thm plus_commD}, @{thm plus_assoc_left}] *}

lemma has_left_inverse [backward]:
  "is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> \<exists>y\<in>.G. y +\<^sub>G x = \<zero>\<^sub>G"
@proof @obtain "y\<in>.G" where "x +\<^sub>G y = \<zero>\<^sub>G" @qed

lemma add_cancel_left [forward]:
  "is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> z \<in>. G \<Longrightarrow> x +\<^sub>G y = x +\<^sub>G z \<Longrightarrow> y = z"
@proof @obtain "x'\<in>.G" where "x' +\<^sub>G x = \<zero>\<^sub>G" @then @have "x' +\<^sub>G (x +\<^sub>G y) = y" @qed
      
lemma add_cancel_right [forward]:
  "is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> z \<in>. G \<Longrightarrow> y +\<^sub>G x = z +\<^sub>G x \<Longrightarrow> y = z" by auto2

definition neg :: "i \<Rightarrow> i \<Rightarrow> i"  ("-\<^sub>_ _" [81,81] 80) where [rewrite]:
  "-\<^sub>G x = (THE y. y \<in>. G \<and> x +\<^sub>G y = \<zero>\<^sub>G)"
setup {* register_wellform_data ("-\<^sub>G x", ["x \<in>. G"]) *}

lemma abgroup_neg_type [typing]:
  "is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> -\<^sub>G x \<in>. G" by auto2
    
lemma abgroup_neg_left [rewrite]:
  "is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> -\<^sub>G x +\<^sub>G x = \<zero>\<^sub>G" by auto2

lemma abgroup_neg_right [rewrite]:
  "is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> x +\<^sub>G -\<^sub>G x = \<zero>\<^sub>G" by auto2

lemma abgroup_neg_unique [forward]:
  "is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> x +\<^sub>G -\<^sub>G y = \<zero>\<^sub>G \<Longrightarrow> x = y" by auto2

lemma abgroup_neg_eq [resolve]:
  "is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> x +\<^sub>G y = \<zero>\<^sub>G \<Longrightarrow> -\<^sub>G x = y"
  "is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> y +\<^sub>G x = \<zero>\<^sub>G \<Longrightarrow> -\<^sub>G x = y"
  "is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> x +\<^sub>G y = \<zero>\<^sub>G \<Longrightarrow> y = -\<^sub>G x"
  "is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> y +\<^sub>G x = \<zero>\<^sub>G \<Longrightarrow> y = -\<^sub>G x" by auto2+

lemma neg_abgroup_fun [rewrite]:
  "is_abgroup_raw(H) \<Longrightarrow> is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> eq_str_abgroup(G,H) \<Longrightarrow> -\<^sub>G x = -\<^sub>H x" by auto2

lemma abgroup_neg_zero [rewrite]:
  "is_abgroup(G) \<Longrightarrow> -\<^sub>G(\<zero>\<^sub>G) = \<zero>\<^sub>G" by auto2
    
lemma abgroup_neg_zero_back [forward]:
  "is_abgroup(G) \<Longrightarrow> a \<in>. G \<Longrightarrow> -\<^sub>G a = \<zero>\<^sub>G \<Longrightarrow> a = \<zero>\<^sub>G" by auto2

lemma abgroup_neg_neg [rewrite]:
  "is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> -\<^sub>G (-\<^sub>G x) = x" by auto2
setup {* del_prfstep_thm @{thm neg_def} *}

lemma abgroup_neg_distrib:
  "is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> -\<^sub>G (x +\<^sub>G y) = -\<^sub>G x +\<^sub>G -\<^sub>G y \<and> -\<^sub>G x \<in>. G \<and> -\<^sub>G y \<in>. G"
@proof @have "(x +\<^sub>G y) +\<^sub>G (-\<^sub>G x +\<^sub>G -\<^sub>G y) = \<zero>\<^sub>G" @qed
  
lemma abgroup_neg_distrib':
  "is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> -\<^sub>G x +\<^sub>G -\<^sub>G y = -\<^sub>G (x +\<^sub>G y) \<and> x +\<^sub>G y \<in>. G"
@proof @have "(x +\<^sub>G y) +\<^sub>G (-\<^sub>G x +\<^sub>G -\<^sub>G y) = \<zero>\<^sub>G" @qed
    
lemma abgroup_neg_inj [forward]: "is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> -\<^sub>G x = -\<^sub>G y \<Longrightarrow> x = y"
@proof @have "x = -\<^sub>G (-\<^sub>G x)" @qed

definition minus :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "minus(G,x,y) = (THE z. z \<in>. G \<and> z +\<^sub>G y = x)"
abbreviation minus_notation ("(_/ -\<^sub>_ _)" [65,65,66] 65) where "x -\<^sub>G y \<equiv> minus(G,x,y)"
setup {* register_wellform_data ("x -\<^sub>G y", ["x \<in>. G", "y \<in>. G"]) *}

lemma minusI:
  "z \<in>. G \<Longrightarrow> z +\<^sub>G y = x \<Longrightarrow> \<forall>z'\<in>.G. z' +\<^sub>G y = x \<longrightarrow> z' = z \<Longrightarrow> minus(G,x,y) = z" by auto2

lemma minus_exist [backward2]:
  "is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> \<exists>z\<in>.G. z +\<^sub>G y = x"
@proof @have "(x +\<^sub>G (-\<^sub>G y)) +\<^sub>G y = x" @qed

lemma minus_type [typing]:
  "is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> x -\<^sub>G y \<in>. G" by auto2

lemma minusD [rewrite]:
  "is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> x -\<^sub>G y = x +\<^sub>G -\<^sub>G y \<and> -\<^sub>G y \<in>. G" by auto2
setup {* del_prfstep_thm @{thm minus_def} *}

lemma minus_abgroup_fun [rewrite]:
  "is_abgroup_raw(H) \<Longrightarrow> is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow>
   eq_str_abgroup(G,H) \<Longrightarrow> x -\<^sub>G y = x -\<^sub>H y"
@proof @have "x -\<^sub>G y = x +\<^sub>G -\<^sub>G y" @qed

setup {* fold del_prfstep_thm [@{thm plus_commD}, @{thm plus_assoc_left}, @{thm minusD}] *}
ML_file "alg_abgroup.ML"

lemma minus_zero [rewrite]: "is_abgroup(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> a -\<^sub>R \<zero>\<^sub>R = a" by auto2

lemma minus_same_eq_zero [rewrite]:
  "is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> x -\<^sub>G x = \<zero>\<^sub>G" by auto2

lemma minus_eq_zero_same [forward]:
  "is_abgroup(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> x -\<^sub>G y = \<zero>\<^sub>G \<Longrightarrow> x = y"
@proof @have "x -\<^sub>G y = x +\<^sub>G -\<^sub>G y" @qed

section {* Subset of an abelian group *}
  
definition nonzero_elts :: "i \<Rightarrow> i" where [rewrite]:
  "nonzero_elts(R) = {x\<in>.R. x \<noteq> \<zero>\<^sub>R}"

lemma nonzero_eltsD [forward]: "x \<in> nonzero_elts(R) \<Longrightarrow> x \<in>. R \<and> x \<noteq> \<zero>\<^sub>R" by auto2
lemma nonzero_eltsI [backward2]: "x \<in>. R \<Longrightarrow> x \<noteq> \<zero>\<^sub>R \<Longrightarrow> x \<in> nonzero_elts(R)" by auto2

end
