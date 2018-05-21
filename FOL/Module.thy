theory Module
imports Int
begin

setup {* fold add_rewrite_rule [@{thm carrier_def}, @{thm plus_fun_def}, @{thm zero_def}] *}
setup {* add_rewrite_rule_bidir @{thm plus_def} *}
  
definition mod_ring :: "i \<Rightarrow> i" where [rewrite]:
  "mod_ring(M) = fst(snd(M))"

definition mtimes_fun :: "i \<Rightarrow> i" where [rewrite]:
  "mtimes_fun(M) = fst(snd(snd(snd(snd(snd(M))))))"

definition mtimes :: "[i, i, i] \<Rightarrow> i" where [rewrite_bidir]:
  "mtimes(M,a,x) = mtimes_fun(M)`\<langle>a,x\<rangle>"
abbreviation mtimes_notation ("(_/ \<bullet>\<^sub>_ _)" [70,70,71] 70) where "a \<bullet>\<^sub>M x \<equiv> mtimes(M,a,x)"
setup {* register_wellform_data ("a \<bullet>\<^sub>M x", ["x \<in>. M", "a \<in>. mod_ring(M)"]) *}

section {* Module structure *}
  
definition is_mod_raw :: "i \<Rightarrow> o" where [rewrite]:
  "is_mod_raw(M) \<longleftrightarrow> is_abgroup_raw(M) \<and> is_ring(mod_ring(M)) \<and>
      mtimes_fun(M) \<in> carrier(mod_ring(M)) \<times> carrier(M) \<rightarrow> carrier(M)"

lemma is_mod_rawI [backward]:
  "is_ring(R) \<Longrightarrow> z \<in> S \<Longrightarrow> p \<in> S \<times> S \<rightarrow> S \<Longrightarrow> f \<in> carrier(R) \<times> S \<rightarrow> S \<Longrightarrow>
   is_mod_raw(\<langle>S,R,x1,\<langle>z,p\<rangle>,x2,f,x3\<rangle>)" by auto2

lemma is_mod_rawD1 [forward]:
  "is_mod_raw(M) \<Longrightarrow> is_abgroup_raw(M)"
  "is_mod_raw(M) \<Longrightarrow> is_ring(mod_ring(M))" by auto2+

lemma is_mod_rawD2 [typing]:
  "is_mod_raw(M) \<Longrightarrow> mtimes_fun(M) \<in> carrier(mod_ring(M)) \<times> carrier(M) \<rightarrow> carrier(M)" by auto2
setup {* del_prfstep_thm @{thm is_mod_raw_def} *}

definition mod_form :: "i \<Rightarrow> o" where [rewrite]:
  "mod_form(M) \<longleftrightarrow> is_mod_raw(M) \<and> M = \<langle>carrier(M),mod_ring(M),\<emptyset>,\<langle>\<zero>\<^sub>M,plus_fun(M)\<rangle>,\<emptyset>,mtimes_fun(M),\<emptyset>\<rangle>"

lemma mod_form_to_raw [forward]: "mod_form(M) \<Longrightarrow> is_mod_raw(M)" by auto2

definition LMod :: "[i, i, i, i \<Rightarrow> i \<Rightarrow> i, i \<Rightarrow> i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "LMod(S,R,z,p,f) = \<langle>S,R,\<emptyset>,\<langle>z,\<lambda>x\<in>S\<times>S. p(fst(x),snd(x))\<in>S\<rangle>,\<emptyset>,\<lambda>x\<in>carrier(R)\<times>S. f(fst(x),snd(x))\<in>S,\<emptyset>\<rangle>"

definition mod_fun :: "i \<Rightarrow> i \<Rightarrow> [i \<Rightarrow> i \<Rightarrow> i] \<Rightarrow> o" where [rewrite]:
  "mod_fun(S,R,f) \<longleftrightarrow> (\<forall>x\<in>.R. \<forall>y\<in>S. f(x,y) \<in> S)"

lemma mod_funD [typing]: "mod_fun(S,R,f) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in> S \<Longrightarrow> f(x,y) \<in> S" by auto2
setup {* del_prfstep_thm_eqforward @{thm mod_fun_def} *}

lemma LMod_is_mod_form [backward]:
  "is_ring(R) \<Longrightarrow> z \<in> S \<Longrightarrow> binary_fun(S,p) \<Longrightarrow> mod_fun(S,R,f) \<Longrightarrow> mod_form(LMod(S,R,z,p,f))" by auto2

lemma mod_eval [rewrite]:
  "carrier(LMod(S,R,z,p,f)) = S"
  "mod_ring(LMod(S,R,z,p,f)) = R"
  "M = LMod(S,R,z,p,f) \<Longrightarrow> \<zero>\<^sub>M = z"
  "M = LMod(S,R,z,p,f) \<Longrightarrow> x \<in>. M \<Longrightarrow> y \<in>. M \<Longrightarrow> is_mod_raw(M) \<Longrightarrow> x +\<^sub>M y = p(x,y)"
  "M = LMod(S,R,z,p,f) \<Longrightarrow> a \<in>. R \<Longrightarrow> x \<in>. M \<Longrightarrow> is_mod_raw(M) \<Longrightarrow> a \<bullet>\<^sub>M x = f(a,x)" by auto2+
setup {* del_prfstep_thm @{thm LMod_def} *}

(* Equality between left modules *)
definition eq_str_mod :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "eq_str_mod(M,N) \<longleftrightarrow> eq_str_abgroup(M,N) \<and> mod_ring(M) = mod_ring(N) \<and> (\<forall>a\<in>.mod_ring(M). \<forall>x\<in>.M. a \<bullet>\<^sub>M x = a \<bullet>\<^sub>N x)"

lemma eq_str_modD1 [forward]:
  "eq_str_mod(M,N) \<Longrightarrow> eq_str_abgroup(M,N)" by auto2

lemma eq_str_modD2 [rewrite]:
  "eq_str_mod(M,N) \<Longrightarrow> mod_ring(M) = mod_ring(N)"
  "a \<in>. mod_ring(M) \<Longrightarrow> x \<in>. M \<Longrightarrow> eq_str_mod(M,N) \<Longrightarrow> a \<bullet>\<^sub>M x = a \<bullet>\<^sub>N x" by auto2+

lemma eq_str_mod_sym [forward]:
  "eq_str_mod(M,N) \<Longrightarrow> eq_str_mod(N,M)" by auto2
setup {* del_prfstep_thm_eqforward @{thm eq_str_mod_def} *}

lemma mod_eq [backward]:
  "mod_form(M) \<Longrightarrow> mod_form(N) \<Longrightarrow> eq_str_mod(M,N) \<Longrightarrow> M = N" by auto2
setup {* del_prfstep_thm @{thm mod_form_def} *}

setup {* fold del_prfstep_thm [@{thm carrier_def}, @{thm plus_fun_def}, @{thm zero_def}] *}
setup {* del_prfstep_thm @{thm plus_def} *}

section {* Definition of a module *}
  
definition is_mod :: "i \<Rightarrow> o" where [rewrite]:
  "is_mod(M) \<longleftrightarrow> (let R = mod_ring(M) in
    is_ring(R) \<and> is_abgroup(M) \<and>
    (\<forall>a\<in>.R. \<forall>b\<in>.R. \<forall>x\<in>.M. (a +\<^sub>R b) \<bullet>\<^sub>M x = a \<bullet>\<^sub>M x +\<^sub>M b \<bullet>\<^sub>M x) \<and>
    (\<forall>a\<in>.R. \<forall>x\<in>.M. \<forall>y\<in>.M. a \<bullet>\<^sub>M (x +\<^sub>M y) = a \<bullet>\<^sub>M x +\<^sub>M a \<bullet>\<^sub>M y) \<and>
    (\<forall>a\<in>.R. \<forall>b\<in>.R. \<forall>x\<in>.M. (a *\<^sub>R b) \<bullet>\<^sub>M x = a \<bullet>\<^sub>M (b \<bullet>\<^sub>M x)) \<and>
    (\<forall>x\<in>.M. \<one>\<^sub>R \<bullet>\<^sub>M x = x))"

lemma is_modD1 [forward]:
  "is_mod(M) \<Longrightarrow> is_ring(mod_ring(M))"
  "is_mod(M) \<Longrightarrow> is_abgroup(M)" by auto2+

lemma is_modD2 [rewrite]:
  "is_mod(M) \<Longrightarrow> R = mod_ring(M) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> x \<in>. M \<Longrightarrow> (a +\<^sub>R b) \<bullet>\<^sub>M x = a \<bullet>\<^sub>M x +\<^sub>M b \<bullet>\<^sub>M x"
  "is_mod(M) \<Longrightarrow> R = mod_ring(M) \<Longrightarrow> a \<in>. R \<Longrightarrow> x \<in>. M \<Longrightarrow> y \<in>. M \<Longrightarrow> a \<bullet>\<^sub>M (x +\<^sub>M y) = a \<bullet>\<^sub>M x +\<^sub>M a \<bullet>\<^sub>M y"
  "is_mod(M) \<Longrightarrow> R = mod_ring(M) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> x \<in>. M \<Longrightarrow> (a *\<^sub>R b) \<bullet>\<^sub>M x = a \<bullet>\<^sub>M (b \<bullet>\<^sub>M x)"
  "is_mod(M) \<Longrightarrow> R = mod_ring(M) \<Longrightarrow> x \<in>. M \<Longrightarrow> \<one>\<^sub>R \<bullet>\<^sub>M x = x"
  by auto2+
setup {* del_prfstep_thm_eqforward @{thm is_mod_def} *}

section {* Every abelian group is a module *}

definition mod_of_abgroup :: "i \<Rightarrow> i" where [rewrite]:
  "mod_of_abgroup(R) = LMod(carrier(R),\<int>,\<zero>\<^sub>R, \<lambda>x y. x +\<^sub>R y, \<lambda>a x. int_act(R,a,x))"

lemma mod_of_abgroup_is_mod [forward]:
  "is_abgroup(R) \<Longrightarrow> mod_form(mod_of_abgroup(R))" by auto2

lemma mod_of_abgroup_eval [rewrite]:
  "carrier(mod_of_abgroup(R)) = carrier(R)"
  "mod_ring(mod_of_abgroup(R)) = \<int>"
  "is_abgroup(R) \<Longrightarrow> M = mod_of_abgroup(R) \<Longrightarrow> \<zero>\<^sub>M = \<zero>\<^sub>R"
  "is_abgroup(R) \<Longrightarrow> M = mod_of_abgroup(R) \<Longrightarrow> x \<in>. M \<Longrightarrow> y \<in>. M \<Longrightarrow> x +\<^sub>M y = x +\<^sub>R y"
  "is_abgroup(R) \<Longrightarrow> M = mod_of_abgroup(R) \<Longrightarrow> a \<in>. mod_ring(M) \<Longrightarrow> x \<in>. M \<Longrightarrow> a \<bullet>\<^sub>M x = int_act(R,a,x)" by auto2+
setup {* del_prfstep_thm @{thm mod_of_abgroup_def} *}

lemma mod_of_abgroup_is_module [forward]:
  "is_abgroup(R) \<Longrightarrow> is_mod(mod_of_abgroup(R))"
@proof @have "eq_str_abgroup(mod_of_abgroup(R),R)" @qed

end
