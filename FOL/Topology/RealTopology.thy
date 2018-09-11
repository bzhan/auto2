(*
  File: RealTopology.thy
  Author: Bohua Zhan

  Topology on real numbers.
*)

theory RealTopology
  imports Real Connected
begin

section {* Open intervals *}
  
lemma open_interval_to_abs [rewrite]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> a \<in>. R \<Longrightarrow> y \<in> open_interval(R,x -\<^sub>R a, x +\<^sub>R a) \<longleftrightarrow> (y \<in>. R \<and> \<bar>y -\<^sub>R x\<bar>\<^sub>R <\<^sub>R a)"
@proof
  @contradiction
  @have "y -\<^sub>R x <\<^sub>R a" @have "y -\<^sub>R x >\<^sub>R -\<^sub>R a"
@qed
      
section {* Topology on real numbers *}

lemma real_topology_is_openD [backward]:
  "is_open(\<real>,U) \<Longrightarrow> x \<in> U \<Longrightarrow> \<exists>c>\<^sub>\<real>\<zero>\<^sub>\<real>. \<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> c \<longrightarrow> y \<in> U"
@proof
  @obtain a b where "x \<in> open_interval(\<real>,a,b)" "open_interval(\<real>,a,b) \<subseteq> U"
  @have "x -\<^sub>\<real> a >\<^sub>\<real> \<zero>\<^sub>\<real>"
  @obtain c where "c >\<^sub>\<real> \<zero>\<^sub>\<real>" "c <\<^sub>\<real> min(\<real>, x -\<^sub>\<real> a, b -\<^sub>\<real> x)"
  @have "open_interval(\<real>, x -\<^sub>\<real> c, x +\<^sub>\<real> c) \<subseteq> open_interval(\<real>,a,b)"
  @have "\<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> c \<longrightarrow> y \<in> U" @with
    @have "y \<in> open_interval(\<real>, x -\<^sub>\<real> c, x +\<^sub>\<real> c)" @end
@qed

lemma real_topology_is_openD_less [backward]:
  "is_open(\<real>,U) \<Longrightarrow> x \<in> U \<Longrightarrow> d >\<^sub>\<real> \<zero>\<^sub>\<real> \<Longrightarrow> \<exists>c>\<^sub>\<real>\<zero>\<^sub>\<real>. c \<le>\<^sub>\<real> d \<and> (\<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> c \<longrightarrow> y \<in> U)"
@proof
  @obtain c where "c >\<^sub>\<real> \<zero>\<^sub>\<real>" "\<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> c \<longrightarrow> y \<in> U"
  @have "\<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> min(\<real>,c,d) \<longrightarrow> y \<in> U"
@qed

lemma real_topology_is_openI [forward]:
  "U \<subseteq> real \<Longrightarrow> \<forall>x\<in>U. \<exists>c>\<^sub>\<real>\<zero>\<^sub>\<real>. \<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> c \<longrightarrow> y \<in> U \<Longrightarrow> is_open(\<real>,U)"
@proof
  @have "\<forall>x\<in>U. \<exists>a b. x \<in> open_interval(\<real>,a,b) \<and> open_interval(\<real>,a,b) \<subseteq> U" @with
    @obtain c where "c >\<^sub>\<real> \<zero>\<^sub>\<real>" "\<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> c \<longrightarrow> y \<in> U"
    @have "x \<in> open_interval(\<real>,x -\<^sub>\<real> c, x +\<^sub>\<real> c)"
    @have "\<forall>y\<in>open_interval(\<real>,x -\<^sub>\<real> c, x +\<^sub>\<real> c). y \<in> U" @end
@qed

section {* Topology on \<real> \<times> \<real> *}

definition real2 :: i where [rewrite_bidir]:
  "real2 = real \<times> real"

definition real2_topology :: i  ("\<real>\<^sup>2") where [rewrite]:
  "\<real>\<^sup>2 = \<real> \<times>\<^sub>T \<real>"

lemma real2_topology_type [typing]: "\<real>\<^sup>2 \<in> raw_top_spaces(real2)" by auto2
lemma real2_topology_is_top_space [forward]: "is_top_space(\<real>\<^sup>2)" by auto2

abbreviation real2_dist_bound :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o" where
  "real2_dist_bound(x,y,c) \<equiv> \<bar>fst(y) -\<^sub>\<real> fst(x)\<bar>\<^sub>\<real> <\<^sub>\<real> c \<and> \<bar>snd(y) -\<^sub>\<real> snd(x)\<bar>\<^sub>\<real> <\<^sub>\<real> c"

lemma real2_topology_is_openI [forward]:
  "U \<subseteq> real2 \<Longrightarrow> \<forall>x\<in>U. \<exists>c>\<^sub>\<real>\<zero>\<^sub>\<real>. \<forall>y\<in>.\<real>\<^sup>2. real2_dist_bound(x,y,c) \<longrightarrow> y \<in> U \<Longrightarrow> is_open(\<real>\<^sup>2, U)"
@proof
  @have "\<forall>x\<in>U. \<exists>V W. is_open(\<real>,V) \<and> is_open(\<real>,W) \<and> x \<in>V\<times>W \<and> V\<times>W \<subseteq> U" @with
    @obtain c where "c >\<^sub>\<real> \<zero>\<^sub>\<real>" "\<forall>y\<in>.\<real>\<^sup>2. real2_dist_bound(x,y,c) \<longrightarrow> y \<in> U"
    @let "V = open_interval(\<real>, fst(x) -\<^sub>\<real> c, fst(x) +\<^sub>\<real> c)"
    @let "W = open_interval(\<real>, snd(x) -\<^sub>\<real> c, snd(x) +\<^sub>\<real> c)"
    @have "\<forall>y\<in>V \<times> W. y \<in> U" @with @have "real2_dist_bound(x,y,c)" @end
    @have "is_open(\<real>,V)" @have "is_open(\<real>,W)" @end
@qed

lemma real2_topology_is_openD [backward]:
  "is_open(\<real>\<^sup>2, U) \<Longrightarrow> x \<in> U \<Longrightarrow> \<exists>c>\<^sub>\<real>\<zero>\<^sub>\<real>. \<forall>y\<in>.\<real>\<^sup>2. real2_dist_bound(x,y,c) \<longrightarrow> y \<in> U"
@proof
  @obtain V W where "is_open(\<real>,V)" "is_open(\<real>,W)" "x \<in> V\<times>W" "V\<times>W \<subseteq> U"
  @obtain c' where "c' >\<^sub>\<real> \<zero>\<^sub>\<real>" "\<forall>y1\<in>.\<real>. \<bar>y1 -\<^sub>\<real> fst(x)\<bar>\<^sub>\<real> <\<^sub>\<real> c' \<longrightarrow> y1 \<in> V"
  @obtain c where "c >\<^sub>\<real> \<zero>\<^sub>\<real>" "c \<le>\<^sub>\<real> c'" "\<forall>y2\<in>.\<real>. \<bar>y2 -\<^sub>\<real> snd(x)\<bar>\<^sub>\<real> <\<^sub>\<real> c \<longrightarrow> y2 \<in> W"
  @have "\<forall>y\<in>.\<real>\<^sup>2. real2_dist_bound(x,y,c) \<longrightarrow> y \<in> U" @with
    @have "\<bar>fst(y) -\<^sub>\<real> fst(x)\<bar>\<^sub>\<real> <\<^sub>\<real> c'" @have "y \<in> V \<times> W" @end
@qed
setup {* del_prfstep_thm @{thm real2_topology_def} *}
setup {* add_rewrite_rule_back @{thm real2_topology_def} *}

section {* Continuous maps on the reals *}
  
definition real_fun :: "i \<Rightarrow> o" where [rewrite]:
  "real_fun(f) \<longleftrightarrow> (f \<in> \<real> \<rightharpoonup> \<real>)"

definition real_continuous_at :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "real_continuous_at(f,x) \<longleftrightarrow> (\<forall>c>\<^sub>\<real>\<zero>\<^sub>\<real>. \<exists>d>\<^sub>\<real>\<zero>\<^sub>\<real>. \<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> d \<longrightarrow> \<bar>f`y -\<^sub>\<real> f`x\<bar>\<^sub>\<real> <\<^sub>\<real> c)"
setup {* register_wellform_data ("real_continuous_at(f,x)", ["x \<in>. \<real>"]) *}

lemma real_continuous_atD [backward2]:
  "real_continuous_at(f,x) \<Longrightarrow> c >\<^sub>\<real> \<zero>\<^sub>\<real> \<Longrightarrow> \<exists>d>\<^sub>\<real>\<zero>\<^sub>\<real>. \<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> d \<longrightarrow> \<bar>f`y -\<^sub>\<real> f`x\<bar>\<^sub>\<real> <\<^sub>\<real> c" by auto2
    
lemma real_continuous_atI [forward]:
  "\<forall>c>\<^sub>\<real>\<zero>\<^sub>\<real>. \<exists>d>\<^sub>\<real>\<zero>\<^sub>\<real>. \<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> d \<longrightarrow> \<bar>f`y -\<^sub>\<real> f`x\<bar>\<^sub>\<real> <\<^sub>\<real> c \<Longrightarrow> real_continuous_at(f,x)" by auto2
setup {* del_prfstep_thm @{thm real_continuous_at_def} *}

lemma real_fun_continuousI [forward]:
  "real_fun(f) \<Longrightarrow> \<forall>x\<in>.\<real>. real_continuous_at(f,x) \<Longrightarrow> continuous(f)"
@proof
  @have "\<forall>V\<in>open_sets(\<real>). is_open(\<real>, f -`` V)" @with
    @let "U = f -`` V" @have "U \<subseteq> real"
    @have "\<forall>x\<in>U. (\<exists>d>\<^sub>\<real>\<zero>\<^sub>\<real>. \<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> d \<longrightarrow> y \<in> U)" @with
      @obtain c where "c >\<^sub>\<real> \<zero>\<^sub>\<real>" "\<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> f`x\<bar>\<^sub>\<real> <\<^sub>\<real> c \<longrightarrow> y \<in> V"
      @obtain d where "d >\<^sub>\<real> \<zero>\<^sub>\<real>" "\<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> d \<longrightarrow> \<bar>f`y -\<^sub>\<real> f`x\<bar>\<^sub>\<real> <\<^sub>\<real> c"
      @have "\<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> d \<longrightarrow> y \<in> U" @with @have "f`y \<in> V" @end
    @end
  @end
@qed
      
lemma real_fun_continuousD [resolve]:
  "real_fun(f) \<Longrightarrow> continuous(f) \<Longrightarrow> x \<in>. \<real> \<Longrightarrow> real_continuous_at(f,x)"
@proof
  @have "\<forall>c>\<^sub>\<real>\<zero>\<^sub>\<real>. \<exists>d>\<^sub>\<real>\<zero>\<^sub>\<real>. \<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> d \<longrightarrow> \<bar>f`y -\<^sub>\<real> f`x\<bar>\<^sub>\<real> <\<^sub>\<real> c" @with
    @let "V = open_interval(\<real>, f`x -\<^sub>\<real> c, f`x +\<^sub>\<real> c)"
    @obtain d where "d >\<^sub>\<real> \<zero>\<^sub>\<real>" "\<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> d \<longrightarrow> y \<in> f -`` V"
    @have "\<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> d \<longrightarrow> \<bar>f`y -\<^sub>\<real> f`x\<bar>\<^sub>\<real> <\<^sub>\<real> c" @with @have "f`y \<in> V" @end
  @end
@qed

lemma real_fun_continuousD' [backward]:
  "real_fun(f) \<Longrightarrow> continuous(f) \<Longrightarrow> x \<in>. \<real> \<Longrightarrow> c >\<^sub>\<real> \<zero>\<^sub>\<real> \<Longrightarrow>
   \<exists>d>\<^sub>\<real>\<zero>\<^sub>\<real>. \<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> d \<longrightarrow> \<bar>f`y -\<^sub>\<real> f`x\<bar>\<^sub>\<real> <\<^sub>\<real> c"
@proof @have "real_continuous_at(f,x)" @qed

section {* Continuous maps from \<real> \<times> \<real> to \<real> *}

definition real2_continuous_at :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "real2_continuous_at(f,x) \<longleftrightarrow> (\<forall>c>\<^sub>\<real>\<zero>\<^sub>\<real>. \<exists>d>\<^sub>\<real>\<zero>\<^sub>\<real>. \<forall>y\<in>.\<real>\<^sup>2. real2_dist_bound(x,y,d) \<longrightarrow> \<bar>f`y -\<^sub>\<real> f`x\<bar>\<^sub>\<real> <\<^sub>\<real> c)"
setup {* register_wellform_data ("real2_continuous_at(f,x)", ["x \<in>. \<real>\<^sup>2"]) *}

lemma real2_continuous_atD [backward2]:
  "real2_continuous_at(f,x) \<Longrightarrow> c >\<^sub>\<real> \<zero>\<^sub>\<real> \<Longrightarrow>
   \<exists>d>\<^sub>\<real>\<zero>\<^sub>\<real>. \<forall>y\<in>.\<real>\<^sup>2. real2_dist_bound(x,y,d) \<longrightarrow> \<bar>f`y -\<^sub>\<real> f`x\<bar>\<^sub>\<real> <\<^sub>\<real> c" by auto2
  
lemma real2_continuous_atI [forward]:
  "\<forall>c>\<^sub>\<real>\<zero>\<^sub>\<real>. \<exists>d>\<^sub>\<real>\<zero>\<^sub>\<real>. \<forall>y\<in>.\<real>\<^sup>2. real2_dist_bound(x,y,d) \<longrightarrow> \<bar>f`y -\<^sub>\<real> f`x\<bar>\<^sub>\<real> <\<^sub>\<real> c \<Longrightarrow> real2_continuous_at(f,x)" by auto2
setup {* del_prfstep_thm @{thm real2_continuous_at_def} *}

lemma real2_fun_continuousI [forward]:
  "f \<in> \<real>\<^sup>2 \<rightharpoonup> \<real> \<Longrightarrow> \<forall>x\<in>.\<real>\<^sup>2. real2_continuous_at(f,x) \<Longrightarrow> continuous(f)"
@proof
  @have "\<forall>V\<in>open_sets(\<real>). is_open(\<real>\<^sup>2, f -`` V)" @with
    @let "U = f -`` V" @have "U \<subseteq> real2"
    @have "\<forall>x\<in>U. \<exists>d>\<^sub>\<real>\<zero>\<^sub>\<real>. \<forall>y\<in>.\<real>\<^sup>2. real2_dist_bound(x,y,d) \<longrightarrow> y \<in> U" @with
      @obtain c where "c >\<^sub>\<real> \<zero>\<^sub>\<real>" "\<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> f`x\<bar>\<^sub>\<real> <\<^sub>\<real> c \<longrightarrow> y \<in> V"
      @obtain d where "d >\<^sub>\<real> \<zero>\<^sub>\<real>" "\<forall>y\<in>.\<real>\<^sup>2. real2_dist_bound(x,y,d) \<longrightarrow> \<bar>f`y -\<^sub>\<real> f`x\<bar>\<^sub>\<real> <\<^sub>\<real> c"
      @have "\<forall>y\<in>.\<real>\<^sup>2. real2_dist_bound(x,y,d) \<longrightarrow> y \<in> U" @with @have "f`y \<in> V" @end
    @end
  @end
@qed

lemma real2_fun_continuousD [resolve]:
  "x \<in>. \<real>\<^sup>2 \<Longrightarrow> f \<in> \<real>\<^sup>2 \<rightharpoonup>\<^sub>T \<real> \<Longrightarrow> real2_continuous_at(f,x)"
@proof
  @have "\<forall>c>\<^sub>\<real>\<zero>\<^sub>\<real>. \<exists>d>\<^sub>\<real>\<zero>\<^sub>\<real>. \<forall>y\<in>.\<real>\<^sup>2. real2_dist_bound(x,y,d) \<longrightarrow> \<bar>f`y -\<^sub>\<real> f`x\<bar>\<^sub>\<real> <\<^sub>\<real> c" @with
    @let "V = open_interval(\<real>, f`x -\<^sub>\<real> c, f`x +\<^sub>\<real> c)"
    @obtain d where "d >\<^sub>\<real> \<zero>\<^sub>\<real>" "\<forall>y\<in>.\<real>\<^sup>2. real2_dist_bound(x,y,d) \<longrightarrow> y \<in> f -`` V"
    @have "\<forall>y\<in>.\<real>\<^sup>2. real2_dist_bound(x,y,d) \<longrightarrow> \<bar>f`y -\<^sub>\<real> f`x\<bar>\<^sub>\<real> <\<^sub>\<real> c" @with @have "f`y \<in> V" @end
  @end
@qed

section {* Continuity of addition and multiplication *}

definition real_add :: i where [rewrite]:
  "real_add = Mor(\<real>\<^sup>2, \<real>, \<lambda>\<langle>x,y\<rangle>. x +\<^sub>\<real> y)"

lemma real_add_type [typing]: "real_add \<in> \<real>\<^sup>2 \<rightharpoonup> \<real>" by auto2
lemma real_add_eval [rewrite]: "\<langle>x,y\<rangle> \<in> source(real_add) \<Longrightarrow> real_add`\<langle>x,y\<rangle> = x +\<^sub>\<real> y" by auto2
setup {* del_prfstep_thm @{thm real_add_def} *}

lemma real_add_continuous [forward]: "continuous(real_add)"
@proof
  @let "f = real_add"
  @have "\<forall>x\<in>.\<real>\<^sup>2. real2_continuous_at(f,x)" @with
    @have "\<forall>c>\<^sub>\<real>\<zero>\<^sub>\<real>. \<exists>d>\<^sub>\<real>\<zero>\<^sub>\<real>. \<forall>y\<in>.\<real>\<^sup>2. real2_dist_bound(x,y,d) \<longrightarrow> \<bar>f`y -\<^sub>\<real> f`x\<bar>\<^sub>\<real> <\<^sub>\<real> c" @with
      @obtain d where "d >\<^sub>\<real> \<zero>\<^sub>\<real>" "c = d +\<^sub>\<real> d"
      @have "\<forall>y\<in>.\<real>\<^sup>2. real2_dist_bound(x,y,d) \<longrightarrow> \<bar>f`y -\<^sub>\<real> f`x\<bar>\<^sub>\<real> <\<^sub>\<real> c" @with
        @have "fst(y) +\<^sub>\<real> snd(y) -\<^sub>\<real> (fst(x) +\<^sub>\<real> snd(x)) = fst(y) -\<^sub>\<real> fst(x) +\<^sub>\<real> (snd(y) -\<^sub>\<real> snd(x))" @end
    @end        
  @end
@qed

definition real_neg :: i where [rewrite]:
  "real_neg = Mor(\<real>, \<real>, \<lambda>x. -\<^sub>\<real> x)"
  
lemma real_neg_type [typing]: "real_neg \<in> \<real> \<rightharpoonup> \<real>" by auto2
lemma real_neg_eval [rewrite]: "x \<in> source(real_neg) \<Longrightarrow> real_neg`x = -\<^sub>\<real> x" by auto2
setup {* del_prfstep_thm @{thm real_neg_def} *}

lemma real_neg_continuous [forward]: "continuous(real_neg)"
@proof
  @let "f = real_neg"
  @have "real_fun(f)"
  @have "\<forall>x\<in>.\<real>. real_continuous_at(f,x)" @with
    @have "\<forall>c>\<^sub>\<real>\<zero>\<^sub>\<real>. \<exists>d>\<^sub>\<real>\<zero>\<^sub>\<real>. \<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> d \<longrightarrow> \<bar>f`y -\<^sub>\<real> f`x\<bar>\<^sub>\<real> <\<^sub>\<real> c" @with
      @have "\<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> c \<longrightarrow> \<bar>f`y -\<^sub>\<real> f`x\<bar>\<^sub>\<real> <\<^sub>\<real> c" @with
        @have "-\<^sub>\<real> y -\<^sub>\<real> (-\<^sub>\<real> x) = -\<^sub>\<real> (y -\<^sub>\<real> x)" @end
    @end
  @end
@qed

definition real_mult :: i where [rewrite]:
  "real_mult = Mor(\<real>\<^sup>2, \<real>, \<lambda>\<langle>x,y\<rangle>. x *\<^sub>\<real> y)"
  
lemma real_mult_type [typing]: "real_mult \<in> \<real>\<^sup>2 \<rightharpoonup> \<real>" by auto2
lemma real_mult_eval [rewrite]: "\<langle>x,y\<rangle> \<in> source(real_mult) \<Longrightarrow> real_mult`\<langle>x,y\<rangle> = x *\<^sub>\<real> y" by auto2
setup {* del_prfstep_thm @{thm real_mult_def} *}

lemma real_mult_continuous_aux [backward]:
  "x \<in>. \<real>\<^sup>2 \<Longrightarrow> c >\<^sub>\<real> \<zero>\<^sub>\<real> \<Longrightarrow> \<exists>d>\<^sub>\<real>\<zero>\<^sub>\<real>. \<forall>y\<in>.\<real>\<^sup>2. real2_dist_bound(x,y,d) \<longrightarrow> \<bar>real_mult`y -\<^sub>\<real> real_mult`x\<bar>\<^sub>\<real> <\<^sub>\<real> c"
@proof
  @let "x1 = fst(x)" "x2 = snd(x)"
  @have "\<bar>x1\<bar>\<^sub>\<real> +\<^sub>\<real> \<bar>x2\<bar>\<^sub>\<real> +\<^sub>\<real> 1\<^sub>\<real> >\<^sub>\<real> 0\<^sub>\<real>" @with
    @have "\<bar>x1\<bar>\<^sub>\<real> +\<^sub>\<real> \<bar>x2\<bar>\<^sub>\<real> \<ge>\<^sub>\<real> 0\<^sub>\<real>" @with @have "\<bar>x1\<bar>\<^sub>\<real> \<ge>\<^sub>\<real> 0\<^sub>\<real>" @end @end
  @have "min(\<real>,1\<^sub>\<real>,c /\<^sub>\<real> (\<bar>x1\<bar>\<^sub>\<real> +\<^sub>\<real> \<bar>x2\<bar>\<^sub>\<real> +\<^sub>\<real> 1\<^sub>\<real>)) >\<^sub>\<real> 0\<^sub>\<real>"
  @obtain d where "d >\<^sub>\<real> 0\<^sub>\<real>" "d <\<^sub>\<real> min(\<real>,1\<^sub>\<real>,c /\<^sub>\<real> (\<bar>x1\<bar>\<^sub>\<real> +\<^sub>\<real> \<bar>x2\<bar>\<^sub>\<real> +\<^sub>\<real> 1\<^sub>\<real>))"
  @have "\<forall>y\<in>.\<real>\<^sup>2. real2_dist_bound(x,y,d) \<longrightarrow> \<bar>real_mult`y -\<^sub>\<real> real_mult`x\<bar>\<^sub>\<real> <\<^sub>\<real> c" @with
    @let "y1 = fst(y)" "y2 = snd(y)"
    @have "c >\<^sub>\<real> d *\<^sub>\<real> (\<bar>x1\<bar>\<^sub>\<real> +\<^sub>\<real> \<bar>x2\<bar>\<^sub>\<real> +\<^sub>\<real> 1\<^sub>\<real>)"
    @have "c >\<^sub>\<real> (\<bar>x1\<bar>\<^sub>\<real> +\<^sub>\<real> 1\<^sub>\<real>) *\<^sub>\<real> d +\<^sub>\<real> d *\<^sub>\<real> \<bar>x2\<bar>\<^sub>\<real>"
    @have "y1 *\<^sub>\<real> y2 -\<^sub>\<real> x1 *\<^sub>\<real> x2 = y1 *\<^sub>\<real> (y2 -\<^sub>\<real> x2) +\<^sub>\<real> (y1 -\<^sub>\<real> x1) *\<^sub>\<real> x2"
    @have "\<bar>y1\<bar>\<^sub>\<real> <\<^sub>\<real> \<bar>x1\<bar>\<^sub>\<real> +\<^sub>\<real> d"
    @have "\<bar>y1 *\<^sub>\<real> (y2 -\<^sub>\<real> x2)\<bar>\<^sub>\<real> <\<^sub>\<real> (\<bar>x1\<bar>\<^sub>\<real> +\<^sub>\<real> 1\<^sub>\<real>) *\<^sub>\<real> d" @end
@qed

lemma real_mult_continuous [forward]: "continuous(real_mult)"
@proof
  @let "f = real_mult"
  @have "\<forall>x\<in>.\<real>\<^sup>2. real2_continuous_at(f,x)" @with
    @have "\<forall>c>\<^sub>\<real>\<zero>\<^sub>\<real>. \<exists>d>\<^sub>\<real>\<zero>\<^sub>\<real>. \<forall>y\<in>.\<real>\<^sup>2. real2_dist_bound(x,y,d) \<longrightarrow> \<bar>f`y -\<^sub>\<real> f`x\<bar>\<^sub>\<real> <\<^sub>\<real> c" @end
@qed
setup {* del_prfstep_thm @{thm real_mult_continuous_aux} *}

lemma real_add_fun_continuous [backward]:
  "F = Mor(X,\<real>,\<lambda>x. f(x)) \<Longrightarrow> G = Mor(X,\<real>,\<lambda>x. g(x)) \<Longrightarrow>
   F \<in> X \<rightharpoonup>\<^sub>T \<real> \<Longrightarrow> G \<in> X \<rightharpoonup>\<^sub>T \<real> \<Longrightarrow> continuous(Mor(X,\<real>,\<lambda>x. f(x) +\<^sub>\<real> g(x)))"
@proof
  @have (@rule) "\<forall>x\<in>.X. F`x = f(x) \<and> G`x = g(x)"
  @have "Mor(X, \<real>, \<lambda>x. f(x) +\<^sub>\<real> g(x)) = real_add \<circ>\<^sub>m prod_top_map(F,G) \<circ>\<^sub>m diag_top_map(X)"
@qed
      
lemma real_mult_fun_continuous [backward]:
  "F = Mor(X,\<real>,\<lambda>x. f(x)) \<Longrightarrow> G = Mor(X,\<real>,\<lambda>x. g(x)) \<Longrightarrow>
   F \<in> X \<rightharpoonup>\<^sub>T \<real> \<Longrightarrow> G \<in> X \<rightharpoonup>\<^sub>T \<real> \<Longrightarrow> continuous(Mor(X,\<real>,\<lambda>x. f(x) *\<^sub>\<real> g(x)))"
@proof
  @have (@rule) "\<forall>x\<in>.X. F`x = f(x) \<and> G`x = g(x)"
  @have "Mor(X,\<real>,\<lambda>x. f(x) *\<^sub>\<real> g(x)) = real_mult \<circ>\<^sub>m prod_top_map(F,G) \<circ>\<^sub>m diag_top_map(X)"
@qed
      
lemma real_neg_fun_continuous [backward]:
  "F = Mor(X,\<real>,\<lambda>x. f(x)) \<Longrightarrow> F \<in> X \<rightharpoonup>\<^sub>T \<real> \<Longrightarrow> continuous(Mor(X,\<real>,\<lambda>x. -\<^sub>\<real> f(x)))"
@proof
  @have (@rule) "\<forall>x\<in>.X. F`x = f(x)"
  @have "Mor(X, \<real>, \<lambda>x. -\<^sub>\<real> f(x)) = real_neg \<circ>\<^sub>m F"
@qed

lemma real_minus_fun_continuous [backward]:
  "F = Mor(X,\<real>,\<lambda>x. f(x)) \<Longrightarrow> G = Mor(X,\<real>,\<lambda>x. g(x)) \<Longrightarrow>
   F \<in> X \<rightharpoonup>\<^sub>T \<real> \<Longrightarrow> G \<in> X \<rightharpoonup>\<^sub>T \<real> \<Longrightarrow> continuous(Mor(X,\<real>,\<lambda>x. f(x) -\<^sub>\<real> g(x)))"
@proof
  @have (@rule) "\<forall>x\<in>.X. F`x = f(x) \<and> G`x = g(x)"
  @have "Mor(X, \<real>, \<lambda>x. f(x) -\<^sub>\<real> g(x)) = Mor(X, \<real>, \<lambda>x. f(x) +\<^sub>\<real> (-\<^sub>\<real> g(x)))"
@qed

lemma real_divide_const_continuous [backward]:
  "F = Mor(X,\<real>,\<lambda>x. f(x)) \<Longrightarrow> F \<in> X \<rightharpoonup>\<^sub>T \<real> \<Longrightarrow> c \<in> units(\<real>) \<Longrightarrow> continuous(Mor(X,\<real>,\<lambda>x. f(x) /\<^sub>\<real> c))"
@proof
  @have (@rule) "\<forall>x\<in>.X. F`x = f(x)"
  @have "Mor(X,\<real>,\<lambda>x. f(x) /\<^sub>\<real> c) = Mor(X,\<real>,\<lambda>x. f(x) *\<^sub>\<real> (1\<^sub>\<real> /\<^sub>\<real> c))"
@qed

section {* Continuity and convergent sequences *}
  
lemma continuous_on_converge_seq [backward]:
  "real_fun(f) \<Longrightarrow> continuous(f) \<Longrightarrow> X \<in> seqs(\<real>) \<Longrightarrow> converges_to(X,s) \<Longrightarrow>
   Y = Seq(\<real>,\<lambda>n. f`(X`n)) \<Longrightarrow> converges_to(Y,f`s)"
@proof
  @have "\<forall>r>\<^sub>\<real>\<zero>\<^sub>\<real>. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>Y`n -\<^sub>\<real> f`s\<bar>\<^sub>\<real> <\<^sub>\<real> r" @with
    @obtain d where "d >\<^sub>\<real> \<zero>\<^sub>\<real>" "\<forall>y\<in>.\<real>. \<bar>y -\<^sub>\<real> s\<bar>\<^sub>\<real> <\<^sub>\<real> d \<longrightarrow> \<bar>f`y -\<^sub>\<real> f`s\<bar>\<^sub>\<real> <\<^sub>\<real> r"
    @obtain "k \<in>. \<nat>" where "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>\<real> s\<bar>\<^sub>\<real> <\<^sub>\<real> d"
    @have "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>Y`n -\<^sub>\<real> f`s\<bar>\<^sub>\<real> <\<^sub>\<real> r"
  @end
@qed

section {* Intermediate value theorem *}

lemma real_connected [forward]: "connected(\<real>)" by auto2

lemma real_connected_interval [resolve]:
  "a <\<^sub>\<real> b \<Longrightarrow> connected_subset(\<real>,closed_interval(\<real>,a,b))"
@proof
  @let "I = closed_interval(\<real>,a,b)"
  @let "A = ord_subspace(\<real>,I)" "B = suborder(\<real>,I)" "C = subspace(\<real>,I)"
  @have "linear_continuum(A)" @with @have "eq_str_order(A,B)" @end
  @have "eq_str_top(C,A)"
@qed

lemma intermediate_value_theorem [backward1]:
  "real_fun(f) \<Longrightarrow> continuous(f) \<Longrightarrow> a <\<^sub>\<real> b \<Longrightarrow> y \<in> closed_interval(\<real>,f`a,f`b) \<Longrightarrow>
   \<exists>x\<in>closed_interval(\<real>,a,b). f`x = y"
@proof
  @let "I = closed_interval(\<real>,a,b)"
  @have "connected_subset(\<real>,f``I)"
  @have "order_convex(\<real>,f``I)"
  @have "closed_interval(\<real>,f`a,f`b) \<subseteq> f``I"
@qed

section {* Rempe-Gillen's challenge *}

definition incr_arg_fun :: "i \<Rightarrow> o" where [rewrite]:
  "incr_arg_fun(f) \<longleftrightarrow> (let S = source_str(f) in \<forall>x\<in>.S. f`x >\<^sub>S x)"
  
lemma incr_arg_funD:
  "incr_arg_fun(f) \<Longrightarrow> is_morphism(f) \<Longrightarrow> S = source_str(f) \<Longrightarrow> x \<in> source(f) \<Longrightarrow> f`x >\<^sub>S x" by auto2
setup {* add_forward_prfstep_cond @{thm incr_arg_funD} [with_term "?f`?x"] *}
setup {* del_prfstep_thm_eqforward @{thm incr_arg_fun_def} *}

lemma rempe_gillen_challenge:
  "real_fun(f) \<Longrightarrow> continuous(f) \<Longrightarrow> incr_arg_fun(f) \<Longrightarrow> x0 \<in>. \<real> \<Longrightarrow>
   S = Seq(\<real>,\<lambda>n. nfold(f,n,x0)) \<Longrightarrow> \<not>upper_bounded(S)"
@proof
  @contradiction
  @have "seq_incr(S)" @with @have "\<forall>n\<in>.\<nat>. S`(n +\<^sub>\<nat> 1) \<ge>\<^sub>\<real> S`n" @end
  @obtain x where "converges_to(S,x)"
  @let "T = Seq(\<real>,\<lambda>n. f`(S`n))"
  @have "converges_to(T,f`x)"
  @have "converges_to(T,x)" @with
    @have "\<forall>r>\<^sub>\<real>\<zero>\<^sub>\<real>. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>T`n -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> r" @with
      @obtain "k \<in>. \<nat>" where "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>S`n -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> r"
      @have "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>T`n -\<^sub>\<real> x\<bar>\<^sub>\<real> <\<^sub>\<real> r" @with @have "T`n = S`(n +\<^sub>\<nat> 1)" @end @end
  @end
@qed

end
