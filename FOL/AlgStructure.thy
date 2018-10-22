(*
  File: AlgStructure.thy
  Author: Bohua Zhan

  Algebraic structures.
*)

theory AlgStructure
  imports Functions
begin

section \<open>Conversion from meta-function to set-theoretic functions\<close>

definition unary_fun :: "i \<Rightarrow> [i \<Rightarrow> i] \<Rightarrow> o" where [rewrite]:
  "unary_fun(S,f) \<longleftrightarrow> (\<forall>x\<in>S. f(x) \<in> S)"

lemma unary_funD [typing]: "unary_fun(S,f) \<Longrightarrow> x \<in> S \<Longrightarrow> f(x) \<in> S" by auto2
setup {* del_prfstep_thm_eqforward @{thm unary_fun_def} *}

definition binary_fun :: "i \<Rightarrow> [i \<Rightarrow> i \<Rightarrow> i] \<Rightarrow> o" where [rewrite]:
  "binary_fun(S,f) \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. f(x,y) \<in> S)"

lemma binary_funD [typing]: "binary_fun(S,f) \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> f(x,y) \<in> S" by auto2
setup {* del_prfstep_thm_eqforward @{thm binary_fun_def} *}

definition binary_fun_of :: "i \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> i) \<Rightarrow> i" where [rewrite]:
  "binary_fun_of(S,f) = Fun(S\<times>S, S, \<lambda>p. f(fst(p),snd(p)))"
setup {* register_wellform_data ("binary_fun_of(S,f)", ["binary_fun(S,f)"]) *}

lemma binary_fun_of_mem [typing]: "binary_fun(S,f) \<Longrightarrow> binary_fun_of(S,f) \<in> S \<times> S \<rightarrow> S" by auto2
lemma binary_fun_eval [rewrite]:
  "F = binary_fun_of(S,f) \<Longrightarrow> F \<in> S \<times> S \<rightarrow> S \<Longrightarrow> \<langle>x,y\<rangle> \<in> source(F) \<Longrightarrow> F`\<langle>x,y\<rangle> = f(x,y)" by auto2
setup {* del_prfstep_thm @{thm binary_fun_of_def} *}

section \<open>Components of an algebraic structure\<close>

(* 0 and +, for additive structures. *)
definition "zero_name = succ(succ(succ(\<emptyset>)))"
definition "zero(S) = graph_eval(S, zero_name)"
definition "plus_fun_name = succ(succ(succ(succ(\<emptyset>))))"
definition "plus_fun(S) = graph_eval(S, plus_fun_name)"
notation zero ("\<zero>\<^sub>_" [96] 95)
setup {* add_field_data (@{term zero_name}, @{term zero}) *}
setup {* add_field_data (@{term plus_fun_name}, @{term plus_fun}) *}

(* 1 and *, for multiplicative structures. *)
definition "one_name = succ(succ(succ(succ(succ(\<emptyset>)))))"
definition "one(S) = graph_eval(S, one_name)"
definition "times_fun_name = succ(succ(succ(succ(succ(succ(\<emptyset>))))))"
definition "times_fun(S) = graph_eval(S, times_fun_name)"
notation one ("\<one>\<^sub>_" [96] 95)
setup {* add_field_data (@{term one_name}, @{term one}) *}
setup {* add_field_data (@{term times_fun_name}, @{term times_fun}) *}

section \<open>Notation for plus and times.\<close>
  
definition plus :: "[i, i, i] \<Rightarrow> i" where [rewrite_bidir]:
  "plus(G,x,y) = plus_fun(G)`\<langle>x,y\<rangle>"
abbreviation plus_notation ("(_/ +\<^sub>_ _)" [65,65,66] 65) where "x +\<^sub>G y \<equiv> plus(G,x,y)"
setup {* register_wellform_data ("x +\<^sub>G y", ["x \<in>. G", "y \<in>. G"]) *}

definition times :: "[i, i, i] \<Rightarrow> i" where [rewrite_bidir]:
  "times(G,x,y) = times_fun(G)`\<langle>x,y\<rangle>"
abbreviation times_notation ("(_/ *\<^sub>_ _)" [70,70,71] 70) where "x *\<^sub>G y \<equiv> times(G,x,y)"
setup {* register_wellform_data ("x *\<^sub>G y", ["x \<in>. G", "y \<in>. G"]) *}

section \<open>Abelian group structure\<close>

definition is_abgroup_raw :: "i \<Rightarrow> o" where [rewrite]:
  "is_abgroup_raw(G) \<longleftrightarrow> \<zero>\<^sub>G \<in>. G \<and> plus_fun(G) \<in> carrier(G) \<times> carrier(G) \<rightarrow> carrier(G)"

lemma is_abgroup_rawD [typing]:
  "is_abgroup_raw(G) \<Longrightarrow> \<zero>\<^sub>G \<in>. G"
  "is_abgroup_raw(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> x +\<^sub>G y \<in>. G"
  "is_abgroup_raw(G) \<Longrightarrow> plus_fun(G) \<in> carrier(G) \<times> carrier(G) \<rightarrow> carrier(G)" by auto2+
setup {* del_prfstep_thm_eqforward @{thm is_abgroup_raw_def} *}  

(* General result on evaluation of plus. *)
lemma plus_eval_gen [rewrite]:
  "is_abgroup_raw(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow>
   plus_fun(R) = binary_fun_of(carrier(R),f) \<Longrightarrow> x +\<^sub>R y = f(x,y)" by auto2

definition abgroup_form :: "i \<Rightarrow> o" where [rewrite]:
  "abgroup_form(G) \<longleftrightarrow> is_abgroup_raw(G) \<and> is_func_graph(G,{carrier_name,zero_name,plus_fun_name})"

lemma abgroup_form_to_raw [forward]: "abgroup_form(G) \<Longrightarrow> is_abgroup_raw(G)" by auto2

definition AbGroup :: "[i, i, i \<Rightarrow> i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "AbGroup(S,z,f) = Struct({\<langle>carrier_name,S\<rangle>,\<langle>zero_name,z\<rangle>,\<langle>plus_fun_name, binary_fun_of(S,f)\<rangle>})"

lemma AbGroup_is_abgroup_raw [backward]:
  "z \<in> S \<Longrightarrow> binary_fun(S,f) \<Longrightarrow> abgroup_form(AbGroup(S,z,f))" by auto2

lemma abgroup_eval [rewrite]:
  "carrier(AbGroup(S,z,f)) = S"
  "zero(AbGroup(S,z,f)) = z"
  "G = AbGroup(S,z,f) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> is_abgroup_raw(G) \<Longrightarrow> x +\<^sub>G y = f(x,y)" by auto2+
setup {* del_prfstep_thm @{thm AbGroup_def} *}
  
(* Equality between abelian groups *)
definition eq_str_abgroup :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "eq_str_abgroup(G,H) \<longleftrightarrow> carrier(G) = carrier(H) \<and> \<zero>\<^sub>G = \<zero>\<^sub>H \<and> plus_fun(G) = plus_fun(H)"

lemma eq_str_abgroupD [rewrite]:
  "eq_str_abgroup(G,H) \<Longrightarrow> carrier(G) = carrier(H)"
  "eq_str_abgroup(G,H) \<Longrightarrow> \<zero>\<^sub>G = \<zero>\<^sub>H"
  "x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> eq_str_abgroup(G,H) \<Longrightarrow> x +\<^sub>G y = x +\<^sub>H y"
  "eq_str_abgroup(G,H) \<Longrightarrow> plus_fun(G) = plus_fun(H)" by auto2+
lemma eq_str_abgroup_sym [forward]: "eq_str_abgroup(G,H) \<Longrightarrow> eq_str_abgroup(H,G)" by auto2

lemma eq_str_abgroupI [backward]:
  "is_abgroup_raw(G) \<Longrightarrow> is_abgroup_raw(H) \<Longrightarrow>
   carrier(G) = carrier(H) \<Longrightarrow> \<zero>\<^sub>G = \<zero>\<^sub>H \<Longrightarrow> \<forall>x\<in>.G. \<forall>y\<in>.G. x +\<^sub>G y = x +\<^sub>H y \<Longrightarrow> eq_str_abgroup(G,H)" by auto2
setup {* del_prfstep_thm @{thm eq_str_abgroup_def} *}

lemma abgroup_eq [backward]:
  "abgroup_form(G) \<Longrightarrow> abgroup_form(H) \<Longrightarrow> eq_str_abgroup(G,H) \<Longrightarrow> G = H" by auto2
setup {* del_prfstep_thm @{thm abgroup_form_def} *}
setup {* del_prfstep_thm @{thm plus_def} *}

section \<open>Group structure\<close>

definition is_group_raw :: "i \<Rightarrow> o" where [rewrite]:
  "is_group_raw(G) \<longleftrightarrow> \<one>\<^sub>G \<in>. G \<and> times_fun(G) \<in> carrier(G) \<times> carrier(G) \<rightarrow> carrier(G)"

lemma is_group_rawD [typing]:
  "is_group_raw(G) \<Longrightarrow> \<one>\<^sub>G \<in>. G"
  "is_group_raw(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> x *\<^sub>G y \<in>. G"
  "is_group_raw(G) \<Longrightarrow> times_fun(G) \<in> carrier(G) \<times> carrier(G) \<rightarrow> carrier(G)" by auto2+
setup {* del_prfstep_thm_eqforward @{thm is_group_raw_def} *}

(* General result on evaluation of times. *)
lemma times_eval_gen [rewrite]:
  "is_group_raw(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow>
   times_fun(R) = binary_fun_of(carrier(R),f) \<Longrightarrow> x *\<^sub>R y = f(x,y)" by auto2

definition group_form :: "i \<Rightarrow> o" where [rewrite]:
  "group_form(G) \<longleftrightarrow> is_group_raw(G) \<and> is_func_graph(G,{carrier_name,one_name,times_fun_name})"
  
lemma group_form_to_raw [forward]: "group_form(G) \<Longrightarrow> is_group_raw(G)" by auto2

definition Group :: "[i, i, i \<Rightarrow> i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "Group(S,u,f) = Struct({\<langle>carrier_name,S\<rangle>, \<langle>one_name,u\<rangle>, \<langle>times_fun_name, binary_fun_of(S,f)\<rangle>})"

lemma Group_is_group_raw [backward]:
  "u \<in> S \<Longrightarrow> binary_fun(S,f) \<Longrightarrow> group_form(Group(S,u,f))" by auto2

lemma group_eval [rewrite]:
  "carrier(Group(S,u,f)) = S"
  "one(Group(S,u,f)) = u"
  "G = Group(S,u,f) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> is_group_raw(G) \<Longrightarrow> x *\<^sub>G y = f(x,y)" by auto2+
setup {* del_prfstep_thm @{thm Group_def} *}

(* Equality between groups *)
definition eq_str_group :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "eq_str_group(G,H) \<longleftrightarrow> carrier(G) = carrier(H) \<and> \<one>\<^sub>G = \<one>\<^sub>H \<and> times_fun(G) = times_fun(H)"
  
lemma eq_str_groupD [rewrite]:
  "eq_str_group(G,H) \<Longrightarrow> carrier(G) = carrier(H)"
  "eq_str_group(G,H) \<Longrightarrow> \<one>\<^sub>G = \<one>\<^sub>H"
  "x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> eq_str_group(G,H) \<Longrightarrow> x *\<^sub>G y = x *\<^sub>H y"
  "eq_str_group(G,H) \<Longrightarrow> times_fun(G) = times_fun(H)" by auto2+
lemma eq_str_group_sym [forward]: "eq_str_group(G,H) \<Longrightarrow> eq_str_group(H,G)" by auto2

lemma eq_str_groupI [backward]:
  "is_group_raw(G) \<Longrightarrow> is_group_raw(H) \<Longrightarrow> carrier(G) = carrier(H) \<Longrightarrow> \<one>\<^sub>G = \<one>\<^sub>H \<Longrightarrow>
   \<forall>x\<in>.G. \<forall>y\<in>.G. x *\<^sub>G y = x *\<^sub>H y \<Longrightarrow> eq_str_group(G,H)" by auto2
setup {* del_prfstep_thm @{thm eq_str_group_def} *}

lemma group_eq [backward]:
  "group_form(G) \<Longrightarrow> group_form(H) \<Longrightarrow> eq_str_group(G,H) \<Longrightarrow> G = H" by auto2
setup {* del_prfstep_thm @{thm group_form_def} *}
setup {* del_prfstep_thm @{thm times_def} *}

section \<open>Ring structure\<close>

definition is_ring_raw :: "i \<Rightarrow> o" where [rewrite]:
  "is_ring_raw(R) \<longleftrightarrow> is_abgroup_raw(R) \<and> is_group_raw(R)"

lemma is_ring_raw_iff [forward]:
  "is_ring_raw(R) \<Longrightarrow> is_abgroup_raw(R)"
  "is_ring_raw(R) \<Longrightarrow> is_group_raw(R)"
  "is_abgroup_raw(R) \<Longrightarrow> is_group_raw(R) \<Longrightarrow> is_ring_raw(R)" by auto2+
setup {* del_prfstep_thm @{thm is_ring_raw_def} *}

definition ring_form :: "i \<Rightarrow> o" where [rewrite]:
  "ring_form(R) \<longleftrightarrow>
    is_ring_raw(R) \<and> is_func_graph(R,{carrier_name,zero_name,plus_fun_name,one_name,times_fun_name})"
  
lemma ring_form_to_raw [forward]: "ring_form(R) \<Longrightarrow> is_ring_raw(R)" by auto2

definition Ring :: "[i, i, i \<Rightarrow> i \<Rightarrow> i, i, i \<Rightarrow> i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "Ring(S,z,f,u,g) =
    Struct({\<langle>carrier_name,S\<rangle>, \<langle>zero_name,z\<rangle>, \<langle>plus_fun_name, binary_fun_of(S,f)\<rangle>,
            \<langle>one_name,u\<rangle>, \<langle>times_fun_name, binary_fun_of(S,g)\<rangle>})"

lemma Ring_is_ring_raw [backward]:
  "z \<in> S \<Longrightarrow> binary_fun(S,f) \<Longrightarrow> u \<in> S \<Longrightarrow> binary_fun(S,g) \<Longrightarrow> ring_form(Ring(S,z,f,u,g))"
@proof @have "is_abgroup_raw(Ring(S,z,f,u,g))" @have "is_group_raw(Ring(S,z,f,u,g))" @qed

lemma ring_eval [rewrite]:
  "carrier(Ring(S,z,f,u,g)) = S"
  "zero(Ring(S,z,f,u,g)) = z"
  "one(Ring(S,z,f,u,g)) = u"
  "R = Ring(S,z,f,u,g) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> is_abgroup_raw(R) \<Longrightarrow> x +\<^sub>R y = f(x,y)"
  "R = Ring(S,z,f,u,g) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> is_group_raw(R) \<Longrightarrow> x *\<^sub>R y = g(x,y)" by auto2+
setup {* del_prfstep_thm @{thm Ring_def} *}

definition eq_str_ring :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "eq_str_ring(G,H) \<longleftrightarrow> eq_str_abgroup(G,H) \<and> eq_str_group(G,H)"

lemma eq_str_ring_sym [forward]: "eq_str_ring(G,H) \<Longrightarrow> eq_str_ring(H,G)" by auto2

lemma ring_eq [backward]:
  "ring_form(R) \<Longrightarrow> ring_form(S) \<Longrightarrow> eq_str_ring(R,S) \<Longrightarrow> R = S" by auto2
setup {* del_prfstep_thm @{thm ring_form_def} *}

section \<open>Ordered ring structure\<close>
  
definition is_ord_ring_raw :: "i \<Rightarrow> o" where [rewrite]:
  "is_ord_ring_raw(R) \<longleftrightarrow> is_ring_raw(R) \<and> raworder(R)"

lemma is_ord_ring_raw_iff [forward]:
  "is_ord_ring_raw(R) \<Longrightarrow> is_ring_raw(R)"
  "is_ord_ring_raw(R) \<Longrightarrow> raworder(R)"
  "is_ring_raw(R) \<Longrightarrow> raworder(R) \<Longrightarrow> is_ord_ring_raw(R)" by auto2+
setup {* del_prfstep_thm @{thm is_ord_ring_raw_def} *}

definition ord_ring_form :: "i \<Rightarrow> o" where [rewrite]:
  "ord_ring_form(R) \<longleftrightarrow> is_ord_ring_raw(R) \<and>
      is_func_graph(R,{carrier_name,order_graph_name,zero_name,plus_fun_name,one_name,times_fun_name})"

lemma ord_ring_form_to_raw [forward]: "ord_ring_form(R) \<Longrightarrow> is_ord_ring_raw(R)" by auto2

definition OrdRing :: "[i, i, i \<Rightarrow> i \<Rightarrow> i, i, i \<Rightarrow> i \<Rightarrow> i, i \<Rightarrow> i \<Rightarrow> o] \<Rightarrow> i" where [rewrite]:
  "OrdRing(S,z,f,u,g,r) = Struct({
      \<langle>carrier_name,S\<rangle>, \<langle>order_graph_name, rel_graph(S,r)\<rangle>,
      \<langle>zero_name,z\<rangle>, \<langle>plus_fun_name, binary_fun_of(S,f)\<rangle>,
      \<langle>one_name,u\<rangle>, \<langle>times_fun_name, binary_fun_of(S,g)\<rangle>})"

lemma OrdRing_is_ord_ring_raw [backward]:
  "z \<in> S \<Longrightarrow> binary_fun(S,f) \<Longrightarrow> u \<in> S \<Longrightarrow> binary_fun(S,g) \<Longrightarrow> R = OrdRing(S,z,f,u,g,r) \<Longrightarrow> ord_ring_form(R)"
@proof
  @have "is_abgroup_raw(R)"
  @have "is_group_raw(R)"
  @have "is_ring_raw(R)"
  @have "raworder(R)"
@qed

lemma ord_ring_eval [rewrite]:
  "carrier(OrdRing(S,z,f,u,g,r)) = S"
  "zero(OrdRing(S,z,f,u,g,r)) = z"
  "one(OrdRing(S,z,f,u,g,r)) = u"
  "R = OrdRing(S,z,f,u,g,r) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> is_ord_ring_raw(R) \<Longrightarrow> x +\<^sub>R y = f(x,y)"
  "R = OrdRing(S,z,f,u,g,r) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> is_ord_ring_raw(R) \<Longrightarrow> x *\<^sub>R y = g(x,y)"
  "R = OrdRing(S,z,f,u,g,r) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x \<le>\<^sub>R y \<longleftrightarrow> r(x,y)" by auto2+
setup {* del_prfstep_thm @{thm OrdRing_def} *}

definition eq_str_ord_ring :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "eq_str_ord_ring(G,H) \<longleftrightarrow> eq_str_ring(G,H) \<and> eq_str_order(G,H)"

lemma eq_str_ord_ring_sym [forward]: "eq_str_ord_ring(G,H) \<Longrightarrow> eq_str_ord_ring(H,G)" by auto2

lemma ord_ring_eq [backward]:
  "ord_ring_form(R) \<Longrightarrow> ord_ring_form(S) \<Longrightarrow> eq_str_ord_ring(R,S) \<Longrightarrow> R = S" by auto2
setup {* del_prfstep_thm @{thm ord_ring_form_def} *}

section \<open>Predicates on additive structure\<close>

definition is_add_id :: "i \<Rightarrow> o" where [rewrite]:
  "is_add_id(G) \<longleftrightarrow> is_abgroup_raw(G) \<and> (\<forall>x\<in>.G. \<zero>\<^sub>G +\<^sub>G x = x)"

lemma is_add_idD [rewrite]: "is_add_id(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> \<zero>\<^sub>G +\<^sub>G x = x" by auto2
lemma is_add_id_abgroup_prop [forward]:
  "is_abgroup_raw(H) \<Longrightarrow> is_add_id(G) \<Longrightarrow> eq_str_abgroup(G,H) \<Longrightarrow> is_add_id(H)" by auto2
setup {* del_prfstep_thm_eqforward @{thm is_add_id_def} *}

definition is_plus_comm :: "i \<Rightarrow> o" where [rewrite]:
  "is_plus_comm(G) \<longleftrightarrow> (is_abgroup_raw(G) \<and> (\<forall>x\<in>.G. \<forall>y\<in>.G. x +\<^sub>G y = y +\<^sub>G x))"

lemma plus_commD: "is_plus_comm(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> x +\<^sub>G y = y +\<^sub>G x" by auto2
lemma is_plus_comm_abgroup_prop [forward]:
  "is_abgroup_raw(H) \<Longrightarrow> is_plus_comm(G) \<Longrightarrow> eq_str_abgroup(G,H) \<Longrightarrow> is_plus_comm(H)" by auto2
setup {* del_prfstep_thm_eqforward @{thm is_plus_comm_def} *}

definition is_plus_assoc :: "i \<Rightarrow> o" where [rewrite]:
  "is_plus_assoc(G) \<longleftrightarrow> is_abgroup_raw(G) \<and> (\<forall>x\<in>.G. \<forall>y\<in>.G. \<forall>z\<in>.G. (x +\<^sub>G y) +\<^sub>G z = x +\<^sub>G (y +\<^sub>G z))"

lemma plus_assoc_right [rewrite]:
  "is_plus_assoc(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> z \<in>. G \<Longrightarrow> (x +\<^sub>G y) +\<^sub>G z = x +\<^sub>G (y +\<^sub>G z) \<and> y +\<^sub>G z \<in>. G" by auto2

lemma plus_assoc_left:
  "is_plus_assoc(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> z \<in>. G \<Longrightarrow> x +\<^sub>G (y +\<^sub>G z) = (x +\<^sub>G y) +\<^sub>G z \<and> x +\<^sub>G y \<in>. G" by auto2
setup {* del_prfstep_thm_eqforward @{thm is_plus_assoc_def} *}
  
lemma is_plus_assoc_abgroup_prop [forward]:
  "is_abgroup_raw(H) \<Longrightarrow> is_plus_assoc(G) \<Longrightarrow> eq_str_abgroup(G,H) \<Longrightarrow> is_plus_assoc(H)" by auto2
setup {* del_prfstep_thm @{thm plus_assoc_right} *}

section \<open>Predicates on multiplicative structure\<close>
  
definition is_mult_id :: "i \<Rightarrow> o" where [rewrite]:
  "is_mult_id(G) \<longleftrightarrow> (\<forall>x\<in>.G. \<one>\<^sub>G *\<^sub>G x = x \<and> x *\<^sub>G \<one>\<^sub>G = x)"

lemma is_mult_id_left [rewrite]: "is_mult_id(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> \<one>\<^sub>G *\<^sub>G x = x" by auto2
lemma is_mult_id_right [rewrite]: "is_mult_id(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> x *\<^sub>G \<one>\<^sub>G = x" by auto2
lemma is_mult_id_group_prop [forward]:
  "is_group_raw(H) \<Longrightarrow> is_mult_id(G) \<Longrightarrow> eq_str_group(G,H) \<Longrightarrow> is_mult_id(H)" by auto2
setup {* del_prfstep_thm_eqforward @{thm is_mult_id_def} *}

definition is_times_comm :: "i \<Rightarrow> o" where [rewrite]:
  "is_times_comm(G) \<longleftrightarrow> (is_group_raw(G) \<and> (\<forall>x\<in>.G. \<forall>y\<in>.G. x *\<^sub>G y = y *\<^sub>G x))"

lemma times_commD: "is_times_comm(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> x *\<^sub>G y = y *\<^sub>G x" by auto2
lemma is_times_comm_group_prop [forward]:
  "is_group_raw(H) \<Longrightarrow> is_times_comm(G) \<Longrightarrow> eq_str_group(G,H) \<Longrightarrow> is_times_comm(H)" by auto2
setup {* del_prfstep_thm_eqforward @{thm is_times_comm_def} *}

definition is_times_assoc :: "i \<Rightarrow> o" where [rewrite]:
  "is_times_assoc(G) \<longleftrightarrow> is_group_raw(G) \<and> (\<forall>x\<in>.G. \<forall>y\<in>.G. \<forall>z\<in>.G. (x *\<^sub>G y) *\<^sub>G z = x *\<^sub>G (y *\<^sub>G z))"

lemma is_times_assocD [forward]:
  "is_times_assoc(G) \<Longrightarrow> is_group_raw(G)" by auto2

lemma times_assoc_right [rewrite]:
  "is_times_assoc(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> z \<in>. G \<Longrightarrow> (x *\<^sub>G y) *\<^sub>G z = x *\<^sub>G (y *\<^sub>G z) \<and> y *\<^sub>G z \<in>. G" by auto2

lemma times_assoc_left:
  "is_times_assoc(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> z \<in>. G \<Longrightarrow> x *\<^sub>G (y *\<^sub>G z) = (x *\<^sub>G y) *\<^sub>G z \<and> x *\<^sub>G y \<in>. G" by auto2
setup {* del_prfstep_thm_eqforward @{thm is_times_assoc_def} *}

lemma is_times_assoc_group_prop [forward]:
  "is_group_raw(H) \<Longrightarrow> is_times_assoc(G) \<Longrightarrow> eq_str_group(G,H) \<Longrightarrow> is_times_assoc(H)" by auto2
setup {* del_prfstep_thm @{thm times_assoc_right} *}

section \<open>Predicates on ring structure\<close>

definition is_left_distrib :: "i \<Rightarrow> o" where [rewrite]:
  "is_left_distrib(R) \<longleftrightarrow> is_ring_raw(R) \<and> (\<forall>x\<in>.R. \<forall>y\<in>.R. \<forall>z\<in>.R. x *\<^sub>R (y +\<^sub>R z) = x *\<^sub>R y +\<^sub>R x *\<^sub>R z)"

lemma left_distribD [rewrite]:
  "is_left_distrib(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow>
   x *\<^sub>R (y +\<^sub>R z) = x *\<^sub>R y +\<^sub>R x *\<^sub>R z \<and> x *\<^sub>R y \<in>. R \<and> x *\<^sub>R z \<in>. R" by auto2
  
lemma left_distribD_back:
  "is_left_distrib(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow>
   x *\<^sub>R y +\<^sub>R x *\<^sub>R z = x *\<^sub>R (y +\<^sub>R z) \<and> y +\<^sub>R z \<in>. R" by auto2
setup {* del_prfstep_thm_eqforward @{thm is_left_distrib_def} *}

lemma is_left_distrib_ring_prop [forward]:
  "is_ring_raw(H) \<Longrightarrow> is_left_distrib(G) \<Longrightarrow> eq_str_ring(G,H) \<Longrightarrow> is_left_distrib(H)" by auto2
setup {* del_prfstep_thm @{thm left_distribD} *}

definition is_right_distrib :: "i \<Rightarrow> o" where [rewrite]:
  "is_right_distrib(R) \<longleftrightarrow> is_ring_raw(R) \<and> (\<forall>x\<in>.R. \<forall>y\<in>.R. \<forall>z\<in>.R. (y +\<^sub>R z) *\<^sub>R x = y *\<^sub>R x +\<^sub>R z *\<^sub>R x)"

lemma right_distribD [rewrite]:
  "is_right_distrib(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow>
   (y +\<^sub>R z) *\<^sub>R x = y *\<^sub>R x +\<^sub>R z *\<^sub>R x \<and> y *\<^sub>R x \<in>. R \<and> z *\<^sub>R x \<in>. R" by auto2

lemma right_distribD_back:
  "is_right_distrib(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow>
   y *\<^sub>R x +\<^sub>R z *\<^sub>R x = (y +\<^sub>R z) *\<^sub>R x \<and> y +\<^sub>R z \<in>. R" by auto2
setup {* del_prfstep_thm_eqforward @{thm is_right_distrib_def} *}

lemma is_right_distrib_ring_prop [forward]:
  "is_ring_raw(H) \<Longrightarrow> is_right_distrib(G) \<Longrightarrow> eq_str_ring(G,H) \<Longrightarrow> is_right_distrib(H)" by auto2
setup {* del_prfstep_thm @{thm right_distribD} *}

section \<open>Predicates on ordered ring structure\<close>

definition ord_ring_add_left :: "i \<Rightarrow> o" where [rewrite]:
  "ord_ring_add_left(R) \<longleftrightarrow> (\<forall>a\<in>.R. \<forall>b c. b \<le>\<^sub>R c \<longrightarrow> a +\<^sub>R b \<le>\<^sub>R a +\<^sub>R c)"

lemma ord_ring_add_leftD [backward]:
  "ord_ring_add_left(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<le>\<^sub>R c \<Longrightarrow> a +\<^sub>R b \<le>\<^sub>R a +\<^sub>R c" by auto2
lemma ord_ring_add_ord_ring_prop [forward]:
  "is_ord_ring_raw(H) \<Longrightarrow> ord_ring_add_left(G) \<Longrightarrow> eq_str_ord_ring(G,H) \<Longrightarrow> ord_ring_add_left(H)" by auto2
setup {* del_prfstep_thm_eqforward @{thm ord_ring_add_left_def} *}

definition ord_ring_mult_pos :: "i \<Rightarrow> o" where [rewrite]:
  "ord_ring_mult_pos(R) \<longleftrightarrow> (\<forall>a b. a \<ge>\<^sub>R \<zero>\<^sub>R \<longrightarrow> b \<ge>\<^sub>R \<zero>\<^sub>R \<longrightarrow> a *\<^sub>R b \<ge>\<^sub>R \<zero>\<^sub>R)"

lemma ord_ring_mult_posD [backward1, backward2]:
  "ord_ring_mult_pos(R) \<Longrightarrow> a \<ge>\<^sub>R \<zero>\<^sub>R \<Longrightarrow> b \<ge>\<^sub>R \<zero>\<^sub>R \<Longrightarrow> a *\<^sub>R b \<ge>\<^sub>R \<zero>\<^sub>R" by auto2
setup {* add_forward_prfstep_cond @{thm ord_ring_mult_posD} [with_term "?a *\<^sub>?R ?b"] *}
lemma ord_ring_mult_pos_ord_ring_prop [forward]:
  "is_ord_ring_raw(H) \<Longrightarrow> ord_ring_mult_pos(G) \<Longrightarrow> eq_str_ord_ring(G,H) \<Longrightarrow> ord_ring_mult_pos(H)" by auto2
setup {* del_prfstep_thm_eqforward @{thm ord_ring_mult_pos_def} *}
  
definition ord_semiring_mult_left :: "i \<Rightarrow> o" where [rewrite]:
  "ord_semiring_mult_left(R) \<longleftrightarrow> (\<forall>a\<in>.R. \<forall>b c. b \<le>\<^sub>R c \<longrightarrow> a *\<^sub>R b \<le>\<^sub>R a *\<^sub>R c)"

lemma ord_semiring_mult_leftD [backward2]:
  "ord_semiring_mult_left(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<le>\<^sub>R c \<Longrightarrow> a *\<^sub>R b \<le>\<^sub>R a *\<^sub>R c" by auto2
lemma ord_semiring_mult_left_ord_ring_prop [forward]:
  "is_ord_ring_raw(H) \<Longrightarrow> ord_semiring_mult_left(G) \<Longrightarrow> eq_str_ord_ring(G,H) \<Longrightarrow> ord_semiring_mult_left(H)" by auto2
setup {* del_prfstep_thm_eqforward @{thm ord_semiring_mult_left_def} *}

ML_file "alg_fol.ML"

end
