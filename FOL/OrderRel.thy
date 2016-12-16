theory OrderRel
imports EquivRel BigProd
begin

section {* Preorder and order relations *}  (* Bourbaki III.1.1 -- III.1.2 *)

(* Definition for meta and object relations *)
definition refl_meta_rel :: "[i \<Rightarrow> i \<Rightarrow> o] \<Rightarrow> o" where refl_meta_rel_def [rewrite]:
  "refl_meta_rel(R) \<longleftrightarrow> (\<forall>x y. R(x,y) \<longrightarrow> R(x,x) \<and> R(y,y))"

definition antisym_meta_rel :: "[i \<Rightarrow> i \<Rightarrow> o] \<Rightarrow> o" where antisym_meta_rel_def [rewrite]:
  "antisym_meta_rel(R) \<longleftrightarrow> (\<forall>x y. R(x,y) \<longrightarrow> R(y,x) \<longrightarrow> x = y)"

lemma antisym_meta_relD [forward]:
  "antisym_meta_rel(R) \<Longrightarrow> R(x,y) \<Longrightarrow> R(y,x) \<Longrightarrow> x = y" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm antisym_meta_rel_def} *}

definition preorder_meta_rel :: "[i \<Rightarrow> i \<Rightarrow> o] \<Rightarrow> o" where preorder_meta_rel_def [rewrite]:
  "preorder_meta_rel(R) \<longleftrightarrow> (refl_meta_rel(R) \<and> trans_meta_rel(R))"

definition preorder_rel_on :: "[i \<Rightarrow> i \<Rightarrow> o, i] \<Rightarrow> o" where preorder_rel_on_def [rewrite]:
  "preorder_rel_on(R,E) \<longleftrightarrow> (preorder_meta_rel(R) \<and> (\<forall>x. x \<in> E \<longleftrightarrow> R(x,x)))"

definition preorder_rel :: "i \<Rightarrow> o" where preorder_rel_def [rewrite]:
  "preorder_rel(R) \<longleftrightarrow> (is_relation(R) \<and> source(R) = target(R) \<and>
                        preorder_rel_on(\<lambda>x y. rel(R,x,y), source(R)))"

definition order_meta_rel :: "[i \<Rightarrow> i \<Rightarrow> o] \<Rightarrow> o" where order_meta_rel_def [rewrite]:
  "order_meta_rel(R) \<longleftrightarrow> (preorder_meta_rel(R) \<and> antisym_meta_rel(R))"

definition order_rel_on :: "[i \<Rightarrow> i \<Rightarrow> o, i] \<Rightarrow> o" where order_rel_on_def [rewrite]:
  "order_rel_on(R,E) \<longleftrightarrow> (order_meta_rel(R) \<and> (\<forall>x. x \<in> E \<longleftrightarrow> R(x,x)))"

definition order_rel :: "i \<Rightarrow> o" where order_rel_def [rewrite]:
  "order_rel(R) \<longleftrightarrow> (is_relation(R) \<and> source(R) = target(R) \<and>
                     order_rel_on(\<lambda>x y. rel(R,x,y), source(R)))"

(* Self-contained condition for preorder_rel. *)
lemma preorder_rel_iff [rewrite]:
  "preorder_rel(R) \<longleftrightarrow> (
    is_relation(R) \<and> source(R) = target(R) \<and>
    (\<forall>x\<in>source(R). rel(R,x,x)) \<and>
    (\<forall>x y z. rel(R,x,y) \<longrightarrow> rel(R,y,z) \<longrightarrow> rel(R,x,z)))" by auto2
setup {* add_property_const @{term preorder_rel} *}
setup {* del_prfstep_thm @{thm preorder_rel_def} *}

lemma preorder_relD:
  "preorder_rel(R) \<Longrightarrow> is_relation(R)"
  "preorder_rel(R) \<Longrightarrow> source(R) = target(R)"
  "preorder_rel(R) \<Longrightarrow> rel(R,x,x) \<longleftrightarrow> x\<in>source(R)"
  "preorder_rel(R) \<Longrightarrow> rel(R,x,y) \<Longrightarrow> rel(R,y,z) \<Longrightarrow> rel(R,x,z)" by auto2+
setup {* fold add_forward_prfstep @{thms preorder_relD(1-2,4)} *}
setup {* add_rewrite_rule_bidir @{thm preorder_relD(3)} *}
setup {* del_prfstep_thm_str "@eqforward" @{thm preorder_rel_iff} *}

(* Self-contained condition for order_rel. *)
lemma order_rel_iff [rewrite]:
  "order_rel(R) \<longleftrightarrow> (
     preorder_rel(R) \<and>
     (\<forall>x y. rel(R,x,y) \<longrightarrow> rel(R,y,x) \<longrightarrow> x = y))" by auto2
setup {* add_property_const @{term order_rel} *}
setup {* del_prfstep_thm @{thm order_rel_def} *}

lemma order_relD [forward]:
  "order_rel(R) \<Longrightarrow> preorder_rel(R)"
  "order_rel(R) \<Longrightarrow> rel(R,x,y) \<Longrightarrow> rel(R,y,x) \<Longrightarrow> x = y" by auto2+
setup {* add_backward2_prfstep @{thm order_relD(2)} *}
setup {* del_prfstep_thm_str "@eqforward" @{thm order_rel_iff} *}

(* Examples *)
lemma eq_is_order_meta_rel: "order_meta_rel(\<lambda>x y. x = y)" by auto2
lemma subset_is_order_meta_rel: "order_meta_rel(\<lambda>x y. x \<subseteq> y)" by auto2
lemma inv_is_meta_order_rel: "order_meta_rel(R) \<Longrightarrow> order_meta_rel(\<lambda>x y. R(y,x))" by auto2
lemma inv_is_order_rel: "order_rel(R) \<Longrightarrow> order_rel(rel_inverse(R))" by auto2
lemma induced_pre_order_rel: "preorder_rel_on(R,E) \<Longrightarrow> preorder_rel(Rel(E,R))" by auto2
lemma induced_order_rel: "order_rel_on(R,E) \<Longrightarrow> order_rel(Rel(E,R))" by auto2

(* Symmetrization of a relation *)
definition sym_of_rel :: "i \<Rightarrow> i" where sym_of_rel_def [rewrite]:
  "sym_of_rel(R) = Rel(source(R), \<lambda>x y. rel(R,x,y) \<and> rel(R,y,x))"

lemma sym_of_rel_is_rel [typing]: "sym_of_rel(R) \<in> rel_space(source(R))" by auto2

lemma sym_of_rel_iff [rewrite]:
  "is_relation(R) \<Longrightarrow> rel(sym_of_rel(R),x,y) \<longleftrightarrow> rel(R,x,y) \<and> rel(R,y,x)" by auto2
setup {* del_prfstep_thm @{thm sym_of_rel_def} *}

(* Symmetrization of a preorder is an equivalence relation. Moreover,
   the preorder induces an order relation on the quotient. *)
lemma preorder_sym_is_equiv_rel [forward]:
  "preorder_rel(R) \<Longrightarrow> equiv_rel(sym_of_rel(R))" by auto2

definition preorder_quot :: "i \<Rightarrow> i" where preorder_quot_def [rewrite]:
  "preorder_quot(R) = Rel(source(R)/sym_of_rel(R), \<lambda>x y. rel(R,rep(sym_of_rel(R),x),rep(sym_of_rel(R),y)))"

lemma preorder_quotient_is_order [forward]:
  "preorder_rel(R) \<Longrightarrow> order_rel(preorder_quot(R))" by auto2

(* Subset ordering. *)
definition subset_order :: "i \<Rightarrow> i" where subset_order_def [rewrite]:
  "subset_order(S) = Rel(S, \<lambda>x y. x \<subseteq> y)"

lemma subset_order_is_order [forward]: "order_rel(subset_order(S))" by auto2

section {* Notations for order relations *}  (* Bourbaki III.1.3 *)

(* Define for object relation only. *)
definition le :: "[i, i, i] \<Rightarrow> o" ("(_/ \<le>\<^sub>_ _)" [51,51,51] 50) where le_def [rewrite]:
  "x \<le>\<^sub>R y \<longleftrightarrow> rel(R,x,y)"

definition less :: "[i, i, i] \<Rightarrow> o" ("(_/ <\<^sub>_ _)" [51,51,51] 50) where less_def [rewrite]:
  "x <\<^sub>R y \<longleftrightarrow> (rel(R,x,y) \<and> x \<noteq> y)"

abbreviation (input) ge :: "[i, i, i] \<Rightarrow> o" ("(_/ \<ge>\<^sub>_ _)" [51,51,51] 50) where
  "x \<ge>\<^sub>R y \<equiv> y \<le>\<^sub>R x"

abbreviation (input) greater :: "[i, i, i] \<Rightarrow> o" ("(_/ >\<^sub>_ _)" [51,51,51] 50) where
  "x >\<^sub>R y \<equiv> y <\<^sub>R x"

(* For order (and preorder) relations only, use both rel and \<le> *)
lemma le_back [rewrite]: "preorder_rel(R) \<Longrightarrow> rel(R,x,y) \<longleftrightarrow> x \<le>\<^sub>R y" by auto2

(* Other versions of transitivity *)
lemma order_trans [forward]:
  "order_rel(R) \<Longrightarrow> x <\<^sub>R y \<Longrightarrow> y \<le>\<^sub>R z \<Longrightarrow> x <\<^sub>R z"
  "order_rel(R) \<Longrightarrow> x \<le>\<^sub>R y \<Longrightarrow> y <\<^sub>R z \<Longrightarrow> x <\<^sub>R z"
  "order_rel(R) \<Longrightarrow> x <\<^sub>R y \<Longrightarrow> y <\<^sub>R z \<Longrightarrow> x <\<^sub>R z" by auto2+

lemma preorder_lessI [forward, backward1, backward2]:
  "preorder_rel(R) \<Longrightarrow> x \<le>\<^sub>R y \<Longrightarrow> x \<noteq> y \<Longrightarrow> x <\<^sub>R y" by auto2

lemma preorder_lessE [forward]:
  "preorder_rel(R) \<Longrightarrow> x <\<^sub>R y \<Longrightarrow> x \<le>\<^sub>R y \<and> x \<noteq> y" by auto2
setup {* del_prfstep_thm @{thm less_def} *}

(* Isomorphism of ordered sets. We can in fact define it for arbitrary relations. *)
definition isomorphism :: "[i, i, i] \<Rightarrow> o" where isomorphism_def [rewrite]:
  "isomorphism(R,S,f) \<longleftrightarrow> (R \<in> rel_space(source(R)) \<and> S \<in> rel_space(source(S)) \<and>
                           f \<in> source(R) \<cong> source(S) \<and>
                           (\<forall>x\<in>source(f). \<forall>y\<in>source(f). rel(R,x,y) \<longleftrightarrow> rel(S,f`x,f`y)))"

lemma isomorphismD1 [forward]:
  "isomorphism(R,S,f) \<Longrightarrow> R \<in> rel_space(source(R)) \<and> S \<in> rel_space(source(S)) \<and>
    f \<in> source(R) \<cong> source(S)" by auto2
lemma isomorphismD2 [rewrite]:
  "isomorphism(R,S,f) \<Longrightarrow> x \<in> source(f) \<Longrightarrow> y \<in> source(f) \<Longrightarrow> rel(S,f`x,f`y) \<longleftrightarrow> rel(R,x,y)" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm isomorphism_def} *}

(* Isomorphism preserves properties on ordering *)
lemma preorder_rel_iso [forward]:
  "preorder_rel(R) \<Longrightarrow> isomorphism(R,S,f) \<Longrightarrow> preorder_rel(S)" by auto2
lemma order_rel_iso [forward]:
  "order_rel(R) \<Longrightarrow> isomorphism(R,S,f) \<Longrightarrow> order_rel(S)" by auto2

section {* Ordering on subsets and products *}  (* Bourbaki III.1.4 *)

(* Define relation on subsets in general *)
definition subrel :: "[i, i] \<Rightarrow> i" where subrel_def [rewrite]:
  "subrel(R,A) = Rel(A, \<lambda>x y. rel(R,x,y))"

lemma subrel_is_relation [typing]: "subrel(R,A) \<in> rel_space(A)" by auto2

lemma subrel_eval [rewrite]:
  "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> rel(subrel(R,A),x,y) \<longleftrightarrow> rel(R,x,y)" by auto2
setup {* del_prfstep_thm @{thm subrel_def} *}

setup {* add_gen_prfstep ("subrel_case",
  [WithTerm @{term_pat "subrel(?R,?A)"}, CreateConcl @{term_pat "?A \<subseteq> source(?R)"}]) *}

lemma subrel_is_preorder:
  "preorder_rel(R) \<Longrightarrow> A \<subseteq> source(R) \<Longrightarrow> preorder_rel(subrel(R,A))" by auto2
setup {* add_forward_prfstep_cond @{thm subrel_is_preorder} [with_term "subrel(?R,?A)"] *}

lemma subrel_is_order:
  "order_rel(R) \<Longrightarrow> A \<subseteq> source(R) \<Longrightarrow> order_rel(subrel(R,A))" by auto2
setup {* add_forward_prfstep_cond @{thm subrel_is_order} [with_term "subrel(?R,?A)"] *}

lemma subset_order_subrel [rewrite]:
  "F \<subseteq> E \<Longrightarrow> subrel(subset_order(E),F) = subset_order(F)" by auto2

(* Define relation on products in general. *)
definition prod_src :: "[i, i] \<Rightarrow> i" where prod_src_def [rewrite]:
  "prod_src(I,R) = Pi(I,\<lambda>a. source(proj(R,a)))"

definition prod_rel :: "[i, i] \<Rightarrow> i" where prod_rel_def [rewrite]:
  "prod_rel(I,R) = Rel(prod_src(I,R), \<lambda>x y. \<forall>a\<in>I. rel(proj(R,a),proj(x,a),proj(y,a)))"

lemma prod_rel_is_rel [typing]: "prod_rel(I,R) \<in> rel_space(prod_src(I,R))" by auto2

lemma prod_rel_eval [rewrite]:
  "x \<in> prod_src(I,R) \<Longrightarrow> y \<in> prod_src(I,R) \<Longrightarrow>
   rel(prod_rel(I,R),x,y) \<longleftrightarrow> (\<forall>a\<in>I. rel(proj(R,a),proj(x,a),proj(y,a)))" by auto2
setup {* del_prfstep_thm @{thm prod_rel_def} *}

lemma prod_rel_is_preorder:
  "\<forall>a\<in>I. preorder_rel(proj(R,a)) \<Longrightarrow> preorder_rel(prod_rel(I,R))" by auto2
setup {* add_forward_prfstep_cond @{thm prod_rel_is_preorder} [with_term "prod_rel(?I,?R)"] *}

lemma prod_rel_is_order:
  "\<forall>a\<in>I. order_rel(proj(R,a)) \<Longrightarrow> order_rel(prod_rel(I,R))" by auto2
setup {* add_forward_prfstep_cond @{thm prod_rel_is_order} [with_term "prod_rel(?I,?R)"] *}

section {* Increasing mappings *}  (* Bourbaki III.1.5 *)

definition incr :: "[i, i, i] \<Rightarrow> o" where incr_def [rewrite]:
  "incr(R,S,f) \<longleftrightarrow> (source(f) = source(R) \<and> target(f) = source(S) \<and>
                    (\<forall>x\<in>source(f). \<forall>y\<in>source(f). x \<le>\<^sub>R y \<longrightarrow> f`x \<le>\<^sub>S f`y))"

definition decr :: "[i, i, i] \<Rightarrow> o" where decr_def [rewrite]:
  "decr(R,S,f) \<longleftrightarrow> (source(f) = source(R) \<and> target(f) = source(S) \<and>
                    (\<forall>x\<in>source(f). \<forall>y\<in>source(f). x \<le>\<^sub>R y \<longrightarrow> f`x \<ge>\<^sub>S f`y))"

definition strict_incr :: "[i, i, i] \<Rightarrow> o" where strict_incr_def [rewrite]:
  "strict_incr(R,S,f) \<longleftrightarrow> (source(f) = source(R) \<and> target(f) = source(S) \<and>
                     (\<forall>x\<in>source(f). \<forall>y\<in>source(f). x <\<^sub>R y \<longrightarrow> f`x <\<^sub>S f`y))"

definition strict_decr :: "[i, i, i] \<Rightarrow> o" where strict_decr_def [rewrite]:
  "strict_decr(R,S,f) \<longleftrightarrow> (source(f) = source(R) \<and> target(f) = source(S) \<and>
                     (\<forall>x\<in>source(f). \<forall>y\<in>source(f). x <\<^sub>R y \<longrightarrow> f`x >\<^sub>S f`y))"

(* Examples *)
lemma subset_order_less [rewrite]:
  "less(X,subset_order(E),Y) \<longleftrightarrow> (X \<in> E \<and> Y \<in> E \<and> X \<subset> Y)" by auto2

lemma compl_strict_decr:
  "strict_decr(subset_order(Pow(E)),subset_order(Pow(E)),\<lambda>X\<in>Pow(E). (E-X)\<in>Pow(E))" by auto2

lemma greater_elts_strict_subset [backward]:
  "order_rel(R) \<Longrightarrow> x \<in> source(R) \<Longrightarrow> y \<in> source(R) \<Longrightarrow> x <\<^sub>R y \<Longrightarrow>
   {z\<in>source(R). z \<ge>\<^sub>R y} \<subset> {z\<in>source(R). z \<ge>\<^sub>R x}"
  by (tactic {* auto2s_tac @{context} (HAVE "x\<in>{z\<in>source(R). z \<ge>\<^sub>R x}") *})

lemma greater_elts_strict_decr:
  "order_rel(R) \<Longrightarrow> strict_decr(R, subset_order(Pow(source(R))),
                      \<lambda>x\<in>source(R). {y\<in>source(R). y \<ge>\<^sub>R x}\<in>Pow(source(R)))" by auto2

lemma inj_to_strict_incr:
  "preorder_rel(R) \<Longrightarrow> preorder_rel(S) \<Longrightarrow> injective(f) \<Longrightarrow> incr(R,S,f) \<Longrightarrow> strict_incr(R,S,f)" by auto2

lemma inj_to_strict_decr:
  "preorder_rel(R) \<Longrightarrow> preorder_rel(S) \<Longrightarrow> injective(f) \<Longrightarrow> decr(R,S,f) \<Longrightarrow> strict_decr(R,S,f)" by auto2

lemma bij_to_isomorphism:
  "preorder_rel(R) \<Longrightarrow> preorder_rel(S) \<Longrightarrow> bijective(f) \<Longrightarrow>
   isomorphism(R,S,f) \<longleftrightarrow> incr(R,S,f) \<and> incr(S,R,inverse(f))" by auto2

lemma restrict_image_incr:
  "order_rel(R) \<Longrightarrow> order_rel(S) \<Longrightarrow> is_function(f) \<Longrightarrow> incr(R,S,f) \<Longrightarrow>
   incr(R,subrel(S,f``source(R)),func_restrict_image(f))" by auto2
setup {* add_forward_prfstep_cond @{thm restrict_image_incr} [with_term "func_restrict_image(?f)"] *}

(* Proposition 2 in III.1.5 *)
lemma two_decr_funs_prop:
  "preorder_rel(R) \<Longrightarrow> preorder_rel(S) \<Longrightarrow> is_function(u) \<Longrightarrow> is_function(v) \<Longrightarrow>
   decr(R,S,u) \<Longrightarrow> decr(S,R,v) \<Longrightarrow> \<forall>x\<in>source(R). v`(u`x) = x \<Longrightarrow> \<forall>x\<in>source(S). u`(v`x) = x \<Longrightarrow>
   u O v O u = u \<and> v O u O v = v" by auto2

section {* Maximal and minimal elements *}  (* Bourbaki III.1.6 *)

definition maximal :: "[i, i] \<Rightarrow> o" where maximal_def [rewrite]:
  "maximal(R,x) \<longleftrightarrow> (x \<in> source(R) \<and> (\<forall>a\<in>source(R). a \<ge>\<^sub>R x \<longrightarrow> a = x))"

definition minimal :: "[i, i] \<Rightarrow> o" where minimal_def [rewrite]:
  "minimal(R,x) \<longleftrightarrow> (x \<in> source(R) \<and> (\<forall>a\<in>source(R). a \<le>\<^sub>R x \<longrightarrow> a = x))"

(* Examples *)
lemma singleton_minimal:
  "x \<in> S \<Longrightarrow> minimal(subset_order(Pow(S)-{\<emptyset>}),{x})" by auto2

section {* Greatest and least elements *}  (* Bourbaki III.1.7 *)

(* We define the more general notion of greatest/least element of a subset, to
   prepare for definition of sup and inf later. *)
definition has_greatest :: "[i, i] \<Rightarrow> o" where has_greatest_def [rewrite]:
  "has_greatest(R,X) \<longleftrightarrow> (\<exists>x\<in>X. \<forall>a\<in>X. a \<le>\<^sub>R x)"

definition greatest :: "[i, i] \<Rightarrow> i" where greatest_def [rewrite]:
  "greatest(R,X) = (THE x. x \<in> X \<and> (\<forall>a\<in>X. a \<le>\<^sub>R x))"

(* We always prove has_greatest(R,X) and assign greatest(R,X) at the same time.
   Similarly for least, sup, and inf below *)
lemma greatestI [backward]:
  "order_rel(R) \<Longrightarrow> x \<in> X \<Longrightarrow> \<forall>a\<in>X. a \<le>\<^sub>R x \<Longrightarrow> has_greatest(R,X) \<and> greatest(R,X) = x" by auto2

lemma greatestE:
  "order_rel(R) \<Longrightarrow> has_greatest(R,X) \<Longrightarrow> greatest(R,X) \<in> X"
  "order_rel(R) \<Longrightarrow> a \<in> X \<Longrightarrow> has_greatest(R,X) \<Longrightarrow> a \<le>\<^sub>R greatest(R,X)" by auto2+
setup {* fold (fn th => add_forward_prfstep_cond th [with_term "greatest(?R,?X)"]) @{thms greatestE} *}
setup {* fold del_prfstep_thm [@{thm has_greatest_def}, @{thm greatest_def}] *}

definition has_least :: "[i, i] \<Rightarrow> o" where has_least_def [rewrite]:
  "has_least(R,X) \<longleftrightarrow> (\<exists>x\<in>X. \<forall>a\<in>X. x \<le>\<^sub>R a)"

definition least :: "[i, i] \<Rightarrow> i" where least_def [rewrite]:
  "least(R,X) = (THE x. x \<in> X \<and> (\<forall>a\<in>X. x \<le>\<^sub>R a))"

lemma leastI [backward]:
  "order_rel(R) \<Longrightarrow> x \<in> X \<Longrightarrow> \<forall>a\<in>X. a \<ge>\<^sub>R x \<Longrightarrow> has_least(R,X) \<and> least(R,X) = x" by auto2

lemma leastE:
  "order_rel(R) \<Longrightarrow> has_least(R,X) \<Longrightarrow> least(R,X) \<in> X"
  "order_rel(R) \<Longrightarrow> a \<in> X \<Longrightarrow> has_least(R,X) \<Longrightarrow> least(R,X) \<le>\<^sub>R a" by auto2+
setup {* fold (fn th => add_forward_prfstep_cond th [with_term "least(?R,?X)"]) @{thms leastE} *}
setup {* fold del_prfstep_thm [@{thm has_least_def}, @{thm least_def}] *}

(* Relation to maximal / minimal *)
lemma greatest_maximal:
  "order_rel(R) \<Longrightarrow> has_greatest(R,X) \<Longrightarrow> maximal(subrel(R,X),greatest(R,X))" by auto2

lemma greatest_maximal_unique:
  "order_rel(R) \<Longrightarrow> has_greatest(R,X) \<Longrightarrow> x \<in> X \<Longrightarrow> maximal(subrel(R,X),x) \<Longrightarrow> x = greatest(R,X)" by auto2

lemma least_minimal:
  "order_rel(R) \<Longrightarrow> has_least(R,X) \<Longrightarrow> minimal(subrel(R,X),least(R,X))" by auto2

lemma least_minimal_unique:
  "order_rel(R) \<Longrightarrow> has_least(R,X) \<Longrightarrow> x \<in> X \<Longrightarrow> minimal(subrel(R,X),x) \<Longrightarrow> x = least(R,X)" by auto2

(* Examples *)
lemma greatest_subset_is_union:
  "has_greatest(subset_order(S),S) \<Longrightarrow> greatest(subset_order(S),S) = \<Union>S" by auto2

lemma greatest_subset_is_union2:
  "\<Union>S \<in> S \<Longrightarrow> has_greatest(subset_order(S),S) \<and> greatest(subset_order(S),S) = \<Union>S" by auto2

lemma least_subset_is_inter:
  "has_least(subset_order(S),S) \<Longrightarrow> least(subset_order(S),S) = \<Inter>S" by auto2

lemma least_subset_is_inter2:
  "\<Inter>S \<in> S \<Longrightarrow> has_least(subset_order(S),S) \<and> least(subset_order(S),S) = \<Inter>S" by auto2

lemma empty_subset_least:
  "least(subset_order(Pow(E)),Pow(E)) = \<emptyset> \<and> has_least(subset_order(Pow(E)),Pow(E))" by auto2

lemma full_subset_greatest:
  "greatest(subset_order(Pow(E)),Pow(E)) = E \<and> has_greatest(subset_order(Pow(E)),Pow(E))" by auto2

lemma has_least_subrel [backward2]:
  "order_rel(R) \<Longrightarrow> has_least(R,A) \<Longrightarrow> X \<subseteq> source(R) \<Longrightarrow> A \<subseteq> X \<Longrightarrow>
   has_least(subrel(R,X),A) \<and> least(subrel(R,X),A) = least(R,A)" by auto2
setup {* add_backward2_prfstep (conj_left_th @{thm has_least_subrel}) *}

lemma has_least_subrel_inv [backward2]:
  "order_rel(R) \<Longrightarrow> has_least(subrel(R,X),A) \<Longrightarrow> X \<subseteq> source(R) \<Longrightarrow> A \<subseteq> X \<Longrightarrow>
   has_least(R,A) \<and> least(R,A) = least(subrel(R,X),A)" by auto2
setup {* add_backward2_prfstep (conj_left_th @{thm has_least_subrel_inv}) *}

lemma has_least_singleton [backward2]:
  "order_rel(R) \<Longrightarrow> a \<in> source(R) \<Longrightarrow> has_least(R,{a}) \<and> least(R,{a}) = a" by auto2
setup {* add_backward2_prfstep (conj_left_th @{thm has_least_singleton}) *}

lemma has_least_sub_singleton [backward2]:
  "order_rel(R) \<Longrightarrow> has_least(R,X-{a}) \<Longrightarrow> \<forall>x\<in>X. x \<le>\<^sub>R a \<Longrightarrow>
   has_least(R,X) \<and> least(R,X) = least(R,X-{a})"
  by (tactic {* auto2s_tac @{context} (
    CASE "a \<in> X" WITH HAVE "X = (X - {a}) \<union> {a}" THEN
    CASE "a \<notin> X" WITH HAVE "X = (X - {a})") *})
setup {* add_backward2_prfstep (conj_left_th @{thm has_least_sub_singleton}) *}

(* Forming a new ordering by appending an element *)
definition adjoin_greatest :: "[i, i] \<Rightarrow> i" where adjoin_greatest_def [rewrite]:
  "adjoin_greatest(R,a) = Rel(source(R)\<union>{a}, \<lambda>x y. y = a \<or> rel(R,x,y))"

lemma adjoin_greatest_is_rel [typing]: "adjoin_greatest(R,a) \<in> rel_space(source(R)\<union>{a})" by auto2

lemma adjoin_greatest_eval1:
  "x \<in> source(R)\<union>{a} \<Longrightarrow> rel(adjoin_greatest(R,a),x,a)" by auto2
setup {* add_forward_prfstep_cond @{thm adjoin_greatest_eval1} [with_term "adjoin_greatest(?R,?a)"] *}
lemma adjoin_greatest_eval2:
  "order_rel(R) \<Longrightarrow> x \<in> source(R) \<Longrightarrow> a \<notin> source(R) \<Longrightarrow> \<not>rel(adjoin_greatest(R,a),a,x)" by auto2
setup {* add_forward_prfstep_cond @{thm adjoin_greatest_eval2} [with_term "adjoin_greatest(?R,?a)"] *}

lemma adjoin_greatest_eval' [rewrite]:
  "x \<in> source(R) \<Longrightarrow> y \<in> source(R) \<Longrightarrow> a \<notin> source(R) \<Longrightarrow>
   rel(adjoin_greatest(R,a),x,y) \<longleftrightarrow> rel(R,x,y)" by auto2
setup {* del_prfstep_thm @{thm adjoin_greatest_def} *}

lemma adjoin_greatest_is_order:
  "order_rel(R) \<Longrightarrow> a \<notin> source(R) \<Longrightarrow> order_rel(adjoin_greatest(R,a))" by auto2
setup {* add_forward_prfstep_cond @{thm adjoin_greatest_is_order} [with_term "adjoin_greatest(?R,?a)"] *}

lemma adjoin_greatest_restrict [rewrite]:
  "order_rel(R) \<Longrightarrow> a \<notin> source(R) \<Longrightarrow> subrel(adjoin_greatest(R,a),source(R)) = R" by auto2

lemma adjoin_greatest_prop:
  "order_rel(R) \<Longrightarrow> a \<notin> source(R) \<Longrightarrow>
   has_greatest(adjoin_greatest(R,a),source(R)\<union>{a}) \<and> greatest(adjoin_greatest(R,a),source(R)\<union>{a}) = a" by auto2

lemma adjoin_greatest_unique [backward]:
  "order_rel(R) \<Longrightarrow> order_rel(S) \<Longrightarrow> a \<notin> source(R) \<Longrightarrow> source(S) = source(R) \<union> {a} \<Longrightarrow>
   \<forall>x\<in>source(S). x \<le>\<^sub>S a \<Longrightarrow> subrel(S,source(R)) = R \<Longrightarrow> S = adjoin_greatest(R,a)" by auto2

(* Cofinal and coinitial subsets *)
definition cofinal :: "[i, i] \<Rightarrow> o" where cofinal_def [rewrite]:
  "cofinal(R,A) \<longleftrightarrow> (A \<subseteq> source(R) \<and> (\<forall>x\<in>source(R). \<exists>y\<in>A. x \<le>\<^sub>R y))"

lemma cofinalE1 [forward]: "cofinal(R,A) \<Longrightarrow> A \<subseteq> source(R)" by auto2
lemma cofinalE2 [backward2]: "cofinal(R,A) \<Longrightarrow> x \<in> source(R) \<Longrightarrow> \<exists>y\<in>A. x \<le>\<^sub>R y" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm cofinal_def} *}

definition coinitial :: "[i, i] \<Rightarrow> o" where coinitial_def [rewrite]:
  "coinitial(R,A) \<longleftrightarrow> (A \<subseteq> source(R) \<and> (\<forall>x\<in>source(R). \<exists>y\<in>A. y \<le>\<^sub>R x))"

lemma coinitialE1 [forward]: "coinitial(R,A) \<Longrightarrow> A \<subseteq> source(R)" by auto2
lemma coinitialE2 [backward2]: "coinitial(R,A) \<Longrightarrow> x \<in> source(R) \<Longrightarrow> \<exists>y\<in>A. y \<le>\<^sub>R x" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm coinitial_def} *}

lemma greatest_is_cofinal:
  "order_rel(R) \<Longrightarrow> has_greatest(R,source(R)) \<Longrightarrow> cofinal(R,{greatest(R,source(R))})" by auto2

lemma least_is_coinitial:
  "order_rel(R) \<Longrightarrow> has_least(R,source(R)) \<Longrightarrow> coinitial(R,{least(R,source(R))})" by auto2

section {* Upper and lower bounds *}  (* Bourbaki III.1.8 *)

definition upper_bound :: "[i, i] \<Rightarrow> i" where upper_bound_def [rewrite]:
  "upper_bound(R,X) = {y\<in>source(R). \<forall>x\<in>X. x \<le>\<^sub>R y}"

definition lower_bound :: "[i, i] \<Rightarrow> i" where lower_bound_def [rewrite]:
  "lower_bound(R,X) = {y\<in>source(R). \<forall>x\<in>X. y \<le>\<^sub>R x}"

lemma upper_bound_trans [forward]:
  "order_rel(R) \<Longrightarrow> x \<in> upper_bound(R,X) \<Longrightarrow> y \<ge>\<^sub>R x \<Longrightarrow> y \<in> upper_bound(R,X)" by auto2

lemma upper_bound_trans_subset [backward]:
  "X \<subseteq> Y \<Longrightarrow> upper_bound(R,Y) \<subseteq> upper_bound(R,X)" by auto2

lemma upper_bound_greatest:
  "order_rel(R) \<Longrightarrow> has_greatest(R,source(R)) \<Longrightarrow> upper_bound(R,source(R)) = {greatest(R,source(R))}" by auto2

lemma upper_bound_greatest':
  "order_rel(R) \<Longrightarrow> upper_bound(R,source(R)) = {a} \<Longrightarrow> greatest(R,source(R)) = a \<and> has_greatest(R,source(R))" by auto2

lemma lower_bound_trans [forward]:
  "order_rel(R) \<Longrightarrow> x \<in> lower_bound(R,X) \<Longrightarrow> y \<le>\<^sub>R x \<Longrightarrow> y \<in> lower_bound(R,X)" by auto2

lemma lower_bound_trans_subset [backward]:
  "X \<subseteq> Y \<Longrightarrow> lower_bound(R,Y) \<subseteq> lower_bound(R,X)" by auto2

lemma lower_bound_least:
  "order_rel(R) \<Longrightarrow> has_least(R,source(R)) \<Longrightarrow> lower_bound(R,source(R)) = {least(R,source(R))}" by auto2

lemma lower_bound_least':
  "order_rel(R) \<Longrightarrow> lower_bound(R,source(R)) = {a} \<Longrightarrow> least(R,source(R)) = a \<and> has_least(R,source(R))" by auto2

section {* Supremum and infimum *}  (* Bourbaki III.1.9 *)

(* Definitions of sup and inf *)
definition has_sup :: "[i, i] \<Rightarrow> o" where has_sup_def [rewrite]:
  "has_sup(R,X) \<longleftrightarrow> has_least(R,upper_bound(R,X))"

definition sup :: "[i, i] \<Rightarrow> i" where sup_def [rewrite]:
  "sup(R,X) = least(R,upper_bound(R,X))"

definition has_inf :: "[i, i] \<Rightarrow> o" where has_inf_def [rewrite]:
  "has_inf(R,X) \<longleftrightarrow> has_greatest(R,lower_bound(R,X))"

definition inf :: "[i, i] \<Rightarrow> i" where inf_def [rewrite]:
  "inf(R,X) = greatest(R,lower_bound(R,X))"

lemma supI [backward]:
  "order_rel(R) \<Longrightarrow> has_least(R,upper_bound(R,X)) \<and> least(R,upper_bound(R,X)) = x \<Longrightarrow>
   has_sup(R,X) \<and> sup(R,X) = x" by auto2

lemma infI [backward]:
  "order_rel(R) \<Longrightarrow> has_greatest(R,lower_bound(R,X)) \<and> greatest(R,lower_bound(R,X)) = x \<Longrightarrow>
   has_inf(R,X) \<and> inf(R,X) = x" by auto2

(* Sup and inf for the image of a mapping *)
definition has_supf :: "[i, i] \<Rightarrow> o" where has_supf_def [rewrite]:
  "has_supf(R,f) \<longleftrightarrow> has_sup(R,f``source(f))"

definition supf :: "[i, i] \<Rightarrow> i" where supf_def [rewrite]:
  "supf(R,f) = sup(R,f``source(f))"

lemma has_supfI [backward]:
  "order_rel(R) \<Longrightarrow> has_least(R,upper_bound(R,f``source(f))) \<and> least(R,upper_bound(R,f``source(f))) = x \<Longrightarrow>
   has_supf(R,f) \<and> supf(R,f) = x" by auto2

(* Examples *)
lemma greatest_elt_is_sup:
  "order_rel(R) \<Longrightarrow> has_greatest(R,X) \<Longrightarrow> sup(R,X) = greatest(R,X) \<and> has_sup(R,X)" by auto2

lemma least_elt_is_inf:
  "order_rel(R) \<Longrightarrow> has_least(R,X) \<Longrightarrow> inf(R,X) = least(R,X) \<and> has_inf(R,X)" by auto2

lemma sup_of_empty:
  "order_rel(R) \<Longrightarrow> has_least(R,source(R)) \<Longrightarrow> sup(R,\<emptyset>) = least(R,source(R)) \<and> has_sup(R,\<emptyset>)" by auto2

lemma inf_of_empty:
  "order_rel(R) \<Longrightarrow> has_greatest(R,source(R)) \<Longrightarrow> inf(R,\<emptyset>) = greatest(R,source(R)) \<and> has_inf(R,\<emptyset>)" by auto2

lemma sup_of_subsets:
  "X \<subseteq> Pow(E) \<Longrightarrow> has_sup(subset_order(Pow(E)),X) \<and> sup(subset_order(Pow(E)),X) = \<Union>X" by auto2

lemma inf_of_subsets:
  "X \<noteq> \<emptyset> \<Longrightarrow> X \<subseteq> Pow(E) \<Longrightarrow> has_inf(subset_order(Pow(E)),X) \<and> inf(subset_order(Pow(E)),X) = \<Inter>X" by auto2

lemma inf_le_sup:
  "order_rel(R) \<Longrightarrow> has_sup(R,X) \<Longrightarrow> has_inf(R,X) \<Longrightarrow> X \<noteq> \<emptyset> \<Longrightarrow> inf(R,X) \<le>\<^sub>R sup(R,X)" by auto2

(* For harder results, we use two lemmas *)
lemma sup_mem [typing]: "order_rel(R) \<Longrightarrow> has_sup(R,X) \<Longrightarrow> sup(R,X) \<in> source(R)" by auto2

lemma sup_le [backward2]:
  "order_rel(R) \<Longrightarrow> has_sup(R,X) \<Longrightarrow> a \<in> source(R) \<Longrightarrow> \<forall>x\<in>X. x \<le>\<^sub>R a \<Longrightarrow> sup(R,X) \<le>\<^sub>R a"
  by (tactic {* auto2s_tac @{context} (HAVE "a \<in> upper_bound(R,X)") *})

lemma sup_on_subset_le:
  "order_rel(R) \<Longrightarrow> has_sup(R,A) \<Longrightarrow> has_sup(R,B) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> sup(R,A) \<le>\<^sub>R sup(R,B)" by auto2

lemma sup_trans:
  "order_rel(R) \<Longrightarrow> f \<in> I \<rightarrow> source(R) \<Longrightarrow> g \<in> I \<rightarrow> source(R) \<Longrightarrow> \<forall>a\<in>I. f`a \<le>\<^sub>R g`a \<Longrightarrow>
   has_supf(R,f) \<Longrightarrow> has_supf(R,g) \<Longrightarrow> supf(R,f) \<le>\<^sub>R supf(R,g)" by auto2

lemma sup_cover:
  "order_rel(R) \<Longrightarrow> f \<in> I \<rightarrow> source(R) \<Longrightarrow> J \<in> L \<rightarrow> Pow(I) \<Longrightarrow> (\<Union>b\<in>L. J`b) = I \<Longrightarrow>
   \<forall>b\<in>L. has_sup(R,f``(J`b)) \<Longrightarrow> has_supf(R, \<lambda>b\<in>L. sup(R,f``(J`b))\<in>source(R)) \<Longrightarrow>
   has_supf(R,f) \<and> supf(R,f) = supf(R, \<lambda>b\<in>L. sup(R,f``(J`b))\<in>source(R))" by auto2

lemma sup_cover_inv:
  "order_rel(R) \<Longrightarrow> f \<in> I \<rightarrow> source(R) \<Longrightarrow> J \<in> L \<rightarrow> Pow(I) \<Longrightarrow> (\<Union>b\<in>L. J`b) = I \<Longrightarrow>
   \<forall>b\<in>L. has_sup(R,f``(J`b)) \<Longrightarrow> has_supf(R,f) \<Longrightarrow>
   has_supf(R, \<lambda>b\<in>L. sup(R,f``(J`b))\<in>source(R)) \<and>
   supf(R, \<lambda>b\<in>L. sup(R,f``(J`b))\<in>source(R)) = supf(R,f)" by auto2

lemma sup_double_family:
  "order_rel(R) \<Longrightarrow> f \<in> I\<times>J \<rightarrow> source(R) \<Longrightarrow> \<forall>a\<in>I. has_sup(R,f``({a}\<times>J)) \<Longrightarrow>
   has_supf(R, \<lambda>a\<in>I. sup(R,f``({a}\<times>J))\<in>source(R)) \<Longrightarrow>
   has_supf(R,f) \<and> supf(R,f) = supf(R, \<lambda>a\<in>I. sup(R,f``({a}\<times>J))\<in>source(R))" by auto2

lemma sup_double_family_inv:
  "order_rel(R) \<Longrightarrow> f \<in> I\<times>J \<rightarrow> source(R) \<Longrightarrow> \<forall>a\<in>I. has_sup(R,f``({a}\<times>J)) \<Longrightarrow>
   has_supf(R,f) \<Longrightarrow>
   has_supf(R, \<lambda>a\<in>I. sup(R,f``({a}\<times>J))\<in>source(R)) \<and>
   supf(R, \<lambda>a\<in>I. sup(R,f``({a}\<times>J))\<in>source(R)) = supf(R,f)" by auto2

lemma sup_prod:
  "\<forall>a\<in>I. order_rel(proj(R,a)) \<Longrightarrow> A \<subseteq> prod_src(I,R) \<Longrightarrow> \<forall>a\<in>I. has_sup(proj(R,a),projs(A,a)) \<Longrightarrow>
   has_sup(prod_rel(I,R),A) \<and> sup(prod_rel(I,R),A) = Tup(I, \<lambda>a. sup(proj(R,a),projs(A,a)))" by auto2

lemma sup_prod_inv:
  "\<forall>a\<in>I. order_rel(proj(R,a)) \<Longrightarrow> A \<subseteq> prod_src(I,R) \<Longrightarrow> has_sup(prod_rel(I,R),A) \<Longrightarrow>
   sup(prod_rel(I,R),A) = Tup(I, \<lambda>a. sup(proj(R,a),projs(A,a)))"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "M, M = sup(prod_rel(I,R),A)" THEN
    HAVE "\<forall>a\<in>I. \<forall>x\<in>upper_bound(proj(R,a),projs(A,a)). rel(proj(R,a),proj(M,a),x)" WITH (
      CHOOSE "f, f = Tup(I, \<lambda>b. if b = a then x else proj(M,b))" THEN
      HAVE "f \<in> upper_bound(prod_rel(I,R),A)") THEN
    HAVE "\<forall>a\<in>I. has_sup(proj(R,a),projs(A,a)) \<and> sup(proj(R,a),projs(A,a)) = proj(M,a)") *})

lemma sup_subset1:
  "order_rel(R) \<Longrightarrow> F \<subseteq> source(R) \<Longrightarrow> A \<subseteq> F \<Longrightarrow> has_sup(R,A) \<Longrightarrow> has_sup(subrel(R,F),A) \<Longrightarrow>
   sup(R,A) \<le>\<^sub>R sup(subrel(R,F),A)" by auto2

lemma sup_subset2:
  "order_rel(R) \<Longrightarrow> F \<subseteq> source(R) \<Longrightarrow> A \<subseteq> F \<Longrightarrow> has_sup(R,A) \<Longrightarrow> sup(R,A) \<in> F \<Longrightarrow>
   has_sup(subrel(R,F),A) \<and> sup(subrel(R,F),A) = sup(R,A)" by auto2

section {* Directed sets *}  (* Bourbaki III.1.10 *)

definition right_directed :: "i \<Rightarrow> o" where right_directed_def [rewrite]:
  "right_directed(R) \<longleftrightarrow> (\<forall>x\<in>source(R). \<forall>y\<in>source(R). \<exists>z\<in>source(R). z \<ge>\<^sub>R x \<and> z \<ge>\<^sub>R y)"
setup {* add_property_const @{term right_directed} *}

definition join :: "[i, i, i] \<Rightarrow> i" where join_def [rewrite]:
  "join(R,x,y) = (SOME z\<in>source(R). z \<ge>\<^sub>R x \<and> z \<ge>\<^sub>R y)"

lemma right_directedE [backward]:
  "right_directed(R) \<Longrightarrow> x \<in> source(R) \<Longrightarrow> y \<in> source(R) \<Longrightarrow> \<exists>z\<in>source(R). z \<ge>\<^sub>R x \<and> z \<ge>\<^sub>R y" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm right_directed_def} *}

lemma right_directed_join:
  "right_directed(R) \<Longrightarrow> x \<in> source(R) \<Longrightarrow> y \<in> source(R) \<Longrightarrow>
   join(R,x,y) \<in> source(R) \<and> join(R,x,y) \<ge>\<^sub>R x \<and> join(R,x,y) \<ge>\<^sub>R y" by auto2
setup {* del_prfstep_thm @{thm right_directedE} *}
setup {* add_forward_prfstep_cond @{thm right_directed_join}
  [with_cond "?x \<noteq> ?y", with_filt (order_filter "x" "y"),
   with_cond "?x \<noteq> join(?R,?u,?v)", with_cond "?y \<noteq> join(?R,?u,?v)"] *}

lemma right_directed_max_is_greatest:
  "order_rel(R) \<Longrightarrow> right_directed(R) \<Longrightarrow> a \<in> source(R) \<Longrightarrow> maximal(R,a) \<Longrightarrow>
   has_greatest(R,source(R)) \<and> greatest(R,source(R)) = a" by auto2

lemma right_directed_prod:
  "\<forall>a\<in>I. order_rel(proj(R,a)) \<Longrightarrow> \<forall>a\<in>I. right_directed(proj(R,a)) \<Longrightarrow>
   right_directed(prod_rel(I,R))"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "E, E = prod_src(I,R)" THEN
    HAVE "\<forall>x\<in>E. \<forall>y\<in>E. \<exists>z\<in>E. ge(z,prod_rel(I,R),x) \<and> ge(z,prod_rel(I,R),y)" WITH (
      CHOOSE "z\<in>E, z = Tup(I, \<lambda>a. join(proj(R,a),proj(x,a),proj(y,a)))" THEN
      HAVE "ge(z,prod_rel(I,R),x)")) *})

lemma right_directed_cofinal:
  "order_rel(R) \<Longrightarrow> right_directed(R) \<Longrightarrow> cofinal(R,A) \<Longrightarrow> right_directed(subrel(R,A))"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x\<in>A. \<forall>y\<in>A. \<exists>z\<in>A. ge(z,subrel(R,A),x) \<and> ge(z,subrel(R,A),y)" WITH (
      CHOOSE "z\<in>A, join(R,x,y) \<le>\<^sub>R z")) *}) 

section {* Totally ordered sets *}  (* Bourbaki III.1.12 *)

definition linorder_rel :: "i \<Rightarrow> o" where linorder_rel_def [rewrite]:
  "linorder_rel(R) \<longleftrightarrow> (order_rel(R) \<and> (\<forall>x\<in>source(R). \<forall>y\<in>source(R). x \<le>\<^sub>R y \<or> x \<ge>\<^sub>R y))"
setup {* add_property_const @{term linorder_rel} *}

lemma linorder_relD [forward]:
  "linorder_rel(R) \<Longrightarrow> order_rel(R)"
  "linorder_rel(R) \<Longrightarrow> \<not>(x \<le>\<^sub>R y) \<Longrightarrow> x \<in> source(R) \<Longrightarrow> y \<in> source(R) \<Longrightarrow> x >\<^sub>R y"
  "linorder_rel(R) \<Longrightarrow> \<not>(x \<ge>\<^sub>R y) \<Longrightarrow> x \<in> source(R) \<Longrightarrow> y \<in> source(R) \<Longrightarrow> x <\<^sub>R y" by auto2+
setup {* del_prfstep_thm_str "@eqforward" @{thm linorder_rel_def} *}

lemma linorder_iso [forward]:
  "linorder_rel(R) \<Longrightarrow> isomorphism(R,S,f) \<Longrightarrow> linorder_rel(S)" by auto2

lemma linorder_subrel:
  "linorder_rel(R) \<Longrightarrow> A \<subseteq> source(R) \<Longrightarrow> linorder_rel(subrel(R,A))" by auto2

lemma linorder_adjoin:
  "linorder_rel(R) \<Longrightarrow> a \<notin> source(R) \<Longrightarrow> linorder_rel(adjoin_greatest(R,a))" by auto2
setup {* add_forward_prfstep_cond @{thm linorder_adjoin} [with_term "adjoin_greatest(?R,?a)"] *}

lemma strict_monotone_to_inj:
  "linorder_rel(R) \<Longrightarrow> order_rel(S) \<Longrightarrow> is_function(f) \<Longrightarrow> strict_incr(R,S,f) \<Longrightarrow> injective(f)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x\<in>source(f). \<forall>y\<in>source(f). x \<noteq> y \<longrightarrow> f`x \<noteq> f`y" WITH CASE "x \<ge>\<^sub>R y") *})

lemma incr_to_iso [backward]:
  "linorder_rel(R) \<Longrightarrow> order_rel(S) \<Longrightarrow> bijective(f) \<Longrightarrow> incr(R,S,f) \<Longrightarrow> isomorphism(R,S,f)" by auto2

lemma supI_alt [backward1]:
  "linorder_rel(R) \<Longrightarrow> b \<in> upper_bound(R,X) \<Longrightarrow>
   \<forall>c\<in>source(R). c <\<^sub>R b \<longrightarrow> (\<exists>x\<in>X. c <\<^sub>R x \<and> x \<le>\<^sub>R b) \<Longrightarrow> has_sup(R,X) \<and> sup(R,X) = b" by auto2

lemma supD_alt [backward1]:
  "linorder_rel(R) \<Longrightarrow> has_sup(R,X) \<Longrightarrow> c \<in> source(R) \<Longrightarrow> c <\<^sub>R sup(R,X) \<Longrightarrow>
   \<exists>x\<in>X. c <\<^sub>R x \<and> x \<le>\<^sub>R sup(R,X)" by auto2

section {* Intervals *}  (* Bourbaki III.1.13 *)

definition closed_interval :: "[i, i, i] \<Rightarrow> i" where closed_interval_def [rewrite]:
  "closed_interval(R,a,b) = {x \<in> source(R). x \<le>\<^sub>R a \<and> a \<le>\<^sub>R b}"

definition open_interval :: "[i, i, i] \<Rightarrow> i" where open_interval_def [rewrite]:
  "open_interval(R,a,b) = {x \<in> source(R). x <\<^sub>R a \<and> a <\<^sub>R b}"

definition open_closed_interval :: "[i, i, i] \<Rightarrow> i" where open_closed_interval_def [rewrite]:
  "open_closed_interval(R,a,b) = {x \<in> source(R). x <\<^sub>R a \<and> a \<le>\<^sub>R b}"

definition closed_open_interval :: "[i, i, i] \<Rightarrow> i" where closed_open_interval_def [rewrite]:
  "closed_open_interval(R,a,b) = {x \<in> source(R). x \<le>\<^sub>R a \<and> a <\<^sub>R b}"

definition le_interval :: "[i, i] \<Rightarrow> i" where le_interval_def [rewrite]:
  "le_interval(R,a) = {x \<in> source(R). x \<le>\<^sub>R a}"

definition less_interval :: "[i, i] \<Rightarrow> i" where less_interval_def [rewrite]:
  "less_interval(R,a) = {x \<in> source(R). x <\<^sub>R a}"

definition ge_interval :: "[i, i] \<Rightarrow> i" where ge_interval_def [rewrite]:
  "ge_interval(R,a) = {x \<in> source(R). x \<ge>\<^sub>R a}"

definition greater_interval :: "[i, i] \<Rightarrow> i" where greater_interval_def [rewrite]:
  "greater_interval(R,a) = {x \<in> source(R). x >\<^sub>R a}"

lemma less_intervalI [typing2]: "preorder_rel(R) \<Longrightarrow> x <\<^sub>R a \<Longrightarrow> x \<in> less_interval(R,a)" by auto2
lemma less_interval_iff [rewrite]: "preorder_rel(R) \<Longrightarrow> x \<in> less_interval(R,a) \<longleftrightarrow> x <\<^sub>R a" by auto2
setup {* del_prfstep_thm @{thm less_interval_def} *}

lemma less_interval_subset: "preorder_rel(R) \<Longrightarrow> less_interval(R,a) \<subseteq> source(R)" by auto2
setup {* add_forward_prfstep_cond @{thm less_interval_subset} [with_term "less_interval(?R,?a)"] *}

lemma ge_intervalI [typing2]: "preorder_rel(R) \<Longrightarrow> x \<ge>\<^sub>R a \<Longrightarrow> x \<in> ge_interval(R,a)" by auto2
lemma ge_interval_iff [rewrite]: "preorder_rel(R) \<Longrightarrow> x \<in> ge_interval(R,a) \<longleftrightarrow> x \<ge>\<^sub>R a" by auto2
setup {* del_prfstep_thm @{thm ge_interval_def} *}

lemma ge_interval_subset: "preorder_rel(R) \<Longrightarrow> ge_interval(R,a) \<subseteq> source(R)" by auto2
setup {* add_forward_prfstep_cond @{thm ge_interval_subset} [with_term "ge_interval(?R,?a)"] *}

(* Complement of intervals with one boundary *)
lemma ge_compl_is_less [rewrite]:
  "linorder_rel(R) \<Longrightarrow> a \<in> source(R) \<Longrightarrow> source(R) - ge_interval(R,a) = less_interval(R,a)" by auto2

lemma ge_compl_is_less' [forward]:
  "linorder_rel(R) \<Longrightarrow> S \<subseteq> source(R) \<Longrightarrow> source(R) - S = ge_interval(R,a) \<Longrightarrow> a \<in> source(R) \<Longrightarrow> S = less_interval(R,a)"
  by (tactic {* auto2s_tac @{context} (HAVE "S = source(R) - (source(R) - S)") *})

(* Intervals with one boundary are distinct *)
lemma less_interval_neq [backward]:
  "linorder_rel(R) \<Longrightarrow> a \<in> source(R) \<Longrightarrow> b \<in> source(R) \<Longrightarrow> a \<noteq> b \<Longrightarrow> less_interval(R,a) \<noteq> less_interval(R,b)"
  by (tactic {* auto2s_tac @{context} (CASE "a <\<^sub>R b") *})

(* Ordering on less_interval. *)
definition less_interval_rel :: "[i, i] \<Rightarrow> i" where less_interval_rel_def [rewrite]:
  "less_interval_rel(R,x) = subrel(R,less_interval(R,x))"

lemma less_interval_rel_trans [rewrite]:
  "linorder_rel(R) \<Longrightarrow> y <\<^sub>R x \<Longrightarrow> less_interval_rel(less_interval_rel(R,x),y) = less_interval_rel(R,y)" by auto2

lemma less_interval_rel_eq_trans [forward]:
  "linorder_rel(R) \<Longrightarrow> linorder_rel(S) \<Longrightarrow> y \<le>\<^sub>R x \<Longrightarrow>
   less_interval_rel(R,x) = less_interval_rel(S,x) \<Longrightarrow> x\<in>source(S) \<Longrightarrow>
   y\<in>source(S) \<and> less_interval_rel(R,y) = less_interval_rel(S,y)"
  by (tactic {* auto2s_tac @{context} (
    CASE "y \<noteq> x" WITH HAVE "less_interval_rel(less_interval_rel(R,x),y) = less_interval_rel(R,y)") *})

(* Some lemmas about adjoin_greatest. *)
lemma adjoin_greatest_less_interval [rewrite]:
  "linorder_rel(M) \<Longrightarrow> a \<notin> source(M) \<Longrightarrow> less_interval(adjoin_greatest(M,a),a) = source(M)" by auto2

lemma adjoin_greatest_less_interval2 [rewrite]:
  "linorder_rel(M) \<Longrightarrow> a \<notin> source(M) \<Longrightarrow> x \<in> source(M) \<Longrightarrow>
   less_interval(adjoin_greatest(M,a),x) = less_interval(M,x)" by auto2

(* To show equality between a linorder and an order, can also compare <. *)
lemma eq_linorder_order_less [backward1]:
  "linorder_rel(R) \<Longrightarrow> order_rel(S) \<Longrightarrow> source(R) = source(S) \<Longrightarrow>
   \<forall>x\<in>source(R). \<forall>y\<in>source(R). x <\<^sub>R y \<longrightarrow> x <\<^sub>S y \<Longrightarrow> R = S"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x\<in>source(R). \<forall>y\<in>source(R). x \<le>\<^sub>R y \<longrightarrow> x \<le>\<^sub>S y" WITH CASE "x = y") *})

section {* Directed family of ordering *}

(* This development is used in Bourbaki III.2.1 *)
definition is_subrel :: "[i, i] \<Rightarrow> o" where is_subrel_def [rewrite]:
  "is_subrel(R,S) \<longleftrightarrow> (source(R) \<subseteq> source(S) \<and> R = subrel(S,source(R)))"

lemma is_subrelD1 [forward]: "is_subrel(R,S) \<Longrightarrow> source(R) \<subseteq> source(S)" by auto2
lemma is_subrelD2 [rewrite_bidir]:
  "is_subrel(R,S) \<Longrightarrow> x \<in> source(R) \<Longrightarrow> y \<in> source(R) \<Longrightarrow> rel(R,x,y) \<longleftrightarrow> rel(S,x,y)" by auto2
lemma is_subrel_rewr [rewrite_back]:
  "is_subrel(R,S) \<Longrightarrow> R = subrel(S,source(R))" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm is_subrel_def} *}

lemma is_subrel_refl [resolve]: "preorder_rel(R) \<Longrightarrow> is_subrel(R,R)" by auto2

definition directed_rels :: "i \<Rightarrow> o" where directed_rels_def [rewrite]:
  "directed_rels(X) \<longleftrightarrow> ((\<forall>R\<in>X. order_rel(R)) \<and>
    (\<forall>R\<in>X. \<forall>S\<in>X. \<exists>T\<in>X. is_subrel(R,T) \<and> is_subrel(S,T)))"
setup {* add_property_const @{term directed_rels} *}

lemma directed_relsD1 [forward]:
  "directed_rels(X) \<Longrightarrow> R \<in> X \<Longrightarrow> order_rel(R)" by auto2
lemma directed_relsD2 [backward]:
  "directed_rels(X) \<Longrightarrow> R \<in> X \<Longrightarrow> S \<in> X \<Longrightarrow> \<exists>T\<in>X. is_subrel(R,T) \<and> is_subrel(S,T)" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm directed_rels_def} *}

(* Union of a family of ordering. Has good properties when the family is directed. *)
definition union_src :: "i \<Rightarrow> i" where union_src_def [rewrite]:
  "union_src(X) = (\<Union>R\<in>X. source(R))"

definition union_rel :: "i \<Rightarrow> i" where union_rel_def [rewrite]:
  "union_rel(X) = Rel(union_src(X), \<lambda>x y. \<exists>R\<in>X. rel(R,x,y))"

lemma union_rel_is_rel [typing]: "union_rel(X) \<in> rel_space(union_src(X))" by auto2

lemma union_rel_eval [rewrite]:
  "x \<in> union_src(X) \<Longrightarrow> y \<in> union_src(X) \<Longrightarrow> rel(union_rel(X),x,y) \<longleftrightarrow> (\<exists>R\<in>X. rel(R,x,y))" by auto2
setup {* del_prfstep_thm @{thm union_rel_def} *}

lemma directed_elt_in_rel2 [backward]:
  "directed_rels(X) \<Longrightarrow> x \<in> union_src(X) \<Longrightarrow> y \<in> union_src(X) \<Longrightarrow>
   \<exists>R\<in>X. x \<in> source(R) \<and> y \<in> source(R)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "R\<in>X, x\<in>source(R)" THEN
    CHOOSE "S\<in>X, y\<in>source(S)" THEN
    CHOOSE "T\<in>X, is_subrel(R,T) \<and> is_subrel(S,T)") *})

lemma directed_elt_in_rel3 [backward]:
  "directed_rels(X) \<Longrightarrow> x \<in> union_src(X) \<Longrightarrow> y \<in> union_src(X) \<Longrightarrow> z \<in> union_src(X) \<Longrightarrow>
   \<exists>R\<in>X. x \<in> source(R) \<and> y \<in> source(R) \<and> z \<in> source(R)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "R\<in>X, x\<in>source(R) \<and> y\<in>source(R)" THEN
    CHOOSE "S\<in>X, z\<in>source(S)" THEN
    CHOOSE "T\<in>X, is_subrel(R,T) \<and> is_subrel(S,T)") *})

lemma union_rel_prop:
  "directed_rels(X) \<Longrightarrow> R \<in> X \<Longrightarrow> is_subrel(R,union_rel(X))"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x\<in>source(R). \<forall>y\<in>source(R). rel(R,x,y) \<longleftrightarrow> rel(union_rel(X),x,y)" WITH (
      CASE "rel(union_rel(X),x,y)" WITH (
        CHOOSE "S\<in>X, rel(S,x,y)" THEN
        CHOOSE "T\<in>X, is_subrel(R,T) \<and> is_subrel(S,T)"))) *})
setup {* add_forward_prfstep_cond @{thm union_rel_prop} [with_term "union_rel(?X)"] *}

lemma union_rel_unique_prop:
  "directed_rels(X) \<Longrightarrow> order_rel(R) \<Longrightarrow> source(R) = union_src(X) \<Longrightarrow>
   \<forall>S\<in>X. is_subrel(S,R) \<Longrightarrow> R = union_rel(X)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x\<in>union_src(X). \<forall>y\<in>union_src(X). rel(R,x,y) \<longleftrightarrow> rel(union_rel(X),x,y)" WITH (
      CHOOSE "S\<in>X, x\<in>source(S) \<and> y\<in>source(S)")) *})

lemma union_rel_preorder [forward]:
  "directed_rels(X) \<Longrightarrow> preorder_rel(union_rel(X))"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "E, E = union_src(X)" THEN
    CHOOSE "R, R = union_rel(X)" THEN
    HAVE "\<forall>x y z. rel(R,x,y) \<longrightarrow> rel(R,y,z) \<longrightarrow> rel(R,x,z)" WITH (
      CHOOSE "S\<in>X, x \<in> source(S) \<and> y \<in> source(S) \<and> z \<in> source(S)")) *})

lemma union_rel_order [forward]:
  "directed_rels(X) \<Longrightarrow> order_rel(union_rel(X))"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "E, E = union_src(X)" THEN
    CHOOSE "R, R = union_rel(X)" THEN
    HAVE "\<forall>x\<in>E. \<forall>y\<in>E. x \<le>\<^sub>R y \<longrightarrow> y \<le>\<^sub>R x \<longrightarrow> x = y" WITH (
      CHOOSE "S\<in>X, x \<in> source(S) \<and> y \<in> source(S)")) *})

lemma union_rel_linorder [backward]:
  "directed_rels(X) \<Longrightarrow> \<forall>R\<in>X. linorder_rel(R) \<Longrightarrow> linorder_rel(union_rel(X))"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "E, E = union_src(X)" THEN
    CHOOSE "R, R = union_rel(X)" THEN
    HAVE "\<forall>x\<in>E. \<forall>y\<in>E. x \<le>\<^sub>R y \<or> x \<ge>\<^sub>R y" WITH (
      CHOOSE "S\<in>X, x \<in> source(S) \<and> y \<in> source(S)")) *})

end
