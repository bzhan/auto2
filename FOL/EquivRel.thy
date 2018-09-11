(*
  File: EquivRel.thy
  Author: Bohua Zhan

  Basics of equivalence relations and quotient sets, including the three
  isomorphism theorems on sets.
*)

theory EquivRel
  imports Coverings
begin

section \<open>Equivalence structures\<close>

definition "equiv_graph_name = succ(succ(\<emptyset>))"
definition "equiv_graph(S) = graph_eval(S, equiv_graph_name)"
setup {* add_field_data (@{term equiv_graph_name}, @{term equiv_graph}) *}

definition rawequiv :: "i \<Rightarrow> o" where [rewrite]:
  "rawequiv(R) \<longleftrightarrow>
    is_func_graph(R,{carrier_name,equiv_graph_name}) \<and> equiv_graph(R) \<in> Pow(carrier(R)\<times>carrier(R))"

lemma rawequiv_graph_is_graph [forward]:
  "rawequiv(R) \<Longrightarrow> is_graph(equiv_graph(R))" by auto2

(* Space of all rawequiv on S *)
definition rawequiv_space :: "i \<Rightarrow> i" where [rewrite]:
  "rawequiv_space(S) = {Struct({\<langle>carrier_name,S\<rangle>, \<langle>equiv_graph_name,G\<rangle>}). G\<in>Pow(S\<times>S)}"
  
lemma rawequiv_spaceD [forward]:
  "R \<in> rawequiv_space(S) \<Longrightarrow> rawequiv(R) \<and> carrier(R) = S" by auto2
    
lemma rawequiv_spaceI [resolve]:
  "rawequiv(R) \<Longrightarrow> R \<in> rawequiv_space(carrier(R))" by auto2

(* Constructor for equivalence *)
definition Equiv :: "i \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> o) \<Rightarrow> i" where [rewrite]:
  "Equiv(S,R) = Struct({\<langle>carrier_name,S\<rangle>, \<langle>equiv_graph_name, rel_graph(S,R)\<rangle>})"

lemma Equiv_is_rawequiv [typing]: "Equiv(S,R) \<in> rawequiv_space(S)" by auto2

(* Evaluation of equiv *)
definition eq_sim :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o" ("(_/ \<sim>\<^sub>_ _)" [51,51,51] 50) where [rewrite_bidir]:
  "x \<sim>\<^sub>R y \<longleftrightarrow> \<langle>x,y\<rangle> \<in> equiv_graph(R)"
setup {* register_wellform_data ("x \<sim>\<^sub>R y", ["x \<in>. R", "y \<in>. R"]) *}

lemma Equiv_eval [rewrite]:
  "R = Equiv(S,f) \<Longrightarrow> x \<sim>\<^sub>R y \<longleftrightarrow> (x \<in> S \<and> y \<in> S \<and> f(x,y))" by auto2

lemma rawequivD [forward]:
  "rawequiv(R) \<Longrightarrow> x \<sim>\<^sub>R y \<Longrightarrow> x \<in>. R \<and> y \<in>. R" by auto2

(* Equality on equivalences *)
lemma equiv_eq [backward]:
  "rawequiv(R) \<Longrightarrow> rawequiv(S) \<Longrightarrow> carrier(R) = carrier(S) \<Longrightarrow>
   \<forall>x y. x \<sim>\<^sub>R y \<longleftrightarrow> x \<sim>\<^sub>S y \<Longrightarrow> R = S" by auto2

setup {* fold del_prfstep_thm [
  @{thm rawequiv_def}, @{thm rawequiv_space_def}, @{thm Equiv_def}, @{thm eq_sim_def}] *}

section {* Equivalence relation *}  (* Bourbaki II.6.1 *)

(* Self-contained condition for equiv. *)
definition equiv :: "i \<Rightarrow> o" where [rewrite]:
  "equiv(R) \<longleftrightarrow>
    rawequiv(R) \<and>
    (\<forall>x\<in>.R. x \<sim>\<^sub>R x) \<and>
    (\<forall>x y. x \<sim>\<^sub>R y \<longrightarrow> y \<sim>\<^sub>R x) \<and>
    (\<forall>x y z. x \<sim>\<^sub>R y \<longrightarrow> y \<sim>\<^sub>R z \<longrightarrow> x \<sim>\<^sub>R z)"

lemma equivD:
  "equiv(R) \<Longrightarrow> rawequiv(R)"
  "equiv(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> x \<sim>\<^sub>R x"
  "equiv(R) \<Longrightarrow> x \<sim>\<^sub>R y \<longleftrightarrow> y \<sim>\<^sub>R x"
  "equiv(R) \<Longrightarrow> x \<sim>\<^sub>R y \<Longrightarrow> y \<sim>\<^sub>R z \<Longrightarrow> x \<sim>\<^sub>R z" by auto2+
setup {* add_forward_prfstep @{thm equivD(1)} *}
setup {* add_backward_prfstep @{thm equivD(2)} *}
setup {* add_rewrite_rule @{thm equivD(3)} *}
setup {* add_forward_prfstep_cond @{thm equivD(4)} [with_cond "?x \<noteq> ?z"] *}
setup {* del_prfstep_thm_eqforward @{thm equiv_def} *}

definition equiv_space :: "i \<Rightarrow> i" where [rewrite]:
  "equiv_space(S) = {R\<in>rawequiv_space(S). equiv(R)}"

lemma equiv_spaceD [forward]:
  "R \<in> equiv_space(S) \<Longrightarrow> equiv(R) \<and> carrier(R) = S" by auto2
    
lemma equiv_spaceI [backward]:
  "equiv(R) \<Longrightarrow> R \<in> equiv_space(carrier(R))" by auto2
setup {* del_prfstep_thm @{thm equiv_space_def} *}

section {* Quotient construction *}  (* Bourbaki II.6.2 *)

(* Equivalence relation induced by a function *)
definition fun_equiv :: "i \<Rightarrow> i" where [rewrite]:
  "fun_equiv(f) = Equiv(source(f), \<lambda>x y. f`x = f`y)"

lemma fun_equiv_is_equiv [typing]:
  "fun_equiv(f) \<in> equiv_space(source(f))" by auto2

lemma fun_equiv_eval [rewrite]:
  "R = fun_equiv(f) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x \<sim>\<^sub>R y \<longleftrightarrow> f`x = f`y" by auto2
setup {* del_prfstep_thm @{thm fun_equiv_def} *}

(* Definition of quotient set as set of equivalence classes. *)
definition equiv_class :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "equiv_class(R,x) = {y\<in>.R. x \<sim>\<^sub>R y}"
setup {* register_wellform_data ("equiv_class(R,x)", ["x \<in>. R"]) *}

lemma equiv_class_iff [rewrite]:
  "equiv(R) \<Longrightarrow> y \<in> equiv_class(R,x) \<longleftrightarrow> (y \<in>. R \<and> x \<sim>\<^sub>R y)" by auto2
setup {* del_prfstep_thm @{thm equiv_class_def} *}

lemma equiv_class_mem [typing2]: "equiv(R) \<Longrightarrow> x \<sim>\<^sub>R y \<Longrightarrow> y \<in> equiv_class(R,x)" by auto2

lemma equiv_class_eq [rewrite]:
  "equiv(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> equiv_class(R,x) = equiv_class(R,y) \<longleftrightarrow> x \<sim>\<^sub>R y"
@proof @have "x \<sim>\<^sub>R x" @qed

(* Usually E = carrier(R) *)
definition quotient_set :: "[i, i] \<Rightarrow> i"  (infixl "'/'/" 90) where [rewrite]:
  "E // R = {equiv_class(R,x). x\<in>E}"

lemma quotient_setI [typing, backward]:
  "y \<in>. R \<Longrightarrow> equiv_class(R,y) \<in> carrier(R)//R" by auto2

lemma quotient_set_union [rewrite]:
  "equiv(R) \<Longrightarrow> \<Union>(carrier(R)//R) = carrier(R)" by auto2
  
(* Choose a representative for x, under the equivalence relation R. *)
definition rep :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "rep(R,x) = Choice(x)"
setup {* register_wellform_data ("rep(R,x)", ["x \<in> carrier(R)//R"]) *}

lemma rep_in_set [typing]: "equiv(R) \<Longrightarrow> x \<in> carrier(R)//R \<Longrightarrow> rep(R,x) \<in>. R" by auto2

lemma equiv_class_of_rep: "equiv(R) \<Longrightarrow> x \<in> carrier(R)//R \<Longrightarrow> equiv_class(R,rep(R,x)) = x" by auto2
setup {* add_forward_prfstep_cond @{thm equiv_class_of_rep} [with_term "rep(?R,?x)"] *}

lemma rep_in_equiv_class: "equiv(R) \<Longrightarrow> y \<in>. R \<Longrightarrow> rep(R,equiv_class(R,y)) \<sim>\<^sub>R y" by auto2
setup {* add_forward_prfstep_cond @{thm rep_in_equiv_class} [with_term "rep(?R,equiv_class(?R,?y))"] *} 

setup {* fold del_prfstep_thm [@{thm rep_def}, @{thm quotient_set_def}] *}

(* Definition of canonical surjection *)
definition qsurj :: "i \<Rightarrow> i" where [rewrite]:
  "qsurj(R) = Fun(carrier(R), carrier(R)//R, \<lambda>x. equiv_class(R,x))"

lemma qsurj_is_fun [typing]: "qsurj(R) \<in> carrier(R) \<rightarrow> carrier(R)//R" by auto2

lemma qsurj_is_surj [forward]: "equiv(R) \<Longrightarrow> surjective(qsurj(R))"
@proof @have (@rule) "\<forall>x\<in>carrier(R)//R. qsurj(R)`rep(R,x) = x" @qed

lemma qsurj_eval [rewrite]:
  "x \<in> source(qsurj(R)) \<Longrightarrow> qsurj(R)`x = equiv_class(R,x)" by auto2
setup {* del_prfstep_thm @{thm qsurj_def} *}

lemma qsurj_eq_iff1:
  "equiv(R) \<Longrightarrow> x \<sim>\<^sub>R y \<Longrightarrow> qsurj(R)`x = qsurj(R)`y" by auto2
setup {* add_rewrite_rule_cond @{thm qsurj_eq_iff1} [with_cond "?x \<noteq> ?y"] *}

lemma qsurj_eq_iff2:
  "equiv(R) \<Longrightarrow> x \<in> source(qsurj(R)) \<Longrightarrow> y \<in> source(qsurj(R)) \<Longrightarrow>
   qsurj(R)`x = qsurj(R)`y \<Longrightarrow> x \<sim>\<^sub>R y" by auto2
setup {* add_forward_prfstep_cond @{thm qsurj_eq_iff2} [with_cond "?x \<noteq> ?y", with_filt (order_filter "x" "y")] *}

(* We show that every equivalence relation is induced by some function. *)
lemma qsurj_equiv: "equiv(R) \<Longrightarrow> R = fun_equiv(qsurj(R))" by auto2

(* Examples *)
definition eq_equiv :: "i \<Rightarrow> i" where [rewrite]:
  "eq_equiv(E) = Equiv(E, \<lambda>x y. x = y)"

lemma eq_equiv_is_equiv [typing]: "eq_equiv(E) \<in> equiv_space(E)" by auto2

lemma qsurj_triv_bij: "qsurj(eq_equiv(E)) \<in> E \<cong> E//eq_equiv(E)" by auto2

definition eq_fst_rel :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "eq_fst_rel(E,F) = Equiv(E\<times>F, \<lambda>u v. fst(u) = fst(v))"

lemma eq_fst_rel_is_equiv [typing]: "eq_fst_rel(E,F) \<in> equiv_space(E\<times>F)" by auto2

lemma eq_fst_rel_eval [rewrite]:
  "R = eq_fst_rel(E,F) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x \<sim>\<^sub>R y \<longleftrightarrow> fst(x) = fst(y)" by auto2
setup {* del_prfstep_thm @{thm eq_fst_rel_def} *}

(* Elements of quotient form a partition. Conversely, every partition is a quotient set. *)
lemma equiv_class_disjoint [backward]:
  "equiv(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> \<not>x \<sim>\<^sub>R y \<Longrightarrow>
   equiv_class(R,x) \<inter> equiv_class(R,y) = \<emptyset>" by auto2

lemma equiv_classes_is_partition:
  "equiv(R) \<Longrightarrow> is_partition_sets(carrier(R),carrier(R)//R)"
@proof @have (@rule) "\<forall>x\<in>carrier(R)//R. x = equiv_class(R,rep(R,x))" @qed

lemma partition_mem_unique [backward]:
  "mutually_disjoint_sets(X) \<Longrightarrow> a \<in> \<Union>X \<Longrightarrow> \<exists>!x. x \<in> X \<and> a \<in> x" by auto2

definition partition_mem :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "partition_mem(X,u) = (THE x. x \<in> X \<and> u \<in> x)"

definition partition_equiv :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "partition_equiv(X,u,v) \<longleftrightarrow> (u \<in> \<Union>X \<and> v \<in> \<Union>X \<and> (partition_mem(X,u) = partition_mem(X,u)))"

section {* Predicate compatible with an equivalence relation *}  (* Bourbaki II.6.3 *)

definition compat_pred :: "[i \<Rightarrow> o, i] \<Rightarrow> o" where [rewrite]:
  "compat_pred(P,R) \<longleftrightarrow> (\<forall>x y. P(x) \<longrightarrow> x \<sim>\<^sub>R y \<longrightarrow> P(y))"

lemma compat_relD [forward]:
  "compat_pred(P,R) \<Longrightarrow> x \<sim>\<^sub>R y \<Longrightarrow> P(x) \<longrightarrow> P(y)" by auto2
setup {* del_prfstep_thm_eqforward @{thm compat_pred_def} *}

(* Example *)
lemma compat_pred_eq_equiv: "compat_pred(P, eq_equiv(E))" by auto2

(* Given a equivalence relation R on E, can induce a predicate on E//R *)
definition induced_pred :: "[i \<Rightarrow> o, i, i] \<Rightarrow> o" where [rewrite]:
  "induced_pred(P,R,t) \<longleftrightarrow> (t \<in> carrier(R)//R \<and> (\<exists>x\<in>t. P(x)))"

lemma induced_pred_iff:
  "equiv(R) \<Longrightarrow> x \<in> source(qsurj(R)) \<Longrightarrow> compat_pred(P,R) \<Longrightarrow>
   induced_pred(P,R,qsurj(R)`x) \<longleftrightarrow> P(x)" by auto2

section {* Saturated subsets *}  (* Bourbaki II.6.4 *)

definition saturated_subset :: "[i, i] \<Rightarrow> o" where [rewrite]:
  "saturated_subset(R,A) \<longleftrightarrow> (A \<subseteq> carrier(R) \<and> compat_pred(\<lambda>x. x\<in>A, R))"

lemma saturated_subset_iff:
  "equiv(R) \<Longrightarrow> saturated_subset(R,A) \<longleftrightarrow> (A \<subseteq> carrier(R) \<and> (\<forall>x\<in>A. equiv_class(R,x) \<subseteq> A))" by auto2

lemma saturated_subset_iff2:
  "equiv(R) \<Longrightarrow> saturated_subset(R,A) \<longleftrightarrow> (A \<subseteq> carrier(R) \<and> A = (\<Union>x\<in>A. equiv_class(R,x)))" by auto2

lemma equiv_class_alt:
  "equiv(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> equiv_class(R,x) = qsurj(R) -`` {qsurj(R) ` x}" by auto2

lemma saturated_subset_alt [resolve]:
  "equiv(R) \<Longrightarrow> saturated_subset(R,A) \<longleftrightarrow> A = qsurj(R) -`` (qsurj(R) `` A)" by auto2

(* Put above lemma into a form that is good for rewriting. *)
lemma saturated_subset_alt' [rewrite]:
  "equiv(R) \<Longrightarrow> saturated_subset(R,A) \<Longrightarrow> qsurj(R) -`` (qsurj(R) `` A) = A" by auto2

lemma saturated_subset_alt2:
  "equiv(R) \<Longrightarrow> saturated_subset(R,A) \<longleftrightarrow> (\<exists>B. B \<subseteq> carrier(R)//R \<and> A = qsurj(R) -`` B)"
@proof @have "saturated_subset(R,A) \<longleftrightarrow> A = qsurj(R) -`` (qsurj(R) `` A)" @qed

lemma saturated_subset_union [backward]:
  "equiv(R) \<Longrightarrow> \<forall>a\<in>I. saturated_subset(R,X(a)) \<Longrightarrow> saturated_subset(R,\<Union>a\<in>I. X(a))" by auto2

lemma saturated_subset_inter [backward]:
  "equiv(R) \<Longrightarrow> I \<noteq> \<emptyset> \<Longrightarrow> \<forall>a\<in>I. saturated_subset(R,X(a)) \<Longrightarrow> saturated_subset(R,\<Inter>a\<in>I. X(a))" by auto2

lemma saturated_subset_comp [backward]:
  "equiv(R) \<Longrightarrow> saturated_subset(R,A) \<Longrightarrow> saturated_subset(R,carrier(R) \<midarrow> A)" by auto2

definition saturation_subset :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "saturation_subset(R,A) = (qsurj(R) -`` (qsurj(R) `` A))"

lemma saturation_subset_prop1:
  "equiv(R) \<Longrightarrow> A \<subseteq> carrier(R) \<Longrightarrow> A \<subseteq> saturation_subset(R,A)" by auto2

lemma saturation_subset_prop2:
  "equiv(R) \<Longrightarrow> saturated_subset(R,A') \<Longrightarrow> A \<subseteq> A' \<Longrightarrow> saturation_subset(R,A) \<subseteq> A'" by auto2

(* Alternative definition *)
lemma saturation_subset_alt [resolve]:
  "equiv(R) \<Longrightarrow> saturation_subset(R,A) = (\<Union>x\<in>A. equiv_class(R,x))" by auto2

lemma saturation_subset_union:
  "equiv(R) \<Longrightarrow> saturation_subset(R,\<Union>a\<in>I. X(a)) = (\<Union>a\<in>I. saturation_subset(R,X(a)))" by auto2

section {* Mappings compatible with an equivalence relation *}  (* Bourbaki II.6.5 *)

definition compat_fun :: "[i, i] \<Rightarrow> o" where [rewrite]:
  "compat_fun(f,R) \<longleftrightarrow> (source(f) = carrier(R) \<and> (\<forall>x y. x \<sim>\<^sub>R y \<longrightarrow> f`x = f`y))"

lemma compat_funD [forward]:
  "compat_fun(f,R) \<Longrightarrow> source(f) = carrier(R)"
  "compat_fun(f,R) \<Longrightarrow> x \<sim>\<^sub>R y \<Longrightarrow> f`x = f`y" by auto2+
setup {* del_prfstep_thm_eqforward @{thm compat_fun_def} *}

(* Alternative definition *)
lemma compat_fun_alt:
  "is_function(f) \<Longrightarrow> equiv(R) \<Longrightarrow>
   compat_fun(f,R) \<longleftrightarrow> (source(f) = carrier(R) \<and> (\<forall>x\<in>source(f). \<forall>y\<in>equiv_class(R,x). f`x = f`y))" by auto2

(* Compatible functions pass to the quotient. *)
lemma exists_induced_fun [backward]:
  "equiv(R) \<Longrightarrow> f \<in> E \<rightarrow> F \<Longrightarrow> compat_fun(f,R) \<Longrightarrow> \<exists>!h. h\<in>(E//R)\<rightarrow>F \<and> f = h \<circ> qsurj(R)"
@proof @have "\<forall>x\<in>E. \<forall>y\<in>E. qsurj(R)`x = qsurj(R)`y \<longrightarrow> f`x = f`y" @qed

definition induced_fun :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "induced_fun(f,R) = (THE h. h \<in> (source(f)//R)\<rightarrow>target(f) \<and> f = h \<circ> qsurj(R))"
setup {* register_wellform_data ("induced_fun(f,R)", ["compat_fun(f,R)"]) *}
setup {* add_prfstep_check_req ("induced_fun(f,R)", "compat_fun(f,R)") *}

lemma induced_fun_prop:
  "func_form(f) \<Longrightarrow> equiv(R) \<Longrightarrow> compat_fun(f,R) \<Longrightarrow>
   induced_fun(f,R) \<in> (source(f)//R)\<rightarrow>target(f) \<and> f = induced_fun(f,R) \<circ> qsurj(R)" by auto2
setup {* add_forward_prfstep_cond @{thm induced_fun_prop} [with_term "induced_fun(?f,?R)"] *}

lemma induced_fun_eval [rewrite]:
  "func_form(f) \<Longrightarrow> equiv(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> compat_fun(f,R) \<Longrightarrow>
   induced_fun(f,R) ` equiv_class(R,x) = f ` x" by auto2
setup {* del_prfstep_thm @{thm induced_fun_def} *}

(* Conversely, any function that passes to the quotient must be compatible. *)
lemma induced_fun_means_compat:
  "equiv(R) \<Longrightarrow> h \<in> (carrier(R)//R)\<rightarrow>F \<Longrightarrow> compat_fun(h \<circ> qsurj(R), R)" by auto2

(* f is compatible with its own induced equivalence relation. *)
lemma fun_equiv_compat: "compat_fun(f,fun_equiv(f))" by auto2
setup {* add_forward_prfstep_cond @{thm fun_equiv_compat} [with_term "fun_equiv(?f)"] *}

(* Canonical decomposition. *)
lemma injective_induced_fun:
  "func_form(f) \<Longrightarrow> g = induced_fun(f,fun_equiv(f)) \<Longrightarrow> injective(g)"
@proof
  @have "\<forall>x\<in>source(g). \<forall>y\<in>source(g). g`x = g`y \<longrightarrow> x = y" @with
    @let "x = rep(fun_equiv(f),x)" "y' = rep(fun_equiv(f),y)"
  @end
@qed
setup {* add_forward_prfstep_cond @{thm injective_induced_fun} [with_term "induced_fun(?f,fun_equiv(?f))"] *}

(* Putting everything together, statement of canonical decomposition. *)
lemma canonical_decomposition:
  "f \<in> E \<rightarrow> F \<Longrightarrow> R = fun_equiv(f) \<Longrightarrow> f' = induced_fun(f,R) \<Longrightarrow>
   f = (inj_fun(f'``(E//R),F) \<circ> func_restrict_image(f')) \<circ> qsurj(R)" by auto2

lemma first_isomorphism_theorem [typing]:
  "func_form(f) \<Longrightarrow> A = source(f) \<Longrightarrow> R = fun_equiv(f) \<Longrightarrow>
   func_restrict_image(induced_fun(f,R)) \<in> A//R \<cong> f``A"
@proof
  @let "i = induced_fun(f,R)"
  @let "g = func_restrict_image(induced_fun(f,R))"
  @have "\<forall>z\<in>i``source(i). z \<in> f``A" @with
    @obtain "y\<in>source(g)" where "g`y = z"
    @obtain "x\<in>source(qsurj(R))" where "qsurj(R)`x = y"
  @end
@qed

lemma first_isomorphism_theorem_surj [typing]:
  "func_form(f) \<Longrightarrow> surjective(f) \<Longrightarrow> A = source(f) \<Longrightarrow> R = fun_equiv(f) \<Longrightarrow>
   induced_fun(f,R) \<in> A//R \<cong> target(f)" by auto2

definition compat_fun_double :: "[i, i, i] \<Rightarrow> o" where [rewrite]:
  "compat_fun_double(f,R,S) \<longleftrightarrow> (source(f) = carrier(R) \<and> target(f) = carrier(S) \<and>
    (\<forall>x y. x \<sim>\<^sub>R y \<longrightarrow> f`x \<sim>\<^sub>S f`y))"

definition induced_fun_double :: "[i, i, i] \<Rightarrow> i" where [rewrite]:
  "induced_fun_double(f,R,S) = induced_fun(qsurj(S) \<circ> f, R)"

lemma induced_fun_double_prop:
  "is_function(f) \<Longrightarrow> equiv(R) \<Longrightarrow> equiv(S) \<Longrightarrow> compat_fun_double(f,R,S) \<Longrightarrow>
   induced_fun_double(f,R,S) \<in> source(f)//R \<rightarrow> target(f)//S \<and>
   qsurj(S) \<circ> f = induced_fun_double(f,R,S) \<circ> qsurj(R)" by auto2

section {* Inverse image of an equivalence relation *}  (* Bourbaki II.6.6 *)

definition vImage_equiv :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "vImage_equiv(f,S) = fun_equiv(qsurj(S) \<circ> f)"
setup {* register_wellform_data ("vImage_equiv(f,S)", ["target(f) = carrier(S)"]) *}

lemma vImage_equiv_is_equiv:
  "is_function(f) \<Longrightarrow> equiv(S) \<Longrightarrow> target(f) = carrier(S) \<Longrightarrow>
   equiv(vImage_equiv(f,S)) \<and> carrier(vImage_equiv(f,S)) = source(f)" by auto2
setup {* add_forward_prfstep_cond @{thm vImage_equiv_is_equiv} [with_term "vImage_equiv(?f,?S)"] *}

lemma vImage_equiv_iff [rewrite]:
  "is_function(f) \<Longrightarrow> equiv(S) \<Longrightarrow> target(f) = carrier(S) \<Longrightarrow>
   R = vImage_equiv(f,S) \<Longrightarrow> x \<in> source(f) \<Longrightarrow> y \<in> source(f) \<Longrightarrow> x \<sim>\<^sub>R y \<longleftrightarrow> f`x \<sim>\<^sub>S f`y" by auto2

lemma vImage_equiv_classes:
  "is_function(f) \<Longrightarrow> equiv(S) \<Longrightarrow> target(f) = carrier(S) \<Longrightarrow>
   x \<in> source(f) \<Longrightarrow> equiv_class(vImage_equiv(f,S),x) = f -`` equiv_class(S,f`x)" by auto2

(* Given subset A of E, pullback an equivalence relation R on E to an equivalence
   relation on A. *)
definition subset_equiv :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "subset_equiv(R,A) = vImage_equiv(inj_fun(A,carrier(R)),R)"

lemma inj_compat_double:
  "equiv(R) \<Longrightarrow> E = carrier(R) \<Longrightarrow> A \<subseteq> E \<Longrightarrow>
   compat_fun_double(inj_fun(A,E),subset_equiv(R,A),R)" by auto2

lemma second_isomorphism_theorem:
  "E = carrier(R) \<Longrightarrow> A \<subseteq> E \<Longrightarrow> R_A = subset_equiv(R,A) \<Longrightarrow>
   func_restrict_image(induced_fun_double(inj_fun(A,E),R_A,R)) \<in> A//R_A \<cong> qsurj(R) `` A"
@proof
  @let "f = induced_fun_double(inj_fun(A,E),R_A,R)"
  @have "\<forall>x. x \<in> image(f) \<longleftrightarrow> x \<in> qsurj(R) `` A" @with
    @case "x \<in> qsurj(R) `` A" @with
      @obtain "y \<in> A" where "qsurj(R)`y = x"
      @have "f`equiv_class(R_A,y) = x"
    @end
    @case "x \<in> image(f)" @with
      @obtain "y \<in> source(f)" where "f`y = x"
      @let "y' = rep(R_A,y)"
    @end
  @end
@qed
  
section {* Quotients of equivalence relations *}  (* Bourbaki II.6.7 *)

(* Finer condition can be defined on all relations *)
definition finer_rel :: "[i, i] \<Rightarrow> o" where [rewrite]:
  "finer_rel(R,S) \<longleftrightarrow> (carrier(R) = carrier(S) \<and> (\<forall>x y. x \<sim>\<^sub>R y \<longrightarrow> x \<sim>\<^sub>S y))"

(* Exercises *)
lemma finer_equiv1:
  "equiv(R) \<Longrightarrow> equiv(S) \<Longrightarrow> finer_rel(R,S) \<longleftrightarrow>
   (carrier(R) = carrier(S) \<and> (\<forall>x\<in>.R. equiv_class(R,x) \<subseteq> equiv_class(S,x)))" by auto2

lemma finer_equiv2:
  "equiv(R) \<Longrightarrow> equiv(S) \<Longrightarrow> finer_rel(R,S) \<longleftrightarrow>
   (carrier(R) = carrier(S) \<and> (\<forall>x\<in>.R. saturated_subset(R,equiv_class(S,x))))" by auto2

lemma finer_equiv_top:
  "equiv(R) \<Longrightarrow> finer_rel(eq_equiv(carrier(R)), R)" by auto2

lemma finer_equiv_bottom:
  "equiv(R) \<Longrightarrow> finer_rel(R, Equiv(carrier(R), \<lambda>x y. True))" by auto2

(* Now the serious business of this section *)

(* Assume R and S are equivalence relations on the same set, and S is finer than R. *)
definition quotient_rel :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "quotient_rel(R,S) = fun_equiv(induced_fun(qsurj(R),S))"

lemma compat_finer_equiv:
  "equiv(R) \<Longrightarrow> equiv(S) \<Longrightarrow> finer_rel(S,R) \<Longrightarrow>
   compat_fun(qsurj(R),S) \<and> induced_fun(qsurj(R),S) \<in> carrier(R)//S \<rightarrow> carrier(R)//R \<and>
   surjective(induced_fun(qsurj(R),S))" by auto2
setup {* add_forward_prfstep_cond @{thm compat_finer_equiv} [with_term "induced_fun(qsurj(?R),?S)"] *}

lemma finer_induced_fun_eval [rewrite]:
  "equiv(R) \<Longrightarrow> equiv(S) \<Longrightarrow> x \<in>. S \<Longrightarrow> finer_rel(S,R) \<Longrightarrow>
   induced_fun(qsurj(R),S) ` equiv_class(S,x) = equiv_class(R,x)" by auto2

lemma quotient_rel_iff [rewrite_back]:
  "equiv(R) \<Longrightarrow> equiv(S) \<Longrightarrow> x\<in>source(qsurj(S)) \<Longrightarrow> y\<in>source(qsurj(S)) \<Longrightarrow> finer_rel(S,R) \<Longrightarrow>
   Q = quotient_rel(R,S) \<Longrightarrow> x \<sim>\<^sub>R y \<longleftrightarrow> qsurj(S)`x \<sim>\<^sub>Q qsurj(S)`y" by auto2

definition third_isomorphism :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "third_isomorphism(R,S) = induced_fun(induced_fun(qsurj(R),S),quotient_rel(R,S))"

lemma third_isomorphism_theorem:
  "equiv(R) \<Longrightarrow> equiv(S) \<Longrightarrow> finer_rel(S,R) \<Longrightarrow>
   third_isomorphism(R,S) \<in> (carrier(R)//S)//(quotient_rel(R,S)) \<cong> carrier(R)//R" by auto2

(* Given an equivalence relation S on E, and an equivalence relation T on E//S,
   the pullback of T on the surjection E \<rightarrow> E//S is an equivalence relation on E coarser than S. *)
lemma vImage_finer [resolve]:
  "equiv(S) \<Longrightarrow> equiv(T) \<Longrightarrow> target(qsurj(S)) = carrier(T) \<Longrightarrow>
   finer_rel(S,vImage_equiv(qsurj(S),T))" by auto2

(* Any equivalence relation T on E//S is the quotient between a coarser equivalence relation R and S. *)
lemma equiv_is_quotient_rel:
  "equiv(S) \<Longrightarrow> equiv(T) \<Longrightarrow> carrier(T) = carrier(S)//S \<Longrightarrow> T = quotient_rel(vImage_equiv(qsurj(S),T),S)"
@proof
  @have "finer_rel(S,vImage_equiv(qsurj(S),T))"
  @have (@rule) "\<forall>y\<in>target(qsurj(S)). \<exists>x\<in>source(qsurj(S)). qsurj(S)`x = y"
@qed

section {* Product of two equivalence relations *}  (* Bourbaki II.6.8 *)

definition prod_equiv :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "prod_equiv(R,S) = Equiv(carrier(R)\<times>carrier(S), \<lambda>p q. fst(p) \<sim>\<^sub>R fst(q) \<and> snd(p) \<sim>\<^sub>S snd(q))"

lemma prod_equivD [typing]:
  "equiv(R) \<Longrightarrow> equiv(S) \<Longrightarrow> prod_equiv(R,S) \<in> equiv_space(carrier(R)\<times>carrier(S))" by auto2

lemma prod_equiv_eval [rewrite]:
  "T = prod_equiv(R,S) \<Longrightarrow> x \<in>. T \<Longrightarrow> y \<in>. T \<Longrightarrow> x \<sim>\<^sub>T y \<longleftrightarrow> (fst(x) \<sim>\<^sub>R fst(y) \<and> snd(x) \<sim>\<^sub>S snd(y))" by auto2
setup {* del_prfstep_thm @{thm prod_equiv_def} *}

lemma prod_fun_equiv [rewrite]:
  "equiv(R) \<Longrightarrow> equiv(S) \<Longrightarrow> fun_equiv(qsurj(R) \<times>\<^sub>f qsurj(S)) = prod_equiv(R,S)" by auto2

definition prod_quotient_isomorphism :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "prod_quotient_isomorphism(R,S) = induced_fun(qsurj(R) \<times>\<^sub>f qsurj(S), prod_equiv(R,S))"

lemma prod_quotient_isomorphism:
  "equiv(R) \<Longrightarrow> equiv(S) \<Longrightarrow> A = carrier(R) \<Longrightarrow> B = carrier(S) \<Longrightarrow>
   prod_quotient_isomorphism(R,S) \<in> (A\<times>B)//prod_equiv(R,S) \<cong> (A//R) \<times> (B//S)"
@proof
  @have "surjective(qsurj(R) \<times>\<^sub>f qsurj(S))"
  @have "fun_equiv(qsurj(R) \<times>\<^sub>f qsurj(S)) = prod_equiv(R,S)"
@qed

section {* Compatible binary operators *}

(* A (meta) binary operator is compatible with a (object) equivalence relation. *)
definition compat_meta_bin :: "[i, i \<Rightarrow> i \<Rightarrow> i] \<Rightarrow> o" where [rewrite]:
  "compat_meta_bin(R,f) \<longleftrightarrow> (\<forall>x1 x2 y1 y2. x1 \<sim>\<^sub>R x2 \<longrightarrow> y1 \<sim>\<^sub>R y2 \<longrightarrow> f(x1,y1) \<sim>\<^sub>R f(x2,y2))"

(* Compatibility can be shown one argument at a time. *)
definition compat_meta_bin1 :: "[i, i \<Rightarrow> i \<Rightarrow> i] \<Rightarrow> o" where [rewrite]:
  "compat_meta_bin1(R,f) \<longleftrightarrow> (\<forall>y\<in>.R. \<forall>x1 x2. x1 \<sim>\<^sub>R x2 \<longrightarrow> f(x1,y) \<sim>\<^sub>R f(x2,y))"

lemma compat_meta_bin1D [backward2]:
  "compat_meta_bin1(R,f) \<Longrightarrow> y \<in>. R \<Longrightarrow> x1 \<sim>\<^sub>R x2 \<Longrightarrow> f(x1,y) \<sim>\<^sub>R f(x2,y)" by auto2
setup {* del_prfstep_thm_eqforward @{thm compat_meta_bin1_def} *}

definition compat_meta_bin2 :: "[i, i \<Rightarrow> i \<Rightarrow> i] \<Rightarrow> o" where [rewrite]:
  "compat_meta_bin2(R,f) \<longleftrightarrow> (\<forall>x\<in>.R. \<forall>y1 y2. y1 \<sim>\<^sub>R y2 \<longrightarrow> f(x,y1) \<sim>\<^sub>R f(x,y2))"

lemma compat_meta_bin2D [backward2]:
  "compat_meta_bin2(R,f) \<Longrightarrow> x \<in>. R \<Longrightarrow> y1 \<sim>\<^sub>R y2 \<Longrightarrow> f(x,y1) \<sim>\<^sub>R f(x,y2)" by auto2
setup {* del_prfstep_thm_eqforward @{thm compat_meta_bin2_def} *}

lemma compat_meta_binI [backward]:
  "equiv(R) \<Longrightarrow> compat_meta_bin1(R,f) \<Longrightarrow> compat_meta_bin2(R,f) \<Longrightarrow> compat_meta_bin(R,f)"
@proof
  @have "\<forall>x1 x2 y1 y2. x1 \<sim>\<^sub>R x2 \<longrightarrow> y1 \<sim>\<^sub>R y2 \<longrightarrow> f(x1,y1) \<sim>\<^sub>R f(x2,y2)" @with
    @have "f(x1,y1) \<sim>\<^sub>R f(x2,y1)" @have "f(x2,y1) \<sim>\<^sub>R f(x2,y2)" @end
@qed

lemma compat_meta_binD [backward2]:
  "compat_meta_bin(R,f) \<Longrightarrow> x1 \<sim>\<^sub>R x2 \<Longrightarrow> y1 \<sim>\<^sub>R y2 \<Longrightarrow> f(x1,y1) \<sim>\<^sub>R f(x2,y2)" by auto2
setup {* del_prfstep_thm @{thm compat_meta_bin_def} *}

(* If the (meta) binary operator f is compatible with R, then f induces a binary
   operator on the quotient of R. *)
lemma induced_meta_bin [rewrite]:
  "equiv(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> compat_meta_bin(R,f) \<Longrightarrow>
   equiv_class(R,f(rep(R,equiv_class(R,x)),rep(R,equiv_class(R,y)))) = equiv_class(R,f(x,y))"
@proof @have "f(rep(R, equiv_class(R, x)), rep(R, equiv_class(R, y))) \<sim>\<^sub>R f(x,y)" @qed

end
