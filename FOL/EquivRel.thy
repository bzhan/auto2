theory EquivRel
imports Coverings
begin

section {* Definition of equivalence relation *}  (* Bourbaki II.6.1 *)

definition sym_meta_rel :: "[i \<Rightarrow> i \<Rightarrow> o] \<Rightarrow> o" where sym_meta_rel_def [rewrite]:
  "sym_meta_rel(R) \<longleftrightarrow> (\<forall>x y. R(x,y) \<longrightarrow> R(y,x))"

definition trans_meta_rel :: "[i \<Rightarrow> i \<Rightarrow> o] \<Rightarrow> o" where trans_meta_rel_def [rewrite]:
  "trans_meta_rel(R) \<longleftrightarrow> (\<forall>x y z. R(x,y) \<longrightarrow> R(y,z) \<longrightarrow> R(x,z))"

lemma trans_meta_relD [forward]:
  "trans_meta_rel(R) \<Longrightarrow> R(x,y) \<Longrightarrow> \<forall>z. R(y,z) \<longrightarrow> R(x,z)" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm trans_meta_rel_def} *}

definition equiv_meta_rel :: "[i \<Rightarrow> i \<Rightarrow> o] \<Rightarrow> o" where equiv_meta_rel_def [rewrite]:
  "equiv_meta_rel(R) \<longleftrightarrow> (sym_meta_rel(R) \<and> trans_meta_rel(R))"

definition equiv_rel_on :: "[i \<Rightarrow> i \<Rightarrow> o, i] \<Rightarrow> o" where equiv_rel_on_def [rewrite]:
  "equiv_rel_on(R,E) \<longleftrightarrow> (equiv_meta_rel(R) \<and> (\<forall>x. x \<in> E \<longleftrightarrow> R(x,x)))"

definition equiv_rel :: "i \<Rightarrow> o" where equiv_rel_def [rewrite]:
  "equiv_rel(R) \<longleftrightarrow> (is_relation(R) \<and> source(R) = target(R) \<and>
                     equiv_rel_on(\<lambda>x y. rel(R,x,y), source(R)))"

(* Examples *)
lemma eq_is_equiv_meta_rel: "equiv_meta_rel(\<lambda>x y. x = y)" by auto2
lemma eq_on_E_is_equiv_rel: "equiv_rel_on(\<lambda>x y. x = y \<and> x \<in> E, E)" by auto2
lemma all_rel_is_equiv_rel: "equiv_rel_on(\<lambda>x y. x \<in> E \<and> y \<in> E, E)" by auto2
lemma subset_is_equiv_rel:
  "A \<subseteq> E \<Longrightarrow> equiv_rel_on(\<lambda>x y. x \<in> E \<and> y \<in> E \<and> (x = y \<or> (x \<in> A \<and> y \<in> A)), E)" by auto2

(* Important example: exists bijection between two sets. *)
definition equipotent :: "i \<Rightarrow> i \<Rightarrow> o" where equipotent_def [rewrite]:
  "equipotent(S,T) \<longleftrightarrow> (\<exists>f. f \<in> S \<cong> T)"

lemma equipotent_sym [resolve]: "equipotent(S,T) \<Longrightarrow> equipotent(T,S)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "f, f \<in> S \<cong> T" THEN HAVE "bijective(inverse(f))") *})

lemma equipotent_trans [backward2]: "equipotent(S,T) \<Longrightarrow> equipotent(T,U) \<Longrightarrow> equipotent(S,U)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "f, f \<in> S \<cong> T" THEN CHOOSE "g, g \<in> T \<cong> U" THEN
    HAVE "g O f \<in> S \<cong> U") *})

lemma bij_is_equiv_meta_real: "equiv_meta_rel(equipotent)" by auto2

(* Self-contained condition for equiv_rel. *)
lemma equiv_rel_iff [rewrite]:
  "equiv_rel(R) \<longleftrightarrow> (
    is_relation(R) \<and> source(R) = target(R) \<and>
    (\<forall>x\<in>source(R). rel(R,x,x)) \<and>
    (\<forall>x y. rel(R,x,y) \<longleftrightarrow> rel(R,y,x))) \<and>
    (\<forall>x y z. rel(R,x,y) \<longrightarrow> rel(R,y,z) \<longrightarrow> rel(R,x,z))" by auto2
setup {* add_property_const @{term equiv_rel} *}
setup {* del_prfstep_thm @{thm equiv_rel_def} *}

lemma equiv_relD:
  "equiv_rel(R) \<Longrightarrow> is_relation(R)"
  "equiv_rel(R) \<Longrightarrow> source(R) = target(R)"
  "equiv_rel(R) \<Longrightarrow> rel(R,x,x) \<longleftrightarrow> x\<in>source(R)"
  "equiv_rel(R) \<Longrightarrow> rel(R,x,y) \<longleftrightarrow> rel(R,y,x)"
  "equiv_rel(R) \<Longrightarrow> rel(R,x,y) \<Longrightarrow> rel(R,y,z) \<Longrightarrow> rel(R,x,z)" by auto2+
setup {* fold add_forward_prfstep @{thms equiv_relD(1-2,5)} *}
setup {* add_rewrite_rule_bidir @{thm equiv_relD(3)} *}
setup {* add_rewrite_rule @{thm equiv_relD(4)} *}
setup {* del_prfstep_thm_str "@eqforward" @{thm equiv_rel_iff} *}

(* Condition in terms of composition and inverse of relations. *)
lemma equiv_rel_graph_iff:
  "equiv_rel(R) \<longleftrightarrow> (is_relation(R) \<and> target(R) = rel_image(R,source(R)) \<and> R = rel_inverse(R) \<and> R O\<^sub>r R = R)" by auto2

lemma induced_equiv_rel_is_equiv_rel [backward]:
  "equiv_rel_on(R,E) \<Longrightarrow> equiv_rel(Rel(E,R))" by auto2

section {* Quotient construction *}  (* Bourbaki II.6.2 *)

(* Equivalence relation induced by a function *)
definition fun_equiv_rel :: "i \<Rightarrow> i" where fun_equiv_rel_def [rewrite]:
  "fun_equiv_rel(f) = Rel(source(f), \<lambda>x y. f`x = f`y)"

lemma fun_equiv_rel_is_rel [typing]:
  "fun_equiv_rel(f) \<in> rel_space(source(f))" by auto2

lemma fun_equiv_rel_eval [rewrite]:
  "rel(fun_equiv_rel(f),x,y) \<longleftrightarrow> (x\<in>source(f) \<and> y\<in>source(f) \<and> f`x = f`y)" by auto2
setup {* del_prfstep_thm @{thm fun_equiv_rel_def} *}

lemma fun_equiv_rel_is_equiv_rel [forward]:
  "equiv_rel(fun_equiv_rel(f))" by auto2

(* Definition of quotient set as set of equivalence classes. *)
definition equiv_class :: "[i, i] \<Rightarrow> i" where equiv_class_def [rewrite]:
  "equiv_class(R,x) = rel_image(R,{x})"

lemma equiv_class_iff [rewrite]:
  "equiv_rel(R) \<Longrightarrow> y \<in> equiv_class(R,x) \<longleftrightarrow> (y \<in> source(R) \<and> rel(R,x,y))" by auto2
setup {* del_prfstep_thm @{thm equiv_class_def} *}

lemma equiv_class_mem [typing2]: "equiv_rel(R) \<Longrightarrow> rel(R,x,y) \<Longrightarrow> y \<in> equiv_class(R,x)" by auto2

lemma equiv_class_eq [rewrite]:
  "equiv_rel(R) \<Longrightarrow> x \<in> source(R) \<Longrightarrow> y \<in> source(R) \<Longrightarrow>
   equiv_class(R,x) = equiv_class(R,y) \<longleftrightarrow> rel(R,x,y)" by auto2

(* Assume E = source(R) *)
definition quotient_set :: "[i, i] \<Rightarrow> i"  (infixl "'/" 90) where quotient_set_def [rewrite]:
  "E / R = {equiv_class(R,x). x\<in>E}"

lemma quotient_setI [backward]:
  "equiv_rel(R) \<Longrightarrow> S \<noteq> \<emptyset> \<Longrightarrow> S \<subseteq> source(R) \<Longrightarrow>
   \<forall>x\<in>S. \<forall>y\<in>source(R). y \<in> S \<longleftrightarrow> rel(R,x,y) \<Longrightarrow> S \<in> source(R) / R" by auto2

lemma quotient_setD:  (* Second part not needed so far *)
  "equiv_rel(R) \<Longrightarrow> S \<in> source(R) / R \<Longrightarrow>
   (S \<subseteq> source(R) \<and> S \<noteq> \<emptyset>) \<and> (\<forall>x\<in>S. \<forall>y\<in>source(R). y \<in> S \<longleftrightarrow> rel(R,x,y))" by auto2
setup {* add_forward_prfstep (conj_left_th @{thm quotient_setD}) *}

(* Definition of canonical surjection *)
definition qsurj :: "i \<Rightarrow> i" where qsurj_def [rewrite]:
  "qsurj(R) = (\<lambda>x\<in>source(R). equiv_class(R,x)\<in>(source(R)/R))"

lemma qsurj_is_fun [typing]: "qsurj(R) \<in> source(R) \<rightarrow> source(R)/R" by auto2

lemma qsurj_is_surj [forward]: "surjective(qsurj(R))" by auto2

lemma qsurj_eval [rewrite]:
  "x \<in> source(R) \<Longrightarrow> qsurj(R)`x = equiv_class(R,x)" by auto2
setup {* del_prfstep_thm @{thm qsurj_def} *}

lemma qsurj_eq_iff1:
  "equiv_rel(R) \<Longrightarrow> rel(R,x,y) \<Longrightarrow> x \<in> source(R) \<Longrightarrow> y \<in> source(R) \<Longrightarrow> qsurj(R)`x = qsurj(R)`y" by auto2
setup {* add_rewrite_rule_cond @{thm qsurj_eq_iff1} [with_cond "?x \<noteq> ?y"] *}

lemma qsurj_eq_iff2:
  "equiv_rel(R) \<Longrightarrow> qsurj(R)`x = qsurj(R)`y \<Longrightarrow> x \<in> source(R) \<Longrightarrow> y \<in> source(R) \<Longrightarrow> rel(R,x,y)" by auto2
setup {* add_forward_prfstep_cond @{thm qsurj_eq_iff2} [with_cond "?x \<noteq> ?y", with_filt (order_filter "x" "y")] *}

(* We show that every equivalence relation is induced by some function. *)
lemma qsurj_equiv_rel: "equiv_rel(R) \<Longrightarrow> R = fun_equiv_rel(qsurj(R))" by auto2

(* Examples *)
definition eq_equiv_rel :: "i \<Rightarrow> i" where eq_equiv_rel_def [rewrite]:
  "eq_equiv_rel(E) = Rel(E, \<lambda>x y. x = y)"

lemma eq_equiv_rel_is_equiv_rel [forward]: "equiv_rel(eq_equiv_rel(E))" by auto2

lemma qsurj_triv_bij: "qsurj(eq_equiv_rel(E)) \<in> E \<cong> E/eq_equiv_rel(E)" by auto2

definition eq_fst_rel :: "i \<Rightarrow> i \<Rightarrow> i" where eq_fst_rel_def [rewrite]:
  "eq_fst_rel(E,F) = Rel(E\<times>F, \<lambda>u v. fst(u) = fst(v))"

lemma eq_fst_rel_is_equiv [forward]: "equiv_rel(eq_fst_rel(E,F))" by auto2

lemma qsurj_proj_is_inj: "F \<noteq> \<emptyset> \<Longrightarrow> bijective(\<lambda>x\<in>E. ({x}\<times>F)\<in>((E\<times>F)/eq_fst_rel(E,F)))"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "f, f = (\<lambda>x\<in>E. ({x}\<times>F)\<in>((E\<times>F)/eq_fst_rel(E,F)))" THEN
     HAVE "f \<in> E \<rightarrow> (E\<times>F) / eq_fst_rel(E,F)" THEN
     HAVE "injective(f)" WITH (
      HAVE "\<forall>x\<in>E. \<forall>y\<in>E. {x}\<times>F = {y}\<times>F \<longrightarrow> x = y" WITH HAVE "{x} \<noteq> \<emptyset>") THEN
    (HAVE "surjective(f)" WITH (
      HAVE "\<forall>S\<in>(E\<times>F)/eq_fst_rel(E,F). \<exists>x\<in>E. f ` x = S" WITH CHOOSE "p, p \<in> S"))) *})

(* Elements of quotient form a partition. Conversely, every partition is a quotient set. *)
lemma equiv_class_disjoint [backward2]:
  "equiv_rel(R) \<Longrightarrow> x \<in> source(R) \<Longrightarrow> y \<in> source(R) \<Longrightarrow> \<not>rel(R,x,y) \<Longrightarrow>
   set_disjoint(equiv_class(R,x), equiv_class(R,y))" by auto2

lemma equiv_classes_is_partition:
  "equiv_rel(R) \<Longrightarrow> is_partition_sets(source(R),source(R)/R)" by auto2

lemma partition_mem_unique [backward2]:
  "mutually_disjoint_sets(X) \<Longrightarrow> a \<in> \<Union>X \<Longrightarrow> \<exists>!x. x \<in> X \<and> a \<in> x" by auto2

definition partition_mem :: "i \<Rightarrow> i \<Rightarrow> i" where partition_mem_def [rewrite]:
  "partition_mem(X,u) = (THE x. x \<in> X \<and> u \<in> x)"

definition partition_equiv_rel :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o" where partition_equiv_rel_def [rewrite]:
  "partition_equiv_rel(X,u,v) \<longleftrightarrow> (u \<in> \<Union>X \<and> v \<in> \<Union>X \<and> (partition_mem(X,u) = partition_mem(X,u)))"

lemma partition_equiv_rel_is_equiv_rel:
  "is_partition_sets(E,X) \<Longrightarrow> equiv_rel_on(partition_equiv_rel(X),E)" by auto2

section {* Predicate compatible with an equivalence relation *}  (* Bourbaki II.6.3 *)

definition compat_pred :: "[i \<Rightarrow> o, i] \<Rightarrow> o" where compat_pred_def [rewrite]:
  "compat_pred(P,R) \<longleftrightarrow> (\<forall>x y. P(x) \<longrightarrow> rel(R,x,y) \<longrightarrow> P(y))"

lemma compat_relD [forward]:
  "compat_pred(P,R) \<Longrightarrow> rel(R,x,y) \<Longrightarrow> P(x) \<longrightarrow> P(y)" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm compat_pred_def} *}

(* Example *)
lemma compat_pred_eq_equiv: "compat_pred(P, eq_equiv_rel(E))" by auto2

(* Given a equivalence relation R on E, can induce a predicate on E/R *)
definition induced_pred :: "[i \<Rightarrow> o, i, i] \<Rightarrow> o" where induced_pred_def [rewrite]:
  "induced_pred(P,R,t) \<longleftrightarrow> (t \<in> source(R)/R \<and> (\<exists>x\<in>t. P(x)))"

lemma induced_pred_iff:
  "equiv_rel(R) \<Longrightarrow> compat_pred(P,R) \<Longrightarrow> x \<in> source(R) \<Longrightarrow>
   induced_pred(P,R,qsurj(R)`x) \<longleftrightarrow> P(x)" by auto2

section {* Saturated subsets *}  (* Bourbaki II.6.4 *)

definition saturated_subset :: "[i, i] \<Rightarrow> o" where saturated_subset_def [rewrite]:
  "saturated_subset(R,A) \<longleftrightarrow> (A \<subseteq> source(R) \<and> compat_pred(\<lambda>x. x\<in>A, R))"

lemma saturated_subset_iff:
  "equiv_rel(R) \<Longrightarrow> saturated_subset(R,A) \<longleftrightarrow> (A \<subseteq> source(R) \<and> (\<forall>x\<in>A. equiv_class(R,x) \<subseteq> A))" by auto2

lemma saturated_subset_iff2:
  "equiv_rel(R) \<Longrightarrow> saturated_subset(R,A) \<longleftrightarrow> (A \<subseteq> source(R) \<and> A = (\<Union>x\<in>A. equiv_class(R,x)))" by auto2

lemma equiv_class_alt:
  "equiv_rel(R) \<Longrightarrow> x \<in> source(R) \<Longrightarrow> equiv_class(R,x) = qsurj(R) -`` {qsurj(R) ` x}" by auto2

lemma saturated_subset_alt [backward]:
  "equiv_rel(R) \<Longrightarrow> saturated_subset(R,A) \<longleftrightarrow> A = qsurj(R) -`` (qsurj(R) `` A)" by auto2

(* Put above lemma into a form that is good for rewriting. *)
lemma saturated_subset_alt' [rewrite]:
  "saturated_subset(R,A) \<Longrightarrow> equiv_rel(R) \<Longrightarrow> qsurj(R) -`` (qsurj(R) `` A) = A" by auto2

lemma saturated_subset_alt2:
  "equiv_rel(R) \<Longrightarrow> saturated_subset(R,A) \<longleftrightarrow> (\<exists>B. B \<subseteq> source(R)/R \<and> A = qsurj(R) -`` B)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "saturated_subset(R,A) \<longleftrightarrow> A = qsurj(R) -`` (qsurj(R) `` A)") *})

lemma saturated_subset_union [backward2]:
  "equiv_rel(R) \<Longrightarrow> \<forall>a\<in>I. saturated_subset(R,X(a)) \<Longrightarrow> saturated_subset(R,\<Union>a\<in>I. X(a))" by auto2

lemma saturated_subset_inter [backward2]:
  "equiv_rel(R) \<Longrightarrow> I \<noteq> \<emptyset> \<Longrightarrow> \<forall>a\<in>I. saturated_subset(R,X(a)) \<Longrightarrow> saturated_subset(R,\<Inter>a\<in>I. X(a))" by auto2

lemma saturated_subset_comp [backward]:
  "equiv_rel(R) \<Longrightarrow> saturated_subset(R,A) \<Longrightarrow> saturated_subset(R,source(R)-A)" by auto2

definition saturation_subset :: "[i, i] \<Rightarrow> i" where saturation_subset_def [rewrite]:
  "saturation_subset(R,A) = (qsurj(R) -`` (qsurj(R) `` A))"

lemma saturation_subset_prop1:
  "equiv_rel(R) \<Longrightarrow> A \<subseteq> source(R) \<Longrightarrow> A \<subseteq> saturation_subset(R,A)" by auto2

lemma saturation_subset_prop2:
  "equiv_rel(R) \<Longrightarrow> saturated_subset(R,A') \<Longrightarrow> A \<subseteq> A' \<Longrightarrow> saturation_subset(R,A) \<subseteq> A'" by auto2

(* Alternative definition *)
lemma saturation_subset_alt [backward]:
  "equiv_rel(R) \<Longrightarrow> A \<subseteq> source(R) \<Longrightarrow> saturation_subset(R,A) = (\<Union>x\<in>A. equiv_class(R,x))" by auto2

lemma saturation_subset_union:
  "equiv_rel(R) \<Longrightarrow> \<forall>a\<in>I. X(a) \<subseteq> source(R) \<Longrightarrow>
   saturation_subset(R,\<Union>a\<in>I. X(a)) = (\<Union>a\<in>I. saturation_subset(R,X(a)))" by auto2

section {* Mappings compatible with an equivalence relation *}  (* Bourbaki II.6.5 *)

definition compat_fun :: "[i, i] \<Rightarrow> o" where compat_fun_def [rewrite]:
  "compat_fun(f,R) \<longleftrightarrow> (source(f) = source(R) \<and> (\<forall>x\<in>source(f). \<forall>y\<in>source(f). rel(R,x,y) \<longrightarrow> f`x = f`y))"

(* Alternative definition *)
lemma compat_fun_alt:
  "is_function(f) \<Longrightarrow> equiv_rel(R) \<Longrightarrow>
   compat_fun(f,R) \<longleftrightarrow> (source(f) = source(R) \<and> (\<forall>x\<in>source(f). \<forall>y\<in>equiv_class(R,x). f`x = f`y))" by auto2

(* Compatible functions pass to the quotient. *)
lemma exists_induced_fun [backward]:
  "f \<in> E \<rightarrow> F \<Longrightarrow> equiv_rel(R) \<Longrightarrow> compat_fun(f,R) \<Longrightarrow> \<exists>!h. h\<in>(E/R)\<rightarrow>F \<and> f = h O qsurj(R)"
  by (tactic {* auto2s_tac @{context}
    (HAVE "\<forall>x\<in>E. \<forall>y\<in>E. qsurj(R)`x = qsurj(R)`y \<longrightarrow> f`x = f`y") *})

definition induced_fun :: "[i, i] \<Rightarrow> i" where induced_fun_def [rewrite]:
  "induced_fun(f,R) = (THE h. h \<in> (source(f)/R)\<rightarrow>target(f) \<and> f = h O qsurj(R))"

lemma induced_fun_prop:
  "is_function(f) \<Longrightarrow> equiv_rel(R) \<Longrightarrow> compat_fun(f,R) \<Longrightarrow>
   induced_fun(f,R) \<in> (source(f)/R)\<rightarrow>target(f) \<and> f = induced_fun(f,R) O qsurj(R)" by auto2
setup {* add_forward_prfstep_cond @{thm induced_fun_prop} [with_term "induced_fun(?f,?R)"] *}

lemma induced_fun_eval [rewrite]:
  "is_function(f) \<Longrightarrow> equiv_rel(R) \<Longrightarrow> compat_fun(f,R) \<Longrightarrow>
   x \<in> source(f) \<Longrightarrow> induced_fun(f,R) ` equiv_class(R,x) = f ` x" by auto2
setup {* del_prfstep_thm @{thm induced_fun_def} *}

setup {* add_gen_prfstep ("induced_fun_case",
  [WithTerm @{term_pat "induced_fun(?f,?R)"}, CreateConcl @{term_pat "compat_fun(?f,?R)"}]) *}

(* Conversely, any function that passes to the quotient must be compatible. *)
lemma induced_fun_means_compat:
  "equiv_rel(R) \<Longrightarrow> h \<in> (source(R)/R)\<rightarrow>F \<Longrightarrow> compat_fun(h O qsurj(R), R)" by auto2

(* f is compatible with its own induced equivalence relation. *)
lemma fun_equiv_rel_compat: "compat_fun(f,fun_equiv_rel(f))" by auto2
setup {* add_forward_prfstep_cond @{thm fun_equiv_rel_compat} [with_term "fun_equiv_rel(?f)"] *}

(* Canonical decomposition. *)
lemma injective_induced_fun:
  "is_function(f) \<Longrightarrow> injective(induced_fun(f,fun_equiv_rel(f)))" by auto2
setup {* add_forward_prfstep_cond @{thm injective_induced_fun} [with_term "induced_fun(?f,fun_equiv_rel(?f))"] *}

lemma induced_fun_image [rewrite]:
  "is_function(f) \<Longrightarrow> induced_fun(f,fun_equiv_rel(f)) `` (source(f)/fun_equiv_rel(f)) = f `` source(f)" by auto2

(* Any function can be restricted to its image. *)
definition func_restrict_image :: "i \<Rightarrow> i" where func_restrict_image_def [rewrite]:
  "func_restrict_image(f) = (\<lambda>x\<in>source(f). (f`x)\<in>(f``source(f)))"

lemma func_restrict_image_is_fun [typing]:
  "is_function(f) \<Longrightarrow> func_restrict_image(f) \<in> source(f) \<rightarrow> f``source(f)" by auto2

lemma func_restrict_image_eval [rewrite]:
  "is_function(f) \<Longrightarrow> x \<in> source(f) \<Longrightarrow> func_restrict_image(f)`x = f`x" by auto2
setup {* del_prfstep_thm @{thm func_restrict_image_def} *}

lemma func_factorize [rewrite_back]:
  "is_function(f) \<Longrightarrow> f = inj_fun(f``source(f),target(f)) O func_restrict_image(f)"
  by (tactic {* auto2s_tac @{context} (HAVE "f `` source(f) \<subseteq> target(f)") *})

lemma inj_restrict_image_bij [typing]:
  "injective(f) \<Longrightarrow> func_restrict_image(f) \<in> source(f) \<cong> f``source(f)" by auto2

(* Putting everything together, statement of canonical decomposition. *)
lemma canonical_decomposition:
  "f \<in> E \<rightarrow> F \<Longrightarrow> R = fun_equiv_rel(f) \<Longrightarrow>
   f = (inj_fun(induced_fun(f,R)``(E/R),F) O func_restrict_image(induced_fun(f,R))) O qsurj(R)" by auto2

lemma first_isomorphism_theorem [typing]:
  "is_function(f) \<Longrightarrow> func_restrict_image(induced_fun(f,fun_equiv_rel(f))) \<in> source(f)/fun_equiv_rel(f) \<cong> f``source(f)" by auto2

lemma first_isomorphism_theorem_surj [typing]:
  "surjective(f) \<Longrightarrow> induced_fun(f,fun_equiv_rel(f)) \<in> source(f)/fun_equiv_rel(f) \<cong> target(f)" by auto2

definition compat_fun_double :: "[i, i, i] \<Rightarrow> o" where compat_fun_double_def [rewrite]:
  "compat_fun_double(f,R,S) \<longleftrightarrow> (source(f) = source(R) \<and> target(f) = source(S) \<and>
    (\<forall>x\<in>source(f). \<forall>y\<in>source(f). rel(R,x,y) \<longrightarrow> rel(S,f`x,f`y)))"

definition induced_fun_double :: "[i, i, i] \<Rightarrow> i" where induced_fun_double_def [rewrite]:
  "induced_fun_double(f,R,S) = induced_fun(qsurj(S) O f, R)"

lemma induced_fun_double_prop:
  "is_function(f) \<Longrightarrow> equiv_rel(R) \<Longrightarrow> equiv_rel(S) \<Longrightarrow> compat_fun_double(f,R,S) \<Longrightarrow>
   induced_fun_double(f,R,S) \<in> source(f)/R \<rightarrow> target(f)/S \<and>
   qsurj(S) O f = induced_fun_double(f,R,S) O qsurj(R)" by auto2

section {* Inverse image of an equivalence relation *}  (* Bourbaki II.6.6 *)

definition vImage_equiv_rel :: "[i, i] \<Rightarrow> i" where vImage_equiv_rel_def [rewrite]:
  "vImage_equiv_rel(f,S) = fun_equiv_rel(qsurj(S) O f)"

lemma vImage_equiv_rel_is_equiv_rel:
  "is_function(f) \<Longrightarrow> equiv_rel(S) \<Longrightarrow> target(f) = source(S) \<Longrightarrow>
   equiv_rel(vImage_equiv_rel(f,S))" by auto2
setup {* add_forward_prfstep_cond @{thm vImage_equiv_rel_is_equiv_rel} [with_term "vImage_equiv_rel(?f,?S)"] *}

lemma vImage_equiv_rel_iff [rewrite]:
  "is_function(f) \<Longrightarrow> equiv_rel(S) \<Longrightarrow> target(f) = source(S) \<Longrightarrow>
   x \<in> source(f) \<Longrightarrow> y \<in> source(f) \<Longrightarrow> rel(vImage_equiv_rel(f,S),x,y) \<longleftrightarrow> rel(S,f`x,f`y)" by auto2

lemma vImage_equiv_rel_classes:
  "is_function(f) \<Longrightarrow> equiv_rel(S) \<Longrightarrow> target(f) = source(S) \<Longrightarrow>
   x \<in> source(f) \<Longrightarrow> equiv_class(vImage_equiv_rel(f,S),x) = f -`` equiv_class(S,f`x)" by auto2

(* Given subset A of E, pullback an equivalence relation R on E to an equivalence
   relation on A. *)
definition subset_equiv_rel :: "[i, i] \<Rightarrow> i" where subset_equiv_rel_def [rewrite]:
  "subset_equiv_rel(R,A) = vImage_equiv_rel(inj_fun(A,source(R)),R)"

lemma inj_compat_double:
  "equiv_rel(R) \<Longrightarrow> E = source(R) \<Longrightarrow> A \<subseteq> E \<Longrightarrow>
   compat_fun_double(inj_fun(A,E),subset_equiv_rel(R,A),R)" by auto2

lemma second_isomorphism_theorem:
  "E = source(R) \<Longrightarrow> A \<subseteq> E \<Longrightarrow>
   func_restrict_image(induced_fun_double(inj_fun(A,E),subset_equiv_rel(R,A),R)) \<in>
     A/subset_equiv_rel(R,A) \<cong> qsurj(R) `` A"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "R_A, R_A = subset_equiv_rel(R,A)" THEN
    HAVE "induced_fun_double(inj_fun(A,E), R_A, R) `` (A/R_A) = qsurj(R) `` A") *})

section {* Quotients of equivalence relations *}  (* Bourbaki II.6.7 *)

(* Finer condition can be defined on all relations *)
definition finer_rel :: "[i, i] \<Rightarrow> o" where finer_rel_def [rewrite]:
  "finer_rel(R,S) \<longleftrightarrow> (source(R) = source(S) \<and> target(R) = target(S) \<and> (\<forall>x y. rel(R,x,y) \<longrightarrow> rel(S,x,y)))"

(* Exercises *)
lemma finer_equiv_rel1:
  "equiv_rel(R) \<Longrightarrow> equiv_rel(S) \<Longrightarrow> finer_rel(R,S) \<longleftrightarrow>
   (source(R) = source(S) \<and> (\<forall>x\<in>source(R). equiv_class(R,x) \<subseteq> equiv_class(S,x)))" by auto2

lemma finer_equiv_rel2:
  "equiv_rel(R) \<Longrightarrow> equiv_rel(S) \<Longrightarrow> finer_rel(R,S) \<longleftrightarrow>
   (source(R) = source(S) \<and> (\<forall>x\<in>source(R). saturated_subset(R,equiv_class(S,x))))" by auto2

lemma finer_equiv_top:
  "equiv_rel(R) \<Longrightarrow> finer_rel(eq_equiv_rel(source(R)), R)" by auto2

lemma finer_equiv_bottom:
  "equiv_rel(R) \<Longrightarrow> finer_rel(R, Rel(source(R), \<lambda>x y. True))" by auto2

(* Now the serious business of this section *)

(* Assume R and S are equivalence relations on the same set, and S is finer than R. *)
definition quotient_rel :: "[i, i] \<Rightarrow> i" where quotient_rel_def [rewrite]:
  "quotient_rel(R,S) = fun_equiv_rel(induced_fun(qsurj(R),S))"

lemma compat_finer_equiv_rel:
  "equiv_rel(R) \<Longrightarrow> equiv_rel(S) \<Longrightarrow> finer_rel(S,R) \<Longrightarrow>
   compat_fun(qsurj(R),S) \<and> induced_fun(qsurj(R),S) \<in> source(R)/S \<rightarrow> source(R)/R \<and>
   surjective(induced_fun(qsurj(R),S))" by auto2
setup {* add_forward_prfstep_cond @{thm compat_finer_equiv_rel} [with_term "induced_fun(qsurj(?R),?S)"] *}

lemma finer_induced_fun_eval [rewrite]:
  "equiv_rel(R) \<Longrightarrow> equiv_rel(S) \<Longrightarrow> finer_rel(S,R) \<Longrightarrow>
   x \<in> source(R) \<Longrightarrow> induced_fun(qsurj(R),S) ` equiv_class(S,x) = equiv_class(R,x)" by auto2

lemma quotient_rel_iff [rewrite_back]:
  "equiv_rel(R) \<Longrightarrow> equiv_rel(S) \<Longrightarrow> finer_rel(S,R) \<Longrightarrow>
   x\<in>source(R) \<Longrightarrow> y\<in>source(R) \<Longrightarrow> rel(R,x,y) \<longleftrightarrow> rel(quotient_rel(R,S),qsurj(S)`x,qsurj(S)`y)" by auto2

definition third_isomorphism :: "[i, i] \<Rightarrow> i" where third_isomorphism_def [rewrite]:
  "third_isomorphism(R,S) = induced_fun(induced_fun(qsurj(R),S),quotient_rel(R,S))"

lemma third_isomorphism_theorem:
  "equiv_rel(R) \<Longrightarrow> equiv_rel(S) \<Longrightarrow> finer_rel(S,R) \<Longrightarrow>
   third_isomorphism(R,S) \<in> (source(R)/S)/(quotient_rel(R,S)) \<cong> source(R)/R" by auto2

(* Given an equivalence relation S on E, and an equivalence relation T on E/S,
   the pullback of T on the surjection E \<rightarrow> E/S is an equivalence relation on E coarser than S. *)
lemma vImage_finer [backward]:
  "equiv_rel(S) \<Longrightarrow> equiv_rel(T) \<Longrightarrow> source(T) = source(S)/S \<Longrightarrow> finer_rel(S,vImage_equiv_rel(qsurj(S),T))" by auto2

(* Any equivalence relation T on E/S is the quotient between a coarser equivalence relation R and S. *)
lemma equiv_rel_is_quotient_rel:
  "equiv_rel(S) \<Longrightarrow> equiv_rel(T) \<Longrightarrow> source(T) = source(S)/S \<Longrightarrow> T = quotient_rel(vImage_equiv_rel(qsurj(S),T),S)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "finer_rel(S,vImage_equiv_rel(qsurj(S),T))") *})

section {* Product of two equivalence relations *}  (* Bourbaki II.6.8 *)

definition prod_equiv_rel :: "[i, i] \<Rightarrow> i" where prod_equiv_rel_def [rewrite]:
  "prod_equiv_rel(R,S) = Rel(source(R)\<times>source(S), \<lambda>p q. rel(R,fst(p),fst(q)) \<and> rel(S,snd(p),snd(q)))"

lemma prod_equiv_relD [typing]: "prod_equiv_rel(R,S) \<in> rel_space(source(R)\<times>source(S))" by auto2

lemma prod_equiv_rel_eval [rewrite]:
  "x \<in> source(R)\<times>source(S) \<Longrightarrow> y \<in> source(R)\<times>source(S) \<Longrightarrow>
   rel(prod_equiv_rel(R,S),x,y) \<longleftrightarrow> rel(R,fst(x),fst(y)) \<and> rel(S,snd(x),snd(y))" by auto2
setup {* del_prfstep_thm @{thm prod_equiv_rel_def} *}

lemma prod_equiv_rel_is_equiv_rel [forward]:
  "equiv_rel(R) \<Longrightarrow> equiv_rel(S) \<Longrightarrow> equiv_rel(prod_equiv_rel(R,S))" by auto2

lemma prod_fun_equiv_rel [rewrite]:
  "equiv_rel(R) \<Longrightarrow> equiv_rel(S) \<Longrightarrow> fun_equiv_rel(qsurj(R) \<times>\<^sub>f qsurj(S)) = prod_equiv_rel(R,S)" by auto2

definition prod_quotient_isomorphism :: "[i, i] \<Rightarrow> i" where prod_quotient_isomorphism_def [rewrite]:
  "prod_quotient_isomorphism(R,S) = induced_fun(qsurj(R) \<times>\<^sub>f qsurj(S), prod_equiv_rel(R,S))"

lemma prod_quotient_isomorphism:
  "equiv_rel(R) \<Longrightarrow> equiv_rel(S) \<Longrightarrow>
   prod_quotient_isomorphism(R,S) \<in> (source(R)\<times>source(S))/prod_equiv_rel(R,S) \<cong> (source(R)/R) \<times> (source(S)/S)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "surjective(qsurj(R) \<times>\<^sub>f qsurj(S))" THEN
    HAVE "fun_equiv_rel(qsurj(R) \<times>\<^sub>f qsurj(S)) = prod_equiv_rel(R,S)") *})

section {* Representatives *}

(* In preparation for future developments, we define terminology for "choosing"
   a representative for x, under the equivalence relation R. *)
definition rep :: "i \<Rightarrow> i \<Rightarrow> i" where rep_def [rewrite]:
  "rep(R,x) = Choice(x)"

lemma rep_in_set [typing]: "equiv_rel(R) \<Longrightarrow> x \<in> source(R)/R \<Longrightarrow> rep(R,x) \<in> source(R)" by auto2
lemma qsurj_of_rep: "equiv_rel(R) \<Longrightarrow> x \<in> source(R)/R \<Longrightarrow> qsurj(R) ` rep(R,x) = x" by auto2
setup {* add_forward_prfstep_cond @{thm qsurj_of_rep} [with_term "rep(?R,?x)"] *}
setup {* del_prfstep_thm @{thm rep_def} *}

end
