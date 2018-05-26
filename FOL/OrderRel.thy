theory OrderRel
  imports Morphism
begin

section {* Transitive relations *}

definition trans :: "i \<Rightarrow> o" where [rewrite]:
  "trans(R) \<longleftrightarrow> (
    raworder(R) \<and>
    (\<forall>x y z. x \<le>\<^sub>R y \<longrightarrow> y \<le>\<^sub>R z \<longrightarrow> x \<le>\<^sub>R z))"

lemma transD [forward]:
  "trans(R) \<Longrightarrow> raworder(R)"
  "trans(R) \<Longrightarrow> x \<le>\<^sub>R y \<Longrightarrow> y \<le>\<^sub>R z \<Longrightarrow> x \<le>\<^sub>R z" by auto2+
setup {* del_prfstep_thm_eqforward @{thm trans_def} *}

section {* Preorder and order relations *}  (* Bourbaki III.1.1 -- III.1.2 *)

definition refl_order :: "i \<Rightarrow> o" where [rewrite]:
  "refl_order(R) \<longleftrightarrow> raworder(R) \<and> (\<forall>x\<in>.R. x \<le>\<^sub>R x)"

lemma refl_orderD [forward]:
  "refl_order(R) \<Longrightarrow> raworder(R)" by auto2

lemma refl_orderD2 [backward]:
  "refl_order(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> x \<le>\<^sub>R x" by auto2
setup {* del_prfstep_thm_eqforward @{thm refl_order_def} *}

definition preorder :: "i \<Rightarrow> o" where [rewrite]:
  "preorder(R) \<longleftrightarrow> trans(R) \<and> refl_order(R)"
  
lemma preorderD [forward]:
  "preorder(R) \<Longrightarrow> trans(R)"
  "preorder(R) \<Longrightarrow> refl_order(R)" by auto2+
setup {* del_prfstep_thm_eqforward @{thm preorder_def} *}
  
definition order :: "i \<Rightarrow> o" where [rewrite]:
  "order(R) \<longleftrightarrow> (preorder(R) \<and> (\<forall>x y. x \<le>\<^sub>R y \<longrightarrow> y \<le>\<^sub>R x \<longrightarrow> x = y))"
  
lemma orderD [forward]:
  "order(R) \<Longrightarrow> preorder(R)"
  "order(R) \<Longrightarrow> x \<le>\<^sub>R y \<Longrightarrow> y \<le>\<^sub>R x \<Longrightarrow> x = y" by auto2+
setup {* del_prfstep_thm_eqforward @{thm order_def} *}

(* Small exercise: opposite order *)
definition opp_order :: "i \<Rightarrow> i" where [rewrite]:
  "opp_order(R) = Order(carrier(R), \<lambda>x y. y \<le>\<^sub>R x)"
lemma inv_is_order: "order(R) \<Longrightarrow> order(opp_order(R))" by auto2

(* Subset ordering. *)
definition subset_order :: "i \<Rightarrow> i" where [rewrite]:
  "subset_order(S) = Order(S, \<lambda>x y. x \<subseteq> y)"

lemma subset_order_type [typing]: "subset_order(S) \<in> raworder_space(S)" by auto2
lemma subset_order_is_order [forward]: "order(subset_order(S))" by auto2

lemma subset_order_eval [rewrite]:
  "R = subset_order(S) \<Longrightarrow> x \<le>\<^sub>R y \<longleftrightarrow> (x \<in>. R \<and> y \<in>. R \<and> x \<subseteq> y)" by auto2
setup {* del_prfstep_thm @{thm subset_order_def} *}

section {* Notations for order relations *}  (* Bourbaki III.1.3 *)

definition less :: "[i, i, i] \<Rightarrow> o" where [rewrite]:
  "less(R,x,y) \<longleftrightarrow> (x \<le>\<^sub>R y \<and> x \<noteq> y)"
abbreviation less_notation ("(_/ <\<^sub>_ _)" [51,51,51] 50) where "x <\<^sub>R y \<equiv> less(R,x,y)"
setup {* register_wellform_data ("x <\<^sub>R y", ["x \<in>. R", "y \<in>. R"]) *}

abbreviation (input) greater :: "[i, i, i] \<Rightarrow> o" ("(_/ >\<^sub>_ _)" [51,51,51] 50) where
  "x >\<^sub>R y \<equiv> y <\<^sub>R x"

syntax
  "_Bex_gt" :: "[pttrn, i, i, o] \<Rightarrow> o"  ("(3\<exists>_ >\<^sub>_ _./ _)" 10)
  "_Bex_ge" :: "[pttrn, i, i, o] \<Rightarrow> o"  ("(3\<exists>_ \<ge>\<^sub>_ _./ _)" 10)
  "_Ball_gt" :: "[pttrn, i, i, o] \<Rightarrow> o"  ("(3\<forall>_ >\<^sub>_ _./ _)" 10)
  "_Ball_ge" :: "[pttrn, i, i, o] \<Rightarrow> o"  ("(3\<forall>_ \<ge>\<^sub>_ _./ _)" 10)
translations
  "\<exists>x >\<^sub>R a. P" => "\<exists>x. x >\<^sub>R a \<and> P"
  "\<exists>x \<ge>\<^sub>R a. P" => "\<exists>x. x \<ge>\<^sub>R a \<and> P"
  "\<forall>x >\<^sub>R a. P" => "\<forall>x. x >\<^sub>R a \<longrightarrow> P"
  "\<forall>x \<ge>\<^sub>R a. P" => "\<forall>x. x \<ge>\<^sub>R a \<longrightarrow> P"

syntax
  "_Bex_lt" :: "[pttrn, i, i, o] \<Rightarrow> o"  ("(3\<exists>_ <\<^sub>_ _./ _)" 10)
  "_Bex_le" :: "[pttrn, i, i, o] \<Rightarrow> o"  ("(3\<exists>_ \<le>\<^sub>_ _./ _)" 10)
  "_Ball_lt" :: "[pttrn, i, i, o] \<Rightarrow> o"  ("(3\<forall>_ <\<^sub>_ _./ _)" 10)
  "_Ball_le" :: "[pttrn, i, i, o] \<Rightarrow> o"  ("(3\<forall>_ \<le>\<^sub>_ _./ _)" 10)
translations
  "\<exists>x <\<^sub>R a. P" => "\<exists>x. x <\<^sub>R a \<and> P"
  "\<exists>x \<le>\<^sub>R a. P" => "\<exists>x. x \<le>\<^sub>R a \<and> P"
  "\<forall>x <\<^sub>R a. P" => "\<forall>x. x <\<^sub>R a \<longrightarrow> P"
  "\<forall>x \<le>\<^sub>R a. P" => "\<forall>x. x \<le>\<^sub>R a \<longrightarrow> P"

(* Other versions of transitivity *)
lemma order_trans [forward]:
  "order(R) \<Longrightarrow> x <\<^sub>R y \<Longrightarrow> y \<le>\<^sub>R z \<Longrightarrow> x <\<^sub>R z"
  "order(R) \<Longrightarrow> x \<le>\<^sub>R y \<Longrightarrow> y <\<^sub>R z \<Longrightarrow> x <\<^sub>R z" by auto2+

lemma preorder_lessI [forward, backward1, backward2]:
  "raworder(R) \<Longrightarrow> x \<le>\<^sub>R y \<Longrightarrow> x \<noteq> y \<Longrightarrow> x <\<^sub>R y" by auto2

lemma order_lessE [forward]: "raworder(R) \<Longrightarrow> x <\<^sub>R y \<Longrightarrow> x \<le>\<^sub>R y" by auto2
lemma order_less_to_neg [forward]: "order(R) \<Longrightarrow> x <\<^sub>R y \<Longrightarrow> \<not>y \<le>\<^sub>R x" by auto2
lemma order_le_to_neg [forward]: "order(R) \<Longrightarrow> x \<le>\<^sub>R y \<Longrightarrow> \<not>y <\<^sub>R x" by auto2
lemma preorder_less_neq [resolve]: "raworder(R) \<Longrightarrow> \<not>x <\<^sub>R x" by auto2

lemma less_eq_str [rewrite]: "eq_str_order(X,Y) \<Longrightarrow> a <\<^sub>X b \<longleftrightarrow> a <\<^sub>Y b" by auto2

setup {* del_prfstep_thm @{thm less_def} *}

section {* Isomorphism between orders *}

definition is_ord_mor :: "i \<Rightarrow> o" where [rewrite]:
  "is_ord_mor(f) \<longleftrightarrow> is_morphism(f) \<and> preorder(source_str(f)) \<and> preorder(target_str(f))"

definition ord_isomorphism :: "i \<Rightarrow> o" where [rewrite]:
  "ord_isomorphism(f) \<longleftrightarrow> (let R = source_str(f) in let S = target_str(f) in
                       is_ord_mor(f) \<and> bijective(f) \<and> (\<forall>x\<in>.R. \<forall>y\<in>.R. x \<le>\<^sub>R y \<longleftrightarrow> f`x \<le>\<^sub>S f`y))"

lemma ord_isomorphismD1 [forward]:
  "ord_isomorphism(f) \<Longrightarrow> is_ord_mor(f)"
  "ord_isomorphism(f) \<Longrightarrow> bijective(f)" by auto2+

lemma ord_isomorphismD2 [rewrite]:
  "ord_isomorphism(f) \<Longrightarrow> R = source_str(f) \<Longrightarrow> S = target_str(f) \<Longrightarrow>
   x \<in> source(f) \<Longrightarrow> y \<in> source(f) \<Longrightarrow> f`x \<le>\<^sub>S f`y \<longleftrightarrow> x \<le>\<^sub>R y" by auto2
setup {* del_prfstep_thm_eqforward @{thm ord_isomorphism_def} *}

definition ord_iso_space :: "i \<Rightarrow> i \<Rightarrow> i"  (infix "\<cong>\<^sub>O" 60) where [rewrite]:
  "ord_iso_space(R,S) = {f \<in> mor_space(R,S). ord_isomorphism(f)}"

lemma ord_iso_spaceD [forward]:
  "f \<in> R \<cong>\<^sub>O S \<Longrightarrow> f \<in> R \<rightharpoonup> S \<and> ord_isomorphism(f)" by auto2

lemma ord_iso_spaceI [typing, backward]:
  "mor_form(f) \<Longrightarrow> ord_isomorphism(f) \<Longrightarrow> f \<in> source_str(f) \<cong>\<^sub>O target_str(f)" by auto2
setup {* del_prfstep_thm @{thm ord_iso_space_def} *}

definition ord_isomorphic :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "ord_isomorphic(R,S) \<longleftrightarrow> (\<exists>f. f \<in> R \<cong>\<^sub>O S)"

lemma ord_isomorphicI [forward]: "f \<in> R \<cong>\<^sub>O S \<Longrightarrow> ord_isomorphic(R,S)" by auto2
lemma ord_isomorphicD [resolve]: "ord_isomorphic(R,S) \<Longrightarrow> \<exists>f. f \<in> R \<cong>\<^sub>O S" by auto2

lemma preorder_iso [forward]: "preorder(R) \<Longrightarrow> ord_isomorphic(R,S) \<Longrightarrow> preorder(S)" by auto2
lemma order_iso [forward]: "order(R) \<Longrightarrow> ord_isomorphic(R,S) \<Longrightarrow> order(S)"
@proof
  @obtain f where "f \<in> R \<cong>\<^sub>O S"
  @have "\<forall>x y. x \<le>\<^sub>S y \<longrightarrow> y \<le>\<^sub>S x \<longrightarrow> x = y" @with
    @obtain "x'\<in>.R" where "f`x' = x"
    @obtain "y'\<in>.R" where "f`y' = y"
  @end
@qed
setup {* del_prfstep_thm @{thm ord_isomorphic_def} *}
  
section {* Ordering on subsets and products *}  (* Bourbaki III.1.4 *)

(* Define relation on subsets in general *)
definition suborder :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "suborder(R,A) = Order(A, \<lambda>x y. x \<le>\<^sub>R y)"
setup {* register_wellform_data ("suborder(R,A)", ["A \<subseteq> carrier(R)"]) *}
setup {* add_prfstep_check_req ("suborder(R,A)", "A \<subseteq> carrier(R)") *}

lemma suborder_type [typing]: "suborder(R,A) \<in> raworder_space(A)" by auto2

lemma suborder_is_preorder:
  "preorder(R) \<Longrightarrow> A \<subseteq> carrier(R) \<Longrightarrow> preorder(suborder(R,A))" by auto2
setup {* add_forward_prfstep_cond @{thm suborder_is_preorder} [with_term "suborder(?R,?A)"] *}

lemma suborder_is_order:
  "order(R) \<Longrightarrow> A \<subseteq> carrier(R) \<Longrightarrow> order(suborder(R,A))" by auto2
setup {* add_forward_prfstep_cond @{thm suborder_is_order} [with_term "suborder(?R,?A)"] *}

lemma suborder_eval [rewrite]:
  "S = suborder(R,A) \<Longrightarrow> x \<le>\<^sub>S y \<longleftrightarrow> (x \<in>. S \<and> y \<in>. S \<and> x \<le>\<^sub>R y)" by auto2
    
lemma suborder_less_eval [rewrite]:
  "preorder(R) \<Longrightarrow> A \<subseteq> carrier(R) \<Longrightarrow> S = suborder(R,A) \<Longrightarrow> x <\<^sub>S y \<longleftrightarrow> (x \<in>. S \<and> y \<in>. S \<and> x <\<^sub>R y)"
@proof @case "x = y" @qed
setup {* del_prfstep_thm @{thm suborder_def} *}

lemma subset_order_suborder [rewrite]:
  "F \<subseteq> carrier(subset_order(E)) \<Longrightarrow> suborder(subset_order(E),F) = subset_order(F)" by auto2
    
definition mor_restrict_image_ord :: "i \<Rightarrow> i"  where [rewrite]:
  "mor_restrict_image_ord(f) = Mor(source_str(f),suborder(target_str(f),image(f)),\<lambda>x. f`x)"

lemma mor_restrict_ord_is_morphism [typing]:
  "is_morphism(f) \<Longrightarrow> mor_restrict_image_ord(f) \<in> source_str(f) \<rightharpoonup> suborder(target_str(f),image(f))" by auto2

lemma mor_restrict_ord_eval [rewrite]:
  "is_morphism(f) \<Longrightarrow> f' = mor_restrict_image_ord(f) \<Longrightarrow> x \<in> source(f') \<Longrightarrow> f' ` x = f ` x" by auto2
setup {* del_prfstep_thm @{thm mor_restrict_image_ord_def} *}

(* Define relation on products in general. *)
definition prod_src :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "prod_src(I,R) = Pi(I,\<lambda>a. carrier(R`a))"

definition prod_rel :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "prod_rel(I,R) = Order(prod_src(I,R), \<lambda>x y. \<forall>a\<in>I. le(R`a,x`a,y`a))"

lemma prod_rel_type [typing]:
  "prod_rel(I,R) \<in> raworder_space(prod_src(I,R))" by auto2

lemma prod_rel_is_preorder:
  "\<forall>a\<in>I. preorder(R`a) \<Longrightarrow> preorder(prod_rel(I,R))" by auto2
setup {* add_forward_prfstep_cond @{thm prod_rel_is_preorder} [with_term "prod_rel(?I,?R)"] *}

lemma prod_rel_is_order:
  "\<forall>a\<in>I. order(R`a) \<Longrightarrow> order(prod_rel(I,R))" by auto2
setup {* add_forward_prfstep_cond @{thm prod_rel_is_order} [with_term "prod_rel(?I,?R)"] *}

lemma prod_rel_eval [rewrite]:
  "S = prod_rel(I,R) \<Longrightarrow> x \<in>. S \<Longrightarrow> y \<in>. S \<Longrightarrow> x \<le>\<^sub>S y \<longleftrightarrow> (\<forall>a\<in>I. le(R`a,x`a,y`a))" by auto2
setup {* del_prfstep_thm @{thm prod_rel_def} *}

section {* Increasing mappings *}  (* Bourbaki III.1.5 *)

definition incr :: "i \<Rightarrow> o" where [rewrite]:
  "incr(f) \<longleftrightarrow> (let R = source_str(f) in let S = target_str(f) in
                is_ord_mor(f) \<and> (\<forall>x\<in>.R. \<forall>y\<in>.R. x \<le>\<^sub>R y \<longrightarrow> f`x \<le>\<^sub>S f`y))"

definition decr :: "i \<Rightarrow> o" where [rewrite]:
  "decr(f) \<longleftrightarrow> (let R = source_str(f) in let S = target_str(f) in
                is_ord_mor(f) \<and> (\<forall>x\<in>.R. \<forall>y\<in>.R. x \<le>\<^sub>R y \<longrightarrow> f`x \<ge>\<^sub>S f`y))"

definition strict_incr :: "i \<Rightarrow> o" where [rewrite]:
  "strict_incr(f) \<longleftrightarrow> (let R = source_str(f) in let S = target_str(f) in
                       is_ord_mor(f) \<and> (\<forall>x\<in>.R. \<forall>y\<in>.R. x <\<^sub>R y \<longrightarrow> f`x <\<^sub>S f`y))"

definition strict_decr :: "i \<Rightarrow> o" where [rewrite]:
  "strict_decr(f) \<longleftrightarrow> (let R = source_str(f) in let S = target_str(f) in
                       is_ord_mor(f) \<and> (\<forall>x\<in>.R. \<forall>y\<in>.R. x <\<^sub>R y \<longrightarrow> f`x >\<^sub>S f`y))"

(* Examples *)
lemma subset_order_less [rewrite]:
  "R = subset_order(E) \<Longrightarrow> X \<in>. R \<Longrightarrow> Y \<in>. R \<Longrightarrow> X <\<^sub>R Y \<longleftrightarrow> X \<subset> Y" by auto2

lemma compl_strict_decr:
  "R = subset_order(Pow(E)) \<Longrightarrow> strict_decr(Mor(R,R,\<lambda>X. E \<midarrow> X))" by auto2

lemma greater_elts_strict_subset [backward]:
  "order(R) \<Longrightarrow> x <\<^sub>R y \<Longrightarrow> {z\<in>.R. z \<ge>\<^sub>R y} \<subset> {z\<in>.R. z \<ge>\<^sub>R x}"
@proof @have "x\<in>{z\<in>.R. z \<ge>\<^sub>R x}" @qed

lemma greater_elts_strict_decr:
  "order(R) \<Longrightarrow> strict_decr(Mor(R,subset_order(Pow(carrier(R))), \<lambda>x. {y\<in>.R. y \<ge>\<^sub>R x}))" by auto2

lemma inj_to_strict_incr: "incr(f) \<Longrightarrow> injective(f) \<Longrightarrow> strict_incr(f)" by auto2
lemma inj_to_strict_decr: "decr(f) \<Longrightarrow> injective(f) \<Longrightarrow> strict_decr(f)" by auto2

lemma restrict_image_incr [forward]:
  "incr(f) \<Longrightarrow> incr(mor_restrict_image_ord(f))" by auto2

(* Proposition 2 in III.1.5 *)
lemma two_decr_funs_prop:
  "decr(u) \<Longrightarrow> decr(v) \<Longrightarrow> mor_form(u) \<Longrightarrow> mor_form(v) \<Longrightarrow> u \<in> R \<rightharpoonup> S \<Longrightarrow> v \<in> S \<rightharpoonup> R \<Longrightarrow>
   \<forall>x\<in>.R. v`(u`x) = x \<Longrightarrow> \<forall>x\<in>.S. u`(v`x) = x \<Longrightarrow> u \<circ>\<^sub>m v \<circ>\<^sub>m u = u \<and> v \<circ>\<^sub>m u \<circ>\<^sub>m v = v" by auto2

section {* Maximal and minimal elements *}  (* Bourbaki III.1.6 *)

definition maximal :: "[i, i] \<Rightarrow> o" where [rewrite]:
  "maximal(R,x) \<longleftrightarrow> (x \<in>. R \<and> (\<forall>a\<in>.R. a \<ge>\<^sub>R x \<longrightarrow> a = x))"

definition minimal :: "[i, i] \<Rightarrow> o" where [rewrite]:
  "minimal(R,x) \<longleftrightarrow> (x \<in>. R \<and> (\<forall>a\<in>.R. a \<le>\<^sub>R x \<longrightarrow> a = x))"

(* Examples *)
lemma singleton_minimal:
  "x \<in> S \<Longrightarrow> minimal(subset_order(Pow(S)\<midarrow>{\<emptyset>}),{x})" by auto2
    
section {* Greatest and least elements *}  (* Bourbaki III.1.7 *)

(* We define the more general notion of greatest/least element of a subset, to
   prepare for definition of sup and inf later. *)
definition has_greatest :: "[i, i] \<Rightarrow> o" where [rewrite]:
  "has_greatest(R,X) \<longleftrightarrow> (\<exists>x\<in>X. \<forall>a\<in>X. a \<le>\<^sub>R x)"

definition greatest :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "greatest(R,X) = (THE x. x \<in> X \<and> (\<forall>a\<in>X. a \<le>\<^sub>R x))"

(* We always prove has_greatest(R,X) and assign greatest(R,X) at the same time.
   Similarly for least, sup, and inf below *)
lemma greatestI [backward]:
  "order(R) \<Longrightarrow> x \<in> X \<Longrightarrow> \<forall>a\<in>X. a \<le>\<^sub>R x \<Longrightarrow> has_greatest(R,X) \<and> greatest(R,X) = x" by auto2

lemma greatestE:
  "order(R) \<Longrightarrow> has_greatest(R,X) \<Longrightarrow> greatest(R,X) \<in> X"
  "order(R) \<Longrightarrow> a \<in> X \<Longrightarrow> has_greatest(R,X) \<Longrightarrow> a \<le>\<^sub>R greatest(R,X)" by auto2+
setup {* fold (fn th => add_forward_prfstep_cond th [with_term "greatest(?R,?X)"]) @{thms greatestE} *}
setup {* fold del_prfstep_thm [@{thm has_greatest_def}, @{thm greatest_def}] *}

definition has_least :: "[i, i] \<Rightarrow> o" where [rewrite]:
  "has_least(R,X) \<longleftrightarrow> (\<exists>x\<in>X. \<forall>a\<in>X. x \<le>\<^sub>R a)"

definition least :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "least(R,X) = (THE x. x \<in> X \<and> (\<forall>a\<in>X. x \<le>\<^sub>R a))"

lemma leastI [backward]:
  "order(R) \<Longrightarrow> x \<in> X \<Longrightarrow> \<forall>a\<in>X. a \<ge>\<^sub>R x \<Longrightarrow> has_least(R,X) \<and> least(R,X) = x" by auto2

lemma leastE:
  "order(R) \<Longrightarrow> has_least(R,X) \<Longrightarrow> least(R,X) \<in> X"
  "order(R) \<Longrightarrow> a \<in> X \<Longrightarrow> has_least(R,X) \<Longrightarrow> least(R,X) \<le>\<^sub>R a" by auto2+
setup {* fold (fn th => add_forward_prfstep_cond th [with_term "least(?R,?X)"]) @{thms leastE} *}
setup {* fold del_prfstep_thm [@{thm has_least_def}, @{thm least_def}] *}

(* Relation to maximal / minimal *)
lemma greatest_maximal:
  "order(R) \<Longrightarrow> has_greatest(R,X) \<Longrightarrow> maximal(suborder(R,X),greatest(R,X))" by auto2

lemma greatest_maximal_unique:
  "order(R) \<Longrightarrow> has_greatest(R,X) \<Longrightarrow> x \<in> X \<Longrightarrow> maximal(suborder(R,X),x) \<Longrightarrow> greatest(R,X) = x" by auto2

lemma least_minimal:
  "order(R) \<Longrightarrow> has_least(R,X) \<Longrightarrow> minimal(suborder(R,X),least(R,X))" by auto2

lemma least_minimal_unique:
  "order(R) \<Longrightarrow> has_least(R,X) \<Longrightarrow> x \<in> X \<Longrightarrow> minimal(suborder(R,X),x) \<Longrightarrow> least(R,X) = x" by auto2

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

lemma has_least_suborder [backward2]:
  "order(R) \<Longrightarrow> X \<subseteq> carrier(R) \<Longrightarrow> has_least(R,A) \<Longrightarrow> A \<subseteq> X \<Longrightarrow>
   has_least(suborder(R,X),A) \<and> least(suborder(R,X),A) = least(R,A)" by auto2
setup {* add_backward2_prfstep (conj_left_th @{thm has_least_suborder}) *}

lemma has_least_suborder_inv [backward2]:
  "order(R) \<Longrightarrow> X \<subseteq> carrier(R) \<Longrightarrow> has_least(suborder(R,X),A) \<Longrightarrow> A \<subseteq> X \<Longrightarrow>
   has_least(R,A) \<and> least(R,A) = least(suborder(R,X),A)" by auto2
setup {* add_backward2_prfstep (conj_left_th @{thm has_least_suborder_inv}) *}

lemma has_least_singleton [backward2]:
  "order(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> has_least(R,{a}) \<and> least(R,{a}) = a" by auto2
setup {* add_backward2_prfstep (conj_left_th @{thm has_least_singleton}) *}

lemma has_least_sub_singleton [backward2]:
  "order(R) \<Longrightarrow> has_least(R,X\<midarrow>{a}) \<Longrightarrow> \<forall>x\<in>X. x \<le>\<^sub>R a \<Longrightarrow>
   has_least(R,X) \<and> least(R,X) = least(R,X\<midarrow>{a})"
@proof @case "a \<in> X" @with @have "X = (X \<midarrow> {a}) \<union> {a}" @end @qed
setup {* add_backward2_prfstep (conj_left_th @{thm has_least_sub_singleton}) *}

(* Cofinal and coinitial subsets *)
definition cofinal :: "[i, i] \<Rightarrow> o" where [rewrite]:
  "cofinal(R,A) \<longleftrightarrow> (A \<subseteq> carrier(R) \<and> (\<forall>x\<in>.R. \<exists>y\<in>A. x \<le>\<^sub>R y))"

lemma cofinalE1 [forward]: "cofinal(R,A) \<Longrightarrow> A \<subseteq> carrier(R)" by auto2
lemma cofinalE2 [backward2]: "cofinal(R,A) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<exists>y\<in>A. x \<le>\<^sub>R y" by auto2
setup {* del_prfstep_thm_eqforward @{thm cofinal_def} *}

definition coinitial :: "[i, i] \<Rightarrow> o" where [rewrite]:
  "coinitial(R,A) \<longleftrightarrow> (A \<subseteq> carrier(R) \<and> (\<forall>x\<in>.R. \<exists>y\<in>A. y \<le>\<^sub>R x))"

lemma coinitialE1 [forward]: "coinitial(R,A) \<Longrightarrow> A \<subseteq> carrier(R)" by auto2
lemma coinitialE2 [backward2]: "coinitial(R,A) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<exists>y\<in>A. y \<le>\<^sub>R x" by auto2
setup {* del_prfstep_thm_eqforward @{thm coinitial_def} *}

lemma greatest_is_cofinal:
  "order(R) \<Longrightarrow> has_greatest(R,carrier(R)) \<Longrightarrow> cofinal(R,{greatest(R,carrier(R))})" by auto2

lemma least_is_coinitial:
  "order(R) \<Longrightarrow> has_least(R,carrier(R)) \<Longrightarrow> coinitial(R,{least(R,carrier(R))})" by auto2

section {* Upper and lower bounds *}  (* Bourbaki III.1.8 *)

definition upper_bound :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "upper_bound(R,X) = {y\<in>.R. \<forall>x\<in>X. x \<le>\<^sub>R y}"

lemma upper_boundD1 [forward]: "y \<in> upper_bound(R,X) \<Longrightarrow> y \<in>. R" by auto2
lemma upper_boundD2 [forward, backward2]:  "y \<in> upper_bound(R,X) \<Longrightarrow> x \<in> X \<Longrightarrow> x \<le>\<^sub>R y" by auto2
lemma upper_boundI [backward]: "y \<in>. R \<Longrightarrow> \<forall>x\<in>X. x \<le>\<^sub>R y \<Longrightarrow> y \<in> upper_bound(R,X)" by auto2
lemma upper_bound_eq_str [rewrite]: "eq_str_order(R,S) \<Longrightarrow> upper_bound(R,T) = upper_bound(S,T)" by auto2
setup {* del_prfstep_thm @{thm upper_bound_def} *}

definition lower_bound :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "lower_bound(R,X) = {y\<in>.R. \<forall>x\<in>X. y \<le>\<^sub>R x}"
  
lemma lower_boundD1 [forward]: "y \<in> lower_bound(R,X) \<Longrightarrow> y \<in>. R" by auto2
lemma lower_boundD2 [forward, backward2]:  "y \<in> lower_bound(R,X) \<Longrightarrow> x \<in> X \<Longrightarrow> x \<ge>\<^sub>R y" by auto2
lemma lower_boundI [backward]: "y \<in>. R \<Longrightarrow> \<forall>x\<in>X. x \<ge>\<^sub>R y \<Longrightarrow> y \<in> lower_bound(R,X)" by auto2
setup {* del_prfstep_thm @{thm lower_bound_def} *}

lemma upper_bound_trans [forward]:
  "order(R) \<Longrightarrow> x \<in> upper_bound(R,X) \<Longrightarrow> y \<ge>\<^sub>R x \<Longrightarrow> y \<in> upper_bound(R,X)" by auto2

lemma upper_bound_trans_subset [backward]:
  "X \<subseteq> Y \<Longrightarrow> upper_bound(R,Y) \<subseteq> upper_bound(R,X)" by auto2

lemma upper_bound_greatest:
  "order(R) \<Longrightarrow> has_greatest(R,carrier(R)) \<Longrightarrow> upper_bound(R,carrier(R)) = {greatest(R,carrier(R))}" by auto2

lemma upper_bound_greatest':
  "order(R) \<Longrightarrow> upper_bound(R,carrier(R)) = {a} \<Longrightarrow> greatest(R,carrier(R)) = a \<and> has_greatest(R,carrier(R))" by auto2

lemma lower_bound_trans [forward]:
  "order(R) \<Longrightarrow> x \<in> lower_bound(R,X) \<Longrightarrow> y \<le>\<^sub>R x \<Longrightarrow> y \<in> lower_bound(R,X)" by auto2

lemma lower_bound_trans_subset [backward]:
  "X \<subseteq> Y \<Longrightarrow> lower_bound(R,Y) \<subseteq> lower_bound(R,X)" by auto2

lemma lower_bound_least:
  "order(R) \<Longrightarrow> has_least(R,carrier(R)) \<Longrightarrow> lower_bound(R,carrier(R)) = {least(R,carrier(R))}" by auto2

lemma lower_bound_least':
  "order(R) \<Longrightarrow> lower_bound(R,carrier(R)) = {a} \<Longrightarrow> least(R,carrier(R)) = a \<and> has_least(R,carrier(R))" by auto2

section {* Supremum and infimum *}  (* Bourbaki III.1.9 *)

(* Definitions of sup and inf *)
definition has_sup :: "[i, i] \<Rightarrow> o" where [rewrite]:
  "has_sup(R,X) \<longleftrightarrow> has_least(R,upper_bound(R,X))"

definition sup :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "sup(R,X) = least(R,upper_bound(R,X))"

definition has_inf :: "[i, i] \<Rightarrow> o" where [rewrite]:
  "has_inf(R,X) \<longleftrightarrow> has_greatest(R,lower_bound(R,X))"

definition inf :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "inf(R,X) = greatest(R,lower_bound(R,X))"

lemma supI [backward]:
  "order(R) \<Longrightarrow> has_least(R,upper_bound(R,X)) \<and> least(R,upper_bound(R,X)) = x \<Longrightarrow>
   has_sup(R,X) \<and> sup(R,X) = x" by auto2

lemma infI [backward]:
  "order(R) \<Longrightarrow> has_greatest(R,lower_bound(R,X)) \<and> greatest(R,lower_bound(R,X)) = x \<Longrightarrow>
   has_inf(R,X) \<and> inf(R,X) = x" by auto2

(* Sup and inf for the image of a mapping *)
definition has_supf :: "[i, i] \<Rightarrow> o" where [rewrite]:
  "has_supf(R,f) \<longleftrightarrow> has_sup(R,image(f))"

definition supf :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "supf(R,f) = sup(R,image(f))"

lemma has_supfI [backward]:
  "order(R) \<Longrightarrow> has_least(R,upper_bound(R,image(f))) \<and> least(R,upper_bound(R,image(f))) = x \<Longrightarrow>
   has_supf(R,f) \<and> supf(R,f) = x" by auto2

(* Examples *)
lemma greatest_elt_is_sup:
  "order(R) \<Longrightarrow> has_greatest(R,X) \<Longrightarrow> sup(R,X) = greatest(R,X) \<and> has_sup(R,X)" by auto2

lemma least_elt_is_inf:
  "order(R) \<Longrightarrow> has_least(R,X) \<Longrightarrow> inf(R,X) = least(R,X) \<and> has_inf(R,X)" by auto2

lemma sup_of_empty:
  "order(R) \<Longrightarrow> has_least(R,carrier(R)) \<Longrightarrow> sup(R,\<emptyset>) = least(R,carrier(R)) \<and> has_sup(R,\<emptyset>)" by auto2

lemma inf_of_empty:
  "order(R) \<Longrightarrow> has_greatest(R,carrier(R)) \<Longrightarrow> inf(R,\<emptyset>) = greatest(R,carrier(R)) \<and> has_inf(R,\<emptyset>)" by auto2

lemma sup_of_subsets:
  "X \<subseteq> Pow(E) \<Longrightarrow> has_sup(subset_order(Pow(E)),X) \<and> sup(subset_order(Pow(E)),X) = \<Union>X" by auto2

lemma inf_of_subsets:
  "X \<noteq> \<emptyset> \<Longrightarrow> X \<subseteq> Pow(E) \<Longrightarrow> has_inf(subset_order(Pow(E)),X) \<and> inf(subset_order(Pow(E)),X) = \<Inter>X" by auto2

lemma inf_le_sup:
  "order(R) \<Longrightarrow> has_sup(R,X) \<Longrightarrow> has_inf(R,X) \<Longrightarrow> X \<noteq> \<emptyset> \<Longrightarrow> inf(R,X) \<le>\<^sub>R sup(R,X)" by auto2

(* For harder results, we use two lemmas *)
lemma sup_mem [typing]: "order(R) \<Longrightarrow> has_sup(R,X) \<Longrightarrow> sup(R,X) \<in>. R" by auto2

lemma sup_le [backward2]:
  "order(R) \<Longrightarrow> has_sup(R,X) \<Longrightarrow> a \<in>. R \<Longrightarrow> \<forall>x\<in>X. x \<le>\<^sub>R a \<Longrightarrow> sup(R,X) \<le>\<^sub>R a"
@proof @have "a \<in> upper_bound(R,X)" @qed

lemma sup_on_subset_le:
  "order(R) \<Longrightarrow> has_sup(R,A) \<Longrightarrow> has_sup(R,B) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> sup(R,A) \<le>\<^sub>R sup(R,B)" by auto2

lemma sup_trans:
  "order(R) \<Longrightarrow> f \<in> I \<rightarrow> carrier(R) \<Longrightarrow> g \<in> I \<rightarrow> carrier(R) \<Longrightarrow> \<forall>a\<in>I. f`a \<le>\<^sub>R g`a \<Longrightarrow>
   has_supf(R,f) \<Longrightarrow> has_supf(R,g) \<Longrightarrow> supf(R,f) \<le>\<^sub>R supf(R,g)" by auto2

lemma sup_subset1:
  "order(R) \<Longrightarrow> F \<subseteq> carrier(R) \<Longrightarrow> A \<subseteq> F \<Longrightarrow> has_sup(R,A) \<Longrightarrow> has_sup(suborder(R,F),A) \<Longrightarrow>
   sup(R,A) \<le>\<^sub>R sup(suborder(R,F),A)" by auto2

lemma sup_subset2:
  "order(R) \<Longrightarrow> F \<subseteq> carrier(R) \<Longrightarrow> A \<subseteq> F \<Longrightarrow> has_sup(R,A) \<Longrightarrow> sup(R,A) \<in> F \<Longrightarrow>
   has_sup(suborder(R,F),A) \<and> sup(suborder(R,F),A) = sup(R,A)" by auto2

section {* Directed sets *}  (* Bourbaki III.1.10 *)

definition right_directed :: "i \<Rightarrow> o" where [rewrite]:
  "right_directed(R) \<longleftrightarrow> order(R) \<and> (\<forall>x\<in>.R. \<forall>y\<in>.R. \<exists>z\<in>.R. z \<ge>\<^sub>R x \<and> z \<ge>\<^sub>R y)"

lemma right_directedE1 [forward]: "right_directed(R) \<Longrightarrow> order(R)" by auto2
lemma right_directedE2 [backward]: "right_directed(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> \<exists>z\<in>.R. z \<ge>\<^sub>R x \<and> z \<ge>\<^sub>R y" by auto2
setup {* del_prfstep_thm_eqforward @{thm right_directed_def} *}

lemma right_directed_max_is_greatest:
  "right_directed(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> maximal(R,a) \<Longrightarrow> has_greatest(R,carrier(R)) \<and> greatest(R,carrier(R)) = a"
@proof
  @have "\<forall>b\<in>.R. b \<le>\<^sub>R a" @with @obtain "z\<in>.R" where "z \<ge>\<^sub>R a \<and> z \<ge>\<^sub>R b" @end
@qed

lemma right_directed_prod:
  "\<forall>a\<in>I. right_directed(R`a) \<Longrightarrow> S = prod_rel(I,R) \<Longrightarrow> right_directed(S)"
@proof
  @let "E = prod_src(I,R)"
  @have "\<forall>x\<in>E. \<forall>y\<in>E. \<exists>z\<in>E. z \<ge>\<^sub>S x \<and> z \<ge>\<^sub>S y" @with
    @let "z = Tup(I, \<lambda>a. SOME w\<in>.R`a. le(R`a,x`a,w) \<and> le(R`a,y`a,w))"
    @have "z \<in> E" @have "z \<ge>\<^sub>S x"
  @end
@qed

lemma right_directed_cofinal:
  "right_directed(R) \<Longrightarrow> cofinal(R,A) \<Longrightarrow> right_directed(suborder(R,A))"
@proof
  @let "S = suborder(R,A)"
  @have "\<forall>x\<in>A. \<forall>y\<in>A. \<exists>z\<in>A. z \<ge>\<^sub>S x \<and> z \<ge>\<^sub>S y" @with
    @obtain "z'\<in>.R" where "z' \<ge>\<^sub>R x \<and> z' \<ge>\<^sub>R y" @obtain "z\<in>A" where "z' \<le>\<^sub>R z"
  @end
@qed

section {* Totally ordered sets *}  (* Bourbaki III.1.12 *)

definition linorder :: "i \<Rightarrow> o" where [rewrite]:
  "linorder(R) \<longleftrightarrow> (order(R) \<and> (\<forall>x\<in>.R. \<forall>y\<in>.R. x \<le>\<^sub>R y \<or> x \<ge>\<^sub>R y))"
  
lemma linorderD [forward]:
  "linorder(R) \<Longrightarrow> order(R)"
  "linorder(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> \<not>(x \<le>\<^sub>R y) \<Longrightarrow> x >\<^sub>R y"
  "linorder(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> \<not>(x <\<^sub>R y) \<Longrightarrow> x \<ge>\<^sub>R y" by auto2+
setup {* del_prfstep_thm_eqforward @{thm linorder_def} *}

lemma linorder_iso [forward]:
  "linorder(R) \<Longrightarrow> ord_isomorphic(R,S) \<Longrightarrow> linorder(S)"
@proof
  @obtain "f \<in> R \<cong>\<^sub>O S"
  @have "\<forall>x\<in>.S. \<forall>y\<in>.S. x \<le>\<^sub>S y \<or> x \<ge>\<^sub>S y" @with
    @obtain "x'\<in>.R" where "f`x' = x"
    @obtain "y'\<in>.R" where "f`y' = y"
  @end
@qed

lemma linorder_suborder:
  "linorder(R) \<Longrightarrow> A \<subseteq> carrier(R) \<Longrightarrow> linorder(suborder(R,A))" by auto2
setup {* add_forward_prfstep_cond @{thm linorder_suborder} [with_term "suborder(?R,?A)"] *}

lemma linorder_eq_str [forward]:
  "linorder(R) \<Longrightarrow> eq_str_order(R,S) \<Longrightarrow> linorder(S)" by auto2

lemma strict_monotone_to_inj:
  "is_morphism(f) \<Longrightarrow> R = source_str(f) \<Longrightarrow> linorder(R) \<Longrightarrow> order(target_str(f)) \<Longrightarrow>
   strict_incr(f) \<Longrightarrow> injective(f)"
@proof
  @have "\<forall>x\<in>.R. \<forall>y\<in>.R. x \<noteq> y \<longrightarrow> f`x \<noteq> f`y" @with @case "x \<ge>\<^sub>R y" @end
@qed

lemma incr_to_iso [backward]:
  "is_morphism(f) \<Longrightarrow> R = source_str(f) \<Longrightarrow> S = target_str(f) \<Longrightarrow>
   linorder(R) \<Longrightarrow> order(S) \<Longrightarrow> bijective(f) \<Longrightarrow> incr(f) \<Longrightarrow> ord_isomorphism(f)" by auto2

lemma supI_alt [backward1]:
  "linorder(R) \<Longrightarrow> b \<in> upper_bound(R,X) \<Longrightarrow>
   \<forall>c\<in>.R. c <\<^sub>R b \<longrightarrow> (\<exists>x\<in>X. c <\<^sub>R x \<and> x \<le>\<^sub>R b) \<Longrightarrow> has_sup(R,X) \<and> sup(R,X) = b" by auto2

lemma supD_alt [backward1]:
  "linorder(R) \<Longrightarrow> has_sup(R,X) \<Longrightarrow> c \<in>. R \<Longrightarrow> c <\<^sub>R sup(R,X) \<Longrightarrow>
   \<exists>x\<in>X. c <\<^sub>R x \<and> x \<le>\<^sub>R sup(R,X)" by auto2

section {* Maximum *}
  
definition max :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where max_def [rewrite]:
  "max(R,x,y) = (if x \<ge>\<^sub>R y then x else y)"
setup {* register_wellform_data ("max(R,x,y)", ["x \<in>. R", "y \<in>. R"]) *}

lemma max_type [typing]: "x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> max(R,x,y) \<in>. R" by auto2

lemma max_type_gen [backward1, backward2]: "a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> max(R,a,b) \<in> S" by auto2

lemma max_idem [rewrite]: "x \<in>. R \<Longrightarrow> max(R,x,x) = x" by auto2

lemma max_geD:
  "linorder(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x \<le>\<^sub>R max(R,x,y)"
  "linorder(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> y \<le>\<^sub>R max(R,x,y)" by auto2+
setup {* fold (fn th => add_forward_prfstep_cond th [with_term "max(?R,?x,?y)"]) @{thms max_geD} *}

lemma max_geI [backward1, backward2]:
  "preorder(R) \<Longrightarrow> x \<ge>\<^sub>R y \<Longrightarrow> x \<ge>\<^sub>R z \<Longrightarrow> x \<ge>\<^sub>R max(R,y,z)" by auto2

lemma max_greaterI [backward1, backward2]:
  "preorder(R) \<Longrightarrow> x >\<^sub>R y \<Longrightarrow> x >\<^sub>R z \<Longrightarrow> x >\<^sub>R max(R,y,z)" by auto2

lemma linorder_has_max3:
  "linorder(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow> \<exists>w. w \<ge>\<^sub>R x \<and> w \<ge>\<^sub>R y \<and> w \<ge>\<^sub>R z"
@proof @let "w = max(R,max(R,x,y),z)" @qed
setup {* add_backward_prfstep_cond @{thm linorder_has_max3} [
  with_filt (order_filter "x" "y"), with_filt (order_filter "y" "z")] *}

section {* Minimum *}
  
definition min :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where min_def [rewrite]:
  "min(R,x,y) = (if x \<le>\<^sub>R y then x else y)"
setup {* register_wellform_data ("min(R,x,y)", ["x \<in>. R", "y \<in>. R"]) *}

lemma min_type [typing]: "x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> min(R,x,y) \<in>. R" by auto2

lemma min_type_gen [backward1, backward2]: "a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> min(R,a,b) \<in> S" by auto2

lemma min_idem [rewrite]: "x \<in>. R \<Longrightarrow> min(R,x,x) = x" by auto2

lemma min_leD:
  "linorder(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x \<ge>\<^sub>R min(R,x,y)"
  "linorder(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> y \<ge>\<^sub>R min(R,x,y)" by auto2+
setup {* fold (fn th => add_forward_prfstep_cond th [with_term "min(?R,?x,?y)"]) @{thms min_leD} *}

lemma min_leI [backward1, backward2]:
  "preorder(R) \<Longrightarrow> x \<le>\<^sub>R y \<Longrightarrow> x \<le>\<^sub>R z \<Longrightarrow> x \<le>\<^sub>R min(R,y,z)" by auto2

lemma min_lessI [backward1, backward2]:
  "preorder(R) \<Longrightarrow> x <\<^sub>R y \<Longrightarrow> x <\<^sub>R z \<Longrightarrow> x <\<^sub>R min(R,y,z)" by auto2

setup {* del_prfstep_thm @{thm min_def} *}

lemma linorder_has_min3:
  "linorder(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow> \<exists>w. w \<le>\<^sub>R x \<and> w \<le>\<^sub>R y \<and> w \<le>\<^sub>R z"
@proof @let "w = min(R,min(R,x,y),z)" @qed
setup {* add_backward_prfstep_cond @{thm linorder_has_min3} [
  with_filt (order_filter "x" "y"), with_filt (order_filter "y" "z")] *}

(* To show equality between a linorder and an order, can also compare <. *)
lemma eq_linorder_order_less [backward1]:
  "ord_form(R) \<Longrightarrow> ord_form(S) \<Longrightarrow> linorder(R) \<Longrightarrow> order(S) \<Longrightarrow> carrier(R) = carrier(S) \<Longrightarrow>
   \<forall>x\<in>.R. \<forall>y\<in>.R. x <\<^sub>R y \<longrightarrow> x <\<^sub>S y \<Longrightarrow> R = S"
@proof
  @have (@rule) "\<forall>x\<in>.R. \<forall>y\<in>.R. x \<le>\<^sub>R y \<longrightarrow> x \<le>\<^sub>S y" @with @case "x = y" @end
@qed

section {* Directed family of ordering *}

(* This development is used in Bourbaki III.2.1 *)
definition is_suborder :: "[i, i] \<Rightarrow> o" where [rewrite]:
  "is_suborder(R,S) \<longleftrightarrow> (raworder(R) \<and> carrier(R) \<subseteq> carrier(S) \<and> (\<forall>x\<in>.R. \<forall>y\<in>.R. x \<le>\<^sub>R y \<longleftrightarrow> x \<le>\<^sub>S y))"

lemma is_suborderD1 [forward]: "is_suborder(R,S) \<Longrightarrow> raworder(R) \<and> carrier(R) \<subseteq> carrier(S)" by auto2
lemma is_suborderD2 [rewrite]:
  "x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> is_suborder(R,S) \<Longrightarrow> x \<le>\<^sub>R y \<longleftrightarrow> x \<le>\<^sub>S y" by auto2
lemma is_suborder_rewr [rewrite_back]:
  "ord_form(R) \<Longrightarrow> is_suborder(R,S) \<Longrightarrow> R = suborder(S,carrier(R))" by auto2
setup {* del_prfstep_thm_eqforward @{thm is_suborder_def} *}

lemma is_suborder_refl [resolve]: "preorder(R) \<Longrightarrow> is_suborder(R,R)" by auto2

lemma is_suborder_preorder [forward]: "preorder(R) \<Longrightarrow> is_suborder(A,R) \<Longrightarrow> preorder(A)" by auto2
lemma is_suborder_order [forward]: "order(R) \<Longrightarrow> is_suborder(A,R) \<Longrightarrow> order(A)" by auto2
lemma is_suborder_linorder [forward]: "linorder(R) \<Longrightarrow> is_suborder(A,R) \<Longrightarrow> linorder(A)" by auto2

definition directed_rels :: "i \<Rightarrow> o" where [rewrite]:
  "directed_rels(X) \<longleftrightarrow> ((\<forall>R\<in>X. order(R)) \<and>
    (\<forall>R\<in>X. \<forall>S\<in>X. \<exists>T\<in>X. is_suborder(R,T) \<and> is_suborder(S,T)))"

lemma directed_relsD1 [forward]:
  "directed_rels(X) \<Longrightarrow> R \<in> X \<Longrightarrow> order(R)" by auto2
lemma directed_relsD2 [backward]:
  "directed_rels(X) \<Longrightarrow> R \<in> X \<Longrightarrow> S \<in> X \<Longrightarrow> \<exists>T\<in>X. is_suborder(R,T) \<and> is_suborder(S,T)" by auto2
setup {* del_prfstep_thm_eqforward @{thm directed_rels_def} *}

(* Union of a family of ordering. Has good properties when the family is directed. *)
definition union_src :: "i \<Rightarrow> i" where [rewrite]:
  "union_src(X) = (\<Union>R\<in>X. carrier(R))"

definition union_rel :: "i \<Rightarrow> i" where [rewrite]:
  "union_rel(X) = Order(union_src(X), \<lambda>x y. \<exists>R\<in>X. x \<le>\<^sub>R y)"

lemma union_rel_is_raworder [typing]: "union_rel(X) \<in> raworder_space(union_src(X))" by auto2

lemma union_rel_eval [rewrite]:
  "U = union_rel(X) \<Longrightarrow> x \<in>. U \<Longrightarrow> y \<in>. U \<Longrightarrow> x \<le>\<^sub>U y \<longleftrightarrow> (\<exists>R\<in>X. x \<le>\<^sub>R y)" by auto2
setup {* del_prfstep_thm @{thm union_rel_def} *}

lemma directed_elt_in_rel2:
  "directed_rels(X) \<Longrightarrow> x \<in> union_src(X) \<Longrightarrow> y \<in> union_src(X) \<Longrightarrow> \<exists>R\<in>X. x \<in>. R \<and> y \<in>. R"
@proof
  @obtain "R\<in>X" where "x\<in>.R"
  @obtain "S\<in>X" where "y\<in>.S"
  @obtain "T\<in>X" where "is_suborder(R,T)" "is_suborder(S,T)"
@qed
setup {* add_backward_prfstep_cond @{thm directed_elt_in_rel2} [with_filt (order_filter "x" "y")] *}

lemma directed_elt_in_rel3:
  "directed_rels(X) \<Longrightarrow> x \<in> union_src(X) \<Longrightarrow> y \<in> union_src(X) \<Longrightarrow> z \<in> union_src(X) \<Longrightarrow>
   \<exists>R\<in>X. x \<in>. R \<and> y \<in>. R \<and> z \<in>. R"
@proof
  @obtain "R\<in>X" where "x\<in>.R" "y\<in>.R"
  @obtain "S\<in>X" where "z\<in>.S"
  @obtain "T\<in>X" where "is_suborder(R,T)" "is_suborder(S,T)"
@qed
setup {* add_backward_prfstep_cond @{thm directed_elt_in_rel3} [
  with_filt (order_filter "x" "y"), with_filt (order_filter "y" "z")] *}

lemma union_rel_prop:
  "directed_rels(X) \<Longrightarrow> R \<in> X \<Longrightarrow> U = union_rel(X) \<Longrightarrow> is_suborder(R,U)"
@proof
  @have "\<forall>x\<in>.R. \<forall>y\<in>.R. x \<le>\<^sub>R y \<longleftrightarrow> x \<le>\<^sub>U y" @with
    @case "x \<le>\<^sub>U y" @with
      @obtain "S\<in>X" where "x \<le>\<^sub>S y"
      @obtain "T\<in>X" where "is_suborder(R,T)" "is_suborder(S,T)"
    @end
  @end
@qed
setup {* add_forward_prfstep_cond @{thm union_rel_prop} [with_term "union_rel(?X)"] *}

lemma union_rel_unique_prop:
  "directed_rels(X) \<Longrightarrow> ord_form(R) \<Longrightarrow> order(R) \<Longrightarrow> carrier(R) = union_src(X) \<Longrightarrow>
   \<forall>S\<in>X. is_suborder(S,R) \<Longrightarrow> R = union_rel(X)"
@proof
  @have "\<forall>x\<in>union_src(X). \<forall>y\<in>union_src(X). x \<le>\<^sub>R y \<longleftrightarrow> le(union_rel(X),x,y)" @with
    @obtain "S\<in>X" where "x \<in>. S" "y \<in>. S" @end
@qed

lemma union_rel_preorder [forward]:
  "directed_rels(X) \<Longrightarrow> R = union_rel(X) \<Longrightarrow> preorder(R)"
@proof
  @have "\<forall>x y z. x \<le>\<^sub>R y \<longrightarrow> y \<le>\<^sub>R z \<longrightarrow> x \<le>\<^sub>R z" @with
    @obtain "S\<in>X" where "x \<in>. S" "y \<in>. S" "z \<in>. S"
    @have "x \<le>\<^sub>S y" @have "y \<le>\<^sub>S z"
  @end
@qed

lemma union_rel_order [forward]:
  "directed_rels(X) \<Longrightarrow> R = union_rel(X) \<Longrightarrow> order(R)"
@proof
  @have "\<forall>x\<in>union_src(X). \<forall>y\<in>union_src(X). x \<le>\<^sub>R y \<longrightarrow> y \<le>\<^sub>R x \<longrightarrow> x = y" @with
    @obtain "S\<in>X" where "x \<in>. S" "y \<in>. S" @end
@qed

lemma union_rel_linorder [backward]:
  "directed_rels(X) \<Longrightarrow> \<forall>R\<in>X. linorder(R) \<Longrightarrow> R = union_rel(X) \<Longrightarrow> linorder(R)"
@proof
  @have "\<forall>x\<in>union_src(X). \<forall>y\<in>union_src(X). x \<le>\<^sub>R y \<or> x \<ge>\<^sub>R y" @with
    @obtain "S\<in>X" where "x \<in>. S" "y \<in>. S" @end
@qed

section {* Linear continuum *}
  
definition order_unbounded :: "i \<Rightarrow> o" where [rewrite]:
  "order_unbounded(R) \<longleftrightarrow> (\<forall>x\<in>.R. (\<exists>y. y <\<^sub>R x) \<and> (\<exists>y. y >\<^sub>R x))"

lemma order_unboundedD [backward]:
  "order_unbounded(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<exists>y. y <\<^sub>R x"
  "order_unbounded(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<exists>y. y >\<^sub>R x" by auto2+
setup {* del_prfstep_thm_eqforward @{thm order_unbounded_def} *}

definition dense_order :: "i \<Rightarrow> o" where [rewrite]:
  "dense_order(R) \<longleftrightarrow> linorder(R) \<and> (\<forall>x y. x <\<^sub>R y \<longrightarrow> (\<exists>z. x <\<^sub>R z \<and> z <\<^sub>R y))"
  
lemma dense_orderI [forward]:
  "linorder(R) \<Longrightarrow> \<forall>x y. x <\<^sub>R y \<longrightarrow> (\<exists>z. x <\<^sub>R z \<and> z <\<^sub>R y) \<Longrightarrow> dense_order(R)" by auto2

lemma dense_orderE1 [forward]: "dense_order(R) \<Longrightarrow> linorder(R)" by auto2
lemma dense_orderE2 [backward]: "dense_order(R) \<Longrightarrow> x <\<^sub>R y \<Longrightarrow> \<exists>z. x <\<^sub>R z \<and> z <\<^sub>R y" by auto2
setup {* del_prfstep_thm @{thm dense_order_def} *}

definition linear_continuum :: "i \<Rightarrow> o" where [rewrite]:
  "linear_continuum(R) \<longleftrightarrow> dense_order(R) \<and> (\<forall>S. S \<noteq> \<emptyset> \<longrightarrow> upper_bound(R,S) \<noteq> \<emptyset> \<longrightarrow> has_sup(R,S))"

lemma linear_continuumD [forward]: "linear_continuum(R) \<Longrightarrow> dense_order(R)" by auto2+
    
lemma linear_continuumD2 [backward]:
  "linear_continuum(R) \<Longrightarrow> S \<noteq> \<emptyset> \<Longrightarrow> upper_bound(R,S) \<noteq> \<emptyset> \<Longrightarrow> has_sup(R,S)" by auto2+
    
lemma linear_continuumI [forward]:
  "dense_order(R) \<Longrightarrow> \<forall>S. S \<noteq> \<emptyset> \<longrightarrow> upper_bound(R,S) \<noteq> \<emptyset> \<longrightarrow> has_sup(R,S) \<Longrightarrow> linear_continuum(R)" by auto2
setup {* del_prfstep_thm @{thm linear_continuum_def} *}

lemma dense_order_eq_str [forward]:
  "dense_order(R) \<Longrightarrow> eq_str_order(R,S) \<Longrightarrow> dense_order(S)"
@proof
  @have "\<forall>x y. x <\<^sub>S y \<longrightarrow> (\<exists>z. x <\<^sub>S z \<and> z <\<^sub>S y)" @with
    @obtain z where "x <\<^sub>R z \<and> z <\<^sub>R y" @end
@qed

lemma linear_continuum_eq_str_ord [forward]:
  "linear_continuum(R) \<Longrightarrow> eq_str_order(R,S) \<Longrightarrow> linear_continuum(S)"
@proof
  @have "\<forall>T. T \<noteq> \<emptyset> \<longrightarrow> upper_bound(S,T) \<noteq> \<emptyset> \<longrightarrow> has_sup(S,T)" @with
    @have "has_sup(R,T)"
    @have "has_sup(S,T) \<and> sup(S,T) = sup(R,T)"
  @end
@qed

end
