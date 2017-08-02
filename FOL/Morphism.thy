theory Morphism
imports Functions
begin

setup {* fold add_rewrite_rule [
  @{thm source_def}, @{thm target_def}, @{thm graph_def}, @{thm carrier_def}] *}

section {* Components of morphisms *}

(* A morphism is a function with two additional components, giving the source
   and target structure of the morphism. *)
definition source_str :: "i \<Rightarrow> i" where [rewrite]:
  "source_str(F) = fst(snd(snd(snd(F))))"
 
definition target_str :: "i \<Rightarrow> i" where [rewrite]:
  "target_str(F) = fst(snd(snd(snd(snd(F)))))"

setup {* fold add_property_field_const [@{term source_str}, @{term target_str}] *}

definition is_morphism :: "i \<Rightarrow> o" where [rewrite]:
  "is_morphism(f) \<longleftrightarrow> is_function(f) \<and> carrier(source_str(f)) = source(f) \<and> carrier(target_str(f)) = target(f)"
setup {* add_property_const @{term is_morphism} *}

definition mor_form :: "i \<Rightarrow> o" where [rewrite]:
  "mor_form(f) \<longleftrightarrow> is_morphism(f) \<and>
      f = \<langle>source(f),target(f),graph(f),source_str(f),target_str(f),\<emptyset>\<rangle>"
setup {* add_property_const @{term mor_form} *}

lemma is_morphism_gen_to_fun [forward]: "is_morphism(F) \<Longrightarrow> is_function(F)" by auto2
lemma is_morphism_to_gen [forward]: "mor_form(F) \<Longrightarrow> is_morphism(F)" by auto2

lemma is_morphism_src [forward]:
  "is_morphism(F) \<Longrightarrow> carrier(source_str(F)) = source(F) \<and> carrier(target_str(F)) = target(F)" by auto2

(* Space of all morphisms between structures S and T. *)
definition mor_space :: "i \<Rightarrow> i \<Rightarrow> i" (infix "\<rightharpoonup>" 60) where [rewrite]:
  "mor_space(S,T) = (let A = carrier(S) in let B = carrier(T) in {\<langle>A,B,G,S,T,\<emptyset>\<rangle>. G\<in>func_graphs(A,B)})"

lemma mor_spaceD [forward]:
  "F \<in> S \<rightharpoonup> T \<Longrightarrow> mor_form(F) \<and> source_str(F) = S \<and> target_str(F) = T" by auto2

lemma mor_spaceI [forward]:
  "mor_form(F) \<Longrightarrow> F \<in> source_str(F) \<rightharpoonup> target_str(F)" by auto2
    
(* Constructor for morphisms *)
definition Mor :: "[i, i, i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "Mor(S,T,b) = (let A = carrier(S) in let B = carrier(T) in \<langle>A,B,{p\<in>A\<times>B. snd(p) = b(fst(p))},S,T,\<emptyset>\<rangle>)"
setup {* add_prfstep_check_req ("Mor(S,T,b)", "Mor(S,T,b) \<in> S \<rightharpoonup> T") *}

lemma Mor_is_morphism [backward]:
  "\<forall>x\<in>.S. f(x)\<in>.T \<Longrightarrow> Mor(S,T,f) \<in> S \<rightharpoonup> T"
@proof @have "\<forall>x\<in>.S. \<langle>x,f(x)\<rangle>\<in>graph(Mor(S,T,f))" @qed

setup {* add_rewrite_rule @{thm feval_def} *}
lemma Mor_eval [rewrite]:
  "F = Mor(S,T,f) \<Longrightarrow> x \<in> source(F) \<Longrightarrow> is_morphism(F) \<Longrightarrow> F`x = f(x)" by auto2

(* Equality between morphisms *)
lemma morphism_eq [backward]:
  "mor_form(f) \<Longrightarrow> mor_form(g) \<Longrightarrow> source_str(f) = source_str(g) \<Longrightarrow> target_str(f) = target_str(g) \<Longrightarrow>
   \<forall>x\<in>source(f). f`x = g`x \<Longrightarrow> f = g" by auto2
setup {* del_prfstep_thm @{thm feval_def} *}

setup {* fold del_prfstep_thm [
  @{thm mor_form_def}, @{thm is_morphism_def}, @{thm mor_space_def}, @{thm Mor_def}] *}
  
setup {* fold del_prfstep_thm [@{thm source_def}, @{thm target_def}, @{thm graph_def},
  @{thm carrier_def}, @{thm source_str_def}, @{thm target_str_def}] *}

(* A small exercise *)
lemma Mor_eq_self:
  "f \<in> A \<rightharpoonup> B \<Longrightarrow> f = Mor(A,B, \<lambda>x. f`x)" by auto2

section {* Important examples of morphisms *}
  
(* Identity morphism *)
definition id_mor :: "i \<Rightarrow> i" where [rewrite]:
  "id_mor(A) = Mor(A,A, \<lambda>x. x)"

lemma id_mor_is_morphism [typing]: "id_mor(A) \<in> A \<rightharpoonup> A" by auto2
lemma id_mor_eval [rewrite]: "x \<in> source(id_mor(A)) \<Longrightarrow> id_mor(A) ` x = x" by auto2
lemma id_mor_vImage [rewrite]: "X \<subseteq> source(id_mor(A)) \<Longrightarrow> id_mor(A) -`` X = X" by auto2
setup {* del_prfstep_thm @{thm id_mor_def} *}
setup {* add_rewrite_rule_back @{thm id_mor_def} *}

(* Constant morphism *)
definition const_mor :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "const_mor(A,B,y) = Mor(A,B, \<lambda>x. y)"
setup {* register_wellform_data ("const_mor(A,B,y)", ["y \<in>. B"]) *}
setup {* add_prfstep_check_req ("const_mor(A,B,y)", "y \<in>. B") *}

lemma const_mor_is_function [typing]: "y \<in>. B \<Longrightarrow> const_mor(A,B,y) \<in> A \<rightharpoonup> B" by auto2
lemma const_mor_eval [rewrite]: "y \<in>. B \<Longrightarrow> f = const_mor(A,B,y) \<Longrightarrow> x \<in> source(f) \<Longrightarrow> f`x = y" by auto2
lemma const_mor_vImage [rewrite]: "y \<in>. Y \<Longrightarrow> y \<notin> A \<Longrightarrow> const_mor(X,Y,y) -`` A = \<emptyset>" by auto2
lemma const_mor_vImage2 [rewrite]: "y \<in>. Y \<Longrightarrow> y \<in> A \<Longrightarrow> const_mor(X,Y,y) -`` A = carrier(X)" by auto2
setup {* del_prfstep_thm @{thm const_mor_def} *}
setup {* add_rewrite_rule_back @{thm const_mor_def} *}

section {* Composition and inverse of morphisms *}
  
(* Composition of two morphisms *)
definition mor_comp :: "i \<Rightarrow> i \<Rightarrow> i"  (infixr "\<circ>\<^sub>m" 60) where [rewrite]:
  "g \<circ>\<^sub>m f = Mor(source_str(f), target_str(g), \<lambda>x. g`(f`x))"
setup {* register_wellform_data
  ("g \<circ>\<^sub>m f", ["mor_form(g)", "mor_form(f)", "target_str(f) = source_str(g)"]) *}
setup {* add_prfstep_check_req ("g \<circ>\<^sub>m f", "target_str(f) = source_str(g)") *}

lemma mor_comp_is_morphism [typing]:
  "is_morphism(f) \<Longrightarrow> is_morphism(g) \<Longrightarrow> target_str(f) = source_str(g) \<Longrightarrow>
   g \<circ>\<^sub>m f \<in> source_str(f) \<rightharpoonup> target_str(g)" by auto2
  
lemma mor_comp_eval [rewrite]:
  "is_morphism(f) \<Longrightarrow> is_morphism(g) \<Longrightarrow> target_str(f) = source_str(g) \<Longrightarrow>
   x \<in> source(f) \<Longrightarrow> (g \<circ>\<^sub>m f) ` x = g ` (f ` x)" by auto2
setup {* add_rewrite_rule_back_cond @{thm mor_comp_eval} [with_term "?g \<circ>\<^sub>m ?f"] *}
setup {* del_prfstep_thm @{thm mor_comp_def} *}

lemma mor_comp_assoc_l:
  "mor_form(x) \<Longrightarrow> mor_form(y) \<Longrightarrow> mor_form(z) \<Longrightarrow> target_str(z) = source_str(y) \<Longrightarrow>
   target_str(y \<circ>\<^sub>m z) = source_str(x) \<Longrightarrow> x \<circ>\<^sub>m (y \<circ>\<^sub>m z) = (x \<circ>\<^sub>m y) \<circ>\<^sub>m z \<and>
   mor_form(x \<circ>\<^sub>m y) \<and> target_str(y) = source_str(x) \<and> target_str(z) = source_str(x \<circ>\<^sub>m y)" by auto2
setup {* add_prfstep (FOL_Assoc.alg_assoc_prfstep (@{term mor_comp}, @{thm mor_comp_assoc_l})) *}

lemma comp_id_left [rewrite]:
  "mor_form(f) \<Longrightarrow> id_mor(target_str(f)) \<circ>\<^sub>m f = f" by auto2

lemma comp_id_right [rewrite]:
  "mor_form(f) \<Longrightarrow> f \<circ>\<^sub>m id_mor(source_str(f)) = f" by auto2

lemma const_mor_left_compose [rewrite]:
  "is_morphism(f) \<Longrightarrow> Y = source_str(f) \<Longrightarrow> Z = target_str(f) \<Longrightarrow> a \<in>. Y \<Longrightarrow>
   f \<circ>\<^sub>m const_mor(X,Y,a) = const_mor(X,Z,f`a)" by auto2

lemma mor_vImage_comp [rewrite]:
  "is_morphism(f) \<Longrightarrow> is_morphism(g) \<Longrightarrow> target_str(f) = source_str(g) \<Longrightarrow>
   (g \<circ>\<^sub>m f) -`` V = f -`` (g -`` V)" by auto2
setup {* add_rewrite_rule_back_cond @{thm mor_vImage_comp} [with_term "?g \<circ>\<^sub>m ?f"] *}

section {* Injective, surjective, and bijective morphisms. *}

(* Example: injective morphism. *)
definition inj_mor :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "inj_mor(S,T) = Mor(S,T,\<lambda>x. x)"
setup {* register_wellform_data ("inj_mor(S,T)", ["carrier(S) \<subseteq> carrier(T)"]) *}

lemma inj_mor_is_morphism [typing]: "carrier(S) \<subseteq> carrier(T) \<Longrightarrow> inj_mor(S,T) \<in> S \<rightharpoonup> T" by auto2
lemma inj_mor_eval [rewrite]: "carrier(S) \<subseteq> carrier(T) \<Longrightarrow> x \<in> source(inj_mor(S,T)) \<Longrightarrow> inj_mor(S,T)`x = x" by auto2
lemma inj_mor_vImage [rewrite]:
  "carrier(X) \<subseteq> carrier(Y) \<Longrightarrow> inj_mor(X,Y) -`` A = carrier(X) \<inter> A" by auto2
setup {* del_prfstep_thm @{thm inj_mor_def} *}
setup {* add_rewrite_rule_back @{thm inj_mor_def} *}

lemma inj_mor_is_injective: "carrier(S) \<subseteq> carrier(T) \<Longrightarrow> injective(inj_mor(S,T))" by auto2
lemma id_mor_is_bijective: "bijective(id_mor(S))" by auto2

section {* Inverse morphism *}

definition inverse_mor :: "i \<Rightarrow> i" where [rewrite]:
  "inverse_mor(f) = Mor(target_str(f), source_str(f), \<lambda>y. THE x. x\<in>source(f) \<and> f`x=y)"

lemma has_inverse_mor [typing]:
  "is_morphism(f) \<Longrightarrow> bijective(f) \<Longrightarrow> inverse_mor(f) \<in> target_str(f) \<rightharpoonup> source_str(f)" by auto2

lemma inverse_mor_eval1 [rewrite]:
  "is_morphism(f) \<Longrightarrow> bijective(f) \<Longrightarrow> x \<in> source(f) \<Longrightarrow> f`x = y \<Longrightarrow> inverse_mor(f)`y = x" by auto2

lemma inverse_mor_eval2 [rewrite]:
  "is_morphism(f) \<Longrightarrow> bijective(f) \<Longrightarrow> y \<in> source(inverse_mor(f)) \<Longrightarrow> inverse_mor(f)`y = x \<Longrightarrow> f`x = y" by auto2
setup {* del_prfstep_thm @{thm inverse_mor_def} *}
  
lemma inv_mor_bijective [forward]:
  "is_morphism(f) \<Longrightarrow> bijective(f) \<Longrightarrow> bijective(inverse_mor(f))"
@proof @have "\<forall>x\<in>source(f). inverse_mor(f)`(f`x) = x" @qed

lemma inverse_is_left_inv [rewrite]:
  "is_morphism(f) \<Longrightarrow> bijective(f) \<Longrightarrow> inverse_mor(f) \<circ>\<^sub>m f = id_mor(source_str(f))" by auto2

lemma inverse_is_right_inv [rewrite]:
  "is_morphism(f) \<Longrightarrow> bijective(f) \<Longrightarrow> f \<circ>\<^sub>m inverse_mor(f) = id_mor(target_str(f))" by auto2

lemma inverse_mor_unique [rewrite]:
  "is_morphism(f) \<Longrightarrow> bijective(f) \<Longrightarrow> mor_form(g) \<Longrightarrow> target_str(f) = source_str(g) \<Longrightarrow>
   g \<circ>\<^sub>m f = id_mor(source_str(f)) \<Longrightarrow> inverse_mor(f) = g" by auto2

lemma inverse_mor_unique' [rewrite]:
  "is_morphism(f) \<Longrightarrow> bijective(f) \<Longrightarrow> mor_form(g) \<Longrightarrow> target_str(g) = source_str(f) \<Longrightarrow>
   f \<circ>\<^sub>m g = id_mor(source_str(f)) \<Longrightarrow> inverse_mor(f) = g" by auto2

section {* Left and right inverses *}

lemma has_left_inverse_mor_inj [forward]:
  "is_morphism(f) \<Longrightarrow> is_morphism(r) \<Longrightarrow> target_str(f) = source_str(r) \<Longrightarrow>
   r \<circ>\<^sub>m f = id_mor(source_str(f)) \<Longrightarrow> injective(f)"
@proof
  @have "\<forall>x\<in>source(f). \<forall>y\<in>source(f). f`x = f`y \<longrightarrow> x=y" @with @have "r`(f`x)=x" @end
@qed

lemma has_right_inverse_mor_surj [forward]:
  "is_morphism(f) \<Longrightarrow> is_morphism(s) \<Longrightarrow> target_str(s) = source_str(f) \<Longrightarrow>
   f \<circ>\<^sub>m s = id_mor(target_str(f)) \<Longrightarrow> surjective(f)"
@proof
  @have "\<forall>x\<in>target(f). x\<in>image(f)" @with @have "f`(s`x) = x" @end
@qed

(* Two morphisms that are inverses of each other. *)
definition inverse_mor_pair :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "inverse_mor_pair(f,g) \<longleftrightarrow> (is_morphism(f) \<and> is_morphism(g) \<and>
     source_str(f) = target_str(g) \<and> target_str(f) = source_str(g) \<and>
     f \<circ>\<^sub>m g = id_mor(source_str(g)) \<and> g \<circ>\<^sub>m f = id_mor(source_str(f)))"

lemma inverse_mor_pair_bijective [forward]:
  "inverse_mor_pair(f,g) \<Longrightarrow> is_morphism(f) \<and> is_morphism(g) \<and>
   source_str(f) = target_str(g) \<and> source_str(g) = target_str(f) \<and> bijective(f) \<and> bijective(g)" by auto2

lemma inverse_mor_pairI [backward]:
  "is_morphism(f) \<Longrightarrow> is_morphism(g) \<Longrightarrow> source_str(f) = target_str(g) \<Longrightarrow> source_str(g) = target_str(f) \<Longrightarrow>
   \<forall>x\<in>source(g). f`(g`x) = x \<Longrightarrow> \<forall>x\<in>source(f). g`(f`x) = x \<Longrightarrow> inverse_mor_pair(f,g)" by auto2

lemma inverse_mor_pairE [rewrite]:
  "inverse_mor_pair(f,g) \<Longrightarrow> f \<circ>\<^sub>m g = id_mor(source_str(g))"
  "inverse_mor_pair(f,g) \<Longrightarrow> g \<circ>\<^sub>m f = id_mor(source_str(f))" by auto2+
setup {* del_prfstep_thm @{thm inverse_mor_pair_def} *}

lemma inverse_mor_pair_inverse [rewrite]:
  "mor_form(g) \<Longrightarrow> inverse_mor_pair(f,g) \<Longrightarrow> inverse_mor(f) = g"
@proof @have "g \<circ>\<^sub>m f = id_mor(source_str(f))" @qed
    
lemma inverse_mor_pair_inverse2 [rewrite]:
  "mor_form(f) \<Longrightarrow> inverse_mor_pair(f,g) \<Longrightarrow> inverse_mor(g) = f"
@proof @have "g \<circ>\<^sub>m f = id_mor(source_str(f))" @qed

(* Construction of left and right inverses. *)
lemma exists_right_inverse_mor [resolve]:
  "is_morphism(f) \<Longrightarrow> surjective(f) \<Longrightarrow> A = source_str(f) \<Longrightarrow> B = target_str(f) \<Longrightarrow> \<exists>s\<in>B\<rightharpoonup>A. f \<circ>\<^sub>m s = id_mor(B)"
@proof @let "s = Mor(B,A, \<lambda>y. SOME x\<in>.A. f`x=y)" @qed

lemma exists_pullback_surj_mor [backward1]:
  "is_morphism(f) \<Longrightarrow> surjective(g) \<Longrightarrow> g \<in> E \<rightharpoonup> F \<Longrightarrow> f \<in> E \<rightharpoonup> G \<Longrightarrow>
   \<forall>x\<in>.E. \<forall>y\<in>.E. g`x=g`y \<longrightarrow> f`x=f`y \<Longrightarrow> \<exists>!h. h\<in>F\<rightharpoonup>G \<and> f = h \<circ>\<^sub>m g"
@proof
  @have "\<exists>h\<in>F\<rightharpoonup>G. f = h \<circ>\<^sub>m g" @with
    @obtain "s\<in>F\<rightharpoonup>E" where "g \<circ>\<^sub>m s = id_mor(F)" @then
    @obtain "h\<in>F\<rightharpoonup>G" where "h = f \<circ>\<^sub>m s"
  @end
@qed

end
