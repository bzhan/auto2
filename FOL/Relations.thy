theory Relations
imports Structure
begin

section {* Relations *}

(* Image *)
definition rel_image :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "rel_image(\<Gamma>,A) = {y \<in> target(\<Gamma>). \<exists>x\<in>A. rel(\<Gamma>,x,y)}"
lemma rel_imageI [typing2]: "is_rel2(\<Gamma>) \<Longrightarrow> rel(\<Gamma>,x,y) \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> rel_image(\<Gamma>,A)" by auto2
lemma rel_image_iff [rewrite]: "is_rel2(\<Gamma>) \<Longrightarrow> y \<in> rel_image(\<Gamma>,A) \<longleftrightarrow> (\<exists>x\<in>A. rel(\<Gamma>,x,y))" by auto2
setup {* del_prfstep_thm @{thm rel_image_def} *}

lemma rel_image_empty [rewrite]: "is_rel2(\<Gamma>) \<Longrightarrow> rel_image(\<Gamma>,\<emptyset>) = \<emptyset>" by auto2
lemma rel_image_mono [backward]: "is_rel2(\<Gamma>) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> rel_image(\<Gamma>,A) \<subseteq> rel_image(\<Gamma>,B)" by auto2
lemma rel_image_domain [resolve]: "is_rel2(\<Gamma>) \<Longrightarrow> rel_image(\<Gamma>,A) \<subseteq> target(\<Gamma>)" by auto2

definition rel_section :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "rel_section(\<Gamma>,x) = {y \<in> target(\<Gamma>). rel(\<Gamma>,x,y)}"
lemma rel_sectionI [typing2]: "is_rel2(\<Gamma>) \<Longrightarrow> rel(\<Gamma>,x,y) \<Longrightarrow> y \<in> rel_section(\<Gamma>,x)" by auto2
lemma rel_section_iff [rewrite]: "is_rel2(\<Gamma>) \<Longrightarrow> y \<in> rel_section(\<Gamma>,x) \<longleftrightarrow> rel(\<Gamma>,x,y)" by auto2
setup {* del_prfstep_thm @{thm rel_section_def} *}

lemma rel_image_singleton [rewrite]:
  "is_rel2(\<Gamma>) \<Longrightarrow> rel_image(\<Gamma>,{x}) = rel_section(\<Gamma>,x)" by auto2

section {* Inverse of a relation *}  (* Bourbaki II.3.2 *)

(* Inverse of a relation *)
definition rel_inverse :: "i \<Rightarrow> i" where [rewrite]:
  "rel_inverse(\<Gamma>) = Rel2(target(\<Gamma>), source(\<Gamma>), \<lambda>x y. rel(\<Gamma>,y,x))"

lemma rel_inverse_is_rel [typing]: "rel_inverse(\<Gamma>) \<in> rel2_space(target(\<Gamma>),source(\<Gamma>))" by auto2

lemma rel_inverse_eval [rewrite]:
  "is_rel2(\<Gamma>) \<Longrightarrow> rel(rel_inverse(\<Gamma>),x,y) \<longleftrightarrow> rel(\<Gamma>,y,x)" by auto2
setup {* add_rewrite_rule_back_cond @{thm rel_inverse_eval} [with_term "rel_inverse(?\<Gamma>)"] *}
setup {* del_prfstep_thm @{thm rel_inverse_def} *}

lemma rel_inverse_inverse [rewrite]:
  "rel_form(\<Gamma>) \<Longrightarrow> rel_inverse(rel_inverse(\<Gamma>)) = \<Gamma>" by auto2

(* Inverse image *)
definition rel_vimage :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "rel_vimage(\<Gamma>,A) = rel_image(rel_inverse(\<Gamma>),A)"
lemma rel_vimageI [typing2]: "is_rel2(\<Gamma>) \<Longrightarrow> rel(\<Gamma>,x,y) \<Longrightarrow> y \<in> A \<Longrightarrow> x \<in> rel_vimage(\<Gamma>,A)" by auto2
lemma rel_vimage_iff [rewrite]: "is_rel2(\<Gamma>) \<Longrightarrow> x \<in> rel_vimage(\<Gamma>,A) \<longleftrightarrow> (\<exists>y\<in>A. rel(\<Gamma>,x,y))" by auto2
setup {* del_prfstep_thm @{thm rel_vimage_def} *}

lemma rel_vimage_empty [rewrite]: "is_rel2(\<Gamma>) \<Longrightarrow> rel_vimage(\<Gamma>,\<emptyset>) = \<emptyset>" by auto2
lemma rel_vimage_mono [backward]: "is_rel2(\<Gamma>) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> rel_vimage(\<Gamma>,A) \<subseteq> rel_vimage(\<Gamma>,B)" by auto2
lemma rel_vimage_domain [resolve]: "is_rel2(\<Gamma>) \<Longrightarrow> rel_vimage(\<Gamma>,A) \<subseteq> source(\<Gamma>)" by auto2

definition rel_vsection :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "rel_vsection(\<Gamma>,x) = rel_section(rel_inverse(\<Gamma>),x)"
lemma rel_vsectionI [typing2]: "is_rel2(\<Gamma>) \<Longrightarrow> rel(\<Gamma>,x,y) \<Longrightarrow> x \<in> rel_vsection(\<Gamma>,y)" by auto2
lemma rel_vsection_iff [rewrite]: "is_rel2(\<Gamma>) \<Longrightarrow> x \<in> rel_vsection(\<Gamma>,y) \<longleftrightarrow> rel(\<Gamma>,x,y)" by auto2
setup {* del_prfstep_thm @{thm rel_vsection_def} *}

lemma gr_vimage_singleton [rewrite]:
  "is_rel2(\<Gamma>) \<Longrightarrow> rel_vimage(\<Gamma>,{x}) = rel_vsection(\<Gamma>,x)" by auto2

section {* Composition of relations *}  (* Bourbaki II.3.3 *)

(* Since we want associativity in general, output \<emptyset> is either side is not a relation. *)
definition rel_comp :: "i \<Rightarrow> i \<Rightarrow> i"  (infixr "\<circ>\<^sub>r" 60) where [rewrite]:
  "\<Gamma>' \<circ>\<^sub>r \<Gamma> = Rel2(source(\<Gamma>), target(\<Gamma>'), \<lambda>x y. \<exists>z. rel(\<Gamma>,x,z) \<and> rel(\<Gamma>',z,y))"
setup {* register_wellform_data ("\<Gamma>' \<circ>\<^sub>r \<Gamma>", ["rel_form(\<Gamma>)", "rel_form(\<Gamma>')"]) *}
  
lemma rel_comp_is_rel [typing]:
  "is_rel2(\<Gamma>) \<Longrightarrow> is_rel2(\<Gamma>') \<Longrightarrow> \<Gamma>' \<circ>\<^sub>r \<Gamma> \<in> rel2_space(source(\<Gamma>), target(\<Gamma>'))" by auto2

lemma rel_comp_eval [rewrite]:
  "is_rel2(\<Gamma>) \<Longrightarrow> is_rel2(\<Gamma>') \<Longrightarrow> rel(\<Gamma>' \<circ>\<^sub>r \<Gamma>,x,y) \<longleftrightarrow> (\<exists>z. rel(\<Gamma>,x,z) \<and> rel(\<Gamma>',z,y))" by auto2
setup {* del_prfstep_thm @{thm rel_comp_def} *}

lemma rel_comp_assoc_l:
  "rel_form(x) \<Longrightarrow> rel_form(y) \<Longrightarrow> rel_form(z) \<Longrightarrow>
   x \<circ>\<^sub>r (y \<circ>\<^sub>r z) = (x \<circ>\<^sub>r y) \<circ>\<^sub>r z \<and> rel_form(x \<circ>\<^sub>r y)" by auto2
setup {* add_prfstep (FOL_Assoc.alg_assoc_prfstep (@{term rel_comp}, @{thm rel_comp_assoc_l})) *}

lemma rel_comp_inverse [rewrite_bidir]:
  "is_rel2(\<Gamma>) \<Longrightarrow> is_rel2(\<Gamma>') \<Longrightarrow> rel_inverse(\<Gamma>' \<circ>\<^sub>r \<Gamma>) = rel_inverse(\<Gamma>) \<circ>\<^sub>r rel_inverse(\<Gamma>')" by auto2

lemma rel_comp_image [rewrite]:
  "is_rel2(\<Gamma>) \<Longrightarrow> is_rel2(\<Gamma>') \<Longrightarrow> rel_image(\<Gamma>' \<circ>\<^sub>r \<Gamma>, A) = rel_image(\<Gamma>', rel_image(\<Gamma>,A))" by auto2

lemma rel_comp_inv_image [backward]:
  "is_rel2(\<Gamma>) \<Longrightarrow> A \<subseteq> rel_vimage(\<Gamma>,target(\<Gamma>)) \<Longrightarrow> A \<subseteq> rel_image(rel_inverse(\<Gamma>) \<circ>\<^sub>r \<Gamma>, A)" by auto2

lemma rel_comp_inv_image2 [backward]:
  "is_rel2(\<Gamma>) \<Longrightarrow> rel_image(\<Gamma>,source(\<Gamma>)) \<subseteq> A \<Longrightarrow> rel_image(\<Gamma> \<circ>\<^sub>r rel_inverse(\<Gamma>), A) \<subseteq> A" by auto2

(* Identity relation *)
definition id_rel :: "i \<Rightarrow> i" where [rewrite]:
  "id_rel(A) = Rel(A, \<lambda>x y. x = y)"

lemma id_rel_is_rel [typing]: "id_rel(A) \<in> rel_space(A)" by auto2

lemma id_rel_inverse [rewrite]:
  "rel_inverse(id_rel(A)) = id_rel(A)" by auto2

lemma id_rel_comp1 [rewrite]:
  "rel_form(\<Gamma>) \<Longrightarrow> id_rel(target(\<Gamma>)) \<circ>\<^sub>r \<Gamma> = \<Gamma>" by auto2

lemma id_rel_comp2 [rewrite]:
  "rel_form(\<Gamma>) \<Longrightarrow> \<Gamma> \<circ>\<^sub>r id_rel(source(\<Gamma>)) = \<Gamma>" by auto2

end
