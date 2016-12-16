theory Relations
imports Set
begin

section {* Relations *}  (* Bourbaki II.3.1 *)

(* Relations (and later functions) are represented by a tuple consisting of
   the source and target sets, and a set of pairs. *)
definition source :: "i \<Rightarrow> i" where source_def [rewrite]:
  "source(\<Gamma>) = fst(\<Gamma>)"
definition target :: "i \<Rightarrow> i" where target_def [rewrite]:
  "target(\<Gamma>) = fst(snd(\<Gamma>))"
definition graph :: "i \<Rightarrow> i" where graph_def [rewrite]:
  "graph(\<Gamma>) = snd(snd(\<Gamma>))"

(* Collection of all relations *)
definition is_relation :: "i \<Rightarrow> o" where is_relation_def [rewrite]:
  "is_relation(\<Gamma>) \<longleftrightarrow> (\<exists>S T G. \<Gamma> = \<langle>S,T,G\<rangle> \<and> G\<in>Pow(S\<times>T))"
setup {* add_property_const @{term is_relation} *}

(* Space of all relations between S and T *)
definition rel2_space :: "i \<Rightarrow> i \<Rightarrow> i" where rel2_space_def [rewrite]:
  "rel2_space(S,T) = {\<langle>S,T,G\<rangle>. G\<in>Pow(S\<times>T)}"

lemma rel2_space_iff [rewrite]:
  "\<Gamma> \<in> rel2_space(S,T) \<longleftrightarrow> (is_relation(\<Gamma>) \<and> source(\<Gamma>) = S \<and> target(\<Gamma>) = T)" by auto2

lemma rel2_spaceI [typing]:
  "is_relation(\<Gamma>) \<Longrightarrow> \<Gamma> \<in> rel2_space(source(\<Gamma>), target(\<Gamma>))" by auto2

(* \<emptyset> is used as a default value. *)
lemma empty_not_relation [resolve]: "\<emptyset> \<notin> rel2_space(S,T)" by auto2

(* Constructor for relations *)
definition Rel2 :: "i \<Rightarrow> i \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> o) \<Rightarrow> i" where Rel_def [rewrite]:
  "Rel2(S,T,R) = \<langle>S, T, {p\<in>S\<times>T. R(fst(p),snd(p))}\<rangle>"

lemma Rel_is_relation [typing]: "Rel2(S,T,R) \<in> rel2_space(S,T)" by auto2

(* Evaluation of relation *)
definition rel :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o" where rel_def [rewrite_bidir]:
  "rel(\<Gamma>,x,y) \<longleftrightarrow> \<langle>x,y\<rangle>\<in>graph(\<Gamma>)"

lemma Rel_eval [rewrite]:
  "rel(Rel2(S,T,R),x,y) \<longleftrightarrow> (x\<in>S \<and> y\<in>T \<and> R(x,y))" by auto2

lemma RelD [forward]:
  "is_relation(\<Gamma>) \<Longrightarrow> rel(\<Gamma>,x,y) \<Longrightarrow> x \<in> source(\<Gamma>) \<and> y \<in> target(\<Gamma>)" by auto2

(* Equality on relations *)
lemma relation_eq:
  "is_relation(\<Gamma>) \<Longrightarrow> is_relation(\<Gamma>') \<Longrightarrow> source(\<Gamma>) = source(\<Gamma>') \<Longrightarrow> target(\<Gamma>) = target(\<Gamma>') \<Longrightarrow>
   \<forall>x y. rel(\<Gamma>,x,y) \<longleftrightarrow> rel(\<Gamma>',x,y) \<Longrightarrow> \<Gamma> = \<Gamma>'"
  by (tactic {* auto2s_tac @{context} (HAVE "graph(\<Gamma>) = graph(\<Gamma>')") *})
setup {* add_backward_prfstep_cond @{thm relation_eq} [with_filt (order_filter "\<Gamma>" "\<Gamma>'")] *}

(* Relations on a single space *)
abbreviation rel_space :: "i \<Rightarrow> i" where
  "rel_space(S) \<equiv> rel2_space(S,S)"

abbreviation Rel :: "i \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> o) \<Rightarrow> i" where
  "Rel(S,R) \<equiv> Rel2(S,S,R)"

setup {* fold del_prfstep_thm [
  @{thm source_def}, @{thm target_def}, @{thm graph_def}, @{thm is_relation_def}, @{thm rel_def},
  @{thm rel2_space_def}, @{thm Rel_def}] *}
hide_const graph

(* Image *)
definition rel_image :: "i \<Rightarrow> i \<Rightarrow> i" where rel_image_def [rewrite]:
  "rel_image(\<Gamma>,A) = {y \<in> target(\<Gamma>). \<exists>x\<in>A. rel(\<Gamma>,x,y)}"
lemma rel_imageI [typing2]: "is_relation(\<Gamma>) \<Longrightarrow> rel(\<Gamma>,x,y) \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> rel_image(\<Gamma>,A)" by auto2
lemma rel_image_iff [rewrite]: "is_relation(\<Gamma>) \<Longrightarrow> y \<in> rel_image(\<Gamma>,A) \<longleftrightarrow> (\<exists>x\<in>A. rel(\<Gamma>,x,y))" by auto2
setup {* del_prfstep_thm @{thm rel_image_def} *}

lemma rel_image_empty [rewrite]: "is_relation(\<Gamma>) \<Longrightarrow> rel_image(\<Gamma>,\<emptyset>) = \<emptyset>" by auto2
lemma rel_image_mono [backward]: "is_relation(\<Gamma>) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> rel_image(\<Gamma>,A) \<subseteq> rel_image(\<Gamma>,B)" by auto2
lemma rel_image_domain [resolve]: "is_relation(\<Gamma>) \<Longrightarrow> rel_image(\<Gamma>,A) \<subseteq> target(\<Gamma>)" by auto2

definition rel_section :: "i \<Rightarrow> i \<Rightarrow> i" where rel_section_def [rewrite]:
  "rel_section(\<Gamma>,x) = {y \<in> target(\<Gamma>). rel(\<Gamma>,x,y)}"
lemma rel_sectionI [typing2]: "is_relation(\<Gamma>) \<Longrightarrow> rel(\<Gamma>,x,y) \<Longrightarrow> y \<in> rel_section(\<Gamma>,x)" by auto2
lemma rel_section_iff [rewrite]: "is_relation(\<Gamma>) \<Longrightarrow> y \<in> rel_section(\<Gamma>,x) \<longleftrightarrow> rel(\<Gamma>,x,y)" by auto2
setup {* del_prfstep_thm @{thm rel_section_def} *}

lemma rel_image_singleton [rewrite]:
  "is_relation(\<Gamma>) \<Longrightarrow> rel_image(\<Gamma>,{x}) = rel_section(\<Gamma>,x)" by auto2

section {* Inverse of a relation *}  (* Bourbaki II.3.2 *)

(* Inverse of a relation *)
definition rel_inverse :: "i \<Rightarrow> i" where rel_inverse_def [rewrite]:
  "rel_inverse(\<Gamma>) = Rel2(target(\<Gamma>), source(\<Gamma>), \<lambda>x y. rel(\<Gamma>,y,x))"

lemma rel_inverse_is_rel [typing]: "rel_inverse(\<Gamma>) \<in> rel2_space(target(\<Gamma>),source(\<Gamma>))" by auto2

lemma rel_inverse_eval [rewrite]:
  "is_relation(\<Gamma>) \<Longrightarrow> rel(rel_inverse(\<Gamma>),x,y) \<longleftrightarrow> rel(\<Gamma>,y,x)" by auto2
setup {* add_rewrite_rule_back_cond @{thm rel_inverse_eval} [with_term "rel_inverse(?\<Gamma>)"] *}
setup {* del_prfstep_thm @{thm rel_inverse_def} *}

lemma rel_inverse_inverse [rewrite]:
  "is_relation(\<Gamma>) \<Longrightarrow> rel_inverse(rel_inverse(\<Gamma>)) = \<Gamma>" by auto2

(* Inverse image *)
definition rel_vimage :: "i \<Rightarrow> i \<Rightarrow> i" where rel_vimage_def [rewrite]:
  "rel_vimage(\<Gamma>,A) = rel_image(rel_inverse(\<Gamma>),A)"
lemma rel_vimageI [typing2]: "is_relation(\<Gamma>) \<Longrightarrow> rel(\<Gamma>,x,y) \<Longrightarrow> y \<in> A \<Longrightarrow> x \<in> rel_vimage(\<Gamma>,A)" by auto2
lemma rel_vimage_iff [rewrite]: "is_relation(\<Gamma>) \<Longrightarrow> x \<in> rel_vimage(\<Gamma>,A) \<longleftrightarrow> (\<exists>y\<in>A. rel(\<Gamma>,x,y))" by auto2
setup {* del_prfstep_thm @{thm rel_vimage_def} *}

lemma rel_vimage_empty [rewrite]: "is_relation(\<Gamma>) \<Longrightarrow> rel_vimage(\<Gamma>,\<emptyset>) = \<emptyset>" by auto2
lemma rel_vimage_mono [backward]: "is_relation(\<Gamma>) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> rel_vimage(\<Gamma>,A) \<subseteq> rel_vimage(\<Gamma>,B)" by auto2
lemma rel_vimage_domain [resolve]: "is_relation(\<Gamma>) \<Longrightarrow> rel_vimage(\<Gamma>,A) \<subseteq> source(\<Gamma>)" by auto2

definition rel_vsection :: "i \<Rightarrow> i \<Rightarrow> i" where rel_vsection_def [rewrite]:
  "rel_vsection(\<Gamma>,x) = rel_section(rel_inverse(\<Gamma>),x)"
lemma rel_vsectionI [typing2]: "is_relation(\<Gamma>) \<Longrightarrow> rel(\<Gamma>,x,y) \<Longrightarrow> x \<in> rel_vsection(\<Gamma>,y)" by auto2
lemma rel_vsection_iff [rewrite]: "is_relation(\<Gamma>) \<Longrightarrow> x \<in> rel_vsection(\<Gamma>,y) \<longleftrightarrow> rel(\<Gamma>,x,y)" by auto2
setup {* del_prfstep_thm @{thm rel_vsection_def} *}

lemma gr_vimage_singleton [rewrite]:
  "is_relation(\<Gamma>) \<Longrightarrow> rel_vimage(\<Gamma>,{x}) = rel_vsection(\<Gamma>,x)" by auto2

section {* Composition of relations *}  (* Bourbaki II.3.3 *)

(* Since we want associativity in general, output \<emptyset> is either side is not a relation. *)
definition rel_comp :: "i \<Rightarrow> i \<Rightarrow> i"  (infixr "O\<^sub>r" 60) where rel_comp_def [rewrite]:
  "\<Gamma>' O\<^sub>r \<Gamma> = (if is_relation(\<Gamma>) then if is_relation(\<Gamma>') then
                Rel2(source(\<Gamma>), target(\<Gamma>'), \<lambda>x y. \<exists>z. rel(\<Gamma>,x,z) \<and> rel(\<Gamma>',z,y))
              else \<emptyset> else \<emptyset>)"

lemma rel_comp_is_rel [typing]:
  "is_relation(\<Gamma>) \<Longrightarrow> is_relation(\<Gamma>') \<Longrightarrow> \<Gamma>' O\<^sub>r \<Gamma> \<in> rel2_space(source(\<Gamma>), target(\<Gamma>'))" by auto2

lemma rel_comp_eval [rewrite]:
  "is_relation(\<Gamma>) \<Longrightarrow> is_relation(\<Gamma>') \<Longrightarrow> rel(\<Gamma>' O\<^sub>r \<Gamma>,x,y) \<longleftrightarrow> (\<exists>z. rel(\<Gamma>,x,z) \<and> rel(\<Gamma>',z,y))" by auto2

lemma rel_comp_non_rel:
  "\<not>is_relation(\<Gamma>) \<Longrightarrow> \<Gamma>' O\<^sub>r \<Gamma> = \<emptyset> \<and> \<not>is_relation(\<emptyset>)"
  "\<not>is_relation(\<Gamma>') \<Longrightarrow> \<Gamma>' O\<^sub>r \<Gamma> = \<emptyset> \<and> \<not>is_relation(\<emptyset>)" by auto2+
setup {* add_forward_prfstep_cond @{thm rel_comp_non_rel(1)} [with_term "?\<Gamma>' O\<^sub>r ?\<Gamma>"] *}
setup {* add_forward_prfstep_cond @{thm rel_comp_non_rel(2)} [with_term "?\<Gamma>' O\<^sub>r ?\<Gamma>"] *}
setup {* del_prfstep_thm @{thm rel_comp_def} *}

lemma rel_comp_assoc: "(x O\<^sub>r y) O\<^sub>r z = x O\<^sub>r (y O\<^sub>r z)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "is_relation(x)" THEN HAVE "is_relation(y)" THEN HAVE "is_relation(z)") *})

ML {*
val rel_ac = ACUtil.constr_ac_info_au {
  assoc_th = @{thm rel_comp_assoc},
  unitl_th = true_th, unitr_th = true_th}
*}
setup {* ACUtil.add_ac_data ("rel_comp", rel_ac) *}

lemma rel_comp_inverse [rewrite_bidir]:
  "is_relation(\<Gamma>) \<Longrightarrow> is_relation(\<Gamma>') \<Longrightarrow> rel_inverse(\<Gamma>' O\<^sub>r \<Gamma>) = rel_inverse(\<Gamma>) O\<^sub>r rel_inverse(\<Gamma>')" by auto2

lemma rel_comp_image [rewrite]:
  "is_relation(\<Gamma>) \<Longrightarrow> is_relation(\<Gamma>') \<Longrightarrow> rel_image(\<Gamma>' O\<^sub>r \<Gamma>, A) = rel_image(\<Gamma>', rel_image(\<Gamma>,A))" by auto2

lemma rel_comp_inv_image [backward]:
  "is_relation(\<Gamma>) \<Longrightarrow> A \<subseteq> rel_vimage(\<Gamma>,target(\<Gamma>)) \<Longrightarrow> A \<subseteq> rel_image(rel_inverse(\<Gamma>) O\<^sub>r \<Gamma>, A)" by auto2

lemma rel_comp_inv_image2 [backward]:
  "is_relation(\<Gamma>) \<Longrightarrow> rel_image(\<Gamma>,source(\<Gamma>)) \<subseteq> A \<Longrightarrow> rel_image(\<Gamma> O\<^sub>r rel_inverse(\<Gamma>), A) \<subseteq> A" by auto2

(* Identity relation *)
definition id_rel :: "i \<Rightarrow> i" where id_rel_def [rewrite]:
  "id_rel(A) = Rel(A, \<lambda>x y. x = y)"

lemma id_rel_is_rel [typing]: "id_rel(A) \<in> rel_space(A)" by auto2

lemma id_rel_inverse [rewrite]:
  "rel_inverse(id_rel(A)) = id_rel(A)" by auto2

lemma id_rel_comp1 [rewrite]:
  "is_relation(\<Gamma>) \<Longrightarrow> id_rel(target(\<Gamma>)) O\<^sub>r \<Gamma> = \<Gamma>" by auto2

lemma id_rel_comp2 [rewrite]:
  "is_relation(\<Gamma>) \<Longrightarrow> \<Gamma> O\<^sub>r id_rel(source(\<Gamma>)) = \<Gamma>" by auto2

end
