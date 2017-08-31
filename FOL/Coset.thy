theory Coset
imports Group EquivRel
begin
  
section {* Normal subgroups *}

definition is_normal_subgroup_set :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "is_normal_subgroup_set(G,H) \<longleftrightarrow> (
    is_subgroup_set(G,H) \<and> (\<forall>a\<in>.G. \<forall>h\<in>H. a *\<^sub>G h *\<^sub>G inv(G,a) \<in> H))"
  
lemma is_normal_subgroup_setD1 [forward]:
  "is_normal_subgroup_set(G,H) \<Longrightarrow> is_subgroup_set(G,H)" by auto2
    
lemma is_normal_subgroup_setD2 [typing]:
  "a \<in>. G \<Longrightarrow> is_normal_subgroup_set(G,H) \<Longrightarrow> h \<in> H \<Longrightarrow> a *\<^sub>G h *\<^sub>G inv(G,a) \<in> H" by auto2    
setup {* del_prfstep_thm_eqforward @{thm is_normal_subgroup_set_def} *}

lemma is_normal_subgroup_setD3 [typing]:
  "a \<in>. G \<Longrightarrow> is_normal_subgroup_set(G,H) \<Longrightarrow> h \<in> H \<Longrightarrow> inv(G,a) *\<^sub>G h *\<^sub>G a \<in> H"
@proof @have "a = inv(G, inv(G,a))" @qed

section {* Cosets as equivalence classes *}
  
definition rcoset_equiv :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "rcoset_equiv(G,H) = Equiv(carrier(G), \<lambda>x y. \<exists>h\<in>H. h *\<^sub>G x = y)"
setup {* register_wellform_data ("rcoset_equiv(G,H)", ["is_subgroup_set(G,H)"]) *}

lemma rcoset_equiv_is_rawequiv [typing]:
  "rcoset_equiv(G,H) \<in> rawequiv_space(carrier(G))" by auto2

lemma rcoset_equiv_eval1 [backward1]:
  "R = rcoset_equiv(G,H) \<Longrightarrow> is_group(G) \<Longrightarrow> is_subgroup_set(G,H) \<Longrightarrow> x \<in>. G \<Longrightarrow>
   h \<in> H \<Longrightarrow> h *\<^sub>G x = y \<Longrightarrow> x \<sim>\<^sub>R y" by auto2

lemma rcoset_equiv_eval2 [resolve]:
  "R = rcoset_equiv(G,H) \<Longrightarrow> x \<sim>\<^sub>R y \<Longrightarrow> \<exists>h\<in>H. h *\<^sub>G x = y" by auto2
setup {* del_prfstep_thm @{thm rcoset_equiv_def} *}

lemma rcoset_equiv_is_equiv [typing]:
  "is_group(G) \<Longrightarrow> is_subgroup_set(G,H) \<Longrightarrow> rcoset_equiv(G,H) \<in> equiv_space(carrier(G))"
@proof
  @let "S = carrier(G)" @then
  @let "R = rcoset_equiv(G,H)" @then
  @have "\<forall>x\<in>.R. x \<sim>\<^sub>R x" @with @have "x = \<one>\<^sub>G *\<^sub>G x" @end
  @have "\<forall>x y. x \<sim>\<^sub>R y \<longrightarrow> y \<sim>\<^sub>R x" @with
    @obtain "h\<in>H" where "h *\<^sub>G x = y" @then
    @have "inv(G,h) *\<^sub>G y = x" @with @have "h *\<^sub>G (inv(G,h) *\<^sub>G y) = h *\<^sub>G inv(G,h) *\<^sub>G y" @end @end
  @have "\<forall>x y z. x \<sim>\<^sub>R y \<longrightarrow> y \<sim>\<^sub>R z \<longrightarrow> x \<sim>\<^sub>R z" @with
    @obtain "h1\<in>H" where "h1 *\<^sub>G x = y" @then
    @obtain "h2\<in>H" where "h2 *\<^sub>G y = z" @then
    @have "(h2 *\<^sub>G h1) *\<^sub>G x = z" @with @have "(h2 *\<^sub>G h1) *\<^sub>G x = h2 *\<^sub>G (h1 *\<^sub>G x)" @end @end
@qed

lemma rcoset_mult_compat2 [backward]:
  "R = rcoset_equiv(G,H) \<Longrightarrow> x \<in>. G \<Longrightarrow>
   is_normal_subgroup_set(G,H) \<Longrightarrow> y \<sim>\<^sub>R z \<Longrightarrow> x *\<^sub>G y \<sim>\<^sub>R x *\<^sub>G z"
@proof
  @obtain "h\<in>H" where "h *\<^sub>G y = z" @then
  @have "(x *\<^sub>G h *\<^sub>G inv(G,x)) *\<^sub>G (x *\<^sub>G y) = x *\<^sub>G (h *\<^sub>G (inv(G,x) *\<^sub>G x) *\<^sub>G y)"
@qed

lemma rcoset_mult_compat1 [backward]:
  "R = rcoset_equiv(G,H) \<Longrightarrow> x \<in>. G \<Longrightarrow>
   is_subgroup_set(G,H) \<Longrightarrow> y \<sim>\<^sub>R z \<Longrightarrow> y *\<^sub>G x \<sim>\<^sub>R z *\<^sub>G x"
@proof
  @obtain "h\<in>H" where "h *\<^sub>G y = z" @then
  @have "h *\<^sub>G (y *\<^sub>G x) = (h *\<^sub>G y) *\<^sub>G x"
@qed

definition rcoset_quot :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "rcoset_quot(G,H) = carrier(rcoset_equiv(G,H)) // rcoset_equiv(G,H)"
setup {* register_wellform_data ("rcoset_quot(G,H)", ["is_subgroup_set(G,H)"]) *}

definition rcoset_mult :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "rcoset_mult(G,H,x,y) =
     equiv_class(rcoset_equiv(G,H), rep(rcoset_equiv(G,H),x) *\<^sub>G rep(rcoset_equiv(G,H),y))"
setup {* register_wellform_data ("rcoset_mult(G,H,x,y)", ["x \<in> rcoset_quot(G,H)", "y \<in> rcoset_quot(G,H)"]) *}

lemma rcoset_mult_type [typing]:
  "is_subgroup_set(G,H) \<Longrightarrow> S = rcoset_quot(G,H) \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> rcoset_mult(G,H,x,y) \<in> S"
  by auto2

lemma rcoset_mult_eval [rewrite]:
  "R = rcoset_equiv(G,H) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> is_normal_subgroup_set(G,H) \<Longrightarrow>
   rcoset_mult(G,H,equiv_class(R,x),equiv_class(R,y)) = equiv_class(R,x *\<^sub>G y)"
@proof @have "compat_meta_bin(R, \<lambda>x y. x *\<^sub>G y)" @qed

lemma rcoset_mult_assoc [rewrite]:
  "S = rcoset_quot(G,H) \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> z \<in> S \<Longrightarrow>
   is_normal_subgroup_set(G,H) \<Longrightarrow>
   rcoset_mult(G,H,rcoset_mult(G,H,x,y),z) = rcoset_mult(G,H,x,rcoset_mult(G,H,y,z))" by auto2
  
definition rcoset_id :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "rcoset_id(G,H) = equiv_class(rcoset_equiv(G,H), \<one>\<^sub>G)"

lemma rcoset_id_type [typing]:
  "is_normal_subgroup_set(G,H) \<Longrightarrow> rcoset_id(G,H) \<in> rcoset_quot(G,H)" by auto2

lemma rcoset_mult_id1 [rewrite]:
  "x \<in> rcoset_quot(G,H) \<Longrightarrow> is_normal_subgroup_set(G,H) \<Longrightarrow>
   rcoset_mult(G,H,rcoset_id(G,H),x) = x" by auto2

lemma rcoset_mult_id2 [rewrite]:
  "x \<in> rcoset_quot(G,H) \<Longrightarrow> is_normal_subgroup_set(G,H) \<Longrightarrow>
   rcoset_mult(G,H,x,rcoset_id(G,H)) = x" by auto2

definition rcoset_inv :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "rcoset_inv(G,H,x) = equiv_class(rcoset_equiv(G,H), inv(G,rep(rcoset_equiv(G,H),x)))"

lemma rcoset_inv_type [typing]:
  "is_normal_subgroup_set(G,H) \<Longrightarrow> x \<in> rcoset_quot(G,H) \<Longrightarrow> rcoset_inv(G,H,x) \<in> rcoset_quot(G,H)" by auto2

lemma rcoset_inv_prop [rewrite]:
  "x \<in> rcoset_quot(G,H) \<Longrightarrow> is_normal_subgroup_set(G,H) \<Longrightarrow>
   rcoset_mult(G,H,rcoset_inv(G,H,x),x) = rcoset_id(G,H)" by auto2
setup {* del_prfstep_thm @{thm rcoset_inv_def} *}

section {* Construction of the quotient group *}
  
definition quotient_group :: "i \<Rightarrow> i \<Rightarrow> i" (infix "'/'/\<^sub>G" 90) where [rewrite]:
  "G //\<^sub>G H = Group(rcoset_quot(G,H), rcoset_id(G,H), \<lambda>x y. rcoset_mult(G,H,x,y))"
setup {* register_wellform_data ("G //\<^sub>G H", ["is_normal_subgroup_set(G,H)"]) *}

lemma quotient_group_is_group_raw:
  "is_normal_subgroup_set(G,H) \<Longrightarrow> group_form(G //\<^sub>G H)" by auto2
setup {* add_forward_prfstep_cond @{thm quotient_group_is_group_raw} [with_term "?G //\<^sub>G ?H"] *}

lemma quotient_group_sel1:
  "carrier(G //\<^sub>G H) = rcoset_quot(G,H)"
  "one(G //\<^sub>G H) = equiv_class(rcoset_equiv(G,H), \<one>\<^sub>G)" by auto2+
setup {* fold (fn th => add_forward_prfstep_cond th [with_term "?G //\<^sub>G ?H"]) @{thms quotient_group_sel1} *}
  
lemma quotient_group_sel2 [rewrite]:
  "K = G //\<^sub>G H \<Longrightarrow> is_normal_subgroup_set(G,H) \<Longrightarrow> x \<in>. K \<Longrightarrow> y \<in>. K \<Longrightarrow> R = rcoset_equiv(G,H) \<Longrightarrow>
   x *\<^sub>K y = equiv_class(R,rep(R,x) *\<^sub>G rep(R,y))" by auto2

lemma quotient_group_is_group:
  "is_normal_subgroup_set(G,H) \<Longrightarrow> is_group(G //\<^sub>G H)"
@proof
  @let "Q = G //\<^sub>G H" @then
  @have "is_monoid(Q)" @then
  @have "\<forall>x\<in>.Q. rcoset_inv(G,H,x) *\<^sub>Q x = \<one>\<^sub>Q"
@qed
setup {* add_forward_prfstep_cond @{thm quotient_group_is_group} [with_term "?G //\<^sub>G ?H"] *}

section {* Canonical surjection *}

definition qsurj_group :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "qsurj_group(G,H) = Mor(G, G //\<^sub>G H, \<lambda>x. equiv_class(rcoset_equiv(G,H), x))"
setup {* register_wellform_data ("qsurj_group(G,H)", ["is_normal_subgroup_set(G,H)"]) *}

lemma qsurj_group_is_morphism [typing]:
  "is_normal_subgroup_set(G,H) \<Longrightarrow> qsurj_group(G,H) \<in> G \<rightharpoonup>\<^sub>G G //\<^sub>G H" by auto2

lemma qsurj_group_is_surjective:
  "is_normal_subgroup_set(G,H) \<Longrightarrow> surjective(qsurj_group(G,H))"
@proof
  @let "R = rcoset_equiv(G,H)" @then
  @have (@rule) "\<forall>x \<in>. G //\<^sub>G H. qsurj_group(G,H)`rep(R,x) = x"
@qed
setup {* add_forward_prfstep_cond @{thm qsurj_group_is_surjective} [with_term "qsurj_group(?G,?H)"] *}
  
lemma qsurj_group_eval [rewrite]:
  "is_normal_subgroup_set(G,H) \<Longrightarrow> x \<in> source(qsurj_group(G,H)) \<Longrightarrow>
   qsurj_group(G,H)`x = equiv_class(rcoset_equiv(G,H),x)" by auto2
setup {* del_prfstep_thm @{thm qsurj_group_def} *}
setup {* del_prfstep_thm @{thm quotient_group_def} *}
  
lemma qsurj_group_eq_iff1 [rewrite]:
  "is_normal_subgroup_set(G,H) \<Longrightarrow> R = rcoset_equiv(G,H) \<Longrightarrow> x \<sim>\<^sub>R y \<Longrightarrow>
   qsurj_group(G,H)`x = qsurj_group(G,H)`y" by auto2

lemma qsurj_group_eq_iff2 [forward]:
  "is_normal_subgroup_set(G,H) \<Longrightarrow> R = rcoset_equiv(G,H) \<Longrightarrow>
   p = qsurj_group(G,H) \<Longrightarrow>
   x \<in> source(p) \<Longrightarrow> y \<in> source(p) \<Longrightarrow> p`x = p`y \<Longrightarrow> x \<sim>\<^sub>R y" by auto2

section {* Kernel is a normal subgroup *}

definition kernel :: "i \<Rightarrow> i" where [rewrite]:
  "kernel(f) = {x\<in>source(f). f`x = one(target_str(f))}"

lemma kernelD [forward]: "H = target_str(f) \<Longrightarrow> x \<in> kernel(f) \<Longrightarrow> x \<in> source(f) \<and> f`x = \<one>\<^sub>H" by auto2
lemma kernelI [typing2, backward]: "H = target_str(f) \<Longrightarrow> x \<in> source(f) \<Longrightarrow> f`x = \<one>\<^sub>H \<Longrightarrow> x \<in> kernel(f)" by auto2
setup {* del_prfstep_thm @{thm kernel_def} *}
  
lemma kernel_is_normal_subgroup:
  "is_group_hom(f) \<Longrightarrow> is_normal_subgroup_set(source_str(f), kernel(f))" by auto2
setup {* add_forward_prfstep_cond @{thm kernel_is_normal_subgroup} [with_term "kernel(?f)"] *}
  
section {* First isomorphism theorem *}
      
lemma exists_induced_group_mor [backward]:
  "is_normal_subgroup_set(G,K) \<Longrightarrow> f \<in> G \<rightharpoonup>\<^sub>G H \<Longrightarrow> K \<subseteq> kernel(f) \<Longrightarrow>
   \<exists>!h. h\<in>(G //\<^sub>G K)\<rightharpoonup>H \<and> f = h \<circ>\<^sub>m qsurj_group(G,K)"
@proof
  @let "p = qsurj_group(G,K)" @then
  @have "\<forall>x\<in>.G. \<forall>y\<in>.G. p`x = p`y \<longrightarrow> f`x = f`y" @with
    @obtain "k \<in> K" where "k *\<^sub>G x = y" @end
@qed

(* Given f \<in> G \<rightharpoonup>\<^sub>G H and a normal subgroup K of G, obtain f' \<in> G//K \<rightharpoonup>\<^sub>G H
   (assuming various requirements hold. *)
definition induced_group_mor :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "induced_group_mor(f,K) =
    (THE h. h \<in> (source_str(f) //\<^sub>G K) \<rightharpoonup> target_str(f) \<and> f = h \<circ>\<^sub>m qsurj_group(source_str(f),K))"
setup {* register_wellform_data ("induced_group_mor(f,K)",
  ["is_normal_subgroup_set(source_str(f),K)", "K \<subseteq> kernel(f)"]) *}
setup {* add_prfstep_check_req ("induced_group_mor(f,K)", "K \<subseteq> kernel(f)") *}

lemma induced_group_mor_prop:
  "is_normal_subgroup_set(G,K) \<Longrightarrow> mor_form(f) \<Longrightarrow> is_group_hom(f) \<Longrightarrow>
   G = source_str(f) \<Longrightarrow> H = target_str(f) \<Longrightarrow> K \<subseteq> kernel(f) \<Longrightarrow>
   induced_group_mor(f,K) \<in> G //\<^sub>G K \<rightharpoonup> H \<and> f = induced_group_mor(f,K) \<circ>\<^sub>m qsurj_group(G,K)" by auto2
setup {* add_forward_prfstep_cond @{thm induced_group_mor_prop} [with_term "induced_group_mor(?f,?K)"] *}

lemma induced_group_mor_eval [rewrite]:
  "mor_form(f) \<Longrightarrow> is_group_hom(f) \<Longrightarrow> G = source_str(f) \<Longrightarrow> is_normal_subgroup_set(G,K) \<Longrightarrow>
   K \<subseteq> kernel(f) \<Longrightarrow> R = rcoset_equiv(G,K) \<Longrightarrow>
   x \<in>. R \<Longrightarrow> induced_group_mor(f,K) ` equiv_class(R,x) = f ` x" by auto2
setup {* del_prfstep_thm @{thm induced_group_mor_def} *}

lemma induced_group_mor_is_hom:
  "mor_form(f) \<Longrightarrow> is_group_hom(f) \<Longrightarrow> is_normal_subgroup_set(source_str(f),K) \<Longrightarrow> K \<subseteq> kernel(f) \<Longrightarrow>
   is_group_hom(induced_group_mor(f,K))" by auto2
setup {* add_forward_prfstep_cond @{thm induced_group_mor_is_hom} [with_term "induced_group_mor(?f,?K)"] *}

(* Canonical decomposition *)
lemma injective_induced_group_mor:
  "mor_form(f) \<Longrightarrow> is_group_hom(f) \<Longrightarrow> injective(induced_group_mor(f,kernel(f)))"
@proof
  @let "h = induced_group_mor(f,kernel(f))" @then
  @let "G = source_str(f)" @then
  @let "p = qsurj_group(G,kernel(f))" @then
  @have "\<forall>x\<in>source(h). \<forall>y\<in>source(h). h`x = h`y \<longrightarrow> x = y" @with
    @obtain "x'\<in>source(p)" where "p`x' = x" @then
    @obtain "y'\<in>source(p)" where "p`y' = y" @then
    @have "f`x' = f`y'" @then
    @have "y' *\<^sub>G inv(G,x') \<in> kernel(f)" @then
    @have "(y' *\<^sub>G inv(G,x')) *\<^sub>G x' = y'"
  @end
@qed
setup {* add_forward_prfstep_cond @{thm injective_induced_group_mor}
  [with_term "induced_group_mor(?f,kernel(?f))"] *}

lemma induced_group_mor_image [rewrite]:
  "mor_form(f) \<Longrightarrow> is_group_hom(f) \<Longrightarrow> image(induced_group_mor(f,kernel(f))) = image(f)" by auto2

lemma first_isomorphism_theorem [typing]:
  "mor_form(f) \<Longrightarrow> is_group_hom(f) \<Longrightarrow> G = source_str(f) \<Longrightarrow> K = kernel(f) \<Longrightarrow>
   group_mor_restrict_image(induced_group_mor(f,K)) \<in> G //\<^sub>G K \<cong>\<^sub>G image_subgroup(f)" by auto2
    
lemma first_isomorphism_theorem_surj [typing]:
  "mor_form(f) \<Longrightarrow> is_group_hom(f) \<Longrightarrow> surjective(f) \<Longrightarrow> G = source_str(f) \<Longrightarrow> K = kernel(f) \<Longrightarrow>
   induced_group_mor(f,K) \<in> G //\<^sub>G K \<cong>\<^sub>G target_str(f)" by auto2

end
