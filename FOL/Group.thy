theory Group
imports AlgStructure Morphism
begin

section {* Monoids *}
  
definition is_monoid :: "i \<Rightarrow> o" where [rewrite]:
  "is_monoid(G) \<longleftrightarrow> is_mult_id(G) \<and> is_times_assoc(G)"
setup {* add_property_const @{term is_monoid} *}

lemma is_monoidD [forward]:
  "is_monoid(G) \<Longrightarrow> is_mult_id(G)"
  "is_monoid(G) \<Longrightarrow> is_times_assoc(G)" by auto2+
setup {* del_prfstep_thm_eqforward @{thm is_monoid_def} *}
  
lemma is_monoid_group_prop [forward]:
  "is_group_raw(H) \<Longrightarrow> is_monoid(G) \<Longrightarrow> eq_str_group(G,H) \<Longrightarrow> is_monoid(H)" by auto2

ML_file "alg_monoid.ML"
  
section {* Units and multiplicative inverse *}

definition units :: "i \<Rightarrow> i" where [rewrite]:
  "units(G) = {x \<in>. G. (\<exists>y\<in>.G. y *\<^sub>G x = \<one>\<^sub>G \<and> x *\<^sub>G y = \<one>\<^sub>G)}"

lemma is_unitD1 [forward]: "x \<in> units(G) \<Longrightarrow> x \<in>. G" by auto2
lemma is_unitD2 [backward]: "x \<in> units(G) \<Longrightarrow> \<exists>y\<in>.G. y *\<^sub>G x = \<one>\<^sub>G \<and> x *\<^sub>G y = \<one>\<^sub>G" by auto2
lemma is_unitI [backward1, backward2]:
  "x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> y *\<^sub>G x = \<one>\<^sub>G \<Longrightarrow> x *\<^sub>G y = \<one>\<^sub>G \<Longrightarrow> x \<in> units(G)" by auto2
lemma unit_exists_invl [backward]: "x \<in> units(G) \<Longrightarrow> \<exists>y\<in>.G. y *\<^sub>G x = \<one>\<^sub>G" by auto2
lemma unit_exists_invr [backward]: "x \<in> units(G) \<Longrightarrow> \<exists>y\<in>.G. x *\<^sub>G y = \<one>\<^sub>G" by auto2
lemma one_is_unit [resolve]: "is_monoid(G) \<Longrightarrow> \<one>\<^sub>G \<in> units(G)" by auto2
lemma units_group_fun [rewrite]:
  "is_group_raw(G) \<Longrightarrow> is_group_raw(H) \<Longrightarrow> eq_str_group(G,H) \<Longrightarrow> units(G) = units(H)" by auto2
setup {* del_prfstep_thm @{thm units_def} *}

definition inv :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "inv(G,x) = (THE y. y \<in>. G \<and> y *\<^sub>G x = \<one>\<^sub>G \<and> x *\<^sub>G y = \<one>\<^sub>G)"
setup {* register_wellform_data ("inv(G,x)", ["x \<in> units(G)"]) *}

lemma inv_unique [forward]:
  "is_monoid(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> y' \<in>. G \<Longrightarrow>
   y *\<^sub>G x = \<one>\<^sub>G \<Longrightarrow> x *\<^sub>G y' = \<one>\<^sub>G \<Longrightarrow> y = y'"
@proof @have "y *\<^sub>G x *\<^sub>G y' = y *\<^sub>G (x *\<^sub>G y')" @qed
    
lemma inv_equality [backward1, backward2]:
  "is_monoid(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> y *\<^sub>G x = \<one>\<^sub>G \<Longrightarrow> x *\<^sub>G y = \<one>\<^sub>G \<Longrightarrow> inv(G,x) = y"
  "is_monoid(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> y *\<^sub>G x = \<one>\<^sub>G \<Longrightarrow> x *\<^sub>G y = \<one>\<^sub>G \<Longrightarrow> y = inv(G,x)" by auto2+

lemma inv_is_unit [typing]:
  "is_monoid(G) \<Longrightarrow> x \<in> units(G) \<Longrightarrow> inv(G,x) \<in> units(G)" by auto2

lemma invD [forward]:
  "is_monoid(G) \<Longrightarrow> inv(G,\<one>\<^sub>G) = \<one>\<^sub>G"
  "is_monoid(G) \<Longrightarrow> x \<in> units(G) \<Longrightarrow> inv(G,x) *\<^sub>G x = \<one>\<^sub>G"
  "is_monoid(G) \<Longrightarrow> x \<in> units(G) \<Longrightarrow> x *\<^sub>G inv(G,x) = \<one>\<^sub>G" by auto2+
setup {* del_prfstep_thm @{thm inv_def} *}
  
lemma inv_group_fun [rewrite]:
  "is_group_raw(H) \<Longrightarrow> is_monoid(G) \<Longrightarrow> x \<in> units(G) \<Longrightarrow> eq_str_group(G,H) \<Longrightarrow>
   inv(G,x) = inv(H,x)" by auto2

lemma unit_l_cancel [forward]:
  "is_monoid(G) \<Longrightarrow> y \<in>. G \<Longrightarrow> z \<in>. G \<Longrightarrow> x *\<^sub>G y = x *\<^sub>G z \<Longrightarrow> x \<in> units(G) \<Longrightarrow> y = z"
@proof
  @have "inv(G,x) *\<^sub>G x *\<^sub>G y = inv(G,x) *\<^sub>G (x *\<^sub>G y)"
  @have "inv(G,x) *\<^sub>G x *\<^sub>G z = inv(G,x) *\<^sub>G (x *\<^sub>G z)"
@qed

lemma unit_r_cancel [forward]:
  "is_monoid(G) \<Longrightarrow> y \<in>. G \<Longrightarrow> z \<in>. G \<Longrightarrow> y *\<^sub>G x = z *\<^sub>G x \<Longrightarrow> x \<in> units(G) \<Longrightarrow> y = z"
@proof
  @have "y *\<^sub>G (x *\<^sub>G inv(G,x)) = y *\<^sub>G x *\<^sub>G inv(G,x)"
  @have "z *\<^sub>G (x *\<^sub>G inv(G,x)) = z *\<^sub>G x *\<^sub>G inv(G,x)"
@qed

lemma unit_inv_inv [rewrite]:
  "is_monoid(G) \<Longrightarrow> x \<in> units(G) \<Longrightarrow> inv(G, inv(G,x)) = x"
@proof @have "inv(G,x) *\<^sub>G x = \<one>\<^sub>G" @qed

lemma unit_inv_comm:
  "is_monoid(G) \<Longrightarrow> y \<in>. G \<Longrightarrow> x \<in> units(G) \<Longrightarrow> x *\<^sub>G y = \<one>\<^sub>G \<Longrightarrow> y *\<^sub>G x = \<one>\<^sub>G" by auto2
setup {* fold del_prfstep_thm @{thms invD} *}
setup {* fold add_rewrite_rule @{thms invD} *}

section {* Definition of groups *}

definition is_group :: "i \<Rightarrow> o" where [rewrite]:
  "is_group(G) \<longleftrightarrow> is_monoid(G) \<and> carrier(G) = units(G)"
setup {* add_property_const @{term is_group} *}

lemma is_groupD [forward]:
  "is_group(G) \<Longrightarrow> is_monoid(G)"
  "is_group(G) \<Longrightarrow> carrier(G) = units(G)" by auto2+

lemma is_groupI [backward1]:
  "is_monoid(G) \<Longrightarrow> unary_fun(carrier(G),f) \<Longrightarrow> \<forall>x\<in>.G. f(x) *\<^sub>G x = \<one>\<^sub>G \<Longrightarrow> is_group(G)" by auto2
setup {* del_prfstep_thm @{thm is_group_def} *}

lemma inv_equality_group1 [backward]:
  "is_group(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> y *\<^sub>G x = \<one>\<^sub>G \<Longrightarrow> inv(G,x) = y"
@proof @have "inv(G,x) *\<^sub>G x = \<one>\<^sub>G" @qed

lemma inv_equality_group2 [backward]:
  "is_group(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> y *\<^sub>G x = \<one>\<^sub>G \<Longrightarrow> y = inv(G,x)"
@proof @have "inv(G,x) *\<^sub>G x = \<one>\<^sub>G" @qed

lemma inv_distrib_group:
  "is_group(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow>
   inv(G, x *\<^sub>G y) = inv(G,y) *\<^sub>G inv(G,x) \<and>
   x \<in> units(G) \<and> y \<in> units(G) \<and> inv(G,y) \<in>. G \<and> inv(G,x) \<in>. G"
@proof @have "inv(G,y) *\<^sub>G inv(G,x) *\<^sub>G (x *\<^sub>G y) = inv(G,y) *\<^sub>G (inv(G,x) *\<^sub>G x) *\<^sub>G y" @qed

ML_file "alg_group.ML"

lemma inv_distrib_test:
  "is_group(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> z \<in>. G \<Longrightarrow>
   inv(G, x *\<^sub>G y *\<^sub>G z) = inv(G,z) *\<^sub>G inv(G,y) *\<^sub>G inv(G,x)" by auto2

lemma move_inv_r [rewrite]:
  "is_group(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> z \<in>. G \<Longrightarrow> x *\<^sub>G inv(G,y) = z \<Longrightarrow> z *\<^sub>G y = x"
@proof @have "z *\<^sub>G y *\<^sub>G inv(G,y) = z" @qed

lemma move_inv_l [rewrite]:
  "is_group(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> z \<in>. G \<Longrightarrow> inv(G,x) *\<^sub>G y = z \<Longrightarrow> x *\<^sub>G z = y"
@proof @have "z = inv(G,x) *\<^sub>G (x *\<^sub>G z)" @qed

section {* Subgroups *}

definition subset_mult_closed :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "subset_mult_closed(G,H) \<longleftrightarrow> (\<forall>x\<in>H. \<forall>y\<in>H. x *\<^sub>G y \<in> H)"

lemma subset_mult_closedD [typing]:
  "subset_mult_closed(G,H) \<Longrightarrow> x \<in> H \<Longrightarrow> y \<in> H \<Longrightarrow> x *\<^sub>G y \<in> H" by auto2
setup {* del_prfstep_thm_eqforward @{thm subset_mult_closed_def} *}

definition subset_inv_closed :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "subset_inv_closed(G,H) \<longleftrightarrow> (\<forall>x\<in>H. inv(G,x) \<in> H)"

lemma subset_inv_closedD [typing]:
  "subset_inv_closed(G,H) \<Longrightarrow> x \<in> H \<Longrightarrow> inv(G,x) \<in> H" by auto2
setup {* del_prfstep_thm_eqforward @{thm subset_inv_closed_def} *}

definition is_subgroup_set :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "is_subgroup_set(G,H) \<longleftrightarrow>
    (is_group(G) \<and> H \<subseteq> carrier(G) \<and> \<one>\<^sub>G \<in> H \<and> subset_mult_closed(G,H) \<and> subset_inv_closed(G,H))"

definition subgroup :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "subgroup(G,H) = Group(H, \<one>\<^sub>G, \<lambda>x y. x *\<^sub>G y)"
setup {* register_wellform_data ("subgroup(G,H)", ["is_subgroup_set(G,H)"]) *}

lemma subgroup_is_group_raw:
  "is_subgroup_set(G,H) \<Longrightarrow> group_form(subgroup(G,H))" by auto2
setup {* add_forward_prfstep_cond @{thm subgroup_is_group_raw} [with_term "subgroup(?G,?H)"] *}

lemma subgroup_sel1:
  "carrier(subgroup(G,H)) = H"
  "one(subgroup(G,H)) = \<one>\<^sub>G" by auto2+
setup {* fold (fn th => add_forward_prfstep_cond th [with_term "subgroup(?G,?H)"]) @{thms subgroup_sel1} *}
  
lemma subgroup_sel2 [rewrite]:
  "\<H> = subgroup(G,H) \<Longrightarrow> x \<in>. \<H> \<Longrightarrow> y \<in>. \<H> \<Longrightarrow> is_subgroup_set(G,H) \<Longrightarrow> x *\<^sub>\<H> y = x *\<^sub>G y" by auto2+
setup {* del_prfstep_thm @{thm subgroup_def} *}

lemma subgroup_is_group:
  "is_subgroup_set(G,H) \<Longrightarrow> \<H> = subgroup(G,H) \<Longrightarrow> is_group(\<H>)"
@proof
  @have "is_monoid(\<H>)" @with
    @have "is_times_assoc(\<H>)" @with
      @have "\<forall>x\<in>H. \<forall>y\<in>H. \<forall>z\<in>H. (x *\<^sub>\<H> y) *\<^sub>\<H> z = x *\<^sub>\<H> (y *\<^sub>\<H> z)" @with
        @have "(x *\<^sub>G y) *\<^sub>G z = x *\<^sub>G (y *\<^sub>G z)" @end @end @end
  @have "\<forall>x\<in>H. inv(G,x) *\<^sub>\<H> x = \<one>\<^sub>\<H>"
@qed
setup {* add_forward_prfstep_cond @{thm subgroup_is_group} [with_term "subgroup(?G,?H)"] *}

lemma subgroup_inv [rewrite]:
  "is_subgroup_set(G,H) \<Longrightarrow> \<H> = subgroup(G,H) \<Longrightarrow> x \<in> units(\<H>) \<Longrightarrow>
   inv(\<H>,x) = inv(G,x)" by auto2

lemma subgroup_non_empty [resolve]: "\<not>is_subgroup_set(G,\<emptyset>)"
@proof @contradiction @have "\<one>\<^sub>G \<in> \<emptyset>" @qed

section {* Direct products *}
  
definition group_prod :: "i \<Rightarrow> i \<Rightarrow> i"  (infixr "\<times>\<^sub>G" 80) where [rewrite]:
  "G \<times>\<^sub>G H = Group(carrier(G)\<times>carrier(H), \<langle>\<one>\<^sub>G,\<one>\<^sub>H\<rangle>, \<lambda>x y. \<langle>fst(x) *\<^sub>G fst(y), snd(x) *\<^sub>H snd(y)\<rangle>)"

lemma group_prod_is_group_raw [forward]:
  "is_group_raw(G) \<Longrightarrow> is_group_raw(H) \<Longrightarrow> group_form(G \<times>\<^sub>G H)" by auto2

lemma group_prod_sel1:
  "carrier(G \<times>\<^sub>G H) = carrier(G) \<times> carrier(H)"
  "one(G \<times>\<^sub>G H) = \<langle>\<one>\<^sub>G,\<one>\<^sub>H\<rangle>" by auto2+
setup {* fold (fn th => add_forward_prfstep_cond th [with_term "?G \<times>\<^sub>G ?H"]) @{thms group_prod_sel1} *}

lemma group_prod_sel2 [rewrite]:
  "K = G \<times>\<^sub>G H \<Longrightarrow> is_group_raw(G) \<Longrightarrow> is_group_raw(H) \<Longrightarrow> x \<in>. K \<Longrightarrow> y \<in>. K \<Longrightarrow>
   x *\<^sub>K y = \<langle>fst(x) *\<^sub>G fst(y), snd(x) *\<^sub>H snd(y)\<rangle>" by auto2
setup {* del_prfstep_thm @{thm group_prod_def} *}

lemma group_prod_is_monoid [forward]:
  "is_monoid(G) \<Longrightarrow> is_monoid(H) \<Longrightarrow> is_monoid(G \<times>\<^sub>G H)"
@proof
  @let "K = G \<times>\<^sub>G H"
  @have "is_times_assoc(K)" @with
    @have "\<forall>x\<in>.K. \<forall>y\<in>.K. \<forall>z\<in>.K. (x *\<^sub>K y) *\<^sub>K z = x *\<^sub>K (y *\<^sub>K z)" @with
      @have "(fst(x) *\<^sub>G fst(y)) *\<^sub>G fst(z) = fst(x) *\<^sub>G (fst(y) *\<^sub>G fst(z))"
      @have "(snd(x) *\<^sub>H snd(y)) *\<^sub>H snd(z) = snd(x) *\<^sub>H (snd(y) *\<^sub>H snd(z))"
    @end
  @end
@qed

lemma group_prod_is_group [forward]:
  "is_group(G) \<Longrightarrow> is_group(H) \<Longrightarrow> is_group(G \<times>\<^sub>G H)"
@proof
  @let "K = G \<times>\<^sub>G H"
  @have "\<forall>x\<in>.K. \<langle>inv(G,fst(x)), inv(H,snd(x))\<rangle> *\<^sub>K x = \<one>\<^sub>K"
@qed

lemma group_prod_inv [rewrite]:
  "is_group(G) \<Longrightarrow> is_group(H) \<Longrightarrow> K = G \<times>\<^sub>G H \<Longrightarrow> \<langle>x,y\<rangle> \<in> units(K) \<Longrightarrow>
   inv(K, \<langle>x,y\<rangle>) = \<langle>inv(G,x), inv(H,y)\<rangle>" by auto2

section {* Homomorphisms and Isomorphisms *}

definition is_group_hom :: "i \<Rightarrow> o" where [rewrite]:
  "is_group_hom(f) \<longleftrightarrow> (let S = source_str(f) in let T = target_str(f) in
    is_morphism(f) \<and> is_group(S) \<and> is_group(T) \<and> (\<forall>x\<in>.S. \<forall>y\<in>.S. f`(x *\<^sub>S y) = f`x *\<^sub>T f`y))"
setup {* add_property_const @{term is_group_hom} *}
  
lemma is_group_homD1 [forward]:
  "is_group_hom(f) \<Longrightarrow> is_morphism(f) \<and> is_group(source_str(f)) \<and> is_group(target_str(f))" by auto2

lemma is_group_homD2 [rewrite]:
  "is_group_hom(f) \<Longrightarrow> G = source_str(f) \<Longrightarrow> H = target_str(f) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow>
   f ` (x *\<^sub>G y) = f`x *\<^sub>H f`y" by auto2
setup {* del_prfstep_thm_eqforward @{thm is_group_hom_def} *}

definition group_hom_space :: "i \<Rightarrow> i \<Rightarrow> i" (infix "\<rightharpoonup>\<^sub>G" 60) where [rewrite]:
  "G \<rightharpoonup>\<^sub>G H = {f \<in> G \<rightharpoonup> H. is_group_hom(f)}"

lemma group_hom_spaceD [forward]:
  "f \<in> G \<rightharpoonup>\<^sub>G H \<Longrightarrow> f \<in> G \<rightharpoonup> H \<and> is_group_hom(f)" by auto2

lemma group_hom_spaceI [typing, backward]:
  "mor_form(f) \<Longrightarrow> is_group_hom(f) \<Longrightarrow> f \<in> source_str(f) \<rightharpoonup>\<^sub>G target_str(f)" by auto2
setup {* del_prfstep_thm @{thm group_hom_space_def} *}

lemma group_hom_compose:
  "is_group_hom(f) \<Longrightarrow> is_group_hom(g) \<Longrightarrow> target_str(f) = source_str(g) \<Longrightarrow>
   is_group_hom(g \<circ>\<^sub>m f)" by auto2
setup {* add_forward_prfstep_cond @{thm group_hom_compose} [with_term "?g \<circ>\<^sub>m ?f"] *}

lemma group_hom_one [rewrite]:
  "is_group_hom(f) \<Longrightarrow> G = source_str(f) \<Longrightarrow> H = target_str(f) \<Longrightarrow> f ` \<one>\<^sub>G = \<one>\<^sub>H"
@proof @have "f ` (\<one>\<^sub>G *\<^sub>G \<one>\<^sub>G) *\<^sub>H \<one>\<^sub>H = f ` \<one>\<^sub>G *\<^sub>H f ` \<one>\<^sub>G" @qed

lemma group_hom_inv [rewrite]:
  "is_group_hom(f) \<Longrightarrow> G = source_str(f) \<Longrightarrow> H = target_str(f) \<Longrightarrow>
   x \<in> units(G) \<Longrightarrow> f`(inv(G,x)) = inv(H,f`x)"
@proof @have "f ` (inv(G,x) *\<^sub>G x) = \<one>\<^sub>H" @qed

definition is_group_iso :: "i \<Rightarrow> o" where [rewrite]:
  "is_group_iso(f) \<longleftrightarrow> (is_group_hom(f) \<and> bijective(f))"
setup {* add_property_const @{term is_group_iso} *}

definition group_iso_space :: "i \<Rightarrow> i \<Rightarrow> i"  (infix "\<cong>\<^sub>G" 60) where [rewrite]:
  "group_iso_space(G,H) = {f \<in> mor_space(G,H). is_group_iso(f)}"

lemma group_iso_spaceD [forward]:
  "f \<in> G \<cong>\<^sub>G H \<Longrightarrow> f \<in> G \<rightharpoonup> H \<and> is_group_iso(f)" by auto2

lemma group_iso_spaceI [backward]:
  "mor_form(f) \<Longrightarrow> is_group_iso(f) \<Longrightarrow> f \<in> source_str(f) \<cong>\<^sub>G target_str(f)" by auto2
setup {* del_prfstep_thm @{thm group_iso_space_def} *}
    
lemma iso_refl [typing]: "is_group(G) \<Longrightarrow> id_mor(G) \<in> G \<cong>\<^sub>G G" by auto2

lemma iso_trans [typing]:
  "is_group_iso(f) \<Longrightarrow> is_group_iso(g) \<Longrightarrow> target_str(f) = source_str(g) \<Longrightarrow>
   g \<circ>\<^sub>m f \<in> source_str(f) \<cong>\<^sub>G target_str(g)"
@proof
  @have (@rule) "\<forall>y\<in>target(f). \<exists>x\<in>source(f). f`x = y"
  @have (@rule) "\<forall>y\<in>target(g). \<exists>x\<in>source(g). g`x = y"
@qed

lemma iso_sym [typing]:
  "is_group_iso(f) \<Longrightarrow> inverse_mor(f) \<in> target_str(f) \<cong>\<^sub>G source_str(f)"
@proof
  @let "g = inverse_mor(f)"
  @have (@rule) "\<forall>y\<in>target(f). \<exists>x\<in>source(f). f`x = y"
  @have (@rule) "\<forall>y\<in>target(g). \<exists>x\<in>source(g). g`x = y"
@qed

section {* Image of a homomorphism *}
  
lemma image_is_subgroup:
  "is_group_hom(f) \<Longrightarrow> H = target_str(f) \<Longrightarrow> is_subgroup_set(H, image(f))"
@proof
  @let "G = source_str(f)"
  @have "f ` \<one>\<^sub>G = \<one>\<^sub>H"
  @have "subset_mult_closed(H, image(f))" @with
    @have "\<forall>x\<in>image(f). \<forall>y\<in>image(f). x *\<^sub>H y \<in> image(f)" @with
      @obtain "x'\<in>source(f)" where "f`x' = x"
      @obtain "y'\<in>source(f)" where "f`y' = y"
      @have "f`(x' *\<^sub>G y') = x *\<^sub>H y"
    @end
  @end
  @have "subset_inv_closed(H, image(f))" @with
    @have "\<forall>x\<in>image(f). inv(H,x) \<in> image(f)" @with
      @obtain "x'\<in>source(f)" where "f`x' = x"
      @have "f`(inv(G,x')) = inv(H,x)"
    @end
  @end
@qed
setup {* add_forward_prfstep_cond @{thm image_is_subgroup} [with_term "image(?f)"] *}

definition image_subgroup :: "i \<Rightarrow> i" where image_subgroup_def [rewrite_bidir]:
  "image_subgroup(f) = subgroup(target_str(f), image(f))"

definition group_mor_restrict_image :: "i \<Rightarrow> i" where [rewrite]:
  "group_mor_restrict_image(f) = Mor(source_str(f), image_subgroup(f), \<lambda>x. f`x)"

lemma group_mor_restrict_image_is_mor [typing]:
  "is_group_hom(f) \<Longrightarrow> group_mor_restrict_image(f) \<in> source_str(f) \<rightharpoonup>\<^sub>G image_subgroup(f)" by auto2
  
lemma group_mor_restrict_image_eval [rewrite]:
  "is_group_hom(f) \<Longrightarrow> f' = group_mor_restrict_image(f) \<Longrightarrow> x \<in> source(f') \<Longrightarrow> f'`x = f`x" by auto2
setup {* del_prfstep_thm @{thm group_mor_restrict_image_def} *}
  
lemma group_mor_factorize [rewrite_back]:
  "mor_form(f) \<Longrightarrow> is_group_hom(f) \<Longrightarrow>
   f = inj_mor(image_subgroup(f), target_str(f)) \<circ>\<^sub>m group_mor_restrict_image(f)" by auto2
  
lemma group_mor_inj_restrict_image_bij [typing]:
  "is_group_hom(f) \<Longrightarrow> injective(f) \<Longrightarrow>
   group_mor_restrict_image(f) \<in> source_str(f) \<cong>\<^sub>G image_subgroup(f)" by auto2

end
