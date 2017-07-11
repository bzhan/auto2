theory FundamentalGroup
imports PathHomotopy
begin
  
section {* Definition of fundamental group *}

definition is_loop :: "i \<Rightarrow> o" where [rewrite]:
  "is_loop(f) \<longleftrightarrow> (is_path(f) \<and> f`(0\<^sub>\<real>) = f`(1\<^sub>\<real>))"
setup {* add_property_const @{term is_loop} *}
  
lemma is_loopI [forward,backward]: "is_path(f) \<Longrightarrow> f`(0\<^sub>\<real>) = f`(1\<^sub>\<real>) \<Longrightarrow> is_loop(f)" by auto2
lemma is_loopD [forward]:
  "is_loop(f) \<Longrightarrow> is_path(f)"
  "is_loop(f) \<Longrightarrow> f`(0\<^sub>\<real>) = f`(1\<^sub>\<real>)" by auto2+
setup {* del_prfstep_thm @{thm is_loop_def} *}
  
lemma const_is_loop:
  "is_top_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> is_loop(const_mor(I,X,x))" by auto2
setup {* add_forward_prfstep_cond @{thm const_is_loop} [with_term "const_mor(?I,?X,?x)"] *}

lemma product_is_loop:
  "is_loop(f) \<Longrightarrow> is_loop(g) \<Longrightarrow> target_str(f) = target_str(g) \<Longrightarrow> f`(1\<^sub>\<real>) = g`(0\<^sub>\<real>) \<Longrightarrow> is_loop(f \<star> g)" by auto2
setup {* add_forward_prfstep_cond @{thm product_is_loop} [with_term "?f \<star> ?g"] *}
  
lemma inv_path_is_loop [forward]:
  "is_loop(f) \<Longrightarrow> is_loop(inv_path(f))" by auto2

definition loop_space :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "loop_space(X,x) = {f \<in> I \<rightharpoonup>\<^sub>T X. f`(0\<^sub>\<real>) = x \<and> f`(1\<^sub>\<real>) = x}"
setup {* register_wellform_data ("loop_space(X,x)", ["x \<in>. X"]) *}

definition loop_space_rel :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "loop_space_rel(X,x) = Equiv(loop_space(X,x), \<lambda>f g. path_homotopic(f,g))"
setup {* register_wellform_data ("loop_space_rel(X,x)", ["x \<in>. X"]) *}

lemma loop_spaceI [typing]:
  "is_loop(f) \<Longrightarrow> f \<in> loop_space(target_str(f),f`(0\<^sub>\<real>))" by auto2

lemma loop_spaceD [forward]:
  "f \<in> loop_space(X,x) \<Longrightarrow> is_loop(f) \<and> target_str(f) = X \<and> f`(0\<^sub>\<real>) = x" by auto2
setup {* del_prfstep_thm @{thm loop_space_def} *}
    
lemma loop_space_rel_is_rel [typing]:
  "is_top_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> loop_space_rel(X,x) \<in> equiv_space(loop_space(X,x))" by auto2

lemma loop_space_rel_eval:
  "is_top_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> \<R> = loop_space_rel(X,x) \<Longrightarrow>
   f \<in>. \<R> \<Longrightarrow> g \<in>. \<R> \<Longrightarrow> f \<sim>\<^sub>\<R> g \<longleftrightarrow> path_homotopic(f,g)" by auto2
setup {* add_rewrite_rule_cond @{thm loop_space_rel_eval} [with_cond "?f \<noteq> ?g"] *}
setup {* del_prfstep_thm @{thm loop_space_rel_def} *}
  
lemma const_mor_in_rel [typing]:
  "is_top_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> \<R> = loop_space_rel(X,x) \<Longrightarrow> const_mor(I,X,x) \<in>. \<R>" by auto2

definition loop_classes :: "i \<Rightarrow> i \<Rightarrow> i" where loop_classes [rewrite_bidir]:
  "loop_classes(X,x) = loop_space(X,x) // loop_space_rel(X,x)"
setup {* register_wellform_data ("loop_classes(X,x)", ["x \<in>. X"]) *}

definition fundamental_group :: "i \<Rightarrow> i \<Rightarrow> i" ("\<pi>\<^sub>1") where [rewrite]:
  "\<pi>\<^sub>1(X,x) = (let \<R> = loop_space_rel(X,x) in
    Group(loop_classes(X,x), equiv_class(\<R>,const_mor(I,X,x)), \<lambda>f g. equiv_class(\<R>,rep(\<R>,f) \<star> rep(\<R>,g))))"
setup {* register_wellform_data ("\<pi>\<^sub>1(X,x)", ["x \<in>. X"]) *}

lemma fundamental_group_group_form:
  "is_top_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> group_form(\<pi>\<^sub>1(X,x))" by auto2
setup {* add_forward_prfstep_cond @{thm fundamental_group_group_form} [with_term "\<pi>\<^sub>1(?X,?x)"] *}

lemma fundamental_group_carrier [rewrite_bidir]:
  "carrier(\<pi>\<^sub>1(X,x)) = loop_classes(X,x)" by auto2
    
lemma fundamental_group_evals [rewrite]:
  "G = \<pi>\<^sub>1(X,x) \<Longrightarrow> \<one>\<^sub>G = equiv_class(loop_space_rel(X,x),const_mor(I,X,x))"
  "is_top_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> G = \<pi>\<^sub>1(X,x) \<Longrightarrow> \<R> = loop_space_rel(X,x) \<Longrightarrow> f \<in>. G \<Longrightarrow> g \<in>. G \<Longrightarrow>
   f *\<^sub>G g = equiv_class(\<R>,rep(\<R>,f) \<star> rep(\<R>,g))" by auto2+
setup {* del_prfstep_thm @{thm fundamental_group_def} *}

section {* Multiplication on the fundamental group *}
  
lemma fundamental_group_mult_compat [resolve]:
  "is_top_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> compat_meta_bin(loop_space_rel(X,x), \<lambda>f g. f \<star> g)" by auto2

lemma fundamental_group_mult_eval [rewrite]:
  "is_top_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> G = \<pi>\<^sub>1(X,x) \<Longrightarrow> \<R> = loop_space_rel(X,x) \<Longrightarrow>
   f \<in>. \<R> \<Longrightarrow> g \<in>. \<R> \<Longrightarrow> equiv_class(\<R>,f) *\<^sub>G equiv_class(\<R>,g) = equiv_class(\<R>,f \<star> g)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "compat_meta_bin(loop_space_rel(X,x), \<lambda>f g. f \<star> g)") *})
setup {* del_prfstep_thm @{thm fundamental_group_mult_compat} *}
setup {* del_prfstep_thm @{thm fundamental_group_evals(2)} *}

lemma fundamental_group_mult_assoc [rewrite]:
  "is_top_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> G = \<pi>\<^sub>1(X,x) \<Longrightarrow> \<R> = loop_space_rel(X,x) \<Longrightarrow>
   f \<in>. G \<Longrightarrow> g \<in>. G \<Longrightarrow> h \<in>. G \<Longrightarrow> f *\<^sub>G g *\<^sub>G h = f *\<^sub>G (g *\<^sub>G h)"
  by (tactic {* auto2s_tac @{context} (
    LET "f' = rep(\<R>,f), g' = rep(\<R>,g), h' = rep(\<R>,h)") *})

lemma fundamental_group_mult_id [rewrite]:
  "is_top_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> G = \<pi>\<^sub>1(X,x) \<Longrightarrow> \<R> = loop_space_rel(X,x) \<Longrightarrow>
   f \<in>. G \<Longrightarrow> f *\<^sub>G \<one>\<^sub>G = f"
  by (tactic {* auto2s_tac @{context} (LET "f' = rep(\<R>,f)") *})

lemma fundamental_group_mult_id2 [rewrite]:
  "is_top_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> G = \<pi>\<^sub>1(X,x) \<Longrightarrow> \<R> = loop_space_rel(X,x) \<Longrightarrow>
   f \<in>. G \<Longrightarrow> \<one>\<^sub>G *\<^sub>G f = f"
  by (tactic {* auto2s_tac @{context} (LET "f' = rep(\<R>,f)") *})
  
definition fundamental_group_inv :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "fundamental_group_inv(\<R>,f) = equiv_class(\<R>,inv_path(rep(\<R>,f)))"

lemma fundamental_group_inv_typing [typing]:
  "is_top_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> G = \<pi>\<^sub>1(X,x) \<Longrightarrow> \<R> = loop_space_rel(X,x) \<Longrightarrow>
   f \<in>. G \<Longrightarrow> fundamental_group_inv(\<R>,f) \<in>. G" by auto2

lemma fundamental_group_inv2 [rewrite]:
  "is_top_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> G = \<pi>\<^sub>1(X,x) \<Longrightarrow> \<R> = loop_space_rel(X,x) \<Longrightarrow>
   f \<in>. G \<Longrightarrow> fundamental_group_inv(\<R>,f) *\<^sub>G f = \<one>\<^sub>G" by auto2

lemma fundamental_group_is_group:
  "is_top_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> is_group(\<pi>\<^sub>1(X,x))"
  by (tactic {* auto2s_tac @{context} (
    LET "G = \<pi>\<^sub>1(X,x), \<R> = loop_space_rel(X,x)" THEN
    HAVE "is_monoid(G)" THEN
    HAVE "\<forall>f\<in>.G. fundamental_group_inv(\<R>,f) *\<^sub>G f = \<one>\<^sub>G") *})
setup {* add_forward_prfstep_cond @{thm fundamental_group_is_group} [with_term "\<pi>\<^sub>1(?X,?x)"] *}

setup {* fold del_prfstep_thm [@{thm fundamental_group_mult_assoc},
  @{thm fundamental_group_mult_id}, @{thm fundamental_group_mult_id2},
  @{thm fundamental_group_inv2}] *}

section {* Morphisms on fundamental groups *}

definition induced_mor :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "induced_mor(k,x) =
    (let X = source_str(k) in let Y = target_str(k) in
     let \<R> = loop_space_rel(X,x) in let \<S> = loop_space_rel(Y,k`x) in
      Mor(\<pi>\<^sub>1(X,x), \<pi>\<^sub>1(Y,k`x), \<lambda>f. equiv_class(\<S>, k \<circ>\<^sub>m rep(\<R>,f))))"
setup {* register_wellform_data ("induced_mor(k,x)", ["x \<in> source(k)"]) *}

lemma induced_mor_is_morphism [typing]:
  "continuous(k) \<Longrightarrow> X = source_str(k) \<Longrightarrow> Y = target_str(k) \<Longrightarrow> x \<in> source(k) \<Longrightarrow>
   induced_mor(k,x) \<in> \<pi>\<^sub>1(X,x) \<rightharpoonup> \<pi>\<^sub>1(Y,k`x)" by auto2

lemma induced_mor_eval [rewrite]:
  "continuous(k) \<Longrightarrow> X = source_str(k) \<Longrightarrow> Y = target_str(k) \<Longrightarrow> x \<in> source(k) \<Longrightarrow>
   \<R> = loop_space_rel(X,x) \<Longrightarrow> \<S> = loop_space_rel(Y,k`x) \<Longrightarrow> f \<in>. \<R> \<Longrightarrow>
   induced_mor(k,x)`equiv_class(\<R>,f) = equiv_class(\<S>, k \<circ>\<^sub>m f)" by auto2
setup {* del_prfstep_thm @{thm induced_mor_def} *}

setup {* add_rewrite_rule_back @{thm path_product_comp} *}
lemma induced_mor_product [rewrite]:
  "continuous(k) \<Longrightarrow> X = source_str(k) \<Longrightarrow> Y = target_str(k) \<Longrightarrow> x \<in> source(k) \<Longrightarrow>
   G = \<pi>\<^sub>1(X,x) \<Longrightarrow> H = \<pi>\<^sub>1(Y,k`x) \<Longrightarrow> f \<in>. G \<Longrightarrow> g \<in>. G \<Longrightarrow>
   induced_mor(k,x)`(f *\<^sub>G g) = induced_mor(k,x)`f *\<^sub>H induced_mor(k,x)`g"
  by (tactic {* auto2s_tac @{context} (
    LET "\<R> = loop_space_rel(X,x)" THEN
    LET "f' = rep(\<R>,f), g' = rep(\<R>,g)") *})
setup {* del_prfstep_thm_str "@sym" @{thm path_product_comp} *}

lemma induced_mor_on_id [rewrite]:
  "continuous(k) \<Longrightarrow> X = source_str(k) \<Longrightarrow> Y = target_str(k) \<Longrightarrow> x \<in> source(k) \<Longrightarrow>
   G = \<pi>\<^sub>1(X,x) \<Longrightarrow> H = \<pi>\<^sub>1(Y,k`x) \<Longrightarrow> induced_mor(k,x)`(\<one>\<^sub>G) = \<one>\<^sub>H"
  by (tactic {* auto2s_tac @{context} (
    LET "\<R> = loop_space_rel(X,x)" THEN
    HAVE "path_homotopic(k \<circ>\<^sub>m rep(\<R>,\<one>\<^sub>G), k \<circ>\<^sub>m const_mor(I,X,x))") *})

lemma induced_mor_is_homomorphism [typing]:
  "continuous(k) \<Longrightarrow> X = source_str(k) \<Longrightarrow> Y = target_str(k) \<Longrightarrow> x \<in> source(k) \<Longrightarrow>
   induced_mor(k,x) \<in> \<pi>\<^sub>1(X,x) \<rightharpoonup>\<^sub>G \<pi>\<^sub>1(Y,k`x)" by auto2

lemma induced_mor_id [rewrite]:
  "is_top_space(X) \<Longrightarrow> x \<in>. X \<Longrightarrow> induced_mor(id_mor(X),x) = id_mor(\<pi>\<^sub>1(X,x))"
  by (tactic {* auto2s_tac @{context} (
    LET "G = \<pi>\<^sub>1(X,x), \<R> = loop_space_rel(X,x)" THEN
    HAVE_RULE "\<forall>f\<in>.G. induced_mor(id_mor(X),x)`f = f" WITH LET "f' = rep(\<R>,f)") *})

lemma induced_mor_comp' [rewrite]:
  "continuous(k) \<Longrightarrow> continuous(h) \<Longrightarrow> target_str(k) = source_str(h) \<Longrightarrow> x \<in> source(k) \<Longrightarrow>
   X = source_str(k) \<Longrightarrow> G = \<pi>\<^sub>1(X,x) \<Longrightarrow> f \<in>. G \<Longrightarrow> \<R> = loop_space_rel(X,x) \<Longrightarrow>
   induced_mor(h \<circ>\<^sub>m k, x) ` f = induced_mor(h,k`x) ` (induced_mor(k,x) ` f)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "f = equiv_class(\<R>,rep(\<R>,f))" THEN
    HAVE "(h \<circ>\<^sub>m k) \<circ>\<^sub>m rep(\<R>,f) = h \<circ>\<^sub>m (k \<circ>\<^sub>m rep(\<R>,f))") *})

lemma induced_mor_comp [rewrite]:
  "continuous(k) \<Longrightarrow> continuous(h) \<Longrightarrow> target_str(k) = source_str(h) \<Longrightarrow> x \<in> source(k) \<Longrightarrow>
   induced_mor(h \<circ>\<^sub>m k, x) = induced_mor(h,k`x) \<circ>\<^sub>m induced_mor(k,x)" by auto2
setup {* del_prfstep_thm @{thm induced_mor_comp'} *}

end
