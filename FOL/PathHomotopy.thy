theory PathHomotopy
imports Homotopy
begin

section {* Paths and homotopy between paths *}

definition is_path :: "i \<Rightarrow> o" where [rewrite_bidir]:
  "is_path(f) \<longleftrightarrow> (f \<in> I \<rightharpoonup>\<^sub>T target_str(f))"
setup {* add_property_const @{term is_path} *}

definition is_path_homotopy :: "[i, i, i] \<Rightarrow> o" where [rewrite]:
  "is_path_homotopy(f,g,F) \<longleftrightarrow> (is_path(f) \<and> is_path(g) \<and> is_homotopy(f,g,F) \<and>
                                (\<forall>t\<in>.I. F`\<langle>0\<^sub>\<real>,t\<rangle> = f`(0\<^sub>\<real>) \<and> F`\<langle>1\<^sub>\<real>,t\<rangle> = f`(1\<^sub>\<real>)))"
setup {* register_wellform_data ("is_path_homotopy(f,g,F)", ["target_str(f) = target_str(g)"]) *}

lemma is_path_homotopyD1 [rewrite]:
  "is_morphism_top(f) \<Longrightarrow> \<langle>0\<^sub>\<real>,t\<rangle> \<in> source(F) \<Longrightarrow> is_path_homotopy(f,g,F) \<Longrightarrow> F`\<langle>0\<^sub>\<real>,t\<rangle> = f`(0\<^sub>\<real>)"
  "is_morphism_top(f) \<Longrightarrow> \<langle>1\<^sub>\<real>,t\<rangle> \<in> source(F) \<Longrightarrow> is_path_homotopy(f,g,F) \<Longrightarrow> F`\<langle>1\<^sub>\<real>,t\<rangle> = f`(1\<^sub>\<real>)" by auto2+
    
lemma is_path_homotopyD2 [forward]:
  "is_path_homotopy(f,g,F) \<Longrightarrow> is_path(f) \<and> is_path(g) \<and> is_homotopy(f,g,F)" by auto2

lemma path_homotopy_eq_ends [forward]:
  "is_path(f) \<Longrightarrow> is_path_homotopy(f,g,F) \<Longrightarrow> f`(0\<^sub>\<real>) = g`(0\<^sub>\<real>) \<and> f`(1\<^sub>\<real>) = g`(1\<^sub>\<real>)" by auto2

lemma is_path_homotopyI [backward2]:
  "is_path(f) \<Longrightarrow> is_path(g) \<Longrightarrow> is_homotopy(f,g,F) \<Longrightarrow>
   \<forall>t\<in>.I. \<langle>0\<^sub>\<real>,t\<rangle> \<in> source(F) \<longrightarrow> F`\<langle>0\<^sub>\<real>,t\<rangle> = f`(0\<^sub>\<real>) \<Longrightarrow>
   \<forall>t\<in>.I. \<langle>1\<^sub>\<real>,t\<rangle> \<in> source(F) \<longrightarrow> F`\<langle>1\<^sub>\<real>,t\<rangle> = f`(1\<^sub>\<real>) \<Longrightarrow> is_path_homotopy(f,g,F)" by auto2
setup {* del_prfstep_thm @{thm is_path_homotopy_def} *}

definition path_homotopic :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "path_homotopic(f,g) \<longleftrightarrow> (\<exists>F. is_path_homotopy(f,g,F))"
setup {* register_wellform_data ("path_homotopic(f,g)", ["target_str(f) = target_str(g)"]) *}

lemma path_homotopicI [forward]:
  "is_path_homotopy(f,g,F) \<Longrightarrow> path_homotopic(f,g)" by auto2

lemma path_homotopicE1 [forward]:
  "path_homotopic(f,g) \<Longrightarrow> is_path(f) \<and> is_path(g) \<and> homotopic(f,g)" by auto2
    
lemma path_homotopicE2 [backward]:
  "path_homotopic(f,g) \<Longrightarrow> \<exists>F. is_path_homotopy(f,g,F)" by auto2
setup {* del_prfstep_thm @{thm path_homotopic_def} *}

lemma id_is_path_homotopy:
  "is_path(f) \<Longrightarrow> is_path_homotopy(f,f,id_homotopy(f))" by auto2
setup {* add_forward_prfstep_cond @{thm id_is_path_homotopy} [with_term "id_homotopy(?f)"] *}

lemma path_homotopic_id [resolve]:
  "is_path(f) \<Longrightarrow> path_homotopic(f,f)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "is_path_homotopy(f,f,id_homotopy(f))") *})
      
lemma inv_is_path_homotopy:
  "is_path_homotopy(f,g,F) \<Longrightarrow> is_path_homotopy(g,f,inv_homotopy(f,g,F))" by auto2
setup {* add_forward_prfstep_cond @{thm inv_is_path_homotopy} [with_term "inv_homotopy(?f,?g,?F)"] *}

lemma path_homotopy_inv [resolve]:
  "path_homotopic(f,g) \<Longrightarrow> path_homotopic(g,f)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "F, is_path_homotopy(f,g,F)" THEN
    HAVE "is_path_homotopy(g,f,inv_homotopy(f,g,F))") *})

lemma compose_is_path_homotopy:
  "is_path_homotopy(f,g,F) \<Longrightarrow> is_path_homotopy(g,h,G) \<Longrightarrow>
   is_path_homotopy(f,h,compose_homotopy(f,g,h,F,G))" by auto2
setup {* add_forward_prfstep_cond @{thm compose_is_path_homotopy}
  [with_term "compose_homotopy(?f,?g,?h,?F,?G)"] *}

lemma path_homotopy_trans [forward]:
  "path_homotopic(f,g) \<Longrightarrow> path_homotopic(g,h) \<Longrightarrow> path_homotopic(f,h)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "F, is_path_homotopy(f,g,F)" THEN
    CHOOSE "G, is_path_homotopy(g,h,G)" THEN
    HAVE "is_path_homotopy(f,h,compose_homotopy(f,g,h,F,G))") *})

section {* Product of paths *}
  
definition path_product :: "i \<Rightarrow> i \<Rightarrow> i"  (infixl "\<star>" 70) where [rewrite]:
  "f \<star> g = glue_morphism(I, f \<circ>\<^sub>m interval_lower, g \<circ>\<^sub>m interval_upper)"
setup {* register_wellform_data ("f \<star> g", ["target_str(f) = target_str(g)", "f`(1\<^sub>\<real>) = g`(0\<^sub>\<real>)"]) *}
setup {* add_prfstep_check_req ("f \<star> g", "f`(1\<^sub>\<real>) = g`(0\<^sub>\<real>)") *}

lemma I1_I2_inter [rewrite]: "carrier(I1) \<inter> carrier(I2) = {1\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real>}" by auto2
lemma I1_I2_union [rewrite]: "carrier(I1) \<union> carrier(I2) = carrier(I)" by auto2

lemma path_product_is_path:
  "is_path(f) \<Longrightarrow> is_path(g) \<Longrightarrow> target_str(f) = target_str(g) \<Longrightarrow> f`(1\<^sub>\<real>) = g`(0\<^sub>\<real>) \<Longrightarrow>
   is_path(f \<star> g) \<and> target_str(f \<star> g) = target_str(f)" by auto2
setup {* add_forward_prfstep_cond @{thm path_product_is_path} [with_term "?f \<star> ?g"] *}

lemma path_product_eval [rewrite]:
  "is_path(f) \<Longrightarrow> is_path(g) \<Longrightarrow> target_str(f) = target_str(g) \<Longrightarrow> f`(1\<^sub>\<real>) = g`(0\<^sub>\<real>) \<Longrightarrow>
   t \<in> source(f \<star> g) \<Longrightarrow> (f \<star> g)`t = (if t \<le>\<^sub>\<real> 1\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real> then f`(2\<^sub>\<real> *\<^sub>\<real> t) else g`(2\<^sub>\<real> *\<^sub>\<real> t -\<^sub>\<real> 1\<^sub>\<real>))"
  by (tactic {* auto2s_tac @{context} (
    CASE "t \<le>\<^sub>\<real> 1\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real>" WITH HAVE "t \<in>. I1") *})

lemma path_product_eval' [rewrite]:
  "is_path(f) \<Longrightarrow> is_path(g) \<Longrightarrow> target_str(f) = target_str(g) \<Longrightarrow> f`(1\<^sub>\<real>) = g`(0\<^sub>\<real>) \<Longrightarrow> (f \<star> g)`(0\<^sub>\<real>) = f`(0\<^sub>\<real>)"
  "is_path(f) \<Longrightarrow> is_path(g) \<Longrightarrow> target_str(f) = target_str(g) \<Longrightarrow> f`(1\<^sub>\<real>) = g`(0\<^sub>\<real>) \<Longrightarrow> (f \<star> g)`(1\<^sub>\<real>) = g`(1\<^sub>\<real>)" by auto2+

setup {* del_prfstep_thm @{thm path_product_def} *}

lemma path_product_comp [rewrite]:
  "is_path(f) \<Longrightarrow> is_path(g) \<Longrightarrow> continuous(h) \<Longrightarrow> target_str(f) = target_str(g) \<Longrightarrow> f`(1\<^sub>\<real>) = g`(0\<^sub>\<real>) \<Longrightarrow>
   target_str(f \<star> g) = source_str(h) \<Longrightarrow> (h \<circ>\<^sub>m (f \<star> g)) = (h \<circ>\<^sub>m f) \<star> (h \<circ>\<^sub>m g)" by auto2

section {* Path homotopy respects product *}

definition homotopy_left_half :: "i \<Rightarrow> i" where [rewrite]:
  "homotopy_left_half(F) = F \<circ>\<^sub>m prod_top_map(interval_lower,id_mor(I))"
setup {* register_wellform_data ("homotopy_left_half(F)", ["F \<in> I \<times>\<^sub>T I \<rightharpoonup>\<^sub>T target(F)"]) *}

lemma homotopy_left_half_type [typing]:
  "F \<in> I \<times>\<^sub>T I \<rightharpoonup>\<^sub>T target_str(F) \<Longrightarrow> homotopy_left_half(F) \<in> I1 \<times>\<^sub>T I \<rightharpoonup>\<^sub>T target_str(F)" by auto2

lemma homotopy_left_half_eval [rewrite]:
  "F \<in> I \<times>\<^sub>T I \<rightharpoonup>\<^sub>T target_str(F) \<Longrightarrow> F' = homotopy_left_half(F) \<Longrightarrow>
   \<langle>s,t\<rangle> \<in> source(F') \<Longrightarrow> F'`\<langle>s,t\<rangle> = F`\<langle>2\<^sub>\<real> *\<^sub>\<real> s, t\<rangle>" by auto2
setup {* del_prfstep_thm @{thm homotopy_left_half_def} *}

definition homotopy_right_half :: "i \<Rightarrow> i" where [rewrite]:
  "homotopy_right_half(F) = F \<circ>\<^sub>m prod_top_map(interval_upper,id_mor(I))"
setup {* register_wellform_data ("homotopy_right_half(F)", ["F \<in> I \<times>\<^sub>T I \<rightharpoonup>\<^sub>T target(f)"]) *}

lemma homotopy_right_half_type [typing]:
  "F \<in> I \<times>\<^sub>T I \<rightharpoonup>\<^sub>T target_str(F) \<Longrightarrow> homotopy_right_half(F) \<in> I2 \<times>\<^sub>T I \<rightharpoonup>\<^sub>T target_str(F)" by auto2

lemma homotopy_right_half_eval [rewrite]:
  "F \<in> I \<times>\<^sub>T I \<rightharpoonup>\<^sub>T target_str(F) \<Longrightarrow> F' = homotopy_right_half(F) \<Longrightarrow>
   \<langle>s,t\<rangle> \<in> source(F') \<Longrightarrow> F'`\<langle>s,t\<rangle> = F`\<langle>2\<^sub>\<real> *\<^sub>\<real> s -\<^sub>\<real> 1\<^sub>\<real>, t\<rangle>" by auto2
setup {* del_prfstep_thm @{thm homotopy_right_half_def} *}

definition join_homotopy :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "join_homotopy(f,g,f',g',F,G) = glue_morphism(I \<times>\<^sub>T I,
    homotopy_left_half(F), homotopy_right_half(G))"
setup {* register_wellform_data ("join_homotopy(f,g,f',g',F,G)",
  ["target_str(f) = target_str(g)", "f`(1\<^sub>\<real>) = g`(0\<^sub>\<real>)", "is_path_homotopy(f,f',F)", "is_path_homotopy(g,g',G)"]) *}

lemma join_homotopy_type [typing]:
  "is_path_homotopy(f,f',F) \<Longrightarrow> is_path_homotopy(g,g',G) \<Longrightarrow>
   target_str(f) = target_str(g) \<Longrightarrow> f`(1\<^sub>\<real>) = g`(0\<^sub>\<real>) \<Longrightarrow>
   join_homotopy(f,g,f',g',F,G) \<in> I \<times>\<^sub>T I \<rightharpoonup>\<^sub>T target_str(f)" by auto2

lemma join_homotopy_eval [rewrite]:
  "is_path_homotopy(f,f',F) \<Longrightarrow> is_path_homotopy(g,g',G) \<Longrightarrow>
   target_str(f) = target_str(g) \<Longrightarrow> f`(1\<^sub>\<real>) = g`(0\<^sub>\<real>) \<Longrightarrow> H = join_homotopy(f,g,f',g',F,G) \<Longrightarrow>
   \<langle>s,t\<rangle> \<in> source(H) \<Longrightarrow> H`\<langle>s,t\<rangle> = (if s \<le>\<^sub>\<real> 1\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real> then F`\<langle>2\<^sub>\<real> *\<^sub>\<real> s,t\<rangle> else G`\<langle>2\<^sub>\<real> *\<^sub>\<real> s -\<^sub>\<real> 1\<^sub>\<real>,t\<rangle>)" by auto2
setup {* del_prfstep_thm @{thm join_homotopy_def} *}

lemma join_is_homotopy:
  "is_path_homotopy(f,f',F) \<Longrightarrow> is_path_homotopy(g,g',G) \<Longrightarrow>
   target_str(f) = target_str(g) \<Longrightarrow> f`(1\<^sub>\<real>) = g`(0\<^sub>\<real>) \<Longrightarrow>
   is_path_homotopy(f \<star> g, f' \<star> g', join_homotopy(f,g,f',g',F,G))"
  by (tactic {* auto2s_tac @{context} (
    HAVE "is_homotopy(f \<star> g, f' \<star> g', join_homotopy(f,g,f',g',F,G))") *})
setup {* add_forward_prfstep_cond @{thm join_is_homotopy} [with_term "join_homotopy(?f,?g,?f',?g',?F,?G)"] *}

lemma path_homotopy_product [backward]:
  "target_str(f) = target_str(g) \<Longrightarrow> f`(1\<^sub>\<real>) = g`(0\<^sub>\<real>) \<Longrightarrow>
   path_homotopic(f,f') \<Longrightarrow> path_homotopic(g,g') \<Longrightarrow> path_homotopic(f \<star> g, f' \<star> g')"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "F, is_path_homotopy(f,f',F)" THEN
    CHOOSE "G, is_path_homotopy(g,g',G)" THEN
    HAVE "is_path_homotopy(f \<star> g, f' \<star> g', join_homotopy(f,g,f',g',F,G))") *})

lemma path_homotopy_maps_comp2 [backward]:
  "continuous(h) \<Longrightarrow> target_str(f) = source_str(h) \<Longrightarrow> is_path_homotopy(f,g,F) \<Longrightarrow>
   is_path_homotopy(h \<circ>\<^sub>m f, h \<circ>\<^sub>m g, h \<circ>\<^sub>m F)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "is_homotopy(h \<circ>\<^sub>m f, h \<circ>\<^sub>m g, h \<circ>\<^sub>m F)") *})

lemma path_homotopy_comp2 [backward]:
  "continuous(h) \<Longrightarrow> target_str(f) = source_str(h) \<Longrightarrow> path_homotopic(f,g) \<Longrightarrow> path_homotopic(h \<circ>\<^sub>m f, h \<circ>\<^sub>m g)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "F, is_path_homotopy(f,g,F)" THEN
    HAVE "is_path_homotopy(h \<circ>\<^sub>m f, h \<circ>\<^sub>m g, h \<circ>\<^sub>m F)") *})

section {* Interval is simply connected *}

definition linear_homotopy :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "linear_homotopy(f,g) = Mor(I \<times>\<^sub>T I, I, \<lambda>\<langle>s,t\<rangle>. (1\<^sub>\<real> -\<^sub>\<real> t) *\<^sub>\<real> (f`s) +\<^sub>\<real> t *\<^sub>\<real> (g`s))"
setup {* register_wellform_data ("linear_homotopy(f,g)", ["f \<in> I \<rightharpoonup>\<^sub>T I", "g \<in> I \<rightharpoonup>\<^sub>T I"]) *}

lemma linear_homotopy_in_range [backward2]:
  "t \<in>. I \<Longrightarrow> a \<in>. I \<Longrightarrow> b \<in>. I \<Longrightarrow> (1\<^sub>\<real> -\<^sub>\<real> t) *\<^sub>\<real> a +\<^sub>\<real> t *\<^sub>\<real> b \<in>. I"
  by (tactic {* auto2s_tac @{context} (
    CASE "a \<le>\<^sub>\<real> b" WITH HAVE "(1\<^sub>\<real> -\<^sub>\<real> t) *\<^sub>\<real> a \<le>\<^sub>\<real> (1\<^sub>\<real> -\<^sub>\<real> t) *\<^sub>\<real> b" THEN
    CASE "a \<ge>\<^sub>\<real> b" WITH HAVE "t *\<^sub>\<real> a \<ge>\<^sub>\<real> t *\<^sub>\<real> b") *})

lemma linear_homotopy_continuous [typing]:
  "f \<in> I \<rightharpoonup>\<^sub>T I \<Longrightarrow> g \<in> I \<rightharpoonup>\<^sub>T I \<Longrightarrow> linear_homotopy(f,g) \<in> I \<times>\<^sub>T I \<rightharpoonup>\<^sub>T I"
  by (tactic {* auto2s_tac @{context} (HAVE "I = subspace(\<real>,carrier(I))") *})
setup {* del_prfstep_thm @{thm linear_homotopy_in_range} *}

lemma linear_homotopy_eval [rewrite]:
  "f \<in> I \<rightharpoonup>\<^sub>T I \<Longrightarrow> g \<in> I \<rightharpoonup>\<^sub>T I \<Longrightarrow> F = linear_homotopy(f,g) \<Longrightarrow>
   \<langle>s,t\<rangle> \<in> source(F) \<Longrightarrow> F`\<langle>s,t\<rangle> = (1\<^sub>\<real> -\<^sub>\<real> t) *\<^sub>\<real> (f`s) +\<^sub>\<real> t *\<^sub>\<real> (g`s)" by auto2
setup {* del_prfstep_thm @{thm linear_homotopy_def} *}

lemma linear_homotopy_is_homotopy:
  "f \<in> I \<rightharpoonup>\<^sub>T I \<Longrightarrow> g \<in> I \<rightharpoonup>\<^sub>T I \<Longrightarrow> is_homotopy(f,g,linear_homotopy(f,g))" by auto2
setup {* add_forward_prfstep_cond @{thm linear_homotopy_is_homotopy} [with_term "linear_homotopy(?f,?g)"] *}

lemma linear_homotopy_eq [rewrite]:
  "a \<in>. \<real> \<Longrightarrow> t \<in>. \<real> \<Longrightarrow> (1\<^sub>\<real> -\<^sub>\<real> t) *\<^sub>\<real> a +\<^sub>\<real> t *\<^sub>\<real> a = a" by auto2

lemma linear_homotopy_is_path_homotopy [backward]:
  "f \<in> I \<rightharpoonup>\<^sub>T I \<Longrightarrow> g \<in> I \<rightharpoonup>\<^sub>T I \<Longrightarrow> f`(0\<^sub>\<real>) = g`(0\<^sub>\<real>) \<Longrightarrow> f`(1\<^sub>\<real>) = g`(1\<^sub>\<real>) \<Longrightarrow>
   is_path_homotopy(f,g,linear_homotopy(f,g))" by auto2
setup {* del_prfstep_thm @{thm linear_homotopy_eq} *}
      
definition simply_connected :: "i \<Rightarrow> o" where [rewrite]:
  "simply_connected(X) \<longleftrightarrow> (is_top_space(X) \<and>
    (\<forall>f\<in>I\<rightharpoonup>\<^sub>TX. \<forall>g\<in>I\<rightharpoonup>\<^sub>TX. f`(0\<^sub>\<real>) = g`(0\<^sub>\<real>) \<longrightarrow> f`(1\<^sub>\<real>) = g`(1\<^sub>\<real>) \<longrightarrow> path_homotopic(f,g)))"
setup {* add_property_const @{term simply_connected} *}
  
lemma simply_connectedI [forward]:
  "is_top_space(X) \<Longrightarrow> \<forall>f\<in>I\<rightharpoonup>\<^sub>TX. \<forall>g\<in>I\<rightharpoonup>\<^sub>TX. f`(0\<^sub>\<real>) = g`(0\<^sub>\<real>) \<longrightarrow> f`(1\<^sub>\<real>) = g`(1\<^sub>\<real>) \<longrightarrow> path_homotopic(f,g) \<Longrightarrow>
   simply_connected(X)" by auto2
  
lemma simply_connectedD [backward]:
  "is_path(f) \<Longrightarrow> is_path(g) \<Longrightarrow> simply_connected(target_str(f)) \<Longrightarrow> target_str(f) = target_str(g) \<Longrightarrow>
   f`(0\<^sub>\<real>) = g`(0\<^sub>\<real>) \<Longrightarrow> f`(1\<^sub>\<real>) = g`(1\<^sub>\<real>) \<Longrightarrow> path_homotopic(f,g)" by auto2
setup {* del_prfstep_thm @{thm simply_connected_def} *}
  
lemma interval_simply_connected [forward]: "simply_connected(I)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>f\<in>I\<rightharpoonup>\<^sub>TI. \<forall>g\<in>I\<rightharpoonup>\<^sub>TI. f`(0\<^sub>\<real>) = g`(0\<^sub>\<real>) \<longrightarrow> f`(1\<^sub>\<real>) = g`(1\<^sub>\<real>) \<longrightarrow> path_homotopic(f,g)" WITH
      HAVE "is_path_homotopy(f,g,linear_homotopy(f,g))") *})

section {* Groupoid properties of product *}

definition I1a :: i where [rewrite]: "I1a = subspace(I1,closed_interval(\<real>,0\<^sub>\<real>,1\<^sub>\<real> /\<^sub>\<real> 4\<^sub>\<real>))"
definition I1b :: i where [rewrite]: "I1b = subspace(I1,closed_interval(\<real>,1\<^sub>\<real> /\<^sub>\<real> 4\<^sub>\<real>, 1\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real>))"

lemma I1a_type [typing]: "I1a \<in> raw_top_spaces(closed_interval(\<real>,0\<^sub>\<real>,1\<^sub>\<real> /\<^sub>\<real> 4\<^sub>\<real>))" by auto2
lemma I1b_type [typing]: "I1b \<in> raw_top_spaces(closed_interval(\<real>,1\<^sub>\<real> /\<^sub>\<real> 4\<^sub>\<real>,1\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real>))" by auto2
lemma I1a_is_top_space [forward]: "is_top_space(I1a)" by auto2
lemma I1b_is_top_space [forward]: "is_top_space(I1b)" by auto2
lemma I1a_subspace [rewrite]: "I1a = subspace(I1,carrier(I1a)) \<and> carrier(I1a) \<subseteq> carrier(I1)" by auto2
lemma I1b_subspace [rewrite]: "I1b = subspace(I1,carrier(I1b)) \<and> carrier(I1b) \<subseteq> carrier(I1)" by auto2
setup {* fold del_prfstep_thm [@{thm I1a_def}, @{thm I1b_def}] *}

lemma I1ab_inter [rewrite]: "carrier(I1a) \<inter> carrier(I1b) = {1\<^sub>\<real> /\<^sub>\<real> 4\<^sub>\<real>}" by auto2
lemma I1ab_union [rewrite]: "carrier(I1a) \<union> carrier(I1b) = carrier(I1)" by auto2

setup {* add_rewrite_rule @{thm interval_def} *}

definition path_assoc_reparam1 :: i where [rewrite]:
  "path_assoc_reparam1 = glue_morphism(I1, Mor(I1a,I,\<lambda>t. 2\<^sub>\<real> *\<^sub>\<real> t), Mor(I1b,I,\<lambda>t. t +\<^sub>\<real> 1\<^sub>\<real> /\<^sub>\<real> 4\<^sub>\<real>))"

lemma I1a_closed [resolve]: "is_closed(I1,carrier(I1a))" by auto2
lemma I1b_closed [resolve]: "is_closed(I1,carrier(I1b))" by auto2

lemma path_assoc_reparam1_type [typing]:
  "path_assoc_reparam1 \<in> I1 \<rightharpoonup>\<^sub>T I" by auto2
    
lemma path_assoc_reparam1_eval [rewrite]:
  "t \<in> source(path_assoc_reparam1) \<Longrightarrow> path_assoc_reparam1`t =
    (if t \<le>\<^sub>\<real> 1\<^sub>\<real> /\<^sub>\<real> 4\<^sub>\<real> then 2\<^sub>\<real> *\<^sub>\<real> t else t +\<^sub>\<real> 1\<^sub>\<real> /\<^sub>\<real> 4\<^sub>\<real>)" by auto2
setup {* del_prfstep_thm @{thm path_assoc_reparam1_def} *}

lemma path_assoc_reparam1_eval' [rewrite]:
  "path_assoc_reparam1`(0\<^sub>\<real>) = 0\<^sub>\<real>"
  "path_assoc_reparam1`(1\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real>) = 3\<^sub>\<real> /\<^sub>\<real> 4\<^sub>\<real>" by auto2+

definition path_assoc_reparam :: i where [rewrite]:
  "path_assoc_reparam = glue_morphism(I, path_assoc_reparam1, Mor(I2, I, \<lambda>t. (t +\<^sub>\<real> 1\<^sub>\<real>) *\<^sub>\<real> (1\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real>)))"
  
lemma path_assoc_reparam_type [typing]:
  "path_assoc_reparam \<in> I \<rightharpoonup>\<^sub>T I" by auto2
    
lemma path_assoc_reparam_eval [rewrite]:
  "t \<in> source(path_assoc_reparam) \<Longrightarrow> path_assoc_reparam`t =
    (if t \<le>\<^sub>\<real> 1\<^sub>\<real> /\<^sub>\<real> 4\<^sub>\<real> then 2\<^sub>\<real> *\<^sub>\<real> t else
     if t \<le>\<^sub>\<real> 1\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real> then t +\<^sub>\<real> 1\<^sub>\<real> /\<^sub>\<real> 4\<^sub>\<real> else (t +\<^sub>\<real> 1\<^sub>\<real>) /\<^sub>\<real> 2\<^sub>\<real>)" by auto2
setup {* del_prfstep_thm @{thm path_assoc_reparam_def} *}

setup {* del_prfstep_thm_str "" @{thm interval_def} *}

lemma path_assoc_eval1 [rewrite]:
  "is_path(f) \<Longrightarrow> is_path(g) \<Longrightarrow> is_path(h) \<Longrightarrow> target_str(f) = target_str(g) \<Longrightarrow>
   target_str(f \<star> g) = target_str(h) \<Longrightarrow> f`(1\<^sub>\<real>) = g`(0\<^sub>\<real>) \<Longrightarrow> (f \<star> g)`(1\<^sub>\<real>) = h`(0\<^sub>\<real>) \<Longrightarrow>
   t \<in> source((f \<star> g) \<star> h) \<Longrightarrow> ((f \<star> g) \<star> h)`t =
    (if t \<le>\<^sub>\<real> 1\<^sub>\<real> /\<^sub>\<real> 4\<^sub>\<real> then f`(2\<^sub>\<real> *\<^sub>\<real> (2\<^sub>\<real> *\<^sub>\<real> t)) else
     if t \<le>\<^sub>\<real> 1\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real> then g`((2\<^sub>\<real> *\<^sub>\<real> (2\<^sub>\<real> *\<^sub>\<real> t)) -\<^sub>\<real> 1\<^sub>\<real>) else h`(2\<^sub>\<real> *\<^sub>\<real> t -\<^sub>\<real> 1\<^sub>\<real>))" by auto2
      
lemma path_assoc_eval2 [rewrite]:
  "is_path(f) \<Longrightarrow> is_path(g) \<Longrightarrow> is_path(h) \<Longrightarrow> target_str(f) = target_str(g \<star> h) \<Longrightarrow>
   target_str(g) = target_str(h) \<Longrightarrow> f`(1\<^sub>\<real>) = (g \<star> h)`(0\<^sub>\<real>) \<Longrightarrow> g`(1\<^sub>\<real>) = h`(0\<^sub>\<real>) \<Longrightarrow>
   t \<in> source(f \<star> (g \<star> h)) \<Longrightarrow> (f \<star> (g \<star> h))`t =
    (if t \<le>\<^sub>\<real> 1\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real> then f`(2\<^sub>\<real> *\<^sub>\<real> t) else
     if t \<le>\<^sub>\<real> 3\<^sub>\<real> /\<^sub>\<real> 4\<^sub>\<real> then g`(2\<^sub>\<real> *\<^sub>\<real> (2\<^sub>\<real> *\<^sub>\<real> t -\<^sub>\<real> 1\<^sub>\<real>)) else h`((2\<^sub>\<real> *\<^sub>\<real> (2\<^sub>\<real> *\<^sub>\<real> t -\<^sub>\<real> 1\<^sub>\<real>)) -\<^sub>\<real> 1\<^sub>\<real>))" by auto2

lemma path_assoc_comp [rewrite]:
  "is_path(f) \<Longrightarrow> is_path(g) \<Longrightarrow> is_path(h) \<Longrightarrow> target_str(f) = target_str(g \<star> h) \<Longrightarrow>
   target_str(g) = target_str(h) \<Longrightarrow> f`(1\<^sub>\<real>) = (g \<star> h)`(0\<^sub>\<real>) \<Longrightarrow> g`(1\<^sub>\<real>) = h`(0\<^sub>\<real>) \<Longrightarrow>
   t \<in> source(path_assoc_reparam) \<Longrightarrow> (f \<star> (g \<star> h)) ` (path_assoc_reparam ` t) = ((f \<star> g) \<star> h) ` t"
  by (tactic {* auto2s_tac @{context} (
    CASE "t \<le>\<^sub>\<real> 1\<^sub>\<real> /\<^sub>\<real> 4\<^sub>\<real>" WITH (
      HAVE "2\<^sub>\<real> *\<^sub>\<real> t \<le>\<^sub>\<real> 1\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real>" WITH (
        HAVE "2\<^sub>\<real> *\<^sub>\<real> t \<le>\<^sub>\<real> 2\<^sub>\<real> *\<^sub>\<real> (1\<^sub>\<real> /\<^sub>\<real> 4\<^sub>\<real>)")) THEN
    CASE "t \<le>\<^sub>\<real> 1\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real>" WITH (
      HAVE "t +\<^sub>\<real> 1\<^sub>\<real> /\<^sub>\<real> 4\<^sub>\<real> >\<^sub>\<real> 1\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real>" THEN
      HAVE "t +\<^sub>\<real> 1\<^sub>\<real> /\<^sub>\<real> 4\<^sub>\<real> \<le>\<^sub>\<real> 3\<^sub>\<real> /\<^sub>\<real> 4\<^sub>\<real>" THEN
      HAVE "2\<^sub>\<real> *\<^sub>\<real> ((2\<^sub>\<real> *\<^sub>\<real> (t +\<^sub>\<real> 1\<^sub>\<real> /\<^sub>\<real> 4\<^sub>\<real>)) -\<^sub>\<real> 1\<^sub>\<real>) = (2\<^sub>\<real> *\<^sub>\<real> (2\<^sub>\<real> *\<^sub>\<real> t)) -\<^sub>\<real> 1\<^sub>\<real>") THEN
    HAVE "(t +\<^sub>\<real> 1\<^sub>\<real>) /\<^sub>\<real> 2\<^sub>\<real> >\<^sub>\<real> 3\<^sub>\<real> /\<^sub>\<real> 4\<^sub>\<real>" WITH (
      HAVE "(t +\<^sub>\<real> 1\<^sub>\<real>) /\<^sub>\<real> 2\<^sub>\<real> >\<^sub>\<real> 3\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real>") THEN
    HAVE "(2\<^sub>\<real> *\<^sub>\<real> ((2\<^sub>\<real> *\<^sub>\<real> ((t +\<^sub>\<real> 1\<^sub>\<real>) /\<^sub>\<real> 2\<^sub>\<real>)) -\<^sub>\<real> 1\<^sub>\<real>)) -\<^sub>\<real> 1\<^sub>\<real> = 2\<^sub>\<real> *\<^sub>\<real> t -\<^sub>\<real> 1\<^sub>\<real>") *})
  
lemma path_assoc_reparam_homotopy [resolve]:
  "path_homotopic(path_assoc_reparam, id_mor(I))" by auto2

lemma path_assoc_homotopic [resolve]:
  "is_path(f) \<Longrightarrow> is_path(g) \<Longrightarrow> is_path(h) \<Longrightarrow> target_str(f) = target_str(g \<star> h) \<Longrightarrow>
   target_str(g) = target_str(h) \<Longrightarrow> f`(1\<^sub>\<real>) = (g \<star> h)`(0\<^sub>\<real>) \<Longrightarrow> g`(1\<^sub>\<real>) = h`(0\<^sub>\<real>) \<Longrightarrow>
   path_homotopic((f \<star> g) \<star> h, f \<star> (g \<star> h))"
  by (tactic {* auto2s_tac @{context} (
    HAVE "(f \<star> (g \<star> h)) \<circ>\<^sub>m path_assoc_reparam = (f \<star> g) \<star> h" THEN
    HAVE "(f \<star> (g \<star> h)) \<circ>\<^sub>m id_mor(I) = f \<star> (g \<star> h)") *})
      
setup {* del_prfstep_thm @{thm path_product_eval} *}

definition inv_path :: "i \<Rightarrow> i" where [rewrite]:
  "inv_path(f) = f \<circ>\<^sub>m interval_inv"

lemma inv_is_path [forward]:
  "is_path(f) \<Longrightarrow> is_path(inv_path(f))" by auto2

(* Remove this *)
lemma const_mor_eval_zero [rewrite]: "const_mor(I,I,0\<^sub>\<real>)`(0\<^sub>\<real>) = 0\<^sub>\<real>" by auto2
lemma const_mor_eval_one [rewrite]: "const_mor(I,I,1\<^sub>\<real>)`(1\<^sub>\<real>) = 1\<^sub>\<real>" by auto2

lemma path_product_right_id [resolve]:
  "is_path(f) \<Longrightarrow> X = target_str(f) \<Longrightarrow> path_homotopic(f, f \<star> const_mor(I,X,f`(1\<^sub>\<real>)))"
  by (tactic {* auto2s_tac @{context} (
    HAVE "path_homotopic(f \<circ>\<^sub>m id_mor(I), f \<circ>\<^sub>m (id_mor(I) \<star> const_mor(I,I,1\<^sub>\<real>)))") *})

lemma path_product_left_id [resolve]:
  "is_path(f) \<Longrightarrow> X = target_str(f) \<Longrightarrow> path_homotopic(f, const_mor(I,X,f`(0\<^sub>\<real>)) \<star> f)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "path_homotopic(f \<circ>\<^sub>m id_mor(I), f \<circ>\<^sub>m (const_mor(I,I,0\<^sub>\<real>) \<star> id_mor(I)))") *})
  
lemma path_product_inv_left [resolve]:
  "is_path(f) \<Longrightarrow> X = target_str(f) \<Longrightarrow> path_homotopic(f \<star> inv_path(f), const_mor(I,X,f`(0\<^sub>\<real>)))"
  by (tactic {* auto2s_tac @{context} (
    HAVE "f \<circ>\<^sub>m const_mor(I,I,0\<^sub>\<real>) = const_mor(I,X,f`(0\<^sub>\<real>))" THEN
    HAVE "f \<circ>\<^sub>m (id_mor(I) \<star> interval_inv) = f \<star> inv_path(f)") *})

lemma path_product_inv_right [resolve]:
  "is_path(f) \<Longrightarrow> X = target_str(f) \<Longrightarrow> path_homotopic(inv_path(f) \<star> f, const_mor(I,X,f`(1\<^sub>\<real>)))"
  by (tactic {* auto2s_tac @{context} (
    HAVE "f \<circ>\<^sub>m const_mor(I,I,1\<^sub>\<real>) = const_mor(I,X,f`(1\<^sub>\<real>))" THEN
    HAVE "f \<circ>\<^sub>m (interval_inv \<star> id_mor(I)) = inv_path(f) \<star> f") *})

end
