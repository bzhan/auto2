theory Homotopy
imports RealTopology
begin

section {* Automation for intervals *}
  
lemma closed_interval_memI:
  "is_ord_field(R) \<Longrightarrow> a \<le>\<^sub>R x \<Longrightarrow> x \<le>\<^sub>R b \<Longrightarrow> x \<in> closed_interval(R,a,b)" by auto2

lemma closed_interval_not_memI:
  "is_ord_field(R) \<Longrightarrow> x <\<^sub>R a \<Longrightarrow> x \<in> closed_interval(R,a,b) \<Longrightarrow> False"
  "is_ord_field(R) \<Longrightarrow> b <\<^sub>R x \<Longrightarrow> x \<in> closed_interval(R,a,b) \<Longrightarrow> False" by auto2+

lemma closed_interval_subset [backward]:
  "is_ord_field(R) \<Longrightarrow> c \<le>\<^sub>R a \<Longrightarrow> b \<le>\<^sub>R d \<Longrightarrow> closed_interval(R,a,b) \<subseteq> closed_interval(R,c,d)" by auto2  

lemma closed_interval_plus:
  "is_ord_field(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> c \<in>. R \<Longrightarrow>
   x +\<^sub>R c \<notin> closed_interval(R,a,b) \<Longrightarrow> x \<notin> closed_interval(R, a -\<^sub>R c, b -\<^sub>R c)" by auto2

lemma closed_interval_minus:
  "is_ord_field(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> c \<in>. R \<Longrightarrow>
   x -\<^sub>R c \<notin> closed_interval(R,a,b) \<Longrightarrow> x \<notin> closed_interval(R, a +\<^sub>R c, b +\<^sub>R c)" by auto2

lemma closed_interval_times:
  "is_ord_field(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> c >\<^sub>R 0\<^sub>R \<Longrightarrow>
   c *\<^sub>R x \<notin> closed_interval(R,a,b) \<Longrightarrow> x \<notin> closed_interval(R, a /\<^sub>R c, b /\<^sub>R c)" by auto2

ML_file "interval_steps.ML"

section {* Commonly used intervals *}

definition interval :: i   ("I") where [rewrite]:
  "interval = subspace(\<real>, closed_interval(\<real>,0\<^sub>\<real>,1\<^sub>\<real>))"

lemma interval_is_top [forward]: "is_top_space(I)" by auto2
lemma interval_carrier [rewrite]: "carrier(I) = closed_interval(\<real>,0\<^sub>\<real>,1\<^sub>\<real>)" by auto2

definition interval_left :: i  ("I1") where [rewrite]:
  "I1 = subspace(\<real>, closed_interval(\<real>,0\<^sub>\<real>,1\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real>))"

definition interval_right :: i  ("I2") where [rewrite]:
  "I2 = subspace(\<real>, closed_interval(\<real>,1\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real>,1\<^sub>\<real>))"

lemma interval_left_type [typing]: "I1 \<in> raw_top_spaces(closed_interval(\<real>,0\<^sub>\<real>,1\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real>))" by auto2
lemma interval_right_type [typing]: "I2 \<in> raw_top_spaces(closed_interval(\<real>,1\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real>,1\<^sub>\<real>))" by auto2
lemma interval_left_is_top [forward]: "is_top_space(I1)" by auto2
lemma interval_right_is_top [forward]: "is_top_space(I2)" by auto2
lemma I1_subspace [rewrite]: "I1 = subspace(I,carrier(I1)) \<and> carrier(I1) \<subseteq> carrier(I)" by auto2
lemma I2_subspace [rewrite]: "I2 = subspace(I,carrier(I2)) \<and> carrier(I2) \<subseteq> carrier(I)" by auto2
setup {* fold del_prfstep_thm [@{thm interval_left_def}, @{thm interval_right_def}] *}

lemma real_topology_sub_closed_interval_closed [backward]:
  "a \<in>. \<real> \<Longrightarrow> b \<in>. \<real> \<Longrightarrow> c \<in>. \<real> \<Longrightarrow> d \<in>. \<real> \<Longrightarrow> A = closed_interval(\<real>,a,b) \<Longrightarrow>
   B = closed_interval(\<real>,c,d) \<Longrightarrow> B \<subseteq> A \<Longrightarrow> is_closed(subspace(\<real>,A),B)"
@proof
  @have "is_closed(\<real>,A)" @have "is_closed(\<real>,B)"
@qed

lemma I1_closed [resolve]: "is_closed(I,carrier(I1))" by auto2
lemma I2_closed [resolve]: "is_closed(I,carrier(I2))" by auto2

lemma restrict_real_fun [backward]:
  "B \<subseteq> carrier(\<real>) \<Longrightarrow> B' = subspace(\<real>,B) \<Longrightarrow>
   Mor(A,B',f) \<in> A \<rightharpoonup> B' \<Longrightarrow> Mor(A,\<real>,f) \<in> A \<rightharpoonup>\<^sub>T \<real> \<Longrightarrow> continuous(Mor(A,B',f))"
@proof
  @have (@rule) "\<forall>x\<in>.A. Mor(A,B',f)`x = f(x)"
  @have "Mor(A,B',f) = mor_restrict_image_top(Mor(A,\<real>,f),B)"
@qed

definition interval_inv :: i where [rewrite]:
  "interval_inv = Mor(I,I,\<lambda>t. 1\<^sub>\<real> -\<^sub>\<real> t)"

lemma interval_inv_continuous [typing]: "interval_inv \<in> I \<rightharpoonup>\<^sub>T I" by auto2
lemma interval_inv_eval [rewrite]: "t \<in> source(interval_inv) \<Longrightarrow> interval_inv`t = 1\<^sub>\<real> -\<^sub>\<real> t" by auto2
setup {* del_prfstep_thm @{thm interval_inv_def} *}

definition interval_lower :: i where [rewrite]:
  "interval_lower = Mor(I1,I,\<lambda>t. 2\<^sub>\<real> *\<^sub>\<real> t)"
  
lemma interval_lower_continuous [typing]: "interval_lower \<in> I1 \<rightharpoonup>\<^sub>T I" by auto2
lemma interval_lower_eval [rewrite]: "t \<in> source(interval_lower) \<Longrightarrow> interval_lower`t = 2\<^sub>\<real> *\<^sub>\<real> t" by auto2
setup {* del_prfstep_thm @{thm interval_lower_def} *}

definition interval_upper :: i where [rewrite]:
  "interval_upper = Mor(I2,I,\<lambda>t. 2\<^sub>\<real> *\<^sub>\<real> t -\<^sub>\<real> 1\<^sub>\<real>)"
  
lemma interval_upper_continuous [typing]: "interval_upper \<in> I2 \<rightharpoonup>\<^sub>T I" by auto2
lemma interval_upper_eval [rewrite]: "t \<in> source(interval_upper) \<Longrightarrow> interval_upper`t = 2\<^sub>\<real> *\<^sub>\<real> t -\<^sub>\<real> 1\<^sub>\<real>" by auto2
setup {* del_prfstep_thm @{thm interval_upper_def} *}

setup {* del_prfstep_thm @{thm interval_def} *}
setup {* add_rewrite_rule_back @{thm interval_def} *}

section {* Homotopy between two continuous functions from X to Y *}

definition is_homotopy :: "[i, i, i] \<Rightarrow> o" where [rewrite]:
  "is_homotopy(f,g,F) \<longleftrightarrow> (let S = source_str(f) in let T = target_str(f) in
                           continuous(f) \<and> continuous(g) \<and> S = source_str(g) \<and> T = target_str(g) \<and>
                           F \<in> S \<times>\<^sub>T I \<rightharpoonup>\<^sub>T T \<and> (\<forall>x\<in>.S. F`\<langle>x,0\<^sub>\<real>\<rangle> = f`x \<and> F`\<langle>x,1\<^sub>\<real>\<rangle> = g`x))"
setup {* register_wellform_data ("is_homotopy(f,g,F)",
  ["source_str(f) = source_str(g)", "target_str(f) = target_str(g)"]) *}

lemma is_homotopyD1 [rewrite]:
  "is_morphism_top(f) \<Longrightarrow> \<langle>x,0\<^sub>\<real>\<rangle> \<in> source(F) \<Longrightarrow> is_homotopy(f,g,F) \<Longrightarrow> F`\<langle>x,0\<^sub>\<real>\<rangle> = f`x"
  "is_morphism_top(f) \<Longrightarrow> \<langle>x,1\<^sub>\<real>\<rangle> \<in> source(F) \<Longrightarrow> is_homotopy(f,g,F) \<Longrightarrow> F`\<langle>x,1\<^sub>\<real>\<rangle> = g`x" by auto2+
    
lemma is_homotopyD2 [forward]:
  "is_homotopy(f,g,F) \<Longrightarrow> continuous(f) \<and> continuous(g) \<and> source_str(f) = source_str(g) \<and>
                          target_str(f) = target_str(g) \<and> F \<in> source_str(f) \<times>\<^sub>T I \<rightharpoonup>\<^sub>T target_str(f)" by auto2
    
lemma is_homotopyI [backward2]:
  "continuous(f) \<Longrightarrow> continuous(g) \<Longrightarrow> source_str(f) = source_str(g) \<Longrightarrow> target_str(f) = target_str(g) \<Longrightarrow>
   F \<in> source_str(f) \<times>\<^sub>T I \<rightharpoonup>\<^sub>T target_str(f) \<Longrightarrow>
   \<forall>x\<in>source(f). \<langle>x,0\<^sub>\<real>\<rangle> \<in> source(F) \<longrightarrow> F`\<langle>x,0\<^sub>\<real>\<rangle> = f`x \<Longrightarrow>
   \<forall>x\<in>source(f). \<langle>x,1\<^sub>\<real>\<rangle> \<in> source(F) \<longrightarrow> F`\<langle>x,1\<^sub>\<real>\<rangle> = g`x \<Longrightarrow> is_homotopy(f,g,F)" by auto2
setup {* del_prfstep_thm @{thm is_homotopy_def} *}

definition homotopic :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "homotopic(f,g) \<longleftrightarrow> (\<exists>F. is_homotopy(f,g,F))"

lemma homotopicI [forward]:
   "is_homotopy(f,g,F) \<Longrightarrow> homotopic(f,g)" by auto2

lemma homotopicE1 [forward]:
  "homotopic(f,g) \<Longrightarrow> continuous(f) \<and> continuous(g)"
  "homotopic(f,g) \<Longrightarrow> source_str(f) = source_str(g) \<and> target_str(f) = target_str(g)" by auto2+
    
lemma homotopicE2 [backward]:
  "homotopic(f,g) \<Longrightarrow> \<exists>F. is_homotopy(f,g,F)" by auto2
setup {* del_prfstep_thm @{thm homotopic_def} *}

definition id_homotopy :: "i \<Rightarrow> i" where [rewrite]:
  "id_homotopy(f) = f \<circ>\<^sub>m proj1_top(source_str(f),I)"

lemma id_is_homotopy:
  "continuous(f) \<Longrightarrow> is_homotopy(f,f,id_homotopy(f))" by auto2
setup {* add_forward_prfstep_cond @{thm id_is_homotopy} [with_term "id_homotopy(?f)"] *}

lemma homotopic_id [resolve]:
  "continuous(f) \<Longrightarrow> homotopic(f,f)"
@proof @have "is_homotopy(f,f,id_homotopy(f))" @qed

definition inv_homotopy :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "inv_homotopy(f,g,F) = F \<circ>\<^sub>m prod_top_map(id_mor(source_str(f)),interval_inv)"
setup {* register_wellform_data ("inv_homotopy(f,g,F)", ["is_homotopy(f,g,F)"]) *}

lemma inv_homotopy_eval [rewrite]:
  "\<langle>x,t\<rangle> \<in> source(inv_homotopy(f,g,F)) \<Longrightarrow> is_homotopy(f,g,F) \<Longrightarrow>
   inv_homotopy(f,g,F)`\<langle>x,t\<rangle> = F`\<langle>x, 1\<^sub>\<real> -\<^sub>\<real> t\<rangle>" by auto2

lemma inv_is_homotopy:
  "is_homotopy(f,g,F) \<Longrightarrow> is_homotopy(g,f,inv_homotopy(f,g,F))"
@proof @have "inv_homotopy(f,g,F) \<in> source_str(f) \<times>\<^sub>T I \<rightharpoonup>\<^sub>T target_str(f)" @qed
setup {* add_forward_prfstep_cond @{thm inv_is_homotopy} [with_term "inv_homotopy(?f,?g,?F)"] *}
setup {* del_prfstep_thm @{thm inv_homotopy_def} *}

lemma homotopic_inv [resolve]:
  "homotopic(f,g) \<Longrightarrow> homotopic(g,f)"
@proof
  @obtain F where "is_homotopy(f,g,F)"
  @have "is_homotopy(g,f,inv_homotopy(f,g,F))"
@qed

definition homotopy_lower_half :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "homotopy_lower_half(X,F) = F \<circ>\<^sub>m prod_top_map(id_mor(X),interval_lower)"
setup {* register_wellform_data ("homotopy_lower_half(X,F)", ["F \<in> X \<times>\<^sub>T I \<rightharpoonup>\<^sub>T target_str(F)"]) *}

lemma homotopy_lower_half_type [typing]:
  "is_top_space(X) \<Longrightarrow> F \<in> X \<times>\<^sub>T I \<rightharpoonup>\<^sub>T target_str(F) \<Longrightarrow>
   homotopy_lower_half(X,F) \<in> X \<times>\<^sub>T I1 \<rightharpoonup>\<^sub>T target_str(F)" by auto2
      
lemma homotopy_lower_half_eval [rewrite]:
  "is_top_space(X) \<Longrightarrow> \<langle>x,t\<rangle> \<in> source(F') \<Longrightarrow> F \<in> X \<times>\<^sub>T I \<rightharpoonup>\<^sub>T target_str(F) \<Longrightarrow>
   F' = homotopy_lower_half(X,F) \<Longrightarrow> F'`\<langle>x,t\<rangle> = F`\<langle>x, 2\<^sub>\<real> *\<^sub>\<real> t\<rangle>" by auto2
setup {* del_prfstep_thm @{thm homotopy_lower_half_def} *}
  
definition homotopy_upper_half :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "homotopy_upper_half(X,F) = F \<circ>\<^sub>m prod_top_map(id_mor(X),interval_upper)"
setup {* register_wellform_data ("homotopy_upper_half(X,F)", ["F \<in> X \<times>\<^sub>T I \<rightharpoonup>\<^sub>T target_str(F)"]) *}

lemma homotopy_upper_half_type [typing]:
  "is_top_space(X) \<Longrightarrow> F \<in> X \<times>\<^sub>T I \<rightharpoonup>\<^sub>T target_str(F) \<Longrightarrow>
   homotopy_upper_half(X,F) \<in> X \<times>\<^sub>T I2 \<rightharpoonup>\<^sub>T target_str(F)" by auto2
      
lemma homotopy_upper_half_eval [rewrite]:
  "is_top_space(X) \<Longrightarrow> \<langle>x,t\<rangle> \<in> source(F') \<Longrightarrow> F \<in> X \<times>\<^sub>T I \<rightharpoonup>\<^sub>T target_str(F) \<Longrightarrow>
   F' = homotopy_upper_half(X,F) \<Longrightarrow> F'`\<langle>x,t\<rangle> = F`\<langle>x, 2\<^sub>\<real> *\<^sub>\<real> t -\<^sub>\<real> 1\<^sub>\<real>\<rangle>" by auto2
setup {* del_prfstep_thm @{thm homotopy_upper_half_def} *}

definition compose_homotopy :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "compose_homotopy(f,g,h,F,G) = glue_morphism(source_str(f) \<times>\<^sub>T I,
     homotopy_lower_half(source_str(f),F), homotopy_upper_half(source_str(f),G))"
setup {* register_wellform_data ("compose_homotopy(f,g,h,F,G)",
  ["F \<in> homotopy_maps(f,g)", "G \<in> homotopy_maps(g,h)"]) *}

lemma I1_I2_inter [rewrite]: "X \<times> carrier(I1) \<inter> X \<times> carrier(I2) = X \<times> {1\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real>}" by auto2
lemma I1_I2_union [rewrite]: "X \<times> carrier(I1) \<union> X \<times> carrier(I2) = X \<times> carrier(I)" by auto2

lemma compose_is_homotopy:
  "is_homotopy(f,g,F) \<Longrightarrow> is_homotopy(g,h,G) \<Longrightarrow> is_homotopy(f,h,compose_homotopy(f,g,h,F,G))"
@proof
  @let "X = source_str(f)" "Y = target_str(f)"
  @have "compose_homotopy(f,g,h,F,G) \<in> X \<times>\<^sub>T I \<rightharpoonup>\<^sub>T Y"
@qed
setup {* add_forward_prfstep_cond @{thm compose_is_homotopy} [with_term "compose_homotopy(?f,?g,?h,?F,?G)"] *}

lemma compose_homotopy_eval [rewrite]:
  "is_homotopy(f,g,F) \<Longrightarrow> is_homotopy(g,h,G) \<Longrightarrow> H = compose_homotopy(f,g,h,F,G) \<Longrightarrow> 
   \<langle>x,t\<rangle> \<in> source(H) \<Longrightarrow> H`\<langle>x,t\<rangle> = (if t \<le>\<^sub>\<real> 1\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real> then F`\<langle>x, 2\<^sub>\<real> *\<^sub>\<real> t\<rangle> else G`\<langle>x, 2\<^sub>\<real> *\<^sub>\<real> t -\<^sub>\<real> 1\<^sub>\<real>\<rangle>)"
@proof
  @case "t \<le>\<^sub>\<real> 1\<^sub>\<real> /\<^sub>\<real> 2\<^sub>\<real>" @with @have "\<langle>x,t\<rangle> \<in> source(f) \<times> carrier(I1)" @end
@qed
setup {* del_prfstep_thm @{thm compose_homotopy_def} *}

lemma homotopic_trans [forward]:
  "homotopic(f,g) \<Longrightarrow> homotopic(g,h) \<Longrightarrow> homotopic(f,h)"
@proof
  @obtain F where "is_homotopy(f,g,F)"
  @obtain G where "is_homotopy(g,h,G)"
  @have "is_homotopy(f,h,compose_homotopy(f,g,h,F,G))"
@qed

lemma homotopy_maps_comp1 [backward]:
  "continuous(h) \<Longrightarrow> target_str(h) = source_str(f) \<Longrightarrow> is_homotopy(f,g,F) \<Longrightarrow>
   is_homotopy(f \<circ>\<^sub>m h, g \<circ>\<^sub>m h, F \<circ>\<^sub>m prod_top_map(h,id_mor(I)))" by auto2

lemma homotopic_comp1 [backward]:
  "continuous(h) \<Longrightarrow> target_str(h) = source_str(f) \<Longrightarrow> homotopic(f,g) \<Longrightarrow> homotopic(f \<circ>\<^sub>m h, g \<circ>\<^sub>m h)"
@proof
  @obtain F where "is_homotopy(f,g,F)"
  @have "is_homotopy(f \<circ>\<^sub>m h, g \<circ>\<^sub>m h, F \<circ>\<^sub>m prod_top_map(h,id_mor(I)))"
@qed

lemma homotopy_maps_comp2 [backward]:
  "continuous(h) \<Longrightarrow> target_str(f) = source_str(h) \<Longrightarrow> is_homotopy(f,g,F) \<Longrightarrow>
   is_homotopy(h \<circ>\<^sub>m f, h \<circ>\<^sub>m g, h \<circ>\<^sub>m F)" by auto2
    
lemma homotopic_comp2 [backward]:
  "continuous(h) \<Longrightarrow> target_str(f) = source_str(h) \<Longrightarrow> homotopic(f,g) \<Longrightarrow> homotopic(h \<circ>\<^sub>m f, h \<circ>\<^sub>m g)"
@proof
  @obtain F where "is_homotopy(f,g,F)"
  @have "is_homotopy(h \<circ>\<^sub>m f, h \<circ>\<^sub>m g, h \<circ>\<^sub>m F)"
@qed
    
section {* Homotopy equivalence between two spaces *}
  
definition homotopy_equiv_pair :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "homotopy_equiv_pair(f,g) \<longleftrightarrow> (continuous(f) \<and> continuous(g) \<and>
    source_str(f) = target_str(g) \<and> target_str(f) = source_str(g) \<and>
    homotopic(g \<circ>\<^sub>m f, id_mor(source_str(f))) \<and>
    homotopic(f \<circ>\<^sub>m g, id_mor(source_str(g))))"
  
lemma homotopy_equiv_pairI [backward]:
  "continuous(f) \<Longrightarrow> continuous(g) \<Longrightarrow> source_str(f) = target_str(g) \<Longrightarrow> target_str(f) = source_str(g) \<Longrightarrow>
   homotopic(g \<circ>\<^sub>m f, id_mor(source_str(f))) \<Longrightarrow> homotopic(f \<circ>\<^sub>m g, id_mor(source_str(g))) \<Longrightarrow>
   homotopy_equiv_pair(f, g)" by auto2

lemma homotopy_equiv_pairD [forward]:
  "homotopy_equiv_pair(f, g) \<Longrightarrow> continuous(f) \<and> continuous(g) \<and> source_str(f) = target_str(g) \<and>
   target_str(f) = source_str(g) \<and> homotopic(g \<circ>\<^sub>m f, id_mor(source_str(f))) \<and>
   homotopic(f \<circ>\<^sub>m g, id_mor(source_str(g)))" by auto2
setup {* del_prfstep_thm @{thm homotopy_equiv_pair_def} *}
  
lemma homotopy_equiv_pair_sym [forward]:
  "homotopy_equiv_pair(f,g) \<Longrightarrow> homotopy_equiv_pair(g,f)" by auto2
    
lemma homotopy_equiv_pair_id [resolve]:
  "is_top_space(X) \<Longrightarrow> homotopy_equiv_pair(id_mor(X),id_mor(X))" by auto2
  
definition homotopy_equiv_space :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "homotopy_equiv_space(X,Y) = {f \<in> X \<rightharpoonup>\<^sub>T Y. \<exists>g\<in>Y \<rightharpoonup>\<^sub>T X. homotopy_equiv_pair(f,g)}"

lemma homotopy_equiv_spaceI [forward]:
  "mor_form(f) \<Longrightarrow> mor_form(g) \<Longrightarrow> homotopy_equiv_pair(f,g) \<Longrightarrow>
   f \<in> homotopy_equiv_space(source_str(f),target_str(f))" by auto2

lemma homotopy_equiv_spaceD1 [forward]:
  "f \<in> homotopy_equiv_space(X,Y) \<Longrightarrow> f \<in> X \<rightharpoonup>\<^sub>T Y" by auto2
    
lemma homotopy_equiv_spaceD2 [backward]:
  "f \<in> homotopy_equiv_space(X,Y) \<Longrightarrow> \<exists>g\<in>Y \<rightharpoonup>\<^sub>T X. homotopy_equiv_pair(f,g)" by auto2
setup {* del_prfstep_thm @{thm homotopy_equiv_space_def} *}

definition homotopy_equivalent :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "homotopy_equivalent(X,Y) \<longleftrightarrow> (is_top_space(X) \<and> is_top_space(Y) \<and> homotopy_equiv_space(X,Y) \<noteq> \<emptyset>)"

lemma homotpy_equivalentI [forward]:
  "is_top_space(X) \<Longrightarrow> is_top_space(Y) \<Longrightarrow> f \<in> homotopy_equiv_space(X,Y) \<Longrightarrow> homotopy_equivalent(X,Y)" by auto2
    
lemma homotopy_equivalentD1 [forward]:
  "homotopy_equivalent(X,Y) \<Longrightarrow> is_top_space(X) \<and> is_top_space(Y)" by auto2
    
lemma homotopy_equivalentD2 [backward]:
  "homotopy_equivalent(X,Y) \<Longrightarrow> \<exists>f. f \<in> homotopy_equiv_space(X,Y)" by auto2
    
lemma homotopy_equivalentD2' [backward]:
  "homotopy_equivalent(X,Y) \<Longrightarrow> \<exists>f\<in>X\<rightharpoonup>\<^sub>TY. \<exists>g\<in>Y\<rightharpoonup>\<^sub>TX. homotopy_equiv_pair(f,g)" by auto2
setup {* del_prfstep_thm @{thm homotopy_equivalent_def} *}
  
lemma homotopy_equivalent_refl [resolve]:
  "is_top_space(X) \<Longrightarrow> homotopy_equivalent(X,X)"
@proof @have "homotopy_equiv_pair(id_mor(X),id_mor(X))" @qed
      
lemma homotopy_equivalent_sym [forward]:
  "homotopy_equivalent(X,Y) \<Longrightarrow> homotopy_equivalent(Y,X)"
@proof
  @obtain "f\<in>X\<rightharpoonup>\<^sub>TY" "g\<in>Y\<rightharpoonup>\<^sub>TX" where "homotopy_equiv_pair(f,g)"
@qed

lemma homotopy_equivalent_trans [forward]:
  "homotopy_equivalent(X,Y) \<Longrightarrow> homotopy_equivalent(Y,Z) \<Longrightarrow> homotopy_equivalent(X,Z)"
@proof
  @obtain "f\<in>X\<rightharpoonup>\<^sub>TY" "f'\<in>Y\<rightharpoonup>\<^sub>TX" where "homotopy_equiv_pair(f,f')"
  @obtain "g\<in>Y\<rightharpoonup>\<^sub>TZ" "g'\<in>Z\<rightharpoonup>\<^sub>TY" where "homotopy_equiv_pair(g,g')"
  @have "homotopy_equiv_pair(g \<circ>\<^sub>m f, f' \<circ>\<^sub>m g')" @with
    @have "homotopic((g \<circ>\<^sub>m f) \<circ>\<^sub>m (f' \<circ>\<^sub>m g'), id_mor(Z))" @with
      @have "homotopic(g \<circ>\<^sub>m (f \<circ>\<^sub>m f') \<circ>\<^sub>m g', g \<circ>\<^sub>m id_mor(Y) \<circ>\<^sub>m g')" @end
    @have "homotopic((f' \<circ>\<^sub>m g') \<circ>\<^sub>m (g \<circ>\<^sub>m f), id_mor(X))" @with
      @have "homotopic(f' \<circ>\<^sub>m (g' \<circ>\<^sub>m g) \<circ>\<^sub>m f, f' \<circ>\<^sub>m id_mor(Y) \<circ>\<^sub>m f)" @end
  @end
@qed

end