theory Union_Find_Func
imports "../Auto2_Main"
begin
  
section {* Partial equivalence relation *}
  
definition part_equiv :: "('a \<times> 'a) set \<Rightarrow> bool" where [rewrite]:
  "part_equiv R \<longleftrightarrow> sym R \<and> trans R"
setup {* add_property_const @{term part_equiv} *}

lemma part_equivI [forward]: "sym R \<Longrightarrow> trans R \<Longrightarrow> part_equiv R" by auto2
lemma part_equivD1 [forward]: "part_equiv R \<Longrightarrow> sym R" by auto2
lemma part_equivD2 [forward]: "part_equiv R \<Longrightarrow> trans R" by auto2
setup {* del_prfstep_thm_eqforward @{thm part_equiv_def} *}

subsection {* Combining two elements in a partial equivalence relation *}

definition per_union :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) set" where [rewrite]:
  "per_union R a b = R \<union> { (x,y). (x,a)\<in>R \<and> (b,y)\<in>R } \<union> { (x,y). (x,b)\<in>R \<and> (a,y)\<in>R }"

lemma per_union_memI1 [backward]:
  "(x, y) \<in> R \<Longrightarrow> (x, y) \<in> per_union R a b" by (simp add: per_union_def)
setup {* add_forward_prfstep_cond @{thm per_union_memI1} [with_term "per_union ?R ?a ?b"] *}

lemma per_union_memI2 [backward]:
  "(x, a) \<in> R \<Longrightarrow> (b, y) \<in> R \<Longrightarrow> (x, y) \<in> per_union R a b" by (simp add: per_union_def)

lemma per_union_memI3 [backward]:
  "(x, b) \<in> R \<Longrightarrow> (a, y) \<in> R \<Longrightarrow> (x, y) \<in> per_union R a b" by (simp add: per_union_def)

lemma per_union_memD:
  "(x, y) \<in> per_union R a b \<Longrightarrow> (x, y) \<in> R \<or> ((x, a) \<in> R \<and> (b, y) \<in> R) \<or> ((x, b) \<in> R \<and> (a, y) \<in> R)"
  by (simp add: per_union_def)
setup {* add_forward_prfstep_cond @{thm per_union_memD} [with_cond "?x \<noteq> ?y", with_filt (order_filter "x" "y")] *}
setup {* del_prfstep_thm @{thm per_union_def} *}

lemma per_union_is_trans [forward]:
  "trans R \<Longrightarrow> trans (per_union R a b)" by auto2

lemma per_union_is_part_equiv [forward]:
  "part_equiv R \<Longrightarrow> part_equiv (per_union R a b)" by auto2

section {* Representing a partial equivalence relation using rep_of array *}
  
function (domintros) rep_of where
  "rep_of l i = (if l ! i = i then i else rep_of l (l ! i))"
  by auto

setup {* register_wellform_data ("rep_of l i", ["i < length l"]) *}
setup {* add_backward_prfstep @{thm rep_of.domintros} *}
setup {* add_rewrite_rule @{thm rep_of.psimps} *}
setup {* add_prop_induct_rule @{thm rep_of.pinduct} *}

definition ufa_invar :: "nat list \<Rightarrow> bool" where [rewrite]:
  "ufa_invar l = (\<forall>i<length l. rep_of_dom (l, i) \<and> l ! i < length l)"
setup {* add_property_const @{term ufa_invar} *}

lemma ufa_invarD:
  "ufa_invar l \<Longrightarrow> i < length l \<Longrightarrow> rep_of_dom (l, i) \<and> l ! i < length l" by auto2
setup {* add_forward_prfstep_cond @{thm ufa_invarD} [with_term "?l ! ?i"] *}
setup {* del_prfstep_thm_eqforward @{thm ufa_invar_def} *}

lemma rep_of_id [rewrite]: "ufa_invar l \<Longrightarrow> i < length l \<Longrightarrow> l ! i = i \<Longrightarrow> rep_of l i = i" by auto2

lemma rep_of_iff [rewrite]:
  "ufa_invar l \<Longrightarrow> i < length l \<Longrightarrow> rep_of l i = (if l ! i = i then i else rep_of l (l ! i))" by auto2

lemma rep_of_min [rewrite]:
  "ufa_invar l \<Longrightarrow> i < length l \<Longrightarrow> l ! (rep_of l i) = rep_of l i"
@proof @prop_induct "rep_of_dom (l, i)" @qed

lemma rep_of_induct:
  "ufa_invar l \<and> i < length l \<Longrightarrow>
   \<forall>i<length l. l ! i = i \<longrightarrow> P l i \<Longrightarrow>
   \<forall>i<length l. l ! i \<noteq> i \<longrightarrow> P l (l ! i) \<longrightarrow> P l i \<Longrightarrow> P l i"
@proof @prop_induct "rep_of_dom (l, i)" @qed
setup {* add_prop_induct_rule @{thm rep_of_induct} *}

lemma rep_of_bound:
  "ufa_invar l \<Longrightarrow> i < length l \<Longrightarrow> rep_of l i < length l"
@proof @prop_induct "ufa_invar l \<and> i < length l" @qed
setup {* add_forward_prfstep_cond @{thm rep_of_bound} [with_term "rep_of ?l ?i"] *}

lemma rep_of_idem [rewrite]:
  "ufa_invar l \<Longrightarrow> i < length l \<Longrightarrow> rep_of l (rep_of l i) = rep_of l i" by auto2

lemma rep_of_idx [rewrite]: 
  "ufa_invar l \<Longrightarrow> i < length l \<Longrightarrow> rep_of l (l ! i) = rep_of l i" by auto2

definition ufa_\<alpha> :: "nat list \<Rightarrow> (nat \<times> nat) set" where [rewrite]:
  "ufa_\<alpha> l = {(x, y). x < length l \<and> y < length l \<and> rep_of l x = rep_of l y}"

lemma ufa_\<alpha>_memI [backward]:
  "x < length l \<Longrightarrow> y < length l \<Longrightarrow> rep_of l x = rep_of l y \<Longrightarrow> (x, y) \<in> ufa_\<alpha> l"
  by (simp add: ufa_\<alpha>_def)
setup {* add_forward_prfstep_cond @{thm ufa_\<alpha>_memI} [with_term "ufa_\<alpha> ?l"] *}
  
lemma ufa_\<alpha>_memD [forward]:
  "(x, y) \<in> ufa_\<alpha> l \<Longrightarrow> x < length l \<and> y < length l \<and> rep_of l x = rep_of l y"
  by (simp add: ufa_\<alpha>_def)
setup {* del_prfstep_thm @{thm ufa_\<alpha>_def} *}

lemma ufa_\<alpha>_equiv [forward]: "part_equiv (ufa_\<alpha> l)" by auto2

lemma ufa_\<alpha>_refl [rewrite]: "(i, i) \<in> ufa_\<alpha> l \<longleftrightarrow> i < length l" by auto2

lemma ufa_\<alpha>_dom [rewrite]: "x \<in> Domain (ufa_\<alpha> l) \<longleftrightarrow> x < length l"
  by (meson Domain.simps ufa_\<alpha>_memD ufa_\<alpha>_refl)

section {* Operations on rep_of array *}

lemma ufa_init_invar [resolve]: "ufa_invar [0..<n]" by auto2

lemma ufa_init_correct [rewrite]:
  "(x, y) \<in> ufa_\<alpha> [0..<n] \<longleftrightarrow> (x = y \<and> x < n)"
@proof @have "ufa_invar [0..<n]" @qed

definition ufa_union :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where [rewrite_bidir]:
  "ufa_union l x y = l[rep_of l x := rep_of l y]"
setup {* register_wellform_data ("ufa_union l x y", ["x < length l", "y < length l"]) *}

lemma ufa_union_length [rewrite]: "length (ufa_union l x y) = length l" by auto2

lemma ufa_union_invar:
  "ufa_invar l \<Longrightarrow> x < length l \<Longrightarrow> y < length l \<Longrightarrow> ufa_invar (ufa_union l x y)"
@proof
  @let "l' = ufa_union l x y"
  @have "\<forall>i<length l'. rep_of_dom (l', i) \<and> l' ! i < length l'" @with
    @prop_induct "ufa_invar l \<and> i < length l"
  @end
@qed
setup {* add_forward_prfstep_cond @{thm ufa_union_invar} [with_term "ufa_union ?l ?x ?y"] *}

lemma ufa_union_aux [rewrite]:
  "ufa_invar l \<Longrightarrow> x < length l \<Longrightarrow> y < length l \<Longrightarrow> l' = ufa_union l x y \<Longrightarrow>
   i < length l' \<Longrightarrow> rep_of l' i = (if rep_of l i = rep_of l x then rep_of l y else rep_of l i)"
@proof @prop_induct "ufa_invar l \<and> i < length l" @qed
  
lemma ufa_union_correct [rewrite]:
  "ufa_invar l \<Longrightarrow> a < length l \<Longrightarrow> b < length l \<Longrightarrow>
   ufa_\<alpha> (ufa_union l a b) = per_union (ufa_\<alpha> l) a b"
@proof
  @let "l' = ufa_union l a b"
  @have "\<forall>x y. (x,y) \<in> ufa_\<alpha> l' \<longleftrightarrow> (x,y) \<in> per_union (ufa_\<alpha> l) a b" @with
    @case "(x,y) \<in> ufa_\<alpha> l'" @with
      @case "rep_of l x = rep_of l a"
      @case "rep_of l y = rep_of l a"
    @end
  @end
@qed

definition ufa_compress :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where [rewrite_bidir]:
  "ufa_compress l x = l[x := rep_of l x]"
setup {* register_wellform_data ("ufa_compress l x", ["x < length l"]) *}

lemma ufa_compress_length [rewrite]: "length (ufa_compress l x) = length l" by auto2

lemma ufa_compress_invar:
  "ufa_invar l \<Longrightarrow> x < length l \<Longrightarrow> ufa_invar (ufa_compress l x)"
@proof
  @let "l' = ufa_compress l x"
  @have "\<forall>i<length l'. rep_of_dom (l', i) \<and> l' ! i < length l'" @with
    @prop_induct "ufa_invar l \<and> i < length l"
  @end
@qed
setup {* add_forward_prfstep_cond @{thm ufa_compress_invar} [with_term "ufa_compress ?l ?x"] *}
  
lemma ufa_compress_aux [rewrite]:
  "ufa_invar l \<Longrightarrow> x < length l \<Longrightarrow> l' = ufa_compress l x \<Longrightarrow> i < length l' \<Longrightarrow>
   rep_of (ufa_compress l x) i = rep_of l i"
@proof @prop_induct "ufa_invar l \<and> i < length l" @qed

lemma ufa_compress_correct [rewrite]:
  "ufa_invar l \<Longrightarrow> x < length l \<Longrightarrow> ufa_\<alpha> (ufa_compress l x) = ufa_\<alpha> l" by auto2

setup {* del_prfstep_thm @{thm rep_of_iff} *}
setup {* del_prfstep_thm @{thm rep_of.psimps} *}

end
