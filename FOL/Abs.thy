theory Abs
imports Field
begin

section {* Absolute value *}

definition abs :: "i \<Rightarrow> i \<Rightarrow> i"  ("\<bar>_\<bar>\<^sub>_" [0,91] 90) where [rewrite]:
  "\<bar>x\<bar>\<^sub>R = (if x \<ge>\<^sub>R \<zero>\<^sub>R then x else -\<^sub>R x)"
setup {* register_wellform_data ("\<bar>x\<bar>\<^sub>R", ["x \<in>. R"]) *}

setup {* add_gen_prfstep ("abs_case",
  [WithTerm @{term_pat "\<bar>?x\<bar>\<^sub>?R"}, CreateCase @{term_pat "?x \<ge>\<^sub>?R \<zero>\<^sub>?R"}]) *}

lemma abs_nonneg [rewrite]: "x \<ge>\<^sub>R \<zero>\<^sub>R \<Longrightarrow> \<bar>x\<bar>\<^sub>R = x" by auto2
lemma abs_neg [rewrite]: "is_ord_ring(R) \<Longrightarrow> x \<le>\<^sub>R \<zero>\<^sub>R \<Longrightarrow> \<bar>x\<bar>\<^sub>R = -\<^sub>R x" by auto2
lemma abs_mem [typing]: "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<bar>x\<bar>\<^sub>R \<in>. R" by auto2
setup {* del_prfstep_thm @{thm abs_def} *}

lemma abs_zero [rewrite]: "is_ord_ring(R) \<Longrightarrow> \<bar>\<zero>\<^sub>R\<bar>\<^sub>R = \<zero>\<^sub>R" by auto2
lemma abs_minus [rewrite]: "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<bar>-\<^sub>R x\<bar>\<^sub>R = \<bar>x\<bar>\<^sub>R" by auto2
lemma abs_not_less_zero [resolve]: "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<bar>x\<bar>\<^sub>R \<ge>\<^sub>R \<zero>\<^sub>R" by auto2
lemma abs_le_zero [forward]: "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<bar>x\<bar>\<^sub>R \<le>\<^sub>R \<zero>\<^sub>R \<Longrightarrow> x = \<zero>\<^sub>R" by auto2
lemma abs_positive [rewrite]: "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<bar>x\<bar>\<^sub>R >\<^sub>R \<zero>\<^sub>R \<longleftrightarrow> x \<noteq> \<zero>\<^sub>R" by auto2
lemma abs_mult [rewrite]: "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> \<bar>x *\<^sub>R y\<bar>\<^sub>R = \<bar>x\<bar>\<^sub>R *\<^sub>R \<bar>y\<bar>\<^sub>R" by auto2
lemma abs_inverse [rewrite]: "is_ord_field(R) \<Longrightarrow> x \<in> units(R) \<Longrightarrow> \<bar>inv(R,x)\<bar>\<^sub>R = inv(R,\<bar>x\<bar>\<^sub>R)" by auto2
lemma abs_div [rewrite]: "is_ord_field(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in> units(R) \<Longrightarrow> \<bar>x /\<^sub>R y\<bar>\<^sub>R = \<bar>x\<bar>\<^sub>R /\<^sub>R \<bar>y\<bar>\<^sub>R"
  @proof @have "x /\<^sub>R y = x *\<^sub>R inv(R,y)" @then @have "\<bar>x\<bar>\<^sub>R /\<^sub>R \<bar>y\<bar>\<^sub>R = \<bar>x\<bar>\<^sub>R *\<^sub>R inv(R,\<bar>y\<bar>\<^sub>R)" @qed

lemma abs_ge_cases [forward]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> r \<in>. R \<Longrightarrow> \<bar>x\<bar>\<^sub>R \<ge>\<^sub>R r \<Longrightarrow> x >\<^sub>R -\<^sub>R r \<Longrightarrow> x \<ge>\<^sub>R r"
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> r \<in>. R \<Longrightarrow> \<bar>x\<bar>\<^sub>R \<ge>\<^sub>R r \<Longrightarrow> x <\<^sub>R r \<Longrightarrow> x \<le>\<^sub>R -\<^sub>R r" by auto2+

lemma abs_gt_cases [forward]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> r \<in>. R \<Longrightarrow> \<bar>x\<bar>\<^sub>R >\<^sub>R r \<Longrightarrow> x \<ge>\<^sub>R -\<^sub>R r \<Longrightarrow> x >\<^sub>R r"
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> r \<in>. R \<Longrightarrow> \<bar>x\<bar>\<^sub>R >\<^sub>R r \<Longrightarrow> x \<le>\<^sub>R r \<Longrightarrow> x <\<^sub>R -\<^sub>R r" by auto2+

lemma abs_le [resolve]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<bar>x\<bar>\<^sub>R \<le>\<^sub>R r \<Longrightarrow> x \<le>\<^sub>R r"
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<bar>x\<bar>\<^sub>R \<le>\<^sub>R r \<Longrightarrow> x \<ge>\<^sub>R -\<^sub>R r" by auto2+

lemma abs_less [resolve]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<bar>x\<bar>\<^sub>R <\<^sub>R r \<Longrightarrow> x <\<^sub>R r"
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<bar>x\<bar>\<^sub>R <\<^sub>R r \<Longrightarrow> x >\<^sub>R -\<^sub>R r" by auto2+

lemma abs_diff_nonneg [rewrite]:
  "is_ord_ring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> a \<ge>\<^sub>R b \<Longrightarrow> \<bar>a -\<^sub>R b\<bar>\<^sub>R = a -\<^sub>R b" by auto2

setup {* del_prfstep "abs_case" *}
  
lemma abs_diff_sym [rewrite]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> \<bar>x -\<^sub>R y\<bar>\<^sub>R = \<bar>y -\<^sub>R x\<bar>\<^sub>R"
@proof @have "y -\<^sub>R x = -\<^sub>R (x -\<^sub>R y)" @qed

lemma abs_sum [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> \<bar>x\<bar>\<^sub>R \<le>\<^sub>R s \<Longrightarrow> \<bar>y\<bar>\<^sub>R \<le>\<^sub>R t \<Longrightarrow> \<bar>x +\<^sub>R y\<bar>\<^sub>R \<le>\<^sub>R s +\<^sub>R t"
@proof
  @have "x +\<^sub>R y \<le>\<^sub>R s +\<^sub>R t" @with @have "x \<le>\<^sub>R s" @end
  @have "x +\<^sub>R y \<ge>\<^sub>R -\<^sub>R s +\<^sub>R -\<^sub>R t" @with @have "x \<ge>\<^sub>R -\<^sub>R s" @end
@qed
      
lemma abs_sum_strict1 [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> \<bar>x\<bar>\<^sub>R <\<^sub>R s \<Longrightarrow> \<bar>y\<bar>\<^sub>R \<le>\<^sub>R t \<Longrightarrow> \<bar>x +\<^sub>R y\<bar>\<^sub>R <\<^sub>R s +\<^sub>R t"
@proof
  @have "x +\<^sub>R y <\<^sub>R s +\<^sub>R t" @with @have "x <\<^sub>R s" @end
  @have "x +\<^sub>R y >\<^sub>R -\<^sub>R s +\<^sub>R -\<^sub>R t" @with @have "x >\<^sub>R -\<^sub>R s" @end
@qed

lemma abs_sum_strict2 [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> \<bar>x\<bar>\<^sub>R \<le>\<^sub>R s \<Longrightarrow> \<bar>y\<bar>\<^sub>R <\<^sub>R t \<Longrightarrow> \<bar>x +\<^sub>R y\<bar>\<^sub>R <\<^sub>R s +\<^sub>R t"
@proof
  @have "x +\<^sub>R y <\<^sub>R s +\<^sub>R t" @with @have "x \<le>\<^sub>R s" @end
  @have "x +\<^sub>R y >\<^sub>R -\<^sub>R s +\<^sub>R -\<^sub>R t" @with @have "x \<ge>\<^sub>R -\<^sub>R s" @end
@qed

lemma abs_sum_half1 [backward1, backward2]:
  "is_ord_field(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> r \<in>. R \<Longrightarrow> \<bar>x\<bar>\<^sub>R <\<^sub>R r /\<^sub>R 2\<^sub>R \<Longrightarrow> \<bar>y\<bar>\<^sub>R <\<^sub>R r /\<^sub>R 2\<^sub>R \<Longrightarrow> \<bar>x +\<^sub>R y\<bar>\<^sub>R <\<^sub>R r"
@proof @have "r = r /\<^sub>R 2\<^sub>R +\<^sub>R r /\<^sub>R 2\<^sub>R" @qed

lemma abs_cancel_diff [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow>
   \<bar>x -\<^sub>R y\<bar>\<^sub>R \<le>\<^sub>R s \<Longrightarrow> \<bar>y -\<^sub>R z\<bar>\<^sub>R \<le>\<^sub>R t \<Longrightarrow> \<bar>x -\<^sub>R z\<bar>\<^sub>R \<le>\<^sub>R s +\<^sub>R t"
@proof @have "x -\<^sub>R z = (x -\<^sub>R y) +\<^sub>R (y -\<^sub>R z)" @qed

lemma abs_cancel_diff_strict1 [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow>
   \<bar>x -\<^sub>R y\<bar>\<^sub>R <\<^sub>R s \<Longrightarrow> \<bar>y -\<^sub>R z\<bar>\<^sub>R \<le>\<^sub>R t \<Longrightarrow> \<bar>x -\<^sub>R z\<bar>\<^sub>R <\<^sub>R s +\<^sub>R t"
@proof @have "x -\<^sub>R z = (x -\<^sub>R y) +\<^sub>R (y -\<^sub>R z)" @qed

lemma abs_cancel_diff_strict2 [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow>
   \<bar>x -\<^sub>R y\<bar>\<^sub>R <\<^sub>R s \<Longrightarrow> \<bar>y -\<^sub>R z\<bar>\<^sub>R <\<^sub>R t \<Longrightarrow> \<bar>x -\<^sub>R z\<bar>\<^sub>R <\<^sub>R s +\<^sub>R t" by auto2

lemma abs_cancel_diff_half1 [backward1, backward2]:
  "is_ord_field(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow> r \<in>. R \<Longrightarrow>
   \<bar>x -\<^sub>R y\<bar>\<^sub>R <\<^sub>R r /\<^sub>R 2\<^sub>R \<Longrightarrow> \<bar>y -\<^sub>R z\<bar>\<^sub>R <\<^sub>R r /\<^sub>R 2\<^sub>R \<Longrightarrow> \<bar>x -\<^sub>R z\<bar>\<^sub>R <\<^sub>R r"
@proof @have "r = r /\<^sub>R 2\<^sub>R +\<^sub>R r /\<^sub>R 2\<^sub>R" @qed

lemma abs_prod_upper_bound [backward1, backward2]:
  "is_ord_field(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> \<bar>x\<bar>\<^sub>R <\<^sub>R s \<Longrightarrow> \<bar>y\<bar>\<^sub>R <\<^sub>R t \<Longrightarrow> \<bar>x *\<^sub>R y\<bar>\<^sub>R <\<^sub>R s *\<^sub>R t"
@proof @contradiction @have "\<bar>x *\<^sub>R y\<bar>\<^sub>R \<noteq> s *\<^sub>R t" @qed

lemma abs_prod_upper_bound2 [backward2]:
  "is_ord_field(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> s \<in>. R \<Longrightarrow> t \<in> units(R) \<Longrightarrow>
   \<bar>x\<bar>\<^sub>R <\<^sub>R s /\<^sub>R t \<Longrightarrow> \<bar>y\<bar>\<^sub>R <\<^sub>R t \<Longrightarrow> \<bar>x *\<^sub>R y\<bar>\<^sub>R <\<^sub>R s"
@proof @have "s = (s /\<^sub>R t) *\<^sub>R t" @qed

lemma abs_prod_upper_bound2' [backward2]:
  "is_ord_field(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> s \<in>. R \<Longrightarrow> t \<in> units(R) \<Longrightarrow>
   \<bar>x\<bar>\<^sub>R <\<^sub>R s /\<^sub>R t \<Longrightarrow> \<bar>y\<bar>\<^sub>R <\<^sub>R t \<Longrightarrow> \<bar>y *\<^sub>R x\<bar>\<^sub>R <\<^sub>R s"
@proof @have "x *\<^sub>R y = y *\<^sub>R x" @qed

lemma abs_prod_lower_bound [backward1]:
  "is_ord_field(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> s >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> t >\<^sub>R \<zero>\<^sub>R \<Longrightarrow>
   \<bar>x\<bar>\<^sub>R >\<^sub>R s \<Longrightarrow> \<bar>y\<bar>\<^sub>R >\<^sub>R t \<Longrightarrow> \<bar>x *\<^sub>R y\<bar>\<^sub>R >\<^sub>R s *\<^sub>R t" by auto2
  
lemma abs_div_upper_bound [backward2]:
  "is_ord_field(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> \<bar>x\<bar>\<^sub>R <\<^sub>R a \<Longrightarrow> \<bar>y\<bar>\<^sub>R >\<^sub>R b \<and> b >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> \<bar>x /\<^sub>R y\<bar>\<^sub>R <\<^sub>R a /\<^sub>R b"
@proof @have "\<bar>x\<bar>\<^sub>R *\<^sub>R inv(R,\<bar>y\<bar>\<^sub>R) <\<^sub>R a *\<^sub>R inv(R,b)" @qed
      
lemma abs_div_upper_bound2 [backward2]:
  "is_ord_field(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in> units(R) \<Longrightarrow> s \<in>. R \<Longrightarrow>
   \<bar>x\<bar>\<^sub>R <\<^sub>R s *\<^sub>R t \<Longrightarrow> \<bar>y\<bar>\<^sub>R >\<^sub>R t \<and> t >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> \<bar>x /\<^sub>R y\<bar>\<^sub>R <\<^sub>R s"
@proof @have "s = s *\<^sub>R t /\<^sub>R t" @qed

(* Bounds on Abs in terms of components. *)
lemma abs_sum_bound [resolve]:
  "is_ord_ring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> \<bar>a +\<^sub>R b\<bar>\<^sub>R \<le>\<^sub>R \<bar>a\<bar>\<^sub>R +\<^sub>R \<bar>b\<bar>\<^sub>R"
@proof @have "\<bar>a\<bar>\<^sub>R \<le>\<^sub>R \<bar>a\<bar>\<^sub>R" @qed

lemma abs_diff_to_abs_bound [resolve]:
  "is_ord_field(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> c \<in>. R \<Longrightarrow> \<bar>a -\<^sub>R b\<bar>\<^sub>R <\<^sub>R c \<Longrightarrow> \<bar>a\<bar>\<^sub>R <\<^sub>R \<bar>b\<bar>\<^sub>R +\<^sub>R c"
@proof @have "\<bar>b +\<^sub>R (a -\<^sub>R b)\<bar>\<^sub>R \<le>\<^sub>R \<bar>b\<bar>\<^sub>R +\<^sub>R \<bar>a -\<^sub>R b\<bar>\<^sub>R" @qed

(* Bounds on differences to averages *)
setup {* add_rewrite_rule @{thm avg_def} *}
lemma avg_diff [rewrite]:
  "is_ord_field(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> \<bar>a -\<^sub>R avg(R,a,b)\<bar>\<^sub>R = \<bar>a -\<^sub>R b\<bar>\<^sub>R /\<^sub>R 2\<^sub>R"
@proof
  @case "a \<le>\<^sub>R b" @with
    @have "a \<le>\<^sub>R avg(R,a,b)" @then @have "(a +\<^sub>R b) /\<^sub>R 2\<^sub>R -\<^sub>R a = (b -\<^sub>R a) /\<^sub>R 2\<^sub>R" @end
  @case "a \<ge>\<^sub>R b" @with
    @have "a \<ge>\<^sub>R avg(R,a,b)" @then @have "a -\<^sub>R (a +\<^sub>R b) /\<^sub>R 2\<^sub>R = (a -\<^sub>R b) /\<^sub>R 2\<^sub>R" @end
@qed

lemma avg_diff2 [rewrite]:
  "is_ord_field(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> \<bar>b -\<^sub>R avg(R,a,b)\<bar>\<^sub>R = \<bar>a -\<^sub>R b\<bar>\<^sub>R /\<^sub>R 2\<^sub>R"
@proof @have "avg(R,a,b) = avg(R,b,a)" @qed
setup {* del_prfstep_thm @{thm avg_def} *}

(* Two redundancies *)
setup {* add_gen_prfstep ("shadow_abs_upper_triv",
  [WithProperty @{term_pat "is_ord_ring(?R)"},
   WithFact @{term_pat "\<bar>?x -\<^sub>?R ?x\<bar>\<^sub>R <\<^sub>?R ?r"},
   WithFact @{term_pat "?r >\<^sub>?R \<zero>\<^sub>?R"}, ShadowFirst]) *}
setup {* add_gen_prfstep ("shadow_abs_upper_sym",
  [WithProperty @{term_pat "is_ord_ring(?R)"},
   WithFact @{term_pat "\<bar>?x -\<^sub>?R ?y\<bar>\<^sub>?R <\<^sub>?R ?r"},
   WithFact @{term_pat "\<bar>?y -\<^sub>?R ?x\<bar>\<^sub>?R <\<^sub>?R ?r"}, ShadowSecond]) *}

end
