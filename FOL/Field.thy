theory Field
imports Ring
begin

section {* Fields *}

definition is_field :: "i \<Rightarrow> o" where [rewrite]:
  "is_field(R) \<longleftrightarrow> (is_comm_ring(R) \<and> (\<forall>x\<in>.R. x \<noteq> \<zero>\<^sub>R \<longleftrightarrow> x \<in> units(R)))"
setup {* add_property_const @{term is_field} *}
  
lemma is_fieldD [forward]:
  "is_field(R) \<Longrightarrow> is_comm_ring(R)"
  "is_field(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> x \<noteq> \<zero>\<^sub>R \<Longrightarrow> x \<in> units(R)"
  "is_field(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> x \<notin> units(R) \<Longrightarrow> x = 0\<^sub>R" by auto2+
    
lemma is_fieldD2 [resolve]:
  "is_field(R) \<Longrightarrow> \<zero>\<^sub>R \<notin> units(R)" by auto2

lemma is_fieldI [backward1]:
  "is_comm_ring(R) \<Longrightarrow> \<forall>x\<in>.R. x \<noteq> \<zero>\<^sub>R \<longrightarrow> f(x) \<in>. R \<Longrightarrow>
   \<forall>x\<in>.R. x \<noteq> \<zero>\<^sub>R \<longrightarrow> x *\<^sub>R f(x) = \<one>\<^sub>R \<Longrightarrow> is_field(R)" by auto2
  
lemma is_field_ring_prop [forward]:
  "is_ring_raw(H) \<Longrightarrow> is_field(G) \<Longrightarrow> eq_str_ring(G,H) \<Longrightarrow> is_field(H)" by auto2
setup {* del_prfstep_thm @{thm is_field_def} *}

lemma field_is_integral_domain [forward]:
  "is_field(R) \<Longrightarrow> integral_domain(R)"
@proof
  @have "\<forall>x\<in>.R. \<forall>y\<in>.R. x *\<^sub>R y = \<zero>\<^sub>R \<longrightarrow> x = \<zero>\<^sub>R \<or> y = \<zero>\<^sub>R" @with
    @contradiction @have "x *\<^sub>R y \<in> units(R)" @end
@qed

section {* Ordered fields *}
  
definition is_ord_field :: "i \<Rightarrow> o" where [rewrite]:
  "is_ord_field(R) \<longleftrightarrow> (is_ord_ring(R) \<and> is_field(R))"
setup {* add_property_const @{term is_ord_field} *}
  
lemma is_ord_fieldD [forward]:
  "is_ord_field(R) \<Longrightarrow> is_ord_ring(R)"
  "is_ord_field(R) \<Longrightarrow> is_field(R)" by auto2+
    
lemma is_ord_fieldI [forward]:
  "is_ord_ring(R) \<Longrightarrow> is_field(R) \<Longrightarrow> is_ord_field(R)" by auto2
setup {* del_prfstep_thm @{thm is_ord_field_def} *}

lemma is_ord_field_prop [forward]:
  "is_ord_field(R) \<Longrightarrow> is_ord_ring_raw(S) \<Longrightarrow> eq_str_ord_ring(R,S) \<Longrightarrow> is_ord_field(S)" by auto2

lemma ord_field_inv_sign [backward]:
  "is_ord_field(R) \<Longrightarrow> x >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> inv(R,x) >\<^sub>R \<zero>\<^sub>R"
@proof @have "x *\<^sub>R inv(R,x) = \<one>\<^sub>R" @have "\<one>\<^sub>R >\<^sub>R \<zero>\<^sub>R" @qed
setup {* add_forward_prfstep_cond @{thm ord_field_inv_sign} [with_term "inv(?R,?x)"] *}

lemma ord_field_inv_sign2 [backward]:
  "is_ord_field(R) \<Longrightarrow> x <\<^sub>R \<zero>\<^sub>R \<Longrightarrow> inv(R,x) <\<^sub>R \<zero>\<^sub>R"
@proof @have "inv(R,-\<^sub>R x) = -\<^sub>R inv(R,x)" @qed
setup {* add_forward_prfstep_cond @{thm ord_field_inv_sign2} [with_term "inv(?R,?x)"] *}

lemma ord_field_inv_le [backward2]:
  "is_ord_field(R) \<Longrightarrow> \<zero>\<^sub>R <\<^sub>R a \<Longrightarrow> a \<le>\<^sub>R b \<Longrightarrow> inv(R,a) \<ge>\<^sub>R inv(R,b)"
@proof @case "inv(R,a) <\<^sub>R inv(R,b)" @with @have "inv(R,a) *\<^sub>R a <\<^sub>R inv(R,b) *\<^sub>R b" @end @qed

lemma ord_field_inv_lt [backward2]:
  "is_ord_field(R) \<Longrightarrow> \<zero>\<^sub>R <\<^sub>R a \<Longrightarrow> a <\<^sub>R b \<Longrightarrow> inv(R,a) >\<^sub>R inv(R,b)"
@proof @case "inv(R,a) \<le>\<^sub>R inv(R,b)" @with @have "inv(R,a) *\<^sub>R a <\<^sub>R inv(R,b) *\<^sub>R b" @end @qed

lemma ord_field_inv_le' [backward1]:
  "is_ord_field(R) \<Longrightarrow> x >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> y >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> x >\<^sub>R inv(R,y) \<Longrightarrow> y >\<^sub>R inv(R,x)"
@proof @have "x = inv(R,inv(R,x))" @qed

lemma ord_field_div_sign [backward1, backward2]:
  "is_ord_field(R) \<Longrightarrow> x >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> y >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> x /\<^sub>R y >\<^sub>R \<zero>\<^sub>R"
@proof @have "x /\<^sub>R y = x *\<^sub>R inv(R,y)" @qed
setup {* add_forward_prfstep_cond @{thm ord_field_div_sign} [with_term "?x /\<^sub>?R ?y"] *}

lemma ord_field_div_sign2 [forward]:
  "is_ord_field(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in> units(R) \<Longrightarrow> x /\<^sub>R y >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> y >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> x >\<^sub>R \<zero>\<^sub>R"
@proof @have "x /\<^sub>R y = x *\<^sub>R inv(R,y)" @qed
    
lemma ord_field_divide_le [backward]:
  "is_ord_field(R) \<Longrightarrow> c >\<^sub>R 0\<^sub>R \<Longrightarrow> a \<le>\<^sub>R b \<Longrightarrow> a /\<^sub>R c \<le>\<^sub>R b /\<^sub>R c"
@proof @have "a /\<^sub>R c = a *\<^sub>R inv(R,c)" @have "b /\<^sub>R c = b *\<^sub>R inv(R,c)" @qed

lemma ord_field_divide_less [backward]:
  "is_ord_field(R) \<Longrightarrow> c >\<^sub>R 0\<^sub>R \<Longrightarrow> a <\<^sub>R b \<Longrightarrow> a /\<^sub>R c <\<^sub>R b /\<^sub>R c"
@proof @have "a *\<^sub>R inv(R,c) <\<^sub>R b *\<^sub>R inv(R,c)" @qed

lemma ord_field_divide_less2 [backward1]:
  "is_ord_field(R) \<Longrightarrow> c \<in>. R \<Longrightarrow> a >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> b >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> inv(R,a) <\<^sub>R c /\<^sub>R b \<Longrightarrow> b <\<^sub>R a *\<^sub>R c"
@proof @have "inv(R,a) *\<^sub>R (a *\<^sub>R b) <\<^sub>R (c /\<^sub>R b) *\<^sub>R (a *\<^sub>R b)" @qed

lemma ord_field_divide_le2 [backward1]:
  "is_ord_field(R) \<Longrightarrow> b \<in>. R \<Longrightarrow> c >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> a \<le>\<^sub>R b /\<^sub>R c \<Longrightarrow> a *\<^sub>R c \<le>\<^sub>R b"
@proof @have "a *\<^sub>R c \<le>\<^sub>R b /\<^sub>R c *\<^sub>R c" @qed

lemma ord_field_divide_le2' [backward1]:
  "is_ord_field(R) \<Longrightarrow> b \<in>. R \<Longrightarrow> c >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> a \<le>\<^sub>R b /\<^sub>R c \<Longrightarrow> c *\<^sub>R a \<le>\<^sub>R b"
@proof @have "a *\<^sub>R c \<le>\<^sub>R b /\<^sub>R c *\<^sub>R c" @qed

lemma ord_field_divide_le3 [backward1]:
  "is_ord_field(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> c >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> a *\<^sub>R c \<le>\<^sub>R b \<Longrightarrow> a \<le>\<^sub>R b /\<^sub>R c"
@proof @have "a *\<^sub>R c \<le>\<^sub>R b /\<^sub>R c *\<^sub>R c" @qed

lemma ord_field_divide_le4 [backward1]:
  "is_ord_field(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> c >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> c *\<^sub>R a \<le>\<^sub>R b \<Longrightarrow> a \<le>\<^sub>R b /\<^sub>R c"
@proof @have "a *\<^sub>R c = c *\<^sub>R a" @qed

lemma ord_field_divide_le5 [backward1]:
  "is_ord_field(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> c >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> c *\<^sub>R a \<ge>\<^sub>R b \<Longrightarrow> a \<ge>\<^sub>R b /\<^sub>R c"
@proof @have "a *\<^sub>R c \<ge>\<^sub>R b /\<^sub>R c *\<^sub>R c" @qed

lemma ord_field_divide_less4 [backward1]:
  "is_ord_field(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> c >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> c *\<^sub>R a <\<^sub>R b \<Longrightarrow> a <\<^sub>R b /\<^sub>R c"
@proof @have "a *\<^sub>R c <\<^sub>R b /\<^sub>R c *\<^sub>R c" @qed

lemma ord_field_divide_less4' [backward1]:
  "is_ord_field(R) \<Longrightarrow> b \<in>. R \<Longrightarrow> c >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> a \<ge>\<^sub>R b /\<^sub>R c \<Longrightarrow> c *\<^sub>R a \<ge>\<^sub>R b"
@proof @have "a *\<^sub>R c \<ge>\<^sub>R b /\<^sub>R c *\<^sub>R c" @qed

lemma ord_field_divide_less5 [backward1]:
  "is_ord_field(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> c >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> c *\<^sub>R a >\<^sub>R b \<Longrightarrow> a >\<^sub>R b /\<^sub>R c"
@proof @have "a *\<^sub>R c >\<^sub>R b /\<^sub>R c *\<^sub>R c" @qed
    
lemma ord_field_divide_less6 [backward1]:
  "is_ord_field(R) \<Longrightarrow> c \<in>. R \<Longrightarrow> d \<in>. R \<Longrightarrow> b >\<^sub>R 0\<^sub>R \<Longrightarrow> d <\<^sub>R c /\<^sub>R b \<Longrightarrow> c >\<^sub>R d *\<^sub>R b"
@proof @have "d *\<^sub>R b <\<^sub>R c /\<^sub>R b *\<^sub>R b" @qed

lemma ord_field_quotient_less [backward]:
  "is_ord_field(R) \<Longrightarrow> a \<ge>\<^sub>R 0\<^sub>R \<Longrightarrow> b \<ge>\<^sub>R 1\<^sub>R \<Longrightarrow> a /\<^sub>R b \<le>\<^sub>R a"
@proof @have "(a /\<^sub>R b) *\<^sub>R b = a *\<^sub>R 1\<^sub>R" @case "(a /\<^sub>R b) *\<^sub>R b >\<^sub>R a *\<^sub>R b" @qed

section {* Fields of characteristic zero *}

lemma ord_field_char_zero [backward]:
  "is_ord_field(R) \<Longrightarrow> n \<in> nat \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> of_nat(R,n) \<in> units(R)"
@proof @have "of_nat(R,n) >\<^sub>R \<zero>\<^sub>R" @qed

lemma ord_field_exists_half [backward]:
  "is_ord_field(R) \<Longrightarrow> r >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> \<exists>s. s >\<^sub>R \<zero>\<^sub>R \<and> r = s +\<^sub>R s"
@proof @have "r = r /\<^sub>R 2\<^sub>R +\<^sub>R r /\<^sub>R 2\<^sub>R" @qed

lemma ord_field_exists_sum2 [backward]:
  "is_ord_field(R) \<Longrightarrow> r >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> \<exists>s t. s >\<^sub>R \<zero>\<^sub>R \<and> t >\<^sub>R \<zero>\<^sub>R \<and> r = s +\<^sub>R t"
@proof @have "r = r /\<^sub>R 2\<^sub>R +\<^sub>R r /\<^sub>R 2\<^sub>R" @qed

section {* Archimedean Fields *}
  
definition is_archimedean :: "i \<Rightarrow> o" where [rewrite]:
  "is_archimedean(R) \<longleftrightarrow> (is_ord_ring(R) \<and> (\<forall>x\<in>.R. \<exists>n\<in>nat. of_nat(R,n) \<ge>\<^sub>R x))"
setup {* add_property_const @{term is_archimedean} *}

lemma is_archimedeanI [forward]:
  "is_ord_ring(R) \<Longrightarrow> \<forall>x\<in>.R. \<exists>n\<in>nat. of_nat(R,n) \<ge>\<^sub>R x \<Longrightarrow> is_archimedean(R)" by auto2
    
lemma is_archimedeanI_pos [forward]:
  "is_ord_ring(R) \<Longrightarrow> \<forall>x >\<^sub>R 0\<^sub>R. \<exists>n\<in>nat. of_nat(R,n) \<ge>\<^sub>R x \<Longrightarrow> is_archimedean(R)" by auto2

lemma is_archimedeanD1 [forward]: "is_archimedean(R) \<Longrightarrow> is_ord_ring(R)" by auto2

lemma is_archimedeanD2 [backward]:
  "is_archimedean(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<exists>n\<in>nat. of_nat(R,n) \<ge>\<^sub>R x" by auto2
setup {* del_prfstep_thm @{thm is_archimedean_def} *}
  
lemma is_archimedeanD_greater [backward]:
  "is_archimedean(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<exists>n\<in>nat. of_nat(R,n) >\<^sub>R x"
@proof
  @obtain "n\<in>nat" where "of_nat(R,n) \<ge>\<^sub>R x"
  @have "of_nat(R, n +\<^sub>\<nat> 1) >\<^sub>R x"
@qed

lemma is_archimedeanD_nat_inverse_less [backward]:
  "is_archimedean(R) \<Longrightarrow> is_field(R) \<Longrightarrow> x >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> \<exists>n>\<^sub>\<nat>0. inv(R,of_nat(R,n)) <\<^sub>R x"
@proof
  @obtain "n\<in>nat" where "of_nat(R,n) >\<^sub>R inv(R,x)"
  @obtain n' where "n'>\<^sub>\<nat>0" "n' = max(\<nat>,n,1)"
  @have "of_nat(R,n') >\<^sub>R inv(R,x)"
@qed

lemma is_archimedeanD_nat_inverse_less_plus1 [backward]:
  "is_archimedean(R) \<Longrightarrow> is_field(R) \<Longrightarrow> x >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> \<exists>n\<in>nat. inv(R,of_nat(R,n +\<^sub>\<nat> 1)) <\<^sub>R x"
@proof
  @obtain n where "n>\<^sub>\<nat>0" "inv(R,of_nat(R,n)) <\<^sub>R x" @have "n \<ge>\<^sub>\<nat> 1"
  @have "n -\<^sub>\<nat> 1 \<in> nat"
@qed

lemma is_archimedeanD_quotient [backward2]:
  "is_archimedean(R) \<Longrightarrow> is_ord_field(R) \<Longrightarrow> b \<in>. R \<Longrightarrow> a >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> \<exists>n\<in>.\<nat>. of_nat(R,n) *\<^sub>R a >\<^sub>R b"
@proof
  @case "b \<le>\<^sub>R \<zero>\<^sub>R" @with @have "of_nat(R,1) *\<^sub>R a >\<^sub>R b" @end
  @obtain n where "n>\<^sub>\<nat>0" "inv(R,of_nat(R,n)) <\<^sub>R a /\<^sub>R b"
@qed
      
lemma power_two_unbounded [backward]:
  "is_archimedean(R) \<Longrightarrow> M \<in>. R \<Longrightarrow> \<exists>n\<in>nat. 2\<^sub>R ^\<^sub>R n >\<^sub>R M"
@proof
  @obtain "n\<in>nat" where "of_nat(R,n) >\<^sub>R M" @have "2\<^sub>R ^\<^sub>R n >\<^sub>R of_nat(R,n)"
@qed

section {* Averages *}

definition avg :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "avg(R,a,b) = (a +\<^sub>R b) /\<^sub>R 2\<^sub>R"
setup {* register_wellform_data ("avg(R,a,b)", ["a \<in>. R", "b \<in>. R"]) *}

lemma avg_type [typing]: "is_ord_field(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> avg(R,a,b) \<in>. R" by auto2

lemma avg_le [backward]: "is_ord_field(R) \<Longrightarrow> a \<le>\<^sub>R b \<Longrightarrow> a \<le>\<^sub>R avg(R,a,b)"
@proof @have "a +\<^sub>R a \<le>\<^sub>R a +\<^sub>R b" @have "a +\<^sub>R a = 2\<^sub>R *\<^sub>R a" @qed
      
lemma avg_le2 [backward]: "is_ord_field(R) \<Longrightarrow> a \<le>\<^sub>R b \<Longrightarrow> avg(R,a,b) \<le>\<^sub>R b"
@proof @have "a +\<^sub>R b \<le>\<^sub>R b +\<^sub>R b" @have "b +\<^sub>R b = 2\<^sub>R *\<^sub>R b" @qed

lemma avg_less [backward]: "is_ord_field(R) \<Longrightarrow> a <\<^sub>R b \<Longrightarrow> a <\<^sub>R avg(R,a,b)"
@proof @have "a +\<^sub>R a <\<^sub>R a +\<^sub>R b" @have "a +\<^sub>R a = 2\<^sub>R *\<^sub>R a" @qed

lemma avg_less2 [backward]: "is_ord_field(R) \<Longrightarrow> a <\<^sub>R b \<Longrightarrow> avg(R,a,b) <\<^sub>R b"
@proof @have "a +\<^sub>R b <\<^sub>R b +\<^sub>R b" @have "b +\<^sub>R b = 2\<^sub>R *\<^sub>R b" @qed

lemma avg_ge [backward]: "is_ord_field(R) \<Longrightarrow> a \<ge>\<^sub>R b \<Longrightarrow> a \<ge>\<^sub>R avg(R,a,b)"
@proof @have "avg(R,a,b) = avg(R,b,a)" @qed

lemma avg_ge2 [backward]: "is_ord_field(R) \<Longrightarrow> a \<ge>\<^sub>R b \<Longrightarrow> avg(R,a,b) \<ge>\<^sub>R b"
@proof @have "avg(R,a,b) = avg(R,b,a)" @qed

lemma ord_field_dense [forward]: "is_ord_field(R) \<Longrightarrow> dense_order(R)"
@proof
  @have "\<forall>a b. a <\<^sub>R b \<longrightarrow> (\<exists>c. a <\<^sub>R c \<and> c <\<^sub>R b)" @with @have "a <\<^sub>R avg(R,a,b)" @end
@qed
setup {* del_prfstep_thm @{thm avg_def} *}

section {* Comparison of rational numbers *}
  
lemma ord_ring_of_nat_ge_zero' [backward]:
  "is_ord_ring(R) \<Longrightarrow> n \<in> nat \<Longrightarrow> of_nat(R,n) \<ge>\<^sub>R 0\<^sub>R" by auto2

lemma ord_ring_of_nat_greater_zero' [backward]:
  "is_ord_ring(R) \<Longrightarrow> n \<in> nat \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> of_nat(R,n) >\<^sub>R 0\<^sub>R" by auto2

lemma ord_field_rat_ge_zero:
  "is_ord_field(R) \<Longrightarrow> m \<in> nat \<Longrightarrow> n \<in> nat \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> of_nat(R,m) /\<^sub>R of_nat(R,n) \<ge>\<^sub>R 0\<^sub>R"
@proof @have "of_nat(R,m) \<ge>\<^sub>R 0\<^sub>R" @have "of_nat(R,n) \<ge>\<^sub>R 0\<^sub>R" @qed

lemma ord_field_rat_greater_zero:
  "is_ord_field(R) \<Longrightarrow> m \<in> nat \<Longrightarrow> n \<in> nat \<Longrightarrow> m \<noteq> 0 \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> of_nat(R,m) /\<^sub>R of_nat(R,n) >\<^sub>R 0\<^sub>R"
@proof @have "of_nat(R,m) >\<^sub>R 0\<^sub>R" @have "of_nat(R,n) \<ge>\<^sub>R 0\<^sub>R" @qed

lemma ord_ring_le_switch_left':
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> 0\<^sub>R \<le>\<^sub>R y -\<^sub>R x \<Longrightarrow> x \<le>\<^sub>R y" by auto2

lemma ord_ring_less_switch_left':
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> 0\<^sub>R <\<^sub>R y -\<^sub>R x \<Longrightarrow> x <\<^sub>R y" by auto2
    
lemma ord_field_le_to_neg: "is_ord_field(R) \<Longrightarrow> x \<le>\<^sub>R y \<Longrightarrow> \<not>y <\<^sub>R x" by auto2
lemma ord_field_less_to_neg: "is_ord_field(R) \<Longrightarrow> x <\<^sub>R y \<Longrightarrow> \<not>y \<le>\<^sub>R x" by auto2

ML_file "field_steps.ML"

end
