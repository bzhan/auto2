theory Ring
imports Nat
begin

section {* Rings *}
  
definition is_ring :: "i \<Rightarrow> o" where [rewrite]:
  "is_ring(R) \<longleftrightarrow> (is_ring_raw(R) \<and> is_abgroup(R) \<and> is_monoid(R) \<and>
    is_left_distrib(R) \<and> is_right_distrib(R) \<and> \<zero>\<^sub>R \<noteq> \<one>\<^sub>R)"
setup {* add_property_const @{term is_ring} *}

lemma is_ringD [forward]:
  "is_ring(R) \<Longrightarrow> is_ring_raw(R)"
  "is_ring(R) \<Longrightarrow> is_abgroup(R)"
  "is_ring(R) \<Longrightarrow> is_monoid(R)"
  "is_ring(R) \<Longrightarrow> is_left_distrib(R)"
  "is_ring(R) \<Longrightarrow> is_right_distrib(R)" by auto2+

lemma is_ringD' [resolve]: "is_ring(R) \<Longrightarrow> \<zero>\<^sub>R \<noteq> \<one>\<^sub>R" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm is_ring_def} *}
  
lemma is_ring_ring_prop [forward]:
  "is_ring_raw(H) \<Longrightarrow> is_ring(G) \<Longrightarrow> eq_str_ring(G,H) \<Longrightarrow> is_ring(H)" by auto2

setup {* fold add_rewrite_rule [
  @{thm times_commD}, @{thm left_distribD}, @{thm right_distribD}, @{thm left_distribD_back},
  @{thm right_distribD_back}] *}

lemma comm_distribs [forward]:
  "is_ring_raw(R) \<Longrightarrow> is_left_distrib(R) \<Longrightarrow> is_times_comm(R) \<Longrightarrow> is_right_distrib(R)" by auto2

lemma ring_mult0_left [rewrite]: "is_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<zero>\<^sub>R *\<^sub>R x = \<zero>\<^sub>R"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<zero>\<^sub>R *\<^sub>R x +\<^sub>R \<zero>\<^sub>R *\<^sub>R x = (\<zero>\<^sub>R +\<^sub>R \<zero>\<^sub>R) *\<^sub>R x +\<^sub>R \<zero>\<^sub>R") *})

lemma ring_mult0_right [rewrite]: "is_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> x *\<^sub>R \<zero>\<^sub>R = \<zero>\<^sub>R"
  by (tactic {* auto2s_tac @{context} (
    HAVE "x *\<^sub>R \<zero>\<^sub>R +\<^sub>R x *\<^sub>R \<zero>\<^sub>R = x *\<^sub>R (\<zero>\<^sub>R +\<^sub>R \<zero>\<^sub>R) +\<^sub>R \<zero>\<^sub>R") *})
    
lemma units_non_zero [forward]: "is_ring(R) \<Longrightarrow> x \<in> units(R) \<Longrightarrow> x \<noteq> \<zero>\<^sub>R"
  by (tactic {* auto2s_tac @{context} (CHOOSE "y\<in>.R, y *\<^sub>R x = \<one>\<^sub>R") *})

lemma ring_mult_sign_l [rewrite]:
  "is_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> (-\<^sub>R x) *\<^sub>R y = -\<^sub>R (x *\<^sub>R y) \<and> x *\<^sub>R y \<in>. R"
  by (tactic {* auto2s_tac @{context} (HAVE "(-\<^sub>R x) *\<^sub>R y +\<^sub>R x *\<^sub>R y = \<zero>\<^sub>R") *})

lemma ring_mult_sign_r [rewrite]:
  "is_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x *\<^sub>R (-\<^sub>R y) = -\<^sub>R (x *\<^sub>R y) \<and> x *\<^sub>R y \<in>. R"
  by (tactic {* auto2s_tac @{context} (HAVE "x *\<^sub>R (-\<^sub>R y) +\<^sub>R x *\<^sub>R y = \<zero>\<^sub>R") *})

lemma ring_mult_sign_both [rewrite]:
  "is_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> (-\<^sub>R x) *\<^sub>R (-\<^sub>R y) = x *\<^sub>R y" by auto2

section {* Commutative rings *}

definition is_comm_ring :: "i \<Rightarrow> o" where [rewrite]:
  "is_comm_ring(R) \<longleftrightarrow> (is_ring(R) \<and> is_times_comm(R))"
setup {* add_property_const @{term is_comm_ring} *}

lemma is_comm_ringD [forward]:
  "is_comm_ring(R) \<Longrightarrow> is_ring(R)"
  "is_comm_ring(R) \<Longrightarrow> is_times_comm(R)" by auto2+
setup {* del_prfstep_thm_str "@eqforward" @{thm is_comm_ring_def} *}

lemma is_comm_ring_ring_prop [forward]:
  "is_ring_raw(H) \<Longrightarrow> is_comm_ring(G) \<Longrightarrow> eq_str_ring(G,H) \<Longrightarrow> is_comm_ring(H)" by auto2

lemma comm_ring_is_unit [forward]:
  "is_comm_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> y *\<^sub>R x = \<one>\<^sub>R \<Longrightarrow> x \<in> units(R)" by auto2

lemma comm_ring_is_unit2 [forward]:
  "is_comm_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x *\<^sub>R y = \<one>\<^sub>R \<Longrightarrow> x \<in> units(R)" by auto2

lemma comm_ring_prod_unit [forward]:
  "is_comm_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x *\<^sub>R y \<in> units(R) \<Longrightarrow> x \<in> units(R) \<and> y \<in> units(R)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "z\<in>.R, z *\<^sub>R (x *\<^sub>R y) = \<one>\<^sub>R \<and> (x *\<^sub>R y) *\<^sub>R z = \<one>\<^sub>R" THEN
    HAVE "(y *\<^sub>R z) *\<^sub>R x = \<one>\<^sub>R" THEN HAVE "y *\<^sub>R (x *\<^sub>R z) = (y *\<^sub>R x) *\<^sub>R z") *})

lemma inv_distrib_comm_ring [rewrite]:
  "is_comm_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x *\<^sub>R y \<in> units(R) \<Longrightarrow>
   inv(R, x *\<^sub>R y) = inv(R,y) *\<^sub>R inv(R,x) \<and> x \<in> units(R) \<and> y \<in> units(R) \<and>
   inv(R,y) \<in>. R \<and> inv(R,x) \<in>. R"
  by (tactic {* auto2s_tac @{context} (
    HAVE "inv(R,y) *\<^sub>R inv(R,x) *\<^sub>R (x *\<^sub>R y) = inv(R,y) *\<^sub>R (inv(R,x) *\<^sub>R x) *\<^sub>R y") *})

lemma comm_ring_prod_is_unit [backward1, backward2]:
  "is_comm_ring(R) \<Longrightarrow> x \<in> units(R) \<Longrightarrow> y \<in> units(R) \<Longrightarrow> x *\<^sub>R y \<in> units(R)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "inv(R,y) *\<^sub>R inv(R,x) *\<^sub>R (x *\<^sub>R y) = inv(R,y) *\<^sub>R (inv(R,x) *\<^sub>R x) *\<^sub>R y") *})

section {* of_nat on rings *}

(* Recursion on x:
    of_nat(0) = 0
  | of_nat(n + 1) = of_nat(n) + 1
*)
definition of_nat :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "of_nat(R,x) = nat_rec(\<zero>\<^sub>R, \<lambda>x' p. p +\<^sub>R \<one>\<^sub>R, x)"
setup {* register_wellform_data ("of_nat(R,x)", ["x \<in> nat"]) *}

lemma of_nat_zero [rewrite_bidir]: "is_ring(R) \<Longrightarrow> of_nat(R,0) = \<zero>\<^sub>R" by auto2
lemma of_nat_Suc [rewrite]: "n \<in> nat \<Longrightarrow> of_nat(R,n +\<^sub>\<nat> 1) = of_nat(R,n) +\<^sub>R \<one>\<^sub>R" by auto2
lemma of_nat_one [rewrite_bidir]: "is_ring(R) \<Longrightarrow> of_nat(R,1) = \<one>\<^sub>R"
  by (tactic {* auto2s_tac @{context} (HAVE "1 = 0 +\<^sub>\<nat> 1") *})
lemma of_nat_type [typing]: "is_ring(R) \<Longrightarrow> n \<in> nat \<Longrightarrow> of_nat(R,n) \<in>. R"
  by (tactic {* auto2s_tac @{context} (INDUCT_ON "x \<in> nat" "of_nat(R,n) \<in>. R") *})

abbreviation ZeroR ("0\<^sub>_" [91] 90) where "0\<^sub>R \<equiv> of_nat(R,0)"
abbreviation OneR ("1\<^sub>_" [91] 90) where "1\<^sub>R \<equiv> of_nat(R,1)"
abbreviation TwoR ("2\<^sub>_" [91] 90) where "2\<^sub>R \<equiv> of_nat(R,2)"
abbreviation ThreeR ("3\<^sub>_" [91] 90) where "3\<^sub>R \<equiv> of_nat(R,3)"
abbreviation FourR ("4\<^sub>_" [91] 90) where "4\<^sub>R \<equiv> of_nat(R,4)"
abbreviation FiveR ("5\<^sub>_" [91] 90) where "5\<^sub>R \<equiv> of_nat(R,5)"
abbreviation NegOneR ("-1\<^sub>_" [91] 90) where "-1\<^sub>R \<equiv> -\<^sub>R of_nat(R,1)"

setup {* del_prfstep_thm @{thm of_nat_def} *}

lemma of_nat_add_aux [backward]:
  "is_comm_ring(R) \<Longrightarrow> x \<in> nat \<Longrightarrow> y \<in> nat \<Longrightarrow> of_nat(R,x) +\<^sub>R of_nat(R,y) = of_nat(R, x +\<^sub>\<nat> y) \<Longrightarrow>
   of_nat(R,x +\<^sub>\<nat> 1) +\<^sub>R of_nat(R,y) = of_nat(R, x +\<^sub>\<nat> 1 +\<^sub>\<nat> y)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "of_nat(R,x) +\<^sub>R 1\<^sub>R +\<^sub>R of_nat(R,y) = of_nat(R,x) +\<^sub>R of_nat(R,y) +\<^sub>R 1\<^sub>R" THEN
    HAVE "x +\<^sub>\<nat> 1 +\<^sub>\<nat> y = x +\<^sub>\<nat> y +\<^sub>\<nat> 1") *})

lemma of_nat_add:
  "is_comm_ring(R) \<Longrightarrow> x \<in> nat \<Longrightarrow> y \<in> nat \<Longrightarrow> of_nat(R,x) +\<^sub>R of_nat(R,y) = of_nat(R, x +\<^sub>\<nat> y) \<and> x +\<^sub>\<nat> y \<in> nat"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "x \<in> nat" "of_nat(R,x) +\<^sub>R of_nat(R,y) = of_nat(R, x +\<^sub>\<nat> y)") *})
setup {* add_rewrite_rule_cond @{thm of_nat_add}
  (with_conds ["?x \<noteq> 0", "?x \<noteq> Suc(?z)", "?y \<noteq> 0", "?y \<noteq> Suc(?z)"]) *}
setup {* del_prfstep_thm @{thm of_nat_add_aux} *}

lemma of_nat_add_back [rewrite]:
  "is_comm_ring(R) \<Longrightarrow> x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> of_nat(R, x +\<^sub>\<nat> y) = of_nat(R,x) +\<^sub>R of_nat(R,y)" by auto2  

lemma of_nat_mult:
  "is_comm_ring(R) \<Longrightarrow> x \<in> nat \<Longrightarrow> y \<in> nat \<Longrightarrow> of_nat(R,x) *\<^sub>R of_nat(R,y) = of_nat(R, x *\<^sub>\<nat> y) \<and> x *\<^sub>\<nat> y \<in> nat"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "x \<in> nat" "of_nat(R,x) *\<^sub>R of_nat(R,y) = of_nat(R, x *\<^sub>\<nat> y)") *})
setup {* add_rewrite_rule_cond @{thm of_nat_mult}
  (with_conds ["?x \<noteq> 0", "?x \<noteq> Suc(?z)", "?y \<noteq> 0", "?y \<noteq> Suc(?z)"]) *}

lemma of_nat_mult_back [rewrite]:
  "is_comm_ring(R) \<Longrightarrow> x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> of_nat(R, x *\<^sub>\<nat> y) = of_nat(R,x) *\<^sub>R of_nat(R,y)" by auto2

lemma of_nat_sub1 [rewrite]:
  "is_comm_ring(R) \<Longrightarrow> x \<ge>\<^sub>\<nat> y \<Longrightarrow> of_nat(R,x) +\<^sub>R -\<^sub>R of_nat(R,y) = of_nat(R,x -\<^sub>\<nat> y) \<and> x -\<^sub>\<nat> y \<in> nat"
  by (tactic {* auto2s_tac @{context} (
    HAVE "(of_nat(R,x) -\<^sub>R of_nat(R,y)) +\<^sub>R of_nat(R,y) = of_nat(R, x -\<^sub>\<nat> y) +\<^sub>R of_nat(R,y)") *})

lemma of_nat_sub2:
  "is_comm_ring(R) \<Longrightarrow> x \<le>\<^sub>\<nat> y \<Longrightarrow> of_nat(R,x) +\<^sub>R -\<^sub>R of_nat(R,y) = -\<^sub>R of_nat(R,y -\<^sub>\<nat> x) \<and>
     y -\<^sub>\<nat> x \<in> nat \<and> of_nat(R,y -\<^sub>\<nat> x) \<in>. R"
  by (tactic {* auto2s_tac @{context} (
    HAVE "of_nat(R,x) +\<^sub>R -\<^sub>R of_nat(R,y) = -\<^sub>R (of_nat(R,y) +\<^sub>R -\<^sub>R of_nat(R,x))") *})
  
lemma of_nat_sub_back [rewrite]:
  "is_comm_ring(R) \<Longrightarrow> x \<ge>\<^sub>\<nat> y \<Longrightarrow> of_nat(R,x -\<^sub>\<nat> y) = of_nat(R,x) -\<^sub>R of_nat(R,y)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "of_nat(R,x) -\<^sub>R of_nat(R,y) = of_nat(R,x) +\<^sub>R -\<^sub>R of_nat(R,y)") *})

lemma add_monomial_l [rewrite]:
  "is_ring(R) \<Longrightarrow> p \<in>. R \<Longrightarrow> r \<in>. R \<Longrightarrow> p +\<^sub>R p *\<^sub>R r = p *\<^sub>R (1\<^sub>R +\<^sub>R r) \<and>
   1 \<in> nat \<and> 1\<^sub>R \<in>. R \<and> 1\<^sub>R +\<^sub>R r \<in>. R" by auto2

lemma add_monomial_same:
  "is_ring(R) \<Longrightarrow> p \<in>. R \<Longrightarrow> p +\<^sub>R p = p *\<^sub>R 2\<^sub>R \<and> 2 \<in> nat \<and> 2\<^sub>R \<in>. R"
  by (tactic {* auto2s_tac @{context} (HAVE "2 = 1 +\<^sub>\<nat> 1") *})
    
lemma neg_is_minus_1:
  "is_ring(R) \<Longrightarrow> p \<in>. R \<Longrightarrow> -\<^sub>R p = p *\<^sub>R -1\<^sub>R \<and> 1 \<in> nat \<and> 1\<^sub>R \<in>. R \<and> -1\<^sub>R \<in>. R" by auto2

setup {* fold del_prfstep_thm [@{thm of_nat_Suc}, @{thm of_nat_sub1}, @{thm add_monomial_l}] *}

section {* Division in commutative rings *}
  
definition divide :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "divide(G,x,y) = (THE z. z \<in>. G \<and> z *\<^sub>G y = x)"
abbreviation divide_notation ("(_/ '/\<^sub>_ _)" [70,70,71] 70) where "x /\<^sub>G y \<equiv> divide(G,x,y)"
setup {* register_wellform_data ("x /\<^sub>G y", ["x \<in>. G", "y \<in> units(G)"]) *}

setup {* add_gen_prfstep ("ring_inv_case",
  [WithProperty @{term_pat "is_ring(?R)"}, WithTerm @{term_pat "inv(?R,?x)"},
   CreateConcl @{term_pat "?x \<in> units(?R)"}]) *}
  
setup {* add_gen_prfstep ("ring_div_case",
  [WithProperty @{term_pat "is_ring(?R)"}, WithTerm @{term_pat "?x /\<^sub>?R ?y"},
   CreateConcl @{term_pat "?y \<in> units(?R)"}]) *}

lemma divide_exist [resolve]:
  "is_comm_ring(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in> units(G) \<Longrightarrow> (x *\<^sub>G inv(G,y)) *\<^sub>G y = x"
  by (tactic {* auto2s_tac @{context} (
    HAVE "(x *\<^sub>G inv(G,y)) *\<^sub>G y = x *\<^sub>G (inv(G,y) *\<^sub>G y)") *})

lemma divide_type [typing]:
  "is_comm_ring(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in> units(G) \<Longrightarrow> x /\<^sub>G y \<in>. G"
  by (tactic {* auto2s_tac @{context} (HAVE "(x *\<^sub>G inv(G,y)) *\<^sub>G y = x") *})

lemma divideD [rewrite]:
  "is_comm_ring(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in> units(G) \<Longrightarrow> x /\<^sub>G y = x *\<^sub>G inv(G,y) \<and> inv(G,y) \<in>. G"
  by (tactic {* auto2s_tac @{context} (HAVE "(x *\<^sub>G inv(G,y)) *\<^sub>G y = x") *})
setup {* del_prfstep_thm @{thm divide_def} *}

lemma comm_ring_divide_1:
  "is_comm_ring(G) \<Longrightarrow> n \<in> nat \<Longrightarrow> of_nat(G,n) = of_nat(G,n) /\<^sub>G 1\<^sub>G \<and>
   of_nat(G,n) \<in>. G \<and> 1 \<in> nat \<and> 1\<^sub>G \<in> units(G)" by auto2

lemma comm_ring_neg_divide_1:
  "is_comm_ring(G) \<Longrightarrow> n \<in> nat \<Longrightarrow> -\<^sub>G of_nat(G,n) = -\<^sub>G of_nat(G,n) /\<^sub>G 1\<^sub>G \<and>
   of_nat(G,n) \<in>. G \<and> -\<^sub>G of_nat(G,n) \<in>. G \<and> 1 \<in> nat \<and> 1\<^sub>G \<in> units(G)" by auto2

lemma comm_ring_divide_1_back [rewrite]:
  "is_comm_ring(G) \<Longrightarrow> p \<in>. G \<Longrightarrow> p /\<^sub>G 1\<^sub>G = p" by auto2

lemma comm_ring_zero_divide [rewrite]:
  "is_comm_ring(R) \<Longrightarrow> a \<in> units(R) \<Longrightarrow> 0\<^sub>R /\<^sub>R a = 0\<^sub>R" by auto2

lemma comm_ring_zero_divide' [forward]:
  "is_comm_ring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in> units(R) \<Longrightarrow> a /\<^sub>R b = 0\<^sub>R \<Longrightarrow> a = 0\<^sub>R"
  by (tactic {* auto2s_tac @{context} (HAVE "a /\<^sub>R b *\<^sub>R b = a") *})

lemma divide_cancel_right [rewrite]:
  "is_comm_ring(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> z \<in>. G \<Longrightarrow> y *\<^sub>G z \<in> units(G) \<Longrightarrow>
   (x *\<^sub>G z) /\<^sub>G (y *\<^sub>G z) = x /\<^sub>G y \<and> y \<in> units(G)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "(x *\<^sub>G z) *\<^sub>G (inv(G,z) *\<^sub>G inv(G,y)) = x *\<^sub>G (z *\<^sub>G inv(G,z)) *\<^sub>G inv(G,y)") *})

lemma divide_cancel_left [rewrite]:
  "is_comm_ring(G) \<Longrightarrow> x \<in>. G \<Longrightarrow> y \<in>. G \<Longrightarrow> z \<in>. G \<Longrightarrow> z *\<^sub>G y \<in> units(G) \<Longrightarrow>
   (z *\<^sub>G x) /\<^sub>G (z *\<^sub>G y) = x /\<^sub>G y \<and> y \<in> units(G)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "z *\<^sub>G x = x *\<^sub>G z" THEN HAVE "z *\<^sub>G y = y *\<^sub>G z") *})

lemma divide_cross:
  "is_comm_ring(G) \<Longrightarrow> p \<in>. G \<Longrightarrow> q \<in> units(G) \<Longrightarrow> r \<in>. G \<Longrightarrow> s \<in> units(G) \<Longrightarrow>
   p /\<^sub>G q +\<^sub>G r /\<^sub>G s = (p *\<^sub>G s +\<^sub>G q *\<^sub>G r) /\<^sub>G (q *\<^sub>G s) \<and>
   q \<in>. G \<and> s \<in>. G \<and> p *\<^sub>G s \<in>. G \<and> q *\<^sub>G r \<in>. G \<and> p *\<^sub>G s +\<^sub>G q *\<^sub>G r \<in>. G \<and> q *\<^sub>G s \<in> units(G)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "(p *\<^sub>G s +\<^sub>G q *\<^sub>G r) /\<^sub>G (q *\<^sub>G s) = (p *\<^sub>G s) /\<^sub>G (q *\<^sub>G s) +\<^sub>G (q *\<^sub>G r) /\<^sub>G (q *\<^sub>G s)") *})

lemma divide_mult:
  "is_comm_ring(G) \<Longrightarrow> p \<in>. G \<Longrightarrow> q \<in> units(G) \<Longrightarrow> r \<in>. G \<Longrightarrow> s \<in> units(G) \<Longrightarrow>
   (p /\<^sub>G q) *\<^sub>G (r /\<^sub>G s) = (p *\<^sub>G r) /\<^sub>G (q *\<^sub>G s) \<and>
   q \<in>. G \<and> s \<in>. G \<and> p *\<^sub>G r \<in>. G \<and> q *\<^sub>G s \<in> units(G)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "(p *\<^sub>G inv(G,q)) *\<^sub>G (r *\<^sub>G inv(G,s)) = p *\<^sub>G (inv(G,q) *\<^sub>G r) *\<^sub>G inv(G,s)" THEN
    HAVE "p *\<^sub>G (r *\<^sub>G inv(G,q)) *\<^sub>G inv(G,s) = (p *\<^sub>G r) *\<^sub>G (inv(G,q) *\<^sub>G inv(G,s))") *})

lemma comm_ring_units_minus [typing]:
  "is_comm_ring(G) \<Longrightarrow> p \<in> units(G) \<Longrightarrow> -\<^sub>G p \<in> units(G)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "q\<in>.G, p *\<^sub>G q = \<one>\<^sub>G" THEN HAVE "(-\<^sub>G p) *\<^sub>G (-\<^sub>G q) = p *\<^sub>G q") *})

lemma comm_ring_units_minus_back [typing]:
  "is_comm_ring(G) \<Longrightarrow> p \<in>. G \<Longrightarrow> -\<^sub>G p \<in> units(G) \<Longrightarrow> p \<in> units(G)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "q\<in>.G, (-\<^sub>G p) *\<^sub>G q = \<one>\<^sub>G" THEN HAVE "p *\<^sub>G (-\<^sub>G q) = -\<^sub>G p *\<^sub>G q") *})

lemma inv_neg [rewrite]:
  "is_comm_ring(G) \<Longrightarrow> p \<in>. G \<Longrightarrow> -\<^sub>G p \<in> units(G) \<Longrightarrow> inv(G, -\<^sub>G p) = -\<^sub>G (inv(G,p)) \<and>
   p \<in> units(G) \<and> inv(G,p) \<in>. G"
  by (tactic {* auto2s_tac @{context} (HAVE "-\<^sub>G p *\<^sub>G (-\<^sub>G inv(G,p)) = \<one>\<^sub>G") *})

lemma divide_inv [rewrite]:
  "is_comm_ring(G) \<Longrightarrow> p \<in>. G \<Longrightarrow> q \<in> units(G) \<Longrightarrow> p /\<^sub>G q \<in> units(G) \<Longrightarrow>
   inv(G,p /\<^sub>G q) = q /\<^sub>G p \<and> p \<in> units(G) \<and> q \<in>. G" by auto2

lemma divide_inv2:
  "is_comm_ring(G) \<Longrightarrow> p \<in>. G \<Longrightarrow> q \<in> units(G) \<Longrightarrow> (-\<^sub>G p) /\<^sub>G q \<in> units(G) \<Longrightarrow>
   inv(G,(-\<^sub>G p) /\<^sub>G q) = (-\<^sub>G q) /\<^sub>G p \<and> p \<in> units(G) \<and> q \<in>. G \<and> -\<^sub>G q \<in>. G"
  by (tactic {* auto2s_tac @{context} (
    HAVE "(-\<^sub>G p) /\<^sub>G q = -\<^sub>G (p /\<^sub>G q)" THEN
    HAVE "p = -\<^sub>G (-\<^sub>G p)" THEN
    HAVE "(-\<^sub>G q) /\<^sub>G p = -\<^sub>G (q /\<^sub>G p)") *})
      
lemma uminus_zero:
  "is_comm_ring(G) \<Longrightarrow> -\<^sub>G 0\<^sub>G = 0\<^sub>G \<and> 0 \<in> nat" by auto2

lemma uminus_inv1:
  "is_comm_ring(G) \<Longrightarrow> p \<in>. G \<Longrightarrow> q \<in> units(G) \<Longrightarrow> -\<^sub>G (p /\<^sub>G q) = (-\<^sub>G p) /\<^sub>G q \<and> -\<^sub>G p \<in>. G" by auto2
    
lemma uminus_inv2:
  "is_comm_ring(G) \<Longrightarrow> p \<in>. G \<Longrightarrow> q \<in> units(G) \<Longrightarrow> -\<^sub>G (-\<^sub>G p /\<^sub>G q) = p /\<^sub>G q" by auto2

setup {* fold del_prfstep_thm [@{thm times_commD}, @{thm left_distribD}, @{thm right_distribD},
  @{thm left_distribD_back}, @{thm right_distribD_back}] *}
setup {* fold del_prfstep_thm [@{thm ring_mult_sign_both}, @{thm divide_exist}, @{thm divideD},
  @{thm divide_cancel_left}, @{thm divide_cancel_right}, @{thm divide_inv}] *}
  
lemma zero_l': "is_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> 0\<^sub>R +\<^sub>R x = x" by auto2
lemma unit_l': "is_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> 1\<^sub>R *\<^sub>R x = x" by auto2
lemma mult_zero_l': "is_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> 0\<^sub>R *\<^sub>R x = 0\<^sub>R" by auto2
lemma inv_l': "is_ring(R) \<Longrightarrow> x \<in> units(R) \<Longrightarrow> inv(R,x) *\<^sub>R x = 1\<^sub>R \<and> 1 \<in> nat" by auto2
lemma of_nat_zero': "is_ring(R) \<Longrightarrow> \<zero>\<^sub>R = of_nat(R,0) \<and> 0 \<in> nat" by auto2
lemma of_nat_one': "is_ring(R) \<Longrightarrow> \<one>\<^sub>R = of_nat(R,1) \<and> 1 \<in> nat" by auto2

ML_file "rat_arith.ML"
ML_file "alg_ring.ML"
ML_file "alg_ring_test.ML"

section {* Integral domain *}
  
definition integral_domain :: "i \<Rightarrow> o" where [rewrite]:
  "integral_domain(R) \<longleftrightarrow> (is_comm_ring(R) \<and> (\<forall>x\<in>.R. \<forall>y\<in>.R. x *\<^sub>R y = \<zero>\<^sub>R \<longrightarrow> x = \<zero>\<^sub>R \<or> y = \<zero>\<^sub>R))"
setup {* add_property_const @{term integral_domain} *}

lemma integral_domainD [forward]:
  "integral_domain(R) \<Longrightarrow> is_comm_ring(R)"
  "integral_domain(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x *\<^sub>R y = \<zero>\<^sub>R \<Longrightarrow> x \<noteq> \<zero>\<^sub>R \<Longrightarrow> y = \<zero>\<^sub>R"
  "integral_domain(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x *\<^sub>R y = \<zero>\<^sub>R \<Longrightarrow> y \<noteq> \<zero>\<^sub>R \<Longrightarrow> x = \<zero>\<^sub>R" by auto2+
setup {* del_prfstep_thm_str "@eqforward" @{thm integral_domain_def} *}

lemma integral_domain_cancel_right [forward]:
  "integral_domain(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow> z \<noteq> \<zero>\<^sub>R \<Longrightarrow> x *\<^sub>R z = y *\<^sub>R z \<Longrightarrow> x = y"
  by (tactic {* auto2s_tac @{context} (
    HAVE "x *\<^sub>R z -\<^sub>R y *\<^sub>R z = (x -\<^sub>R y) *\<^sub>R z") *})
      
lemma integral_domain_cancel_left [forward]:
  "integral_domain(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow> z \<noteq> \<zero>\<^sub>R \<Longrightarrow> z *\<^sub>R x = z *\<^sub>R y \<Longrightarrow> x = y"
  by (tactic {* auto2s_tac @{context} (
    HAVE "z *\<^sub>R x -\<^sub>R z *\<^sub>R y = z *\<^sub>R (x -\<^sub>R y)") *})

section {* Ordered rings *}

definition is_ord_ring :: "i \<Rightarrow> o" where [rewrite]:
  "is_ord_ring(R) \<longleftrightarrow> (is_ord_ring_raw(R) \<and> is_comm_ring(R) \<and> linorder(R) \<and>
                       ord_ring_add_left(R) \<and> ord_ring_mult_pos(R))"
setup {* add_property_const @{term is_ord_ring} *}

lemma is_ord_ringD [forward]:
  "is_ord_ring(R) \<Longrightarrow> is_ord_ring_raw(R)"
  "is_ord_ring(R) \<Longrightarrow> is_comm_ring(R)"
  "is_ord_ring(R) \<Longrightarrow> linorder(R)"
  "is_ord_ring(R) \<Longrightarrow> ord_ring_add_left(R)"
  "is_ord_ring(R) \<Longrightarrow> ord_ring_mult_pos(R)" by auto2+
setup {* del_prfstep_thm_str "@eqforward" @{thm is_ord_ring_def} *}
  
lemma is_ord_ring_prop [forward]:
  "is_ord_ring(R) \<Longrightarrow> is_ord_ring_raw(S) \<Longrightarrow> eq_str_ord_ring(R,S) \<Longrightarrow> is_ord_ring(S)" by auto2
  
(* Usually we don't convert > to \<noteq>, but this case is especially frequent. *)
lemma ord_ring_nonzero [forward]:
  "is_ord_ring(R) \<Longrightarrow> x >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> x \<noteq> \<zero>\<^sub>R"
  "is_ord_ring(R) \<Longrightarrow> x <\<^sub>R \<zero>\<^sub>R \<Longrightarrow> x \<noteq> \<zero>\<^sub>R" by auto2+

lemma ord_ring_ordered_left_iff [rewrite]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow> z +\<^sub>R x \<le>\<^sub>R z +\<^sub>R y \<longleftrightarrow> x \<le>\<^sub>R y"
  by (tactic {* auto2s_tac @{context} (
    HAVE "x = (-\<^sub>R z) +\<^sub>R (x +\<^sub>R z)" THEN HAVE "y = (-\<^sub>R z) +\<^sub>R (y +\<^sub>R z)") *})

lemma ord_ring_ordered_right_iff [rewrite]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow> x +\<^sub>R z \<le>\<^sub>R y +\<^sub>R z \<longleftrightarrow> x \<le>\<^sub>R y"
  by (tactic {* auto2s_tac @{context} (
    HAVE "x +\<^sub>R z = z +\<^sub>R x" THEN HAVE "y +\<^sub>R z = z +\<^sub>R y") *})
      
(* The main results for automatic simplification *)
lemma ord_ring_le_switch_left:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> (x \<le>\<^sub>R y \<longleftrightarrow> 0\<^sub>R \<le>\<^sub>R y -\<^sub>R x) \<and> y -\<^sub>R x \<in>. R \<and> 0\<^sub>R \<in>. R \<and> 0 \<in> nat"
  by (tactic {* auto2s_tac @{context} (HAVE "0\<^sub>R +\<^sub>R x = y -\<^sub>R x +\<^sub>R x") *})
      
lemma ord_ring_less_switch_left:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> (x <\<^sub>R y \<longleftrightarrow> 0\<^sub>R <\<^sub>R y -\<^sub>R x) \<and> y -\<^sub>R x \<in>. R \<and> 0\<^sub>R \<in>. R \<and> 0 \<in> nat"
  by (tactic {* auto2s_tac @{context} (HAVE "0\<^sub>R +\<^sub>R x = y -\<^sub>R x +\<^sub>R x") *})
ML_file "ord_ring_steps.ML"

lemma ord_ring_single_less_add [backward]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<zero>\<^sub>R <\<^sub>R y \<Longrightarrow> x <\<^sub>R x +\<^sub>R y" by auto2
    
lemma ord_ring_single_less_sub [backward]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<zero>\<^sub>R <\<^sub>R y \<Longrightarrow> x >\<^sub>R x -\<^sub>R y" by auto2

lemma ord_ring_single_le_add [backward]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<zero>\<^sub>R \<le>\<^sub>R y \<Longrightarrow> x \<le>\<^sub>R x +\<^sub>R y" by auto2

lemma ord_ring_mix1 [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> p \<le>\<^sub>R q \<Longrightarrow> r \<le>\<^sub>R s \<Longrightarrow> p +\<^sub>R r \<le>\<^sub>R q +\<^sub>R s"
  by (tactic {* auto2s_tac @{context} (HAVE "p +\<^sub>R r \<le>\<^sub>R p +\<^sub>R s") *})
    
lemma ord_ring_mix2 [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> p \<le>\<^sub>R q \<Longrightarrow> r <\<^sub>R s \<Longrightarrow> p +\<^sub>R r <\<^sub>R q +\<^sub>R s"
  by (tactic {* auto2s_tac @{context} (HAVE "p +\<^sub>R r <\<^sub>R p +\<^sub>R s") *})
  
lemma ord_ring_mix3 [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> p <\<^sub>R q \<Longrightarrow> r \<le>\<^sub>R s \<Longrightarrow> p +\<^sub>R r <\<^sub>R q +\<^sub>R s"
  by (tactic {* auto2s_tac @{context} (HAVE "p +\<^sub>R r <\<^sub>R q +\<^sub>R r") *})

lemma ord_ring_strict_ordered_left_iff [rewrite]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow> z +\<^sub>R x <\<^sub>R z +\<^sub>R y \<longleftrightarrow> x <\<^sub>R y" by auto2

lemma ord_ring_strict_ordered_right_iff [rewrite]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow> x +\<^sub>R z <\<^sub>R y +\<^sub>R z \<longleftrightarrow> x <\<^sub>R y" by auto2

lemma ord_ring_ge_equiv [rewrite]:
  "is_ord_ring(R) \<Longrightarrow> p \<in>. R \<Longrightarrow> q \<in>. R \<Longrightarrow> p -\<^sub>R q \<ge>\<^sub>R \<zero>\<^sub>R \<longleftrightarrow> p \<ge>\<^sub>R q" by auto2

lemma ord_ring_gt_equiv [rewrite]:
  "is_ord_ring(R) \<Longrightarrow> p \<in>. R \<Longrightarrow> q \<in>. R \<Longrightarrow> p -\<^sub>R q >\<^sub>R \<zero>\<^sub>R \<longleftrightarrow> p >\<^sub>R q" by auto2

lemma ord_ring_mult_le_right [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> x \<ge>\<^sub>R y \<Longrightarrow> z \<ge>\<^sub>R \<zero>\<^sub>R \<Longrightarrow> x *\<^sub>R z \<ge>\<^sub>R y *\<^sub>R z"
  by (tactic {* auto2s_tac @{context} (
    HAVE "x -\<^sub>R y \<ge>\<^sub>R \<zero>\<^sub>R" THEN
    HAVE "x *\<^sub>R z -\<^sub>R y *\<^sub>R z = (x -\<^sub>R y) *\<^sub>R z" THEN
    HAVE "x *\<^sub>R z -\<^sub>R y *\<^sub>R z \<ge>\<^sub>R \<zero>\<^sub>R") *})

lemma ord_ring_mult_le_left [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> x \<ge>\<^sub>R y \<Longrightarrow> z \<ge>\<^sub>R \<zero>\<^sub>R \<Longrightarrow> z *\<^sub>R x \<ge>\<^sub>R z *\<^sub>R y"
  by (tactic {* auto2s_tac @{context} (HAVE "x *\<^sub>R z \<ge>\<^sub>R y *\<^sub>R z") *})

lemma ord_ring_mult_lt_right [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> integral_domain(R) \<Longrightarrow> x >\<^sub>R y \<Longrightarrow> z >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> x *\<^sub>R z >\<^sub>R y *\<^sub>R z"
  by (tactic {* auto2s_tac @{context} (HAVE "x \<noteq> y" THEN HAVE "x *\<^sub>R z \<noteq> y *\<^sub>R z") *})

lemma ord_ring_mult_lt_left [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> integral_domain(R) \<Longrightarrow> x >\<^sub>R y \<Longrightarrow> z >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> z *\<^sub>R x >\<^sub>R z *\<^sub>R y"
  by (tactic {* auto2s_tac @{context} (HAVE "x *\<^sub>R z >\<^sub>R y *\<^sub>R z") *})

lemma ord_ring_mult_mix [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> p \<ge>\<^sub>R q \<Longrightarrow> q \<ge>\<^sub>R \<zero>\<^sub>R \<Longrightarrow> s \<ge>\<^sub>R \<zero>\<^sub>R \<Longrightarrow> r \<ge>\<^sub>R s \<Longrightarrow> p *\<^sub>R r \<ge>\<^sub>R q *\<^sub>R s"
  by (tactic {* auto2s_tac @{context} (HAVE "p *\<^sub>R r \<ge>\<^sub>R q *\<^sub>R r") *})

lemma ord_ring_mult_mix2 [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> integral_domain(R) \<Longrightarrow> p >\<^sub>R q \<Longrightarrow> q >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> s >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> r \<ge>\<^sub>R s \<Longrightarrow> p *\<^sub>R r >\<^sub>R q *\<^sub>R s"
  by (tactic {* auto2s_tac @{context} (HAVE "p *\<^sub>R r >\<^sub>R q *\<^sub>R r") *})

lemma ord_ring_mult_mix3 [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> integral_domain(R) \<Longrightarrow> p \<ge>\<^sub>R q \<Longrightarrow> q >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> s >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> r >\<^sub>R s \<Longrightarrow> p *\<^sub>R r >\<^sub>R q *\<^sub>R s"
  by auto2

lemma ord_ring_neg_ge_zero [backward]:
  "is_ord_ring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> a \<ge>\<^sub>R \<zero>\<^sub>R \<Longrightarrow> -\<^sub>R a \<le>\<^sub>R \<zero>\<^sub>R" by auto2
setup {* add_forward_prfstep_cond @{thm ord_ring_neg_ge_zero} [with_term "-\<^sub>?R ?a"] *}

lemma ord_ring_neg_gt_zero [backward]:
  "is_ord_ring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> a >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> -\<^sub>R a <\<^sub>R \<zero>\<^sub>R" by auto2
setup {* add_forward_prfstep_cond @{thm ord_ring_neg_gt_zero} [with_term "-\<^sub>?R ?a"] *}

lemma ord_ring_neg_le_zero [backward]:
  "is_ord_ring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> a \<le>\<^sub>R \<zero>\<^sub>R \<Longrightarrow> -\<^sub>R a \<ge>\<^sub>R \<zero>\<^sub>R" by auto2
setup {* add_forward_prfstep_cond @{thm ord_ring_neg_le_zero} [with_term "-\<^sub>?R ?a"] *}
  
lemma ord_ring_neg_lt_zero [backward]:
  "is_ord_ring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> a <\<^sub>R \<zero>\<^sub>R \<Longrightarrow> -\<^sub>R a >\<^sub>R \<zero>\<^sub>R" by auto2
setup {* add_forward_prfstep_cond @{thm ord_ring_neg_lt_zero} [with_term "-\<^sub>?R ?a"] *}

lemma ord_ring_mult_pos_neg [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> a \<ge>\<^sub>R \<zero>\<^sub>R \<Longrightarrow> b \<le>\<^sub>R \<zero>\<^sub>R \<Longrightarrow> a *\<^sub>R b \<le>\<^sub>R \<zero>\<^sub>R"
  by (tactic {* auto2s_tac @{context} (HAVE "a *\<^sub>R (-\<^sub>R b) \<ge>\<^sub>R \<zero>\<^sub>R") *})
setup {* add_forward_prfstep_cond @{thm ord_ring_mult_pos_neg} [with_term "?a *\<^sub>?R ?b"] *}

lemma ord_ring_mult_neg_pos [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> a \<le>\<^sub>R \<zero>\<^sub>R \<Longrightarrow> b \<ge>\<^sub>R \<zero>\<^sub>R \<Longrightarrow> a *\<^sub>R b \<le>\<^sub>R \<zero>\<^sub>R"
  by (tactic {* auto2s_tac @{context} (HAVE "b *\<^sub>R a \<ge>\<^sub>R \<zero>\<^sub>R") *})
setup {* add_forward_prfstep_cond @{thm ord_ring_mult_neg_pos} [with_term "?a *\<^sub>?R ?b"] *}
    
lemma ord_field_mult_le_cancel_right [forward]:
  "is_ord_ring(R) \<Longrightarrow> integral_domain(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z >\<^sub>R \<zero>\<^sub>R \<Longrightarrow>
   x *\<^sub>R z \<ge>\<^sub>R y *\<^sub>R z \<Longrightarrow> x \<ge>\<^sub>R y" by auto2

lemma ord_ring_mult_neg [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> a \<le>\<^sub>R \<zero>\<^sub>R \<Longrightarrow> b \<le>\<^sub>R \<zero>\<^sub>R \<Longrightarrow> a *\<^sub>R b \<ge>\<^sub>R \<zero>\<^sub>R"
  by (tactic {* auto2s_tac @{context} (HAVE "(-\<^sub>R a) *\<^sub>R (-\<^sub>R b) \<ge>\<^sub>R \<zero>\<^sub>R") *})
setup {* add_forward_prfstep_cond @{thm ord_ring_mult_neg} [with_term "?a *\<^sub>?R ?b"] *}

lemma ord_ring_square_ge_zero [resolve]:
  "is_ord_ring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> a *\<^sub>R a \<ge>\<^sub>R \<zero>\<^sub>R"
  by (tactic {* auto2s_tac @{context} (CASE "a \<ge>\<^sub>R \<zero>\<^sub>R") *})
    
lemma ord_ring_square_gt_zero [backward]:
  "is_ord_ring(R) \<Longrightarrow> integral_domain(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> a \<noteq> \<zero>\<^sub>R \<Longrightarrow> a *\<^sub>R a >\<^sub>R \<zero>\<^sub>R"
  by (tactic {* auto2s_tac @{context} (HAVE "a *\<^sub>R a \<noteq> \<zero>\<^sub>R") *})

lemma ord_ring_one_ge_zero [resolve]:
  "is_ord_ring(R) \<Longrightarrow> \<one>\<^sub>R >\<^sub>R \<zero>\<^sub>R"
  by (tactic {* auto2s_tac @{context} (HAVE "\<one>\<^sub>R = \<one>\<^sub>R *\<^sub>R \<one>\<^sub>R") *})

lemma ord_ring_mult_pos_strict [backward1]:
  "is_ord_ring(R) \<Longrightarrow> integral_domain(R) \<Longrightarrow> a >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> b >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> a *\<^sub>R b >\<^sub>R \<zero>\<^sub>R" by auto2
setup {* add_forward_prfstep_cond @{thm ord_ring_mult_pos_strict} [with_term "?a *\<^sub>?R ?b"] *}

lemma ord_ring_mult_pos_neg_strict [backward1]:
  "is_ord_ring(R) \<Longrightarrow> integral_domain(R) \<Longrightarrow> a >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> b <\<^sub>R \<zero>\<^sub>R \<Longrightarrow> a *\<^sub>R b <\<^sub>R \<zero>\<^sub>R" by auto2

lemma ord_ring_nonneg_add [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> a \<ge>\<^sub>R \<zero>\<^sub>R \<Longrightarrow> b \<ge>\<^sub>R \<zero>\<^sub>R \<Longrightarrow> a +\<^sub>R b \<ge>\<^sub>R \<zero>\<^sub>R" by auto2
    
lemma ord_ring_pos_add1 [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> a >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> b \<ge>\<^sub>R \<zero>\<^sub>R \<Longrightarrow> a +\<^sub>R b >\<^sub>R \<zero>\<^sub>R" by auto2

lemma ord_ring_pos_add2 [backward1, backward2]:
  "is_ord_ring(R) \<Longrightarrow> a \<ge>\<^sub>R \<zero>\<^sub>R \<Longrightarrow> b >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> a +\<^sub>R b >\<^sub>R \<zero>\<^sub>R" by auto2

lemma ord_ring_le_to_lt_plus_one [backward]:
  "is_ord_ring(R) \<Longrightarrow> x \<le>\<^sub>R y \<Longrightarrow> x <\<^sub>R y +\<^sub>R \<one>\<^sub>R"
  by (tactic {* auto2s_tac @{context} (HAVE "x +\<^sub>R \<zero>\<^sub>R <\<^sub>R y +\<^sub>R \<one>\<^sub>R") *})

lemma ord_ring_le_minus_switch [rewrite]:
  "is_ord_ring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> -\<^sub>R a \<le>\<^sub>R -\<^sub>R b \<longleftrightarrow> a \<ge>\<^sub>R b" by auto2

lemma ord_ring_le_minus_switch2 [resolve]:
  "is_ord_ring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> -\<^sub>R a \<le>\<^sub>R b \<Longrightarrow> a \<ge>\<^sub>R -\<^sub>R b" by auto2

lemma ord_ring_le_minus_switch3 [resolve]:
  "is_ord_ring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> -\<^sub>R a \<ge>\<^sub>R b \<Longrightarrow> a \<le>\<^sub>R -\<^sub>R b" by auto2

lemma ord_ring_of_nat_Suc:
  "is_ord_ring(R) \<Longrightarrow> n \<in>. \<nat> \<Longrightarrow> of_nat(R,n) <\<^sub>R of_nat(R, n +\<^sub>\<nat> 1)" by auto2
setup {* add_forward_prfstep_cond @{thm ord_ring_of_nat_Suc} [with_term "of_nat(?R, ?n +\<^sub>\<nat> 1)"] *}

lemma ord_ring_of_nat_ge_zero [backward]:
  "is_ord_ring(R) \<Longrightarrow> n \<in> nat \<Longrightarrow> of_nat(R,n) \<ge>\<^sub>R \<zero>\<^sub>R"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "n \<in> nat" "of_nat(R,n) \<ge>\<^sub>R \<zero>\<^sub>R") *})
setup {* del_prfstep_thm @{thm ord_ring_of_nat_Suc} *}

lemma ord_field_char_zero' [backward]:
  "is_ord_ring(R) \<Longrightarrow> n \<in> nat \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> of_nat(R,n) >\<^sub>R \<zero>\<^sub>R"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "m\<in>.\<nat>, n = m +\<^sub>\<nat> 1" THEN HAVE "of_nat(R,m) \<ge>\<^sub>R \<zero>\<^sub>R") *})

lemma ord_ring_of_nat_le [backward]:
  "is_ord_ring(R) \<Longrightarrow> m \<le>\<^sub>\<nat> n \<Longrightarrow> of_nat(R,m) \<le>\<^sub>R of_nat(R,n)"
  by (tactic {* auto2s_tac @{context} (CHOOSE "p\<in>.\<nat>, n = m +\<^sub>\<nat> p") *})
    
lemma ord_ring_of_nat_less [backward]:
  "is_ord_ring(R) \<Longrightarrow> m <\<^sub>\<nat> n \<Longrightarrow> of_nat(R,m) <\<^sub>R of_nat(R,n)"
  by (tactic {* auto2s_tac @{context} (CHOOSE "p\<in>nat, p\<noteq>0 \<and> n = m +\<^sub>\<nat> p") *})
    
lemma ord_ring_of_nat_le_back [forward]:
  "is_ord_ring(R) \<Longrightarrow> m \<in> nat \<Longrightarrow> n \<in> nat \<Longrightarrow> of_nat(R,m) \<le>\<^sub>R of_nat(R,n) \<Longrightarrow> m \<le>\<^sub>\<nat> n"
  by (tactic {* auto2s_tac @{context} (HAVE "\<not>of_nat(R,n) <\<^sub>R of_nat(R,m)") *})

lemma ord_ring_of_nat_eq [forward]:
  "is_ord_ring(R) \<Longrightarrow> m \<in> nat \<Longrightarrow> n \<in> nat \<Longrightarrow> of_nat(R,m) = of_nat(R,n) \<Longrightarrow> m = n"
  by (tactic {* auto2s_tac @{context} (
    CASE "m <\<^sub>\<nat> n" WITH HAVE "of_nat(R,m) <\<^sub>R of_nat(R,n)" THEN
    CASE "m >\<^sub>\<nat> n" WITH HAVE "of_nat(R,m) >\<^sub>R of_nat(R,n)") *})

lemma ord_ring_of_nat_ge_one [backward]:
  "is_ord_ring(R) \<Longrightarrow> a \<in> nat \<Longrightarrow> b \<in> nat \<Longrightarrow> of_nat(R,a) >\<^sub>R of_nat(R,b) \<Longrightarrow>
   of_nat(R,a) \<ge>\<^sub>R of_nat(R,b) +\<^sub>R 1\<^sub>R"
  by (tactic {* auto2s_tac @{context} (HAVE "of_nat(R,b) +\<^sub>R 1\<^sub>R = of_nat(R, b +\<^sub>\<nat> 1)") *})

lemma ord_ring_has_pos_greater [backward]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<exists>y\<in>.R. y >\<^sub>R \<zero>\<^sub>R \<and> y \<ge>\<^sub>R x"
  by (tactic {* auto2s_tac @{context} (
    LET "m = max(R,\<one>\<^sub>R,x)" THEN HAVE "\<one>\<^sub>R >\<^sub>R \<zero>\<^sub>R") *})

lemma ord_ring_is_unbounded [forward]:
  "is_ord_ring(R) \<Longrightarrow> order_unbounded(R)"
  by (tactic {* auto2s_tac @{context} (
    HAVE_RULE "\<forall>x\<in>.R. \<exists>y. y <\<^sub>R x" WITH (
      HAVE "x <\<^sub>R x +\<^sub>R 1\<^sub>R" THEN HAVE "x -\<^sub>R 1\<^sub>R <\<^sub>R x") THEN
    HAVE_RULE "\<forall>x\<in>.R. \<exists>y. y >\<^sub>R x" WITH HAVE "x +\<^sub>R 1\<^sub>R >\<^sub>R x") *})

lemma power_gt_0 [backward]:
  "is_ord_ring(R) \<Longrightarrow> integral_domain(R) \<Longrightarrow> e \<in> nat \<Longrightarrow> b >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> b ^\<^sub>R e >\<^sub>R \<zero>\<^sub>R"
  by (tactic {* auto2s_tac @{context} (INDUCT_ON "e \<in> nat" "b ^\<^sub>R e >\<^sub>R \<zero>\<^sub>R") *})
    
lemma power_gt_n [resolve]: "is_ord_ring(R) \<Longrightarrow> n \<in> nat \<Longrightarrow> of_nat(R,n) <\<^sub>R 2\<^sub>R ^\<^sub>R n"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>m\<in>nat. of_nat(R, m) <\<^sub>R 2\<^sub>R ^\<^sub>R m \<longrightarrow> of_nat(R, m +\<^sub>\<nat> 1) <\<^sub>R 2\<^sub>R ^\<^sub>R (m +\<^sub>\<nat> 1)" WITH (
      HAVE "2\<^sub>R ^\<^sub>R (m +\<^sub>\<nat> 1) = 2\<^sub>R ^\<^sub>R m +\<^sub>R 2\<^sub>R ^\<^sub>R m") THEN
    INDUCT_ON "n \<in> nat" "of_nat(R,n) <\<^sub>R 2\<^sub>R ^\<^sub>R n") *})

section {* Subsets of an ordered ring *}
  
definition pos_elts :: "i \<Rightarrow> i" where [rewrite]:
  "pos_elts(R) = {x\<in>.R. x >\<^sub>R \<zero>\<^sub>R}"
  
lemma pos_eltsD [forward]: "x \<in> pos_elts(R) \<Longrightarrow> x \<in>. R \<and> x >\<^sub>R \<zero>\<^sub>R" by auto2
lemma pos_eltsI [backward2]: "x \<in>. R \<Longrightarrow> x >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> x \<in> pos_elts(R)" by auto2
lemma pos_elts_one [resolve]: "is_ord_ring(R) \<Longrightarrow> \<one>\<^sub>R \<in> pos_elts(R)" by auto2
lemma pos_elts_mult [typing]:
  "is_ord_ring(R) \<Longrightarrow> integral_domain(R) \<Longrightarrow> x \<in> pos_elts(R) \<Longrightarrow> y \<in> pos_elts(R) \<Longrightarrow> x *\<^sub>R y \<in> pos_elts(R)" by auto2
lemma pos_elts_add [typing]:
  "is_ord_ring(R) \<Longrightarrow> x \<in> pos_elts(R) \<Longrightarrow> y \<in> pos_elts(R) \<Longrightarrow> x +\<^sub>R y \<in> pos_elts(R)" by auto2
    
section {* Construction of ordered ring from non-negative elements *}

(* See Bourbaki, Algebra VI.2.1 *)

definition subset_add_closed :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "subset_add_closed(R,S) \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. x +\<^sub>R y \<in> S)"

lemma subset_add_closedD [typing]:
  "subset_add_closed(R,S) \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x +\<^sub>R y \<in> S" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm subset_add_closed_def} *}
  
definition subset_mult_closed :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "subset_mult_closed(R,S) \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. x *\<^sub>R y \<in> S)"
  
lemma subset_mult_closedD [typing]:
  "subset_mult_closed(R,S) \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x *\<^sub>R y \<in> S" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm subset_mult_closed_def} *}

definition nonneg_compat_inter :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "nonneg_compat_inter(R,S) \<longleftrightarrow> (\<forall>x\<in>S. -\<^sub>R x \<in> S \<longrightarrow> x = \<zero>\<^sub>R)"

lemma nonneg_compat_interD [forward]:
  "nonneg_compat_inter(R,S) \<Longrightarrow> -\<^sub>R x \<in> S \<Longrightarrow> x \<in> S \<Longrightarrow> x = \<zero>\<^sub>R" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm nonneg_compat_inter_def} *}

definition nonneg_compat_union :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "nonneg_compat_union(R,S) \<longleftrightarrow> (\<forall>x\<in>.R. x \<in> S \<or> -\<^sub>R x \<in> S)"
  
lemma nonneg_compat_unionD [forward]:
  "x \<in>. R \<Longrightarrow> nonneg_compat_union(R,S) \<Longrightarrow> -\<^sub>R x \<notin> S \<Longrightarrow> x \<in> S" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm nonneg_compat_union_def} *}

definition ord_ring_from_nonneg :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "ord_ring_from_nonneg(R,S) =
    OrdRing(carrier(R), \<zero>\<^sub>R, \<lambda>x y. x +\<^sub>R y, \<one>\<^sub>R, \<lambda>x y. x *\<^sub>R y, \<lambda>x y. y -\<^sub>R x \<in> S)"
  
definition nonneg_compat :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "nonneg_compat(R,S) \<longleftrightarrow>
    (\<zero>\<^sub>R \<in> S \<and> subset_add_closed(R,S) \<and> subset_mult_closed(R,S) \<and>
     nonneg_compat_inter(R,S) \<and> nonneg_compat_union(R,S))"

lemma ord_ring_from_nonneg_is_ord_ring_raw [forward]:
  "is_ring_raw(R) \<Longrightarrow> ord_ring_form(ord_ring_from_nonneg(R,S))" by auto2

lemma ord_ring_from_nonneg_eq_str:
  "is_ring_raw(R) \<Longrightarrow> eq_str_ring(R,ord_ring_from_nonneg(R,S))" by auto2
setup {* add_forward_prfstep_cond @{thm ord_ring_from_nonneg_eq_str} [with_term "ord_ring_from_nonneg(?R,?S)"] *}

lemma ord_ring_from_nonneg_eval [rewrite]:
  "is_ring_raw(R) \<Longrightarrow> A = ord_ring_from_nonneg(R,S) \<Longrightarrow> is_abgroup(A) \<Longrightarrow>
   x \<in>. A \<Longrightarrow> y \<in>. A \<Longrightarrow> x \<le>\<^sub>A y \<longleftrightarrow> y -\<^sub>A x \<in> S" by auto2
setup {* del_prfstep_thm @{thm ord_ring_from_nonneg_def} *}

lemma ord_ring_from_nonneg_is_linorder [forward]:
  "is_ring_raw(R) \<Longrightarrow> A = ord_ring_from_nonneg(R,S) \<Longrightarrow> is_comm_ring(A) \<Longrightarrow>
   nonneg_compat(A,S) \<Longrightarrow> linorder(A)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x y z. x \<le>\<^sub>A y \<longrightarrow> y \<le>\<^sub>A z \<longrightarrow> x \<le>\<^sub>A z" WITH
      HAVE "z -\<^sub>A x = (z -\<^sub>A y) +\<^sub>A (y -\<^sub>A x)" THEN
    HAVE "\<forall>x y. x \<le>\<^sub>A y \<longrightarrow> y \<le>\<^sub>A x \<longrightarrow> x = y" WITH
      HAVE "-\<^sub>A (y -\<^sub>A x) = x -\<^sub>A y" THEN
    HAVE "\<forall>x\<in>.A. \<forall>y\<in>.A. x \<le>\<^sub>A y \<or> x \<ge>\<^sub>A y" WITH
      HAVE "-\<^sub>A (y -\<^sub>A x) = x -\<^sub>A y") *})

lemma ord_ring_from_nonneg_compat_plus [forward]:
  "is_ring_raw(R) \<Longrightarrow> A = ord_ring_from_nonneg(R,S) \<Longrightarrow> is_comm_ring(A) \<Longrightarrow>
   nonneg_compat(A,S) \<Longrightarrow> ord_ring_add_left(A)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>a\<in>.A. \<forall>b c. b \<le>\<^sub>A c \<longrightarrow> a +\<^sub>A b \<le>\<^sub>A a +\<^sub>A c" WITH
      HAVE "(a +\<^sub>R c) -\<^sub>R (a +\<^sub>R b) = c -\<^sub>R b") *})

lemma ord_ring_from_nonneg_is_ord_ring [forward]:
  "is_ring_raw(R) \<Longrightarrow> A = ord_ring_from_nonneg(R,S) \<Longrightarrow> is_comm_ring(A) \<Longrightarrow>
   nonneg_compat(A,S) \<Longrightarrow> is_ord_ring(ord_ring_from_nonneg(R,S))" by auto2
  
end
