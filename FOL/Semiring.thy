theory Semiring
imports Group AbGroup OrderRel
begin
  
(* We define semirings to be commutative (it is only used for Nat). *)
  
section {* Semirings *}

definition is_zero_mult :: "i \<Rightarrow> o" where [rewrite]:
  "is_zero_mult(R) \<longleftrightarrow> (\<forall>x\<in>.R. \<zero>\<^sub>R *\<^sub>R x = \<zero>\<^sub>R \<and> x *\<^sub>R \<zero>\<^sub>R = \<zero>\<^sub>R)"
setup {* add_property_const @{term is_zero_mult} *}
  
lemma is_zero_multD [rewrite]:
  "is_zero_mult(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<zero>\<^sub>R *\<^sub>R x = \<zero>\<^sub>R"
  "is_zero_mult(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> x *\<^sub>R \<zero>\<^sub>R = \<zero>\<^sub>R" by auto2+
setup {* del_prfstep_thm_str "@eqforward" @{thm is_zero_mult_def} *}

definition is_semiring :: "i \<Rightarrow> o" where [rewrite]:
  "is_semiring(R) \<longleftrightarrow> (is_ring_raw(R) \<and> is_ab_monoid(R) \<and> is_monoid(R) \<and>
    is_times_comm(R) \<and> is_left_distrib(R) \<and> is_zero_mult(R) \<and> \<zero>\<^sub>R \<noteq> \<one>\<^sub>R)"
setup {* add_property_const @{term is_semiring} *}

lemma is_semiringD [forward]:
  "is_semiring(R) \<Longrightarrow> is_ring_raw(R)"
  "is_semiring(R) \<Longrightarrow> is_ab_monoid(R)"
  "is_semiring(R) \<Longrightarrow> is_monoid(R)"
  "is_semiring(R) \<Longrightarrow> is_times_comm(R)"
  "is_semiring(R) \<Longrightarrow> is_left_distrib(R)"
  "is_semiring(R) \<Longrightarrow> is_zero_mult(R)" by auto2+

lemma is_semiringD' [resolve]: "is_semiring(R) \<Longrightarrow> \<zero>\<^sub>R \<noteq> \<one>\<^sub>R" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm is_semiring_def} *}

ML_file "alg_semiring.ML"

section {* Ordered semirings *}

definition is_ord_semiring :: "i \<Rightarrow> o" where [rewrite]:
  "is_ord_semiring(R) \<longleftrightarrow> (is_ord_ring_raw(R) \<and> is_semiring(R) \<and> linorder(R) \<and>
                           ord_ring_add_left(R) \<and> ord_semiring_mult_left(R))"
setup {* add_property_const @{term is_ord_semiring} *}

lemma is_ord_semiringD [forward]:
  "is_ord_semiring(R) \<Longrightarrow> is_ord_ring_raw(R)"
  "is_ord_semiring(R) \<Longrightarrow> is_semiring(R)"
  "is_ord_semiring(R) \<Longrightarrow> linorder(R)"
  "is_ord_semiring(R) \<Longrightarrow> ord_ring_add_left(R)"
  "is_ord_semiring(R) \<Longrightarrow> ord_semiring_mult_left(R)" by auto2+
setup {* del_prfstep_thm_str "@eqforward" @{thm is_ord_semiring_def} *}

lemma ord_semiring_mult_right [backward]:
  "is_ord_semiring(R) \<Longrightarrow> c \<in>. R \<Longrightarrow> a \<le>\<^sub>R b \<Longrightarrow> a *\<^sub>R c \<le>\<^sub>R b *\<^sub>R c"
  by (tactic {* auto2s_tac @{context} (HAVE "c *\<^sub>R a \<le>\<^sub>R c *\<^sub>R b") *})

lemma ord_semiring_add_right [backward]:
  "is_ord_semiring(R) \<Longrightarrow> c \<in>. R \<Longrightarrow> a \<le>\<^sub>R b \<Longrightarrow> a +\<^sub>R c \<le>\<^sub>R b +\<^sub>R c"
  by (tactic {* auto2s_tac @{context} (HAVE "c +\<^sub>R a \<le>\<^sub>R c +\<^sub>R b") *})

lemma ord_semiring_add_mix [backward1, backward2]:
  "is_ord_semiring(R) \<Longrightarrow> p \<le>\<^sub>R q \<Longrightarrow> r \<le>\<^sub>R s \<Longrightarrow> p +\<^sub>R r \<le>\<^sub>R q +\<^sub>R s"
  by (tactic {* auto2s_tac @{context} (HAVE "p +\<^sub>R r \<le>\<^sub>R p +\<^sub>R s") *})

end
