theory Rat
imports Int Field
begin

section {* Definition of rational numbers *}

definition rat_rel_space :: i where [rewrite]:
  "rat_rel_space = carrier(\<int>)\<times>pos_elts(\<int>)"

definition rat_rel :: i where [rewrite]:
  "rat_rel = Equiv(rat_rel_space, \<lambda>p q. let \<langle>a,b\<rangle> = p; \<langle>c,d\<rangle> = q in a *\<^sub>\<int> d = b *\<^sub>\<int> c)"
notation rat_rel ("\<R>")

lemma rat_rel_spaceI [typing]: "x \<in> int \<Longrightarrow> y >\<^sub>\<int> \<zero>\<^sub>\<int> \<Longrightarrow> \<langle>x,y\<rangle> \<in>. \<R>" by auto2
lemma rat_rel_spaceI' [typing]: "x \<in> int \<Longrightarrow> \<langle>x,\<one>\<^sub>\<int>\<rangle> \<in>. \<R>" by auto2
lemma rat_rel_spaceD [forward]: "p \<in>. \<R> \<Longrightarrow> p = \<langle>fst(p),snd(p)\<rangle> \<and> fst(p) \<in> int \<and> snd(p) >\<^sub>\<int> \<zero>\<^sub>\<int>" by auto2
setup {* del_prfstep_thm @{thm rat_rel_space_def} *}

lemma rat_rel_trans [backward1]:
  "a1 \<in>. \<int> \<Longrightarrow> a2 \<in>. \<int> \<Longrightarrow> b1 \<in>. \<int> \<Longrightarrow> b2 \<in>. \<int> \<Longrightarrow> c1 \<in>. \<int> \<Longrightarrow> c2 \<in>. \<int> \<Longrightarrow> b2 \<noteq> \<zero>\<^sub>\<int> \<Longrightarrow>
   a1 *\<^sub>\<int> b2 = a2 *\<^sub>\<int> b1 \<Longrightarrow> b1 *\<^sub>\<int> c2 = b2 *\<^sub>\<int> c1 \<Longrightarrow> a1 *\<^sub>\<int> c2 = a2 *\<^sub>\<int> c1"
  by (tactic {* auto2s_tac @{context} (
    HAVE "(a1 *\<^sub>\<int> c2) *\<^sub>\<int> b2 = (a1 *\<^sub>\<int> b2) *\<^sub>\<int> c2" THEN
    HAVE "(a2 *\<^sub>\<int> b1) *\<^sub>\<int> c2 = a2 *\<^sub>\<int> (b1 *\<^sub>\<int> c2)" THEN
    HAVE "a2 *\<^sub>\<int> (b2 *\<^sub>\<int> c1) = (a2 *\<^sub>\<int> c1) *\<^sub>\<int> b2") *})

lemma rat_rel_is_rel [typing]: "\<R> \<in> equiv_space(rat_rel_space)" by auto2
setup {* del_prfstep_thm @{thm rat_rel_trans} *}

lemma rat_rel_eval:
  "x \<in>. \<R> \<Longrightarrow> y \<in>. \<R> \<Longrightarrow> x \<sim>\<^sub>\<R> y \<longleftrightarrow> (fst(x) *\<^sub>\<int> snd(y) = snd(x) *\<^sub>\<int> fst(y))" by auto2
setup {* add_rewrite_rule_cond @{thm rat_rel_eval} [with_cond "?x \<noteq> ?y"] *}
setup {* del_prfstep_thm @{thm rat_rel_def} *}

definition rat :: i where [rewrite_bidir]:
  "rat = carrier(\<R>) // \<R>"
  
abbreviation Rat :: "i \<Rightarrow> i" where "Rat(p) \<equiv> equiv_class(\<R>,p)"

section {* Rationals as a ring *}

definition rat_mult_raw :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "rat_mult_raw(p,q) = \<langle>fst(p)*\<^sub>\<int>fst(q),snd(p)*\<^sub>\<int>snd(q)\<rangle>"
setup {* register_wellform_data ("rat_mult_raw(p,q)", ["p \<in>. \<R>", "q \<in>. \<R>"]) *}

lemma rat_mult_raw_eval [rewrite]: "rat_mult_raw(\<langle>a,b\<rangle>,\<langle>c,d\<rangle>) = \<langle>a*\<^sub>\<int>c, b*\<^sub>\<int>d\<rangle>" by auto2
setup {* del_prfstep_thm @{thm rat_mult_raw_def} *}

definition rat_add_raw :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "rat_add_raw(p,q) = \<langle>fst(p)*\<^sub>\<int>snd(q)+\<^sub>\<int>snd(p)*\<^sub>\<int>fst(q), snd(p)*\<^sub>\<int>snd(q)\<rangle>"
setup {* register_wellform_data ("rat_add_raw(p,q)", ["p \<in>. \<R>", "q \<in>. \<R>"]) *}

lemma rat_add_raw_eval [rewrite]: "rat_add_raw(\<langle>a,b\<rangle>,\<langle>c,d\<rangle>) = \<langle>a*\<^sub>\<int>d+\<^sub>\<int>b*\<^sub>\<int>c, b*\<^sub>\<int>d\<rangle>" by auto2
setup {* del_prfstep_thm @{thm rat_add_raw_def} *}

definition nonneg_rat_raw :: "i \<Rightarrow> o" where [rewrite]:
  "nonneg_rat_raw(p) \<longleftrightarrow> fst(p) \<ge>\<^sub>\<int> \<zero>\<^sub>\<int>"

definition nonneg_rat :: "i \<Rightarrow> o" where [rewrite]:
  "nonneg_rat(x) \<longleftrightarrow> nonneg_rat_raw(rep(\<R>,x))"
setup {* add_property_const @{term nonneg_rat} *}

definition nonneg_rats :: i where [rewrite]:
  "nonneg_rats = {x\<in>rat. nonneg_rat(x)}"

definition rat_ring :: i where [rewrite]:
  "rat_ring = Ring(rat, Rat(\<langle>\<zero>\<^sub>\<int>,\<one>\<^sub>\<int>\<rangle>), \<lambda>x y. Rat(rat_add_raw(rep(\<R>,x), rep(\<R>,y))),
                        Rat(\<langle>\<one>\<^sub>\<int>,\<one>\<^sub>\<int>\<rangle>), \<lambda>x y. Rat(rat_mult_raw(rep(\<R>,x), rep(\<R>,y))))"

lemma rat_ring_is_ring_raw [forward]: "ring_form(rat_ring)" by auto2

definition rat_ord_ring :: i  ("\<rat>") where [rewrite]:
  "rat_ord_ring = ord_ring_from_nonneg(rat_ring, nonneg_rats)"

lemma rat_is_ring_raw [forward]: "is_ring_raw(\<rat>)" by auto2
lemma rat_carrier [rewrite_bidir]: "carrier(\<rat>) = rat" by auto2
lemma rat_evals [rewrite]:
  "\<zero>\<^sub>\<rat> = Rat(\<langle>\<zero>\<^sub>\<int>,\<one>\<^sub>\<int>\<rangle>)"
  "\<one>\<^sub>\<rat> = Rat(\<langle>\<one>\<^sub>\<int>,\<one>\<^sub>\<int>\<rangle>)"
  "x \<in>. \<rat> \<Longrightarrow> y \<in>. \<rat> \<Longrightarrow> x +\<^sub>\<rat> y = Rat(rat_add_raw(rep(\<R>,x), rep(\<R>,y)))"
  "x \<in>. \<rat> \<Longrightarrow> y \<in>. \<rat> \<Longrightarrow> x *\<^sub>\<rat> y = Rat(rat_mult_raw(rep(\<R>,x), rep(\<R>,y)))" by auto2+

lemma rat_is_ord_field_prep [forward]:
  "is_field(\<rat>) \<Longrightarrow> nonneg_compat(\<rat>,nonneg_rats) \<Longrightarrow> is_ord_field(\<rat>)" by auto2
    
setup {* fold del_prfstep_thm [@{thm rat_ring_def}, @{thm rat_ord_ring_def}] *}
    
lemma rat_zero_raw_mem [typing]: "\<langle>\<zero>\<^sub>\<int>,\<one>\<^sub>\<int>\<rangle> \<in>. \<R>" by auto2
lemma rat_one_raw_mem [typing]: "\<langle>\<one>\<^sub>\<int>,\<one>\<^sub>\<int>\<rangle> \<in>. \<R>" by auto2

lemma rat_choose_rep: "r \<in>. \<rat> \<Longrightarrow> r = Rat(rep(\<R>,r))" by auto2
setup {* add_rewrite_rule_cond @{thm rat_choose_rep} [with_filt (size1_filter "r")] *}

section {* Multiplication on rationals *}

lemma rat_mult_raw_type [typing]:
  "\<langle>a,b\<rangle> \<in>. \<R> \<Longrightarrow> \<langle>c,d\<rangle> \<in>. \<R> \<Longrightarrow> rat_mult_raw(\<langle>a,b\<rangle>,\<langle>c,d\<rangle>) \<in>. \<R>" by auto2

lemma rat_mult_raw_compat1 [backward]:
  "\<langle>c,d\<rangle> \<in>. \<R> \<Longrightarrow> \<langle>a',b'\<rangle> \<sim>\<^sub>\<R> \<langle>a,b\<rangle> \<Longrightarrow> rat_mult_raw(\<langle>a',b'\<rangle>,\<langle>c,d\<rangle>) \<sim>\<^sub>\<R> rat_mult_raw(\<langle>a,b\<rangle>,\<langle>c,d\<rangle>)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "(a' *\<^sub>\<int> c) *\<^sub>\<int> (b *\<^sub>\<int> d) = (a' *\<^sub>\<int> b) *\<^sub>\<int> (c *\<^sub>\<int> d)" THEN
    HAVE "(b' *\<^sub>\<int> d) *\<^sub>\<int> (a *\<^sub>\<int> c) = (b' *\<^sub>\<int> a) *\<^sub>\<int> (c *\<^sub>\<int> d)") *})

lemma rat_mult_raw_compat2 [backward]:
  "\<langle>a,b\<rangle> \<in>. \<R> \<Longrightarrow> \<langle>c',d'\<rangle> \<sim>\<^sub>\<R> \<langle>c,d\<rangle> \<Longrightarrow> rat_mult_raw(\<langle>a,b\<rangle>,\<langle>c',d'\<rangle>) \<sim>\<^sub>\<R> rat_mult_raw(\<langle>a,b\<rangle>,\<langle>c,d\<rangle>)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "(a *\<^sub>\<int> c') *\<^sub>\<int> (b *\<^sub>\<int> d) = (a *\<^sub>\<int> b) *\<^sub>\<int> (c' *\<^sub>\<int> d)" THEN
    HAVE "(b *\<^sub>\<int> d') *\<^sub>\<int> (a *\<^sub>\<int> c) = (a *\<^sub>\<int> b) *\<^sub>\<int> (d' *\<^sub>\<int> c)") *})

lemma rat_mult_raw_compat [resolve]: "compat_meta_bin(\<R>, rat_mult_raw)" by auto2

lemma rat_mult_eval [rewrite]:
  "x \<in>. \<R> \<Longrightarrow> y \<in>. \<R> \<Longrightarrow> Rat(x) *\<^sub>\<rat> Rat(y) = Rat(rat_mult_raw(x,y))"
  by (tactic {* auto2s_tac @{context} (HAVE "compat_meta_bin(\<R>, rat_mult_raw)") *})
setup {* del_prfstep_thm @{thm rat_mult_raw_compat} *}
setup {* del_prfstep_thm @{thm rat_evals(4)} *}

lemma rat_mult_comm [forward]: "is_times_comm(\<rat>)" by auto2
lemma rat_mult_assoc [forward]: "is_times_assoc(\<rat>)" by auto2
    
section {* Addition on rationals *}

lemma rat_add_raw_type [typing]:
  "\<langle>a,b\<rangle> \<in>. \<R> \<Longrightarrow> \<langle>c,d\<rangle> \<in>. \<R> \<Longrightarrow> rat_add_raw(\<langle>a,b\<rangle>,\<langle>c,d\<rangle>) \<in>. \<R>" by auto2

lemma rat_add_raw_compat1 [backward]:
  "\<langle>c,d\<rangle> \<in>. \<R> \<Longrightarrow> \<langle>a',b'\<rangle> \<sim>\<^sub>\<R> \<langle>a,b\<rangle> \<Longrightarrow> rat_add_raw(\<langle>a',b'\<rangle>,\<langle>c,d\<rangle>) \<sim>\<^sub>\<R> rat_add_raw(\<langle>a,b\<rangle>,\<langle>c,d\<rangle>)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "(a'*\<^sub>\<int>d +\<^sub>\<int> b'*\<^sub>\<int>c) *\<^sub>\<int> (b*\<^sub>\<int>d) = (a'*\<^sub>\<int>b)*\<^sub>\<int>d*\<^sub>\<int>d +\<^sub>\<int> b*\<^sub>\<int>b'*\<^sub>\<int>c*\<^sub>\<int>d" THEN
    HAVE "(b'*\<^sub>\<int>d) *\<^sub>\<int> (a*\<^sub>\<int>d +\<^sub>\<int> b*\<^sub>\<int>c) = (b'*\<^sub>\<int>a)*\<^sub>\<int>d*\<^sub>\<int>d +\<^sub>\<int> b*\<^sub>\<int>b'*\<^sub>\<int>c*\<^sub>\<int>d") *})

lemma rat_add_raw_compat2 [backward]:
  "\<langle>a,b\<rangle> \<in>. \<R> \<Longrightarrow> \<langle>c',d'\<rangle> \<sim>\<^sub>\<R> \<langle>c,d\<rangle> \<Longrightarrow> rat_add_raw(\<langle>a,b\<rangle>,\<langle>c',d'\<rangle>) \<sim>\<^sub>\<R> rat_add_raw(\<langle>a,b\<rangle>,\<langle>c,d\<rangle>)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "(a*\<^sub>\<int>d' +\<^sub>\<int> b*\<^sub>\<int>c') *\<^sub>\<int> (b*\<^sub>\<int>d) = (c'*\<^sub>\<int>d)*\<^sub>\<int>b*\<^sub>\<int>b +\<^sub>\<int> a*\<^sub>\<int>b*\<^sub>\<int>d*\<^sub>\<int>d'" THEN
    HAVE "(b*\<^sub>\<int>d') *\<^sub>\<int> (a*\<^sub>\<int>d +\<^sub>\<int> b*\<^sub>\<int>c)  = (d'*\<^sub>\<int>c)*\<^sub>\<int>b*\<^sub>\<int>b +\<^sub>\<int> a*\<^sub>\<int>b*\<^sub>\<int>d*\<^sub>\<int>d'") *})  

lemma rat_add_raw_compat [resolve]: "compat_meta_bin(\<R>, rat_add_raw)" by auto2

lemma rat_add_eval [rewrite]:
  "x \<in>. \<R> \<Longrightarrow> y \<in>. \<R> \<Longrightarrow> Rat(x) +\<^sub>\<rat> Rat(y) = Rat(rat_add_raw(x,y))"
  by (tactic {* auto2s_tac @{context} (HAVE "compat_meta_bin(\<R>, rat_add_raw)") *})
setup {* del_prfstep_thm @{thm rat_add_raw_compat} *}
setup {* del_prfstep_thm @{thm rat_evals(3)} *}

lemma rat_add_comm [forward]: "is_plus_comm(\<rat>)" by auto2

lemma rat_add_raw_assoc [rewrite]:
  "\<langle>a,b\<rangle> \<in>. \<R> \<Longrightarrow> \<langle>c,d\<rangle> \<in>. \<R> \<Longrightarrow> \<langle>e,f\<rangle> \<in>. \<R> \<Longrightarrow>
   rat_add_raw(rat_add_raw(\<langle>a,b\<rangle>,\<langle>c,d\<rangle>),\<langle>e,f\<rangle>) = rat_add_raw(\<langle>a,b\<rangle>,rat_add_raw(\<langle>c,d\<rangle>,\<langle>e,f\<rangle>))"
  by (tactic {* auto2s_tac @{context} (
    HAVE "(a*\<^sub>\<int>d +\<^sub>\<int> b*\<^sub>\<int>c) *\<^sub>\<int> f +\<^sub>\<int> (b*\<^sub>\<int>d)*\<^sub>\<int>e = a*\<^sub>\<int>(d*\<^sub>\<int>f) +\<^sub>\<int> b *\<^sub>\<int> (c*\<^sub>\<int>f +\<^sub>\<int> d*\<^sub>\<int>e)") *})

lemma rat_add_assoc [forward]: "is_plus_assoc(\<rat>)" by auto2
setup {* del_prfstep_thm @{thm rat_add_raw_assoc} *}

lemma rat_distrib_l_raw [resolve]:
  "\<langle>a,b\<rangle> \<in>. \<R> \<Longrightarrow> \<langle>c,d\<rangle> \<in>. \<R> \<Longrightarrow> \<langle>e,f\<rangle> \<in>. \<R> \<Longrightarrow>
   rat_mult_raw(\<langle>a,b\<rangle>,rat_add_raw(\<langle>c,d\<rangle>,\<langle>e,f\<rangle>)) \<sim>\<^sub>\<R> rat_add_raw(rat_mult_raw(\<langle>a,b\<rangle>,\<langle>c,d\<rangle>),rat_mult_raw(\<langle>a,b\<rangle>,\<langle>e,f\<rangle>))"
  by (tactic {* auto2s_tac @{context} (
    HAVE "a*\<^sub>\<int>(c*\<^sub>\<int>f+\<^sub>\<int>d*\<^sub>\<int>e) *\<^sub>\<int> ((b*\<^sub>\<int>d)*\<^sub>\<int>(b*\<^sub>\<int>f)) = b*\<^sub>\<int>(d*\<^sub>\<int>f) *\<^sub>\<int> ((a*\<^sub>\<int>c)*\<^sub>\<int>(b*\<^sub>\<int>f) +\<^sub>\<int> (b*\<^sub>\<int>d)*\<^sub>\<int>(a*\<^sub>\<int>e))") *})

lemma rat_distrib_l [forward]: "is_left_distrib(\<rat>)" by auto2
setup {* del_prfstep_thm @{thm rat_distrib_l_raw} *}

section {* 0 and 1 *}
  
lemma rat_is_add_id [forward]: "is_add_id(\<rat>)" by auto2
lemma rat_is_mult_id [forward]: "is_mult_id(\<rat>)" by auto2
lemma rat_zero_neq_one [resolve]: "\<zero>\<^sub>\<rat> \<noteq> \<one>\<^sub>\<rat>" by auto2

section {* Negation on rationals *}
  
definition rat_neg_raw :: "i \<Rightarrow> i" where [rewrite]:
  "rat_neg_raw(p) = \<langle>-\<^sub>\<int> fst(p), snd(p)\<rangle>"
  
definition rat_neg :: "i \<Rightarrow> i" where [rewrite]:
  "rat_neg(x) = Rat(rat_neg_raw(rep(\<R>,x)))"
  
lemma rat_neg_typing [typing]: "x \<in>. \<rat> \<Longrightarrow> rat_neg(x) \<in>. \<rat>" by auto2

lemma rat_add_raw_eval_eq_denom [rewrite]:
  "\<langle>p,r\<rangle> \<in>. \<R> \<Longrightarrow> \<langle>q,r\<rangle> \<in>. \<R> \<Longrightarrow> Rat(\<langle>p,r\<rangle>) +\<^sub>\<rat> Rat(\<langle>q,r\<rangle>) = Rat(\<langle>p+\<^sub>\<int>q, r\<rangle>)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "(p*\<^sub>\<int>r +\<^sub>\<int> r*\<^sub>\<int>q) *\<^sub>\<int> r = r *\<^sub>\<int> r *\<^sub>\<int> (p +\<^sub>\<int> q)") *})

lemma rat_equiv_class_zero [rewrite]: "q >\<^sub>\<int> \<zero>\<^sub>\<int> \<Longrightarrow> Rat(\<langle>\<zero>\<^sub>\<int>,q\<rangle>) = \<zero>\<^sub>\<rat>" by auto2

lemma rat_has_add_inverse [forward]: "has_add_inverse(\<rat>)"
  by (tactic {* auto2s_tac @{context} (HAVE "\<forall>x\<in>.\<rat>. x +\<^sub>\<rat> rat_neg(x) = \<zero>\<^sub>\<rat>") *})

lemma rat_is_comm_ring [forward]: "is_comm_ring(\<rat>)" by auto2

section {* Inverse in rationals *}

definition rat_inverse_raw :: "i \<Rightarrow> i" where [rewrite]:
  "rat_inverse_raw(p) = (if fst(p) >\<^sub>\<int> \<zero>\<^sub>\<int> then \<langle>snd(p),fst(p)\<rangle> else \<langle>-\<^sub>\<int> snd(p), -\<^sub>\<int> fst(p)\<rangle>)"
setup {* register_wellform_data ("rat_inverse_raw(p)", ["p \<in>. \<R>"]) *}
  
lemma rat_inverse_raw_eval [rewrite]:
  "\<langle>a,b\<rangle> \<in>. \<R> \<Longrightarrow> a >\<^sub>\<int> \<zero>\<^sub>\<int> \<Longrightarrow> rat_inverse_raw(\<langle>a,b\<rangle>) = \<langle>b,a\<rangle>"
  "\<langle>a,b\<rangle> \<in>. \<R> \<Longrightarrow> a <\<^sub>\<int> \<zero>\<^sub>\<int> \<Longrightarrow> rat_inverse_raw(\<langle>a,b\<rangle>) = \<langle>-\<^sub>\<int> b, -\<^sub>\<int> a\<rangle>" by auto2+
setup {* del_prfstep_thm @{thm rat_inverse_raw_def} *}

lemma rat_inverse_raw_type [typing]:
  "\<langle>a,b\<rangle> \<in>. \<R> \<Longrightarrow> a \<noteq> \<zero>\<^sub>\<int> \<Longrightarrow> rat_inverse_raw(\<langle>a,b\<rangle>) \<in>. \<R>"
  by (tactic {* auto2s_tac @{context} (CASE "a >\<^sub>\<int> \<zero>\<^sub>\<int>") *})

definition rat_inverse :: "i \<Rightarrow> i" where [rewrite]:
  "rat_inverse(r) = Rat(rat_inverse_raw(rep(\<R>,r)))"

lemma rat_equiv_zero [rewrite]:
  "\<langle>a,b\<rangle> \<in>. \<R> \<Longrightarrow> Rat(\<langle>a,b\<rangle>) = \<zero>\<^sub>\<rat> \<longleftrightarrow> a = \<zero>\<^sub>\<int>" by auto2

lemma rat_inverse_typing [typing]:
  "x \<in>. \<rat> \<Longrightarrow> x \<noteq> \<zero>\<^sub>\<rat> \<Longrightarrow> rat_inverse(x) \<in>. \<rat>" by auto2

lemma rat_inverse_raw_mult_inv [rewrite]:
  "\<langle>p,q\<rangle> \<in>. \<R> \<Longrightarrow> p \<noteq> \<zero>\<^sub>\<int> \<Longrightarrow> Rat(rat_mult_raw(\<langle>p,q\<rangle>,rat_inverse_raw(\<langle>p,q\<rangle>))) = \<one>\<^sub>\<rat>"
  by (tactic {* auto2s_tac @{context} (CASE "p >\<^sub>\<int> \<zero>\<^sub>\<int>") *})

lemma rat_is_field [forward]: "is_field(\<rat>)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x\<in>.\<rat>. x \<noteq> \<zero>\<^sub>\<rat> \<longrightarrow> x *\<^sub>\<rat> rat_inverse(x) = \<one>\<^sub>\<rat>") *})

section {* Nonnegative rationals *}

lemma nonneg_rat_eval [rewrite]:
  "x \<in>. \<R> \<Longrightarrow> nonneg_rat(Rat(x)) \<longleftrightarrow> nonneg_rat_raw(x)" by auto2
setup {* del_prfstep_thm @{thm nonneg_rat_def} *}

lemma rat_neg_eval [rewrite]: "x \<in>. \<R> \<Longrightarrow> -\<^sub>\<rat> Rat(x) = Rat(rat_neg_raw(x))"
  by (tactic {* auto2s_tac @{context} (HAVE "Rat(x) +\<^sub>\<rat> Rat(rat_neg_raw(x)) = \<zero>\<^sub>\<rat>") *})

lemma rat_nonneg_compat [resolve]: "nonneg_compat(\<rat>, nonneg_rats)" by auto2
setup {* fold del_prfstep_thm [
  @{thm nonneg_rat_eval}, @{thm nonneg_rat_raw_def}, @{thm nonneg_rats_def}] *}

lemma rat_is_ord_field [forward]: "is_ord_field(\<rat>)"
  by (tactic {* auto2s_tac @{context} (HAVE "nonneg_compat(\<rat>, nonneg_rats)") *})
setup {* del_prfstep_thm @{thm rat_is_ord_field_prep} *}

section {* Rational as a quotient of two integers *}
          
lemma rat_of_nat [rewrite]:
  "n \<in> nat \<Longrightarrow> of_nat(\<rat>,n) = Rat(\<langle>of_nat(\<int>,n),1\<^sub>\<int>\<rangle>)"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "n \<in> nat" "of_nat(\<rat>,n) = Rat(\<langle>of_nat(\<int>,n),1\<^sub>\<int>\<rangle>)") *})

lemma rat_diff_raw_eval [rewrite]:
  "\<langle>p,r\<rangle> \<in>. \<R> \<Longrightarrow> \<langle>q,r\<rangle> \<in>. \<R> \<Longrightarrow> Rat(\<langle>p,r\<rangle>) -\<^sub>\<rat> Rat(\<langle>q,r\<rangle>) = Rat(\<langle>p-\<^sub>\<int>q, r\<rangle>)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "Rat(\<langle>p,r\<rangle>) -\<^sub>\<rat> Rat(\<langle>q,r\<rangle>) = Rat(\<langle>p,r\<rangle>) +\<^sub>\<rat> (-\<^sub>\<rat> Rat(\<langle>q,r\<rangle>))" THEN
    HAVE "p -\<^sub>\<int> q = p +\<^sub>\<int> (-\<^sub>\<int> q)") *})

lemma rat_of_int [rewrite]: "z \<in> int \<Longrightarrow> of_int(\<rat>,z) = Rat(\<langle>z,1\<^sub>\<int>\<rangle>)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "a\<in>.\<nat>, b\<in>.\<nat>, z = of_nat(\<int>,a) -\<^sub>\<int> of_nat(\<int>,b)") *})

lemma rat_inverse_eval [rewrite]:
  "\<langle>a,b\<rangle> \<in>. \<R> \<Longrightarrow> a >\<^sub>\<int> \<zero>\<^sub>\<int> \<Longrightarrow> inv(\<rat>,Rat(\<langle>a,b\<rangle>)) = Rat(\<langle>b,a\<rangle>)"
  by (tactic {* auto2s_tac @{context} (HAVE "Rat(\<langle>a,b\<rangle>) *\<^sub>\<rat> Rat(\<langle>b,a\<rangle>) = \<one>\<^sub>\<rat>") *})

lemma rat_div_eval [rewrite]:
  "\<langle>a,b\<rangle> \<in>. \<R> \<Longrightarrow> \<langle>c,d\<rangle> \<in>. \<R> \<Longrightarrow> c >\<^sub>\<int> \<zero>\<^sub>\<int> \<Longrightarrow> Rat(\<langle>a,b\<rangle>) /\<^sub>\<rat> Rat(\<langle>c,d\<rangle>) = Rat(\<langle>a*\<^sub>\<int>d,b*\<^sub>\<int>c\<rangle>)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "Rat(\<langle>a,b\<rangle>) /\<^sub>\<rat> Rat(\<langle>c,d\<rangle>) = Rat(\<langle>a,b\<rangle>) *\<^sub>\<rat> inv(\<rat>,Rat(\<langle>c,d\<rangle>))") *})

lemma rat_is_quotient [backward]:
  "r \<in>. \<rat> \<Longrightarrow> \<exists>a\<in>.\<int>. \<exists>b>\<^sub>\<int>0\<^sub>\<int>. r = of_int(\<rat>,a) /\<^sub>\<rat> of_int(\<rat>,b)"
  by (tactic {* auto2s_tac @{context} (
    LET "p = rep(\<R>,r)" THEN
    HAVE "r = of_int(\<rat>,fst(p)) /\<^sub>\<rat> of_int(\<rat>,snd(p))") *})

section {* Definition of of_rat *}
  
definition of_rat_raw :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "of_rat_raw(R,p) = of_int(R,fst(p)) /\<^sub>R of_int(R,snd(p))"

lemma of_rat_raw_eval [rewrite]: "of_rat_raw(R,\<langle>a,b\<rangle>) = of_int(R,a) /\<^sub>R of_int(R,b)" by auto2
setup {* del_prfstep_thm @{thm of_rat_raw_def} *}

lemma field_switch_sides4 [resolve]:
  "is_field(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in> units(R) \<Longrightarrow> c \<in>. R \<Longrightarrow> d \<in> units(R) \<Longrightarrow>
   a *\<^sub>R d = b *\<^sub>R c \<Longrightarrow> a /\<^sub>R b = c /\<^sub>R d"
  by (tactic {* auto2s_tac @{context} (
    HAVE "(a /\<^sub>R b) *\<^sub>R (b *\<^sub>R d) = (c /\<^sub>R d) *\<^sub>R (b *\<^sub>R d)" THEN HAVE "b *\<^sub>R d \<in> units(R)") *})

lemma of_rat_raw_compat [rewrite]:
  "is_ord_field(R) \<Longrightarrow> \<langle>a,b\<rangle> \<sim>\<^sub>\<R> \<langle>c,d\<rangle> \<Longrightarrow> of_rat_raw(R,\<langle>a,b\<rangle>) = of_rat_raw(R,\<langle>c,d\<rangle>)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "of_int(R,d) \<noteq> of_int(R,0\<^sub>\<int>)" THEN
    HAVE "of_int(R,a) *\<^sub>R of_int(R,d) = of_int(R,b) *\<^sub>R of_int(R,c)") *})

definition of_rat :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "of_rat(R,r) = of_rat_raw(R,rep(\<R>,r))"
setup {* register_wellform_data ("of_rat(R,r)", ["r \<in>. \<rat>"]) *}

lemma of_rat_eval [rewrite]:
  "is_ord_field(R) \<Longrightarrow> x \<in>. \<R> \<Longrightarrow> of_rat(R,Rat(x)) = of_rat_raw(R,x)" by auto2
setup {* del_prfstep_thm @{thm of_rat_def} *}

lemma of_int_is_unit [typing]:
  "is_ord_field(R) \<Longrightarrow> x >\<^sub>\<int> \<zero>\<^sub>\<int> \<Longrightarrow> of_int(R,x) \<in> units(R)"
  by (tactic {* auto2s_tac @{context} (HAVE "of_int(R,x) >\<^sub>R of_int(R,0\<^sub>\<int>)") *})

lemma of_rat_type [typing]:
  "is_ord_field(R) \<Longrightarrow> r \<in>. \<rat> \<Longrightarrow> of_rat(R,r) \<in>. R" by auto2

lemma of_rat_eval_quotient [rewrite]:
  "is_ord_field(R) \<Longrightarrow> x \<in>. \<int> \<Longrightarrow> y >\<^sub>\<int> 0\<^sub>\<int> \<Longrightarrow>
   of_rat(R,of_int(\<rat>,x) /\<^sub>\<rat> of_int(\<rat>,y)) = of_int(R,x) /\<^sub>R of_int(R,y)"
  by (tactic {* auto2s_tac @{context} (
    LET "r = of_int(\<rat>,x) /\<^sub>\<rat> of_int(\<rat>,y)" THEN
    LET "p = rep(\<R>,r)" THEN HAVE "p \<sim>\<^sub>\<R> \<langle>x,y\<rangle>") *})

lemma of_rat_is_zero [forward]:
  "is_ord_field(R) \<Longrightarrow> x \<in>. \<rat> \<Longrightarrow> of_rat(R,x) = 0\<^sub>R \<Longrightarrow> x = 0\<^sub>\<rat>"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "a\<in>.\<int>, b>\<^sub>\<int>0\<^sub>\<int>, x = of_int(\<rat>,a) /\<^sub>\<rat> of_int(\<rat>,b)" THEN
    HAVE "of_int(R,a) = of_int(R,0\<^sub>\<int>)") *})
  
lemma of_rat_of_int [rewrite]:
  "is_ord_field(R) \<Longrightarrow> x \<in>. \<int> \<Longrightarrow> of_rat(R,of_int(\<rat>,x)) = of_int(R,x)" by auto2

lemma of_rat_of_nat [rewrite]:
  "is_ord_field(R) \<Longrightarrow> n \<in> nat \<Longrightarrow> of_rat(R,of_nat(\<rat>,n)) = of_nat(R,n)" by auto2

setup {* fold del_prfstep_thm [@{thm of_rat_eval}, @{thm rat_of_nat}, @{thm rat_of_int}] *}
setup {* fold del_prfstep_thm [@{thm rat_def}, @{thm rat_rel_spaceI}, @{thm rat_rel_spaceD}] *}
setup {* fold del_prfstep_thm @{thms rat_evals(1-2)} *}
setup {* fold del_prfstep_thm [@{thm rat_choose_rep}, @{thm rat_neg_eval}, @{thm rat_inverse_eval},
  @{thm rat_div_eval}, @{thm rat_mult_eval}, @{thm rat_add_eval}] *}
no_notation rat_rel ("\<R>")
hide_const Rat

section {* Further properties *}
  
lemma of_rat_mult [rewrite_bidir]:
  "is_ord_field(R) \<Longrightarrow> x \<in>. \<rat> \<Longrightarrow> y \<in>. \<rat> \<Longrightarrow> of_rat(R,x) *\<^sub>R of_rat(R,y) = of_rat(R,x *\<^sub>\<rat> y)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "a\<in>.\<int>, b>\<^sub>\<int>0\<^sub>\<int>, x = of_int(\<rat>,a) /\<^sub>\<rat> of_int(\<rat>,b)" THEN
    CHOOSE "c\<in>.\<int>, d>\<^sub>\<int>0\<^sub>\<int>, y = of_int(\<rat>,c) /\<^sub>\<rat> of_int(\<rat>,d)" THEN
    LET "qa = of_int(\<rat>,a), qb = of_int(\<rat>,b), qc = of_int(\<rat>,c), qd = of_int(\<rat>,d)" THEN
    LET "ra = of_int(R,a), rb = of_int(R,b), rc = of_int(R,c), rd = of_int(R,d)" THEN
    HAVE "(qa /\<^sub>\<rat> qb) *\<^sub>\<rat> (qc /\<^sub>\<rat> qd) = (qa *\<^sub>\<rat> qc) /\<^sub>\<rat> (qb *\<^sub>\<rat> qd)" THEN
    HAVE "(ra /\<^sub>R rb) *\<^sub>R (rc /\<^sub>R rd) = (ra *\<^sub>R rc) /\<^sub>R (rb *\<^sub>R rd)") *})

lemma of_rat_inverse [rewrite_bidir]:
  "is_ord_field(R) \<Longrightarrow> x \<in> units(\<rat>) \<Longrightarrow> inv(R,of_rat(R,x)) = of_rat(R,inv(\<rat>,x))"
  by (tactic {* auto2s_tac @{context} (
    HAVE "of_rat(R,inv(\<rat>,x)) *\<^sub>R of_rat(R,x) = \<one>\<^sub>R") *})

lemma of_rat_add [rewrite_bidir]:
  "is_ord_field(R) \<Longrightarrow> x \<in>. \<rat> \<Longrightarrow> y \<in>. \<rat> \<Longrightarrow> of_rat(R,x) +\<^sub>R of_rat(R,y) = of_rat(R,x +\<^sub>\<rat> y)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "a\<in>.\<int>, b>\<^sub>\<int>0\<^sub>\<int>, x = of_int(\<rat>,a) /\<^sub>\<rat> of_int(\<rat>,b)" THEN
    CHOOSE "c\<in>.\<int>, d>\<^sub>\<int>0\<^sub>\<int>, y = of_int(\<rat>,c) /\<^sub>\<rat> of_int(\<rat>,d)" THEN
    LET "qa = of_int(\<rat>,a), qb = of_int(\<rat>,b), qc = of_int(\<rat>,c), qd = of_int(\<rat>,d)" THEN
    LET "ra = of_int(R,a), rb = of_int(R,b), rc = of_int(R,c), rd = of_int(R,d)" THEN
    HAVE "(qa /\<^sub>\<rat> qb) +\<^sub>\<rat> (qc /\<^sub>\<rat> qd) = (qa *\<^sub>\<rat> qd +\<^sub>\<rat> qb *\<^sub>\<rat> qc) /\<^sub>\<rat> (qb *\<^sub>\<rat> qd)" THEN
    HAVE "(ra /\<^sub>R rb) +\<^sub>R (rc /\<^sub>R rd) = (ra *\<^sub>R rd +\<^sub>R rb *\<^sub>R rc) /\<^sub>R (rb *\<^sub>R rd)") *})
      
lemma ord_field_le_divide_switch [backward1]:
  "is_ord_field(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> c \<in>. R \<Longrightarrow> b >\<^sub>R 0\<^sub>R \<Longrightarrow> d >\<^sub>R 0\<^sub>R \<Longrightarrow>
   a /\<^sub>R b \<le>\<^sub>R c /\<^sub>R d \<Longrightarrow> a *\<^sub>R d \<le>\<^sub>R b *\<^sub>R c"
  by (tactic {* auto2s_tac @{context} (
    HAVE "a /\<^sub>R b *\<^sub>R (b *\<^sub>R d) \<le>\<^sub>R c /\<^sub>R d *\<^sub>R (b *\<^sub>R d)" THEN HAVE "b *\<^sub>R d >\<^sub>R 0\<^sub>R") *})

lemma ord_field_le_divide_switch2 [backward1]:
  "is_ord_field(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> c \<in>. R \<Longrightarrow> b >\<^sub>R 0\<^sub>R \<Longrightarrow> d >\<^sub>R 0\<^sub>R \<Longrightarrow>
   a *\<^sub>R d \<le>\<^sub>R b *\<^sub>R c \<Longrightarrow> a /\<^sub>R b \<le>\<^sub>R c /\<^sub>R d"
  by (tactic {* auto2s_tac @{context} (
    HAVE "a *\<^sub>R d /\<^sub>R (b *\<^sub>R d) \<le>\<^sub>R b *\<^sub>R c /\<^sub>R (b *\<^sub>R d)" THEN HAVE "b *\<^sub>R d >\<^sub>R 0\<^sub>R") *})
      
lemma ord_field_le_divide_switch3 [backward1]:
  "is_ord_field(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> c \<in>. R \<Longrightarrow> b >\<^sub>R 0\<^sub>R \<Longrightarrow> d >\<^sub>R 0\<^sub>R \<Longrightarrow>
   a /\<^sub>R b <\<^sub>R c /\<^sub>R d \<Longrightarrow> a *\<^sub>R d <\<^sub>R b *\<^sub>R c"
  by (tactic {* auto2s_tac @{context} (
    HAVE "a /\<^sub>R b *\<^sub>R (b *\<^sub>R d) <\<^sub>R c /\<^sub>R d *\<^sub>R (b *\<^sub>R d)" THEN HAVE "b *\<^sub>R d >\<^sub>R 0\<^sub>R") *})

lemma ord_field_le_divide_switch4 [backward1]:
  "is_ord_field(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> c \<in>. R \<Longrightarrow> b >\<^sub>R 0\<^sub>R \<Longrightarrow> d >\<^sub>R 0\<^sub>R \<Longrightarrow>
   a *\<^sub>R d <\<^sub>R b *\<^sub>R c \<Longrightarrow> a /\<^sub>R b <\<^sub>R c /\<^sub>R d"
  by (tactic {* auto2s_tac @{context} (
    HAVE "a *\<^sub>R d /\<^sub>R (b *\<^sub>R d) <\<^sub>R b *\<^sub>R c /\<^sub>R (b *\<^sub>R d)" THEN HAVE "b *\<^sub>R d >\<^sub>R 0\<^sub>R") *})

lemma ord_field_of_rat_le [backward]:
  "is_ord_field(R) \<Longrightarrow> r \<le>\<^sub>\<rat> s \<Longrightarrow> of_rat(R,r) \<le>\<^sub>R of_rat(R,s)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "a\<in>.\<int>, b>\<^sub>\<int>0\<^sub>\<int>, r = of_int(\<rat>,a) /\<^sub>\<rat> of_int(\<rat>,b)" THEN
    CHOOSE "c\<in>.\<int>, d>\<^sub>\<int>0\<^sub>\<int>, s = of_int(\<rat>,c) /\<^sub>\<rat> of_int(\<rat>,d)" THEN
    HAVE "of_int(\<rat>,a) *\<^sub>\<rat> of_int(\<rat>,d) \<le>\<^sub>\<rat> of_int(\<rat>,b) *\<^sub>\<rat> of_int(\<rat>,c)" THEN
    HAVE "of_int(R,a) *\<^sub>R of_int(R,d) \<le>\<^sub>R of_int(R,b) *\<^sub>R of_int(R,c)") *})

lemma ord_field_of_rat_less [backward]:
  "is_ord_field(R) \<Longrightarrow> r <\<^sub>\<rat> s \<Longrightarrow> of_rat(R,r) <\<^sub>R of_rat(R,s)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "a\<in>.\<int>, b>\<^sub>\<int>0\<^sub>\<int>, r = of_int(\<rat>,a) /\<^sub>\<rat> of_int(\<rat>,b)" THEN
    CHOOSE "c\<in>.\<int>, d>\<^sub>\<int>0\<^sub>\<int>, s = of_int(\<rat>,c) /\<^sub>\<rat> of_int(\<rat>,d)" THEN
    HAVE "of_int(\<rat>,a) *\<^sub>\<rat> of_int(\<rat>,d) <\<^sub>\<rat> of_int(\<rat>,b) *\<^sub>\<rat> of_int(\<rat>,c)" THEN
    HAVE "of_int(R,a) *\<^sub>R of_int(R,d) <\<^sub>R of_int(R,b) *\<^sub>R of_int(R,c)") *})

lemma ord_field_of_rat_positive:
  "is_ord_field(R) \<Longrightarrow> r >\<^sub>\<rat> \<zero>\<^sub>\<rat> \<Longrightarrow> of_rat(R,r) >\<^sub>R \<zero>\<^sub>R"
  by (tactic {* auto2s_tac @{context} (HAVE "of_rat(R,r) >\<^sub>R of_rat(R,0\<^sub>\<rat>)") *})
setup {* add_forward_prfstep_cond @{thm ord_field_of_rat_positive} [with_term "of_rat(?R,?r)"] *}

section {* Rationals is an archimedean field *}

lemma int_has_of_nat_ge [forward]: "is_archimedean(\<int>)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>z\<in>.\<int>. \<exists>n\<in>nat. of_nat(\<int>,n) \<ge>\<^sub>\<int> z" WITH (
      CHOOSE "a\<in>.\<nat>, b\<in>.\<nat>, z = of_nat(\<int>,a) -\<^sub>\<int> of_nat(\<int>,b)" THEN
      HAVE "of_nat(\<int>,a) \<ge>\<^sub>\<int> z")) *})

lemma is_archimedeanI_pos_of_int [forward]:
  "is_ord_ring(R) \<Longrightarrow> \<forall>x >\<^sub>R 0\<^sub>R. \<exists>z\<in>.\<int>. of_int(R,z) \<ge>\<^sub>R x \<Longrightarrow> is_archimedean(R)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x >\<^sub>R 0\<^sub>R. \<exists>n\<in>nat. of_nat(R,n) \<ge>\<^sub>R x" WITH (
      CHOOSE "z\<in>.\<int>, of_int(R,z) \<ge>\<^sub>R x" THEN
      CHOOSE "n\<in>nat, of_nat(\<int>,n) \<ge>\<^sub>\<int> z" THEN
      HAVE "of_nat(R,n) = of_int(R,of_nat(\<int>,n))")) *})

lemma rat_is_archimedean [forward]: "is_archimedean(\<rat>)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>r >\<^sub>\<rat> 0\<^sub>\<rat>. \<exists>z\<in>int. of_int(\<rat>,z) \<ge>\<^sub>\<rat> r" WITH (
      CHOOSE "a\<in>.\<int>, b>\<^sub>\<int>0\<^sub>\<int>, r = of_int(\<rat>,a) /\<^sub>\<rat> of_int(\<rat>,b)" THEN
      HAVE "of_int(\<rat>,b) \<ge>\<^sub>\<rat> of_int(\<rat>,1\<^sub>\<int>)")) *})

lemma is_archimedeanI_pos_of_rat [forward]:
  "is_ord_field(R) \<Longrightarrow> \<forall>x >\<^sub>R 0\<^sub>R. \<exists>z\<in>.\<rat>. of_rat(R,z) \<ge>\<^sub>R x \<Longrightarrow> is_archimedean(R)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x >\<^sub>R 0\<^sub>R. \<exists>n\<in>nat. of_nat(R,n) \<ge>\<^sub>R x" WITH (
      CHOOSE "r\<in>.\<rat>, of_rat(R,r) \<ge>\<^sub>R x" THEN
      CHOOSE "n\<in>nat, of_nat(\<rat>,n) \<ge>\<^sub>\<rat> r" THEN
      HAVE "of_nat(R,n) = of_rat(R,of_nat(\<rat>,n))" THEN
      HAVE "of_rat(R,of_nat(\<rat>,n)) \<ge>\<^sub>R of_rat(R,r)")) *})

section {* More properties of archimedean fields *}
  
lemma is_archimedeanD_rat [backward]:
  "is_archimedean(R) \<Longrightarrow> is_field(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<exists>r\<in>.\<rat>. of_rat(R,r) >\<^sub>R x"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "n\<in>nat, of_nat(R,n) >\<^sub>R x" THEN
    HAVE "of_rat(R,of_nat(\<rat>,n)) = of_nat(R,n)") *})

lemma is_archimedeanD_rat_pos [backward]:
  "is_archimedean(R) \<Longrightarrow> is_field(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> \<exists>r>\<^sub>\<rat>\<zero>\<^sub>\<rat>. of_rat(R,r) >\<^sub>R x"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r\<in>.\<rat>, of_rat(R,r) >\<^sub>R x" THEN
    CHOOSE "r'\<in>.\<rat>, r' >\<^sub>\<rat> \<zero>\<^sub>\<rat> \<and> r' \<ge>\<^sub>\<rat> r") *})

lemma is_archimedeanD_rat_less [backward]:
  "is_archimedean(R) \<Longrightarrow> is_field(R) \<Longrightarrow> x >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> \<exists>r>\<^sub>\<rat>\<zero>\<^sub>\<rat>. of_rat(R,r) <\<^sub>R x"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r>\<^sub>\<rat>\<zero>\<^sub>\<rat>, of_rat(R,r) >\<^sub>R inv(R,x)" THEN
    HAVE "of_rat(R,inv(\<rat>,r)) <\<^sub>R x") *})

end
