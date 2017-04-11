(* Construction of real numbers, following HOL/Real. *)

theory Real_Auto2
imports Seq_Thms Conditionally_Complete_Lattices
begin

subsection {* Preliminaries *}

setup {* add_gen_prfstep ("shadow_abs_upper_triv",
  [WithFact @{term_pat "\<bar>?x - ?x\<bar> < (?r::?'a::linordered_idom)"},
   WithFact @{term_pat "(?r::?'a::linordered_idom) > 0"}, ShadowFirst]) *}
setup {* add_gen_prfstep ("shadow_abs_upper_sym",
  [WithFact @{term_pat "\<bar>?x - ?y\<bar> < (?r::?'a::linordered_idom)"},
   WithFact @{term_pat "\<bar>?y - ?x\<bar> < (?r::?'a::linordered_idom)"}, ShadowSecond]) *}

lemma abs_sum_upper_bound [backward1]:
  "\<bar>(x::('a::linordered_idom))\<bar> < s \<Longrightarrow> \<bar>y\<bar> < t \<Longrightarrow> \<bar>x + y\<bar> < s + t" by arith

lemma abs_sum_upper_bound' [backward1]:
  "\<bar>(x::('a::linordered_field))\<bar> < r/2 \<Longrightarrow> \<bar>y\<bar> < r/2 \<Longrightarrow> \<bar>x + y\<bar> < r" by arith

theorem abs_cancel_diff1 [backward1]:
  "\<bar>(x::('a::linordered_idom)) - y\<bar> < s \<Longrightarrow> \<bar>y - z\<bar> \<le> t \<Longrightarrow> \<bar>x - z\<bar> < s + t" by simp
theorem abs_cancel_diff2 [backward1]:
  "\<bar>(x::('a::linordered_idom)) - y\<bar> < s \<Longrightarrow> \<bar>y - z\<bar> < t \<Longrightarrow> \<bar>x - z\<bar> < s + t" by simp

theorem abs_cancel_diff2' [backward1]:
  "\<bar>(x::('a::linordered_field)) - y\<bar> < r/2 \<Longrightarrow> \<bar>y - z\<bar> < r/2 \<Longrightarrow> \<bar>x - z\<bar> < r" by arith

lemma abs_prod_upper_bound [backward1]:
  "\<bar>(x::('a::linordered_idom))\<bar> < s \<Longrightarrow> \<bar>y\<bar> < t \<Longrightarrow> \<bar>x * y\<bar> < s * t" by (simp add: abs_mult abs_mult_less)

lemma abs_prod_upper_bound2 [backward2]:
  "\<bar>(x::('a::linordered_field))\<bar> < s / t \<Longrightarrow> \<bar>y\<bar> < t \<Longrightarrow> \<bar>x * y\<bar> < s"
  by (tactic {* auto2s_tac @{context} (HAVE "t > 0" THEN HAVE "s = s * t / t") *})

lemma abs_prod_upper_bound2' [backward2]:
  "\<bar>(x::('a::linordered_field))\<bar> < s / t \<Longrightarrow> \<bar>y\<bar> < t \<Longrightarrow> \<bar>y * x\<bar> < s"
  by (tactic {* auto2s_tac @{context} (HAVE "t > 0" THEN HAVE "s = s * t / t") *})

lemma abs_prod_lower_bound [backward1]:
  "s > 0 \<Longrightarrow> t > 0 \<Longrightarrow> \<bar>(x::('a::linordered_idom))\<bar> > s \<Longrightarrow> \<bar>y\<bar> > t \<Longrightarrow> \<bar>x * y\<bar> > s * t"
  by (smt abs_mult abs_of_pos abs_prod_upper_bound)

lemma abs_div_upper_bound [backward2]:
  "b > 0 \<Longrightarrow> \<bar>x::('a::linordered_field)\<bar> < a \<Longrightarrow> \<bar>y\<bar> > b \<Longrightarrow> \<bar>x\<bar> / \<bar>y\<bar> < a / b" by (simp add: frac_less)

lemma abs_div_upper_bound2 [backward2]:
  "t > 0 \<Longrightarrow> \<bar>(x::('a::linordered_field))\<bar> < s * t \<Longrightarrow> \<bar>y\<bar> > t \<Longrightarrow> \<bar>x\<bar> / \<bar>y\<bar> < s"
  using abs_div_upper_bound by fastforce

lemma bound_diff_concl [resolve]:
  "\<bar>(a::('a::linordered_field)) - b\<bar> < c \<Longrightarrow> \<bar>a\<bar> < \<bar>b\<bar> + c" by simp

subsection {* Boundedness on sequences *}

definition bounded :: "('a::linordered_idom) seq \<Rightarrow> bool" where
  "bounded X = (\<exists>r>0. \<forall>n. \<bar>X\<langle>n\<rangle>\<bar> \<le> r)"
setup {* add_property_const @{term "bounded"} *}

(* Basic introduction and elimination rules for bounded. *)
setup {* add_backward_prfstep (equiv_backward_th @{thm bounded_def}) *}
lemma bounded_intro [forward]: "\<forall>n. \<bar>X\<langle>n\<rangle>\<bar> \<le> r \<Longrightarrow> bounded X"
  by (tactic {* auto2s_tac @{context} (HAVE "\<forall>n. \<bar>X\<langle>n\<rangle>\<bar> \<le> max r 1") *})
setup {* del_prfstep_thm @{thm bounded_def} #> add_resolve_prfstep (equiv_forward_th @{thm bounded_def}) *}

(* Less than version of intro and elim rules. *)
lemma bounded_intro_less [forward]: "\<forall>n. \<bar>X\<langle>n\<rangle>\<bar> < r \<Longrightarrow> bounded X"
  by (tactic {* auto2s_tac @{context} (HAVE "\<forall>n. \<bar>X\<langle>n\<rangle>\<bar> \<le> r") *})

lemma bounded_elim_less [resolve]: "bounded X \<Longrightarrow> \<exists>r>0. \<forall>n. \<bar>X\<langle>n\<rangle>\<bar> < r"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "r > 0, \<forall>n. \<bar>X\<langle>n\<rangle>\<bar> \<le> r" THEN HAVE "\<forall>n. \<bar>X\<langle>n\<rangle>\<bar> < r + 1") *})

lemma bounded_on_tail [forward]: "\<forall>n\<ge>k. \<bar>X\<langle>n\<rangle>\<bar> \<le> r \<Longrightarrow> bounded X"
  by (tactic {* auto2s_tac @{context}
    (HAVE "\<forall>n. \<bar>X\<langle>n\<rangle>\<bar> \<le> max r (Max ((\<lambda>i. \<bar>X\<langle>i\<rangle>\<bar>) ` {..<k}))" WITH
      (CASE "n < k" WITH HAVE "\<bar>X\<langle>n\<rangle>\<bar> \<le> Max ((\<lambda>i. \<bar>X\<langle>i\<rangle>\<bar>) ` {..<k})")) *})

theorem bounded_def_less_on_tail [forward]: "\<forall>n\<ge>k. \<bar>X\<langle>n\<rangle>\<bar> < r \<Longrightarrow> bounded X"
  by (tactic {* auto2s_tac @{context} (HAVE "\<forall>n\<ge>k. \<bar>X\<langle>n\<rangle>\<bar> \<le> r") *})

subsection {* Vanishes condition on sequences *}

definition vanishes :: "('a::linordered_field) seq \<Rightarrow> bool" where
  "vanishes X = (\<forall>r>0. \<exists>k. \<forall>n\<ge>k. \<bar>X\<langle>n\<rangle>\<bar> < r)"
setup {* add_property_const @{term "vanishes"} *}
setup {* add_backward_prfstep (equiv_backward_th @{thm vanishes_def})*}

theorem vanishes_elim [resolve]:
  "vanishes X \<Longrightarrow> r > 0 \<Longrightarrow> \<exists>k. \<forall>n\<ge>k. \<bar>X\<langle>n\<rangle>\<bar> < r" by (simp add: vanishes_def)

lemma vanishes_const [rewrite]: "vanishes {c}\<^sub>S \<longleftrightarrow> c = 0"
  by (tactic {* auto2s_tac @{context}
    (CASE "vanishes {c}\<^sub>S" WITH (CHOOSE "k, \<forall>n\<ge>k. \<bar>{c}\<^sub>S\<langle>n\<rangle>\<bar> < \<bar>c\<bar>" THEN HAVE "\<bar>{c}\<^sub>S\<langle>k\<rangle>\<bar> < \<bar>c\<bar>") THEN
     CASE "c = 0" WITH (CHOOSE "r > 0, \<not>(\<exists>k. \<forall>n\<ge>k. \<bar>{c}\<^sub>S\<langle>n\<rangle>\<bar> < r)" THEN HAVE "\<forall>n\<ge>0. \<bar>{c}\<^sub>S\<langle>n\<rangle>\<bar> < r")) *})

lemma vanishes_minus [backward]: "vanishes X \<Longrightarrow> vanishes (-X)"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "r > 0, \<not>(\<exists>k. \<forall>n\<ge>k. \<bar>(-X)\<langle>n\<rangle>\<bar> < r)" THEN
     CHOOSE "k, \<forall>n\<ge>k. \<bar>X\<langle>n\<rangle>\<bar> < r" THEN HAVE "\<forall>n\<ge>k. \<bar>(-X)\<langle>n\<rangle>\<bar> < r") *})
setup {* add_resolve_prfstep_cond @{thm vanishes_minus} [with_term "?X"] *}

lemma vanishes_add: "vanishes X \<Longrightarrow> vanishes Y \<Longrightarrow> vanishes (X + Y)"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "r > 0, \<not>(\<exists>k. \<forall>n\<ge>k. \<bar>(X + Y)\<langle>n\<rangle>\<bar> < r)" THEN
     CHOOSE "k, (\<forall>n\<ge>k. \<bar>X\<langle>n\<rangle>\<bar> < r/2) \<and> (\<forall>n\<ge>k. \<bar>Y\<langle>n\<rangle>\<bar> < r/2)" THEN
     HAVE "\<forall>n\<ge>k. \<bar>(X + Y)\<langle>n\<rangle>\<bar> < r") *})
setup {* add_backward_prfstep_cond @{thm vanishes_add} [with_term "?X"] *}

lemma vanishes_diff: "vanishes X \<Longrightarrow> vanishes Y \<Longrightarrow> vanishes (X - Y)"
  by (tactic {* auto2s_tac @{context} (HAVE "X - Y = X + (-Y)") *}) 

lemma vanishes_diff': "vanishes (X - Y) \<Longrightarrow> vanishes X \<longleftrightarrow> vanishes Y"
  by (tactic {* auto2s_tac @{context}
    ((CASE "vanishes X" WITH HAVE "X - (X - Y) = Y") THEN
     (CASE "vanishes Y" WITH HAVE "Y + (X - Y) = X")) *})
setup {* add_forward_prfstep (equiv_forward_th @{thm vanishes_diff'}) #>
  add_forward_prfstep (equiv_backward_th @{thm vanishes_diff'}) *}

lemma vanishes_mult_bounded [backward]: "bounded X \<Longrightarrow> vanishes Y \<Longrightarrow> vanishes (X * Y)"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "a > 0, \<forall>n. \<bar>X\<langle>n\<rangle>\<bar> < a" THEN
     CHOOSE "r > 0, \<not>(\<exists>k. \<forall>n\<ge>k. \<bar>(X * Y)\<langle>n\<rangle>\<bar> < r)" THEN
     CHOOSE "k, \<forall>n\<ge>k. \<bar>Y\<langle>n\<rangle>\<bar> < r/a" THEN
     HAVE "\<forall>n\<ge>k. \<bar>(X * Y)\<langle>n\<rangle>\<bar> < r") *})

subsection {* Cauchy condition on sequences *}

definition cauchy :: "('a::linordered_field) seq \<Rightarrow> bool" where
  "cauchy X = (\<forall>r>0. \<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>X\<langle>m\<rangle> - X\<langle>n\<rangle>\<bar> < r)"
setup {* add_property_const @{term "cauchy"} *}
setup {* add_resolve_prfstep (equiv_backward_th @{thm cauchy_def}) *}

theorem cauchy_elim [resolve]:
  "cauchy X \<Longrightarrow> r > 0 \<Longrightarrow> \<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>X\<langle>m\<rangle> - X\<langle>n\<rangle>\<bar> < r" by (simp add: cauchy_def)

lemma cauchy_elim2 [resolve]:
  "cauchy X \<Longrightarrow> r > 0 \<Longrightarrow> \<exists>k. \<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - X\<langle>k\<rangle>\<bar> < r"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "k, \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>X\<langle>m\<rangle> - X\<langle>n\<rangle>\<bar> < r" THEN
     HAVE "\<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - X\<langle>k\<rangle>\<bar> < r") *})

lemma cauchy_intro2 [forward]:
  "\<forall>r>0. \<exists>k. \<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - X\<langle>k\<rangle>\<bar> < r \<Longrightarrow> cauchy X"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "r > 0, \<not>(\<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>X\<langle>m\<rangle> - X\<langle>n\<rangle>\<bar> < r)" THEN
     CHOOSE "k, \<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - X\<langle>k\<rangle>\<bar> < r/2" THEN
     HAVE "\<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>X\<langle>m\<rangle> - X\<langle>n\<rangle>\<bar> < r") *})

lemma cauchy_elim_le [resolve]:
  "cauchy X \<Longrightarrow> r > 0 \<Longrightarrow> \<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>X\<langle>m\<rangle> - X\<langle>n\<rangle>\<bar> \<le> r"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "k, \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>X\<langle>m\<rangle> - X\<langle>n\<rangle>\<bar> < r" THEN
     HAVE "\<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>X\<langle>m\<rangle> - X\<langle>n\<rangle>\<bar> \<le> r") *})

lemma cauchy_const: "cauchy {c}\<^sub>S"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "r > 0, \<not>(\<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>{c}\<^sub>S\<langle>m\<rangle> - {c}\<^sub>S\<langle>n\<rangle>\<bar> < r)" THEN
     HAVE "\<forall>m\<ge>0. \<forall>n\<ge>0. \<bar>{c}\<^sub>S\<langle>m\<rangle> - {c}\<^sub>S\<langle>n\<rangle>\<bar> < r") *})
setup {* add_forward_prfstep_cond @{thm cauchy_const} [with_term "{?c}\<^sub>S"] *}

lemma cauchy_vanishes [forward]: "vanishes X \<Longrightarrow> cauchy X"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "r > 0, \<not>(\<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>X\<langle>m\<rangle> - X\<langle>n\<rangle>\<bar> < r)" THEN
     CHOOSE "i, \<forall>n\<ge>i. \<bar>X\<langle>n\<rangle>\<bar> < r/2" THEN
     HAVE "\<forall>m\<ge>i. \<forall>n\<ge>i. \<bar>X\<langle>m\<rangle> - X\<langle>n\<rangle>\<bar> < r") *})

lemma cauchy_add [backward]: "cauchy X \<Longrightarrow> cauchy Y \<Longrightarrow> cauchy (X + Y)"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "r > 0, \<not>(\<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>(X + Y)\<langle>m\<rangle> - (X + Y)\<langle>n\<rangle>\<bar> < r)" THEN
     CHOOSE "k, (\<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>X\<langle>m\<rangle> - X\<langle>n\<rangle>\<bar> < r/2) \<and> (\<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>Y\<langle>m\<rangle> - Y\<langle>n\<rangle>\<bar> < r/2)" THEN
     HAVE "\<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>(X + Y)\<langle>m\<rangle> - (X + Y)\<langle>n\<rangle>\<bar> < r") *})
setup {* add_forward_prfstep_cond @{thm cauchy_add} [with_term "?X + ?Y"] *}

lemma cauchy_minus [backward]: "cauchy X \<Longrightarrow> cauchy (-X)"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "r > 0, \<not>(\<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>(-X)\<langle>m\<rangle> - (-X)\<langle>n\<rangle>\<bar> < r)" THEN
     CHOOSE "k, \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>X\<langle>m\<rangle> - X\<langle>n\<rangle>\<bar> < r" THEN
     HAVE "\<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>(-X)\<langle>m\<rangle> - (-X)\<langle>n\<rangle>\<bar> < r") *})

theorem cauchy_minus' [forward]: "cauchy (-X) \<Longrightarrow> cauchy X" using cauchy_minus by fastforce

lemma cauchy_diff [backward]: "cauchy X \<Longrightarrow> cauchy Y \<Longrightarrow> cauchy (X - Y)"
  by (tactic {* auto2s_tac @{context} (HAVE "X - Y = X + (-Y)") *})

lemma cauchy_imp_bounded [forward]: "cauchy X \<Longrightarrow> bounded X"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "k, \<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - X\<langle>k\<rangle>\<bar> < 1" THEN HAVE "\<forall>n\<ge>k. \<bar>X\<langle>n\<rangle>\<bar> < \<bar>X\<langle>k\<rangle>\<bar> + 1") *})

lemma cauchy_mult [backward]: "cauchy X \<Longrightarrow> cauchy Y \<Longrightarrow> cauchy (X * Y)"
  by (tactic {* auto2s_tac @{context}
    (CHOOSES ["r > 0, \<not>(\<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>(X * Y)\<langle>m\<rangle> - (X * Y)\<langle>n\<rangle>\<bar> < r)",
              "a > 0, (\<forall>n. \<bar>X\<langle>n\<rangle>\<bar> < a)",
              "b > 0, (\<forall>n. \<bar>Y\<langle>n\<rangle>\<bar> < b)",
              "k, (\<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>X\<langle>m\<rangle> - X\<langle>n\<rangle>\<bar> < r/2/b) \<and> (\<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>Y\<langle>m\<rangle> - Y\<langle>n\<rangle>\<bar> < r/2/a)"] THEN
     HAVE "\<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>(X * Y)\<langle>m\<rangle> - (X * Y)\<langle>n\<rangle>\<bar> < r" WITH
      (HAVE "(X * Y)\<langle>m\<rangle> - (X * Y)\<langle>n\<rangle> = X\<langle>m\<rangle> * (Y\<langle>m\<rangle> - Y\<langle>n\<rangle>) + (X\<langle>m\<rangle> - X\<langle>n\<rangle>) * Y\<langle>n\<rangle>" THEN
       HAVE "\<bar>X\<langle>m\<rangle> * (Y\<langle>m\<rangle> - Y\<langle>n\<rangle>)\<bar> < r/2")) *})
setup {* add_forward_prfstep_cond @{thm cauchy_mult} [with_term "?X * ?Y"] *}

lemma cauchy_not_vanishes_cases [backward]:
  "cauchy X \<Longrightarrow> \<not> vanishes X \<Longrightarrow> \<exists>b>0. \<exists>k. (\<forall>n\<ge>k. b < - X\<langle>n\<rangle>) \<or> (\<forall>n\<ge>k. b < X\<langle>n\<rangle>)"
  by (tactic {* auto2s_tac @{context}
    (CHOOSES ["r > 0, (\<forall>k. \<exists>n\<ge>k. r \<le> \<bar>X\<langle>n\<rangle>\<bar>)",
              "i, \<forall>m\<ge>i. \<forall>n\<ge>i. \<bar>X\<langle>m\<rangle> - X\<langle>n\<rangle>\<bar> < r/2",
              "k \<ge> i, r \<le> \<bar>X\<langle>k\<rangle>\<bar>"] THEN
     HAVE "\<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - X\<langle>k\<rangle>\<bar> < r/2" THEN
     CASE "X\<langle>k\<rangle> \<le> -r" WITH HAVE "\<forall>n\<ge>k. r/2 < -X\<langle>n\<rangle>" THEN
     CASE "X\<langle>k\<rangle> \<ge> r" WITH HAVE "\<forall>n\<ge>k. r/2 < X\<langle>n\<rangle>") *})

lemma cauchy_not_vanishes [backward]:
  "cauchy X \<Longrightarrow> \<not> vanishes X \<Longrightarrow> \<exists>b>0. \<exists>k. \<forall>n\<ge>k. b < \<bar>X\<langle>n\<rangle>\<bar>"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "b > 0, k, (\<forall>n\<ge>k. b < - X\<langle>n\<rangle>) \<or> (\<forall>n\<ge>k. b < X\<langle>n\<rangle>)" THEN HAVE "\<forall>n\<ge>k. b < \<bar>X\<langle>n\<rangle>\<bar>") *})

lemma cauchy_inverse: "cauchy X \<Longrightarrow> \<not> vanishes X \<Longrightarrow> cauchy (seq_inverse X)"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "r > 0, \<not>(\<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>(seq_inverse X) \<langle>m\<rangle> - (seq_inverse X) \<langle>n\<rangle>\<bar> < r)" THEN
     CHOOSE "b > 0, i, \<forall>n\<ge>i. b < \<bar>X\<langle>n\<rangle>\<bar>" THEN
     CHOOSE "j \<ge> i, \<forall>m\<ge>j. \<forall>n\<ge>j. \<bar>X\<langle>m\<rangle> - X\<langle>n\<rangle>\<bar> < r*(b*b)" THEN
     HAVE "\<forall>m\<ge>j. \<forall>n\<ge>j. \<bar>(seq_inverse X) \<langle>m\<rangle> - (seq_inverse X) \<langle>n\<rangle>\<bar> < r" WITH
      (HAVE "\<bar>1 / X\<langle>m\<rangle> - 1 / X\<langle>n\<rangle>\<bar> = \<bar>X\<langle>m\<rangle> - X\<langle>n\<rangle>\<bar> / \<bar>X\<langle>m\<rangle> * X\<langle>n\<rangle>\<bar>")) *})
setup {* add_forward_prfstep_cond @{thm cauchy_inverse} [with_term "seq_inverse ?X"] *}

lemma vanishes_diff_inverse [backward1]: "cauchy X \<Longrightarrow> cauchy Y \<Longrightarrow> \<not> vanishes X \<Longrightarrow> \<not> vanishes Y \<Longrightarrow>
  vanishes (X - Y) \<Longrightarrow> vanishes (seq_inverse X - seq_inverse Y)"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "r > 0, \<not>(\<exists>k. \<forall>n\<ge>k. \<bar>(seq_inverse X - seq_inverse Y) \<langle>n\<rangle>\<bar> < r)" THEN
     CHOOSE "a > 0, i, \<forall>n\<ge>i. a < \<bar>X\<langle>n\<rangle>\<bar>" THEN
     CHOOSE "b > 0, j, \<forall>n\<ge>j. b < \<bar>Y\<langle>n\<rangle>\<bar>" THEN
     CHOOSE "k \<ge> max i j, \<forall>n\<ge>k. \<bar>(X - Y)\<langle>n\<rangle>\<bar> < r*(a*b)" THEN
     HAVE "\<forall>n\<ge>k. \<bar>(seq_inverse X - seq_inverse Y) \<langle>n\<rangle>\<bar> < r" WITH
      (HAVE "\<bar>1 / X\<langle>n\<rangle> - 1 / Y\<langle>n\<rangle>\<bar> = \<bar>X\<langle>n\<rangle> - Y\<langle>n\<rangle>\<bar> / \<bar>X\<langle>n\<rangle> * Y\<langle>n\<rangle>\<bar>")) *})

lemma seq_inverse_is_inverse [backward]:
  "cauchy X \<Longrightarrow> \<not> vanishes X \<Longrightarrow> vanishes ((seq_inverse X) * X - 1)"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "r > 0, \<not>(\<exists>k. \<forall>n\<ge>k. \<bar>((seq_inverse X) * X - 1) \<langle>n\<rangle>\<bar> < r)" THEN
     CHOOSE "b > 0, k, \<forall>n\<ge>k. b < \<bar>X\<langle>n\<rangle>\<bar>" THEN
     HAVE "\<forall>n\<ge>k. \<bar>((seq_inverse X) * X - 1) \<langle>n\<rangle>\<bar> < r") *})

subsection {* Equivalence relation on Cauchy sequences *}

definition realrel :: "rat seq \<Rightarrow> rat seq \<Rightarrow> bool" where
  "realrel X Y \<longleftrightarrow> cauchy X \<and> cauchy Y \<and> vanishes (X - Y)"
setup {* add_rewrite_rule @{thm realrel_def} *}

lemma realrel_refl [rewrite_back]: "cauchy X \<longleftrightarrow> realrel X X" by auto2
setup {* del_prfstep_thm @{thm realrel_def} #> add_rewrite_rule_cond @{thm realrel_def} [with_cond "?X \<noteq> ?Y"] *}

lemma symp_realrel [resolve]: "symp realrel" by auto2

lemma transp_realrel: "transp realrel"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "X, Y, Z, realrel X Y \<and> realrel Y Z \<and> \<not> realrel X Z" THEN
    HAVE "(X - Y) + (Y - Z) = X - Z") *})

lemma part_equivp_realrel: "part_equivp realrel"
  by (meson cauchy_const part_equivpI realrel_refl symp_realrel transp_realrel)

subsection {* The field of real numbers *}

quotient_type real = "rat seq" / partial: realrel morphisms rep_real Real
  by (rule part_equivp_realrel)

theorem exists_lift_real [resolve]: "\<exists>S. cauchy S \<and> r = Real S"
  by (metis Quotient_alt_def2 Quotient_real cr_real_def realrel_def)

instantiation real :: field
begin

lift_definition zero_real :: "real" is "0" by auto2
lift_definition one_real :: "real" is "1" by auto2
lift_definition plus_real :: "real \<Rightarrow> real \<Rightarrow> real" is "\<lambda>X Y. X + Y" by auto2
lift_definition uminus_real :: "real \<Rightarrow> real" is "\<lambda>X. -X" by auto2

lift_definition times_real :: "real \<Rightarrow> real \<Rightarrow> real" is "\<lambda>X Y. X * Y"
proof -
  fix X1 Y1 X2 Y2
  show "realrel X1 Y1 \<Longrightarrow> realrel X2 Y2 \<Longrightarrow> realrel (X1 * X2) (Y1 * Y2)"
    by (tactic {* auto2s_tac @{context}
      (HAVE "(X1 * X2) - (Y1 * Y2) = X1 * (X2 - Y2) + Y2 * (X1 - Y1)" THEN
       HAVE "vanishes (X1 * (X2 - Y2))") *})
qed

lift_definition inverse_real :: "real \<Rightarrow> real" is
  "\<lambda>X. if vanishes X then {0}\<^sub>S else seq_inverse X" by auto2

definition "x - y = (x::real) + (-y)"
definition "x div y = (x::real) * inverse y"

lemma add_Real [rewrite_back]: "cauchy X \<Longrightarrow> cauchy Y \<Longrightarrow> Real X + Real Y = Real (X + Y)"
  by (simp add: realrel_refl plus_real.abs_eq)

lemma minus_Real [rewrite_back]: "cauchy X \<Longrightarrow> - Real X = Real (-X)"
  by (simp add: realrel_refl uminus_real.abs_eq)

lemma diff_Real [rewrite_back]: "cauchy X \<Longrightarrow> cauchy Y \<Longrightarrow> Real X - Real Y = Real (X - Y)"
  by (simp add: add_Real cauchy_minus minus_Real minus_real_def)

lemma mult_Real [rewrite_back]: "cauchy X \<Longrightarrow> cauchy Y \<Longrightarrow> Real X * Real Y = Real (X * Y)"
  by (simp add: realrel_refl times_real.abs_eq)

lemma inverse_Real [rewrite]:
  "cauchy X \<Longrightarrow> inverse (Real X) = (if vanishes X then Real {0}\<^sub>S else Real (seq_inverse X))"
  by (simp add: realrel_refl inverse_real.abs_eq zero_real.abs_eq)

instance proof
  fix a b c :: real
  show "a - b = a + (-b)" by (rule minus_real_def)
  show "a div b = a * inverse b" by (rule divide_real_def)
  show "a + b = b + a" by transfer auto2
  show "a * b = b * a" by transfer auto2
  show "0 + a = a" by transfer auto2
  show "1 * a = a" by transfer auto2
  show "a * b * c = a * (b * c)" by transfer auto2
  show "a + b + c = a + (b + c)" by transfer auto2
  show "-a + a = 0" by transfer auto2
  show "(0::real) \<noteq> 1" by transfer auto2
  show "inverse (0::real) = 0" by transfer auto2
  show "(a + b) * c = a * c + b * c" by transfer auto2
  show "a \<noteq> 0 \<Longrightarrow> inverse a * a = 1" by transfer auto2
qed

end

setup {* fold add_rewrite_rule_back [@{thm zero_real.abs_eq}, @{thm one_real.abs_eq}] *}

theorem inverse_Real1 [rewrite]: "vanishes X \<Longrightarrow> inverse (Real X) = 0" by auto2
theorem inverse_Real2 [rewrite_bidir]:
  "cauchy X \<Longrightarrow> \<not> vanishes X \<Longrightarrow> inverse (Real X) = Real (seq_inverse X)" by auto2
theorem inverse_Real_const [rewrite_bidir]:
  "b > 0 \<Longrightarrow> Real {inverse b}\<^sub>S = inverse (Real {b}\<^sub>S)" by auto2
setup {* del_prfstep_thm @{thm inverse_Real}*}

subsection {* Positive reals *}

definition positive_seq :: "('a::linordered_field) seq \<Rightarrow> bool" where
  "positive_seq X \<longleftrightarrow> (\<exists>r>0. \<exists>k. \<forall>n\<ge>k. r < X\<langle>n\<rangle>)"
setup {* add_rewrite_rule @{thm positive_seq_def} *}

theorem positive_seq_rel [backward1]: "realrel X Y \<Longrightarrow> positive_seq X \<Longrightarrow> positive_seq Y"
  by (tactic {* auto2s_tac @{context}
    (CHOOSES ["r > 0, i, \<forall>n\<ge>i. r < X\<langle>n\<rangle>",
              "j \<ge> i, \<forall>n\<ge>j. \<bar>(X - Y)\<langle>n\<rangle>\<bar> < r/2"] THEN
     HAVE "\<forall>n\<ge>j. r/2 < Y\<langle>n\<rangle>") *})

lift_definition positive :: "real \<Rightarrow> bool" is "\<lambda>X. positive_seq X" by auto2

lemma positive_Real [rewrite]: "cauchy X \<Longrightarrow> positive (Real X) \<longleftrightarrow> positive_seq X"
  by (simp add: positive.abs_eq realrel_refl)

lemma positive_zero [resolve]: "\<not> positive 0"
  by transfer (metis le_square less_imp_not_less seq_evals(1) positive_seq_def)

lemma positive_seq_add [backward2]: "positive_seq X \<Longrightarrow> positive_seq Y \<Longrightarrow> positive_seq (X + Y)"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "s > 0, i, \<forall>n\<ge>i. s < X\<langle>n\<rangle>" THEN
     CHOOSE "t > 0, j, \<forall>n\<ge>j. t < Y\<langle>n\<rangle>" THEN
     HAVE "\<forall>n\<ge>max i j. s + t < (X + Y)\<langle>n\<rangle>" THEN HAVE "s + t > 0") *})

lemma positive_add [backward2]:
  "positive x \<Longrightarrow> positive y \<Longrightarrow> positive (x + y)" by transfer auto2

lemma positive_seq_mult [backward2]: "positive_seq X \<Longrightarrow> positive_seq Y \<Longrightarrow> positive_seq (X * Y)"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "s > 0, i, \<forall>n\<ge>i. s < X\<langle>n\<rangle>" THEN
     CHOOSE "t > 0, j, \<forall>n\<ge>j. t < Y\<langle>n\<rangle>" THEN
     HAVE "\<forall>n\<ge>max i j. s * t < (X * Y)\<langle>n\<rangle>" THEN HAVE "s * t > 0") *})

lemma positive_mult [backward2]:
  "positive x \<Longrightarrow> positive y \<Longrightarrow> positive (x * y)" by transfer auto2

lemma positive_seq_minus: "cauchy X \<Longrightarrow> \<not> vanishes X \<Longrightarrow> positive_seq X \<or> positive_seq (-X)"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "b > 0, k, (\<forall>n\<ge>k. b < - X\<langle>n\<rangle>) \<or> (\<forall>n\<ge>k. b < X\<langle>n\<rangle>)" THEN
     HAVE "\<exists>n\<ge>k. X\<langle>n\<rangle> \<le> b" THEN HAVE "\<exists>n\<ge>k. (-X)\<langle>n\<rangle> \<le> b") *})

lemma positive_minus [backward2]: "\<not> positive x \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> positive (-x)"
  apply transfer using positive_seq_minus realrel_def zero_real.rsp by auto

lemma positive_minus' [resolve]: "positive (a - b) \<Longrightarrow> \<not>positive (b - a)"
  using Real_Auto2.positive_add Real_Auto2.positive_zero by fastforce

instantiation real :: linordered_field
(* This instantiation directly copies from HOL/Real.thy *)
begin

definition "x < y \<longleftrightarrow> positive (y - x)"
definition "x \<le> (y::real) \<longleftrightarrow> x < y \<or> x = y"
definition "abs (a::real) = (if a < 0 then - a else a)"
definition "sgn (a::real) = (if a = 0 then 0 else if 0 < a then 1 else - 1)"
local_setup {* fold (local_context_map o add_rewrite_rule_gnrc)
  [@{thm less_real_def}, @{thm less_eq_real_def}, @{thm abs_real_def}, @{thm sgn_real_def}] *}

instance proof
  fix a b c :: real
  show "\<bar>a\<bar> = (if a < 0 then - a else a)" by auto2
  show "a < b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a" by auto2
  show "a \<le> a" by auto2
  show "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c"
    by (tactic {* auto2s_tac @{context} (HAVE "c-a = (c-b) + (b-a)") *})
  show "a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b" by auto2
  show "a \<le> b \<Longrightarrow> c + a \<le> c + b"
    by (tactic {* auto2s_tac @{context} (HAVE "c+b-(c+a) = b-a") *})
  show "sgn a = (if a = 0 then 0 else if 0 < a then 1 else - 1)" by auto2
  show "a \<le> b \<or> b \<le> a"
    by (tactic {* auto2s_tac @{context} (HAVE "-(a-b) = b-a") *})
  show "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"
    by (tactic {* auto2s_tac @{context} (HAVE "c*b-c*a = c*(b-a)") *})
qed

end

instantiation real :: distrib_lattice
(* This instantiation directly copies from HOL/Real.thy *)
begin

definition "(inf :: real \<Rightarrow> real \<Rightarrow> real) = min"
definition "(sup :: real \<Rightarrow> real \<Rightarrow> real) = max"

instance proof
  qed (auto simp add: inf_real_def sup_real_def max_min_distrib2)

end

lemma of_nat_Real [rewrite_back]: "of_nat x = Real {rat_of_nat x}\<^sub>S"
  by (tactic {* auto2s_tac @{context} (CASE "x = 0") *})

lemma of_int_Real [rewrite_back]: "of_int x = Real {rat_of_int x}\<^sub>S"
  by (tactic {* auto2s_tac @{context} (CHOOSE "m, n, x = int m - int n") *})

lemma of_rat_Real [rewrite_back]: "of_rat x = Real {x}\<^sub>S"
  by (tactic {* auto2s_tac @{context} (CHOOSE "a, b > 0, x = Fract a b") *})

theorem le_real_def [rewrite]: "x \<le> y \<longleftrightarrow> \<not> positive (x - y)"
  using less_real_def not_le by blast

subsection {* Further properties on positivity and ordering *}

lemma not_positive_Real [rewrite]:
  "cauchy X \<Longrightarrow> \<not> positive (Real X) \<longleftrightarrow> (\<forall>r>0. \<exists>k. \<forall>n\<ge>k. X\<langle>n\<rangle> \<le> r)"
  by (tactic {* auto2s_tac @{context}
    (CASE "\<not>positive (Real X)" WITH (
       CHOOSE "r > 0, \<not>(\<exists>k. \<forall>n\<ge>k. X\<langle>n\<rangle> \<le> r)" THEN
       CHOOSE "i, \<forall>m\<ge>i. \<forall>n\<ge>i. \<bar>X\<langle>m\<rangle> - X\<langle>n\<rangle>\<bar> < r/2" THEN
       CHOOSE "k \<ge> i, r/2 \<ge> X\<langle>k\<rangle>" THEN
       HAVE "\<forall>n\<ge>k. X\<langle>n\<rangle> \<le> r") THEN
     CASE "positive (Real X)" WITH (
       CHOOSE "r > 0, k, \<forall>n\<ge>k. r < X\<langle>n\<rangle>" THEN
       CHOOSE "k' \<ge> k, \<forall>n\<ge>k'. X\<langle>n\<rangle> \<le> r" THEN
       HAVE "X\<langle>k'\<rangle> \<le> r")) *})

lemma le_Real [rewrite]:
  "cauchy X \<Longrightarrow> cauchy Y \<Longrightarrow> Real X \<le> Real Y \<longleftrightarrow> (\<forall>r>0. \<exists>k. \<forall>n\<ge>k. (X - Y)\<langle>n\<rangle> \<le> r)"
  by (tactic {* auto2s_tac @{context}
    (HAVE "Real (X - Y) = Real X - Real Y" THEN HAVE "cauchy (X - Y)") *})
setup {* del_prfstep_thm @{thm le_real_def} *}

lemma le_Real_all_n [backward]: "cauchy X \<Longrightarrow> cauchy Y \<Longrightarrow> \<forall>n. X\<langle>n\<rangle> \<le> Y\<langle>n\<rangle> \<Longrightarrow> Real X \<le> Real Y"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "r > 0, \<not>(\<exists>k. \<forall>n\<ge>k. (X - Y)\<langle>n\<rangle> \<le> r)" THEN
     HAVE "\<forall>n\<ge>0. (X - Y)\<langle>n\<rangle> \<le> r") *})

theorem archimedean_Real [resolve]: "cauchy X \<Longrightarrow> \<exists>z. Real X \<le> of_int z"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "b > 0, \<forall>n. \<bar>X\<langle>n\<rangle>\<bar> \<le> b" THEN
     HAVE "rat_of_int \<lceil>b\<rceil> \<ge> b" THEN
     HAVE "of_int \<lceil>b\<rceil> = Real {rat_of_int \<lceil>b\<rceil>}\<^sub>S" THEN
     HAVE "\<forall>n. X\<langle>n\<rangle> \<le> {rat_of_int \<lceil>b\<rceil>}\<^sub>S \<langle>n\<rangle>" WITH HAVE "\<bar>X\<langle>n\<rangle>\<bar> \<le> b" THEN
     HAVE "Real X \<le> Real {rat_of_int \<lceil>b\<rceil>}\<^sub>S") *})

instance real :: archimedean_field
proof
  fix x :: real show "\<exists>z. x \<le> of_int z"
    by (tactic {* auto2s_tac @{context} (CHOOSE "S, cauchy S \<and> x = Real S") *})
qed

instantiation real :: floor_ceiling
(* This instantiation directly copies from HOL/Real.thy *)
begin

definition [code del]:
  "floor (x::real) = (THE z. of_int z \<le> x \<and> x < of_int (z + 1))"

instance proof
  fix x :: real
  show "of_int (floor x) \<le> x \<and> x < of_int (floor x + 1)"
    unfolding floor_real_def using floor_exists1 by (rule theI')
qed

end

subsection {* Ordering on and distance between real numbers *}

(* Unusual order to check cauchy X. *)
theorem le_rat_Real [backward]:
  "r > 0 \<Longrightarrow> Real X \<le> of_rat c \<Longrightarrow> cauchy X \<Longrightarrow> \<exists>k. \<forall>n\<ge>k. X\<langle>n\<rangle> \<le> c + r"
  by (tactic {* auto2s_tac @{context}
    (HAVE "of_rat c = Real {c}\<^sub>S" THEN
     CHOOSE "k, \<forall>n\<ge>k. (X - {c}\<^sub>S) \<langle>n\<rangle> \<le> r" THEN
     HAVE "\<forall>n\<ge>k. X\<langle>n\<rangle> \<le> c + r") *})

theorem diff_le_rat_Real [backward]:
  "cauchy X \<Longrightarrow> cauchy Y \<Longrightarrow> r > 0 \<Longrightarrow> Real X - Real Y \<le> of_rat c \<Longrightarrow> \<exists>k. \<forall>n\<ge>k. (X - Y)\<langle>n\<rangle> \<le> c + r"
  by (tactic {* auto2s_tac @{context}
    (HAVE "Real (X - Y) = Real X - Real Y") *})

theorem diff_le_rat_Real2 [backward]:
  "cauchy X \<Longrightarrow> cauchy Y \<Longrightarrow> r > 0 \<Longrightarrow> Real X - Real Y \<le> of_rat c \<Longrightarrow> \<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. X\<langle>m\<rangle> - Y\<langle>n\<rangle> \<le> c + r"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "k, (\<forall>n\<ge>k. (X - Y)\<langle>n\<rangle> \<le> c + r/2) \<and> (\<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>X\<langle>m\<rangle> - X\<langle>n\<rangle>\<bar> < r/2)" THEN
     HAVE "\<forall>m\<ge>k. \<forall>n\<ge>k. X\<langle>m\<rangle> - Y\<langle>n\<rangle> \<le> c + r" WITH
      (HAVE "X\<langle>m\<rangle> - Y\<langle>n\<rangle> = (X\<langle>m\<rangle> - X\<langle>n\<rangle>) + (X\<langle>n\<rangle> - Y\<langle>n\<rangle>)")) *})

theorem abs_diff_le_rat_Real2D [backward]:
  "cauchy X \<Longrightarrow> cauchy Y \<Longrightarrow> r > 0 \<Longrightarrow> \<bar>Real X - Real Y\<bar> \<le> of_rat c \<Longrightarrow> \<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>X\<langle>m\<rangle> - Y\<langle>n\<rangle>\<bar> \<le> c + r"
  by (tactic {* auto2s_tac @{context}
    (HAVE "Real X - Real Y \<le> of_rat c" THEN HAVE "Real Y - Real X \<le> of_rat c" THEN
     CHOOSE "k, (\<forall>m\<ge>k. \<forall>n\<ge>k. X\<langle>m\<rangle> - Y\<langle>n\<rangle> \<le> c + r) \<and> (\<forall>m\<ge>k. \<forall>n\<ge>k. Y\<langle>m\<rangle> - X\<langle>n\<rangle> \<le> c + r)" THEN
     HAVE "\<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>X\<langle>m\<rangle> - Y\<langle>n\<rangle>\<bar> \<le> c + r") *})

theorem le_rat_RealI [backward]:
  "cauchy X \<Longrightarrow> \<forall>r>0. \<exists>k. \<forall>n\<ge>k. X\<langle>n\<rangle> \<le> c + r \<Longrightarrow> Real X \<le> of_rat c"
  by (tactic {* auto2s_tac @{context}
    (HAVE "of_rat c = Real {c}\<^sub>S" THEN
     HAVE "\<forall>r>0. \<exists>k. \<forall>n\<ge>k. (X - {c}\<^sub>S) \<langle>n\<rangle> \<le> r" WITH
      (CHOOSE "k, \<forall>n\<ge>k. X\<langle>n\<rangle> \<le> c + r" THEN
       HAVE "\<forall>n\<ge>k. (X - {c}\<^sub>S) \<langle>n\<rangle> \<le> r")) *})

theorem diff_le_rat_RealI [backward]:
  "cauchy X \<Longrightarrow> cauchy Y \<Longrightarrow> \<forall>r>0. \<exists>k. \<forall>n\<ge>k. (X - Y)\<langle>n\<rangle> \<le> c + r \<Longrightarrow> Real X - Real Y \<le> of_rat c"
  by (tactic {* auto2s_tac @{context}
    (HAVE "Real (X - Y) = Real X - Real Y" THEN HAVE "cauchy (X - Y)") *})

theorem abs_diff_le_rat_RealI [backward]:
  "cauchy X \<Longrightarrow> cauchy Y \<Longrightarrow> \<forall>r>0. \<exists>k. \<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - Y\<langle>n\<rangle>\<bar> \<le> c + r \<Longrightarrow> \<bar>Real X - Real Y\<bar> \<le> of_rat c"
  by (tactic {* auto2s_tac @{context}
    (HAVE "Real X - Real Y \<le> of_rat c" WITH
      (CHOOSE "r > 0, \<not>(\<exists>k. \<forall>n\<ge>k. (X - Y)\<langle>n\<rangle> \<le> c + r)" THEN
       CHOOSE "k, \<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - Y\<langle>n\<rangle>\<bar> \<le> c + r" THEN
       HAVE "\<forall>n\<ge>k. (X - Y)\<langle>n\<rangle> \<le> c + r") THEN
     HAVE "Real Y - Real X \<le> of_rat c" WITH
      (CHOOSE "r > 0, \<not>(\<exists>k. \<forall>n\<ge>k. (Y - X)\<langle>n\<rangle> \<le> c + r)" THEN
       CHOOSE "k, \<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - Y\<langle>n\<rangle>\<bar> \<le> c + r" THEN
       HAVE "\<forall>n\<ge>k. (Y - X)\<langle>n\<rangle> \<le> c + r")) *})

theorem abs_diff_le_rat_RealI' [backward]:
  "cauchy X \<Longrightarrow> cauchy Y \<Longrightarrow> \<exists>k. \<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - Y\<langle>n\<rangle>\<bar> < c \<Longrightarrow> \<bar>Real X - Real Y\<bar> \<le> of_rat c"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "r > 0, \<not>(\<exists>k. \<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - Y\<langle>n\<rangle>\<bar> \<le> c + r)" THEN
     CHOOSE "k, \<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - Y\<langle>n\<rangle>\<bar> < c" THEN
     HAVE "\<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - Y\<langle>n\<rangle>\<bar> \<le> c + r") *})

subsection {* Convergence of sequences, limits *}

definition converges_to :: "('a::linordered_field) seq \<Rightarrow> 'a \<Rightarrow> bool" where
  "converges_to X s = (\<forall>r>0. \<exists>k. \<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - s\<bar> < r)"
theorem converges_to_elim [backward]: "r > 0 \<Longrightarrow> converges_to X s \<Longrightarrow> \<exists>k. \<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - s\<bar> < r"
  by (simp add: converges_to_def)
setup {* add_backward_prfstep (equiv_backward_th @{thm converges_to_def}) *}

(* In archimedean fields, suffice to check for rational numbers. *)

theorem ex_inverse_of_rat [resolve]: "(c::('a::archimedean_field)) > 0 \<Longrightarrow> \<exists>r>0. of_rat r < c"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "n > 0, inverse (of_nat n) < c" THEN
     HAVE "of_rat (inverse (of_nat n)) < c") *})

theorem converges_to_in_rat [backward]:
  "\<forall>r>0. \<exists>k. \<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - s\<bar> \<le> of_rat r \<Longrightarrow> converges_to X (s::('a::archimedean_field))"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "r > 0, \<not>(\<exists>k. \<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - s\<bar> < r)" THEN
     CHOOSE "r' > 0, of_rat r' < r" THEN
     CHOOSE "k, \<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - s\<bar> \<le> of_rat r'" THEN
     HAVE "\<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - s\<bar> < r") *})

theorem lt_limit [backward2]: "converges_to X x \<Longrightarrow> y < x \<Longrightarrow> \<exists>n. y < X\<langle>n\<rangle>"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "k, \<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - x\<bar> < x - y" THEN  (* Can simplify one line *)
     HAVE "\<bar>X\<langle>k\<rangle> - x\<bar> < x - y") *})

theorem gt_limit [backward2]: "converges_to X x \<Longrightarrow> y > x \<Longrightarrow> \<exists>n. y > X\<langle>n\<rangle>"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "k, \<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - x\<bar> < y - x" THEN
     HAVE "\<bar>X\<langle>k\<rangle> - x\<bar> < y - x" THEN HAVE "x + (y-x) = y") *})

theorem limit_equal [forward]: "vanishes (X - Y) \<Longrightarrow> converges_to X x \<Longrightarrow> converges_to Y x"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "r > 0, \<not>(\<exists>k. \<forall>n\<ge>k. \<bar>Y\<langle>n\<rangle> - x\<bar> < r)" THEN
     CHOOSE "k, (\<forall>n\<ge>k. \<bar>(X - Y)\<langle>n\<rangle>\<bar> < r/2) \<and> (\<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - x\<bar> < r/2)" THEN
     HAVE "\<forall>n\<ge>k. \<bar>Y\<langle>n\<rangle> - x\<bar> < r") *})

theorem limit_unique [forward]: "converges_to X x \<Longrightarrow> converges_to X y \<Longrightarrow> x = y"
  by (tactic {* auto2s_tac @{context}
    (LET "r = \<bar>x - y\<bar>" THEN HAVE "r > 0" THEN
     CHOOSE "k, (\<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - x\<bar> < r/2) \<and> (\<forall>n\<ge>k. \<bar>X\<langle>n\<rangle> - y\<bar> < r/2)" THEN
     HAVE "\<bar>X\<langle>k\<rangle> - x\<bar> < r/2 \<and> \<bar>X\<langle>k\<rangle> - y\<bar> < r/2" THEN
     HAVE "\<bar>x - y\<bar> < r") *})

subsection {* Cauchy completeness *}

(* First step: define a positive rational sequence converging to zero. *)

definition err :: "nat \<Rightarrow> rat" where "err n = inverse (of_nat (n + 1))"
setup {* add_rewrite_rule @{thm err_def} *}

theorem err_gt_zero [forward]: "is_positive (err n)" by (simp add: err_def)

theorem err_less_than_r [resolve]:
  "r > 0 \<Longrightarrow> \<exists>n. err n < r" using reals_Archimedean err_def by simp

theorem err_decreasing [backward]: "m > n \<Longrightarrow> err m < err n"
  by (tactic {* auto2s_tac @{context} (HAVE "rat_of_nat (m + 1) > rat_of_nat (n + 1)") *})

theorem err_converge_to_zero [backward]: "r > 0 \<Longrightarrow> \<exists>k. \<forall>n\<ge>k. err n < r"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "k, err k < r" THEN HAVE "\<forall>n\<ge>k. err n < r" WITH HAVE "err n < err k") *})
setup {* del_prfstep_thm @{thm err_def} *}

(* Now the main proof. *)

theorem real_complete [resolve]: "cauchy (R::real seq) \<Longrightarrow> \<exists>x. converges_to R x"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "S, \<forall>n. cauchy (S\<langle>n\<rangle>) \<and> R\<langle>n\<rangle> = Real (S\<langle>n\<rangle>)" THEN
    HAVE "\<forall>n. \<exists>k. (\<forall>i\<ge>k. \<bar>S\<langle>n\<rangle>\<langle>i\<rangle> - S\<langle>n\<rangle>\<langle>k\<rangle>\<bar> < err n)" THEN
    CHOOSE "S', \<forall>n. \<exists>k. (\<forall>i\<ge>k. \<bar>S\<langle>n\<rangle>\<langle>i\<rangle> - S\<langle>n\<rangle>\<langle>k\<rangle>\<bar> < err n) \<and> S'\<langle>n\<rangle> = S\<langle>n\<rangle>\<langle>k\<rangle>" THEN
    HAVE "cauchy S'" WITH
      (CHOOSE "r > 0, \<not>(\<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. \<bar>S'\<langle>m\<rangle> - S'\<langle>n\<rangle>\<bar> < r)" THEN
       CHOOSE "r1 > 0, r2 > 0, r3 > 0, r = r1 + r1 + r2 + r3" WITH
         HAVE "r = r / 6 + r / 6 + r / 3 + r / 3" THEN
       CHOOSE "i, (\<forall>n\<ge>i. err n < r1) \<and> (\<forall>m\<ge>i. \<forall>n\<ge>i. \<bar>R\<langle>m\<rangle> - R\<langle>n\<rangle>\<bar> \<le> of_rat r2)" THEN
       HAVE "\<forall>m\<ge>i. \<forall>n\<ge>i. \<bar>S'\<langle>m\<rangle> - S'\<langle>n\<rangle>\<bar> < r" WITH
        (CHOOSE "k1, (\<forall>k'\<ge>k1. \<bar>S\<langle>m\<rangle>\<langle>k'\<rangle> - S\<langle>m\<rangle>\<langle>k1\<rangle>\<bar> < err m) \<and> S'\<langle>m\<rangle> = S\<langle>m\<rangle>\<langle>k1\<rangle>" THEN
         CHOOSE "k2, (\<forall>k'\<ge>k2. \<bar>S\<langle>n\<rangle>\<langle>k'\<rangle> - S\<langle>n\<rangle>\<langle>k2\<rangle>\<bar> < err n) \<and> S'\<langle>n\<rangle> = S\<langle>n\<rangle>\<langle>k2\<rangle>" THEN
         CHOOSE "k \<ge> max k1 k2, \<forall>k'\<ge>k. \<forall>k''\<ge>k. \<bar>S\<langle>m\<rangle>\<langle>k'\<rangle> - S\<langle>n\<rangle>\<langle>k''\<rangle>\<bar> \<le> r2 + r3" THEN
         HAVE "k \<ge> k1 \<and> k \<ge> k2 \<and> k \<ge> k" THEN HAVE "\<bar>S\<langle>n\<rangle>\<langle>k\<rangle> - S'\<langle>m\<rangle>\<bar> < err m + r2 + r3" THEN
         HAVE "\<bar>S'\<langle>m\<rangle> - S'\<langle>n\<rangle>\<bar> < err m + err n + r2 + r3")) THEN
    HAVE "converges_to R (Real S')" WITH
     (CHOOSE "r > 0, \<not>(\<exists>k. \<forall>n\<ge>k. \<bar>R\<langle>n\<rangle> - Real S'\<bar> \<le> of_rat r)" THEN
      CHOOSE "i, \<forall>n\<ge>i. err n < r/2" THEN
      CHOOSE "j, \<forall>m\<ge>j. \<forall>n\<ge>j. \<bar>S'\<langle>m\<rangle> - S'\<langle>n\<rangle>\<bar> < r/2" THEN
      HAVE "\<forall>n\<ge>max i j. \<bar>R\<langle>n\<rangle> - Real S'\<bar> \<le> of_rat r" WITH
       (CHOOSE "k1, (\<forall>k'\<ge>k1. \<bar>S\<langle>n\<rangle>\<langle>k'\<rangle> - S\<langle>n\<rangle>\<langle>k1\<rangle>\<bar> < err n) \<and> S'\<langle>n\<rangle> = S\<langle>n\<rangle>\<langle>k1\<rangle>" THEN
        HAVE "\<forall>p\<ge>max k1 j. \<bar>S\<langle>n\<rangle>\<langle>p\<rangle> - S'\<langle>p\<rangle>\<bar> < r"))) *})

subsection {* Monotone convergence theorem *}

lemma induct_diff [backward1]: "(a::('a::linordered_idom)) > 0 \<Longrightarrow> \<forall>k. \<exists>n\<ge>k. X\<langle>n\<rangle> - X\<langle>k\<rangle> \<ge> a \<Longrightarrow>
  \<exists>n\<ge>k. X\<langle>n\<rangle> - X\<langle>k\<rangle> \<ge> (of_nat N) * a"
  by (tactic {* auto2s_tac @{context}
    (CASE "N = 0" WITH CHOOSE "n \<ge> k, X\<langle>n\<rangle> - X\<langle>k\<rangle> \<ge> a" THEN
     INDUCT ("N", []) THEN
     CHOOSE "n1 \<ge> k, X\<langle>n1\<rangle> - X\<langle>k\<rangle> \<ge> of_nat (N - 1) * a" THEN
     CHOOSE "n2 \<ge> n1, X\<langle>n2\<rangle> - X\<langle>n1\<rangle> \<ge> a" THEN
     HAVE "of_nat (N - 1) * a + a = of_nat N * a") *})

theorem monotone_cauchy [backward2]:
  "monotone_incr (X::('a::archimedean_field) seq) \<Longrightarrow> upper_bounded X \<Longrightarrow> cauchy X"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "a > 0, \<forall>k. \<exists>n\<ge>k. \<bar>X\<langle>n\<rangle> - X\<langle>k\<rangle>\<bar> \<ge> a" THEN
     HAVE "\<forall>k. \<exists>n\<ge>k. X\<langle>n\<rangle> - X\<langle>k\<rangle> \<ge> a" WITH
      (CHOOSE "n \<ge> k, \<bar>X\<langle>n\<rangle> - X\<langle>k\<rangle>\<bar> \<ge> a" THEN HAVE "X\<langle>n\<rangle> \<ge> X\<langle>k\<rangle>") THEN
     CHOOSE "M, \<forall>n. X\<langle>n\<rangle> \<le> M" THEN
     CHOOSE "N, (of_nat N) * a > (M - X\<langle>0\<rangle>)" THEN
     CHOOSE "n \<ge> 0, X\<langle>n\<rangle> - X\<langle>0\<rangle> \<ge> (of_nat N) * a" THEN HAVE "X\<langle>n\<rangle> \<le> M") *})

theorem monotone_convergence [backward2]:
  "monotone_incr (X::real seq) \<Longrightarrow> upper_bounded X \<Longrightarrow> \<exists>x. converges_to X x"
  by (tactic {* auto2s_tac @{context} (HAVE "cauchy X") *})

theorem monotone_decr_cauchy [backward2]:
  "monotone_decr (X::('a::archimedean_field) seq) \<Longrightarrow> lower_bounded X \<Longrightarrow> cauchy X"
  by (tactic {* auto2s_tac @{context} (HAVE "monotone_incr (-X)" THEN HAVE "cauchy (-X)") *})

theorem monotone_decr_convergence [backward2]:
  "monotone_decr (X::real seq) \<Longrightarrow> lower_bounded X \<Longrightarrow> \<exists>x. converges_to X x"
  by (tactic {* auto2s_tac @{context} (HAVE "cauchy X") *})

subsection {* Dedekind cut completeness *}

theorem half_seq_induct [resolve]:
  "\<forall>n. \<bar>(X::('a::linordered_field) seq)\<langle>n+1\<rangle>\<bar> \<le> \<bar>X\<langle>n\<rangle>\<bar> / 2 \<Longrightarrow> \<bar>X\<langle>n\<rangle>\<bar> \<le> \<bar>X\<langle>0\<rangle>\<bar> / (2 ^ n)"
  by (tactic {* auto2s_tac @{context}
    (CASE "n = 0" THEN HAVE "n = (n-1) + 1" THEN HAVE "\<bar>X\<langle>n\<rangle>\<bar> \<le> \<bar>X\<langle>n-1\<rangle>\<bar> / 2") *})

theorem half_seq_abs_decr [backward2]:
  "\<forall>n. \<bar>(X::('a::linordered_field) seq)\<langle>n+1\<rangle>\<bar> \<le> \<bar>X\<langle>n\<rangle>\<bar> / 2 \<Longrightarrow> n' \<ge> n \<Longrightarrow> \<bar>X\<langle>n'\<rangle>\<bar> \<le> \<bar>X\<langle>n\<rangle>\<bar>"
  by (tactic {* auto2s_tac @{context}
    (HAVE "\<forall>k. \<bar>X\<langle>k+1\<rangle>\<bar> \<le> \<bar>X\<langle>k\<rangle>\<bar>" WITH HAVE "\<bar>X\<langle>k+1\<rangle>\<bar> \<le> \<bar>X\<langle>k\<rangle>\<bar> / 2") *})

theorem nat_less_two_power [resolve]: "n < (2::nat) ^ n"
  by (tactic {* auto2s_tac @{context}
    (CASE "n = 0" THEN HAVE "(n - 1) + 1 < (2::nat) ^ (n-1) + 2 ^ (n-1)") *})

theorem two_power_no_bound [resolve]: "\<exists>n. 2 ^ n > (M::('a::archimedean_field))"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "n, of_nat n > M" THEN HAVE "of_nat (2 ^ n) > M") *})

theorem half_seq_vanishes [resolve]:
  "\<forall>n. \<bar>(X::('a::archimedean_field) seq)\<langle>n+1\<rangle>\<bar> \<le> \<bar>X\<langle>n\<rangle>\<bar> / 2 \<Longrightarrow> vanishes X"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "r > 0, \<not>(\<exists>k. \<forall>n\<ge>k. \<bar>X\<langle>n\<rangle>\<bar> < r)" THEN
     CHOOSE "k, 2 ^ k > \<bar>X\<langle>0\<rangle>\<bar> / r" THEN
     HAVE "\<forall>n\<ge>k. \<bar>X\<langle>n\<rangle>\<bar> < r" WITH HAVE "\<bar>X\<langle>k\<rangle>\<bar> \<le> \<bar>X\<langle>0\<rangle>\<bar> / (2 ^ k)") *})

(* Definition of Dedekind cut: third part is closed downwards condition,
   fourth part is no greatest element condition. *)
definition dedekind_cut :: "('a::linorder) set \<Rightarrow> bool" where
  "dedekind_cut U \<longleftrightarrow> (U \<noteq> {}) \<and> (U \<noteq> UNIV) \<and> (\<forall>a\<in>U. \<forall>b\<le>a. b \<in> U) \<and> (\<forall>a\<in>U. \<exists>b>a. b \<in> U)"
setup {* add_rewrite_rule @{thm dedekind_cut_def} *}

theorem dedekind_cutI1 [forward]:
  "dedekind_cut U \<Longrightarrow> U \<noteq> {} \<and> U \<noteq> UNIV \<and> (\<forall>a\<in>U. \<forall>b\<le>a. b \<in> U)" by auto2
theorem dedekind_cutI2 [backward2]:
  "dedekind_cut U \<Longrightarrow> a \<in> U \<Longrightarrow> \<exists>b>a. b \<in> U" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm dedekind_cut_def} *}

theorem dedekind_cut_compl_closed_upward [forward]:
  "dedekind_cut U \<Longrightarrow> a \<notin> U \<Longrightarrow> \<forall>b>a. b \<notin> U" by auto2

theorem dedekind_complete [resolve]: "dedekind_cut (U::real set) \<Longrightarrow> \<exists>x. \<forall>y. y < x \<longleftrightarrow> y \<in> U"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "a0, a0 \<in> U" THEN CHOOSE "b0, b0 \<notin> U" THEN HAVE "a0 \<le> b0" THEN
     CHOOSE ("A, B, A\<langle>0\<rangle> = a0 \<and> B\<langle>0\<rangle> = b0 \<and>" ^
                   "(\<forall>n. A\<langle>1+n\<rangle> = (if (A\<langle>n\<rangle>+B\<langle>n\<rangle>)/2 \<notin> U then A\<langle>n\<rangle> else (A\<langle>n\<rangle>+B\<langle>n\<rangle>)/2)) \<and>" ^
                   "(\<forall>n. B\<langle>1+n\<rangle> = (if (A\<langle>n\<rangle>+B\<langle>n\<rangle>)/2 \<notin> U then (A\<langle>n\<rangle>+B\<langle>n\<rangle>)/2 else B\<langle>n\<rangle>))") THEN
     CHOOSE "x, converges_to A x \<and> converges_to B x" WITH
      (HAVE "\<forall>n. A\<langle>n\<rangle> \<le> B\<langle>n\<rangle>" WITH INDUCT ("n", []) THEN
       HAVE "monotone_incr A" THEN HAVE "monotone_decr B" THEN
       HAVE "\<forall>n. A\<langle>n\<rangle> \<le> B\<langle>0\<rangle>" THEN HAVE "\<forall>n. B\<langle>n\<rangle> \<ge> A\<langle>0\<rangle>" THEN
       HAVE "\<forall>n. \<bar>(B - A)\<langle>1+n\<rangle>\<bar> \<le> \<bar>(B - A)\<langle>n\<rangle>\<bar> / 2" THEN
       HAVE "vanishes (B - A)" THEN CHOOSE "x', converges_to B x'") THEN
     HAVE "\<forall>n. A\<langle>n\<rangle> \<in> U" WITH INDUCT ("n", []) THEN
     HAVE "\<forall>n. B\<langle>n\<rangle> \<notin> U" WITH INDUCT ("n", []) THEN
     HAVE "\<forall>y. y < x \<longleftrightarrow> y \<in> U" WITH
      (CASE "y < x" WITH CHOOSE "n, y < A\<langle>n\<rangle>" THEN  (* now show \<lbrakk> y \<ge> x, y \<in> U \<rbrakk> \<Longrightarrow> False *)
       HAVE "x \<in> U" THEN CHOOSE "x' > x, x' \<in> U" THEN
       CHOOSE "n, x' > B\<langle>n\<rangle>" THEN HAVE "B\<langle>n\<rangle> \<notin> U")) *})

subsection {* Least upper bound property *}

setup {* add_resolve_prfstep (equiv_forward_th @{thm bdd_above_def}) *}
setup {* add_backward_prfstep (equiv_backward_th @{thm bdd_above_def}) *}
definition upper_bound :: "('a::linorder) set \<Rightarrow> 'a \<Rightarrow> bool" where
  "upper_bound S x \<longleftrightarrow> (\<forall>y\<in>S. x \<ge> y)"
setup {* add_rewrite_rule @{thm upper_bound_def} *}

theorem complete_real [backward1]: "(S::real set) \<noteq> {} \<Longrightarrow> upper_bound S z \<Longrightarrow>
  \<exists>y. upper_bound S y \<and> (\<forall>z. upper_bound S z \<longrightarrow> y \<le> z)"
  by (tactic {* auto2s_tac @{context}
    (LET "U = {x. \<not> upper_bound S x}" THEN
     HAVE "dedekind_cut U" WITH
      (HAVE "U \<noteq> {}" WITH (CHOOSE "x, x \<in> S" THEN CHOOSE "y, y < x" THEN HAVE "y \<in> U") THEN
       HAVE "U \<noteq> UNIV" WITH HAVE "z \<notin> U" THEN
       HAVE "\<forall>u\<in>U. \<forall>v\<le>u. v \<in> U" THEN
       HAVE "\<forall>a\<in>U. \<exists>b>a. b \<in> U" WITH
        (CHOOSE "c \<in> S, a < c" THEN CHOOSE "b, a < b \<and> b < c" THEN HAVE "b \<in> U")) THEN
     CHOOSE "y, \<forall>z. z < y \<longleftrightarrow> z \<in> U" THEN
     HAVE "y \<notin> U" THEN HAVE "upper_bound S y") *})

theorem Sup_real_prop [forward]: "x \<in> (S::real set) \<Longrightarrow> bdd_above S \<Longrightarrow>
  x \<le> (LEAST y. upper_bound S y) \<and> (\<forall>z. upper_bound S z \<longrightarrow> (LEAST y. upper_bound S y) \<le> z)"
  by (tactic {* auto2s_tac @{context}
    (HAVE "S \<noteq> {}" THEN CHOOSE "z, \<forall>x\<in>S. x \<le> z" THEN HAVE "upper_bound S z" THEN
     CHOOSE "y, upper_bound S y \<and> (\<forall>z. upper_bound S z \<longrightarrow> y \<le> z)" THEN
     HAVE "(LEAST y. upper_bound S y) = y") *})

instantiation real :: linear_continuum
(* Part of the proof copies from HOL/Real.thy *)
begin

definition "Sup X = (LEAST z::real. upper_bound X z)"
definition "Inf (X::real set) = - Sup (uminus ` X)"
local_setup {* fold (local_context_map o add_rewrite_rule_gnrc)
  [@{thm Sup_real_def}, @{thm Inf_real_def}] *}

instance proof
  { fix x :: real and X :: "real set"
    show "x \<in> X \<Longrightarrow> bdd_above X \<Longrightarrow> x \<le> Sup X" by auto2 }
  note Sup_upper = this

  { fix z :: real and X :: "real set"
    show "X \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup X \<le> z"
    by (tactic {* auto2s_tac @{context} (HAVE "bdd_above X" THEN CHOOSE "x, x \<in> X") *}) }
  note Sup_least = this

  { fix x :: real and X :: "real set" assume x: "x \<in> X" "bdd_below X" then show "Inf X \<le> x"
      using Sup_upper[of "-x" "uminus ` X"] by (auto simp: Inf_real_def) }
  { fix z :: real and X :: "real set" assume "X \<noteq> {}" "\<And>x. x \<in> X \<Longrightarrow> z \<le> x" then show "z \<le> Inf X"
      using Sup_least[of "uminus ` X" "- z"] by (force simp: Inf_real_def) }
  show "\<exists>a b::real. a \<noteq> b"
    using zero_neq_one by blast
qed

end

end
