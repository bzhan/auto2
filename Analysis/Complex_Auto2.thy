theory Complex_Auto2
imports Real Rat_Thms
begin

datatype complex = Complex (Re: real) (Im: real)

setup {* fold add_rewrite_rule @{thms complex.sel} *}
setup {* add_gen_prfstep ("complex_eq_goal_case",
  [WithGoal @{term_pat "(?c::complex) = ?c'"},
   CreateCase @{term_pat "Re ?c \<noteq> Re ?c'"},
   Filter (order_filter "c" "c'")]) *}
theorem complex_eq_goal2: "Re c = Re c' \<Longrightarrow> Im c = Im c' \<Longrightarrow> c = c'" using complex.expand by auto
setup {* add_backward2_prfstep_cond @{thm complex_eq_goal2} [with_filt (order_filter "c" "c'")] *}

instantiation complex :: ab_group_add
begin

definition zero_complex where "0 = Complex 0 0"
definition plus_complex where "x + y = Complex (Re x + Re y) (Im x + Im y)"
definition uminus_complex where "-x = Complex (-Re x) (-Im x)"
definition minus_complex where "x - y = Complex (Re x - Re y) (Im x - Im y)"

theorem complex_evals1 [rewrite]:
  "Re 0 = 0" "Im 0 = 0" "Re (x + y) = Re x + Re y" "Im (x + y) = Im x + Im y"
  "Re (-x) = -(Re x)" "Im (-x) = -(Im x)" "Re (x - y) = Re x - Re y" "Im (x - y) = Im x - Im y"
by (simp add: zero_complex_def plus_complex_def uminus_complex_def minus_complex_def)+

local_setup {* fold add_rewrite_rule_ctxt @{thms complex_evals1} *}

instance by intro_classes auto2+

end

setup {* add_rewrite_rule_back @{thm zero_complex_def} *}

theorem square_positive [backward]: "(a::real) \<noteq> 0 \<Longrightarrow> a * a > 0" using mult_neg_neg by force
setup {* add_resolve_prfstep @{thm Rings.linordered_ring_class.zero_le_square} *}

lemma complex_neq0 [backward]: "a \<noteq> 0 \<Longrightarrow> (Re a)\<^sup>2 + (Im a)\<^sup>2 > 0"
  by (tactic {* auto2s_tac @{context} (
    OBTAIN "a = Complex (Re a) (Im a)" THEN
    OBTAIN "Re a \<noteq> 0 \<or> Im a \<noteq> 0" THEN
    CASE "Re a \<noteq> 0" WITH OBTAIN "Re a * Re a > 0") *})

instantiation complex :: field
begin

definition one_complex where "1 = Complex 1 0"
definition times_complex where
  "x * y = Complex (Re x * Re y - Im x * Im y) (Re x * Im y + Im x * Re y)"
definition inverse_complex where
  "inverse x = Complex (Re x / ((Re x)\<^sup>2 + (Im x)\<^sup>2)) (- Im x / ((Re x)\<^sup>2 + (Im x)\<^sup>2))"
definition "x div (y::complex) = x * inverse y"

theorem complex_evals2 [rewrite]:
  "Re 1 = 1" "Im 1 = 0" "Re (x * y) = Re x * Re y - Im x * Im y" "Im (x * y) = Re x * Im y + Im x * Re y"
  "Re (inverse x) = Re x / ((Re x)\<^sup>2 + (Im x)\<^sup>2)" "Im (inverse x) = - Im x / ((Re x)\<^sup>2 + (Im x)\<^sup>2)"
by (simp add: one_complex_def times_complex_def inverse_complex_def divide_complex_def)+

local_setup {* fold add_rewrite_rule_ctxt (@{thms complex_evals2} @ [@{thm divide_complex_def}]) *}

instance proof
fix a b c :: complex
show "a * b = b * a" by auto2
show "1 * a = a" by auto2
show "(a + b) * c = a * c + b * c" by auto2
show "a * b * c = a * (b * c)" by auto2
show "a div b = a * inverse b" by auto2
show "(0::complex) \<noteq> 1"
  by (tactic {* auto2s_tac @{context} (OBTAIN "Re 0 = 0 \<and> Re 1 = 1") *})
show "inverse (0::complex) = 0" by auto2
show "a \<noteq> 0 \<Longrightarrow> inverse a * a = 1"
  by (tactic {* auto2s_tac @{context} (OBTAIN "(Re a)\<^sup>2 + (Im a)\<^sup>2 > 0") *})
qed

end

end
