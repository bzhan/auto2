(* Arrow's impossibility theorem for strict linear orders, following
   Arrow_Order in AFP/ArrowImpossibilityGS (Tobias Nipkow, 2007). *)

theory Arrow_Order_Ex
imports "../Auto2" "~~/src/HOL/Library/FuncSet"
begin

typedecl alt
typedecl indi

abbreviation "I == (UNIV::indi set)"

axiomatization where
  alt3: "\<exists>a b c::alt. distinct[a,b,c]" and
  finite_indi [resolve]: "finite I"

abbreviation "N == card I"

lemma second_alt [resolve]: "\<exists>a b::alt. a \<noteq> b"
  using alt3 by auto
lemma third_alt [backward]: "a \<noteq> b \<Longrightarrow> \<exists>c::alt. distinct[a,b,c]"
  using alt3 by simp metis

type_synonym pref = "(alt * alt) set"

definition "Lin == {L::pref. strict_linear_order L}"
setup {* add_property_const @{term "strict_linear_order"} *}

theorem Lin_def' [rewrite]: "L \<in> Lin \<longleftrightarrow> strict_linear_order L"
  by (simp add: Lin_def)

theorem trans_strict_linorder [forward]:
  "strict_linear_order L \<Longrightarrow> (x, y) \<in> L \<Longrightarrow> (y, z) \<in> L \<Longrightarrow> (x, z) \<in> L"
  by (meson order_on_defs(4) trans_def)

theorem notin_strict_linorder [forward]:
  "strict_linear_order L \<Longrightarrow> x \<noteq> y \<Longrightarrow> (x, y) \<notin> L \<Longrightarrow> (y, x) \<in> L"
  by (meson UNIV_I irrefl_def order_on_defs(4) total_on_def transD)

theorem irrefl_strict_linorder [resolve]: "strict_linear_order L \<Longrightarrow> (x, x) \<notin> L"
  by (simp add: irrefl_def order_on_defs(4))

theorem total_def: "total L \<longleftrightarrow> (\<forall>x y. x \<noteq> y \<longrightarrow> (x, y) \<in> L \<or> (y, x) \<in> L)"
  by (simp add: total_on_def)

setup {* fold (add_backward_prfstep o equiv_backward_th) [
  @{thm trans_def}, @{thm irrefl_def}, @{thm total_def}, to_obj_eq_th @{thm strict_linear_order_on_def}] *}

lemma linear_alt [resolve]: "\<exists>L::pref. L \<in> Lin"
  using well_order_on[where 'a = "alt", of UNIV]
  apply (auto simp:well_order_on_def Lin_def)
  by (metis strict_linear_order_on_diff_Id)

abbreviation rem :: "pref \<Rightarrow> alt \<Rightarrow> pref" where
  "rem L a \<equiv> {(x,y). (x,y) \<in> L \<and> x\<noteq>a \<and> y\<noteq>a}"

definition mktop :: "pref \<Rightarrow> alt \<Rightarrow> pref" where
  "mktop L b \<equiv> rem L b \<union> {(x,b)|x. x\<noteq>b}"

definition mkbot :: "pref \<Rightarrow> alt \<Rightarrow> pref" where
  "mkbot L b \<equiv> rem L b \<union> {(b,y)|y. y\<noteq>b}"

lemma in_mktop [rewrite]: "(x,y) \<in> mktop L z \<longleftrightarrow> x\<noteq>z \<and> (if y=z then x\<noteq>y else (x,y) \<in> L)"
  by (auto simp: mktop_def)

lemma in_mkbot [rewrite]: "(x,y) \<in> mkbot L z \<longleftrightarrow> y\<noteq>z \<and> (if x=z then x\<noteq>y else (x,y) \<in> L)"
  by (auto simp: mkbot_def)

lemma mktop_Lin [backward]: "L \<in> Lin \<Longrightarrow> mktop L x \<in> Lin" by auto2
lemma mkbot_Lin [backward]: "L \<in> Lin \<Longrightarrow> mkbot L x \<in> Lin" by auto2

definition "Prof = I \<rightarrow> Lin"
theorem Prof_def': "P \<in> Prof \<Longrightarrow> P i \<in> Lin" by (simp add: Pi_def Prof_def)
setup {* add_forward_prfstep_cond @{thm Prof_def'} [with_term "?P ?i"] *}
theorem is_Prof [backward]: "\<forall>i. P i \<in> Lin \<Longrightarrow> P \<in> Prof" by (simp add: Prof_def)

definition "SWF = Prof \<rightarrow> Lin"
theorem SWF_def': "F \<in> SWF \<Longrightarrow> P \<in> Prof \<Longrightarrow> F P \<in> Lin" using SWF_def by fastforce
setup {* add_forward_prfstep_cond @{thm SWF_def'} [with_term "?F ?P"] *}

definition "unanimity F \<longleftrightarrow> (\<forall>P\<in>Prof. \<forall>a b. (\<forall>i. (a, b) \<in> P i) \<longrightarrow> (a, b) \<in> F P)"

theorem unanimity_elim [forward]: "unanimity F \<Longrightarrow> \<forall>i. (a, b) \<in> P i \<Longrightarrow> P \<in> Prof \<Longrightarrow> (a, b) \<in> F P"
  using unanimity_def by blast

definition "IIA F \<longleftrightarrow> (\<forall>P\<in>Prof.\<forall>P'\<in>Prof.\<forall>a b.
   (\<forall>i. (a, b) \<in> P i \<longleftrightarrow> (a, b) \<in> P' i) \<longrightarrow> ((a, b) \<in> F P \<longleftrightarrow> (a, b) \<in> F P'))"

theorem IIA_elim [forward]:
  "IIA F \<Longrightarrow> \<forall>i. (a, b) \<in> P i \<longleftrightarrow> (a, b) \<in> P' i \<Longrightarrow> P \<in> Prof \<Longrightarrow> P' \<in> Prof \<Longrightarrow> (a, b) \<in> F P \<longleftrightarrow> (a, b) \<in> F P'"
  using IIA_def by blast

definition "dictator F i \<longleftrightarrow> (\<forall>P\<in>Prof. F P = P i)"
setup {* add_rewrite_rule @{thm dictator_def} *}

theorem strict_linorder_eq [backward]: "L \<in> Lin \<Longrightarrow> L' \<in> Lin \<Longrightarrow> \<forall>a b. (a, b) \<in> L \<longrightarrow> (a, b) \<in> L' \<Longrightarrow> L = L'"
  by (tactic {* auto2s_tac @{context} (
    OBTAIN "\<forall>a b. (a, b) \<in> L \<longleftrightarrow> (a, b) \<in> L'" WITH CASE "a = b") *})

lemma dictatorI [backward1]:
  "F \<in> SWF \<Longrightarrow> \<forall>P\<in>Prof. \<forall>a b. (a,b) \<in> P i \<longrightarrow> (a,b) \<in> F P \<Longrightarrow> dictator F i" by auto2
setup {* del_prfstep_thm @{thm strict_linorder_eq} *}
setup {* del_prfstep_thm @{thm dictator_def} *}

lemma complete_Lin [backward]: "a \<noteq> b \<Longrightarrow> \<exists>L\<in>Lin. (a, b) \<in> L"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "L', L' \<in> Lin" THEN OBTAIN "(a, b) \<in> (mktop L' b)") *})

lemma complete_Lin3 [backward]: "distinct [a, b, c] \<Longrightarrow> \<exists>L\<in>Lin. (a, b) \<in> L \<and> (b, c) \<in> L"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "L' \<in> Lin, (a, b) \<in> L'" THEN OBTAIN "(b, c) \<in> (mktop L' c)") *})

theorem choice_prof: "\<forall>i. \<exists>L\<in>Lin. A i L \<Longrightarrow> \<exists>P\<in>Prof. \<forall>i. A i (P i)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "P, \<forall>i. P i \<in> Lin \<and> A i (P i)") *})

setup {* add_prfstep_custom ("ex_choice_prof",
  [WithGoal @{term_pat "\<exists>P\<in>Prof. \<forall>i. ?A i P"}],
  PRIORITY_URGENT,
  (fn ((id, _), ths) => fn items => fn _ =>
    [Update.thm_update (id, (ths MRS (backward_th @{thm choice_prof}))),
     Update.ShadowItem {id = id, item = the_single items}]
    handle THM _ => []))
*}

theorem exists_Lin_if [backward]:
  "if C then (\<exists>x\<in>Lin. P x) else (\<exists>x\<in>Lin. Q x) \<Longrightarrow> \<exists>x\<in>Lin. (if C then P x else Q x)" by presburger

definition "arrow_conds F \<longleftrightarrow> F \<in> SWF \<and> unanimity F \<and> IIA F"
setup {* add_rewrite_rule @{thm arrow_conds_def} *}

(* Generalization of IIA (which is when a = a', b = b') *)
definition "strict_neutral F a b a' b' \<longleftrightarrow> (\<forall>P\<in>Prof. \<forall>P'\<in>Prof.
  (\<forall>i. (a, b) \<in> P i \<longleftrightarrow> (a', b') \<in> P' i) \<longrightarrow> ((a, b) \<in> F P \<longleftrightarrow> (a', b') \<in> F P'))"
setup {* add_resolve_prfstep (equiv_backward_th @{thm strict_neutral_def}) *}

theorem strict_neutral_elim [forward]: "strict_neutral F a b a' b' \<Longrightarrow> \<forall>i. (a, b) \<in> P i \<longleftrightarrow> (a', b') \<in> P' i \<Longrightarrow>
  P \<in> Prof \<Longrightarrow> P' \<in> Prof \<Longrightarrow> (a, b) \<in> F P \<longleftrightarrow> (a', b') \<in> F P'"
  using strict_neutral_def by blast

theorem strict_neutrality1: "arrow_conds F \<Longrightarrow> distinct [a, b, b'] \<Longrightarrow> strict_neutral F a b a b'"
  by (tactic {* auto2s_tac @{context} (
    OBTAIN "\<forall>P\<in>Prof. \<forall>P'\<in>Prof. (\<forall>i. (a, b) \<in> P i \<longleftrightarrow> (a, b') \<in> P' i) \<longrightarrow> (a, b) \<in> F P \<longleftrightarrow> (a, b') \<in> F P'" WITH (
    CASE "(a, b) \<in> F P" WITH (
    CHOOSE_FUN ("P''\<in>Prof, (\<forall>i. (if (a, b) \<in> P i then ((a, b) \<in> P'' i \<and> (b, b') \<in> P'' i)" ^
                                "else ((b, b') \<in> P'' i \<and> (b', a) \<in> P'' i)))") THEN
    OBTAIN "\<forall>i. (b, b') \<in> P'' i" THEN
    OBTAIN "\<forall>i. ((a, b) \<in> P i \<longleftrightarrow> (a, b) \<in> P'' i) \<and> ((a, b) \<in> P i \<longleftrightarrow> (a, b') \<in> P'' i)" THEN
    OBTAIN "\<forall>i. (a, b') \<in> P'' i \<longleftrightarrow> (a, b') \<in> P' i") THEN
    (* Other direction *)
    CHOOSE_FUN ("P''\<in>Prof, (\<forall>i. (if (b, a) \<in> P i then ((b', b) \<in> P'' i \<and> (b, a) \<in> P'' i)" ^
                                "else ((a, b') \<in> P'' i \<and> (b', b) \<in> P'' i)))") THEN
    OBTAIN "\<forall>i. (b', b) \<in> P'' i" THEN
    OBTAIN "\<forall>i. ((b, a) \<in> P i \<longleftrightarrow> (b, a) \<in> P'' i) \<and> ((b, a) \<in> P i \<longleftrightarrow> (b', a) \<in> P'' i)" THEN
    OBTAIN "\<forall>i. (b', a) \<in> P'' i \<longleftrightarrow> (b', a) \<in> P' i")) *})
setup {* add_backward2_prfstep_cond @{thm strict_neutrality1} [with_cond "?b \<noteq> ?b'"] *}

theorem strict_neutrality2: "arrow_conds F \<Longrightarrow> distinct [a, b, b'] \<Longrightarrow> strict_neutral F b a b' a"
  by (tactic {* auto2s_tac @{context} (
    OBTAIN "strict_neutral F a b a b'" THEN
    OBTAIN "\<forall>P\<in>Prof. \<forall>P'\<in>Prof. (\<forall>i. (b, a) \<in> P i \<longleftrightarrow> (b', a) \<in> P' i) \<longrightarrow> ((b, a) \<in> F P \<longleftrightarrow> (b', a) \<in> F P')" WITH
      OBTAIN "\<forall>i. (a, b) \<in> P i \<longleftrightarrow> (a, b') \<in> P' i") *})
setup {* add_backward2_prfstep_cond @{thm strict_neutrality2} [with_cond "?b \<noteq> ?b'"] *}

theorem strict_neutrality_trans [forward]:
  "strict_neutral F a b a'' b'' \<Longrightarrow> strict_neutral F a'' b'' a' b' \<Longrightarrow> a'' \<noteq> b'' \<Longrightarrow> strict_neutral F a b a' b'"
  by (tactic {* auto2s_tac @{context} (
    OBTAIN "\<forall>P\<in>Prof. \<forall>P'\<in>Prof. (\<forall>i. (a, b) \<in> P i \<longleftrightarrow> (a', b') \<in> P' i) \<longrightarrow> ((a, b) \<in> F P \<longleftrightarrow> (a', b') \<in> F P')" WITH (
      CHOOSE_FUN "P''\<in>Prof, (\<forall>i. (if (a, b) \<in> P i then (a'', b'') \<in> P'' i else (b'', a'') \<in> P'' i))" THEN
      OBTAIN "\<forall>i. (a, b) \<in> P i \<longleftrightarrow> (a'', b'') \<in> P'' i" THEN
      OBTAIN "\<forall>i. (a'', b'') \<in> P'' i \<longleftrightarrow> (a', b') \<in> P' i")) *})

theorem strict_neutrality [backward2]: "arrow_conds F \<Longrightarrow> a \<noteq> b \<Longrightarrow> a' \<noteq> b' \<Longrightarrow> strict_neutral F a b a' b'"
  by (tactic {* auto2s_tac @{context} (
    OBTAIN "strict_neutral F a b b a" WITH (
      CHOOSE "c, distinct [a, b, c]" THEN OBTAIN "strict_neutral F a b a c" THEN
      OBTAIN "strict_neutral F a c b c" THEN OBTAIN "strict_neutral F b c b a") THEN
    OBTAIN "strict_neutral F a b a b" WITH (
      OBTAIN "\<forall>P\<in>Prof. \<forall>P'\<in>Prof. (\<forall>i. (a, b) \<in> P i \<longleftrightarrow> (a, b) \<in> P' i) \<longrightarrow> (a, b) \<in> F P \<longleftrightarrow> (a, b) \<in> F P'") THEN
    CASE "b' = a" WITH OBTAIN "strict_neutral F b a a' a" THEN
    CASE "a' = b" WITH OBTAIN "strict_neutral F b a b b'" THEN
    CASE "b' = b" THEN CASE "a' = a" THEN  (* All distinct *)
    OBTAIN "strict_neutral F a b a b'" THEN OBTAIN "strict_neutral F a b' a' b'") *})

(* Setup about bijections *)
setup {* add_backward_prfstep @{thm ex_bij_betw_finite_nat} *}

theorem bij_betw_range [backward2]: "bij_betw h S {0..<N} \<Longrightarrow> i \<in> S \<Longrightarrow> h i < N"
  by (metis atLeastLessThan_iff bij_betw_def image_eqI)

theorem bij_I_prop [rewrite]: "bij_betw f I B \<Longrightarrow> inv f (f x) = x"
  using bij_betw_def inv_f_f by metis

(* Exists splitting n *)
setup {* add_backward1_prfstep @{thm ex_least_nat_less} *}
theorem ex_nat_split [backward1]: "\<not> P 0 \<Longrightarrow> P (n::nat) \<Longrightarrow> \<exists>k<n. \<not> P k \<and> P (k + 1)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "k < n, (\<forall>i\<le>k. \<not> P i) \<and> P (k + 1)") *})

theorem Arrow: "arrow_conds F \<Longrightarrow> \<exists>i. dictator F i"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "h::(indi \<Rightarrow> nat), bij_betw h I {0..<N}" THEN
    OBTAIN "\<forall>i. h i < N" THEN
    CHOOSE "a, b::alt, a \<noteq> b" THEN
    CHOOSE_FUN2 "P, (\<forall>n. P n \<in> Prof \<and> (\<forall>i. if h i \<ge> n then (a, b) \<in> P n i else (b, a) \<in> P n i))" THEN
    OBTAIN "(a, b) \<in> F (P 0)" WITH OBTAIN "\<forall>i. (a, b) \<in> P 0 i" THEN
    OBTAIN "(b, a) \<in> F (P N)" WITH OBTAIN "\<forall>i. (b, a) \<in> P N i" THEN
    CHOOSE "n < N, (b, a) \<notin> F (P n) \<and> (b, a) \<in> F (P (n + 1))" THEN
    OBTAIN "dictator F (inv h n)" WITH
      OBTAIN "\<forall>P'\<in>Prof. \<forall>a' b'. (a', b') \<in> P' (inv h n) \<longrightarrow> (a', b') \<in> F P'" WITH (
        CHOOSE "c', distinct [a', b', c']" THEN
        CHOOSE_FUN ("P'' \<in> Prof, (\<forall>i. (if h i < n then P'' i = mktop (P' i) c' " ^
                                      "else if h i > n then P'' i = mkbot (P' i) c' " ^
                                      "else ((a', c') \<in> P'' i \<and> (c', b') \<in> P'' i)))") THEN
        OBTAIN "\<forall>i. (a', b') \<in> P' i \<longleftrightarrow> (a', b') \<in> P'' i" THEN
        OBTAIN "\<forall>i. (c', b') \<in> P'' i \<longleftrightarrow> (a, b) \<in> P n i" THEN
        OBTAIN "\<forall>i. (a', c') \<in> P'' i \<longleftrightarrow> (b, a) \<in> P (n + 1) i" THEN
        OBTAIN "strict_neutral F c' b' a b" THEN OBTAIN "strict_neutral F a' c' b a")) *})

end
