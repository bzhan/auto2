(* Hoare logic, following chapters Hoare and Hoare2 in "Software
   Foundations". *)

theory Hoare_Rules
imports Hoare_States
begin

datatype assertion = Assert "state \<Rightarrow> bool"

fun aseval :: "assertion \<Rightarrow> state \<Rightarrow> bool" where "aseval (Assert f) st = f st"
setup {* add_rewrite_rule @{thm aseval.simps} *}
theorem assert_ext [backward]:
  "\<forall>st. aseval A1 st = aseval A2 st \<Longrightarrow> A1 = A2" apply (cases A1) apply (cases A2) by auto

definition assert_implies :: "assertion \<Rightarrow> assertion \<Rightarrow> bool" (infix "\<longmapsto>" 50) where
  "assert_implies P Q = (\<forall>st. aseval P st \<longrightarrow> aseval Q st)"

definition assert_iff :: "assertion \<Rightarrow> assertion \<Rightarrow> bool" where
  "assert_iff P Q = (P \<longmapsto> Q \<and> Q \<longmapsto> P)"

definition hoare_triple :: "assertion \<Rightarrow> com \<Rightarrow> assertion \<Rightarrow> bool" ("{{ _ }}/ _/ {{ _ }}" [90,90,90] 90) where
  "{{ P }} c {{ Q }} = (\<forall>st st'. ceval c st st' \<longrightarrow> aseval P st \<longrightarrow> aseval Q st')"

setup {* add_rewrite_rule @{thm hoare_triple_def} *}
setup {* add_rewrite_rule @{thm assert_implies_def} *}
setup {* add_rewrite_rule @{thm assert_iff_def} *}

theorem assert_implies_triv [resolve]: "P \<longmapsto> P" by auto2
theorem assert_iff_triv [resolve]: "assert_iff P P" by auto2

theorem hoare_post_true: "\<forall>st. aseval Q st \<Longrightarrow> {{ P }} c {{ Q }}" by auto2
theorem hoare_pre_false: "\<forall>st. \<not>(aseval P st) \<Longrightarrow> {{ P }} c {{ Q }}" by auto2

theorem hoare_consequence_pre: "{{ P' }} c {{ Q }} \<Longrightarrow> P \<longmapsto> P' \<Longrightarrow> {{ P }} c {{ Q }}" by auto2
theorem hoare_consequence_post: "{{ P }} c {{ Q' }} \<Longrightarrow> Q' \<longmapsto> Q \<Longrightarrow> {{ P }} c {{ Q }}" by auto2
theorem hoare_consequence: "{{ P' }} c {{ Q' }} \<Longrightarrow> P \<longmapsto> P' \<Longrightarrow> Q' \<longmapsto> Q \<Longrightarrow> {{ P }} c {{ Q }}" by auto2

theorem hoare_skip: "{{ P }} SKIP {{ P }}" by auto2
theorem hoare_seq: "{{ Q }} c2 {{ R }} \<Longrightarrow> {{ P }} c1 {{ Q }} \<Longrightarrow> {{ P }} (c1 ; c2) {{ R }}" by auto2

definition assign_sub :: "assertion \<Rightarrow> id \<Rightarrow> aexp \<Rightarrow> assertion" (" _ [ _ \<rightarrow> _ ]" [94,95,95] 95) where
  "(P [ x \<rightarrow> a ]) = Assert (\<lambda>st. aseval P (st {x \<rightarrow> aeval st a}))"
theorem eval_assign_sub [rewrite]:
  "aseval (P [ x \<rightarrow> a ]) st = aseval P (st {x \<rightarrow> aeval st a})" by (simp add: assign_sub_def)

(* Example for assign_sub. *)
definition Xle5 :: assertion where "Xle5 = Assert (\<lambda>st. eval st X \<le> 5)"
setup {* add_rewrite_rule @{thm Xle5_def} *}
theorem Xle5_test: "aseval (Xle5 [ X \<rightarrow> ANum 3 ]) st" by auto2

definition incrXle5 :: assertion where "incrXle5 = Xle5 [ X \<rightarrow> (APlus (AId X) (ANum 1)) ]"
setup {* add_rewrite_rule @{thm incrXle5_def} *}
theorem incrXle5_spec: "incrXle5 = Assert (\<lambda>st. eval st X \<le> 4)" by auto2

definition XtimesYis6 :: assertion where "XtimesYis6 = Assert (\<lambda>st. eval st X * eval st Y = 6)"
setup {* add_rewrite_rule @{thm XtimesYis6_def} *}
theorem XtimesYis6_test: "XtimesYis6 [ X \<rightarrow> ANum 2 ] [Y \<rightarrow> ANum 3 ] = Assert (\<lambda>st. True)" by auto2

theorem hoare_assign: "{{ Q [ x \<rightarrow> a ] }} (x := a) {{ Q }}" by auto2

definition and_bassn :: "assertion \<Rightarrow> bexp \<Rightarrow> assertion" (infixl "&&" 95) where
  "(A && b) = Assert (\<lambda>st. aseval A st \<and> beval st b)"
definition and_nbassn :: "assertion \<Rightarrow> bexp \<Rightarrow> assertion" (infixl "&~" 95) where
  "(A &~ b) = Assert (\<lambda>st. aseval A st \<and> \<not> beval st b)"

theorem eval_bassn [rewrite]: "aseval (A && b) st = (aseval A st \<and> beval st b)"
  by (simp add: and_bassn_def)
theorem eval_nbassn [rewrite]: "aseval (A &~ b) st = (aseval A st \<and> \<not> beval st b)"
  by (simp add: and_nbassn_def)

theorem hoare_if: "{{ (P && b) }} c1 {{ Q }} \<Longrightarrow> {{ P &~ b }} c2 {{ Q }} \<Longrightarrow>
                   {{ P }} (IF b THEN c1 ELSE c2 FI) {{ Q }}" by auto2

theorem hoare_while: "{{ P && b }} c {{ P }} \<Longrightarrow> {{ P }} (WHILE b DO c OD) {{ P &~ b }}"
@proof
  @let "v = WHILE b DO c OD" @then
  @have "\<forall>st st'. ceval v st st' \<longrightarrow> aseval P st \<longrightarrow> aseval (P &~ b) st'" @with
    @prop_induct "ceval v st st'" "v = WHILE b DO c OD \<longrightarrow> aseval P st \<longrightarrow> aseval (P &~ b) st'" @end
@qed

(* Formally decorated programs. *)
datatype dcom =
  DCSkip assertion   ("DSKIP {{ _ }}")
| DCAss id aexp assertion  ("(2_ ::=/ _) {{ _ }}" [70, 65] 60)
| DCSeq dcom dcom    (infixr ";;" 60)
| DCIf bexp assertion dcom assertion dcom assertion ("(1IF _/ THEN {{ _ }}/ _/ ELSE {{ _ }}/ _/ FI {{ _ }})" [0,0,0] 61)
| DCWhile bexp assertion dcom assertion  ("(1WHILE _/ DO {{ _ }} _ /OD {{ _ }})" [0,0] 61)
| DCPre assertion dcom  ("{{ _ }}/ _" [80,79] 80)
| DCPost dcom assertion ("_ \<rightarrow>/ {{ _ }}" [75,76] 75)

definition noCond :: assertion where "noCond = Assert (\<lambda>st. True)"
theorem eval_noCond [resolve]: "aseval noCond st" by (simp add: noCond_def)

fun extract_dcom :: "dcom \<Rightarrow> com" where
  "extract_dcom (DCSkip P) = SKIP"
| "extract_dcom (d1 ;; d2) = (extract_dcom d1; extract_dcom d2)"
| "extract_dcom (x ::= a {{ P }}) = (x := a)"
| "extract_dcom (IF b THEN {{ P }} d1 ELSE {{ Q }} d2 FI {{ R }}) = IF b THEN extract_dcom d1 ELSE extract_dcom d2 FI"
| "extract_dcom (WHILE b DO {{ P }} d OD {{ Q }}) = WHILE b DO extract_dcom d OD"
| "extract_dcom ({{ P }} d) = extract_dcom d"
| "extract_dcom (d \<rightarrow> {{ Q }}) = extract_dcom d"
setup {* add_eval_fun_prfsteps @{thms extract_dcom.simps} *}

fun post :: "dcom \<Rightarrow> assertion" where
  "post (DCSkip P) = P"
| "post (d1 ;; d2) = post d2"
| "post (x ::= a {{ P }}) = P"
| "post (IF b THEN {{ P }} d1 ELSE {{ Q }} d2 FI {{ R }}) = R"
| "post (WHILE b DO {{ P }} d OD {{ Q }}) = Q"
| "post ({{ P }} d) = post d"
| "post (d \<rightarrow> {{ Q }}) = Q"
setup {* add_eval_fun_prfsteps @{thms post.simps} *}

fun pre :: "dcom \<Rightarrow> assertion" where
  "pre (d1 ;; d2) = pre d1"
| "pre ({{ P }} d) = P"
| "pre (d \<rightarrow> {{ Q }}) = pre d"
| "pre _ = noCond"
setup {* add_eval_fun_prfsteps @{thms pre.simps} *}

definition dec_correct :: "dcom \<Rightarrow> bool" where
  "dec_correct d = {{ pre d }} (extract_dcom d) {{ post d }}"
setup {* add_rewrite_rule @{thm dec_correct_def} *}

fun vcond :: "assertion \<Rightarrow> dcom \<Rightarrow> bool" where
  "vcond P (DCSkip Q) = (P \<longmapsto> Q)"
| "vcond P (d1 ;; d2) = (vcond P d1 \<and> vcond (post d1) d2)"
| "vcond P (x ::= a {{ Q }}) = (P \<longmapsto> (Q [ x \<rightarrow> a ]))"
| "vcond P (IF b THEN {{ P1 }} d1 ELSE {{ P2 }} d2 FI {{ Q }}) =
  (P && b \<longmapsto> P1 \<and> P &~ b \<longmapsto> P2 \<and>
   assert_iff Q (post d1) \<and> assert_iff Q (post d2) \<and>
   vcond P1 d1 \<and> vcond P2 d2)"
| "vcond P (WHILE b DO {{ Pbody }} d OD {{ Ppost }}) =
  (P \<longmapsto> post d \<and> assert_iff Pbody (post d && b) \<and> assert_iff Ppost (post d &~ b) \<and>
   vcond Pbody d)"
| "vcond P ({{ P' }} d) = (P \<longmapsto> P' \<and> vcond P' d)"
| "vcond P (d \<rightarrow> {{ Q }}) = (vcond P d \<and> post d \<longmapsto> Q)"
setup {* fold add_rewrite_rule @{thms vcond.simps} *}
setup {* add_eval_fun_prfsteps' @{thms vcond.simps}
  (@{thms vcond.simps} @ @{thms post.simps} @ @{thms pre.simps}) *}

setup {* add_var_induct_rule @{thm dcom.induct} *}

(* Proof using verification conditions. *)
setup {* del_prfstep_thm @{thm hoare_triple_def} *}
ML {* val hoare_rules =
  [@{thm hoare_skip}, @{thm hoare_assign}, @{thm hoare_seq}, @{thm hoare_if}, @{thm hoare_while},
   @{thm hoare_consequence}, @{thm hoare_consequence_pre}, @{thm hoare_consequence_post}] *}
setup {* fold add_backward1_prfstep [@{thm hoare_consequence_pre}, @{thm hoare_consequence_post}] *}
setup {* fold add_forward_prfstep [@{thm hoare_consequence_pre}, @{thm hoare_consequence_post}] *}
setup {* add_resolve_prfstep @{thm hoare_skip} *}
setup {* add_resolve_prfstep @{thm hoare_assign} *}
setup {* add_backward1_prfstep @{thm hoare_seq} *}
setup {* add_backward1_prfstep @{thm hoare_if} *}
setup {* add_backward_prfstep @{thm hoare_while} *}
theorem vcond_correct: "vcond P d \<Longrightarrow> {{ P }} (extract_dcom d) {{ post d }}"
  @proof @induct d arbitrary P @qed

setup {* add_backward_prfstep @{thm vcond_correct} *}
setup {* fold del_prfstep_thm @{thms extract_dcom.simps} *}

definition dec_while :: dcom where "dec_while =
     {{ noCond }} (
     WHILE (BNot (BEq (AId X) (ANum 0)))
     DO
      {{ noCond && BNot (BEq (AId X) (ANum 0)) }}
      (X ::= AMinus (AId X) (ANum 1)
      {{ noCond }})
     OD
     {{ noCond &~ BNot (BEq (AId X) (ANum 0)) }}) \<rightarrow>
     {{ noCond }}
"
setup {* add_rewrite_rule @{thm dec_while_def} *}
theorem dec_while_correct: "dec_correct dec_while" by auto2

end
