(* States and commands, following chapter Imp in "Software
   Foundations". *)

theory Hoare_States
imports "../Auto2"
begin

datatype id = Id nat

theorem id_ext1: "Id m = Id n \<Longrightarrow> m = n" by simp
theorem id_ext2: "m = n \<Longrightarrow> Id m = Id n" by simp
setup {* add_forward_prfstep_cond @{thm id_ext1} [with_cond "?m \<noteq> ?n"] *}
setup {* add_backward_prfstep @{thm id_ext2} *}

datatype state = State "id \<Rightarrow> nat"

definition empty_state :: state ("ES") where "ES = State (\<lambda>x. 0)"
fun eval :: "state \<Rightarrow> id \<Rightarrow> nat" where "eval (State f) x = f x"

definition update :: "state \<Rightarrow> id \<Rightarrow> nat \<Rightarrow> state" (" _ { _ \<rightarrow> _ }" [89,90,90] 90) where
  "st { x \<rightarrow> n } = State (\<lambda>x'. (if x = x' then n else eval st x'))"

theorem state_ext [backward]:
  "\<forall>x. eval s x = eval t x \<Longrightarrow> s = t" apply (cases s) apply (cases t) by auto
theorem eval_update: "eval (st { x \<rightarrow> n }) x' = (if x = x' then n else eval st x')" by (simp add: update_def)
theorem eval_empty: "eval ES n = 0" by (simp add: empty_state_def)

ML_file "hoare_eval.ML"

theorem update_example: "eval (ES {Id 2 \<rightarrow> n}) (Id 3) = 0" by auto2
theorem update_shadow: "st {x \<rightarrow> m} {x \<rightarrow> n} = st {x \<rightarrow> n}" by auto2
theorem update_same [rewrite]: "eval st x = n \<Longrightarrow> st {x \<rightarrow> n} = st" by auto2
theorem update_permute: "x \<noteq> y \<Longrightarrow> st {y \<rightarrow> m} {x \<rightarrow> n} = st {x \<rightarrow> n} {y \<rightarrow> m}" by auto2

abbreviation X :: id where "X \<equiv> Id 0"
abbreviation Y :: id where "Y \<equiv> Id 1"
abbreviation Z :: id where "Z \<equiv> Id 2"

datatype aexp =
  ANum nat
| AId id
| APlus aexp aexp
| AMinus aexp aexp
| AMult aexp aexp

datatype bexp =
  BTrue
| BFalse
| BEq aexp aexp
| BLe aexp aexp
| BNot bexp
| BAnd bexp bexp

fun aeval :: "state \<Rightarrow> aexp \<Rightarrow> nat" where
  "aeval st (ANum n) = n"
| "aeval st (AId x) = eval st x"
| "aeval st (APlus m n) = aeval st m + aeval st n"
| "aeval st (AMinus m n) = aeval st m - aeval st n"
| "aeval st (AMult m n) = aeval st m * aeval st n"
setup {* add_eval_fun_prfsteps @{thms aeval.simps} *}

theorem test_aeval1: "aeval (ES {X \<rightarrow> 5})
        (APlus (ANum 3) (AMult (AId X) (ANum 2))) = 13" by auto2

fun beval :: "state \<Rightarrow> bexp \<Rightarrow> bool" where
  "beval st BTrue = True"
| "beval st BFalse = False"
| "beval st (BEq a1 a2) = (aeval st a1 = aeval st a2)"
| "beval st (BLe a1 a2) = (aeval st a1 \<le> aeval st a2)"
| "beval st (BNot b) = (\<not> beval st b)"
| "beval st (BAnd b1 b2) = (beval st b1 \<and> beval st b2)"
setup {* fold add_rewrite_rule @{thms beval.simps} *}
setup {* add_eval_fun_prfsteps' @{thms beval.simps} (@{thms aeval.simps} @ @{thms beval.simps}) *}

theorem test_beval1: "beval (ES {X \<rightarrow> 5})
        (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))" by auto2

datatype com =
  CSkip                    ("SKIP")
| CAss id aexp             ("(2_ :=/ _)" [70, 65] 61)
| CSeq com com             ("(_;/ _)" [61,60] 60)
| CIf bexp com com         ("(1IF _/ THEN _ / ELSE _/ FI)" [0,0,0] 61)
| CWhile bexp com          ("(1WHILE _/ DO _ /OD)"  [0,0] 61)
setup {* fold add_resolve_prfstep @{thms com.simps(5-24)} *}
setup {* fold add_forward_prfstep (map equiv_forward_th @{thms com.simps(1-4)}) *}

(* Factorial function. *)
definition fact_fun :: com where "fact_fun =
  Z := AId X;
  Y := ANum 1;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y := AMult (AId Y) (AId Z);
    Z := AMinus (AId Z) (ANum 1)
  OD"

(* Assignment. *)
definition plus2 :: com where "plus2 =
  X := APlus (AId X) (ANum 2)"

definition XtimesYinZ :: com where "XtimesYinZ =
  Z := (AMult (AId X) (AId Y))"

definition subtract_slowly_body :: com where "subtract_slowly_body =
  Z := AMinus (AId Z) (ANum 1);
  X := AMinus (AId X) (ANum 1)"

(* Loops. *)
definition subtract_slowly :: com where "subtract_slowly =
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  OD"

definition subtract_3_from_5_slowly :: com where "subtract_3_from_5_slowly =
  X := ANum 3 ;
  Z := ANum 5 ;
  subtract_slowly"

(* An infinite loop. *)
definition loop :: com where "loop =
  WHILE BTrue DO
    SKIP
  OD"

inductive ceval :: "com \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
where
  "ceval SKIP st st"
| "aeval st a = n \<Longrightarrow> ceval (x := a) st (st {x \<rightarrow> n})"
| "ceval c1 st st' \<Longrightarrow> ceval c2 st' st'' \<Longrightarrow> ceval (c1 ; c2) st st''"
| "beval st b \<Longrightarrow> ceval c1 st st' \<Longrightarrow> ceval (IF b THEN c1 ELSE c2 FI) st st'"
| "\<not>(beval st b) \<Longrightarrow> ceval c2 st st' \<Longrightarrow> ceval (IF b THEN c1 ELSE c2 FI) st st'"
| "\<not>(beval st b) \<Longrightarrow> ceval (WHILE b DO c OD) st st"
| "beval st b \<Longrightarrow> ceval c st st' \<Longrightarrow> ceval (WHILE b DO c OD) st' st'' \<Longrightarrow> ceval (WHILE b DO c OD) st st''"

(* Using the introduction rules. *)
setup {* add_gen_prfstep ("ceval_if_intro",
  [WithFact @{term_pat "ceval (IF ?b THEN ?c1 ELSE ?c2 FI) ?st ?st'"},
   CreateCase @{term_pat "beval ?st ?b"}]) *}
setup {* add_gen_prfstep ("ceval_if_intro'",
  [WithGoal @{term_pat "ceval (IF ?b THEN ?c1 ELSE ?c2 FI) ?st ?st'"},
   CreateCase @{term_pat "beval ?st ?b"}]) *}
setup {* add_gen_prfstep ("ceval_while_intro",
  [WithFact @{term_pat "ceval (WHILE ?b DO ?c OD) ?st ?st''"},
   CreateCase @{term_pat "beval ?st ?b"}]) *}
setup {* add_gen_prfstep ("ceval_while_intro'",
  [WithGoal @{term_pat "ceval (WHILE ?b DO ?c OD) ?st ?st''"},
   CreateCase @{term_pat "beval ?st ?b"}]) *}
setup {* add_resolve_prfstep @{thm ceval.intros(1)} *}
setup {* add_backward_prfstep @{thm ceval.intros(2)} *}
setup {* add_backward1_prfstep @{thm ceval.intros(3)} *}
setup {* fold add_backward2_prfstep [@{thm ceval.intros(3)}, @{thm ceval.intros(4)}, @{thm ceval.intros(5)}] *}
setup {* add_resolve_prfstep @{thm ceval.intros(6)} *}
theorem ceval_intros7' [forward]: "beval st b \<Longrightarrow> \<not>(ceval (WHILE b DO c OD) st st'') \<Longrightarrow>
  \<forall>st'. ceval c st st' \<longrightarrow> \<not>(ceval (WHILE b DO c OD) st' st'')" using ceval.intros(7) by blast

(* Automatically step forward an assignment step. *)
theorem ceval_assign [backward]: "ceval B (st { x \<rightarrow> aeval st a }) st' \<Longrightarrow> ceval (x := a; B) st st'" by auto2
theorem ceval_assign' [backward]: "st' = st { x \<rightarrow> aeval st a } \<Longrightarrow> ceval (x := a) st st'" by auto2

(* Automatically step forward a skip step. *)
theorem ceval_skip_left [backward]: "ceval C st st' \<Longrightarrow> ceval (SKIP; C) st st'"
  by (tactic {* auto2s_tac @{context} (HAVE "ceval SKIP st st") *})

theorem ceval_example1: "ceval (X := ANum 2; IF BLe (AId X) (ANum 1) THEN Y := ANum 3 ELSE Z := ANum 4 FI)
  ES (ES {X \<rightarrow> 2} {Z \<rightarrow> 4})" by auto2

theorem ceval_example2: "ceval (X := ANum 0; Y := ANum 1; Z := ANum 2)
  ES (ES {X \<rightarrow> 0} {Y \<rightarrow> 1} {Z \<rightarrow> 2})" by auto2

definition pup_to_n :: com where "pup_to_n =
  Y := ANum 0;
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    Y := APlus (AId Y) (AId X);
    X := AMinus (AId X) (ANum 1)
  OD"
setup {* add_rewrite_rule @{thm pup_to_n_def} *}

theorem pup_to_2_ceval: "ceval pup_to_n (ES { X \<rightarrow> 2 })
  (ES {X \<rightarrow> 2} {Y \<rightarrow> 0} {Y \<rightarrow> 2} {X \<rightarrow> 1} {Y \<rightarrow> 3} {X \<rightarrow> 0})"
  by (tactic {* auto2s_tac @{context}
    (HAVE
      ("ceval (Y := APlus (AId Y) (AId X); X := AMinus (AId X) (ANum 1))" ^
       "(ES {X \<rightarrow> 2} {Y \<rightarrow> 0})" ^
       "(ES {X \<rightarrow> 2} {Y \<rightarrow> 0} {Y \<rightarrow> 2} {X \<rightarrow> 1})")
     THEN HAVE
      ("ceval (Y := APlus (AId Y) (AId X); X := AMinus (AId X) (ANum 1))" ^
       "(ES {X \<rightarrow> 2} {Y \<rightarrow> 0} {Y \<rightarrow> 2} {X \<rightarrow> 1})" ^
       "(ES {X \<rightarrow> 2} {Y \<rightarrow> 0} {Y \<rightarrow> 2} {X \<rightarrow> 1} {Y \<rightarrow> 3} {X \<rightarrow> 0})"))
  *})

(* Inversion rules. *)
theorem skip_invert: "ceval SKIP st st' \<Longrightarrow> st = st'" using ceval.cases by auto
theorem assign_invert: "ceval (x := a) st st' \<Longrightarrow> st' = st { x \<rightarrow> aeval st a }" using ceval.cases by auto
theorem seq_invert: "ceval (c; d) st st'' \<Longrightarrow> \<exists>st'. ceval c st st' \<and> ceval d st' st''" using ceval.cases by blast
theorem if_invert: "ceval (IF b THEN c ELSE d FI) st st' \<Longrightarrow> beval st b \<Longrightarrow> ceval c st st'" using ceval.cases by auto
theorem if_invert2: "ceval (IF b THEN c ELSE d FI) st st' \<Longrightarrow> \<not>(beval st b) \<Longrightarrow> ceval d st st'" using ceval.cases by auto
theorem while_invert: "ceval (WHILE b DO c OD) st st' \<Longrightarrow> \<not>(beval st b) \<Longrightarrow> st = st'" using ceval.cases by auto
theorem while_invert2: "ceval (WHILE b DO c OD) st st' \<Longrightarrow> beval st b \<Longrightarrow> \<exists>st''. ceval c st st'' \<and> ceval (WHILE b DO c OD) st'' st'"
  using ceval.cases by blast
setup {* fold add_forward_prfstep [@{thm skip_invert}, @{thm assign_invert}, @{thm seq_invert},
  @{thm if_invert}, @{thm if_invert2}, @{thm while_invert}, @{thm while_invert2}] *}

setup {* add_rewrite_rule @{thm plus2_def} *}
theorem plus2_spec: "eval st X = n \<Longrightarrow> ceval plus2 st st' \<Longrightarrow> eval st' X = n + 2" by auto2

setup {* add_rewrite_rule @{thm XtimesYinZ_def} *}
theorem XtimesYinZ_spec: "eval st X = m \<and> eval st Y = n \<Longrightarrow> ceval XtimesYinZ st st' \<Longrightarrow> eval st' Z = m * n" by auto2

(* Induction rule. *)
setup {* add_prfstep_prop_induction @{thm ceval.induct} *}

(* ceval is deterministic. *)
theorem ceval_deterministic: "ceval c st st1 \<Longrightarrow> ceval c st st2 \<Longrightarrow> st1 = st2"
  by (tactic {* auto2s_tac @{context} (PROP_INDUCT ("ceval c st st1", [Arbitrary "st2"])) *})

setup {* add_rewrite_rule @{thm loop_def} *}
theorem loop_never_stops: "\<not>(ceval loop st st')"
  by (tactic {* auto2s_tac @{context} (PROP_INDUCT ("ceval loop st st'", [])) *})

end
