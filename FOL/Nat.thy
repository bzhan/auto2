theory Nat
imports Ordinal Semiring
begin

section {* Axiom of infinity *}

axiomatization Inf :: "i" where
  infinity: "\<emptyset> \<in> Inf \<and> (\<forall>y\<in>Inf. succ(y) \<in> Inf)"
setup {* add_forward_prfstep_cond @{thm infinity} [with_term "Inf"] *}

lemma infinityD1 [typing2]: "\<emptyset> \<in> Inf" by auto2
lemma infinityD2 [typing]: "y \<in> Inf \<Longrightarrow> succ(y) \<in> Inf" by auto2
setup {* del_prfstep_thm @{thm infinity} *}

section {* Definition of natural numbers *}

definition Zero ("0") where [rewrite]: "0 = \<emptyset>"

(* Considered only applied to nat *)
definition Suc :: "i \<Rightarrow> i" where [rewrite]:
  "Suc(n) = succ(n)"
setup {* register_wellform_data ("Suc(n)", ["n \<in> nat"]) *}

definition nat :: i where [rewrite]:
  "nat = lfp(Inf, \<lambda>X. {0} \<union> {Suc(i). i \<in> X})"

lemma nat_bnd_mono [resolve]: "bnd_mono(Inf, \<lambda>X. {0} \<union> {Suc(i). i \<in> X})" by auto2

lemma nat_induct [script_induct]:
  "P(0) \<Longrightarrow> \<forall>x\<in>nat. P(x) \<longrightarrow> P(Suc(x)) \<Longrightarrow> n \<in> nat \<Longrightarrow> P(n)"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "n \<in> lfp(Inf, \<lambda>X. {0} \<union> {Suc(i). i \<in> X})" "P(n)") *})

lemma nat_unfold [rewrite]: "nat = {0} \<union> {Suc(x). x \<in> nat}" by auto2
lemma nat_case_split [backward2]: "x \<in> nat \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> \<exists>m\<in>nat. x = Suc(m)" by auto2
lemma nat_0I [typing]: "0 \<in> nat" by auto2
lemma nat_SucI [typing]: "n \<in> nat \<Longrightarrow> Suc(n) \<in> nat" by auto2
lemma nat_Suc_not_zero [resolve]: "0 \<noteq> Suc(n)" by auto2
lemma nat_Suc_inj [forward]: "Suc(a) = Suc(b) \<Longrightarrow> a = b" by auto2

setup {* fold del_prfstep_thm [@{thm nat_def}, @{thm nat_bnd_mono}, @{thm nat_unfold}] *}

abbreviation One ("1") where "1 \<equiv> Suc(0)"
abbreviation Two ("2") where "2 \<equiv> Suc(1)"
abbreviation Three ("3") where "3 \<equiv> Suc(2)"
abbreviation Four ("4") where "4 \<equiv> Suc(3)"
abbreviation Five ("5") where "5 \<equiv> Suc(4)"

section {* Defining functions on natural numbers *}

definition nat_case :: "[i, i \<Rightarrow> i, i] \<Rightarrow> i" where [rewrite]:
  "nat_case(a,b,k) = (THE y. k = 0 \<and> y = a \<or> (\<exists>x. k = Suc(x) \<and> y = b(x)))"
setup {* register_wellform_data ("nat_case(a,b,k)", ["k \<in> nat"]) *}

lemma nat_case_0 [rewrite]: "nat_case(a,b,0) = a" by auto2
lemma nat_case_Suc [rewrite]: "nat_case(a,b,Suc(m)) = b(m)" by auto2
setup {* del_prfstep_thm @{thm nat_case_def} *}

lemma nat_case_type [backward]:
  "k \<in> nat \<Longrightarrow> a \<in> T \<Longrightarrow> \<forall>m\<in>nat. b(m) \<in> T \<Longrightarrow> nat_case(a,b,k) \<in> T"
  by (tactic {* auto2s_tac @{context} (CHOOSE "k'\<in>nat, k = Suc(k')") *})

definition nat_rec :: "[i, [i, i] \<Rightarrow> i, i] \<Rightarrow> i" where [rewrite]:
  "nat_rec(a,b,k) = wfrec(mem_rel(nat), \<lambda>n f. nat_case(a, \<lambda>m. b(m, f`m), n), k)"
setup {* register_wellform_data ("nat_rec(a,b,k)", ["k \<in> nat"]) *}

lemma nat_rec_0 [rewrite]: "nat_rec(a,b,0) = a" by auto2
lemma nat_rec_Suc [rewrite]: "m \<in> nat \<Longrightarrow> nat_rec(a,b,Suc(m)) = b(m, nat_rec(a,b,m))"
  by (tactic {* auto2s_tac @{context} (HAVE "m \<in> rel_vsection(mem_rel(nat),Suc(m))") *})
setup {* del_prfstep_thm @{thm nat_rec_def} *}

lemma nat_rec_type [backward]:
  "k \<in> nat \<Longrightarrow> a \<in> T \<Longrightarrow> \<forall>m\<in>nat. \<forall>p\<in>T. b(m,p)\<in>T \<Longrightarrow> nat_rec(a,b,k) \<in> T"
  by (tactic {* auto2s_tac @{context} (INDUCT_ON "k \<in> nat" "nat_rec(a,b,k) \<in> T") *})

setup {* fold del_prfstep_thm [@{thm Zero_def}, @{thm Suc_def}] *}

section {* Natural numbers as an ordered semiring *}

(* Recursion on x:
    nat_add(0,y) = y
  | nat_add(Suc(x),y) = Suc(nat_add(x,y))
*)
definition nat_add :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "nat_add(x,y) = nat_rec(y, \<lambda>_ p. Suc(p), x)"
setup {* register_wellform_data ("nat_add(x,y)", ["x \<in> nat", "y \<in> nat"]) *}
  
lemma nat_add_0 [rewrite]: "nat_add(0,x) = x" by auto2
lemma nat_add_Suc [rewrite]: "x \<in> nat \<Longrightarrow> nat_add(Suc(x),y) = Suc(nat_add(x,y))" by auto2
lemma nat_add_type [typing]: "x \<in> nat \<Longrightarrow> y \<in> nat \<Longrightarrow> nat_add(x,y) \<in> nat" by auto2
setup {* del_prfstep_thm @{thm nat_add_def} *}

(* Recursion on x:
    nat_mult(0,y) = 0
  | nat_mult(Suc(x),y) = y + nat_mult(x,y)
*)
definition nat_mult :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "nat_mult(x,y) = nat_rec(0, \<lambda>_ p. nat_add(y,p), x)"
setup {* register_wellform_data ("nat_mult(x,y)", ["x \<in> nat", "y \<in> nat"]) *}
  
lemma nat_mult_0 [rewrite]: "nat_mult(0,x) = 0" by auto2
lemma nat_mult_Suc [rewrite]: "x \<in> nat \<Longrightarrow> nat_mult(Suc(x),y) = nat_add(y,nat_mult(x,y))" by auto2
lemma nat_mult_type [typing]: "x \<in> nat \<Longrightarrow> y \<in> nat \<Longrightarrow> nat_mult(x,y) \<in> nat" by auto2
setup {* del_prfstep_thm @{thm nat_mult_def} *}

definition nat_le :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "nat_le(x,y) \<longleftrightarrow> (\<exists>p\<in>nat. y = nat_add(x,p))"

lemma nat_leI: "x \<in> nat \<Longrightarrow> p \<in> nat \<Longrightarrow> nat_le(x,nat_add(x,p))" by auto2

definition nat_ring :: i  ("\<nat>") where [rewrite]:
  "\<nat> = OrdRing(nat, 0, \<lambda>x y. nat_add(x,y), 1, \<lambda>x y. nat_mult(x,y), \<lambda>x y. nat_le(x,y))"

lemma nat_ring_is_ord_ring_raw [forward]: "ord_ring_form(\<nat>)" by auto2
lemma nat_carrier [rewrite_bidir]: "carrier(\<nat>) = nat" by auto2
lemma nat_evals:
  "\<zero>\<^sub>\<nat> = 0"
  "\<one>\<^sub>\<nat> = 1"
  "x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> x +\<^sub>\<nat> y = nat_add(x,y)"
  "x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> x *\<^sub>\<nat> y = nat_mult(x,y)"
  "x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> x \<le>\<^sub>\<nat> y \<longleftrightarrow> nat_le(x,y)" by auto2+
setup {* fold add_rewrite_rule @{thms nat_evals(1,2)} *}
setup {* del_prfstep_thm @{thm nat_ring_def} *}

section {* Addition on natural numbers *}

setup {* add_rewrite_rule @{thm nat_evals(3)} *}
lemma nat_add_0_left [rewrite]: "x \<in>. \<nat> \<Longrightarrow> 0 +\<^sub>\<nat> x = x" by auto2
lemma nat_add_Suc' [rewrite]: "x \<in> nat \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> Suc(x) +\<^sub>\<nat> y = Suc(x +\<^sub>\<nat> y)" by auto2
setup {* fold del_prfstep_thm [@{thm nat_add_0}, @{thm nat_add_Suc}, @{thm nat_add_type}, @{thm nat_evals(3)}] *}

lemma nat_add_0_right [rewrite]: "x \<in>. \<nat> \<Longrightarrow> x +\<^sub>\<nat> 0 = x"
  by (tactic {* auto2s_tac @{context} (INDUCT_ON "x \<in> nat" "x +\<^sub>\<nat> 0 = x") *})

lemma nat_add_assoc [rewrite_bidir]:
  "x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> z \<in>. \<nat> \<Longrightarrow> (x +\<^sub>\<nat> y) +\<^sub>\<nat> z = x +\<^sub>\<nat> (y +\<^sub>\<nat> z)"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "x \<in> nat" "(x +\<^sub>\<nat> y) +\<^sub>\<nat> z = x +\<^sub>\<nat> (y +\<^sub>\<nat> z)") *})

lemma nat_add_1 [rewrite_bidir]:
  "x \<in>. \<nat> \<Longrightarrow> Suc(x) = x +\<^sub>\<nat> 1"
  by (tactic {* auto2s_tac @{context} (INDUCT_ON "x \<in> nat" "Suc(x) = x +\<^sub>\<nat> 1") *})

lemma nat_add_comm [rewrite]: "x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> x +\<^sub>\<nat> y = y +\<^sub>\<nat> x"
  by (tactic {* auto2s_tac @{context} (INDUCT_ON "x \<in> nat" "x +\<^sub>\<nat> y = y +\<^sub>\<nat> x") *})

section {* Multiplication on natural numbers *}

setup {* fold add_rewrite_rule @{thms nat_evals(3,4)} *}
lemma nat_mult_0_left [rewrite]: "x \<in>. \<nat> \<Longrightarrow> 0 *\<^sub>\<nat> x = 0" by auto2
lemma nat_mult_Suc' [rewrite]: "x \<in> nat \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> Suc(x) *\<^sub>\<nat> y = y +\<^sub>\<nat> (x *\<^sub>\<nat> y)" by auto2
setup {* fold del_prfstep_thm [@{thm nat_mult_0}, @{thm nat_mult_Suc}, @{thm nat_mult_type}] *}
setup {* fold del_prfstep_thm @{thms nat_evals(3,4)} *}

lemma nat_mult_0_right [rewrite]: "x \<in>. \<nat> \<Longrightarrow> x *\<^sub>\<nat> 0 = 0"
  by (tactic {* auto2s_tac @{context} (INDUCT_ON "x \<in> nat" "x *\<^sub>\<nat> 0 = 0") *})

lemma nat_mult_1 [rewrite]: "x \<in>. \<nat> \<Longrightarrow> 1 *\<^sub>\<nat> x = x" by auto2
lemma nat_mult_1_right [rewrite]: "x \<in>. \<nat> \<Longrightarrow> x *\<^sub>\<nat> 1 = x"
  by (tactic {* auto2s_tac @{context} (INDUCT_ON "x \<in> nat" "x *\<^sub>\<nat> 1 = x") *})

lemma nat_distrib_l [rewrite]:
  "x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> z \<in>. \<nat> \<Longrightarrow> x *\<^sub>\<nat> (y +\<^sub>\<nat> z) = x *\<^sub>\<nat> y +\<^sub>\<nat> x *\<^sub>\<nat> z"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "x \<in> nat" "x *\<^sub>\<nat> (y +\<^sub>\<nat> z) = x *\<^sub>\<nat> y +\<^sub>\<nat> x *\<^sub>\<nat> z") *})
  
lemma nat_distrib_r [rewrite]:
  "x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> z \<in>. \<nat> \<Longrightarrow> (x +\<^sub>\<nat> y) *\<^sub>\<nat> z = x *\<^sub>\<nat> z +\<^sub>\<nat> y *\<^sub>\<nat> z"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "x \<in> nat" "(x +\<^sub>\<nat> y) *\<^sub>\<nat> z = x *\<^sub>\<nat> z +\<^sub>\<nat> y *\<^sub>\<nat> z") *})

lemma nat_mult_assoc [rewrite_bidir]:
  "x \<in> nat \<Longrightarrow> y \<in> nat \<Longrightarrow> z \<in> nat \<Longrightarrow> (x *\<^sub>\<nat> y) *\<^sub>\<nat> z = x *\<^sub>\<nat> (y *\<^sub>\<nat> z)"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "x \<in> nat" "(x *\<^sub>\<nat> y) *\<^sub>\<nat> z = x *\<^sub>\<nat> (y *\<^sub>\<nat> z)") *})

lemma nat_mult_Suc_right [rewrite]:
  "x \<in> nat \<Longrightarrow> y \<in> nat \<Longrightarrow> x *\<^sub>\<nat> Suc(y) = x +\<^sub>\<nat> (x *\<^sub>\<nat> y)"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "x \<in> nat" "x *\<^sub>\<nat> Suc(y) = x +\<^sub>\<nat> (x *\<^sub>\<nat> y)") *})

lemma nat_mult_comm [rewrite]:
  "x \<in> nat \<Longrightarrow> y \<in> nat \<Longrightarrow> x *\<^sub>\<nat> y = y *\<^sub>\<nat> x"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "x \<in> nat" "x *\<^sub>\<nat> y = y *\<^sub>\<nat> x") *})

lemma nat_is_semiring [forward]: "is_semiring(\<nat>)" by auto2

setup {* fold del_prfstep_thm [@{thm nat_add_assoc}, @{thm nat_add_comm}] *}
setup {* fold del_prfstep_thm [@{thm nat_mult_assoc}, @{thm nat_mult_comm}] *}
setup {* fold del_prfstep_thm [@{thm nat_distrib_l}, @{thm nat_distrib_r}] *}

lemma nat_add_cancel_left [forward]:
  "a \<in>. \<nat> \<Longrightarrow> b \<in>. \<nat> \<Longrightarrow> c \<in>. \<nat> \<Longrightarrow> c +\<^sub>\<nat> a = c +\<^sub>\<nat> b \<Longrightarrow> a = b"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "c \<in> nat" "c +\<^sub>\<nat> a = c +\<^sub>\<nat> b \<longrightarrow> a = b") *})

lemma nat_add_cancel_right [forward]:
  "a \<in>. \<nat> \<Longrightarrow> b \<in>. \<nat> \<Longrightarrow> c \<in>. \<nat> \<Longrightarrow> a +\<^sub>\<nat> c = b +\<^sub>\<nat> c \<Longrightarrow> a = b"
  by (tactic {* auto2s_tac @{context} (
    HAVE "a +\<^sub>\<nat> c = c +\<^sub>\<nat> a" THEN HAVE "b +\<^sub>\<nat> c = c +\<^sub>\<nat> b") *})

lemma nat_add_right_eq_zero [forward]:
  "x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> x +\<^sub>\<nat> y = x \<Longrightarrow> y = 0"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "x \<in> nat" "x +\<^sub>\<nat> y = x \<longrightarrow> y = 0") *})

lemma nat_add_left_eq_zero [forward]:
  "x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> x +\<^sub>\<nat> y = y \<Longrightarrow> x = 0"
  by (tactic {* auto2s_tac @{context} (HAVE "x +\<^sub>\<nat> y = y +\<^sub>\<nat> x") *})

lemma nat_add_is_zero [forward]:
  "x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> x +\<^sub>\<nat> y = 0 \<Longrightarrow> x = 0 \<and> y = 0"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "x \<in> nat" "x +\<^sub>\<nat> y = 0 \<longrightarrow> x = 0") *})

lemma nat_mult_nonzero [forward]:
  "x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> x *\<^sub>\<nat> y = 0 \<Longrightarrow> x = 0 \<or> y = 0"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "y \<in> nat" "y \<noteq> 0 \<longrightarrow> x *\<^sub>\<nat> y \<noteq> 0") *})
setup {* del_prfstep_thm @{thm nat_mult_Suc_right} *}

section {* Ordering on natural numbers *}

setup {* fold add_rewrite_rule @{thms nat_evals(3,5)} *}
lemma nat_leD [backward]: "x \<le>\<^sub>\<nat> y \<Longrightarrow> \<exists>p\<in>.\<nat>. y = x +\<^sub>\<nat> p" by auto2
lemma nat_leI_right [resolve]: "x \<in>. \<nat> \<Longrightarrow> p \<in>. \<nat> \<Longrightarrow> x \<le>\<^sub>\<nat> x +\<^sub>\<nat> p" by auto2
setup {* del_prfstep_thm @{thm nat_le_def} *}
setup {* fold del_prfstep_thm @{thms nat_evals(3,5)} *}

lemma nat_leI_left [resolve]: "x \<in>. \<nat> \<Longrightarrow> k \<in>. \<nat> \<Longrightarrow> k \<le>\<^sub>\<nat> x +\<^sub>\<nat> k"
  by (tactic {* auto2s_tac @{context} (HAVE "x +\<^sub>\<nat> k = k +\<^sub>\<nat> x") *})

lemma nat_le_refl [resolve]: "x \<in>. \<nat> \<Longrightarrow> x \<le>\<^sub>\<nat> x"
  by (tactic {* auto2s_tac @{context} (HAVE "x = x +\<^sub>\<nat> 0") *})

lemma nat_le_antisym [forward]:
  "x \<le>\<^sub>\<nat> y \<Longrightarrow> y \<le>\<^sub>\<nat> x \<Longrightarrow> x = y"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "p\<in>nat, y = x +\<^sub>\<nat> p" THEN CHOOSE "q\<in>nat, x = y +\<^sub>\<nat> q" THEN
    HAVE "(x +\<^sub>\<nat> p) +\<^sub>\<nat> q = x +\<^sub>\<nat> (p +\<^sub>\<nat> q)") *})

lemma nat_le_trans [forward]:
  "x \<le>\<^sub>\<nat> y \<Longrightarrow> y \<le>\<^sub>\<nat> z \<Longrightarrow> x \<le>\<^sub>\<nat> z"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "p\<in>nat, y = x +\<^sub>\<nat> p" THEN CHOOSE "q\<in>nat, z = y +\<^sub>\<nat> q" THEN
    HAVE "(x +\<^sub>\<nat> p) +\<^sub>\<nat> q = x +\<^sub>\<nat> (p +\<^sub>\<nat> q)") *})
      
lemma nat_is_order [forward]: "order(\<nat>)" by auto2
setup {* fold del_prfstep_thm [@{thm nat_le_refl}, @{thm nat_le_antisym}, @{thm nat_le_trans}] *}

lemma nat_less_exI [backward]:
  "x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> x <\<^sub>\<nat> x +\<^sub>\<nat> y"
  by (tactic {* auto2s_tac @{context} (HAVE "x \<noteq> x +\<^sub>\<nat> y") *})

lemma nat_less_ex [backward]: "x <\<^sub>\<nat> y \<Longrightarrow> \<exists>p\<in>nat. p \<noteq> 0 \<and> y = x +\<^sub>\<nat> p"
  by (tactic {* auto2s_tac @{context} (CHOOSE "p\<in>nat, y = x +\<^sub>\<nat> p") *})

lemma nat_zero_le [resolve]: "x \<in>. \<nat> \<Longrightarrow> 0 \<le>\<^sub>\<nat> x"
  by (tactic {* auto2s_tac @{context} (HAVE "x = 0 +\<^sub>\<nat> x") *})

lemma nat_le_Suc [resolve]: "x \<in>. \<nat> \<Longrightarrow> x <\<^sub>\<nat> Suc(x)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "x \<noteq> Suc(x)" WITH HAVE "x = x +\<^sub>\<nat> 0") *})

lemma nat_le_to_less_Suc [resolve]: "x \<le>\<^sub>\<nat> y \<Longrightarrow> x \<le>\<^sub>\<nat> Suc(y)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "p\<in>nat, y = x +\<^sub>\<nat> p" THEN HAVE "(x +\<^sub>\<nat> p) +\<^sub>\<nat> 1 = x +\<^sub>\<nat> (p +\<^sub>\<nat> 1)") *})

lemma nat_less_to_Suc_le [resolve]: "x <\<^sub>\<nat> y \<Longrightarrow> Suc(x) \<le>\<^sub>\<nat> y"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "p\<in>nat, p \<noteq> 0 \<and> y = x +\<^sub>\<nat> p" THEN
    CHOOSE "p'\<in>nat, p = Suc(p')" THEN
    HAVE "x +\<^sub>\<nat> (p' +\<^sub>\<nat> 1) = (x +\<^sub>\<nat> 1) +\<^sub>\<nat> p'") *})

lemma nat_le_to_Suc_le [backward2]: "x \<le>\<^sub>\<nat> y \<Longrightarrow> x \<noteq> y \<Longrightarrow> Suc(x) \<le>\<^sub>\<nat> y"
  by (tactic {* auto2s_tac @{context} (HAVE "x <\<^sub>\<nat> y") *})

lemma nat_comparable [resolve]: "x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> \<not>x \<le>\<^sub>\<nat> y \<Longrightarrow> y \<le>\<^sub>\<nat> x"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "x \<in> nat" "x \<le>\<^sub>\<nat> y \<or> y \<le>\<^sub>\<nat> x") *})

lemma nat_is_linorder [forward]: "linorder(\<nat>)" by auto2
setup {* del_prfstep_thm @{thm nat_comparable} *}

lemma nat_le_zero [forward]: "n \<in>. \<nat> \<Longrightarrow> n \<le>\<^sub>\<nat> 0 \<Longrightarrow> n = 0" by auto2

lemma nat_less_one [forward]: "n \<in>. \<nat> \<Longrightarrow> n <\<^sub>\<nat> 1 \<Longrightarrow> n = 0"
  by (tactic {* auto2s_tac @{context} (HAVE "n \<le>\<^sub>\<nat> 0") *})

lemma nat_add_ordered_right [rewrite_back]:
  "x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> z \<in>. \<nat> \<Longrightarrow> x \<le>\<^sub>\<nat> y \<longleftrightarrow> x +\<^sub>\<nat> z \<le>\<^sub>\<nat> y +\<^sub>\<nat> z"
  by (tactic {* auto2s_tac @{context} (
    CASE "x \<le>\<^sub>\<nat> y" WITH (
      CHOOSE "p\<in>nat, y = x +\<^sub>\<nat> p" THEN
      HAVE "(x +\<^sub>\<nat> p) +\<^sub>\<nat> z = (x +\<^sub>\<nat> z) +\<^sub>\<nat> p") THEN
    CASE "x +\<^sub>\<nat> z \<le>\<^sub>\<nat> y +\<^sub>\<nat> z" WITH (
      CHOOSE "p\<in>nat, y +\<^sub>\<nat> z = x +\<^sub>\<nat> z +\<^sub>\<nat> p" THEN
      HAVE "x +\<^sub>\<nat> z +\<^sub>\<nat> p = x +\<^sub>\<nat> p +\<^sub>\<nat> z")) *})

lemma nat_add_ordered_left [rewrite_back]:
  "x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> z \<in>. \<nat> \<Longrightarrow> y \<le>\<^sub>\<nat> z \<longleftrightarrow> x +\<^sub>\<nat> y \<le>\<^sub>\<nat> x +\<^sub>\<nat> z"
  by (tactic {* auto2s_tac @{context} (
    HAVE "x +\<^sub>\<nat> y = y +\<^sub>\<nat> x" THEN HAVE "x +\<^sub>\<nat> z = z +\<^sub>\<nat> x") *})

lemma nat_mult_ordered_left [backward]:
  "z \<in>. \<nat> \<Longrightarrow> x \<le>\<^sub>\<nat> y \<Longrightarrow> z *\<^sub>\<nat> x \<le>\<^sub>\<nat> z *\<^sub>\<nat> y"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "p\<in>nat, y = x +\<^sub>\<nat> p" THEN
    HAVE "z *\<^sub>\<nat> (x +\<^sub>\<nat> p) = z *\<^sub>\<nat> x +\<^sub>\<nat> z *\<^sub>\<nat> p") *})

lemma nat_is_ord_semiring [forward]: "is_ord_semiring(\<nat>)" by auto2

lemma nat_add_strict_ordered_right [rewrite_back]:
  "x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> z \<in>. \<nat> \<Longrightarrow> x <\<^sub>\<nat> y \<longleftrightarrow> x +\<^sub>\<nat> z <\<^sub>\<nat> y +\<^sub>\<nat> z" by auto2

lemma nat_add_strict_ordered_left [rewrite_back]:
  "x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> z \<in>. \<nat> \<Longrightarrow> y <\<^sub>\<nat> z \<longleftrightarrow> x +\<^sub>\<nat> y <\<^sub>\<nat> x +\<^sub>\<nat> z" by auto2

lemma nat_add_order_mix2 [backward1]:
  "p \<le>\<^sub>\<nat> q \<Longrightarrow> r <\<^sub>\<nat> s \<Longrightarrow> p +\<^sub>\<nat> r <\<^sub>\<nat> q +\<^sub>\<nat> s"
  by (tactic {* auto2s_tac @{context} (HAVE "p +\<^sub>\<nat> r <\<^sub>\<nat> p +\<^sub>\<nat> s") *})

lemma nat_add_order_mix3 [backward1]:
  "p <\<^sub>\<nat> q \<Longrightarrow> r \<le>\<^sub>\<nat> s \<Longrightarrow> p +\<^sub>\<nat> r <\<^sub>\<nat> q +\<^sub>\<nat> s"
  by (tactic {* auto2s_tac @{context} (HAVE "p +\<^sub>\<nat> r \<le>\<^sub>\<nat> p +\<^sub>\<nat> s") *})

lemma nat_mult_less_right [backward2]:
  "z \<in>. \<nat> \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> x <\<^sub>\<nat> y \<Longrightarrow> x *\<^sub>\<nat> z <\<^sub>\<nat> y *\<^sub>\<nat> z"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "p\<in>nat, p \<noteq> 0 \<and> y = x +\<^sub>\<nat> p" THEN
    HAVE "(x +\<^sub>\<nat> p) *\<^sub>\<nat> z = x *\<^sub>\<nat> z +\<^sub>\<nat> p *\<^sub>\<nat> z") *})

lemma nat_mult_less_left [backward2]:
  "z \<in>. \<nat> \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> x <\<^sub>\<nat> y \<Longrightarrow> z *\<^sub>\<nat> x <\<^sub>\<nat> z *\<^sub>\<nat> y"
  by (tactic {* auto2s_tac @{context} (
    HAVE "z *\<^sub>\<nat> x = x *\<^sub>\<nat> z" THEN HAVE "z *\<^sub>\<nat> y = y *\<^sub>\<nat> z") *})

lemma nat_mult_cancel_left [forward]:
  "x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> z \<in>. \<nat> \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> z *\<^sub>\<nat> x = z *\<^sub>\<nat> y \<Longrightarrow> x = y"
  by (tactic {* auto2s_tac @{context} (
    CASE "x <\<^sub>\<nat> y" WITH HAVE "z *\<^sub>\<nat> x <\<^sub>\<nat> z *\<^sub>\<nat> y" THEN
    CASE "x >\<^sub>\<nat> y" WITH HAVE "z *\<^sub>\<nat> x >\<^sub>\<nat> z *\<^sub>\<nat> y") *})

lemma nat_mult_cancel_right [forward]:
  "x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> z \<in>. \<nat> \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> x *\<^sub>\<nat> z = y *\<^sub>\<nat> z \<Longrightarrow> x = y"
  by (tactic {* auto2s_tac @{context} (
    HAVE "x *\<^sub>\<nat> z = z *\<^sub>\<nat> x" THEN HAVE "y *\<^sub>\<nat> z = z *\<^sub>\<nat> y") *})

section {* Subtraction in natural numbers *}

setup {* add_backward2_prfstep @{thm minusI} *}
lemma nat_minusI [resolve]:
  "y \<in>. \<nat> \<Longrightarrow> p \<in>. \<nat> \<Longrightarrow> p +\<^sub>\<nat> y = x \<Longrightarrow> x -\<^sub>\<nat> y = p" by auto2
setup {* del_prfstep_thm @{thm minusI} *}

lemma nat_minus_prop:
  "x \<in>. \<nat> \<Longrightarrow> y \<in>. \<nat> \<Longrightarrow> x \<ge>\<^sub>\<nat> y \<Longrightarrow> x -\<^sub>\<nat> y \<in>. \<nat> \<and> (x -\<^sub>\<nat> y) +\<^sub>\<nat> y = x"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "p\<in>.\<nat>, x = y +\<^sub>\<nat> p" THEN HAVE "x = p +\<^sub>\<nat> y" THEN
    HAVE "x -\<^sub>\<nat> y = p") *})
setup {* add_typing_rule (conj_left_th @{thm nat_minus_prop}) *}
setup {* add_rewrite_rule (conj_right_th @{thm nat_minus_prop}) *}

ML_file "nat_arith.ML"

section {* Replace lemmas about Suc(x) with x + 1 *}

setup {* fold del_prfstep_thm [@{thm nat_Suc_inj}] *}

lemma nat_Suc_not_zero' [resolve]: "n \<in>. \<nat> \<Longrightarrow> 0 \<noteq> n +\<^sub>\<nat> 1" by auto2
lemma nat_case_split' [backward2]: "x \<in> nat \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> \<exists>m\<in>.\<nat>. x = m +\<^sub>\<nat> 1"
  by (tactic {* auto2s_tac @{context} (CHOOSE "m\<in>.\<nat>, x = Suc(m)") *})
lemma nat_case_Suc' [rewrite]: "m \<in>. \<nat> \<Longrightarrow> nat_case(a,b,m +\<^sub>\<nat> 1) = b(m)" by auto2
lemma nat_rec_Suc' [rewrite]: "m \<in>. \<nat> \<Longrightarrow> nat_rec(a,b,m +\<^sub>\<nat> 1) = b(m, nat_rec(a,b,m))" by auto2
lemma nat_le_Suc' [resolve]: "x \<in>. \<nat> \<Longrightarrow> x <\<^sub>\<nat> x +\<^sub>\<nat> 1" by auto2
lemma nat_le_to_less_Suc' [resolve]: "x \<le>\<^sub>\<nat> y \<Longrightarrow> x \<le>\<^sub>\<nat> y +\<^sub>\<nat> 1" by auto2
lemma nat_less_to_Suc_le' [resolve]: "x <\<^sub>\<nat> y \<Longrightarrow> x +\<^sub>\<nat> 1 \<le>\<^sub>\<nat> y" by auto2
lemma nat_le_to_Suc_le' [backward2]: "x \<le>\<^sub>\<nat> y \<Longrightarrow> x \<noteq> y \<Longrightarrow> x +\<^sub>\<nat> 1 \<le>\<^sub>\<nat> y" by auto2
setup {* fold del_prfstep_thm [@{thm nat_Suc_not_zero}, @{thm nat_case_split},
  @{thm nat_case_Suc}, @{thm nat_rec_Suc}, @{thm nat_add_Suc'}, @{thm nat_mult_Suc'},
  @{thm nat_le_Suc}, @{thm nat_le_to_less_Suc},
  @{thm nat_less_to_Suc_le}, @{thm nat_le_to_Suc_le}] *}

lemma nat_induct' [script_induct]:
  "P(0) \<Longrightarrow> \<forall>x\<in>nat. P(x) \<longrightarrow> P(x +\<^sub>\<nat> 1) \<Longrightarrow> n \<in> nat \<Longrightarrow> P(n)"
  by (tactic {* auto2s_tac @{context} (INDUCT_ON "n \<in> nat" "P(n)") *})
setup {* delete_script_induct_data @{thm nat_induct} *}
setup {* del_prfstep_thm @{thm nat_add_1} *}

section {* Other induction principles *}

lemma nat_induct_k [script_induct]:
  "P(k) \<Longrightarrow> \<forall>x\<in>nat. x \<ge>\<^sub>\<nat> k \<longrightarrow> P(x) \<longrightarrow> P(x +\<^sub>\<nat> 1) \<Longrightarrow> n \<ge>\<^sub>\<nat> k \<Longrightarrow> P(n)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>m\<in>nat. P(m +\<^sub>\<nat> k)" WITH
      INDUCT_ON "m \<in> nat" "P(m +\<^sub>\<nat> k)" THEN
    HAVE "n = (n -\<^sub>\<nat> k) +\<^sub>\<nat> k") *})

lemma nat_induct_less:
  "\<forall>n\<in>nat. (\<forall>m. m <\<^sub>\<nat> n \<longrightarrow> P(m)) \<longrightarrow> P(n) \<Longrightarrow> n \<in> nat \<Longrightarrow> P(n)"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "n \<in> nat" "\<forall>m. m \<le>\<^sub>\<nat> n \<longrightarrow> P(m)") *})

lemma nat_double_induct [script_induct]:
  "P(0,0) \<Longrightarrow> \<forall>x\<in>nat. \<forall>y\<in>nat. P(x,y) \<longrightarrow> P(x,y +\<^sub>\<nat> 1) \<Longrightarrow>
   \<forall>x\<in>nat. \<forall>y\<in>nat. P(x,y) \<longrightarrow> P(x +\<^sub>\<nat> 1,y) \<Longrightarrow> m \<in> nat \<and> n \<in> nat \<Longrightarrow> P(m,n)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x\<in>nat. P(0,x)" WITH INDUCT_ON "x \<in> nat" "P(0,x)" THEN
    INDUCT_ON "m \<in> nat" "\<forall>n'\<in>nat. P(m,n')") *})

section {* Definition of power *}
  
definition power :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "power(R,b,e) = nat_rec(\<one>\<^sub>R, \<lambda>_ p. p *\<^sub>R b, e)"
setup {* register_wellform_data ("power(R,b,e)", ["b \<in>. R", "e \<in> nat"]) *}
abbreviation power_notation ("(_/ ^\<^sub>_ _)" [90,90,91] 90) where "x ^\<^sub>R y \<equiv> power(R,x,y)"
  
lemma power_0 [rewrite]: "b ^\<^sub>R 0 = \<one>\<^sub>R" by auto2
lemma power_Suc [rewrite]: "e \<in> nat \<Longrightarrow> b ^\<^sub>R (e +\<^sub>\<nat> 1) = (b ^\<^sub>R e) *\<^sub>R b" by auto2
lemma power_type [typing]: "is_group_raw(R) \<Longrightarrow> e \<in> nat \<Longrightarrow> b \<in>. R \<Longrightarrow> b ^\<^sub>R e \<in>. R" by auto2
setup {* del_prfstep_thm @{thm power_def} *}

section {* n-fold composition *}
  
(* nfold(f,0,x) = x
 | nfold(f,Suc(n),x) = f`(nfold(f,n,x))
*)
definition nfold :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "nfold(f,n,x) = nat_rec(x, \<lambda>_ p. f`p, n)"
setup {* register_wellform_data ("nfold(f,n,x)", ["n \<in> nat", "x \<in> source(f)", "source(f) = target(f)"]) *}
  
lemma nfold_0 [rewrite]: "nfold(f,0,x) = x" by auto2
lemma nfold_Suc [rewrite]: "n \<in> nat \<Longrightarrow> nfold(f,n +\<^sub>\<nat> 1,x) = f`(nfold(f,n,x))" by auto2
lemma nfold_type [typing]:
  "is_function(f) \<Longrightarrow> source(f) = target(f) \<Longrightarrow> x \<in> source(f) \<Longrightarrow> n \<in> nat \<Longrightarrow> nfold(f,n,x) \<in> source(f)" by auto2
setup {* del_prfstep_thm @{thm nfold_def} *}

end
