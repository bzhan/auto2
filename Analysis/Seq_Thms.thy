(* Definition of sequences, and some properties. *)

theory Seq_Thms
imports Rat_Thms
begin

subsection {* Sequences of numbers *}

datatype 'a seq = Seq "nat \<Rightarrow> 'a"

fun eval :: "'a seq \<Rightarrow> nat \<Rightarrow> 'a" ("_\<langle>_\<rangle>" [90]) where "(Seq f) \<langle>n\<rangle> = f n"
setup {* add_rewrite_rule @{thm eval.simps} *}

theorem seq_ext [backward]: "\<forall>n. s\<langle>n\<rangle> = t\<langle>n\<rangle> \<Longrightarrow> s = t" apply (cases s) apply (cases t) by auto

instantiation seq :: (comm_ring_1) comm_ring_1
begin

definition "(zero_seq::'a seq) = Seq (\<lambda>n. 0)"
definition "(one_seq::'a seq) = Seq (\<lambda>n. 1)"
definition "plus_seq (X::'a seq) Y = Seq (\<lambda>n. X\<langle>n\<rangle> + Y\<langle>n\<rangle>)"
definition "uminus_seq (X::'a seq) = Seq (\<lambda>n. -X\<langle>n\<rangle>)"
definition "minus_seq (X::'a seq) Y = Seq (\<lambda>n. X\<langle>n\<rangle> - Y\<langle>n\<rangle>)"
definition "times_seq (X::'a seq) Y = Seq (\<lambda>n. X\<langle>n\<rangle> * Y\<langle>n\<rangle>)"

theorem seq_evals:
  "0\<langle>n\<rangle> = 0"
  "1\<langle>n\<rangle> = 1"
  "(X + Y)\<langle>n\<rangle> = X\<langle>n\<rangle> + Y\<langle>n\<rangle>"
  "(-X)\<langle>n\<rangle> = -X\<langle>n\<rangle>"
  "(X - Y)\<langle>n\<rangle> = X\<langle>n\<rangle> - Y\<langle>n\<rangle>"
  "(X * Y)\<langle>n\<rangle> = X\<langle>n\<rangle> * Y\<langle>n\<rangle>"
  by (simp add: zero_seq_def one_seq_def plus_seq_def uminus_seq_def minus_seq_def times_seq_def)+

instance proof
  fix a b c :: "'a seq"
  show
    "a * b * c = a * (b * c)"
    "a * b = b * a"
    "a + b + c = a + (b + c)"
    "a + b = b + a"
    "a - b = a + (-b)"
    "-a + a = 0"
    "(a + b) * c = a * c + b * c"
    "(0::'a seq) \<noteq> 1"
  using seq_evals zero_seq_def plus_seq_def minus_seq_def uminus_seq_def times_seq_def
  by (clarsimp simp: algebra_simps)+
  show "1 * a = a" apply (rule seq_ext) using seq_evals by simp
  show "0 + a = a" apply (rule seq_ext) using seq_evals by simp
qed

end

setup {* fold add_rewrite_rule @{thms seq_evals} *}

definition seq_const :: "'a \<Rightarrow> 'a seq" ("{_}\<^sub>S") where
  "{a}\<^sub>S = Seq (\<lambda>n. a)"

theorem eval_seq_const [rewrite]: "{a}\<^sub>S\<langle>n\<rangle> = a" by (simp add: seq_const_def)

theorem eval_seq_const_zero [rewrite_bidir]: "{0}\<^sub>S = 0" by auto2
theorem eval_seq_const_one [rewrite_bidir]: "{1}\<^sub>S = 1" by auto2
theorem add_const_seqs [rewrite_bidir]: "{a}\<^sub>S + {b}\<^sub>S = {a + b}\<^sub>S" by auto2
theorem uminus_const_seqs [rewrite_bidir]: "-{a}\<^sub>S = {-a}\<^sub>S" by auto2
theorem minus_const_seqs [rewrite_back]: "{a}\<^sub>S - {b}\<^sub>S = {a - b}\<^sub>S" by auto2
theorem times_const_seqs [rewrite_bidir]: "{a}\<^sub>S * {b}\<^sub>S = {a * b}\<^sub>S" by auto2
theorem inverse_const_seqs [rewrite_back]: "{a::'a::linordered_field}\<^sub>S * {inverse b}\<^sub>S = {a / b}\<^sub>S" by auto2

definition seq_inverse :: "('a::inverse) seq \<Rightarrow> 'a seq" where
  "seq_inverse X = Seq (\<lambda>n. inverse (X\<langle>n\<rangle>))"
theorem eval_seq_inverse [rewrite]: "(seq_inverse (X::(('a::field) seq))) \<langle>n\<rangle> = 1 / X\<langle>n\<rangle>"
  by (simp add: divide_inverse seq_inverse_def)
theorem seq_inverse_const_seqs [rewrite]: "seq_inverse {a::('a::field)}\<^sub>S = {1 / a}\<^sub>S" by auto2

subsection {* Upper and lower bounded property *}

definition upper_bounded :: "('a::linorder) seq \<Rightarrow> bool" where
  "upper_bounded X = (\<exists>r. \<forall>n. X\<langle>n\<rangle> \<le> r)"
setup {* add_rewrite_rule @{thm upper_bounded_def} *}

definition lower_bounded :: "('a::linorder) seq \<Rightarrow> bool" where
  "lower_bounded X = (\<exists>r. \<forall>n. X\<langle>n\<rangle> \<ge> r)"
setup {* add_rewrite_rule @{thm lower_bounded_def} *}

theorem lower_bounded_is_neg_upper:
  "lower_bounded (X::('a::linordered_field) seq) \<longleftrightarrow> upper_bounded (-X)"
  by (tactic {* auto2s_tac @{context}
    (CASE "lower_bounded X" WITH (CHOOSE "r, \<forall>n. r \<le> X\<langle>n\<rangle>" THEN HAVE "\<forall>n. -r \<ge> (-X)\<langle>n\<rangle>") THEN
     CASE "upper_bounded (-X)" WITH (
      CHOOSE "r, \<forall>n. r \<ge> (-X)\<langle>n\<rangle>" THEN HAVE "\<forall>n. -r \<le> X\<langle>n\<rangle>" WITH HAVE "r \<ge> (-X)\<langle>n\<rangle>")) *})

setup {* fold del_prfstep_thm [@{thm upper_bounded_def}, @{thm lower_bounded_def}] *}
setup {* fold (add_resolve_prfstep o equiv_forward_th)
  [@{thm upper_bounded_def}, @{thm lower_bounded_def}, @{thm lower_bounded_is_neg_upper}] *}
setup {* fold (add_backward_prfstep o equiv_backward_th) [@{thm upper_bounded_def}, @{thm lower_bounded_def}] *}

subsection {* Monotone property *}

definition monotone_incr :: "('a::linorder) seq \<Rightarrow> bool" where
  "monotone_incr X = (\<forall>m. \<forall>n\<ge>m. X\<langle>n\<rangle> \<ge> X\<langle>m\<rangle>)"
setup {* add_rewrite_rule @{thm monotone_incr_def} *}

definition monotone_decr :: "('a::linorder) seq \<Rightarrow> bool" where
  "monotone_decr X = (\<forall>m. \<forall>n\<ge>m. X\<langle>n\<rangle> \<le> X\<langle>m\<rangle>)"
setup {* add_rewrite_rule @{thm monotone_decr_def} *}

theorem monotone_incrE [backward2]: "monotone_incr X \<Longrightarrow> n \<ge> m \<Longrightarrow> X\<langle>n\<rangle> \<ge> X\<langle>m\<rangle>" by auto2

theorem monotone_incrI [backward]: "\<forall>n. X\<langle>n+1\<rangle> \<ge> X\<langle>n\<rangle> \<Longrightarrow> monotone_incr X" by auto2

theorem monotone_decr_is_neg_incr:
  "monotone_decr (X::('a::linordered_field) seq) \<longleftrightarrow> monotone_incr (-X)" by auto2
setup {* add_resolve_prfstep (equiv_forward_th @{thm monotone_decr_is_neg_incr}) *}

theorem monotone_decrI [backward]:
  "\<forall>n. X\<langle>n+1\<rangle> \<le> X\<langle>n\<rangle> \<Longrightarrow> monotone_decr (X::('a::linordered_idom) seq)" by auto2

theorem monotone_decrE [backward2]: "monotone_decr X \<Longrightarrow> n \<ge> m \<Longrightarrow> X\<langle>n\<rangle> \<le> X\<langle>m\<rangle>" by auto2

setup {* fold del_prfstep_thm [@{thm monotone_incr_def}, @{thm monotone_decr_def}] *}

(* Definitions from existence. *)

theorem ex_seq: "\<forall>n. \<exists>x. P n x \<Longrightarrow> \<exists>S. \<forall>n. P n (S\<langle>n\<rangle>)"
  by (rule exI [where x="Seq (\<lambda>n. SOME x. P n x)"], simp add: someI_ex)

theorem ex_seq2 [backward]: "\<forall>n. \<exists>k. P n k \<Longrightarrow> \<exists>S. \<forall>n. \<exists>k. P n k \<and> S\<langle>n\<rangle> = F n k"
  apply (rule exI [where x="Seq (\<lambda>n. F n (SOME k. P n k))"])
  by (meson Seq_Thms.eval.simps someI_ex)

(* Inductive definitions. *)

fun ind_gen :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "ind_gen f I 0 = I"
| "ind_gen f I (Suc n) = f (ind_gen f I n)"

theorem ex_ind_seq: "\<exists>S. S\<langle>0\<rangle> = I \<and> (\<forall>n. S\<langle>1+n\<rangle> = f (S\<langle>n\<rangle>))"
  by (rule exI [where x="Seq (\<lambda>n. ind_gen f I n)"], simp)

theorem ex_mutual_ind_seq:
  "\<exists>S T. S\<langle>0\<rangle> = I \<and> T\<langle>0\<rangle> = J \<and> (\<forall>n. S\<langle>1+n\<rangle> = f (S\<langle>n\<rangle>) (T\<langle>n\<rangle>)) \<and> (\<forall>n. T\<langle>1+n\<rangle> = g (S\<langle>n\<rangle>) (T\<langle>n\<rangle>))"
proof -
  define H where "H = ind_gen (\<lambda>(x, y). (f x y, g x y)) (I, J)"
  show ?thesis
  apply (rule exI [where x="Seq (\<lambda>n. fst (H n))"])
  apply (rule exI [where x="Seq (\<lambda>n. snd (H n))"])
  by (simp add: H_def case_prod_beta')
qed

theorem convert_eval_Suc_n: "\<forall>(n::nat). f (1+n) = F n \<Longrightarrow> \<forall>n. n \<noteq> 0 \<longrightarrow> f n = F (n-1)"
  by (metis add.commute nat_minus_add_1)

definition monotone_pred :: "('a::linorder \<Rightarrow> bool) \<Rightarrow> bool"
  where "monotone_pred P = (\<forall>n. P n \<longrightarrow> (\<forall>m\<ge>n. P m))"
setup {* add_rewrite_rule @{thm monotone_pred_def} *}

theorem monotone_pred_ex:
  "monotone_pred P \<Longrightarrow> monotone_pred Q \<Longrightarrow> (\<exists>k. P k) \<and> (\<exists>k. Q k) \<Longrightarrow> \<exists>k. P k \<and> Q k" by auto2

theorem monotone_pred_ge: "monotone_pred (\<lambda>n. n \<ge> m)" by auto2
theorem monotone_pred_forall: "monotone_pred (\<lambda>n. \<forall>k\<ge>n. P k)" by auto2
theorem monotone_pred_forall2: "monotone_pred (\<lambda>n. \<forall>k\<ge>n. \<forall>m\<ge>n. P k m)" by auto2

ML_file "seq_steps.ML"

end
