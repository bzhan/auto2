theory Ordinal
imports Wfrec
begin

section {* Axiom of foundation *}

axiomatization where
  foundation [backward]: "x \<noteq> \<emptyset> \<Longrightarrow> \<exists>y\<in>x. y \<inter> x = \<emptyset>"

lemma no_mem_cycle1 [resolve]: "a \<notin> a"
@proof
  @obtain "x\<in>{a}" where "x \<inter> {a} = \<emptyset>"
@qed

lemma no_mem_cycle2 [resolve]: "x \<in> y \<Longrightarrow> y \<notin> x"
@proof
  @obtain "a \<in> {x,y}" where "a \<inter> {x,y} = \<emptyset>"
@qed

section {* Membership relation is well-founded *}

definition mem_rel :: "i \<Rightarrow> i" where [rewrite]:
  "mem_rel(A) = Order(A, \<lambda>x y. x \<in> y)"

lemma mem_rel_is_rel [typing]: "mem_rel(A) \<in> raworder_space(A)" by auto2
lemma mem_rel_eval [rewrite]:
  "R = mem_rel(A) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x \<le>\<^sub>R y \<longleftrightarrow> x \<in> y" by auto2
setup {* del_prfstep_thm @{thm mem_rel_def} *}

lemma wf_mem_rel [forward]: "wf(mem_rel(A))"
@proof
  @have "\<forall>B\<in>Pow(A). B \<noteq> \<emptyset> \<longrightarrow> (\<exists>x\<in>B. ord_minimal(mem_rel(A),B,x))" @with
    @obtain "x\<in>B" where "x \<inter> B = \<emptyset>" @end
@qed

section {* Definition of ordinals *}

definition trans_set :: "i \<Rightarrow> o" where [rewrite]:
  "trans_set(i) \<longleftrightarrow> (\<forall>x\<in>i. x \<subseteq> i)"
setup {* add_property_const @{term trans_set} *}

definition ord :: "i \<Rightarrow> o" where [rewrite]:
  "ord(i) \<longleftrightarrow> (trans_set(i) \<and> (\<forall>x\<in>i. trans_set(x)))"
setup {* add_property_const @{term ord} *}

lemma ordI [backward]: "trans_set(i) \<and> (\<forall>j\<in>i. trans_set(j)) \<Longrightarrow> ord(i)" by auto2

lemma ord_mem_is_ord [forward]: "ord(i) \<Longrightarrow> j \<in> i \<Longrightarrow> ord(j)" by auto2
lemma ord_is_trans_set [forward]: "ord(i) \<Longrightarrow> trans_set(i)" by auto2
setup {* del_prfstep_thm @{thm ord_def} *}

lemma trans_mem_rel [forward]: "ord(i) \<Longrightarrow> trans(mem_rel(i))" by auto2

(* Properties of succ *)
lemma ord_succ_is_ord [forward]: "ord(i) \<Longrightarrow> ord(succ(i))" by auto2
lemma succ_nonzero [resolve]: "succ(x) \<noteq> \<emptyset>" by auto2
lemma succ_inj [forward]: "succ(x) = succ(y) \<Longrightarrow> x = y" by auto2

(* Union is an ordinal. *)
lemma union_ord: "\<forall>x\<in>S. ord(x) \<Longrightarrow> ord(\<Union>S)" by auto2
lemma union_ordP: "\<forall>a\<in>I. ord(X(a)) \<Longrightarrow> ord(\<Union>a\<in>I. X(a))" by auto2

section {* Induction on ordinals *}

lemma ord_induct' [strong_induct]:
  "ord(k) \<and> i \<in> k \<Longrightarrow> \<forall>x\<in>k. (\<forall>y\<in>x. P(y)) \<longrightarrow> P(x) \<Longrightarrow> P(i)"
@proof @strong_induct "wf(mem_rel(k)) \<and> i \<in>. mem_rel(k)" @qed

lemma ord_induct [script_induct]:
  "ord(i) \<Longrightarrow> \<forall>x. ord(x) \<longrightarrow> (\<forall>y\<in>x. P(y)) \<longrightarrow> P(x) \<Longrightarrow> P(i)"
@proof @strong_induct "ord(succ(i)) \<and> i \<in> succ(i)" @qed

lemma ord_double_induct [script_induct]:
  "ord(i) \<and> ord(j) \<Longrightarrow> 
   \<forall>x y. ord(x) \<longrightarrow> ord(y) \<longrightarrow> (\<forall>x'\<in>x. P(x',y)) \<longrightarrow> (\<forall>y'\<in>y. P(x,y')) \<longrightarrow> P(x,y) \<Longrightarrow> P(i,j)"
@proof
  @have "\<forall>i' j'. ord(i') \<longrightarrow> (\<forall>i\<in>i'. \<forall>j. ord(j) \<longrightarrow> P(i, j)) \<longrightarrow> ord(j') \<longrightarrow> P(i', j')" @with
    @induct "ord(j')" "P(i',j')" @end
  @induct "ord(i)" "\<forall>j. ord(j) \<longrightarrow> P(i,j)"
@qed

(* Ordinals are linearly ordered *)
lemma ord_linear: "ord(i) \<Longrightarrow> ord(j) \<Longrightarrow> i \<in> j \<or> i = j \<or> j \<in> i"
@proof
  @induct "ord(i) \<and> ord(j)" "i \<in> j \<or> i = j \<or> j \<in> i"
@qed

end
