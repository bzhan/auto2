(*
  File: FixedPt.thy
  Author: Bohua Zhan

  Fixed point theorems, roughly following FixedPt in Isabelle/ZF.
*)

theory FixedPt
  imports OrderRel
begin

(* h is a function from Pow(D) to itself, and is monotone in the sense that
   given two subsets W and X of D such that W \<subseteq> X, then h(W) \<subseteq> h(X). *)
definition bnd_mono :: "i \<Rightarrow> (i \<Rightarrow> i) \<Rightarrow> o" where [rewrite]:
  "bnd_mono(D,h) \<longleftrightarrow> (h(D) \<subseteq> D \<and> (\<forall>W X. W \<subseteq> X \<longrightarrow> X \<subseteq> D \<longrightarrow> h(W) \<subseteq> h(X)))"

(* Least fixed point of h. *)
definition lfp :: "i \<Rightarrow> (i \<Rightarrow> i) \<Rightarrow> i" where [rewrite]:
  "lfp(D,h) = \<Inter>({X \<in> Pow(D). h(X) \<subseteq> X})"
setup {* add_prfstep_check_req ("lfp(D,h)", "bnd_mono(D,h)") *}

(* Greatest fixed point of h. *)
definition gfp :: "i \<Rightarrow> (i \<Rightarrow> i) \<Rightarrow> i" where [rewrite]:
  "gfp(D,h) = \<Union>({X \<in> Pow(D). X \<subseteq> h(X)})"

section {* Monotone operators *}

lemma bnd_monoD1 [forward]: "bnd_mono(D,h) \<Longrightarrow> h(D) \<subseteq> D" by auto2
lemma bnd_monoD2 [backward2]: "bnd_mono(D,h) \<Longrightarrow> W \<subseteq> X \<Longrightarrow> X \<subseteq> D \<Longrightarrow> h(W) \<subseteq> h(X)" by auto2
setup {* del_prfstep_thm_eqforward @{thm bnd_mono_def} *}

lemma bnd_mono_subset: "bnd_mono(D,h) \<Longrightarrow> X \<subseteq> D \<Longrightarrow> h(X) \<subseteq> D" by auto2
lemma bnd_mono_Un: "bnd_mono(D,h) \<Longrightarrow> A \<subseteq> D \<Longrightarrow> B \<subseteq> D \<Longrightarrow> h(A) \<union> h(B) \<subseteq> h(A \<union> B)" by auto2

section {* Knaster-Tarski Theorem using lfp *}

lemma lfp_set_nonempty [backward2]:
  "h(A) \<subseteq> A \<Longrightarrow> A \<subseteq> D \<Longrightarrow> {X \<in> Pow(D). h(X) \<subseteq> X} \<noteq> \<emptyset>"
@proof @have "A \<in> {X \<in> Pow(D). h(X) \<subseteq> X}" @qed

(* lfp(D,h) is a subset of any fixed point of h. *)
lemma lfp_lowerbound [backward]:
  "h(A) \<subseteq> A \<Longrightarrow> A \<subseteq> D \<Longrightarrow> lfp(D,h) \<subseteq> A" by auto2

(* If A is a subset of any fixed point of h, then A is a subset of lfp(D,h). *)
lemma lfp_greatest [backward2]:
  "h(D) \<subseteq> D \<Longrightarrow> \<forall>X. h(X) \<subseteq> X \<longrightarrow> X \<subseteq> D \<longrightarrow> A \<subseteq> X \<Longrightarrow> A \<subseteq> lfp(D,h)" by auto2

(* lfp is indeed a fixed point of h. *)
lemma lfp_unfold [rewrite]:
  "bnd_mono(D,h) \<Longrightarrow> h(lfp(D,h)) = lfp(D,h)"
@proof @have  "h(lfp(D,h)) \<subseteq> lfp(D,h)" @qed

section {* General induction rule for least fixed points *}

(* Induction rule: given predicate P and let A be the subset of lfp that satisfies P.
   If everything in h(A) also satisfies P, then in fact A = lfp. *)
lemma lfp_induct [script_induct]:
  "a \<in> lfp(D,h) \<Longrightarrow> bnd_mono(D,h) \<Longrightarrow> \<forall>x\<in>h(Collect(lfp(D,h),P)). P(x) \<Longrightarrow> P(a)"
@proof @have "h(Collect(lfp(D,h),P)) \<subseteq> lfp(D,h)" @qed

lemma lfp_Int_lowerbound [backward1]:
  "bnd_mono(D,h) \<Longrightarrow> h(D \<inter> A) \<subseteq> A \<Longrightarrow> lfp(D,h) \<subseteq> A" by auto2

lemma lfp_mono:
  "bnd_mono(D,h) \<Longrightarrow> bnd_mono(E,i) \<Longrightarrow> \<forall>X. X \<subseteq> D \<longrightarrow> h(X) \<subseteq> i(X) \<Longrightarrow>
   lfp(D,h) \<subseteq> lfp(E,i)"
@proof
  @have "\<forall>X. i(X) \<subseteq> X \<longrightarrow> X \<subseteq> E \<longrightarrow> lfp(D,h) \<subseteq> X" @with
    @have "h(D \<inter> X) \<subseteq> X" @with @have "h(D \<inter> X) \<subseteq> i(D \<inter> X)" @end @end
@qed

lemma lfp_cong:
  "\<forall>X. X \<subseteq> D \<longrightarrow> h(X) = h'(X) \<Longrightarrow> lfp(D,h) = lfp(D,h')" by auto2
setup {* del_prfstep_thm @{thm lfp_def} *}

section {* Knaster-Tarski Theorem using gfp *}

(* Any fixed point of h is contained in gfp(D,h). *)
lemma gfp_upperbound [backward]:
  "A \<subseteq> h(A) \<Longrightarrow> A \<subseteq> D \<Longrightarrow> A \<subseteq> gfp(D,h)" by auto2

(* If A contains any fixed point of h, then A contains gfp(D,h). *)
lemma gfp_least [backward2]:
  "h(D) \<subseteq> D \<Longrightarrow> \<forall>X. X \<subseteq> h(X) \<longrightarrow> X \<subseteq> D \<longrightarrow> X \<subseteq> A \<Longrightarrow> gfp(D,h) \<subseteq> A" by auto2

(* gfp is indeed a fixed point of h. *)
lemma gfp_unfold [rewrite]:
  "bnd_mono(D,h) \<Longrightarrow> h(gfp(D,h)) = gfp(D,h)"
@proof @have "gfp(D,h) \<subseteq> h(gfp(D,h))" @qed

section {* General induction rule for greatest fixed points *}

lemma gfp_weak_coinduct:
  "a \<in> X \<Longrightarrow> X \<subseteq> h(X) \<Longrightarrow> X \<subseteq> D \<Longrightarrow> a \<in> gfp(D,h)" by auto2

lemma gfp_coinduct_lemma [backward1]:
  "X \<subseteq> D \<Longrightarrow> bnd_mono(D,h) \<Longrightarrow> X \<subseteq> h(X \<union> gfp(D,h)) \<Longrightarrow> X \<union> gfp(D,h) \<subseteq> h(X \<union> gfp(D,h))" by auto2

lemma gfp_coinduct:
  "bnd_mono(D,h) \<Longrightarrow> a \<in> X \<Longrightarrow> X \<subseteq> h(X \<union> gfp(D,h)) \<Longrightarrow> X \<subseteq> D \<Longrightarrow> a \<in> gfp(D,h)" by auto2

lemma gfp_mono:
  "bnd_mono(D,h) \<Longrightarrow> D \<subseteq> E \<Longrightarrow> \<forall>X. X \<subseteq> D \<longrightarrow> h(X) \<subseteq> i(X) \<Longrightarrow> gfp(D,h) \<subseteq> gfp(E,i)" by auto2
setup {* del_prfstep_thm @{thm gfp_def} *}

section {* Transitive closure *}

definition rtrans_cl :: "i \<Rightarrow> i" where [rewrite]:
  "rtrans_cl(r) = lfp(gr_field(r)\<times>gr_field(r), \<lambda>s. gr_id(gr_field(r)) \<union> (r \<circ>\<^sub>g s))"

lemma rtrans_cl_bnd_mono [resolve]:
  "bnd_mono(gr_field(r)\<times>gr_field(r), \<lambda>s. gr_id(gr_field(r)) \<union> (r \<circ>\<^sub>g s))" by auto2

lemma rtrans_cl_eq [rewrite]:
  "rtrans_cl(r) = gr_id(gr_field(r)) \<union> (r \<circ>\<^sub>g rtrans_cl(r))" by auto2

lemma rtrans_cl_is_graph [forward]: "is_graph(r) \<Longrightarrow> is_graph(rtrans_cl(r))" by auto2
lemma rtrans_clI1 [typing2]: "a \<in> gr_field(r) \<Longrightarrow> \<langle>a,a\<rangle>\<in>rtrans_cl(r)" by auto2
lemma rtrans_clI2 [typing2]: "\<langle>a,b\<rangle> \<in> r \<Longrightarrow> \<langle>a,b\<rangle> \<in> rtrans_cl(r)" by auto2
lemma rtrans_clI3 [forward]: "\<langle>a,b\<rangle>\<in>rtrans_cl(r) \<Longrightarrow> \<langle>b,c\<rangle>\<in>r \<Longrightarrow> \<langle>a,c\<rangle>\<in>rtrans_cl(r)" by auto2

lemma rtrans_cl_full_induct [script_induct]:
  "x \<in> rtrans_cl(r) \<Longrightarrow> \<forall>x\<in>gr_field(r). P(\<langle>x,x\<rangle>) \<Longrightarrow>
   \<forall>x y z. P(\<langle>x,y\<rangle>) \<longrightarrow> \<langle>x,y\<rangle>\<in>rtrans_cl(r) \<longrightarrow> \<langle>y,z\<rangle>\<in>r \<longrightarrow> P(\<langle>x,z\<rangle>) \<Longrightarrow> P(x)"
@proof
  @induct "x \<in> lfp(gr_field(r)\<times>gr_field(r), \<lambda>s. gr_id(gr_field(r)) \<union> (r \<circ>\<^sub>g s))" "P(x)"
@qed
setup {* del_prfstep_thm @{thm rtrans_cl_def} *}

lemma rtrans_cl_induct [script_induct]:
  "\<langle>a,b\<rangle> \<in> rtrans_cl(r) \<Longrightarrow>
   \<forall>y z. \<langle>a,y\<rangle>\<in>rtrans_cl(r) \<longrightarrow> \<langle>y,z\<rangle>\<in>r \<longrightarrow> y \<noteq> z \<longrightarrow> P(y) \<longrightarrow> P(z) \<Longrightarrow>
   P(a) \<Longrightarrow> P(b)"
@proof
  @induct "\<langle>a,b\<rangle> \<in> rtrans_cl(r)" "fst(\<langle>a,b\<rangle>) = a \<longrightarrow> P(snd(\<langle>a,b\<rangle>))"
@qed
setup {* delete_script_induct_data @{thm rtrans_cl_full_induct} *}

lemma rtrans_cl_trans [forward]:
  "\<langle>c,a\<rangle>\<in>rtrans_cl(r) \<Longrightarrow> \<langle>a,b\<rangle>\<in>rtrans_cl(r) \<Longrightarrow> \<langle>c,b\<rangle>\<in>rtrans_cl(r)"
@proof
  @induct "\<langle>a,b\<rangle> \<in> rtrans_cl(r)" "\<langle>c,b\<rangle>\<in>rtrans_cl(r)"
@qed
setup {* del_prfstep_thm @{thm rtrans_cl_eq} *}

definition rel_rtrans_cl :: "i \<Rightarrow> i" where [rewrite]:
  "rel_rtrans_cl(R) = Order(carrier(R), \<lambda>x y. \<langle>x,y\<rangle> \<in> rtrans_cl(order_graph(R)))"

lemma rel_rtrans_cl_is_rel [typing]:
  "raworder(R) \<Longrightarrow> rel_rtrans_cl(R) \<in> raworder_space(carrier(R))" by auto2

lemma rel_rtrans_clI1:
  "raworder(R) \<Longrightarrow> x \<le>\<^sub>R y \<Longrightarrow> le(rel_rtrans_cl(R),x,y)"
@proof @have "\<langle>x,y\<rangle> \<in> order_graph(R)" @qed
setup {* add_forward_prfstep_cond @{thm rel_rtrans_clI1} [with_term "rel_rtrans_cl(?R)"] *}

lemma rel_rtrans_clI2 [forward]: "raworder(R) \<Longrightarrow> trans(rel_rtrans_cl(R))" by auto2
lemma rel_rtrans_clI3 [forward]: "refl_order(R) \<Longrightarrow> preorder(rel_rtrans_cl(R))"
@proof
  @let "S = rel_rtrans_cl(R)"
  @have "\<forall>x\<in>.S. x \<le>\<^sub>S x" @with @have "\<langle>x,x\<rangle> \<in> order_graph(R)" @end
@qed

lemma rel_rtrans_cl_induct [script_induct]:
  "le(rel_rtrans_cl(R),a,b) \<Longrightarrow> raworder(R) \<Longrightarrow>
   \<forall>y z. le(rel_rtrans_cl(R),a,y) \<longrightarrow> y <\<^sub>R z \<longrightarrow> P(y) \<longrightarrow> P(z) \<Longrightarrow> P(a) \<Longrightarrow> P(b)"
@proof
  @induct "\<langle>a,b\<rangle>\<in>rtrans_cl(order_graph(R))" "P(b)"
@qed

setup {* del_prfstep_thm @{thm rel_rtrans_cl_def} *}

end
