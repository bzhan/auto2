theory Wfrec
imports FixedPt
begin

definition ord_minimal :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "ord_minimal(r,Z,x) \<longleftrightarrow> (\<forall>y\<in>.r. y \<le>\<^sub>r x \<longrightarrow> y \<notin> Z)"

lemma rel_minimalD [forward]:
  "y \<in>. r \<Longrightarrow> ord_minimal(r,Z,x) \<Longrightarrow> y \<le>\<^sub>r x \<Longrightarrow> y \<notin> Z" by auto2
setup {* del_prfstep_thm_eqforward @{thm ord_minimal_def} *}

definition wf :: "i \<Rightarrow> o" where [rewrite]:
  "wf(r) \<longleftrightarrow> raworder(r) \<and> (\<forall>Z\<in>Pow(carrier(r)). Z \<noteq> \<emptyset> \<longrightarrow> (\<exists>x\<in>Z. ord_minimal(r,Z,x)))"
setup {* add_property_const @{term wf} *}

lemma wfD1 [forward]: "wf(r) \<Longrightarrow> raworder(r)" by auto2
lemma wfD2 [backward]: "wf(r) \<Longrightarrow> Z \<noteq> \<emptyset> \<Longrightarrow> \<exists>x\<in>Z. ord_minimal(r,Z,x)" by auto2
setup {* del_prfstep_thm_eqforward @{thm wf_def} *}

(* Given \<langle>a,b\<rangle> \<in> r^+, take a' to be the predecessor of b in the chain from a to b. *)
lemma rel_trans_cl_prev [backward]:
  "raworder(R) \<Longrightarrow> S = rel_trans_cl(R) \<Longrightarrow> a \<le>\<^sub>S b \<Longrightarrow>
   \<exists>a'\<in>.R. a' \<le>\<^sub>R b \<and> (a = a' \<or> le(S,a,a'))"
@proof
  @induct "le(rel_trans_cl(R),a,b)" "\<exists>a'\<in>.R. a' \<le>\<^sub>R b \<and> (a = a' \<or> a \<le>\<^sub>S a')"
@qed

lemma wf_trans_cl [forward]:
  "wf(r) \<Longrightarrow> wf(rel_trans_cl(r))"
@proof
  @let "A = carrier(r)"
  @let "r' = rel_trans_cl(r)"
  @have "\<forall>B\<in>Pow(A). B \<noteq> \<emptyset> \<longrightarrow> (\<exists>x\<in>B. ord_minimal(r',B,x))" @with
    @contradiction
    @let "B' = {x\<in>A. \<exists>y\<in>B. le(r',y,x)}"
    @obtain "m\<in>B'" where "ord_minimal(r,B',m)"
    @have "m \<in> B" @with
      @obtain "y \<in> B" where "le(r',y,m)"
      @obtain "y' \<in> A" where "le(r,y',m)" "(y=y' \<or> le(r',y,y'))"
    @end
    @have "\<forall>y\<in>carrier(r). le(r',y,m) \<longrightarrow> y \<notin> B" @with
      @obtain "y' \<in> A" where "le(r,y',m)" "(y=y' \<or> le(r',y,y'))"
    @end
  @end
@qed

(* Well-founded induction *)
lemma wf_induct [strong_induct]:
  "wf(r) \<and> a \<in>. r \<Longrightarrow> \<forall>x\<in>.r. (\<forall>y\<in>.r. y \<le>\<^sub>r x \<longrightarrow> P(y)) \<longrightarrow> P(x) \<Longrightarrow> P(a)"
@proof
  @let "Z = {z \<in>. r. \<not>P(z)}"
  @case "Z = \<emptyset>" @with @have "a \<notin> Z" @end
  @obtain "m\<in>Z" where "ord_minimal(r,Z,m)"
@qed

definition ord_pred :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "ord_pred(r,a) = {x\<in>.r. x \<le>\<^sub>r a}"
setup {* register_wellform_data ("ord_pred(r,a)", ["a \<in>. r"]) *}

lemma ord_predI [typing2,backward]: "raworder(r) \<Longrightarrow> x \<le>\<^sub>r a \<Longrightarrow> x \<in> ord_pred(r,a)" by auto2
lemma ord_predE [forward]: "x \<in> ord_pred(r,a) \<Longrightarrow> x \<le>\<^sub>r a" by auto2
setup {* del_prfstep_thm @{thm ord_pred_def} *}

(* f is a family indexed by ord_pred(r,a) (set of all x such that le(r,x,a)),
   H is a meta-function from x and the segment of f before x to T. *)
definition is_recfun :: "[i, i, [i, i] \<Rightarrow> i, i] \<Rightarrow> o" where [rewrite]:
  "is_recfun(r,a,H,f) \<longleftrightarrow> f = Tup(ord_pred(r,a), \<lambda>x. H(x, proj_set(f, ord_pred(r,x))))"

lemma is_recfun_is_family [forward]:
  "is_recfun(r,a,H,f) \<Longrightarrow> is_family(f) \<and> source(f) = ord_pred(r,a)" by auto2

lemma is_recfun_eval [rewrite]:
  "x \<in> source(f) \<Longrightarrow> is_recfun(r,a,H,f) \<Longrightarrow> f`x = H(x, proj_set(f, ord_pred(r,x)))" by auto2

lemma is_recfunI [backward2]:
  "is_family(f) \<Longrightarrow> source(f) = ord_pred(r,a) \<Longrightarrow>
   \<forall>x\<in>source(f). f`x = H(x, proj_set(f, ord_pred(r,x))) \<Longrightarrow> is_recfun(r,a,H,f)" by auto2
setup {* del_prfstep_thm @{thm is_recfun_def} *}

(* Uniqueness of is_recfun: main result proved by well-founded induction,
   followed by two corollaries. *)
lemma is_recfun_agree [forward]:
  "wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> is_recfun(r,a,H,f) \<Longrightarrow> is_recfun(r,b,H,g) \<Longrightarrow>
   \<forall>x. le(r,x,a) \<longrightarrow> le(r,x,b) \<longrightarrow> f`x = g`x"
@proof
  @have "\<forall>x. x \<le>\<^sub>r a \<longrightarrow> x \<le>\<^sub>r b \<longrightarrow> f`x = g`x" @with
    @strong_induct "wf(r) \<and> x \<in>. r"
  @end
@qed

lemma is_recfun_unique [forward]:
  "wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> is_recfun(r,a,H,f) \<Longrightarrow> is_recfun(r,a,H,g) \<Longrightarrow> f = g" by auto2

lemma is_recfun_restrict_eq [forward]:
  "wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> is_recfun(r,a,H,f) \<Longrightarrow> is_recfun(r,b,H,g) \<Longrightarrow>
   b \<le>\<^sub>r a \<Longrightarrow> proj_set(f, ord_pred(r,b)) = g" by auto2
setup {* del_prfstep_thm @{thm is_recfun_agree} *}

(* Define recursive function using THE operator. *)
definition the_recfun :: "[i, i, [i, i] \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "the_recfun(r,a,H) = (THE f. is_recfun(r,a,H,f))"

lemma the_recfun_eq [rewrite]:
  "wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> is_recfun(r,a,H,f) \<Longrightarrow> the_recfun(r,a,H) = f" by auto2

lemma is_the_recfun:
  "wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> is_recfun(r,a,H,f) \<Longrightarrow> is_recfun(r,a,H,the_recfun(r,a,H))" by auto2
setup {* add_forward_prfstep_cond @{thm is_the_recfun} [with_term "the_recfun(?r,?a,?H)"] *}
setup {* del_prfstep_thm @{thm the_recfun_def} *}

(* Existence of recursive function, proved by a second well-founded induction. *)
lemma unfold_the_recfun:
  "wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> a \<in>. r \<Longrightarrow> is_recfun(r,a,H,the_recfun(r,a,H))"
@proof
  @strong_induct "wf(r) \<and> a \<in>. r"
  @let "f = Tup(ord_pred(r,a), \<lambda>y. H(y, the_recfun(r,y,H)))"
  @have "is_recfun(r,a,H,f)"
@qed
setup {* add_forward_prfstep_cond @{thm unfold_the_recfun} [with_term "the_recfun(?r,?a,?H)"] *}

(* The full recursive function and its rewrite property. *)
definition wftrec :: "[i, [i, i] \<Rightarrow> i, i] \<Rightarrow> i" where [rewrite]:
  "wftrec(r,H,a) = H(a, the_recfun(r,a,H))"
setup {* register_wellform_data ("wftrec(r,H,a)", ["a \<in> source(r)"]) *}

lemma wftrec_unfold [rewrite]:
  "wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> a \<in>. r \<Longrightarrow>
   wftrec(r,H,a) = H(a, Tup(ord_pred(r,a), \<lambda>x. wftrec(r,H,x)))" by auto2
setup {* del_prfstep_thm @{thm wftrec_def} *}

(* Definition that does not assume transitivity.

   Assuming r is a well-founded order and a is an element in source(r),
   H is a meta-function indicating how to obtain value at x from a mapping
   from x and the family of values at the set r^-1(x).
*)
definition wfrec :: "[i, [i, i] \<Rightarrow> i, i] \<Rightarrow> i" where [rewrite]:
  "wfrec(r,H,a) = wftrec(rel_trans_cl(r), \<lambda>x f. H(x, proj_set(f,ord_pred(r,x))), a)"
setup {* register_wellform_data ("wfrec(r,H,a)", ["a \<in> source(r)"]) *}

lemma wfrec_unfold [rewrite]:
  "wf(r) \<Longrightarrow> a \<in>. r \<Longrightarrow>
   wfrec(r,H,a) = H(a, Tup(ord_pred(r,a), \<lambda>x. wfrec(r,H,x)))" by auto2
setup {* del_prfstep_thm @{thm wfrec_def} *}

end
