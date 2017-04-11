theory Wfrec
imports FixedPt
begin

definition rel_minimal :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "rel_minimal(r,Z,x) \<longleftrightarrow> (\<forall>y\<in>source(r). rel(r,y,x) \<longrightarrow> y \<notin> Z)"

lemma rel_minimalD [forward]:
  "y \<in> source(r) \<Longrightarrow> rel_minimal(r,Z,x) \<Longrightarrow> rel(r,y,x) \<Longrightarrow> y \<notin> Z" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm rel_minimal_def} *}

definition wf :: "i \<Rightarrow> o" where [rewrite]:
  "wf(r) \<longleftrightarrow> is_rel(r) \<and> (\<forall>Z\<in>Pow(source(r)). Z \<noteq> \<emptyset> \<longrightarrow> (\<exists>x\<in>Z. rel_minimal(r,Z,x)))"
setup {* add_property_const @{term wf} *}

lemma wfD1 [forward]: "wf(r) \<Longrightarrow> is_rel(r)" by auto2
lemma wfD2 [backward]: "wf(r) \<Longrightarrow> Z \<subseteq> source(r) \<Longrightarrow> Z \<noteq> \<emptyset> \<Longrightarrow> \<exists>x\<in>Z. rel_minimal(r,Z,x)" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm wf_def} *}

(* Given \<langle>a,b\<rangle> \<in> r^+, take a' to be the predecessor of b in the chain from a to b. *)
lemma rel_trans_cl_prev [backward]:
  "is_rel(R) \<Longrightarrow> R' = rel_trans_cl(R) \<Longrightarrow> rel(R',a,b) \<Longrightarrow>
   \<exists>a'\<in>source(R). rel(R,a',b) \<and> (a = a' \<or> rel(R',a,a'))"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "rel(rel_trans_cl(R),a,b)" "\<exists>a'\<in>source(R). rel(R,a',b) \<and> (a = a' \<or> rel(R',a,a'))") *})

lemma wf_trans_cl [forward]:
  "wf(r) \<Longrightarrow> wf(rel_trans_cl(r))"
  by (tactic {* auto2s_tac @{context} (
    LET "A = source(r)" THEN
    LET "r' = rel_trans_cl(r)" THEN
    HAVE "\<forall>B\<in>Pow(A). B \<noteq> \<emptyset> \<longrightarrow> (\<exists>x\<in>B. rel_minimal(r',B,x))" WITH (
      LET "B' = {x\<in>A. \<exists>y\<in>B. rel(r',y,x)}" THEN
      CHOOSE "m\<in>B', rel_minimal(r,B',m)" THEN
      HAVE "m \<in> B" WITH (
        CHOOSE "y \<in> B, rel(r',y,m)" THEN
        CHOOSE "y' \<in> A, rel(r,y',m) \<and> (y=y' \<or> rel(r',y,y'))") THEN
      HAVE "\<forall>y\<in>source(r). rel(r',y,m) \<longrightarrow> y \<notin> B" WITH (
        CHOOSE "y' \<in> A, rel(r,y',m) \<and> (y=y' \<or> rel(r',y,y'))"))) *})

(* Well-founded induction *)
lemma wf_induct [script_induct]:
  "\<forall>x\<in>source(r). (\<forall>y\<in>source(r). rel(r,y,x) \<longrightarrow> P(y)) \<longrightarrow> P(x) \<Longrightarrow> wf(r) \<and> a \<in> source(r) \<Longrightarrow> P(a)"
  by (tactic {* auto2s_tac @{context} (
    LET "Z = {z \<in> source(r). \<not>P(z)}" THEN
    CASE "Z = \<emptyset>" WITH HAVE "a \<notin> Z" THEN
    CHOOSE "m\<in>Z, rel_minimal(r,Z,m)") *})

(* f is a family indexed by rel_vsection(r,a) (set of all x such that rel(r,x,a)),
   H is a meta-function from x and the segment of f before x to T. *)
definition is_recfun :: "[i, i, [i, i] \<Rightarrow> i, i] \<Rightarrow> o" where [rewrite]:
  "is_recfun(r,a,H,f) \<longleftrightarrow> f = Tup(rel_vsection(r,a), \<lambda>x. H(x, proj_set(f, rel_vsection(r,x))))"

lemma is_recfun_is_family [forward]:
  "is_recfun(r,a,H,f) \<Longrightarrow> is_family(f) \<and> source(f) = rel_vsection(r,a)" by auto2

lemma is_recfun_eval [rewrite]:
  "x \<in> source(f) \<Longrightarrow> is_recfun(r,a,H,f) \<Longrightarrow> f`x = H(x, proj_set(f, rel_vsection(r,x)))" by auto2

lemma is_recfunI [backward2]:
  "is_family(f) \<Longrightarrow> source(f) = rel_vsection(r,a) \<Longrightarrow>
   \<forall>x\<in>source(f). f`x = H(x, proj_set(f, rel_vsection(r,x))) \<Longrightarrow> is_recfun(r,a,H,f)" by auto2
setup {* del_prfstep_thm @{thm is_recfun_def} *}

(* Uniqueness of is_recfun: main result proved by well-founded induction,
   followed by two corollaries. *)
lemma is_recfun_agree [forward]:
  "wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> is_recfun(r,a,H,f) \<Longrightarrow> is_recfun(r,b,H,g) \<Longrightarrow>
   \<forall>x. rel(r,x,a) \<longrightarrow> rel(r,x,b) \<longrightarrow> f`x = g`x"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x. rel(r,x,a) \<longrightarrow> rel(r,x,b) \<longrightarrow> f`x = g`x" WITH (
      INDUCT_ON "wf(r) \<and> x \<in> source(r)" "rel(r,x,a) \<longrightarrow> rel(r,x,b) \<longrightarrow> f`x = g`x")) *})

lemma is_recfun_unique [forward]:
  "wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> is_recfun(r,a,H,f) \<Longrightarrow> is_recfun(r,a,H,g) \<Longrightarrow> f = g" by auto2

lemma is_recfun_restrict_eq [forward]:
  "wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> is_recfun(r,a,H,f) \<Longrightarrow> is_recfun(r,b,H,g) \<Longrightarrow>
   rel(r,b,a) \<Longrightarrow> proj_set(f, rel_vsection(r,b)) = g" by auto2
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
  "wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> a \<in> source(r) \<Longrightarrow> is_recfun(r,a,H,the_recfun(r,a,H))"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x\<in>source(r). (\<forall>y\<in>source(r). rel(r,y,x) \<longrightarrow> is_recfun(r,y,H,the_recfun(r,y,H))) \<longrightarrow> is_recfun(r,x,H,the_recfun(r,x,H))" WITH (
      LET "f = Tup(rel_vsection(r,x), \<lambda>y. H(y, the_recfun(r,y,H)))" THEN
      HAVE "is_recfun(r,x,H,f)") THEN
    INDUCT_ON "wf(r) \<and> a \<in> source(r)" "is_recfun(r,a,H,the_recfun(r,a,H))") *})
setup {* add_forward_prfstep_cond @{thm unfold_the_recfun} [with_term "the_recfun(?r,?a,?H)"] *}

(* The full recursive function and its rewrite property. *)
definition wftrec :: "[i, [i, i] \<Rightarrow> i, i] \<Rightarrow> i" where [rewrite]:
  "wftrec(r,H,a) = H(a, the_recfun(r,a,H))"
setup {* register_wellform_data ("wftrec(r,H,a)", ["a \<in> source(r)"]) *}

lemma wftrec_unfold [rewrite]:
  "wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> a \<in> source(r) \<Longrightarrow>
   wftrec(r,H,a) = H(a, Tup(rel_vsection(r,a), \<lambda>x. wftrec(r,H,x)))" by auto2
setup {* del_prfstep_thm @{thm wftrec_def} *}

(* Definition that does not assume transitivity. *)
definition wfrec :: "[i, [i, i] \<Rightarrow> i, i] \<Rightarrow> i" where [rewrite]:
  "wfrec(r,H,a) = wftrec(rel_trans_cl(r), \<lambda>x f. H(x, proj_set(f,rel_vsection(r,x))), a)"
setup {* register_wellform_data ("wfrec(r,H,a)", ["a \<in> source(r)"]) *}

lemma wfrec_unfold [rewrite]:
  "wf(r) \<Longrightarrow> a \<in> source(r) \<Longrightarrow>
   wfrec(r,H,a) = H(a, Tup(rel_vsection(r,a), \<lambda>x. wfrec(r,H,x)))" by auto2
setup {* del_prfstep_thm @{thm wfrec_def} *}

end
