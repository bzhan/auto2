theory WellOrder
imports OrderRel
begin

section {* Well-ordered sets *}  (* Bourbaki III.2.1 *)

(* Definition of well_order *)
definition well_order :: "i \<Rightarrow> o" where well_order_def [rewrite]:
  "well_order(R) \<longleftrightarrow> (linorder_rel(R) \<and> (\<forall>X. X \<subseteq> source(R) \<longrightarrow> X \<noteq> \<emptyset> \<longrightarrow> has_least(R,X)))"
setup {* add_property_const @{term well_order} *}

lemma well_orderD1 [forward]: "well_order(R) \<Longrightarrow> linorder_rel(R)" by auto2
lemma well_orderD2 [forward, backward]:
  "well_order(R) \<Longrightarrow> X \<subseteq> source(R) \<Longrightarrow> X \<noteq> \<emptyset> \<Longrightarrow> has_least(R,X)" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm well_order_def} *}

lemma wellorder_iso [forward]:
  "well_order(R) \<Longrightarrow> isomorphism(R,S,f) \<Longrightarrow> well_order(S)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>X. X \<subseteq> source(S) \<longrightarrow> X \<noteq> \<emptyset> \<longrightarrow> has_least(S,X)" WITH (
      CHOOSE "U, U = f -`` X" THEN
      HAVE "has_least(R,U)" THEN
      HAVE "has_least(S,X) \<and> least(S,X) = f ` least(R,U)")) *})

lemma well_order_subrel:
  "well_order(R) \<Longrightarrow> A \<subseteq> source(R) \<Longrightarrow> well_order(subrel(R,A))" by auto2

lemma well_order_adjoin [backward]:
  "well_order(R) \<Longrightarrow> a \<notin> source(R) \<Longrightarrow> well_order(adjoin_greatest(R,a))"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>X. X \<subseteq> source(R)\<union>{a} \<longrightarrow> X \<noteq> \<emptyset> \<longrightarrow> has_least(adjoin_greatest(R,a),X)" WITH (
      HAVE "has_least(R,X-{a})" THEN
      HAVE "R = subrel(adjoin_greatest(R,a),source(R))" THEN
      HAVE "has_least(adjoin_greatest(R,a), X-{a})")) *})

(* Segments. Correspond to less_intervals for well_order. The main result in
   this portion is that if R is well-ordered, the set of segments of R is well-ordered,
   and isomorphic to R adjoining a greatest element. *)
definition is_segment :: "[i, i] \<Rightarrow> o" where is_segment_def [rewrite]:
  "is_segment(R,S) \<longleftrightarrow> (S \<subseteq> source(R) \<and> (\<forall>x\<in>S. \<forall>y\<in>source(R). y \<le>\<^sub>R x \<longrightarrow> y \<in> S))"

lemma is_segmentD [forward]:
  "is_segment(R,S) \<Longrightarrow> S \<subseteq> source(R)"
  "is_segment(R,S) \<Longrightarrow> x \<in> S \<Longrightarrow> \<forall>y\<in>source(R). y \<le>\<^sub>R x \<longrightarrow> y \<in> S" by auto2+
setup {* del_prfstep_thm_str "@eqforward" @{thm is_segment_def} *}

lemma segment_is_interval [backward2]:
  "well_order(R) \<Longrightarrow> is_segment(R,S) \<Longrightarrow> S \<noteq> source(R) \<Longrightarrow> \<exists>a\<in>source(R). S = less_interval(R,a)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "has_least(R,source(R)-S)" THEN
    HAVE "least(R,source(R)-S) \<in> source(R)" THEN
    HAVE "source(R)-S = ge_interval(R,least(R,source(R)-S))") *})

lemma interval_is_segment [resolve]:
  "order_rel(R) \<Longrightarrow> is_segment(R,less_interval(R,a))" by auto2

definition segments :: "i \<Rightarrow> i" where segment_set_def [rewrite]:
  "segments(R) = {S \<in> Pow(source(R)). is_segment(R,S)}"

definition pt_to_segment_fun :: "i \<Rightarrow> i" where pt_to_segment_fun_def [rewrite]:
  "pt_to_segment_fun(R) = (\<lambda>a\<in>source(R). less_interval(R,a)\<in>segments(R))"

lemma pt_to_segment_fun_is_fun [typing]:
  "well_order(R) \<Longrightarrow> pt_to_segment_fun(R) \<in> source(R) \<rightarrow> segments(R)" by auto2

lemma pt_to_segment_eval [rewrite]:
  "well_order(R) \<Longrightarrow> a \<in> source(R) \<Longrightarrow> pt_to_segment_fun(R) ` a = less_interval(R,a)" by auto2
setup {* del_prfstep_thm @{thm pt_to_segment_fun_def} *}

lemma pt_to_segment_fun_inj [forward]:
  "well_order(R) \<Longrightarrow> injective(pt_to_segment_fun(R))" by auto2

lemma pt_to_segment_fun_incr [resolve]:
  "well_order(R) \<Longrightarrow> incr(R,subset_order(segments(R)),pt_to_segment_fun(R))" by auto2
setup {* add_forward_prfstep_cond @{thm pt_to_segment_fun_incr} [with_term "pt_to_segment_fun(?R)"] *}

lemma pt_to_segment_fun_image [rewrite]:
  "well_order(R) \<Longrightarrow> pt_to_segment_fun(R) `` source(R) = segments(R) - {source(R)}"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>S\<in>segments(R) - {source(R)}. S \<in> pt_to_segment_fun(R) `` source(R)" WITH (
      CHOOSE "a\<in>source(R), S = less_interval(R,a)" THEN
      HAVE "S = pt_to_segment_fun(R) ` a")) *})

lemma pt_to_segment_fun_iso:
  "well_order(R) \<Longrightarrow>
   isomorphism(R,subset_order(segments(R)-{source(R)}),func_restrict_image(pt_to_segment_fun(R))) \<and>
   well_order(subset_order(segments(R)-{source(R)}))" by auto2
setup {* add_forward_prfstep_cond (conj_right_th @{thm pt_to_segment_fun_iso})
    [with_term "subset_order(segments(?R)-{source(?R)})"] *}

lemma segments_order [rewrite_back]:
  "well_order(R) \<Longrightarrow> subset_order(segments(R)) =
    adjoin_greatest(subset_order(segments(R)-{source(R)}),source(R))" by auto2

lemma segments_wellorder:
  "well_order(R) \<Longrightarrow> well_order(subset_order(segments(R)))"
  by (tactic {* auto2s_tac @{context} (
    HAVE "subset_order(segments(R)) = adjoin_greatest(subset_order(segments(R)-{source(R)}),source(R))") *})

(* Families of well-ordered sets *)
definition is_segment_rel :: "[i, i] \<Rightarrow> o" where is_segment_rel_def [rewrite]:
  "is_segment_rel(R,S) \<longleftrightarrow> (is_subrel(R,S) \<and> is_segment(S,source(R)))"

definition well_order_family :: "i \<Rightarrow> o" where well_order_family_def [rewrite]:
  "well_order_family(X) \<longleftrightarrow> ((\<forall>R\<in>X. well_order(R)) \<and>
    (\<forall>R\<in>X. \<forall>S\<in>X. is_segment_rel(R,S) \<or> is_segment_rel(S,R)))"
setup {* add_property_const @{term well_order_family} *}

lemma well_order_familyD [forward]:
  "well_order_family(X) \<Longrightarrow> R \<in> X \<Longrightarrow> well_order(R)"
  "well_order_family(X) \<Longrightarrow> \<not>is_segment_rel(R,S) \<Longrightarrow> R \<in> X \<Longrightarrow> S \<in> X \<Longrightarrow> is_segment_rel(S,R)" by auto2+
setup {* del_prfstep_thm_str "@eqforward" @{thm well_order_family_def} *}

lemma well_order_familyD' [backward]:
  "well_order_family(X) \<Longrightarrow> R \<in> X \<Longrightarrow> y \<in> union_src(X) \<Longrightarrow> \<exists>S\<in>X. y \<in> source(S) \<and> is_segment_rel(R,S)"
  by auto2

lemma well_order_family_directed [forward]:
  "well_order_family(X) \<Longrightarrow> directed_rels(X)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>R\<in>X. \<forall>S\<in>X. \<exists>T\<in>X. is_subrel(R,T) \<and> is_subrel(S,T)" WITH (
      CASE "is_segment_rel(R,S)")) *})

lemma is_segment_union [backward]:
  "well_order_family(X) \<Longrightarrow> R \<in> X \<Longrightarrow> is_segment_rel(R,union_rel(X))"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "U, U = union_rel(X)" THEN
    HAVE "\<forall>x\<in>source(R). \<forall>y\<in>union_src(X). y \<le>\<^sub>U x \<longrightarrow> y \<in> source(R)" WITH (
      CHOOSE "S\<in>X, y \<in> source(S) \<and> is_segment_rel(R,S)")) *})

lemma well_order_family_union_prop [forward]:
  "well_order_family(X) \<Longrightarrow> well_order(union_rel(X))"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>H. H \<subseteq> union_src(X) \<longrightarrow> H \<noteq> \<emptyset> \<longrightarrow> has_least(union_rel(X),H)" WITH (
      CHOOSE "R\<in>X, H \<inter> source(R) \<noteq> \<emptyset>" WITH (
        CHOOSE "x, x \<in> H" THEN CHOOSE "S\<in>X, x \<in> source(S)" THEN
        HAVE "x \<in> H \<inter> source(S)") THEN
      HAVE "has_least(R, H \<inter> source(R))" THEN
      CHOOSE "m, m = least(R, H \<inter> source(R))" THEN
      HAVE "has_least(union_rel(X),H) \<and> least(union_rel(X),H) = m" WITH (
        HAVE "\<forall>x\<in>H. ge(x,union_rel(X),m)" WITH (
          CASE "x \<in> source(R)" WITH HAVE "x \<in> H \<inter> source(R)" THEN
          CHOOSE "S\<in>X, x \<in> source(S) \<and> is_segment_rel(R,S)")))) *})

lemma well_order_family_segments [rewrite]:
  "well_order_family(X) \<Longrightarrow> R \<in> X \<Longrightarrow> x \<in> source(R) \<Longrightarrow> less_interval(R,x) = less_interval(union_rel(X),x)"
  by (tactic {* auto2s_tac @{context} (HAVE "is_segment_rel(R,union_rel(X))") *})

lemma well_order_family_segments2:
  "well_order_family(X) \<Longrightarrow> is_segment(union_rel(X),S) \<Longrightarrow> S \<noteq> union_src(X) \<Longrightarrow>
   \<exists>R\<in>X. is_segment(R,S)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "x\<in>union_src(X), S = less_interval(union_rel(X),x)" THEN
    CHOOSE "R\<in>X, x \<in> source(R)" THEN
    HAVE "less_interval(R,x) = less_interval(union_rel(X),x)") *})

section {* Zermelo's Theorem *}  (* Bourbaki III.2.3 *)

(* Set of relations on subsets of E. *)
definition subrel_space :: "i \<Rightarrow> i" where subrel_space_def [rewrite]:
  "subrel_space(E) = (\<Union>X\<in>Pow(E). rel_space(X))"

lemma subrel_space_iff [rewrite]:
  "R \<in> subrel_space(E) \<longleftrightarrow> (is_relation(R) \<and> source(R) = target(R) \<and> source(R) \<subseteq> E)" by auto2
setup {* del_prfstep_thm @{thm subrel_space_def} *}

(* Given a set E, a collection S of subsets of E, and a map p from S to E such
   that p(X) \<notin> X for all X \<in> S, define collection of compatible well-ordering
   on subsets of E. *)
definition compat_wellorders :: "[i, i, i] \<Rightarrow> i" where compat_wellorders_def [rewrite]:
  "compat_wellorders(E,S,p) = {R\<in>subrel_space(E).
    well_order(R) \<and> (\<forall>x\<in>source(R). less_interval(R,x) \<in> S \<and> p`(less_interval(R,x)) = x)}"

lemma compat_wellordersD:
  "R \<in> compat_wellorders(E,S,p) \<Longrightarrow> well_order(R) \<and> source(R) \<subseteq> E"
  "R \<in> compat_wellorders(E,S,p) \<Longrightarrow> x \<in> source(R) \<Longrightarrow> less_interval(R,x) \<in> S"
  "R \<in> compat_wellorders(E,S,p) \<Longrightarrow> x \<in> source(R) \<Longrightarrow> p`(less_interval(R,x)) = x" by auto2+
setup {* fold add_forward_prfstep @{thms compat_wellordersD(1-2)} *}
setup {* add_rewrite_rule @{thm compat_wellordersD(3)} *}

lemma compat_wellordersI [backward]:
  "well_order(R) \<Longrightarrow> source(R) \<subseteq> E \<Longrightarrow>
   \<forall>x\<in>source(R). less_interval(R,x) \<in> S \<and> p`(less_interval(R,x)) = x \<Longrightarrow>
   R \<in> compat_wellorders(E,S,p)" by auto2
setup {* del_prfstep_thm @{thm compat_wellorders_def} *}

lemma less_interval_rel_is_segment:
  "well_order(R) \<Longrightarrow> x \<in> R \<Longrightarrow> is_segment_rel(less_interval_rel(R,x),R)" by auto2
setup {* add_forward_prfstep_cond @{thm less_interval_rel_is_segment}
  [with_term "less_interval_rel(?R,?x)"] *}

definition compat_wellorder_segs :: "[i, i, i, i, i] \<Rightarrow> i" where compat_wellorder_segs_def [rewrite]:
  "compat_wellorder_segs(E,S,p,R1,R2) =
    {x\<in>source(R1)\<inter>source(R2). less_interval_rel(R1,x) = less_interval_rel(R2,x)}"

(* Basic properties of compat_wellorder_segs *)
lemma compat_wellorder_segs_basic:
  "R1 \<in> compat_wellorders(E,S,p) \<Longrightarrow> R2 \<in> compat_wellorders(E,S,p) \<Longrightarrow>
   is_segment(R1,compat_wellorder_segs(E,S,p,R1,R2)) \<and>
   is_segment(R2,compat_wellorder_segs(E,S,p,R1,R2)) \<and>
   subrel(R1,compat_wellorder_segs(E,S,p,R1,R2)) = subrel(R2,compat_wellorder_segs(E,S,p,R1,R2))" by auto2
setup {* add_forward_prfstep_cond @{thm compat_wellorder_segs_basic}
  [with_term "compat_wellorder_segs(?E,?S,?p,?R1.0,?R2.0)"] *}

(* Condition for Zermelo's theorem *)
definition compat_wellorder_cond :: "[i, i, i] \<Rightarrow> o" where compat_wellorder_cond_def [rewrite]:
  "compat_wellorder_cond(E,S,p) \<longleftrightarrow> (S \<subseteq> Pow(E) \<and> p \<in> S \<rightarrow> E \<and> (\<forall>X\<in>S. p`X \<notin> X))"

lemma compat_wellorder_prop [forward]:
  "R1 \<in> compat_wellorders(E,S,p) \<Longrightarrow> R2 \<in> compat_wellorders(E,S,p) \<Longrightarrow>
   compat_wellorder_cond(E,S,p) \<Longrightarrow> is_segment_rel(R1,R2) \<or> is_segment_rel(R2,R1)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "V, V = compat_wellorder_segs(E,S,p,R1,R2)" THEN
    HAVE "V = source(R1) \<or> V = source(R2)" WITH (
      CHOOSE "x\<in>source(R1), V = less_interval(R1,x)" THEN
      CHOOSE "y\<in>source(R2), V = less_interval(R2,y)" THEN HAVE "x = y") THEN
    CASE "V = source(R1)") *})

lemma compat_wellorders_family [forward]:
  "compat_wellorder_cond(E,S,p) \<Longrightarrow> well_order_family(compat_wellorders(E,S,p))" by auto2
setup {* del_prfstep_thm @{thm compat_wellorder_prop} *}

definition compat_wellorder_rel :: "[i, i, i] \<Rightarrow> i" where compat_wellorder_rel_def [rewrite]:
  "compat_wellorder_rel(E,S,p) = union_rel(compat_wellorders(E,S,p))"

lemma compat_wellorders_step [backward2]:
  "compat_wellorder_cond(E,S,p) \<Longrightarrow> source(M) \<in> S \<Longrightarrow> M \<in> compat_wellorders(E,S,p) \<Longrightarrow>
   adjoin_greatest(M,p`source(M)) \<in> compat_wellorders(E,S,p)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "M', M' = adjoin_greatest(M,p`source(M))" THEN
    HAVE "well_order(M')" THEN
    HAVE "\<forall>x\<in>source(M'). less_interval(M',x) \<in> S \<and> p`(less_interval(M',x)) = x" WITH (
      CASE "x = p`source(M)" THEN HAVE "x \<in> source(M)" THEN
      HAVE "less_interval(M,x) = less_interval(M',x)")) *})

lemma compat_wellorders_rel_not_in [forward]:
  "compat_wellorder_cond(E,S,p) \<Longrightarrow> source(compat_wellorder_rel(E,S,p)) \<notin> S"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "M, M = compat_wellorder_rel(E,S,p)" THEN
    CHOOSE "a, a = p`source(M)" THEN
    CHOOSE "M', M' = adjoin_greatest(compat_wellorder_rel(E,S,p),a)" THEN
    HAVE "M' \<in> compat_wellorders(E,S,p)") *})

(* The final result *)
lemma compat_wellorders_cond_prop [resolve]:
  "compat_wellorder_cond(E,S,p) \<Longrightarrow>
   \<exists>\<Gamma>. well_order(\<Gamma>) \<and> (\<forall>x\<in>source(\<Gamma>). less_interval(\<Gamma>,x)\<in>S \<and> p`less_interval(\<Gamma>,x) = x) \<and>
       source(\<Gamma>) \<subseteq> E \<and> source(\<Gamma>) \<notin> S" by auto2

lemma compat_wellorders_cond_prop' [resolve]:
  "compat_wellorder_cond(E,S,p) \<Longrightarrow> \<exists>\<Gamma>. well_order(\<Gamma>) \<and> source(\<Gamma>) \<subseteq> E \<and> source(\<Gamma>) \<notin> S" by auto2
setup {* del_prfstep_thm @{thm compat_wellorders_rel_not_in} *}

(* Wellordering theorem *)
lemma wellorder_theorem:
  "\<exists>R. well_order(R) \<and> source(R) = E"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "S, S = Pow(E)-{E}" THEN
    CHOOSE "p, p = (\<lambda>X\<in>S. (SOME x\<in>E. x \<notin> X)\<in>E)" THEN
    HAVE "compat_wellorder_cond(E,S,p)" THEN
    CHOOSE "\<Gamma>, well_order(\<Gamma>) \<and> source(\<Gamma>) \<subseteq> E \<and> source(\<Gamma>) \<notin> S") *})

section {* Zorn's lemma *}  (* Bourbaki III.2.4 *)

definition inductive_order :: "i \<Rightarrow> o" where inductive_order_def [rewrite]:
  "inductive_order(R) \<longleftrightarrow> (order_rel(R) \<and>
    (\<forall>X. X \<subseteq> source(R) \<longrightarrow> linorder_rel(subrel(R,X)) \<longrightarrow> upper_bound(R,X) \<noteq> \<emptyset>))"
setup {* add_property_const @{term inductive_order} *}

lemma inductive_orderE1 [forward]: "inductive_order(R) \<Longrightarrow> order_rel(R)" by auto2
lemma inductive_orderE2 [backward]:
  "inductive_order(R) \<Longrightarrow> X \<subseteq> source(R) \<Longrightarrow> linorder_rel(subrel(R,X)) \<Longrightarrow> upper_bound(R,X) \<noteq> \<emptyset>" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm inductive_order_def} *}

lemma zorn_aux [resolve]:
  "order_rel(R) \<Longrightarrow> \<forall>X. X \<subseteq> source(R) \<longrightarrow> well_order(subrel(R,X)) \<longrightarrow> upper_bound(R,X) \<noteq> \<emptyset> \<Longrightarrow>
   \<exists>x. maximal(R,x)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "E, E = source(R)" THEN
    CHOOSE "S, S = {X\<in>Pow(source(R)). upper_bound(R,X) - X \<noteq> \<emptyset>}" THEN
    CHOOSE "p, p = (\<lambda>X\<in>S. (SOME x\<in>upper_bound(R,X). x \<notin> X)\<in>E)" THEN
    HAVE "p \<in> S \<rightarrow> E" THEN
    HAVE "\<forall>X\<in>S. p`X \<in> upper_bound(R,X)" THEN
    HAVE "compat_wellorder_cond(source(R),S,p)" THEN
    CHOOSE ("\<Gamma>, well_order(\<Gamma>) \<and> (\<forall>x\<in>source(\<Gamma>). less_interval(\<Gamma>,x)\<in>S \<and> p`less_interval(\<Gamma>,x) = x)" ^
            "\<and> source(\<Gamma>) \<subseteq> E \<and> source(\<Gamma>) \<notin> S") THEN
    CHOOSE "M, M = source(\<Gamma>)" THEN
    HAVE "\<Gamma> = subrel(R,M)" WITH (
      HAVE "\<forall>x\<in>M. \<forall>y\<in>M. x <\<^sub>\<Gamma> y \<longrightarrow> less(x,subrel(R,M),y)" WITH (
        HAVE "p`less_interval(\<Gamma>,y) = y")) THEN
    CHOOSE "x, x \<in> upper_bound(R,M)" THEN HAVE "maximal(R,x)") *})

lemma zorn [resolve]:
  "inductive_order(R) \<Longrightarrow> \<exists>x. maximal(R,x)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>X. X \<subseteq> source(R) \<longrightarrow> well_order(subrel(R,X)) \<longrightarrow> upper_bound(R,X) \<noteq> \<emptyset>") *})

lemma inductive_ge_interval:
  "inductive_order(R) \<Longrightarrow> a \<in> source(R) \<Longrightarrow> inductive_order(subrel(R,ge_interval(R,a)))"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "S, S = subrel(R,ge_interval(R,a))" THEN
    HAVE "\<forall>X. X \<subseteq> source(S) \<longrightarrow> linorder_rel(subrel(S,X)) \<longrightarrow> upper_bound(S,X) \<noteq> \<emptyset>" WITH (
      CASE "X = \<emptyset>" WITH HAVE "a \<in> upper_bound(S,X)" THEN
      HAVE "subrel(R,X) = subrel(S,X)" THEN
      CHOOSE "x, x \<in> upper_bound(R,X)" THEN
      CHOOSE "y, y \<in> X" THEN HAVE "x \<ge>\<^sub>R y" THEN
      HAVE "x \<in> upper_bound(S,X)")) *})
setup {* add_forward_prfstep_cond @{thm inductive_ge_interval} [with_term "subrel(?R,ge_interval(?R,?a))"] *}

lemma zorn_ge_elt:
  "inductive_order(R) \<Longrightarrow> a \<in> source(R) \<Longrightarrow> \<exists>x. x \<ge>\<^sub>R a \<and> maximal(R,x)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "inductive_order(subrel(R,ge_interval(R,a)))" THEN
    CHOOSE "x, maximal(subrel(R,ge_interval(R,a)),x)" THEN
    HAVE "maximal(R,x)") *})

lemma zorn_subsets:
  "F \<subseteq> Pow(E) \<Longrightarrow> \<forall>X. X \<subseteq> F \<longrightarrow> linorder_rel(subset_order(X)) \<longrightarrow> \<Union>X \<in> F \<Longrightarrow>
   \<exists>x. maximal(subset_order(F),x)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "R, R = subset_order(F)" THEN
    HAVE "inductive_order(R)" WITH (
      HAVE "\<forall>X. X \<subseteq> source(R) \<longrightarrow> linorder_rel(subrel(R,X)) \<longrightarrow> upper_bound(R,X) \<noteq> \<emptyset>" WITH (
        HAVE "\<Union>X \<in> upper_bound(R,X)"))) *})

end
