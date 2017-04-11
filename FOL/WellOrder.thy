theory WellOrder
imports Interval
begin

section {* Operation of adjoining a greatest element to an order *}
  
(* Abbreviated to ++ in this theory only *)
definition adjoin_greatest :: "[i, i] \<Rightarrow> i"  (infix "++" 55) where [rewrite]:
  "R ++ a = Order(carrier(R)\<union>{a}, \<lambda>x y. y = a \<or> x \<le>\<^sub>R y)"
setup {* register_wellform_data ("R ++ a", ["a \<notin> carrier(R)"]) *}
setup {* add_prfstep_check_req ("R ++ a", "a \<notin> carrier(R)") *}

lemma adjoin_greatest_type [typing]:
  "order(R) \<Longrightarrow> a \<notin> carrier(R) \<Longrightarrow> R ++ a \<in> raworder_space(carrier(R)\<union>{a})" by auto2

lemma adjoin_greatest_is_order:
  "order(R) \<Longrightarrow> a \<notin> carrier(R) \<Longrightarrow> order(R ++ a)" by auto2
setup {* add_forward_prfstep_cond @{thm adjoin_greatest_is_order} [with_term "?R ++ ?a"] *}

lemma adjoin_greatest_eval1:
  "x \<in> carrier(R)\<union>{a} \<Longrightarrow> S = R ++ a \<Longrightarrow> x \<le>\<^sub>S a" by auto2
setup {* add_forward_prfstep_cond @{thm adjoin_greatest_eval1} [with_term "?R ++ ?a"] *}

lemma adjoin_greatest_eval2:
  "order(R) \<Longrightarrow> a \<notin> carrier(R) \<Longrightarrow> S = R ++ a \<Longrightarrow> x \<in>. R \<Longrightarrow> \<not>a \<le>\<^sub>S x" by auto2
setup {* add_forward_prfstep_cond @{thm adjoin_greatest_eval2} [with_term "?R ++ ?a"] *}

lemma adjoin_greatest_eval3 [rewrite]:
  "a \<notin> carrier(R) \<Longrightarrow> S = R ++ a \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x \<le>\<^sub>S y \<longleftrightarrow> x \<le>\<^sub>R y" by auto2
setup {* del_prfstep_thm @{thm adjoin_greatest_def} *}

lemma adjoin_greatest_restrict [rewrite]:
  "ord_form(R) \<Longrightarrow> order(R) \<Longrightarrow> a \<notin> carrier(R) \<Longrightarrow> suborder(R ++ a,carrier(R)) = R" by auto2

lemma adjoin_greatest_prop:
  "order(R) \<Longrightarrow> a \<notin> carrier(R) \<Longrightarrow>
   has_greatest(R ++ a,carrier(R)\<union>{a}) \<and> greatest(R ++ a,carrier(R)\<union>{a}) = a" by auto2

lemma adjoin_greatest_unique [backward]:
  "order(R) \<Longrightarrow> ord_form(S) \<Longrightarrow> order(S) \<Longrightarrow> a \<notin> carrier(R) \<Longrightarrow> carrier(S) = carrier(R) \<union> {a} \<Longrightarrow>
   \<forall>x\<in>.S. x \<le>\<^sub>S a \<Longrightarrow> suborder(S,carrier(R)) = R \<Longrightarrow> S = R ++ a" by auto2

lemma linorder_adjoin:
  "linorder(R) \<Longrightarrow> a \<notin> carrier(R) \<Longrightarrow> linorder(R ++ a)" by auto2
setup {* add_forward_prfstep_cond @{thm linorder_adjoin} [with_term "?R ++ ?a"] *}

lemma adjoin_greatest_less_interval [rewrite]:
  "linorder(M) \<Longrightarrow> a \<notin> carrier(M) \<Longrightarrow> less_interval(M ++ a,a) = carrier(M)" by auto2

lemma adjoin_greatest_less_interval2 [rewrite]:
  "linorder(M) \<Longrightarrow> a \<notin> carrier(M) \<Longrightarrow> x \<in>. M \<Longrightarrow> less_interval(M ++ a,x) = less_interval(M,x)" by auto2

section {* Well-ordered sets *}  (* Bourbaki III.2.1 *)

(* Definition of well_order *)
definition well_order :: "i \<Rightarrow> o" where [rewrite]:
  "well_order(R) \<longleftrightarrow> (linorder(R) \<and> (\<forall>X. X \<subseteq> carrier(R) \<longrightarrow> X \<noteq> \<emptyset> \<longrightarrow> has_least(R,X)))"
setup {* add_property_const @{term well_order} *}

lemma well_orderD1 [forward]: "well_order(R) \<Longrightarrow> linorder(R)" by auto2
lemma well_orderD2 [forward, backward]:
  "well_order(R) \<Longrightarrow> X \<subseteq> carrier(R) \<Longrightarrow> X \<noteq> \<emptyset> \<Longrightarrow> has_least(R,X)" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm well_order_def} *}

lemma wellorder_iso [forward]:
  "well_order(R) \<Longrightarrow> ord_isomorphic(R,S) \<Longrightarrow> well_order(S)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "f, f \<in> R \<cong>\<^sub>O S" THEN
    HAVE "\<forall>X. X \<subseteq> carrier(S) \<longrightarrow> X \<noteq> \<emptyset> \<longrightarrow> has_least(S,X)" WITH (
      LET "U = f -`` X" THEN
      HAVE "has_least(R,U)" THEN
      HAVE "has_least(S,X) \<and> least(S,X) = f ` least(R,U)")) *})

lemma well_order_suborder:
  "well_order(R) \<Longrightarrow> linorder(A) \<Longrightarrow> is_suborder(A,R) \<Longrightarrow> well_order(A)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>X. X \<subseteq> carrier(A) \<longrightarrow> X \<noteq> \<emptyset> \<longrightarrow> has_least(A,X)" WITH (
      HAVE "has_least(A,X) \<and> least(A,X) = least(R,X)")) *})

lemma well_order_adjoin [resolve]:
  "well_order(R) \<Longrightarrow> a \<notin> carrier(R) \<Longrightarrow> well_order(R ++ a)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>X. X \<subseteq> carrier(R)\<union>{a} \<longrightarrow> X \<noteq> \<emptyset> \<longrightarrow> has_least(R ++ a,X)" WITH (
      HAVE "has_least(R,X\<midarrow>{a})" THEN
      HAVE "has_least(R ++ a, X\<midarrow>{a}) \<and> least(R ++ a, X\<midarrow>{a}) = least(R, X\<midarrow>{a})")) *})

(* Segments. Correspond to less_intervals for well_order. The main result in
   this portion is that if R is well-ordered, the set of segments of R is well-ordered,
   and ord_isomorphic to R adjoining a greatest element. *)
definition is_segment :: "[i, i] \<Rightarrow> o" where [rewrite]:
  "is_segment(R,S) \<longleftrightarrow> (S \<subseteq> carrier(R) \<and> (\<forall>x\<in>S. \<forall>y\<in>.R. y \<le>\<^sub>R x \<longrightarrow> y \<in> S))"

lemma is_segmentD [forward]:
  "is_segment(R,S) \<Longrightarrow> S \<subseteq> carrier(R)"
  "is_segment(R,S) \<Longrightarrow> x \<in> S \<Longrightarrow> \<forall>y\<in>.R. y \<le>\<^sub>R x \<longrightarrow> y \<in> S" by auto2+
setup {* del_prfstep_thm_str "@eqforward" @{thm is_segment_def} *}

lemma segment_is_interval [backward2]:
  "well_order(R) \<Longrightarrow> is_segment(R,S) \<Longrightarrow> S \<noteq> carrier(R) \<Longrightarrow> \<exists>a\<in>.R. S = less_interval(R,a)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "has_least(R,carrier(R)\<midarrow>S)" THEN
    HAVE "least(R,carrier(R)\<midarrow>S) \<in>. R" THEN
    HAVE "carrier(R)\<midarrow>S = ge_interval(R,least(R,carrier(R)\<midarrow>S))") *})

lemma interval_is_segment [resolve]:
  "order(R) \<Longrightarrow> is_segment(R,less_interval(R,a))" by auto2

definition segments :: "i \<Rightarrow> i" where [rewrite]:
  "segments(R) = {S \<in> Pow(carrier(R)). is_segment(R,S)}"

definition pt_to_segment_fun :: "i \<Rightarrow> i" where [rewrite]:
  "pt_to_segment_fun(R) = Mor(R,subset_order(segments(R)),\<lambda>a. less_interval(R,a))"

lemma pt_to_segment_fun_is_fun [typing]:
  "well_order(R) \<Longrightarrow> pt_to_segment_fun(R) \<in> R \<rightharpoonup> subset_order(segments(R))" by auto2

lemma pt_to_segment_eval [rewrite]:
  "well_order(R) \<Longrightarrow> a \<in> source(pt_to_segment_fun(R)) \<Longrightarrow>
   pt_to_segment_fun(R) ` a = less_interval(R,a)" by auto2
setup {* del_prfstep_thm @{thm pt_to_segment_fun_def} *}

lemma pt_to_segment_fun_inj [forward]:
  "well_order(R) \<Longrightarrow> injective(pt_to_segment_fun(R))" by auto2

lemma pt_to_segment_fun_incr [forward]:
  "well_order(R) \<Longrightarrow> incr(pt_to_segment_fun(R))" by auto2
setup {* add_forward_prfstep_cond @{thm pt_to_segment_fun_incr} [with_term "pt_to_segment_fun(?R)"] *}

lemma pt_to_segment_fun_image [rewrite]:
  "well_order(R) \<Longrightarrow> image(pt_to_segment_fun(R)) = segments(R) \<midarrow> {carrier(R)}"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>S\<in>segments(R) \<midarrow> {carrier(R)}. S \<in> image(pt_to_segment_fun(R))" WITH (
      CHOOSE "a\<in>.R, S = less_interval(R,a)" THEN
      HAVE "S = pt_to_segment_fun(R) ` a")) *})

lemma pt_to_segment_fun_iso:
  "well_order(R) \<Longrightarrow> S = subset_order(segments(R)\<midarrow>{carrier(R)}) \<Longrightarrow> well_order(S)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "mor_restrict_image_ord(pt_to_segment_fun(R)) \<in> R \<cong>\<^sub>O S") *})
setup {* add_forward_prfstep_cond @{thm pt_to_segment_fun_iso} [with_term "?S"] *}

lemma segments_order [rewrite_back]:
  "well_order(R) \<Longrightarrow> subset_order(segments(R)) = subset_order(segments(R)\<midarrow>{carrier(R)}) ++ carrier(R)" by auto2

lemma segments_wellorder:
  "well_order(R) \<Longrightarrow> well_order(subset_order(segments(R)))"
  by (tactic {* auto2s_tac @{context} (
    HAVE "subset_order(segments(R)) = subset_order(segments(R)\<midarrow>{carrier(R)}) ++ carrier(R)") *})

(* Families of well-ordered sets *)
definition is_segment_rel :: "[i, i] \<Rightarrow> o" where [rewrite]:
  "is_segment_rel(R,S) \<longleftrightarrow> (is_suborder(R,S) \<and> is_segment(S,carrier(R)))"

definition well_order_family :: "i \<Rightarrow> o" where [rewrite]:
  "well_order_family(X) \<longleftrightarrow> ((\<forall>R\<in>X. well_order(R)) \<and>
    (\<forall>R\<in>X. \<forall>S\<in>X. is_segment_rel(R,S) \<or> is_segment_rel(S,R)))"
setup {* add_property_const @{term well_order_family} *}

lemma well_order_familyD [forward]:
  "well_order_family(X) \<Longrightarrow> R \<in> X \<Longrightarrow> well_order(R)"
  "well_order_family(X) \<Longrightarrow> \<not>is_segment_rel(R,S) \<Longrightarrow> R \<in> X \<Longrightarrow> S \<in> X \<Longrightarrow> is_segment_rel(S,R)" by auto2+
setup {* del_prfstep_thm_str "@eqforward" @{thm well_order_family_def} *}

lemma well_order_familyD' [backward]:
  "well_order_family(X) \<Longrightarrow> R \<in> X \<Longrightarrow> y \<in> union_src(X) \<Longrightarrow> \<exists>S\<in>X. y \<in>. S \<and> is_segment_rel(R,S)"
  by auto2

lemma well_order_family_directed [forward]:
  "well_order_family(X) \<Longrightarrow> directed_rels(X)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>R\<in>X. \<forall>S\<in>X. \<exists>T\<in>X. is_suborder(R,T) \<and> is_suborder(S,T)" WITH (
      CASE "is_segment_rel(R,S)")) *})

lemma is_segment_union [backward]:
  "well_order_family(X) \<Longrightarrow> R \<in> X \<Longrightarrow> U = union_rel(X) \<Longrightarrow> is_segment_rel(R,U)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x\<in>.R. \<forall>y\<in>union_src(X). y \<le>\<^sub>U x \<longrightarrow> y \<in>. R" WITH (
      CHOOSE "S\<in>X, y \<in>. S \<and> is_segment_rel(R,S)")) *})

lemma well_order_family_union_prop [forward]:
  "well_order_family(X) \<Longrightarrow> well_order(union_rel(X))"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>H. H \<subseteq> union_src(X) \<longrightarrow> H \<noteq> \<emptyset> \<longrightarrow> has_least(union_rel(X),H)" WITH (
      CHOOSE "R\<in>X, H \<inter> carrier(R) \<noteq> \<emptyset>" WITH (
        CHOOSE "x, x \<in> H" THEN CHOOSE "S\<in>X, x \<in>. S") THEN
      HAVE "has_least(R, H \<inter> carrier(R))" THEN
      LET "m = least(R, H \<inter> carrier(R))" THEN
      HAVE "has_least(union_rel(X),H) \<and> least(union_rel(X),H) = m" WITH (
        HAVE "\<forall>x\<in>H. ge(x,union_rel(X),m)" WITH (
          CASE "x \<in>. R" WITH HAVE "x \<in> H \<inter> carrier(R)" THEN
          CHOOSE "S\<in>X, x \<in>. S \<and> is_segment_rel(R,S)")))) *})

lemma well_order_family_segments [rewrite]:
  "well_order_family(X) \<Longrightarrow> x \<in>. R \<Longrightarrow> R \<in> X \<Longrightarrow> less_interval(R,x) = less_interval(union_rel(X),x)"
  by (tactic {* auto2s_tac @{context} (HAVE "is_segment_rel(R,union_rel(X))") *})

lemma well_order_family_segments2:
  "well_order_family(X) \<Longrightarrow> is_segment(union_rel(X),S) \<Longrightarrow> S \<noteq> union_src(X) \<Longrightarrow>
   \<exists>R\<in>X. is_segment(R,S)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "x\<in>union_src(X), S = less_interval(union_rel(X),x)" THEN
    CHOOSE "R\<in>X, x \<in>. R" THEN
    HAVE "less_interval(R,x) = less_interval(union_rel(X),x)") *})

section {* Zermelo's Theorem *}  (* Bourbaki III.2.3 *)

(* Set of relations on subsets of E. *)
definition suborder_space :: "i \<Rightarrow> i" where [rewrite]:
  "suborder_space(E) = (\<Union>X\<in>Pow(E). raworder_space(X))"

lemma suborder_space_iff [rewrite]:
  "R \<in> suborder_space(E) \<longleftrightarrow> (ord_form(R) \<and> raworder(R) \<and> carrier(R) \<subseteq> E)" by auto2
setup {* del_prfstep_thm @{thm suborder_space_def} *}

(* Given a set E, a collection S of subsets of E, and a map p from S to E such
   that p(X) \<notin> X for all X \<in> S, define collection of compatible well-ordering
   on subsets of E. *)
definition compat_wellorders :: "[i, i, i] \<Rightarrow> i" where [rewrite]:
  "compat_wellorders(E,S,p) = {R\<in>suborder_space(E).
    well_order(R) \<and> (\<forall>x\<in>.R. less_interval(R,x) \<in> S \<and> p`(less_interval(R,x)) = x)}"

lemma compat_wellordersD:
  "R \<in> compat_wellorders(E,S,p) \<Longrightarrow> well_order(R) \<and> carrier(R) \<subseteq> E"
  "x \<in>. R \<Longrightarrow> R \<in> compat_wellorders(E,S,p) \<Longrightarrow> less_interval(R,x) \<in> S"
  "x \<in>. R \<Longrightarrow> R \<in> compat_wellorders(E,S,p) \<Longrightarrow> p`(less_interval(R,x)) = x" by auto2+
setup {* fold add_forward_prfstep @{thms compat_wellordersD(1-2)} *}
setup {* add_rewrite_rule @{thm compat_wellordersD(3)} *}

lemma compat_wellordersI [backward]:
  "ord_form(R) \<Longrightarrow> well_order(R) \<Longrightarrow> carrier(R) \<subseteq> E \<Longrightarrow>
   \<forall>x\<in>.R. less_interval(R,x) \<in> S \<and> p`(less_interval(R,x)) = x \<Longrightarrow>
   R \<in> compat_wellorders(E,S,p)" by auto2
setup {* del_prfstep_thm @{thm compat_wellorders_def} *}

lemma less_interval_rel_is_segment:
  "well_order(R) \<Longrightarrow> is_segment_rel(less_interval_rel(R,x),R)" by auto2
setup {* add_forward_prfstep_cond @{thm less_interval_rel_is_segment}
  [with_term "less_interval_rel(?R,?x)"] *}

definition compat_wellorder_segs :: "[i, i, i, i, i] \<Rightarrow> i" where [rewrite]:
  "compat_wellorder_segs(E,S,p,R1,R2) =
    {x\<in>carrier(R1)\<inter>carrier(R2). less_interval_rel(R1,x) = less_interval_rel(R2,x)}"
setup {* register_wellform_data ("compat_wellorder_segs(E,S,p,R1,R2)",
  ["R1 \<in> compat_wellorders(E,S,p)", "R2 \<in> compat_wellorders(E,S,p)"]) *}

(* Basic properties of compat_wellorder_segs *)
lemma compat_wellorder_segs_basic:
  "R1 \<in> compat_wellorders(E,S,p) \<Longrightarrow> R2 \<in> compat_wellorders(E,S,p) \<Longrightarrow>
   is_segment(R1,compat_wellorder_segs(E,S,p,R1,R2)) \<and>
   is_segment(R2,compat_wellorder_segs(E,S,p,R1,R2)) \<and>
   suborder(R1,compat_wellorder_segs(E,S,p,R1,R2)) = suborder(R2,compat_wellorder_segs(E,S,p,R1,R2))" by auto2
setup {* add_forward_prfstep_cond @{thm compat_wellorder_segs_basic}
  [with_term "compat_wellorder_segs(?E,?S,?p,?R1.0,?R2.0)"] *}

(* Condition for Zermelo's theorem *)
definition compat_wellorder_cond :: "[i, i, i] \<Rightarrow> o" where [rewrite]:
  "compat_wellorder_cond(E,S,p) \<longleftrightarrow> (S \<subseteq> Pow(E) \<and> p \<in> S \<rightarrow> E \<and> (\<forall>X\<in>S. p`X \<notin> X))"

lemma compat_wellorder_prop [forward]:
  "R1 \<in> compat_wellorders(E,S,p) \<Longrightarrow> R2 \<in> compat_wellorders(E,S,p) \<Longrightarrow>
   compat_wellorder_cond(E,S,p) \<Longrightarrow> is_segment_rel(R1,R2) \<or> is_segment_rel(R2,R1)"
  by (tactic {* auto2s_tac @{context} (
    LET "V = compat_wellorder_segs(E,S,p,R1,R2)" THEN
    HAVE "V = carrier(R1) \<or> V = carrier(R2)" WITH (
      CHOOSE "x\<in>.R1, V = less_interval(R1,x)" THEN
      CHOOSE "y\<in>.R2, V = less_interval(R2,y)" THEN HAVE "x = y") THEN
    CASE "V = carrier(R1)") *})

lemma compat_wellorders_family [forward]:
  "compat_wellorder_cond(E,S,p) \<Longrightarrow> well_order_family(compat_wellorders(E,S,p))" by auto2
setup {* del_prfstep_thm @{thm compat_wellorder_prop} *}

definition compat_wellorder :: "[i, i, i] \<Rightarrow> i" where [rewrite]:
  "compat_wellorder(E,S,p) = union_rel(compat_wellorders(E,S,p))"

lemma compat_wellorders_step [backward2]:
  "compat_wellorder_cond(E,S,p) \<Longrightarrow> carrier(M) \<in> S \<Longrightarrow> M \<in> compat_wellorders(E,S,p) \<Longrightarrow>
   M' = M ++ p`carrier(M) \<Longrightarrow> M' \<in> compat_wellorders(E,S,p)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "well_order(M')" THEN
    HAVE "\<forall>x\<in>.M'. less_interval(M',x) \<in> S \<and> p`(less_interval(M',x)) = x" WITH (
      CASE "x = p`carrier(M)" THEN HAVE "x \<in>. M" THEN
      HAVE "less_interval(M,x) = less_interval(M',x)")) *})

lemma compat_wellorders_rel_not_in [forward]:
  "compat_wellorder_cond(E,S,p) \<Longrightarrow> M = compat_wellorder(E,S,p) \<Longrightarrow> carrier(M) \<notin> S"
  by (tactic {* auto2s_tac @{context} (
    LET "a = p`carrier(M)" THEN
    LET "M' = compat_wellorder(E,S,p) ++ a" THEN
    HAVE "M' \<in> compat_wellorders(E,S,p)") *})

(* The final result *)
lemma compat_wellorders_cond_prop [resolve]:
  "compat_wellorder_cond(E,S,p) \<Longrightarrow>
   \<exists>\<Gamma>. ord_form(\<Gamma>) \<and> well_order(\<Gamma>) \<and> (\<forall>x\<in>.\<Gamma>. less_interval(\<Gamma>,x)\<in>S \<and> p`less_interval(\<Gamma>,x) = x) \<and>
       carrier(\<Gamma>) \<subseteq> E \<and> carrier(\<Gamma>) \<notin> S" by auto2

lemma compat_wellorders_cond_prop' [resolve]:
  "compat_wellorder_cond(E,S,p) \<Longrightarrow>
   \<exists>\<Gamma>. ord_form(\<Gamma>) \<and> well_order(\<Gamma>) \<and> carrier(\<Gamma>) \<subseteq> E \<and> carrier(\<Gamma>) \<notin> S" by auto2
setup {* del_prfstep_thm @{thm compat_wellorders_rel_not_in} *}

(* Wellordering theorem *)
lemma wellorder_theorem:
  "\<exists>R. ord_form(R) \<and> well_order(R) \<and> carrier(R) = E"
  by (tactic {* auto2s_tac @{context} (
    LET "S = Pow(E)\<midarrow>{E}" THEN
    LET "p = (\<lambda>X\<in>S. (SOME x\<in>E. x \<notin> X)\<in>E)" THEN
    HAVE "compat_wellorder_cond(E,S,p)" THEN
    CHOOSE "\<Gamma>, ord_form(\<Gamma>) \<and> well_order(\<Gamma>) \<and> carrier(\<Gamma>) \<subseteq> E \<and> carrier(\<Gamma>) \<notin> S") *})

no_notation adjoin_greatest (infix "++" 55)

section {* Zorn's lemma *}  (* Bourbaki III.2.4 *)

definition inductive_order :: "i \<Rightarrow> o" where [rewrite]:
  "inductive_order(R) \<longleftrightarrow> (order(R) \<and>
    (\<forall>X. X \<subseteq> carrier(R) \<longrightarrow> linorder(suborder(R,X)) \<longrightarrow> upper_bound(R,X) \<noteq> \<emptyset>))"
setup {* add_property_const @{term inductive_order} *}

lemma inductive_orderE1 [forward]: "inductive_order(R) \<Longrightarrow> order(R)" by auto2
lemma inductive_orderE2 [backward]:
  "inductive_order(R) \<Longrightarrow> X \<subseteq> carrier(R) \<Longrightarrow> linorder(suborder(R,X)) \<Longrightarrow> upper_bound(R,X) \<noteq> \<emptyset>" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm inductive_order_def} *}

lemma zorn_aux [resolve]:
  "order(R) \<Longrightarrow> \<forall>X. X \<subseteq> carrier(R) \<longrightarrow> well_order(suborder(R,X)) \<longrightarrow> upper_bound(R,X) \<noteq> \<emptyset> \<Longrightarrow>
   \<exists>x. maximal(R,x)"
  by (tactic {* auto2s_tac @{context} (
    LET "E = carrier(R)" THEN
    LET "S = {X\<in>Pow(carrier(R)). upper_bound(R,X) \<midarrow> X \<noteq> \<emptyset>}" THEN
    LET "p = (\<lambda>X\<in>S. (SOME x\<in>upper_bound(R,X). x \<notin> X)\<in>E)" THEN
    HAVE "p \<in> S \<rightarrow> E" THEN
    HAVE "\<forall>X\<in>S. p`X \<in> upper_bound(R,X)" THEN
    HAVE "compat_wellorder_cond(carrier(R),S,p)" THEN
    CHOOSE ("\<Gamma>, ord_form(\<Gamma>) \<and> well_order(\<Gamma>) \<and> (\<forall>x\<in>.\<Gamma>. less_interval(\<Gamma>,x)\<in>S \<and> p`less_interval(\<Gamma>,x) = x)" ^
            "\<and> carrier(\<Gamma>) \<subseteq> E \<and> carrier(\<Gamma>) \<notin> S") THEN
    LET "M = carrier(\<Gamma>)" THEN
    HAVE "\<Gamma> = suborder(R,M)" WITH (
      HAVE "\<forall>x\<in>M. \<forall>y\<in>M. x <\<^sub>\<Gamma> y \<longrightarrow> less(suborder(R,M),x,y)" WITH (
        HAVE "p`less_interval(\<Gamma>,y) = y")) THEN
    CHOOSE "x, x \<in> upper_bound(R,M)" THEN HAVE "maximal(R,x)") *})

lemma zorn [resolve]:
  "inductive_order(R) \<Longrightarrow> \<exists>x. maximal(R,x)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>X. X \<subseteq> carrier(R) \<longrightarrow> well_order(suborder(R,X)) \<longrightarrow> upper_bound(R,X) \<noteq> \<emptyset>") *})

lemma inductive_ge_interval:
  "inductive_order(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> S = suborder(R,ge_interval(R,a)) \<Longrightarrow> inductive_order(S)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>X. X \<subseteq> carrier(S) \<longrightarrow> linorder(suborder(S,X)) \<longrightarrow> upper_bound(S,X) \<noteq> \<emptyset>" WITH (
      CASE "X = \<emptyset>" WITH HAVE "a \<in> upper_bound(S,X)" THEN
      HAVE "suborder(R,X) = suborder(S,X)" THEN
      CHOOSE "x, x \<in> upper_bound(R,X)" THEN
      CHOOSE "y, y \<in> X" THEN HAVE "x \<ge>\<^sub>R y" THEN
      HAVE "x \<in> upper_bound(S,X)")) *})
setup {* add_forward_prfstep_cond @{thm inductive_ge_interval} [with_term "?S"] *}

lemma zorn_ge_elt: "inductive_order(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> \<exists>x. x \<ge>\<^sub>R a \<and> maximal(R,x)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "inductive_order(suborder(R,ge_interval(R,a)))" THEN
    CHOOSE "x, maximal(suborder(R,ge_interval(R,a)),x)" THEN
    HAVE "maximal(R,x)") *})

lemma zorn_subsets:
  "F \<subseteq> Pow(E) \<Longrightarrow> R = subset_order(F) \<Longrightarrow>
   \<forall>X. X \<subseteq> F \<longrightarrow> linorder(subset_order(X)) \<longrightarrow> \<Union>X \<in> F \<Longrightarrow> \<exists>x. maximal(R,x)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "inductive_order(R)" WITH (
      HAVE "\<forall>X. X \<subseteq> carrier(R) \<longrightarrow> linorder(suborder(R,X)) \<longrightarrow> upper_bound(R,X) \<noteq> \<emptyset>" WITH (
        HAVE "\<Union>X \<in> upper_bound(R,X)"))) *})

end
