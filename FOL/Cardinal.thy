(* Based on OrderType and Cardinal in Isabelle/ZF. *)

theory Cardinal
  imports Finite WellOrder
begin

section \<open>Least ordinal satisfying a property\<close>

(* Least ordinal satisfying property P. *)
definition least_ord :: "(i \<Rightarrow> o) \<Rightarrow> i"  (binder "\<mu> " 10) where [rewrite]:
  "(\<mu> i. P(i)) = (THE i. ord(i) \<and> P(i) \<and> (\<forall>j\<in>i. \<not>P(j)))"

(* Show the definition of least_ord make sense. *)
lemma least_ord_eq [backward]:
  "P(i) \<Longrightarrow> ord(i) \<Longrightarrow> \<forall>x\<in>i. \<not>P(x) \<Longrightarrow> (\<mu> i. P(i)) = i"
@proof
  @have "\<forall>j. P(j) \<longrightarrow> ord(j) \<longrightarrow> (\<forall>y\<in>j. \<not>P(y)) \<longrightarrow> j = i" @with
    @have (@rule) "i \<in> j \<or> i = j \<or> j \<in> i"
  @end
@qed

definition le_ord :: "i \<Rightarrow> i \<Rightarrow> o"  (infix "\<le>\<^sub>O" 50) where [rewrite]:
  "i \<le>\<^sub>O j \<longleftrightarrow> (i \<in> j \<or> i = j)"

lemma least_ord_le [backward]:
  "P(i) \<Longrightarrow> ord(i) \<Longrightarrow> (\<mu> i. P(i)) \<le>\<^sub>O i"
@proof
  @have "\<forall>x. ord(x) \<longrightarrow> (\<forall>y\<in>x. P(y) \<longrightarrow> (\<mu> i. P(i)) \<in> y) \<longrightarrow> P(x) \<longrightarrow> (\<mu> i. P(i)) \<le>\<^sub>O x" @with
    @contradiction
    @have "(\<mu> i. P(i)) = x"
  @end
  @induct "ord(i)" "P(i) \<longrightarrow> (\<mu> i. P(i)) \<le>\<^sub>O i"
@qed

lemma least_ord_prop:
  "ord(i) \<Longrightarrow> P(i) \<Longrightarrow> P(\<mu> i. P(i))"
@proof
  @have "\<forall>x. ord(x) \<longrightarrow> (\<forall>y\<in>x. P(y) \<longrightarrow> P(\<mu> i. P(i))) \<longrightarrow> P(x) \<longrightarrow> P(\<mu> i. P(i))" @with
    @contradiction
    @have "(\<mu> i. P(i)) = x"
  @end
  @induct "ord(i)" "P(i) \<longrightarrow> P(\<mu> i. P(i))"
@qed
setup {* add_forward_prfstep_cond @{thm least_ord_prop} [with_term "\<mu> i. ?P(i)"] *}

lemma ord_least_is_ord [backward]:
  "\<exists>i. ord(i) \<and> P(i) \<Longrightarrow> ord(\<mu> i. P(i))"
@proof
  @obtain i where "ord(i)" "P(i)"
  @have "(\<mu> i. P(i)) \<le>\<^sub>O i"
@qed

section \<open>Order type and order map\<close>

(* In this section, we construct an ordinal from any well-ordering on a set. *)

definition Tup_image :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "Tup_image(f,S) = {f`x. x \<in> S}"

(* Order map: given a well-founded relation r, and an element x in source(r),
   construct the ordinal corresponding to x. This is simply the collection
   of ordermap(r,y), where y < x under r.
*)
definition ordermap :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "ordermap(r,x) = wfrec(r, \<lambda>x f. Tup_image(f,ord_pred(r,x)), x)"

lemma ordermap_eq [rewrite]:
  "wf(r) \<Longrightarrow> x \<in>. r \<Longrightarrow> ordermap(r,x) = {ordermap(r,y). y \<in> ord_pred(r,x)}" by auto2
setup {* del_prfstep_thm @{thm ordermap_def} *}

lemma ord_ordermap:
  "wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> x \<in>. r \<Longrightarrow> ord(ordermap(r,x))" by auto2
setup {* add_forward_prfstep_cond @{thm ord_ordermap} [with_term "ordermap(?r,?x)"] *}

(* The image of ordermap. *)
definition ordertype :: "i \<Rightarrow> i" where [rewrite]:
  "ordertype(r) = {ordermap(r,x). x \<in>. r}"

lemma ord_ordertype [forward]:
  "wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> ord(ordertype(r))" by auto2

definition ordermap_fun :: "i \<Rightarrow> i" where [rewrite]:
  "ordermap_fun(r) = Fun(carrier(r),ordertype(r), \<lambda>x. ordermap(r,x))"

lemma ordermap_fun_type [typing]:
  "ordermap_fun(r) \<in> carrier(r) \<rightarrow> ordertype(r)" by auto2

lemma ordermap_fun_eval [rewrite]:
  "x \<in> source(ordermap_fun(r)) \<Longrightarrow> ordermap_fun(r)`x = ordermap(r,x)" by auto2
setup {* del_prfstep_thm @{thm ordermap_fun_def} *}

lemma ordermap_inj [forward]:
  "well_order(r) \<Longrightarrow> injective(ordermap_fun(r))"
@proof
  @let "f = ordermap_fun(r)"
  @have "\<forall>x\<in>.r. \<forall>y\<in>.r. x \<noteq> y \<longrightarrow> f`x \<noteq> f`y" @with
    @case "x \<le>\<^sub>r y" @with
      @have "ordermap(r,x) \<in> ordermap(r,y)"
    @end
    @case "y \<le>\<^sub>r x" @with
      @have "ordermap(r,y) \<in> ordermap(r,x)"
    @end
  @end
@qed

lemma ordermap_bij [forward]:
  "well_order(r) \<Longrightarrow> bijective(ordermap_fun(r))"
  by auto2

section \<open>Cardinals\<close>

definition cardinal :: "i \<Rightarrow> i" where [rewrite]:
  "cardinal(A) = (\<mu> i. equipotent(i,A))"

definition card :: "i \<Rightarrow> o" where [rewrite]:
  "card(i) \<longleftrightarrow> (i = cardinal(i))"
setup {* add_property_const @{term card} *}

section \<open>Basic properties of cardinals\<close>

(* Without assuming axiom of choice *)
lemma cardinal_equipotent_gen [resolve]:
  "well_order(r) \<Longrightarrow> A = carrier(r) \<Longrightarrow> equipotent(A,cardinal(A))"
@proof
  @let "i = ordertype(r)"
  @have "equipotent(A,i)" @with
    @have "ordermap_fun(r) \<in> A \<cong> ordertype(r)"
  @end
@qed

lemma card_is_ordinal_gen [forward]:
  "well_order(r) \<Longrightarrow> A = carrier(r) \<Longrightarrow> ord(cardinal(A))"
@proof
  @let "i = ordertype(r)"
  @have "equipotent(A,i)" @with
    @have "ordermap_fun(r) \<in> A \<cong> ordertype(r)"
  @end
@qed

lemma cardinal_cong_gen [resolve]:
  "well_order(r) \<Longrightarrow> well_order(s) \<Longrightarrow> A = carrier(r) \<Longrightarrow> B = carrier(s) \<Longrightarrow>
   equipotent(A,B) \<Longrightarrow> cardinal(A) = cardinal(B)"
@proof
  @have "equipotent(A,cardinal(A))"
  @have "equipotent(B,cardinal(B))"
  @have "cardinal(A) \<le>\<^sub>O cardinal(B)"
  @have "cardinal(B) \<le>\<^sub>O cardinal(A)"
@qed

(* With axiom of choice. Will make this assumption from now on. *)
lemma cardinal_equipotent [resolve]:
  "equipotent(A,cardinal(A))"
@proof
  @obtain "R\<in>raworder_space(A)" where "well_order(R)"
@qed

lemma card_is_ordinal [forward]:
  "ord(cardinal(A))"
@proof
  @obtain "R\<in>raworder_space(A)" where "well_order(R)"
@qed

lemma cardinal_cong [resolve]:
  "equipotent(A,B) \<Longrightarrow> cardinal(A) = cardinal(B)"
@proof
  @obtain "R\<in>raworder_space(A)" where "well_order(R)"
  @obtain "S\<in>raworder_space(B)" where "well_order(S)"
@qed

lemma card_is_cardinal [forward]:
  "card(cardinal(A))"
@proof @have "equipotent(A,cardinal(A))" @qed

section \<open>Ordering on cardinality\<close>

definition le_potent :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "le_potent(S,T) \<longleftrightarrow> (\<exists>f\<in>S\<rightarrow>T. injective(f))"

lemma le_potentI [resolve]: "injective(f) \<Longrightarrow> f \<in> A \<rightarrow> B \<Longrightarrow> le_potent(A,B)" by auto2
lemma le_potentE [resolve]: "le_potent(S,T) \<Longrightarrow> \<exists>f\<in>S\<rightarrow>T. injective(f)" by auto2
setup {* del_prfstep_thm @{thm le_potent_def} *}

definition less_potent :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "less_potent(S,T) \<longleftrightarrow> le_potent(S,T) \<and> \<not>equipotent(S,T)"

lemma le_potent_trans [forward]:
  "equipotent(A,B) \<Longrightarrow> le_potent(B,C) \<Longrightarrow> le_potent(A,C)"
@proof
  @obtain "f \<in> A \<cong> B"
  @obtain "g \<in> B \<rightarrow> C" where "injective(g)"
  @let "h = g \<circ> f"
  @have "h \<in> A \<rightarrow> C" @have "injective(h)"
@qed

lemma schroeder_bernstein_potent [forward]:
  "le_potent(S,T) \<Longrightarrow> le_potent(T,S) \<Longrightarrow> equipotent(S,T)"
@proof
  @obtain "f\<in>S\<rightarrow>T" where "injective(f)"
  @obtain "g\<in>T\<rightarrow>S" where "injective(g)"
@qed

lemma subset_le_potent [resolve]:
  "S \<subseteq> T \<Longrightarrow> le_potent(S,T)"
@proof
  @let "f = Fun(S,T,\<lambda>x. x)"
  @have "injective(f)" @have "f \<in> S \<rightarrow> T"
@qed

lemma pow_le_potent [resolve]:
  "le_potent(S,Pow(S))"
@proof
  @let "f = Fun(S,Pow(S),\<lambda>x. {x})"
  @have "injective(f)" @have "f \<in> S \<rightarrow> Pow(S)"
@qed

lemma ord_le_potent [resolve]:
  "ord(i) \<Longrightarrow> ord(j) \<Longrightarrow> i \<in> j \<Longrightarrow> le_potent(i,j)" by auto2

section \<open>Two successor function for cardinals\<close>

definition pow_cardinal :: "i \<Rightarrow> i" where [rewrite]:
  "pow_cardinal(K) = cardinal(Pow(K))"

lemma pow_cardinal_is_cardinal [forward]:
  "card(pow_cardinal(K))" by auto2

lemma pow_cardinal_equipotent [resolve]:
  "equipotent(Pow(K),pow_cardinal(K))" by auto2

lemma cantor_non_equipotent [resolve]:
  "\<not>equipotent(K,Pow(K))"
@proof
  @contradiction
  @obtain f where "f \<in> K \<cong> Pow(K)"
  @let "S = {x \<in> K. x \<notin> f`x}"
  @have "\<forall>x\<in>K. f`x \<noteq> S" @with @case "x \<in> f`x" @end
@qed

lemma cantor_non_lepotent [resolve]:
  "\<not>le_potent(Pow(K),K)"
@proof @have "le_potent(K,Pow(K))" @qed

lemma pow_cardinal_less [resolve]:
  "card(K) \<Longrightarrow> K \<in> pow_cardinal(K)"
@proof
  @let "L = pow_cardinal(K)"
  @have "equipotent(Pow(K),L)"
  @have (@rule) "K \<in> L \<or> K = L \<or> L \<in> K"
  @case "L \<in> K" @with @have "le_potent(L,K)" @end
@qed

(* Assume K is a cardinal in this definition *)
definition succ_cardinal :: "i \<Rightarrow> i" where [rewrite]:
  "succ_cardinal(K) = (\<mu> L. card(L) \<and> K \<in> L)"

lemma succ_cardinal_is_cardinal:
  "card(K) \<Longrightarrow> card(succ_cardinal(K)) \<and> K \<in> succ_cardinal(K)"
@proof
  @let "P = pow_cardinal(K)"
  @have "card(P) \<and> K \<in> P"
@qed
setup {* add_forward_prfstep (conj_left_th @{thm succ_cardinal_is_cardinal}) *}
setup {* add_resolve_prfstep (conj_right_th @{thm succ_cardinal_is_cardinal}) *}

lemma succ_cardinal_ineq [backward]:
  "card(K) \<Longrightarrow> succ_cardinal(K) \<le>\<^sub>O pow_cardinal(K)"
@proof
  @let "P = pow_cardinal(K)"
  @have "card(P) \<and> K \<in> P"
@qed

end
