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
  "cardinal(A) = (\<mu> i. i \<approx>\<^sub>S A)"

definition card :: "i \<Rightarrow> o" where [rewrite]:
  "card(i) \<longleftrightarrow> (i = cardinal(i))"
setup {* add_property_const @{term card} *}

section \<open>Basic properties of cardinals\<close>

(* Without assuming axiom of choice *)
lemma cardinal_equipotent_gen [resolve]:
  "well_order(r) \<Longrightarrow> A = carrier(r) \<Longrightarrow> A \<approx>\<^sub>S cardinal(A)"
@proof
  @let "i = ordertype(r)"
  @have "A \<approx>\<^sub>S i" @with
    @have "ordermap_fun(r) \<in> A \<cong> ordertype(r)"
  @end
@qed

lemma card_is_ordinal_gen [forward]:
  "well_order(r) \<Longrightarrow> A = carrier(r) \<Longrightarrow> ord(cardinal(A))"
@proof
  @let "i = ordertype(r)"
  @have "A \<approx>\<^sub>S i" @with
    @have "ordermap_fun(r) \<in> A \<cong> ordertype(r)"
  @end
@qed

lemma cardinal_cong_gen [resolve]:
  "well_order(r) \<Longrightarrow> well_order(s) \<Longrightarrow> A = carrier(r) \<Longrightarrow> B = carrier(s) \<Longrightarrow>
   A \<approx>\<^sub>S B \<Longrightarrow> cardinal(A) = cardinal(B)"
@proof
  @have "A \<approx>\<^sub>S cardinal(A)"
  @have "B \<approx>\<^sub>S cardinal(B)"
  @have "cardinal(A) \<le>\<^sub>O cardinal(B)"
  @have "cardinal(B) \<le>\<^sub>O cardinal(A)"
@qed

(* With axiom of choice. Will make this assumption from now on. *)
lemma cardinal_equipotent [resolve]:
  "A \<approx>\<^sub>S cardinal(A)"
@proof
  @obtain "R\<in>raworder_space(A)" where "well_order(R)"
@qed

lemma card_is_ordinal [forward]:
  "ord(cardinal(A))"
@proof
  @obtain "R\<in>raworder_space(A)" where "well_order(R)"
@qed

lemma cardinal_cong [resolve]:
  "A \<approx>\<^sub>S B \<Longrightarrow> cardinal(A) = cardinal(B)"
@proof
  @obtain "R\<in>raworder_space(A)" where "well_order(R)"
  @obtain "S\<in>raworder_space(B)" where "well_order(S)"
@qed

lemma card_is_cardinal [forward]:
  "card(cardinal(A))"
@proof @have "A \<approx>\<^sub>S cardinal(A)" @qed

section \<open>Ordering on cardinality\<close>

definition le_potent :: "i \<Rightarrow> i \<Rightarrow> o"  (infix "\<lesssim>\<^sub>S" 50) where [rewrite]:
  "S \<lesssim>\<^sub>S T \<longleftrightarrow> (\<exists>f\<in>S\<rightarrow>T. injective(f))"

lemma le_potentI [resolve]: "injective(f) \<Longrightarrow> f \<in> A \<rightarrow> B \<Longrightarrow> A \<lesssim>\<^sub>S B" by auto2
lemma le_potentE [resolve]: "S \<lesssim>\<^sub>S T \<Longrightarrow> \<exists>f\<in>S\<rightarrow>T. injective(f)" by auto2
setup {* del_prfstep_thm @{thm le_potent_def} *}

lemma le_potent_trans [forward]:
  "A \<approx>\<^sub>S B \<Longrightarrow> B \<lesssim>\<^sub>S C \<Longrightarrow> A \<lesssim>\<^sub>S C"
@proof
  @obtain "f \<in> A \<cong> B"
  @obtain "g \<in> B \<rightarrow> C" where "injective(g)"
  @let "h = g \<circ> f"
  @have "h \<in> A \<rightarrow> C" @have "injective(h)"
@qed

lemma le_potent_trans2 [forward]:
  "A \<lesssim>\<^sub>S B \<Longrightarrow> B \<approx>\<^sub>S C \<Longrightarrow> A \<lesssim>\<^sub>S C"
@proof
  @obtain "f \<in> A \<rightarrow> B" where "injective(f)"
  @obtain "g \<in> B \<cong> C"
  @let "h = g \<circ> f"
  @have "h \<in> A \<rightarrow> C" @have "injective(h)"
@qed

lemma schroeder_bernstein_potent [forward]:
  "S \<lesssim>\<^sub>S T \<Longrightarrow> T \<lesssim>\<^sub>S S \<Longrightarrow> S \<approx>\<^sub>S T"
@proof
  @obtain "f\<in>S\<rightarrow>T" where "injective(f)"
  @obtain "g\<in>T\<rightarrow>S" where "injective(g)"
@qed

lemma subset_le_potent [resolve]:
  "S \<subseteq> T \<Longrightarrow> S \<lesssim>\<^sub>S T"
@proof
  @let "f = Fun(S,T,\<lambda>x. x)"
  @have "injective(f)" @have "f \<in> S \<rightarrow> T"
@qed

lemma pow_le_potent [resolve]:
  "S \<lesssim>\<^sub>S Pow(S)"
@proof
  @let "f = Fun(S,Pow(S),\<lambda>x. {x})"
  @have "injective(f)" @have "f \<in> S \<rightarrow> Pow(S)"
@qed

lemma ord_le_potent [resolve]:
  "ord(i) \<Longrightarrow> ord(j) \<Longrightarrow> i \<in> j \<Longrightarrow> i \<lesssim>\<^sub>S j" by auto2

section \<open>Two successor function for cardinals\<close>

definition pow_cardinal :: "i \<Rightarrow> i" where [rewrite]:
  "pow_cardinal(K) = cardinal(Pow(K))"

lemma pow_cardinal_is_cardinal [forward]:
  "card(pow_cardinal(K))" by auto2

lemma pow_cardinal_equipotent [resolve]:
  "Pow(K) \<approx>\<^sub>S pow_cardinal(K)" by auto2

lemma cantor_non_equipotent [resolve]:
  "\<not> K \<approx>\<^sub>S Pow(K)"
@proof
  @contradiction
  @obtain f where "f \<in> K \<cong> Pow(K)"
  @let "S = {x \<in> K. x \<notin> f`x}"
  @have "\<forall>x\<in>K. f`x \<noteq> S" @with @case "x \<in> f`x" @end
@qed

lemma cantor_non_lepotent [resolve]:
  "\<not> Pow(K) \<lesssim>\<^sub>S K"
@proof @have "K \<lesssim>\<^sub>S Pow(K)" @qed

lemma pow_cardinal_less [resolve]:
  "card(K) \<Longrightarrow> K \<in> pow_cardinal(K)"
@proof
  @let "L = pow_cardinal(K)"
  @have "Pow(K) \<approx>\<^sub>S L"
  @have (@rule) "K \<in> L \<or> K = L \<or> L \<in> K"
  @case "L \<in> K" @with @have "L \<lesssim>\<^sub>S K" @end
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

definition limit_ord :: "i \<Rightarrow> o" where [rewrite]:
  "limit_ord(i) \<longleftrightarrow> (ord(i) \<and> \<emptyset> \<in> i \<and> (\<forall>y. y \<in> i \<longrightarrow> succ(y) \<in> i))"
setup {* add_property_const @{term limit_ord} *}

lemma limit_ordD [forward]:
  "limit_ord(i) \<Longrightarrow> ord(i)"
  "limit_ord(i) \<Longrightarrow> \<emptyset> \<in> i" by auto2+

lemma limit_ordD2 [backward]:
  "limit_ord(i) \<Longrightarrow> y \<in> i \<Longrightarrow> succ(y) \<in> i" by auto2

lemma limit_ord_not_succ [resolve]:
  "\<not>limit_ord(succ(a))" by auto2
setup {* del_prfstep_thm_eqforward @{thm limit_ord_def} *}

section \<open>Transfinite induction on ordinals\<close>

(* Given G a meta-function taking the family of values less than an ordinal i
   to the value at i, return the value at i. *)
definition trans_seq :: "(i \<Rightarrow> i) \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "trans_seq(G,a) = wfrec(mem_rel(succ(a)), \<lambda>_ f. G(f), a)"

lemma trans_seq_eq1 [backward]:
  "ord(b) \<Longrightarrow> a \<in> b \<Longrightarrow> i \<in> a \<Longrightarrow> wfrec(mem_rel(b),H,i) = wfrec(mem_rel(a),H,i)"
@proof
  @let "r = mem_rel(a)" "s = mem_rel(b)"
  @have "\<forall>x. ord(x) \<longrightarrow> x \<in> a \<longrightarrow> (\<forall>y\<in>x. y \<in> a \<longrightarrow> wfrec(s, H, y) = wfrec(r, H, y)) \<longrightarrow> wfrec(s, H, x) = wfrec(r, H, x)" @with
    @have "wfrec(s,H,x) = H(x, Tup(x, \<lambda>x. wfrec(s,H,x)))"
    @have "wfrec(r,H,x) = H(x, Tup(x, \<lambda>x. wfrec(r,H,x)))"
    @have "Tup(x, \<lambda>x. wfrec(s,H,x)) = Tup(x, \<lambda>x. wfrec(r,H,x))"
  @end
  @induct "ord(i)" "i \<in> a \<longrightarrow> wfrec(s,H,i) = wfrec(r,H,i)"
@qed

lemma not_limit_ordinal_eq [backward1]:
  "ord(a) \<Longrightarrow> \<emptyset> \<in> a \<Longrightarrow> \<not>limit_ord(a) \<Longrightarrow> \<exists>b. a = succ(b)"
@proof
  @obtain b where "b \<in> a" "succ(b) \<notin> a"
  @have (@rule) "a \<in> succ(b) \<or> a = succ(b) \<or> succ(b) \<in> a"
@qed

lemma empty_ord [resolve]: "ord(\<emptyset>)" by auto2

lemma nonzero_ordinal [resolve]: "ord(a) \<Longrightarrow> x \<in> a \<Longrightarrow> \<emptyset> \<in> a"
@proof @have "ord(\<emptyset>)" @have (@rule) "\<emptyset> \<in> x \<or> \<emptyset> = x \<or> x \<in> \<emptyset>" @qed

lemma ord_mem_succ [backward]: "ord(a) \<Longrightarrow> i \<in> a \<Longrightarrow> succ(i) \<in> succ(a)"
@proof
  @case "limit_ord(a)"
  @have "\<emptyset> \<in> a"
  @obtain b where "a = succ(b)"
  @have "\<forall>x xa. ord(x) \<longrightarrow> (\<forall>y\<in>x. \<forall>x. x \<in> y \<longrightarrow> succ(x) \<in> succ(y)) \<longrightarrow> xa \<in> x \<longrightarrow> succ(xa) \<in> succ(x)" @with
    @case "limit_ord(x)"
    @obtain y where "x = succ(y)"
    @have "xa \<in> succ(y)"
    @have (@rule) "xa = y \<or> xa \<in> y"
    @case "xa = y"
  @end
  @induct "ord(a)" "(\<forall>x. x \<in> a \<longrightarrow> succ(x) \<in> succ(a))"
@qed

lemma trans_seq_unfold [rewrite]:
  "ord(a) \<Longrightarrow> trans_seq(G,a) = G(Tup(a, \<lambda>x. trans_seq(G,x)))"
@proof
  @let "r = mem_rel(succ(a))"
  @have "trans_seq(G,a) = G(Tup(a, \<lambda>x. wfrec(r, \<lambda>_ f. G(f), x)))"
  @have "\<forall>x\<in>a. trans_seq(G,x) = wfrec(r, \<lambda>_ f. G(f), x)" @with
    @have "trans_seq(G,x) = wfrec(mem_rel(succ(x)), \<lambda>_ f. G(f), x)"
    @have "wfrec(r, \<lambda>_ f. G(f), x) = wfrec(mem_rel(succ(x)), \<lambda>_ f. G(f), x)"
  @end
@qed

setup {* del_prfstep_thm @{thm trans_seq_def} *}

definition pred :: "i \<Rightarrow> i" where [rewrite]:
  "pred(x) = (THE y. x = succ(y))"
setup {* register_wellform_data ("pred(x)", ["\<not>limit_ord(x)", "\<emptyset> \<in> x"]) *}

lemma pred_eq [rewrite]:
  "ord(x) \<Longrightarrow> \<not>limit_ord(x) \<Longrightarrow> \<emptyset> \<in> x \<Longrightarrow> succ(pred(x)) = x" by auto2

lemma pred_eq2 [rewrite]:
  "ord(x) \<Longrightarrow> pred(succ(x)) = x" by auto2
setup {* del_prfstep_thm @{thm pred_def} *}

(* Another definition of transfinite induction *)
definition trans_seq2 :: "i \<Rightarrow> (i \<Rightarrow> i) \<Rightarrow> (i \<Rightarrow> i) \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "trans_seq2(g1,G2,G3,a) =
     trans_seq(\<lambda>f. if source(f) = \<emptyset> then g1
                   else if limit_ord(source(f)) then G3(f)
                   else G2(f`pred(source(f))), a)"

lemma trans_seq2_unfold1 [rewrite]:
  "trans_seq2(g1,G2,G3,\<emptyset>) = g1"
@proof @have "ord(\<emptyset>)" @qed

lemma trans_seq2_unfold2 [rewrite]:
  "ord(a) \<Longrightarrow> trans_seq2(g1,G2,G3,succ(a)) = G2(trans_seq2(g1,G2,G3,a))"
@proof
  @have "\<not>limit_ord(succ(a))"
  @have "\<emptyset> \<in> succ(a)"
  @have "pred(succ(a)) = a"
@qed

lemma trans_seq2_unfold3 [rewrite]:
  "limit_ord(a) \<Longrightarrow> trans_seq2(g1,G2,G3,a) = G3(Tup(a, \<lambda>x. trans_seq2(g1,G2,G3,x)))" by auto2

setup {* del_prfstep_thm @{thm trans_seq2_def} *}

section \<open>Union of cardinals is a cardinal\<close>

lemma card_less [resolve]:
  "card(c) \<Longrightarrow> i \<in> c \<Longrightarrow> \<not>i \<approx>\<^sub>S c"
@proof
  @contradiction
  @have "c \<le>\<^sub>O i"
@qed

lemma union_card [backward]:
  "\<forall>x\<in>S. card(x) \<Longrightarrow> card(\<Union>S)"
@proof
  @have "(\<mu> i. i \<approx>\<^sub>S \<Union>S) = \<Union>S" @with
    @have "\<forall>i\<in>\<Union>S. \<not>i \<approx>\<^sub>S \<Union>S" @with
      @obtain c where "i \<in> c" "c \<in> S"
      @have "\<not>c \<lesssim>\<^sub>S i" @with
        @have "i \<lesssim>\<^sub>S c"
      @end
      @have "c \<lesssim>\<^sub>S \<Union>S" @with
        @have "c \<subseteq> \<Union>S"
      @end
    @end
  @end
@qed
  
section \<open>Aleph numbers\<close>

definition aleph :: "i \<Rightarrow> i" where [rewrite]:
  "aleph(i) = trans_seq2(nat,succ_cardinal,\<lambda>f. \<Union>(Tup_image(f,source(f))),i)"

lemma aleph_unfold1 [rewrite]:
  "aleph(\<emptyset>) = nat" by auto2

lemma aleph_unfold2 [rewrite]:
  "ord(a) \<Longrightarrow> aleph(succ(a)) = succ_cardinal(aleph(a))" by auto2

lemma aleph_unfold3 [rewrite]:
  "limit_ord(a) \<Longrightarrow> aleph(a) = \<Union>{aleph(c). c \<in> a}" by auto2

section \<open>Beth numbers\<close>

definition beth :: "i \<Rightarrow> i" where [rewrite]:
  "beth(i) = trans_seq2(nat,pow_cardinal,\<lambda>f. \<Union>(Tup_image(f,source(f))),i)"

lemma beth_unfold1 [rewrite]:
  "beth(\<emptyset>) = nat" by auto2

lemma beth_unfold2 [rewrite]:
  "ord(a) \<Longrightarrow> beth(succ(a)) = pow_cardinal(beth(a))" by auto2

lemma beth_unfold3 [rewrite]:
  "limit_ord(a) \<Longrightarrow> beth(a) = \<Union>{beth(c). c \<in> a}" by auto2

section \<open>Natural numbers as cardinals\<close>

declare nat_def [rewrite]
declare nat_bnd_mono [resolve]
declare nat_unfold [rewrite]
declare Zero_def [rewrite]
declare nat_add_1 [rewrite_back]
declare Suc_def [rewrite]

lemma nat_into_ordinal [resolve]:
  "n \<in> nat \<Longrightarrow> ord(n)"
@proof @var_induct "n \<in> nat" @qed

lemma nat_ordinal [resolve]:
  "ord(nat)"
@proof
  @have "trans_set(nat)" @with
    @have "\<forall>x\<in>nat. x \<subseteq> nat" @with
      @var_induct "x \<in> nat"
    @end
  @end
  @have "\<forall>n\<in>nat. trans_set(n)" @with
    @have "ord(n)"
  @end
@qed

lemma nat_limit_ordinal [forward]:
  "limit_ord(nat)" by auto2

lemma nat_Suc_diff [rewrite]:
  "n \<in> nat \<Longrightarrow> Suc(n) \<midarrow> {n} = n" by auto2

(* TODO: unify with proof of equipotent_nat_less_range in Finite *)
lemma equipotent_nat_less_range [forward]:
  "m \<in> nat \<Longrightarrow> n \<in> nat \<Longrightarrow> m \<approx>\<^sub>S n \<Longrightarrow> m = n"
@proof
  @var_induct "m \<in> nat" arbitrary n @with
    @subgoal "m = m' +\<^sub>\<nat> 1"
      @obtain "n'\<in>nat" where "n = n' +\<^sub>\<nat> 1"
      @have "m' = Suc(m') \<midarrow> {m'}"
      @have "n' = Suc(n') \<midarrow> {n'}"
      @have "m' \<approx>\<^sub>S n'"
    @endgoal
  @end
@qed

lemma nat_not_equipotent [resolve]:
  "x \<in> nat \<Longrightarrow> \<not> x \<approx>\<^sub>S nat"
@proof
  @contradiction
  @have "Suc(x) \<lesssim>\<^sub>S nat"
  @have "nat \<approx>\<^sub>S x"
  @have "x \<approx>\<^sub>S Suc(x)" @with
    @have "x \<lesssim>\<^sub>S Suc(x)"
  @end
@qed

lemma nat_cardinal [forward]:
  "card(nat)"
@proof
  @have "(\<mu> i. i \<approx>\<^sub>S nat) = nat"
@qed

section \<open>Aleph and Beth numbers are cardinals\<close>

lemma aleph_cardinal [forward]:
  "ord(a) \<Longrightarrow> card(aleph(a))"
@proof
  @have "\<forall>x. ord(x) \<longrightarrow> (\<forall>y\<in>x. card(aleph(y))) \<longrightarrow> card(aleph(x))" @with
    @case "x = \<emptyset>"
    @case "limit_ord(x)"
    @obtain y where "x = succ(y)"
  @end
  @induct "ord(a)" "card(aleph(a))"
@qed

lemma beth_cardinal [forward]:
  "ord(a) \<Longrightarrow> card(beth(a))"
@proof
  @have "\<forall>x. ord(x) \<longrightarrow> (\<forall>y\<in>x. card(beth(y))) \<longrightarrow> card(beth(x))" @with
    @case "x = \<emptyset>"
    @case "limit_ord(x)"
    @obtain y where "x = succ(y)"
  @end
  @induct "ord(a)" "card(beth(a))"
@qed

end
