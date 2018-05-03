(* Based on OrderType and Cardinal in Isabelle/ZF. *)

theory Cardinal
  imports Finite
begin

declare [[print_trace]]

section \<open>Least ordinal satisfying a property\<close>

(* Least ordinal satisfying property P. *)
definition least_ord :: "(i \<Rightarrow> o) \<Rightarrow> i"  (binder "\<mu> " 10) where [rewrite]:
  "(\<mu> i. P(i)) = (THE i. ord(i) \<and> P(i) \<and> (\<forall>j\<in>i. \<not>P(j)))"

declare ord_linear[resolve]

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
  "ordermap(r,x) = wfrec(r, \<lambda>x f. Tup_image(f,rel_vsection(r,x)), x)"

lemma ordermap_eq [rewrite]:
  "wf(r) \<Longrightarrow> x \<in> source(r) \<Longrightarrow> ordermap(r,x) = {ordermap(r,y). y \<in> rel_vsection(r,x)}" by auto2
setup {* del_prfstep_thm @{thm ordermap_def} *}

lemma ord_ordermap:
  "wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> x \<in> source(r) \<Longrightarrow> ord(ordermap(r,x))" by auto2
setup {* add_forward_prfstep_cond @{thm ord_ordermap} [with_term "ordermap(?r,?x)"] *}

(* The image of ordermap. *)
definition ordertype :: "i \<Rightarrow> i" where [rewrite]:
  "ordertype(r) = {ordermap(r,x). x \<in> source(r)}"

lemma ord_ordertype [forward]:
  "wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> ord(ordertype(r))" by auto2

definition linear_rel :: "i \<Rightarrow> o" where [rewrite]:
  "linear_rel(r) \<longleftrightarrow> (\<forall>x\<in>source(r). \<forall>y\<in>source(r). rel(r,x,y) \<or> rel(r,y,x))"
setup {* add_property_const @{term linear_rel} *}

lemma linear_relD [forward]:
  "linear_rel(r) \<Longrightarrow> x \<in> source(r) \<Longrightarrow> y \<in> source(r) \<Longrightarrow> \<not>rel(r,x,y) \<Longrightarrow> rel(r,y,x)" by auto2
setup {* del_prfstep_thm_eqforward @{thm linear_rel_def} *}

definition ordermap_fun :: "i \<Rightarrow> i" where [rewrite]:
  "ordermap_fun(r) = Fun(source(r),ordertype(r), \<lambda>x. ordermap(r,x))"

lemma ordermap_fun_type [typing]:
  "ordermap_fun(r) \<in> source(r) \<rightarrow> ordertype(r)" by auto2

lemma ordermap_fun_eval [rewrite]:
  "x \<in> source(r) \<Longrightarrow> ordermap_fun(r)`x = ordermap(r,x)" by auto2
setup {* del_prfstep_thm @{thm ordermap_fun_def} *}

lemma ordermap_inj [forward]:
  "wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> linear_rel(r) \<Longrightarrow> injective(ordermap_fun(r))"
@proof
  @let "f = ordermap_fun(r)"
  @let "A = source(r)"
  @have "\<forall>x\<in>A. \<forall>y\<in>A. x \<noteq> y \<longrightarrow> f`x \<noteq> f`y" @with
    @case "rel(r,x,y)" @with
      @have "ordermap(r,x) \<in> ordermap(r,y)"
    @end
    @case "rel(r,y,x)" @with
      @have "ordermap(r,y) \<in> ordermap(r,x)"
    @end
  @end
@qed

lemma ordermap_bij [forward]:
  "wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> linear_rel(r) \<Longrightarrow> bijective(ordermap_fun(r))"
  by auto2

section \<open>Cardinals\<close>

definition cardinal :: "i \<Rightarrow> i" where [rewrite]:
  "cardinal(A) = (\<mu> i. equipotent(i,A))"

definition card :: "i \<Rightarrow> o" where [rewrite]:
  "card(i) \<longleftrightarrow> (i = cardinal(i))"

section \<open>Basic properties of cardinals\<close>

lemma cardinal_equipotent [resolve]:
  "wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> linear_rel(r) \<Longrightarrow> A = source(r) \<Longrightarrow> equipotent(A,cardinal(A))"
@proof
  @let "i = ordertype(r)"
  @have "equipotent(A,i)" @with
    @have "ordermap_fun(r) \<in> A \<cong> ordertype(r)"
  @end
@qed

lemma card_is_ordinal:
  "wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> linear_rel(r) \<Longrightarrow> A = source(r) \<Longrightarrow> ord(cardinal(A))"
@proof
  @let "i = ordertype(r)"
  @have "equipotent(A,i)" @with
    @have "ordermap_fun(r) \<in> A \<cong> ordertype(r)"
  @end
@qed

end
