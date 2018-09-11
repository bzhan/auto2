(*
  File: Structure.thy
  Author: Bohua Zhan

  Definition of mathematical structures. Structures are represented as
  partial functions from natural numbers, with each field given an unique
  natural number index.
*)

theory Structure
  imports Graph
begin

definition Struct :: "i \<Rightarrow> i" where [rewrite]:
  "Struct(S) = S"

lemma not_mem_cons: "x \<noteq> a \<Longrightarrow> x \<notin> S \<Longrightarrow> x \<notin> cons(a,S)" by auto2
lemma mem_cons_head: "x \<in> cons(x,S)" by auto2
lemma mem_cons_tail: "x \<in> S \<Longrightarrow> x \<in> cons(y,S)" by auto2
lemma forall_single: "(\<forall>x\<in>{a}. P(x)) \<longleftrightarrow> P(a)" by auto2
lemma forall_cons: "(\<forall>x\<in>cons(a,X). P(x)) \<longleftrightarrow> (P(a) \<and> (\<forall>x\<in>X. P(x)))" by auto2

ML_file "structure.ML"

section \<open>Components of a structure\<close>

definition "source_name = \<emptyset>"
definition "target_name = succ(\<emptyset>)"
definition "graph_name = succ(succ(\<emptyset>))"

definition "source(S) = graph_eval(S, source_name)"
definition "target(S) = graph_eval(S, target_name)"
definition "graph(S) = graph_eval(S, graph_name)"

setup {* add_field_data (@{term source_name}, @{term source}) *}
setup {* add_field_data (@{term target_name}, @{term target}) *}
setup {* add_field_data (@{term graph_name}, @{term graph}) *}

section {* Evaluation function: shared by families and functions *}

definition feval :: "i \<Rightarrow> i \<Rightarrow> i" (infixl "`" 90) where [rewrite]:
  "f ` x = graph_eval(graph(f),x)"
setup {* register_wellform_data ("f ` x", ["x \<in> source(f)"]) *}
setup {* add_prfstep_check_req ("f ` x", "x \<in> source(f)") *}

section {* Families *}

(* Predicate for families. *)
definition is_family :: "i \<Rightarrow> o" where [rewrite]:
  "is_family(F) \<longleftrightarrow> is_func_graph(F,{source_name,graph_name}) \<and> is_func_graph(graph(F),source(F))"

(* Constructor for families. *)
definition Tup :: "i \<Rightarrow> (i \<Rightarrow> i) \<Rightarrow> i" where [rewrite]:
  "Tup(I,f) = Struct({\<langle>source_name, I\<rangle>, \<langle>graph_name, {\<langle>a, f(a)\<rangle>. a \<in> I}\<rangle>})"

lemma TupD: "is_family(Tup(I,f)) \<and> source(Tup(I,f)) = I"
@proof
  @let "G = {\<langle>a, f(a)\<rangle>. a \<in> I}"
  @have "is_graph(G)"
  @have "\<forall>x. x \<in> gr_source(G) \<longleftrightarrow> x \<in> I" @with
    @case "x \<in> gr_source(G)" @with @obtain y where "\<langle>x,y\<rangle> \<in> G" @end
    @case "x \<in> I" @with @have "\<langle>x, f(x)\<rangle> \<in> G" @end
  @end
  @have "is_func_graph(G,I)"
@qed
setup {* add_forward_prfstep_cond @{thm TupD} [with_term "Tup(?I,?f)"] *}

(* Evaluation for families. *)
lemma Tup_eval [rewrite]: "a \<in> source(Tup(I,f)) \<Longrightarrow> Tup(I,f) ` a = f(a)" by auto2

(* Equality on families. *)
lemma family_eq [backward]:
  "is_family(f) \<Longrightarrow> is_family(g) \<Longrightarrow> source(f) = source(g) \<Longrightarrow> \<forall>a\<in>source(f). f`a = g`a \<Longrightarrow> f = g"
@proof @have "\<forall>a\<in>source(f). graph_eval(graph(f),a) = graph_eval(graph(g),a)" @qed
setup {* del_prfstep_thm @{thm Tup_def} *}

(* Pi space is the space of families with values in specified sets.
   Need to use Sigma(I,B) to construct the set. *)
definition Pi :: "[i, i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "Pi(I,B) = {Struct({\<langle>source_name, I\<rangle>, \<langle>graph_name, P\<rangle>}). P \<in> {f \<in> Pow(Sigma(I,B)). is_func_graph(f,I)}}"

lemma Pi_iff [rewrite]:
  "f \<in> Pi(I,B) \<longleftrightarrow> (\<exists>P. P \<in> Pow(Sigma(I,B)) \<and> is_func_graph(P,I) \<and> f = Struct({\<langle>source_name, I\<rangle>, \<langle>graph_name, P\<rangle>}))" by auto2
setup {* del_prfstep_thm @{thm Pi_def} *}

lemma Pi_memI [backward]:
  "is_family(f) \<Longrightarrow> source(f) = I \<Longrightarrow> \<forall>a\<in>I. f`a\<in>B(a) \<Longrightarrow> f \<in> Pi(I,B)"
@proof @have "graph(f) \<in> Pow(Sigma(I,B))" @qed

lemma Pi_is_family [forward]: "f \<in> Pi(I,B) \<Longrightarrow> is_family(f) \<and> source(f) = I" by auto2
lemma Pi_memD [typing]: "a \<in> source(f) \<Longrightarrow> f \<in> Pi(I,B) \<Longrightarrow> f`a \<in> B(a)" by auto2

(* Restriction of a family to a subset of the source *)
definition proj_set :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "proj_set(f,J) = Tup(J, \<lambda>a. f`a)"
setup {* register_wellform_data ("proj_set(f,J)", ["J \<subseteq> source(f)"]) *}
setup {* add_prfstep_check_req ("proj_set(f,J)", "J \<subseteq> source(f)") *}

lemma proj_set_is_family:
  "is_family(f) \<Longrightarrow> is_family(proj_set(f,J)) \<and> source(proj_set(f,J)) = J" by auto2
setup {* add_forward_prfstep_cond @{thm proj_set_is_family} [with_term "proj_set(?f,?J)"] *}

lemma proj_set_eval [rewrite]:
  "a \<in> source(proj_set(f,J)) \<Longrightarrow> proj_set(f,J) ` a = f`a" by auto2

setup {* fold del_prfstep_thm [@{thm is_family_def}, @{thm Pi_iff}, @{thm proj_set_def}] *}

section {* Functions *}

(* A function is a relation where every element in the source corresponds
   to exactly one value in the target. *)
definition is_function :: "i \<Rightarrow> o" where [rewrite]:
  "is_function(f) \<longleftrightarrow> graph(f) \<in> func_graphs(source(f),target(f))"
  
definition func_form :: "i \<Rightarrow> o" where [rewrite]:
  "func_form(f) \<longleftrightarrow> is_function(f) \<and> is_func_graph(f,{source_name, target_name, graph_name})"

lemma is_function_from_form [forward]: "func_form(f) \<Longrightarrow> is_function(f)" by auto2

(* The set of functions *)
definition function_space :: "i \<Rightarrow> i \<Rightarrow> i" (infixr "\<rightarrow>" 60)  where [rewrite]:
  "A \<rightarrow> B = {Struct({\<langle>source_name,A\<rangle>, \<langle>target_name,B\<rangle>, \<langle>graph_name,G\<rangle>}). G\<in>func_graphs(A,B)}"

lemma function_spaceD [forward]:
  "f \<in> A \<rightarrow> B \<Longrightarrow> func_form(f) \<and> source(f) = A \<and> target(f) = B" by auto2

lemma function_spaceI [typing]:
  "func_form(f) \<Longrightarrow> f \<in> source(f) \<rightarrow> target(f)" by auto2

(* Constructor for functions *)
definition Fun :: "[i, i, i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "Fun(A,B,b) = Struct({\<langle>source_name,A\<rangle>, \<langle>target_name,B\<rangle>, \<langle>graph_name, {p\<in>A\<times>B. snd(p) = b(fst(p))}\<rangle>})"
setup {* add_prfstep_check_req ("Fun(A,B,b)", "Fun(A,B,b) \<in> A \<rightarrow> B") *}

lemma lambda_is_function [backward]:
  "\<forall>x\<in>A. f(x)\<in>B \<Longrightarrow> Fun(A,B,f) \<in> A \<rightarrow> B"
@proof
  @let "G = {p\<in>A\<times>B. snd(p) = f(fst(p))}"
  @have "is_graph(G)"
  @have "\<forall>x. x \<in> gr_source(G) \<longleftrightarrow> x \<in> A" @with
    @case "x \<in> gr_source(G)" @with @obtain y where "\<langle>x,y\<rangle> \<in> G" @end
    @case "x \<in> A" @with @have "\<langle>x, f(x)\<rangle> \<in> G" @end
  @end
  @have "G \<in> func_graphs(A,B)"
@qed

(* Function evaluation *)
lemma beta [rewrite]:
  "F = Fun(A,B,f) \<Longrightarrow> x \<in> source(F) \<Longrightarrow> is_function(F) \<Longrightarrow> F`x = f(x)" by auto2

lemma feval_in_range [typing]:
  "is_function(f) \<Longrightarrow> x \<in> source(f) \<Longrightarrow> f`x \<in> target(f)" by auto2

(* Equality between functions *)
lemma function_eq [backward]:
  "func_form(f) \<Longrightarrow> func_form(g) \<Longrightarrow> source(f) = source(g) \<Longrightarrow> target(f) = target(g) \<Longrightarrow>
   \<forall>x\<in>source(f). f`x = g`x \<Longrightarrow> f = g"
@proof @have "\<forall>a\<in>source(f). graph_eval(graph(f),a) = graph_eval(graph(g),a)" @qed
setup {* fold del_prfstep_thm [
  @{thm is_function_def}, @{thm Fun_def}, @{thm func_form_def}, @{thm function_space_def}, @{thm feval_def}] *}
setup {* add_rewrite_rule_back @{thm feval_def} *}

(* A small exercise *)
lemma lam_eq_self: "f \<in> A \<rightarrow> B \<Longrightarrow> f = Fun(A,B, \<lambda>x. f`x)" by auto2

section {* Carrier of a structure *}

(* Underlying set of a structure. *)
definition "carrier_name = \<emptyset>"
definition "carrier(S) = graph_eval(S, carrier_name)"
setup {* add_field_data (@{term carrier_name}, @{term carrier}) *}

setup {* add_property_field_const @{term carrier} *}

abbreviation mem_carrier :: "[i, i] \<Rightarrow> o" (infix "\<in>." 50) where
  "x \<in>. S \<equiv> x \<in> carrier(S)"

abbreviation Ball_carrier :: "[i, i \<Rightarrow> o] \<Rightarrow> o" where "Ball_carrier(S, P) \<equiv> Ball(carrier(S), P)"
abbreviation Bex_carrier :: "[i, i \<Rightarrow> o] \<Rightarrow> o" where "Bex_carrier(S, P) \<equiv> Bex(carrier(S), P)"
abbreviation Collect_carrier :: "[i, i \<Rightarrow> o] \<Rightarrow> i" where "Collect_carrier(S, P) \<equiv> Collect(carrier(S), P)"
abbreviation RepFun_carrier :: "[i, i \<Rightarrow> i] \<Rightarrow> i" where "RepFun_carrier(S, f) \<equiv> RepFun(carrier(S), f)"
abbreviation UnionS_carrier :: "[i, i \<Rightarrow> i] \<Rightarrow> i" where "UnionS_carrier(S, X) \<equiv> UnionS(carrier(S), X)"
abbreviation InterS_carrier :: "[i, i \<Rightarrow> i] \<Rightarrow> i" where "InterS_carrier(S, X) \<equiv> InterS(carrier(S), X)"
  
syntax
  "_Ball_carrier" :: "[pttrn, i, o] \<Rightarrow> o"  ("(3\<forall>_\<in>._./ _)" 10)
  "_Bex_carrier" :: "[pttrn, i, o] \<Rightarrow> o"  ("(3\<exists>_\<in>._./ _)" 10)
  "_Collect_carrier" :: "[pttrn, i, o] \<Rightarrow> i"  ("(1{_ \<in>. _ ./ _})")
  "_RepFun_carrier" :: "[i, pttrn, i] => i"  ("(1{_ ./ _ \<in>. _})" [51,0,51])
  "_UNION_carrier" :: "[pttrn, i, i] => i"  ("(3\<Union>_\<in>._./ _)" 10)
  "_INTER_carrier" :: "[pttrn, i, i] => i"  ("(3\<Inter>_\<in>._./ _)" 10)
translations
  "\<forall>x\<in>.S. P" \<rightleftharpoons> "CONST Ball_carrier(S, \<lambda>x. P)"
  "\<exists>x\<in>.S. P" \<rightleftharpoons> "CONST Bex_carrier(S, \<lambda>x. P)"
  "{x\<in>.S. P}" \<rightleftharpoons> "CONST Collect_carrier(S, \<lambda>x. P)"
  "{b. x\<in>.S}" \<rightleftharpoons> "CONST RepFun_carrier(S, \<lambda>x. b)"
  "\<Union>a\<in>.I. X" == "CONST UnionS_carrier(I, \<lambda>a. X)"
  "\<Inter>a\<in>.I. X" == "CONST InterS_carrier(I, \<lambda>a. X)"

section \<open>Order structures\<close>

definition "order_graph_name = succ(succ(\<emptyset>))"
definition "order_graph(S) = graph_eval(S, order_graph_name)"

setup {* add_field_data (@{term order_graph_name}, @{term order_graph}) *}

(* Evaluation of order *)
definition le :: "[i, i, i] \<Rightarrow> o" where [rewrite_bidir]:
  "le(R,x,y) \<longleftrightarrow> \<langle>x,y\<rangle> \<in> order_graph(R)"
abbreviation le_notation ("(_/ \<le>\<^sub>_ _)" [51,51,51] 50) where "x \<le>\<^sub>R y \<equiv> le(R,x,y)"
setup {* register_wellform_data ("x \<le>\<^sub>R y", ["x \<in>. R", "y \<in>. R"]) *}

abbreviation (input) ge :: "[i, i, i] \<Rightarrow> o" ("(_/ \<ge>\<^sub>_ _)" [51,51,51] 50) where
  "x \<ge>\<^sub>R y \<equiv> y \<le>\<^sub>R x"

(* General result on evaluation of le. *)
lemma le_eval_gen [rewrite]:
  "order_graph(R) = rel_graph(carrier(R),r) \<Longrightarrow> x \<le>\<^sub>R y \<longleftrightarrow> (x \<in>. R \<and> y \<in>. R \<and> r(x,y))" by auto2

(* General predicate on order. *)
definition raworder :: "i \<Rightarrow> o" where [rewrite]:
  "raworder(R) \<longleftrightarrow> order_graph(R) \<in> Pow(carrier(R)\<times>carrier(R))"

lemma raworderD [forward]:
  "raworder(R) \<Longrightarrow> x \<le>\<^sub>R y \<Longrightarrow> x \<in>. R \<and> y \<in>. R"
  "raworder(R) \<Longrightarrow> is_graph(order_graph(R))" by auto2+
setup {* del_prfstep_thm_eqforward @{thm raworder_def} *}

(* Strict predicate on order. *)
definition ord_form :: "i \<Rightarrow> o" where [rewrite]:
  "ord_form(R) \<longleftrightarrow> raworder(R) \<and> is_func_graph(R,{carrier_name,order_graph_name})"
  
lemma ord_form_to_raw [forward]: "ord_form(R) \<Longrightarrow> raworder(R)" by auto2

(* Space of all order structures on S *)
definition raworder_space :: "i \<Rightarrow> i" where [rewrite]:
  "raworder_space(S) = {Struct({\<langle>carrier_name,S\<rangle>, \<langle>order_graph_name,G\<rangle>}). G\<in>Pow(S\<times>S)}"
  
lemma raworder_spaceD [forward]:
  "R \<in> raworder_space(S) \<Longrightarrow> ord_form(R) \<and> carrier(R) = S" by auto2
    
lemma raworder_spaceI [resolve]:
  "ord_form(R) \<Longrightarrow> R \<in> raworder_space(carrier(R))"
@proof @have "R = Struct({\<langle>carrier_name,carrier(R)\<rangle>, \<langle>order_graph_name,order_graph(R)\<rangle>})" @qed

(* Constructor for ordering *)
definition Order :: "i \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> o) \<Rightarrow> i" where [rewrite]:
  "Order(S,R) = Struct({\<langle>carrier_name,S\<rangle>, \<langle>order_graph_name,rel_graph(S,R)\<rangle>})"

lemma Order_is_raworder [typing]: "Order(S,R) \<in> raworder_space(S)" by auto2

lemma Order_eval [rewrite]:
  "le(Order(S,R),x,y) \<longleftrightarrow> (x \<in> S \<and> y \<in> S \<and> R(x,y))" by auto2

(* Equality on ordering *)
definition eq_str_order :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "eq_str_order(G,H) \<longleftrightarrow> (raworder(G) \<and> raworder(H) \<and> carrier(G) = carrier(H) \<and> (\<forall>x\<in>.G. \<forall>y\<in>.G. x \<le>\<^sub>G y \<longleftrightarrow> x \<le>\<^sub>H y))"

lemma eq_str_orderD1 [forward]: "eq_str_order(G,H) \<Longrightarrow> raworder(G) \<and> raworder(H) \<and> carrier(G) = carrier(H)" by auto2
lemma eq_str_orderD2 [rewrite]: "eq_str_order(G,H) \<Longrightarrow> x \<le>\<^sub>G y \<longleftrightarrow> x \<le>\<^sub>H y" by auto2
lemma eq_str_orderD2' [rewrite]: "eq_str_order(G,H) \<Longrightarrow> order_graph(G) = order_graph(H)" by auto2
lemma eq_str_order_sym [forward]: "eq_str_order(G,H) \<Longrightarrow> eq_str_order(H,G)" by auto2
setup {* del_prfstep_thm_eqforward @{thm eq_str_order_def} *}

lemma order_eq [backward]:
  "ord_form(R) \<Longrightarrow> ord_form(S) \<Longrightarrow> eq_str_order(R,S) \<Longrightarrow> R = S" by auto2

setup {* fold del_prfstep_thm [@{thm ord_form_def}, @{thm raworder_space_def}, @{thm Order_def}, @{thm le_def}] *}
setup {* add_rewrite_rule_back @{thm le_def} *}

end
