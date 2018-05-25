theory Structure
imports Graph
begin

section {* Components of a structure *}

(* Domain set of a relation. *)
definition source :: "i \<Rightarrow> i" where [rewrite]:
  "source(\<Gamma>) = fst(\<Gamma>)"

(* Codomain set of a relation. *)
definition target :: "i \<Rightarrow> i" where [rewrite]:
  "target(\<Gamma>) = fst(snd(\<Gamma>))"

(* Set of pairs specifying a relation between source and target *)
definition graph :: "i \<Rightarrow> i" where [rewrite]:
  "graph(\<Gamma>)  = fst(snd(snd(\<Gamma>)))"

section {* Evaluation function: shared by families and functions *}

definition feval :: "i \<Rightarrow> i \<Rightarrow> i" (infixl "`" 90) where [rewrite]:
  "f ` x = graph_eval(graph(f),x)"
setup {* register_wellform_data ("f ` x", ["x \<in> source(f)"]) *}
setup {* add_prfstep_check_req ("f ` x", "x \<in> source(f)") *}

section {* Families *}

(* Predicate for families. *)
definition is_family :: "i \<Rightarrow> o" where [rewrite]:
  "is_family(F) \<longleftrightarrow> (let G = graph(F) in let S = source(F) in
     is_func_graph(G,S) \<and> F = \<langle>S,\<emptyset>,G,\<emptyset>\<rangle>)"

(* Constructor for families. *)
definition Tup :: "i \<Rightarrow> (i \<Rightarrow> i) \<Rightarrow> i" where [rewrite]:
  "Tup(I,f) = \<langle>I, \<emptyset>, {\<langle>a, f(a)\<rangle>. a \<in> I}, \<emptyset>\<rangle>"

lemma TupD: "is_family(Tup(I,f)) \<and> source(Tup(I,f)) = I"
@proof @have (@rule) "\<forall>a\<in>I. \<langle>a, f(a)\<rangle>\<in>graph(Tup(I,f))" @qed
setup {* add_forward_prfstep_cond @{thm TupD} [with_term "Tup(?I,?f)"] *}

(* Evaluation for families. *)
lemma Tup_eval [rewrite]: "a \<in> source(Tup(I,f)) \<Longrightarrow> Tup(I,f) ` a = f(a)" by auto2

(* Equality on families. *)
lemma family_eq [backward]:
  "is_family(f) \<Longrightarrow> is_family(g) \<Longrightarrow> source(f) = source(g) \<Longrightarrow> \<forall>a\<in>source(f). f`a = g`a \<Longrightarrow> f = g"
@proof @have "\<forall>a\<in>source(f). graph_eval(graph(f),a) = graph_eval(graph(g),a)" @qed

(* Pi space is the space of families with values in specified sets.
   Need to use Sigma(I,B) to construct the set. *)
definition Pi :: "[i, i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "Pi(I,B) = {\<langle>I,\<emptyset>,P,\<emptyset>\<rangle>. P \<in> {f \<in> Pow(Sigma(I,B)). is_family(\<langle>I,\<emptyset>,f,\<emptyset>\<rangle>)}}"

lemma Pi_memI [backward]:
  "is_family(f) \<Longrightarrow> source(f) = I \<Longrightarrow> \<forall>a\<in>I. f`a\<in>B(a) \<Longrightarrow> f \<in> Pi(I,B)" by auto2

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

setup {* fold del_prfstep_thm [
  @{thm is_family_def}, @{thm Tup_def}, @{thm Pi_def}, @{thm proj_set_def}] *}

section {* Functions *}

(* A function is a relation where every element in the source corresponds
   to exactly one value in the target. *)
definition is_function :: "i \<Rightarrow> o" where [rewrite]:
  "is_function(f) \<longleftrightarrow> graph(f) \<in> func_graphs(source(f),target(f))"

lemma is_functionD [typing]:
  "is_function(F) \<Longrightarrow> graph(F) \<in> func_graphs(source(F),target(F))" by auto2

lemma is_functionI [backward]:
  "G \<in> func_graphs(S,T) \<Longrightarrow> is_function(\<langle>S,T,G,x1\<rangle>)" by auto2
setup {* del_prfstep_thm @{thm is_function_def} *}
  
definition func_form :: "i \<Rightarrow> o" where [rewrite]:
  "func_form(f) \<longleftrightarrow> is_function(f) \<and> f = \<langle>source(f),target(f),graph(f),\<emptyset>\<rangle>"

lemma is_function_from_form [forward]: "func_form(f) \<Longrightarrow> is_function(f)" by auto2

(* The set of functions *)
definition function_space :: "i \<Rightarrow> i \<Rightarrow> i" (infixr "\<rightarrow>" 60)  where [rewrite]:
  "A \<rightarrow> B = {\<langle>A,B,G,\<emptyset>\<rangle>. G\<in>func_graphs(A,B)}"

lemma function_spaceD [forward]:
  "f \<in> A \<rightarrow> B \<Longrightarrow> func_form(f) \<and> source(f) = A \<and> target(f) = B" by auto2

lemma function_spaceI [typing]:
  "func_form(f) \<Longrightarrow> f \<in> source(f) \<rightarrow> target(f)" by auto2

(* Constructor for functions *)
definition Fun :: "[i, i, i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "Fun(A,B,b) = \<langle>A,B,{p\<in>A\<times>B. snd(p) = b(fst(p))},\<emptyset>\<rangle>"
setup {* add_prfstep_check_req ("Fun(A,B,b)", "Fun(A,B,b) \<in> A \<rightarrow> B") *}

syntax
  "_lam" :: "[pttrn, i, i, i] \<Rightarrow> i"  ("(3\<lambda>_\<in>_./ _\<in>_)" 10)
translations
  "\<lambda>x\<in>A. f\<in>B" == "CONST Fun(A,B,\<lambda>x. f)"

lemma lambda_is_function [backward]:
  "\<forall>x\<in>A. f(x)\<in>B \<Longrightarrow> Fun(A,B,f) \<in> A \<rightarrow> B"
@proof @have (@rule) "\<forall>x\<in>A. \<langle>x,f(x)\<rangle>\<in>graph(Fun(A,B,f))" @qed

(* Function evaluation *)
lemma beta [rewrite]:
  "F = Fun(A,B,f) \<Longrightarrow> x \<in> source(F) \<Longrightarrow> is_function(F) \<Longrightarrow> F`x = f(x)" by auto2

lemma feval_in_range [typing]:
  "is_function(f) \<Longrightarrow> x \<in> source(f) \<Longrightarrow> f`x \<in> target(f)" by auto2

(* Equality between functions *)
lemma function_eq [backward]:
  "func_form(f) \<Longrightarrow> func_form(g) \<Longrightarrow> source(f) = source(g) \<Longrightarrow> target(f) = target(g) \<Longrightarrow>
   \<forall>x\<in>source(f). f`x = g`x \<Longrightarrow> f = g" by auto2
setup {* fold del_prfstep_thm [
  @{thm func_form_def}, @{thm function_space_def}, @{thm Fun_def}, @{thm feval_def}] *}

setup {* fold del_prfstep_thm [@{thm source_def}, @{thm target_def}, @{thm graph_def}] *}

(* A small exercise *)
lemma lam_eq_self: "f \<in> A \<rightarrow> B \<Longrightarrow> f = Fun(A,B, \<lambda>x. f`x)" by auto2

section {* Carrier of a structure *}

(* Underlying set of a structure. *)
definition carrier :: "i \<Rightarrow> i" where [rewrite]:
  "carrier(R) = fst(R)"

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

section {* Order structures *}

definition order_graph :: "i \<Rightarrow> i" where [rewrite]:
  "order_graph(R) = fst(snd(snd(R)))"

(* Evaluation of order *)
definition le :: "[i, i, i] \<Rightarrow> o" where [rewrite_bidir]:
  "le(R,x,y) \<longleftrightarrow> \<langle>x,y\<rangle> \<in> order_graph(R)"
abbreviation le_notation ("(_/ \<le>\<^sub>_ _)" [51,51,51] 50) where "x \<le>\<^sub>R y \<equiv> le(R,x,y)"
setup {* register_wellform_data ("x \<le>\<^sub>R y", ["x \<in>. R", "y \<in>. R"]) *}

abbreviation (input) ge :: "[i, i, i] \<Rightarrow> o" ("(_/ \<ge>\<^sub>_ _)" [51,51,51] 50) where
  "x \<ge>\<^sub>R y \<equiv> y \<le>\<^sub>R x"

(* General predicate on order. *)
definition raworder :: "i \<Rightarrow> o" where [rewrite]:
  "raworder(R) \<longleftrightarrow> order_graph(R) \<in> Pow(carrier(R)\<times>carrier(R))"

lemma raworderI [backward]:
  "G \<in> Pow(S\<times>S) \<Longrightarrow> raworder(\<langle>S,x1,G,x2\<rangle>)" by auto2

lemma raworderD [forward]:
  "raworder(R) \<Longrightarrow> x \<le>\<^sub>R y \<Longrightarrow> x \<in>. R \<and> y \<in>. R"
  "raworder(R) \<Longrightarrow> is_graph(order_graph(R))" by auto2+
setup {* del_prfstep_thm @{thm raworder_def} *}

(* Strict predicate on order. *)
definition ord_form :: "i \<Rightarrow> o" where [rewrite]:
  "ord_form(R) \<longleftrightarrow> raworder(R) \<and> R = \<langle>carrier(R),\<emptyset>,order_graph(R),\<emptyset>\<rangle>"
  
lemma ord_form_to_raw [forward]: "ord_form(R) \<Longrightarrow> raworder(R)" by auto2

(* Space of all order structures on S *)
definition raworder_space :: "i \<Rightarrow> i" where [rewrite]:
  "raworder_space(S) = {\<langle>S,\<emptyset>,G,\<emptyset>\<rangle>. G\<in>Pow(S\<times>S)}"
  
lemma raworder_spaceD [forward]:
  "R \<in> raworder_space(S) \<Longrightarrow> ord_form(R) \<and> carrier(R) = S" by auto2
    
lemma raworder_spaceI [resolve]:
  "ord_form(R) \<Longrightarrow> R \<in> raworder_space(carrier(R))" by auto2

(* Constructor for ordering *)
definition Order :: "i \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> o) \<Rightarrow> i" where [rewrite]:
  "Order(S,R) = \<langle>S, \<emptyset>, {p\<in>S\<times>S. R(fst(p),snd(p))}, \<emptyset>\<rangle>"

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

setup {* fold del_prfstep_thm [
  @{thm ord_form_def}, @{thm raworder_space_def}, @{thm Order_def}, @{thm le_def}] *}
setup {* add_rewrite_rule_back @{thm le_def} *}

setup {* fold del_prfstep_thm [@{thm carrier_def}, @{thm order_graph_def}] *}

end
