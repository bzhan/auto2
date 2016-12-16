theory Functions
imports Relations Choice
begin

section {* Functions *}  (* Bourbaki II.3.4 -- II.3.6 *)

(* A function is a relation where every element in the source corresponds
   to exactly one value in the target. *)
definition is_function :: "i \<Rightarrow> o" where is_function_def [rewrite]:
  "is_function(f) \<longleftrightarrow> (is_relation(f) \<and> (\<forall>x\<in>source(f). \<exists>!y. rel(f,x,y)))"
setup {* add_property_const @{term is_function} *}

(* The set of functions *)
definition function_space :: "i \<Rightarrow> i \<Rightarrow> i" (infixr "\<rightarrow>" 60)  where function_space_def [rewrite]:
  "A \<rightarrow> B = {f \<in> rel2_space(A,B). is_function(f)}"

lemma function_spaceD [forward]:
  "f \<in> A \<rightarrow> B \<Longrightarrow> is_function(f) \<and> source(f) = A \<and> target(f) = B" by auto2
setup {* add_fixed_sc ("Functions.function_spaceD", 1) *}

lemma function_spaceI [typing]:
  "is_function(f) \<Longrightarrow> f \<in> source(f) \<rightarrow> target(f)" by auto2

(* \<emptyset> is used as a default value. *)
lemma empty_not_function [resolve]: "\<emptyset> \<notin> function_space(S,T)" by auto2

(* Constructor for functions *)
definition lambda :: "i \<Rightarrow> i \<Rightarrow> (i \<Rightarrow> i) \<Rightarrow> i" where lambda_def [rewrite]:
  "lambda(A,B,b) = Rel2(A,B, \<lambda>x y. y=b(x))"

lemma lambda_is_function [backward]:
  "\<forall>x\<in>A. f(x)\<in>B \<Longrightarrow> lambda(A,B,f) \<in> A \<rightarrow> B"
  by (tactic {* auto2s_tac @{context} (HAVE "\<forall>x\<in>A. rel(lambda(A,B,f),x,f(x))") *})

(* Function evaluation *)
definition feval :: "i \<Rightarrow> i \<Rightarrow> i" (infixl "`" 90) where feval_def [rewrite]:
  "f ` x = (THE y. rel(f,x,y))"

lemma beta [rewrite]:
  "is_function(lambda(A,B,f)) \<Longrightarrow> x \<in> A \<Longrightarrow> lambda(A,B,f) ` x = f(x)" by auto2

lemma feval_in_range [typing]:
  "is_function(f) \<Longrightarrow> x \<in> source(f) \<Longrightarrow> f`x \<in> target(f)" by auto2

setup {* add_gen_prfstep ("lambda_case",
  [WithTerm @{term_pat "lambda(?A,?B,?b)"},
   CreateConcl @{term_pat "lambda(?A,?B,?b) \<in> ?A \<rightarrow> ?B"}]) *}

syntax
  "_lam" :: "[pttrn, i, i, i] \<Rightarrow> i"  ("(3\<lambda>_\<in>_./ _\<in>_)" 10)
translations
  "\<lambda>x\<in>A. f\<in>B" == "CONST lambda(A,B,\<lambda>x. f)"

(* Equality between functions *)
lemma function_eq:
  "is_function(f) \<Longrightarrow> is_function(g) \<Longrightarrow> source(f) = source(g) \<Longrightarrow> target(f) = target(g) \<Longrightarrow>
   (\<forall>x\<in>source(f). f`x = g`x) \<Longrightarrow> f = g" by auto2
setup {* add_backward_prfstep_cond @{thm function_eq} [with_filt (order_filter "f" "g")] *}

setup {* fold del_prfstep_thm [
  @{thm is_function_def}, @{thm function_space_def}, @{thm lambda_def}, @{thm feval_def}] *}

(* A small exercise *)
lemma lam_eq_self:
  "f \<in> A \<rightarrow> B \<Longrightarrow> f = lambda(A,B, \<lambda>x. f`x)" by auto2

(* Image under a function *)
definition fImage :: "i \<Rightarrow> i \<Rightarrow> i" (infixl "``" 90) where fImage_def [rewrite]:
  "fImage(f,A) = {y\<in>target(f). \<exists>x\<in>source(f). x\<in>A \<and> f`x=y}"

lemma fImageI [typing2]: "is_function(f) \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> source(f) \<Longrightarrow> f ` x \<in> f `` A" by auto2
lemma fImage_iff [rewrite]: "is_function(f) \<Longrightarrow> y \<in> f `` A \<longleftrightarrow> (\<exists>x\<in>source(f). x \<in> A \<and> f`x = y)" by auto2
setup {* del_prfstep_thm @{thm fImage_def} *}

lemma fImage_empty [rewrite]: "is_function(f) \<Longrightarrow> f `` \<emptyset> = \<emptyset>" by auto2
lemma fImage_mono [backward]: "is_function(f) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> f `` A \<subseteq> f `` B" by auto2

(* Inverse image under a function *)
definition fVImage :: "i \<Rightarrow> i \<Rightarrow> i"  (infixl "-``" 90) where fVImage_def [rewrite]:
  "fVImage(f,A) = {x\<in>source(f). f`x\<in>A}"

lemma fVImageI [typing2]: "is_function(f) \<Longrightarrow> f ` x \<in> A \<Longrightarrow> x \<in> source(f) \<Longrightarrow> x \<in> f -`` A" by auto2
lemma fVImage_iff [rewrite]: "is_function(f) \<Longrightarrow> x \<in> f -`` A \<longleftrightarrow> (x \<in> source(f) \<and> f ` x \<in> A)" by auto2
setup {* del_prfstep_thm @{thm fVImage_def} *}

lemma fVImage_empty [rewrite]: "is_function(f) \<Longrightarrow> f -`` \<emptyset> = \<emptyset>" by auto2
lemma fVImage_mono [backward]: "is_function(f) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> f -`` A \<subseteq> f -`` B" by auto2

(* Restrictions and extensions of functions *)
definition func_coincide :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o" where func_coincide_def [rewrite]:
  "func_coincide(f,g,E) \<longleftrightarrow> (E \<subseteq> source(f) \<and> E \<subseteq> source(g) \<and> (\<forall>x\<in>E. f`x = g`x))"

definition is_func_extension :: "i \<Rightarrow> i \<Rightarrow> o" where is_func_extension_def [rewrite]:
  "is_func_extension(f,g) \<longleftrightarrow> (source(g) \<subseteq> source(f) \<and> func_coincide(f,g,source(g)))"

(* Here we characterize when a function space is empty. *)
lemma empty_fun_space [rewrite]: "A \<rightarrow> B = \<emptyset> \<longleftrightarrow> A \<noteq> \<emptyset> \<and> B = \<emptyset>"
  by (tactic {* auto2s_tac @{context} (
    CASE "A \<rightarrow> B = \<emptyset>" WITH (  (* Show A \<noteq> 0 and B = 0 *)
      CASE "A = \<emptyset>" WITH HAVE "(\<lambda>a\<in>\<emptyset>. \<emptyset>\<in>B) \<in> A \<rightarrow> B" THEN
      CASE "B \<noteq> \<emptyset>" WITH (CHOOSE "b, b \<in> B" THEN HAVE "(\<lambda>a\<in>A. b\<in>B) \<in> A \<rightarrow> B")) THEN
    (* Know A \<noteq> \<emptyset> and B = \<emptyset>, show A \<rightarrow> B = \<emptyset> *)
    CHOOSE "f, f \<in> A \<rightarrow> B" THEN CHOOSE "a, a \<in> A" THEN HAVE "f ` a \<in> B") *})

section {* Important examples of functions *}

(* Identity function *)
definition id_fun :: "i \<Rightarrow> i" where id_fun_def [rewrite]:
  "id_fun(A) = (\<lambda>x\<in>A. x\<in>A)"

lemma id_fun_is_function [typing]: "id_fun(A) \<in> A \<rightarrow> A" by auto2
lemma id_fun_eval [rewrite]: "x \<in> A \<Longrightarrow> id_fun(A) ` x = x" by auto2
setup {* del_prfstep_thm @{thm id_fun_def} *}

(* Constant function *)
definition const_fun :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where const_fun_def [rewrite]:
  "const_fun(A,B,y) = (\<lambda>x\<in>A. y\<in>B)"

lemma const_fun_is_function [typing]: "y \<in> B \<Longrightarrow> const_fun(A,B,y) \<in> A \<rightarrow> B" by auto2
lemma const_fun_eval [rewrite]: "x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> const_fun(A,B,y) ` x = y" by auto2
setup {* del_prfstep_thm @{thm const_fun_def} *}

(* Restriction of function to a set A *)
definition func_restrict :: "i \<Rightarrow> i \<Rightarrow> i" where func_restrict_def [rewrite]:
  "func_restrict(f,A) = (\<lambda>x\<in>A. f`x\<in>target(f))"

lemma func_restrict_is_function [typing]:
  "is_function(f) \<Longrightarrow> A \<subseteq> source(f) \<Longrightarrow> func_restrict(f,A) \<in> A \<rightarrow> target(f)" by auto2
lemma func_restrict_eval [rewrite]:
  "is_function(f) \<Longrightarrow> A \<subseteq> source(f) \<Longrightarrow> x \<in> A \<Longrightarrow> func_restrict(f,A) ` x = f ` x" by auto2
setup {* add_gen_prfstep ("func_restrict_case",
  [WithTerm @{term_pat "func_restrict(?f,?A)"}, CreateConcl @{term_pat "?A \<subseteq> source(?f)"}]) *}
setup {* del_prfstep_thm @{thm func_restrict_def} *}

lemma extension_of_restrict [backward]:
  "is_function(f) \<Longrightarrow> A \<subseteq> source(f) \<Longrightarrow> is_func_extension(f,func_restrict(f,A))" by auto2

lemma func_coincide_iff [backward]:
  "is_function(f) \<Longrightarrow> is_function(g) \<Longrightarrow>
   E \<subseteq> source(f) \<and> E \<subseteq> source(g) \<and> target(f) = target(g) \<and> func_coincide(f,g,E) \<Longrightarrow>
   func_restrict(f,E) = func_restrict(g,E)" by auto2

(* Projection functions *)
definition proj1_fun :: "i \<Rightarrow> i \<Rightarrow> i" where proj1_fun_def [rewrite]:
  "proj1_fun(A,B) = (\<lambda>p\<in>A\<times>B. fst(p)\<in>A)"

lemma proj1_fun_is_function [typing]: "proj1_fun(A,B) \<in> A\<times>B \<rightarrow> A" by auto2
lemma proj1_eval [rewrite]: "p \<in> A\<times>B \<Longrightarrow> proj1_fun(A,B)`p = fst(p)" by auto2
setup {* del_prfstep_thm @{thm proj1_fun_def} *}

definition proj2_fun :: "i \<Rightarrow> i \<Rightarrow> i" where proj2_fun_def [rewrite]:
  "proj2_fun(A,B) = (\<lambda>p\<in>A\<times>B. snd(p)\<in>B)"

lemma proj2_fun_is_function [typing]: "proj2_fun(A,B) \<in> A\<times>B \<rightarrow> B" by auto2
lemma proj2_fun_eval [rewrite]: "p \<in> A\<times>B \<Longrightarrow> proj2_fun(A,B)`p = snd(p)" by auto2
setup {* del_prfstep_thm @{thm proj2_fun_def} *}

section {* Composition of and inverse of functions *}  (* Bourbaki II.3.7 *)

(* Composition of two functions. *)
definition fun_comp :: "i \<Rightarrow> i \<Rightarrow> i"  (infixr "O" 60) where fun_comp_def [rewrite]:
  "f' O f = (if is_function(f) then if is_function(f') then if target(f) = source(f') then
               (\<lambda>x\<in>source(f). (f' ` (f ` x))\<in>target(f'))
             else \<emptyset> else \<emptyset> else \<emptyset>)"

lemma comp_is_function [typing]:
  "is_function(f) \<Longrightarrow> is_function(f') \<Longrightarrow> target(f) = source(f') \<Longrightarrow>
   f' O f \<in> source(f) \<rightarrow> target(f')" by auto2

lemma comp_eval [rewrite]:
  "is_function(f) \<Longrightarrow> is_function(f') \<Longrightarrow> target(f) = source(f') \<Longrightarrow>
   x \<in> source(f) \<Longrightarrow> (f' O f) ` x = f' ` (f ` x)" by auto2
setup {* add_rewrite_rule_back_cond @{thm comp_eval} [with_term "?f' O ?f"] *}

lemma comp_non_fun:
  "\<not>is_function(f) \<Longrightarrow> f' O f = \<emptyset> \<and> \<not>is_function(\<emptyset>)"
  "\<not>is_function(f') \<Longrightarrow> f' O f = \<emptyset> \<and> \<not>is_function(\<emptyset>)"
  "target(f) \<noteq> source(f') \<Longrightarrow> f' O f = \<emptyset> \<and> \<not>is_function(\<emptyset>)" by auto2+
setup {* fold (fn th => add_forward_prfstep_cond th [with_term "?f' O ?f"]) @{thms comp_non_fun} *}
setup {* del_prfstep_thm @{thm fun_comp_def} *}

setup {* add_gen_prfstep ("comp_fun_case",
  [WithTerm @{term_pat "?f' O ?f"},
   CreateConcl @{term_pat "target(?f) = source(?f')"}]) *}

lemma comp_assoc: "(x O y) O z = x O (y O z)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "is_function(x)" THEN HAVE "is_function(y)" THEN HAVE "is_function(z)" THEN
    HAVE "target(z) = source(y)" THEN HAVE "target(y) = source(x)") *})
setup {* fold del_prfstep_thm @{thms comp_non_fun} *}

ML {*
val comp_ac = ACUtil.constr_ac_info_au {
  assoc_th = @{thm comp_assoc},
  unitl_th = true_th, unitr_th = true_th}
*}
setup {* ACUtil.add_ac_data ("fun_comp", comp_ac) *}

lemma comp_id_left [rewrite]:
  "is_function(f) \<Longrightarrow> id_fun(target(f)) O f = f" by auto2

lemma comp_id_right [rewrite]:
  "is_function(f) \<Longrightarrow> f O id_fun(source(f)) = f" by auto2

(* Injective, surjective, and bijective functions. *)
definition injective :: "i \<Rightarrow> o" where injective_def [rewrite]:
  "injective(f) \<longleftrightarrow> (is_function(f) \<and> (\<forall>x\<in>source(f). \<forall>y\<in>source(f). f`x = f`y \<longrightarrow> x=y))"
setup {* add_property_const @{term injective} *}

definition surjective :: "i \<Rightarrow> o" where surjective_def [rewrite]:
  "surjective(f) \<longleftrightarrow> (is_function(f) \<and> (f `` source(f) = target(f)))"
setup {* add_property_const @{term surjective} *}

definition bijective :: "i \<Rightarrow> o" where bijective_def [rewrite]:
  "bijective(f) \<longleftrightarrow> (injective(f) \<and> surjective(f))"
setup {* add_property_const @{term bijective} *}

lemma injectiveD [forward]:
  "injective(f) \<Longrightarrow> is_function(f)"
  "injective(f) \<Longrightarrow> f`x = f`y \<Longrightarrow> x \<in> source(f) \<Longrightarrow> y \<in> source(f) \<Longrightarrow> x = y" by auto2+

lemma surjectiveD:
  "surjective(f) \<Longrightarrow> is_function(f)"
  "surjective(f) \<Longrightarrow> y \<in> target(f) \<Longrightarrow> \<exists>x\<in>source(f). f ` x = y"
  "surjective(f) \<Longrightarrow> f `` source(f) = target(f)" by auto2+
setup {* fold add_forward_prfstep @{thms surjectiveD(1-2)} *}
setup {* add_backward_prfstep @{thm surjectiveD(2)} *}
setup {* add_fixed_sc ("Functions.surjectiveD_2", 500) *}
setup {* add_rewrite_rule @{thm surjectiveD(3)} *}

lemma bijectiveD [forward]:
  "bijective(f) \<Longrightarrow> injective(f)"
  "bijective(f) \<Longrightarrow> surjective(f)" by auto2+

setup {* fold del_prfstep_thm [
  @{thm injective_def}, @{thm surjective_def}, @{thm bijective_def}] *}
setup {* fold (add_backward_prfstep o equiv_backward_th) [
  @{thm injective_def}, @{thm surjective_def}, @{thm bijective_def}] *}

definition bijection_space :: "i \<Rightarrow> i \<Rightarrow> i"  (infix "\<cong>" 60) where bijection_space_def [rewrite]:
  "A \<cong> B = {f \<in> A \<rightarrow> B. bijective(f)}"

lemma bijective_spaceD [forward]:
  "f \<in> A \<cong> B \<Longrightarrow> f \<in> A \<rightarrow> B \<and> bijective(f)" by auto2

lemma bijective_spaceI [typing, backward]:
  "bijective(f) \<Longrightarrow> f \<in> source(f) \<cong> target(f)" by auto2
setup {* del_prfstep_thm @{thm bijection_space_def} *}

(* Some properties of surjective functions *)
lemma surjective_to_singleton [backward2]:
  "f \<in> A \<rightarrow> {x} \<Longrightarrow> A \<noteq> \<emptyset> \<Longrightarrow> surjective(f)" by auto2

lemma surj_source_nonempty [forward, backward]:
  "surjective(f) \<Longrightarrow> target(f) \<noteq> \<emptyset> \<Longrightarrow> source(f) \<noteq> \<emptyset>" by auto2

(* Properties of bijective functions *)
lemma bijective_exist_unique [backward]:
  "bijective(f) \<Longrightarrow> y \<in> target(f) \<Longrightarrow> \<exists>!x. x\<in>source(f) \<and> f`x=y" by auto2

(* Example: canonical injection. *)
definition inj_fun :: "i \<Rightarrow> i \<Rightarrow> i" where inj_fun_def [rewrite]:
  "inj_fun(A,B) = (\<lambda>x\<in>A. x\<in>B)"

lemma inj_fun_is_function [typing]: "A \<subseteq> B \<Longrightarrow> inj_fun(A,B) \<in> A \<rightarrow> B" by auto2
lemma inj_fun_eval [rewrite]: "x \<in> A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> inj_fun(A,B) ` x = x" by auto2
setup {* del_prfstep_thm @{thm inj_fun_def} *}

lemma inj_fun_is_injection: "A \<subseteq> B \<Longrightarrow> injective(inj_fun(A,B))" by auto2

(* Other examples. *)
lemma id_bij: "id_fun(A) \<in> A \<cong> A" by auto2
lemma proj1_surj: "B \<noteq> \<emptyset> \<Longrightarrow> surjective(proj1_fun(A,B))"
  by (tactic {* auto2s_tac @{context} (CHOOSE "b, b \<in> B" THEN HAVE "\<forall>a\<in>A. \<langle>a,b\<rangle>\<in>A\<times>B") *})
lemma proj2_surj: "A \<noteq> \<emptyset> \<Longrightarrow> surjective(proj2_fun(A,B))"
  by (tactic {* auto2s_tac @{context} (CHOOSE "a, a \<in> A" THEN HAVE "\<forall>b\<in>B. \<langle>a,b\<rangle>\<in>A\<times>B") *})
lemma swap_bij: "(\<lambda>p\<in>A\<times>B. \<langle>snd(p),fst(p)\<rangle>\<in>B\<times>A) \<in> A\<times>B \<cong> B\<times>A"
  by (tactic {* auto2s_tac @{context} (HAVE "\<forall>p\<in>B\<times>A. \<langle>snd(p),fst(p)\<rangle> \<in> A\<times>B") *})
lemma pair_bij: "(\<lambda>x\<in>A. \<langle>x,b\<rangle>\<in>A\<times>{b}) \<in> A \<cong> A\<times>{b}" by auto2
lemma rpair_bij: "(\<lambda>x\<in>A. \<langle>b,x\<rangle>\<in>{b}\<times>A) \<in> A \<cong> {b}\<times>A" by auto2

(* Inverse function *)
definition inverse :: "i \<Rightarrow> i" where inverse_def [rewrite]:
  "inverse(f) = (\<lambda>y\<in>target(f). (THE x. x\<in>source(f) \<and> f`x=y)\<in>source(f))"

lemma has_inverse [typing]:
  "bijective(f) \<Longrightarrow> inverse(f) \<in> target(f) \<rightarrow> source(f)" by auto2

lemma inverse_eval1 [rewrite]:
  "bijective(f) \<Longrightarrow> f ` x = y \<Longrightarrow> x \<in> source(f) \<Longrightarrow> inverse(f) ` y = x" by auto2

lemma inverse_eval2 [rewrite]:
  "bijective(f) \<Longrightarrow> inverse(f) ` y = x \<Longrightarrow> y \<in> target(f) \<Longrightarrow> f ` x = y" by auto2
setup {* del_prfstep_thm @{thm inverse_def} *}

lemma inverse_bij [forward]: "bijective(f) \<Longrightarrow> surjective(inverse(f))"
  by (tactic {* auto2s_tac @{context} (HAVE "\<forall>x\<in>source(f). inverse(f)`(f`x) = x") *})

lemma inverse_of_inj [rewrite]:
  "injective(f) \<Longrightarrow> X \<subseteq> source(f) \<Longrightarrow> f -`` (f `` X) = X" by auto2

lemma inverse_of_surj [rewrite]:
  "surjective(f) \<Longrightarrow> Y \<subseteq> target(f) \<Longrightarrow> f `` (f -`` Y) = Y" by auto2

lemma inverse_is_left_inv [rewrite]:
  "bijective(f) \<Longrightarrow> inverse(f) O f = id_fun(source(f))" by auto2

lemma inverse_is_right_inv [rewrite]:
  "bijective(f) \<Longrightarrow> f O inverse(f) = id_fun(target(f))" by auto2

setup {* add_gen_prfstep ("inverse_fun_case",
  [WithTerm @{term_pat "inverse(?f)"}, CreateConcl @{term_pat "bijective(?f)"}]) *}

section {* Left and right inverses *}  (* Bourbaki II.3.8 *)

(* Left and right inverses always exists, but that takes more work. *)
lemma has_left_inverse_inj [forward]:
  "r O f = id_fun(A) \<Longrightarrow> f \<in> A \<rightarrow> B \<Longrightarrow> r \<in> B \<rightarrow> A \<Longrightarrow> injective(f)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x\<in>source(f). \<forall>y\<in>source(f). f`x = f`y \<longrightarrow> x=y" WITH HAVE "r`(f`x)=x") *})

lemma has_right_inverse_surj [forward]:
  "f O s = id_fun(B) \<Longrightarrow> f \<in> A \<rightarrow> B \<Longrightarrow> s \<in> B \<rightarrow> A \<Longrightarrow> surjective(f)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x\<in>target(f). x\<in>f``source(f)" WITH HAVE "f`(s`x) = x") *})

lemma has_left_right_inverse_bij [forward]:
  "r O f = id_fun(A) \<Longrightarrow> f O s = id_fun(B) \<Longrightarrow>
   f \<in> A \<rightarrow> B \<Longrightarrow> r \<in> B \<rightarrow> A \<Longrightarrow> s \<in> B \<rightarrow> A \<Longrightarrow> f \<in> A \<cong> B" by auto2

lemma right_inverse_unique:
  "surjective(f) \<Longrightarrow> f O s = id_fun(B) \<Longrightarrow> f O s' = id_fun(B) \<Longrightarrow>
   f \<in> A \<rightarrow> B \<Longrightarrow> s \<in> B \<rightarrow> A \<Longrightarrow> s' \<in> B \<rightarrow> A \<Longrightarrow> s `` B = s' `` B \<Longrightarrow> s = s'"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x\<in>B. s`x = s'`x" WITH HAVE "f`(s`x) = x") *})

(* Two functions are inverses of each other. This pattern occurs very frequently. *)
definition inverse_pair :: "i \<Rightarrow> i \<Rightarrow> o" where inverse_pair_def [rewrite]:
  "inverse_pair(f,g) \<longleftrightarrow> (is_function(f) \<and> is_function(g) \<and> source(f) = target(g) \<and> target(f) = source(g) \<and>
                          f O g = id_fun(source(g)) \<and> g O f = id_fun(source(f)))"

lemma inverse_pair_bijective [forward]:
  "inverse_pair(f,g) \<Longrightarrow> source(f) = target(g) \<and> source(g) = target(f) \<and> bijective(f) \<and> bijective(g)" by auto2

lemma inverse_pairI [backward]:
  "is_function(f) \<Longrightarrow> is_function(g) \<Longrightarrow> source(f) = target(g) \<Longrightarrow> source(g) = target(f) \<Longrightarrow>
   \<forall>x\<in>source(g). f`(g`x) = x \<Longrightarrow> \<forall>x\<in>source(f). g`(f`x) = x \<Longrightarrow> inverse_pair(f,g)" by auto2

lemma inverse_pairE [rewrite]:
  "inverse_pair(f,g) \<Longrightarrow> f O g = id_fun(source(g))"
  "inverse_pair(f,g) \<Longrightarrow> g O f = id_fun(source(f))" by auto2+
setup {* del_prfstep_thm @{thm inverse_pair_def} *}

(* Six parts of Theorem 1 in Bourbaki II.3.8. May be easier with existence
   of left/right-inverse, but not necessary. *)
lemma comp_is_inj:
  "injective(f) \<Longrightarrow> injective(f') \<Longrightarrow> target(f) = source(f') \<Longrightarrow> injective(f' O f)" by auto2
setup {* add_forward_prfstep_cond @{thm comp_is_inj} [with_term "?f' O ?f"] *}

lemma comp_is_surj:
  "surjective(f) \<Longrightarrow> surjective(f') \<Longrightarrow> target(f) = source(f') \<Longrightarrow> surjective(f' O f)" by auto2
setup {* add_forward_prfstep_cond @{thm comp_is_surj} [with_term "?f' O ?f"] *}

lemma comp_is_inj_to_first_inj [forward]:
  "is_function(f) \<Longrightarrow> is_function(f') \<Longrightarrow> target(f) = source(f') \<Longrightarrow> injective(f' O f) \<Longrightarrow> injective(f)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x\<in>source(f). \<forall>y\<in>source(f). f`x = f`y \<longrightarrow> x=y" WITH
      HAVE "(f' O f) ` x = (f' O f) ` y") *})

lemma comp_is_surj_to_second_surj [forward]:
  "is_function(f) \<Longrightarrow> is_function(f') \<Longrightarrow> target(f) = source(f') \<Longrightarrow> surjective(f' O f) \<Longrightarrow> surjective(f')"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x\<in>target(f'). x\<in>(f' O f)``source(f)") *})

lemma comp_is_surj_to_first_surj [forward]:
  "is_function(f) \<Longrightarrow> injective(f') \<Longrightarrow> target(f) = source(f') \<Longrightarrow> surjective(f' O f) \<Longrightarrow> surjective(f)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "f = inverse(f') O (f' O f)") *})

lemma comp_is_inj_to_second_inj [forward]:
  "surjective(f) \<Longrightarrow> is_function(f') \<Longrightarrow> target(f) = source(f') \<Longrightarrow> injective(f' O f) \<Longrightarrow> injective(f')"
  by (tactic {* auto2s_tac @{context} (
    HAVE "f' = (f' O f) O inverse(f)") *})

lemma inverse_unique [forward]:
  "bijective(f) \<Longrightarrow> is_function(f') \<Longrightarrow> target(f) = source(f') \<Longrightarrow>
   f' O f = id_fun(source(f)) \<Longrightarrow> f' = inverse(f)" by auto2

lemma inverse_unique' [forward]:
  "bijective(f) \<Longrightarrow> is_function(f') \<Longrightarrow> target(f') = source(f) \<Longrightarrow>
   f O f' = id_fun(target(f)) \<Longrightarrow> f' = inverse(f)" by auto2

(* Now we construct the left and right inverses explicitly. *)
lemma exists_right_inverse [resolve]:
  "surjective(f) \<Longrightarrow> f \<in> A \<rightarrow> B \<Longrightarrow> \<exists>s\<in>B\<rightarrow>A. f O s = id_fun(B)"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "s, s = (\<lambda>y\<in>B. (SOME x\<in>A. f`x=y)\<in>A)") *})

definition right_inverse :: "i \<Rightarrow> i" where right_inverse_def [rewrite]:
  "right_inverse(f) = (SOME s\<in>target(f)\<rightarrow>source(f). f O s = id_fun(target(f)))"

lemma right_inverse_prop:
  "surjective(f) \<Longrightarrow> f \<in> A \<rightarrow> B \<Longrightarrow> right_inverse(f) \<in> B \<rightarrow> A \<and> f O right_inverse(f) = id_fun(B)" by auto2
setup {* add_forward_prfstep_cond @{thm right_inverse_prop} [with_term "right_inverse(?f)"] *}
setup {* del_prfstep_thm @{thm right_inverse_def} *}

lemma exists_left_inverse [backward2]:
  "injective(f) \<Longrightarrow> f \<in> A \<rightarrow> B \<Longrightarrow> A \<noteq> \<emptyset> \<Longrightarrow> \<exists>r\<in>B\<rightarrow>A. r O f = id_fun(A)"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "a, a \<in> A" THEN
     CHOOSE "r, r = (\<lambda>y\<in>B. (if (\<exists>x\<in>A. f`x=y) then (SOME x\<in>A. f`x=y) else a)\<in>A)") *})

definition left_inverse :: "i \<Rightarrow> i" where left_inverse_def [rewrite]:
  "left_inverse(f) = (SOME r\<in>target(f)\<rightarrow>source(f). r O f = id_fun(source(f)))"

lemma left_inverse_prop:
  "injective(f) \<Longrightarrow> f \<in> A \<rightarrow> B \<Longrightarrow> A \<noteq> \<emptyset> \<Longrightarrow> left_inverse(f) \<in> B \<rightarrow> A \<and> left_inverse(f) O f = id_fun(A)" by auto2
setup {* add_forward_prfstep_cond @{thm left_inverse_prop} [with_term "left_inverse(?f)"] *}
setup {* add_gen_prfstep ("left_inverse_case",
  [WithTerm @{term_pat "left_inverse(?f)"}, CreateConcl @{term_pat "source(?f) \<noteq> \<emptyset>"}]) *}
setup {* del_prfstep_thm @{thm left_inverse_def} *}

(* Using left and right inverses to construct functions. *)
lemma exists_pullback_surj [backward1]: 
  "surjective(g) \<Longrightarrow> g \<in> E \<rightarrow> F \<Longrightarrow> f \<in> E \<rightarrow> G \<Longrightarrow> \<forall>x\<in>E. \<forall>y\<in>E. g`x=g`y \<longrightarrow> f`x=f`y \<Longrightarrow>
   \<exists>!h. h\<in>F\<rightarrow>G \<and> f = h O g"
  by (tactic {* auto2s_tac @{context}
    (HAVE "\<exists>h\<in>F\<rightarrow>G. f = h O g" WITH (
      CHOOSE "s\<in>F\<rightarrow>E, g O s = id_fun(F)" THEN
      CHOOSE "h\<in>F\<rightarrow>G, h = f O s")) *})

lemma exists_pullback_inj:
  "injective(g) \<Longrightarrow> g \<in> F \<rightarrow> E \<Longrightarrow> f \<in> G \<rightarrow> E \<Longrightarrow> F \<noteq> \<emptyset> \<Longrightarrow> f``G \<subseteq> g``F \<Longrightarrow>
   \<exists>!h. h\<in>G\<rightarrow>F \<and> f = g O h"
  by (tactic {* auto2s_tac @{context}
    (HAVE "\<exists>h\<in>G\<rightarrow>F. f = g O h" WITH (
      CHOOSE "r\<in>E\<rightarrow>F, r O g = id_fun(F)" THEN
      CHOOSE "h\<in>G\<rightarrow>F, h = r O f")) *})

section {* Function of two arguments *}  (* Bourbaki II.3.9 *)

(* We consider functions on product sets only. *)

(* Currying: given a function (A \<times> B) \<rightarrow> D, return a function A \<rightarrow> (B \<rightarrow> D). *)
definition curry :: "[i, i, i] \<Rightarrow> i" where curry_def [rewrite]:
  "curry(A,B,D) = (\<lambda>f\<in>(A\<times>B)\<rightarrow>D. (\<lambda>x\<in>A. (\<lambda>y\<in>B. f`\<langle>x,y\<rangle>\<in>D)\<in>B\<rightarrow>D)\<in>(A\<rightarrow>(B\<rightarrow>D)))"

lemma curry_is_function [typing]:
  "curry(A,B,D) \<in> ((A \<times> B) \<rightarrow> D) \<rightarrow> (A \<rightarrow> (B \<rightarrow> D))" by auto2

lemma curry_eval [rewrite]:
  "f \<in> (A \<times> B) \<rightarrow> D \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> curry(A,B,D)`f`x`y = f`\<langle>x,y\<rangle>" by auto2
setup {* del_prfstep_thm @{thm curry_def} *}

(* Constant functions *)
definition is_const_fun :: "i \<Rightarrow> o" where is_const_fun_def [rewrite]:
  "is_const_fun(f) \<longleftrightarrow> (\<forall>x\<in>source(f). \<forall>y\<in>source(f). f`x = f`y)"
setup {* add_property_const @{term is_const_fun} *}

lemma is_const_funD [forward]:
  "is_const_fun(f) \<Longrightarrow> x \<in> source(f) \<Longrightarrow> y \<in> source(f) \<Longrightarrow> f`x = f`y" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm is_const_fun_def} *}

(* Functions that do not depend on the second argument. *)
lemma exists_proj_fun:
  "B \<noteq> \<emptyset> \<Longrightarrow> f \<in> (A \<times> B) \<rightarrow> D \<Longrightarrow> \<forall>x\<in>A. is_const_fun(curry(A,B,D)`f`x) \<Longrightarrow>
   \<exists>g\<in>A\<rightarrow>D. \<forall>x\<in>A. \<forall>y\<in>B. f`\<langle>x,y\<rangle> = g`x"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "y, y \<in> B" THEN CHOOSE "g, g = (\<lambda>x\<in>A. f`\<langle>x,y\<rangle>\<in>D)") *})

(* Product map *)
definition prod_map :: "i \<Rightarrow> i \<Rightarrow> i" (infixr "\<times>\<^sub>f" 80) where prod_map_def [rewrite]:
  "u \<times>\<^sub>f v = (\<lambda>p\<in>source(u)\<times>source(v). \<langle>u`fst(p), v`snd(p)\<rangle> \<in> target(u)\<times>target(v))"

lemma prod_map_is_function [typing]:
  "is_function(u) \<Longrightarrow> is_function(v) \<Longrightarrow> u \<times>\<^sub>f v \<in> source(u)\<times>source(v) \<rightarrow> target(u)\<times>target(v)" by auto2

lemma prod_map_eval [rewrite]:
  "is_function(u) \<Longrightarrow> is_function(v) \<Longrightarrow> x \<in> source(u) \<Longrightarrow> y \<in> source(v) \<Longrightarrow>
   (u \<times>\<^sub>f v) ` \<langle>x,y\<rangle> = \<langle>u`x, v`y\<rangle>" by auto2
setup {* del_prfstep_thm @{thm prod_map_def} *}

lemma prod_map_inj [forward]:
  "injective(u) \<Longrightarrow> injective(v) \<Longrightarrow> injective(u \<times>\<^sub>f v)" by auto2

lemma prod_map_surj [forward]:
  "surjective(u) \<Longrightarrow> surjective(v) \<Longrightarrow> surjective(u \<times>\<^sub>f v)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>p\<in>target(u \<times>\<^sub>f v). p\<in>(u \<times>\<^sub>f v)``source(u \<times>\<^sub>f v)" WITH (
     CHOOSE "x\<in>source(u), u`x=fst(p)" THEN CHOOSE "y\<in>source(v), v`y=snd(p)" THEN
     HAVE "(u \<times>\<^sub>f v)`\<langle>x,y\<rangle> = p")) *})

lemma prod_map_bij [forward]:
  "bijective(u) \<Longrightarrow> bijective(v) \<Longrightarrow> bijective(u \<times>\<^sub>f v)" by auto2

lemma prod_map_comp [rewrite]:
  "is_function(u) \<Longrightarrow> is_function(u') \<Longrightarrow> is_function(v) \<Longrightarrow> is_function(v') \<Longrightarrow>
   target(u) = source(u') \<Longrightarrow> target(v) = source(v') \<Longrightarrow>
   (u' O u) \<times>\<^sub>f (v' O v) = (u' \<times>\<^sub>f v') O (u \<times>\<^sub>f v)" by auto2

lemma prod_map_id_fun [rewrite]:
  "(id_fun(A) \<times>\<^sub>f id_fun(B)) = id_fun(A\<times>B)" by auto2

lemma prod_inverse [rewrite]:
  "bijective(u) \<Longrightarrow> bijective(v) \<Longrightarrow> inverse(u) \<times>\<^sub>f inverse(v) = inverse(u \<times>\<^sub>f v)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "(u \<times>\<^sub>f v) O (inverse(u) \<times>\<^sub>f inverse(v)) = (u O inverse(u)) \<times>\<^sub>f (v O inverse(v))") *})

section {* Extension of a function to Pow *}  (* Bourbaki II.5.1 *)

definition pow_ext :: "i \<Rightarrow> i" where pow_ext_def [rewrite]:
  "pow_ext(f) = (\<lambda>X\<in>Pow(source(f)). (f `` X)\<in>Pow(target(f)))"

lemma pow_ext_is_function [typing]:
  "is_function(f) \<Longrightarrow> pow_ext(f) \<in> Pow(source(f)) \<rightarrow> Pow(target(f))" by auto2

lemma pow_ext_eval [rewrite]:
  "is_function(f) \<Longrightarrow> X \<subseteq> source(f) \<Longrightarrow> pow_ext(f) ` X = f `` X" by auto2
setup {* del_prfstep_thm @{thm pow_ext_def} *}

lemma pow_ext_comp [rewrite]:
  "is_function(f) \<Longrightarrow> is_function(g) \<Longrightarrow> target(f) = source(g) \<Longrightarrow>
   pow_ext(g O f) = pow_ext(g) O pow_ext(f)" by auto2

lemma pow_ext_id [rewrite]:
  "pow_ext(id_fun(A)) = id_fun(Pow(A))" by auto2

lemma pow_ext_surj [backward]:
  "surjective(f) \<Longrightarrow> surjective(pow_ext(f))"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "A, B, f \<in> A \<rightarrow> B" THEN
    CHOOSE "s\<in>B\<rightarrow>A, f O s = id_fun(target(f))" THEN
    HAVE "pow_ext(f O s) = pow_ext(f) O pow_ext(s)") *})

lemma pow_ext_inj [backward]:
  "injective(f) \<Longrightarrow> injective(pow_ext(f))" by auto2

section {* Map on function spaces *}  (* Bourbaki II.5.2 *)

(* Define left and right composition separately. *)

definition left_comp :: "i \<Rightarrow> i \<Rightarrow> i" where left_comp_def [rewrite]:
  "left_comp(u,E) = (\<lambda>f\<in>E\<rightarrow>source(u). (u O f)\<in>E\<rightarrow>target(u))"

lemma left_comp_is_function [typing]:
  "is_function(u) \<Longrightarrow> left_comp(u,E) \<in> (E\<rightarrow>source(u)) \<rightarrow> (E\<rightarrow>target(u))" by auto2

lemma left_comp_eval [rewrite]:
  "is_function(u) \<Longrightarrow> f \<in> E\<rightarrow>source(u) \<Longrightarrow> left_comp(u,E) ` f = u O f" by auto2
setup {* del_prfstep_thm @{thm left_comp_def} *}

lemma injective_left_comp [forward]:
  "injective(u) \<Longrightarrow> injective(left_comp(u,E))"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r\<in>target(u)\<rightarrow>source(u), r O u = id_fun(source(u))" THEN
    HAVE "left_comp(r,E) O left_comp(u,E) = id_fun(E\<rightarrow>source(u))" WITH (
      HAVE "\<forall>f\<in>E\<rightarrow>source(u). left_comp(r,E) ` (left_comp(u,E) ` f) = f" WITH (
        HAVE "r O (u O f) = (r O u) O f"))) *})

lemma surjective_left_comp [forward]:
  "surjective(u) \<Longrightarrow> surjective(left_comp(u,E))"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "s\<in>target(u)\<rightarrow>source(u), u O s = id_fun(target(u))" THEN
    HAVE "left_comp(u,E) O left_comp(s,E) = id_fun(E\<rightarrow>target(u))") *})

lemma bijective_left_comp [forward]:
  "bijective(u) \<Longrightarrow> bijective(left_comp(u,E))" by auto2

definition right_comp :: "i \<Rightarrow> i \<Rightarrow> i" where right_comp_def [rewrite]:
  "right_comp(E,u) = (\<lambda>f\<in>target(u)\<rightarrow>E. (f O u)\<in>source(u)\<rightarrow>E)"

lemma right_comp_is_function [typing]:
  "is_function(u) \<Longrightarrow> right_comp(E,u) \<in> (target(u)\<rightarrow>E) \<rightarrow> (source(u)\<rightarrow>E)" by auto2

lemma right_comp_eval [rewrite]:
  "is_function(u) \<Longrightarrow> f \<in> target(u)\<rightarrow>E \<Longrightarrow> right_comp(E,u) ` f = f O u" by auto2
setup {* del_prfstep_thm @{thm right_comp_def} *}

lemma injective_right_comp [forward]:
  "surjective(u) \<Longrightarrow> injective(right_comp(E,u))"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "s\<in>target(u)\<rightarrow>source(u), u O s = id_fun(target(u))" THEN
    HAVE "right_comp(E,s) O right_comp(E,u) = id_fun(target(u)\<rightarrow>E)") *})

lemma surjective_right_comp [backward]:
  "injective(u) \<Longrightarrow> source(u) \<noteq> \<emptyset> \<Longrightarrow> surjective(right_comp(E,u))"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r\<in>target(u)\<rightarrow>source(u), r O u = id_fun(source(u))" THEN
    HAVE "right_comp(E,u) O right_comp(E,r) = id_fun(target(r)\<rightarrow>E)") *})

(* The requirement that source(u) \<noteq> \<emptyset> is necessary here, as the following example shows. *)
lemma injective_two_side_comp_counterexample:
  "u = (\<lambda>a\<in>\<emptyset>. \<emptyset>\<in>{\<emptyset>}) \<Longrightarrow> injective(u) \<and> \<not>surjective(right_comp(\<emptyset>,u))"
  by (tactic {* auto2s_tac @{context} (HAVE "target(u) \<rightarrow> \<emptyset> = \<emptyset>") *})

(* Nevertheless, no condition is required when u is bijective. *)
lemma bijective_right_comp [forward]:
  "bijective(u) \<Longrightarrow> bijective(right_comp(E,u))" by auto2

(* Given a function A \<rightarrow> (B \<rightarrow> D), return a function (A \<times> B) \<rightarrow> D. *)
definition uncurry :: "[i, i, i] \<Rightarrow> i" where uncurry_def [rewrite]:
  "uncurry(A,B,D) = (\<lambda>f\<in>A\<rightarrow>B\<rightarrow>D. (\<lambda>x\<in>A\<times>B. (f`fst(x)`snd(x))\<in>D)\<in>(A\<times>B\<rightarrow>D))"

lemma uncurry_is_function [typing]:
  "uncurry(A,B,D) \<in> (A \<rightarrow> B \<rightarrow> D) \<rightarrow> (A \<times> B \<rightarrow> D)" by auto2

lemma uncurry_eval [rewrite]:
  "f \<in> A \<rightarrow> (B \<rightarrow> D) \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> uncurry(A,B,D)`f`\<langle>x,y\<rangle> = f`x`y" by auto2
setup {* del_prfstep_thm @{thm uncurry_def} *}

lemma curry_bijective [forward]: "bijective(curry(A,B,D))"
  by (tactic {* auto2s_tac @{context} (
    HAVE "inverse_pair(curry(A,B,D), uncurry(A,B,D))") *})

end
