(*
  File: Functions.thy
  Author: Bohua Zhan

  Basic results on (set-theoretic) functions.
*)

theory Functions
  imports Choice
begin

section {* Functions *}  (* Bourbaki II.3.4 -- II.3.6 *)

(* Image under a function *)
definition image_on :: "i \<Rightarrow> i \<Rightarrow> i" (infixl "``" 90) where [rewrite]:
  "f `` A = {y\<in>target(f). \<exists>x\<in>source(f). x\<in>A \<and> f`x=y}"

lemma image_onI [backward]: "is_function(f) \<Longrightarrow> x \<in> source(f) \<Longrightarrow> x \<in> A \<Longrightarrow> f ` x \<in> f `` A" by auto2
lemma image_onD [forward]: "is_function(f) \<Longrightarrow> y \<in> f `` A \<Longrightarrow> \<exists>x\<in>source(f). x \<in> A \<and> f`x = y" by auto2
setup {* del_prfstep_thm @{thm image_on_def} *}

lemma image_on_empty [rewrite]: "is_function(f) \<Longrightarrow> f `` \<emptyset> = \<emptyset>" by auto2
lemma image_on_mono [backward]: "is_function(f) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> f `` A \<subseteq> f `` B" by auto2

lemma image_non_empty [backward]: "is_function(f) \<Longrightarrow> S \<subseteq> source(f) \<Longrightarrow> S \<noteq> \<emptyset> \<Longrightarrow> f `` S \<noteq> \<emptyset>"
@proof
  @obtain x where "x \<in> S"
  @have "f`x \<in> f``S"
@qed

definition image :: "i \<Rightarrow> i" where image_def [rewrite_bidir]:
  "image(f) = f `` source(f)"
lemma image_in_target: "is_function(f) \<Longrightarrow> image(f) \<subseteq> target(f)" by auto2
setup {* add_forward_prfstep_cond @{thm image_in_target} [with_term "image(?f)"] *}

lemma imageI: "is_function(f) \<Longrightarrow> x \<in> source(f) \<Longrightarrow> f`x \<in> image(f)" by auto2
setup {* add_forward_prfstep_cond @{thm imageI} [with_term "?f`?x", with_term "image(?f)"] *}

(* Inverse image under a function *)
definition fVImage :: "i \<Rightarrow> i \<Rightarrow> i"  (infixl "-``" 90) where [rewrite]:
  "fVImage(f,A) = {x\<in>source(f). f`x\<in>A}"

lemma fVImageI [typing2]: "is_function(f) \<Longrightarrow> x \<in> source(f) \<Longrightarrow> f ` x \<in> A \<Longrightarrow> x \<in> f -`` A" by auto2
lemma fVImage_iff [rewrite]: "is_function(f) \<Longrightarrow> x \<in> f -`` A \<longleftrightarrow> (x \<in> source(f) \<and> f ` x \<in> A)" by auto2
setup {* del_prfstep_thm @{thm fVImage_def} *}

lemma fVImage_empty [rewrite]: "is_function(f) \<Longrightarrow> f -`` \<emptyset> = \<emptyset>" by auto2
lemma fVImage_mono [backward]: "is_function(f) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> f -`` A \<subseteq> f -`` B" by auto2
lemma fVImage_compl [rewrite]: "is_function(f) \<Longrightarrow> f -`` (target(f) \<midarrow> A) = source(f) \<midarrow> (f -`` A)" by auto2    
lemma fVImage_union [rewrite]: "is_function(f) \<Longrightarrow> (f -`` A) \<union> (f -`` B) = f -`` (A \<union> B)" by auto2
lemma fVImage_target [rewrite]: "is_function(f) \<Longrightarrow> f -`` target(f) = source(f)" by auto2

lemma fVImage_subset [backward1]: "is_function(f) \<Longrightarrow> U \<subseteq> source(f) \<Longrightarrow> f `` U \<subseteq> V \<Longrightarrow> U \<subseteq> f -`` V"
@proof
  @have "\<forall>x'\<in>U. x'\<in>f-``V" @with
    @have "f`x' \<in> f``U" @have "f`x' \<in> V"
  @end
@qed

(* Here we characterize when a function space is empty. *)
lemma empty_fun_space [rewrite]: "A \<rightarrow> B = \<emptyset> \<longleftrightarrow> A \<noteq> \<emptyset> \<and> B = \<emptyset>"
@proof
  @case "A \<rightarrow> B = \<emptyset>" @with  (* Show A \<noteq> 0 and B = 0 *)
    @case "A = \<emptyset>" @with @have "Fun(A,B,\<lambda>_.\<emptyset>) \<in> A \<rightarrow> B" @end
    @case "B \<noteq> \<emptyset>" @with @obtain "b \<in> B" @have "Fun(A,B,\<lambda>_.b) \<in> A \<rightarrow> B" @end
  @end
  @case "A \<noteq> \<emptyset> \<and> B = \<emptyset>" @with
    @obtain "f \<in> A \<rightarrow> B" "a \<in> A" @have "f ` a \<in> B"
  @end
@qed

section {* Important examples of functions *}

(* Identity function *)
definition id_fun :: "i \<Rightarrow> i" where [rewrite]:
  "id_fun(A) = Fun(A,A, \<lambda>x. x)"

lemma id_fun_is_function [typing]: "id_fun(A) \<in> A \<rightarrow> A" by auto2
lemma id_fun_eval [rewrite]: "x \<in> source(id_fun(A)) \<Longrightarrow> id_fun(A) ` x = x" by auto2
setup {* del_prfstep_thm @{thm id_fun_def} *}

lemma id_fun_image [rewrite]: "S \<subseteq> A \<Longrightarrow> id_fun(A) `` S = S"
@proof @have "\<forall>x\<in>S. x \<in> id_fun(A)``S" @with @have "id_fun(A)`x = x" @end @qed

(* Constant function *)
definition const_fun :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "const_fun(A,B,y) = Fun(A,B, \<lambda>x. y)"
setup {* register_wellform_data ("const_fun(A,B,y)", ["y \<in> B"]) *}

lemma const_fun_is_function [typing]: "y \<in> B \<Longrightarrow> const_fun(A,B,y) \<in> A \<rightarrow> B" by auto2
lemma const_fun_eval [rewrite]: "y \<in> B \<Longrightarrow> x \<in> source(const_fun(A,B,y)) \<Longrightarrow> const_fun(A,B,y) ` x = y" by auto2
setup {* del_prfstep_thm @{thm const_fun_def} *}

(* Restriction of function to a set A *)
definition func_restrict :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "func_restrict(f,A) = Fun(A, target(f), \<lambda>x. f`x)"
setup {* register_wellform_data ("func_restrict(f,A)", ["A \<subseteq> source(f)"]) *}
setup {* add_prfstep_check_req ("func_restrict(f,A)", "A \<subseteq> source(f)") *}

lemma func_restrict_is_function [typing]:
  "is_function(f) \<Longrightarrow> A \<subseteq> source(f) \<Longrightarrow> func_restrict(f,A) \<in> A \<rightarrow> target(f)" by auto2

lemma func_restrict_eval [rewrite]:
  "is_function(f) \<Longrightarrow> A \<subseteq> source(f) \<Longrightarrow> x \<in> source(func_restrict(f,A)) \<Longrightarrow>
   func_restrict(f,A) ` x = f ` x" by auto2
setup {* del_prfstep_thm @{thm func_restrict_def} *}

lemma func_restrict_trans [rewrite]:
  "is_function(f) \<Longrightarrow> B \<subseteq> source(func_restrict(f,A)) \<Longrightarrow> A \<subseteq> source(f) \<Longrightarrow>
   func_restrict(func_restrict(f,A),B) = func_restrict(f,B)" by auto2

lemma func_restrict_fImage [rewrite]:
  "is_function(f) \<Longrightarrow> A \<subseteq> source(f) \<Longrightarrow> func_restrict(f,A) `` A = f `` A"
@proof
  @let "g = func_restrict(f,A)"
  @have "\<forall>x\<in>f``A. x \<in> g``A" @with
    @obtain y where "y \<in> A" "f`y = x"
    @have "g`y \<in> g``A"
  @end
@qed

definition func_coincide :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "func_coincide(f,g,E) \<longleftrightarrow> (E \<subseteq> source(f) \<and> E \<subseteq> source(g) \<and> (\<forall>x\<in>E. f`x = g`x))"

lemma func_coincideD1 [forward]:
  "func_coincide(f,g,E) \<Longrightarrow> E \<subseteq> source(f) \<and> E \<subseteq> source(g)" by auto2

lemma func_coincideD2 [rewrite_bidir]:
  "func_coincide(f,g,E) \<Longrightarrow> x \<in> E \<Longrightarrow> f`x = g`x" by auto2
setup {* del_prfstep_thm_eqforward @{thm func_coincide_def} *}

definition is_func_extension :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "is_func_extension(f,g) \<longleftrightarrow> (source(g) \<subseteq> source(f) \<and> func_coincide(f,g,source(g)))"

lemma extension_of_restrict [backward]:
  "is_function(f) \<Longrightarrow> A \<subseteq> source(f) \<Longrightarrow> is_func_extension(f,func_restrict(f,A))" by auto2

(* Any function can be restricted to its image. *)
definition func_restrict_image :: "i \<Rightarrow> i" where [rewrite]:
  "func_restrict_image(f) = Fun(source(f),image(f), \<lambda>x. f`x)"

lemma func_restrict_image_is_fun [typing]:
  "is_function(f) \<Longrightarrow> func_restrict_image(f) \<in> source(f) \<rightarrow> image(f)" by auto2

lemma func_restrict_image_type [backward]:
  "is_function(f) \<Longrightarrow> f `` source(f) = C \<Longrightarrow> func_restrict_image(f) \<in> source(f) \<rightarrow> C" by auto2

lemma func_restrict_image_eval [rewrite]:
  "is_function(f) \<Longrightarrow> x \<in> source(func_restrict_image(f)) \<Longrightarrow> func_restrict_image(f)`x = f`x" by auto2
setup {* del_prfstep_thm @{thm func_restrict_image_def} *}

(* Projection functions *)
definition proj1_fun :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "proj1_fun(A,B) = Fun(A\<times>B, A, \<lambda>p. fst(p))"

lemma proj1_fun_is_function [typing]: "proj1_fun(A,B) \<in> A\<times>B \<rightarrow> A" by auto2
lemma proj1_eval [rewrite]: "p \<in> source(proj1_fun(A,B)) \<Longrightarrow> proj1_fun(A,B)`p = fst(p)" by auto2
setup {* del_prfstep_thm @{thm proj1_fun_def} *}

definition proj2_fun :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "proj2_fun(A,B) = Fun(A\<times>B, B, \<lambda>p. snd(p))"

lemma proj2_fun_is_function [typing]: "proj2_fun(A,B) \<in> A\<times>B \<rightarrow> B" by auto2
lemma proj2_fun_eval [rewrite]: "p \<in> source(proj2_fun(A,B)) \<Longrightarrow> proj2_fun(A,B)`p = snd(p)" by auto2
setup {* del_prfstep_thm @{thm proj2_fun_def} *}

section {* Composition of functions *}  (* Bourbaki II.3.7 *)

(* Composition of two functions. *)
definition fun_comp :: "i \<Rightarrow> i \<Rightarrow> i"  (infixr "\<circ>" 60) where [rewrite]:
  "f' \<circ> f = Fun(source(f), target(f'), \<lambda>x. f' ` (f ` x))"
setup {* register_wellform_data ("f' \<circ> f", ["func_form(f')", "func_form(f)", "target(f) = source(f')"]) *}
setup {* add_prfstep_check_req ("f' \<circ> f", "target(f) = source(f')") *}

lemma comp_is_function [typing]:
  "is_function(f) \<Longrightarrow> is_function(f') \<Longrightarrow> target(f) = source(f') \<Longrightarrow> f' \<circ> f \<in> source(f) \<rightarrow> target(f')" by auto2

lemma comp_eval [rewrite]:
  "is_function(f) \<Longrightarrow> is_function(f') \<Longrightarrow> target(f) = source(f') \<Longrightarrow>
   x \<in> source(f) \<Longrightarrow> (f' \<circ> f) ` x = f' ` (f ` x)" by auto2
setup {* add_rewrite_rule_back_cond @{thm comp_eval} [with_term "?f' \<circ> ?f"] *}
setup {* del_prfstep_thm @{thm fun_comp_def} *}

lemma comp_assoc_l:
  "func_form(x) \<Longrightarrow> func_form(y) \<Longrightarrow> func_form(z) \<Longrightarrow> target(z) = source(y) \<Longrightarrow>
   target(y \<circ> z) = source(x) \<Longrightarrow> x \<circ> (y \<circ> z) = (x \<circ> y) \<circ> z \<and>
   func_form(x \<circ> y) \<and> target(y) = source(x) \<and> target(z) = source(x \<circ> y)" by auto2
setup {* add_prfstep (FOL_Assoc.alg_assoc_prfstep (@{term fun_comp}, @{thm comp_assoc_l})) *}

lemma comp_id_left [rewrite]:
  "func_form(f) \<Longrightarrow> id_fun(target(f)) \<circ> f = f" by auto2

lemma comp_id_right [rewrite]:
  "func_form(f) \<Longrightarrow> f \<circ> id_fun(source(f)) = f" by auto2

lemma func_vImage_comp [rewrite]:
  "is_function(f) \<Longrightarrow> is_function(g) \<Longrightarrow> target(f) = source(g) \<Longrightarrow>
   (g \<circ> f) -`` V = f -`` (g -`` V)" by auto2
setup {* add_rewrite_rule_back_cond @{thm func_vImage_comp} [with_term "?g \<circ> ?f"] *}

section {* Injective, surjective, and bijective functions. *}

definition injective :: "i \<Rightarrow> o" where [rewrite]:
  "injective(f) \<longleftrightarrow> (is_function(f) \<and> (\<forall>x\<in>source(f). \<forall>y\<in>source(f). f`x = f`y \<longrightarrow> x=y))"

lemma injectiveI [backward]:
  "is_function(f) \<Longrightarrow> (\<forall>x\<in>source(f). \<forall>y\<in>source(f). f`x = f`y \<longrightarrow> x=y) \<Longrightarrow> injective(f)" by auto2

lemma injectiveD [forward]:
  "injective(f) \<Longrightarrow> is_function(f)"
  "injective(f) \<Longrightarrow> x \<in> source(f) \<Longrightarrow> y \<in> source(f) \<Longrightarrow> f`x = f`y \<Longrightarrow> x = y" by auto2+

definition surjective :: "i \<Rightarrow> o" where [rewrite]:
  "surjective(f) \<longleftrightarrow> (is_function(f) \<and> image(f) = target(f))"
  
lemma surjectiveD:
  "surjective(f) \<Longrightarrow> is_function(f)"
  "surjective(f) \<Longrightarrow> y \<in> target(f) \<Longrightarrow> \<exists>x\<in>source(f). f ` x = y"
  "surjective(f) \<Longrightarrow> image(f) = target(f)" by auto2+
setup {* add_forward_prfstep @{thm surjectiveD(1)} *}
setup {* add_backward_prfstep @{thm surjectiveD(2)} *}
setup {* add_rewrite_rule @{thm surjectiveD(3)} *}

lemma surjectiveI [backward]:
  "is_function(f) \<Longrightarrow> \<forall>y\<in>target(f). \<exists>x\<in>source(f). f`x = y \<Longrightarrow> surjective(f)" by auto2

lemma surjectiveI' [forward]:
  "is_function(f) \<Longrightarrow> image(f) = target(f) \<Longrightarrow> surjective(f)" by auto2

definition bijective :: "i \<Rightarrow> o" where [rewrite]:
  "bijective(f) \<longleftrightarrow> (injective(f) \<and> surjective(f))"

lemma bijectiveD [forward]:
  "bijective(f) \<Longrightarrow> injective(f)"
  "bijective(f) \<Longrightarrow> surjective(f)" by auto2+

lemma bijectiveI [backward]:
  "injective(f) \<and> surjective(f) \<Longrightarrow> bijective(f)" by auto2

setup {* fold del_prfstep_thm [@{thm injective_def}, @{thm surjective_def}, @{thm bijective_def}] *}

definition bijection_space :: "i \<Rightarrow> i \<Rightarrow> i"  (infix "\<cong>" 60) where [rewrite]:
  "A \<cong> B = {f \<in> A \<rightarrow> B. bijective(f)}"

lemma bijective_spaceD [forward]:
  "f \<in> A \<cong> B \<Longrightarrow> f \<in> A \<rightarrow> B \<and> bijective(f)" by auto2

lemma bijective_spaceI [backward]:
  "func_form(f) \<Longrightarrow> bijective(f) \<Longrightarrow> f \<in> source(f) \<cong> target(f)" by auto2
setup {* del_prfstep_thm @{thm bijection_space_def} *}

(* Some properties of surjective functions *)
lemma surjective_to_singleton [backward2]:
  "f \<in> A \<rightarrow> {x} \<Longrightarrow> A \<noteq> \<emptyset> \<Longrightarrow> surjective(f)" by auto2

lemma surj_source_nonempty [forward, backward]:
  "surjective(f) \<Longrightarrow> target(f) \<noteq> \<emptyset> \<Longrightarrow> source(f) \<noteq> \<emptyset>"
@proof
  @obtain b where "b \<in> target(f)"
  @obtain "a \<in> source(f)" where "f`a = b"
@qed
    
lemma surjective_inv_image [backward2]:
  "surjective(f) \<Longrightarrow> U \<subseteq> target(f) \<Longrightarrow> U \<noteq> \<emptyset> \<Longrightarrow> f -`` U \<noteq> \<emptyset>"
@proof
  @obtain u where "u \<in> U"
  @obtain "x \<in> source(f)" where "f`x = u"
@qed

(* Properties of bijective functions *)
lemma bijective_exist_unique [backward]:
  "bijective(f) \<Longrightarrow> y \<in> target(f) \<Longrightarrow> \<exists>!x. x\<in>source(f) \<and> f`x=y" by auto2

(* Restrictions of functions *)
lemma func_restrict_injective:
  "injective(f) \<Longrightarrow> A \<subseteq> source(f) \<Longrightarrow> injective(func_restrict(f,A))" by auto2
setup {* add_forward_prfstep_cond @{thm func_restrict_injective} [with_term "func_restrict(?f,?A)"] *}

lemma func_restrict_image_bij [forward]:
  "injective(f) \<Longrightarrow> bijective(func_restrict_image(f))" by auto2

(* Example: canonical injection. *)
definition inj_fun :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "inj_fun(A,B) = Fun(A,B, \<lambda>x. x)"
setup {* register_wellform_data ("inj_fun(A,B)", ["A \<subseteq> B"]) *}

lemma inj_fun_is_function [typing]: "A \<subseteq> B \<Longrightarrow> inj_fun(A,B) \<in> A \<rightarrow> B" by auto2
lemma inj_fun_eval [rewrite]: "A \<subseteq> B \<Longrightarrow> x \<in> source(inj_fun(A,B)) \<Longrightarrow> inj_fun(A,B) ` x = x" by auto2
setup {* del_prfstep_thm @{thm inj_fun_def} *}

lemma inj_fun_is_injection: "A \<subseteq> B \<Longrightarrow> injective(inj_fun(A,B))" by auto2

lemma func_factorize [rewrite_back]:
  "func_form(f) \<Longrightarrow> f = inj_fun(image(f),target(f)) \<circ> func_restrict_image(f)" by auto2

lemma inj_restrict_image_bij [typing]:
  "injective(f) \<Longrightarrow> func_restrict_image(f) \<in> source(f) \<cong> image(f)" by auto2

lemma inj_restrict_image_bij' [backward]:
  "injective(f) \<Longrightarrow> f `` source(f) = C \<Longrightarrow> func_restrict_image(f) \<in> source(f) \<cong> C" by auto2

(* Other examples. *)
lemma id_bij: "id_fun(A) \<in> A \<cong> A" by auto2
lemma proj1_surj: "B \<noteq> \<emptyset> \<Longrightarrow> surjective(proj1_fun(A,B))" by auto2
lemma proj2_surj: "A \<noteq> \<emptyset> \<Longrightarrow> surjective(proj2_fun(A,B))" by auto2
lemma swap_bij: "Fun(A\<times>B, B\<times>A, \<lambda>p. \<langle>snd(p),fst(p)\<rangle>) \<in> A\<times>B \<cong> B\<times>A" by auto2
lemma pair_bij: "Fun(A, A\<times>{b}, \<lambda>x. \<langle>x,b\<rangle>) \<in> A \<cong> A\<times>{b}" by auto2
lemma rpair_bij: "Fun(A, {b}\<times>A, \<lambda>x. \<langle>b,x\<rangle>) \<in> A \<cong> {b}\<times>A" by auto2

section {* Inverse function *}

definition inverse :: "i \<Rightarrow> i" where [rewrite]:
  "inverse(f) = Fun(target(f),source(f), \<lambda>y. THE x. x\<in>source(f) \<and> f`x=y)"
setup {* add_prfstep_check_req ("inverse(f)", "bijective(f)") *}

lemma has_inverse [typing]:
  "bijective(f) \<Longrightarrow> inverse(f) \<in> target(f) \<rightarrow> source(f)" by auto2

lemma inverse_eval1 [rewrite]:
  "bijective(f) \<Longrightarrow> x \<in> source(f) \<Longrightarrow> f ` x = y \<Longrightarrow> inverse(f) ` y = x" by auto2

lemma inverse_eval2 [rewrite]:
  "bijective(f) \<Longrightarrow> y \<in> source(inverse(f)) \<Longrightarrow> inverse(f) ` y = x \<Longrightarrow> f ` x = y" by auto2
setup {* del_prfstep_thm @{thm inverse_def} *}

lemma inv_bijective [typing]:
  "bijective(f) \<Longrightarrow> inverse(f) \<in> target(f) \<cong> source(f)"
@proof @have (@rule) "\<forall>x\<in>source(f). inverse(f)`(f`x) = x" @qed

lemma inverse_of_inj [rewrite]:
  "injective(f) \<Longrightarrow> X \<subseteq> source(f) \<Longrightarrow> f -`` (f `` X) = X" by auto2

lemma inverse_of_surj [rewrite]:
  "surjective(f) \<Longrightarrow> Y \<subseteq> target(f) \<Longrightarrow> f `` (f -`` Y) = Y"
@proof
  @have "\<forall>y\<in>Y. y \<in> f``(f-``Y)" @with
    @obtain "x\<in>source(f)" where "f`x = y"
  @end
@qed

lemma inverse_is_left_inv [rewrite]:
  "bijective(f) \<Longrightarrow> inverse(f) \<circ> f = id_fun(source(f))" by auto2

lemma inverse_is_right_inv [rewrite]:
  "bijective(f) \<Longrightarrow> f \<circ> inverse(f) = id_fun(target(f))" by auto2

section {* Left and right inverses *}  (* Bourbaki II.3.8 *)

(* Left and right inverses always exists, but that takes more work. *)
lemma has_left_inverse_inj [forward]:
  "is_function(f) \<Longrightarrow> is_function(r) \<Longrightarrow> target(f) = source(r) \<Longrightarrow>
   r \<circ> f = id_fun(source(f)) \<Longrightarrow> injective(f)"
@proof
  @have "\<forall>x\<in>source(f). \<forall>y\<in>source(f). f`x = f`y \<longrightarrow> x=y" @with @have "r`(f`x)=x" @end
@qed

lemma has_right_inverse_surj [forward]:
  "is_function(f) \<Longrightarrow> is_function(s) \<Longrightarrow> target(s) = source(f) \<Longrightarrow>
   f \<circ> s = id_fun(source(s)) \<Longrightarrow> surjective(f)"
@proof
  @have "\<forall>x\<in>target(f). x\<in>image(f)" @with @have "f`(s`x) = x" @end
@qed

lemma has_left_right_inverse_bij [forward]:
  "func_form(f) \<Longrightarrow> is_function(r) \<Longrightarrow> is_function(s) \<Longrightarrow> target(f) = source(r) \<Longrightarrow>
   target(s) = source(f) \<Longrightarrow> r \<circ> f = id_fun(A) \<Longrightarrow> f \<circ> s = id_fun(B) \<Longrightarrow> f \<in> A \<cong> B" by auto2

lemma right_inverse_unique:
  "is_function(f) \<Longrightarrow> f \<circ> s = id_fun(B) \<Longrightarrow> f \<circ> s' = id_fun(B) \<Longrightarrow>
   f \<in> A \<rightarrow> B \<Longrightarrow> s \<in> B \<rightarrow> A \<Longrightarrow> s' \<in> B \<rightarrow> A \<Longrightarrow> s `` B = s' `` B \<Longrightarrow> s = s'"
@proof
  @have "\<forall>x\<in>B. s`x = s'`x" @with @have "f`(s`x) = x" @end
@qed

(* Six parts of Theorem 1 in Bourbaki II.3.8. May be easier with existence
   of left/right-inverse, but not necessary. *)
lemma comp_is_inj:
  "injective(f) \<Longrightarrow> injective(f') \<Longrightarrow> target(f) = source(f') \<Longrightarrow> injective(f' \<circ> f)" by auto2
setup {* add_forward_prfstep_cond @{thm comp_is_inj} [with_term "?f' \<circ> ?f"] *}

lemma comp_is_surj:
  "surjective(f) \<Longrightarrow> surjective(f') \<Longrightarrow> target(f) = source(f') \<Longrightarrow> surjective(f' \<circ> f)"
@proof
  @have "\<forall>z\<in>target(f'). \<exists>x\<in>source(f). (f' \<circ> f) ` x = z" @with
    @obtain "y \<in> source(f')" where "f' ` y = z"
    @obtain "x \<in> source(f)" where "f ` x = y"
  @end
@qed
setup {* add_forward_prfstep_cond @{thm comp_is_surj} [with_term "?f' \<circ> ?f"] *}

lemma comp_is_inj_to_first_inj [forward]:
  "is_function(f) \<Longrightarrow> is_function(f') \<Longrightarrow> target(f) = source(f') \<Longrightarrow> injective(f' \<circ> f) \<Longrightarrow> injective(f)"
@proof
  @have "\<forall>x\<in>source(f). \<forall>y\<in>source(f). f`x = f`y \<longrightarrow> x=y" @with
    @have "(f' \<circ> f) ` x = (f' \<circ> f) ` y" @end
@qed

lemma comp_is_surj_to_second_surj [forward]:
  "is_function(f) \<Longrightarrow> is_function(f') \<Longrightarrow> target(f) = source(f') \<Longrightarrow> surjective(f' \<circ> f) \<Longrightarrow> surjective(f')"
@proof
  @have "\<forall>y\<in>target(f'). \<exists>x\<in>source(f'). f' ` x = y" @with
    @obtain "x \<in> source(f)" where "(f' \<circ> f) ` x = y"
  @end
@qed

lemma comp_is_surj_to_first_surj [forward]:
  "is_function(f) \<Longrightarrow> injective(f') \<Longrightarrow> target(f) = source(f') \<Longrightarrow> surjective(f' \<circ> f) \<Longrightarrow> surjective(f)"
@proof
  @have "\<forall>y\<in>target(f). \<exists>x\<in>source(f). f ` x = y" @with
    @obtain "x \<in> source(f)" where "(f' \<circ> f) ` x = f' ` y"
  @end
@qed

lemma comp_is_inj_to_second_inj [forward]:
  "surjective(f) \<Longrightarrow> func_form(f') \<Longrightarrow> target(f) = source(f') \<Longrightarrow> injective(f' \<circ> f) \<Longrightarrow> injective(f')"
@proof @have "f' = (f' \<circ> f) \<circ> inverse(f)" @qed

lemma inverse_unique [rewrite]:
  "bijective(f) \<Longrightarrow> func_form(g) \<Longrightarrow> target(f) = source(g) \<Longrightarrow>
   g \<circ> f = id_fun(source(f)) \<Longrightarrow> inverse(f) = g"
@proof
  @have "\<forall>x\<in>target(f). inverse(f)`x = g`x" @with
    @obtain "y\<in>source(f)" where "f`y = x"
  @end
@qed

lemma inverse_unique' [rewrite]:
  "bijective(f) \<Longrightarrow> func_form(g) \<Longrightarrow> target(g) = source(f) \<Longrightarrow>
   f \<circ> g = id_fun(target(f)) \<Longrightarrow> inverse(f) = g"
@proof
  @have "\<forall>x\<in>target(f). inverse(f)`x = g`x" @with
    @have "f ` (g ` x) = (f \<circ> g) ` x"
  @end
@qed

(* Now we construct the left and right inverses explicitly. *)
lemma exists_right_inverse [resolve]:
  "surjective(f) \<Longrightarrow> A = source(f) \<Longrightarrow> B = target(f) \<Longrightarrow> \<exists>s\<in>B\<rightarrow>A. f \<circ> s = id_fun(B)"
@proof @let "s = Fun(B,A, \<lambda>y. SOME x\<in>A. f`x=y)" @qed

definition right_inverse :: "i \<Rightarrow> i" where [rewrite]:
  "right_inverse(f) = (SOME s\<in>target(f)\<rightarrow>source(f). f \<circ> s = id_fun(target(f)))"

lemma right_inverse_prop:
  "surjective(f) \<Longrightarrow>
   right_inverse(f) \<in> target(f) \<rightarrow> source(f) \<and> f \<circ> right_inverse(f) = id_fun(target(f))" by auto2
setup {* add_forward_prfstep_cond @{thm right_inverse_prop} [with_term "right_inverse(?f)"] *}
setup {* del_prfstep_thm @{thm right_inverse_def} *}

lemma exists_left_inverse [backward]:
  "injective(f) \<Longrightarrow> A = source(f) \<Longrightarrow> B = target(f) \<Longrightarrow> A \<noteq> \<emptyset> \<Longrightarrow> \<exists>r\<in>B\<rightarrow>A. r \<circ> f = id_fun(A)"
@proof
  @obtain "a \<in> A"
  @let "r = Fun(B, A, \<lambda>y. if \<exists>x\<in>A. f`x=y then SOME x\<in>A. f`x=y else a)"
  @have (@rule) "\<forall>x\<in>A. r`(f`x) = x" @with @have "\<exists>x'\<in>A. f`x' = f`x" @end
@qed

definition left_inverse :: "i \<Rightarrow> i" where [rewrite]:
  "left_inverse(f) = (SOME r\<in>target(f)\<rightarrow>source(f). r \<circ> f = id_fun(source(f)))"
setup {* register_wellform_data ("left_inverse(f)", ["source(f) \<noteq> \<emptyset>"]) *}
setup {* add_prfstep_check_req ("left_inverse(f)", "source(f) \<noteq> \<emptyset>") *}

lemma left_inverse_prop:
  "injective(f) \<Longrightarrow> source(f) \<noteq> \<emptyset> \<Longrightarrow>
   left_inverse(f) \<in> target(f) \<rightarrow> source(f) \<and> left_inverse(f) \<circ> f = id_fun(source(f))" by auto2
setup {* add_forward_prfstep_cond @{thm left_inverse_prop} [with_term "left_inverse(?f)"] *}
setup {* del_prfstep_thm @{thm left_inverse_def} *}

(* Using left and right inverses to construct functions. *)
lemma exists_pullback_surj [backward1]:
  "surjective(g) \<Longrightarrow> g \<in> E \<rightarrow> F \<Longrightarrow> f \<in> E \<rightarrow> G \<Longrightarrow> \<forall>x\<in>E. \<forall>y\<in>E. g`x=g`y \<longrightarrow> f`x=f`y \<Longrightarrow>
   \<exists>!h. h\<in>F\<rightarrow>G \<and> f = h \<circ> g"
@proof
  @have "\<exists>h\<in>F\<rightarrow>G. f = h \<circ> g" @with
    @obtain "s \<in> F \<rightarrow> E" where "g \<circ> s = id_fun(F)"
    @obtain "h \<in> F \<rightarrow> G" where "h = f \<circ> s"
  @end
  @have "\<forall>h1 h2. h1 \<in> F \<rightarrow> G \<and> f = h1 \<circ> g \<longrightarrow> h2 \<in> F \<rightarrow> G \<and> f = h2 \<circ> g \<longrightarrow> h1 = h2" @with
    @have "\<forall>x\<in>F. h1`x = h2`x" @with
      @obtain "y\<in>E" where "g`y = x"
    @end
  @end
@qed

lemma exists_pullback_inj:
  "injective(g) \<Longrightarrow> g \<in> F \<rightarrow> E \<Longrightarrow> f \<in> G \<rightarrow> E \<Longrightarrow> F \<noteq> \<emptyset> \<Longrightarrow> image(f) \<subseteq> image(g) \<Longrightarrow>
   \<exists>!h. h\<in>G\<rightarrow>F \<and> f = g \<circ> h"
@proof
  @have "\<exists>h\<in>G\<rightarrow>F. f = g \<circ> h" @with
    @obtain "r \<in> E \<rightarrow> F" where "r \<circ> g = id_fun(F)"
    @obtain "h \<in> G \<rightarrow> F" where "h = r \<circ> f"
  @end
  @have "\<forall>h1 h2. h1 \<in> G \<rightarrow> F \<and> f = g \<circ> h1 \<longrightarrow> h2 \<in> G \<rightarrow> F \<and> f = g \<circ> h2 \<longrightarrow> h1 = h2" @with
    @have "\<forall>x\<in>G. h1`x = h2`x" @with
      @have "g`(h1`x) = g`(h2`x)"
    @end
  @end
@qed

section {* Inverse pair *}

(* Two functions are inverses of each other. This pattern occurs very frequently. *)
definition inverse_pair :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "inverse_pair(f,g) \<longleftrightarrow> (is_function(f) \<and> is_function(g) \<and> source(f) = target(g) \<and> target(f) = source(g) \<and>
                          f \<circ> g = id_fun(source(g)) \<and> g \<circ> f = id_fun(source(f)))"

lemma inverse_pair_bijective [forward]:
  "inverse_pair(f,g) \<Longrightarrow> source(f) = target(g) \<and> source(g) = target(f) \<and> bijective(f) \<and> bijective(g)" by auto2

lemma inverse_pairI [backward]:
  "is_function(f) \<Longrightarrow> is_function(g) \<Longrightarrow> source(f) = target(g) \<Longrightarrow> source(g) = target(f) \<Longrightarrow>
   \<forall>x\<in>source(g). f`(g`x) = x \<Longrightarrow> \<forall>x\<in>source(f). g`(f`x) = x \<Longrightarrow> inverse_pair(f,g)" by auto2

lemma inverse_pairE [rewrite]:
  "inverse_pair(f,g) \<Longrightarrow> f \<circ> g = id_fun(source(g))"
  "inverse_pair(f,g) \<Longrightarrow> g \<circ> f = id_fun(source(f))" by auto2+
setup {* del_prfstep_thm @{thm inverse_pair_def} *}

lemma inverse_pair_inverse [rewrite]: "func_form(g) \<Longrightarrow> inverse_pair(f,g) \<Longrightarrow> inverse(f) = g"
@proof @have "g \<circ> f = id_fun(source(f))" @qed

lemma inverse_pair_inverse2 [rewrite]: "func_form(f) \<Longrightarrow> inverse_pair(f,g) \<Longrightarrow> inverse(g) = f"
@proof @have "g \<circ> f = id_fun(source(f))" @qed

section {* Function of two arguments *}  (* Bourbaki II.3.9 *)

(* We consider functions on product sets only. *)

(* Currying: given a function (A \<times> B) \<rightarrow> D, return a function A \<rightarrow> (B \<rightarrow> D). *)
definition curry :: "[i, i, i] \<Rightarrow> i" where [rewrite]:
  "curry(A,B,D) = Fun(A\<times>B\<rightarrow>D, A\<rightarrow>B\<rightarrow>D, \<lambda>f. Fun(A, B\<rightarrow>D, \<lambda>x. Fun(B, D, \<lambda>y. f`\<langle>x,y\<rangle>)))"

lemma curry_is_function [typing]:
  "curry(A,B,D) \<in> ((A \<times> B) \<rightarrow> D) \<rightarrow> (A \<rightarrow> (B \<rightarrow> D))" by auto2

lemma curry_eval [rewrite]:
  "f \<in> source(curry(A,B,D)) \<Longrightarrow> x \<in> source(curry(A,B,D)`f) \<Longrightarrow> y \<in> source(curry(A,B,D)`f`x) \<Longrightarrow>
   curry(A,B,D)`f`x`y = f`\<langle>x,y\<rangle>" by auto2
setup {* del_prfstep_thm @{thm curry_def} *}

(* Constant functions *)
definition is_const_fun :: "i \<Rightarrow> o" where [rewrite]:
  "is_const_fun(f) \<longleftrightarrow> (\<forall>x\<in>source(f). \<forall>y\<in>source(f). f`x = f`y)"

lemma is_const_funD [forward]:
  "is_const_fun(f) \<Longrightarrow> x \<in> source(f) \<Longrightarrow> y \<in> source(f) \<Longrightarrow> f`x = f`y" by auto2
setup {* del_prfstep_thm_eqforward @{thm is_const_fun_def} *}

(* Functions that do not depend on the second argument. *)
lemma exists_proj_fun:
  "B \<noteq> \<emptyset> \<Longrightarrow> f \<in> (A \<times> B) \<rightarrow> D \<Longrightarrow> \<forall>x\<in>A. is_const_fun(curry(A,B,D)`f`x) \<Longrightarrow>
   \<exists>g\<in>A\<rightarrow>D. \<forall>x\<in>A. \<forall>y\<in>B. f`\<langle>x,y\<rangle> = g`x"
@proof
  @obtain "y \<in> B" @let "g = Fun(A,D, \<lambda>x. f`\<langle>x,y\<rangle>)"
@qed

(* Product map *)
definition prod_map :: "i \<Rightarrow> i \<Rightarrow> i" (infixr "\<times>\<^sub>f" 80) where [rewrite]:
  "u \<times>\<^sub>f v = Fun(source(u)\<times>source(v), target(u)\<times>target(v), \<lambda>p. \<langle>u`fst(p), v`snd(p)\<rangle>)"

lemma prod_map_is_function [typing]:
  "is_function(u) \<Longrightarrow> is_function(v) \<Longrightarrow> u \<times>\<^sub>f v \<in> source(u)\<times>source(v) \<rightarrow> target(u)\<times>target(v)" by auto2

lemma prod_map_eval [rewrite]:
  "is_function(u) \<Longrightarrow> is_function(v) \<Longrightarrow> \<langle>x,y\<rangle> \<in> source(u \<times>\<^sub>f v) \<Longrightarrow> (u \<times>\<^sub>f v) ` \<langle>x,y\<rangle> = \<langle>u`x, v`y\<rangle>" by auto2
setup {* del_prfstep_thm @{thm prod_map_def} *}

lemma prod_map_inj [forward]:
  "injective(u) \<Longrightarrow> injective(v) \<Longrightarrow> injective(u \<times>\<^sub>f v)" by auto2

lemma prod_map_surj [forward]:
  "surjective(u) \<Longrightarrow> surjective(v) \<Longrightarrow> surjective(u \<times>\<^sub>f v)"
@proof
  @let "f = u \<times>\<^sub>f v"
  @have "\<forall>q\<in>target(f). \<exists>p\<in>source(f). f`p = q" @with
    @obtain "x\<in>source(u)" where "u`x = fst(q)"
    @obtain "y\<in>source(v)" where "v`y = snd(q)"
  @end
@qed

lemma prod_map_bij [forward]:
  "bijective(u) \<Longrightarrow> bijective(v) \<Longrightarrow> bijective(u \<times>\<^sub>f v)" by auto2

lemma prod_map_comp [resolve]:
  "is_function(u) \<Longrightarrow> is_function(u') \<Longrightarrow> is_function(v) \<Longrightarrow> is_function(v') \<Longrightarrow>
   target(u) = source(u') \<Longrightarrow> target(v) = source(v') \<Longrightarrow>
   (u' \<circ> u) \<times>\<^sub>f (v' \<circ> v) = (u' \<times>\<^sub>f v') \<circ> (u \<times>\<^sub>f v)" by auto2

lemma prod_map_id_fun [rewrite]:
  "id_fun(A) \<times>\<^sub>f id_fun(B) = id_fun(A\<times>B)" by auto2

lemma prod_inverse [resolve]:
  "bijective(u) \<Longrightarrow> bijective(v) \<Longrightarrow> inverse(u \<times>\<^sub>f v) = inverse(u) \<times>\<^sub>f inverse(v)"
@proof
  @have "inverse_pair(inverse(u) \<times>\<^sub>f inverse(v), u \<times>\<^sub>f v)"
@qed

section {* Extension of a function to Pow *}  (* Bourbaki II.5.1 *)

definition pow_ext :: "i \<Rightarrow> i" where [rewrite]:
  "pow_ext(f) = Fun(Pow(source(f)), Pow(target(f)), \<lambda>X. f `` X)"

lemma pow_ext_is_function [typing]:
  "is_function(f) \<Longrightarrow> pow_ext(f) \<in> Pow(source(f)) \<rightarrow> Pow(target(f))" by auto2

lemma pow_ext_eval [rewrite]:
  "is_function(f) \<Longrightarrow> X \<in> source(pow_ext(f)) \<Longrightarrow> pow_ext(f) ` X = f `` X" by auto2
setup {* del_prfstep_thm @{thm pow_ext_def} *}

lemma pow_ext_comp [rewrite]:
  "is_function(f) \<Longrightarrow> is_function(g) \<Longrightarrow> target(f) = source(g) \<Longrightarrow>
   pow_ext(g \<circ> f) = pow_ext(g) \<circ> pow_ext(f)" by auto2

lemma pow_ext_id [rewrite]:
  "pow_ext(id_fun(A)) = id_fun(Pow(A))" by auto2

lemma pow_ext_surj [forward]:
  "is_function(f) \<Longrightarrow> surjective(f) \<Longrightarrow> surjective(pow_ext(f))"
@proof
  @let "A = source(f)" "B = target(f)"
  @obtain "s \<in> B \<rightarrow> A" where "f \<circ> s = id_fun(target(f))"
  @have "pow_ext(f \<circ> s) = pow_ext(f) \<circ> pow_ext(s)"
@qed

lemma pow_ext_inj [forward]:
  "injective(f) \<Longrightarrow> injective(pow_ext(f))"
@proof
  @let "U = source(pow_ext(f))"
  @have (@rule) "\<forall>S\<in>U. \<forall>T\<in>U. f `` S = f `` T \<longrightarrow> S = T" @with
    @have "\<forall>x. x \<in> S \<longleftrightarrow> x \<in> T" @with
      @case "x \<in> S" @with @have "f`x \<in> f``S" @end
      @case "x \<in> T" @with @have "f`x \<in> f``T" @end
    @end
  @end
@qed

section {* Map on function spaces *}  (* Bourbaki II.5.2 *)

(* Define left and right composition separately. *)

definition left_comp :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "left_comp(u,E) = Fun(E\<rightarrow>source(u), E\<rightarrow>target(u), \<lambda>f. u \<circ> f)"

lemma left_comp_is_function [typing]:
  "is_function(u) \<Longrightarrow> left_comp(u,E) \<in> (E\<rightarrow>source(u)) \<rightarrow> (E\<rightarrow>target(u))" by auto2

lemma left_comp_eval [rewrite]:
  "is_function(u) \<Longrightarrow> f \<in> source(left_comp(u,E)) \<Longrightarrow> left_comp(u,E) ` f = u \<circ> f" by auto2
setup {* del_prfstep_thm @{thm left_comp_def} *}

lemma injective_left_comp [forward]:
  "injective(u) \<Longrightarrow> injective(left_comp(u,E))"
@proof
  @contradiction
  @obtain "r \<in> target(u) \<rightarrow> source(u)" where "r \<circ> u = id_fun(source(u))"
  @have "left_comp(r,E) \<circ> left_comp(u,E) = id_fun(E\<rightarrow>source(u))"
@qed

lemma surjective_left_comp [forward]:
  "surjective(u) \<Longrightarrow> surjective(left_comp(u,E))"
@proof
  @obtain "s \<in> target(u) \<rightarrow> source(u)" where "u \<circ> s = id_fun(target(u))"
  @have "left_comp(u,E) \<circ> left_comp(s,E) = id_fun(E\<rightarrow>target(u))"
@qed

lemma bijective_left_comp [forward]:
  "bijective(u) \<Longrightarrow> bijective(left_comp(u,E))" by auto2

definition right_comp :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "right_comp(E,u) = Fun(target(u)\<rightarrow>E, source(u)\<rightarrow>E, \<lambda>f. f \<circ> u)"

lemma right_comp_is_function [typing]:
  "is_function(u) \<Longrightarrow> right_comp(E,u) \<in> (target(u)\<rightarrow>E) \<rightarrow> (source(u)\<rightarrow>E)" by auto2

lemma right_comp_eval [rewrite]:
  "is_function(u) \<Longrightarrow> f \<in> source(right_comp(E,u)) \<Longrightarrow> right_comp(E,u) ` f = f \<circ> u" by auto2
setup {* del_prfstep_thm @{thm right_comp_def} *}

lemma injective_right_comp [forward]:
  "surjective(u) \<Longrightarrow> injective(right_comp(E,u))"
@proof
  @obtain "s \<in> target(u) \<rightarrow> source(u)" where "u \<circ> s = id_fun(target(u))"
  @have "right_comp(E,s) \<circ> right_comp(E,u) = id_fun(target(u)\<rightarrow>E)"
@qed

lemma surjective_right_comp [backward]:
  "injective(u) \<Longrightarrow> source(u) \<noteq> \<emptyset> \<Longrightarrow> surjective(right_comp(E,u))"
@proof
  @obtain "r \<in> target(u) \<rightarrow> source(u)" where "r \<circ> u = id_fun(source(u))"
  @have "right_comp(E,u) \<circ> right_comp(E,r) = id_fun(target(r)\<rightarrow>E)"
@qed

(* The requirement that source(u) \<noteq> \<emptyset> is necessary here, as the following example shows. *)
lemma injective_two_side_comp_counterexample:
  "u = const_fun(\<emptyset>,{\<emptyset>},\<emptyset>) \<Longrightarrow> injective(u) \<and> \<not>surjective(right_comp(\<emptyset>,u))"
@proof @have "target(u) \<rightarrow> \<emptyset> = \<emptyset>" @qed

(* Nevertheless, no condition is required when u is bijective. *)
lemma bijective_right_comp [forward]:
  "bijective(u) \<Longrightarrow> bijective(right_comp(E,u))" by auto2

(* Given a function A \<rightarrow> (B \<rightarrow> D), return a function (A \<times> B) \<rightarrow> D. *)
definition uncurry :: "[i, i, i] \<Rightarrow> i" where [rewrite]:
  "uncurry(A,B,D) = Fun(A\<rightarrow>B\<rightarrow>D, A\<times>B\<rightarrow>D, \<lambda>f. Fun(A\<times>B, D, \<lambda>x. f`fst(x)`snd(x)))"

lemma uncurry_is_function [typing]:
  "uncurry(A,B,D) \<in> (A \<rightarrow> B \<rightarrow> D) \<rightarrow> (A \<times> B \<rightarrow> D)" by auto2

lemma uncurry_eval [rewrite]:
  "f \<in> source(uncurry(A,B,D)) \<Longrightarrow> \<langle>x,y\<rangle>\<in>source(uncurry(A,B,D)`f) \<Longrightarrow> uncurry(A,B,D)`f`\<langle>x,y\<rangle> = f`x`y" by auto2
setup {* del_prfstep_thm @{thm uncurry_def} *}

lemma curry_bijective [forward]: "bijective(curry(A,B,D))"
@proof
  @have "inverse_pair(curry(A,B,D), uncurry(A,B,D))"
@qed

end
