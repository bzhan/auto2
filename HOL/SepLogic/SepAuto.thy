(* The development here follows Separation_Logic_Imperative_HOL
   (by Lammich and Meis) in the AFP *)

theory SepAuto
  imports "../Auto2_Main" "~~/src/HOL/Imperative_HOL/Imperative_HOL"
  keywords "@hoare_induct" :: prf_decl % "proof"
begin

section {* Partial Heaps *}

type_synonym pheap = "heap \<times> addr set"

fun in_range :: "(heap \<times> addr set) \<Rightarrow> bool" where
  "in_range (h,as) \<longleftrightarrow> (\<forall>a\<in>as. a < lim h)"
setup {* add_rewrite_rule @{thm in_range.simps} *}

(* Two heaps agree on a set of addresses. *)
definition relH :: "addr set \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> bool" where [rewrite]:
  "relH as h h' = (in_range (h, as) \<and> in_range (h', as) \<and>
     (\<forall>t. \<forall>a\<in>as. refs h t a = refs h' t a \<and> arrays h t a = arrays h' t a))"

lemma relH_dist_union [forward]:
  "relH (as \<union> as') h h' \<Longrightarrow> relH as h h' \<and> relH as' h h'" by auto2

lemma relH_ref [rewrite]:
  "relH as h h' \<Longrightarrow> addr_of_ref r \<in> as \<Longrightarrow> Ref.get h r = Ref.get h' r"
  by (simp add: Ref.get_def relH_def)

lemma relH_array [rewrite]:
  "relH as h h' \<Longrightarrow> addr_of_array r \<in> as \<Longrightarrow> Array.get h r = Array.get h' r"
  by (simp add: Array.get_def relH_def)

lemma relH_set_ref [resolve]:
  "relH {a. a < lim h \<and> a \<notin> {addr_of_ref r}} h (Ref.set r x h)"
  by (simp add: Ref.set_def relH_def)

lemma relH_set_array [resolve]:
  "relH {a. a < lim h \<and> a \<notin> {addr_of_array r}} h (Array.set r x h)"
  by (simp add: Array.set_def relH_def)

section {* Assertions *}

datatype assn_raw = Assn (assn_fn: "pheap \<Rightarrow> bool")

fun aseval :: "assn_raw \<Rightarrow> pheap \<Rightarrow> bool" where
  "aseval (Assn f) h = f h"
setup {* add_rewrite_rule @{thm aseval.simps} *}

definition proper :: "assn_raw \<Rightarrow> bool" where [rewrite]:
  "proper P = (
    (\<forall>h as. aseval P (h,as) \<longrightarrow> in_range (h,as)) \<and>
    (\<forall>h h' as. aseval P (h,as) \<longrightarrow> relH as h h' \<longrightarrow> in_range (h',as) \<longrightarrow> aseval P (h',as)))"
setup {* add_property_const @{term proper} *}

typedef assn = "Collect proper"
@proof @have "Assn in_range \<in> Collect proper" @qed

setup {* add_rewrite_rule @{thm Rep_assn_inject} *}
setup {* register_wellform_data ("Abs_assn P", ["proper P"]) *}
setup {* add_prfstep_check_req ("Abs_assn P", "proper P") *}

lemma Abs_assn_inverse' [rewrite]: "proper y \<Longrightarrow> Rep_assn (Abs_assn y) = y"
  by (simp add: Abs_assn_inverse)

lemma proper_Rep_assn [forward]: "proper (Rep_assn P)" using Rep_assn by auto

definition models :: "pheap \<Rightarrow> assn \<Rightarrow> bool" (infix "\<Turnstile>" 50) where [rewrite_bidir]:
  "h \<Turnstile> P \<longleftrightarrow> aseval (Rep_assn P) h"

lemma models_in_range [resolve]: "h \<Turnstile> P \<Longrightarrow> in_range h" by auto2

lemma mod_relH [forward]: "relH as h h' \<Longrightarrow> (h, as) \<Turnstile> P \<Longrightarrow> (h', as) \<Turnstile> P" by auto2

instantiation assn :: one begin
definition one_assn :: assn where [rewrite]:
  "1 \<equiv> Abs_assn (Assn (\<lambda>h. snd h = {}))"
instance .. end

abbreviation one_assn :: assn ("emp") where "one_assn \<equiv> 1"

lemma one_assn_rule [rewrite]: "h \<Turnstile> emp \<longleftrightarrow> snd h = {}" by auto2
setup {* del_prfstep_thm @{thm one_assn_def} *}

instantiation assn :: times begin
definition times_assn where [rewrite]:
  "P * Q = Abs_assn (Assn (
    \<lambda>(h, as). (\<exists>as1 as2. as = as1 \<union> as2 \<and> as1 \<inter> as2 = {} \<and>
                   aseval (Rep_assn P) (h, as1) \<and> aseval (Rep_assn Q) (h, as2))))"
instance .. end

lemma mod_star_conv [rewrite]:
  "(h, as) \<Turnstile> A * B \<longleftrightarrow> (\<exists>as1 as2. as = as1 \<union> as2 \<and> as1 \<inter> as2 = {} \<and> (h, as1) \<Turnstile> A \<and> (h, as2) \<Turnstile> B)" by auto2
setup {* del_prfstep_thm @{thm times_assn_def} *}

lemma aseval_ext [backward]: "\<forall>h. aseval P h = aseval P' h \<Longrightarrow> P = P'"
  apply (cases P) apply (cases P') by auto

lemma assn_ext: "\<forall>h as. (h, as) \<Turnstile> P \<longleftrightarrow> (h, as) \<Turnstile> Q \<Longrightarrow> P = Q"
@proof @have "Rep_assn P = Rep_assn Q" @qed
setup {* add_backward_prfstep_cond @{thm assn_ext} [with_filt (order_filter "P" "Q")] *}

setup {* del_prfstep_thm @{thm aseval_ext} *}

lemma assn_one_left: "1 * P = (P::assn)"
@proof
  @have "\<forall>h as. (h, as) \<Turnstile> P \<longleftrightarrow> (h, as) \<Turnstile> 1 * P" @with
    @have "as = {} \<union> as"
  @end
@qed

lemma assn_times_comm: "P * Q = Q * (P::assn)"
@proof
  @have "\<forall>h as. (h, as) \<Turnstile> P * Q \<longleftrightarrow> (h, as) \<Turnstile> Q * P" @with
    @case "(h, as) \<Turnstile> P * Q" @with
      @obtain as1 as2 where "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "(h, as1) \<Turnstile> P" "(h, as2) \<Turnstile> Q"
      @have "as = as2 \<union> as1"
    @end
    @case "(h, as) \<Turnstile> Q * P" @with
      @obtain as1 as2 where "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "(h, as1) \<Turnstile> Q" "(h, as2) \<Turnstile> P"
      @have "as = as2 \<union> as1"
    @end
  @end
@qed

lemma assn_times_assoc: "(P * Q) * R = P * (Q * (R::assn))"
@proof
  @have "\<forall>h as. (h, as) \<Turnstile> (P * Q) * R \<longleftrightarrow> (h, as) \<Turnstile> P * (Q * R)" @with
    @case "(h, as) \<Turnstile> (P * Q) * R" @with
      @obtain as1 as2 where "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "(h, as1) \<Turnstile> P * Q" "(h, as2) \<Turnstile> R"
      @obtain as11 as12 where "as1 = as11 \<union> as12" "as11 \<inter> as12 = {}" "(h, as11) \<Turnstile> P" "(h, as12) \<Turnstile> Q"
      @have "as = as11 \<union> (as12 \<union> as2)"
    @end
    @case "(h, as) \<Turnstile> P * (Q * R)" @with
      @obtain as1 as2 where "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "(h, as1) \<Turnstile> P" "(h, as2) \<Turnstile> Q * R"
      @obtain as21 as22 where "as2 = as21 \<union> as22" "as21 \<inter> as22 = {}" "(h, as21) \<Turnstile> Q" "(h, as22) \<Turnstile> R"
      @have "as = (as1 \<union> as21) \<union> as22"
    @end
  @end
@qed

instantiation assn :: comm_monoid_mult begin
  instance apply standard
  apply (rule assn_times_assoc) apply (rule assn_times_comm) by (rule assn_one_left)
end

subsection {* Existential Quantification *}

definition ex_assn :: "('a \<Rightarrow> assn) \<Rightarrow> assn" (binder "\<exists>\<^sub>A" 11) where [rewrite]:
  "(\<exists>\<^sub>Ax. P x) = Abs_assn (Assn (\<lambda>h. \<exists>x. h \<Turnstile> P x))"

lemma mod_ex_dist [rewrite]: "(h \<Turnstile> (\<exists>\<^sub>Ax. P x)) \<longleftrightarrow> (\<exists>x. h \<Turnstile> P x)" by auto2
setup {* del_prfstep_thm @{thm ex_assn_def} *}

lemma ex_distrib_star: "(\<exists>\<^sub>Ax. P x * Q) = (\<exists>\<^sub>Ax. P x) * Q"
@proof
  @have "\<forall>h as. (h, as) \<Turnstile> (\<exists>\<^sub>Ax. P x) * Q \<longleftrightarrow> (h, as) \<Turnstile> (\<exists>\<^sub>Ax. P x * Q)" @with
    @case "(h, as) \<Turnstile> (\<exists>\<^sub>Ax. P x) * Q" @with
      @obtain as1 as2 where "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "(h, as1) \<Turnstile> (\<exists>\<^sub>Ax. P x)" "(h, as2) \<Turnstile> Q"
      @obtain x where "(h, as1) \<Turnstile> P x"
      @have "(h, as) \<Turnstile> P x * Q"
    @end
  @end
@qed

subsection {* Pointers *}

definition sngr_assn :: "'a::heap ref \<Rightarrow> 'a \<Rightarrow> assn" (infix "\<mapsto>\<^sub>r" 82) where [rewrite]:
  "r \<mapsto>\<^sub>r x = Abs_assn (Assn (
    \<lambda>(h, as). Ref.get h r = x \<and> as = {addr_of_ref r} \<and> addr_of_ref r < lim h))"

lemma sngr_assn_rule [rewrite]:
  "(h, as) \<Turnstile> r \<mapsto>\<^sub>r x \<longleftrightarrow> (Ref.get h r = x \<and> as = {addr_of_ref r} \<and> addr_of_ref r < lim h)" by auto2
setup {* del_prfstep_thm @{thm sngr_assn_def} *}

definition snga_assn :: "'a::heap array \<Rightarrow> 'a list \<Rightarrow> assn" (infix "\<mapsto>\<^sub>a" 82) where [rewrite]:
  "r \<mapsto>\<^sub>a x = Abs_assn (Assn (
    \<lambda>(h, as). Array.get h r = x \<and> as = {addr_of_array r} \<and> addr_of_array r < lim h))"

lemma snga_assn_rule [rewrite]:
  "(h, as) \<Turnstile> r \<mapsto>\<^sub>a x \<longleftrightarrow> (Array.get h r = x \<and> as = {addr_of_array r} \<and> addr_of_array r < lim h)" by auto2
setup {* del_prfstep_thm @{thm snga_assn_def} *}

subsection {* Pure Assertions *}

definition pure_assn :: "bool \<Rightarrow> assn" ("\<up>") where [rewrite]:
  "\<up>b = Abs_assn (Assn (\<lambda>h. snd h = {} \<and> b))"

lemma pure_assn_rule [rewrite]: "h \<Turnstile> \<up>b \<longleftrightarrow> (snd h = {} \<and> b)" by auto2
setup {* del_prfstep_thm @{thm pure_assn_def} *}

definition top_assn :: assn ("true") where [rewrite]:
  "top_assn = Abs_assn (Assn in_range)"

lemma top_assn_rule [rewrite]: "h \<Turnstile> true \<longleftrightarrow> in_range h" by auto2
setup {* del_prfstep_thm @{thm top_assn_def} *}

setup {* del_prfstep_thm @{thm models_def} *}

subsection {* Properties of assertions *}

abbreviation bot_assn :: assn ("false") where "bot_assn \<equiv> \<up>False"

lemma mod_false' [resolve]: "\<not> (h \<Turnstile> false * Ru)" by auto2

lemma mod_star_trueI: "h \<Turnstile> P \<Longrightarrow> h \<Turnstile> P * true"
@proof @have "snd h = snd h \<union> {}" @qed

lemma sngr_same_false [resolve]: "\<not>h \<Turnstile> p \<mapsto>\<^sub>r x * p \<mapsto>\<^sub>r y * Qu" by auto2

lemma ref_prec: "h \<Turnstile> p \<mapsto>\<^sub>r x * Qu \<Longrightarrow> h \<Turnstile> p \<mapsto>\<^sub>r y * Ru \<Longrightarrow> x = y" by auto2
setup {* add_forward_prfstep_cond @{thm ref_prec} [with_cond "?x \<noteq> ?y"] *}

lemma array_prec: "h \<Turnstile> p \<mapsto>\<^sub>a x * Qu \<Longrightarrow> h \<Turnstile> p \<mapsto>\<^sub>a y * Ru \<Longrightarrow> x = y" by auto2
setup {* add_forward_prfstep_cond @{thm array_prec} [with_cond "?x \<noteq> ?y"] *}

lemma mod_pure_star_dist [rewrite]:
  "h \<Turnstile> P * \<up>b \<longleftrightarrow> (h \<Turnstile> P \<and> b)"
@proof
  @case "h \<Turnstile> P \<and> b" @with
    @have "snd h = snd h \<union> {}"
  @end
@qed

lemma mod_pure': "h \<Turnstile> \<up>b \<longleftrightarrow> (h \<Turnstile> emp \<and> b)" by auto2
lemma pure_conj:  "\<up>(P \<and> Q) = \<up>P * \<up>Q" by auto2

subsection {* Entailment and its properties *}

definition entails :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infix "\<Longrightarrow>\<^sub>A" 10) where [rewrite]:
  "(P \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<forall>h. h \<Turnstile> P \<longrightarrow> h \<Turnstile> Q)"

lemma entails_triv: "A \<Longrightarrow>\<^sub>A A" by auto2
lemma entails_true: "A \<Longrightarrow>\<^sub>A true" by auto2
lemma entail_equiv_forward: "P = Q \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q" by auto2
lemma entail_equiv_backward: "P = Q \<Longrightarrow> Q \<Longrightarrow>\<^sub>A P" by auto2
lemma entailsD [forward]: "P \<Longrightarrow>\<^sub>A Q \<Longrightarrow> h \<Turnstile> P \<Longrightarrow> h \<Turnstile> Q" by auto2
lemma entailsD': "P \<Longrightarrow>\<^sub>A Q \<Longrightarrow> h \<Turnstile> P * R \<Longrightarrow> h \<Turnstile> Q * R" by auto2
lemma entailsD_back: "P \<Longrightarrow>\<^sub>A Q \<Longrightarrow> \<not>h \<Turnstile> Q * R \<Longrightarrow> \<not>h \<Turnstile> P * R" by auto2
lemma entail_trans2: "A \<Longrightarrow>\<^sub>A D * B \<Longrightarrow> B \<Longrightarrow>\<^sub>A C \<Longrightarrow> A \<Longrightarrow>\<^sub>A D * C" by auto2
lemma entail_trans2': "D * B \<Longrightarrow>\<^sub>A A \<Longrightarrow> C \<Longrightarrow>\<^sub>A B \<Longrightarrow> D * C \<Longrightarrow>\<^sub>A A" by auto2
lemma entails_invD: "A \<Longrightarrow>\<^sub>A B \<Longrightarrow> \<not>(h \<Turnstile> B) \<Longrightarrow> \<not>(h \<Turnstile> A)" by auto2

section {* Definition of the run predicate *}

inductive run :: "'a Heap \<Rightarrow> heap option \<Rightarrow> heap option \<Rightarrow> 'a \<Rightarrow> bool" where
  "run c None None r"
| "execute c h = None \<Longrightarrow> run c (Some h) None r"
| "execute c h = Some (r, h') \<Longrightarrow> run c (Some h) (Some h') r"
setup {* add_case_induct_rule @{thm run.cases} *}
setup {* fold add_resolve_prfstep @{thms run.intros(1,2)} *}
setup {* add_forward_prfstep @{thm run.intros(3)} *}
setup {* add_backward_prfstep @{thm run.intros(3)} *}

lemma run_preserve_None [forward]:
  "run c None \<sigma>' r \<Longrightarrow> \<sigma>' = None"
@proof @case_induct "run c None \<sigma>' r" @qed

lemma run_execute_fail [forward]:
  "execute c h = None \<Longrightarrow> run c (Some h) \<sigma>' r \<Longrightarrow> \<sigma>' = None"
@proof @case_induct "run c (Some h) \<sigma>' r" @qed

lemma run_execute_succeed [forward]:
  "execute c h = Some (r', h') \<Longrightarrow> run c (Some h) \<sigma>' r \<Longrightarrow> \<sigma>' = Some h' \<and> r = r'"
@proof @case_induct "run c (Some h) \<sigma>' r" @qed

lemma run_complete [resolve]:
  "\<exists>\<sigma>' r. run c \<sigma> \<sigma>' (r::'a)"
@proof
  @obtain "r::'a" where "r = r"
  @case "\<sigma> = None" @with @have "run c None None r" @end
  @case "execute c (the \<sigma>) = None" @with @have "run c \<sigma> None r" @end
@qed

lemma run_to_execute [forward]:
  "run c (Some h) \<sigma>' r \<Longrightarrow> if \<sigma>' = None then execute c h = None else execute c h = Some (r, the \<sigma>')"
@proof @case_induct "run c (Some h) \<sigma>' r" @qed

setup {* add_rewrite_rule @{thm execute_bind(1)} *}
lemma runE [forward]:
  "run f (Some h) (Some h') r' \<Longrightarrow> run (f \<bind> g) (Some h) \<sigma> r \<Longrightarrow> run (g r') (Some h') \<sigma> r"
@proof @case "\<sigma> = None" @qed

setup {* add_rewrite_rule @{thm Array.get_alloc} *}
setup {* add_rewrite_rule @{thm Ref.get_alloc} *}
setup {* add_rewrite_rule_bidir @{thm Array.length_def} *}

section {* Definition of hoare triple, and the frame rule. *}

definition new_addrs :: "heap \<Rightarrow> addr set \<Rightarrow> heap \<Rightarrow> addr set" where [rewrite]:
  "new_addrs h as h' = as \<union> {a. lim h \<le> a \<and> a < lim h'}"

lemma new_addr_refl [rewrite]: "new_addrs h as h = as" by auto2

definition hoare_triple :: "assn \<Rightarrow> 'a Heap \<Rightarrow> ('a \<Rightarrow> assn) \<Rightarrow> bool" ("<_>/ _/ <_>") where [rewrite]:
  "<P> c <Q> \<longleftrightarrow> (\<forall>h as \<sigma> r. (h, as) \<Turnstile> P \<longrightarrow> run c (Some h) \<sigma> r \<longrightarrow>
    (\<sigma> \<noteq> None \<and> (the \<sigma>, new_addrs h as (the \<sigma>)) \<Turnstile> Q r \<and> relH {a . a < lim h \<and> a \<notin> as} h (the \<sigma>) \<and>
     lim h \<le> lim (the \<sigma>)))"

abbreviation hoare_triple' :: "assn \<Rightarrow> 'r Heap \<Rightarrow> ('r \<Rightarrow> assn) \<Rightarrow> bool" ("<_> _ <_>\<^sub>t") where
  "<P> c <Q>\<^sub>t \<equiv> <P> c <\<lambda>r. Q r * true>"

lemma frame_rule [backward]:
  "<P> c <Q> \<Longrightarrow> <P * R> c <\<lambda>x. Q x * R>"
@proof
  @have "\<forall>h as \<sigma> r. (h, as) \<Turnstile> P * R \<longrightarrow> run c (Some h) \<sigma> r \<longrightarrow>
                    (\<sigma> \<noteq> None \<and> (the \<sigma>, new_addrs h as (the \<sigma>)) \<Turnstile> Q r * R \<and>
                     relH {a . a < lim h \<and> a \<notin> as} h (the \<sigma>) \<and> lim h \<le> lim (the \<sigma>))" @with
    @obtain as1 as2 where "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "(h, as1) \<Turnstile> P \<and> (h, as2) \<Turnstile> R" @then
    @have "relH as2 h (the \<sigma>)" @then
    @have "new_addrs h as (the \<sigma>) = new_addrs h as1 (the \<sigma>) \<union> as2"
  @end
@qed

(* This is the last use of the definition of separating conjunction. *)
setup {* del_prfstep_thm @{thm mod_star_conv} *}

lemma norm_pre_pure_iff: "<P * \<up>b> c <Q> \<longleftrightarrow> (b \<longrightarrow> <P> c <Q>)" by auto2

section {* Hoare triples for atomic commands *}

(* First, those that do not modify the heap. *)
setup {* add_rewrite_rule @{thm execute_assert(1)} *}
lemma assert_rule:
  "<\<up>(R x)> assert R x <\<lambda>r. \<up>(r = x)>" by auto2

lemma execute_return' [rewrite]: "execute (return x) h = Some (x, h)" by (metis comp_eq_dest_lhs execute_return)
lemma return_rule:
  "<emp> return x <\<lambda>r. \<up>(r = x)>" by auto2

setup {* add_rewrite_rule @{thm execute_nth(1)} *}
lemma nth_rule:
  "<a \<mapsto>\<^sub>a xs * \<up>(i < length xs)> Array.nth a i <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = xs ! i)>" by auto2

setup {* add_rewrite_rule @{thm execute_len} *}
lemma length_rule:
  "<a \<mapsto>\<^sub>a xs> Array.len a <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = length xs)>" by auto2

setup {* add_rewrite_rule @{thm execute_lookup} *}
lemma lookup_rule:
  "<p \<mapsto>\<^sub>r x> !p <\<lambda>r. p \<mapsto>\<^sub>r x * \<up>(r = x)>" by auto2

(* Next, the update rules. *)
setup {* add_rewrite_rule @{thm Ref.lim_set} *}
lemma Array_lim_set [rewrite]: "lim (Array.set p xs h) = lim h" by (simp add: Array.set_def)

setup {* fold add_rewrite_rule [@{thm Ref.get_set_eq}, @{thm Array.get_set_eq}] *}
setup {* add_rewrite_rule @{thm Array.update_def} *}

setup {* add_rewrite_rule @{thm execute_upd(1)} *}
lemma upd_rule:
  "<a \<mapsto>\<^sub>a xs * \<up>(i < length xs)> Array.upd i x a <\<lambda>r. a \<mapsto>\<^sub>a list_update xs i x * \<up>(r = a)>" by auto2

setup {* add_rewrite_rule @{thm execute_update} *}
lemma update_rule:
  "<p \<mapsto>\<^sub>r y> p := x <\<lambda>r. p \<mapsto>\<^sub>r x>" by auto2

(* Finally, the allocation rules. *)
lemma lim_set_gen [rewrite]: "lim (h\<lparr>lim := l\<rparr>) = l" by simp

lemma Array_alloc_def' [rewrite]: 
  "Array.alloc xs h = (let l = lim h; r = Array l in (r, (Array.set r xs (h\<lparr>lim := l + 1\<rparr>))))"
  by (simp add: Array.alloc_def)

setup {* fold add_rewrite_rule [
  @{thm addr_of_array.simps}, @{thm addr_of_ref.simps}, @{thm Ref.alloc_def}] *}

lemma refs_on_Array_set [rewrite]: "refs (Array.set p xs h) t i = refs h t i"
  by (simp add: Array.set_def)

lemma arrays_on_Ref_set [rewrite]: "arrays (Ref.set p x h) t i = arrays h t i"
  by (simp add: Ref.set_def)

lemma refs_on_Array_alloc [rewrite]: "refs (snd (Array.alloc xs h)) t i = refs h t i"
  by (metis (no_types, lifting) Array.alloc_def refs_on_Array_set select_convs(2) snd_conv surjective update_convs(3))

lemma arrays_on_Ref_alloc [rewrite]: "arrays (snd (Ref.alloc x h)) t i = arrays h t i"
  by (metis (no_types, lifting) Ref.alloc_def arrays_on_Ref_set select_convs(1) sndI surjective update_convs(3))

lemma arrays_on_Array_alloc [rewrite]: "i < lim h \<Longrightarrow> arrays (snd (Array.alloc xs h)) t i = arrays h t i"
  by (smt Array.alloc_def Array.set_def addr_of_array.simps fun_upd_apply less_or_eq_imp_le
          linorder_not_less simps(1) snd_conv surjective update_convs(1) update_convs(3))

lemma refs_on_Ref_alloc [rewrite]: "i < lim h \<Longrightarrow> refs (snd (Ref.alloc x h)) t i = refs h t i"
  by (smt Ref.alloc_def Ref.set_def addr_of_ref.simps fun_upd_apply less_or_eq_imp_le
          linorder_not_less select_convs(2) simps(6) snd_conv surjective update_convs(3))

setup {* add_rewrite_rule @{thm execute_new} *}
lemma new_rule:
  "<emp> Array.new n x <\<lambda>r. r \<mapsto>\<^sub>a replicate n x>" by auto2

setup {* add_rewrite_rule @{thm execute_of_list} *}
lemma of_list_rule:
  "<emp> Array.of_list xs <\<lambda>r. r \<mapsto>\<^sub>a xs>" by auto2

setup {* add_rewrite_rule @{thm execute_ref} *}
lemma ref_rule:
  "<emp> ref x <\<lambda>r. r \<mapsto>\<^sub>r x>" by auto2

setup {* fold del_prfstep_thm [@{thm sngr_assn_rule}, @{thm snga_assn_rule}] *}
setup {* fold del_prfstep_thm [@{thm pure_assn_rule}, @{thm top_assn_rule}, @{thm mod_pure_star_dist}] *}

section {* success_run and its properties. *}

lemma new_addrs_bind [rewrite]:
  "lim h \<le> lim h' \<Longrightarrow> lim h' \<le> lim h'' \<Longrightarrow> new_addrs h' (new_addrs h as h') h'' = new_addrs h as h''" by auto2

fun success_run :: "'a Heap \<Rightarrow> pheap \<Rightarrow> pheap \<Rightarrow> 'a \<Rightarrow> bool" where
  "success_run f (h, as) (h', as') r \<longleftrightarrow>
    as' = new_addrs h as h' \<and> run f (Some h) (Some h') r \<and> relH {a. a < lim h \<and> a \<notin> as} h h' \<and> lim h \<le> lim h'"
setup {* add_rewrite_rule @{thm success_run.simps} *}

lemma success_run_bind:
  "success_run f h h' r \<Longrightarrow> success_run (g r) h' h'' r' \<Longrightarrow> success_run (f \<bind> g) h h'' r'" by auto2

lemma success_run_next: "success_run f h h'' r' \<Longrightarrow>
  \<forall>h'. \<sigma> = Some (fst h') \<and> success_run (f \<bind> g) h h' r \<longrightarrow> \<not> h' \<Turnstile> Q \<Longrightarrow>
  \<forall>h'. \<sigma> = Some (fst h') \<and> success_run (g r') h'' h' r \<longrightarrow> \<not> h' \<Turnstile> Q" by auto2

lemma hoare_triple_def' [rewrite]:
  "<P> c <Q> \<longleftrightarrow> (\<forall>h \<sigma> r. h \<Turnstile> P \<longrightarrow> run c (Some (fst h)) \<sigma> r \<longrightarrow>
    (\<sigma> \<noteq> None \<and> (the \<sigma>, new_addrs (fst h) (snd h) (the \<sigma>)) \<Turnstile> Q r \<and>
     relH {a . a < lim (fst h) \<and> a \<notin> (snd h)} (fst h) (the \<sigma>) \<and>
     lim (fst h) \<le> lim (the \<sigma>)))" using hoare_triple_def by fastforce

lemma hoare_tripleE':
  "<P> c <Q> \<Longrightarrow> h \<Turnstile> P * Ru \<Longrightarrow> run c (Some (fst h)) \<sigma> r \<Longrightarrow>
   \<exists>h'. h' \<Turnstile> Q r * Ru \<and> \<sigma> = Some (fst h') \<and> success_run c h h' r"
@proof @have "<P * Ru> c <\<lambda>r. Q r * Ru>" @qed

lemma hoare_tripleI:
  "\<not><P> c <Q> \<Longrightarrow> \<exists>h \<sigma> r. h \<Turnstile> P \<and> run c (Some (fst h)) \<sigma> r \<and>
   (\<forall>h'. \<sigma> = Some (fst h') \<and> success_run c h h' r \<longrightarrow> \<not>h' \<Turnstile> Q r)" by auto2

lemma hoare_triple_mp:
  "<P> c <Q> \<Longrightarrow> h \<Turnstile> P * Ru \<Longrightarrow> success_run c h h' r \<Longrightarrow> h' \<Turnstile> (Q r) * Ru"
@proof @have "<P * Ru> c <\<lambda>r. Q r * Ru>" @qed

lemma hoare_tripleE'':
  "<P> c <Q> \<Longrightarrow> h \<Turnstile> P * Ru \<Longrightarrow> run (c \<bind> g) (Some (fst h)) \<sigma> r \<Longrightarrow>
   \<exists>r' h'. run (g r') (Some (fst h')) \<sigma> r \<and> h' \<Turnstile> Q r' * Ru \<and> success_run c h h' r'"
@proof
  @have "<P * Ru> c <\<lambda>r. Q r * Ru>" @then
  @obtain \<sigma>' r' where "run c (Some (fst h)) \<sigma>' r'"
@qed

definition heap_preserving :: "'a Heap \<Rightarrow> bool" where [rewrite]:
  "heap_preserving c = (\<forall>h h' r. effect c h h' r \<longrightarrow> h = h')"

setup {* add_forward_prfstep @{thm effectI} *}
lemma heap_preservingD [forward]:
  "heap_preserving c \<Longrightarrow> success_run c h h' r \<Longrightarrow> h = h'" by auto2
setup {* del_prfstep_thm @{thm effectI} *}

lemma heap_preserving_effectD:
  "heap_preserving c \<Longrightarrow> effect c h h' r \<Longrightarrow> h = h'" by auto2

lemma effect_bind [forward]:
  "effect (f \<bind> g) h h'' r' \<Longrightarrow> \<exists>h' r. effect f h h' r \<and> effect (g r) h' h'' r'"
  by (elim effect_elims) auto

lemma hoare_tripleE'_preserve:
  "heap_preserving c \<Longrightarrow>
   \<exists>h'. h' \<Turnstile> Q \<and> \<sigma> = Some (fst h') \<and> success_run c h h' r \<Longrightarrow>
   h \<Turnstile> Q \<and> \<sigma> = Some (fst h) \<and> success_run c h h r" by auto2

lemma hoare_tripleE''_preserve:
  "heap_preserving c \<Longrightarrow>
   \<exists>r' h'. run (g r') (Some (fst h')) \<sigma> r \<and> h' \<Turnstile> Q r' * Ru \<and> success_run c h h' r' \<Longrightarrow>
   \<exists>r'. run (g r') (Some (fst h)) \<sigma> r \<and> h \<Turnstile> Q r' * Ru \<and> success_run c h h r'" by auto2

setup {* del_prfstep_thm @{thm success_run.simps} *}
setup {* del_prfstep_thm @{thm hoare_triple_def} *}
setup {* del_prfstep_thm @{thm hoare_triple_def'} *}

subsection {* Definition of procedures *}

named_theorems sep_proc_defs "Seplogic: definitions of procedures"
named_theorems sep_prec_thms "Seplogic: precision theorems"
(* Note adding to sep_heap_presv_thms is taken care of by heap_presv_thms attribute. *)
named_theorems sep_heap_presv_thms "Seplogic: heap preservation theorems"

declare ref_prec [sep_prec_thms]
declare array_prec [sep_prec_thms]

(* ASCII abbreviations for ML files. *)
abbreviation (input) ex_assn_ascii :: "('a \<Rightarrow> assn) \<Rightarrow> assn" (binder "EXA" 11)
  where "ex_assn_ascii \<equiv> ex_assn"

abbreviation (input) models_ascii :: "pheap \<Rightarrow> assn \<Rightarrow> bool" (infix "|=" 50)
  where "h |= P \<equiv> h \<Turnstile> P"

ML_file "sep_util.ML"
ML_file "assn_matcher.ML"
ML_file "sep_steps.ML"
ML_file "sep_steps_test.ML"
ML_file "sep_induct.ML"

attribute_setup heap_presv_thms = {* setup_attrib add_heap_preserving_thm *}
attribute_setup forward_ent = {* setup_attrib add_forward_ent_prfstep *}
attribute_setup forward_ent_shadow = {* setup_attrib add_forward_ent_shadowing_prfstep *}
attribute_setup rewrite_ent = {* setup_attrib add_rewrite_ent_rule *}
attribute_setup hoare_create_case = {* setup_attrib add_match_hoare_create_case *}
attribute_setup hoare_triple = {* setup_attrib add_hoare_triple_prfstep *}
attribute_setup hoare_triple_direct = {* setup_attrib add_hoare_triple_direct_prfstep *}

lemma heap_preserving_lookup [heap_presv_thms]: "heap_preserving (!p)"
  using effect_lookupE heap_preserving_def by fastforce

lemma heap_preserving_return [heap_presv_thms]: "heap_preserving (return x)"
  using effect_returnE heap_preserving_def by fastforce

lemma heap_preserving_nth [heap_presv_thms]: "heap_preserving (Array.nth a i)"
  using effect_nthE heap_preserving_def by fastforce

lemma heap_preserving_len [heap_presv_thms]: "heap_preserving (Array.len a)"
  using effect_lengthE heap_preserving_def by fastforce

lemma heap_preserve_assert [heap_presv_thms]: "heap_preserving (assert P x)"
  using effect_assertE heap_preserving_def by fastforce

setup {* fold add_hoare_triple_prfstep [
  @{thm assert_rule}, @{thm update_rule}, @{thm nth_rule}, @{thm upd_rule}] *}

setup {* fold add_match_hoare_create_case [
  @{thm assert_rule}, @{thm nth_rule}, @{thm upd_rule}] *}

setup {* fold add_hoare_triple_direct_prfstep [
  @{thm return_rule}, @{thm ref_rule}, @{thm lookup_rule}, @{thm new_rule},
  @{thm of_list_rule}, @{thm length_rule}] *}

(* Some simple tests *)

theorem "<emp> ref x <\<lambda>r. r \<mapsto>\<^sub>r x>" by auto2
theorem "<a \<mapsto>\<^sub>r x> ref x <\<lambda>r. a \<mapsto>\<^sub>r x * r \<mapsto>\<^sub>r x>" by auto2
theorem "<a \<mapsto>\<^sub>r x> (!a) <\<lambda>r. a \<mapsto>\<^sub>r x * \<up>(r = x)>" by auto2
theorem "<a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y> (!a) <\<lambda>r. a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y * \<up>(r = x)>" by auto2
theorem "<a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y> (!b) <\<lambda>r. a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y * \<up>(r = y)>" by auto2
theorem "<a \<mapsto>\<^sub>r x> do { a := y; !a } <\<lambda>r. a \<mapsto>\<^sub>r y * \<up>(r = y)>" by auto2
theorem "<a \<mapsto>\<^sub>r x> do { a := y; a := z; !a } <\<lambda>r. a \<mapsto>\<^sub>r z * \<up>(r = z)>" by auto2
theorem "<a \<mapsto>\<^sub>r x> do { y \<leftarrow> !a; ref y} <\<lambda>r. a \<mapsto>\<^sub>r x * r \<mapsto>\<^sub>r x>" by auto2
theorem "<emp> return x <\<lambda>r. \<up>(r = x)>" by auto2

end
