(*
  File: Int.thy
  Author: Bohua Zhan

  Construction of integers (as pairs of natural numbers, under the equivalence
  relation (a,b) ~ (c,d) iff a + d = b + c.
*)

theory Int
  imports Nat Ring EquivRel
begin

section \<open>Integers as a quotient set\<close>

definition int_rel_space :: i where [rewrite]:
  "int_rel_space = nat\<times>nat"

definition int_rel :: i where [rewrite]:
  "int_rel = Equiv(int_rel_space, \<lambda>p q. let \<langle>a,b\<rangle> = p; \<langle>c,d\<rangle> = q in a +\<^sub>\<nat> d = b +\<^sub>\<nat> c)"
notation int_rel ("\<R>")

lemma int_rel_spaceI [typing]: "x \<in> nat \<Longrightarrow> y \<in> nat \<Longrightarrow> \<langle>x,y\<rangle> \<in>. \<R>" by auto2
lemma int_rel_spaceD [forward]: "p \<in>. \<R> \<Longrightarrow> p = \<langle>fst(p),snd(p)\<rangle> \<and> fst(p) \<in> nat \<and> snd(p) \<in> nat" by auto2
setup {* del_prfstep_thm @{thm int_rel_space_def} *}

lemma int_rel_trans [backward2]:
  "a1 \<in>. \<nat> \<Longrightarrow> a2 \<in>. \<nat> \<Longrightarrow> b1 \<in>. \<nat> \<Longrightarrow> b2 \<in>. \<nat> \<Longrightarrow> c1 \<in>. \<nat> \<Longrightarrow> c2 \<in>. \<nat> \<Longrightarrow>
   a1 +\<^sub>\<nat> b2 = a2 +\<^sub>\<nat> b1 \<Longrightarrow> b1 +\<^sub>\<nat> c2 = b2 +\<^sub>\<nat> c1 \<Longrightarrow> a1 +\<^sub>\<nat> c2 = a2 +\<^sub>\<nat> c1"
@proof
  @have "(a1 +\<^sub>\<nat> c2) +\<^sub>\<nat> b2 = (a1 +\<^sub>\<nat> b2) +\<^sub>\<nat> c2"
  @have "(a2 +\<^sub>\<nat> b1) +\<^sub>\<nat> c2 = a2 +\<^sub>\<nat> (b1 +\<^sub>\<nat> c2)"
  @have "a2 +\<^sub>\<nat> (b2 +\<^sub>\<nat> c1) = (a2 +\<^sub>\<nat> c1) +\<^sub>\<nat> b2"
@qed

lemma int_rel_is_rel [typing]: "\<R> \<in> equiv_space(int_rel_space)" by auto2
setup {* del_prfstep_thm @{thm int_rel_trans} *}

lemma int_rel_eval:
  "x \<in>. \<R> \<Longrightarrow> y \<in>. \<R> \<Longrightarrow> x \<sim>\<^sub>\<R> y \<longleftrightarrow> fst(x) +\<^sub>\<nat> snd(y) = snd(x) +\<^sub>\<nat> fst(y)" by auto2
setup {* add_rewrite_rule_cond @{thm int_rel_eval} [with_cond "?x \<noteq> ?y"] *}
setup {* del_prfstep_thm @{thm int_rel_def} *}

definition int :: i where int_def [rewrite_bidir]:
  "int = carrier(\<R>) // \<R>"

abbreviation Int :: "i \<Rightarrow> i" where "Int(p) \<equiv> equiv_class(\<R>,p)"

section \<open>Integers as a ring\<close>
  
definition int_add_raw :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "int_add_raw(p,q) = \<langle>fst(p)+\<^sub>\<nat>fst(q),snd(p)+\<^sub>\<nat>snd(q)\<rangle>"
setup {* register_wellform_data ("int_add_raw(p,q)", ["p \<in>. \<R>", "q \<in>. \<R>"]) *}

lemma int_add_raw_eval [rewrite]: "int_add_raw(\<langle>a,b\<rangle>,\<langle>c,d\<rangle>) = \<langle>a+\<^sub>\<nat>c, b+\<^sub>\<nat>d\<rangle>" by auto2
setup {* del_prfstep_thm @{thm int_add_raw_def} *}

definition int_mult_raw :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "int_mult_raw(p,q) = \<langle>fst(p)*\<^sub>\<nat>fst(q) +\<^sub>\<nat> snd(p)*\<^sub>\<nat>snd(q), fst(p)*\<^sub>\<nat>snd(q) +\<^sub>\<nat> snd(p)*\<^sub>\<nat>fst(q)\<rangle>"
setup {* register_wellform_data ("int_mult_raw(p,q)", ["p \<in>. \<R>", "q \<in>. \<R>"]) *}

lemma int_mult_raw_eval [rewrite]: "int_mult_raw(\<langle>a,b\<rangle>,\<langle>c,d\<rangle>) = \<langle>a*\<^sub>\<nat>c +\<^sub>\<nat> b*\<^sub>\<nat>d, a*\<^sub>\<nat>d +\<^sub>\<nat> b*\<^sub>\<nat>c\<rangle>" by auto2
setup {* del_prfstep_thm @{thm int_mult_raw_def} *}

definition nonneg_int_raw :: "i \<Rightarrow> o" where [rewrite]:
  "nonneg_int_raw(p) \<longleftrightarrow> fst(p) \<ge>\<^sub>\<nat> snd(p)"

definition nonneg_int :: "i \<Rightarrow> o" where [rewrite]:
  "nonneg_int(x) \<longleftrightarrow> nonneg_int_raw(rep(\<R>,x))"

definition nonneg_ints :: i where [rewrite]:
  "nonneg_ints = {x\<in>int. nonneg_int(x)}"

definition int_ring :: i where [rewrite]:
  "int_ring = Ring(int, Int(\<langle>0,0\<rangle>), \<lambda>x y. Int(int_add_raw(rep(\<R>,x), rep(\<R>,y))),
                        Int(\<langle>1,0\<rangle>), \<lambda>x y. Int(int_mult_raw(rep(\<R>,x), rep(\<R>,y))))"

lemma int_ring_is_ring_raw [forward]: "ring_form(int_ring)" by auto2

definition int_ord_ring :: i  ("\<int>") where [rewrite]:
  "int_ord_ring = ord_ring_from_nonneg(int_ring, nonneg_ints)"

lemma int_is_ring_raw [forward]: "is_ring_raw(\<int>)" by auto2
lemma int_carrier [rewrite_bidir]: "carrier(\<int>) = int" by auto2
lemma int_evals [rewrite]:
  "\<zero>\<^sub>\<int> = Int(\<langle>0,0\<rangle>)"
  "\<one>\<^sub>\<int> = Int(\<langle>1,0\<rangle>)"
  "x \<in>. \<int> \<Longrightarrow> y \<in>. \<int> \<Longrightarrow> x +\<^sub>\<int> y = Int(int_add_raw(rep(\<R>,x), rep(\<R>,y)))"
  "x \<in>. \<int> \<Longrightarrow> y \<in>. \<int> \<Longrightarrow> x *\<^sub>\<int> y = Int(int_mult_raw(rep(\<R>,x), rep(\<R>,y)))" by auto2+
    
lemma int_is_ord_ring_prep [forward]:
  "is_comm_ring(\<int>) \<Longrightarrow> nonneg_compat(\<int>,nonneg_ints) \<Longrightarrow> is_ord_ring(\<int>)" by auto2

setup {* fold del_prfstep_thm [@{thm int_ring_def}, @{thm int_ord_ring_def}] *}

lemma int_choose_rep: "x \<in>. \<int> \<Longrightarrow> x = Int(rep(\<R>,x))" by auto2
setup {* add_rewrite_rule_cond @{thm int_choose_rep} [with_filt (size1_filter "x")] *}

section \<open>Addition on integers\<close>

lemma int_add_eval [rewrite]:
  "x \<in>. \<R> \<Longrightarrow> y \<in>. \<R> \<Longrightarrow> Int(x) +\<^sub>\<int> Int(y) = Int(int_add_raw(x,y))"
@proof
  @have "compat_meta_bin1(\<R>, int_add_raw)" @with
    @have (@rule) "\<forall>a b c d a' b'. \<langle>c,d\<rangle> \<in>. \<R> \<longrightarrow> \<langle>a',b'\<rangle> \<sim>\<^sub>\<R> \<langle>a,b\<rangle> \<longrightarrow>
                   int_add_raw(\<langle>a',b'\<rangle>,\<langle>c,d\<rangle>) \<sim>\<^sub>\<R> int_add_raw(\<langle>a,b\<rangle>,\<langle>c,d\<rangle>)" @with
      @have "(a' +\<^sub>\<nat> c) +\<^sub>\<nat> (b +\<^sub>\<nat> d) = (a' +\<^sub>\<nat> b) +\<^sub>\<nat> (c +\<^sub>\<nat> d)"
      @have "(b' +\<^sub>\<nat> d) +\<^sub>\<nat> (a +\<^sub>\<nat> c) = (b' +\<^sub>\<nat> a) +\<^sub>\<nat> (c +\<^sub>\<nat> d)"
    @end
  @end
  @have "compat_meta_bin2(\<R>, int_add_raw)" @with
    @have (@rule) "\<forall>a b c d c' d'. \<langle>a,b\<rangle> \<in>. \<R> \<longrightarrow> \<langle>c',d'\<rangle> \<sim>\<^sub>\<R> \<langle>c,d\<rangle> \<longrightarrow>
                   int_add_raw(\<langle>a,b\<rangle>,\<langle>c',d'\<rangle>) \<sim>\<^sub>\<R> int_add_raw(\<langle>a,b\<rangle>,\<langle>c,d\<rangle>)" @with
      @have "(a +\<^sub>\<nat> c') +\<^sub>\<nat> (b +\<^sub>\<nat> d) = (a +\<^sub>\<nat> b) +\<^sub>\<nat> (c' +\<^sub>\<nat> d)"
      @have "(b +\<^sub>\<nat> d') +\<^sub>\<nat> (a +\<^sub>\<nat> c) = (a +\<^sub>\<nat> b) +\<^sub>\<nat> (d' +\<^sub>\<nat> c)"
    @end
  @end
  @have "compat_meta_bin(\<R>, int_add_raw)"
@qed
setup {* del_prfstep_thm @{thm int_evals(3)} *}

lemma int_add_comm [forward]: "is_plus_comm(\<int>)" by auto2
lemma int_add_assoc [forward]: "is_plus_assoc(\<int>)" by auto2

section \<open>Multiplication on integers\<close>

lemma int_mult_eval [rewrite]:
  "x \<in>. \<R> \<Longrightarrow> y \<in>. \<R> \<Longrightarrow> Int(x) *\<^sub>\<int> Int(y) = Int(int_mult_raw(x,y))"
@proof
  @have "compat_meta_bin1(\<R>, int_mult_raw)" @with
    @have (@rule) "\<forall>a b c d a' b'. \<langle>c,d\<rangle> \<in>. \<R> \<longrightarrow> \<langle>a',b'\<rangle> \<sim>\<^sub>\<R> \<langle>a,b\<rangle> \<longrightarrow>
                   int_mult_raw(\<langle>a',b'\<rangle>,\<langle>c,d\<rangle>) \<sim>\<^sub>\<R> int_mult_raw(\<langle>a,b\<rangle>,\<langle>c,d\<rangle>)" @with
      @have "(a'*\<^sub>\<nat>c +\<^sub>\<nat> b'*\<^sub>\<nat>d) +\<^sub>\<nat> (a*\<^sub>\<nat>d +\<^sub>\<nat> b*\<^sub>\<nat>c) = (a'+\<^sub>\<nat>b) *\<^sub>\<nat> c +\<^sub>\<nat> (b'+\<^sub>\<nat>a) *\<^sub>\<nat> d"
      @have "(a'*\<^sub>\<nat>d +\<^sub>\<nat> b'*\<^sub>\<nat>c) +\<^sub>\<nat> (a*\<^sub>\<nat>c +\<^sub>\<nat> b*\<^sub>\<nat>d) = (b'+\<^sub>\<nat>a) *\<^sub>\<nat> c +\<^sub>\<nat> (a'+\<^sub>\<nat>b) *\<^sub>\<nat> d"
    @end
  @end
  @have "compat_meta_bin2(\<R>, int_mult_raw)" @with
    @have (@rule) "\<forall>a b c d c' d'. \<langle>a,b\<rangle> \<in>. \<R> \<longrightarrow> \<langle>c',d'\<rangle> \<sim>\<^sub>\<R> \<langle>c,d\<rangle> \<longrightarrow>
                   int_mult_raw(\<langle>a,b\<rangle>,\<langle>c',d'\<rangle>) \<sim>\<^sub>\<R> int_mult_raw(\<langle>a,b\<rangle>,\<langle>c,d\<rangle>)" @with
      @have "(a*\<^sub>\<nat>c' +\<^sub>\<nat> b*\<^sub>\<nat>d') +\<^sub>\<nat> (a*\<^sub>\<nat>d +\<^sub>\<nat> b*\<^sub>\<nat>c) = (c'+\<^sub>\<nat>d) *\<^sub>\<nat> a +\<^sub>\<nat> (d'+\<^sub>\<nat>c) *\<^sub>\<nat> b"
      @have "(a*\<^sub>\<nat>d' +\<^sub>\<nat> b*\<^sub>\<nat>c') +\<^sub>\<nat> (a*\<^sub>\<nat>c +\<^sub>\<nat> b*\<^sub>\<nat>d) = (d'+\<^sub>\<nat>c) *\<^sub>\<nat> a +\<^sub>\<nat> (c'+\<^sub>\<nat>d) *\<^sub>\<nat> b"
    @end
  @end  
  @have "compat_meta_bin(\<R>, int_mult_raw)"
@qed
setup {* del_prfstep_thm @{thm int_evals(4)} *}

lemma int_mult_comm [forward]: "is_times_comm(\<int>)" by auto2
lemma int_mult_assoc [forward]: "is_times_assoc(\<int>)" by auto2
lemma int_distrib_l [forward]: "is_left_distrib(\<int>)" by auto2

section \<open>0 and 1\<close>

lemma int_is_add_id [forward]: "is_add_id(\<int>)" by auto2
lemma int_is_mult_id [forward]: "is_mult_id(\<int>)" by auto2
lemma int_zero_neq_one [resolve]: "\<zero>\<^sub>\<int> \<noteq> \<one>\<^sub>\<int>" by auto2

section \<open>Negation and subtraction on integers\<close>
  
definition int_neg_raw :: "i \<Rightarrow> i" where [rewrite]:
  "int_neg_raw(p) = \<langle>snd(p), fst(p)\<rangle>"

definition int_neg :: "i \<Rightarrow> i" where [rewrite]:
  "int_neg(x) = Int(int_neg_raw(rep(\<R>,x)))"

lemma int_neg_typing [typing]: "x \<in>. \<int> \<Longrightarrow> int_neg(x) \<in>. \<int>" by auto2
lemma int_has_add_inverse [forward]: "has_add_inverse(\<int>)"
@proof @have "\<forall>x\<in>.\<int>. x +\<^sub>\<int> int_neg(x) = \<zero>\<^sub>\<int>" @qed
  
lemma int_is_comm_ring [forward]: "is_comm_ring(\<int>)" by auto2

section \<open>Nonnegative integers\<close>

lemma nonneg_int_eval [rewrite]:
  "x \<in>. \<R> \<Longrightarrow> nonneg_int(Int(x)) \<longleftrightarrow> nonneg_int_raw(x)"
@proof
  @have (@rule) "\<forall>a b c d. \<langle>a,b\<rangle> \<sim>\<^sub>\<R> \<langle>c,d\<rangle> \<longrightarrow> a \<ge>\<^sub>\<nat> b \<longrightarrow> c \<ge>\<^sub>\<nat> d" @with
    @contradiction @have "a +\<^sub>\<nat> d >\<^sub>\<nat> b +\<^sub>\<nat> c"
  @end
@qed
setup {* del_prfstep_thm @{thm nonneg_int_def} *}

lemma int_neg_eval [rewrite]: "x \<in>. \<R> \<Longrightarrow> -\<^sub>\<int> Int(x) = Int(int_neg_raw(x))"
@proof @have "Int(x) +\<^sub>\<int> Int(int_neg_raw(x)) = \<zero>\<^sub>\<int>" @qed

lemma nonneg_int_raw_mult [backward2]:
  "\<langle>a,b\<rangle> \<in>. \<R> \<Longrightarrow> \<langle>c,d\<rangle> \<in>. \<R> \<Longrightarrow> nonneg_int_raw(\<langle>a,b\<rangle>) \<Longrightarrow> nonneg_int_raw(\<langle>c,d\<rangle>) \<Longrightarrow>
   nonneg_int_raw(int_mult_raw(\<langle>a,b\<rangle>, \<langle>c,d\<rangle>))"
@proof
  @obtain "p\<in>nat" where "a = b +\<^sub>\<nat> p"
  @obtain "q\<in>nat" where "c = d +\<^sub>\<nat> q"
  @have "(b+\<^sub>\<nat>p)*\<^sub>\<nat>d +\<^sub>\<nat> b*\<^sub>\<nat>(d+\<^sub>\<nat>q) +\<^sub>\<nat> p*\<^sub>\<nat>q = (b+\<^sub>\<nat>p)*\<^sub>\<nat>(d+\<^sub>\<nat>q) +\<^sub>\<nat> b*\<^sub>\<nat>d"
@qed

lemma int_nonneg_compat [resolve]: "nonneg_compat(\<int>, nonneg_ints)" by auto2
setup {* fold del_prfstep_thm [@{thm nonneg_int_eval}, @{thm nonneg_int_raw_mult},
  @{thm nonneg_int_raw_def}, @{thm nonneg_ints_def}] *}

lemma int_is_ord_ring [forward]: "is_ord_ring(\<int>)"
@proof @have "nonneg_compat(\<int>, nonneg_ints)" @qed
setup {* del_prfstep_thm @{thm int_is_ord_ring_prep} *}

section \<open>Integers as integral domain\<close>

lemma int_is_domain_raw [forward]:
  "x1 \<in>. \<nat> \<Longrightarrow> y1 \<in>. \<nat> \<Longrightarrow> x2 \<in>. \<nat> \<Longrightarrow> y2 \<in>. \<nat> \<Longrightarrow>
   x1 *\<^sub>\<nat> x2 +\<^sub>\<nat> y1 *\<^sub>\<nat> y2 = x1 *\<^sub>\<nat> y2 +\<^sub>\<nat> y1 *\<^sub>\<nat> x2 \<Longrightarrow> x1 = y1 \<or> x2 = y2"
@proof
  @case "x1 <\<^sub>\<nat> y1" @with
    @obtain "p\<in>nat" where "p \<noteq> 0" "y1 = x1 +\<^sub>\<nat> p"
    @have "x1 *\<^sub>\<nat> x2 +\<^sub>\<nat> (x1 +\<^sub>\<nat> p) *\<^sub>\<nat> y2 = (x1 *\<^sub>\<nat> x2 +\<^sub>\<nat> x1 *\<^sub>\<nat> y2) +\<^sub>\<nat> p *\<^sub>\<nat> y2"
    @have "x1 *\<^sub>\<nat> y2 +\<^sub>\<nat> (x1 +\<^sub>\<nat> p) *\<^sub>\<nat> x2 = (x1 *\<^sub>\<nat> x2 +\<^sub>\<nat> x1 *\<^sub>\<nat> y2) +\<^sub>\<nat> p *\<^sub>\<nat> x2" @end
  @case "x1 >\<^sub>\<nat> y1" @with
    @obtain "p\<in>nat" where "p \<noteq> 0" "x1 = y1 +\<^sub>\<nat> p"
    @have "(y1 +\<^sub>\<nat> p) *\<^sub>\<nat> x2 +\<^sub>\<nat> y1 *\<^sub>\<nat> y2 = (y1 *\<^sub>\<nat> x2 +\<^sub>\<nat> y1 *\<^sub>\<nat> y2) +\<^sub>\<nat> p *\<^sub>\<nat> x2"
    @have "(y1 +\<^sub>\<nat> p) *\<^sub>\<nat> y2 +\<^sub>\<nat> y1 *\<^sub>\<nat> x2 = (y1 *\<^sub>\<nat> x2 +\<^sub>\<nat> y1 *\<^sub>\<nat> y2) +\<^sub>\<nat> p *\<^sub>\<nat> y2" @end
@qed

lemma int_is_domain [forward]: "integral_domain(\<int>)" by auto2

section \<open>Integer as a difference of two natural numbers\<close>

lemma int_of_nat [rewrite]: "n \<in> nat \<Longrightarrow> of_nat(\<int>,n) = Int(\<langle>n,0\<rangle>)"
@proof @var_induct "n \<in> nat" @qed

lemma int_diff_eval [rewrite]:
  "\<langle>a,b\<rangle> \<in>. \<R> \<Longrightarrow> \<langle>c,d\<rangle> \<in>. \<R> \<Longrightarrow> Int(\<langle>a,b\<rangle>) -\<^sub>\<int> Int(\<langle>c,d\<rangle>) = Int(\<langle>a+\<^sub>\<nat>d,b+\<^sub>\<nat>c\<rangle>)"
@proof @have "Int(\<langle>a,b\<rangle>) -\<^sub>\<int> Int(\<langle>c,d\<rangle>) = Int(\<langle>a,b\<rangle>) +\<^sub>\<int> (-\<^sub>\<int> Int(\<langle>c,d\<rangle>))" @qed

lemma int_is_diff [backward]:
  "n \<in> int \<Longrightarrow> \<exists>a\<in>.\<nat>. \<exists>b\<in>.\<nat>. n = of_nat(\<int>,a) -\<^sub>\<int> of_nat(\<int>,b)"
@proof
  @let "p = rep(\<R>,n)"
  @have "n = of_nat(\<int>,fst(p)) -\<^sub>\<int> of_nat(\<int>,snd(p))"
@qed

section \<open>Definition of int\_act\<close>

definition int_act_raw :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "int_act_raw(R,p,x) = nat_act(R,fst(p),x) -\<^sub>R nat_act(R,snd(p),x)"

lemma int_act_raw_eval [rewrite]:
  "int_act_raw(R,\<langle>a,b\<rangle>,x) = nat_act(R,a,x) -\<^sub>R nat_act(R,b,x)" by auto2
setup {* del_prfstep_thm @{thm int_act_raw_def} *}

lemma comm_ring_switch_sides4 [resolve]:
  "is_abgroup(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> c \<in>. R \<Longrightarrow> d \<in>. R \<Longrightarrow>
   a +\<^sub>R d = b +\<^sub>R c \<Longrightarrow> a -\<^sub>R b = c -\<^sub>R d"
@proof @have "a -\<^sub>R b +\<^sub>R (b +\<^sub>R d) = c -\<^sub>R d +\<^sub>R (b +\<^sub>R d)" @qed

definition int_act :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "int_act(R,z,x) = int_act_raw(R,rep(\<R>,z),x)"
setup {* register_wellform_data ("int_act(R,z,x)", ["z \<in>. \<int>"]) *}
  
lemma int_act_eval [rewrite]:
  "is_abgroup(R) \<Longrightarrow> p \<in>. \<R> \<Longrightarrow> x \<in>. R \<Longrightarrow> int_act(R,Int(p),x) = int_act_raw(R,p,x)"
@proof
  @have (@rule) "\<forall>a b c d. \<langle>a,b\<rangle> \<sim>\<^sub>\<R> \<langle>c,d\<rangle> \<longrightarrow> int_act_raw(R,\<langle>a,b\<rangle>,x) = int_act_raw(R,\<langle>c,d\<rangle>,x)" @with
    @have "nat_act(R,a,x) +\<^sub>R nat_act(R,d,x) = nat_act(R,b,x) +\<^sub>R nat_act(R,c,x)"
  @end
@qed
setup {* del_prfstep_thm @{thm int_act_def} *}

lemma int_act_type [typing]:
  "is_abgroup(R) \<Longrightarrow> a \<in>. \<int> \<Longrightarrow> x \<in>. R \<Longrightarrow> int_act(R,a,x) \<in>. R" by auto2

lemma int_act_eval_diff [rewrite]:
  "is_abgroup(R) \<Longrightarrow> a \<in> nat \<Longrightarrow> b \<in> nat \<Longrightarrow> x \<in>. R \<Longrightarrow>
   int_act(R,of_nat(\<int>,a) -\<^sub>\<int> of_nat(\<int>,b),x) = nat_act(R,a,x) -\<^sub>R nat_act(R,b,x)" by auto2

lemma int_act_of_nat [rewrite]:
  "is_abgroup(R) \<Longrightarrow> n \<in> nat \<Longrightarrow> x \<in>. R \<Longrightarrow> int_act(R,of_nat(\<int>,n),x) = nat_act(R,n,x)" by auto2
  
lemma int_act_zero [rewrite]:
  "is_abgroup(R) \<Longrightarrow> r \<in>. R \<Longrightarrow> int_act(R,\<zero>\<^sub>\<int>,r) = \<zero>\<^sub>R" by auto2

lemma int_act_one [rewrite]:
  "is_abgroup(R) \<Longrightarrow> r \<in>. R \<Longrightarrow> int_act(R,\<one>\<^sub>\<int>,r) = r" by auto2

lemma int_act_zero_right [rewrite]:
  "is_abgroup(R) \<Longrightarrow> n \<in>. \<int> \<Longrightarrow> int_act(R,n,\<zero>\<^sub>R) = \<zero>\<^sub>R" by auto2

setup {* del_prfstep_thm @{thm int_of_nat} *}
setup {* fold del_prfstep_thm [@{thm int_act_raw_eval}, @{thm int_act_eval}] *}
setup {* fold del_prfstep_thm [@{thm int_def}, @{thm int_rel_spaceI}, @{thm int_rel_spaceD}] *}
setup {* fold del_prfstep_thm @{thms int_evals(1-2)} *}
setup {* fold del_prfstep_thm [@{thm int_choose_rep}, @{thm int_neg_eval}, @{thm int_add_eval},
  @{thm int_diff_eval}, @{thm int_mult_eval}] *}
no_notation int_rel ("\<R>")
hide_const Int

section \<open>Further properties of int\_act\<close>

lemma int_act_add [rewrite_bidir]:
  "is_abgroup(R) \<Longrightarrow> x \<in>. \<int> \<Longrightarrow> y \<in>. \<int> \<Longrightarrow> r \<in>. R \<Longrightarrow> int_act(R,x +\<^sub>\<int> y,r) = int_act(R,x,r) +\<^sub>R int_act(R,y,r)"
@proof
  @obtain "a\<in>.\<nat>" "b\<in>.\<nat>" where "x = of_nat(\<int>,a) -\<^sub>\<int> of_nat(\<int>,b)"
  @obtain "c\<in>.\<nat>" "d\<in>.\<nat>" where "y = of_nat(\<int>,c) -\<^sub>\<int> of_nat(\<int>,d)"
  @let "za = of_nat(\<int>,a)" "zb = of_nat(\<int>,b)" "zc = of_nat(\<int>,c)" "zd = of_nat(\<int>,d)"
  @let "ra = nat_act(R,a,r)" "rb = nat_act(R,b,r)" "rc = nat_act(R,c,r)" "rd = nat_act(R,d,r)"
  @have "(za -\<^sub>\<int> zb) +\<^sub>\<int> (zc -\<^sub>\<int> zd) = (za +\<^sub>\<int> zc) -\<^sub>\<int> (zb +\<^sub>\<int> zd)"
  @have "(ra -\<^sub>R rb) +\<^sub>R (rc -\<^sub>R rd) = (ra +\<^sub>R rc) -\<^sub>R (rb +\<^sub>R rd)"
@qed

lemma int_act_uminus [rewrite_bidir]:
  "is_abgroup(R) \<Longrightarrow> x \<in>. \<int> \<Longrightarrow> r \<in>. R \<Longrightarrow> int_act(R,-\<^sub>\<int> x, r) = -\<^sub>R int_act(R,x,r)"
@proof @have "int_act(R,-\<^sub>\<int> x,r) +\<^sub>R int_act(R,x,r) = \<zero>\<^sub>R" @qed

lemma int_act_minus [rewrite_bidir]:
  "is_abgroup(R) \<Longrightarrow> x \<in>. \<int> \<Longrightarrow> y \<in>. \<int> \<Longrightarrow> r \<in>. R \<Longrightarrow> int_act(R,x -\<^sub>\<int> y,r) = int_act(R,x,r) -\<^sub>R int_act(R,y,r)"
@proof @have "int_act(R,x,r) -\<^sub>R int_act(R,y,r) = int_act(R,x,r) +\<^sub>R (-\<^sub>R int_act(R,y,r))" @qed

lemma int_act_add_right [rewrite_bidir]:
  "is_abgroup(R) \<Longrightarrow> x \<in>. \<int> \<Longrightarrow> r \<in>. R \<Longrightarrow> s \<in>. R \<Longrightarrow> int_act(R,x,r +\<^sub>R s) = int_act(R,x,r) +\<^sub>R int_act(R,x,s)"
@proof
  @obtain "a\<in>.\<nat>" "b\<in>.\<nat>" where "x = of_nat(\<int>,a) -\<^sub>\<int> of_nat(\<int>,b)"
  @have "(nat_act(R,a,r) +\<^sub>R nat_act(R,a,s)) -\<^sub>R (nat_act(R,b,r) +\<^sub>R nat_act(R,b,s)) =
         (nat_act(R,a,r) -\<^sub>R nat_act(R,b,r)) +\<^sub>R (nat_act(R,a,s) -\<^sub>R nat_act(R,b,s))"
@qed

lemma int_act_uminus_right [rewrite_bidir]:
  "is_abgroup(R) \<Longrightarrow> x \<in>. \<int> \<Longrightarrow> r \<in>. R \<Longrightarrow> int_act(R,x,-\<^sub>R r) = -\<^sub>R int_act(R,x,r)"
@proof @have "int_act(R,x,-\<^sub>R r) +\<^sub>R int_act(R,x,r) = \<zero>\<^sub>R" @qed

lemma int_act_sub_right [rewrite_bidir]:
  "is_abgroup(R) \<Longrightarrow> x \<in>. \<int> \<Longrightarrow> r \<in>. R \<Longrightarrow> s \<in>. R \<Longrightarrow> int_act(R,x,r -\<^sub>R s) = int_act(R,x,r) -\<^sub>R int_act(R,x,s)"
@proof @have "int_act(R,x,r) -\<^sub>R int_act(R,x,s) = int_act(R,x,r) +\<^sub>R (-\<^sub>R int_act(R,x,s))" @qed

lemma int_act_mult [rewrite_bidir]:
  "is_abgroup(R) \<Longrightarrow> x \<in>. \<int> \<Longrightarrow> y \<in>. \<int> \<Longrightarrow> r \<in>. R \<Longrightarrow> int_act(R,x *\<^sub>\<int> y, r) = int_act(R,x,int_act(R,y,r))"
@proof
  @obtain "a\<in>.\<nat>" "b\<in>.\<nat>" where "x = of_nat(\<int>,a) -\<^sub>\<int> of_nat(\<int>,b)"
  @obtain "c\<in>.\<nat>" "d\<in>.\<nat>" where "y = of_nat(\<int>,c) -\<^sub>\<int> of_nat(\<int>,d)"
  @let "za = of_nat(\<int>,a)" "zb = of_nat(\<int>,b)" "zc = of_nat(\<int>,c)" "zd = of_nat(\<int>,d)"
  @have "(za -\<^sub>\<int> zb) *\<^sub>\<int> (zc -\<^sub>\<int> zd) = (za *\<^sub>\<int> zc +\<^sub>\<int> zb *\<^sub>\<int> zd) -\<^sub>\<int> (za *\<^sub>\<int> zd +\<^sub>\<int> zb *\<^sub>\<int> zc)"
@qed

section \<open>Definition of of\_int\<close>

definition of_int :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite_bidir]:
  "of_int(R,z) = int_act(R,z,\<one>\<^sub>R)"
setup {* register_wellform_data ("of_int(R,z)", ["z \<in>. \<int>"]) *}

lemma of_int_type [typing]:
  "is_comm_ring(R) \<Longrightarrow> a \<in>. \<int> \<Longrightarrow> of_int(R,a) \<in>. R" by auto2

lemma of_int_of_nat [rewrite]:
  "is_comm_ring(R) \<Longrightarrow> n \<in> nat \<Longrightarrow> of_int(R,of_nat(\<int>,n)) = of_nat(R,n)" by auto2

lemma of_int_add [rewrite_bidir]:
  "is_comm_ring(R) \<Longrightarrow> x \<in>. \<int> \<Longrightarrow> y \<in>. \<int> \<Longrightarrow> of_int(R,x) +\<^sub>R of_int(R,y) = of_int(R,x +\<^sub>\<int> y)" by auto2

lemma of_int_uminus [rewrite_bidir]:
  "is_comm_ring(R) \<Longrightarrow> x \<in>. \<int> \<Longrightarrow> -\<^sub>R of_int(R,x) = of_int(R,-\<^sub>\<int> x)" by auto2

lemma of_int_sub [rewrite_bidir]:
  "is_comm_ring(R) \<Longrightarrow> x \<in>. \<int> \<Longrightarrow> y \<in>. \<int> \<Longrightarrow> of_int(R,x) -\<^sub>R of_int(R,y) = of_int(R,x -\<^sub>\<int> y)" by auto2
      
setup {* del_prfstep_thm_str "" @{thm of_int_def} *}

lemma of_int_mult [rewrite_bidir]:
  "is_comm_ring(R) \<Longrightarrow> x \<in>. \<int> \<Longrightarrow> y \<in>. \<int> \<Longrightarrow> of_int(R,x) *\<^sub>R of_int(R,y) = of_int(R,x *\<^sub>\<int> y)"
@proof
  @obtain "a\<in>.\<nat>" "b\<in>.\<nat>" where "x = of_nat(\<int>,a) -\<^sub>\<int> of_nat(\<int>,b)"
  @obtain "c\<in>.\<nat>" "d\<in>.\<nat>" where "y = of_nat(\<int>,c) -\<^sub>\<int> of_nat(\<int>,d)"
  @let "za = of_nat(\<int>,a)" "zb = of_nat(\<int>,b)" "zc = of_nat(\<int>,c)" "zd = of_nat(\<int>,d)"
  @let "ra = of_nat(R,a)" "rb = of_nat(R,b)" "rc = of_nat(R,c)" "rd = of_nat(R,d)"
  @have "(za -\<^sub>\<int> zb) *\<^sub>\<int> (zc -\<^sub>\<int> zd) = (za *\<^sub>\<int> zc +\<^sub>\<int> zb *\<^sub>\<int> zd) -\<^sub>\<int> (za *\<^sub>\<int> zd +\<^sub>\<int> zb *\<^sub>\<int> zc)"
  @have "(ra -\<^sub>R rb) *\<^sub>R (rc -\<^sub>R rd) = (ra *\<^sub>R rc +\<^sub>R rb *\<^sub>R rd) -\<^sub>R (ra *\<^sub>R rd +\<^sub>R rb *\<^sub>R rc)"
@qed

lemma ord_ring_switch_sides4 [resolve]:
  "is_ord_ring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> c \<in>. R \<Longrightarrow> d \<in>. R \<Longrightarrow>
   a -\<^sub>R b \<le>\<^sub>R c -\<^sub>R d \<Longrightarrow> a +\<^sub>R d \<le>\<^sub>R b +\<^sub>R c" by auto2

lemma ord_ring_switch_sides4' [resolve]:
  "is_ord_ring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> c \<in>. R \<Longrightarrow> d \<in>. R \<Longrightarrow>
   a +\<^sub>R d \<le>\<^sub>R b +\<^sub>R c \<Longrightarrow> a -\<^sub>R b \<le>\<^sub>R c -\<^sub>R d" by auto2

lemma ord_ring_switch_sides4_less [resolve]:
  "is_ord_ring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> c \<in>. R \<Longrightarrow> d \<in>. R \<Longrightarrow>
   a -\<^sub>R b <\<^sub>R c -\<^sub>R d \<Longrightarrow> a +\<^sub>R d <\<^sub>R b +\<^sub>R c" by auto2

lemma ord_ring_switch_sides4_less' [resolve]:
  "is_ord_ring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> c \<in>. R \<Longrightarrow> d \<in>. R \<Longrightarrow>
   a +\<^sub>R d <\<^sub>R b +\<^sub>R c \<Longrightarrow> a -\<^sub>R b <\<^sub>R c -\<^sub>R d" by auto2

lemma ord_ring_of_int_le [backward]:
  "is_ord_ring(R) \<Longrightarrow> x \<le>\<^sub>\<int> y \<Longrightarrow> of_int(R,x) \<le>\<^sub>R of_int(R,y)"
@proof
  @obtain "a\<in>.\<nat>" "b\<in>.\<nat>" where "x = of_nat(\<int>,a) -\<^sub>\<int> of_nat(\<int>,b)"
  @obtain "c\<in>.\<nat>" "d\<in>.\<nat>" where "y = of_nat(\<int>,c) -\<^sub>\<int> of_nat(\<int>,d)"
  @have "of_nat(\<int>,a) +\<^sub>\<int> of_nat(\<int>,d) \<le>\<^sub>\<int> of_nat(\<int>,b) +\<^sub>\<int> of_nat(\<int>,c)"
  @have "of_nat(R,a) +\<^sub>R of_nat(R,d) \<le>\<^sub>R of_nat(R,b) +\<^sub>R of_nat(R,c)"
@qed

lemma ord_ring_of_int_less [backward]:
  "is_ord_ring(R) \<Longrightarrow> x <\<^sub>\<int> y \<Longrightarrow> of_int(R,x) <\<^sub>R of_int(R,y)"
@proof
  @obtain "a\<in>.\<nat>" "b\<in>.\<nat>" where "x = of_nat(\<int>,a) -\<^sub>\<int> of_nat(\<int>,b)"
  @obtain "c\<in>.\<nat>" "d\<in>.\<nat>" where "y = of_nat(\<int>,c) -\<^sub>\<int> of_nat(\<int>,d)"
  @have "of_nat(\<int>,a) +\<^sub>\<int> of_nat(\<int>,d) <\<^sub>\<int> of_nat(\<int>,b) +\<^sub>\<int> of_nat(\<int>,c)"
  @have "of_nat(R,a) +\<^sub>R of_nat(R,d) <\<^sub>R of_nat(R,b) +\<^sub>R of_nat(R,c)"
@qed

lemma ord_ring_of_int_le_back [forward]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. \<int> \<Longrightarrow> y \<in>. \<int> \<Longrightarrow> of_int(R,x) \<le>\<^sub>R of_int(R,y) \<Longrightarrow> x \<le>\<^sub>\<int> y"
@proof @case "of_int(R,y) <\<^sub>R of_int(R,x)" @qed

lemma ord_ring_of_int_eq [forward]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. \<int> \<Longrightarrow> y \<in>. \<int> \<Longrightarrow> of_int(R,x) = of_int(R,y) \<Longrightarrow> x = y"
@proof
  @case "x <\<^sub>\<int> y" @with @have "of_int(R,x) <\<^sub>R of_int(R,y)" @end
  @case "x >\<^sub>\<int> y" @with @have "of_int(R,x) >\<^sub>R of_int(R,y)" @end
@qed

lemma ord_ring_of_int_positive:
  "is_ord_ring(R) \<Longrightarrow> b >\<^sub>\<int> 0\<^sub>\<int> \<Longrightarrow> of_int(R,b) >\<^sub>R 0\<^sub>R"
@proof @have "of_int(R,b) >\<^sub>R of_int(R,0\<^sub>\<int>)" @qed
setup {* add_forward_prfstep_cond @{thm ord_ring_of_int_positive} [with_term "of_int(?R,?b)"] *}

lemma int_gt_to_ge [backward]:
  "x >\<^sub>\<int> y \<Longrightarrow> x \<ge>\<^sub>\<int> y +\<^sub>\<int> 1\<^sub>\<int>"
@proof
  @obtain "a\<in>.\<nat>" "b\<in>.\<nat>" where "x = of_nat(\<int>,a) -\<^sub>\<int> of_nat(\<int>,b)"
  @obtain "c\<in>.\<nat>" "d\<in>.\<nat>" where "y = of_nat(\<int>,c) -\<^sub>\<int> of_nat(\<int>,d)"
  @have "of_nat(\<int>,a) +\<^sub>\<int> of_nat(\<int>,d) >\<^sub>\<int> of_nat(\<int>,b) +\<^sub>\<int> of_nat(\<int>,c)"
  @have "of_nat(\<int>,a) +\<^sub>\<int> of_nat(\<int>,d) \<ge>\<^sub>\<int> of_nat(\<int>,b) +\<^sub>\<int> of_nat(\<int>,c) +\<^sub>\<int> 1\<^sub>\<int>"
  @have "of_nat(\<int>,a) -\<^sub>\<int> of_nat(\<int>,b) \<ge>\<^sub>\<int> of_nat(\<int>,c) -\<^sub>\<int> of_nat(\<int>,d) +\<^sub>\<int> 1\<^sub>\<int>"
@qed
  
lemma int_gt_to_ge_one [resolve]:
  "x >\<^sub>\<int> 0\<^sub>\<int> \<Longrightarrow> x \<ge>\<^sub>\<int> 1\<^sub>\<int>"
@proof @have "1\<^sub>\<int> = 0\<^sub>\<int> +\<^sub>\<int> 1\<^sub>\<int>" @qed

end
