theory GCD_Impl
  imports SepAuto
begin

(* Turn on auto2's trace. *)
declare [[print_trace]]

(* Property of gcd that justifies the recursive computation. Add as a
   right-to-left rewrite rule. *)
setup {* add_rewrite_rule_back @{thm gcd_red_nat} *}

(* Functional version of gcd. *)
fun gcd_fun :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "gcd_fun a b = (if b = 0 then a else gcd_fun b (a mod b))"

(* The fun package automatically generates induction rule upon showing
   termination. This adds the induction rule for the @fun_induct command. *)
setup {* add_fun_induct_rule (@{term gcd_fun}, @{thm gcd_fun.induct}) *}

lemma gcd_fun_correct:
  "gcd_fun a b = gcd a b"
@proof
  @fun_induct "gcd_fun a b"
  @unfold "gcd_fun a b"
@qed

(* Imperative version of gcd *)
partial_function (heap) gcd_impl :: "nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "gcd_impl a b = (
    if b = 0 then return a
    else do {
      c \<leftarrow> return (a mod b);
      r \<leftarrow> gcd_impl b c;
      return r
    })"

(* The program is sufficiently simple that we can prove the Hoare triple
   directly (without going through the functional program). *)
lemma gcd_impl_correct:
  "<emp> gcd_impl a b <\<lambda>r. \<up>(r = gcd a b)>"
@proof
  @fun_induct "gcd_fun a b"
@qed

(* Turn off trace *)
declare [[print_trace = false]]

end
