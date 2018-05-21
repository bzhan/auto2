theory Lattice
imports OrderRel
begin

(* First, we define join-semilattice. Note this is declared as a property. *)
definition join_semilattice :: "i \<Rightarrow> o" where [rewrite]:
  "join_semilattice(R) \<longleftrightarrow> order(R) \<and>
    (\<forall>x\<in>.R. \<forall>y\<in>.R. \<exists>z. z \<ge>\<^sub>R x \<and> z \<ge>\<^sub>R y \<and> (\<forall>z'. z' \<ge>\<^sub>R x \<longrightarrow> z' \<ge>\<^sub>R y \<longrightarrow> z' \<ge>\<^sub>R z))"

(* Next, we prove two results on how to *use* the join-semilattice property. *)
lemma join_semilatticeD1 [forward]: "join_semilattice(R) \<Longrightarrow> order(R)" by auto2

(* In this case, we add the lemma as a *backward* reasoning rule. This rule is
   only applied when the conclusion is needed. If we add this as a forward
   reasoning rule instead, a join element will be created for every pair of
   elements in R.
 *)
lemma join_semilatticeD2 [backward]:
  "join_semilattice(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow>
   \<exists>z. z \<ge>\<^sub>R x \<and> z \<ge>\<^sub>R y \<and> (\<forall>z'. z' \<ge>\<^sub>R x \<longrightarrow> z' \<ge>\<^sub>R y \<longrightarrow> z' \<ge>\<^sub>R z)" by auto2
setup {* del_prfstep_thm_eqforward @{thm join_semilattice_def} *}
  
(* The *unique* existence of join can be proved automatically. *)
lemma join_semilattice_unique [backward]:
  "join_semilattice(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow>
   \<exists>!z. z \<ge>\<^sub>R x \<and> z \<ge>\<^sub>R y \<and> (\<forall>z'. z' \<ge>\<^sub>R x \<longrightarrow> z' \<ge>\<^sub>R y \<longrightarrow> z' \<ge>\<^sub>R z)" by auto2

(* Define the join function and specify its notation. *)
definition join :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "join(R,x,y) = (THE z. z \<ge>\<^sub>R x \<and> z \<ge>\<^sub>R y \<and> (\<forall>z'. z' \<ge>\<^sub>R x \<longrightarrow> z' \<ge>\<^sub>R y \<longrightarrow> z' \<ge>\<^sub>R z))"
abbreviation join_notation ("(_/ \<squnion>\<^sub>_ _)" [66,66,66] 65) where "x \<squnion>\<^sub>R y \<equiv> join(R,x,y)"
setup {* register_wellform_data ("x \<squnion>\<^sub>R y", ["x \<in>. R", "y \<in>. R"]) *}

(* The main properties of join are proved. The first one is added whenever the
   term join(R,x,y) appears in the proof.
 *)
lemma joinD1:
  "join_semilattice(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x \<squnion>\<^sub>R y \<ge>\<^sub>R x \<and> x \<squnion>\<^sub>R y \<ge>\<^sub>R y" by auto2
setup {* add_forward_prfstep_cond @{thm joinD1} [with_term "join(?R,?x,?y)"] *}

(* The second one is invoked whenever we want to prove something is greater than
   or equal to the join.
 *)
lemma joinD2 [backward]:
  "join_semilattice(R) \<Longrightarrow> z \<ge>\<^sub>R x \<Longrightarrow> z \<ge>\<^sub>R y \<Longrightarrow> z \<ge>\<^sub>R x \<squnion>\<^sub>R y" by auto2

(* Finally, a third property on how to show the join of x and y is equal to something. *)
lemma joinI [backward]:
  "join_semilattice(R) \<Longrightarrow> z \<ge>\<^sub>R x \<Longrightarrow> z \<ge>\<^sub>R y \<Longrightarrow> \<forall>z'. z' \<ge>\<^sub>R x \<longrightarrow> z' \<ge>\<^sub>R y \<longrightarrow> z' \<ge>\<^sub>R z \<Longrightarrow> x \<squnion>\<^sub>R y = z" by auto2
setup {* del_prfstep_thm @{thm join_def} *}

(* A few algebraic rules for join. *)
lemma join_idem [rewrite]:
  "join_semilattice(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> x \<squnion>\<^sub>R x = x" by auto2

lemma join_comm [rewrite]:
  "join_semilattice(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x \<squnion>\<^sub>R y = y \<squnion>\<^sub>R x" by auto2
    
lemma join_assoc [rewrite]:
  "join_semilattice(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow> (x \<squnion>\<^sub>R y) \<squnion>\<^sub>R z = x \<squnion>\<^sub>R (y \<squnion>\<^sub>R z)" by auto2

(* Meet is defined in a completely analogous manner. *)
definition meet_semilattice :: "i \<Rightarrow> o" where [rewrite]:
  "meet_semilattice(R) \<longleftrightarrow> order(R) \<and>
    (\<forall>x\<in>.R. \<forall>y\<in>.R. \<exists>z. z \<le>\<^sub>R x \<and> z \<le>\<^sub>R y \<and> (\<forall>z'. z' \<le>\<^sub>R x \<longrightarrow> z' \<le>\<^sub>R y \<longrightarrow> z' \<le>\<^sub>R z))"
  
lemma meet_semilatticeD1 [forward]: "meet_semilattice(R) \<Longrightarrow> order(R)" by auto2
    
lemma meet_semilatticeD2 [backward]:
  "meet_semilattice(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow>
   \<exists>z. z \<le>\<^sub>R x \<and> z \<le>\<^sub>R y \<and> (\<forall>z'. z' \<le>\<^sub>R x \<longrightarrow> z' \<le>\<^sub>R y \<longrightarrow> z' \<le>\<^sub>R z)" by auto2
setup {* del_prfstep_thm_eqforward @{thm meet_semilattice_def} *}
  
lemma meet_semilattice_unique [backward]:
  "meet_semilattice(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow>
   \<exists>!z. z \<le>\<^sub>R x \<and> z \<le>\<^sub>R y \<and> (\<forall>z'. z' \<le>\<^sub>R x \<longrightarrow> z' \<le>\<^sub>R y \<longrightarrow> z' \<le>\<^sub>R z)" by auto2

definition meet :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "meet(R,x,y) = (THE z. z \<le>\<^sub>R x \<and> z \<le>\<^sub>R y \<and> (\<forall>z'. z' \<le>\<^sub>R x \<longrightarrow> z' \<le>\<^sub>R y \<longrightarrow> z' \<le>\<^sub>R z))"
abbreviation meet_notation ("(_/ \<sqinter>\<^sub>_ _)" [66,66,66] 65) where "x \<sqinter>\<^sub>R y \<equiv> meet(R,x,y)"
setup {* register_wellform_data ("meet(R,x,y)", ["x \<in>. R", "y \<in>. R"]) *}

lemma meetD1:
  "meet_semilattice(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x \<sqinter>\<^sub>R y \<le>\<^sub>R x \<and> x \<sqinter>\<^sub>R y \<le>\<^sub>R y" by auto2
setup {* add_forward_prfstep_cond @{thm meetD1} [with_term "meet(?R,?x,?y)"] *}
  
lemma meetD2 [backward]:
  "meet_semilattice(R) \<Longrightarrow> z' \<le>\<^sub>R x \<Longrightarrow> z' \<le>\<^sub>R y \<Longrightarrow> z' \<le>\<^sub>R x \<sqinter>\<^sub>R y" by auto2
    
lemma meetI [backward]:
  "meet_semilattice(R) \<Longrightarrow> z \<le>\<^sub>R x \<Longrightarrow> z \<le>\<^sub>R y \<Longrightarrow> \<forall>z'. z' \<le>\<^sub>R x \<longrightarrow> z' \<le>\<^sub>R y \<longrightarrow> z' \<le>\<^sub>R z \<Longrightarrow> x \<sqinter>\<^sub>R y = z" by auto2
setup {* del_prfstep_thm @{thm meet_def} *}

lemma meet_idem [rewrite]:
  "meet_semilattice(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> x \<sqinter>\<^sub>R x = x" by auto2

(* Adding commutativity and associativity as rewrite rules is NOT a good idea.
   TODO: use special rules for AC functions instead.
 *)
lemma meet_comm [rewrite]:
  "meet_semilattice(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x \<sqinter>\<^sub>R y = y \<sqinter>\<^sub>R x" by auto2
    
lemma meet_assoc [rewrite]:
  "meet_semilattice(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow> (x \<sqinter>\<^sub>R y) \<sqinter>\<^sub>R z = x \<sqinter>\<^sub>R (y \<sqinter>\<^sub>R z)" by auto2

(* An ordering is a lattice if it is both join-semilattice and meet-semilattice. *)
definition lattice :: "i \<Rightarrow> o" where [rewrite]:
  "lattice(R) \<longleftrightarrow> join_semilattice(R) \<and> meet_semilattice(R)"
  
(* The absorption rules. *)
lemma lattice_absorb1 [rewrite]:
  "lattice(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x \<squnion>\<^sub>R (x \<sqinter>\<^sub>R y) = x" by auto2
    
lemma lattice_absorb2 [rewrite]:
  "lattice(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x \<sqinter>\<^sub>R (x \<squnion>\<^sub>R y) = x" by auto2

(* Distributive lattices. *)
definition distributive_lattice :: "i \<Rightarrow> o" where [rewrite]:
  "distributive_lattice(R) \<longleftrightarrow> (lattice(R) \<and> (\<forall>x\<in>.R. \<forall>y\<in>.R. \<forall>z\<in>.R. x \<sqinter>\<^sub>R (y \<squnion>\<^sub>R z) = (x \<sqinter>\<^sub>R y) \<squnion>\<^sub>R (x \<sqinter>\<^sub>R z)))"

lemma distributive_latticeD1 [forward]:
  "distributive_lattice(R) \<Longrightarrow> lattice(R)" by auto2

lemma distributive_latticeD2 [rewrite_back]:
  "distributive_lattice(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow> x \<sqinter>\<^sub>R (y \<squnion>\<^sub>R z) = (x \<sqinter>\<^sub>R y) \<squnion>\<^sub>R (x \<sqinter>\<^sub>R z)" by auto2
setup {* del_prfstep_thm_eqforward @{thm distributive_lattice_def} *}
  
(* An equivalent formulation of distributive lattices. Their equivalence requires
   several equality steps.
 *)
lemma distributive_latticeD2' [rewrite_bidir]:
  "distributive_lattice(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow> x \<squnion>\<^sub>R (y \<sqinter>\<^sub>R z) = (x \<squnion>\<^sub>R y) \<sqinter>\<^sub>R (x \<squnion>\<^sub>R z)"
@proof
  @have "x \<squnion>\<^sub>R (y \<sqinter>\<^sub>R z) = (x \<squnion>\<^sub>R (x \<sqinter>\<^sub>R z)) \<squnion>\<^sub>R (y \<sqinter>\<^sub>R z)"
  @have "x \<squnion>\<^sub>R ((x \<squnion>\<^sub>R y) \<sqinter>\<^sub>R z) = (x \<sqinter>\<^sub>R (x \<squnion>\<^sub>R y)) \<squnion>\<^sub>R ((x \<squnion>\<^sub>R y) \<sqinter>\<^sub>R z)"
@qed

(* Part of distributivity is true for all lattices. This can be shown automatically. *)
lemma lattice_distributive1 [resolve]:
  "lattice(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow> (x \<sqinter>\<^sub>R y) \<squnion>\<^sub>R (x \<sqinter>\<^sub>R z) \<le>\<^sub>R x \<sqinter>\<^sub>R (y \<squnion>\<^sub>R z)" by auto2

lemma lattice_distributive2 [resolve]:
  "lattice(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow> x \<squnion>\<^sub>R (y \<sqinter>\<^sub>R z) \<le>\<^sub>R (x \<squnion>\<^sub>R y) \<sqinter>\<^sub>R (x \<squnion>\<^sub>R z)" by auto2

section {* Examples of lattices *}

(* The subset ordering on the power set of S is a lattice. Join and meet
   is given by union and intersection, respectively.
 *)
lemma subset_order_is_lattice: "lattice(subset_order(Pow(S)))"
@proof
  @let "R = subset_order(Pow(S))"
  @have "join_semilattice(R)" @with
    @have "\<forall>x\<in>.R. \<forall>y\<in>.R. \<exists>z. z \<ge>\<^sub>R x \<and> z \<ge>\<^sub>R y \<and> (\<forall>z'. z' \<ge>\<^sub>R x \<longrightarrow> z' \<ge>\<^sub>R y \<longrightarrow> z' \<ge>\<^sub>R z)" @with
      @have "x \<union> y \<ge>\<^sub>R x"
    @end
  @end
  @have "meet_semilattice(R)" @with
    @have "\<forall>x\<in>.R. \<forall>y\<in>.R. \<exists>z. z \<le>\<^sub>R x \<and> z \<le>\<^sub>R y \<and> (\<forall>z'. z' \<le>\<^sub>R x \<longrightarrow> z' \<le>\<^sub>R y \<longrightarrow> z' \<le>\<^sub>R z)" @with
      @have "x \<inter> y \<le>\<^sub>R x"
    @end
  @end
@qed
setup {* add_forward_prfstep_cond @{thm subset_order_is_lattice} [with_term "subset_order(Pow(?S))"] *}

lemma subset_order_join_eval [rewrite]:
  "R = subset_order(Pow(S)) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x \<squnion>\<^sub>R y = x \<union> y" by auto2
lemma subset_order_meet_eval [rewrite]:
  "R = subset_order(Pow(S)) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> x \<sqinter>\<^sub>R y = x \<inter> y" by auto2

lemma subset_order_is_distrib_lattice:
  "distributive_lattice(subset_order(Pow(S)))" by auto2
setup {* add_forward_prfstep_cond @{thm subset_order_is_distrib_lattice} [with_term "subset_order(Pow(?S))"] *}

(* We define the product ordering on any two orders *)
definition product_ord :: "i \<Rightarrow> i \<Rightarrow> i"  (infixr "\<times>\<^sub>O" 80) where [rewrite]:
  "R \<times>\<^sub>O S = Order(carrier(R)\<times>carrier(S), \<lambda>p q. fst(p) \<le>\<^sub>R fst(q) \<and> snd(p) \<le>\<^sub>S snd(q))"

lemma product_ord_type [typing]: "R \<times>\<^sub>O S \<in> raworder_space(carrier(R)\<times>carrier(S))" by auto2

lemma product_ord_is_order [forward]:
  "order(R) \<Longrightarrow> order(S) \<Longrightarrow> order(R \<times>\<^sub>O S)" by auto2

lemma product_ord_eval [rewrite]:
  "T = R \<times>\<^sub>O S \<Longrightarrow> x \<in>. T \<Longrightarrow> y \<in>. T \<Longrightarrow> x \<le>\<^sub>T y \<longleftrightarrow> (fst(x) \<le>\<^sub>R fst(y) \<and> snd(x) \<le>\<^sub>S snd(y))" by auto2
setup {* del_prfstep_thm @{thm product_ord_def} *}

(* Product of two lattices is a lattice. *)
lemma product_ord_is_lattice [forward]:
  "lattice(R) \<Longrightarrow> lattice(S) \<Longrightarrow> lattice(R \<times>\<^sub>O S)"
@proof
  @let "T = R \<times>\<^sub>O S"
  @have "join_semilattice(T)" @with
    @have "\<forall>x\<in>.T. \<forall>y\<in>.T. \<exists>z. z \<ge>\<^sub>T x \<and> z \<ge>\<^sub>T y \<and> (\<forall>z'. z' \<ge>\<^sub>T x \<longrightarrow> z' \<ge>\<^sub>T y \<longrightarrow> z' \<ge>\<^sub>T z)" @with
      @have "\<langle>fst(x) \<squnion>\<^sub>R fst(y), snd(x) \<squnion>\<^sub>S snd(y)\<rangle> \<ge>\<^sub>T x"
    @end
  @end
  @have "meet_semilattice(T)" @with
    @have "\<forall>x\<in>.T. \<forall>y\<in>.T. \<exists>z. z \<le>\<^sub>T x \<and> z \<le>\<^sub>T y \<and> (\<forall>z'. z' \<le>\<^sub>T x \<longrightarrow> z' \<le>\<^sub>T y \<longrightarrow> z' \<le>\<^sub>T z)" @with
      @have "\<langle>fst(x) \<sqinter>\<^sub>R fst(y), snd(x) \<sqinter>\<^sub>S snd(y)\<rangle> \<le>\<^sub>T x"
    @end
  @end
@qed  

lemma product_ord_join_eval [rewrite]:
  "lattice(R) \<Longrightarrow> lattice(S) \<Longrightarrow> T = R \<times>\<^sub>O S \<Longrightarrow> x \<in>. T \<Longrightarrow> y \<in>. T \<Longrightarrow>
   x \<squnion>\<^sub>T y = \<langle>fst(x) \<squnion>\<^sub>R fst(y), snd(x) \<squnion>\<^sub>S snd(y)\<rangle>"
@proof
  @have "\<langle>fst(x) \<squnion>\<^sub>R fst(y), snd(x) \<squnion>\<^sub>S snd(y)\<rangle> \<ge>\<^sub>T x"
  @have "\<langle>fst(x) \<squnion>\<^sub>R fst(y), snd(x) \<squnion>\<^sub>S snd(y)\<rangle> \<ge>\<^sub>T y"
@qed

lemma product_ord_meet_eval [rewrite]:
  "lattice(R) \<Longrightarrow> lattice(S) \<Longrightarrow> T = R \<times>\<^sub>O S \<Longrightarrow> x \<in>. T \<Longrightarrow> y \<in>. T \<Longrightarrow>
   x \<sqinter>\<^sub>T y = \<langle>fst(x) \<sqinter>\<^sub>R fst(y), snd(x) \<sqinter>\<^sub>S snd(y)\<rangle>"
@proof
  @have "\<langle>fst(x) \<sqinter>\<^sub>R fst(y), snd(x) \<sqinter>\<^sub>S snd(y)\<rangle> \<le>\<^sub>T x"
  @have "\<langle>fst(x) \<sqinter>\<^sub>R fst(y), snd(x) \<sqinter>\<^sub>S snd(y)\<rangle> \<le>\<^sub>T y"
@qed

lemma product_ord_distrib_lattice [forward]:
  "distributive_lattice(R) \<Longrightarrow> distributive_lattice(S) \<Longrightarrow> distributive_lattice(R \<times>\<^sub>O S)" by auto2

section {* Other examples *}

lemma join_eq_str [forward]:
  "join_semilattice(R) \<Longrightarrow> eq_str_order(R,S) \<Longrightarrow> join_semilattice(S)"
@proof
  @have "\<forall>x\<in>.S. \<forall>y\<in>.S. \<exists>z. z \<ge>\<^sub>S x \<and> z \<ge>\<^sub>S y \<and> (\<forall>z'. z' \<ge>\<^sub>S x \<longrightarrow> z' \<ge>\<^sub>S y \<longrightarrow> z' \<ge>\<^sub>S z)" @with
    @have "x \<squnion>\<^sub>R y \<ge>\<^sub>S x"
  @end
@qed

lemma join_ord_isomorphism [forward]:
  "join_semilattice(R) \<Longrightarrow> ord_isomorphic(R,S) \<Longrightarrow> join_semilattice(S)"
@proof
  @obtain "f \<in> R \<cong>\<^sub>O S"
  @have (@rule) "\<forall>y\<in>.S. \<exists>x\<in>.R. f`x = y"
  @let "g = inverse(f)"
  @have "\<forall>x\<in>.S. \<forall>y\<in>.S. \<exists>z. z \<ge>\<^sub>S x \<and> z \<ge>\<^sub>S y \<and> (\<forall>z'. z' \<ge>\<^sub>S x \<longrightarrow> z' \<ge>\<^sub>S y \<longrightarrow> z' \<ge>\<^sub>S z)" @with
    @have "f ` (g ` x \<squnion>\<^sub>R g ` y) \<ge>\<^sub>S x"
  @end
@qed
    
lemma join_eval_ord_isomorphism [rewrite]:
  "join_semilattice(R) \<Longrightarrow> f \<in> R \<cong>\<^sub>O S \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> f ` (x \<squnion>\<^sub>R y) = f ` x \<squnion>\<^sub>S f ` y"
@proof
  @have (@rule) "\<forall>y'\<in>.S. \<exists>x\<in>.R. f`x = y'"
  @let "g = inverse(f)" 
  @have "x \<squnion>\<^sub>R y = g ` (f ` x \<squnion>\<^sub>S f ` y)" @with
    @have "\<forall>z. z \<ge>\<^sub>R x \<longrightarrow> z \<ge>\<^sub>R y \<longrightarrow> z \<ge>\<^sub>R g ` (f ` x \<squnion>\<^sub>S f ` y)"  @with
      @have "f ` z \<ge>\<^sub>S f ` x \<squnion>\<^sub>S f ` y" 
    @end
  @end
@qed

section {* Modular lattices *}

definition modular_lattice :: "i \<Rightarrow> o" where [rewrite]:
  "modular_lattice(R) \<longleftrightarrow> (lattice(R) \<and> (\<forall>x y. x \<le>\<^sub>R y \<longrightarrow> (\<forall>z\<in>.R. x \<squnion>\<^sub>R (y \<sqinter>\<^sub>R z) = y \<sqinter>\<^sub>R (x \<squnion>\<^sub>R z))))"
  
lemma modular_latticeD1 [forward]:
  "modular_lattice(R) \<Longrightarrow> lattice(R)" by auto2

lemma modular_latticeD2 [rewrite_bidir]:
  "modular_lattice(R) \<Longrightarrow> z \<in>. R \<Longrightarrow> x \<le>\<^sub>R y \<Longrightarrow> x \<squnion>\<^sub>R (y \<sqinter>\<^sub>R z) = y \<sqinter>\<^sub>R (x \<squnion>\<^sub>R z)" by auto2
setup {* del_prfstep_thm_eqforward @{thm modular_lattice_def} *}
  
lemma modular_latticeD3:
  "modular_lattice(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> y \<in>. R \<Longrightarrow> z \<in>. R \<Longrightarrow> (x \<sqinter>\<^sub>R y) \<squnion>\<^sub>R (y \<sqinter>\<^sub>R z) = y \<sqinter>\<^sub>R ((x \<sqinter>\<^sub>R y) \<squnion>\<^sub>R z)" by auto2

end
