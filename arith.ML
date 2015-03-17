(* Arithmetic proof steps. *)

val _ = Theory.setup add_arith_ac_data

val _ = Theory.setup (
      fold add_rewrite_rule [
        ([WithTerm @{term_pat "even (?a::nat)"}], @{thm even_iff_2_dvd}),

        ([WithTerm @{term_pat "(?b::nat) dvd ?a"}], @{thm dvd_def}),

        ([WithTerm @{term_pat "~ (?x::nat) < ?y"}],
         @{thm Orderings.linorder_not_less}),

        ([WithTerm @{term_pat "(?a::nat) ^ 0"}], @{thm power_0}),

        ([WithTerm @{term_pat "(1::nat) ^ ?n"},
          Filter (neqt_filter "n" @{term "0::nat"})], @{thm power_one}),

        ([WithTerm @{term_pat "(?a::nat) ^ 1"},
          Filter (neqt_filter "a" @{term "1::nat"})], @{thm power_one_right}),
        
        ([WithTerm @{term_pat "(?p::nat) ^ ?m"},
          Filter (neqt_filter "p" @{term "1::nat"}),
          Filter (neqt_filter "m" @{term "0::nat"}),
          Filter (neqt_filter "m" @{term "1::nat"})], @{thm power_eq_if}),

        ([WithTerm @{term_pat "((?p::nat) ^ ?i) * ?p"},
          Filter (size1_filter "i")], @{thm power_add_one})])

(* m ~= n, where m, n are constant natural numbers, give raise to
   contradiction.
 *)
val _ = Theory.setup (
      add_prfstep_thm_fn (
        "compare_consts",
        [WithFact @{term_pat "(?NUMC1::nat) = ?NUMC2"},
         Filter (fn _ => fn (_, inst) =>
                    HOLogic.dest_number (lookup_instn inst ("NUMC", 1)) <>
                    HOLogic.dest_number (lookup_instn inst ("NUMC", 2)))],
        (fn ctxt => fn (_, ths) =>
            let
              val goal = Logic.mk_implies (
                    Thm.prop_of (the_single ths), @{prop "False"})
            in
              ths MRS (Goal.prove ctxt [] [] goal
                                  (K (Arith_Data.arith_tac ctxt 1)))
            end)))

(* Using n - 1 = 0. *)
val _ = Theory.setup (
      add_gen_prfstep (
        "n_minus_1_eq_0",
        [WithFact @{term_pat "(?n::nat) ~= 0"},
         WithFact @{term_pat "(?n::nat) - 1 = 0"},
         GetFact (@{term_pat "(?n::nat) = 1"}, @{thm n_minus_1_eq_0})]))

(* Contradiction between < and =. *)
val _ = Theory.setup (
      add_gen_prfstep (
        "less_equal_contradiction",
        [WithFact @{term_pat "(?n::nat) < ?n"},
         GetResolve @{thm le_contra}]))

(* <= and >= implies =. *)
val _ = Theory.setup (
      add_gen_prfstep (
        "greater_eq_and_less_eq",
        [WithFact @{term_pat "(?m::nat) >= ?n"},
         WithFact @{term_pat "(?m::nat) <= ?n"},
         GetFact (@{term_pat "(?m::nat) = ?n"}, @{thm ge_and_le}),
         Filter (order_filter "m" "n"),
         Filter (neq_filter "m" "n")]))

(* <= and ~= implies <. *)
val _ = Theory.setup (
      add_gen_prfstep (
        "less_eq_and_not_eq",
        [WithFact @{term_pat "(?m::nat) <= ?n"},
         WithFact @{term_pat "(?m::nat) ~= ?n"},
         GetFact (@{term_pat "(?m::nat) < ?n"}, @{thm le_and_ne}),
         Filter (neq_filter "m" "n")]))

(* Less than 1 means zero. *)
val _ = Theory.setup (
      add_gen_prfstep (
        "less_than_one",
        [WithFact @{term_pat "(?m::nat) < 1"},
         GetFact (@{term_pat "(?m::nat) = 0"}, @{thm lt_one})]))

(* Greater than anything for nat is greater than zero. *)
val _ = Theory.setup (
      add_gen_prfstep (
        "greater_than_zero",
        [WithFact @{term_pat "(?m::nat) > ?C"},
         GetFact (@{term_pat "(?m::nat) > 0"}, @{thm gt_zero}),
         Filter (neqt_filter "C" @{term "0::nat"})]))

(* Deriving inequalities from products. *)
val _ = Theory.setup (
      add_gen_prfstep (
        "product_inequalities",
        [WithFact @{term_pat "(?m::nat) * ?k > 0"},
         GetFact (@{term_pat "(1::nat) <= ?m"}, @{thm prod_ineqs1}),
         GetFact (@{term_pat "(?m::nat) <= ?m * ?k"}, @{thm prod_ineqs2}),
         Filter (ac_atomic_filter @{const_name times} "m"),
         Filter (neqt_filter "m" @{term "1::nat"}),
         Filter (neqt_filter "k" @{term "1::nat"})]))

(* From n = m * n, conclude m = 1. *)
val _ = Theory.setup (
      add_gen_prfstep (
        "mult_concl_one_side",
        [WithFact @{term_pat "(?n::nat) > 0"},
         WithFact @{term_pat "(?n::nat) = ?m * ?n"},
         GetFact (@{term_pat "(?m::nat) = 1"}, @{thm mult_n1n}),
         Filter (neqt_filter "m" @{term "1::nat"})]))

(* To show ?k dvd (?m * ?n), try to show (?k dvd ?m) or (?k dvd ?n). *)
val _ = Theory.setup (
      add_gen_prfstep (
        "prod_dvd_intro",
        [WithGoal @{term_pat "(?k::nat) dvd ?m * ?n"},
         GetGoal (@{term_pat "((?k::nat) dvd ?m) | ((?k::nat) dvd ?n)"},
                  @{thm prod_dvd_intro}),
         Filter (canonical_split_filter @{const_name times} "m" "n")]))

(* n divides 1 implies n = 1. *)
val _ = Theory.setup (
      add_gen_prfstep (
        "n_dvd_one_implies_n_is_one",
        [WithFact @{term_pat "(?n::nat) dvd 1"},
         GetFact (@{term_pat "(?n::nat) = 1"}, @{thm n_dvd_one}),
         Filter (neqt_filter "n" @{term "1::nat"})]))

(* xy = 1 means x = y = 1. *)
val _ = Theory.setup (
      add_gen_prfstep (
        "prod_is_one",
        [WithFact @{term_pat "(?x::nat) * ?y = 1"},
         GetFact (@{term_pat "(?x::nat) = 1"}, @{thm prod_is_one})]))

(* 1 divides anything. *)
val _ = Theory.setup (
      add_gen_prfstep (
        "one_dvd_any",
        [WithGoal @{term_pat "1 dvd (?n::nat)"},
         GetResolve @{thm one_dvd_any}]))

(* m|n and n|p implies m|p. *)
val _ = Theory.setup (
      add_gen_prfstep (
        "dvd_transitive",
        [WithFact @{term_pat "(?m::nat) dvd ?n"},
         WithFact @{term_pat "(?n::nat) dvd ?p"},
         GetFact (@{term_pat "(?m::nat) dvd ?p"}, @{thm dvd_transitive}),
         Filter (neq_filter "m" "n"),
         Filter (neq_filter "n" "p"),
         Filter (neq_filter "m" "p")]))
val _ = Theory.setup (
      add_gen_prfstep (
        "dvd_transitive'",
        [WithFact @{term_pat "(?m::nat) dvd ?n"},
         WithFact @{term_pat "(?n::nat) dvd ?m"},
         GetFact (@{term_pat "(?m::nat) = ?n"}, @{thm dvd_transitive'}),
         Filter (neq_filter "m" "n")]))

(* Some existence claims about dvd. *)
val _ = Theory.setup (
      add_gen_prfstep (
        "n_dvd_n",
        [WithGoal @{term_pat "(?n::nat) dvd ?n"},
         GetResolve @{thm n_dvd_n}]))

val _ = Theory.setup (
      add_prfstep_two_stage (
        "exists_n_dvd_n",
        [WithGoal @{term_pat "EX k. k dvd (?n::nat) & ?A"},
         GetFact (@{term_pat "(?n::nat) dvd ?n"}, @{thm n_dvd_n})],
        @{thm exists_intro}))

val _ = Theory.setup (
      add_prfstep_thm (
        "any_n_dvd_0",
        [WithGoal @{term_pat "(EX k. k dvd (0::nat) & ?A)"}],
        @{thm any_n_dvd_0}))

val _ = Theory.setup (
      add_prfstep_two_stage (
        "one_is_power_zero",
        [WithGoal @{term_pat "EX i. (1::nat) = ?a ^ i"},
         GetFact (@{term_pat "(1::nat) = ?a ^ 0"}, @{thm power_0'})],
        @{thm exists_resolve}))

val _ = Theory.setup (
      add_prfstep_two_stage (
        "dvd_prod",
        [WithFact @{term_pat "! m::nat. m dvd (?a * ?b) --> ?C"},
         GetFact (@{term_pat "(?a::nat) dvd (?a * ?b)"}, @{thm dvd_prod1}),
         Filter (ac_atomic_filter @{const_name times} "a"),
         Filter (neqt_filter "a" @{term "1::nat"}),
         Filter (neqt_filter "b" @{term "1::nat"})],
        @{thm forall_resolve}))

(* Cancelling a multiplicative factor from both sides. *)
val _ = Theory.setup (
      add_gen_prfstep (
        "prod_cancel",
        [WithFact @{term_pat "(?a::nat) > 0"},
         WithFact @{term_pat "(?a::nat) * ?b = ?a * ?c"},
         GetFact (@{term_pat "(?b::nat) = ?c"}, @{thm prod_cancel}),
         Filter (neq_filter "b" "c")]))

(* Invoke definition of gcd. *)
val _ = Theory.setup (
      add_gen_prfstep (
        "gcd_def",
        [WithTerm @{term_pat "gcd (?m::nat) ?n"},
         GetFact (@{term_pat "gcd (?m::nat) ?n dvd ?m"}, @{thm gcd_dvd1_nat})]))

(* Various facts about coprimality. *)
val _ = Theory.setup (
      add_gen_prfstep (
        "coprime_dvd_mult_nat",
        [WithFact @{term_pat "(?k::nat) dvd ?m * ?n"},
         WithGoal @{term_pat "(?k::nat) dvd ?m"},
         GetGoal (@{term_pat "coprime (?k::nat) ?n"},
                  @{thm coprime_dvd_mult_nat})]))

val _ = Theory.setup (
      add_gen_prfstep (
        "power_dvd",
        [WithFact @{term_pat "(?p::nat) ^ ?n dvd ?a"},
         WithFact @{term_pat "(?n::nat) ~= 0"},
         GetFact (@{term_pat "(?p::nat) dvd ?a"}, @{thm power_dvd})]))

val _ = Theory.setup (
      add_gen_prfstep (
        "coprime_dvd",
        [WithFact @{term_pat "coprime (?a::nat) ?b"},
         WithFact @{term_pat "(?p::nat) dvd ?a"},
         GetFact (@{term_pat "(?p::nat) > 1 --> ~ ((?p::nat) dvd ?b)"},
                  @{thm coprime_dvd})]))

val _ = Theory.setup (
      add_gen_prfstep (
        "coprime_exp_nat",
        [WithGoal @{term_pat "coprime ?d ((?a::nat) ^ ?n)"},
         GetGoal (@{term_pat "coprime (?d::nat) ?a"}, @{thm coprime_exp_nat})]))

(* b ^ n = 1 implies b = 1 or n = 0. *)
val _ = Theory.setup (
      add_gen_prfstep (
        "power_eq_one",
        [WithFact @{term_pat "(?b::nat) ^ (?n::nat) = 1"},
         GetFact (@{term_pat "((?b::nat) = 1) | (?n::nat) = 0"},
                  @{thm power_eq_one}),
         Filter (neqt_filter "b" @{term "1::nat"}),
         Filter (neqt_filter "n" @{term "0::nat"})]))
