(* Arithmetic proof steps. *)

fun add_arith_ac_data thy =
    thy |> add_ac_data {fname = @{const_name plus}, assoc_r = false,
                        unit_val = @{term 0}, comm_th = @{thm add_ac(2)},
                        assoc_th = @{thm add_ac(1)},
                        unit_th = @{thm Groups.monoid_add_class.add_0_left}}
        |> add_ac_data {fname = @{const_name times}, assoc_r = false,
                        unit_val = @{term 1}, comm_th = @{thm mult_ac(2)},
                        assoc_th = @{thm mult_ac(1)},
                        unit_th = @{thm Groups.monoid_mult_class.mult_1_left}}
        |> add_ac_data {fname = @{const_name gcd}, assoc_r = false,
                        unit_val = @{term "0::nat"},
                        comm_th = @{thm gcd_nat.commute},
                        assoc_th = @{thm gcd_nat.assoc},
                        unit_th = @{thm GCD.gcd_nat.left_neutral}}

val _ = Theory.setup add_arith_ac_data

fun lookup_numc inst n = dest_numc (lookup_instn inst ("NUMC", n))
fun mk_nat n = HOLogic.mk_number HOLogic.natT n
fun prove_by_arith ctxt ths goal =
    let
      val goal' = Logic.list_implies (
            map Thm.prop_of ths, HOLogic.mk_Trueprop goal)
    in
      ths MRS (Goal.prove ctxt [] [] goal' (K (Arith_Data.arith_tac ctxt 1)))
    end
fun contra_by_arith ctxt ths = prove_by_arith ctxt ths @{term "False"}

val _ = Theory.setup (
      add_prfstep_thm_fn (
        "le_plus_consts",
        [WithGoal @{term_pat "(?NUMC1::nat) + ?a <= ?NUMC2 + ?b"},
         Filter (fn _ => fn (_, inst) =>
                    lookup_numc inst 1 <> 0 andalso lookup_numc inst 2 <> 0)],
        (fn ctxt => fn ((_, inst), ths) =>
            let
              val (n1, n2) = (lookup_numc inst 1, lookup_numc inst 2)
            in
              if n1 <= n2 then
                let
                  val inst' = update_env (("DIFF", 0), mk_nat (n2 - n1)) inst
                  val res_pat = @{term_pat "~ ((?a::nat) <= ?DIFF + ?b)"}
                in
                  prove_by_arith ctxt ths (Envir.subst_term inst' res_pat)
                end
              else
                let
                  val inst' = update_env (("DIFF", 0), mk_nat (n1 - n2)) inst
                  val res_pat = @{term_pat "~ (?DIFF + (?a::nat) <= ?b)"}
                in
                  prove_by_arith ctxt ths (Envir.subst_term inst' res_pat)
                end
            end)))

val _ = Theory.setup (
      add_prfstep_thm_fn (
        "le_plus_consts_fact'",
        [WithFact @{term_pat "(?NUMC1::nat) + ?a <= ?NUMC2"},
         Filter (fn _ => fn (_, inst) => lookup_numc inst 1 <> 0)],
        (fn ctxt => fn ((_, inst), ths) =>
            let
              val (n1, n2) = (lookup_numc inst 1, lookup_numc inst 2)
            in
              if n1 <= n2 then
                let
                  val inst' = update_env (("DIFF", 0), mk_nat (n2 - n1)) inst
                  val res_pat = @{term_pat "(?a::nat) <= ?DIFF"}
                in
                  prove_by_arith ctxt ths (Envir.subst_term inst' res_pat)
                end
              else contra_by_arith ctxt ths
            end)))

val _ = Theory.setup (
      add_prfstep_thm_fn (
        "le_plus_consts_goal'",
        [WithGoal @{term_pat "(?NUMC1::nat) + ?a <= ?NUMC2"},
         Filter (fn _ => fn (_, inst) =>
                    lookup_numc inst 1 <> 0 andalso
                    lookup_numc inst 1 <= lookup_numc inst 2)],
        (fn ctxt => fn ((_, inst), ths) =>
            let
              val (n1, n2) = (lookup_numc inst 1, lookup_numc inst 2)
              val inst' = update_env (("DIFF", 0), mk_nat (n2 - n1)) inst
              val res_pat = @{term_pat "~ ((?a::nat) <= ?DIFF)"}
            in
              prove_by_arith ctxt ths (Envir.subst_term inst' res_pat)
            end)))

(* Resolve equality facts with constants. *)
val _ = Theory.setup (
      add_prfstep_thm_fn (
        "compare_consts",
        [WithFact @{term_pat "(?NUMC1::nat) = ?NUMC2"},
         Filter (fn _ => fn (_, inst) =>
                    lookup_numc inst 1 <> lookup_numc inst 2)],
        fn ctxt => fn (_, ths) => contra_by_arith ctxt ths))

(* Resolve > facts with constants. *)
val _ = Theory.setup (
      add_prfstep_thm_fn (
        "compare_consts_greater",
        [WithFact @{term_pat "(?NUMC1::nat) > ?NUMC2"},
         Filter (fn _ => fn (_, inst) =>
                    lookup_numc inst 1 <= lookup_numc inst 2)],
        fn ctxt => fn (_, ths) => contra_by_arith ctxt ths))

(* Resolve <= facts with constants. *)
val _ = Theory.setup (
      add_prfstep_thm_fn (
        "compare_consts_le'",
        [WithFact @{term_pat "(?NUMC1::nat) <= ?NUMC2"},
         Filter (fn _ => fn (_, inst) =>
                    lookup_numc inst 1 > lookup_numc inst 2)],
        fn ctxt => fn (_, ths) => contra_by_arith ctxt ths))

val _ = Theory.setup (
      add_prfstep_thm_fn (
        "squeeze_nat'",
        [WithFact @{term_pat "(?NUMC1::nat) < ?a"},
         WithFact @{term_pat "?a < (?NUMC2::nat)"},
         Filter (fn _ => fn (_, inst) =>
                    (lookup_numc inst 1) + 1 = lookup_numc inst 2)],
        fn ctxt => fn (_, ths) => contra_by_arith ctxt ths))

(* Resolve + with constants. *)
val _ = Theory.setup (
      add_prfstep_thm_fn (
        "eval_plus_consts",
        [WithTerm @{term_pat "(?NUMC1::nat) + ?NUMC2"},
         Filter (order_filter_n ("NUMC", 1) ("NUMC", 2)),
         Filter (fn _ => fn (_, inst) =>
                    lookup_numc inst 1 > 0 andalso lookup_numc inst 2 > 0)],
        (fn ctxt => fn ((_, inst), _) =>
            let
              val (n1, n2) = (lookup_numc inst 1, lookup_numc inst 2)
              val inst' = update_env (("SUM", 0), mk_nat (n1 + n2)) inst
              val pat = @{term_pat "?NUMC1 + ?NUMC2 = (?SUM::nat)"}
            in
              prove_by_arith ctxt [] (Envir.subst_term inst' pat)
            end)))

(* Resolve * with constants. *)
val _ = Theory.setup (
      add_prfstep_thm_fn (
        "eval_mult_consts",
        [WithTerm @{term_pat "(?NUMC1::nat) * ?NUMC2"},
         Filter (order_filter_n ("NUMC", 1) ("NUMC", 2)),
         Filter (fn _ => fn (_, inst) =>
                    lookup_numc inst 1 > 1 andalso lookup_numc inst 2 > 1)],
        (fn ctxt => fn ((_, inst), _) =>
            let
              val (n1, n2) = (lookup_numc inst 1, lookup_numc inst 2)
              val inst' = update_env (("PROD", 0), mk_nat (n1 * n2)) inst
              val pat = @{term_pat "?NUMC1 * ?NUMC2 = (?PROD::nat)"}
            in
              prove_by_arith ctxt [] (Envir.subst_term inst' pat)
            end)))

(* Resolve - with constants. *)
val _ = Theory.setup (
      add_prfstep_thm_fn (
        "eval_minus_consts",
        [WithTerm @{term_pat "(?NUMC1::nat) - ?NUMC2"},
         Filter (fn _ => fn (_, inst) =>
                    lookup_numc inst 1 >= lookup_numc inst 2 andalso
                    lookup_numc inst 2 >= 1)],
        (fn ctxt => fn ((_, inst), _) =>
            let
              val (n1, n2) = (lookup_numc inst 1, lookup_numc inst 2)
              val inst' = update_env (("DIFF", 0), mk_nat (n1 - n2)) inst
              val pat = @{term_pat "?NUMC1 - ?NUMC2 = (?DIFF::nat)"}
            in
              prove_by_arith ctxt [] (Envir.subst_term inst' pat)
            end)))
