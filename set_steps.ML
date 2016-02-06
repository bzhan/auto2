(* Set proofsteps. *)

fun finite_set_strong_induction vars_spec =
    prfstep_custom
        "finite_set_strong_induction"
        [WithFact @{term_pat "finite ?A"}]
        [Update.ADD_ITEMS]
        (fn ((id, inst), ths) => fn _ => fn (st as {ctxt, ...}) =>
            let
              val trm_A = lookup_inst inst "A"
              val (var_infos, extra_vars) = get_ind_vars ([trm_A], vars_spec)
              val (_, var_eq) = the_single var_infos
              val search_vars = filter is_Free [trm_A] @ extra_vars
              val var_ctxt = get_var_context id search_vars st
              val ind_th = apply_to_thm (to_obj_conv_on_horn ctxt)
                           @{thm finite_less_induct}

              (* Similar to use_var_eq in induction.ML, but converts
                 finite trm_A to finite ind_var.
               *)
              fun use_var_eq ctxt var_eq =
                  case var_eq of
                      NONE => I
                    | SOME eq => eq |> assume_thm ctxt |> obj_sym |> rewr_obj_eq
                                    |> Conv.arg_conv |> Conv.arg_conv
                                    |> apply_to_thm

              val finite_th = ths |> the_single |> use_var_eq ctxt var_eq
            in
              if is_none var_ctxt then []
              else apply_induction id (the var_ctxt) var_infos ctxt ind_th
                                   [finite_th]
            end)

fun FINSET_INDUCT' (var_spec_str, ind_infos) ctxt =
    let
      val var_spec = Syntax.read_term ctxt var_spec_str
      val new_var =
          case var_spec of
              Const ("HOL.eq", _) $ lhs $ _ => [lhs]
            | _ => []

      val arbitraries = (collect_arbitraries ind_infos)
                            |> map (Syntax.read_term ctxt)
      val facts = (collect_facts ind_infos)
                      |> map (Syntax.read_term ctxt)
                      |> map (fn t => (TY_PROP, t))
      val _ = assert (length facts = 1)
                     "FINSET_INDUCT: should have exactly one fact."
      val prfstep = finite_set_strong_induction (new_var @ arbitraries)
    in
      [Script_Info {prfstep = prfstep, source = facts, end_vars = new_var}]
    end

(* Simplified form *)
fun FINSET_INDUCT (var, extra_vars) =
    let
      val finite_str = "finite " ^ var
    in
      OBTAIN finite_str THEN
             FINSET_INDUCT' (var, OnFact finite_str :: Arbitraries extra_vars)
    end

fun FINSET_INDUCT_NEWVAR (exp, var, extra_vars) =
    let
      val finite_str = "finite (" ^ exp ^ ")"
    in
      OBTAIN finite_str THEN
             FINSET_INDUCT' (var ^ " = (" ^ exp ^ ")",
                             OnFact finite_str :: Arbitraries extra_vars)
    end

val _ = Theory.setup (add_reserved_name "finite_set_strong_induction")
