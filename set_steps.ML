(* Set proofsteps. *)

fun FINSET_INDUCT (var_spec_str, ind_infos) ctxt =
    let
      val ind_th =
          apply_to_thm (to_obj_conv_on_horn ctxt) @{thm finite_less_induct}

      val (var, rhs, var_eq) = process_var_spec_str ctxt var_spec_str
      val concl = mk_Trueprop (
            Const (@{const_name finite}, type_of var --> boolT) $ rhs)
      val arbitraries = collect_arbitraries ctxt ind_infos
      val search_vars = filter is_Free [rhs] @ arbitraries

      (* Similar to use_var_eq in induction.ML, but converts finite t
         to finite ind_var.
       *)
      fun use_var_eq ctxt var_eq =
          case var_eq of
              NONE => I
            | SOME eq => eq |> assume_thm ctxt |> obj_sym |> rewr_obj_eq
                            |> Conv.arg_conv |> apply_to_thm'

      fun callback ((id, fin_th), st as {ctxt, ...}) =
          let
            val var_ctxt = get_var_context id search_vars st
            val _ = assert (is_some var_ctxt)
                           "FINSET_INDUCT: cannot get var context."

            val fin_th' = fin_th |> use_var_eq ctxt var_eq
            val var_infos = [(var, var_eq)]
            val ritems =
                apply_induction (the var_ctxt) var_infos ctxt ind_th [fin_th']
          in
            [Update.thm_update (id, fin_th),
             AddItems {id = id, raw_items = ritems}]
          end
    in
      [Script_Task {inits = [InitAssum (get_neg' concl)], subs = [],
                    cb = callback, end_vars = get_new_vars var_eq}]
    end
