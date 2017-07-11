(* Set proofsteps. *)

fun FINSET_INDUCT (var_str, ind_infos) ctxt =
    let
      val ind_th =
          apply_to_thm (to_obj_conv_on_horn ctxt) @{thm finite_less_induct}

      val var = read_term ctxt var_str
      val concl = mk_Trueprop (
            Const (@{const_name finite}, type_of var --> boolT) $ var)
      val arbitraries = collect_arbitraries ctxt ind_infos
      val search_vars = var :: arbitraries

      fun callback ((id, fin_th), st as {ctxt, ...}) =
          let
            val var_ctxt = get_var_context id search_vars st
            val _ = assert (is_some var_ctxt)
                           "FINSET_INDUCT: cannot get var context."

            val ritems =
                apply_induction (the var_ctxt) [var] ctxt ind_th [fin_th]
          in
            [Update.thm_update (id, fin_th),
             AddItems {id = id, sc = NONE, raw_items = ritems}]
          end
    in
      [Script_Task {inits = [InitAssum (get_neg' concl)], subs = [],
                    cb = callback, end_vars = []}]
    end
