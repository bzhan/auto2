(* Using induction rules derived from function definitions. *)

fun prfstep_hoare_triple_induction name descs ind_th =
    prfstep_custom
        name descs PRIORITY_ADD
        (fn ((id, _), ths) => fn _ => fn (st as {ctxt, ...}) =>
            let
              val init_th = the_single ths
              val init_prop = Thm.prop_of init_th
              val init_prop' = HOLogic.dest_Trueprop init_prop
              val (_, c, _) = Sep_Logic.dest_hoare_triple (get_neg init_prop')
              val ind_vars = dest_args c
              val gen_vars = map Free (Term.add_frees init_prop' [])
              val var_ctxt = get_var_context id gen_vars st
            in
              case var_ctxt of
                  NONE => []
                | SOME (inits as (_, assums)) =>
                  if member (op aconv) assums init_prop then
                    let
                      val ritems =
                          apply_induction
                              inits (map (rpair NONE) ind_vars) ctxt ind_th []
                    in
                      [Update.AddItems {id = id, raw_items = ritems}]
                    end
                  else []
            end)

fun add_prfstep_imp_induction cmd_pat ind_th thy =
    let
      val name = name_of_thm ind_th

      (* Obtain type 'a Heap. *)
      val ctxt = Proof_Context.init_global thy
      val ty_aHeap = @{typ_pat "?'a Heap"}
      val ty_inst = pattern_match_ty ctxt (ty_aHeap, type_of cmd_pat)
      val cmd_inst = update_env (("c", 0), cmd_pat) fo_init

      val name_ht = name ^ "@htinduct"
      val ht_pat = @{term_pat "~ (<?P> (?c::?'a Heap) <?Q>)"}
                        |> Envir.subst_term_types ty_inst
                        |> Envir.subst_term cmd_inst
      val descs_ht = [WithFact ht_pat] @ [Filter (id_filter (equal [0]))]
      val _ = writeln (name_ht ^ "\n" ^ (string_of_descs thy descs_ht))
      val prfstep_ht = prfstep_hoare_triple_induction name_ht descs_ht ind_th
    in
      add_prfstep prfstep_ht thy
    end
