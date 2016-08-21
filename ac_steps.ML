(* Proof steps related to AC relations. *)

signature AC_PROOFSTEPS =
sig
  val reduce_unit: proofstep
  val ac_equiv: proofstep
  val ac_equiv_strong: string * term -> proofstep
  val add_ac_proofsteps: theory -> theory
end;

structure AC_ProofSteps : AC_PROOFSTEPS =
struct

(* Reduce terms of the form 1 * n and n * 1. *)
fun reduce_unit_fn rtype _ {id, tname, ...} =
    let
      val (tbl as {ctxt, ...}) = RewriteTable.table_of_rtype rtype
    in
      case RewriteTable.get_head_ac_info_with_inv tbl tname of
          NONE => []
        | SOME (ac_info as {cfhead, uinv_op, unit_val, ...}) =>
          if not (ACUtil.has_unit_th ac_info) then []
          else if Term.head_of tname aconv uinv_op then []
          else let  (* cfhead and inv_op cases. *)
            val unit_cv = ACUtil.unit_cv ac_info
            val (f, (A, B)) = dest_binop tname
            val l_equivs = (RewriteTable.equiv_info tbl id (A, unit_val))
                               |> RewriteTable.replace_id_for_type' rtype
            val r_equivs = (RewriteTable.equiv_info tbl id (B, unit_val))
                               |> RewriteTable.replace_id_for_type' rtype
            val ct = cert ctxt tname
            val l_cv =
                if f aconv Thm.term_of cfhead then unit_cv
                else (ACUtil.binop_inv_cv ac_info) then_conv unit_cv
            val r_cv =
                if f aconv Thm.term_of cfhead then unit_cv
                else (ACUtil.binop_inv_cv ac_info)
                         then_conv (Conv.arg_conv (ACUtil.unit_inv_cv ac_info))
                         then_conv unit_cv
            fun process_l_equiv (id', eq_th) =
                (id', ct |> Conv.arg1_conv (Conv.rewr_conv eq_th)
                         |> apply_to_rhs l_cv |> to_obj_eq)
            fun process_r_equiv (id', eq_th) =
                (id', ct |> Conv.arg_conv (Conv.rewr_conv eq_th)
                         |> apply_to_rhs r_cv |> to_obj_eq)
          in
            map Update.thm_update (map process_l_equiv l_equivs @
                                   map process_r_equiv r_equivs)
          end
    end

val reduce_unit =
    {name = "reduce_unit",
     args = [TypedMatch (TY_TERM, @{term_pat "?A"})],
     priority = PRIORITY_ADD,
     func = OneStep reduce_unit_fn}

(* Compare term with all other terms by matching AC. *)
fun ac_equiv_fn rtype _ {id, tname, ...} =
    let
      val (tbl as {lat, ...}) = RewriteTable.table_of_rtype rtype
    in
      case RewriteTable.get_head_ac_info_with_inv tbl tname of
          NONE => []
        | SOME ac_info =>
          let
            val ts = (RewriteTable.get_all_id_terms tbl)
                         |> filter (ACUtil.head_agrees_with_inv ac_info o snd)
            fun process_t (id', t) =
                let
                  val id'' = BoxID.merge_boxes lat (id, id')
                in
                  if RewriteTable.is_equiv id'' tbl (tname, t) then []
                  else let
                    val insts =
                        (Matcher.rewrite_match_ac false
                             ac_info tbl (tname, t) (id'', fo_init))
                            |> RewriteTable.replace_id_for_type rtype
                            |> max_partial (Matcher.inst_eq_better tbl [])
                    fun process_inst ((id''', _), eq_th) =
                        Update.thm_update (id''', to_obj_eq eq_th)
                  in
                    map process_inst insts
                  end
                end
          in
            maps process_t ts
          end
    end

(* Get possible ac head equivs for each of us, then combine. *)
fun get_ac_head_equiv_list (tbl as {lat, ...}) ac_info (id, us) =
    let
      fun get_equiv u =
          [(id, RewriteTable.refl tbl u)] @
          Matcher.get_ac_head_equiv tbl ac_info (id, u)

      fun process_equiv_list (id, eq_ths) =
          (id, (ACUtil.comb_ac_equiv ac_info eq_ths)
                   |> apply_to_rhs (ACUtil.normalize_assoc_l ac_info))
    in
      us |> map get_equiv
         |> BoxID.get_all_merges_info lat
         |> map process_equiv_list
    end

fun get_ac_head_expansion (tbl as {ctxt, ...}) ac_info (id, t) =
    let
      val norm_t = t |> cert ctxt |> ACUtil.normalize_minus_assoc_l ac_info
      val ts = ACUtil.dest_ac_l ac_info (rhs_of norm_t)
    in
      (get_ac_head_equiv_list tbl ac_info (id, ts))
          |> map (fn (id, th) => (id, transitive_list [norm_t, th]))
    end

val ac_equiv =
    {name = "ac_equiv",
     args = [TypedMatch (TY_TERM, @{term_pat "?A::?'a"})],
     priority = PRIORITY_ADD,
     func = OneStep ac_equiv_fn}

(* Pay more attention when a goal is to prove A = B. *)
fun ac_equiv_strong_fn pat rtype _ (item as {id, ...}) =
    let
      val (tbl as {lat, ...}) = RewriteTable.table_of_rtype rtype
      val insts = ItemIO_Data.match_arg tbl (PropMatch pat) item (id, fo_init)
      fun process_inst ((id, _), prop) =
          let
            val (A, B) = prop_of' prop |> get_neg |> dest_binop |> snd
          in
            case RewriteTable.get_head_ac_info_with_inv tbl A of
                NONE => []
              | SOME ac_info =>
                let
                  val A_equivs = get_ac_head_expansion tbl ac_info (id, A)
                  val B_equivs = get_ac_head_expansion tbl ac_info (id, B)
                  val equivs = all_pairs (A_equivs, B_equivs)
                  fun process_equiv ((id1, eq_A), (id2, eq_B)) =
                      let
                        val id' = BoxID.merge_boxes lat (id1, id2)
                        val (A', B') = (rhs_of eq_A, rhs_of eq_B)
                        val insts =
                            (Matcher.rewrite_match_ac false
                                 ac_info tbl (A', B') (id', fo_init))
                                |> RewriteTable.replace_id_for_type rtype
                                |> max_partial (Matcher.inst_eq_better tbl [])
                        fun process_inst ((id'', _), eq_th) =
                            let
                              val eq = to_obj_eq (
                                    transitive_list [
                                      eq_A, eq_th, meta_sym eq_B])
                              val contra_eq = [prop, eq] MRS @{thm contra_triv}
                            in
                              Update.thm_update (id'', contra_eq)
                            end
                      in
                        map process_inst insts
                      end
                in
                  maps process_equiv equivs
                end
          end
    in
      maps process_inst insts
    end

fun ac_equiv_strong (nm, pat) =
    {name = nm,
     args = [PropMatch pat],
     priority = PRIORITY_RESOLVE,
     func = OneStep (ac_equiv_strong_fn pat)}

val add_ac_proofsteps =
    fold add_prfstep [
      reduce_unit, ac_equiv
    ]

end  (* structure AC_ProofSteps. *)

val _ = Theory.setup AC_ProofSteps.add_ac_proofsteps
