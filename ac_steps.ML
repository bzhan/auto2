(* Proof steps related to AC relations. *)

signature AC_PROOFSTEPS =
sig
  val reduce_unit: proofstep
  val ac_equiv: proofstep
  val get_ac_head_equiv_list: rewrite_table -> ac_inst_info ->
                              box_id * cterm list -> (box_id * thm) list
  val get_ac_head_expansion: rewrite_table -> ac_inst_info -> box_id * cterm ->
                             (box_id * thm) list
  val ac_equiv_strong: string * term -> proofstep
  val wf_ac_equiv: proofstep
  val add_ac_proofsteps: theory -> theory
end;

functor AC_ProofSteps(Base:UTIL_BASE) : AC_PROOFSTEPS =
struct

structure UtilLogic = UtilLogic(Base)
structure ACUtil = ACUtil(Base)
structure RewriteTable = RewriteTable(Base)
structure WfTerm = WfTerm(Base)
structure WfACUtil = WfACUtil(Base)
structure Matcher = Matcher(Base)
structure ItemIO = ItemIO(Base)
structure Update = Update(Base)
structure ProofStep_Data = ProofStep_Data(Base)
open Base
open UtilLogic

(* Reduce terms of the form 1 * n and n * 1. *)
fun reduce_unit_fn rtype _ {id, tname, ...} =
    let
      val (tbl as {ctxt, ...}) = RewriteTable.table_of_rtype rtype
      val ct = the_single tname
      val t = Thm.term_of ct
    in
      case ACUtil.get_head_ac_info_all ctxt t of
          NONE => []
        | SOME (ac_info as {cfhead, uinv_op, unit_val, ...}) =>
          if not (ACUtil.has_unit_th ac_info) then []
          else if Term.head_of t aconv (Thm.term_of uinv_op) then []
          else let  (* cfhead and inv_op cases. *)
            val unit_cv = #unit_cv ac_info
            val f = dest_binop_head t
            val (cA, cB) = dest_binop_cargs ct
            val l_equivs = (RewriteTable.equiv_info tbl id (cA, unit_val))
                               |> RewriteTable.replace_id_for_type' rtype
            val r_equivs = (RewriteTable.equiv_info tbl id (cB, unit_val))
                               |> RewriteTable.replace_id_for_type' rtype
            val l_cv =
                if f aconv Thm.term_of cfhead then unit_cv
                else (#inv_cv ac_info) then_conv unit_cv
            val r_cv =
                if f aconv Thm.term_of cfhead then unit_cv
                else (#inv_cv ac_info)
                         then_conv (Conv.arg_conv (#uinv_cv ac_info))
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
      val (tbl as {lat, ctxt, ...}) = RewriteTable.table_of_rtype rtype
      val ct = the_single tname
      val t = Thm.term_of ct
    in
      case ACUtil.get_head_ac_info_all ctxt t of
          NONE => []
        | SOME ac_info =>
          let
            fun head_agrees (_, ct) =
                ACUtil.head_agrees_all ac_info (Thm.term_of ct)
            val cts = filter head_agrees (RewriteTable.get_all_id_terms tbl)

            fun process_t (id', ct') =
                let
                  val id'' = BoxID.merge_boxes lat (id, id')
                in
                  if RewriteTable.is_equiv id'' tbl (ct, ct') then []
                  else let
                    val insts =
                        (Matcher.rewrite_match_ac
                             false ac_info tbl (t, ct') (id'', fo_init))
                            |> RewriteTable.replace_id_for_type rtype
                            |> max_partial (Matcher.inst_eq_better tbl [])
                    fun process_inst ((id''', _), eq_th) =
                        Update.thm_update (id''', to_obj_eq eq_th)
                  in
                    map process_inst insts
                  end
                end
          in
            maps process_t cts
          end
    end

(* Get possible ac head equivs for each of us, then combine. *)
fun get_ac_head_equiv_list (tbl as {lat, ...}) ac_info (id, cus) =
    let
      fun get_equiv cu =
          [(id, Thm.reflexive cu)] @
          Matcher.get_ac_head_equiv tbl ac_info (id, cu)

      fun process_equiv_list (id, eq_ths) =
          (id, (ACUtil.comb_ac_equiv ac_info eq_ths)
                   |> apply_to_rhs (ACUtil.normalize_assoc_l ac_info))
    in
      cus |> map get_equiv
          |> BoxID.get_all_merges_info lat
          |> map process_equiv_list
    end

fun get_ac_head_expansion tbl ac_info (id, ct) =
    let
      val norm_t = ACUtil.normalize_minus_assoc_l ac_info ct
      val cts = ACUtil.cdest_ac_l ac_info (Thm.rhs_of norm_t)
    in
      (get_ac_head_equiv_list tbl ac_info (id, cts))
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
      val (tbl as {lat, ctxt, ...}) = RewriteTable.table_of_rtype rtype
      val insts = ItemIO.match_arg tbl (PropMatch pat) item (id, fo_init)
      fun process_inst ((id, _), prop) =
          let
            val (A, B) = prop_of' prop |> get_neg |> dest_binop_args
            val (cA, cB) = (cert ctxt A, cert ctxt B)
          in
            case ACUtil.get_head_ac_info_all ctxt A of
                NONE => []
              | SOME ac_info =>
                let
                  val A_equivs = get_ac_head_expansion tbl ac_info (id, cA)
                  val B_equivs = get_ac_head_expansion tbl ac_info (id, cB)
                  val equivs = all_pairs (A_equivs, B_equivs)
                  fun process_equiv ((id1, eq_A), (id2, eq_B)) =
                      let
                        val id' = BoxID.merge_boxes lat (id1, id2)
                        val (A', cB') = (rhs_of eq_A, Thm.rhs_of eq_B)
                        val insts =
                            (Matcher.rewrite_match_ac
                                 false ac_info tbl (A', cB') (id', fo_init))
                                |> RewriteTable.replace_id_for_type rtype
                                |> max_partial (Matcher.inst_eq_better tbl [])
                        fun process_inst ((id'', _), eq_th) =
                            let
                              val eq = to_obj_eq (
                                    transitive_list [
                                      eq_A, eq_th, meta_sym eq_B])
                              val contra_eq = [prop, eq] MRS contra_triv_th
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

fun wf_ac_equiv_fn rtype _ {id, prop, ...} =
    let
      val (A, B) = prop_of' prop |> get_neg |> dest_binop_args
      val (tbl as {lat, ...}) = RewriteTable.table_of_rtype rtype
      val thy = RewriteTable.theory_of tbl
      val ac_info1_opt = WfACUtil.find_inst_ac_info thy A
      val ac_info2_opt = WfACUtil.find_inst_ac_info thy B
    in
      if is_none ac_info1_opt orelse is_none ac_info2_opt then [] else
      let
        val ac_info1 = the ac_info1_opt
        val ac_info2 = the ac_info2_opt
        val fhead = Term.head_of A
        val wfts1 = RewriteTable.term_to_wfterm_on_tbl_t tbl [fhead] (id, A)
        val wfts2 = RewriteTable.term_to_wfterm_on_tbl_t tbl [fhead] (id, B)
        fun process_wfts (id', (wft1, wft2)) =
            let
              val (_, eq1) = WfACUtil.normalize_assoc_l ac_info1 wft1
              val (_, eq2) = WfACUtil.normalize_assoc_l ac_info2 wft2
            in
              if rhs_of eq1 aconv rhs_of eq2 then
                let
                  val eq_th = transitive_list [eq1, meta_sym eq2]
                  val contra = [prop, to_obj_eq eq_th] MRS @{thm contra_triv}
                in
                  [(id', contra)]
                end
              else []
            end
      in
        (all_pairs (wfts1, wfts2))
            |> map (fn ((id1, wft1), (id2, wft2)) =>
                       (BoxID.merge_boxes lat (id1, id2), (wft1, wft2)))
            |> RewriteTable.replace_id_for_type' rtype
            |> maps process_wfts
            |> map Update.thm_update
      end
    end

val wf_ac_equiv =
    {name = "wf_ac_equiv",
     args = [TypedMatch (TY_PROP, @{term_pat "?A ~= ?B"})],
     priority = PRIORITY_RESOLVE,
     func = OneStep wf_ac_equiv_fn}

val add_ac_proofsteps =
    fold ProofStep_Data.add_prfstep [
      reduce_unit, ac_equiv, wf_ac_equiv
    ]

end  (* structure AC_ProofSteps. *)
