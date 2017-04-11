(* Algebraic manipulations in FOL. *)

signature FOL_ALG_UTIL =
sig
  val get_struct_t: term list -> term -> term option
  val alg_norm1_prfstep: term list * (term -> term -> term) * term -> proofstep
  val alg_norm2_prfstep: term list * (term -> term -> term) * term -> proofstep
end;

structure FOLAlgUtil : FOL_ALG_UTIL =
struct

fun get_struct_t op_heads t =
    if member (op aconv) op_heads (head_of t) then
      SOME (hd (dest_args t))
    else NONE

fun alg_norm1_prfstep_fn (op_heads, norm_fn, pred_t) rtype _ {id, tname, ...} =
    let
      val tbl = RewriteTable.table_of_rtype rtype
      val {lat, ctxt, ...} = tbl
      val ct = the_single tname
      val t = Thm.term_of ct
      val G_opt = get_struct_t op_heads t
    in
      if is_none G_opt then []
      else let
        val G = the G_opt
        val t' = norm_fn G t
      in
        if member (op aconv) op_heads (head_of t') orelse
           RewriteTable.is_equiv id tbl (ct, cert ctxt t') then []
        else let
          val fheads = map (fn t => t $ G) op_heads
          val alg_inst_infos = WfACUtil.lookup_alg_inst_info ctxt G

          fun process_wft (_, wfcv) (id', wft) =
              let
                val (_, eq) = wfcv wft
              in
                if rhs_of eq aconv t' then
                  AddItems {id = id', sc = SOME 1,
                            raw_items = [Update.thm_to_ritem (to_obj_eq eq)]}
                else let
                  val _ = trace_tlist_ctxt ctxt "" [t, rhs_of eq, t']
                  val nm = fst (Term.dest_Const pred_t)
                in
                  raise AUTO2 ("alg_norm1 for " ^ nm)
                end
              end

          fun process_inst_info (id', (pred, _, wfcv)) =
              if not (Term.head_of pred aconv pred_t) then []
              else let
                val id'' = BoxID.merge_boxes lat (id, id')
                val wfts =
                    RewriteTable.term_to_wfterm_on_tbl tbl fheads (id'', ct)
              in
                wfts |> RewriteTable.replace_id_for_type' rtype
                     |> map (process_wft (pred, wfcv))
              end
        in
          maps process_inst_info alg_inst_infos
        end
      end
    end

fun alg_norm1_prfstep (op_heads, norm_fn, pred_t) =
    let
      val nm = fst (Term.dest_Const pred_t)
               handle TERM _ => raise AUTO2 "alg_norm1_prfstep"
    in
      {name = nm ^ "@norm1",
       args = [TypedMatch (TY_TERM, @{term_pat "?A"})],
       priority = PRIORITY_ADD,
       func = OneStep (alg_norm1_prfstep_fn (op_heads, norm_fn, pred_t))}
    end

fun alg_norm2_prfstep_fn (op_heads, norm_fn, pred_t) rtype _ item1 item2 =
    let
      val tbl = RewriteTable.table_of_rtype rtype
      val {lat, ctxt, ...} = tbl
      val {id = id1, tname = tname1, ...} = item1
      val {id = id2, tname = tname2, ...} = item2
      val id = BoxID.merge_boxes lat (id1, id2)
      val (ct1, ct2) = (the_single tname1, the_single tname2)
      val (t1, t2) = (Thm.term_of ct1, Thm.term_of ct2)
      val (G1_opt, G2_opt) = apply2 (get_struct_t op_heads) (t1, t2)
    in
      if is_none G1_opt orelse is_none G2_opt orelse
         not (the G1_opt aconv the G2_opt) then []
      else let
        val G = the G1_opt
        val t1' = norm_fn G t1
        val t2' = norm_fn G t2
      in
        if not (t1' aconv t2') orelse
           RewriteTable.is_equiv id tbl (ct1, ct2) then []
        else let
          val fheads = map (fn t => t $ G) op_heads
          val alg_inst_infos = WfACUtil.lookup_alg_inst_info ctxt G

          fun process_wft (_, wfcv) (id', (wft1, wft2)) =
              let
                val (_, eq1) = wfcv wft1
                val (_, eq2) = wfcv wft2
              in
                if rhs_of eq1 aconv t1' andalso rhs_of eq2 aconv t2' then
                  let
                    val th = to_obj_eq (transitive_list [eq1, meta_sym eq2])
                  in
                    AddItems {id = id', sc = SOME 1,
                              raw_items = [Update.thm_to_ritem th]}
                  end
                else let
                  val _ = trace_tlist_ctxt ctxt "" [t1, rhs_of eq1, t1']
                  val _ = trace_tlist_ctxt ctxt "" [t2, rhs_of eq2, t2']
                  val nm = fst (Term.dest_Const pred_t)
                in
                  raise AUTO2 ("alg_norm2 for " ^ nm)
                end
              end

          fun process_inst_info (id', (pred, _, wfcv)) =
              if not (Term.head_of pred aconv pred_t) then []
              else let
                val id'' = BoxID.merge_boxes lat (id, id')
                val wfts1 =
                    RewriteTable.term_to_wfterm_on_tbl tbl fheads (id'', ct1)
                val wfts2 =
                    RewriteTable.term_to_wfterm_on_tbl tbl fheads (id'', ct2)
              in
                (all_pairs (wfts1, wfts2))
                    |> map (fn ((id1, wft1), (id2, wft2)) =>
                               (BoxID.merge_boxes lat (id1, id2), (wft1, wft2)))
                    |> RewriteTable.replace_id_for_type' rtype
                    |> map (process_wft (pred, wfcv))
              end
        in
          maps process_inst_info alg_inst_infos
        end
      end
    end

fun alg_norm2_prfstep (op_heads, norm_fn, pred_t) =
    let
      val nm = fst (Term.dest_Const pred_t)
    in
      {name = nm ^ "@norm2",
       args = [TypedMatch (TY_TERM, @{term_pat "?A"}),
               TypedMatch (TY_TERM, @{term_pat "?B"})],
       priority = PRIORITY_ADD,
       func = TwoStep (alg_norm2_prfstep_fn (op_heads, norm_fn, pred_t))}
    end

end  (* structure AlgUtil. *)
