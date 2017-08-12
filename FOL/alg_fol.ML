(* Algebraic manipulations in FOL. *)

signature FOL_ALG_UTIL =
sig
  type alg_norm_info
  val get_struct_t: term list -> term -> term option
  val alg_norm1_prfstep: alg_norm_info -> proofstep
  val alg_norm2_prfstep: alg_norm_info -> proofstep
end;

structure FOLAlgUtil : FOL_ALG_UTIL =
struct

type alg_norm_info = {
  op_heads: term list,
  pred_t: term,
  norm_t: term -> term -> term,
  excl_norm_t: (term -> term -> term) list,
  norm_wfcv: thm -> wfconv
}

fun get_struct_t op_heads t =
    if member (op aconv) op_heads (head_of t) then
      SOME (hd (dest_args t))
    else NONE

fun alg_norm1_prfstep_fn norm_info rtype _ {id, tname, ...} =
    let
      val tbl = RewriteTable.table_of_rtype rtype
      val {ctxt, ...} = tbl
      val {op_heads, pred_t, norm_t, excl_norm_t, norm_wfcv} = norm_info
      val ct = the_single tname
      val t = Thm.term_of ct
      val G_opt = get_struct_t op_heads t
    in
      if is_none G_opt then []
      else let
        val G = the G_opt
        val t' = norm_t G t
      in
        if member (op aconv) op_heads (head_of t') orelse
           RewriteTable.is_equiv id tbl (ct, cert ctxt t') orelse
           exists (fn f => f G t aconv t') excl_norm_t then []
        else let
          val fheads = map (fn t => t $ G) op_heads
          val property_infos = RewriteTable.get_property_t tbl (id, pred_t $ G)

          fun process_wft property_th (id', wft) =
              let
                val wfcv = norm_wfcv property_th
                val (_, eq) = wfcv wft
              in
                if rhs_of eq aconv t' then
                  AddItems {id = id', sc = SOME 1,
                            raw_items = [Update.thm_to_ritem (to_obj_eq eq)]}
                else let
                  val _ = trace_tlist ctxt "" [t, rhs_of eq, t']
                  val nm = fst (Term.dest_Const pred_t)
                in
                  raise Fail ("alg_norm1 for " ^ nm)
                end
              end

          fun process_property_info (id', property_th) =
              (RewriteTable.term_to_wfterm_on_tbl tbl fheads (id', ct))
                  |> RewriteTable.replace_id_for_type' rtype
                  |> map (process_wft property_th)
        in
          maps process_property_info property_infos
        end
      end
    end

fun alg_norm1_prfstep norm_info =
    let
      val {pred_t, ...} = norm_info
      val nm = fst (Term.dest_Const pred_t)
               handle TERM _ => raise Fail "alg_norm1_prfstep"
    in
      {name = nm ^ "@norm1",
       args = [TypedMatch (TY_TERM, @{term_pat "?A"})],
       priority = PRIORITY_ADD,
       func = OneStep (alg_norm1_prfstep_fn norm_info)}
    end

fun alg_norm2_prfstep_fn norm_info rtype _ item1 item2 =
    let
      val tbl = RewriteTable.table_of_rtype rtype
      val {lat, ctxt, ...} = tbl
      val {op_heads, pred_t, norm_t, excl_norm_t, norm_wfcv} = norm_info
      val {id = id1, tname = tname1, ...} = item1
      val {id = id2, tname = tname2, ...} = item2
      val id = BoxID.merge_boxes lat (id1, id2)
      val (ct1, ct2) = (the_single tname1, the_single tname2)
      val (t1, t2) = (Thm.term_of ct1, Thm.term_of ct2)
      val (G1_opt, G2_opt) = apply2 (get_struct_t op_heads) (t1, t2)
    in
      if is_none G1_opt orelse is_none G2_opt orelse
         not (the G1_opt aconv the G2_opt) orelse
         Term_Ord.termless (t2, t1) then []
      else let
        val G = the G1_opt
        val t1' = norm_t G t1
        val t2' = norm_t G t2
      in
        if not (t1' aconv t2') orelse
           RewriteTable.is_equiv id tbl (ct1, ct2) orelse
           exists (fn f => f G t1 aconv f G t2) excl_norm_t then []
        else let
          val fheads = map (fn t => t $ G) op_heads
          val property_infos = RewriteTable.get_property_t tbl (id, pred_t $ G)

          fun process_wft property_th (id', (wft1, wft2)) =
              let
                val wfcv = norm_wfcv property_th
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
                  val _ = trace_tlist ctxt "" [t1, rhs_of eq1, t1']
                  val _ = trace_tlist ctxt "" [t2, rhs_of eq2, t2']
                  val nm = fst (Term.dest_Const pred_t)
                in
                  raise Fail ("alg_norm2 for " ^ nm)
                end
              end

          fun process_property_info (id', property_th) =
              let
                val wfts1 =
                    RewriteTable.term_to_wfterm_on_tbl tbl fheads (id', ct1)
                val wfts2 =
                    RewriteTable.term_to_wfterm_on_tbl tbl fheads (id', ct2)
              in
                (all_pairs (wfts1, wfts2))
                    |> map (fn ((id1, wft1), (id2, wft2)) =>
                               (BoxID.merge_boxes lat (id1, id2), (wft1, wft2)))
                    |> RewriteTable.replace_id_for_type' rtype
                    |> map (process_wft property_th)
              end
        in
          maps process_property_info property_infos
        end
      end
    end

fun alg_norm2_prfstep norm_info =
    let
      val {pred_t, ...} = norm_info
      val nm = fst (Term.dest_Const pred_t)
    in
      {name = nm ^ "@norm2",
       args = [TypedMatch (TY_TERM, @{term_pat "?A"}),
               TypedMatch (TY_TERM, @{term_pat "?B"})],
       priority = PRIORITY_ADD,
       func = TwoStep (alg_norm2_prfstep_fn norm_info)}
    end

end  (* structure AlgUtil. *)
