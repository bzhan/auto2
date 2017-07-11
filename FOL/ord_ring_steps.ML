(* Proof steps for ordered rings. *)

val le_t = @{term le}
val less_t = @{term less}
fun ord_heads G = rat_fheads G @ [le_t $ G, less_t $ G]

fun is_le G t = is_head (le_t $ G) t
fun is_less G t = is_head (less_t $ G) t
fun is_ineq G t = is_le G t orelse is_less G t
fun is_neg_le G t = is_neg t andalso is_le G (dest_not t)
fun is_neg_less G t = is_neg t andalso is_less G (dest_not t)
fun is_neg_ineq G t = is_neg t andalso is_ineq G (dest_not t)

signature ORD_RING_STEPS =
sig
  type ord_ring_info
  val normalize_ineq: ord_ring_info -> wfconv
  val ord_ring_alg_data: thm -> ord_ring_info
  val ord_normalize_le: proofstep
  val ord_normalize_less: proofstep
  val add_ord_ring_proofsteps: theory -> theory
end;


structure OrdRingSteps : ORD_RING_STEPS =
struct

type ord_ring_info = {
  G: term,
  ring_info: AlgCommRing.comm_ring_info,
  switch_le: wfconv,  (* x <= y <--> 0 <= y - x *)
  switch_less: wfconv  (* x < y <--> 0 < y - x *)
}

fun normalize_ineq info wft =
    let
      val {G, ring_info, switch_le, switch_less, ...} = info
      val t = WfTerm.term_of wft
    in
      if is_le G t then
        WfTerm.every_conv
            [switch_le, WfTerm.arg_conv (AlgCommRing.norm_full ring_info)] wft
      else if is_less G t then
        WfTerm.every_conv
            [switch_less, WfTerm.arg_conv (AlgCommRing.norm_full ring_info)] wft
      else
        WfTerm.all_conv wft
    end

fun ord_ring_alg_data ord_ring_th =
    let
      val G = dest_arg (prop_of' ord_ring_th)
      val fheads = ord_heads G
      fun rewr th = WfTerm.rewr_obj_eq fheads th
      val c_ring_th = ord_ring_th RS @{thm is_ord_ringD(2)}
    in
      {G = G,
       ring_info = AlgCommRing.comm_ring_alg_data c_ring_th,
       switch_le = rewr (ord_ring_th RS @{thm ord_ring_le_switch_left}),
       switch_less = rewr (ord_ring_th RS @{thm ord_ring_less_switch_left})
      }
    end

fun ord_normalize_fn rtype _ item1 item2 =
    let
      val tbl = RewriteTable.table_of_rtype rtype
      val {lat, ...} = tbl
      val {id = id1, prop = prop1, ...} = item1
      val {id = id2, prop = prop2, ...} = item2
      val id = BoxID.merge_boxes lat (id1, id2)

      (* t1 is the statement of prop1, t2 is statement of prop2 with
         negation removed.
       *)
      val (ct1, ct2) = (cprop_of' prop1, Thm.dest_arg (cprop_of' prop2))
      val (t1, t2) = (Thm.term_of ct1, Thm.term_of ct2)
      val (x1, y1) = dest_binop_args t1
      val (x2, y2) = dest_binop_args t2
      val G = hd (dest_args (Thm.term_of ct1))
      val diff1 = AlgCommRing.norm_term G (minus_t $ G $ y1 $ x1)
      val diff2 = AlgCommRing.norm_term G (minus_t $ G $ y2 $ x2)
    in
      if not (diff1 aconv diff2) then []
      else let
        val pred_t = @{term is_ord_ring}
        val fheads = ord_heads G
        val property_infos = RewriteTable.get_property_t tbl (id, pred_t $ G)

        fun process_wft property_th (id', (wft1, wft2)) =
            let
              val wfcv = normalize_ineq (ord_ring_alg_data property_th)
              val (_, eq1) = wfcv wft1
              val (_, eq2) = wfcv wft2
            in
              if not (rhs_of eq1 aconv rhs_of eq2) then []
              else let
                val prop1' =
                    apply_to_thm' (Conv.rewr_conv eq1) prop1
                val prop2' =
                    apply_to_thm' (Conv.arg_conv (Conv.rewr_conv eq2)) prop2
                val contra_th = [prop2', prop1'] MRS @{thm contra_triv}
              in
                [Update.thm_update (id', contra_th)]
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
                  |> maps (process_wft property_th)
            end
      in
        maps process_property_info property_infos
      end
    end

val ord_normalize_le =
    {name = "ord_normalize_le",
     args = [TypedMatch (TY_PROP, @{term_pat "le(?G,?A,?B)"}),
             TypedMatch (TY_PROP, @{term_pat "~le(?G,?C,?D)"})],
     priority = PRIORITY_RESOLVE,
     func = TwoStep ord_normalize_fn}

val ord_normalize_less =
    {name = "ord_normalize_less",
     args = [TypedMatch (TY_PROP, @{term_pat "less(?G,?A,?B)"}),
             TypedMatch (TY_PROP, @{term_pat "~less(?G,?C,?D)"})],
     priority = PRIORITY_RESOLVE,
     func = TwoStep ord_normalize_fn}

val add_ord_ring_proofsteps =
    fold ProofStep_Data.add_prfstep [
      ord_normalize_le, ord_normalize_less
    ]

end  (* OrdRingSteps *)

val _ = Theory.setup OrdRingSteps.add_ord_ring_proofsteps
