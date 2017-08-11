(* Associativity (outside structures) *)

signature FOL_ASSOC =
sig
  val dest_assoc: term -> term -> term list
  val normalize_assoc: term * thm -> wfconv
  val alg_assoc_prfstep: term * thm -> proofstep
end;

structure FOL_Assoc : FOL_ASSOC =
struct

fun dest_assoc fhead t =
    if Term.head_of t aconv fhead then
      maps (dest_assoc fhead) [dest_arg1 t, dest_arg t]
    else [t]

fun normalize_assoc (fhead, assoc_l) wft =
    let
      val assoc_l_cv = WfTerm.rewr_obj_eq [fhead] assoc_l
      fun normalize wft =
          if Term.head_of (WfTerm.term_of wft) aconv fhead then
            WfTerm.every_conv [WfTerm.repeat_conv assoc_l_cv,
                               WfTerm.arg1_conv normalize] wft
          else
            WfTerm.all_conv wft
    in
      normalize wft
    end

fun alg_assoc_prfstep_fn (fhead, assoc_l) rtype _ item1 item2 =
    let
      val tbl = RewriteTable.table_of_rtype rtype
      val {lat, ...} = tbl
      val {id = id1, tname = tname1, ...} = item1
      val {id = id2, tname = tname2, ...} = item2
      val id = BoxID.merge_boxes lat (id1, id2)
      val (ct1, ct2) = (the_single tname1, the_single tname2)
      val (t1, t2) = (Thm.term_of ct1, Thm.term_of ct2)
      val (ts1, ts2) = apply2 (dest_assoc fhead) (t1, t2)
    in
      if not (eq_list (op aconv) (ts1, ts2)) then []
      else if RewriteTable.is_equiv id tbl (ct1, ct2) then []
      else let
        val wfts1 = RewriteTable.term_to_wfterm_on_tbl_t tbl [fhead] (id, t1)
        val wfts2 = RewriteTable.term_to_wfterm_on_tbl_t tbl [fhead] (id, t2)
        fun process_wft (id', (wft1, wft2)) =
            let
              val (_, eq1) = normalize_assoc (fhead, assoc_l) wft1
              val (_, eq2) = normalize_assoc (fhead, assoc_l) wft2
              val _ = assert (rhs_of eq1 aconv rhs_of eq2)
                             "alg_assoc_prfstep"
              val eq_th = to_obj_eq (transitive_list [eq1, meta_sym eq2])
            in
              AddItems {id = id', sc = SOME 1,
                        raw_items = [Update.thm_to_ritem eq_th]}
            end
      in
        (all_pairs (wfts1, wfts2))
            |> map (fn ((id1, wft1), (id2, wft2)) =>
                       (BoxID.merge_boxes lat (id1, id2), (wft1, wft2)))
            |> RewriteTable.replace_id_for_type' rtype
            |> map process_wft
      end
    end

fun alg_assoc_prfstep (fhead, assoc_l) =
    let
      val nm = fst (Term.dest_Const fhead)
    in
      {name = nm ^ "@assoc",
       args = [TypedMatch (TY_TERM, @{term_pat "?A"}),
               TypedMatch (TY_TERM, @{term_pat "?B"})],
       priority = PRIORITY_ADD,
       func = TwoStep (alg_assoc_prfstep_fn (fhead, assoc_l))}
    end

end  (* structure FOL_Assoc *)