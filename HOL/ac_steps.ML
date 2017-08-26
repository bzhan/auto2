(* Proof steps related to AC relations. *)

signature AC_PROOFSTEPS =
sig
  val max_ac: int Config.T
  val ac_expand_once:
      rewrite_table -> ac_info -> box_id * cterm -> (box_id * thm) list
  val ac_expand:
      rewrite_table -> ac_info -> box_id * cterm -> (box_id * thm) list
  val ac_expand_equiv: proofstep

  val add_ac_proofsteps: theory -> theory
end;

structure AC_ProofSteps : AC_PROOFSTEPS =
struct

val max_ac = Attrib.setup_config_int @{binding "max_ac"} (K 20)

fun get_ac_head_equiv (tbl as {ctxt, ...}) ac_info (id, cu) =
    let
      fun process_equiv_list (id', eq_th) (id'', eq_ths) =
          (BoxID.merge_boxes ctxt (id', id''),
           Util.transitive_list [eq_th, ACUtil.comb_ac_equiv ac_info eq_ths])

      (* Simplify each term of the AC expression on the right side. *)
      fun process_head_equiv (id', eq_th) =
          let
            val cus = ACUtil.cdest_ac ac_info (Thm.rhs_of eq_th)
          in
            cus |> map (RewriteTable.simplify_info tbl)
                |> BoxID.get_all_merges_info ctxt
                |> map (process_equiv_list (id', eq_th))
          end
    in
      cu |> RewriteTable.get_head_equiv tbl
         |> maps snd
         |> RewriteTable.merge_box_with_info ctxt id
         |> maps process_head_equiv
         |> filter_out (Thm.is_reflexive o snd)
    end

fun is_subseq eq (l1, l2) =
    case l1 of
        [] => true
      | x :: l1' =>
        case l2 of
            [] => false
          | y :: l2' => if eq (x, y) then is_subseq eq (l1', l2')
                        else is_subseq eq (l1, l2')

(* Find ways to modify ct once by rewriting one of the subterms. *)
fun ac_expand_once tbl ac_info (id, ct) =
    let
      val cus = ACUtil.cdest_ac ac_info ct
      val refls = map Thm.reflexive cus
      fun get_equiv cu = get_ac_head_equiv tbl ac_info (id, cu)

      fun equivs_i i =
          let
            val u_equivs = get_equiv (nth cus i)
            fun get_head_equiv_th eq_i =
                (ACUtil.comb_ac_equiv ac_info (nth_map i (K eq_i) refls))
                    |> apply_to_rhs (ACUtil.normalize_all_ac ac_info)
          in
            map (apsnd get_head_equiv_th) u_equivs
          end
    in
      maps equivs_i (0 upto (length cus - 1))
    end

(* Find all ways to write ct, up to a certain limit. *)
fun ac_expand tbl ac_info (id, ct) =
    let
      val {ctxt, ...} = tbl
      val max_ac = Config.get ctxt max_ac

      fun merge_info (id, th) (id', th') =
          (BoxID.merge_boxes ctxt (id, id'), Util.transitive_list [th, th'])

      fun ac_equiv_eq_better (id, th) (id', th') =
          let
            val seq1 = ACUtil.dest_ac ac_info (Util.rhs_of th)
            val seq2 = ACUtil.dest_ac ac_info (Util.rhs_of th')
          in
            is_subseq (op aconv) (seq1, seq2) andalso
            BoxID.is_eq_ancestor ctxt id id'
          end

      fun has_ac_equiv_eq_better infos info' =
          exists (fn info => ac_equiv_eq_better info info') infos

      fun helper (old, new) =
          case new of
              [] => old
            | (id', eq_th) :: rest =>
              if length old + length new > max_ac then
                old @ take (max_ac - length old) new
              else let
                val old' = ((id', eq_th) :: old)
                val rhs_expand =
                    (ac_expand_once tbl ac_info (id, Thm.rhs_of eq_th))
                        |> Util.max_partial ac_equiv_eq_better
                        |> map (merge_info (id', eq_th))
                        |> filter_out (has_ac_equiv_eq_better (old' @ rest))
              in
                helper (old', rest @ rhs_expand)
              end

      (* Start term *)
      val cts = ACUtil.cdest_ac ac_info ct
      val ths = map (RewriteTable.simplify id tbl) cts
      val eq_th = (ACUtil.comb_ac_equiv ac_info ths)
                      |> apply_to_rhs (ACUtil.normalize_all_ac ac_info)
    in
      helper ([], [(id, eq_th)])
    end

fun ac_expand_equiv_fn rtype item1 item2 =
    let
      val (tbl as {ctxt, ...}) = RewriteTable.table_of_rtype rtype
      val {id = id1, tname = tname1, ...} = item1
      val {id = id2, tname = tname2, ...} = item2
      val (ct1, ct2) = (the_single tname1, the_single tname2)
      val (t1, t2) = (Thm.term_of ct1, Thm.term_of ct2)
      val id = BoxID.merge_boxes ctxt (id1, id2)
      val thy = RewriteTable.theory_of tbl
    in
      case ACUtil.get_head_ac_info thy t1 of
          NONE => []
        | SOME ac_info =>
          if not (ACUtil.head_agrees ac_info t2) then []
          else if Term_Ord.termless (t2, t1) then []
          else if RewriteTable.is_equiv id tbl (ct1, ct2) then []
          else let
            val expand1 = ac_expand tbl ac_info (id, ct1)
            val expand2 = ac_expand tbl ac_info (id, ct2)

            fun get_equiv ((id1, eq_th1), (id2, eq_th2)) =
                if Util.rhs_of eq_th1 aconv Util.rhs_of eq_th2 then
                  [(BoxID.merge_boxes ctxt (id1, id2),
                    to_obj_eq (Util.transitive_list [eq_th1, meta_sym eq_th2]))]
                else []
          in
            (maps get_equiv (Util.all_pairs (expand1, expand2)))
                |> Util.max_partial (BoxID.id_is_eq_ancestor ctxt)
                |> RewriteTable.replace_id_for_type' rtype
                |> map (fn (id, th) => Update.thm_update (id, th))
          end
    end

val ac_expand_equiv =
    {name = "ac_expand_equiv",
     args = [TypedMatch (TY_TERM, @{term_pat "?A::?'a"}),
             TypedMatch (TY_TERM, @{term_pat "?B::?'a"})],
     priority = PRIORITY_ADD,
     func = TwoStep ac_expand_equiv_fn}

fun ac_expand_unit_fn rtype item =
    let
      val tbl = RewriteTable.table_of_rtype rtype
      val {id, tname, ...} = item
      val ct = the_single tname
      val t = Thm.term_of ct
      val thy = RewriteTable.theory_of tbl
    in
      case ACUtil.get_head_ac_info thy t of
          NONE => []
        | SOME ac_info =>
          let
            val expand = ac_expand tbl ac_info (id, ct)

            fun process_expand (id', eq_th) =
                if not (ACUtil.head_agrees ac_info (Util.rhs_of eq_th)) then
                  [(id', to_obj_eq eq_th)]
                else []
          in
            (maps process_expand expand)
                |> RewriteTable.replace_id_for_type' rtype
                |> map (fn (id, th) => Update.thm_update (id, th))
          end
    end

val ac_expand_unit =
    {name = "ac_expand_unit",
     args = [TypedMatch (TY_TERM, @{term_pat "?A::?'a"})],
     priority = PRIORITY_ADD,
     func = OneStep ac_expand_unit_fn}

val add_ac_proofsteps =
    fold add_prfstep [
      ac_expand_equiv, ac_expand_unit

    ] #> fold add_fixed_sc [
      ("ac_expand_equiv", 1), ("ac_expand_unit", 1)
    ]

end  (* structure AC_ProofSteps. *)

val _ = Theory.setup AC_ProofSteps.add_ac_proofsteps
