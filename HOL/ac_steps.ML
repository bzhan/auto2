(* Proof steps related to AC relations. *)

signature AC_PROOFSTEPS =
sig
  val max_ac: int Config.T
  val simp_ac_expr: Proof.context -> ac_info -> box_id * cterm -> (box_id * thm) list
  val get_ac_head_equiv:
      Proof.context -> ac_info -> box_id * cterm -> (box_id * thm) list
  val ac_expand_once:
      Proof.context -> ac_info -> box_id * cterm -> (box_id * thm) list
  val ac_expand:
      Proof.context -> ac_info -> box_id * cterm -> (box_id * thm) list
  val ac_expand_equiv: proofstep
  val ac_expand_unit: proofstep

  val add_ac_proofsteps: theory -> theory
end;

structure AC_ProofSteps : AC_PROOFSTEPS =
struct

val max_ac = Attrib.setup_config_int @{binding "max_ac"} (K 20)

(* Simplify each term of the AC expression. *)
fun simp_ac_expr ctxt ac_info (id, cu) =
    let
      val cus = ACUtil.cdest_ac ac_info cu
    in
      if null id then [(id, Thm.reflexive cu)] else
      cus |> map (RewriteTable.simplify_info ctxt)
          |> BoxID.get_all_merges_info ctxt
          |> map (apsnd (ACUtil.comb_ac_equiv ac_info))
    end

(* Obtain head equivalences of cu, where each term is simplified. *)
fun get_ac_head_equiv ctxt ac_info (id, cu) =
    let
      fun process_head_equiv (id', eq_th) =
          let
            val infos = simp_ac_expr ctxt ac_info (id', Thm.rhs_of eq_th)
          in
            map (BoxID.merge_eq_infos ctxt (id', eq_th)) infos
          end
    in
      cu |> RewriteTable.get_head_equiv ctxt
         |> maps snd
         |> BoxID.merge_box_with_info ctxt id
         |> maps process_head_equiv
         |> filter_out (Thm.is_reflexive o snd)
    end

(* Find ways to modify ct once by rewriting one of the subterms. *)
fun ac_expand_once ctxt ac_info (id, ct) =
    let
      val cus = ACUtil.cdest_ac ac_info ct
      val refls = map Thm.reflexive cus
      fun get_equiv cu = get_ac_head_equiv ctxt ac_info (id, cu)

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
fun ac_expand ctxt ac_info (id, ct) =
    let
      val max_ac = Config.get ctxt max_ac

      fun ac_equiv_eq_better (id, th) (id', th') =
          let
            val seq1 = ACUtil.dest_ac ac_info (Util.rhs_of th)
            val seq2 = ACUtil.dest_ac ac_info (Util.rhs_of th')
          in
            Util.is_subseq (op aconv) (seq1, seq2) andalso
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
                    (ac_expand_once ctxt ac_info (id', Thm.rhs_of eq_th))
                        |> Util.max_partial ac_equiv_eq_better
                        |> map (BoxID.merge_eq_infos ctxt (id', eq_th))
                        |> filter_out (has_ac_equiv_eq_better (old' @ rest))
              in
                helper (old', rest @ rhs_expand)
              end

      (* Start term *)
      val cts = ACUtil.cdest_ac ac_info ct
      val ths = map (RewriteTable.simplify id ctxt) cts
      val eq_th = (ACUtil.comb_ac_equiv ac_info ths)
                      |> apply_to_rhs (ACUtil.normalize_all_ac ac_info)
    in
      helper ([], [(id, eq_th)])
    end

fun ac_expand_equiv_fn ictxt item1 item2 =
    let
      val ctxt = IncrContext.context_of ictxt
      val thy = Proof_Context.theory_of ctxt
      val {id = id1, tname = tname1, ...} = item1
      val {id = id2, tname = tname2, ...} = item2
      val (ct1, ct2) = (the_single tname1, the_single tname2)
      val (t1, t2) = (Thm.term_of ct1, Thm.term_of ct2)
      val id = BoxID.merge_boxes ctxt (id1, id2)
    in
      case ACUtil.get_head_ac_info thy t1 of
          NONE => []
        | SOME ac_info =>
          if not (ACUtil.head_agrees ac_info t2) then []
          else if Term_Ord.termless (t2, t1) then []
          else if RewriteTable.is_equiv id ctxt (ct1, ct2) then []
          else let
            val expand1 = ac_expand ctxt ac_info (id, ct1)
            val expand2 = ac_expand ctxt ac_info (id, ct2)

            fun get_equiv ((id1, eq_th1), (id2, eq_th2)) =
                if Util.rhs_of eq_th1 aconv Util.rhs_of eq_th2 then
                  [(BoxID.merge_boxes ctxt (id1, id2),
                    to_obj_eq (Util.transitive_list [eq_th1, meta_sym eq_th2]))]
                else []
          in
            (maps get_equiv (Util.all_pairs (expand1, expand2)))
                |> Util.max_partial (BoxID.id_is_eq_ancestor ctxt)
                |> IncrContext.replace_id_for_type' ictxt
                |> map (fn (id, th) => Update.thm_update (id, th))
          end
    end

val ac_expand_equiv =
    {name = "ac_expand_equiv",
     args = [TypedMatch (TY_TERM, @{term_pat "?A::?'a"}),
             TypedMatch (TY_TERM, @{term_pat "?B::?'a"})],
     priority = PRIORITY_ADD,
     func = TwoStep ac_expand_equiv_fn}

fun ac_expand_unit_fn ictxt item =
    let
      val ctxt = IncrContext.context_of ictxt
      val thy = Proof_Context.theory_of ctxt
      val {id, tname, ...} = item
      val ct = the_single tname
      val t = Thm.term_of ct
    in
      case ACUtil.get_head_ac_info thy t of
          NONE => []
        | SOME ac_info =>
          let
            val expand = ac_expand ctxt ac_info (id, ct)

            fun process_expand (id', eq_th) =
                if not (ACUtil.head_agrees ac_info (Util.rhs_of eq_th)) then
                  [(id', to_obj_eq eq_th)]
                else []
          in
            (maps process_expand expand)
                |> IncrContext.replace_id_for_type' ictxt
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
