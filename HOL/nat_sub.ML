(* Subtraction on natural numbers. *)

signature NAT_SUB =
sig
  val fheads: term list
  val norm_plus1: wfconv
  val norm_plus': wfconv
  val norm_plus: wfconv
  val norm_minus': wfconv
  val move_outmost: term -> wfconv
  val cancel_terms_step: wfconv
  val cancel_terms: wfconv
  val cancel_const: wfconv
  val norm_minus: wfconv
  val norm_minus_ct: cterm -> cterm list * cterm list * int
  val get_sub_head_equiv: Proof.context -> box_id * cterm -> (box_id * (wfterm * thm)) list
  val nat_sub_expand_once: Proof.context -> box_id * wfterm -> (box_id * (wfterm * thm)) list
  val nat_sub_expand: Proof.context -> box_id * cterm -> (box_id * (wfterm * thm)) list

  val nat_sub_expand_equiv: proofstep
  val nat_sub_expand_unit: proofstep

  val add_nat_sub_proofsteps: theory -> theory
end;

structure NatSub : NAT_SUB =
struct

val fheads = [@{term "(op +) :: (nat => nat => nat)"},
              @{term "(op -) :: (nat => nat => nat)"}]

val plus_info = Nat_Arith.plus_ac_on_typ @{theory} natT
val is_numc = UtilArith.is_numc
val dest_numc = UtilArith.dest_numc
val is_plus = Nat_Arith.is_plus
val is_minus = Nat_Arith.is_minus
val nat_fold_conv = Nat_Arith.nat_fold_conv
val wf_rewr_obj_eq = WfTerm.rewr_obj_eq fheads

(* When comparing atoms, constants are greater than non-constants. *)
fun compare_atom (t1, t2) =
    if is_numc t1 andalso is_numc t2 then EQUAL
    else if is_numc t1 then GREATER
    else if is_numc t2 then LESS
    else Term_Ord.term_ord (t1, t2)

(* Normalize a + b, where a is a sum and b is an atom. If b is a
   constant, add it to the end of a. Otherwise, insert b into sorted
   position.
 *)
fun norm_plus1 wft =
    let
      val (a, b) = wft |> WfTerm.term_of |> Util.dest_binop_args
    in
      if is_plus a then
        case compare_atom (dest_arg a, b) of
            LESS => WfTerm.all_conv wft
          | EQUAL =>
            if is_numc b then
              WfTerm.every_conv [wf_rewr_obj_eq @{thm add_ac(1)},
                                 WfTerm.arg_conv (WfTerm.conv_of nat_fold_conv)] wft
            else WfTerm.all_conv wft
          | GREATER =>
            WfTerm.every_conv [wf_rewr_obj_eq @{thm add_ac(1)},
                               WfTerm.arg_conv (wf_rewr_obj_eq @{thm add_ac(2)}),
                               wf_rewr_obj_eq (obj_sym @{thm add_ac(1)}),
                               WfTerm.arg1_conv norm_plus1] wft
      else
        case compare_atom (a, b) of
            LESS => WfTerm.all_conv wft
          | EQUAL => if is_numc b then WfTerm.conv_of nat_fold_conv wft
                     else WfTerm.all_conv wft
          | GREATER => wf_rewr_obj_eq @{thm add_ac(2)} wft
    end

(* Normalize a + b, where a and b are both sums. *)
fun norm_plus' wft =
    if is_plus (dest_arg (WfTerm.term_of wft)) then
      WfTerm.every_conv [wf_rewr_obj_eq (obj_sym @{thm add_ac(1)}),
                         WfTerm.arg1_conv norm_plus',
                         norm_plus1] wft
    else
      norm_plus1 wft

fun norm_plus ct =
    WfTerm.every_conv [norm_plus',
                       WfTerm.try_conv (wf_rewr_obj_eq @{thm add_0_right})] ct

(* First step, put wft into the form a - b, where a and b are
   normalized sums.
 *)
fun norm_minus' wft =
    let
      val t = WfTerm.term_of wft
    in
      if is_plus t then
        WfTerm.every_conv [WfTerm.binop_conv norm_minus',
                           wf_rewr_obj_eq @{thm nat_sub1},
                           WfTerm.binop_conv norm_plus] wft
      else if is_minus t then
        WfTerm.every_conv [WfTerm.binop_conv norm_minus',
                           wf_rewr_obj_eq @{thm nat_sub2},
                           WfTerm.binop_conv norm_plus] wft
      else
        wf_rewr_obj_eq @{thm nat_sub_norm} wft
    end

fun move_outmost u wft =
    if u aconv (WfTerm.term_of wft) then WfTerm.all_conv wft
    else let
      val t = WfTerm.term_of wft
    in
      if not (is_plus t) then
        raise Fail "move_outmost: u not found in wft."
      else let
        val (a, b) = Util.dest_binop_args t
      in
        if u aconv b then WfTerm.all_conv wft
        else if is_plus a then
          WfTerm.every_conv [
            WfTerm.arg1_conv (move_outmost u),
            wf_rewr_obj_eq @{thm add_ac(1)},
            WfTerm.arg_conv (
              wf_rewr_obj_eq @{thm add_ac(2)}),
            wf_rewr_obj_eq (obj_sym @{thm add_ac(1)})] wft
        else if u aconv a then
          wf_rewr_obj_eq @{thm add_ac(2)} wft
        else
          raise Fail "move_outmost: u not found in wft."
      end
    end

(* Next, cancel identical terms from the two sides. *)
fun cancel_terms_step wft =
    let
      val (ts1, ts2) = wft |> WfTerm.term_of |> Util.dest_binop_args
                           |> apply2 (ACUtil.dest_ac plus_info)
    in
      case filter_out is_numc (inter (op aconv) ts1 ts2) of
          [] => WfTerm.no_conv wft
        | t :: _ =>
          WfTerm.every_conv [
            (* Ensure both sides have at least two terms. *)
            if length ts1 = 1 then
              WfTerm.arg1_conv (
                wf_rewr_obj_eq (obj_sym @{thm add_0_right}))
            else WfTerm.all_conv,

            if length ts2 = 1 then
              WfTerm.arg_conv (
                wf_rewr_obj_eq (obj_sym @{thm add_0_right}))
            else WfTerm.all_conv,

            (* Move t to the right in both terms. *)
            WfTerm.binop_conv (move_outmost t),

            (* Apply the rewrite rule cancelling t. *)
            wf_rewr_obj_eq @{thm nat_sub3}] wft
    end

fun cancel_terms wft =
    WfTerm.repeat_conv cancel_terms_step wft

(* Finally, try to cancel any constants that are present. *)
fun cancel_const wft =
    let
      val (t1, t2) = wft |> WfTerm.term_of |> Util.dest_binop_args
      val c1 = if is_plus t1 then dest_arg t1 else t1
      val c2 = if is_plus t2 then dest_arg t2 else t2
    in
      if is_numc c1 andalso is_numc c2 andalso
         not (c1 aconv Nat_Arith.nat0) andalso not (c2 aconv Nat_Arith.nat0) then
        let
          val (n1, n2) = (dest_numc c1, dest_numc c2)
          val th = if n1 >= n2 then
                     (Nat_Arith.nat_le_th n2 n1) RS @{thm nat_sub4}
                   else
                     (Nat_Arith.nat_le_th n1 n2) RS @{thm nat_sub5}
        in
          WfTerm.every_conv [
            (* If left side is a number, add 0 to the left. *)
            if is_numc t1 then
              WfTerm.arg1_conv (
                wf_rewr_obj_eq (obj_sym @{thm add_0_left}))
            else WfTerm.all_conv,

            (* If right side is a number, add 0 to the right. *)
            if is_numc t2 then
              WfTerm.arg_conv (
                wf_rewr_obj_eq (obj_sym @{thm add_0_left}))
            else WfTerm.all_conv,

            (* Now apply the theorem. *)
            wf_rewr_obj_eq th,

            (* Fold the subtraction and the zero if necessary. Zero at
               right appears when n1 = n2. Zero at left appears when
               both sides are numbers.
             *)
            if n1 >= n2 then
              WfTerm.arg1_conv (
                WfTerm.every_conv [
                  WfTerm.arg_conv (WfTerm.conv_of nat_fold_conv),
                  WfTerm.try_conv (wf_rewr_obj_eq @{thm add_0_left}),
                  WfTerm.try_conv (wf_rewr_obj_eq @{thm add_0_right})])
            else
              WfTerm.arg_conv (
                WfTerm.every_conv [
                  WfTerm.arg_conv (WfTerm.conv_of nat_fold_conv),
                  WfTerm.try_conv (wf_rewr_obj_eq @{thm add_0_left})])
          ] wft
        end
      else WfTerm.all_conv wft
    end

fun norm_minus wft =
    WfTerm.every_conv [
      norm_minus', cancel_terms, cancel_const,
      WfTerm.try_conv (wf_rewr_obj_eq @{thm diff_zero})] wft

(* Fast computation of the expected normalization. Return in two lists
   and a constant.
 *)
fun norm_minus_ct' ct =
    let
      val t = Thm.term_of ct
    in
      if is_plus t then
        let
          val (p1, m1, n1) = norm_minus_ct' (Thm.dest_arg1 ct)
          val (p2, m2, n2) = norm_minus_ct' (Thm.dest_arg ct)
        in
          (p1 @ p2, m1 @ m2, n1 + n2)
        end
      else if is_minus t then
        let
          val (p1, m1, n1) = norm_minus_ct' (Thm.dest_arg1 ct)
          val (p2, m2, n2) = norm_minus_ct' (Thm.dest_arg ct)
        in
          (p1 @ m2, m1 @ p2, n1 - n2)
        end
      else if is_numc t then
        ([], [], dest_numc t)
      else
        ([ct], [], 0)
    end

fun norm_minus_ct ct =
    let
      val (p, m, n) = norm_minus_ct' ct
      val cterm_ord = Term_Ord.term_ord o apply2 Thm.term_of
      val (p'', m'') =
          Util.remove_dup_lists cterm_ord (sort cterm_ord p, sort cterm_ord m)
    in
      (p'', m'', n)
    end

fun subterms_of ct =
    let val (p, m, _) = norm_minus_ct ct in p @ m end

(* Obtain head equivalences of cu, normalized to a - b form, and where
   each term is simplified.
 *)
fun get_sub_head_equiv ctxt (id, ct) =
    let
      fun process_wf_head_equiv (id', (wft, eq_th)) =
          let
            val cts = subterms_of (Thm.rhs_of eq_th)
            val simps = WellformData.simplify ctxt fheads cts (id', wft)

            fun process_simp (id'', (wft', eq_th')) =
                (BoxID.merge_boxes ctxt (id', id''),
                 (wft', Util.transitive_list [eq_th, eq_th']))
          in
            map process_simp simps
          end
    in
      (id, ct) |> WellformData.get_head_equiv ctxt fheads
               |> maps process_wf_head_equiv
               |> filter_out (Thm.is_reflexive o snd o snd)
    end

(* Given wft in normalized form a - b, expand one of the subterms
   once. Calls the corresponding function in ac_steps on a and b, then
   combine the results.
 *)
fun nat_sub_expand_once ctxt (id, wft) =
    let
      val ct = WfTerm.cterm_of wft
      val subt = subterms_of ct
      fun get_equiv cu = get_sub_head_equiv ctxt (id, cu)

      fun process_info (id', wf_eq) =
          (id', WfTerm.rewrite_on_eqs fheads [wf_eq] wft)
    in
      map process_info (maps get_equiv subt)
    end

(* Find all ways to write ct, up to a certain limit. *)
fun nat_sub_expand ctxt (id, ct) =
    let
      val max_ac = Config.get ctxt AC_ProofSteps.max_ac

      fun ac_equiv_eq_better (id, (_, th)) (id', (_, th')) =
          let
            val (p1, _, _) = norm_minus_ct (Thm.rhs_of th)
            val (p2, _, _) = norm_minus_ct (Thm.rhs_of th')
          in
            Util.is_subseq (op aconvc) (p1, p2) andalso
            BoxID.is_eq_ancestor ctxt id id'
          end

      fun has_ac_equiv_eq_better infos info' =
          exists (fn info => ac_equiv_eq_better info info') infos

      fun helper (old, new) =
          case new of
              [] => old
            | (id', (wft, eq_th)) :: rest =>
              if length old + length new > max_ac then
                old @ take (max_ac - length old) new
              else let
                val old' = ((id', (wft, eq_th)) :: old)

                fun merge_info (id'', (wft', eq_th')) =
                    (BoxID.merge_boxes ctxt (id', id''),
                     (wft', Util.transitive_list [eq_th, eq_th']))

                val rhs_expand =
                    (nat_sub_expand_once ctxt (id', wft))
                        |> Util.max_partial ac_equiv_eq_better
                        |> map merge_info
                        |> filter_out (has_ac_equiv_eq_better (old' @ rest))
              in
                helper (old', rest @ rhs_expand)
              end

      (* Start term *)
      val ts = subterms_of ct
      val start = (WellformData.cterm_to_wfterm ctxt fheads (id, ct))
                      |> maps (WellformData.simplify ctxt fheads ts)
    in
      helper ([], start)
    end

fun is_nat_sub_form t =
    if is_plus t orelse is_minus t then fastype_of (dest_arg t) = natT
    else false

fun nat_sub_expand_equiv_fn ictxt item1 item2 =
    let
      val ctxt = IncrContext.context_of ictxt
      val {id = id1, tname = tname1, ...} = item1
      val {id = id2, tname = tname2, ...} = item2
      val (ct1, ct2) = (the_single tname1, the_single tname2)
      val (t1, t2) = (Thm.term_of ct1, Thm.term_of ct2)
      val id = BoxID.merge_boxes ctxt (id1, id2)
    in
      if not (is_nat_sub_form t1) orelse not (is_nat_sub_form t2) then []
      else if Term_Ord.termless (t2, t1) then []
      else if RewriteTable.is_equiv id ctxt (ct1, ct2) then []
      else let
        val expand1 = nat_sub_expand ctxt (id, ct1)
        val expand2 = nat_sub_expand ctxt (id, ct2)

        fun get_equiv ((id1, (wft1, eq_th1)), (id2, (wft2, eq_th2))) =
            let
              val ct1 = Thm.rhs_of eq_th1
              val ct2 = Thm.rhs_of eq_th2
              val (p1, m1, n1) = norm_minus_ct ct1
              val (p2, m2, n2) = norm_minus_ct ct2
            in
              if eq_list (op aconvc) (p1, p2) andalso
                 eq_list (op aconvc) (m1, m2) andalso n1 = n2 then
                let
                  val (wft1', eq1) = norm_minus wft1
                  val (wft2', eq2) = norm_minus wft2
                  val _ = assert (WfTerm.term_of wft1' aconv WfTerm.term_of wft2')
                                 "nat_sub_expand_equiv_fn"
                  val id' = BoxID.merge_boxes ctxt (id1, id2)
                  val eq = Util.transitive_list [
                        eq_th1, eq1, meta_sym eq2, meta_sym eq_th2]
                in
                  [(id', to_obj_eq eq)]
                end
              else []
            end
      in
        (maps get_equiv (Util.all_pairs (expand1, expand2)))
            |> Util.max_partial (BoxID.id_is_eq_ancestor ctxt)
            |> IncrContext.replace_id_for_type' ictxt
            |> map (fn (id, th) => Update.thm_update (id, th))
      end
    end

val nat_sub_expand_equiv =
    {name = "nat_sub_expand_equiv",
     args = [TypedMatch (TY_TERM, @{term_pat "?A::nat"}),
             TypedMatch (TY_TERM, @{term_pat "?B::nat"})],
     priority = PRIORITY_ADD,
     func = TwoStep nat_sub_expand_equiv_fn}

fun nat_sub_expand_unit_fn ictxt item =
    let
      val ctxt = IncrContext.context_of ictxt
      val {id, tname, ...} = item
      val ct = the_single tname
      val t = Thm.term_of ct
    in
      if not (is_nat_sub_form t) then []
      else let
        val expand = nat_sub_expand ctxt (id, ct)

        fun process_expand (id', (wft, eq_th)) =
            let
              val ct = Thm.rhs_of eq_th
              val (p, m, n) = norm_minus_ct ct
            in
              if length p + length m + (if n = 0 then 0 else 1) <= 1 then
                let
                  val (_, eq') = norm_minus wft
                  val eq = Util.transitive_list [eq_th, eq']
                in
                  [(id', to_obj_eq eq)]
                end
              else []
            end
      in
        (maps process_expand expand)
            |> IncrContext.replace_id_for_type' ictxt
            |> map (fn (id, th) => Update.thm_update (id, th))
      end
    end

val nat_sub_expand_unit =
    {name = "nat_sub_expand_unit",
     args = [TypedMatch (TY_TERM, @{term_pat "?A::nat"})],
     priority = PRIORITY_ADD,
     func = OneStep nat_sub_expand_unit_fn}

val add_nat_sub_proofsteps =
    fold add_prfstep [
      nat_sub_expand_equiv, nat_sub_expand_unit

    ] #> fold add_fixed_sc [
      ("nat_sub_expand_equiv", 1), ("nat_sub_expand_unit", 1)
    ]

end  (* NatSub *)

val _ = Theory.setup NatSub.add_nat_sub_proofsteps
