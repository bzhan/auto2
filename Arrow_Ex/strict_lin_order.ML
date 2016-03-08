(* Strict linear order. *)

val TY_STRICT_LINORDER = "STRICT_LINORDER"

signature STRICT_LINORDER =
sig
  val strict_linorder_th: thm * thm -> thm
  val strict_linorder_updt: box_id * (thm * thm) -> Update.raw_update list
  val strict_linorder_typed_matcher: item_matcher
  val to_strict_linorder_prfstep: proofstep
  val to_neg_strict_linorder_prfstep: proofstep
  val trans_strict_linorder_prfstep: proofstep
  val irrefl_strict_linorder_prfstep: proofstep
  val notin_strict_linorder_prfstep: proofstep

  val add_strict_linorder_proofsteps: theory -> theory
end;

structure Strict_Linorder : STRICT_LINORDER =
struct

fun strict_linorder_th (th_order, th_L) =
    let
      val L1 =
          case prop_of' th_order of
              Const ("Set.member", _) $ _ $ L => L
            | Const ("HOL.Not", _) $ (Const ("Set.member", _) $ _ $ L) => L
            | _ => raise AUTO2 "strict_linorder_th: wrong form of th_order"
      val L2 =
          case prop_of' th_L of
              Const (@{const_name strict_linear_order_on}, _) $
                    Const (@{const_name top}, _) $ L => L
            | _ => raise AUTO2 "strict_linorder_th: wrong form of th_L"
    in
      if L1 aconv L2 then [th_order, th_L] MRS @{thm conjI}
      else raise AUTO2 "L in th_order and th_L do not match"
    end

(* th_order is of form either (x, y) : L or (x, y) ~: L, and th_L is
   of form strict_linear_order L. Form the ritem, where tname is the
   statement of th_order, and theorem is th_order & th_L.
 *)
fun strict_linorder_updt (id, (th_order, th_L)) =
    let
      val ritem = Fact (TY_STRICT_LINORDER, prop_of' th_order,
                        strict_linorder_th (th_order, th_L))
    in
      [Update.AddItems {id = id, raw_items = [ritem]}]
    end

(* pat is either of form (x, y) : L or (x, y) ~: L, where x, y, L are
   patterns. Match pat against tname.
 *)
val strict_linorder_typed_matcher =
    let
      fun pre_match pat {id, tname, ...} tbl =
          length (fo_table_match id tbl (pat, tname)) > 0

      fun mem_conv (eq_t, eq_L) =
          (Conv.arg1_conv (Conv.rewr_conv (meta_sym eq_t)))
              then_conv (Conv.arg_conv (Conv.rewr_conv (meta_sym eq_L)))

      fun L_conv eq_L = Conv.arg_conv (Conv.rewr_conv (meta_sym eq_L))

      fun match pat {tname, prop, ...} tbl (id, inst) =
          let
            val (neg, (p, pL)) =
                case pat of
                    Const ("Set.member", _) $ p $ pL => (false, (p, pL))
                  | Const ("HOL.Not", _) $ (Const ("Set.member", _) $ p $ pL) =>
                    (true, (p, pL))
                  | _ => raise AUTO2
                               "strict_linorder_typed_matcher: wrong pattern"
          in
            if neg <> is_neg tname then []
            else let
              val (t, L) =
                  if neg then
                    tname |> get_neg |> Term.strip_comb |> snd |> the_pair
                  else
                    tname |> Term.strip_comb |> snd |> the_pair
              val insts' =
                  RewriteTable.fo_rewrite_match_list
                      tbl [(false, (p, t)), (false, (pL, L))] (id, inst)
              fun process_inst (inst, eq_ths) =
                  let
                    val (eq_t, eq_L) = the_pair eq_ths
                    val (th_order, th_L) = prop |> split_conj_th |> the_pair
                    val th_order_cv =
                        if neg then Conv.arg_conv (mem_conv (eq_t, eq_L))
                        else mem_conv (eq_t, eq_L)
                    val th_order' = apply_to_thm (
                          HOLogic.Trueprop_conv (th_order_cv)) th_order
                    val th_L' = apply_to_thm (
                          HOLogic.Trueprop_conv (L_conv eq_L)) th_L
                  in
                    [(inst, strict_linorder_th (th_order', th_L'))]
                  end
              in
                maps process_inst insts'
              end
          end
    in
      {pre_match = pre_match, match = match}
    end

val to_strict_linorder_prfstep =
    prfstep_custom
        "to_strict_linorder"
        [WithItem (TY_PROP, @{term_pat "(?x, ?y) : ?L"}),
         WithFact @{term_pat "strict_linear_order ?L"}]
        [Update.ADD_ITEMS]
        (fn ((id, _), ths) => fn _ => fn _ =>
            strict_linorder_updt (id, (hd ths, nth ths 1)))

val to_neg_strict_linorder_prfstep =
    prfstep_custom
        "to_neg_strict_linorder"
        [WithItem (TY_PROP, @{term_pat "(?x, ?y) ~: ?L"}),
         WithFact @{term_pat "strict_linear_order ?L"}]
        [Update.ADD_ITEMS]
        (fn ((id, _), ths) => fn _ => fn _ =>
            strict_linorder_updt (id, (hd ths, nth ths 1)))

val trans_strict_linorder_prfstep =
    prfstep_custom
        "strict_linorder_transitive"
        [WithItem (TY_STRICT_LINORDER, @{term_pat "(?x, ?y) : ?L"}),
         WithItem (TY_STRICT_LINORDER, @{term_pat "(?y, ?z) : ?L"})]
        [Update.ADD_ITEMS]
        (fn ((id, _), ths) => fn _ => fn _ =>
            let
              val (th1, th2) = the_pair ths
              val (th1', th2') = (conj_left_th th1, conj_left_th th2)
              val th_L = conj_right_th th1
              val th_trans = [th_L, th1', th2'] MRS @{thm trans_strict_linorder}
            in
              [Update.thm_update (id, th_trans)]
            end)

val irrefl_strict_linorder_prfstep =
    prfstep_custom
        "strict_linorder_irrefl"
        [WithItem (TY_STRICT_LINORDER, @{term_pat "(?x, ?x) : ?L"})]
        [Update.RESOLVE_BOX]
        (fn ((id, _), ths) => fn _ => fn _ =>
            let
              val th = the_single ths
              val (th_order, th_L) = (conj_left_th th, conj_right_th th)
            in
              [Update.thm_update (
                  id, [th_L, th_order] MRS @{thm irrefl_strict_linorder})]
            end)

val notin_strict_linorder_prfstep =
    prfstep_custom
        "strict_linorder_notin"
        [WithItem (TY_STRICT_LINORDER, @{term_pat "(?x, ?y) ~: ?L"}),
         WithFact @{term_pat "?x ~= ?y"}]
        [Update.ADD_ITEMS]
        (fn ((id, _), ths) => fn _ => fn _ =>
            let
              val (th1, neq_th) = the_pair ths
              val (th_order, th_L) = (conj_left_th th1, conj_right_th th1)
              val eq_th = [th_L, neq_th] MRS @{thm notin_strict_linorder}
              val th_order' =
                  Thm.equal_elim (make_trueprop_eq (to_meta_eq eq_th)) th_order
            in
              [Update.thm_update (id, th_order')]
            end)

val add_strict_linorder_proofsteps =
    ItemIO_Data.add_item_type (
      TY_STRICT_LINORDER, NONE

    ) #> ItemIO_Data.add_typed_matcher (
      TY_STRICT_LINORDER, strict_linorder_typed_matcher

    ) #> fold add_prfstep [
      to_strict_linorder_prfstep, to_neg_strict_linorder_prfstep,
      trans_strict_linorder_prfstep, irrefl_strict_linorder_prfstep,
      notin_strict_linorder_prfstep
    ]

end

val _ = Theory.setup (Strict_Linorder.add_strict_linorder_proofsteps)
