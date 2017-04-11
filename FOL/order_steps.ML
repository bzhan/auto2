(* Proof steps on ordering *)

signature ORDER_STEPS =
sig
  datatype ord_type = LE | LT | NOT_LE | NOT_LT
  val dest_order_t: term -> (ord_type * term * term * term) option
  val is_pos_order: term -> bool
  val is_neg_order: term -> bool
  val neg_ineq_to_pos: term -> term
  val pos_ineq_to_neg_th: thm * ord_type * thm -> thm
  val add_order_proofsteps: theory -> theory
end;

structure OrderSteps : ORDER_STEPS =
struct

val setT = @{typ "i"}
val le_t = Const (@{const_name le}, setT --> setT --> setT --> boolT)
val less_t = Const (@{const_name less}, setT --> setT --> setT --> boolT)

datatype ord_type = LE | LT | NOT_LE | NOT_LT

fun dest_order_t pat =
    case pat of
        Const (@{const_name le}, _) $ G $ a $ b => SOME (LE, G, a, b)
      | Const (@{const_name less}, _) $ G $ a $ b => SOME (LT, G, a, b)
      | Const (@{const_name Not}, _) $ (
          Const (@{const_name le}, _) $ G $ a $ b) => SOME (NOT_LE, G, a, b)
      | Const (@{const_name Not}, _) $ (
          Const (@{const_name less}, _) $ G $ a $ b) => SOME (NOT_LT, G, a, b)
      | _ => NONE

fun is_pos_order t =
    case dest_order_t t of
        NONE => false
      | SOME (ty, _, _, _) => ty = LE orelse ty = LT

fun is_neg_order t =
    case dest_order_t t of
        NONE => false
      | SOME (ty, _, _, _) => ty = NOT_LE orelse ty = NOT_LT

fun neg_ineq_to_pos t =
    case dest_not t of
        Const (@{const_name le}, _) $ G $ a $ b => less_t $ G $ b $ a
      | Const (@{const_name less}, _) $ G $ a $ b => le_t $ G $ b $ a
      | _ => raise AUTO2 "neg_ineq_to_pos"

fun pos_ineq_to_neg_th (order_th, order_type, th) =
    if order_type = NOT_LE then [order_th, th] MRS @{thm order_less_to_neg}
    else [order_th, th] MRS @{thm order_le_to_neg}

val neg_order_matcher =
    let
      fun pre_match pat {tname, ...} tbl =
          is_neg_order pat andalso
          is_pos_order (Thm.term_of (the_single tname)) andalso
          Matcher.pre_match tbl (neg_ineq_to_pos pat, the_single tname)

      fun match pat {tname, prop, ...} tbl (id, inst) =
          if not (is_neg_order pat) then []
          else if not (is_pos_order (Thm.term_of (the_single tname))) then []
          else let
            val pat' = neg_ineq_to_pos pat
            val ct = the_single tname
            val insts' = Matcher.rewrite_match tbl (pat', ct) (id, inst)
            fun process_inst ((id', inst'), eq_th) =
                let
                  val pat_inst = subst_term_norm inst' pat
                  val (order_type, G, _, _) = the (dest_order_t pat_inst)
                  val prop' =
                      Thm.equal_elim (make_trueprop_eq (meta_sym eq_th)) prop
                  val order_t = @{term order} $ G
                  val order_ths = RewriteTable.get_property_t tbl (id', order_t)

                  fun process_order_th (id'', order_th) =
                      ((id'', inst'),
                       pos_ineq_to_neg_th (order_th, order_type, prop'))
                in
                  map process_order_th order_ths
                end
          in
            maps process_inst insts'
          end
    in
      {pre_match = pre_match, match = match}
    end

val add_order_proofsteps =
    fold ItemIO.add_prop_matcher [
      (TY_PROP, neg_order_matcher)

    ] #> fold add_gen_prfstep [
      ("shadow_not_le",
       [WithProperty @{term_pat "order(?R)"},
        WithFact @{term_pat "less(?R,?x,?y)"},
        WithFact @{term_pat "Not(le(?R,?y,?x))"}, ShadowSecond]),

      ("shadow_not_less",
       [WithProperty @{term_pat "order(?R)"},
        WithFact @{term_pat "le(?R,?x,?y)"},
        WithFact @{term_pat "Not(less(?R,?y,?x))"}, ShadowSecond])
    ]

end  (* OrderSteps *)

val _ = Theory.setup OrderSteps.add_order_proofsteps
