signature UTIL_ARITH =
sig
  (* Types. *)
  val natT: typ
  val intT: typ
  val ratT: typ
  val rat_zero: Rat.rat

  (* Terms. *)
  val dest_numc: term -> int
  val dest_numc_rat: term -> Rat.rat
  val is_order: term -> bool
  val is_linorder: Proof.context -> term -> bool

  (* Theorems. *)
  val neg_ineq_cv: conv
  val neg_ineq_back_cv: conv

  (* Arith tactic. *)
  val prove_by_arith: Proof.context -> thm list -> term -> thm
  val contra_by_arith: Proof.context -> thm list -> thm
end;

structure UtilArith : UTIL_ARITH =
struct

val natT = HOLogic.natT
val intT = @{typ int}
val ratT = @{typ rat}
val rat_zero = Rat.of_int 0

(* Deconstruct numerical constant. Discard type. *)
fun dest_numc t = HOLogic.dest_number t |> snd
                  handle TERM ("dest_number", _) =>
                         raise AUTO2 "dest_numc: invalid term."

(* Rational numbers version of dest_numc. *)
fun dest_numc_rat t =
    case t of
        Const (@{const_name inverse}, _) $ t' =>
        let
          val r' = dest_numc_rat t'
        in
          if r' = rat_zero then rat_zero
          else Rat.inv r'
        end
      | Const (@{const_name uminus}, _) $ t' => Rat.neg (dest_numc_rat t')
      | Const (@{const_name of_rat}, _) $ r => dest_numc_rat r
      | Const (@{const_name Fract}, _) $ n $ d =>
        Rat.make (dest_numc n, dest_numc d)
      | _ => Rat.of_int (dest_numc t)

(* Whether the given term is a < b or a <= b. *)
fun is_order t =
    let
      val _ = assert (fastype_of t = boolT) "is_order: wrong type"
    in
      case t of Const (@{const_name less}, _) $ _ $ _ => true
              | Const (@{const_name less_eq}, _) $ _ $ _ => true
              | _ => false
    end

fun is_linorder ctxt t =
    is_order t andalso Sign.of_sort (Proof_Context.theory_of ctxt)
                                    (get_arg_type t, ["Orderings.linorder"])

(* Convert ~ x < y to y <= x, and ~ x <= y to y < x. *)
val neg_ineq_cv =
    (Conv.try_conv o Conv.first_conv)
        (map rewr_obj_eq [@{thm Orderings.linorder_not_less},
                          @{thm Orderings.linorder_not_le}])

(* Convert x < y to ~ y <= x, and x <= y to ~ y < x. *)
val neg_ineq_back_cv =
    (Conv.try_conv o Conv.first_conv)
        (map (rewr_obj_eq o obj_sym) [@{thm Orderings.linorder_not_less},
                                      @{thm Orderings.linorder_not_le}])

val prove_by_arith = prove_by_tac Arith_Data.arith_tac
val contra_by_arith = contra_by_tac Arith_Data.arith_tac

end  (* structure UtilArith *)

open UtilArith
