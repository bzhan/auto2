(* Subtraction on natural numbers. *)

signature NAT_SUB =
sig
  val fheads: term list
  val norm_plus1: conv
  val norm_plus: conv
  val norm_minus': wfconv
  val cancel_terms: wfconv
  val cancel_const: wfconv
  val norm_minus: wfconv
end;

structure NatSub : NAT_SUB =
struct

val fheads = [@{term "(op +) :: (nat => nat => nat)"},
              @{term "(op -) :: (nat => nat => nat)"}]

val plus_info = Nat_Arith.plus_ac_on_typ @{theory} natT
val is_numc = UtilArith.is_numc
val dest_numc = UtilArith.dest_numc
val nat0 = Nat_Arith.nat0
val is_plus = Nat_Arith.is_plus
val nat_fold_conv = Nat_Arith.nat_fold_conv

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
fun norm_plus1 ct =
    let
      val (a, b) = ct |> Thm.term_of |> Util.dest_binop_args
    in
      if is_plus a then
        case compare_atom (dest_arg a, b) of
            LESS => Conv.all_conv ct
          | EQUAL =>
            if is_numc b then
              Conv.every_conv [rewr_obj_eq @{thm add_ac(1)},
                               Conv.arg_conv nat_fold_conv] ct
            else Conv.all_conv ct
          | GREATER =>
            Conv.every_conv [rewr_obj_eq @{thm add_ac(1)},
                             Conv.arg_conv (rewr_obj_eq @{thm add_ac(2)}),
                             rewr_obj_eq (obj_sym @{thm add_ac(1)}),
                             Conv.arg1_conv norm_plus1] ct
      else
        case compare_atom (a, b) of
            LESS => Conv.all_conv ct
          | EQUAL => if is_numc b then nat_fold_conv ct
                     else Conv.all_conv ct
          | GREATER => rewr_obj_eq @{thm add_ac(2)} ct
    end

(* Normalize a + b, where a and b are both sums. *)
fun norm_plus' ct =
    if is_plus (dest_arg (Thm.term_of ct)) then
      Conv.every_conv [rewr_obj_eq (obj_sym @{thm add_ac(1)}),
                       Conv.arg1_conv norm_plus1,
                       norm_plus'] ct
    else
      norm_plus1 ct

fun norm_plus ct =
    Conv.every_conv [norm_plus',
                     Conv.try_conv (rewr_obj_eq @{thm add_0_right})] ct

fun conv_of cv wft =
    let
      val ct = WfTerm.cterm_of wft
      val eq_th = cv ct
    in
      (WfTerm (Thm.rhs_of eq_th), eq_th)
    end

(* First step, put wft into the form a - b, where a and b are
   normalized sums.
 *)
fun norm_minus' wft =
    let
      val t = WfTerm.term_of wft
    in
      if is_plus t then
        WfTerm.every_conv [WfTerm.binop_conv norm_minus',
                           WfTerm.rewr_obj_eq fheads @{thm nat_sub1},
                           WfTerm.binop_conv (conv_of norm_plus)] wft
      else if Nat_Arith.is_minus t then
        WfTerm.every_conv [WfTerm.binop_conv norm_minus',
                           WfTerm.rewr_obj_eq fheads @{thm nat_sub2},
                           WfTerm.binop_conv (conv_of norm_plus)] wft
      else
        WfTerm.rewr_obj_eq fheads @{thm nat_sub_norm} wft
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
            if length ts1 = 1 then
              WfTerm.arg1_conv (
                conv_of (rewr_obj_eq (obj_sym @{thm add_0_right})))
            else WfTerm.all_conv,
            if length ts2 = 1 then
              WfTerm.arg_conv (
                conv_of (rewr_obj_eq (obj_sym @{thm add_0_right})))
            else WfTerm.all_conv,
            WfTerm.binop_conv (conv_of (ACUtil.move_outmost plus_info t)),
            WfTerm.rewr_obj_eq fheads @{thm nat_sub3}] wft
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
         not (c1 aconv nat0) andalso not (c2 aconv nat0) then
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
                conv_of (rewr_obj_eq (obj_sym @{thm add_0_left})))
            else WfTerm.all_conv,

            (* If right side is a number, add 0 to the right. *)
            if is_numc t2 then
              WfTerm.arg_conv (
                conv_of (rewr_obj_eq (obj_sym @{thm add_0_left})))
            else WfTerm.all_conv,

            (* Now apply the theorem. *)
            WfTerm.rewr_obj_eq fheads th,

            (* Fold the subtraction and the zero if necessary. Zero at
               right appears when n1 = n2. Zero at left appears when
               both sides are numbers.
             *)
            if n1 >= n2 then
              WfTerm.arg1_conv (
                conv_of (
                  Conv.every_conv [
                    Conv.arg_conv nat_fold_conv,
                    Conv.try_conv (rewr_obj_eq @{thm add_0_left}),
                    Conv.try_conv (rewr_obj_eq @{thm add_0_right})]))
            else
              WfTerm.arg_conv (WfTerm.arg_conv (conv_of nat_fold_conv))] wft
        end
      else WfTerm.all_conv wft
    end

fun norm_minus wft =
    WfTerm.every_conv [norm_minus', cancel_terms, cancel_const] wft

end  (* NatSub *)
