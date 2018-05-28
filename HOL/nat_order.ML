(* Difference logic on natural numbers. *)

type ineq_info = term * term * int

signature NAT_ORDER =
sig
  val eq_info: (box_id * thm) * (box_id * thm) -> bool

  val is_plus_const: term -> bool
  val is_minus_const: term -> bool
  val is_standard_ineq: term -> bool
  val dest_ineq: term -> ineq_info
  val dest_ineq_th: thm -> ineq_info
  val is_refl_ineq: thm -> bool
  val ineq_to_contradiction: thm -> thm
  val combine_ineqs: thm -> thm -> thm

  val norm_ineq_th': thm -> thm
  val convert_const_x: thm -> thm
  val convert_const_y: thm -> thm
  val norm_ineq_th: thm -> thm
  val norm_ineq_minus_th': thm -> thm option
  val norm_ineq_minus_th: thm -> thm option
end;

structure NatOrder : NAT_ORDER =
struct

(* Compare two infos. *)
fun eq_info ((id, th), (id', th')) =
    id = id' andalso Thm.eq_thm_prop (th, th')

(* Check whether t is in the form a + n, where n is a constant. *)
fun is_plus_const t =
    UtilArith.is_plus t andalso UtilArith.is_numc (dest_arg t)

(* Check whether t is in the form a - n, where n is a constant. *)
fun is_minus_const t =
    UtilArith.is_minus t andalso UtilArith.is_numc (dest_arg t)

(* Check whether t is in the form a <= b (boolean value). *)
fun is_less_eq t =
    case t of
        Const (@{const_name less_eq}, _) $ lhs $ _ => fastype_of lhs = natT
      | _ => false

(* Check whether t is in the form a < b (boolean value). *)
fun is_less t =
    case t of
        Const (@{const_name less}, _) $ lhs $ _ => fastype_of lhs = natT
      | _ => false

(* Check whether t is an inequality in the standard form. In this
   form, t is in the form a <= b, where a and b are natural numbers,
   and at least one of them is in the form x + n, where n is a
   constant.
 *)
fun is_standard_ineq t =
    if is_less_eq t then
      let
        val (lhs, rhs) = Util.dest_binop_args t
      in
        fastype_of lhs = natT andalso
        ((is_plus_const lhs andalso not (is_plus_const rhs) andalso
          UtilArith.dest_numc (dest_arg lhs) > 0) orelse
         (is_plus_const rhs andalso not (is_plus_const lhs)))
      end
    else false

(* Assume t is in the form x + n <= y or x <= y + n, deconstruct into
   the triple (x, y, d), where d = -n in the first case and n in the
   second case.
 *)
fun dest_ineq t =
    let
      val _ = assert (is_standard_ineq t) "dest_ineq"
      val (lhs, rhs) = Util.dest_binop_args t
    in
      if is_plus_const lhs then
        (dest_arg1 lhs, rhs, ~ (UtilArith.dest_numc (dest_arg lhs)))
      else
        (lhs, dest_arg1 rhs, UtilArith.dest_numc (dest_arg rhs))
    end

fun dest_ineq_th th =
    if UtilLogic.is_Trueprop (Thm.prop_of th) andalso
       is_standard_ineq (prop_of' th) then
      dest_ineq (prop_of' th)
    else let
      val _ = trace_thm_global "th:" th
    in
      raise Fail "dest_ineq_th"
    end

(* Whether the given theorem is x + n <= x or x <= x + n (either a
   contradiction or is trivial).
 *)
fun is_refl_ineq th =
    let
      val (x, y, _) = dest_ineq_th th
    in
      x aconv y
    end

(* Given an inequality of the form x + n <= x, where n > 0, return the
   theorem False.
 *)
fun ineq_to_contradiction th =
    let
      val (_, _, d) = dest_ineq_th th
      val _ = assert (d < 0) "ineq_to_contradiction"
    in
      [Nat_Util.nat_less_th 0 (~d), th] MRS @{thm single_resolve}
    end

(* In expression x + n < y, fold n. *)
val fold_const_left =
    apply_to_thm' (Conv.arg1_conv (Conv.arg_conv Nat_Util.nat_fold_conv))

(* In expression x < y + n, fold n. *)
val fold_const_right =
    apply_to_thm' (Conv.arg_conv (Conv.arg_conv Nat_Util.nat_fold_conv))

(* Combine two inequalities. *)
fun combine_ineqs th1 th2 =
    let
      val (_, y1, d1) = dest_ineq_th th1
      val (x2, _, d2) = dest_ineq_th th2
      val _ = assert (y1 aconv x2) "combine_ineqs"
    in
      if d1 < 0 andalso d2 < 0 then
        ([th1, th2] MRS @{thm trans1}) |> fold_const_left
      else if d1 >= 0 andalso d2 >= 0 then
        ([th1, th2] MRS @{thm trans2}) |> fold_const_right
      else if d1 < 0 andalso d2 >= 0 then
        if d2 >= (~d1) then
          ([th1, th2] MRS @{thm trans3}) |> fold_const_right
        else  (* d2 < (~d1) *)
          ([Nat_Util.nat_less_th d2 (~d1), th1, th2] MRS @{thm trans4})
              |> fold_const_left
      else  (* d1 >= 0 andalso d2 < 0 *)
        if d1 >= (~d2) then
          ([th1, th2] MRS @{thm trans5}) |> fold_const_right
        else
          ([Nat_Util.nat_less_th d1 (~d2), th1, th2] MRS @{thm trans6})
              |> fold_const_left
    end

(* Normalize inequality to standard form. This function is able to
   process any theorem of the form a </<= b.
 *)
fun norm_ineq_th' th =
    let
      val t = prop_of' th
      val _ = assert (is_less_eq t orelse is_less t) "norm_ineq_th"
      val (lhs, rhs) = Util.dest_binop_args t
      val try_fold0 = Conv.try_conv (Conv.arg_conv Nat_Util.nat_fold_conv0_right)
    in
      if is_less_eq t then
        if is_plus_const lhs andalso is_plus_const rhs then
          let
            val (lhs, rhs) = Util.dest_binop_args t
            val (n1, n2) = apply2 (UtilArith.dest_numc o dest_arg) (lhs, rhs)
          in
            if n1 <= n2 then
              (th RS @{thm reduce_le_plus_consts}) |> fold_const_right
            else
              ([Nat_Util.nat_le_th n2 n1, th]
                   MRS @{thm reduce_le_plus_consts'}) |> fold_const_left
          end
        else if is_plus_const lhs then
          if UtilArith.dest_numc (dest_arg lhs) = 0 then
            th RS @{thm norm_le_lplus0}
          else th
        else if is_plus_const rhs then th
        else if is_minus_const lhs then
          th RS @{thm norm_le_lminus}
        else if is_minus_const rhs then
          th RS @{thm norm_le_rminus}
        else
          th RS @{thm norm_le}
      else  (* is_less t *)
        if is_plus_const lhs andalso is_plus_const rhs then
          let
            val (lhs, rhs) = Util.dest_binop_args t
            val (n1, n2) = apply2 (UtilArith.dest_numc o dest_arg) (lhs, rhs)
          in
            if n1 <= n2 then
              (th RS @{thm reduce_less_plus_consts}) |> fold_const_right
                                                     |> apply_to_thm' try_fold0
                                                     |> norm_ineq_th'
            else
              ([Nat_Util.nat_le_th n2 n1, th]
                   MRS @{thm reduce_less_plus_consts'}) |> fold_const_left
                                                        |> norm_ineq_th'
          end
        else if is_plus_const lhs then
          (th RS @{thm norm_less_lplus}) |> fold_const_left
        else if is_plus_const rhs then
          (th RS @{thm norm_less_rplus}) |> fold_const_right
        else if is_minus_const lhs then
          (th RS @{thm norm_less_lminus}) |> fold_const_right
        else if is_minus_const rhs then
          (th RS @{thm norm_less_rminus}) |> fold_const_left
        else
          th RS @{thm norm_less}
    end

fun convert_const_x th =
    let
      val (x, _, d) = dest_ineq_th th
    in
      if UtilArith.is_numc x then
        let
          val xn = UtilArith.dest_numc x
        in
          if xn = 0 then th
          else if d < 0 then
            (th RS @{thm cv_const1}) |> fold_const_left
          else if d - xn < 0 then
            (th RS @{thm cv_const4}) |> fold_const_left
          else
            (th RS @{thm cv_const5}) |> fold_const_right
        end
      else th
    end

fun convert_const_y th =
    let
      val (_, y, d) = dest_ineq_th th
    in
      if UtilArith.is_numc y then
        let
          val yn = UtilArith.dest_numc y
        in
          if yn = 0 then th
          else if d < 0 andalso yn + d >= 0 then
            (th RS @{thm cv_const2}) |> fold_const_right
          else if d < 0 andalso yn + d < 0 then
            ([Nat_Util.nat_less_th yn (~d), th] MRS @{thm cv_const3})
                |> fold_const_left
          else
            (th RS @{thm cv_const6}) |> fold_const_right
        end
      else th
    end

fun norm_ineq_th th =
    let
      val th' =
          th |> norm_ineq_th' |> convert_const_x |> convert_const_y
    in
      if is_standard_ineq (prop_of' th') then th'
      else let
        val _ = trace_thm_global "th':" th'
      in
        raise Fail "norm_ineq_th: invalid output."
      end
    end

fun norm_ineq_minus_th' th =
    let
      val t = prop_of' th
      val _ = assert (is_less_eq t orelse is_less t) "norm_ineq_minus_th"
      val (lhs, rhs) = Util.dest_binop_args t
    in
      if is_less_eq t then
        if is_minus_const lhs andalso not (is_plus_const rhs) then
          SOME (th RS @{thm norm_le})
        else if is_minus_const rhs andalso not (is_plus_const lhs) then
          SOME (th RS @{thm norm_le})
        else NONE
      else  (* is_less t *)
        if is_minus_const lhs andalso not (is_plus_const rhs) then
          SOME (th RS @{thm norm_less})
        else if is_minus_const rhs andalso not (is_plus_const lhs) then
          SOME (th RS @{thm norm_less})
        else NONE
    end

fun norm_ineq_minus_th th =
    case norm_ineq_minus_th' th of
        NONE => NONE
      | SOME th' =>
        let
          val th'' = th' |> convert_const_x |> convert_const_y
        in
          if is_standard_ineq (prop_of' th'') then SOME th''
          else let
            val _ = trace_thm_global "th'':" th''
          in
            raise Fail "norm_ineq_minus_th: invalid output."
          end
        end

end  (* NatOrder *)
