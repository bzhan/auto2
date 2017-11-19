(* Arithmetic proof steps. *)

signature NAT_ARITH =
sig
  val lookup_numc: Type.tyenv * Envir.tenv -> int -> int
  val lookup_numc0: Type.tyenv * Envir.tenv -> int
  val lookup_numc1: Type.tyenv * Envir.tenv -> int
  val lookup_numc2: Type.tyenv * Envir.tenv -> int
  val mk_nat: int -> term
  val mk_int: int -> term
  val nat0: term
  val cnat0: cterm
  val plusT: term

  val is_plus: term -> bool
  val is_minus: term -> bool
  val nat_le_th: int -> int -> thm
  val nat_less_th: int -> int -> thm
  val nat_neq_th: int -> int -> thm
  val nat_fold_reduce: term -> term
  val nat_fold_conv: conv
  val plus_eq_th: int -> int -> thm

  val nat_fold_conv0_right: conv
  val nat_fold_conv0_left: conv
  val nat_fold_rec_conv: Proof.context -> conv
  val nat_fold_rec_thm: Proof.context -> thm -> thm

  val plus_ac_on_typ: theory -> typ -> ac_info
  val times_ac_on_typ: theory -> typ -> ac_info
  val add_arith_ac_data: theory -> theory
  val add_arith_proofsteps: theory -> theory
end;

structure Nat_Arith : NAT_ARITH =
struct

fun lookup_numc inst n = UtilArith.dest_numc (lookup_instn inst ("NUMC", n))
fun lookup_numc0 inst = lookup_numc inst 0
fun lookup_numc1 inst = lookup_numc inst 1
fun lookup_numc2 inst = lookup_numc inst 2
fun mk_nat n = HOLogic.mk_number natT n
fun mk_int n = HOLogic.mk_number intT n
val nat0 = mk_nat 0
val cnat0 = @{cterm "0::nat"}
val plusT = Const (@{const_name plus}, natT --> natT --> natT)

(* Check whether t is in the form a + b. *)
fun is_plus t =
    case t of
        Const (@{const_name plus}, _) $ _ $ _ => true
      | _ => false

(* Check whether t is in the form a - b. *)
fun is_minus t =
    case t of
        Const (@{const_name minus}, _) $ _ $ _ => true
      | _ => false

local
  val ctxt = @{context}
in

(* Obtain the theorem m <= n. *)
fun nat_le_th m n =
    if m > n then raise Fail "nat_le_th: input"
    else UtilArith.prove_by_arith ctxt [] (
        Const (@{const_name less_eq}, natT --> natT --> boolT)
              $ mk_nat m $ mk_nat n)

(* Obtain the theorem m < n. *)
fun nat_less_th m n =
    if m >= n then raise Fail "nat_less_th: input"
    else UtilArith.prove_by_arith ctxt [] (
        Const (@{const_name less}, natT --> natT --> boolT)
              $ mk_nat m $ mk_nat n)

(* Obtain the theorem m ~= n. *)
fun nat_neq_th m n =
    if m = n orelse m < 0 orelse n < 0 then raise Fail "nat_neq_th: input"
    else UtilArith.prove_by_arith ctxt [] (mk_not (mk_eq (mk_nat m, mk_nat n)))

fun nat_fold_reduce t =
    if fastype_of t <> natT then t else
    let
      val (f, (n1, n2)) = t |> Util.dest_binop |> apsnd (apply2 UtilArith.dest_numc)
    in
      case f of
          Const (@{const_name plus}, _) => mk_nat (n1 + n2)
        | Const (@{const_name minus}, _) => mk_nat (Int.max (0, n1 - n2))
        | Const (@{const_name times}, _) => mk_nat (n1 * n2)
        | _ => t
    end
    handle Fail "dest_binop" => t | Fail "dest_numc" => t

fun nat_fold_conv ct =
    let
      val t = Thm.term_of ct
      val t' = nat_fold_reduce t
    in
      if t aconv t' then Conv.all_conv ct
      else to_meta_eq (UtilArith.prove_by_arith ctxt [] (mk_eq (t, t')))
    end

(* Given natural numbers m and n, return the theorem m + n = p. *)
fun plus_eq_th m n =
    let
      val expr = plusT $ mk_nat m $ mk_nat n
    in
      expr |> Thm.cterm_of ctxt |> nat_fold_conv
    end

end  (* local ctxt = @{context}. *)

val nat_fold_conv0_right =
    Conv.try_conv (rewr_obj_eq @{thm Nat.add_0_right})
val nat_fold_conv0_left =
    Conv.try_conv (rewr_obj_eq @{thm Nat.plus_nat.add_0})

val nat_fold_rec_conv =
    Conv.bottom_conv (fn _ => nat_fold_conv then_conv nat_fold_conv0_right
                                            then_conv nat_fold_conv0_left)
fun nat_fold_rec_thm ctxt = apply_to_thm (nat_fold_rec_conv ctxt)

val plus_ac =
    {cfhead = @{cterm plus}, unit = SOME @{cterm 0},
     assoc_th = @{thm add_ac(1)}, comm_th = @{thm add_ac(2)},
     unitl_th = @{thm add_0}, unitr_th = @{thm add_0_right}}

val times_ac =
    {cfhead = @{cterm times}, unit = SOME @{cterm 1},
     assoc_th = @{thm mult_ac(1)}, comm_th = @{thm mult_ac(2)},
     unitl_th = @{thm mult_1}, unitr_th = @{thm mult_1_right}}

val gcd_ac =
    {cfhead = @{cterm gcd}, unit = SOME @{cterm 0},
     assoc_th = @{thm gcd.assoc}, comm_th = @{thm gcd.commute},
     unitl_th = @{thm gcd_0_left_nat}, unitr_th = @{thm gcd_0_nat}}

val add_arith_ac_data =
    fold ACUtil.add_ac_data [plus_ac, times_ac, gcd_ac]

fun plus_ac_on_typ thy T =
    the (ACUtil.inst_ac_info thy T plus_ac)
    handle Option.Option => raise Fail "plus_ac_on_typ: cannot inst ac_info."

fun times_ac_on_typ thy T =
    the (ACUtil.inst_ac_info thy T times_ac)
    handle Option.Option => raise Fail "times_ac_on_typ: cannot inst ac_info."

val add_arith_proofsteps =
    fold add_prfstep_custom [
      (* Resolve equality facts with constants. *)
      ("compare_consts",
       [WithFact @{term_pat "(?NUMC1::nat) = ?NUMC2"},
        Filter (fn _ => fn (_, inst) =>
                   lookup_numc1 inst <> lookup_numc2 inst)],
       PRIORITY_RESOLVE,
       fn ((id, _), ths) => fn _ => fn ctxt =>
          [Update.thm_update (id, UtilArith.contra_by_arith ctxt ths)]),

      ("compare_consts_le",
       [WithFact @{term_pat "(?NUMC1::nat) <= ?NUMC2"},
        Filter (fn _ => fn (_, inst) =>
                   lookup_numc1 inst > lookup_numc2 inst)],
       PRIORITY_RESOLVE,
       fn ((id, _), ths) => fn _ => fn ctxt =>
          [Update.thm_update (id, UtilArith.contra_by_arith ctxt ths)]),

      ("compare_consts_less",
       [WithFact @{term_pat "(?NUMC1::nat) < ?NUMC2"},
        Filter (fn _ => fn (_, inst) =>
                   lookup_numc1 inst >= lookup_numc2 inst)],
       PRIORITY_RESOLVE,
       fn ((id, _), ths) => fn _ => fn ctxt =>
          [Update.thm_update (id, UtilArith.contra_by_arith ctxt ths)])

    ] #> fold add_prfstep_conv [
      ("eval_plus_consts",
       [WithTerm @{term_pat "(?NUMC1::nat) + ?NUMC2"},
        Filter (fn _ => fn (_, inst) =>
                   lookup_numc1 inst > 0 andalso lookup_numc2 inst > 0)],
       nat_fold_conv),

      ("eval_mult_consts",
       [WithTerm @{term_pat "(?NUMC1::nat) * ?NUMC2"},
        Filter (fn _ => fn (_, inst) =>
                   lookup_numc1 inst <> 1 andalso lookup_numc2 inst <> 1)],
       nat_fold_conv),

      ("eval_minus_consts",
       [WithTerm @{term_pat "(?NUMC1::nat) - ?NUMC2"},
        Filter (fn _ => fn (_, inst) => lookup_numc2 inst >= 1)],
       nat_fold_conv)]

end  (* structure Nat_Arith. *)

val mk_nat = Nat_Arith.mk_nat
val mk_int = Nat_Arith.mk_int
val plus_ac_on_typ = Nat_Arith.plus_ac_on_typ
val times_ac_on_typ = Nat_Arith.times_ac_on_typ
val _ = Theory.setup Nat_Arith.add_arith_ac_data
val _ = Theory.setup Nat_Arith.add_arith_proofsteps
