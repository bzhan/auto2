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
  val prove_by_arith: Proof.context -> thm list -> term -> thm
  val contra_by_arith: Proof.context -> thm list -> thm
  val nat_le_th: int -> int -> thm
  val nat_less_th: int -> int -> thm
  val nat_neq_th: int -> int -> thm

  val nat_fold_reduce: term -> term
  val nat_fold_conv: conv
  val nat_fold_conv0_right: conv
  val nat_fold_conv0_left: conv
  val nat_fold_rec_conv: Proof.context -> conv
  val nat_fold_rec_thm: Proof.context -> thm -> thm

  val add_arith_ac_data: theory -> theory
  val add_arith_proofsteps: theory -> theory
end;

structure Nat_Arith : NAT_ARITH =
struct

fun lookup_numc inst n = dest_numc (lookup_instn inst ("NUMC", n))
fun lookup_numc0 inst = lookup_numc inst 0
fun lookup_numc1 inst = lookup_numc inst 1
fun lookup_numc2 inst = lookup_numc inst 2
fun mk_nat n = HOLogic.mk_number natT n
fun mk_int n = HOLogic.mk_number @{typ int} n
val nat0 = mk_nat 0
fun prove_by_arith ctxt ths goal =
    let
      val goal' = Logic.list_implies (
            map Thm.prop_of ths, HOLogic.mk_Trueprop goal)
    in
      ths MRS (Goal.prove ctxt [] [] goal' (K (Arith_Data.arith_tac ctxt 1)))
    end
fun contra_by_arith ctxt ths = prove_by_arith ctxt ths @{term "False"}

(* Obtain the theorem m <= n. *)
fun nat_le_th m n =
    if m > n then raise AUTO2 "nat_le_th: input"
    else prove_by_arith @{context} [] (
        Const (@{const_name less_eq}, natT --> natT --> boolT)
              $ mk_nat m $ mk_nat n)

(* Obtain the theorem m < n. *)
fun nat_less_th m n =
    if m >= n then raise AUTO2 "nat_less_th: input"
    else prove_by_arith @{context} [] (
        Const (@{const_name less}, natT --> natT --> boolT)
              $ mk_nat m $ mk_nat n)

(* Obtain the theorem m ~= n. *)
fun nat_neq_th m n =
    if m = n orelse m < 0 orelse n < 0 then raise AUTO2 "nat_neq_th: input"
    else prove_by_arith @{context} [] (HOLogic.mk_not (
                                          HOLogic.mk_eq (mk_nat m, mk_nat n)))

fun nat_fold_reduce t =
    if fastype_of t <> natT then t else
    let
      val (f, (n1, n2)) =
          t |> Term.strip_comb |> apsnd (the_pair o map dest_numc)
    in
      case f of
          Const (@{const_name plus}, _) => mk_nat (n1 + n2)
        | Const (@{const_name minus}, _) => mk_nat (Int.max (0, n1 - n2))
        | Const (@{const_name times}, _) => mk_nat (n1 * n2)
        | _ => t
    end
    handle AUTO2 _ => t | TERM ("dest_number", _) => t

fun nat_fold_conv ct =
    let
      val t = Thm.term_of ct
      val t' = nat_fold_reduce t
    in
      if t aconv t' then Conv.all_conv ct
      else to_meta_eq (prove_by_arith @{context} [] (HOLogic.mk_eq (t, t')))
    end

val nat_fold_conv0_right =
    Conv.try_conv (rewr_obj_eq @{thm Nat.add_0_right})
val nat_fold_conv0_left =
    Conv.try_conv (rewr_obj_eq @{thm Nat.plus_nat.add_0})

val nat_fold_rec_conv =
    Conv.bottom_conv (fn _ => nat_fold_conv then_conv nat_fold_conv0_right
                                            then_conv nat_fold_conv0_left)
fun nat_fold_rec_thm ctxt = apply_to_thm (nat_fold_rec_conv ctxt)

val add_arith_ac_data =
    fold add_ac_data [
      {fname = @{const_name plus}, assoc_r = false,
       unit_val = @{term 0}, comm_th = @{thm add_ac(2)},
       assoc_th = @{thm add_ac(1)},
       unit_th = @{thm Groups.monoid_add_class.add_0_left}},

      {fname = @{const_name times}, assoc_r = false,
       unit_val = @{term 1}, comm_th = @{thm mult_ac(2)},
       assoc_th = @{thm mult_ac(1)},
       unit_th = @{thm Groups.monoid_mult_class.mult_1_left}},

      {fname = @{const_name gcd}, assoc_r = false,
       unit_val = @{term "0::nat"}, comm_th = @{thm gcd_nat.commute},
       assoc_th = @{thm gcd_nat.assoc},
       unit_th = @{thm GCD.gcd_nat.left_neutral}}]

val add_arith_proofsteps =
    fold add_prfstep_thm_fn [
      (* Resolve equality facts with constants. *)
      ("compare_consts",
       [WithFact @{term_pat "(?NUMC1::nat) = ?NUMC2"},
        Filter (fn _ => fn (_, inst) =>
                   lookup_numc1 inst <> lookup_numc2 inst)],
       [Update.RESOLVE_BOX],
       fn ctxt => fn (_, ths) => contra_by_arith ctxt ths)

    ] #> fold add_prfstep_conv [
      ("eval_plus_consts",
       [WithTerm @{term_pat "(?NUMC1::nat) + ?NUMC2"},
        Filter (order_filter_n ("NUMC", 1) ("NUMC", 2)),
        Filter (fn _ => fn (_, inst) =>
                   lookup_numc1 inst > 0 andalso lookup_numc2 inst > 0)],
       nat_fold_conv),

      ("eval_mult_consts",
       [WithTerm @{term_pat "(?NUMC1::nat) * ?NUMC2"},
        Filter (order_filter_n ("NUMC", 1) ("NUMC", 2)),
        Filter (fn _ => fn (_, inst) =>
                   lookup_numc1 inst > 1 andalso lookup_numc2 inst > 1)],
       nat_fold_conv),

      ("eval_minus_consts",
       [WithTerm @{term_pat "(?NUMC1::nat) - ?NUMC2"},
        Filter (fn _ => fn (_, inst) =>
                   lookup_numc1 inst >= lookup_numc2 inst andalso
                   lookup_numc2 inst >= 1)],
       nat_fold_conv)]

end  (* structure Nat_Arith. *)

val _ = Theory.setup Nat_Arith.add_arith_ac_data
val _ = Theory.setup Nat_Arith.add_arith_proofsteps
