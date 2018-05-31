(* Arithmetic on natural numbers *)

signature NAT_ARITH =
sig
  (* Construction of natural numbers *)
  val is_Suc: term -> bool
  val is_nat: term -> bool
  val dest_nat: term -> int
  val mk_nat: int -> term
  val mk_nat_ct: int -> cterm

  (* Construction of theorems with nat *)
  val in_nat_raw: term -> thm
  val in_nat_raw': int -> thm
  val nat_add_raw: conv
  val nat_mult_raw: conv
  val nat_le_raw: int * int -> thm

  (* Construction of theorems with NN *)
  val rewr_to_nat: conv
  val rewr_to_NN: conv
  val in_nat: term -> thm
  val in_nat': int -> thm
  val nat_add: conv
  val nat_mult: conv
  val nat_le: int * int -> thm
  val nat_sub: conv
  val mk_nat_add_th: int * int -> thm
  val mk_nat_mult_th: int * int -> thm
  val nat_neq_resolve: thm -> thm
  val nat_neq_zero: int -> thm
  val nat_neq: int * int -> thm
  val nat_less: int * int -> thm

  val add_nat_arith_proofsteps: theory -> theory
end;

structure NatArith : NAT_ARITH =
struct

val ctxt = @{context}

fun is_Suc t =
    case t of
        Const ("Nat.Suc", _) $ _ => true
      | _ => false

fun is_nat t =
    case t of
        Const ("Nat.Zero", _) => true
      | Const ("Nat.Suc", _) $ t' => is_nat t'
      | _ => false

fun dest_nat t =
    case t of
        Const ("Nat.Zero", _) => 0
      | Const ("Nat.Suc", _) $ t' => 1 + dest_nat t'
      | _ => raise Fail "dest_nat_const"

val NN = @{term nat_ring}
val nat_Zero = @{term Zero}
val nat_Zero_ct = @{cterm Zero}
val nat_Suc = @{term Suc}
val nat_Suc_ct = @{cterm Suc}

(* Construct term for the given natural number n. *)
fun mk_nat n =
    if n < 0 then raise Fail "mk_nat"
    else if n = 0 then nat_Zero
    else nat_Suc $ mk_nat (n - 1)

fun mk_nat_ct n =
    if n < 0 then raise Fail "mk_nat_ct"
    else if n = 0 then nat_Zero_ct
    else Thm.apply nat_Suc_ct (mk_nat_ct (n-1))

(* Given t of form Suc(Suc(...)), return the theorem t : nat. *)
fun in_nat_raw t =
    case t of
        Const ("Nat.Zero", _) => @{thm nat_0I}
      | Const ("Nat.Suc", _) $ t' => (in_nat_raw t') RS @{thm nat_SucI}
      | _ => raise Fail "nat_type_th"

(* Like above, except taking a number as input. *)
fun in_nat_raw' n =
    if n < 0 then raise Fail "nat_type_th_n"
    else if n = 0 then @{thm nat_0I}
    else (in_nat_raw' (n - 1)) RS @{thm nat_SucI}

(* Simplify nat_add(m,n). *)
fun nat_add_raw ct =
    case dest_arg1 (Thm.term_of ct) of
        Const ("Nat.Zero", _) => rewr_obj_eq @{thm nat_add_0} ct
      | Const ("Nat.Suc", _) $ t' =>
        Conv.every_conv [rewr_obj_eq (in_nat_raw t' RS @{thm nat_add_Suc}),
                         Conv.arg_conv nat_add_raw] ct
      | _ => raise Fail "nat_add"

(* Simplify nat_mult(m,n). *)
fun nat_mult_raw ct =
    case dest_arg1 (Thm.term_of ct) of
        Const ("Nat.Zero", _) => rewr_obj_eq @{thm nat_mult_0} ct
      | Const ("Nat.Suc", _) $ t' =>
        Conv.every_conv [rewr_obj_eq (in_nat_raw t' RS @{thm nat_mult_Suc}),
                         Conv.arg_conv nat_mult_raw, nat_add_raw] ct
      | _ => raise Fail "nat_mult"

(* Return the theorem nat_le(m,n) (if valid). *)
fun nat_le_raw (m, n) =
    if m < 0 orelse n < 0 then raise Fail "nat_le"
    else if m > n then raise Fail "nat_le"
    else ([in_nat_raw' m, in_nat_raw' (n - m)] MRS @{thm nat_leI})
             |> apply_to_thm' (Conv.arg_conv nat_add_raw)

val rewr_to_nat = rewr_obj_eq @{thm nat_carrier}
val rewr_to_NN = rewr_obj_eq (obj_sym @{thm nat_carrier})

fun in_nat t = apply_to_thm' (Conv.arg_conv rewr_to_NN) (in_nat_raw t)
fun in_nat' n = apply_to_thm' (Conv.arg_conv rewr_to_NN) (in_nat_raw' n)

fun nat_add ct =
    let
      val (arg1, arg2) = Util.dest_binop_args (Thm.term_of ct)
      val eq_th = [in_nat arg1, in_nat arg2] MRS @{thm nat_evals(3)}
    in
      Conv.every_conv [rewr_obj_eq eq_th, nat_add_raw] ct
    end

fun nat_mult ct =
    let
      val (arg1, arg2) = Util.dest_binop_args (Thm.term_of ct)
      val eq_th = [in_nat arg1, in_nat arg2] MRS @{thm nat_evals(4)}
    in
      Conv.every_conv [rewr_obj_eq eq_th, nat_mult_raw] ct
    end

fun nat_le (m, n) =
    let
      val eq_th = [in_nat' m, in_nat' n] MRS @{thm nat_evals(5)}
    in
      apply_to_thm' (rewr_obj_eq (obj_sym eq_th)) (nat_le_raw (m, n))
    end

fun mk_nat_add_th (m, n) =
    nat_add (Thm.cterm_of ctxt (plus_t $ NN $ mk_nat m $ mk_nat n))

fun mk_nat_mult_th (m, n) =
    nat_mult (Thm.cterm_of ctxt (times_t $ NN $ mk_nat m $ mk_nat n))

fun nat_sub ct =
    let
      val (arg1, arg2) = Util.dest_binop_args (Thm.term_of ct)
      val (x, y) = (dest_nat arg1, dest_nat arg2)
    in
      if x < y then raise Fail "nat_sub"
      else let
        val p = x - y
        val eq_th = to_obj_eq (mk_nat_add_th (p, y))
      in
        to_meta_eq ([in_nat' y, in_nat' p, eq_th] MRS @{thm nat_minusI})
      end
    end

(* Given a theorem m = n, where m and n are nat constants that are in
   fact not equal, return the theorem False.
 *)
fun nat_neq_resolve th =
    let
      val (m, n) = th |> prop_of' |> dest_eq
    in
      if m aconv nat_Zero then
        [@{thm nat_Suc_not_zero}, th] MRS UtilBase.contra_triv_th
      else if n aconv nat_Zero then
        [@{thm nat_Suc_not_zero}, obj_sym th] MRS UtilBase.contra_triv_th
      else
        nat_neq_resolve (th RS @{thm nat_Suc_inj})
    end

(* Produce the theorem n ~= 0. *)
fun nat_neq_zero n =
    if n <= 0 then raise Fail "nat_neq_zero"
    else let
      val nt = mk_nat (n - 1)
      val inst = Util.update_env (("n",0), nt) fo_init
    in
      (Util.subst_thm ctxt inst @{thm nat_Suc_not_zero}) RS @{thm not_sym}
    end

(* Produce the theorem m ~= n. *)
fun nat_neq (m, n) =
    if m = n then raise Fail "nat_neq" else
    let
      val m_eq_n = mk_eq (mk_nat m, mk_nat n) |> mk_Trueprop |> Thm.cterm_of ctxt
    in
      m_eq_n |> Thm.assume
             |> nat_neq_resolve
             |> Thm.implies_intr m_eq_n
             |> apply_to_thm UtilLogic.rewrite_from_contra_form
    end

val nat_linorder_th = @{thm nat_is_linorder}
val nat_order_th = nat_linorder_th RS @{thm linorderD(1)}
val nat_preorder_th = nat_order_th RS @{thm orderD(1)}
val nat_trans_th = nat_preorder_th RS @{thm preorderD(1)}
val nat_raworder_th = nat_trans_th RS @{thm transD(1)}

(* Produce the theorem m < n. *)
fun nat_less (m, n) =
    if m >= n then raise Fail "nat_less" else
    let
      val le_th = nat_le (m, n)
      val neq_th = nat_neq (m, n)
    in
      [nat_raworder_th, le_th, neq_th] MRS @{thm preorder_lessI}
    end

val add_nat_arith_proofsteps =
    fold Consts.add_const_data [
      ("nat", is_nat)

    ] #> fold add_prfstep_custom [
      ("nat_eq_consts",
       [WithFact @{term_pat "?NUMC1 = ?NUMC2"}],
       fn ((id, _), ths) => fn _ => fn _ =>
          let
            val th = the_single ths
            val (m, n) = th |> prop_of' |> dest_eq
          in
            if is_nat m andalso is_nat n andalso dest_nat m <> dest_nat n then
              [Update.thm_update (id, nat_neq_resolve th)]
            else []
          end),

      ("nat_le_consts",
       [WithGoal @{term_pat "le(nat_ring,?NUMC1,?NUMC2)"}],
       fn ((id, _), ths) => fn _ => fn _ =>
          let
            val th = the_single ths
            val (m, n) = th |> prop_of' |> dest_not |> Util.dest_binop_args
          in
            if is_nat m andalso is_nat n andalso dest_nat m <= dest_nat n then
              let
                val le_th = nat_le (dest_nat m, dest_nat n)
              in
                [Update.thm_update (id, [th, le_th] MRS UtilBase.contra_triv_th)]
              end
            else []
          end),

      ("nat_less_consts",
       [WithGoal @{term_pat "less(nat_ring,?NUMC1,?NUMC2)"}],
       fn ((id, _), ths) => fn _ => fn _ =>
          let
            val th = the_single ths
            val (m, n) = th |> prop_of' |> dest_not |> Util.dest_binop_args
          in
            if is_nat m andalso is_nat n andalso dest_nat m < dest_nat n then
              let
                val less_th = nat_less (dest_nat m, dest_nat n)
              in
                [Update.thm_update (id, [th, less_th] MRS UtilBase.contra_triv_th)]
              end
            else []
          end)

    ] #> fold add_prfstep_conv [
      ("eval_nat_add_consts",
       [WithTerm @{term_pat "plus(nat_ring,?NUMC1,?NUMC2)"},
        Filter (fn _ => fn (_, inst) =>
                   is_nat (lookup_instn inst ("NUMC", 1)) andalso
                   is_nat (lookup_instn inst ("NUMC", 2)))],
       nat_add),

      ("eval_nat_mult_consts",
       [WithTerm @{term_pat "times(nat_ring,?NUMC1,?NUMC2)"},
        Filter (fn _ => fn (_, inst) =>
                   is_nat (lookup_instn inst ("NUMC", 1)) andalso
                   is_nat (lookup_instn inst ("NUMC", 2)))],
       nat_mult),

      ("eval_nat_sub_consts",
       [WithTerm @{term_pat "minus(nat_ring,?NUMC1,?NUMC2)"},
        Filter (fn _ => fn (_, inst) =>
                   let
                     val m = lookup_instn inst ("NUMC", 1)
                     val n = lookup_instn inst ("NUMC", 2)
                   in
                     is_nat m andalso is_nat n andalso dest_nat m >= dest_nat n
                   end)],
       nat_sub)
    ]

end  (* structure NatArith *)

val _ = Theory.setup NatArith.add_nat_arith_proofsteps
