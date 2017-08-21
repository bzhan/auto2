(* Arithmetic on rational numbers *)

val rat_zero = Rat.make (0, 1)
val rat_one = Rat.make (1, 1)
val of_nat_t = @{term of_nat}
val of_nat_ct = @{cterm of_nat}
val divide_t = @{term divide}
val divide_ct = @{cterm divide}
fun is_divide G t = Util.is_head (divide_t $ G) t

(* Produce wfconv from conv. Currently do not add wellform information
   on the resulting term.
 *)
fun cv_to_wfcv cv wft =
    let
      val eq_th = cv (WfTerm.cterm_of wft)
      val rhs = WfTerm (Thm.rhs_of eq_th)
    in
      (rhs, eq_th)
    end

val nat_add_wf = cv_to_wfcv NatArith.nat_add
val nat_mult_wf = cv_to_wfcv NatArith.nat_mult
val nat_sub_wf = cv_to_wfcv NatArith.nat_sub

signature RAT_ARITH =
sig
  type rat_info

  val rat_opheads: term list
  val rat_fheads: term -> term list
  val comm_ring_rat_info: thm -> rat_info

  (* Construction of rational numbers *)
  val is_of_nat: term -> term -> bool
  val is_int: term -> term -> bool
  val is_rat: term -> term -> bool
  val dest_of_nat: term -> int
  val dest_int: term -> int
  val dest_rat: term -> Rat.rat
  val mk_int: term -> int -> term
  val mk_rat: term -> Rat.rat -> term

  (* Construction of theorems n :. G for integers n *)
  val in_carrier_int: rat_info -> int -> thm
  val mk_int_wfterm: rat_info -> int -> wfterm

  (* Arithmetics on rational numbers *)
  val int_add: rat_info -> wfconv
  val int_mult: rat_info -> wfconv
  val int_eval_once: rat_info -> wfconv
  val int_eval: rat_info -> wfconv
  val mk_int_add_th: rat_info -> int * int -> thm
  val mk_int_mult_th: rat_info -> int * int -> thm
  val mk_int_mult_th_back: rat_info -> int * int -> thm
  val rat_reduce_to_int: rat_info -> wfconv
  val rat_reduce: rat_info -> wfconv
  val rat_to_frac: rat_info -> wfconv
  val rat_add: rat_info -> wfconv
  val rat_mult: rat_info -> wfconv
  val rat_inv: rat_info -> wfconv
  val rat_uminus: rat_info -> wfconv
  val rat_minus: rat_info -> wfconv
  val rat_divide: rat_info -> wfconv
end;

structure RatArith : RAT_ARITH =
struct

open NatArith

type rat_info = {
  G: term,
  cG: cterm,
  of_nat_type: thm,     (* n : nat ==> of_nat(n) :. G *)
  neg_type: thm,        (* x :. G ==> -x :. G *)
  divide_type: thm,     (* x :. G ==> y : units(G) ==> x / y :. G *)
  of_nat_add: wfconv,   (* of_nat(x) + of_nat(y) = of_nat(x + y) *)
  of_nat_mult: wfconv,  (* of_nat(x) * of_nat(y) = of_nat(x * y) *)
  plus_comm: wfconv,    (* x + y = y + x *)
  neg_distrib': wfconv, (* -x + -y = -(x + y) *)
  sign_l: wfconv,       (* -x * y = -(x * y) *)
  sign_r: wfconv,       (* x * -y = -(x * y) *)
  sign_both: wfconv,    (* -x * -y = x * y *)
  div_cleft: wfconv,    (* (z*x) / (z*y) = x / y *)
  div_cross: wfconv,    (* p/q + r/s = (p*s+q*r) / (q*s) *)
  div_mult: wfconv,     (* p/q * r/s = (p*r) / (q*s) *)
  div_1: wfconv,        (* p = p/1 *)
  div_1_neg: wfconv,    (* -p = -p/1 *)
  div_1_back: wfconv,   (* p/1 = p *)
  div_inv: wfconv,      (* inv(p/q) = q/p *)
  div_inv2: wfconv,     (* inv(-p/q) = -q/p *)
  neg_zero': wfconv,    (* -of_nat(0) = of_nat(0) *)
  neg_inv: wfconv,      (* -(p/q) = -p/q *)
  neg_inv2: wfconv,     (* -(-p/q) = p/q *)
  minus: wfconv,        (* x - y = x + -y *)
  divide: wfconv,       (* x / y = x * inv(y) *)
  (* x >= y ==> of_nat(x) + -of_nat(y) = of_nat(x-y) *)
  of_nat_sub1: thm -> wfconv,
  (* x <= y ==> of_nat(x) + -of_nat(y) = -of_nat(y-x) *)
  of_nat_sub2: thm -> wfconv
}

val rat_opheads =
    [plus_t, uminus_t, minus_t, times_t, inv_t, divide_t, of_nat_t]

fun rat_fheads G = map (fn t => t $ G) rat_opheads

fun comm_ring_rat_info c_ring_th =
    let
      val G = dest_arg (prop_of' c_ring_th)
      val cG = Thm.dest_arg (cprop_of' c_ring_th)
      val fheads = rat_fheads G
      fun rewr th = WfTerm.rewr_obj_eq fheads th
      val ring_th = c_ring_th RS @{thm is_comm_ringD(1)}
      val abgroup_th = ring_th RS @{thm is_ringD(2)}
      val ab_monoid_th = abgroup_th RS @{thm is_abgroupD(1)}
      val plus_comm_th = ab_monoid_th RS @{thm is_ab_monoidD(3)}
    in
      {G = G,
       cG = cG,
       of_nat_type  = ring_th    RS @{thm of_nat_type},
       neg_type     = abgroup_th RS @{thm abgroup_neg_type},
       divide_type  = c_ring_th  RS @{thm divide_type},
       of_nat_add   = rewr (c_ring_th    RS @{thm of_nat_add}),
       of_nat_mult  = rewr (c_ring_th    RS @{thm of_nat_mult}),
       plus_comm    = rewr (plus_comm_th RS @{thm plus_commD}),
       neg_distrib' = rewr (abgroup_th   RS @{thm abgroup_neg_distrib'}),
       sign_l       = rewr (ring_th      RS @{thm ring_mult_sign_l}),
       sign_r       = rewr (ring_th      RS @{thm ring_mult_sign_r}),
       sign_both    = rewr (ring_th      RS @{thm ring_mult_sign_both}),
       div_cleft    = rewr (c_ring_th    RS @{thm divide_cancel_left}),
       div_cross    = rewr (c_ring_th    RS @{thm divide_cross}),
       div_mult     = rewr (c_ring_th    RS @{thm divide_mult}),
       div_1        = rewr (c_ring_th    RS @{thm comm_ring_divide_1}),
       div_1_neg    = rewr (c_ring_th    RS @{thm comm_ring_neg_divide_1}),
       div_1_back   = rewr (c_ring_th    RS @{thm comm_ring_divide_1_back}),
       div_inv      = rewr (c_ring_th    RS @{thm divide_inv}),
       div_inv2     = rewr (c_ring_th    RS @{thm divide_inv2}),
       neg_zero'    = rewr (c_ring_th    RS @{thm uminus_zero}),
       neg_inv      = rewr (c_ring_th    RS @{thm uminus_inv1}),
       neg_inv2     = rewr (c_ring_th    RS @{thm uminus_inv2}),
       minus        = rewr (abgroup_th   RS @{thm minusD}),
       divide       = rewr (c_ring_th    RS @{thm divideD}),
       of_nat_sub1  = (fn th => rewr ([c_ring_th, th] MRS @{thm of_nat_sub1})),
       of_nat_sub2  = (fn th => rewr ([c_ring_th, th] MRS @{thm of_nat_sub2}))
      }
    end

(* Check if t is of the form of_nat n *)
fun is_of_nat G t =
    case t of
        Const (@{const_name of_nat}, _) $ G' $ t' =>
        G aconv G' andalso is_nat t'
      | _ => false

(* Convert of_nat(.) term to integer. *)
fun dest_of_nat t =
    case t of
        Const (@{const_name of_nat}, _) $ _ $ _ => dest_nat (dest_arg t)
      | _ => raise Fail "dest_of_nat"

(* Check if t is of the form of_nat n or -(of_nat n) *)
fun is_int G t =
    case t of
        Const (@{const_name of_nat}, _) $ _ $ _ => is_of_nat G t
      | Const (@{const_name neg}, _) $ G' $ t' =>
        G' aconv G andalso is_of_nat G t' andalso dest_of_nat t' > 0
      | _ => false

(* Convert term to integer. *)
fun dest_int t =
    case t of
        Const (@{const_name of_nat}, _) $ _ $ _ => dest_of_nat t
      | Const (@{const_name neg}, _) $ _ $ t' => ~(dest_of_nat t')
      | _ => raise Fail "dest_int"

(* Numbers are in one of the following standard forms: "n", "-n",
   "m/n", and "-(m/n)", where m and n are natural numbers.
 *)
fun is_rat G t =
    case t of
        Const (@{const_name divide}, _) $ G' $ t1 $ t2 =>
        G aconv G' andalso is_int G t1 andalso is_of_nat G t2 andalso
        dest_of_nat t2 > 1 andalso
        Integer.gcd (dest_int t1) (dest_of_nat t2) = 1
      | Const (@{const_name neg}, _) $ _ $ _ => is_int G t
      | Const (@{const_name of_nat}, _) $ _ $ _ => is_of_nat G t
      | _ => false

(* Convert term to rational number. *)
fun dest_rat t =
    case t of
        Const (@{const_name divide}, _) $ _ $ t1 $ t2 =>
        Rat.make (dest_int t1, dest_of_nat t2)
      | Const (@{const_name neg}, _) $ _ $ _ => Rat.make (dest_int t, 1)
      | Const (@{const_name of_nat}, _) $ _ $ _ => Rat.make (dest_of_nat t, 1)
      | _ => raise Fail "dest_rat"

(* Construct term for the given integer. *)
fun mk_int G n =
    if n >= 0 then of_nat_t $ G $ mk_nat n
    else uminus_t $ G $ (of_nat_t $ G $ mk_nat (~n))

(* Construct term for the given rational number. *)
fun mk_rat G r =
    let
      val (p, q) = Rat.dest r
    in
      if q = 1 then mk_int G p
      else divide_t $ G $ mk_int G p $ mk_int G q
    end

(* Here n is an integer. *)
fun in_carrier_int info n =
    let
      val {of_nat_type, neg_type, ...} = info
    in
      if n >= 0 then
        [in_nat_raw' n] MRS of_nat_type
      else
        [in_carrier_int info (~n)] MRS neg_type
    end

(* Construct wfterm corresponding to integer n. *)
fun mk_int_wfterm (info as {cG, ...}) n =
    if n >= 0 then
      WfComb (of_nat_ct, [WfTerm cG, WfTerm (mk_nat_ct n)], [in_nat_raw' n])
    else
      WfComb (uminus_ct, [WfTerm cG, mk_int_wfterm info (~n)],
              [in_carrier_int info (~n)])

(* Evaluate m + n for integers. *)
fun int_add info wft =
    let
      val {of_nat_add, plus_comm, of_nat_sub1, of_nat_sub2,
           neg_distrib', ...} = info
      val (arg1, arg2) = Util.dest_binop_args (WfTerm.term_of wft)
      val (m, n) = (dest_int arg1, dest_int arg2)
    in
      if m >= 0 andalso n >= 0 then
        WfTerm.every_conv [of_nat_add, WfTerm.arg_conv nat_add_wf] wft
      else if m >= 0 andalso n < 0 then
        if m >= ~n then
          WfTerm.every_conv [of_nat_sub1 (nat_le (~n, m)),
                             WfTerm.arg_conv nat_sub_wf] wft
        else
          WfTerm.every_conv [of_nat_sub2 (nat_le (m, ~n)),
                             WfTerm.arg_conv (WfTerm.arg_conv nat_sub_wf)] wft
      else if m < 0 andalso n >= 0 then
        WfTerm.every_conv [plus_comm, int_add info] wft
      else  (* m < 0 andalso n < 0 *)
        WfTerm.every_conv [neg_distrib', WfTerm.arg_conv (int_add info)] wft
    end

(* Evaluate m * n for integers. *)
fun int_mult info wft =
    let
      val {of_nat_mult, sign_l, sign_r, sign_both, ...} = info
      val (arg1, arg2) = Util.dest_binop_args (WfTerm.term_of wft)
      val (m, n) = (dest_int arg1, dest_int arg2)
    in
      if m >= 0 andalso n >= 0 then
        WfTerm.every_conv [of_nat_mult, WfTerm.arg_conv nat_mult_wf] wft
      else if m < 0 andalso n >= 0 then
        WfTerm.every_conv [sign_l, WfTerm.arg_conv (int_mult info)] wft
      else if m >= 0 andalso n < 0 then
        WfTerm.every_conv [sign_r, WfTerm.arg_conv (int_mult info)] wft
      else  (* m < 0 andalso n < 0 *)
        WfTerm.every_conv [sign_both, int_mult info] wft
    end

(* Evaluate a binary operation on integers once. *)
fun int_eval_once info wft =
    let
      val {G, ...} = info
      val t = WfTerm.term_of wft
    in
      if is_plus G t andalso is_int G (dest_arg1 t) andalso
         is_int G (dest_arg t) then
        int_add info wft
      else if is_times G t andalso is_int G (dest_arg1 t) andalso
              is_int G (dest_arg t) then
        int_mult info wft
      else
        WfTerm.all_conv wft
    end

(* Complete evaluation of an expression in integers. *)
fun int_eval info wft =
    let
      val {G, ...} = info
      val t = WfTerm.term_of wft
    in
      if is_plus G t orelse is_times G t then
        WfTerm.every_conv [WfTerm.binop_conv (int_eval info),
                           int_eval_once info] wft
      else
        WfTerm.all_conv wft
    end

(* Produce the equation m + n == sum. *)
fun mk_int_add_th info (m, n) =
    let
      val {cG, ...} = info
      val plus_exp =
          WfComb (plus_ct,
                  [WfTerm cG, mk_int_wfterm info m, mk_int_wfterm info n],
                  [in_carrier_int info m, in_carrier_int info n])
    in
      snd (int_add info plus_exp)
    end

(* Produce the equation m * n == prod. *)
fun mk_int_mult_th info (m, n) =
    let
      val {cG, ...} = info
      val times_exp =
          WfComb (times_ct,
                  [WfTerm cG, mk_int_wfterm info m, mk_int_wfterm info n],
                  [in_carrier_int info m, in_carrier_int info n])
    in
      snd (int_mult info times_exp)
    end

(* Produce the equation (prod = m * n & m :. G & n :. G). *)
fun mk_int_mult_th_back info (m, n) =
    let
      val m_in_G = in_carrier_int info m
      val n_in_G = in_carrier_int info n
      val m_ths = WfTerm.wellform_ths_of (mk_int_wfterm info m)
      val n_ths = WfTerm.wellform_ths_of (mk_int_wfterm info n)
      val prod_th = to_obj_eq (meta_sym (mk_int_mult_th info (m, n)))
    in
      mk_conjs_th ([prod_th, m_in_G, n_in_G] @ m_ths @ n_ths)
    end

(* Given a fraction of the form p / 1, reduce to p. *)
fun rat_reduce_to_int info wft =
    let
      val {div_1_back, ...} = info
      val (_, arg2) = Util.dest_binop_args (WfTerm.term_of wft)
      val q = dest_int arg2
    in
      if q = 1 then div_1_back wft
      else WfTerm.all_conv wft
    end

(* Reduce the fraction p / q. *)
fun rat_reduce info wft =
    let
      val {G, div_cleft, ...} = info
      val fheads = rat_fheads G
      val (arg1, arg2) = Util.dest_binop_args (WfTerm.term_of wft)
      val (p, q) = (dest_int arg1, dest_int arg2)
      val gcd = Integer.gcd p q
      val (p', q') = (fst (Integer.div_mod p gcd), fst (Integer.div_mod q gcd))

      (* Get rewrite rules p = gcd * p' and q = gcd * q' *)
      val p_rewr = mk_int_mult_th_back info (gcd, p')
      val q_rewr = mk_int_mult_th_back info (gcd, q')
    in
      WfTerm.every_conv [WfTerm.arg1_conv (WfTerm.rewr_obj_eq fheads p_rewr),
                         WfTerm.arg_conv (WfTerm.rewr_obj_eq fheads q_rewr),
                         div_cleft,
                         rat_reduce_to_int info] wft
    end

(* Convert any rational to p/q form. *)
fun rat_to_frac info wft =
    let
      val {G, div_1, div_1_neg, ...} = info
      val t = WfTerm.term_of wft
    in
      if is_int G t then
        if dest_int t >= 0 then div_1 wft
        else div_1_neg wft
      else WfTerm.all_conv wft
    end

(* Evaluate r + s for rational numbers *)
fun rat_add info wft =
    let
      val {G, div_cross, ...} = info
      val (arg1, arg2) = Util.dest_binop_args (WfTerm.term_of wft)
    in
      if is_int G arg1 andalso is_int G arg2 then
        int_add info wft
      else
        WfTerm.every_conv [WfTerm.binop_conv (rat_to_frac info),
                           div_cross,
                           WfTerm.binop_conv (int_eval info),
                           rat_reduce info] wft
    end

(* Evaluate r * s for rational numbers *)
fun rat_mult info wft =
    let
      val {G, div_mult, ...} = info
      val (arg1, arg2) = Util.dest_binop_args (WfTerm.term_of wft)
    in
      if is_int G arg1 andalso is_int G arg2 then
        int_mult info wft
      else
        WfTerm.every_conv [WfTerm.binop_conv (rat_to_frac info),
                           div_mult,
                           WfTerm.binop_conv (int_eval info),
                           rat_reduce info] wft
    end

(* Evaluate inv(r) for rational numbers *)
fun rat_inv info wft =
    let
      val {div_inv, div_inv2, ...} = info
      val arg = dest_arg (WfTerm.term_of wft)
      val r = dest_rat arg
      val (p, _) = Rat.dest r
    in
      WfTerm.every_conv [WfTerm.arg_conv (rat_to_frac info),
                         if p >= 0 then div_inv else div_inv2,
                         rat_reduce info] wft
    end

(* Evaluate -r for rational numbers *)
fun rat_uminus info wft =
    let
      val {neg_zero', neg_inv, neg_inv2, ...} = info
      val arg = dest_arg (WfTerm.term_of wft)
      val r = dest_rat arg
      val (p, _) = Rat.dest r
    in
      if p = 0 then neg_zero' wft else
      WfTerm.every_conv [WfTerm.arg_conv (rat_to_frac info),
                         if p > 0 then neg_inv else neg_inv2,
                         rat_reduce info] wft
    end

(* Evaluate r - s for rational numbers *)
fun rat_minus info wft =
    let
      val {minus, ...} = info
    in
      WfTerm.every_conv [minus, WfTerm.arg_conv (rat_uminus info),
                         rat_add info] wft
    end

(* Evaluate r / s for rational numbers *)
fun rat_divide info wft =
    let
      val {divide, ...} = info
    in
      WfTerm.every_conv [divide, WfTerm.arg_conv (rat_inv info),
                         rat_mult info] wft
    end

end  (* structure FOLNum *)

open RatArith
