(* Proof steps related to rational numbers. *)

signature RAT_ARITH =
sig
  val ratT: typ
  val dest_rat: term -> Rat.rat
  val mk_rat: typ -> Rat.rat -> term
  val lookup_numc: Type.tyenv * Envir.tenv -> int -> Rat.rat
  val lookup_numc0: Type.tyenv * Envir.tenv -> Rat.rat
  val lookup_numc1: Type.tyenv * Envir.tenv -> Rat.rat
  val lookup_numc2: Type.tyenv * Envir.tenv -> Rat.rat

  val rat_le_th: Proof.context -> typ -> Rat.rat -> Rat.rat -> thm
  val rat_less_th: Proof.context -> typ -> Rat.rat -> Rat.rat -> thm
  val rat_fold_reduce: term -> term
  val rat_fold_conv: Proof.context -> conv

  val shift_neg_once_cv: theory -> conv
  val shift_neg_cv: theory -> conv

  val rewrite_with_coeff: theory -> conv
  val rewrite_without_coeff: conv
  val combine_terms_once: (term * term -> thm option) -> Proof.context -> conv
  val combine_terms: (term * term -> thm option) -> Proof.context -> conv
  val combine_terms_gen: (term * term -> thm option) -> Proof.context -> conv

  val combine_terms_ineq_cv:
      (term * term -> thm option) -> Proof.context -> conv

  val add_rat_arith_proofsteps: theory -> theory
end;

structure Rat_Arith : RAT_ARITH =
struct

val ratT = @{typ rat}

fun dest_rat r =
    (case r of
         Const (@{const_name inverse}, _) $ d =>
         Rat.rat_of_quotient (1, dest_numc d)
       | Const (@{const_name uminus}, _) $ r' => Rat.neg (dest_rat r')
       | Const (@{const_name of_rat}, _) $ r' => dest_rat r'
       | Const (@{const_name Fract}, _) $ n $ d =>
         Rat.rat_of_quotient (dest_numc n, dest_numc d)
       | _ => Rat.rat_of_int (dest_numc r))
    handle AUTO2 _ => raise AUTO2 "dest_rat: invalid term."

fun mk_rat T r =
    let
      val (n, d) = Rat.quotient_of_rat r
    in
      if n < 0 then
        Const (@{const_name uminus}, T --> T) $ (mk_rat T (Rat.neg r))
      else if d = 1 then HOLogic.mk_number T n
      else if n = 1 then
        Const (@{const_name inverse}, T --> T) $ (HOLogic.mk_number T d)
      else if T = ratT then
        Const (@{const_name Fract}, intT --> intT --> ratT)
              $ mk_int n $ mk_int d
      else
        Const (@{const_name of_rat}, ratT --> T) $ (mk_rat ratT r)
    end

fun lookup_numc inst n = dest_rat (lookup_instn inst ("NUMC", n))
fun lookup_numc0 inst = lookup_numc inst 0
fun lookup_numc1 inst = lookup_numc inst 1
fun lookup_numc2 inst = lookup_numc inst 2

local
  val ctxt = @{context}
in

(* Obtain the theorem r <= s. *)
fun rat_le_th ctxt T r s =
    if not (Rat.le r s) then raise AUTO2 "rat_le_th: input"
    else prove_by_simp ctxt [] (
        Const (@{const_name less_eq}, T --> T --> boolT)
              $ mk_rat T r $ mk_rat T s)

(* Obtain the theorem r < s. *)
fun rat_less_th ctxt T r s =
    if not (Rat.lt r s) then raise AUTO2 "nat_less_th: input"
    else prove_by_simp ctxt [] (
        Const (@{const_name less}, T --> T --> boolT)
              $ mk_rat T r $ mk_rat T s)

fun rat_fold_reduce t =
    let
      val (f, (r1, r2)) = t |> dest_binop |> apsnd (apply2 dest_rat)
      val T = fastype_of t
    in
      case f of
          Const (@{const_name plus}, _) => mk_rat T (Rat.add r1 r2)
        | Const (@{const_name times}, _) => mk_rat T (Rat.mult r1 r2)
        | _ => t
    end
    handle AUTO2 _ => t

fun rat_fold_conv ctxt ct =
    let
      val t = Thm.term_of ct
      val t' = rat_fold_reduce t
      val ctxt' = ctxt addsimps [@{thm of_rat_divide},
                                 @{thm Fract_of_int_quotient}]
    in
      if t aconv t' then Conv.all_conv ct
      else rewr_obj_eq (prove_by_simp ctxt' [] (HOLogic.mk_eq (t, t'))) ct
    end

fun is_minus t =
    case t of
        Const (@{const_name uminus}, _) $ _ => true
      | _ => false

fun dest_minus t =
    case t of
        Const (@{const_name uminus}, _) $ t' => t'
      | _ => raise AUTO2 "dest_minus: not in minus form."

(* In r < s or r <= s, shift one minus term in either r or s to the
   other side. There are two corner cases to consider: if the minus
   term is the only term in r and s, and if the other side has no
   terms (equals zero).
 *)
fun shift_neg_once_cv thy ct =
    let
      val (f, (r, s)) = dest_binop (Thm.term_of ct)
      val is_strict =
          case f of
              Const (@{const_name less}, _) => true
            | Const (@{const_name less_eq}, _) => false
            | _ => raise AUTO2 "shift_neg_th: input should be inequality."

      val ac_info = Nat_Arith.plus_ac_on_typ thy (fastype_of r)
      val terms_r = ACUtil.dest_ac_l ac_info r
      val terms_s = ACUtil.dest_ac_l ac_info s
      val move_outmost = ACUtil.move_outmost ac_info
      val add_zero_cv = rewr_obj_eq (obj_sym @{thm add_0})
      val reduce_zero_cv = Conv.try_conv (rewr_obj_eq @{thm add_0})
    in
      case find_first is_minus terms_r of
          NONE =>
          (case find_first is_minus terms_s of
               NONE => Conv.no_conv ct
             | SOME u =>
               let
                 val diff_conv_th =
                     if is_strict then @{thm less_diff_conv_right}
                     else @{thm le_diff_conv_right}
               in
                 ((Conv.arg_conv (
                      (move_outmost u)
                          then_conv (if length terms_s = 1 then add_zero_cv
                                     else Conv.all_conv)))
                      then_conv (rewr_obj_eq diff_conv_th)
                      then_conv (Conv.arg1_conv reduce_zero_cv)) ct
               end)
        | SOME u =>
          let
            val diff_conv_th =
                if is_strict then @{thm less_diff_conv_left}
                else @{thm le_diff_conv_left}
          in
            ((Conv.arg1_conv (
                 (move_outmost u)
                     then_conv (if length terms_r = 1 then add_zero_cv
                                else Conv.all_conv)))
                 then_conv (rewr_obj_eq diff_conv_th)
                 then_conv (Conv.arg_conv reduce_zero_cv)) ct
          end
    end

fun shift_neg_cv thy = Conv.repeat_conv (shift_neg_once_cv thy)

fun shift_neg_prfstep_fn (nm, descs) =
    prfstep_custom
        nm descs PRIORITY_ADD
        (fn ((id, _), ths) => fn _ => fn {tbl, ...} =>
            let
              val thy = RewriteTable.theory_of tbl
              val th = the_single ths
              val t = prop_of' th
              val (_, (r, _)) = dest_binop t
              val ac_info = Nat_Arith.plus_ac_on_typ thy (fastype_of r)
              val cv = Conv.every_conv [
                    Conv.arg1_conv (Matcher.normalize_minus_assoc_l ac_info),
                    Conv.arg_conv (Matcher.normalize_minus_assoc_l ac_info),
                    shift_neg_cv thy]
              val th' = apply_to_thm' cv th
            in
              if prop_of' th' aconv prop_of' th then []
              else [Update.thm_update (id, th')]
            end)

(* Write any term as a constant times the remaining terms, with the
   constant at the right. For example, "a" becomes a * 1, "-a" becomes
   a * -1, and "a/2" becomes a * 1/2. For constant c, c becomes 1 * c.
 *)
fun rewrite_with_coeff thy ct =
    let
      val t = Thm.term_of ct
      val b_minus = is_minus t
      val t' = if b_minus then dest_minus t else t
      val ac_info = Nat_Arith.times_ac_on_typ thy (fastype_of t)
      val terms_t' = ACUtil.dest_ac_l ac_info t'
      val move_outmost = ACUtil.move_outmost ac_info
    in
      case find_first is_numc terms_t' of
          NONE =>
          if b_minus then rewr_obj_eq (obj_sym @{thm mult_minus1_right}) ct
          else rewr_obj_eq (obj_sym @{thm mult_1_right}) ct
        | SOME u =>
          if length terms_t' = 1 then
            rewr_obj_eq (obj_sym @{thm mult_1}) ct
          else if b_minus then
            ((Conv.arg_conv (move_outmost u))
                 then_conv (rewr_obj_eq @{thm minus_mult_right})) ct
          else move_outmost u ct
    end

(* Write a term times a constant without the constant when
   simpler. For example, a * 1 becomes a, a * -1 becomes -a, and 1 * c
   becomes c.
 *)
val rewrite_without_coeff =
    Conv.try_conv (
      Conv.first_conv (
        map rewr_obj_eq [
          @{thm mult_1}, @{thm mult_1_right}, @{thm mult_minus1_right},
          obj_sym @{thm minus_mult_right}]))

(* Find component terms of ct, considering inverse and removing units. *)
fun dest_ac_total_with_inv (ac_info as {unit_val, ...}) ct =
    ct |> ACUtil.normalize_minus ac_info
       |> rhs_of |> ACUtil.dest_ac_total ac_info
       |> filter_out (fn t => t aconv unit_val)

(* Conversion combining terms that are same except for a rational
   coefficient. Assume all terms in the input are in coefficient form
   (output of rewrite_with_coeff). equiv_fn is a function term * term
   -> thm option that produces the equality between s and t if they
   are equivalent.
 *)
fun combine_terms_once equiv_fn ctxt ct =
    let
      val t = Thm.term_of ct
      val thy = Proof_Context.theory_of ctxt
      val ac_info = Nat_Arith.plus_ac_on_typ thy (fastype_of t)
      val terms_t = ACUtil.dest_ac_l ac_info t
      fun check_equiv (t1, t2) =
          let
            val (_, (a1, _)) = dest_binop t1
            val (_, (a2, _)) = dest_binop t2
          in
            equiv_fn (a1, a2)
          end
      val pairs = all_distinct_pairs terms_t
      val length_ct = length terms_t
    in
      case get_index check_equiv pairs of
          NONE => Conv.no_conv ct
        | SOME (i, eq_th) =>
          let
            val (t1, t2) = nth pairs i
            (* Conversion on the two terms is the following in
               sequence: rewrite t1 using eq_th, apply distributivity,
               fold the constant addition, and remove if the constant
               is zero.
             *)
            val cv = Conv.every_conv [
                  Conv.arg_conv (Conv.arg1_conv (Conv.rewr_conv eq_th)),
                  rewr_obj_eq (obj_sym @{thm distrib_left}),
                  Conv.arg_conv (rat_fold_conv ctxt),
                  Conv.try_conv (rewr_obj_eq @{thm mult_zero_right})]
          in
            ((ACUtil.move_outmost2 ac_info (t1, t2))
                 then_conv (if length_ct > 2 then Conv.arg_conv cv else cv)
                 then_conv (ACUtil.normalize_unit ac_info)) ct
          end
    end

fun combine_terms equiv_fn ctxt =
    Conv.repeat_conv (combine_terms_once equiv_fn ctxt)

(* Same with combine terms, but convert to coefficient before and
   un-convert afterwards.
 *)
fun combine_terms_gen equiv_fn ctxt ct =
    let
      val t = Thm.term_of ct
      val thy = Proof_Context.theory_of ctxt
      val ac_info = Nat_Arith.plus_ac_on_typ thy (fastype_of t)
    in
      Conv.every_conv [
        Matcher.normalize_minus_assoc_l ac_info,
        ACUtil.ac_subterms_conv ac_info (rewrite_with_coeff thy),
        combine_terms equiv_fn ctxt,
        ACUtil.ac_subterms_conv ac_info rewrite_without_coeff,
        Matcher.normalize_minus_assoc_l ac_info] ct
    end

fun combine_terms_prfstep_fn (nm, pat) =
    prfstep_custom
        nm [WithTerm @{term_pat "?a::(?'a::comm_ring_1)"},
            WithTerm pat,
            Filter (neqp_filter "a" @{term_pat "?c * ?NUMC"})]
        PRIORITY_ADD
        (fn ((id, _), ths) => fn _ => fn {tbl, ctxt, ...} =>
            let
              val thy = RewriteTable.theory_of tbl

              (* eq1 is meta_eq from pat(inst) to item. *)
              val eq1 = nth ths 1
              val (lhs, rhs) = Thm.dest_equals (Thm.cprop_of eq1)
              val ac_info = Nat_Arith.plus_ac_on_typ thy (Thm.typ_of_cterm rhs)

              (* Combine terms on the left side (pat(inst)). *)
              val equiv_fn = RewriteTable.is_equiv_th id tbl
              val eq_th = combine_terms_gen equiv_fn ctxt lhs

              (* Check whether the result (rhs of eq_th) is different
                 and not more complicated than item (rhs).
               *)
              val item_args = rhs |> dest_ac_total_with_inv ac_info
                                  |> sort Term_Ord.fast_term_ord
              val res_args = eq_th |> rhs_of |> ACUtil.dest_ac_l ac_info
                                   |> sort Term_Ord.fast_term_ord
            in
              if length res_args > length item_args orelse
                 eq_list (op aconv) (res_args, item_args) then []
              else [Update.thm_update (
                       id, to_obj_eq (transitive_list [meta_sym eq1, eq_th]))]
            end)

val combine_terms_prfsteps =
    let
      val ctxt' = ctxt |> Variable.declare_term
                  @{term_pat "?a::(?'a::comm_ring_1)"}

      val pat_strs = [
        "?a * ?NUMCu + ?a * ?NUMCu1 + ?bu",
        "?a * ?NUMCu + -(?a * ?NUMCu1) + ?bu"
      ]
      val pats = map (read_pat ctxt') pat_strs
      fun prfstep_i i =
          combine_terms_prfstep_fn
              ("combine_terms_" ^ (string_of_int i), nth pats i)
    in
      map prfstep_i (0 upto (length pats - 1))
    end

fun combine_terms_ineq_cv equiv_fn ctxt ct =
    let
      val thy = Proof_Context.theory_of ctxt
      val rewr_th =
          case Term.head_of (Thm.term_of ct) of
              Const (@{const_name less}, _) => @{thm less_iff_diff_less_0}
            | Const (@{const_name less_eq}, _) => @{thm le_iff_diff_le_0}
            | _ => raise AUTO2 "combine_terms_ineq: input should be inequality."
    in
      Conv.every_conv [
        rewr_obj_eq rewr_th,
        Conv.arg1_conv (combine_terms_gen equiv_fn ctxt),
        shift_neg_cv thy] ct
    end

fun combine_terms_ineq_prfstep_fn (nm, descs) =
    prfstep_custom
        nm descs PRIORITY_ADD
        (fn ((id, _), ths) => fn items => fn {tbl, ctxt, ...} =>
            let
              val equiv_fn = RewriteTable.is_equiv_th id tbl
              val cv = combine_terms_ineq_cv equiv_fn ctxt
              val th = the_single (ths |> filter_out is_meta_eq_thm)
              val th' = apply_to_thm' cv th
              val {prop = ori_th, ...} = nth items 1

              (* Compare statement of th' and ori_th. Output th' only
                 if it does not have more terms.
               *)
              fun size_of_prop th =
                  let
                    val thy = RewriteTable.theory_of tbl
                    val (lhs, rhs) = th |> Thm.cprop_of |> Thm.dest_arg
                                        |> Thm.dest_binop
                    val ac_info =
                        Nat_Arith.plus_ac_on_typ thy (Thm.typ_of_cterm lhs)
                  in
                    length (maps (dest_ac_total_with_inv ac_info) [lhs, rhs])
                  end
            in
              if size_of_prop th' > size_of_prop ori_th then []
              else [Update.thm_update (id, th')]
            end)

fun ring_pat str =
    let
      val ctxt' = ctxt |> fold Variable.declare_term
                       [@{term_pat "?NUMC1::(?'a::linordered_idom)"},
                        @{term_pat "?a::(?'a::linordered_idom)"},
                        @{term_pat "?s::(?'a::linordered_idom)"}]
    in
      read_pat ctxt' str
    end

end  (* local ctxt = @{context}. *)

val add_rat_arith_proofsteps =
    fold add_prfstep_custom [
      (* Resolve equality facts with constants. *)
      ("compare_rat_consts",
       [WithFact (ring_pat "?NUMC1 = ?NUMC2"),
        Filter (fn _ => fn (_, inst) =>
                   not (Rat.eq (lookup_numc1 inst, lookup_numc2 inst)))],
       PRIORITY_RESOLVE,
       fn ((id, _), ths) => fn _ => fn {ctxt, ...} =>
          [Update.thm_update (id, contra_by_simp ctxt ths)]),

      (* Resolve inequality facts with constants. *)
      ("le_rat_consts",
       [WithFact (ring_pat "?NUMC1 <= ?NUMC2"),
        Filter (fn _ => fn (_, inst) =>
                   not (Rat.le (lookup_numc1 inst) (lookup_numc2 inst)))],
       PRIORITY_RESOLVE,
       fn ((id, _), ths) => fn _ => fn {ctxt, ...} =>
          [Update.thm_update (id, contra_by_simp ctxt ths)]),

      ("less_rat_consts",
       [WithFact (ring_pat "?NUMC1 < ?NUMC2"),
        Filter (fn _ => fn (_, inst) =>
                   not (Rat.lt (lookup_numc1 inst) (lookup_numc2 inst)))],
       PRIORITY_RESOLVE,
       fn ((id, _), ths) => fn _ => fn {ctxt, ...} =>
          [Update.thm_update (id, contra_by_simp ctxt ths)]),

      (* Cancel constants factors from both sides of an inequality. *)
      ("cancel_nonneg_factor_less",
       [WithTerm (ring_pat "?NUMC1"),
        WithFact (ring_pat "?NUMC1 * ?a < ?NUMC1 * ?b"),
        Filter (fn _ => fn (_, inst) =>
                   lookup_numc1 inst <> Rat.one andalso
                   Rat.le Rat.zero (lookup_numc1 inst))],
       PRIORITY_ADD,
       fn ((id, inst), ths) => fn _ => fn {ctxt, ...} =>
          let
            val c = lookup_instn inst ("NUMC", 1)
            val T = fastype_of c
            val ge0 = rat_le_th ctxt T Rat.zero (lookup_numc1 inst)
            val prem = the_single (ths |> filter_out is_meta_eq_thm)
            val th = [prem, ge0] MRS @{thm mult_left_less_imp_less}
          in
            [Update.thm_update (id, th)]
          end),

      ("cancel_positive_factor_le",
       [WithTerm (ring_pat "?NUMC1"),
        WithFact (ring_pat "?NUMC1 * ?a <= ?NUMC1 * ?b"),
        Filter (fn _ => fn (_, inst) =>
                   lookup_numc1 inst <> Rat.one andalso
                   Rat.lt Rat.zero (lookup_numc1 inst))],
       PRIORITY_ADD,
       fn ((id, inst), ths) => fn _ => fn {ctxt, ...} =>
          let
            val c = lookup_instn inst ("NUMC", 1)
            val T = fastype_of c
            val ge0 = rat_less_th ctxt T Rat.zero (lookup_numc1 inst)
            val prem = the_single (ths |> filter_out is_meta_eq_thm)
            val th = [prem, ge0] MRS @{thm mult_left_le_imp_le}
          in
            [Update.thm_update (id, th)]
          end),

      (* Positive times positive is positive, on constants. *)
      ("positive_coeff_gt_0",
       [WithFact (ring_pat "?a > 0"),
        WithTerm (ring_pat "?a * ?NUMC1"),
        Filter (fn _ => fn (_, inst) =>
                   lookup_numc1 inst <> Rat.one andalso
                   Rat.lt Rat.zero (lookup_numc1 inst))],
       PRIORITY_ADD,
       fn ((id, inst), ths) => fn _ => fn {ctxt, ...} =>
          let
            val c = lookup_instn inst ("NUMC", 1)
            val T = fastype_of c
            val ge0 = rat_less_th ctxt T Rat.zero (lookup_numc1 inst)
            val prem = the_single (ths |> filter_out is_meta_eq_thm)
            val th = [prem, ge0] MRS @{thm mult_pos_pos}
          in
            [Update.thm_update (id, th)]
          end),

      (* Fold of_nat on constants. *)
      ("of_nat_constant",
       [WithTerm @{term_pat "(of_nat ?NUMC)::(?'a::semiring_1)"}],
       PRIORITY_ADD,
       fn ((id, inst), _) => fn _ => fn {ctxt, ...} =>
          let
            val t = lookup_inst inst "NUMC"
            val n = dest_numc t
            val T = lookup_tyinst inst "'a"
            val of_nat_n = Const (@{const_name of_nat}, natT --> T) $ t
            val eq = HOLogic.mk_eq (of_nat_n, HOLogic.mk_number T n)
            val th = rewr_obj_eq (prove_by_simp ctxt [] eq) (cert ctxt of_nat_n)
          in
            [Update.thm_update (id, to_obj_eq th)]
          end)

    ] #> fold add_prfstep [
      shift_neg_prfstep_fn (
        "shift_neg_less_left",
        [WithFact (ring_pat "?ru + (-?s) < ?t"),
         Filter (neq_filter "s" "ru"),
         Filter (neqp_filter "ru" (ring_pat "?s + ?s'")),
         Filter (ac_atomic_filter @{const_name plus} "s")]),

      shift_neg_prfstep_fn (
        "shift_neg_less_left'",
        [WithFact (ring_pat "(-?s) + ?ru < ?t"),
         Filter (neq_filter "s" "ru"),
         Filter (neqp_filter "ru" (ring_pat "?s + ?s'")),
         Filter (ac_atomic_filter @{const_name plus} "s")]),

      shift_neg_prfstep_fn (
        "shift_neg_less_left''",
        [WithFact (ring_pat "?ru - ?s < ?t"),
         Filter (neq_filter "s" "ru"),
         Filter (neqp_filter "ru" (ring_pat "?s + ?s'")),
         Filter (ac_atomic_filter @{const_name plus} "s")]),

      shift_neg_prfstep_fn (
        "shift_neg_le_left",
        [WithFact (ring_pat "?ru + (-?s) <= ?t"),
         Filter (neq_filter "s" "ru"),
         Filter (neqp_filter "ru" (ring_pat "?s + ?s'")),
         Filter (ac_atomic_filter @{const_name plus} "s")]),

      shift_neg_prfstep_fn (
        "shift_neg_le_left'",
        [WithFact (ring_pat "(-?s) + ?ru <= ?t"),
         Filter (neq_filter "s" "ru"),
         Filter (neqp_filter "ru" (ring_pat "?s + ?s'")),
         Filter (ac_atomic_filter @{const_name plus} "s")]),

      shift_neg_prfstep_fn (
        "shift_neg_le_left''",
        [WithFact (ring_pat "?ru - ?s <= ?t"),
         Filter (neq_filter "s" "ru"),
         Filter (neqp_filter "ru" (ring_pat "?s + ?s'")),
         Filter (ac_atomic_filter @{const_name plus} "s")]),

      shift_neg_prfstep_fn (
        "shift_neg_less_right",
        [WithFact (ring_pat "?t < ?ru + (-?s)"),
         Filter (neq_filter "s" "ru"),
         Filter (neqp_filter "ru" (ring_pat "?s + ?s'")),
         Filter (ac_atomic_filter @{const_name plus} "s")]),

      shift_neg_prfstep_fn (
        "shift_neg_less_right'",
        [WithFact (ring_pat "?t < (-?s) + ?ru"),
         Filter (neq_filter "s" "ru"),
         Filter (neqp_filter "ru" (ring_pat "?s + ?s'")),
         Filter (ac_atomic_filter @{const_name plus} "s")]),

      shift_neg_prfstep_fn (
        "shift_neg_less_right''",
        [WithFact (ring_pat "?t < ?ru - ?s"),
         Filter (neq_filter "s" "ru"),
         Filter (neqp_filter "ru" (ring_pat "?s + ?s'")),
         Filter (ac_atomic_filter @{const_name plus} "s")]),

      shift_neg_prfstep_fn (
        "shift_neg_le_right",
        [WithFact (ring_pat "?t <= ?ru + (-?s)"),
         Filter (neq_filter "s" "ru"),
         Filter (neqp_filter "ru" (ring_pat "?s + ?s'")),
         Filter (ac_atomic_filter @{const_name plus} "s")]),

      shift_neg_prfstep_fn (
        "shift_neg_le_right'",
        [WithFact (ring_pat "?t <= (-?s) + ?ru"),
         Filter (neq_filter "s" "ru"),
         Filter (neqp_filter "ru" (ring_pat "?s + ?s'")),
         Filter (ac_atomic_filter @{const_name plus} "s")]),

      shift_neg_prfstep_fn (
        "shift_neg_le_right''",
        [WithFact (ring_pat "?t <= ?ru - ?s"),
         Filter (neq_filter "s" "ru"),
         Filter (neqp_filter "ru" (ring_pat "?s + ?s'")),
         Filter (ac_atomic_filter @{const_name plus} "s")]),

      combine_terms_ineq_prfstep_fn (
        "combine_terms_less",
        [WithTerm (ring_pat "?a"),
         WithFact (ring_pat "?a * ?NUMCu + ?bu < ?a * ?NUMCu1 + ?cu")]),

      combine_terms_ineq_prfstep_fn (
        "combine_terms_le",
        [WithTerm (ring_pat "?a"),
         WithFact (ring_pat "?a * ?NUMCu + ?bu <= ?a * ?NUMCu1 + ?cu")])

    ] #> fold add_prfstep combine_terms_prfsteps

end  (* structure Rat_Arith. *)

val _ = Theory.setup Rat_Arith.add_rat_arith_proofsteps

(* Prop-matching for negation of order. *)
val neg_order_matcher =
    let
      fun pre_match pat {tname, ...} (tbl as {ctxt, ...}) =
          if is_neg pat andalso is_linorder ctxt tname andalso
             get_arg_type tname <> natT then
            let
              val neg_pat = pat |> cert ctxt |> neg_ineq_cv |> rhs_of
            in
              Matcher.pre_match tbl (neg_pat, tname)
            end
          else false

      fun match pat {tname, prop, ...} (tbl as {ctxt, ...}) (id, inst) =
          if is_neg pat andalso is_linorder ctxt tname andalso
             get_arg_type tname <> natT then
            let
              val neg_pat = pat |> cert ctxt |> neg_ineq_cv |> rhs_of
              val insts' = Matcher.rewrite_match tbl (neg_pat, tname) (id, inst)
              fun process_inst (inst, eq_th) =
                  (inst,
                   prop |> Thm.equal_elim (make_trueprop_eq (meta_sym eq_th))
                        |> apply_to_thm' neg_ineq_back_cv)
            in
              map process_inst insts'
            end
          else []
    in
      {pre_match = pre_match, match = match}
    end

val _ = Theory.setup (ItemIO_Data.add_prop_matcher (TY_PROP, neg_order_matcher))
