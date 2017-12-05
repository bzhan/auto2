(* Normalization in natural numbers *)

signature NAT_RING =
sig
  val norm_mult_atom: conv
  val norm_mult_monomial: conv

  val dest_monomial: term -> term * int
  val norm_monomial: conv
  val combine_monomial: conv
  val norm_add_monomial: conv
  val norm_add_polynomial: conv
  val norm_mult_poly_monomial: conv
  val norm_mult_polynomials: conv
  val norm_full: conv
  val norm_ring_term: term -> term

  val nat_ring_equiv: proofstep
  val nat_ring_unit: proofstep
  val add_nat_ring_proofsteps: theory -> theory
end;

structure NatRing : NAT_RING =
struct

val mult_1 = @{thm mult_1}  (* 1 * a = a *)
val mult_1_right = @{thm mult_1_right}  (* a * 1 = a *)
val mult_0 = @{thm mult_0}  (* 0 * a = 0 *)
val mult_0_right = @{thm mult_0_right}  (* a * 0 = 0 *)
val add_0 = @{thm add_0}  (* 0 + a = a *)
val add_0_right = @{thm add_0_right}  (* a + 0 = a *)
val distrib_r = @{thm nat_distrib(1)}  (* (m + n) * k = m * k + n * k *)
val distrib_l = @{thm nat_distrib(2)}  (* a * (b + c) = a * b + a * c *)
val times_ac_info = Nat_Arith.times_ac_on_typ @{theory} natT
val plus_ac_info = Nat_Arith.plus_ac_on_typ @{theory} natT
val is_numc = UtilArith.is_numc
val is_plus = Nat_Arith.is_plus
val nat_fold_conv = Nat_Arith.nat_fold_conv

fun is_times t =
    case t of
        Const (@{const_name times}, _) $ _ $ _ => true
      | _ => false

fun is_zero t =
    case t of
        Const (@{const_name zero_class.zero}, _) => true
      | _ => false

fun is_one t =
    case t of
        Const (@{const_name one_class.one}, _) => true
      | _ => false

fun is_Suc t =
    case t of
        Const (@{const_name Suc}, _) $ _ => true
      | _ => false

fun compare_atom (t1, t2) =
    if is_numc t1 andalso is_numc t2 then EQUAL
    else if is_numc t1 then GREATER
    else if is_numc t2 then LESS
    else Term_Ord.term_ord (t1, t2)

fun norm_mult_atom ct =
    let
      val t = Thm.term_of ct
      val (arg1, arg2) = Util.dest_binop_args t
    in
      if is_one arg1 then rewr_obj_eq mult_1 ct
      else if is_one arg2 then rewr_obj_eq mult_1_right ct
      else if is_zero arg1 then rewr_obj_eq mult_0 ct
      else if is_zero arg2 then rewr_obj_eq mult_0_right ct
      else if is_times arg1 then
        case compare_atom (dest_arg arg1, arg2) of
            GREATER => Conv.every_conv [ACUtil.swap_cv times_ac_info,
                                        Conv.arg1_conv norm_mult_atom] ct
          | EQUAL =>
            if is_numc (dest_arg arg1) andalso is_numc arg2 then
              Conv.every_conv [ACUtil.assoc_cv times_ac_info,
                               Conv.arg_conv nat_fold_conv] ct
            else
              Conv.all_conv ct
          | _ => Conv.all_conv ct
      else
        case compare_atom (arg1, arg2) of
            GREATER => ACUtil.comm_cv times_ac_info ct
          | EQUAL =>
            if is_numc arg1 andalso is_numc arg2 then
              nat_fold_conv ct
            else
              Conv.all_conv ct
          | _ => Conv.all_conv ct
    end

fun norm_mult_monomial ct =
    let
      val t = Thm.term_of ct
      val (_, arg2) = Util.dest_binop_args t
    in
      if is_times arg2 then
        Conv.every_conv [ACUtil.assoc_sym_cv times_ac_info,
                         Conv.arg1_conv norm_mult_monomial,
                         norm_mult_atom] ct
      else
        norm_mult_atom ct
    end

(* Destruct t into the form arg * coeff, where coeff is a constant. *)
fun dest_monomial t =
    if is_times t andalso is_numc (dest_arg t) then
      (dest_arg1 t, UtilArith.dest_numc (dest_arg t))
    else if is_numc t then
      (Nat_Arith.mk_nat 1, UtilArith.dest_numc t)
    else
      (t, 1)

(* Normalize ct into the form arg * coeff.

   Example: a * 4 == a * 4, a == a * 1, 4 == 1 * 4.
 *)
fun norm_monomial ct =
    let
      val t = Thm.term_of ct
    in
      if is_times t andalso is_numc (dest_arg t) then
        Conv.all_conv ct
      else if is_numc t then
        rewr_obj_eq (obj_sym @{thm mult_1}) ct
      else
        rewr_obj_eq (obj_sym @{thm mult_1_right}) ct
    end

fun compare_monomial (t1, t2) =
    let
      val (arg1, _) = dest_monomial t1
      val (arg2, _) = dest_monomial t2
    in
      if is_one arg1 andalso is_one arg2 then EQUAL
      else if is_one arg1 then GREATER
      else if is_one arg2 then LESS
      else Term_Ord.term_ord (arg1, arg2)
    end

fun combine_monomial ct =
    Conv.every_conv [Conv.binop_conv norm_monomial,
                     rewr_obj_eq (obj_sym distrib_l),
                     Conv.arg_conv nat_fold_conv] ct

fun norm_add_monomial ct =
    let
      val t = Thm.term_of ct
      val (arg1, arg2) = Util.dest_binop_args t
    in
      if is_zero arg1 then rewr_obj_eq add_0 ct
      else if is_zero arg2 then rewr_obj_eq add_0_right ct
      else if is_plus arg1 then
        case compare_monomial (dest_arg arg1, arg2) of
            GREATER => Conv.every_conv [ACUtil.swap_cv plus_ac_info,
                                        Conv.arg1_conv norm_add_monomial] ct
          | EQUAL =>
            if is_numc (dest_arg arg1) andalso is_numc arg2 then
              Conv.every_conv [ACUtil.assoc_cv plus_ac_info,
                               Conv.arg_conv nat_fold_conv] ct
            else
              Conv.every_conv [ACUtil.assoc_cv plus_ac_info,
                               Conv.arg_conv combine_monomial] ct
          | _ => Conv.all_conv ct
      else
        case compare_monomial (arg1, arg2) of
            GREATER => ACUtil.comm_cv plus_ac_info ct
          | EQUAL =>
            if is_numc arg1 andalso is_numc arg2 then
              nat_fold_conv ct
            else
              combine_monomial ct
          | _ => Conv.all_conv ct
    end

fun norm_add_polynomial ct =
    let
      val t = Thm.term_of ct
      val (_, arg2) = Util.dest_binop_args t
    in
      if is_plus arg2 then
        Conv.every_conv [ACUtil.assoc_sym_cv plus_ac_info,
                         Conv.arg1_conv norm_add_polynomial,
                         norm_add_monomial] ct
      else
        norm_add_monomial ct
    end

fun norm_mult_poly_monomial ct =
    let
      val t = Thm.term_of ct
      val (arg1, _) = Util.dest_binop_args t
    in
      if is_plus arg1 then
        Conv.every_conv [rewr_obj_eq distrib_r,
                         Conv.arg1_conv norm_mult_poly_monomial,
                         Conv.arg_conv norm_mult_monomial,
                         norm_add_polynomial] ct
      else
        norm_mult_monomial ct
    end

fun norm_mult_polynomials ct =
    let
      val t = Thm.term_of ct
      val (_, arg2) = Util.dest_binop_args t
    in
      if is_plus arg2 then
        Conv.every_conv [rewr_obj_eq distrib_l,
                         Conv.arg1_conv norm_mult_polynomials,
                         Conv.arg_conv norm_mult_poly_monomial,
                         norm_add_polynomial] ct
      else
        norm_mult_poly_monomial ct
    end

fun norm_full ct =
    let
      val t = Thm.term_of ct
    in
      if is_plus t then
        Conv.every_conv [Conv.binop_conv norm_full,
                         norm_add_polynomial] ct
      else if is_times t then
        Conv.every_conv [Conv.binop_conv norm_full,
                         norm_mult_polynomials] ct
      else if is_Suc t then
        Conv.every_conv [rewr_obj_eq @{thm Nat.Suc_eq_plus1},
                         norm_full] ct
      else
        Conv.all_conv ct
    end

fun mk_plus (t1, t2) =
    Const (@{const_name plus}, natT --> natT --> natT) $ t1 $ t2

fun list_plus ts =
    let
      fun list_rev ts =
          case ts of
              [] => Nat_Arith.mk_nat 0
            | [t] => t
            | t :: ts' => mk_plus (list_rev ts', t)
    in
      list_rev (rev ts)
    end

fun mk_times (t1, t2) =
    Const (@{const_name times}, natT --> natT --> natT) $ t1 $ t2

fun list_times ts =
    let
      fun list_rev ts =
          case ts of
              [] => Nat_Arith.mk_nat 1
            | [t] => t
            | t :: ts' => mk_times (list_rev ts', t)
    in
      list_rev (rev ts)
    end

(* Term simplification on natural numbers. *)
type monomial = term list * int

(* Compare two monomials *)
fun compare_monomial_list ((l1, _), (l2, _)) =
    if null l1 andalso null l2 then EQUAL
    else if null l1 then GREATER
    else if null l2 then LESS
    else Term_Ord.term_ord (list_times l1, list_times l2)

(* Reduce a list of monomials: combine monomials of the same body. *)
fun reduce_monomial_list ls =
    if null ls then []
    else let
      val (head, rest) = (hd ls, reduce_monomial_list (tl ls))
    in
      if null rest then [head]
      else let
        val (l1, c1) = head
        val (l2, c2) = hd rest
      in
        if list_times l1 aconv list_times l2 then
          if c1 + c2 = 0 then tl rest
          else (l1, c1 + c2) :: tl rest
        else head :: rest
      end
    end

(* Multiply two monomials. *)
fun mult_monomial ((l1, c1), (l2, c2)) =
    ((l1 @ l2) |> sort compare_atom, c1 * c2)

(* Multiply two such lists: take the pairwise product, sort within
   each monomial, then sort the list of monomials.
 *)
fun mult_polynomial_term (ls1, ls2) =
    (Util.all_pairs (ls1, ls2))
        |> map mult_monomial
        |> sort compare_monomial_list
        |> reduce_monomial_list

fun add_polynomial_list (ls1, ls2) =
    (ls1 @ ls2) |> sort compare_monomial_list |> reduce_monomial_list

fun dest_ring_full t =
    if is_plus t then
      add_polynomial_list
          (dest_ring_full (dest_arg1 t), dest_ring_full (dest_arg t))
    else if is_times t then
      mult_polynomial_term (dest_ring_full (dest_arg1 t),
                            dest_ring_full (dest_arg t))
    else if is_Suc t then
      add_polynomial_list
          (dest_ring_full (dest_arg t), dest_ring_full (Nat_Arith.mk_nat 1))
    else if is_zero t then []
    else if is_one t then [([], 1)]
    else if is_numc t then [([], UtilArith.dest_numc t)]
    else [([t], 1)]

fun to_monomial (l, c) =
    if null l then mk_nat c
    else if c = 1 then list_times l
    else mk_times (list_times l, mk_nat c)

fun norm_ring_term t =
    let
      val dest_ring = dest_ring_full t
    in
      list_plus (map to_monomial dest_ring)
    end

fun dest_subs t =
    t |> dest_ring_full
      |> map fst |> flat

fun rewrite_on_eqs eqs ct =
    let
      val t = Thm.term_of ct
    in
      if is_times t orelse is_plus t then
        Conv.binop_conv (rewrite_on_eqs eqs) ct
      else if is_Suc t then
        Conv.arg_conv (rewrite_on_eqs eqs) ct
      else
        case find_first (fn eq => t aconv (Util.lhs_of eq)) eqs of
            NONE => Conv.all_conv ct
          | SOME eq_th => eq_th
    end

fun simp_ring_expr ctxt (id, cu) =
    let
      val u = Thm.term_of cu
      val cus = map (Thm.cterm_of ctxt) (dest_subs u)
    in
      if null cus then [(id, Thm.reflexive cu)] else
      cus |> map (RewriteTable.simplify_info ctxt)
          |> BoxID.get_all_merges_info ctxt
          |> BoxID.merge_box_with_info ctxt id
          |> map (fn (id', eqs) => (id', rewrite_on_eqs eqs cu))
    end

fun get_ring_head_equiv ctxt (id, cu) =
    let
      fun process_head_equiv (id', eq_th) =
          let
            val infos = simp_ring_expr ctxt (id', Thm.rhs_of eq_th)
          in
            map (BoxID.merge_eq_infos ctxt (id', eq_th)) infos
          end
    in
      cu |> RewriteTable.get_head_equiv ctxt
         |> BoxID.merge_box_with_info ctxt id
         |> maps process_head_equiv
         |> filter_out (Thm.is_reflexive o snd)
    end

(* Find ways to modify ct once by rewriting one of the subterms. *)
fun ring_expand_once ctxt (id, ct) =
    let
      val t = Thm.term_of ct
      val us = dest_subs t
      val cus = map (Thm.cterm_of ctxt) us
      fun get_equiv cu = get_ring_head_equiv ctxt (id, cu)

      fun process_info (id', eq) =
          (id', rewrite_on_eqs [eq] ct)
    in
      map process_info (maps get_equiv cus)
    end

(* Find all ways to write ct, up to a certain limit. *)
fun ring_expand ctxt (id, ct) =
    let
      val max_ac = Config.get ctxt AC_ProofSteps.max_ac

      fun ring_equiv_eq_better (id, th) (id', th') =
          let
            val seq1 = dest_subs (Util.rhs_of th)
            val seq2 = dest_subs (Util.rhs_of th')
          in
            Util.is_subseq (op aconv) (seq1, seq2) andalso
            BoxID.is_eq_ancestor ctxt id id'
          end

      fun has_ring_equiv_eq_better infos info' =
          exists (fn info => ring_equiv_eq_better info info') infos

      fun helper (old, new) =
          case new of
              [] => old
            | (id', eq_th) :: rest =>
              if length old + length new > max_ac then
                old @ take (max_ac - length old) new
              else let
                val old' = ((id', eq_th) :: old)
                val rhs_expand =
                    (ring_expand_once ctxt (id', Thm.rhs_of eq_th))
                        |> Util.max_partial ring_equiv_eq_better
                        |> map (BoxID.merge_eq_infos ctxt (id', eq_th))
                        |> filter_out (has_ring_equiv_eq_better (old' @ rest))
              in
                helper (old', rest @ rhs_expand)
              end

      (* Start term *)
      val start = simp_ring_expr ctxt (id, ct)
    in
      helper ([], start)
    end

fun is_nat_op_head t =
    is_plus t orelse is_times t orelse is_Suc t

fun nat_ring_equiv_fn ictxt item1 item2 =
    let
      val ctxt = IncrContext.context_of ictxt
      val {id = id1, tname = tname1, ...} = item1
      val {id = id2, tname = tname2, ...} = item2
      val (ct1, ct2) = (the_single tname1, the_single tname2)
      val (t1, t2) = (Thm.term_of ct1, Thm.term_of ct2)
      val id = BoxID.merge_boxes ctxt (id1, id2)
    in
      if Term_Ord.termless (t2, t1) then []
      else if RewriteTable.is_equiv id ctxt (ct1, ct2) then []
      else if not (is_nat_op_head t1) orelse not (is_nat_op_head t2) then []
      else let
        val expand1 = ring_expand ctxt (id, ct1)
        val expand2 = ring_expand ctxt (id, ct2)

        fun get_equiv ((id1, eq_th1), (id2, eq_th2)) =
            let
              val ct1 = Thm.rhs_of eq_th1
              val ct2 = Thm.rhs_of eq_th2
              val ts1 = dest_ring_full (Thm.term_of ct1)
              val ts2 = dest_ring_full (Thm.term_of ct2)
            in
              if eq_list (eq_pair (eq_list (op aconv)) (op =)) (ts1, ts2) then
                let
                  val eq_th1' = norm_full ct1
                  val eq_th2' = norm_full ct2
                  val id' = BoxID.merge_boxes ctxt (id1, id2)
                  val eq = Util.transitive_list [
                        eq_th1, eq_th1', meta_sym eq_th2', meta_sym eq_th2]
                in
                  [(id', to_obj_eq eq)]
                end
              else []
            end
      in
        (maps get_equiv (Util.all_pairs (expand1, expand2)))
            |> Util.max_partial (BoxID.id_is_eq_ancestor ctxt)
            |> IncrContext.replace_id_for_type' ictxt
            |> map (fn (id, th) => Update.thm_update (id, th))
      end
    end

val nat_ring_equiv =
    {name = "nat_ring_equiv",
     args = [TypedMatch (TY_TERM, @{term_pat "?m::nat"}),
             TypedMatch (TY_TERM, @{term_pat "?n::nat"})],
     priority = PRIORITY_ADD,
     func = TwoStep nat_ring_equiv_fn}

fun nat_ring_unit_fn ictxt item =
    let
      val ctxt = IncrContext.context_of ictxt
      val {id, tname, ...} = item
      val ct = the_single tname
      val t = Thm.term_of ct
    in
      if not (is_nat_op_head t) then []
      else let
        val expand = ring_expand ctxt (id, ct)

        fun process_expand (id', eq_th) =
            let
              val ct = Thm.rhs_of eq_th
              val ts = dest_ring_full (Thm.term_of ct)
            in
              if length ts <= 1 then
                let
                  val eq' = norm_full ct
                  val eq = Util.transitive_list [eq_th, eq']
                in
                  [(id', to_obj_eq eq)]
                end
              else []
            end
      in
        (maps process_expand expand)
            |> IncrContext.replace_id_for_type' ictxt
            |> map (fn (id, th) => Update.thm_update (id, th))
      end
    end

val nat_ring_unit =
    {name = "nat_ring_unit",
     args = [TypedMatch (TY_TERM, @{term_pat "?m::nat"})],
     priority = PRIORITY_ADD,
     func = OneStep nat_ring_unit_fn}

val add_nat_ring_proofsteps =
    fold add_prfstep [
      nat_ring_equiv, nat_ring_unit

    ] #> fold add_fixed_sc [
      ("nat_ring_equiv", 1), ("nat_ring_unit", 1)
    ]

end;  (* NatRing *)

val _ = Theory.setup NatRing.add_nat_ring_proofsteps
