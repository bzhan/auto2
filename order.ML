(* Ordering on natural numbers. *)

val TY_NAT_ORDER = "NAT_ORDER"

signature NAT_ORDER =
sig
  val add_reduce_plus_consts: theory -> theory

  datatype order_type =
           LESS | LESS_LMINUS | LESS_LPLUS | LESS_RMINUS | LESS_RPLUS |
           LE | LE_LMINUS | LE_LPLUS | LE_RMINUS | LE_RPLUS
  type order_info
  val order_diffs: order_type -> int -> int
  val order_diffs_inst: order_type -> Type.tyenv * Envir.tenv -> int
  val to_normal_th: order_type -> thm -> thm
  val order_info_to_prop: term * term * int -> term
  val get_nat_order_ritem: order_info -> raw_item
  val convert_compare_const: order_info -> order_info
  val get_to_nat_order_prfstep:
      theory -> string * string * order_type -> proofstep
  val to_nat_order_prfsteps: proofstep list
  val nat_eq_diff_prfstep: proofstep
  val get_nat_order_info: box_item -> order_info

  val convert_compare_const_prfstep_fn: proofstep_fn
  val convert_compare_const_prfstep: proofstep

  val transitive_match: box_id -> rewrite_table -> order_info -> order_info ->
                        (box_id * order_info) list
  val transitive_prfstep_fn: proofstep_fn
  val transitive_prfstep: proofstep

  val transitive_resolve:
      box_id -> rewrite_table -> order_info -> order_info -> (box_id * thm) list
  val transitive_resolve_prfstep_fn: proofstep_fn
  val transitive_resolve_prfstep: proofstep

  val single_resolve:
      box_id -> rewrite_table -> order_info -> (box_id * thm) list
  val single_resolve_prfstep_fn: proofstep_fn
  val single_resolve_prfstep: proofstep

  val nat_order_match_side: term -> term -> rewrite_table -> id_inst ->
                            (id_inst * int * thm) list
  val nat_order_match': term -> term * term -> rewrite_table -> id_inst ->
                        (id_inst * (order_type * int * thm)) list
  val nat_order_filt: term -> pre_filter option
  val nat_order_match: match_fn

  val single_resolve_match: box_id -> rewrite_type -> thm -> (box_id * thm) list
  val single_resolve_match_prfstep: proofstep list

  val shadow_nat_order_fn: proofstep_fn
  val shadow_nat_order: proofstep

  val shadow_nat_order_single_fn: proofstep_fn
  val shadow_nat_order_single: proofstep

  val string_of_nat_order: Proof.context -> order_info -> string
  val add_nat_order_proofsteps: theory -> theory
end;

structure Nat_Order : NAT_ORDER =
struct

local open Nat_Arith in

(* Fold one arithmetic operation on constants. *)

(* In expression x + n < y, fold n. *)
val fold_const_left =
    apply_to_thm (Conv.arg_conv (Conv.arg1_conv (Conv.arg_conv nat_fold_conv)))
(* In expression x < y + n, fold n. *)
val fold_const_right =
    apply_to_thm (Conv.arg_conv (Conv.arg_conv (Conv.arg_conv nat_fold_conv)))
(* In expression, x < y + n, fold y + 0 = y if n = 0. *)
val fold0_right =
    apply_to_thm (Conv.arg_conv (Conv.arg_conv nat_fold_conv0_right))

(* Reduce facts of the form x + m <= y + n and x + m < y + n, where m
   and n are numerical constants.
 *)
val add_reduce_plus_consts =
    fold add_prfstep_thm_fn [
      ("reduce_le_plus_consts",
       [WithFact @{term_pat "(?x::nat) + ?NUMC1 <= ?y + ?NUMC2"},
        Filter (fn _ => fn (_, inst) =>
                   lookup_numc1 inst <> 0 andalso lookup_numc2 inst <> 0)],
       [Update.ADD_ITEMS],
       (fn _ => fn ((_, inst), ths) =>
           let val (n1, n2) = (lookup_numc1 inst, lookup_numc2 inst) in
             if n1 >= n2 then
               ((nat_le_th n2 n1 :: ths) MRS @{thm reduce_le_plus_consts'})
                   |> fold_const_left
             else  (* n1 < n2 *)
               (ths MRS @{thm reduce_le_plus_consts}) |> fold_const_right
           end)),

      ("reduce_less_plus_consts",
       [WithFact @{term_pat "(?x::nat) + ?NUMC1 < ?y + ?NUMC2"},
        Filter (fn _ => fn (_, inst) =>
                   lookup_numc1 inst <> 0 andalso lookup_numc2 inst <> 0)],
       [Update.ADD_ITEMS],
       (fn _ => fn ((_, inst), ths) =>
           let val (n1, n2) = (lookup_numc1 inst, lookup_numc2 inst) in
             if n1 >= n2 then
               ((nat_le_th n2 n1 :: ths) MRS @{thm reduce_less_plus_consts'})
                   |> fold_const_left
             else  (* n1 < n2 *)
               (ths MRS @{thm reduce_less_plus_consts}) |> fold_const_right
           end))]

datatype order_type =
         LESS_LMINUS | LESS_LPLUS | LESS_RMINUS | LESS_RPLUS | LESS |
         LE_LMINUS | LE_LPLUS | LE_RMINUS | LE_RPLUS | LE

(* With (x, y, n, prop): If n >= 0, then prop is x <= y +
   n. Otherwise, prop is x + (~n) <= y.
 *)
type order_info = term * term * int * thm

(* For the given order_ty, convert the natural number n > 0 appearing
   in the expression to the signed difference in the normal form of
   the theorem.
 *)
fun order_diffs order_ty n =
    case order_ty of
        LESS_LMINUS => n - 1
      | LESS_LPLUS => ~(n + 1)
      | LESS_RMINUS => ~(n + 1)
      | LESS_RPLUS => n - 1
      | LESS => ~1
      | LE_LMINUS => n
      | LE_LPLUS => ~n
      | LE_RMINUS => 0  (* special *)
      | LE_RPLUS => n
      | LE => 0

(* Given inst (containing value for ?NUMC for cases other than LESS
   and LE), return the signed difference in the normal form of the
   theorem.
 *)
fun order_diffs_inst order_ty inst =
    case order_ty of
        LESS => ~1
      | LE => 0
      | _ => order_diffs order_ty (lookup_numc0 inst)

(* Conversion from a theorem to its normal form. *)
fun to_normal_th order_ty th =
    case order_ty of
        LESS_LMINUS => (th RS @{thm norm_less_lminus}) |> fold_const_right
      | LESS_LPLUS => (th RS @{thm norm_less_lplus}) |> fold_const_left
      | LESS_RMINUS => (th RS @{thm norm_less_rminus}) |> fold_const_left
      | LESS_RPLUS => (th RS @{thm norm_less_rplus}) |> fold_const_right
      | LESS => th RS @{thm norm_less}
      | LE_LMINUS => th RS @{thm norm_le_lminus}
      | LE_RMINUS => th RS @{thm norm_le_rminus}
      | LE => th RS @{thm norm_le}
      | _ => th

(* Obtain the normal form statement for given (x, y, diff). *)
fun order_info_to_prop (x, y, diff) =
    let
      val inst = fo_init |> update_env (("x",0), x) |> update_env (("y",0), y)
                         |> update_env (("n",0), mk_nat (Int.abs diff))
    in
      if diff >= 0 then
        Envir.subst_term inst @{term_pat "Trueprop ((?x::nat) <= ?y + ?n)"}
      else
        Envir.subst_term inst @{term_pat "Trueprop ((?x::nat) + ?n <= ?y)"}
    end

(* Given information for a NAT_ORDER item and its theorem, form the
   NAT_ORDER item. Verify that the theorem is in the right form.
 *)
fun get_nat_order_ritem (x, y, diff, th) =
    let
      val prop = order_info_to_prop (x, y, diff)
    in
      if prop aconv Thm.prop_of th then
        Fact (TY_NAT_ORDER, [x, y, mk_int diff], th)
      else let
        val ctxt = Proof_Context.init_global (Thm.theory_of_thm th)
        val _ = trace_t_ctxt ctxt "Expected:" prop
        val _ = trace_t_ctxt ctxt "Given:" (Thm.prop_of th)
      in
        raise AUTO2 "get_nat_order_ritem: wrong form of theorem."
      end
    end

(* Convert any NAT_ORDER info with comparison to a constant to one
   with comparison to zero.
 *)
fun convert_compare_const_x (info as (x, y, diff, th)) =
    if not (is_numc x) then info else
    let val xn = dest_numc x in
      (* Over integers, x <= y + diff means 0 <= y + (diff - x). *)
      if dest_numc x = 0 then info
      else if diff < 0 then
        (nat0, y, diff - xn, (th RS @{thm cv_const1}) |> fold_const_left)
      else (* diff >= 0 *) if diff - xn < 0 then
        (nat0, y, diff - xn, (th RS @{thm cv_const4}) |> fold_const_left)
      else (* diff - xn >= 0 *)
        (nat0, y, diff - xn, (th RS @{thm cv_const5}) |> fold_const_right)
    end

fun convert_compare_const_y (info as (x, y, diff, th)) =
    if not (is_numc y) then info else
    let val yn = dest_numc y in
      (* Over integers, x <= y + diff means x <= 0 + (y + diff). *)
      if dest_numc y = 0 then info
      else if diff < 0 andalso yn + diff >= 0 then
        (x, nat0, yn + diff, (th RS @{thm cv_const2}) |> fold_const_right)
      else if diff < 0 andalso yn + diff < 0 then
        (x, nat0, yn + diff, ([nat_less_th yn (~diff), th] MRS @{thm cv_const3})
                                 |> fold_const_left)
      else  (* diff >= 0 *)
        (x, nat0, yn + diff, (th RS @{thm cv_const6}) |> fold_const_right)
    end

val convert_compare_const = convert_compare_const_x #> convert_compare_const_y

(* Helper functions, decomposing a term into A + n or n + A (without
   matching).
 *)
fun dest_plus t =
    case t of Const (@{const_name plus}, _) $ A $ B =>
              if is_numc B andalso dest_numc B > 0 then SOME (A, dest_numc B)
              else NONE | _ => NONE

fun dest_plus' t =
    case t of Const (@{const_name plus}, _) $ A $ B =>
              if is_numc A andalso dest_numc A > 0 then SOME (B, dest_numc A)
              else NONE | _ => NONE

fun simp_in_plus_form (id, tbl) t =
    let val t' = RewriteTable.simp_val id tbl t in
      is_some (dest_plus t') orelse is_some (dest_plus' t')
    end

(* eq_x is a meta equality. Use it to rewrite x in an order info. *)
fun rewrite_info_x eq_x (x, y, diff, th) =
    let
      val (lhs, rhs) = Logic.dest_equals (Thm.prop_of eq_x)
      val _ = assert (lhs aconv x) "rewrite_info_x: invalid equality."
      val th' =
          if diff >= 0 then  (* rewrite x in x <= y + n. *)
            th |> apply_to_thm (
              Conv.arg_conv (Conv.arg1_conv (Conv.rewr_conv eq_x)))
          else  (* rewrite x in x + n <= y. *)
            th |> apply_to_thm (
              Conv.arg_conv (
                Conv.arg1_conv (Conv.arg1_conv (Conv.rewr_conv eq_x))))
    in
      (rhs, y, diff, th')
    end

(* eq_y is a meta equality. *)
fun rewrite_info_y eq_y (x, y, diff, th) =
    let
      val (lhs, rhs) = Logic.dest_equals (Thm.prop_of eq_y)
      val _ = assert (lhs aconv y) "rewrite_info_y: invalid equality."
      val th' =
          if diff >= 0 then  (* rewrite y in x <= y + n. *)
            th |> apply_to_thm (
              Conv.arg_conv (
                Conv.arg_conv (Conv.arg1_conv (Conv.rewr_conv eq_y))))
          else  (* rewrite y in x + n <= y. *)
            th |> apply_to_thm (
              Conv.arg_conv (Conv.arg_conv (Conv.rewr_conv eq_y)))
    in
      (x, rhs, diff, th')
    end

(* Create proofstep converting PROP item to NAT_ORDER item. *)
fun get_to_nat_order_prfstep thy (nm, pat_str, order_ty) =
    let
      val sch_xy = [@{term_pat "?x::nat"}, @{term_pat "?y::nat"}]
      val ctxt = (Proof_Context.init_global thy)
                     |> fold Variable.declare_term sch_xy
      val pat = Proof_Context.read_term_pattern ctxt pat_str
      val has_numc = member (op aconv) (map Var (Term.add_vars pat []))
                     @{term_pat "?NUMC::nat"}
      fun filt tbl (id, inst) =
          not (simp_in_plus_form (id, tbl) (lookup_inst inst "x")) andalso
          not (simp_in_plus_form (id, tbl) (lookup_inst inst "y")) andalso
          (if has_numc then lookup_numc0 inst > 0 else true)

      val descs = [WithFact pat, Filter filt]
      fun prfstep_fn ((id, inst), ths) {tbl, ...} =
          let
            val (x, y) = apply2 (lookup_inst inst) ("x", "y")
            val (simpx, simpy) = apply2 (RewriteTable.simplify id tbl) (x, y)
            val diff = order_diffs_inst order_ty inst
            val th' = to_normal_th order_ty (the_single ths)
            val info = (x, y, diff, th') |> rewrite_info_x simpx
                                         |> rewrite_info_y simpy
                                         |> convert_compare_const
          in
            [Update.AddItems {id = id, raw_items = [get_nat_order_ritem info]}]
          end
    in
      prfstep_custom thy nm descs [Update.ADD_ITEMS] prfstep_fn
    end

val to_nat_order_prfsteps =
    map (get_to_nat_order_prfstep @{theory}) [
      ("cv_nat_less_lminus", "?x - ?NUMC < ?y", LESS_LMINUS),
      ("cv_nat_less_lplus", "?x + ?NUMC < ?y", LESS_LPLUS),
      ("cv_nat_less_rminus", "?x < ?y - ?NUMC", LESS_RMINUS),
      ("cv_nat_less_rplus", "?x < ?y + ?NUMC", LESS_RPLUS),
      ("cv_nat_less", "?x < ?y", LESS),
      ("cv_nat_le_lminus", "?x - ?NUMC <= ?y", LE_LMINUS),
      ("cv_nat_le_lplus", "?x + ?NUMC <= ?y", LE_LPLUS),
      ("cv_nat_le_rminus", "?x <= ?y - ?NUMC", LE_RMINUS),
      ("cv_nat_le_rplus", "?x <= ?y + ?NUMC", LE_RPLUS),
      ("cv_nat_le", "?x <= ?y", LE)
    ]

(* Proofstep creating x <= y + n and x >= y + n from x = y + n. *)
val nat_eq_diff_prfstep =
    prfstep_custom
        @{theory} "nat_eq_diff"
        [WithFact @{term_pat "(?x::nat) = ?y + ?NUMC"},
         Filter (fn tbl => fn (id, inst) =>
                    let val (x, y) = apply2 (lookup_inst inst) ("x", "y") in
                      lookup_numc0 inst > 0 andalso
                      not (simp_in_plus_form (id, tbl) x) andalso
                      not (simp_in_plus_form (id, tbl) y) andalso
                      not (is_numc x) andalso not (is_numc y)
                    end)]
        [Update.ADD_ITEMS]
        (fn ((id, inst), ths) => fn {tbl, ...} =>
            let
              val (x, y) = (lookup_inst inst "x", lookup_inst inst "y")
              val (simpx, simpy) = apply2 (RewriteTable.simplify id tbl) (x, y)
              val diff = lookup_numc0 inst
              val th' = ths MRS @{thm nat_eq_to_ineqs}
              val info1 = (x, y, diff, th' RS @{thm conjunct1})
                              |> rewrite_info_x simpx |> rewrite_info_y simpy
              val info2 = (y, x, ~diff, th' RS @{thm conjunct2})
                              |> rewrite_info_x simpy |> rewrite_info_y simpx
            in
              [Update.AddItems {
                  id = id, raw_items = map get_nat_order_ritem [info1, info2]}]
            end)

(* Obtain quadruple x, y, diff, and theorem from item. *)
fun get_nat_order_info {tname, prop, ...} =
    let
      val (x, y, diff_t) = the_triple tname
    in
      (x, y, dest_numc diff_t, prop)
    end

(* Proofstep reducing NAT_ORDER with one side newly found to be
   constant to a NAT_ORDER with one side zero.
 *)
fun convert_compare_const_prfstep_fn items rtype _ =
    let
      val (x, y, diff, th) = get_nat_order_info (the_single items)
      val id = merged_id rtype items
      val tbl = RewriteTable.table_of_rtype rtype
      val equivs_x = (fo_table_match id tbl (@{term_pat "?NUMC::nat"}, x))
                         |> RewriteTable.replace_id_for_type rtype
      fun process_equiv_x ((id', _), eq_th) =
          let
            val info' = (x, y, diff, th) |> rewrite_info_x (meta_sym eq_th)
                                         |> convert_compare_const_x
          in
            Update.AddItems {id = id', raw_items = [get_nat_order_ritem info']}
          end

      val equivs_y = (fo_table_match id tbl (@{term_pat "?NUMC::nat"}, y))
                         |> RewriteTable.replace_id_for_type rtype
      fun process_equiv_y ((id', _), eq_th) =
          let
            val info' = (x, y, diff, th) |> rewrite_info_y (meta_sym eq_th)
                                         |> convert_compare_const_y
          in
            Update.AddItems {id = id', raw_items = [get_nat_order_ritem info']}
          end
    in
      map process_equiv_x equivs_x @ map process_equiv_y equivs_y
    end

val convert_compare_const_prfstep =
    {name = "nat_order_convert_compare_const",
     filt = [{ty_str = TY_NAT_ORDER, pre_filt = no_prereq_fn}],
     res_types = [Update.ADD_ITEMS],
     func = convert_compare_const_prfstep_fn}

(* Helper function for transitive_match'. *)
fun trans d1 d2 th1 th2 =
    if d1 < 0 andalso d2 < 0 then
      ([th1, th2] MRS @{thm trans1}) |> fold_const_left
    else if d1 >= 0 andalso d2 >= 0 then
      ([th1, th2] MRS @{thm trans2}) |> fold_const_right
    else if d1 < 0 andalso d2 >= 0 then
      if d2 >= (~d1) then
        ([th1, th2] MRS @{thm trans3}) |> fold_const_right
      else  (* d2 < (~d1) *)
        ([nat_less_th d2 (~d1), th1, th2] MRS @{thm trans4}) |> fold_const_left
    else  (* d1 >= 0 andalso d2 < 0 *)
      if d1 >= (~d2) then
        ([th1, th2] MRS @{thm trans5}) |> fold_const_right
      else
        ([nat_less_th d1 (~d2), th1, th2] MRS @{thm trans6}) |> fold_const_left

(* Apply transitivity to two NAT_ORDER infos. *)
fun transitive_match id tbl (x, y1, diff1, th1) (y2, z, diff2, th2) =
    let
      fun filt (id, _) =
          not (exists (RewriteTable.is_equiv id tbl) [(x, y1), (y2, z), (x, z)])
      val y_equivs = filter filt (RewriteTable.equiv_info tbl id (y2, y1))
      fun process_y_equiv (id', eq_th) =
          let
            val (_, _, _, th2') = (y2, z, diff2, th2) |> rewrite_info_x eq_th
            val res = trans diff1 diff2 th1 th2'
          in
            (id', (x, z, diff1 + diff2, res))
          end
    in
      map process_y_equiv y_equivs
    end

(* Version of transitive match on items. *)
fun transitive_prfstep_fn items rtype _ =
    let
      val (info1, info2) = apply2 get_nat_order_info (the_pair items)
      val id = merged_id rtype items
      val tbl = RewriteTable.table_of_rtype rtype
      val insts = (transitive_match id tbl info1 info2)
                      |> RewriteTable.replace_id_for_type' rtype
      fun process_trans_res (id', info') =
          Update.AddItems {
            id = id', raw_items = [get_nat_order_ritem info']}
    in
      map process_trans_res insts
    end

val transitive_prfstep =
    {name = "nat_order_transitive",
     filt = replicate 2 {ty_str = TY_NAT_ORDER, pre_filt = no_prereq_fn},
     res_types = [Update.ADD_ITEMS],
     func = transitive_prfstep_fn}

fun trans_resolve d1 d2 th1 th2 =
    if d1 < 0 andalso d2 < 0 then
      [nat_less_th 0 (~d1), th1, th2] MRS @{thm trans_resolve1}
    else if d1 < 0 andalso d2 >= 0 then
      [nat_less_th d2 (~d1), th1, th2] MRS @{thm trans_resolve2}
    else (* d1 >= 0 andalso d2 < 0 *)
      [nat_less_th d1 (~d2), th2, th1] MRS @{thm trans_resolve2}

(* Try to derive a contradiction from two NAT_ORDER items. *)
fun transitive_resolve id tbl (x1, y1, diff1, th1) (y2, x2, diff2, th2) =
    let
      val equivs =
          RewriteTable.fo_rewrite_match_list
              tbl [(false, (x2, x1)), (false, (y2, y1))] (id, fo_init)
      fun process_equiv ((id', _), ths) =
          let
            val (eq_x, eq_y) = the_pair ths
            (* First convert th2 to use y1 and x1. *)
            val (_, _, _, th2') = (y2, x2, diff2, th2) |> rewrite_info_x eq_y
                                                       |> rewrite_info_y eq_x
          in
            if diff1 + diff2 < 0 then
              [(id', trans_resolve diff1 diff2 th1 th2')]
            else if diff1 = 0 andalso diff2 = 0 then
              [(id', (map fold0_right [th1, th2'])
                         MRS @{thm Orderings.order_antisym})]
            else if diff1 + diff2 = 0 then
              [(id', [th1, th2'] MRS @{thm Orderings.order_antisym})]
            else []
          end
    in
      maps process_equiv equivs
    end

(* Version of transitive resolve on items. *)
fun transitive_resolve_prfstep_fn items rtype st =
    let
      val (info1, info2) = apply2 get_nat_order_info (the_pair items)
      val id = merged_id rtype items
      val tbl = RewriteTable.table_of_rtype rtype
      val thy = Status.theory_of st
      val insts = (transitive_resolve id tbl info1 info2)
                      |> RewriteTable.replace_id_for_type' rtype
    in
      map (Update.thm_update thy) insts
    end

val transitive_resolve_prfstep =
    {name = "nat_order_transitive_resolve",
     filt = replicate 2 {ty_str = TY_NAT_ORDER, pre_filt = no_prereq_fn},
     res_types = [Update.ADD_ITEMS, Update.RESOLVE_BOX],
     func = transitive_resolve_prfstep_fn}

(* Try to derive a contradiction from a single NAT_ORDER item. There
   are two types of resolves: when two sides are equal, and when the
   right side is zero (both with negative diff).
 *)
fun single_resolve id tbl (x1, x2, diff, th) =
    if diff >= 0 then []
    else if x2 aconv nat0 then
      [(id, [nat_less_th 0 (~diff), th] MRS @{thm single_resolve_const})]
    else let
      val x_equivs = RewriteTable.equiv_info tbl id (x1, x2)
      fun process_x_equiv (id', eq_th) =
          let
            val (_, _, _, th') = (x1, x2, diff, th) |> rewrite_info_x eq_th
            val res = [nat_less_th 0 (~diff), th'] MRS @{thm single_resolve}
          in
            (id', res)
          end
    in
      map process_x_equiv x_equivs
    end

(* Version of single resolve on items. *)
fun single_resolve_prfstep_fn items rtype _ =
    let
      val (item as {id, ...}) = the_single items
      val info = get_nat_order_info item
      val tbl = RewriteTable.table_of_rtype rtype
      val insts = (single_resolve id tbl info)
                      |> RewriteTable.replace_id_for_type' rtype
    in
      map (fn (id', th') => Update.ResolveBox {id = id', th = th'}) insts
    end

val single_resolve_prfstep =
    {name = "nat_order_single_resolve",
     filt = [{ty_str = TY_NAT_ORDER, pre_filt = no_prereq_fn}],
     res_types = [Update.RESOLVE_BOX],
     func = single_resolve_prfstep_fn}

(* Helper function for nat_order_match_side. Analyze pattern into P +
   n, n + P, or P - n, where n is a constant.
 *)
fun dest_minus t =
    case t of Const (@{const_name minus}, _) $ A $ B =>
              if is_numc B andalso dest_numc B > 0 then SOME (A, dest_numc B)
              else NONE | _ => NONE

(* Add 0 on the left. *)
fun add_0_eq ct = rewr_obj_eq (obj_sym @{thm Nat.plus_nat.add_0}) ct

val plus_nat_ct =
    cert @{context} (Const (@{const_name plus}, natT --> natT --> natT))
val minus_nat_ct =
    cert @{context} (Const (@{const_name minus}, natT --> natT --> natT))
fun nat_n_refl n = Thm.reflexive (cert @{context} (mk_nat n))
fun plus_n_eq eq n = comb_equiv (plus_nat_ct, [eq, nat_n_refl n])
fun plus_n_eq' n eq = comb_equiv (plus_nat_ct, [nat_n_refl n, eq])
fun minus_n_eq eq n = comb_equiv (minus_nat_ct, [eq, nat_n_refl n])
val plus_comm_eq = rewr_obj_eq (obj_sym @{thm add_ac(2)})

(* Match one side of an inequality on natural numbers. Return the
   tuple ((id', inst'), n, eq_th), where n is the signed difference.
 *)
fun nat_order_match_side pat x tbl (id, inst) =
    if is_some (dest_plus pat) then
      let
        val (p, n) = the (dest_plus pat)
        val insts = RewriteTable.fo_rewrite_match tbl (p, x) (id, inst)
        fun process_inst ((id', inst'), eq_th) =
            ((id', inst'), n, plus_n_eq eq_th n)
      in
        map process_inst insts
      end
    else if is_some (dest_plus' pat) then
      let
        val (p, n) = the (dest_plus' pat)
        val insts = RewriteTable.fo_rewrite_match tbl (p, x) (id, inst)
        fun process_inst ((id', inst'), eq_th) =
            ((id', inst'), n, plus_n_eq' n eq_th |> apply_to_rhs plus_comm_eq)
      in
        map process_inst insts
      end
    else let
      val numc_match =
          if has_vars pat orelse not (x aconv nat0) then []
          else fo_table_match id tbl (@{term_pat "?NUMC::nat"}, pat)
      fun process_numc_match ((id', inst'), eq_th) =
          let
            val n = lookup_numc0 inst'
            val th' = if n = 0 then meta_sym eq_th
                      else apply_to_rhs add_0_eq (meta_sym eq_th)
          in
            ((id', inst), n, th')
          end

      val minus_insts =
          if is_some (dest_minus pat) then
            let
              val (p, n) = the (dest_minus pat)
              val insts = RewriteTable.fo_rewrite_match tbl (p, x) (id, inst)
              fun process_inst ((id', inst'), eq_th) =
                  ((id', inst'), ~n, minus_n_eq eq_th n)
            in
              map process_inst insts
            end
          else []

      (* insts without modifications. *)
      val insts = if x aconv nat0 then []
                  else RewriteTable.fo_rewrite_match tbl (pat, x) (id, inst)
      fun process_inst ((id', inst'), eq_th) = ((id', inst'), 0, eq_th)
    in
      map process_numc_match numc_match @ minus_insts @ map process_inst insts
    end

(* Match both sides of pat against x and y, respectively. Here pat is
   a boolean inequality. The eq_th returned is from the instantiated
   pat to the normal form proposition.
 *)
fun nat_order_match' pat (x, y) (tbl as {ctxt, ...}) (id, inst) =
    let
      (* Classify t into A < B or A <= B. *)
      val (f, (patA, patB)) = pat |> strip_comb |> apsnd the_pair
      val is_strict =
          case f of
              Const (@{const_name less}, _) => true
            | Const (@{const_name less_eq}, _) => false
            | _ => raise AUTO2 "match_order: input should be inequality."
      val cf = cert ctxt f

      (* Assume at least one of nA and nB is zero. *)
      fun order_info (nA, nB) =
          if nB = 0 then
            if nA = 0 then if is_strict then LESS else LE
            else if nA > 0 then if is_strict then LESS_LPLUS else LE_LPLUS
            else (* nA < 0 *) if is_strict then LESS_LMINUS else LE_LMINUS
          else  (* nA = 0 *)
            if nB > 0 then if is_strict then LESS_RPLUS else LE_RPLUS
            else (* nB < 0 *) if is_strict then LESS_RMINUS else LE_RMINUS

      (* Now match A and B in sequence. *)
      val insts_A = nat_order_match_side patA x tbl (id, inst)
      fun process_inst_A ((id', inst'), nA, eqA) =
          let
            val insts_B = nat_order_match_side patB y tbl (id', inst')
            fun process_inst_B ((id'', inst''), nB, eqB) =
                if nA <> 0 andalso nB <> 0 then []
                else let
                  val eq_th = comb_equiv (cf, [eqA, eqB])
                  val order_ty = order_info (nA, nB)
                  val n = Int.abs (nA + nB)
                  val diff = order_diffs order_ty n
                in
                  [((id'', inst''), (order_ty, diff, eq_th))]
                end
          in
            maps process_inst_B insts_B
          end
    in
      maps process_inst_A insts_A
    end

fun nat_order_filt t =
    if fastype_of t = @{typ prop} andalso is_Trueprop t andalso
       (is_nat_order' t orelse is_nat_order' (get_neg' t)) then
      SOME {ty_str = TY_NAT_ORDER, pre_filt = no_prereq_fn}
    else NONE

val neg_ineq_cv =
    (Conv.try_conv o Conv.arg_conv o Conv.first_conv)
        (map rewr_obj_eq [@{thm Orderings.linorder_not_less},
                          @{thm Orderings.linorder_not_le}])

fun nat_order_match pat item (tbl as {ctxt, ...}) (id, inst) =
    if not (is_nat_order' pat orelse is_nat_order' (get_neg' pat)) then [] else
    let
      val (info1 as (x, y, _, _)) = get_nat_order_info item
      val is_neg = is_neg (HOLogic.dest_Trueprop pat)
      val neg_ct = (get_neg' pat) |> cert ctxt |> neg_ineq_cv |> Thm.rhs_of
      val neg_t = neg_ct |> Thm.term_of
      val negt_th = neg_ct |> Thm.trivial
      val insts =
          nat_order_match' (HOLogic.dest_Trueprop neg_t) (y, x) tbl (id, inst)
      fun process_inst ((id', inst'), (order_ty, diff2, eq_th)) =
          let
            val neg_t' = subst_term_norm inst' neg_t
            val negt_th' = negt_th |> subst_thm ctxt inst'
                                   |> send_to_hyps (cert ctxt neg_t')
            val th2 = (Thm.equal_elim (make_trueprop_eq eq_th) negt_th')
                          |> to_normal_th order_ty
            val resolves = transitive_resolve id' tbl info1 (y, x, diff2, th2)
            fun process_resolve (id'', contra_th) =
                if Thm.prop_of contra_th aconv prop_False then
                  [((id'', inst'),
                    contra_th |> Thm.implies_intr (cert ctxt neg_t')
                              |> rewrite_thm_from_contra_form
                              |> (if is_neg then I
                                  else apply_to_thm neg_ineq_cv))]
                else []
          in
            maps process_resolve resolves
          end
    in
      maps process_inst insts
    end

(* Self update removing ~ (x + n >= x) from DISJ. Given a boolean t,
   try to find theorem ~t.
 *)
fun single_resolve_match id rtype th =
    if not (is_nat_order (prop_of' th) orelse
            is_nat_order (get_neg (prop_of' th))) then [] else
    let
      val (tbl as {lat, ctxt, ...}) = RewriteTable.table_of_rtype rtype
      val th' = th |> apply_to_thm neg_ineq_cv
      val normed_t = prop_of' th'
      val (f, (A, B)) = normed_t |> strip_comb |> apsnd the_pair
      val insts_A = (nat_order_match' normed_t (A, A) tbl (id, fo_init))
                        |> RewriteTable.replace_id_for_type rtype
      val insts_B = (nat_order_match' normed_t (B, B) tbl (id, fo_init))
                        |> RewriteTable.replace_id_for_type rtype

      fun process_inst x ((id', _), (order_ty, diff2, eq_th)) =
          let
            val th'' = (Thm.equal_elim (make_trueprop_eq eq_th) th')
                           |> to_normal_th order_ty
          in
            single_resolve id' tbl (x, x, diff2, th'')
          end

      val const_ineqs =
          if not (is_numc A andalso is_numc B) then []
          else let
            val (nA, nB) = (dest_numc A, dest_numc B)
          in
            case f of
                Const (@{const_name less}, _) =>
                if nA >= nB then [(id, contra_by_arith ctxt [th'])] else []
              | Const (@{const_name less_eq}, _) =>
                if nA > nB then [(id, contra_by_arith ctxt [th'])] else []
              | _ => []
          end
    in
      (const_ineqs @
       maps (process_inst A) insts_A @ maps (process_inst B) insts_B)
          |> max_partial (fn (i,_) => fn (j,_) => BoxID.is_eq_ancestor lat i j)
    end

val single_resolve_match_prfstep =
    Logic_ProofSteps.disj_self_update_gen (
      single_resolve_match, "disj_nat_order_contra",
      fn t => is_nat_order t orelse is_nat_order (get_neg t))

(* Shadow the second item if it is looser than the first (same x and
   y, but larger diff.
 *)
fun shadow_nat_order_fn items rtype _ =
    let
      val ((x1, y1, d1, _), (x2, y2, d2, _)) =
          apply2 get_nat_order_info (the_pair items)
    in
      if d1 > d2 then [] else
      let
        val id = merged_id rtype items
        val (tbl as {lat, ...}) = RewriteTable.table_of_rtype rtype
        val equivs =
            (RewriteTable.fo_rewrite_match_list
                 tbl [(false, (x1, x2)), (false, (y1, y2))] (id, fo_init))
                |> RewriteTable.replace_id_for_type rtype
                |> map (fn ((id', _), _) => id')
                |> max_partial (BoxID.is_eq_ancestor lat)
      in
        map (fn id' => Update.ShadowItem {id = id', item = nth items 1}) equivs
      end
    end

val shadow_nat_order =
    {name = "shadow_nat_order",
     filt = replicate 2 {ty_str = TY_NAT_ORDER, pre_filt = no_prereq_fn},
     res_types = [Update.SHADOW_ITEM],
     func = shadow_nat_order_fn}

(* Shadow the given item if it is trivial. There are two cases: when
   two sides are equal, and when the left side is zero (both with
   positive diff).
 *)
fun shadow_nat_order_single_fn items rtype _ =
    let
      val (item as {id, ...}) = the_single items
      val (x1, x2, d, _) = get_nat_order_info item
    in
      if d < 0 then []
      else if x1 aconv nat0 then
        [Update.ShadowItem {id = id, item = item}]
      else let
        val (tbl as {lat, ...}) = RewriteTable.table_of_rtype rtype
        val equivs =
            (RewriteTable.fo_rewrite_match_list
                 tbl [(false, (x1, x2))] (id, fo_init))
                |> RewriteTable.replace_id_for_type rtype
                |> map (fn ((id', _), _) => id')
                |> max_partial (BoxID.is_eq_ancestor lat)
      in
        map (fn id' => Update.ShadowItem {id = id', item = item}) equivs
      end
    end

fun string_of_nat_order ctxt (x, y, diff, th) =
    if x aconv nat0 andalso diff < 0 then  (* 0 + n <= y *)
      th |> apply_to_thm (Conv.arg_conv (Conv.arg1_conv nat_fold_conv0_left))
         |> Thm.prop_of |> pretty_term ctxt |> str
    else if y aconv nat0 andalso diff >= 0 then  (* x <= 0 + n *)
      th |> apply_to_thm (Conv.arg_conv (Conv.arg_conv nat_fold_conv0_left))
         |> Thm.prop_of |> pretty_term ctxt |> str
    else if diff = 0 then  (* x <= y + 0 *)
      th |> apply_to_thm (Conv.arg_conv (Conv.arg_conv nat_fold_conv0_right))
         |> Thm.prop_of |> pretty_term ctxt |> str
    else
      th |> Thm.prop_of |> pretty_term ctxt |> str

val shadow_nat_order_single =
    {name = "shadow_nat_order_single",
     filt = [{ty_str = TY_NAT_ORDER, pre_filt = no_prereq_fn}],
     res_types = [Update.SHADOW_ITEM],
     func = shadow_nat_order_single_fn}

val add_nat_order_proofsteps =
    fold add_prfstep (
      to_nat_order_prfsteps @
      [nat_eq_diff_prfstep, convert_compare_const_prfstep] @
      [transitive_prfstep, transitive_resolve_prfstep, single_resolve_prfstep] @
      single_resolve_match_prfstep @
      [shadow_nat_order, shadow_nat_order_single]

    ) #> fold ItemIO_Data.add_item_to_th [
      (nat_order_filt, nat_order_match)

    ] #> fold ItemIO_Data.add_str_of_item [
      (TY_NAT_ORDER,
       fn ctxt => fn (tname, th) =>
          let
            val (x, y, diff_t) = the_triple tname
            val diff = dest_numc diff_t
          in "ORDER " ^ string_of_nat_order ctxt (x, y, diff, th) end)
    ]

end
end

val _ = Theory.setup (Nat_Order.add_reduce_plus_consts)
val _ = Theory.setup (Nat_Order.add_nat_order_proofsteps)
