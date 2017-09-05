(* Ordering on natural numbers. *)

val TY_NAT_ORDER = "NAT_ORDER"

signature NAT_ORDER =
sig
  val is_order: term -> bool

  datatype order_type =
           LESS | LESS_LMINUS | LESS_LPLUS | LESS_RMINUS | LESS_RPLUS |
           LE | LE_LMINUS | LE_LPLUS | LE_RMINUS | LE_RPLUS
  type order_info
  val to_normal_th: order_type -> thm -> thm
  val th_to_ritem: thm -> raw_item
  val th_to_normed_ritems: thm -> raw_item list
  val to_nat_order_prfstep_templ: string * term -> proofstep
  val to_nat_order_prfsteps: proofstep list
  val nat_eq_diff_prfstep: proofstep

  val get_nat_order_info: box_item -> order_info
  val nat_order_typed_matcher: item_matcher
  val transitive: proofstep
  val transitive_resolve: proofstep
  val single_resolve: proofstep
  val single_resolve_zero: proofstep

  val nat_order_match: term -> box_item -> Proof.context -> id_inst ->
                       id_inst_th list
  val nat_order_matcher: item_matcher
  val nat_order_noteq_matcher: item_matcher
  val nat_order_single_match: term -> box_item -> Proof.context -> id_inst ->
                              id_inst_th list
  val nat_order_single_matcher: item_matcher

  val shadow_nat_order: proofstep
  val shadow_nat_order_single: proofstep

  val string_of_nat_order: Proof.context -> term * term * int * thm -> string
  val output_nat_order: Proof.context -> term list * thm -> string
  val add_nat_order_proofsteps: theory -> theory
end;

structure Nat_Order : NAT_ORDER =
struct

local
  open UtilArith
  open Nat_Arith
in

(* Fold one arithmetic operation on constants. *)

(* In expression x + n < y, fold n. *)
val fold_const_left =
    apply_to_thm' (Conv.arg1_conv (Conv.arg_conv nat_fold_conv))

(* In expression x < y + n, fold n. *)
val fold_const_right =
    apply_to_thm' (Conv.arg_conv (Conv.arg_conv nat_fold_conv))

(* Whether the given term is < or <= on natural numbers. *)
fun is_less t =
    case t of Const (@{const_name less}, _) $ _ $ _ => true
            | _ => false

fun is_less_eq t =
    case t of Const (@{const_name less_eq}, _) $ _ $ _ => true
            | _ => false

fun is_order t = is_less t orelse is_less_eq t

datatype order_type =
         LESS_LMINUS | LESS_LPLUS | LESS_RMINUS | LESS_RPLUS | LESS |
         LE_LMINUS | LE_LPLUS | LE_RMINUS | LE_RPLUS | LE

(* The first three values (x, y, n) specify a NAT_ORDER item, and the
   last value provides theorem justifying it. If n >= 0, then the
   theorem is x <= y + n. Otherwise, the theorem is x + (~n) <= y.
 *)
type order_info = cterm * cterm * int * thm

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

(* eq_x is a meta equality. Use it to rewrite x in an order info. *)
fun rewrite_info_x eq_x (cx, cy, diff, th) =
    let
      val _ = assert (Thm.lhs_of eq_x aconvc cx)
                     "rewrite_info_x: invalid equality."
      val th' =
          if diff >= 0 then  (* rewrite x in x <= y + n. *)
            th |> apply_to_thm' (Conv.arg1_conv (Conv.rewr_conv eq_x))
          else  (* rewrite x in x + n <= y. *)
            th |> apply_to_thm' (Conv.arg1_conv (
                                    Conv.arg1_conv (Conv.rewr_conv eq_x)))
    in
      (Thm.rhs_of eq_x, cy, diff, th')
    end

(* eq_y is a meta equality. Use it to rewrite y in an order info. *)
fun rewrite_info_y eq_y (cx, cy, diff, th) =
    let
      val _ = assert (Thm.lhs_of eq_y aconvc cy)
                     "rewrite_info_y: invalid equality."
      val th' =
          if diff >= 0 then  (* rewrite y in x <= y + n. *)
            th |> apply_to_thm' (Conv.arg_conv (
                                   Conv.arg1_conv (Conv.rewr_conv eq_y)))
          else  (* rewrite y in x + n <= y. *)
            th |> apply_to_thm' (Conv.arg_conv (Conv.rewr_conv eq_y))
    in
      (cx, Thm.rhs_of eq_y, diff, th')
    end

fun th_to_ritem th =
    let
      val (x, y, n) = NatOrder.dest_ineq (prop_of' th)
    in
      Fact (TY_NAT_ORDER, [x, y, mk_int n], th)
    end

fun th_to_normed_ritems th =
    let
      val th' = NatOrder.norm_ineq_th th
      val minus_th = the_list (NatOrder.norm_ineq_minus_th th)
    in
      map th_to_ritem (th' :: minus_th)
    end

(* Template for proofsteps converting a PROP item to a NAT_ORDER
   item. The proofstep simplifies the instantiations of x and y, and
   verifies that the simplified terms are not in plus form. If the
   result is a comparison with a constant, it is converted to a
   comparison with zero.
 *)
fun to_nat_order_prfstep_templ (prfstep_name, pat) =
    ProofStep.prfstep_custom
        prfstep_name
        [WithProp pat]
        PRIORITY_SHADOW
        (fn ((id, _), ths) => fn items => fn _ =>
            [AddItems {id = id, sc = NONE,
                       raw_items = maps th_to_normed_ritems ths},
             ShadowItem {id = id, item = hd items}])

val to_nat_order_prfsteps =
    map to_nat_order_prfstep_templ [
      ("cv_nat_order", @{term_pat "(?x::nat) < ?y"}),
      ("cv_nat_order2", @{term_pat "(?x::nat) <= ?y"})
    ]

val nat_eq_diff_prfstep =
    ProofStep.prfstep_custom
      "nat_eq_diff"
      [WithItem (TY_EQ, @{term_pat "(?x::nat) = ?y"})]
      PRIORITY_ADD
      (fn ((id, _), _) => fn items => fn _ =>
          let
            val {prop, ...} = the_single items
            val (lhs, rhs) = prop |> prop_of' |> Util.dest_binop_args
          in
            if NatOrder.is_plus_const lhs orelse
               NatOrder.is_plus_const rhs orelse
               is_numc lhs orelse is_numc rhs then
              let
                val prop' = to_meta_eq prop
                val ths = (prop' RS @{thm eq_to_ineqs}) |> UtilLogic.split_conj_th
              in
                [AddItems {id = id, sc = NONE,
                           raw_items = maps th_to_normed_ritems ths}]
              end
            else []
          end)

(* Obtain quadruple x, y, diff, and theorem from item. *)
fun get_nat_order_info {tname, prop, ...} =
    let
      val (cx, cy, cdiff_t) = the_triple tname
    in
      (cx, cy, dest_numc (Thm.term_of cdiff_t), prop)
    end

val nat_order_typed_matcher =
    let
      fun pre_match pat {tname, ...} ctxt =
          Matcher.pre_match_head
              ctxt (pat, Thm.cterm_of ctxt (HOLogic.mk_tuple (map Thm.term_of tname)))

      fun match pat (item as {tname = cts, ...}) ctxt (id, inst) =
          let
            val pats = HOLogic.strip_tuple pat
            val insts' = Matcher.rewrite_match_list
                             ctxt (map (pair false) (pats ~~ cts)) (id, inst)
            fun process_inst (inst, ths) =
                let
                  (* eq_x: pat_x(env) == x, eq_y: pat_y(env) = y *)
                  val (eq_x, eq_y, eq_n) = the_triple ths
                in
                  if Thm.is_reflexive eq_n then
                    let
                      val (_, _, _, prop) =
                          item |> get_nat_order_info
                               |> rewrite_info_x (meta_sym eq_x)
                               |> rewrite_info_y (meta_sym eq_y)
                    in
                      [(inst, prop)]
                    end
                  else []
                end
          in
            maps process_inst insts'
          end
    in
      {pre_match = pre_match, match = match}
    end

(* Apply transitivity to two NAT_ORDER infos. *)
val transitive =
    ProofStep.prfstep_custom
        "nat_order_transitive"
        [WithItem (TY_NAT_ORDER, @{term_pat "(?x, ?y, ?m)"}),
         WithItem (TY_NAT_ORDER, @{term_pat "(?y, ?z, ?n)"}),
         Filter (neq_filter @{term_pat "?x ~= ?y"}),
         Filter (neq_filter @{term_pat "?y ~= ?z"}),
         Filter (neq_filter @{term_pat "?x ~= ?z"})]
        PRIORITY_ADD
        (fn ((id, _), ths) => fn _ => fn _ =>
            let
              val (th1, th2) = the_pair ths
              val item' = th_to_ritem (NatOrder.combine_ineqs th1 th2)
            in
              [AddItems {id = id, sc = NONE, raw_items = [item']}]
            end)

(* Helper function for transitive resolve. *)
fun trans_resolve th1 th2 =
    let
      val (_, _, d1) = NatOrder.dest_ineq (prop_of' th1)
      val (_, _, d2) = NatOrder.dest_ineq (prop_of' th2)
    in
      if d1 < 0 andalso d2 < 0 then
        [nat_less_th 0 (~d1), th1, th2] MRS @{thm trans_resolve1}
      else if d1 < 0 andalso d2 >= 0 then
        [nat_less_th d2 (~d1), th1, th2] MRS @{thm trans_resolve2}
      else (* d1 >= 0 andalso d2 < 0 *)
        [nat_less_th d1 (~d2), th2, th1] MRS @{thm trans_resolve2}
    end

(* Try to derive a contradiction from two NAT_ORDER items. *)
val transitive_resolve =
    ProofStep.prfstep_custom
        "nat_order_transitive_resolve"
        [WithItem (TY_NAT_ORDER, @{term_pat "(?x, ?y, ?m)"}),
         WithItem (TY_NAT_ORDER, @{term_pat "(?y, ?x, ?n)"})]
        PRIORITY_RESOLVE
        (fn ((id, inst), ths) => fn _ => fn _ =>
            let
              val m = dest_numc (lookup_inst inst "m")
              val n = dest_numc (lookup_inst inst "n")
              val (th1, th2) = the_pair ths
              (* Fold x <= y + 0 to x <= y. *)
              val fold0 = apply_to_thm' (Conv.arg_conv nat_fold_conv0_right)
              val try_fold0l = Conv.try_conv nat_fold_conv0_left
              val res_ths =
                  if m + n < 0 then [trans_resolve th1 th2]
                  else if m = 0 andalso n = 0 then
                    [(map fold0 [th1, th2]) MRS @{thm Orderings.order_antisym}]
                  else if m + n = 0 then
                    (* Fold 0 at left in case x or y is zero. *)
                    [([th1, th2] MRS @{thm Orderings.order_antisym})
                         |> apply_to_thm' (Conv.arg_conv try_fold0l)
                         |> apply_to_thm' (Conv.arg1_conv try_fold0l)]
                  else []
            in
              map (fn th => Update.thm_update (id, th)) res_ths
            end)

(* Try to derive a contradiction from a single NAT_ORDER item. There
   are two types of resolves: when two sides are equal, and when the
   right side is zero (both with negative diff).
 *)
val single_resolve =
    ProofStep.prfstep_custom
        "nat_order_single_resolve"
        [WithItem (TY_NAT_ORDER, @{term_pat "(?x, ?x, ?n)"})]
        PRIORITY_RESOLVE
        (fn ((id, inst), ths) => fn _ => fn _ =>
            let
              val n = dest_numc (lookup_inst inst "n")
              val th = the_single ths
            in
              if n < 0 then
                [Update.thm_update (
                    id, [nat_less_th 0 (~n), th] MRS @{thm single_resolve})]
              else []
            end)

val single_resolve_zero =
    ProofStep.prfstep_custom
        "nat_order_single_resolve_zero"
        [WithItem (TY_NAT_ORDER, @{term_pat "(?x, 0, ?n)"})]
        PRIORITY_RESOLVE
        (fn ((id, inst), ths) => fn _ => fn _ =>
            let
              val n = dest_numc (lookup_inst inst "n")
              val th = the_single ths
            in
              if n < 0 then
                [Update.thm_update (id, [nat_less_th 0 (~n), th]
                                            MRS @{thm single_resolve_const})]
              else []
            end)

(* Returns true if ty is either natT or a schematic type of sort
   linorder.
 *)
fun valid_type ctxt ty =
    case ty of
        TVar _ => Sign.of_sort (Proof_Context.theory_of ctxt)
                               (ty, ["Orderings.linorder"])
      | _ => (ty = natT)

(* Given t in inequality form, return whether the type of the argument
   is appropriate for nat_order_match: that is, either natT or a
   schematic type of sort linorder.
 *)
fun valid_arg_type ctxt t = valid_type ctxt (fastype_of (dest_arg t))

fun is_order_pat ctxt pat =
    (is_order pat andalso valid_arg_type ctxt pat) orelse
    (is_order (get_neg pat) andalso valid_arg_type ctxt (get_neg pat))

val less_nat = @{term "op <::nat => nat => bool"}
val le_nat = @{term "op <=::nat => nat => bool"}

(* Assuming t is an order. Return the simplified form of the negation of t. *)
fun get_neg_order t =
    if is_neg t then dest_not t
    else if is_less t then le_nat $ dest_arg t $ dest_arg1 t
    else if is_less_eq t then less_nat $ dest_arg t $ dest_arg1 t
    else raise Fail "get_neg_order"

fun is_plus_const_gen t =
    NatOrder.is_plus_const t orelse (is_numc t andalso not (t aconv nat0))

fun plus_const_of_gen t =
    if NatOrder.is_plus_const t then dest_arg1 t else nat0

fun rewr_side eq_th ct =
    if Thm.lhs_of eq_th aconvc ct then
      Conv.rewr_conv eq_th ct
    else if is_numc (Thm.term_of ct) then
      Conv.every_conv [rewr_obj_eq (obj_sym @{thm Nat.plus_nat.add_0}),
                       Conv.arg1_conv (Conv.rewr_conv eq_th)] ct
    else
      Conv.arg1_conv (Conv.rewr_conv eq_th) ct

(* Return a pair of terms to be matched. *)
fun analyze_pattern t =
    let
      val (lhs, rhs) = Util.dest_binop_args t
    in
      if is_plus_const_gen lhs then
        (plus_const_of_gen lhs, rhs,
         if is_less t then LESS_LPLUS else LE_LPLUS)
      else if is_plus_const_gen rhs then
        (lhs, plus_const_of_gen rhs,
         if is_less t then LESS_RPLUS else LE_RPLUS)
      else if NatOrder.is_minus_const lhs then
        (dest_arg1 lhs, rhs,
         if is_less t then LESS_LMINUS else LE_LMINUS)
      else if NatOrder.is_minus_const rhs then
        (lhs, dest_arg1 rhs,
         if is_less t then LESS_RMINUS else LE_RMINUS)
      else
        (lhs, rhs, if is_less t then LESS else LE)
    end

fun analyze_pattern2 t =
    let
      val (lhs, rhs) = Util.dest_binop_args t
    in
      if NatOrder.is_minus_const lhs andalso not (is_plus_const_gen rhs) then
        SOME (lhs, rhs, if is_less t then LESS else LE)
      else if NatOrder.is_minus_const rhs andalso not (is_plus_const_gen lhs) then
        SOME (lhs, rhs, if is_less t then LESS else LE)
      else NONE
    end

(* Matching function. *)
fun find_contradiction_item pat item ctxt (id, inst) =
    let
      val (x, y, d1, th1) = get_nat_order_info item

      fun process_pattern (pat_l, pat_r, order_ty) =
          let
            val pairs = [(false, (pat_l, y)), (false, (pat_r, x))]
          in
            map (pair order_ty)
                (Matcher.rewrite_match_list ctxt pairs (id, inst))
          end

      val insts = process_pattern (analyze_pattern pat)
      val insts2 = case analyze_pattern2 pat of
                       NONE => [] | SOME pattern => process_pattern pattern

      fun process_inst (order_ty, ((id', inst'), eq_ths)) =
          let
            val (eq_th1, eq_th2) = the_pair eq_ths
            val assum = pat |> Util.subst_term_norm inst'
                            |> mk_Trueprop |> Thm.cterm_of ctxt
            val th2 = assum |> Thm.assume
                            |> apply_to_thm' (Conv.arg1_conv (rewr_side eq_th1))
                            |> apply_to_thm' (Conv.arg_conv (rewr_side eq_th2))
                            |> to_normal_th order_ty
            val (_, _, d2) = NatOrder.dest_ineq (prop_of' th2)
          in
            if d1 + d2 < 0 then
              [((id', inst'),
                (trans_resolve th1 th2)
                    |> Thm.implies_intr assum
                    |> apply_to_thm UtilLogic.rewrite_from_contra_form)]
            else []
          end
    in
      maps process_inst (insts @ insts2)
    end

fun nat_order_match pat item ctxt (id, inst) =
    if not (is_order_pat ctxt pat) then [] else
    let
      val is_neg = is_neg pat
      val neg_pat = get_neg_order pat
      val res = find_contradiction_item neg_pat item ctxt (id, inst)
    in
      if is_neg then res
      else res |> map (apsnd (apply_to_thm' neg_ineq_cv))
    end

fun nat_order_pre_match pat _ ctxt = is_order_pat ctxt pat

(* Prop-matching with a NAT_ORDER item. *)
val nat_order_matcher =
    {pre_match = nat_order_pre_match, match = nat_order_match}

(* Use x < y to match x ~= y. *)
val nat_order_noteq_matcher =
    let
      fun get_insts pat item ctxt (id, inst) =
          if not (is_neg pat andalso is_eq_term (dest_not pat)) then ([], [])
          else let
            val (A, B) = pat |> dest_not |> dest_eq
            val (cx, cy, n, _) = get_nat_order_info item
          in
            if n >= 0 then ([], [])
            else (Matcher.rewrite_match_list
                      ctxt [(false, (A, cx)), (false, (B, cy))] (id, inst),
                  Matcher.rewrite_match_list
                      ctxt [(false, (B, cx)), (false, (A, cy))] (id, inst))
          end

      fun pre_match pat item ctxt =
          if not (is_neg pat andalso is_eq_term (dest_not pat)) then false
          else let
            val (A, B) = pat |> dest_not |> dest_eq
            val (cx, cy, n, _) = get_nat_order_info item
          in
            n < 0 andalso ((Matcher.pre_match ctxt (A, cx) andalso
                            Matcher.pre_match ctxt (B, cy)) orelse
                           (Matcher.pre_match ctxt (A, cy) andalso
                            Matcher.pre_match ctxt (A, cx)))
          end

      fun match pat item ctxt (id, inst) =
          if Util.has_vars pat then [] else
          let
            val (instAB, instBA) = get_insts pat item ctxt (id, inst)
            fun process_inst (inst', ths) =
                let
                  (* eq_x: (A/B) = x, eq_y: (B/A) = y *)
                  val (eq_x, eq_y) = the_pair ths
                  val (_, _, n, prop) = item |> get_nat_order_info
                                             |> rewrite_info_x (meta_sym eq_x)
                                             |> rewrite_info_y (meta_sym eq_y)
                in
                  (inst', [prop, nat_less_th 0 (~n)]
                              MRS @{thm nat_ineq_impl_not_eq})
                end
            fun switch_ineq (inst', th) = (inst', th RS @{thm HOL.not_sym})
          in
            map process_inst instAB @ (map (switch_ineq o process_inst) instBA)
          end
    in
      {pre_match = pre_match, match = match}
    end

(* Given pattern pat, find substitutions of pat that give rise to a
   contradiction.
 *)
fun find_contradiction pat ctxt (id, inst) =
    let
      fun process_pattern (pat_l, pat_r, order_ty) =
          map (fn (id', eq_th) =>
                  (order_ty,
                   (id', eq_th, Thm.reflexive (Thm.cterm_of ctxt pat_r))))
              (RewriteTable.equiv_info_t ctxt id (pat_l, pat_r))

      val insts = process_pattern (analyze_pattern pat)
      val insts2 = case analyze_pattern2 pat of
                       NONE => [] | SOME pattern => process_pattern pattern

      fun process_inst (order_ty, (id', eq_th1, eq_th2)) =
          let
            val assum = pat |> Util.subst_term_norm inst
                            |> mk_Trueprop |> Thm.cterm_of ctxt
            val norm_th =
                assum |> Thm.assume
                      |> apply_to_thm' (Conv.arg1_conv (rewr_side eq_th1))
                      |> apply_to_thm' (Conv.arg_conv (rewr_side eq_th2))
                      |> to_normal_th order_ty
            val (lhs, rhs) = Util.dest_binop_args (prop_of' norm_th)
          in
            if NatOrder.is_plus_const lhs andalso dest_arg1 lhs aconv rhs then
              let
                val d = dest_numc (dest_arg lhs)
              in
                [((id', inst),
                  ([nat_less_th 0 d, norm_th] MRS @{thm single_resolve})
                      |> Thm.implies_intr assum
                      |> apply_to_thm UtilLogic.rewrite_from_contra_form)]
              end
            else []
          end
    in
      maps process_inst (insts @ insts2)
    end

(* For patterns in the form m < n, where m and n are constants. *)
fun find_contradiction_trivial pat ctxt (id, inst) =
    let
      val (A, B) = Util.dest_binop_args pat
    in
      if not (is_numc A andalso is_numc B) then [] else
      if not (is_less pat andalso dest_numc A >= dest_numc B) andalso
         not (is_less_eq pat andalso dest_numc A > dest_numc B) then []
      else let
        val assum = pat |> mk_Trueprop |> Thm.cterm_of ctxt
      in
        [((id, inst),
          (contra_by_arith ctxt [Thm.assume assum])
              |> Thm.implies_intr assum
              |> apply_to_thm UtilLogic.rewrite_from_contra_form)]
      end
    end

(* For patterns in the form x < 0. *)
fun find_contradiction_trivial2 pat ctxt (id, inst) =
    let
      val (_, B) = Util.dest_binop_args pat
    in
      if is_less pat andalso B aconv nat0 then
        let
          val assum = pat |> mk_Trueprop |> Thm.cterm_of ctxt
        in
          [((id, inst),
            ([@{thm Nat.not_less0}, Thm.assume assum] MRS UtilBase.contra_triv_th)
                |> Thm.implies_intr assum
                |> apply_to_thm UtilLogic.rewrite_from_contra_form)]
        end
      else []
    end

(* Using term x to justify propositions of the form x <= x + n, where
   n >= 0. This follows the same general outline as nat_order_match.
 *)
fun nat_order_single_match pat _ ctxt (id, inst) =
    if not (is_order_pat ctxt pat) orelse Util.has_vars pat then [] else
    let
      val is_neg = is_neg pat
      val neg_pat = get_neg_order pat
      val (A, B) = Util.dest_binop_args neg_pat
      val res =
          if is_less neg_pat andalso B aconv nat0 then
            find_contradiction_trivial2 neg_pat ctxt (id, inst)
          else if is_numc A andalso is_numc B then
            find_contradiction_trivial neg_pat ctxt (id, inst)
          else
            find_contradiction neg_pat ctxt (id, inst)
    in
      if is_neg then res
      else res |> map (apsnd (apply_to_thm' neg_ineq_cv))
    end

val nat_order_single_matcher =
    {pre_match = nat_order_pre_match, match = nat_order_single_match}

(* Shadow the second item if it is looser than the first (same x and
   y, but larger diff.
 *)
val shadow_nat_order =
    ProofStep.gen_prfstep
        "shadow_nat_order"
        [WithItem (TY_NAT_ORDER, @{term_pat "(?x, ?y, ?m)"}),
         WithItem (TY_NAT_ORDER, @{term_pat "(?x, ?y, ?n)"}),
         Filter (fn _ => fn (_, inst) =>
                    dest_numc (lookup_inst inst "m") <=
                    dest_numc (lookup_inst inst "n")),
         ShadowSecond]

(* Shadow the given item if it is trivial. There are two cases: when
   two sides are equal, and when the left side is zero (both with
   nonnegative diff).
 *)
val shadow_nat_order_single =
    ProofStep.gen_prfstep
        "shadow_nat_order_single"
        [WithItem (TY_NAT_ORDER, @{term_pat "(?x, ?x, ?n)"}),
         Filter (fn _ => fn (_, inst) => dest_numc (lookup_inst inst "n") >= 0),
         ShadowFirst]

val shadow_nat_order_single_zero =
    ProofStep.gen_prfstep
        "shadow_nat_order_single_zero"
        [WithItem (TY_NAT_ORDER, @{term_pat "(0, ?x, ?n)"}),
         Filter (fn _ => fn (_, inst) => dest_numc (lookup_inst inst "n") >= 0),
         ShadowFirst]

fun string_of_nat_order ctxt (x, y, diff, th) =
    if x aconv nat0 andalso diff < 0 then  (* 0 + n <= y *)
      th |> apply_to_thm' (Conv.arg1_conv nat_fold_conv0_left)
         |> Thm.prop_of |> Syntax.string_of_term ctxt
    else if y aconv nat0 andalso diff >= 0 then  (* x <= 0 + n *)
      th |> apply_to_thm' (Conv.arg_conv nat_fold_conv0_left)
         |> Thm.prop_of |> Syntax.string_of_term ctxt
    else if diff = 0 then  (* x <= y + 0 *)
      th |> apply_to_thm' (Conv.arg_conv nat_fold_conv0_right)
         |> Thm.prop_of |> Syntax.string_of_term ctxt
    else
      th |> Thm.prop_of |> Syntax.string_of_term ctxt

fun output_nat_order ctxt (ts, th) =
    let
      val (x, y, diff_t) = the_triple ts
      val diff = dest_numc diff_t
    in
      "ORDER " ^ string_of_nat_order ctxt (x, y, diff, th)
    end

val add_nat_order_proofsteps =
    ItemIO.add_item_type (
      TY_NAT_ORDER, SOME (take 2), SOME output_nat_order

    ) #> ItemIO.add_typed_matcher (
      TY_NAT_ORDER, nat_order_typed_matcher

    ) #> fold ItemIO.add_prop_matcher [
      (TY_NAT_ORDER, nat_order_matcher),
      (TY_NAT_ORDER, nat_order_noteq_matcher),
      (TY_NULL, nat_order_single_matcher)

    ] #> fold add_prfstep (
      to_nat_order_prfsteps @
      [nat_eq_diff_prfstep,
       transitive, transitive_resolve, single_resolve, single_resolve_zero,
       shadow_nat_order, shadow_nat_order_single, shadow_nat_order_single_zero])

end

end

val _ = Theory.setup (Nat_Order.add_nat_order_proofsteps)
