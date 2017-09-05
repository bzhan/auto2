(* Ordering on natural numbers. *)

val TY_NAT_ORDER = "NAT_ORDER"

signature NAT_ORDER =
sig
  val is_order: term -> bool

  datatype order_type =
           LESS | LESS_LMINUS | LESS_LPLUS | LESS_RMINUS | LESS_RPLUS |
           LE | LE_LMINUS | LE_LPLUS | LE_RMINUS | LE_RPLUS
  type order_info
  val order_diffs: order_type -> int -> int
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

  val nat_order_match_side: Proof.context -> term * cterm -> id_inst ->
                            (id_inst * int * thm) list
  val nat_order_match': term -> cterm * cterm -> Proof.context -> id_inst ->
                        (id_inst * (order_type * int * thm)) list
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
fun is_order t =
    let
      val _ = assert (fastype_of t = boolT) "is_order: wrong type"
    in
      case t of Const (@{const_name less}, _) $ _ $ _ => true
              | Const (@{const_name less_eq}, _) $ _ $ _ => true
              | _ => false
    end

datatype order_type =
         LESS_LMINUS | LESS_LPLUS | LESS_RMINUS | LESS_RPLUS | LESS |
         LE_LMINUS | LE_LPLUS | LE_RMINUS | LE_RPLUS | LE

(* The first three values (x, y, n) specify a NAT_ORDER item, and the
   last value provides theorem justifying it. If n >= 0, then the
   theorem is x <= y + n. Otherwise, the theorem is x + (~n) <= y.
 *)
type order_info = cterm * cterm * int * thm

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

(* Decompose a term into A + n or n + A (without matching). *)
fun dest_plus (Const (@{const_name plus}, _) $ A $ B) =
    if is_numc B andalso dest_numc B > 0 then SOME (A, dest_numc B) else NONE
  | dest_plus _ = NONE

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
fun trans_resolve d1 d2 th1 th2 =
    if d1 < 0 andalso d2 < 0 then
      [nat_less_th 0 (~d1), th1, th2] MRS @{thm trans_resolve1}
    else if d1 < 0 andalso d2 >= 0 then
      [nat_less_th d2 (~d1), th1, th2] MRS @{thm trans_resolve2}
    else (* d1 >= 0 andalso d2 < 0 *)
      [nat_less_th d1 (~d2), th2, th1] MRS @{thm trans_resolve2}

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
                  if m + n < 0 then [trans_resolve m n th1 th2]
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

(* Decompose a term into A - n (without matching). *)
fun dest_minus (Const (@{const_name minus}, _) $ A $ B) =
    if is_numc B andalso dest_numc B > 0 then SOME (A, dest_numc B) else NONE
  | dest_minus _ = NONE

(* Add 0 on the left. *)
fun add_0_eq ct = rewr_obj_eq (obj_sym @{thm Nat.plus_nat.add_0}) ct

(* Plus and minus operators. *)
val plus_nat_ct = @{cterm "op +::nat=>nat=>nat"}
val minus_nat_ct = @{cterm "op -::nat=>nat=>nat"}

(* From n, get n = n. *)
fun nat_n_refl n = Thm.reflexive (Thm.cterm_of @{context} (mk_nat n))

(* From a == b, get a + n == b + n. *)
fun plus_n_eq eq n = Util.comb_equiv (plus_nat_ct, [eq, nat_n_refl n])

(* From a == b, get a - n == b - n. *)
fun minus_n_eq eq n = Util.comb_equiv (minus_nat_ct, [eq, nat_n_refl n])

(* Match one side of an inequality on natural numbers. Input pattern
   is pat. Goal is to instantiate schematic variables in pat, so that
   pat is equal to either x + n, n + x (converted to x + n), or x -
   (~n). Returns the tuple ((id', inst'), n, eq_th), where eq_th is
   pat(env) = x + n (or other forms).

   First try to match pat with x + n or n + x, and then with other
   forms.
 *)
fun nat_order_match_side ctxt (pat, cx) (id, inst) =
    (* Match pat with x + n. *)
    if is_some (dest_plus pat) then
      let
        val (p, n) = the (dest_plus pat)
        val insts = Matcher.rewrite_match ctxt (p, cx) (id, inst)
        fun process_inst ((id', inst'), eq_th) =
            (* eq_th: p(env) = x, return p(env) + n = x + n. *)
            ((id', inst'), n, plus_n_eq eq_th n)
      in
        map process_inst insts
      end
    else
      let
        (* Match pat with n (where input is x = 0). *)
        val numc_insts =
            if Util.has_vars pat orelse not (cx aconvc cnat0) then [] else
            let
              val cpat = Thm.cterm_of ctxt pat
              val insts = Matcher.rewrite_match
                              ctxt (@{term_pat "?NUMC::nat"}, cpat) (id, fo_init)
              fun process_inst ((id', inst'), eq_th) =
                  let
                    (* eq_th: n = pat, return pat = 0 or pat = n + 0. *)
                    val n = lookup_numc0 inst'
                    val th' = if n = 0 then meta_sym eq_th
                              else apply_to_rhs add_0_eq (meta_sym eq_th)
                  in
                    ((id', inst), n, th')
                  end
            in
              map process_inst insts
            end

        (* Match pat with x - n. *)
        val minus_insts =
            if is_none (dest_minus pat) then [] else
            let
              val (p, n) = the (dest_minus pat)
              val insts = Matcher.rewrite_match ctxt (p, cx) (id, inst)
              fun process_inst ((id', inst'), eq_th) =
                  (* eq_th: p(env) = x, return p(env) - n = x - n. *)
                  ((id', inst'), ~n, minus_n_eq eq_th n)
            in
              map process_inst insts
            end

        (* Match pat with x (x = 0 case already covered. *)
        val self_insts =
            if cx aconvc cnat0 then [] else
            let
              val insts = Matcher.rewrite_match ctxt (pat, cx) (id, inst)
              fun process_inst ((id', inst'), eq_th) =
                  (* eq_th: p(env) = x, return the same. *)
                  ((id', inst'), 0, eq_th)
            in
              map process_inst insts
            end
      in
        numc_insts @ minus_insts @ self_insts
      end

(* Match the two sides of pat against x and y, respectively. Here pat
   is a boolean inequality. Returns ((id', inst'), (order_type, n,
   eq_th)), where eq_th is the equality between pat(env) and x (+/-) n
   (</<=) y or x (</<=) y (+/-) n.
 *)
fun nat_order_match' pat (cx, cy) ctxt (id, inst) =
    let
      (* Classify pat into A < B or A <= B. *)
      val (f, (patA, patB)) = Util.dest_binop pat
      val is_strict =
          case f of
              Const (@{const_name less}, _) => true
            | Const (@{const_name less_eq}, _) => false
            | _ => raise Fail "match_order: input should be inequality."

      (* Given nA and nB (the value of n on the two sides), return
         order_type. Assume at least one of nA and nB is zero.
       *)
      fun order_info (nA, nB) =
          if nB = 0 then
            if nA = 0 then if is_strict then LESS else LE
            else if nA > 0 then if is_strict then LESS_LPLUS else LE_LPLUS
            else (* nA < 0 *) if is_strict then LESS_LMINUS else LE_LMINUS
          else  (* nA = 0 *)
            if nB > 0 then if is_strict then LESS_RPLUS else LE_RPLUS
            else (* nB < 0 *) if is_strict then LESS_RMINUS else LE_RMINUS

      (* Match A and B in sequence. *)
      val insts_A = nat_order_match_side ctxt (patA, cx) (id, inst)
      fun process_inst_A ((id', inst'), nA, eqA) =
          let
            val insts_B = nat_order_match_side ctxt (patB, cy) (id', inst')
            fun process_inst_B ((id'', inst''), nB, eqB) =
                if nA <> 0 andalso nB <> 0 then [] else
                let
                  (* n is the Abs of either nA or nB. *)
                  val n = if nA = 0 then Int.abs nB else Int.abs nA
                  val cf = f |> Util.subst_term_norm inst'' |> Thm.cterm_of ctxt
                  val eq_th = Util.comb_equiv (cf, [eqA, eqB])
                  val order_ty = order_info (nA, nB)
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

(* Main matching function: pat is a pattern of form either A (</<=) B
   or ~ A (</<=) B, where A and B can possibly contain schematic
   variables. Try to use theorem contained in item to justify an
   instantiated version of pat.
 *)
fun nat_order_match pat item ctxt (id, inst) =
    if not (is_order_pat ctxt pat) then [] else
    let
      (* is_neg records whether pat is originally a negation. *)
      val is_neg = is_neg pat

      (* Obtain the two sides (x, y) of the inequality contained in
         item. Then (y, x) will be matched with two sides of ~pat.
       *)
      val (x, y, diff1, th1) = get_nat_order_info item

      (* Obtain ~pat in non-negated form. *)
      val neg_t = get_neg pat |> Thm.cterm_of ctxt |> neg_ineq_cv |> Util.rhs_of
      val neg_tp = mk_Trueprop neg_t
      val negt_th = neg_tp |> Thm.cterm_of ctxt |> Thm.trivial

      (* Match ~pat against inequality with (y, x) on the two
         sides. If diff1 + diff2 < 0, obtain a contradiction from th1
         and the normalized version of negt_th (~pat).
       *)
      val insts = nat_order_match' neg_t (y, x) ctxt (id, inst)
      fun process_inst ((id', inst'), (order_ty, diff2, eq_th)) =
          if diff1 + diff2 >= 0 then [] else
          let
            (* Instantiate ~pat with inst' *)
            val negt_th' = negt_th |> Util.subst_thm ctxt inst'
                                   |> Util.send_first_to_hyps

            (* th2 is the normal form of negt_th', after rewriting to
               become an inequality in y and x.
             *)
            val th2 = (Thm.equal_elim (make_trueprop_eq eq_th) negt_th')
                          |> to_normal_th order_ty

            (* Attempt to obtain a contradiction from item1 and th2. *)
            val contra_th = trans_resolve diff1 diff2 th1 th2
            val neg_tp' = Util.subst_term_norm inst' neg_tp
            val pat_th =
                contra_th |> Thm.implies_intr (Thm.cterm_of ctxt neg_tp')
                          |> apply_to_thm UtilLogic.rewrite_from_contra_form
                          |> (if is_neg then I else apply_to_thm' neg_ineq_cv)
          in
            [((id', inst'), pat_th)]
          end
    in
      maps process_inst insts
    end

fun nat_order_pre_match pat _ ctxt = is_order_pat ctxt pat

(* Prop-matching with a NAT_ORDER item. *)
val nat_order_matcher =
    {pre_match = nat_order_pre_match, match = nat_order_match}

(* Use x < y to match x <= y. *)
val nat_order_noteq_matcher =
    let
      fun get_insts pat item ctxt (id, inst) =
          let
            val (A, B) = pat |> dest_not |> dest_eq
            val (cx, cy, n, _) = get_nat_order_info item
          in
            if n >= 0 then ([], [])
            else (Matcher.rewrite_match_list
                      ctxt [(false, (A, cx)), (false, (B, cy))] (id, inst),
                  Matcher.rewrite_match_list
                      ctxt [(false, (B, cx)), (false, (A, cy))] (id, inst))
          end
          handle Fail "dest_not" => ([], [])
               | Fail "dest_eq" => ([], [])

      fun pre_match pat item ctxt =
          let
            val (A, B) = pat |> dest_not |> dest_eq
            val (cx, cy, n, _) = get_nat_order_info item
          in
            n < 0 andalso ((Matcher.pre_match ctxt (A, cx) andalso
                            Matcher.pre_match ctxt (B, cy)) orelse
                           (Matcher.pre_match ctxt (A, cy) andalso
                            Matcher.pre_match ctxt (A, cx)))
          end
          handle Fail "dest_not" => false
               | Fail "dest_eq" => false

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

(* Using term x to justify propositions of the form x <= x + n, where
   n >= 0. This follows the same general outline as nat_order_match.
 *)
fun nat_order_single_match pat _ ctxt (id, inst) =
    if not (is_order_pat ctxt pat) orelse
       Util.has_vars pat then [] else
    let
      val is_neg = is_neg pat
      val neg_ct = get_neg pat |> Thm.cterm_of ctxt |> neg_ineq_cv |> Thm.rhs_of
      val neg_t = Thm.term_of neg_ct
      val neg_tp = neg_t |> mk_Trueprop
      val negt_th = neg_tp |> Thm.cterm_of ctxt |> Thm.trivial
      val (cA, cB) = Util.dest_binop_cargs neg_ct
      val (f, (A, B)) = Util.dest_binop neg_t

      fun contra_to_pat_th assum contra_th =
          contra_th |> Thm.implies_intr (Thm.cterm_of ctxt assum)
                    |> apply_to_thm UtilLogic.rewrite_from_contra_form
                    |> (if is_neg then I else apply_to_thm' neg_ineq_cv)

      val insts_A = nat_order_match' neg_t (cA, cA) ctxt (id, inst)
      val insts_B = nat_order_match' neg_t (cB, cB) ctxt (id, inst)

      fun process_inst ((id', inst'), (order_ty, diff, eq_th)) =
          if diff >= 0 then [] else
          let
            val neg_tp' = Util.subst_term_norm inst' neg_tp
            val negt_th' = negt_th |> Util.subst_thm ctxt inst'
                                   |> Util.send_first_to_hyps
            val th2 = (Thm.equal_elim (make_trueprop_eq eq_th) negt_th')
                          |> to_normal_th order_ty
            val contra_th =
                [nat_less_th 0 (~diff), th2] MRS @{thm single_resolve}
          in
            [((id', inst'), contra_to_pat_th neg_tp' contra_th)]
          end

      val const_ineqs =
          if not (is_numc A andalso is_numc B) then [] else
          let
            val (nA, nB) = (dest_numc A, dest_numc B)
            val negt_th' = negt_th |> Util.subst_thm ctxt inst
                                   |> Util.send_first_to_hyps
            val contra_ths =
                case f of
                    Const (@{const_name less}, _) =>
                    if nA >= nB then [contra_by_arith ctxt [negt_th']] else []
                  | Const (@{const_name less_eq}, _) =>
                    if nA > nB then [contra_by_arith ctxt [negt_th']] else []
                  | _ => []
          in
            map (fn contra_th =>
                    ((id, inst), contra_to_pat_th neg_tp contra_th)) contra_ths
          end
    in
      (maps process_inst (insts_A @ insts_B) @ const_ineqs)
          |> Util.max_partial (fn ((i,_),_) => fn ((j,_),_) =>
                               BoxID.is_eq_ancestor ctxt i j)
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
       shadow_nat_order, shadow_nat_order_single])

end

end

val _ = Theory.setup (Nat_Order.add_nat_order_proofsteps)
