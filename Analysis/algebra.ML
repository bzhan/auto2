(* Algebraic manipulations. *)

signature ALGEBRA =
sig
  val TY_POLY: string
  val dest_poly_tname: term list -> term * term list
  val output_poly_fn: item_output
  val poly_typed_matcher: item_matcher
  val get_poly_raw_item: thm -> raw_item
  val get_poly_update: box_id * thm -> raw_update list
  val expand_polys: proofstep list

  val nonzero_poly_update: box_id * thm -> raw_update list
  val ineq_poly_gen: proofstep
  val clear_denom_poly: proofstep
  val less_poly_gen: proofstep
  val le_poly_gen: proofstep
  val add_algebra_proofsteps: theory -> theory
end;

structure Algebra : ALGEBRA =
struct

val TY_POLY = "POLY"

(* An item of type POLY has form P x, where x is in the form of a
   polynomial. The tname of the item consists of the tuple (P x,
   subs), where subs is the list of terms that appear in x. The prop
   of the item is P x. Deconstruct into (P x, [subs])
 *)
fun dest_poly_tname tname =
    (hd tname, tl tname)

(* Output function for item type POLY. *)
fun output_poly_fn ctxt (_, th) =
    "POLY " ^ (th |> Thm.prop_of |> pretty_term ctxt |> str)

(* Apply on argument of POLY item. *)
val apply_to_arg = apply_to_thm' o Conv.arg_conv

(* Pattern is of the form (pat_p, pat_subs). Each element of pat_subs
   is matched against distinct element of subs. After replacement of
   subs by corresponding pat_subs(inst), pat should match P x exactly.
 *)
val poly_typed_matcher =
    let
      fun pre_match pat {tname, ...} tbl =
          let
            val (pat_p, pat_subs) = dest_poly_tname (HOLogic.strip_tuple pat)
            val (cpx, csubs) = dest_poly_tname tname
            fun pre_match_sub s =
                exists (fn ct => Matcher.pre_match_head tbl (s, ct)) csubs
          in
            Matcher.pre_match_head tbl (pat_p, cpx) andalso
            forall pre_match_sub pat_subs
          end

      (* Return value is (inst, P x'), where P x' is obtained from P x
         by replacing the matched subterms with vars(inst).
       *)
      fun match pat {tname, prop, ...} (tbl as {ctxt, ...}) (id, inst) =
          let
            val (pat_p, pat_subs) = dest_poly_tname (HOLogic.strip_tuple pat)
            val (_, csubs) = dest_poly_tname tname

            (* Process each result of matching pat_subs as a subset of
               subs. Each th in the returned value is in the form
               pat_subs_i(inst) == subs_j.
             *)
            fun process_inst ((id', inst'), ths) =
                let
                  val cvs =
                      map (rewr_obj_eq_top ctxt o to_obj_eq o meta_sym) ths
                  val prop' = apply_to_arg (Conv.every_conv cvs) prop
                  val thy = Proof_Context.theory_of ctxt
                  val inst'' = Pattern.first_order_match
                                   thy (pat_p, prop_of' prop') inst'
                in
                  [((id', inst''), prop')]
                end
                handle Pattern.MATCH => []
          in
            maps process_inst
                 (Matcher.rewrite_match_subset tbl (pat_subs, csubs) (id, inst))
          end
    in
      {pre_match = pre_match, match = match}
    end

(* Produce POLY item from the given proposition. Assume the argument
   is normalized.
 *)
fun get_poly_raw_item th =
    let
      val arg = th |> prop_of' |> dest_arg
      val ts = Ring_Arith.polynomial_terms arg
    in
      Fact (TY_POLY, prop_of' th :: ts, th)
    end

(* Normalize the argument, then get update with POLY item. *)
fun get_poly_update (id, th) =
    let
      val th' = th |> apply_to_arg Ring_Arith.norm_full
    in
      [AddItems {id = id, sc = NONE, raw_items = [get_poly_raw_item th']}]
    end

fun expand_poly_gen (nm, pat) =
    let
      val pat_lhs = dest_eq pat |> fst
      val pat_A = HOLogic.mk_tuple [@{term_pat "?P::bool"}, pat_lhs]
      fun prfstep_fn ((id, _), ths) _ {ctxt, ...} =
          let
            (* Here th is P x where x contains A, and eq_th is A = A'. *)
            val (th, eq_th) = the_pair ths
            val (lhs, rhs) = dest_eq (prop_of' eq_th)
          in
            if is_subterm lhs rhs then []
            else get_poly_update (
                id, apply_to_arg (rewr_obj_eq_top ctxt eq_th) th)
          end
    in
      prfstep_custom nm [WithItem (TY_POLY, pat_A), WithFact pat]
                     PRIORITY_ADD prfstep_fn
    end

val expand_polys =
    map expand_poly_gen [
      ("expand_poly_plus", @{term_pat "(?A::?'a::comm_ring) = ?B + ?C"}),
      ("expand_poly_times", @{term_pat "(?A::?'a::comm_ring) = ?B * ?C"}),
      ("expand_poly_divide", @{term_pat "(?A::?'a::field) = ?B / ?C"}),
      ("expand_poly_minus", @{term_pat "(?A::?'a::field) = ?B - ?C"}),
      ("expand_poly_uminus", @{term_pat "(?A::?'a::field) = -?B"}),
      ("expand_poly_num", @{term_pat "(?A::?'a::comm_ring) = ?NUMC"})
    ]

val expand_poly_merge =
    let
      val nm = "expand_poly_merge"
      val pat_A = @{term_pat "?A::?'a::comm_ring"}
      val pat = HOLogic.mk_tuple [@{term_pat "?P::bool"}, pat_A, pat_A]
      fun prfstep_fn ((id, _), ths) _ _ =
          get_poly_update (id, the_single ths)
    in
      prfstep_custom nm [WithItem (TY_POLY, pat)] PRIORITY_ADD
                     prfstep_fn
    end

(* Given theorem is of the form nonzero x. First normalize the
   argument, then check whether it is zero.
 *)
fun nonzero_poly_update (id, th) =
    let
      val th' = th |> apply_to_arg Ring_Arith.norm_full
      val arg = th' |> prop_of' |> dest_arg
    in
      if is_numc arg then
        if dest_numc_rat arg = rat_zero then
          [Update.thm_update (id, th' RS @{thm nonzero_resolve})]
        else []
      else
        [AddItems {id = id, sc = NONE, raw_items = [get_poly_raw_item th']}]
    end

val ineq_poly_gen =
    prfstep_custom
        "ineq_poly_gen"
        [WithGoal @{term_pat "(?A::?'a::comm_ring) = ?B"},
         Filter (order_filter "A" "B")]
        PRIORITY_ADD
        (fn ((id, _), ths) => fn _ => fn _ =>
            nonzero_poly_update (id, ths MRS @{thm ineq_to_nonzero}))

val clear_denom_poly =
    prfstep_custom
        "clear_denom_poly"
        [WithItem (
            TY_POLY,
            @{term_pat "(nonzero ?X, inverse (?A::?'a::linordered_field))"}),
         WithFact @{term_pat "(?A::?'a::linordered_field) > 0"}]
        PRIORITY_ADD
        (fn ((id, _), ths) => fn _ => fn _ =>
            let
              val (th, gt0_th) = the_pair ths
              val neq0_th = gt0_th RS @{thm dual_order.strict_implies_not_eq}
              val cv = Ring_Arith.cancel_inverse_polynomial neq0_th
              val th' = ([neq0_th, th] MRS @{thm nonzero_multiple})
                            |> apply_to_arg cv
            in
              nonzero_poly_update (id, th')
            end)

val ineq_poly_numc =
    prfstep_custom
        "ineq_poly_numc"
        [WithItem (TY_POLY, @{term_pat "nonzero ?X"})]
        PRIORITY_SHADOW
        (fn ((id, _), ths) => fn items => fn _ =>
            let
              val th = the_single ths
              val arg = th |> prop_of' |> dest_arg
            in
              if is_numc arg then
                if dest_numc_rat arg = rat_zero then
                  [Update.thm_update (id, th RS @{thm nonzero_resolve})]
                else [ShadowItem {id = id, item = the_single items}]
              else []
            end)

val less_poly_gen =
    prfstep_custom
        "less_poly_gen"
        [WithFact @{term_pat "(?A::?'a::linordered_idom) < ?B"}]
        PRIORITY_ADD
        (fn ((id, _), ths) => fn _ => fn _ =>
            let
              val th =
                  (the_single ths)
                      |> apply_to_thm' (rewr_obj_eq @{thm less_to_is_positive})
            in
              get_poly_update (id, th)
            end)

val le_poly_gen =
    prfstep_custom
        "le_poly_gen"
        [WithFact @{term_pat "(?A::?'a::linordered_idom) <= ?B"}]
        PRIORITY_ADD
        (fn ((id, _), ths) => fn _ => fn _ =>
            let
              val th =
                  (the_single ths)
                      |> apply_to_thm' (rewr_obj_eq @{thm le_to_is_nonneg})
            in
              get_poly_update (id, th)
            end)

val less_poly_reduce =
    prfstep_custom
        "less_poly_reduce"
        [WithItem (TY_POLY, @{term_pat "is_positive ?X"})]
        PRIORITY_ADD
        (fn ((id, _), ths) => fn _ => fn _ =>
            let
              val cv = Conv.every_conv [
                    Conv.arg_conv Ring_Arith.split_polynomial_by_sign,
                    rewr_obj_eq (obj_sym @{thm less_to_is_positive})]
            in
              [Update.thm_update (id, ths |> the_single |> apply_to_thm' cv)]
            end)

val le_poly_reduce =
    prfstep_custom
        "le_poly_reduce"
        [WithItem (TY_POLY, @{term_pat "is_non_negative ?X"})]
        PRIORITY_ADD
        (fn ((id, _), ths) => fn _ => fn _ =>
            let
              val cv = Conv.every_conv [
                    Conv.arg_conv Ring_Arith.split_polynomial_by_sign,
                    rewr_obj_eq (obj_sym @{thm le_to_is_nonneg})]
            in
              [Update.thm_update (id, ths |> the_single |> apply_to_thm' cv)]
            end)

val add_algebra_proofsteps =
    fold ItemIO.add_item_type [
      (TY_POLY, SOME (fn t => t |> dest_poly_tname |> snd), SOME output_poly_fn)

    ] #> fold ItemIO.add_typed_matcher [
      (TY_POLY, poly_typed_matcher)

    ] #> fold add_prfstep [
      expand_poly_merge,
      ineq_poly_gen, clear_denom_poly, ineq_poly_numc,
      less_poly_gen, le_poly_gen, less_poly_reduce, le_poly_reduce

    ] #> fold add_prfstep expand_polys

end  (* structure Algebra. *)

val _ = Theory.setup Algebra.add_algebra_proofsteps
