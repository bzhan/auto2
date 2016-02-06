(* Algebraic manipulation for rings. *)

signature RING_ARITH =
sig
  val plus_info: ac_info
  val times_info: ac_info
  val distrib_raw_conv: conv
  val shift_mult_minus: conv
  val distrib_conv: theory -> conv
  val distrib_terms_conv: theory -> conv
  val add_ring_proofsteps: theory -> theory
end;

structure Ring_Arith : RING_ARITH =
struct

val plus_info = the (ACUtil.lookup_ac_data @{theory} @{const_name plus})
val times_info = the (ACUtil.lookup_ac_data @{theory} @{const_name times})

fun is_plus t =
    case t of
        Const (@{const_name plus}, _) $ _ $ _ => true
      | _ => false

(* Expand using distributive rule. May produce extraeous parentheses. *)
fun distrib_raw_conv ct =
    case Thm.term_of ct of
        Const (@{const_name times}, _) $ A $ B =>
        if is_plus A then
          ((rewr_obj_eq @{thm ring_distribs(2)})
               then_conv (Conv.binop_conv distrib_raw_conv)) ct
        else if is_plus B then
          ((rewr_obj_eq @{thm ring_distribs(1)})
               then_conv (Conv.binop_conv distrib_raw_conv)) ct
        else
          Conv.all_conv ct
      | _ => Conv.all_conv ct

fun shift_mult_minus ct =
    (Conv.try_conv o Conv.first_conv)
        (map rewr_obj_eq [@{thm minus_mult_minus}, @{thm mult_minus_left},
                          @{thm mult_minus_right}]) ct

(* Apply distributive rule on a single product term. *)
fun distrib_conv thy ct =
    let
      val eq1 = distrib_raw_conv ct
    in
      if Thm.is_reflexive eq1 then eq1
      else let
        val ct' = Thm.rhs_of eq1
        val ac_info = the (ACUtil.get_head_ac_info thy (Thm.term_of ct'))
        val cv_minus_terms = ACUtil.ac_subterms_conv ac_info shift_mult_minus
        val eq2 = (ACUtil.normalize_assoc ac_info then_conv cv_minus_terms) ct'
      in
        Thm.transitive eq1 eq2
      end
    end

(* Apply distributive rule on each term. *)
fun distrib_terms_conv thy ct =
    if not (is_plus (Thm.term_of ct)) then Conv.no_conv ct
    else let
      val ac_info = the (ACUtil.get_head_ac_info thy (Thm.term_of ct))
    in
      ((ACUtil.ac_subterms_conv_trav_uinv ac_info (distrib_conv thy))
           then_conv (ACUtil.normalize_minus ac_info)
           then_conv (ACUtil.normalize_assoc ac_info)) ct
    end

val add_ring_proofsteps =
    fold add_prfstep_pre_conv [
      ("ring_distrib",
       [WithTerm @{term_pat "(?A::(?'a::semiring)) * (?B + ?C)"},
        Filter (canonical_split_filter @{const_name plus} "B" "C")],
       (distrib_conv o Proof_Context.theory_of)),

      ("ring_distrib_terms1",
       [WithTerm @{term_pat "(?A::(?'a::semiring)) + ?B * (?C + ?D)"},
        Filter (canonical_split_filter @{const_name plus} "C" "D")],
       (distrib_terms_conv o Proof_Context.theory_of)),

      ("ring_distrib_terms2",
       [WithTerm @{term_pat "(?A::(?'a::ring)) + -(?B * (?C + ?D))"},
        Filter (canonical_split_filter @{const_name plus} "C" "D")],
       (distrib_terms_conv o Proof_Context.theory_of))
    ]

end  (* structure Ring_Arith. *)

val _ = Theory.setup Ring_Arith.add_ring_proofsteps
