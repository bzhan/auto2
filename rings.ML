(* Algebraic manipulation for rings. *)

signature RING_ARITH =
sig
  val distrib_raw_conv: conv
  val shift_mult_minus: conv
  val distrib_conv: theory -> conv
  val add_ring_proofsteps: theory -> theory
end;

structure Ring_Arith : RING_ARITH =
struct

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

(* Convert -a * -b to a * b, and -a * b and a * -b to -(a * b). *)
fun shift_mult_minus ct =
    (Conv.try_conv o Conv.first_conv)
        (map rewr_obj_eq [@{thm minus_mult_minus}, @{thm mult_minus_left},
                          @{thm mult_minus_right}]) ct

(* Apply distributive rule on a single product term. *)
fun distrib_conv thy ct =
    let
      val T = fastype_of (Thm.term_of ct)
      val plus_ac = Nat_Arith.plus_ac_on_typ thy T
      val times_ac = Nat_Arith.times_ac_on_typ thy T
      val eq1 = ((ACUtil.ac_subterms_conv
                      times_ac (Matcher.normalize_minus_assoc_l plus_ac))
                     then_conv distrib_raw_conv) ct
    in
      if Thm.is_reflexive eq1 then eq1
      else let
        val ct' = Thm.rhs_of eq1
        val cv_minus_terms = ACUtil.ac_subterms_conv plus_ac shift_mult_minus
        val cv_unit = ACUtil.ac_subterms_conv_trav_uinv
                          plus_ac (ACUtil.normalize_unit times_ac)
        val eq2 = ((ACUtil.normalize_assoc_l plus_ac)
                       then_conv cv_minus_terms
                       then_conv cv_unit) ct'
      in
        Thm.transitive eq1 eq2
      end
    end

val add_ring_proofsteps =
    fold add_prfstep_pre_conv [
      ("ring_distrib",
       [WithTerm @{term_pat "(?A::(?'a::semiring)) * (?B + ?C)"}],
       (distrib_conv o Proof_Context.theory_of)),

      ("ring_distrib2",
       [WithTerm @{term_pat "(?A::(?'a::ring)) * (?B - ?C)"}],
       (distrib_conv o Proof_Context.theory_of))
    ]

end  (* structure Ring_Arith. *)

val _ = Theory.setup Ring_Arith.add_ring_proofsteps
