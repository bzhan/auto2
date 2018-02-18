(* Setup for FOL *)

structure UtilBase : UTIL_BASE =
struct

(* Types *)

val boolT = @{typ "o"}
val setT = @{typ "i"}
val mk_setT = K setT

(* Equality *)

fun dest_eq t =
    case t of
        Const (@{const_name IFOL.eq}, _) $ lhs $ rhs => (lhs, rhs)
      | Const (@{const_name IFOL.iff}, _) $ lhs $ rhs => (lhs, rhs)
      | _ => raise Fail "dest_eq"

fun cdest_eq ct =
    case Thm.term_of ct of
        Const (@{const_name IFOL.eq}, _) $ _ $ _ => (Thm.dest_arg1 ct, Thm.dest_arg ct)
      | Const (@{const_name IFOL.iff}, _) $ _ $ _ => (Thm.dest_arg1 ct, Thm.dest_arg ct)
      | _ => raise Fail "dest_eq"

fun mk_eq (t, u) =
    let
      val T = fastype_of t
    in
      Const (@{const_name IFOL.eq}, T --> T --> boolT) $ t $ u
    end

fun is_eq_term t =
    let
      val _ = assert (fastype_of t = boolT) "is_eq_term: wrong type"
    in
      case t of Const (@{const_name IFOL.eq}, _) $ _ $ _ => true
              | Const (@{const_name IFOL.iff}, _) $ _ $ _ => true
              | _ => false
    end

val bTrue = @{term True}
val bFalse = @{term False}
val Trueprop_name = @{const_name IFOL.Trueprop}
val Not_name = @{const_name IFOL.Not}
val Conj_name = @{const_name IFOL.conj}
val Disj_name = @{const_name IFOL.disj}
val Imp_name = @{const_name IFOL.imp}
val All_name = @{const_name IFOL.All}
val Ex_name = @{const_name IFOL.Ex}

(* If expressions are treated differently. In a term "if a then b else
   c", only terms in "a" are considered in the proof state.
 *)
fun is_if t =
    case t of
        Const ("Set.If", _) $ _ $ _ $ _ => true
      | Const ("Set.Ifb", _) $ _ $ _ $ _ => true
      | _ => false

val cTrueprop = @{cterm Trueprop}
val cNot = @{cterm Not}
val cConj = @{cterm conj}
val cDisj = @{cterm disj}

(* Theorems for equality *)
val to_meta_eq_cv =
    (Conv.rewr_conv @{thm to_meta_eq})
        else_conv (Conv.rewr_conv @{thm to_meta_eq_iff})

val to_obj_eq_cv =
    (Conv.rewr_conv @{thm atomize_eq})
        else_conv (Conv.rewr_conv @{thm atomize_iff})

val to_obj_eq_iff =
    apply_to_thm (Util.concl_conv (Conv.rewr_conv @{thm atomize_iff}))

val obj_sym_cv =
    (Conv.rewr_conv @{thm obj_sym})
        else_conv (Conv.rewr_conv @{thm obj_sym_iff})

(* Theorems *)
val true_th = @{thm TrueI}
val nn_create_th = @{thm nn_create}
val nn_cancel_th = @{thm FOL.cla_simps(12)}
val to_contra_form_th = @{thm to_contra_form}
val to_contra_form_th' = @{thm to_contra_form'}
val atomize_imp_th = @{thm atomize_imp}
val atomize_all_th = @{thm atomize_all}
val conjunct1_th = @{thm conjunct1}
val conjunct2_th = @{thm conjunct2}
val conjI_th = @{thm conjI}
val or_intro1_th = @{thm or_intro1}
val or_intro2_th = @{thm or_intro2}
val iffD1_th = @{thm iffD1}
val iffD2_th = @{thm iffD2}
val inv_back_th = @{thm inv_backward}
val sym_th = @{thm sym}
val exE_th' = @{thm exE'}
val eq_True_th = @{thm eq_True}
val eq_True_inv_th = @{thm eq_True_inv}
val disj_True1_th = @{thm disj_True1}
val disj_True2_th = @{thm disj_True2}
val ex_vardef_th = @{thm ex_vardef}
val imp_conv_disj_th = @{thm imp_conv_disj}
val de_Morgan_conj_th = @{thm de_Morgan_conj}
val de_Morgan_disj_th = @{thm de_Morgan_disj}
val not_ex_th = @{thm not_ex}
val not_all_th = @{thm not_all}
val not_imp_th = @{thm not_imp}
val or_cancel1_th = @{thm or_cancel1}
val or_cancel2_th = @{thm or_cancel2}
val swap_all_disj_th = @{thm swap_all_disj}
val swap_ex_conj_th = @{thm swap_ex_conj}
val all_trivial_th = @{thm all_trivial}
val case_split_th = @{thm case_split}

val atomize_conjL_th = @{thm FOL_Base.atomize_conjL}
val backward_conv_th = @{thm backward_conv}
val backward1_conv_th = @{thm backward1_conv}
val backward2_conv_th = @{thm backward2_conv}
val resolve_conv_th = @{thm resolve_conv}
val contra_triv_th = @{thm contra_triv}

val conj_assoc_th = @{thm conj_assoc}
val conj_commute_th = @{thm conj_commute}
val disj_assoc_th = @{thm disj_assoc}
val disj_commute_th = @{thm disj_commute}

val Mem_name = "FOL_Base.mem"
val Ball_name = "FOL_Base.Ball"
val Bex_name = "FOL_Base.Bex"
val Bex_def_th = @{thm Bex_def'}
val Ball_def_th = @{thm Ball_def'}

end  (* structure UtilBase *)

structure Basic_UtilBase: BASIC_UTIL_BASE = UtilBase
open Basic_UtilBase
