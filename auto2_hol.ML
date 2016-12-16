(* Setup for HOL *)

structure Base : UTIL_BASE =
struct

(* Types *)

val boolT = @{typ bool}
val mk_setT = HOLogic.mk_setT

(* Equality *)

fun dest_eq t =
    case t of
        Const ("HOL.eq", _) $ lhs $ rhs => (lhs, rhs)
      | _ => raise AUTO2T ("dest_eq", [t])

fun mk_eq (t, u) =
    let
      val T = fastype_of t
    in
      Const ("HOL.eq", T --> T --> boolT) $ t $ u
    end

fun is_eq_term t =
    let
      val _ = assert (fastype_of t = boolT) "is_eq_term: wrong type"
    in
      case t of Const ("HOL.eq", _) $ _ $ _ => true
              | _ => false
    end

(* Terms *)

val bTrue = @{term True}
val bFalse = @{term False}
val Trueprop_name = "HOL.Trueprop"
val Not_name = "HOL.Not"
val Conj_name = "HOL.conj"
val Disj_name = "HOL.disj"
val Imp_name = "HOL.implies"
val All_name = "HOL.All"
val Ex_name = "HOL.Ex"

(* Test if a term represents a numerical constant. In addition to use
   dest_number from HOLogic, test for inverse, uminus, of_rat, etc.
 *)
fun is_numc t =
    case t of
        Const (@{const_name inverse}, _) $ t' => is_numc t'
      | Const (@{const_name uminus}, _) $ t' => is_numc t'
      | Const (@{const_name of_rat}, _) $ r => is_numc r
      | Const (@{const_name Fract}, _) $ n $ d => is_numc n andalso is_numc d
      | _ => let val _ = HOLogic.dest_number t in true end
             handle TERM ("dest_number", _) => false

(* If expressions are treated differently. In a term "if a then b else
   c", only terms in "a" are considered in the proof state.
 *)
fun is_if t =
    case t of
        Const (@{const_name If}, _) $ _ $ _ $ _ => true
      | _ => false

val cTrueprop = cert @{context} HOLogic.Trueprop
val cNot = cert @{context} HOLogic.Not
val cConj = cert @{context} HOLogic.conj
val cDisj = cert @{context} HOLogic.disj

(* Theorems for equality *)
val to_meta_eq = apply_to_thm (concl_conv (Conv.rewr_conv @{thm to_meta_eq}))
val to_obj_eq = apply_to_thm (concl_conv (Conv.rewr_conv @{thm atomize_eq}))
val obj_sym = apply_to_thm (concl_conv (Conv.rewr_conv @{thm obj_sym}))

(* Theorems *)
val true_th = @{thm TrueI}
val nn_cancel_th = @{thm HOL.nnf_simps(6)}
val to_contra_form_th = @{thm to_contra_form}
val to_contra_form_th' = @{thm to_contra_form'}
val atomize_imp_th = @{thm atomize_imp}
val atomize_all_th = @{thm atomize_all}
val conjunct1_th = @{thm conjunct1}
val conjunct2_th = @{thm conjunct2}
val or_intro1_th = @{thm or_intro1}
val or_intro2_th = @{thm or_intro2}
val iffD1_th = @{thm iffD1}
val iffD2_th = @{thm iffD2}
val sym_th = @{thm sym}
val exE_th' = @{thm exE'}
val eq_True_th = @{thm HOL.eq_True}
val eq_False_th = @{thm HOL.eq_False}
val eq_False_th' = @{thm eq_False'}
val disj_True1_th = @{thm disj_True1}
val disj_True2_th = @{thm disj_True2}
val use_vardef_th = @{thm HOL.simp_thms(41)}
val imp_conv_disj_th = @{thm imp_conv_disj}
val de_Morgan_conj_th = @{thm de_Morgan_conj}
val de_Morgan_disj_th = @{thm de_Morgan_disj}
val not_ex_th = @{thm HOL.not_ex}
val not_all_th = @{thm HOL.not_all}
val not_conjI1_th = @{thm not_conjI1}
val not_conjI2_th = @{thm not_conjI2}
val not_imp_th = @{thm HOL.not_imp}

val swap_prems_eq_th = @{thm swap_prems_eq}
val atomize_conjL_th = @{thm atomize_conjL}
val atomize_conjL2_th = @{thm atomize_conjL2}
val backward_conv_th = @{thm backward_conv}
val backward1_conv_th = @{thm backward1_conv}
val backward2_conv_th = @{thm backward2_conv}
val resolve_conv_th = @{thm resolve_conv}
val contra_triv_th = @{thm contra_triv}

val conj_assoc_th = @{thm conj_assoc}
val conj_commute_th = @{thm conj_commute}
val conj_unitL_th = @{thm HOL.simp_thms(22)}
val disj_assoc_th = @{thm disj_assoc}
val disj_commute_th = @{thm disj_commute}
val disj_unitL_th = @{thm HOL.simp_thms(32)}

val Mem_name = "Set.member"
val mk_mem = HOLogic.mk_mem
val Ball_name = "Set.Ball"
val Bex_name = "Set.Bex"
val Bex_def_th = @{thm Bex_def'}
val Ball_def_th = @{thm Ball_def'}
val swap_ex_conj_th = @{thm swap_ex_conj}
val swap_all_implies_th = @{thm swap_all_implies}

end  (* structure UtilBase_HOL *)

structure UtilLogic = UtilLogic(Base)
structure ACUtil = ACUtil(Base)
structure Subterms = Subterms(Base)
structure Property_Data = Property_Data(Base)
structure RewriteTable = RewriteTable(Base)
structure Matcher = Matcher(Base)
structure BoxItem = BoxItem(Base)
structure ItemIO_Data = ItemIO_Data(Base)
structure Update = Update(Base)
structure Box = Box(Base)
structure Status = Status(Base)
structure Normalizer = Normalizer(Base)
structure ProofStep = ProofStep(Base)
structure ProofStep_Data = ProofStep_Data(Base)
structure Script = Script(Base)
structure Scores = Scores(Base)
structure ProofStatus = ProofStatus(Base)
structure Auto2 = Auto2(Base)
structure Induct_ProofSteps = Induct_ProofSteps(Base)
structure AC_ProofSteps = AC_ProofSteps(Base)
structure Logic_ProofSteps = Logic_ProofSteps(Base)
open Base
open UtilLogic
open Property_Data
open Normalizer
open ProofStep
open ProofStep_Data
open Script
open Auto2
open Induct_ProofSteps

val _ = Theory.setup (ItemIO_Data.add_basic_item_io)
val _ = Theory.setup (AC_ProofSteps.add_ac_proofsteps)
val _ = Theory.setup Logic_ProofSteps.add_logic_proofsteps
val _ = Theory.setup Logic_ProofSteps.add_disj_proofsteps
val _ = Theory.setup Logic_ProofSteps.add_disj_normalizers
val _ = Theory.setup Logic_ProofSteps.add_term_def_proofsteps
val TY_DISJ = Logic_ProofSteps.TY_DISJ
val CHOOSE = Logic_ProofSteps.CHOOSE
val CHOOSES = Logic_ProofSteps.CHOOSES
val CHOOSE_FUN_N = Logic_ProofSteps.CHOOSE_FUN_N
val CHOOSE_FUN = CHOOSE_FUN_N 1
val CHOOSE_FUN2 = CHOOSE_FUN_N 2
