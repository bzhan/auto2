(* Utility functions for separation logic. *)

signature SEP_UTIL =
sig
  val assnT: typ
  val pheapT: typ
  val emp: term
  val assn_true: term
  val assn_ac_info: ac_info
  val assn_comm_cv: conv
  val assn_assoc_sym_cv: conv
  val is_true_assn: term -> bool
  val is_entail: term -> bool
  val dest_entail: term -> term * term
  val cdest_entail: cterm -> cterm * cterm
  val mk_star: term * term -> term
  val is_mod: term -> bool
  val dest_mod: term -> term * term
  val cdest_mod: cterm -> cterm * cterm
  val mk_mod: term * term -> term
  val is_ex_assn: term -> bool
  val is_times: term -> bool
  val mod_assn_conv: conv -> conv
  val heap_of_mod_th: thm -> term
  val is_pure_assn: term -> bool
  val has_pure_assn: term -> bool
  val strip_pure_assn: term -> term

  val is_hoare_triple: term -> bool
  val dest_hoare_triple: term -> term * term * term
  val name_of_sep_proc: term -> string

  val mult_emp_left: conv
  val mult_emp_right: conv
  val reduce_emp_right: conv
  val entail_triv_th: Proof.context -> term -> thm
  val entail_true_th: Proof.context -> term -> thm
  val apply_to_entail_l: conv -> thm -> thm
  val apply_to_entail_r: conv -> thm -> thm
end;

structure SepUtil : SEP_UTIL =
struct

val assnT = @{typ assn}
val pheapT = @{typ pheap}
val emp = @{term emp}
val assn_true = @{term true}
val assn_ac_info = Nat_Arith.times_ac_on_typ @{theory} assnT
val assn_comm_cv = rewr_obj_eq (#comm_th assn_ac_info)
val assn_assoc_sym_cv = rewr_obj_eq (obj_sym (#assoc_th assn_ac_info))

fun is_true_assn t =
    case t of
        Const (@{const_name top_assn}, _) => true
      | _ => false

fun is_entail t =
    case t of
        Const (@{const_name entails}, _) $ _ $ _ => true
      | _ => false

(* Deconstruct A ==>_A B into (A, B). *)
fun dest_entail t =
    case t of
        Const (@{const_name entails}, _) $ A $ B => (A, B)
      | _ => raise Fail "dest_entail: unexpected t."

fun cdest_entail ct =
    case Thm.term_of ct of
        Const (@{const_name entails}, _) $ _ $ _ =>
        (Thm.dest_arg1 ct, Thm.dest_arg ct)
      | _ => raise Fail "dest_entail: unexpected t."

(* Given pair of assertions (A, B), form the assertion A * B. *)
fun mk_star (A, B) =
    Const (@{const_name times}, assnT --> assnT --> assnT) $ A $ B

(* Tests whether t is of form h |= P. *)
fun is_mod t =
    case t of Const (@{const_name models}, _) $ _ $ _ => true
            | _ => false

(* Deconstruct h |= P into (h, P). *)
fun dest_mod t =
    case t of
        Const (@{const_name models}, _) $ h $ P => (h, P)
      | _ => raise Fail "dest_mod: unexpected t."

fun cdest_mod ct =
    case Thm.term_of ct of
        Const (@{const_name models}, _) $ _ $ _ =>
        (Thm.dest_arg1 ct, Thm.dest_arg ct)
      | _ => raise Fail "dest_mod: unexpected t."

(* Given pheap h and assertion P, form the proposition h |= P. *)
fun mk_mod (h, P) =
    Const (@{const_name models}, pheapT --> assnT --> boolT) $ h $ P

fun is_ex_assn t =
    case t of
        Const (@{const_name ex_assn}, _) $ _ => true
      | _ => false

fun is_times t =
    case t of
        Const (@{const_name times}, _) $ _ $ _ => true
      | _ => false

(* Given term h |= P, apply conversion on P. *)
val mod_assn_conv = Conv.arg_conv

(* Given theorem h |= P, return the term h. *)
fun heap_of_mod_th mod_th =
    mod_th |> prop_of' |> dest_mod |> fst

(* Whether t is of the form \<up>(b). *)
fun is_pure_assn t =
    case t of
        Const (@{const_name pure_assn}, _) $ _ => true
      | _ => false

(* Given t of form t1 * ... * tn, check whether any of them is of the
   form \<up>(b).
 *)
fun has_pure_assn t =
    exists is_pure_assn (ACUtil.dest_ac assn_ac_info t)

(* Given t of form t1 * ... * tn, remove those ti that are pure
   assertions and return the product of the remaining terms.
 *)
fun strip_pure_assn t =
    if is_times t andalso is_pure_assn (dest_arg t) then
      strip_pure_assn (dest_arg1 t)
    else if is_pure_assn t then emp
    else t

fun is_hoare_triple t =
    case t of
        Const (@{const_name hoare_triple}, _) $ _ $ _ $ _ => true
      | _ => false

fun dest_hoare_triple t =
    case t of
        Const (@{const_name hoare_triple}, _) $ P $ c $ Q => (P, c, Q)
      | _ => raise Fail "dest_hoare_triple"

fun name_of_sep_proc c =
    case Term.head_of c of
        Const (nm, _) => nm
      | _ => raise Fail "name_of_sep_proc"

(* Convert A to emp * A *)
val mult_emp_left = rewr_obj_eq (obj_sym @{thm mult_1})

(* Convert A to A * emp *)
val mult_emp_right = rewr_obj_eq (obj_sym @{thm mult_1_right})

(* Convert A * emp to A *)
val reduce_emp_right = rewr_obj_eq @{thm mult_1_right}

(* Given A of type assnT, return the theorem A ==> A. *)
fun entail_triv_th ctxt A =
    let
      val thy = Proof_Context.theory_of ctxt
      val inst = Pattern.first_order_match thy (Var (("A", 0), assnT), A) fo_init
    in
      Util.subst_thm ctxt inst @{thm entails_triv}
    end

(* Given A of type assnT, return the theorem A ==> true. *)
fun entail_true_th ctxt A =
    let
      val thy = Proof_Context.theory_of ctxt
      val inst = Pattern.first_order_match thy (Var (("A", 0), assnT), A) fo_init
    in
      Util.subst_thm ctxt inst @{thm entails_true}
    end

(* Given theorem A ==> B and a conversion cv, apply cv to A *)
val apply_to_entail_l = apply_to_thm' o Conv.arg1_conv

(* Given theorem A ==> B and a conversion cv, apply cv to B *)
val apply_to_entail_r = apply_to_thm' o Conv.arg_conv

end  (* structure SepUtil *)
