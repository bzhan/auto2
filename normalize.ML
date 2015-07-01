(* Normalizing a given theorem. *)

type normalizer = Proof.context -> thm -> thm list

(* Keeps list of normalizers. *)
structure NormData =
Theory_Data (
  type T = normalizer Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge pointer_eq
)

signature NORMALIZER =
sig
  val add_normalizer: string * normalizer -> theory -> theory
  val add_single_normalizer:
      string * (Proof.context -> thm -> thm) -> theory -> theory
  val add_ctxt_conv_normalizer:
      string * (Proof.context -> conv) -> theory -> theory
  val add_conv_normalizer: string * conv -> theory -> theory
  val add_ctxt_prop_normalizer:
      string * (Proof.context -> conv) -> theory -> theory
  val add_eq_th_normalizer: thm -> theory -> theory
  val add_top_eq_th_normalizer: thm -> theory -> theory
  val add_top_eq_th_const_normalizer: thm -> theory -> theory
  val add_top_conv_normalizer:
      string * (Proof.context -> conv) -> theory -> theory
  val get_normalizers: theory -> (string * normalizer) list
  val normalize: Proof.context -> thm -> thm list
end;

structure Normalizer : NORMALIZER =
struct

fun add_normalizer (nm, norm_fun) =
    NormData.map (Symtab.update_new (nm, norm_fun))

fun add_single_normalizer (nm, norm_single_fun) =
    add_normalizer (nm, fn ctxt => fn th => [norm_single_fun ctxt th])

(* ctxt_cv is of type Proof.context -> conv. Apply ctxt_cv ctxt to the
   argument (skipping Trueprop).
 *)
fun add_ctxt_conv_normalizer (nm, ctxt_cv) =
    add_single_normalizer (
      nm, fn ctxt => apply_to_thm (Conv.arg_conv (ctxt_cv ctxt)))

fun add_conv_normalizer (nm, cv) = add_ctxt_conv_normalizer (nm, K cv)

(* ctxt_cv is of type Proof.context -> conv. If th is an equality,
   apply to right side. Otherwise to statement of theorem.
 *)
fun add_ctxt_prop_normalizer (nm, ctxt_cv) =
    add_single_normalizer (
      nm, fn ctxt => apply_to_thm (prop_conv (ctxt_cv ctxt)))

(* Apply the rewriting theorem eq_th: A = B on the statement (skipping
   Trueprop).
 *)
fun add_eq_th_normalizer eq_th =
    add_conv_normalizer (name_of_thm eq_th, Conv.try_conv (rewr_obj_eq eq_th))

(* Add the given eq_th to rewrite on subterms. *)
fun add_top_eq_th_normalizer eq_th =
    add_ctxt_prop_normalizer (name_of_thm eq_th, rewr_obj_eq_top eq_th)

(* Add the given eq_th to rewrite on subterms, only on constants. *)
fun add_top_eq_th_const_normalizer eq_th =
    add_ctxt_prop_normalizer (name_of_thm eq_th, rewr_obj_eq_const_top eq_th)

(* Add the given conversion to rewrite on subterms. *)
fun add_top_conv_normalizer (nm, conv) =
    add_ctxt_prop_normalizer (
      nm, fn ctxt => Conv.top_conv (K (Conv.try_conv (conv ctxt))) ctxt)

fun get_normalizers thy = Symtab.dest (NormData.get thy)

fun normalize ctxt th =
    let
      val norms = get_normalizers (Proof_Context.theory_of ctxt)
      fun apply_norm (_, norm_fun) ths = maps (norm_fun ctxt) ths
      val norm_once = fold apply_norm norms [th]
    in
      case norm_once of
          [th'] => if Thm.eq_thm (th, th') then [th']
                   else normalize ctxt th'
        | _ => maps (normalize ctxt) norm_once
    end

end  (* structure Normalizer. *)

open Normalizer

val _ = Theory.setup (add_ctxt_conv_normalizer (
                         "rearrange_assoc",
                         ACUtil.rearrange_assoc_full o Proof_Context.theory_of))
val _ = Theory.setup (add_ctxt_conv_normalizer (
                         "rearrange_ac",
                         ACUtil.rearrange_ac o Proof_Context.theory_of))
