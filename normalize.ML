(* Normalizing a given theorem. *)

type normalizer = Proof.context -> raw_item -> raw_item list

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
  val add_th_normalizer:
      string * (Proof.context -> thm -> thm list) -> theory -> theory
  val add_single_normalizer:
      string * (Proof.context -> raw_item -> raw_item) -> theory -> theory
  val add_ctxt_conv_normalizer:
      string * (Proof.context -> conv) -> theory -> theory
  val add_conv_normalizer: string * conv -> theory -> theory
  val add_ctxt_prop_normalizer:
      string * (Proof.context -> conv) -> theory -> theory
  val add_eq_th_normalizer: thm -> theory -> theory
  val rewr_obj_eq_top: thm -> Proof.context -> conv
  val add_top_eq_th_normalizer: thm -> theory -> theory
  val const_conv: conv -> conv
  val rewr_obj_eq_const_top: thm -> Proof.context -> conv
  val add_top_eq_th_const_normalizer: thm -> theory -> theory
  val add_top_conv_normalizer:
      string * (Proof.context -> conv) -> theory -> theory
  val get_normalizers: theory -> (string * normalizer) list
  val normalize: Proof.context -> raw_item -> raw_item list
end;

structure Normalizer : NORMALIZER =
struct

fun add_normalizer (nm, norm_fun) =
    NormData.map (Symtab.update_new (nm, norm_fun))

fun add_th_normalizer (nm, norm_th_fun) =
    add_normalizer (
      nm, fn ctxt => fn ritem =>
             case ritem of
                 Handler _ => [ritem]
               | Fact (ty_str, _, th) =>
                 if ty_str = "PROP" then
                   map (thm_to_ritem_ctxt ctxt) (norm_th_fun ctxt th)
                 else [ritem])

fun add_single_normalizer (nm, norm_single_fun) =
    add_normalizer (nm, fn ctxt => fn ritem => [norm_single_fun ctxt ritem])

(* Apply the conversion ctxt_cv ctxt to the statement (skipping
   Trueprop) of a PROP item or EQ item.
 *)
fun add_ctxt_conv_normalizer (nm, ctxt_cv) =
    add_single_normalizer (
      nm, fn ctxt => fn ritem =>
             case ritem of
                 Handler _ => ritem
               | Fact (ty_str, _, th) =>
                 if member (op =) ["PROP", "EQ"] ty_str then
                   thm_to_ritem_ctxt
                       ctxt (apply_to_thm (Conv.arg_conv (ctxt_cv ctxt)) th)
                 else ritem)

(* Apply cv to the statement (skipping Trueprop) of a PROP item. *)
fun add_conv_normalizer (nm, cv) = add_ctxt_conv_normalizer (nm, K cv)

(* Apply ctxt_cv ctxt to either the statement (skipping Trueprop) of a
   PROP item, or the right side of an EQ item.
 *)
fun add_ctxt_prop_normalizer (nm, ctxt_cv) =
    add_single_normalizer (
      nm, fn ctxt => fn ritem =>
             case ritem of
                 Handler _ => ritem
               | Fact (ty_str, _, th) =>
                 let val cv = ctxt_cv ctxt in
                   if ty_str = "PROP" then
                     thm_to_ritem_ctxt ctxt (apply_to_thm (Conv.arg_conv cv) th)
                   else if ty_str = "EQ" then
                     thm_to_ritem_ctxt ctxt (
                       apply_to_thm (Conv.arg_conv (Conv.arg_conv cv)) th)
                   else ritem
                 end)

(* Apply the rewriting theorem eq_th: A = B on the statement (skipping
   Trueprop) of a PROP item.
 *)
fun add_eq_th_normalizer eq_th =
    add_conv_normalizer (name_of_thm eq_th, Conv.try_conv (rewr_obj_eq eq_th))

(* Rewrite on subterms, top order. *)
fun rewr_obj_eq_top eq_th =
    Conv.top_conv (K (Conv.try_conv (rewr_obj_eq eq_th)))

(* Add the given eq_th to rewrite on subterms. *)
fun add_top_eq_th_normalizer eq_th =
    add_ctxt_prop_normalizer (name_of_thm eq_th, rewr_obj_eq_top eq_th)

(* Return whether a given term is a constant (no free or schematic
   variables).
 *)
fun const_conv cv ct =
    if is_const (Thm.term_of ct) then cv ct else Conv.no_conv ct

(* Rewrite on subterms, top order, only on constants. *)
fun rewr_obj_eq_const_top eq_th =
    Conv.top_conv (K (Conv.try_conv (const_conv (rewr_obj_eq eq_th))))

(* Add the given eq_th to rewrite on subterms, only on constants. *)
fun add_top_eq_th_const_normalizer eq_th =
    add_ctxt_prop_normalizer (name_of_thm eq_th, rewr_obj_eq_const_top eq_th)

(* Add the given conversion to rewrite on subterms. *)
fun add_top_conv_normalizer (nm, conv) =
    add_ctxt_prop_normalizer (
      nm, fn ctxt => Conv.top_conv (K (Conv.try_conv (conv ctxt))) ctxt)

fun get_normalizers thy = Symtab.dest (NormData.get thy)

fun normalize ctxt ritem =
    let
      val norms = get_normalizers (Proof_Context.theory_of ctxt)
      fun apply_norm (_, norm_fun) ritems = maps (norm_fun ctxt) ritems
      val norm_once = fold apply_norm norms [ritem]
    in
      case norm_once of
          [ritem'] => if eq_ritem (ritem, ritem') then [ritem']
                      else normalize ctxt ritem'
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
