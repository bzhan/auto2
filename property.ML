(* Register for property predicates. *)

structure PropertyData =
Theory_Data (
  type T = unit Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge pointer_eq
)

(* Rules deriving new properties of t from other properties of t, or
   properties of f x_1 ... x_n from properties of x_1, ... x_n. In the
   first case, they are indexed under the names of the properties in
   the premises. In the second case, they are indexed under the name
   of the head function f.
 *)
structure PropertyUpdateData =
Theory_Data (
  type T = (thm list) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge_list (op pointer_eq)
)

signature PROPERTY_DATA =
sig
  (* About the PropertyData table. *)
  val add_property_const: term -> theory -> theory
  val is_property_const: theory -> term -> bool
  val is_property_prem: theory -> term -> bool
  val is_property_prem': theory -> term -> bool
  val is_property_prem_ctxt': Proof.context -> term -> bool
  val get_property_name: term -> string
  val get_property_names: term list -> string list
  val get_property_arg: term -> term
  val get_property_args: term list -> term list

  (* About the PropertyUpdateData table.*)
  val add_property_update: thm -> theory -> theory
  val lookup_property_update: theory -> string -> thm list
  val instantiate_property_update: Proof.context -> term -> thm -> thm option
end;

structure Property_Data : PROPERTY_DATA =
struct

fun add_property_const t thy =
    case Term.head_of t of
        Const (nm, T) =>
        let
          val (pTs, cT) = strip_type T
          val _ = assert (cT = boolT)
                         "add_property_const: input should be a predicate."
          val _ = writeln ("Add property " ^ nm ^ ", " ^
                           (string_of_int (length pTs)) ^ " arguments.")
        in
          thy |> PropertyData.map (Symtab.update_new (nm, ()))
        end
      | _ => raise AUTO2 "add_property_const: input should be a constant."

(* Whether the term is a fully-applied property predicate. *)
fun is_property_const thy t =
    if fastype_of t = propT then
      raise AUTO2 "is_property_const: checked on type prop."
    else if not (fastype_of t = boolT) then false else
    case Term.head_of t of
        Const (nm, _) => Symtab.defined (PropertyData.get thy) nm
      | _ => false

(* Stricter condition than is_property_const: the argument must be a
   schematic variable.
 *)
fun is_property_prem thy t =
    is_property_const thy t andalso Term.is_Var (dest_arg t)

fun is_property_prem' thy t =
    is_Trueprop t andalso is_property_prem thy (HOLogic.dest_Trueprop t)

fun is_property_prem_ctxt' ctxt t =
    is_property_prem' (Proof_Context.theory_of ctxt) t

fun get_property_name t =
    case Term.head_of t of
        Const (nm, _) => nm
      | _ => raise AUTO2 "get_property_name: not a constant."

fun get_property_names ts =
    ts |> map get_property_name |> distinct (op =)

fun get_property_arg t =
    dest_arg t
    handle AUTO2 _ => raise AUTO2 "get_property_arg: th in wrong form."

fun get_property_args ts =
    ts |> map get_property_arg |> distinct (op aconv)

(* Add the given rule as a property update. The requirements on th is
   as follows:

   - The conclusion must be a property constant, with argument in the
     form of either ?x or f ?x1 ... ?xn.

   - Each premise must be a property constant on ?x (in the first
     case) or one of ?x1 ... ?xn (in the second case). The argument of
     the property in the conclusion must contain all schematic
     variables of the theorem.
 *)
fun add_property_update th thy =
    let
      val (prems, concl) = strip_horn' th
      val _ = assert (is_property_const thy concl)
                     "add_property_update: concl must be a property constant."
      val _ = assert (forall (is_property_prem thy) prems)
                     "add_property_update: prem must be a property premise."
      val concl_arg = get_property_arg concl
      val all_vars = map Var (Term.add_vars (Thm.prop_of th) [])
    in
      if is_Var concl_arg then
        (* First case. Each premise must also be about ?x. *)
        let
          val _ = assert (length all_vars = 1)
                         "add_property_update: extraneous Vars in th."
          val names = get_property_names prems
          val _ = writeln ("Add property rule for " ^ (string_of_list I names))
        in
          thy |> PropertyUpdateData.map (
            fold (Symtab.update_list (op pointer_eq)) (map (rpair th) names))
        end
      else
        (* Second case. concl_arg in the form f ?x1 ... ?xn. *)
        let
          val (f, args) = Term.strip_comb concl_arg
          val nm =
              case f of
                  Const (nm, _) => nm
                | _ => raise AUTO2 "add_property_update: f is not constant."
          val _ = assert (forall is_Var args)
                         "add_property_update: all args of concl must be Vars."
          val _ = assert (subset (op aconv) (all_vars, args))
                         "add_property_update: extraneous Vars in th."
          val _ = writeln ("Add property rule for function " ^ nm)
        in
          thy |> PropertyUpdateData.map (
            Symtab.update_list (op pointer_eq) (nm, th))
        end
    end

(* Find rules registered under the given name. *)
fun lookup_property_update thy nm =
    Symtab.lookup_list (PropertyUpdateData.get thy) nm

(* Instantiate th by matching t with the argument of the conclusion of
   th. Return NONE if instantiation is unsuccessful (because type does
   not match)
 *)
fun instantiate_property_update ctxt t th =
    let
      val (_, concl) = strip_horn' th
      val concl_arg = get_property_arg concl
      val thy = Proof_Context.theory_of ctxt
    in
      if Sign.typ_instance thy (fastype_of t, fastype_of concl_arg) then
        let
          val inst = pattern_fo_match ctxt (concl_arg, t)
                     handle Pattern.MATCH =>
                            raise AUTO2 "inst_property: cannot match with t."
        in
          SOME (subst_thm ctxt inst th)
        end
      else NONE
    end

end  (* structure Property_Data. *)

open Property_Data
