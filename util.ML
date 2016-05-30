(* Utility functions. *)

infix andf2 orf2

signature UTIL =
sig
  (* Exceptions *)
  exception AUTO2 of string
  exception AUTO2T of string * term list
  exception AUTO2CT of string * cterm list
  val assert: bool -> string -> unit

  (* Booleans *)
  val andf2: ('a -> 'b -> bool) * ('a -> 'b -> bool) -> 'a -> 'b -> bool
  val orf2: ('a -> 'b -> bool) * ('a -> 'b -> bool) -> 'a -> 'b -> bool

  (* Types *)
  val propT: typ
  val natT: typ
  val intT: typ
  val boolT: typ
  val get_arg_type: term -> typ

  (* Lists *)
  val max: ('a * 'a -> order) -> 'a list -> 'a
  val max_partial: ('a -> 'a -> bool) -> 'a list -> 'a list
  val is_sorted: ('a * 'a -> order) -> 'a list -> bool
  val subsets: 'a list -> 'a list list
  val nth_drop_list: int list -> 'a list -> 'a list
  val the_pair: 'a list -> 'a * 'a
  val the_triple: 'a list -> 'a * 'a * 'a
  val list_pair: 'a * 'a -> 'a list
  val filter_split: ('a -> bool) -> 'a list -> 'a list * 'a list
  val filter_first_split: ('a -> bool) -> 'a list -> 'a list * 'a list
  val all_pairs: 'a list * 'b list -> ('a * 'b) list
  val all_distinct_pairs: 'a list -> ('a * 'a) list

  (* Strings. *)
  val is_prefix_str: string -> string -> bool

  (* Managing matching environments. *)
  val fo_init: Type.tyenv * Envir.tenv
  val defined_instn: Type.tyenv * Envir.tenv -> string * int -> bool
  val lookup_instn: Type.tyenv * Envir.tenv -> string * int -> term
  val lookup_inst: Type.tyenv * Envir.tenv -> string -> term
  val lookup_tyinst: Type.tyenv * Envir.tenv -> string -> typ
  val update_env: indexname * term -> Type.tyenv * Envir.tenv ->
                  Type.tyenv * Envir.tenv

  (* Wrapper around matching functions in pattern. *)
  val pattern_fo_match_thy: theory -> term * term -> Type.tyenv * Envir.tenv
  val pattern_fo_match: Proof.context -> term * term -> Type.tyenv * Envir.tenv
  val pattern_match: Proof.context -> term * term -> Type.tyenv * Envir.tenv
  val pattern_match_ty: Proof.context -> typ * typ -> Type.tyenv
  val typ_match: theory -> typ * typ -> Type.tyenv

  (* Printing functions, mostly from Isabelle Cookbook. *)
  val pretty_term: Proof.context -> term -> Pretty.T
  val pretty_term_thy: theory -> term -> Pretty.T
  val pwriteln: Pretty.T -> unit
  val str: Pretty.T -> string
  val pretty_terms: Proof.context -> term list -> Pretty.T
  val pretty_terms_thy: theory -> term list -> Pretty.T
  val pretty_cterm: Proof.context -> cterm -> Pretty.T
  val pretty_cterms: Proof.context -> cterm list -> Pretty.T
  val pretty_typ: Proof.context -> typ -> Pretty.T
  val pretty_typs: Proof.context -> typ list -> Pretty.T
  val pretty_ctyp: Proof.context -> ctyp -> Pretty.T
  val pretty_ctyps: Proof.context -> ctyp list -> Pretty.T
  val pretty_tyenv: Proof.context -> Type.tyenv -> string
  val pretty_env: Proof.context -> Envir.tenv -> string
  val string_of_list: ('a -> string) -> 'a list -> string
  val string_of_list': ('a -> string) -> 'a list -> string
  val string_of_int_list: int list -> string
  val string_of_bool: bool -> string
  val enum_noindent: string -> string -> string -> Pretty.T list -> Pretty.T

  (* Tracing functions. *)
  val trace_t_ctxt: Proof.context -> string -> term -> unit
  val trace_tlist_ctxt: Proof.context -> string -> term list -> unit
  val trace_thm_ctxt: Proof.context -> string -> thm -> unit
  val trace_fullthm_ctxt: Proof.context -> string -> thm -> unit
  val trace_t: string -> term -> unit
  val trace_tlist: string -> term list -> unit
  val trace_thm: string -> thm -> unit
  val trace_fullthm: string -> thm -> unit

  (* Certifying terms and types. *)
  val cert: Proof.context -> term -> cterm
  val tycert: Proof.context -> typ -> ctyp
  val cert_thy: theory -> term -> cterm
  val tycert_thy: theory -> typ -> ctyp

  (* Managing context. *)
  val declare_free_term: term -> Proof.context -> Proof.context
  val read_term: Proof.context -> string -> term
  val read_pat: Proof.context -> string -> term

  (* Terms. *)
  val null_term: term
  val is_null_term: term -> bool
  val bool_False: term
  val prop_False: term
  val is_Trueprop: term -> bool
  val is_neg: term -> bool
  val get_neg: term -> term
  val get_neg': term -> term
  val is_implies: term -> bool
  val dest_binop: term -> term * (term * term)
  val is_numc: term -> bool
  val dest_numc: term -> int
  val is_eq_term: term -> bool
  val is_eq_term': term -> bool
  val is_meta_eq_term: term -> bool
  val is_meta_eq_thm: thm -> bool
  val occurs_frees: term list -> term -> bool
  val occurs_free: term -> term -> bool
  val has_vars: term -> bool
  val is_subterm: term -> term -> bool
  val has_subterm: term list -> term -> bool
  val dest_obj_all_var: term -> int -> term * term
  val strip_obj_all_var: term -> term list * term
  val strip_obj_imp: term -> term list * term
  val lambda_abstract: term -> term -> term
  val is_order: term -> bool
  val is_linorder: Proof.context -> term -> bool
  val is_pattern: term -> bool
  val print_term_detail: Proof.context -> term -> string

  (* Theorems. *)
  val true_th: thm
  val is_true_th: thm -> bool
  val apply_on: thm list -> thm -> thm
  val prop_of': thm -> term
  val comb_equiv: cterm * thm list -> thm
  val name_of_thm: thm -> string
  val update_name_of_thm: thm -> string -> thm -> thm
  val dest_eq_thm: thm -> term * term
  val lhs_of: thm -> term
  val rhs_of: thm -> term
  val make_trueprop_eq: thm -> thm
  val assume_eq: theory -> term * term -> thm
  val assume_meta_eq: theory -> term * term -> thm
  val assume_thm: Proof.context -> term -> thm
  val rename_abs: Type.tyenv * Envir.tenv -> term -> term
  val rename_abs_thm: Type.tyenv * Envir.tenv -> thm -> thm
  val subst_thm_thy: theory -> Type.tyenv * Envir.tenv -> thm -> thm
  val subst_thm: Proof.context -> Type.tyenv * Envir.tenv -> thm -> thm
  val subst_term_norm: Type.tyenv * Envir.tenv -> term -> term
  val apply_to_thm: conv -> thm -> thm
  val apply_to_thm': conv -> thm -> thm
  val to_meta_eq: thm -> thm
  val to_obj_eq: thm -> thm
  val obj_sym: thm -> thm
  val meta_sym: thm -> thm
  val rewr_obj_eq: thm -> conv
  val rewr_obj_eq_top: thm -> Proof.context -> conv
  val apply_to_lhs: conv -> thm -> thm
  val apply_to_rhs: conv -> thm -> thm
  val concl_conv: int -> conv -> conv
  val make_neg_eq: thm -> thm
  val rewrite_to_contra_form: conv
  val rewrite_thm_to_contra_form: thm -> thm
  val rewrite_from_contra_form: conv
  val rewrite_thm_from_contra_form: thm -> thm
  val send_to_hyps: cterm -> thm -> thm
  val send_all_to_hyps: thm -> thm
  val send_concrete_to_hyps: thm -> thm
  val transitive_list: thm list -> thm
  val skip_n_conv: int -> conv -> conv
  val to_obj_conv: Proof.context -> conv
  val to_obj_conv_on_horn: Proof.context -> conv
  val to_obj_conv_on_horn_th: thm -> thm
  val to_meta_imp_conv: conv
  val to_meta_imp_conv_n: int -> conv
  val to_meta_all_conv: Proof.context -> conv
  val conj_left_th: thm -> thm
  val conj_right_th: thm -> thm
  val equiv_forward_th: thm -> thm
  val equiv_backward_th: thm -> thm
  val to_obj_eq_th: thm -> thm
  val obj_sym_th: thm -> thm
  val horn_conv: conv -> conv
  val split_conj_th: thm -> thm list
  val split_not_disj_th: thm -> thm list
  val strip_horn': thm -> term list * term
  val ex_elim: Proof.context -> term -> thm -> thm
  val to_eqF_th: thm -> thm
  val neg_ineq_cv: conv
  val neg_ineq_back_cv: conv
  val normalize_exs_conv: int -> Proof.context -> conv
  val normalize_alls_conv: int -> Proof.context -> conv

  (* Conversions *)
  val reverse_eta_conv: Proof.context -> conv
  val repeat_n_conv: int -> conv -> conv

  (* Wrapper around common tactics. *)
  val prove_by_tac: (Proof.context -> int -> tactic) -> Proof.context ->
                    thm list -> term -> thm
  val contra_by_tac: (Proof.context -> int -> tactic) -> Proof.context ->
                     thm list -> thm
  val prove_by_simp: Proof.context -> thm list -> term -> thm
  val contra_by_simp: Proof.context -> thm list -> thm
  val prove_by_arith: Proof.context -> thm list -> term -> thm
  val contra_by_arith: Proof.context -> thm list -> thm

  (* Miscellaneous. *)
  val test_conv: Proof.context -> conv -> string -> string * string -> unit
  val term_pat_setup: theory -> theory
  val cterm_pat_setup: theory -> theory
  val type_pat_setup: theory -> theory
  val timer: string * (unit -> 'a) -> 'a
  val exn_trace: (unit -> 'a) -> 'a
end;

structure Util : UTIL =
struct

exception AUTO2 of string
exception AUTO2T of string * term list
exception AUTO2CT of string * cterm list
fun assert b exn_str = if b then () else raise AUTO2 exn_str

fun p andf2 q = fn x => fn y => p x y andalso q x y
fun p orf2 q = fn x => fn y => p x y orelse q x y

val propT = @{typ prop}
val natT = HOLogic.natT
val intT = @{typ int}
val boolT = HOLogic.boolT

(* Given t in inequality form, return the type of the argument. *)
fun get_arg_type t = t |> strip_comb |> snd |> hd |> Term.type_of

fun max comp lst =
    let
      fun max2 t1 t2 = if comp (t1, t2) = LESS then t2 else t1
    in
      case lst of
          [] => raise AUTO2 "max: empty list"
        | l :: ls => fold max2 ls l
    end

(* Given a function comp, remove y for each pair (x, y) such that comp
   x y = true (if x dominates y).
 *)
fun max_partial comp lst =
    let
      fun helper taken remains =
          case remains of
              [] => taken
            | x :: xs =>
              if exists (fn y => comp y x) taken then
                helper taken xs
              else
                helper (x :: filter_out (fn y => comp x y) taken) xs
    in
      helper [] lst
    end

(* Determine whether lst is sorted according to ord. *)
fun is_sorted comp lst =
    case lst of [] => true | [_] => true
                | a1 :: a2 :: a' => comp (a1, a2) <> GREATER andalso
                                    is_sorted comp (a2 :: a')

(* Return all subsets of lst. *)
fun subsets [] = [[]]
  | subsets (l::ls) = let val prev = subsets ls
                      in prev @ map (cons l) prev end

(* Drop indices specified by is. *)
fun nth_drop_list is lst = fold nth_drop (sort (rev_order o int_ord) is) lst

(* Convert list to pair. List must consist of exactly two items. *)
fun the_pair lst =
    case lst of [i1, i2] => (i1, i2)
              | _ => raise AUTO2 "the_pair: list is not of length 2."

(* Convert list to triple. List must consist of exactly three items. *)
fun the_triple lst =
    case lst of [i1, i2, i3] => (i1, i2, i3)
              | _ => raise AUTO2 "the_triple: list is not of length 3."

(* Convert pair to list of two elements. *)
fun list_pair (x, y) = [x, y]

(* Split list into (ins, outs), where ins satisfy f, and outs don't. *)
fun filter_split _ [] = ([], [])
  | filter_split f (x :: xs) =
    let
      val (ins, outs) = filter_split f xs
    in
      if f x then (x :: ins, outs) else (ins, x :: outs)
    end

(* Split list into (ins, outs), where ins is the longest prefix of
   list for which every element satisfy f, and outs is the rest.
 *)
fun filter_first_split _ [] = ([], [])
  | filter_first_split f (x :: xs) =
    if not (f x) then ([], x :: xs)
    else let
      val (ins, outs) = filter_first_split f xs
    in
      (x :: ins, outs)
    end

(* Form the Cartesian product of two lists. *)
fun all_pairs (l1, l2) =
    maps (fn y => (map (fn x => (x, y)) l1)) l2

(* For l of length n, form the n * (n-1) / 2 distinct pairs of
   elements in l.
 *)
fun all_distinct_pairs l =
    let
      fun list_i i = map (rpair (nth l i)) (take i l)
    in
      maps list_i (0 upto (length l - 1))
    end

(* Whether pre is a prefix of str. *)
fun is_prefix_str pre str =
    is_prefix (op =) (String.explode pre) (String.explode str)

val fo_init = (Vartab.empty, Vartab.empty)

(* Lookup a Vartab inst with string and integer specifying indexname. *)
fun defined_instn (_, inst) (str, n) = Vartab.defined inst (str, n)
fun lookup_instn (_, inst) (str, n) =
    case Vartab.lookup inst (str, n) of
        NONE => raise AUTO2 ("lookup_inst: not found " ^ str ^
                             (if n = 0 then "" else string_of_int n))
      | SOME (_, u) => u
fun lookup_inst (tyinst, inst) str = lookup_instn (tyinst, inst) (str, 0)
fun lookup_tyinst (tyinst, _) str =
    case Vartab.lookup tyinst (str, 0) of
        NONE => raise AUTO2 ("lookup_tyinst: not found " ^ str)
      | SOME (_, T) => T

fun update_env (idx, t) (tyenv, tenv) =
    (tyenv, tenv |> Vartab.update_new (idx, (type_of t, t)))

fun pattern_fo_match_thy thy (t, u) =
    Pattern.first_order_match thy (t, u) fo_init
fun pattern_fo_match ctxt (t, u) =
    Pattern.first_order_match (Proof_Context.theory_of ctxt) (t, u) fo_init
fun pattern_match ctxt (t, u) =
    Pattern.match (Proof_Context.theory_of ctxt) (t, u) fo_init
fun pattern_match_ty ctxt (ty, ty') =
    Sign.typ_match (Proof_Context.theory_of ctxt) (ty, ty') Vartab.empty
fun typ_match thy (T, U) = Sign.typ_match thy (T, U) Vartab.empty

val pretty_term = Syntax.pretty_term
val pretty_term_thy = Syntax.pretty_term_global
val pwriteln = Pretty.writeln
val str = Pretty.string_of
fun pretty_terms ctxt trms =
    Pretty.block (Pretty.commas (map (pretty_term ctxt) trms))
fun pretty_terms_thy thy trms =
    Pretty.block (Pretty.commas (map (pretty_term_thy thy) trms))
fun pretty_cterm ctxt ctrm = pretty_term ctxt (Thm.term_of ctrm)
fun pretty_cterms ctxt ctrms =
    Pretty.block (Pretty.commas (map (pretty_cterm ctxt) ctrms))
fun pretty_typ ctxt ty = Syntax.pretty_typ ctxt ty
fun pretty_typs ctxt tys =
    Pretty.block (Pretty.commas (map (pretty_typ ctxt) tys))
fun pretty_ctyp ctxt cty = pretty_typ ctxt (Thm.typ_of cty)
fun pretty_ctyps ctxt ctys =
    Pretty.block (Pretty.commas (map (pretty_ctyp ctxt) ctys))

fun pretty_helper aux env =
    env |> Vartab.dest
        |> map aux
        |> map (fn (s1, s2) => Pretty.block [s1, Pretty.str " := ", s2])
        |> Pretty.enum "," "[" "]"
        |> str

fun pretty_tyenv ctxt tyenv =
    let
      fun get_typs (v, (s, T)) = (TVar (v, s), T)
      val print = apply2 (pretty_typ ctxt)
    in
      pretty_helper (print o get_typs) tyenv
    end

fun pretty_env ctxt env =
    let
      fun get_trms (v, (T, t)) = (Var (v, T), t)
      val print = apply2 (pretty_term ctxt)
    in
      pretty_helper (print o get_trms) env
    end

fun string_of_list func lst =
    Pretty.str_list "[" "]" (map func lst) |> str
fun string_of_list' func lst =
    if length lst = 1 then func (the_single lst) else string_of_list func lst
val string_of_int_list = string_of_list (string_of_int)
fun string_of_bool b = if b then "true" else "false"
fun block_noindent prts = Pretty.blk (0, prts)
fun enclose_noindent lpar rpar prts =
    block_noindent (Pretty.str lpar :: (prts @ [Pretty.str rpar]))
fun enum_noindent sep lpar rpar prts =
    enclose_noindent lpar rpar (Pretty.separate sep prts)

fun trace_t_ctxt ctxt s trm =
    tracing (s ^ " " ^ (trm |> pretty_term ctxt |> str))
fun trace_tlist_ctxt ctxt s tlist =
    tracing (s ^ " " ^ (tlist |> pretty_terms ctxt |> str))
fun trace_thm_ctxt ctxt s th =
    tracing (s ^ " " ^ (th |> Thm.prop_of |> pretty_term ctxt |> str))
fun trace_fullthm_ctxt ctxt s th =
    tracing (s ^ " [" ^ (Thm.hyps_of th |> pretty_terms ctxt |> str) ^
             "] ==> " ^ (Thm.prop_of th |> pretty_term ctxt |> str))
val trace_t = trace_t_ctxt @{context}
val trace_tlist = trace_tlist_ctxt @{context}
fun trace_thm s th = trace_thm_ctxt (
      Proof_Context.init_global (Thm.theory_of_thm th)) s th
fun trace_fullthm s th = trace_fullthm_ctxt (
      Proof_Context.init_global (Thm.theory_of_thm th)) s th

fun cert ctxt t = Thm.cterm_of ctxt t
fun tycert ctxt ty = Thm.ctyp_of ctxt ty
fun cert_thy thy t = Thm.global_cterm_of thy t
fun tycert_thy thy ty = Thm.global_ctyp_of thy ty

fun declare_free_term t ctxt =
    if not (is_Free t) then raise AUTO2 "declare_free_term: t not free."
    else ctxt |> Variable.add_fixes_direct [t |> Term.dest_Free |> fst]
              |> Variable.declare_term t
val read_term = Syntax.read_term
val read_pat = Proof_Context.read_term_pattern

val null_term = Term.dummy
fun is_null_term t = (t aconv null_term)
val bool_False = @{term False}
val prop_False = @{prop False}

(* Returns whether the given term is Trueprop. *)
fun is_Trueprop t =
    let val _ = assert (fastype_of t = propT) "is_Trueprop: wrong type"
    in case t of Const (@{const_name Trueprop}, _) $ _ => true
               | _ => false
    end

(* Returns whether the given term is in neg form. *)
fun is_neg t =
    let val _ = assert (fastype_of t = boolT) "is_neg: wrong type"
    in case t of Const ("HOL.Not", _) $ _ => true
               | _ => false
    end

(* Returns the negation of the given term. Avoids double negatives. *)
fun get_neg t =
    let val _ = assert (fastype_of t = boolT) "get_neg: wrong type"
    in case t of Const ("HOL.Not", _) $ t => t
               | _ => HOLogic.Not $ t
    end

(* Version of get_neg for Trueprop terms. *)
fun get_neg' t =
    let val _ = assert (is_Trueprop t) "get_neg': input should be a Trueprop."
    in t |> HOLogic.dest_Trueprop |> get_neg |> HOLogic.mk_Trueprop end

(* Whether a given term is ==>. *)
fun is_implies t =
    let val _ = assert (fastype_of t = propT) "is_implies: wrong type"
    in case t of Const ("Pure.imp", _) $ _ $ _ => true
               | _ => false
    end

(* Extract the last two arguments on t, collecting the rest into f. *)
fun dest_binop t =
    case t of
        f $ a $ b => (f, (a, b))
      | _ => raise AUTO2 "dest_binop: invalid input"

(* Test if a term represents a numerical constant. is_numc_raw just
   uses dest_number from HOLogic. is_numc tests for inverses.
 *)
fun is_numc_raw t =
    let val _ = HOLogic.dest_number t in true end
    handle TERM ("dest_number", _) => false

fun is_numc t =
    case t of
        Const (@{const_name inverse}, _) $ t' => is_numc t'
      | Const (@{const_name uminus}, _) $ t' => is_numc t'
      | Const (@{const_name of_rat}, _) $ r => is_numc r
      | Const (@{const_name Fract}, _) $ n $ d => is_numc n andalso is_numc d
      | _ => is_numc_raw t

(* Deconstruct numerical constant. Discard type. *)
fun dest_numc t = HOLogic.dest_number t |> snd
                  handle TERM ("dest_number", _) =>
                         raise AUTO2 "dest_numc: invalid term."

(* Test if a given fact is an equality. *)
fun is_eq_term t =
    let val _ = assert (fastype_of t = boolT) "is_eq_term: wrong type"
    in case t of Const ("HOL.eq", _) $ _ $ _ => true
               | _ => false
    end

(* Version of is_eq_term' for Trueprop terms. *)
fun is_eq_term' t =
    let val _ = assert (fastype_of t = propT) "is_eq_term': wrong type"
    in is_Trueprop t andalso is_eq_term (HOLogic.dest_Trueprop t) end

(* Whether the term is of the form A == B. *)
fun is_meta_eq_term t =
    let val _ = assert (fastype_of t = propT) "is_meta_eq_term: wrong type"
    in case t of Const ("Pure.eq", _) $ _ $ _ => true
               | _ => false
    end

val is_meta_eq_thm = is_meta_eq_term o Thm.prop_of

(* Given free variable freevar (or a list of free variables freevars),
   determine whether any of the inputs appears in t.
 *)
fun occurs_frees freevars t =
    inter (op aconv) (map Free (Term.add_frees t [])) freevars <> []
fun occurs_free freevar t = occurs_frees [freevar] t

(* Whether the given term contains schematic variables. *)
fun has_vars t = length (Term.add_vars t []) > 0

(* Whether subt is a subterm of t. *)
fun is_subterm subt t = exists_subterm (fn t' => t' aconv subt) t

(* Whether any of subts is a subterm of t. *)
fun has_subterm subts t = exists_subterm (fn t' => member (op aconv) subts t') t

(* Given t of the form !a. P(a), return pair (?a, P(?a_)). Here idx is
   the index to assign to the created Var.
 *)
fun dest_obj_all_var t idx =
    case t of
        Const ("HOL.All", _) $ Abs (abs as (_, T, _)) =>
        let
          val (nm, body) = Term.dest_abs abs
          val bd_var = Var ((Name.internal nm, idx), T)
          val bd_free = Free (nm, T)
          val body' = Term.subst_atomic [(bd_free, bd_var)] body
        in
          (bd_var, body')
        end
      | _ => raise AUTO2 "dest_obj_all_var"

(* Given t of the form !a1, ... an. P(a1, ..., an), return pair
   ([?a1_, ... ?an_], P(?a1_, ..., ?an_).
 *)
fun strip_obj_all_var_aux t idx =
    case t of
        Const ("HOL.All", _) $ Abs _ =>
        let
          val (bd_var, body) = dest_obj_all_var t idx
          val (rest, body') = strip_obj_all_var_aux body (idx + 1)
        in
          (bd_var :: rest, body')
        end
      | _ => ([], t)
fun strip_obj_all_var t = strip_obj_all_var_aux t 0

(* Given t of form A1 --> ... --> An, return ([A1, ..., A(n-1)], An). *)
fun strip_obj_imp t =
    case t of
        Const ("HOL.implies", _) $ A $ B =>
        let val (As, B') = strip_obj_imp B in (A :: As, B') end
      | _ => ([], t)

(* If stmt is P(t), return lambda t. P(t). *)
fun lambda_abstract t stmt = lambda t (Term.abstract_over (t, stmt))

(* Whether the given term is a < b or a <= b. *)
fun is_order t =
    let
      val _ = assert (fastype_of t = boolT) "is_order: wrong type"
    in
      case t of Const (@{const_name less}, _) $ _ $ _ => true
              | Const (@{const_name less_eq}, _) $ _ $ _ => true
              | _ => false
    end

fun is_linorder ctxt t =
    is_order t andalso Sign.of_sort (Proof_Context.theory_of ctxt)
                                    (get_arg_type t, ["Orderings.linorder"])

(* A more general criterion for patterns. In combinations, any
   argument that is a pattern (in the more general sense) frees up
   checking for any functional schematic variables in that argument.
 *)
fun is_pattern t =
    let
      fun is_funT T = case T of Type ("fun", _) => true | _ => false
      fun get_fun_vars t = (Term.add_vars t [])
                               |> filter (is_funT o snd) |> map Var

      fun test_list exclude_vars ts =
          case ts of
              [] => true
            | [t] => test_term exclude_vars t
            | t :: ts' =>
              if test_term exclude_vars t then
                test_list (merge (op aconv) (exclude_vars, get_fun_vars t)) ts'
              else if test_list exclude_vars ts' then
                test_term (distinct (op aconv)
                                    (exclude_vars @ maps get_fun_vars ts')) t
              else false

      and test_term exclude_vars t =
          case t of
              Abs (_, _, t') => test_term exclude_vars t'
            | _ => let val (head, args) = strip_comb t in
                     if is_Var head then
                       if member (op aconv) exclude_vars head then
                         test_list exclude_vars args
                       else
                         forall is_Bound args andalso
                         not (has_duplicates (op aconv) args)
                     else
                       test_list exclude_vars args
                   end
    in
      test_term [] t
    end

fun print_term_detail ctxt t =
    case t of
        Const (s, ty) => "Const (" ^ s ^ ", " ^ (pretty_typ ctxt ty |> str)
      | Free (s, ty) => "Free (" ^ s ^ ", " ^ (pretty_typ ctxt ty |> str)
      | Var ((nm, i), ty) => "Var ((" ^ nm ^ ", " ^ (string_of_int i) ^ "), " ^
                             (pretty_typ ctxt ty |> str) ^ ")"
      | Bound n => "Bound " ^ (string_of_int n)
      | Abs (s, ty, b) => "Abs (" ^ s ^ ", " ^ (pretty_typ ctxt ty |> str) ^
                          ", " ^ (print_term_detail ctxt b) ^ ")"
      | u $ v => "(" ^ print_term_detail ctxt u ^ ") $ (" ^
                 print_term_detail ctxt v ^ ")"

val true_th = @{thm TrueI}
fun is_true_th th = pointer_eq (th, true_th)
fun apply_on ths th = ths MRS th

fun prop_of' th = HOLogic.dest_Trueprop (Thm.prop_of th)

(* Given a head cterm f (function to be applied), and a list of
   equivalence theorems of arguments, produce an equivalent theorem
   for the overall term.
 *)
fun comb_equiv (cf, arg_equivs) =
    Library.foldl (uncurry Thm.combination) (Thm.reflexive cf, arg_equivs)

(* Retrive name of theorem. *)
fun name_of_thm th = if Thm.has_name_hint th then Thm.get_name_hint th
                     else raise AUTO2 "name_of_thm: not found"

(* Set the name of th to the name of ori_th, followed by suffix. *)
fun update_name_of_thm ori_th suffix th =
    if Thm.has_name_hint ori_th then
      th |> Thm.put_name_hint (Thm.get_name_hint ori_th ^ suffix)
    else th

fun dest_eq_thm th = th |> prop_of' |> HOLogic.dest_eq

val lhs_of = Thm.term_of o Thm.lhs_of
val rhs_of = Thm.term_of o Thm.rhs_of

(* Given an equality between bools, make it an equality between props,
   by applying the function Trueprop to both sides.
 *)
fun make_trueprop_eq th =
    Thm.combination (Thm.reflexive (cert @{context} HOLogic.Trueprop)) th

(* Assumed theorems. *)
fun assume_eq thy (t1, t2) =
    Thm.assume (cert_thy thy (HOLogic.mk_Trueprop (HOLogic.mk_eq (t1, t2))))
fun assume_meta_eq thy (t1, t2) =
    Thm.assume (cert_thy thy (Logic.mk_equals (t1, t2)))
fun assume_thm ctxt t =
    if type_of t <> propT then
      raise AUTO2CT ("assume_thm: t is not of type prop", [cert ctxt t])
    else Thm.assume (cert ctxt t)

(* Given a term with schematic variables, and instantiation for those
   schematic variables, adjust names of abstractions in the term using
   names of abstractions in the instantiations.

   For example, if t is !x. P x, and P is instantiated to %m. Q m,
   then the new term should be !m. P m.
 *)
fun rename_abs inst t =
    let
      fun obtain_abs_nms instP =
          case instP of
              Abs (nm, _, body) => nm :: (obtain_abs_nms body)
            | _ => []

      fun obtain_hint (nm, arg) hints =
          case arg of
              Bound i => hints |> Inttab.update (i, nm)
            | _ => hints

      (* Given t as a possibly open subterm of the proposition of th,
         obtain name hints from t (as a Inttab mapping de-Bruijn
         indices to names) and rename using hint for de-Bruijn zero if
         t is an abstraction.
       *)
      fun helper t =
          case t of
              (Abs (nm, T, body)) =>
              let
                val (body', hints) = helper body
                val nm' = case Inttab.lookup hints 0 of
                              NONE => nm | SOME hint => hint
                fun shift_id (i, str) =
                    if i = 0 then [] else [(i-1, str)]
                val hints' = hints |> Inttab.dest |> maps shift_id
                                   |> Inttab.make
              in
                (Abs (nm', T, body'), hints')
              end
            | _ $ _ =>
              let
                val (f, args) = Term.strip_comb t
              in
                case f of
                    Var ((P, n), _) =>
                    if not (defined_instn inst (P, n))
                    then (t, Inttab.empty) else
                    let
                      val instP = lookup_instn inst (P, n)
                      val P_nms = obtain_abs_nms instP
                    in
                      if length P_nms = length args then
                        (t, fold obtain_hint (P_nms ~~ args) Inttab.empty)
                      else  (* This case is unclear *)
                        (t, Inttab.empty)
                    end
                  | _ =>
                    let
                      (* Apply to args to get new arguments args'. For
                         hints, take the last non-empty hint.
                       *)
                      val res = map helper args
                      val args' = map fst res
                      val hints = filter_out Inttab.is_empty (map snd res)
                      val hints_last = if length hints > 0 then List.last hints
                                       else Inttab.empty
                    in
                      (Term.list_comb (f, args'), hints_last)
                    end
              end
            | _ => (t, Inttab.empty)
      val t' = helper t |> fst
      val _ = assert (t aconv t') "rename_abs: not aconv"
    in
      t'
    end

fun rename_abs_thm inst th =
    let
      val prop' = rename_abs inst (Thm.prop_of th)
    in
      Thm.renamed_prop prop' th
    end

(* Similar to Envir.subst_term. Apply an instantiation to a theorem. *)
fun subst_thm_thy thy (tyinsts, insts) th =
    let
      fun process_tyenv (v, (S, T)) =
          ((v, S), tycert_thy thy T)
      val tys = map process_tyenv (Vartab.dest tyinsts)
      fun process_tenv (v, (T, u)) =
          ((v, Envir.subst_type tyinsts T), cert_thy thy u)
      val ts = map process_tenv (Vartab.dest insts)
    in
      th |> rename_abs_thm (tyinsts, insts)
         |> Drule.instantiate_normalize (tys, ts)
    end
fun subst_thm ctxt (tyinsts, insts) th =
    subst_thm_thy (Proof_Context.theory_of ctxt) (tyinsts, insts) th

(* Substitution into terms used in AUTO2. Substitute types first and
   instantiate the types in the table of term instantiations. Also
   perform beta_norm at the end.
 *)
fun subst_term_norm (tyinsts, insts) t =
    let
      fun inst_tenv tenv =
          tenv |> Vartab.dest
               |> map (fn (ixn, (T, v)) =>
                          (ixn, (Envir.subst_type tyinsts T, v)))
               |> Vartab.make
    in
      t |> rename_abs (tyinsts, insts)
        |> Envir.subst_term_types tyinsts
        |> Envir.subst_term (tyinsts, inst_tenv insts)
        |> Envir.beta_norm
    end

(* Apply the conversion cv to the statement of th, yielding the
   equivalent theorem.
 *)
fun apply_to_thm cv th =
    let val eq = cv (Thm.cprop_of th)
    in if Thm.is_reflexive eq then th else Thm.equal_elim eq th end

(* Apply cv to the statement of th, skipping Trueprop. *)
fun apply_to_thm' cv th = apply_to_thm (HOLogic.Trueprop_conv cv) th

(* Given th of form A = B, get th' of form A == B. *)
val to_meta_eq = apply_to_thm (Conv.rewr_conv @{thm to_meta_eq})
(* Given th of form A == B, get th' of form A = B. *)
val to_obj_eq = apply_to_thm (Conv.rewr_conv @{thm to_obj_eq})
(* Given th of form A = B, get th' of form B = A. *)
val obj_sym = apply_to_thm (Conv.rewr_conv @{thm obj_sym})
(* Given th of form A == B, get th' of form B == A. *)
val meta_sym = apply_to_thm (Conv.rewr_conv @{thm meta_sym})

(* Obtain rewriting conv from obj equality. *)
fun rewr_obj_eq eq_th = Conv.rewr_conv (to_meta_eq eq_th)

(* Rewrite on subterms, top order. *)
fun rewr_obj_eq_top eq_th =
    Conv.top_conv (K (Conv.try_conv (rewr_obj_eq eq_th)))

(* Apply conv to rewrite the left hand side of th. *)
fun apply_to_lhs cv th =
    let val eq = cv (Thm.lhs_of th)
    in if Thm.is_reflexive eq then th else Thm.transitive (meta_sym eq) th end

(* Apply conv to rewrite the right hand side of th. *)
fun apply_to_rhs cv th =
    let val eq = cv (Thm.rhs_of th)
    in if Thm.is_reflexive eq then th else Thm.transitive th eq end

(* Using cv, rewrite the part of ct after stripping i premises. *)
fun concl_conv i cv ct =
    if i = 0 then cv ct
    else (Conv.arg_conv (concl_conv (i-1) cv)) ct

(* Given an equality A == B, make the equality ~A == ~B. Cancel ~~ on
   both sides if exists.
 *)
fun make_neg_eq th =
    th |> Thm.combination (Thm.reflexive (cert @{context} HOLogic.Not))
       |> apply_to_lhs (Conv.try_conv (rewr_obj_eq nn_cancel_th))
       |> apply_to_rhs (Conv.try_conv (rewr_obj_eq nn_cancel_th))

(* If ct is of the form [...] ==> False, leave it unchanged.
   Otherwise, change [...] ==> B to [..., ~ B] ==> False and change
   [...] ==> ~ B to [..., B] ==> False.
 *)
fun rewrite_to_contra_form ct =
    let
      val (prems, concl) = Logic.strip_horn (Thm.term_of ct)
      val num_prems = length prems
      val concl' = HOLogic.dest_Trueprop concl
    in
      if concl' aconv @{term "False"} then
        Conv.all_conv ct
      else if is_neg concl' then
        concl_conv num_prems (Conv.rewr_conv @{thm to_contra_form'}) ct
      else
        concl_conv num_prems (Conv.rewr_conv @{thm to_contra_form}) ct
    end

val rewrite_thm_to_contra_form = apply_to_thm rewrite_to_contra_form

(* Rewrite ct from [...] ==> A ==> False to [...] ==> ~ A and from
   [...] ==> ~ A ==> False to [...] ==> A.
 *)
fun rewrite_from_contra_form ct =
    let
      val (prems, concl) = Logic.strip_horn (Thm.term_of ct)
      val _ = assert (concl aconv @{prop "False"})
                     "rewrite_from_contra_form: concl should be false."
      val num_prems = length prems
      val last_prem' = HOLogic.dest_Trueprop (nth prems (num_prems-1))
      val to_contra_form_th = if is_neg last_prem' then @{thm to_contra_form}
                              else @{thm to_contra_form'}
    in
      concl_conv (num_prems-1) (Conv.rewr_conv (meta_sym to_contra_form_th)) ct
    end

val rewrite_thm_from_contra_form = apply_to_thm rewrite_from_contra_form

fun send_to_hyps ct th =
    Thm.implies_elim th (Thm.assume ct)
fun send_all_to_hyps th =
    let
      val thy = Thm.theory_of_thm th
      val _ = assert (forall (not o has_vars) (Thm.prems_of th))
                     "send_all_to_hyps: schematic variables in hyps."
      val cprems = map (cert_thy thy) (Thm.prems_of th)
    in
      fold send_to_hyps cprems th
    end
fun send_concrete_to_hyps th =
    case Thm.prems_of th of
        [] => th
      | prem :: _ => if has_vars prem then th
                     else th |> send_to_hyps (Thm.cprem_of th 1)
                             |> send_concrete_to_hyps

(* Given a list of theorems A = B, B = C, etc., apply
   Thm.transitive to get equality between start and end.
 *)
fun transitive_list ths =
    let
      fun rev_transitive btoc atob =
          let
            val (b, c) = btoc |> Thm.cprop_of |> Thm.dest_equals
            val (a, b') = atob |> Thm.cprop_of |> Thm.dest_equals
          in
            if b aconvc b' then
              if a aconvc b then btoc
              else if b aconvc c then atob
              else Thm.transitive atob btoc
            else
              raise AUTO2CT ("transitive_list: intermediate does not agree",
                             map Thm.cprop_of ths)
          end
    in
      fold rev_transitive (tl ths) (hd ths)
    end

(* Skip to argument n times. For example, if applied to rewrite a
   proposition in implication form (==> or -->), it will skip the
   first n assumptions.
 *)
fun skip_n_conv n cv =
    if n <= 0 then cv else Conv.arg_conv (skip_n_conv (n-1) cv)

(* Converts ==> to --> and !! to !. *)
fun to_obj_conv ctxt ct =
    (case Thm.term_of ct of
         @{const Pure.imp} $ _ $ _ =>
         Conv.binop_conv (to_obj_conv ctxt) then_conv
                         Conv.rewr_conv @{thm atomize_imp}
       | Const (@{const_name Pure.all}, _) $ Abs _ =>
         Conv.binder_conv (to_obj_conv o snd) ctxt then_conv
                          Conv.rewr_conv @{thm atomize_all}
       | _ => Conv.all_conv) ct

(* When ct is of form A1 ==> ... ==> An, apply to_obj_conv to each Ai. *)
fun to_obj_conv_on_horn ctxt ct =
    (case Thm.term_of ct of
        @{const Pure.imp} $ _ $ _ =>
        Conv.combination_conv (Conv.arg_conv (to_obj_conv ctxt))
                              (to_obj_conv_on_horn ctxt)
      | _ => Conv.all_conv) ct

fun to_obj_conv_on_horn_th th =
    let val ctxt = Proof_Context.init_global (Thm.theory_of_thm th) in
      apply_to_thm (to_obj_conv_on_horn ctxt) th
    end

(* Converts A1 --> ... --> An to A1 ==> ... ==> An. *)
fun to_meta_imp_conv ct =
    (case Thm.term_of ct of
         @{const HOL.Trueprop} $ (@{const HOL.implies} $ _ $ _) =>
         Conv.rewr_conv (meta_sym @{thm atomize_imp}) then_conv
                        Conv.arg_conv to_meta_imp_conv
       | _ => Conv.all_conv) ct

(* Convert the first n object implies to meta implies. *)
fun to_meta_imp_conv_n n ct =
    (case n of
         0 => Conv.all_conv
       | _ => Conv.rewr_conv (meta_sym @{thm atomize_imp}) then_conv
                             Conv.arg_conv (to_meta_imp_conv_n (n-1))) ct

(* Converts ! to !! on the outermost level. *)
fun to_meta_all_conv ctxt ct =
    (case Thm.term_of ct of
         @{const HOL.Trueprop} $ (Const (@{const_name HOL.All}, _) $ Abs _) =>
         Conv.rewr_conv (meta_sym @{thm atomize_all}) then_conv
                        Conv.binder_conv (to_meta_all_conv o snd) ctxt
       | _ => Conv.all_conv) ct

(* Modify th using imp_th, and add postfix to name (if available). *)
fun thm_RS_mod imp_th suffix th =
    (th RS imp_th) |> Drule.zero_var_indexes
                   |> update_name_of_thm th suffix

(* From A & B, obtain A. *)
val conj_left_th = thm_RS_mod @{thm conjunct1} "@left"
(* From A & B, obtain B. *)
val conj_right_th = thm_RS_mod @{thm conjunct2} "@right"
(* From (A::bool) = B, obtain A ==> B. *)
val equiv_forward_th = thm_RS_mod @{thm iffD1} "@eqforward"
(* From (A::bool) = B, obtain B ==> A. *)
val equiv_backward_th = thm_RS_mod @{thm iffD2} "@eqbackward"
(* Same as to_obj_eq, except keeping names and indices. *)
val to_obj_eq_th = thm_RS_mod @{thm meta_eq_to_obj_eq} "@obj_eq"
(* Same as obj_sym_th, except keeping names and indices. *)
val obj_sym_th = thm_RS_mod @{thm sym} "@sym"

(* Using cv, rewrite all assumptions and conclusion in ct. *)
fun horn_conv cv ct =
    (case Thm.term_of ct of
         @{const Pure.imp} $ _ $ _ =>
         (Conv.arg1_conv (HOLogic.Trueprop_conv cv))
             then_conv (Conv.arg_conv (horn_conv cv))
       | _ => HOLogic.Trueprop_conv cv) ct

(* Given th of form A1 & ... & An, return theorems A1, ..., An. *)
fun split_conj_th th =
    case prop_of' th of
        Const ("HOL.conj", _) $ _ $ _ =>
        (conj_left_th th) :: (split_conj_th (conj_right_th th))
      | _ => [th]

(* Given th of form ~ (A1 | ... | An), return theorems ~ A1, ... ~ An. *)
fun split_not_disj_th th =
    case prop_of' th of
        Const ("HOL.Not", _) $ (Const ("HOL.disj", _) $ _ $ _) =>
        (th RS @{thm or_intro1}) :: (split_not_disj_th (th RS @{thm or_intro2}))
      | _ => [th]

(* Similar to Logic.strip_horn, except remove Trueprop. *)
fun strip_horn' th = (Logic.strip_horn (Thm.prop_of th))
                         |> apfst (map HOLogic.dest_Trueprop)
                         |> apsnd HOLogic.dest_Trueprop

(* Given th of form P x ==> False, where x is the given free variable,
   obtain new theorem of form (EX x. P x) ==> False. The function is
   written so it can be applied to multiple variables with fold. For
   example, "fold (ex_elim ctxt) [x, y] (P x y ==> False) will give
   (EX y x. P x y) ==> False.
 *)
fun ex_elim ctxt freevar th =
    let
      val th' = th |> Thm.forall_intr (cert ctxt freevar)
      val head_prem = hd (Thm.prems_of @{thm exE'})
      val inst = pattern_match ctxt (head_prem, Thm.prop_of th')
      val exE_inst = subst_thm ctxt inst @{thm exE'}
    in
      Thm.elim_implies th' exE_inst
    end

(* Rewrite ~A to A = False, and A to ~A = False. *)
fun to_eqF_th th =
    let
      val eq_False_th = if is_neg (prop_of' th) then @{thm eq_False}
                        else @{thm eq_False'}
      val eq_False_cv = Conv.arg_conv (rewr_obj_eq (obj_sym eq_False_th))
    in
      apply_to_thm eq_False_cv th
    end

(* Convert ~ x < y to y <= x, and ~ x <= y to y < x. *)
val neg_ineq_cv =
    (Conv.try_conv o Conv.first_conv)
        (map rewr_obj_eq [@{thm Orderings.linorder_not_less},
                          @{thm Orderings.linorder_not_le}])

(* Convert x < y to ~ y <= x, and x <= y to ~ y < x. *)
val neg_ineq_back_cv =
    (Conv.try_conv o Conv.first_conv)
        (map (rewr_obj_eq o obj_sym) [@{thm Orderings.linorder_not_less},
                                      @{thm Orderings.linorder_not_le}])

(* Helper function for normalize_exs_conv. Attempt to rewrite ct into
   the form Ex x. P x. This includes:

   - Ex x : S. P x to Ex x. x : S & P x.

   - A & Ex x. P x to Ex x. A & P x.
 *)
fun normalize_ex_conv ct =
    case Thm.term_of ct of
        Const ("HOL.Ex", _) $ Abs _ => Conv.all_conv ct
      | Const ("Set.Bex", _) $ _ $ Abs _ => rewr_obj_eq @{thm Bex_def'} ct
      | Const ("Set.Bex", _) $ _ $ _ => rewr_obj_eq @{thm Bex_def} ct
      | Const ("HOL.conj", _) $ _ $ _ =>
        ((Conv.arg_conv normalize_ex_conv)
             then_conv (rewr_obj_eq @{thm swap_ex_conj})) ct
      | _ => Conv.no_conv ct

(* Move existence quantifiers to the left of ct. If the integer
   argument n is at least 0, move exactly n existence quantifiers to
   the left (throwing an error if it is not possible). Otherwise, move
   as many existence quantifiers to the left as possible.
 *)
fun normalize_exs_conv n ctxt ct =
    if n = 0 then
      Conv.all_conv ct
    else
      (normalize_ex_conv then_conv (
          Conv.binder_conv ((normalize_exs_conv (n-1)) o snd) ctxt)) ct
      handle CTERM _ =>
             if n > 0 then raise AUTO2CT ("normalize_exs_conv", [ct])
             else Conv.all_conv ct

(* Similar to normalize_ex_conv, swapping forall and implies. *)
fun normalize_all_conv ct =
    case Thm.term_of ct of
        Const ("HOL.All", _) $ Abs _ => Conv.all_conv ct
      | Const ("Set.Ball", _) $ _ $ Abs _ => rewr_obj_eq @{thm Ball_def'} ct
      | Const ("Set.Ball", _) $ _ $ _ => rewr_obj_eq @{thm Ball_def} ct
      | Const ("HOL.implies", _) $ _ $ _ =>
        ((Conv.arg_conv normalize_all_conv)
             then_conv (rewr_obj_eq @{thm swap_all_implies})) ct
      | _ => Conv.no_conv ct

(* Similar to normalize_exs_conv. Move forall quantifiers to the front. *)
fun normalize_alls_conv n ctxt ct =
    if n = 0 then
      Conv.all_conv ct
    else
      (normalize_all_conv then_conv (
          Conv.binder_conv ((normalize_alls_conv (n-1)) o snd) ctxt)) ct
      handle CTERM _ =>
             if n > 0 then raise AUTO2CT ("normalize_alls_conv", [ct])
             else Conv.all_conv ct

(* Given P of function type, produce P == %x. P x. *)
fun reverse_eta_conv ctxt ct =
    let
      val t = Thm.term_of ct
      val argT = Term.domain_type (fastype_of t)
                 handle Match => raise CTERM ("reverse_eta_conv", [ct])
      val rhs = Abs ("x", argT, t $ Bound 0)
      val eq_th = Thm.eta_conversion (cert ctxt rhs)
    in
      meta_sym eq_th
    end

(* Repeat cv exactly n times. *)
fun repeat_n_conv n cv t =
    if n = 0 then Conv.all_conv t
    else (cv then_conv (repeat_n_conv (n-1) cv)) t

(* Generic wrapper function. tac can be arith_tac, simp_tac, etc. *)
fun prove_by_tac tac ctxt ths goal =
    let
      val goal' = Logic.list_implies (
            map Thm.prop_of ths, HOLogic.mk_Trueprop goal)
    in
      ths MRS (Goal.prove ctxt [] [] goal' (K (tac ctxt 1)))
    end

fun contra_by_tac tac ctxt ths = prove_by_tac tac ctxt ths @{term "False"}

val prove_by_simp = prove_by_tac Simplifier.asm_full_simp_tac
val contra_by_simp = contra_by_tac Simplifier.asm_full_simp_tac
val prove_by_arith = prove_by_tac Arith_Data.arith_tac
val contra_by_arith = contra_by_tac Arith_Data.arith_tac

(* Generic function for testing a conv. *)
fun test_conv ctxt cv err_str (str1, str2) =
    let
      val (t1, t2) = (read_pat ctxt str1, read_pat ctxt str2)
      val th = cv (cert ctxt t1)
    in
      if t1 aconv (lhs_of th) andalso t2 aconv (rhs_of th) then ()
      else let
        val _ = trace_t_ctxt ctxt "Input:" t1
        val _ = trace_t_ctxt ctxt "Expected:" t2
        val _ = trace_t_ctxt ctxt "Actual:" (Thm.prop_of th)
      in
        raise AUTO2 err_str
      end
    end

(* term_pat and typ_pat, from Isabelle Cookbook. *)
val term_pat_setup =
    let
      val parser = Args.context -- Scan.lift Args.name_inner_syntax
      fun term_pat (ctxt, str) =
          str |> Proof_Context.read_term_pattern ctxt
              |> ML_Syntax.print_term
              |> ML_Syntax.atomic
    in
      ML_Antiquotation.inline @{binding "term_pat"} (parser >> term_pat)
    end

val cterm_pat_setup =
    let
      val parser = Args.context -- Scan.lift Args.name_inner_syntax
      fun cterm_pat (ctxt, str) =
          str |> Proof_Context.read_term_pattern ctxt
              |> ML_Syntax.print_term
              |> ML_Syntax.atomic
              |> prefix "Thm.cterm_of ML_context"
    in
      ML_Antiquotation.value @{binding "cterm_pat"} (parser >> cterm_pat)
    end

val type_pat_setup =
    let
      val parser = Args.context -- Scan.lift Args.name_inner_syntax
      fun typ_pat (ctxt, str) =
          let
            val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
          in
            str |> Syntax.read_typ ctxt'
                |> ML_Syntax.print_typ
                |> ML_Syntax.atomic
          end
    in
      ML_Antiquotation.inline @{binding "typ_pat"} (parser >> typ_pat)
    end

(* Time the given function f : unit -> 'a. *)
fun timer (msg, f) =
    let
      val t_start = Timing.start ()
      val res = f ()
      val t_end = Timing.result t_start
    in
      (writeln (msg ^ (Timing.message t_end)); res)
    end

(* When exception is shown when running function f : unit -> 'a, print
   stack trace.
 *)
fun exn_trace f = Runtime.exn_trace f

end  (* structure Util. *)

open Util

val _ = Theory.setup (term_pat_setup)
val _ = Theory.setup (cterm_pat_setup)
val _ = Theory.setup (type_pat_setup)
