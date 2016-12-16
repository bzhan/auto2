(* Utility functions. *)

infix andf2 orf2 check_MRS

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
  val get_arg_type: term -> typ

  (* Lists *)
  val max: ('a * 'a -> order) -> 'a list -> 'a
  val max_partial: ('a -> 'a -> bool) -> 'a list -> 'a list
  val is_sorted: ('a * 'a -> order) -> 'a list -> bool
  val subsets: 'a list -> 'a list list
  val nth_drop_list: int list -> 'a list -> 'a list
  val the_pair: 'a list -> 'a * 'a
  val the_triple: 'a list -> 'a * 'a * 'a
  val the_quadruple: 'a list -> 'a * 'a * 'a * 'a
  val list_pair: 'a * 'a -> 'a list
  val filter_split: ('a -> bool) -> 'a list -> 'a list * 'a list
  val filter_first_split: ('a -> bool) -> 'a list -> 'a list * 'a list
  val all_pairs: 'a list * 'b list -> ('a * 'b) list
  val all_distinct_pairs: 'a list -> ('a * 'a) list

  (* Strings. *)
  val is_prefix_str: string -> string -> bool
  val is_just_internal: string -> bool
  val split_commas: string -> string list

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
  val typ_match: theory -> typ * typ -> Type.tyenv
  val pattern_fo_match_list_thy:
      theory -> (term * term) list -> Type.tyenv * Envir.tenv ->
      Type.tyenv * Envir.tenv
  val pattern_fo_match_list:
      Proof.context -> (term * term) list -> Type.tyenv * Envir.tenv ->
      Type.tyenv * Envir.tenv

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
  val check_MRS: thm list * thm -> thm

  (* Generic context. *)
  val theory_of_gnrc: Context.generic -> theory
  val context_of_gnrc: Context.generic -> Proof.context

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
  val is_abs: term -> bool
  val is_implies: term -> bool
  val dest_binop: term -> term * (term * term)
  val dest_arg: term -> term
  val dest_arg1: term -> term
  val dest_args: term -> term list
  val dest_argn: int -> term -> term
  val is_meta_eq_term: term -> bool
  val is_meta_eq_thm: thm -> bool
  val occurs_frees: term list -> term -> bool
  val occurs_free: term -> term -> bool
  val has_vars: term -> bool
  val is_subterm: term -> term -> bool
  val has_subterm: term list -> term -> bool
  val lambda_abstract: term -> term -> term
  val is_pattern_list: term list -> bool
  val is_pattern: term -> bool
  val strip_pure_goal: Proof.context -> term -> (bool * term) list * term
  val print_term_detail: Proof.context -> term -> string

  (* Theorems. *)
  val apply_on: thm list -> thm -> thm
  val arg_backn_conv: int -> conv -> conv
  val argn_conv: int -> conv -> conv
  val comb_equiv: cterm * thm list -> thm
  val name_of_thm: thm -> string
  val update_name_of_thm: thm -> string -> thm -> thm
  val lhs_of: thm -> term
  val rhs_of: thm -> term
  val assume_meta_eq: theory -> term * term -> thm
  val assume_thm: Proof.context -> term -> thm
  val rename_abs: Type.tyenv * Envir.tenv -> term -> term
  val rename_abs_thm: Type.tyenv * Envir.tenv -> thm -> thm
  val subst_thm_thy: theory -> Type.tyenv * Envir.tenv -> thm -> thm
  val subst_thm: Proof.context -> Type.tyenv * Envir.tenv -> thm -> thm
  val subst_thm_atomic: (cterm * cterm) list -> thm -> thm
  val subst_term_norm: Type.tyenv * Envir.tenv -> term -> term
  val apply_to_thm: conv -> thm -> thm
  val meta_sym: thm -> thm
  val apply_to_lhs: conv -> thm -> thm
  val apply_to_rhs: conv -> thm -> thm
  val concl_conv_n: int -> conv -> conv
  val concl_conv: conv -> conv
  val send_to_hyps: cterm -> thm -> thm
  val send_all_to_hyps: thm -> thm
  val transitive_list: thm list -> thm
  val skip_n_conv: int -> conv -> conv

  (* Conversions *)
  val reverse_eta_conv: Proof.context -> conv
  val repeat_n_conv: int -> conv -> conv

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

(* Convert list to quadruple. *)
fun the_quadruple lst =
    case lst of [i1, i2, i3, i4] => (i1, i2, i3, i4)
              | _ => raise AUTO2 "the_triple: list is not of length 4."

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

(* Test whether nm is followed by exactly one _. *)
fun is_just_internal nm =
    Name.is_internal nm andalso not (Name.is_skolem nm)

(* Split a string by commas. Do not split on commas that are inside
   any kind of brackets.
 *)
val left_brackets = ["(", "[", "{", "\<langle>"]
val right_brackets = [")", "]", "}", "\<rangle>"]

fun count_brackets str =
    if member (op =) left_brackets str then 1
    else if member (op =) right_brackets str then ~1
    else 0

fun split_commas str =
    let
      val syms = Symbol.explode str
      fun can_split_id i =
          nth syms i = "," andalso
          Integer.sum (map count_brackets (take i syms)) = 0
    in
      case find_first can_split_id (0 upto (length syms - 1)) of
          NONE => [str]
        | SOME n =>
          String.concat (take n syms) ::
          split_commas (String.concat (drop (n+1) syms))
    end

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
fun typ_match thy (T, U) = Sign.typ_match thy (T, U) Vartab.empty
fun pattern_fo_match_list_thy thy pairs inst =
    case pairs of
        [] => inst
      | (t, u) :: rest =>
        let
          val inst' = Pattern.first_order_match thy (t, u) inst
        in
          pattern_fo_match_list_thy thy rest inst'
        end
fun pattern_fo_match_list ctxt pairs inst =
    pattern_fo_match_list_thy (Proof_Context.theory_of ctxt) pairs inst

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

(* Debugging version of MRS. *)
fun ths check_MRS th =
    ths MRS th
    handle THM _ => let
      val _ = trace_thm "Applying" th
      val _ = map (trace_thm "input") ths
    in
      raise AUTO2 "check_MRS"
    end

val theory_of_gnrc = Context.cases I Proof_Context.theory_of
val context_of_gnrc = Context.cases Proof_Context.init_global I

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
fun is_abs t = case t of Abs _ => true | _ => false

(* Whether a given term is of the form A ==> B. *)
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

(* Return the argument of t. If t is f applied to multiple arguments,
   return the last argument.
 *)
fun dest_arg t =
    case t of _ $ arg => arg | _ => raise AUTO2 "dest_arg"

(* Return the first of two arguments of t. *)
fun dest_arg1 t =
    case t of _ $ arg1 $ _ => arg1 | _ => raise AUTO2 "dest_arg1"

(* Return the list of all arguments of t. *)
fun dest_args t = t |> Term.strip_comb |> snd

(* Return the nth argument of t, counting from left and starting at zero. *)
fun dest_argn n t = nth (dest_args t) n

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

(* If stmt is P(t), return lambda t. P(t). *)
fun lambda_abstract t stmt = lambda t (Term.abstract_over (t, stmt))

(* A more general criterion for patterns. In combinations, any
   argument that is a pattern (in the more general sense) frees up
   checking for any functional schematic variables in that argument.
 *)
fun is_pattern_list ts =
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
      test_list [] ts
    end

fun is_pattern t = is_pattern_list [t]

(* Given a term t in pure logic form, strip out !! and ==>, and return
   the list of variables, assumptions, and conclusion.

   For example:

   !!a b. P ==> Q gives ([(true, a), (true, b), (false, P)], Q)

   P ==> !!a b. Q gives ([(false, P), (true, a), (true, b)], Q)
 *)
fun strip_pure_goal_aux ctxt prevs t =
    case t of
        Const ("Pure.all", _) $ Abs (abs as (_, T, _)) =>
        let
          val (nm, body) = Term.dest_abs abs
          val (nm', _) = singleton (Variable.variant_frees ctxt prevs) (nm, T)
          val bd_var = Free (nm', T)
          val body' = if nm = nm' then body
                      else Term.subst_atomic [(Free (nm, T), bd_var)] body
          val (assums, concl) = strip_pure_goal_aux ctxt (bd_var :: prevs) body'
        in
          ((true, bd_var) :: assums, concl)
        end
      | Const ("Pure.imp", _) $ P $ Q =>
        let
          val (assums, concl) = strip_pure_goal_aux ctxt prevs Q
        in
          ((false, P) :: assums, concl)
        end
      | _ => ([], t)

fun strip_pure_goal ctxt t = strip_pure_goal_aux ctxt [] t

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

fun apply_on ths th = ths MRS th

(* Apply cv to nth argument of t, counting from right and starting at 0. *)
fun arg_backn_conv n cv ct =
    if n = 0 then Conv.arg_conv cv ct
    else Conv.fun_conv (arg_backn_conv (n-1) cv) ct

(* Apply cv to nth argument of t, counting from left and starting at 0. *)
fun argn_conv n cv ct =
    let
      val args_count = ct |> Thm.term_of |> dest_args |> length
      val _ = assert (n >= 0 andalso n < args_count)
    in
      arg_backn_conv (args_count - n - 1) cv ct
    end

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

val lhs_of = Thm.term_of o Thm.lhs_of
val rhs_of = Thm.term_of o Thm.rhs_of

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

(* Replace using subst the internal variables in th. This proceeds in
   several steps: first, pull any hypotheses of the theorem involving
   the replaced variables into statement of the theorem, perform the
   replacement (using forall_intr then forall_elim), finally return
   the hypotheses to their original place.
 *)
fun subst_thm_atomic subst th =
    let
      val old_cts = map fst subst
      val old_ts = map Thm.term_of old_cts
      val new_cts = map snd subst
      val chyps = filter (fn ct => has_subterm old_ts (Thm.term_of ct))
                         (Thm.chyps_of th)
    in
      th |> fold Thm.implies_intr chyps
         |> fold Thm.forall_intr old_cts
         |> fold Thm.forall_elim (rev new_cts)
    end

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

(* Given th of form A == B, get th' of form B == A. *)
val meta_sym = Thm.symmetric

(* Apply conv to rewrite the left hand side of th. *)
fun apply_to_lhs cv th =
    let val eq = cv (Thm.lhs_of th)
    in if Thm.is_reflexive eq then th else Thm.transitive (meta_sym eq) th end

(* Apply conv to rewrite the right hand side of th. *)
fun apply_to_rhs cv th =
    let val eq = cv (Thm.rhs_of th)
    in if Thm.is_reflexive eq then th else Thm.transitive th eq end

(* Using cv, rewrite the part of ct after stripping i premises. *)
fun concl_conv_n i cv ct =
    if i = 0 then cv ct
    else (Conv.arg_conv (concl_conv_n (i-1) cv)) ct

(* Rewrite part of ct after stripping all premises. *)
fun concl_conv cv ct =
    case Thm.term_of ct of
        Const ("Pure.imp", _) $ _ $ _ => Conv.arg_conv (concl_conv cv) ct
      | _ => cv ct

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
      val parser = Args.context -- Scan.lift Args.embedded_inner_syntax
      fun term_pat (ctxt, str) =
          str |> Proof_Context.read_term_pattern ctxt
              |> ML_Syntax.print_term
              |> ML_Syntax.atomic
    in
      ML_Antiquotation.inline @{binding "term_pat"} (parser >> term_pat)
    end

val cterm_pat_setup =
    let
      val parser = Args.context -- Scan.lift Args.embedded_inner_syntax
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
      val parser = Args.context -- Scan.lift Args.embedded_inner_syntax
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
