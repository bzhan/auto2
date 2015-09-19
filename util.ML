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
  val natT: typ
  val boolT: typ

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

  (* Strings. *)
  val is_prefix_str: string -> string -> bool

  (* Managing matching environments. *)
  val fo_init: Type.tyenv * Envir.tenv
  val lookup_instn: Type.tyenv * Envir.tenv -> string * int -> term
  val lookup_inst: Type.tyenv * Envir.tenv -> string -> term
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

  (* Terms. *)
  val prop_False: term
  val is_Trueprop: term -> bool
  val is_neg: term -> bool
  val get_neg: term -> term
  val get_neg': term -> term
  val is_implies: term -> bool
  val get_head: term -> term
  val dest_binop: term -> term * (term * term)
  val is_numc: term -> bool
  val dest_numc: term -> int
  val is_eq_term: term -> bool
  val is_eq_term': term -> bool
  val all_frees: term list -> (string * typ) list
  val occurs_frees: term list -> term -> bool
  val occurs_free: term -> term -> bool
  val has_vars: term -> bool
  val is_subterm: term -> term -> bool
  val has_subterm: term list -> term -> bool
  val dest_obj_all_var: term -> term * term
  val strip_obj_all_var: term -> term list * term
  val strip_obj_imp: term -> term list * term
  val lambda_abstract: term -> term -> term
  val is_const: term -> bool
  val is_nat_order: term -> bool
  val is_nat_order': term -> bool

  (* Theorems. *)
  val true_th: thm
  val prop_of': thm -> term
  val comb_equiv: cterm * thm list -> thm
  val name_of_thm: thm -> string
  val dest_eq_thm: thm -> term * term
  val lhs_of: thm -> term
  val rhs_of: thm -> term
  val make_trueprop_eq: thm -> thm
  val elim_eq_thm: thm * thm -> thm
  val assume_eq: theory -> term * term -> thm
  val assume_meta_eq: theory -> term * term -> thm
  val assume_thm: Proof.context -> term -> thm
  val subst_thm_thy: theory -> Type.tyenv * Envir.tenv -> thm -> thm
  val subst_thm: Proof.context -> Type.tyenv * Envir.tenv -> thm -> thm
  val subst_term_norm: Type.tyenv * Envir.tenv -> term -> term
  val apply_to_thm: conv -> thm -> thm
  val to_meta_eq: thm -> thm
  val to_obj_eq: thm -> thm
  val obj_sym: thm -> thm
  val meta_sym: thm -> thm
  val rewr_obj_eq: thm -> conv
  val apply_to_rhs: conv -> thm -> thm
  val concl_conv: int -> conv -> conv
  val rewrite_to_contra_form: conv
  val rewrite_thm_to_contra_form: thm -> thm
  val rewrite_from_contra_form: conv
  val rewrite_thm_from_contra_form: thm -> thm
  val send_to_hyps: cterm -> thm -> thm
  val send_all_to_hyps: thm -> thm
  val send_concrete_to_hyps: thm -> thm
  val transitive_list: thm list -> thm
  val to_obj_conv: Proof.context -> conv
  val to_obj_conv_skip_n: Proof.context -> int -> conv
  val to_obj_conv_on_horn: Proof.context -> conv
  val to_meta_imp_conv: conv
  val to_meta_imp_conv_n: int -> conv
  val to_meta_all_conv: Proof.context -> conv
  val conj_left_th: thm -> thm
  val conj_right_th: thm -> thm
  val equiv_forward_th: thm -> thm
  val equiv_backward_th: thm -> thm
  val to_obj_eq_th: thm -> thm
  val obj_sym_th: thm -> thm
  val backward_th: thm -> thm
  val backward1_th: thm -> thm
  val backward2_th: thm -> thm
  val to_contra_th: thm -> thm
  val split_conj_th: thm -> thm list
  val split_not_disj_th: thm -> thm list
  val strip_horn': thm -> term list * term
  val ex_elim: Proof.context -> term -> thm -> thm
  val to_eqF_th: thm -> thm

  (* Miscellaneous. *)
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

val natT = HOLogic.natT
val boolT = HOLogic.boolT

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

(* Split list into pairs (ins, outs), where ins satisfy f, and outs don't. *)
fun filter_split _ [] = ([], [])
  | filter_split f (x :: xs) =
    let
      val (ins, outs) = filter_split f xs
    in
      if f x then (x :: ins, outs) else (ins, x :: outs)
    end

(* Whether pre is a prefix of str. *)
fun is_prefix_str pre str =
    is_prefix (op =) (String.explode pre) (String.explode str)

val fo_init = (Vartab.empty, Vartab.empty)

(* Lookup a Vartab inst with string and integer specifying indexname. *)
fun lookup_instn (_, inst) (str, n) =
    case Vartab.lookup inst (str, n) of
        NONE => raise AUTO2 ("lookup_inst: not found " ^ str ^
                             (if n = 0 then "" else string_of_int n))
      | SOME (_, u) => u
fun lookup_inst (tyinst, inst) str = lookup_instn (tyinst, inst) (str, 0)

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

val prop_False = @{prop False}

(* Returns whether the given term is Trueprop. *)
fun is_Trueprop t =
    let val _ = assert (fastype_of t = @{typ prop}) "is_Trueprop: wrong type"
    in case t of Const (@{const_name Trueprop}, _) $ _ => true
               | _ => false
    end

(* Returns whether the given term is in neg form. *)
fun is_neg t =
    let val _ = assert (fastype_of t = @{typ bool}) "is_neg: wrong type"
    in case t of Const ("HOL.Not", _) $ _ => true
               | _ => false
    end

(* Returns the negation of the given term. Avoids double negatives. *)
fun get_neg t =
    let val _ = assert (fastype_of t = @{typ bool}) "get_neg: wrong type"
    in case t of Const ("HOL.Not", _) $ t => t
               | _ => HOLogic.Not $ t
    end

(* Version of get_neg for Trueprop terms. *)
fun get_neg' t =
    let val _ = assert (is_Trueprop t) "get_neg': input should be a Trueprop."
    in t |> HOLogic.dest_Trueprop |> get_neg |> HOLogic.mk_Trueprop end

(* Whether a given term is ==>. *)
fun is_implies t =
    let val _ = assert (fastype_of t = @{typ prop}) "is_implies: wrong type"
    in case t of Const ("Pure.imp", _) $ _ $ _ => true
               | _ => false
    end

fun get_head t = let val (fhead, _) = strip_comb t in fhead end
fun dest_binop t = t |> strip_comb ||> the_pair
                   handle AUTO2 _ => raise AUTO2 "dest_binop: invalid input"

(* Test if a term represents a numerical constant. *)
fun is_numc t =
    let val _ = HOLogic.dest_number t in true end
    handle TERM ("dest_number", _) => false

(* Deconstruct numerical constant. Discard type. *)
fun dest_numc t = HOLogic.dest_number t |> snd

(* Test if a given fact is an equality. *)
fun is_eq_term t =
    let val _ = assert (fastype_of t = @{typ bool}) "is_eq_term: wrong type"
    in case t of Const ("HOL.eq", _) $ _ $ _ => true
               | _ => false
    end

(* Version of is_eq_term' for Trueprop terms. *)
fun is_eq_term' t =
    let val _ = assert (fastype_of t = @{typ prop}) "is_eq_term': wrong type"
    in is_Trueprop t andalso is_eq_term (HOLogic.dest_Trueprop t) end

(* Find all free variables in a list of terms. *)
fun all_frees ts = fold Term.add_frees ts []

(* Given a term freevar that is a free variable, determine whether it
   appears in trm.
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

(* Given t of the form !a. P(a), return pair (?a, P(?a_)). *)
fun dest_obj_all_var t =
    case t of
        Const ("HOL.All", _) $ Abs (abs as (_, T, _)) =>
        let
          val (nm, body) = Term.dest_abs abs
          val bd_var = Var ((Name.internal nm, 0), T)
          val bd_free = Free (nm, T)
          val body' = Term.subst_atomic [(bd_free, bd_var)] body
        in
          (bd_var, body')
        end
      | _ => raise AUTO2 "dest_obj_all_var"

(* Given t of the form !a1, ... an. P(a1, ..., an), return pair
   ([?a1_, ... ?an_], P(?a1_, ..., ?an_).
 *)
fun strip_obj_all_var t =
    case t of
        Const ("HOL.All", _) $ Abs _ =>
        let
          val (bd_var, body) = dest_obj_all_var t
          val (rest, body') = strip_obj_all_var body
        in
          (bd_var :: rest, body')
        end
      | _ => ([], t)

(* Given t of form A1 --> ... --> An, return ([A1, ..., A(n-1)], An). *)
fun strip_obj_imp t =
    case t of
        Const ("HOL.implies", _) $ A $ B =>
        let val (As, B') = strip_obj_imp B in (A :: As, B') end
      | _ => ([], t)

(* If stmt is P(t), return lambda t. P(t). *)
fun lambda_abstract t stmt = lambda t (Term.abstract_over (t, stmt))

(* Whether the given term is entirely constant. *)
fun is_const t = (length (Term.add_vars t []) = 0 andalso
                  length (Term.add_frees t []) = 0)

(* Whether the given term is < or <= on natural numbers. *)
fun is_nat_order t =
    let
      val _ = assert (fastype_of t = @{typ bool}) "is_nat_order: wrong type"
    in
      case t of Const (@{const_name less}, _) $ A $ _ =>
                (Term.fastype_of A = natT)
              | Const (@{const_name less_eq}, _) $ A $ _ =>
                (Term.fastype_of A = natT)
              | _ => false
    end

fun is_nat_order' t =
    let
      val _ = assert (fastype_of t = @{typ prop}) "is_nat_order': wrong type"
    in
      is_Trueprop t andalso is_nat_order (HOLogic.dest_Trueprop t)
    end

val true_th = @{thm TrueI}

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

fun dest_eq_thm th = th |> prop_of' |> HOLogic.dest_eq

val lhs_of = Thm.term_of o Thm.lhs_of
val rhs_of = Thm.term_of o Thm.rhs_of

(* Given an equality between bools, make it an equality between props,
   by applying the function Trueprop to both sides.
 *)
fun make_trueprop_eq th =
    Thm.combination (Thm.reflexive (cert @{context} HOLogic.Trueprop)) th

(* Given an equality (A:bool) == B and a theorem A, return theorem B. *)
fun elim_eq_thm (eq_th, th) = Thm.equal_elim eq_th th

(* Assumed theorems. *)
fun assume_eq thy (t1, t2) =
    Thm.assume (cert_thy thy (HOLogic.mk_Trueprop (HOLogic.mk_eq (t1, t2))))
fun assume_meta_eq thy (t1, t2) =
    Thm.assume (cert_thy thy (Logic.mk_equals (t1, t2)))
fun assume_thm ctxt t =
    if type_of t <> @{typ prop} then
      raise AUTO2CT ("assume_thm: t is not of type prop", [cert ctxt t])
    else Thm.assume (cert ctxt t)

(* Similar to Envir.subst_term. Apply an instantiation to a theorem. *)
fun subst_thm_thy thy (tyinsts, insts) th =
    let
      fun process_tyenv (v, (S, T)) =
          (tycert_thy thy (TVar (v, S)), tycert_thy thy T)
      val tys = map process_tyenv (Vartab.dest tyinsts)
      fun process_tenv (v, (T, u)) =
          (cert_thy thy (Var (v, Envir.subst_type tyinsts T)), cert_thy thy u)
      val ts = map process_tenv (Vartab.dest insts)
    in
      Drule.instantiate_normalize (tys, ts) th
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
      t |> Envir.subst_term_types tyinsts
        |> Envir.subst_term (tyinsts, inst_tenv insts)
        |> Envir.beta_norm
    end

(* Apply the conversion cv to the statement of th, yielding the
   equivalent theorem.
 *)
fun apply_to_thm cv th =
    let val eq = cv (Thm.cprop_of th)
    in if Thm.is_reflexive eq then th else Thm.equal_elim eq th end

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

(* Apply conv to rewrite the right hand side of th. *)
fun apply_to_rhs cv th =
    let val eq = cv (Thm.rhs_of th)
    in if Thm.is_reflexive eq then th else Thm.transitive th eq end

(* Using cv, rewrite the part of ct after stripping i premises. *)
fun concl_conv i cv ct =
    if i = 0 then cv ct
    else (Conv.arg_conv (concl_conv (i-1) cv)) ct

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

(* Skip the first n meta imps. *)
fun to_obj_conv_skip_n ctxt n ct =
    if n = 0 then to_obj_conv ctxt ct
    else Conv.arg_conv (to_obj_conv_skip_n ctxt (n-1)) ct

(* When ct is of form A1 ==> ... ==> An, apply to_obj_conv to each Ai. *)
fun to_obj_conv_on_horn ctxt ct =
    (case Thm.term_of ct of
        @{const Pure.imp} $ _ $ _ =>
        Conv.combination_conv (Conv.arg_conv (to_obj_conv ctxt))
                              (to_obj_conv_on_horn ctxt)
      | _ => Conv.all_conv) ct

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
fun thm_RS_mod imp_th postfix th =
    (th RS imp_th) |> Drule.zero_var_indexes
                   |> Thm.has_name_hint th ?
                   Thm.put_name_hint (Thm.get_name_hint th ^ postfix)

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
         Conv.combination_conv (Conv.arg_conv cv) (horn_conv cv)
       | _ => Conv.all_conv) ct

(* Rewrite th using eq_th, rewrite double negs and add postfix to name. *)
fun thm_rewr_mod eq_th postfix th =
    th |> apply_to_thm (Conv.rewr_conv eq_th)
       |> apply_to_thm (horn_conv (Conv.try_conv (rewr_obj_eq nn_cancel_th)))
       |> Thm.has_name_hint th ?
       Thm.put_name_hint (Thm.get_name_hint th ^ postfix)

(* From A ==> B obtain ~B ==> ~A. *)
val backward_th = thm_rewr_mod @{thm backward_conv} "@back"
(* From A ==> B ==> C obtain ~C ==> B ==> ~A. *)
val backward1_th = thm_rewr_mod @{thm backward1_conv} "@back1"
(* From A ==> B ==> C obtain ~C ==> A ==> ~B. *)
val backward2_th = thm_rewr_mod @{thm backward2_conv} "@back2"
(* Rewrite to contradiction form. *)
fun to_contra_th th = th |> rewrite_thm_to_contra_form
                         |> Thm.has_name_hint th ?
                         Thm.put_name_hint (Thm.get_name_hint th ^ "@res")

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
