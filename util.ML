(* Utility functions. *)

infix andf2

signature UTIL =
sig
  (* Exceptions *)
  exception AUTO2 of string
  exception AUTO2T of string * term list
  exception AUTO2CT of string * cterm list
  val assert: bool -> string -> unit

  (* Booleans *)
  val andf2: ('a -> 'b -> bool) * ('a -> 'b -> bool) -> 'a -> 'b -> bool

  (* Lists *)
  val max: ('a * 'a -> order) -> 'a list -> 'a
  val max_partial: ('a -> 'a -> bool) -> 'a list -> 'a list
  val is_sorted: ('a * 'a -> order) -> 'a list -> bool
  val subsets: 'a list -> 'a list list
  val nth_drop_list: int list -> 'a list -> 'a list
  val the_pair: 'a list -> 'a * 'a
  val apply2: ('a -> 'b) -> 'a * 'a -> 'b * 'b

  (* Managing matching environments. *)
  val fo_init: Type.tyenv * Envir.tenv
  val lookup_instn: Type.tyenv * Envir.tenv -> string * int -> term
  val lookup_inst: Type.tyenv * Envir.tenv -> string -> term

  (* Wrapper around matching functions in pattern. *)
  val pattern_fo_match: Proof.context -> term * term -> Type.tyenv * Envir.tenv
  val pattern_match: Proof.context -> term * term -> Type.tyenv * Envir.tenv
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
  val trace_tlist: string -> term list -> unit
  val trace_thm: string -> thm -> unit
  val trace_fullthm_ctxt: Proof.context -> string -> thm -> unit
  val trace_t: string -> term -> unit
  val trace_fullthm: string -> thm -> unit

  (* Certifying terms and types. *)
  val cert: Proof.context -> term -> cterm
  val tycert: Proof.context -> typ -> ctyp
  val cert_thy: theory -> term -> cterm
  val tycert_thy: theory -> typ -> ctyp

  (* Terms. *)
  val is_Trueprop: term -> bool
  val is_neg: term -> bool
  val get_neg: term -> term
  val get_neg': term -> term
  val is_implies: term -> bool
  val get_head: term -> term
  val dest_binop: term -> term * (term * term)
  val is_numc: term -> bool
  val is_eq_term: term -> bool
  val is_eq_term': term -> bool
  val inplace_abstract_over: term -> term
  val all_frees: term list -> (string * typ) list
  val occurs_frees: term list -> term -> bool
  val occurs_free: term -> term -> bool
  val has_vars: term -> bool

  (* Theorems. *)
  val comb_equiv: cterm * thm list -> thm
  val name_of_thm: thm -> string
  val dest_eq_thm: thm -> term * term
  val lhs_of: thm -> term
  val rhs_of: thm -> term
  val make_trueprop_eq: thm -> thm
  val to_meta_eq: thm -> thm
  val to_obj_eq: thm -> thm
  val obj_sym: thm -> thm
  val meta_sym: thm -> thm
  val elim_eq_thm: thm * thm -> thm
  val assume_eq: theory -> term * term -> thm
  val assume_thm: Proof.context -> term -> thm
  val subst_thm_thy: theory -> Type.tyenv * Envir.tenv -> thm -> thm
  val subst_thm: Proof.context -> Type.tyenv * Envir.tenv -> thm -> thm
  val normalize_pred_comm: conv
  val exists_split_conv: conv
  val apply_to_thm: conv -> thm -> thm
  val apply_to_rhs: conv -> thm -> thm
  val concl_conv: int -> conv -> conv
  val rewrite_to_contra_form: conv
  val rewrite_thm_to_contra_form: thm -> thm
  val rewrite_from_contra_form: conv
  val rewrite_thm_from_contra_form: thm -> thm
  val move_to_front_conv: int -> conv
  val rotate_prems_conv: term list -> conv
  val rotate_prems_conv_thm: term list -> thm -> thm
  val send_to_hyps: cterm -> thm -> thm
  val send_all_to_hyps: thm -> thm
  val send_concrete_to_hyps: thm -> thm
  val transitive_list: thm list -> thm
  val to_obj_conv: Proof.context -> conv
  val to_meta_imp_conv: conv
  val to_meta_all_conv: Proof.context -> conv

  (* TERM. *)
  val TermConst: typ -> term
  val is_Term: term -> bool
  val make_term_eq: thm -> thm
  val make_term_th: Proof.context -> term -> thm
  val make_eq_term_triv: Proof.context -> thm * term -> thm

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

val apply2 = pairself

val fo_init = (Vartab.empty, Vartab.empty)

(* Lookup a Vartab inst with string and integer specifying indexname. *)
fun lookup_instn (_, inst) (str, n) =
    case Vartab.lookup inst (str, n) of
        NONE => raise AUTO2 ("lookup_inst: not found " ^ str ^
                             (if n = 0 then "" else string_of_int n))
      | SOME (_, u) => u
fun lookup_inst (tyinst, inst) str = lookup_instn (tyinst, inst) (str, 0)

fun pattern_fo_match ctxt (t, u) =
    Pattern.first_order_match (Proof_Context.theory_of ctxt) (t, u) fo_init
fun pattern_match ctxt (t, u) =
    Pattern.match (Proof_Context.theory_of ctxt) (t, u) fo_init
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
fun trace_tlist s tlist =
    tracing (s ^ " " ^ (tlist |> pretty_terms @{context} |> str))
fun trace_thm s th =
    tracing (s ^ " " ^ (th |> Thm.prop_of |> pretty_term @{context} |> str))
fun trace_fullthm_ctxt ctxt s th =
    tracing (s ^ " [" ^ (Thm.hyps_of th |> pretty_terms ctxt |> str) ^
             "] ==> " ^ (Thm.prop_of th |> pretty_term ctxt |> str))
val trace_t = trace_t_ctxt @{context}
val trace_fullthm = trace_fullthm_ctxt @{context}

fun cert ctxt t = Thm.cterm_of (Proof_Context.theory_of ctxt) t
fun tycert ctxt ty = Thm.ctyp_of (Proof_Context.theory_of ctxt) ty
fun cert_thy thy t = Thm.cterm_of thy t
fun tycert_thy thy ty = Thm.ctyp_of thy ty

(* Returns whether the given term is Trueprop. *)
fun is_Trueprop t =
    let val _ = assert (type_of t = @{typ prop}) "is_Trueprop: wrong type"
    in case t of Const (@{const_name Trueprop}, _) $ _ => true
               | _ => false
    end

(* Returns whether the given term is in neg form. *)
fun is_neg t =
    let val _ = assert (type_of t = @{typ bool}) "is_neg: wrong type"
    in case t of Const("HOL.Not", _) $ _ => true
               | _ => false
    end

(* Returns the negation of the given term. Avoids double negatives. *)
fun get_neg t =
    let val _ = assert (type_of t = @{typ bool}) "get_neg: wrong type"
    in case t of Const("HOL.Not", _) $ t => t
               | _ => HOLogic.Not $ t
    end

(* Version of get_neg for Trueprop terms. *)
fun get_neg' t =
    let val _ = assert (is_Trueprop t) "get_neg': input should be a Trueprop."
    in t |> HOLogic.dest_Trueprop |> get_neg |> HOLogic.mk_Trueprop end

(* Whether a given term is ==>. *)
fun is_implies t =
    let val _ = assert (type_of t = @{typ prop}) "is_implies: wrong type"
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

(* Test if a given fact is an equality. *)
fun is_eq_term t =
    let val _ = assert (type_of t = @{typ bool}) "is_eq_term: wrong type"
    in case t of Const ("HOL.eq", _) $ _ $ _ => true
               | _ => false
    end

(* Version of is_eq_term' for Trueprop terms. *)
fun is_eq_term' t =
    let val _ = assert (type_of t = @{typ prop}) "is_eq_term': wrong type"
    in is_Trueprop t andalso is_eq_term (HOLogic.dest_Trueprop t) end

(* Replace schematic variables with corresponding bound variables.
   Abstract over the schematic variable with index i.
 *)
fun inplace_abstract_over_i i t =
    case t of
        Abs (nm, T, body) =>
        let
          val vars = (Term.add_vars body [])
                         |> filter (fn ((_, i'), _) => i = i')
          val _ = assert (length vars <= 1)
                         "inplace_abstract_over: invalid input"
          val body' = inplace_abstract_over_i (i+1) body
        in
          if vars = [] then Abs (nm, T, body')
          else
            let
              val ((nm',_), T') = the_single vars
              val nm'' =
                  if Name.is_internal nm' then Name.dest_internal nm'
                  else raise AUTO2 "inplace_abstract_over: not internal"
            in
              Abs (nm'', T', abstract_over (Var ((nm', i), T'), body'))
            end
        end
      | t1 $ t2 => inplace_abstract_over_i i t1 $ inplace_abstract_over_i i t2
      | _ => t
val inplace_abstract_over = inplace_abstract_over_i 0

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

(* Given a head cterm f (function to be applied), and a list of
   equivalence theorems of arguments, produce an equivalent theorem
   for the overall term.
 *)
fun comb_equiv (cf, arg_equivs) =
    Library.foldl (uncurry Thm.combination) (Thm.reflexive cf, arg_equivs)

(* Retrive name of theorem. *)
fun name_of_thm th =
    case Properties.get (Thm.get_tags th) "name" of
        NONE => raise AUTO2 "name_of_thm: not found"
      | SOME nm => nm

fun dest_eq_thm th =
    th |> Thm.prop_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq

val lhs_of = Thm.term_of o Thm.lhs_of
val rhs_of = Thm.term_of o Thm.rhs_of

(* Given an equality between bools, make it an equality between props,
   by applying the function Trueprop to both sides.
 *)
fun make_trueprop_eq th =
    Thm.combination (Thm.reflexive (cert @{context} HOLogic.Trueprop)) th

(* Given th of form A = B, get th' of form A == B. *)
fun to_meta_eq th = th RS @{thm eq_reflection}
(* Given th of form A == B, get th' of form A = B. *)
fun to_obj_eq th = th RS @{thm meta_eq_to_obj_eq}
(* Given th of form A = B, get th' of form B = A. *)
fun obj_sym th = th RS @{thm sym}
(* Given th of form A == B, get th' of form B == A. *)
fun meta_sym th = th RS @{thm symmetric}

(* Given an equality (A:bool) == B and a theorem A, return theorem B. *)
fun elim_eq_thm (eq_th, th) = Thm.equal_elim eq_th th

(* Assumed theorems. *)
fun assume_eq thy (t1, t2) =
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

(* Normalize order of existence and forall statements. *)
fun normalize_pred_comm ct =
    let
      val cv = Conv.try_conv (
            Conv.first_conv [Conv.rewr_conv (to_meta_eq @{thm ex_comm}),
                             Conv.rewr_conv (to_meta_eq (@{thm all_comm}))])
      val th = cv ct
    in
      if Term_Ord.termless (Thm.prop_of th |> Logic.dest_equals) then th
      else Conv.all_conv ct
    end

(* Turn EX x y. P x & Q y into EX x. P x & EX y. Q y. *)
val exists_split_conv =
    Conv.try_conv (
      Conv.first_conv [Conv.rewr_conv @{thm exists_split},
                       Conv.rewr_conv @{thm exists_split'}])

(* Apply the conversion cv to the statement of th, yielding the
   equivalent theorem.
 *)
fun apply_to_thm cv th =
    let val eq = cv (Thm.cprop_of th)
    in if Thm.is_reflexive eq then th else Thm.equal_elim eq th end

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
        concl_conv num_prems (Conv.rewr_conv contra_eq2_th) ct
      else
        concl_conv num_prems (Conv.rewr_conv contra_eq1_th) ct
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
    in
      if is_neg last_prem' then
        concl_conv (num_prems-1) (Conv.rewr_conv (contra_eq1_th_sym)) ct
      else
        concl_conv (num_prems-1) (Conv.rewr_conv (contra_eq2_th_sym)) ct
    end

val rewrite_thm_from_contra_form = apply_to_thm rewrite_from_contra_form

(* Swap the first two hypothesis. *)
val swap_conv = Conv.rewr_conv Drule.swap_prems_eq

(* Rotate i'th premise (zero-based, counting from front) of ct to the
   front.
 *)
fun move_to_front_conv i ct =
    if i = 0 then Conv.all_conv ct
    else ((Conv.arg_conv (move_to_front_conv (i-1))) then_conv swap_conv) ct
         handle CTERM _ => raise AUTO2 "move_to_front: index out of bounds"

(* Given ct and a permutation of premises of ct, rotate premises of ct
   so that it matches the given list.
 *)
fun rotate_prems_conv prems ct =
    case prems of
        [] => Thm.reflexive ct
      | prem :: rest =>
        let
          val id = find_index (fn t => t aconv prem)
                              (Logic.strip_imp_prems (Thm.term_of ct))
        in
          ct |> ((move_to_front_conv id)
                     then_conv (Conv.arg_conv (rotate_prems_conv rest)))
        end

fun rotate_prems_conv_thm prems th = apply_to_thm (rotate_prems_conv prems) th

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

(* Converts A1 --> ... --> An to A1 ==> ... ==> An. *)
fun to_meta_imp_conv ct =
    (case Thm.term_of ct of
         @{const HOL.Trueprop} $ (@{const HOL.implies} $ _ $ _) =>
         Conv.rewr_conv (meta_sym @{thm atomize_imp}) then_conv
                        Conv.arg_conv to_meta_imp_conv
       | _ => Conv.all_conv) ct

(* Converts ! to !! on the outermost level. *)
fun to_meta_all_conv ctxt ct =
    (case Thm.term_of ct of
         @{const HOL.Trueprop} $ (Const (@{const_name HOL.All}, _) $ Abs _) =>
         Conv.rewr_conv (meta_sym @{thm atomize_all}) then_conv
                        Conv.binder_conv (to_meta_all_conv o snd) ctxt
       | _ => Conv.all_conv) ct

fun TermConst T = Const("Pure.term", (T --> @{typ prop}))
fun is_Term t = case t of Const("Pure.term", _) $ _ => true
                        | _ => false

(* Transform A == B into TERM A == TERM B. *)
fun make_term_eq th =
    let val T = th |> Thm.lhs_of |> Thm.term_of |> type_of
    in Thm.combination (Thm.reflexive (cert @{context} (TermConst T))) th end

(* The theorem TERM ?x. *)
val term_triv_th =
    let
      val A = cert @{context} (Free ("A", @{typ prop}))
    in
      (Thm.trivial A) |> Thm.forall_intr A
                      |> Thm.equal_elim (meta_sym @{thm term_def})
    end

(* Construct the theorem TERM t. *)
fun make_term_th ctxt t =
    let
      val inst =
          pattern_fo_match ctxt (Thm.prop_of term_triv_th, Logic.mk_term t)
    in
      subst_thm ctxt inst term_triv_th
    end

(* The theorem ?P ==> (?P == TERM ?x). *)
val eq_term_triv_th =
    let
      val P = cert @{context} (Free ("P", @{typ prop}))
      (* P ==> TERM ?x. *)
      val PtoT = term_triv_th |> Thm.implies_intr P
      (* TERM ?x ==> P [P]. *)
      val TtoP = Thm.assume P |> Thm.implies_intr (Thm.cprop_of term_triv_th)
      (* P == TERM ?x [P]. *)
      val PisT = Thm.equal_intr PtoT TtoP
    in
      PisT |> Thm.implies_intr P |> Thm.generalize (["P"], ["P"]) 2
    end

(* Given theorem th and a term t, form the theorem th == TERM t. *)
fun make_eq_term_triv ctxt (th, t) =
    let
      (* th ==> (th == TERM t) *)
      val t' = Logic.mk_implies (
            Thm.prop_of th, Logic.mk_equals (Thm.prop_of th, Logic.mk_term t))
      val inst = pattern_fo_match ctxt (Thm.prop_of eq_term_triv_th, t')
    in
      th RS (subst_thm ctxt inst eq_term_triv_th)
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
              |> prefix "Thm.cterm_of (Proof_Context.theory_of ML_context) "
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
