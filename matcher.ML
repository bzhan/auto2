(* Matching up to equivalence (E-matching) using a rewrite table. *)

signature MATCHER =
sig
  (* Internal *)
  val check_type_term:
      rewrite_table -> term * term -> id_inst -> (id_inst * term) option
  val check_type: rewrite_table -> typ * typ -> id_inst -> id_inst option
  val update_inst: term list -> indexname -> cterm -> id_inst -> id_inst_th list
  val id_eq_better: rewrite_table -> box_id * 'a -> box_id * 'a -> bool
  val inst_eq_better: rewrite_table -> (string * int) list -> id_inst_th ->
                      id_inst_th -> bool

  (* THe actual matching function. These are defined together. *)
  val match_list: rewrite_table -> term list -> term list * cterm list ->
                  id_inst -> id_inst_ths list
  val match_comb: rewrite_table -> term list -> term * cterm -> id_inst ->
                  id_inst_th list
  val match_head: rewrite_table -> term list -> term * cterm -> id_inst ->
                  id_inst_th list
  val match_all_head: rewrite_table -> term list -> term * cterm -> id_inst ->
                      id_inst_th list
  val match: rewrite_table -> term list -> term * cterm -> id_inst ->
             id_inst_th list

  (* Defined in terms of match. *)
  val rewrite_match: rewrite_table -> term * cterm -> id_inst -> id_inst_th list
  val rewrite_match_head:
      rewrite_table -> term * cterm -> id_inst -> id_inst_th list
  val rewrite_match_list: rewrite_table -> (bool * (term * cterm)) list ->
                          id_inst -> id_inst_ths list
  val rewrite_match_subset:
      rewrite_table -> term list -> term list * cterm list -> id_inst ->
      id_inst_ths list

  (* Prematching. *)
  val pre_match_type: rewrite_table -> typ * typ -> bool
  val pre_match_comb: rewrite_table -> term * cterm -> bool
  val pre_match_head': rewrite_table -> term * cterm -> bool
  val pre_match_all_head: rewrite_table -> term * cterm -> bool
  val pre_match: rewrite_table -> term * cterm -> bool
  val pre_match_head: rewrite_table -> term * cterm -> bool
end;

functor Matcher(Base:UTIL_BASE) : MATCHER =
struct

structure UtilLogic = UtilLogic(Base)
structure Consts = Consts(Base)
structure RewriteTable = RewriteTable(Base)
open Base
open UtilLogic

fun compare_inst (((id1, inst1), _), ((id2, inst2), _)) =
    eq_list (op =) (id1, id2) andalso eq_env (inst1, inst2)

(* Match type at the top level for t and u. If there is no match,
   return NONE. Otherwise, return the updated instsp as well as t
   instantiated with the new type.
 *)
fun check_type_term tbl (t, u) (id, (tyinst, inst)) =
    let
      val (T, U) = (fastype_of t, fastype_of u)
      val thy = RewriteTable.theory_of tbl
    in
      if T = U then SOME ((id, (tyinst, inst)), t) else
      let
        val tyinst' = Sign.typ_match thy (T, U) tyinst
        val t' = Envir.subst_term_types tyinst' t
      in
        SOME ((id, (tyinst', inst)), t')
      end
    end
    handle Type.TYPE_MATCH => NONE

(* Match two types. *)
fun check_type tbl (T, U) (id, (tyinst, inst)) =
    let
      val thy = RewriteTable.theory_of tbl
      val tyinst' = if T = U then tyinst
                    else Sign.typ_match thy (T, U) tyinst
    in
      SOME (id, (tyinst', inst))
    end
    handle Type.TYPE_MATCH => NONE

(* Starting here, bd_vars is the list of free variables substituted
   for bound variables, when matching goes inside abstractions.
 *)
fun is_open bd_vars u =
    case bd_vars of
        [] => false
      | _ =>
        length (inter (op aconv) bd_vars (map Free (Term.add_frees u []))) > 0

(* Assign schematic variable with indexname ixn to u. Type of the
   schematic variable is determined by the type of u.
 *)
fun update_inst bd_vars ixn cu (id, inst) =
    let
      val u = Thm.term_of cu
    in
      if is_open bd_vars u then []
      else [((id, update_env (ixn, u) inst), Thm.reflexive cu)]
    end

(* Partial comparison using just the ID. *)
fun id_eq_better {lat, ...} (id, _) (id', _) = BoxID.is_eq_ancestor lat id id'

(* Whether the second instantiation is extraneous compared to the
   first. Currently use a fast version where instantiated terms are
   compared using aconv.
 *)
fun inst_eq_better {lat, ...} vars ((id, inst), _) ((id', inst'), _) =
    BoxID.is_eq_ancestor lat id id' andalso
    forall (fn var => lookup_instn inst var aconv lookup_instn inst' var) vars

(* Matching an order list of patterns against terms. *)
fun match_list tbl bd_vars (ts, cus) instsp =
    if length ts = 0 andalso length cus = 0 then [(instsp, [])]
    else if length ts = 0 orelse length cus = 0 then []
    else let
      (* Two choices, one of which should always work (encounter no
         illegal higher-order patterns.
       *)
      fun hd_first () =
          let
            val insts_t = match tbl bd_vars (hd ts, hd cus) instsp
            fun process_inst_t (instsp', th) =
                let
                  val insts_ts' = match_list tbl bd_vars (tl ts, tl cus) instsp'
                in
                  map (apsnd (cons th)) insts_ts'
                end
          in
            maps process_inst_t insts_t
          end
      fun tl_first () =
          let
            val insts_ts' = match_list tbl bd_vars (tl ts, tl cus) instsp
            fun process_inst_ts' (instsp', ths) =
                let
                  val insts_t = match tbl bd_vars (hd ts, hd cus) instsp'
                in
                  map (apsnd (fn th => th :: ths)) insts_t
                end
          in
            maps process_inst_ts' insts_ts'
          end
    in
      hd_first () handle Fail "invalid pattern" => tl_first ()
    end

(* Match a non-AC function. *)
and match_comb tbl bd_vars (t, cu) (instsp as (_, (_, inst))) =
    let
      val {ctxt, ...} = tbl
      val (tf, targs) = Term.strip_comb t
      val (cuf, cuargs) = Drule.strip_comb cu
      val uf = Thm.term_of cuf
    in
      if Term.aconv_untyped (tf, uf) then
        let
          val instsps' = match_list tbl bd_vars (targs, cuargs) instsp
          fun process_inst (instsp', ths) =
              (instsp', comb_equiv (cuf, ths))
        in
          map process_inst instsps'
        end
      else if is_Var tf then
        let
          val (ixn, _) = Term.dest_Var tf
        in
          case Vartab.lookup inst ixn of
              NONE =>
              if subset (op aconv) (targs, bd_vars) andalso
                 not (has_duplicates (op aconv) targs) then
                let
                  val cu' = cu |> Thm.term_of
                               |> fold lambda_abstract (rev targs)
                               |> cert ctxt
                in
                  map (fn (instsp', _) => (instsp', Thm.reflexive cu))
                      (update_inst bd_vars ixn cu' instsp)
                end
              else
                raise Fail "invalid pattern"
            | SOME (_, tf') =>
              let
                val t' = Term.list_comb (tf', targs) |> Envir.beta_norm
              in
                match tbl bd_vars (t', cu) instsp
              end
        end
      else []
    end

(* Match t and u at head. *)
and match_head tbl bd_vars (t, cu) (instsp as (_, (_, inst))) =
    let
      val {ctxt, ...} = tbl
      val u = Thm.term_of cu
    in
      if fastype_of t <> fastype_of u then [] else
      case (t, u) of
          (Var ((nm, i), _), _) =>
          (case Vartab.lookup inst (nm, i) of
               NONE => if nm = "NUMC" andalso
                          not (Consts.is_const_ctxt ctxt u) then []
                       else if nm = "FREE" andalso not (Term.is_Free u) then []
                       else update_inst bd_vars (nm, i) cu instsp
             | SOME (_, u') => match_head tbl bd_vars (u', cu) instsp)
        | (Free (a, _), Free (b, _)) =>
          if a = b then [(instsp, Thm.reflexive cu)] else []
        | (Const (a, _), Const (b, _)) =>
          if a = b then [(instsp, Thm.reflexive cu)] else []
        | (_ $ _, _) => match_comb tbl bd_vars (t, cu) instsp
        | _ => []
    end

(* With fixed t, match with all equivalences of u. *)
and match_all_head tbl bd_vars (t, cu) (id, env) =
    let
      val u = Thm.term_of cu
      val u_equivs =
          if is_open bd_vars u then [(id, Thm.reflexive cu)]
          else RewriteTable.get_head_equiv_with_t tbl (id, cu) t

      fun process_equiv (id', eq_u) =
          let
            val cu' = Thm.rhs_of eq_u
            val insts_u' = match_head tbl bd_vars (t, cu') (id', env)
            fun process_inst ((id', env'), eq_th) =
                (* eq_th: t(env') == u', eq_u: u == u'. *)
                ((id', env'), transitive_list [eq_th, meta_sym eq_u])
          in
            map process_inst insts_u'
          end
    in
      maps process_equiv u_equivs
    end

(* Match t and u, possibly by rewriting u at head. *)
and match tbl bd_vars (t, cu) (instsp as (_, (_, inst))) =
    case check_type_term tbl (t, Thm.term_of cu) instsp of
        NONE => []
      | SOME (instsp', t') =>
        case (t', Thm.term_of cu) of
            (Var ((nm, i), _), _) =>
            (case Vartab.lookup inst (nm, i) of
                 NONE => if member (op =) ["NUMC", "FREE"] nm then
                           match_all_head tbl bd_vars (t', cu) instsp'
                         else
                           update_inst bd_vars (nm, i) cu instsp'
               | SOME (_, u') => match tbl bd_vars (u', cu) instsp')
          | (Abs (_, T, t'), Abs (nm, U, _)) => (
            case check_type tbl (T, U) instsp' of
                NONE => []
              | SOME (instsp'' as (_, (tyinst', _))) =>
                let
                  val (cv, cu') = Thm.dest_abs (SOME Name.uu) cu
                  val v = Thm.term_of cv
                  val t'' = Envir.subst_term_types tyinst' t'
                  val t_free = Term.subst_bound (v, t'')
                  val insts' = match tbl (v :: bd_vars) (t_free, cu') instsp''
                  fun process_inst (inst', th') =
                      (inst', Thm.abstract_rule nm cv th')
                in
                  map process_inst insts'
                end)
          | _ => (* Free, Const, and comb case *)
            (match_all_head tbl bd_vars (t', cu) instsp')
                |> distinct compare_inst

(* Function for export *)
fun rewrite_match_gen at_head tbl (t, cu) (id, env) =
    if at_head then
      case check_type_term tbl (t, Thm.term_of cu) (id, env) of
          NONE => []
        | SOME ((id, env), t) => match_head tbl [] (t, cu) (id, env)
    else
      match tbl [] (t, cu) (id, env)

val rewrite_match = rewrite_match_gen false
val rewrite_match_head = rewrite_match_gen true

(* pairs is a list of (at_head, (t, u)). Match the pairs in sequence,
   and return a list of ((id, inst), ths), where ths is the list of
   equalities t(env) == u.
 *)
fun rewrite_match_list tbl pairs instsp =
    case pairs of
        [] => [(instsp, [])]
      | (at_head, (t, cu)) :: pairs' =>
        let
          val insts_t = rewrite_match_gen at_head tbl (t, cu) instsp
          fun process_inst_t (instsp', th) =
              let
                val insts_ts' = rewrite_match_list tbl pairs' instsp'
              in
                map (apsnd (cons th)) insts_ts'
              end
        in
          maps process_inst_t insts_t
        end

(* Given two lists of terms (ts, us), match ts with a subset of
   us. Return a list of ((id, inst), ths), where ths is the list of
   equalities t_i(env) == u_j.
 *)
fun rewrite_match_subset tbl bd_vars (ts, cus) instsp =
    case ts of
        [] => [(instsp, [])]
      | t :: ts' =>
        let
          fun match_i i =
              map (pair i) (match tbl bd_vars (t, nth cus i) instsp)

          fun process_match_i (i, (instsp', th)) =
              let
                val insts_ts' = rewrite_match_subset
                                    tbl bd_vars (ts', nth_drop i cus) instsp'
              in
                map (apsnd (cons th)) insts_ts'
              end
        in
          (0 upto (length cus - 1))
              |> maps match_i |> maps process_match_i
        end
        handle Fail "invalid pattern" =>
               if length ts' > 0 andalso Term_Ord.termless (t, hd ts') then
                 rewrite_match_subset tbl bd_vars (ts' @ [t], cus) instsp
               else raise Fail "rewrite_match_subset: invalid pattern"

(* Fast function for determining whether there can be a match between
   t and u.
 *)
fun pre_match_type tbl (T, U) =
    let
      val thy = RewriteTable.theory_of tbl
      val _ = Sign.typ_match thy (T, U) Vartab.empty
    in
      true
    end
    handle Type.TYPE_MATCH => false

fun pre_match_comb tbl (t, cu) =
    let
      val (tf, targs) = Term.strip_comb t
      val (cuf, cuargs) = Drule.strip_comb cu
      val uf = Thm.term_of cuf
    in
      is_Var tf orelse (Term.aconv_untyped (tf, uf) andalso
                        length targs = length cuargs andalso
                        forall (pre_match tbl) (targs ~~ cuargs))
    end

and pre_match_head' (tbl as {ctxt, ...}) (t, cu) =
    let
      val u = Thm.term_of cu
    in
      case (t, u) of
          (Var ((nm, _), T), _) =>
          if Term.is_open u then false
          else if not (pre_match_type tbl (T, fastype_of u)) then false
          else if nm = "NUMC" then Consts.is_const_ctxt ctxt u
          else if nm = "FREE" then Term.is_Free u
          else true
        | (Free (a, T), Free (b, U)) =>
          (a = b andalso pre_match_type tbl (T, U))
        | (Const (a, T), Const (b, U)) =>
          (a = b andalso pre_match_type tbl (T, U))
        | (_ $ _, _) => pre_match_comb tbl (t, cu)
        | _ => false
    end

and pre_match_all_head tbl (t, cu) =
    let
      val thy = RewriteTable.theory_of tbl
      val u = Thm.term_of cu
      val tyinst = Sign.typ_match thy (fastype_of t, fastype_of u) Vartab.empty
      val t' = Envir.subst_term_types tyinst t
    in
      if Term.is_open u then pre_match_head' tbl (t', cu)
      else let
        val u_equivs =
            (RewriteTable.get_head_equiv_with_t tbl ([], cu) t')
                |> map snd |> map Thm.rhs_of
      in
        exists (fn cu' => pre_match_head' tbl (t', cu')) u_equivs
      end
    end
    handle Type.TYPE_MATCH => false

and pre_match tbl (t, cu) =
    let
      val u = Thm.term_of cu
    in
      case (t, u) of
          (Var ((nm, _), T), _) =>
          if Term.is_open u then false
          else if not (pre_match_type tbl (T, fastype_of u)) then false
          else if member (op =) ["NUMC", "FREE"] nm then
            pre_match_all_head tbl (t, cu)
          else true
        | (Abs (_, T, t'), Abs (_, U, _)) =>
          if not (pre_match_type tbl (T, U)) then false
          else let
            val (cv, cu') = Thm.dest_abs (SOME Name.uu) cu
            val t'' = subst_bound (Thm.term_of cv, t')
          in
            pre_match tbl (t'', cu')
          end
        | (Bound i, Bound j) => (i = j)
        | (_, _) => pre_match_all_head tbl (t, cu)
    end

fun pre_match_head tbl (t, cu) =
    let
      val thy = RewriteTable.theory_of tbl
      val u = Thm.term_of cu
      val tyinst = Sign.typ_match thy (fastype_of t, fastype_of u) Vartab.empty
      val t' = Envir.subst_term_types tyinst t
    in
      pre_match_head' tbl (t', cu)
    end
    handle Type.TYPE_MATCH => false

end  (* structure Matcher. *)
