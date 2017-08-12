(* Deconstruct a term into head and subterms, customized for auto2. *)

signature SUBTERMS =
sig
  val dest_subterms: cterm -> cterm * cterm list
  val list_subterms: cterm -> cterm list
  val get_all_subterms: cterm -> cterm list
  val get_all_subterms_skip_if: cterm -> cterm list
  val subst_subterms: term * term list -> term
  val build_equiv: thm list -> cterm -> thm
end;

structure Subterms : SUBTERMS =
struct

open Base
open UtilLogic

fun get_subvar n ct = Thm.var (("SUB", n), Thm.ctyp_of_cterm ct)
fun get_subvar_t n t = Var (("SUB", n), fastype_of t)

(* bd_vars is the list of free variables substituted for bound
   variables, when matching goes inside abstractions.
 *)
fun is_open bd_vars u =
    case bd_vars of
        [] => false
      | _ =>
        length (inter (op aconv) bd_vars (map Free (Term.add_frees u []))) > 0

(* Destruct ct into head and subterm structure. *)
fun dest_subterms ct =
    let
      (* See description for dest below, except here ct itself is
         eligible as a subterm. Break down only if it is in Abs form.
       *)
      fun dest_at_head bd_vars (prevs, ct) =
          let
            val t = Thm.term_of ct
          in
            case t of
                _ $ _ =>
                if is_open bd_vars t then
                  dest bd_vars (prevs, ct)
                else
                  (ct :: prevs, get_subvar (length prevs) ct)
              | Abs _ =>
                let
                  val (cvar, ct') = Thm.dest_abs NONE ct
                  val (prevs', ct'') =
                      dest_at_head (Thm.term_of cvar :: bd_vars) (prevs, ct')
                in
                  (prevs', Thm.lambda cvar ct'')
                end
              | _ =>
                if is_open bd_vars t then (prevs, ct)
                else (ct :: prevs, get_subvar (length prevs) ct)
          end

      (* See description of dest below, except here, we have a list of
         input terms.
       *)
      and dest_list_at_head bd_vars (prevs, cts) =
          let
            fun append_dest ct (prevs', prev_cts') =
                let
                  val (prevs'', ct') = dest_at_head bd_vars (prevs', ct)
                in
                  (prevs'', ct' :: prev_cts')
                end

            val (prevs', rev_cts') = fold append_dest cts (prevs, [])
          in
            (prevs', rev rev_cts')
          end

      (* Given an existing list of subterms (prevs) and the current
         term (ct), append the subterms of ct onto prevs, and return
         the version of ct with subterms replaced by ?SUBi.
       *)
      and dest bd_vars (prevs, ct) =
          let
            val t = Thm.term_of ct
          in
            case t of
                _ $ _ =>
                let
                  val (cf, cargs) = Drule.strip_comb ct
                  val (prevs', cts') = dest_list_at_head bd_vars (prevs, cargs)
                in
                  (prevs', Drule.list_comb (cf, cts'))
                end
              | Abs _ => dest_at_head bd_vars (prevs, ct)
              | _ => (prevs, ct)
          end

      val (rev_subs, t') = dest [] ([], ct)
    in
      (t', rev rev_subs)
    end

fun list_subterms ct = snd (dest_subterms ct)

(* List all (closed) subterms. Larger ones will be listed first. *)
fun get_all_subterms ct =
    ct :: (ct |> list_subterms |> maps get_all_subterms |> distinct (op aconvc))

(* List all (closed) subterms. For terms of form if cond then yes or
   no, list only subterms of cond.
 *)
fun get_all_subterms_skip_if ct =
    if is_if (Thm.term_of ct) then
      ct :: get_all_subterms_skip_if (ct |> dest_cargs |> hd)
    else
      ct :: (ct |> list_subterms |> maps get_all_subterms_skip_if
                |> distinct (op aconvc))

(* Note this also works when t is a subterm of original decomposition
   (so t only contain some of the subs).
 *)
fun subst_subterms (t, subs) =
    let
      val subst =
          (0 upto (length subs - 1) ~~ subs)
              |> map (fn (i, sub') => (get_subvar_t i sub', sub'))
    in
      subst_atomic subst t
    end

(* Given a decomposition into (t, subs) of a term u, and a list of
   equivalences from subs to subs', produce equivalence from u to the
   result of making the replacements.
 *)
fun build_equiv equivs ct =
    let
      val _ = assert (not (Term.is_open (Thm.term_of ct)))
                     "build_equiv: t is open"

      fun build ct =
          case Thm.term_of ct of
              _ $ _ => Thm.combination (build (Thm.dest_fun ct))
                                       (build (Thm.dest_arg ct))
            | Abs (x, _, _) =>
              let
                val (cv, ct') = Thm.dest_abs (SOME Name.uu) ct
              in
                Thm.abstract_rule x cv (build ct')
              end
            | Var (("SUB", i), _) => nth equivs i
            | _ => Thm.reflexive ct
    in
      build ct
    end

end  (* structure Subterms. *)
