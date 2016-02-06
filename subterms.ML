(* Deconstruct a term into head and subterms, customized for AUTO2. *)

signature SUBTERMS =
sig
  val triv_subterms: term -> term * term list
  val dest_subterms: theory -> bool -> term -> term * term list
  val list_subterms: theory -> bool -> term -> term list
  val get_all_subterms: theory -> bool -> term -> term list
  val subst_subterms: term * term list -> term
  val build_equiv: Proof.context -> thm list -> term -> thm

  val get_head_ac_info_with_inv: theory -> term -> ac_inst_info option
  val normalize_all_ac: Proof.context -> ac_inst_info -> conv
end;

structure Subterms : SUBTERMS =
struct

fun is_if f =
    case f of
        Const ("HOL.If", _) => true
      | _ => false

fun get_subvar n t = Var (("SUB", n), fastype_of t)

fun triv_subterms t = (get_subvar 0 t, [t])

(* Destruct t into head and subterm structure. *)
fun dest_subterms thy skip_if t =
    let
      (* t is eligible as a subterm, expand in special cases. The
         prevs list record previous subterms.
       *)
      fun dest_at_head (prevs, t) =
          case t of
              _ $ _ =>
              if Term.is_open t then
                dest (prevs, t)
              else
                (t :: prevs, get_subvar (length prevs) t)
            | Abs (nm, T, t') =>
              let
                val (prevs', t'') = dest_at_head (prevs, t')
              in
                (prevs', Abs (nm, T, t''))
              end
            | Bound _ => (prevs, t)
            | _ => (t :: prevs, get_subvar (length prevs) t)

      and dest_list_at_head (prevs, ts) =
          let
            fun append_dest t (prevs', prev_ts') =
                let
                  val (prevs'', t') = dest_at_head (prevs', t)
                in
                  (prevs'', t' :: prev_ts')
                end
            val (prevs', rev_ts') = fold append_dest ts (prevs, [])
          in
            (prevs', rev rev_ts')
          end

      and dest (prevs, t) =
          case t of
              _ $ _ =>
              let
                val (tf, targs) = Term.strip_comb t
                val ac_info_opt = ACUtil.get_head_ac_info thy t
              in
                if skip_if andalso is_if tf then
                  let
                    val (prevs', t') = dest_at_head (prevs, hd targs)
                  in
                    (prevs', Term.list_comb (tf, t' :: tl targs))
                  end
                else if is_none ac_info_opt then
                  let
                    val (prevs', ts') = dest_list_at_head (prevs, targs)
                  in
                    (prevs', Term.list_comb (tf, ts'))
                  end
                else
                  let
                    val ac_info = the ac_info_opt
                    val ac_args = ACUtil.dest_ac ac_info t
                    val (prevs', ts') = dest_list_at_head (prevs, ac_args)
                  in
                    (prevs', ACUtil.list_ac ac_info ts')
                  end
              end
            | Abs _ => dest_at_head (prevs, t)
            | _ => (prevs, t)

      val (rev_subs, t') = dest ([], t)
    in
      (t', rev rev_subs)
    end

fun list_subterms thy skip_if t = snd (dest_subterms thy skip_if t)

(* List all (closed) subterms. Larger ones will be listed first. *)
fun get_all_subterms thy skip_if t =
    let
      val args = list_subterms thy skip_if t
      val subs = fold (curry (merge (op aconv)))
                      (map (get_all_subterms thy skip_if) args) []
    in
      t :: subs
    end

(* Note this also works when t is a subterm of original decomposition
   (so t only contain some of the subs).
 *)
fun subst_subterms (t, subs) =
    let
      val subst = (0 upto (length subs - 1) ~~ subs)
                      |> map (fn (i, sub') => (get_subvar i sub', sub'))
    in
      subst_atomic subst t
    end

(* Given a decomposition into (t, subs) of a term u, and a list of
   equivalences from subs to subs', produce equivalence from u to the
   result of making the replacements.
 *)
fun build_equiv ctxt equivs t =
    let
      fun build ctxt t' =
          case t' of
              t1 $ t2 => Thm.combination (build ctxt t1) (build ctxt t2)
            | Abs (v, T, t'') =>
              let
                val (v', ctxt') =
                    yield_singleton Variable.variant_fixes Name.uu ctxt
                val fvar = Free (v', T)
                val t''' = subst_bound (fvar, t'')
              in
                Thm.abstract_rule v (cert ctxt fvar) (build ctxt' t''')
              end
            | Var (("SUB", i), _) => nth equivs i
            | _ => Thm.reflexive (cert ctxt t')
      val _ = if Term.is_open t then
                raise AUTO2 "build_equiv: t is open" else ()
    in
      build ctxt t
    end

(* Wrapper around functions in ACUtil, adapted to take account of
   binders.
 *)
fun get_head_ac_info_with_inv thy t =
    case t of
        _ $ Abs (_, _, t') => get_head_ac_info_with_inv thy t'
      | _ => ACUtil.get_head_ac_info_with_inv thy t

fun normalize_all_ac ctxt ac_info ct =
    case Thm.term_of ct of
        _ $ Abs _ =>
        Conv.arg_conv (
          Conv.abs_conv (fn _ => normalize_all_ac ctxt ac_info) ctxt) ct
      | _ => ACUtil.normalize_all_ac ac_info ct

end  (* structure Subterms. *)
