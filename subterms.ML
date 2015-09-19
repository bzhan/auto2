(* Deconstruct a term into head and subterms, customized for AUTO2. *)

signature SUBTERMS =
sig
  val triv_subterms: term -> term * term list
  val dest_subterms: theory -> bool -> term -> term * term list
  val list_subterms: theory -> bool -> term -> term list
  val get_all_subterms: theory -> bool -> term -> term list
  val subst_subterms: term * term list -> term
  val build_equiv: Proof.context -> thm list -> term -> thm

  val get_head_ac_item: theory -> term -> ac_item option
  val rearrange_fast: theory -> term -> term
  val rearrange_subterms: theory -> ac_item -> conv
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
              _ $ _ => if Term.is_open t then dest (prevs, t)
                       else (t :: prevs, get_subvar (length prevs) t)
            | Abs (nm, T, t') =>
              let
                val (prevs', t'') = dest_at_head (prevs, t')
              in (prevs', Abs (nm, T, t'')) end
            | Bound _ => (prevs, t)
            | _ => (t :: prevs, get_subvar (length prevs) t)

      (* Special case, for AC functions. *)
      and dest_ac_at_head (ac_itm as {assoc_r, ...}) (prevs, t) =
          if Term.is_open t then dest (prevs, t)
          else if ACUtil.head_agrees ac_itm t then
            let
              val (tf, (arg1, arg2)) = dest_binop t
            in
              if assoc_r then
                let
                  val prevs' = arg1 :: prevs
                  val (prevs'', t') = dest_ac_at_head ac_itm (prevs', arg2)
                in
                  (prevs'', tf $ (get_subvar (length prevs) arg1) $ t')
                end
              else
                let
                  val (prevs', t') = dest_ac_at_head ac_itm (prevs, arg1)
                in
                  (arg2 :: prevs', tf $ t' $ (get_subvar (length prevs') arg2))
                end
            end
          else (t :: prevs, get_subvar (length prevs) t)

      and dest (prevs, t) =
          case t of
              _ $ _ =>
              let
                val (tf, targs) = Term.strip_comb t
              in
                if skip_if andalso is_if tf then
                  let val (prevs', t') = dest_at_head (prevs, hd targs)
                  in (prevs', Term.list_comb (tf, t' :: tl targs)) end
                else
                  case ACUtil.get_head_ac_item thy t of
                      NONE =>
                      let
                        fun append_dest targ (prevs', prev_args) =
                            let
                              val (prevs'', targ') = dest_at_head (prevs', targ)
                            in
                              (prevs'', targ' :: prev_args)
                            end
                        val (prevs', targs_rev) =
                            fold append_dest targs (prevs, [])
                        val t' = Term.list_comb (tf, rev targs_rev)
                      in
                        (prevs', t')
                      end
                    | SOME (ac_itm as {assoc_r, ...}) =>
                      let
                        val (arg1, arg2) = the_pair targs
                      in
                        if assoc_r then
                          let
                            val (prevs', arg1') = dest_at_head (prevs, arg1)
                            val (prevs'', arg2') =
                                dest_ac_at_head ac_itm (prevs', arg2)
                          in
                            (prevs'', Term.list_comb (tf, [arg1', arg2']))
                          end
                        else
                          let
                            val (prevs', arg1') =
                                dest_ac_at_head ac_itm (prevs, arg1)
                            val (prevs'', arg2') = dest_at_head (prevs', arg2)
                          in
                            (prevs'', Term.list_comb (tf, [arg1', arg2']))
                          end
                      end
              end
            | Abs (nm, T, t') => let val (prevs', t'') = dest (prevs, t')
                                 in (prevs', Abs (nm, T, t'')) end
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
fun get_head_ac_item thy t =
    case t of
        _ $ Abs (_, _, t') => get_head_ac_item thy t'
      | _ => ACUtil.get_head_ac_item thy t

fun rearrange_fast thy t =
    case t of
        f $ Abs (nm, T, t') => f $ Abs (nm, T, rearrange_fast thy t')
      | _ => ACUtil.rearrange_fast thy t

fun rearrange_subterms thy ac_itm ct =
    case Thm.term_of ct of
        _ $ Abs _ => Conv.arg_conv (
                      Conv.abs_conv (fn _ => rearrange_subterms thy ac_itm)
                                    (Proof_Context.init_global thy)) ct
      | _ => ACUtil.rearrange_subterms ac_itm ct

end  (* structure Subterms. *)
