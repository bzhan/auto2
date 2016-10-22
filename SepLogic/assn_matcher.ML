(* Matching of assertions. *)

(* Given arguments tbl pat t (id, inst), match pat with t. Assume pat
   is not a product. Produce either t ==> pat(s) or t ==> t' * pat(s).
 *)
type assn_matcher = rewrite_table -> term -> term -> id_inst -> id_inst_th list

structure AssnMatchData =
Theory_Data (
  type T = (bool * assn_matcher) list
  val empty = []
  val extend = I;
  val merge = merge (op pointer_eq)
)

signature ASSN_MATCHER =
sig
  val entail_triv_th: Proof.context -> term -> thm
  val entail_trans_l_th: thm -> thm -> thm
  val entail_trans_r_th: thm -> thm -> thm
  val entail_trans_th: thm -> thm -> thm
  val dest_ent_r: thm -> term
  val ent_r_cv: conv -> thm -> thm

  val add_assn_matcher: bool * assn_matcher -> theory -> theory
  val is_full_match: Type.tyenv * Envir.tenv -> term -> thm -> bool
  val assn_match_term: rewrite_table -> term -> term -> id_inst ->
                       (bool * id_inst_th) list
  val assn_match_all: bool -> rewrite_table -> term -> term -> id_inst ->
                      (bool * id_inst_th) list
  val assn_matcher: item_matcher
  val triv_assn_matcher: assn_matcher
  val emp_assn_matcher: assn_matcher
  val add_assn_matcher_proofsteps: theory -> theory
  val add_entail_matcher: thm -> theory -> theory
end

structure AssnMatcher : ASSN_MATCHER =
struct

open Sep_Logic

(* Given A of type assnT, return the theorem A ==> A. *)
fun entail_triv_th ctxt A =
    let
      val inst = pattern_fo_match ctxt (Var (("A", 0), assnT), A)
    in
      subst_thm ctxt inst @{thm entails_triv}
    end

(* Given th2 of form B ==> C, and th1 of form A ==> B or A ==> B * D
   or A ==> D * B, return the result of chaining th2 with th1.
 *)
fun entail_trans_l_th th2 th1 =
    [th1, th2] MRS @{thm entail_trans3}
fun entail_trans_r_th th2 th1 =
    [th1, th2] MRS @{thm entail_trans2}
fun entail_trans_th th2 th1 =
    [th1, th2] MRS @{thm entail_trans}

val dest_ent_r = dest_arg o prop_of'
val ent_r_cv = apply_to_thm' o Conv.arg_conv

fun add_assn_matcher (sp, matcher) = AssnMatchData.map (cons (sp, matcher))

(* th is of form A ==> B. Test whether B = pat(inst). *)
fun is_full_match inst pat th =
    dest_arg (prop_of' th) aconv subst_term_norm inst pat

(* Assume pat is not in the form A * B. Match pat with one or more
   terms of t. Return theorem of form t ==> t' * pat(s).
 *)
fun assn_match_term (tbl as {ctxt, ...}) pat t (id, inst) =
    case pat of
        Var (ixn, _) =>
        [(false, ((id, update_env (ixn, t) inst), entail_triv_th ctxt t))]
      | _ =>
        let
          val thy = RewriteTable.theory_of tbl
          val matchers = AssnMatchData.get thy
          fun apply_matcher (sp, matcher) =
              map (pair sp) (matcher tbl pat t (id, inst))
          val res = maps apply_matcher matchers
          fun check_res (_, ((_, inst'), th)) =
              let
                val rhs = th |> prop_of' |> dest_arg
                val exp_rhs = subst_term_norm inst' pat
              in
                if rhs aconv exp_rhs orelse dest_arg rhs aconv exp_rhs then ()
                else raise AUTO2 "assn_match_term"
              end
          val _ = map check_res res
        in
          res
        end

(* Match each term of pat with some term in t. If is_full = true, then
   each match must cover all of t, returning t ==> pat(s). Otherwise,
   the function is allowed to return t ==> pat(s) * t'.
 *)
fun assn_match_all is_full tbl pat t (id, inst) =
    case pat of
        Const (@{const_name times}, _) $ A $ B =>
        if is_Var B then
          let
            val insts = assn_match_all false tbl A t (id, inst)

            (* th is t ==> pat(s) or t ==> pat(s) * t'. *)
            fun process_inst (sp, ((id', inst'), th)) =
                let
                  val (ixn, _) = dest_Var B
                  val rhs = th |> prop_of' |> dest_arg |> dest_arg
                in
                  if is_full_match inst' A th then
                    (sp, ((id', update_env (ixn, emp) inst'),
                          th |> ent_r_cv (
                            rewr_obj_eq (obj_sym @{thm mult_1_right}))))
                  else
                    (sp, ((id', update_env (ixn, rhs) inst'), th))
                end
          in
            map process_inst insts
          end
        else
          let
            val insts = assn_match_term tbl B t (id, inst)

            (* th is t ==> pat(s) or t ==> t' * pat(s). *)
            fun process_inst (sp1, ((id', inst'), th)) =
                let
                  val is_full1 = is_full_match inst' B th
                  val t' = if is_full1 then emp
                           else th |> prop_of' |> dest_arg |> dest_arg1
                  val A' = subst_term_norm inst' A
                  val insts' = assn_match_all is_full tbl A' t' (id', inst')
                  val thy = RewriteTable.theory_of tbl
                  val ac_data = Nat_Arith.times_ac_on_typ thy assnT

                  (* th' is t' ==> A(s) or t' ==> A(s) * t''. *)
                  fun process_inst' (sp2, ((id'', inst''), th')) =
                      let
                        val is_full2 = is_full_match inst'' A' th'
                        val res =
                            th |> (is_full1 ? ent_r_cv (
                                      rewr_obj_eq (obj_sym @{thm mult_1})))
                               |> entail_trans_l_th th'
                               |> (not is_full2
                                       ? ent_r_cv (ACUtil.swap_r_cv ac_data))
                      in
                        if is_full andalso not is_full2 then []
                        else [(sp1 orelse sp2, ((id'', inst''), res))]
                      end
                in
                  maps process_inst' insts'
                end
          in
            maps process_inst insts
          end
      | _ =>
        let
          val insts = assn_match_term tbl pat t (id, inst)
          fun process_inst (sp, ((id', inst'), th)) =
              if is_full_match inst' pat th then [(sp, ((id', inst'), th))]
              else if is_full then []
              else
                [(sp, ((id', inst'),
                       th |> ent_r_cv (rewr_obj_eq @{thm mult_ac(2)})))]
        in
          maps process_inst insts
        end

val assn_matcher =
    let
      fun filt pat tname =
          is_mod pat andalso is_mod tname andalso
          (pat |> dest_mod |> fst) aconv (tname |> dest_mod |> fst)

      fun pre_match pat {tname, ...} _ = filt pat tname

      fun match pat {tname, prop, ...} tbl (id, inst) =
          if not (filt pat tname) then []
          else let
            val pat_assn = pat |> dest_mod |> snd
            val t_assn = tname |> dest_mod |> snd
            val insts = assn_match_all true tbl pat_assn t_assn (id, inst)

            (* th is t_assn ==> pat_assn(s). *)
            fun process_inst (sp, ((id', inst'), th)) =
                if sp then [((id', inst'), [th, prop] MRS @{thm entailsD})]
                else []
          in
            maps process_inst insts
          end
    in
      {pre_match = pre_match, match = match}
    end

fun triv_assn_matcher (tbl as {ctxt, ...}) pat t (id, inst) =
    if pat aconv emp then []  (* leave to emp_assn_matcher *)
    else let
      val thy = RewriteTable.theory_of tbl
      val ac_info = Nat_Arith.times_ac_on_typ thy assnT
      val ts = ACUtil.dest_ac_l ac_info t

      fun match_i i =
          let
            val t' = nth ts i
            val insts = Matcher.rewrite_match tbl (pat, t') (id, inst)

            (* eq_th is of form pat(inst') == t'. *)
            fun process_inst ((id', inst'), eq_th) =
                let
                  val th = entail_triv_th ctxt t
                  val cv = Conv.every_conv [
                        ACUtil.move_outmost ac_info t',
                        ACUtil.ac_last_conv
                            ac_info (Conv.rewr_conv (meta_sym eq_th))]
                in
                  ((id', inst'), th |> ent_r_cv cv)
                end
          in
            map process_inst insts
          end
    in
      maps match_i (0 upto (length ts - 1))
    end

(* Consider the case where pat = emp. If t is also emp, then return
   emp ==> emp. Otherwise, return t ==> t * emp.
 *)
fun emp_assn_matcher {ctxt, ...} pat t (id, inst) =
    if not (pat aconv emp) then []
    else let
      val th = entail_triv_th ctxt t
    in
      [((id, inst),
        if t aconv emp then th
        else th |> ent_r_cv (rewr_obj_eq (obj_sym @{thm mult_1_right})))]
    end

val add_assn_matcher_proofsteps =
    fold ItemIO_Data.add_prop_matcher [
      (TY_PROP, assn_matcher)

    ] #> fold add_assn_matcher [
      (false, triv_assn_matcher), (false, emp_assn_matcher)

    ]

(* Given entailment theorem A ==> B, where B is of the form f ?xs
   pat_r, where f is a constant, and pat_r may contain schematic
   variables. Attempt to find a term of form f xs r within t, for the
   given r, by matching the pattern A. For each match, return the
   implication t ==> f xs r or t ==> t' * f xs r. This function serves
   as the first step of entail_matcher.
 *)
fun entail_matcher' entail_th (tbl as {ctxt, ...}) r t id =
    let
      (* Match pat_r with r. *)
      val pat_r = entail_th |> dest_ent_r |> dest_arg
      val inst_r = Matcher.rewrite_match tbl (pat_r, r) (id, fo_init)

      (* For each match, recursively match the instantiated version of
         A (named pat here) with t.
       *)
      fun process_inst_r ((id', inst'), eq_th) =
          let
            val entail_th' = subst_thm ctxt inst' entail_th
            val pat = entail_th' |> prop_of' |> dest_arg1
            val matches = assn_match_all false tbl pat t (id', fo_init)

            (* th is of form t ==> pat(s) or t ==> pat(s) * t'. In the
               latter case, convert to t ==> t' * pat(s). Then use
               entailment theorem to convert to t ==> t' * B. Finally,
               convert the argument in B to the given r.
             *)
            fun process_match (_, ((id'', inst''), th)) =
                let
                  val thy = RewriteTable.theory_of tbl
                  val ac_info = Nat_Arith.times_ac_on_typ thy assnT
                  val cv = argn_conv 1 (Conv.rewr_conv eq_th)
                  val is_full = is_full_match inst'' pat th
                  val th' = if is_full then th
                            else th |> ent_r_cv (rewr_obj_eq @{thm mult_ac(2)})
                in
                  (id'', th' |> (if is_full then entail_trans_th entail_th'
                                 else entail_trans_r_th entail_th')
                             |> ent_r_cv (ACUtil.ac_last_conv ac_info cv))
                end
          in
            map process_match matches
          end
    in
      maps process_inst_r inst_r
    end

(* Given entailment theorem A ==> B, with same condition as in
   entail_matcher', attempt to match pat with t, and return t ==>
   pat(s) or t ==> t' * pat(s). For any matching to be performed, pat
   must be in the form f pat_xs r, where pat_xs may contain schematic
   variables, but r cannot. First, find f xs r using entail_matcher',
   then match pat_xs with xs.
 *)
fun entail_matcher entail_th tbl pat t (id, inst) =
    let
      val (f, args) = Term.strip_comb pat
      val pat_f = entail_th |> dest_ent_r |> Term.head_of
    in
      if not (Term.aconv_untyped (f, pat_f)) orelse
         has_vars (nth args 1) then []
      else let
        val (pat_xs, r) = the_pair args
        val matches = entail_matcher' entail_th tbl r t id

        fun process_res (id', th) =
            let
              val thy = RewriteTable.theory_of tbl
              val ac_info = Nat_Arith.times_ac_on_typ thy assnT
              val xs = th |> prop_of' |> dest_arg |> ACUtil.dest_ac_l ac_info
                          |> List.last |> dest_args |> hd
              val insts = Matcher.rewrite_match tbl (pat_xs, xs) (id', inst)

              fun process_inst ((id'', inst'), eq_th) =
                  let
                    val cv = (Conv.arg1_conv o Conv.rewr_conv o meta_sym) eq_th
                  in
                    ((id'', inst'),
                     th |> ent_r_cv (ACUtil.ac_last_conv ac_info cv))
                  end
            in
              map process_inst insts
            end
      in
        maps process_res matches
      end
    end

fun add_entail_matcher th = add_assn_matcher (true, entail_matcher th)

end  (* structure AssnMatcher. *)

val add_assn_matcher = AssnMatcher.add_assn_matcher
val add_entail_matcher = AssnMatcher.add_entail_matcher
val _ = Theory.setup (AssnMatcher.add_assn_matcher_proofsteps)
