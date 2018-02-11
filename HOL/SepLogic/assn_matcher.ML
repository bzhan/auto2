(* Matching of assertions. *)

(* Given arguments ctxt (pat, t) (id, inst), match pat with t. Assume
   pat is not a product. Produce t ==> pat(s) or t ==> pat(s) * t' for
   those in AssnMatchData. Produce pat(s) or pat(s) * t' ==> t for
   those in AssnInvMatchData.
 *)
type assn_matcher = Proof.context -> term * cterm -> id_inst -> id_inst_th list

signature ASSN_MATCHER =
sig
  val add_assn_matcher: assn_matcher -> theory -> theory
  val assn_match_term:
      Proof.context -> term * cterm -> id_inst -> id_inst_th list
  val assn_match_all:
      Proof.context -> term * cterm -> id_inst -> id_inst_th list
  val assn_match_all_strict:
      Proof.context -> term * cterm -> id_inst -> id_inst_th list
  val mod_match: Proof.context -> term * thm -> id_inst -> id_inst_th list
  val assn_matcher: item_matcher
  val triv_assn_matcher: assn_matcher
  val emp_assn_matcher: assn_matcher
  val true_assn_matcher: assn_matcher
  val add_entail_matcher: thm -> theory -> theory

  val add_assn_inv_matcher: assn_matcher -> theory -> theory
  val assn_inv_match_term:
      Proof.context -> term * cterm -> id_inst -> id_inst_th list
  val assn_inv_match_all:
      Proof.context -> term * cterm -> id_inst -> id_inst_th list
  val assn_inv_match_all_strict:
      Proof.context -> term * cterm -> id_inst -> id_inst_th list
  val mod_inv_match: Proof.context -> term * thm -> id_inst -> id_inst_th list
  val assn_inv_matcher: item_matcher
  val triv_assn_inv_matcher: assn_matcher
  val emp_assn_inv_matcher: assn_matcher

  val add_assn_matcher_proofsteps: theory -> theory
end

structure AssnMatcher : ASSN_MATCHER =
struct

open SepUtil

structure MatchData = Theory_Data (
  type T = assn_matcher list
  val empty = []
  val extend = I;
  val merge = merge (op pointer_eq)
)

structure InvMatchData = Theory_Data (
  type T = assn_matcher list
  val empty = []
  val extend = I;
  val merge = merge (op pointer_eq)
)

(* Matching in the forward direction *)

fun add_assn_matcher matcher = MatchData.map (cons matcher)

(* Assume pat is not in the form A * B. Match pat with one or more
   terms of t. Return theorem of form t ==> pat(s) * t'.
 *)
fun assn_match_term ctxt (pat, ct) (id, inst) =
    case pat of
        Var (ixn, _) =>
        let
          val t = Thm.term_of ct
        in
          [((id, Util.update_env (ixn, t) inst),
            t |> entail_triv_th ctxt |> apply_to_entail_r mult_emp_right)]
        end
      | _ =>
        let
          val thy = Proof_Context.theory_of ctxt
          fun apply_matcher matcher = matcher ctxt (pat, ct) (id, inst)

          (* th must be an entailment, and the right side must be
             pat(s), pat(s) * t', or t' * pat(s).
           *)
          fun process_res ((id, inst'), th) =
              let
                val _ = assert (is_entail (prop_of' th)) "assn_match_term"
                val (_, rhs) = th |> prop_of' |> dest_entail
                val exp_rhs = Util.subst_term_norm inst' pat
              in
                if rhs aconv exp_rhs then
                  ((id, inst'), th |> apply_to_entail_r mult_emp_right)
                else if is_times rhs andalso dest_arg1 rhs aconv exp_rhs then
                  ((id, inst'), th)
                else if is_times rhs andalso dest_arg rhs aconv exp_rhs then
                  ((id, inst'), th |> apply_to_entail_r assn_comm_cv)
                else
                  raise Fail "assn_match_term"
              end
        in
          (maps apply_matcher (MatchData.get thy))
              |> map process_res
        end

(* Match each term of pat with some term in t. Returns t ==> pat(s) * t'. *)
fun assn_match_all ctxt (pat, ct) (id, inst) =
    case pat of
        Const (@{const_name times}, _) $ A $ B =>
        let
          val insts = assn_match_all ctxt (A, ct) (id, inst)

          (* th is t ==> A(s) * t'. Match B(s) with t', with result t'
             ==> B(s) * t''. Produce t ==> (A(s) * B(s)) * t''
           *)
          fun process_inst ((id', inst'), th) =
              let
                val ct' = th |> cprop_of' |> cdest_entail |> snd |> Thm.dest_arg
                val B' = Util.subst_term_norm inst' B
                val insts' = assn_match_all ctxt (B', ct') (id', inst')

                (* th' is t' ==> B(s) * t''. *)
                fun process_inst' ((id'', inst''), th') =
                    let
                      val res = ([th, th'] MRS @{thm entail_trans2})
                                    |> apply_to_entail_r assn_assoc_sym_cv
                    in
                      ((id'', inst''), res)
                    end
              in
                map process_inst' insts'
              end
        in
          maps process_inst insts
        end
      | _ => assn_match_term ctxt (pat, ct) (id, inst)

(* Guarantees that every term in t is matched. Returns t ==> pat(s). *)
fun assn_match_all_strict ctxt (pat, ct) (id, inst) =
    let
      val inst = assn_match_all ctxt (pat, ct) (id, inst)
      fun process_inst ((id', inst'), th) =
          let
            val rhs = th |> prop_of' |> dest_entail |> snd
            val _ = assert (is_times rhs andalso
                            dest_arg1 rhs aconv Util.subst_term_norm inst' pat)
                           "assn_match_all"
          in
            if dest_arg rhs aconv emp then
              [((id', inst'), th |> apply_to_entail_r reduce_emp_right)]
            else []
          end
    in
      maps process_inst inst
    end

(* Given pat of form pat_h |= pat_P, and a theorem h |= P, match pat_h
   to h using regular matching, then match pat_P to P using assertion
   matching. Return the theorem pat_h(s) |= pat_P(s).
 *)
fun mod_match_gen strict ctxt (pat, th) (id, inst) =
    let
      val (pat_h, pat_P) = pat |> dest_mod
      val (ch, cP) = th |> cprop_of' |> cdest_mod
      val insts_h = Matcher.rewrite_match ctxt (pat_h, ch) (id, inst)

      (* eq_th is pat_h(s) == h. *)
      fun process_inst_h ((id', inst'), eq_th) =
          let
            val insts'' =
                if strict then
                  assn_match_all_strict ctxt (pat_P, cP) (id', inst')
                else
                  assn_match_all ctxt (pat_P, cP) (id', inst')
            val rewr_eq_th = eq_th |> Conv.rewr_conv |> Conv.arg1_conv

            (* ent_th is P ==> pat_P(s) * R. Obtain h |= pat_P(s) then
               pat_h(s) |= pat_P(s).
             *)
            fun process_inst ((id', inst'), ent_th) =
                [((id', inst'), ([ent_th, th] MRS @{thm entailsD})
                                    |> apply_to_thm' rewr_eq_th)]
          in
            maps process_inst insts''
          end
    in
      maps process_inst_h insts_h
    end

fun mod_match ctxt (pat, th) (id, inst) =
    mod_match_gen false ctxt (pat, th) (id, inst)

val assn_matcher =
    let
      fun pre_match pat {tname, ...} _ =
          is_mod pat andalso is_mod (Thm.term_of (the_single tname))

      fun match pat (item as {prop, ...}) ctxt (id, inst) =
          if not (pre_match pat item ctxt) then []
          else mod_match_gen true ctxt (pat, prop) (id, inst)
    in
      {pre_match = pre_match, match = match}
    end

(* Specific assertion matchers *)

(* Matcher using the theorem A ==> A. *)
fun triv_assn_matcher ctxt (pat, ct) (id, inst) =
    if pat aconv emp then []  (* leave to emp_assn_matcher *)
    else let
      val cts = ACUtil.cdest_ac assn_ac_info ct

      fun match_i i =
          let
            val ct' = nth cts i
            val insts = Matcher.rewrite_match ctxt (pat, ct') (id, inst)

            (* eq_th is of form pat(inst') == t'. *)
            fun process_inst ((id', inst'), eq_th) =
                let
                  val th = entail_triv_th ctxt (Thm.term_of ct)
                  val cv = Conv.every_conv [
                        ACUtil.move_outmost assn_ac_info (Thm.term_of ct'),
                        ACUtil.ac_last_conv
                            assn_ac_info (Conv.rewr_conv (meta_sym eq_th))]
                in
                  ((id', inst'), th |> apply_to_entail_r cv)
                end
          in
            map process_inst insts
          end
    in
      maps match_i (0 upto (length cts - 1))
    end

(* Consider the case where pat = emp. Return t ==> emp * t. *)
fun emp_assn_matcher ctxt (pat, ct) (id, inst) =
    if not (pat aconv emp) then []
    else [((id, inst), ct |> Thm.term_of |> entail_triv_th ctxt
                          |> apply_to_entail_r mult_emp_left)]

(* If pat = true, match all of t. Return t ==> emp * true. *)
fun true_assn_matcher ctxt (pat, ct) (id, inst) =
    if not (pat aconv assn_true) then []
    else [((id, inst), ct |> Thm.term_of |> entail_true_th ctxt
                          |> apply_to_entail_r mult_emp_left)]

(* We now consider the case of generating a matcher from an entailment
   theorem of a particular form.

   Given an entailment A ==> B, where B is of the form f ?xs pat_r,
   where f is a constant, and pat_r may contain additional schematic
   variables. Attempt to find a term of form f xs r within t, for the
   input term r, by matching the pattern A. For each match, return the
   implication t ==> f xs r or t ==> t' * f xs r. This function serves
   as the first step of entail_matcher.
 *)
fun entail_matcher' entail_th ctxt r ct id =
    let
      (* Match pat_r with r. *)
      val pat_r = entail_th |> prop_of' |> dest_entail |> snd |> dest_arg
      val inst_r = Matcher.rewrite_match ctxt (pat_r, Thm.cterm_of ctxt r) (id, fo_init)

      (* For each match, recursively match the instantiated version of
         A (named pat here) with t.
       *)
      fun process_inst_r ((id', inst'), eq_th) =
          let
            val entail_th' = Util.subst_thm ctxt inst' entail_th
            val pat = entail_th' |> prop_of' |> dest_arg1
            val matches = assn_match_all ctxt (pat, ct) (id', fo_init)

            (* th is of form t ==> pat(s) * t'. Convert to t ==> t' *
               pat(s). Then use entailment theorem to convert to t ==>
               t' * B. Finally, convert the argument in B to the given
               r.
             *)
            fun process_match ((id'', _), th) =
                let
                  val cv = eq_th |> Conv.rewr_conv |> Util.argn_conv 1
                                 |> ACUtil.ac_last_conv assn_ac_info
                  val th' = th |> apply_to_entail_r assn_comm_cv
                in
                  (id'', ([th', entail_th'] MRS @{thm entail_trans2})
                             |> apply_to_entail_r cv)
                end
          in
            map process_match matches
          end
    in
      maps process_inst_r inst_r
    end

(* Given entailment theorem A ==> B, with same condition as in
   entail_matcher', attempt to match pat with t, and return t ==> t' *
   pat(s). For any matching to be performed, pat must be in the form f
   pat_xs r, where pat_xs may contain schematic variables, but r
   cannot. First, find f xs r using entail_matcher', then match pat_xs
   with xs.
 *)
fun entail_matcher entail_th ctxt (pat, ct) (id, inst) =
    let
      val (f, args) = Term.strip_comb pat
      val pat_f = entail_th |> prop_of' |> dest_entail |> snd |> Term.head_of
    in
      if not (Term.aconv_untyped (f, pat_f)) orelse
         Util.has_vars (nth args 1) then []
      else let
        val (pat_xs, r) = the_pair args
        val matches = entail_matcher' entail_th ctxt r ct id

        fun process_res (id', th) =
            let
              val xs = th |> cprop_of' |> Thm.dest_arg
                          |> ACUtil.cdest_ac assn_ac_info
                          |> List.last |> Drule.strip_comb |> snd |> hd
              val insts = Matcher.rewrite_match ctxt (pat_xs, xs) (id', inst)

              fun process_inst ((id'', inst'), eq_th) =
                  let
                    val cv = eq_th |> meta_sym |> Conv.rewr_conv
                                   |> Conv.arg1_conv
                                   |> ACUtil.ac_last_conv assn_ac_info
                  in
                    ((id'', inst'), th |> apply_to_entail_r cv)
                  end
            in
              map process_inst insts
            end
      in
        maps process_res matches
      end
    end

fun add_entail_matcher th =
    let
      val (pat_f, pat_args) = th |> prop_of' |> dest_entail |> snd
                                 |> Term.strip_comb

      val _ = assert (length pat_args = 2 andalso Term.is_Const pat_f)
                     "add_entail_matcher: th must be in form A ==> f ?xs pat_r."
    in
      add_assn_matcher (entail_matcher th)
    end

(* Matching in the backward direction *)

fun add_assn_inv_matcher matcher = InvMatchData.map (cons matcher)

(* Assume pat is not in the form A * B. Match pat with one or more
   terms of t. Return theorem of form pat(s) * t' ==> t.
 *)
fun assn_inv_match_term ctxt (pat, ct) (id, inst) =
    case pat of
        Var (ixn, _) =>
        let
          val t = Thm.term_of ct
        in
          [((id, Util.update_env (ixn, t) inst),
            t |> entail_triv_th ctxt |> apply_to_entail_l mult_emp_right)]
        end
      | _ =>
        let
          val thy = Proof_Context.theory_of ctxt
          fun apply_matcher matcher = matcher ctxt (pat, ct) (id, inst)

          (* th must be an entailment, and the left side must be
             pat(s), pat(s) * t', or t' * pat(s).
           *)
          fun process_res ((id, inst'), th) =
              let
                val _ = assert (is_entail (prop_of' th)) "assn_inv_match_term"
                val (lhs, _) = th |> prop_of' |> dest_entail
                val exp_lhs = Util.subst_term_norm inst' pat
              in
                if lhs aconv exp_lhs then
                  ((id, inst'), th |> apply_to_entail_l mult_emp_right)
                else if is_times lhs andalso dest_arg1 lhs aconv exp_lhs then
                  ((id, inst'), th)
                else if is_times lhs andalso dest_arg lhs aconv exp_lhs then
                  ((id, inst'), th |> apply_to_entail_l assn_comm_cv)
                else
                  raise Fail "assn_inv_match_term"
              end
        in
          (maps apply_matcher (InvMatchData.get thy))
              |> map process_res
        end

(* Match each term of pat with some term in t. Return pat(s) * t' ==> t. *)
fun assn_inv_match_all ctxt (pat, ct) (id, inst) =
    case pat of
        Const (@{const_name times}, _) $ A $ B =>
        let
          val insts = assn_inv_match_all ctxt (A, ct) (id, inst)

          (* th is A(s) * t' ==> t. Match B(s) with t', with result
             B(s) * t'' ==> t'. Produce (A(s) * B(s)) * t'' ==> t.
           *)
          fun process_inst ((id', inst'), th) =
              let
                val ct' = th |> cprop_of' |> cdest_entail |> fst |> Thm.dest_arg
                val B' = Util.subst_term_norm inst' B
                val insts' = assn_inv_match_all ctxt (B', ct') (id', inst')

                (* th' is B(s) * t'' ==> t'. *)
                fun process_inst' ((id'', inst''), th') =
                    let
                      val res = ([th, th'] MRS @{thm entail_trans2'})
                                    |> apply_to_entail_l assn_assoc_sym_cv
                    in
                      ((id'', inst''), res)
                    end
              in
                map process_inst' insts'
              end
        in
          maps process_inst insts
        end
      | _ => assn_inv_match_term ctxt (pat, ct) (id, inst)

(* Guarantees that every term in t is matched. Returns pat(s) ==> t. *)
fun assn_inv_match_all_strict ctxt (pat, ct) (id, inst) =
    let
      val inst = assn_inv_match_all ctxt (pat, ct) (id, inst)
      fun process_inst ((id', inst'), th) =
          let
            val lhs = th |> prop_of' |> dest_entail |> fst
            val _ = assert (is_times lhs andalso
                            dest_arg1 lhs aconv Util.subst_term_norm inst' pat)
                           "assn_match_all"
          in
            if dest_arg lhs aconv emp then
              [((id', inst'), th |> apply_to_entail_l reduce_emp_right)]
            else []
          end
    in
      maps process_inst inst
    end

(* Given pat of form ~(pat_h |= pat_P), and a theorem ~(h |= P), match
   pat_h to h using regular matching, then match pat_P to P using
   inverted assertion matching. Return the theorem ~(pat_h(s) |=
   pat_P(s)).
 *)
fun mod_inv_match_gen strict ctxt (pat, th) (id, inst) =
    let
      val (pat_h, pat_P) = pat |> dest_not |> dest_mod
      val (ch, cP) = th |> cprop_of' |> Thm.dest_arg |> cdest_mod
      val insts_h = Matcher.rewrite_match ctxt (pat_h, ch) (id, inst)

      (* eq_th is pat_h(s) == h. *)
      fun process_inst_h ((id', inst'), eq_th) =
          let
            val insts'' =
                if strict then
                  assn_inv_match_all_strict ctxt (pat_P, cP) (id', inst')
                else
                  assn_inv_match_all ctxt (pat_P, cP) (id', inst')
            val rewr_eq_th = eq_th |> Conv.rewr_conv |> Conv.arg1_conv
                                   |> Conv.arg_conv

            (* ent_th is pat_P(s) ==> P. Obtain ~(h |= pat_P(s)) then
               ~(pat_h(s) |= pat_P(s)).
             *)
            fun process_inst ((id', inst'), ent_th) =
                [((id', inst'), ([ent_th, th] MRS @{thm entails_invD})
                                    |> apply_to_thm' rewr_eq_th)]
          in
            maps process_inst insts''
          end
    in
      maps process_inst_h insts_h
    end

fun mod_inv_match ctxt (pat, th) (id, inst) =
    mod_inv_match_gen false ctxt (pat, th) (id, inst)

val assn_inv_matcher =
    let
      fun is_neg_mod t = is_neg t andalso is_mod (dest_not t)
      fun pre_match pat {tname, ...} _ =
          let
            val t = tname |> the_single |> Thm.term_of
          in
            is_neg_mod pat andalso is_neg_mod t andalso
            (pat |> dest_not |> dest_mod |> fst)
                aconv (t |> dest_not |> dest_mod |> fst)
          end

      fun match pat (item as {prop, ...}) ctxt (id, inst) =
          if not (pre_match pat item ctxt) then []
          else mod_inv_match_gen true ctxt (pat, prop) (id, inst)
    in
      {pre_match = pre_match, match = match}
    end

(* Specific inverted assertion matchers *)

(* Matcher using the theorem A ==> A. *)
fun triv_assn_inv_matcher ctxt (pat, ct) (id, inst) =
    if pat aconv emp then []  (* leave to emp_assn_matcher *)
    else let
      val cts = ACUtil.cdest_ac assn_ac_info ct

      fun match_i i =
          let
            val ct' = nth cts i
            val insts = Matcher.rewrite_match ctxt (pat, ct') (id, inst)

            (* eq_th is of form pat(inst') == t'. *)
            fun process_inst ((id', inst'), eq_th) =
                let
                  val th = entail_triv_th ctxt (Thm.term_of ct)
                  val cv = Conv.every_conv [
                        ACUtil.move_outmost assn_ac_info (Thm.term_of ct'),
                        ACUtil.ac_last_conv
                            assn_ac_info (Conv.rewr_conv (meta_sym eq_th))]
                in
                  ((id', inst'), th |> apply_to_entail_l cv)
                end
          in
            map process_inst insts
          end
    in
      maps match_i (0 upto (length cts - 1))
    end

(* Consider the case where pat = emp. Return emp * t ==> t. *)
fun emp_assn_inv_matcher ctxt (pat, ct) (id, inst) =
    if not (pat aconv emp) then []
    else [((id, inst), ct |> Thm.term_of |> entail_triv_th ctxt
                          |> apply_to_entail_l mult_emp_left)]

val add_assn_matcher_proofsteps =
    fold ItemIO.add_prop_matcher [
      (TY_PROP, assn_matcher), (TY_PROP, assn_inv_matcher)

    ] #> fold add_assn_matcher [
      triv_assn_matcher, emp_assn_matcher, true_assn_matcher

    ] #> fold add_assn_inv_matcher [
      triv_assn_inv_matcher, emp_assn_inv_matcher
    ]

end  (* structure AssnMatcher. *)

val add_assn_matcher = AssnMatcher.add_assn_matcher
val add_entail_matcher = AssnMatcher.add_entail_matcher
val _ = Theory.setup (AssnMatcher.add_assn_matcher_proofsteps)
