(* Proof steps for separation logic. *)

signature SEP_LOGIC =
sig
  val assnT: typ
  val pheapT: typ
  val dest_entail: term -> term * term
  val mk_star: term * term -> term
  val mk_mod: term * term -> term
  val heap_of_mod_th: thm -> term * term
  val is_pure_assn: term -> bool
  val has_pure_assn: theory -> term -> bool
  val normalize_assn_cv: Proof.context -> conv
  val normalize_mod_cv: Proof.context -> conv

  val add_forward_ent_prfstep_ctxt: thm -> Proof.context -> Proof.context
  val frame_entail: proofstep

  val TY_CODE_POS: string
  val TY_CODE_POS_MATCH: string
  val TY_SUCCESS_RUN: string
  val output_code_pos_fn: item_output
  val output_code_pos_match_fn: item_output
  val output_success_run_fn: item_output
  val code_pos_typed_matcher: item_matcher

  val find_proc_def: Proof.context -> term -> thm option
  val heap_preservingI: proofstep
  val heap_preserving_effectD: thm -> proofstep
  val add_heap_preserving_thm: thm -> Proof.context -> Proof.context
  val init_code_pos: proofstep
  val find_heap_preserving_th: Proof.context -> term -> thm option
  val next_code_pos_ritems:
      Proof.context -> thm -> thm -> thm -> thm * raw_item list
  val match_code_pos: proofstep
  val dest_bind_code_pos: proofstep
  val disj_match_code_pos: proofstep
  val convert_code_pos_match: proofstep
  val use_prec_thms: RewriteTable.rewrite_table -> thm -> thm -> thm
  val match_code_pos_success: proofstep
  val match_pure_assn: proofstep
  val add_match_code_pos_emp_prfstep_ctxt: thm -> Proof.context -> Proof.context
  val add_match_code_pos_emp_prfstep: thm -> theory -> theory
  val match_code_pos_create_case_gen: string * term -> proofstep
  val add_match_code_pos_create_case_ctxt: thm -> Proof.context -> Proof.context
  val add_match_code_pos_create_case: thm -> theory -> theory
  val match_code_pos_heap: proofstep
  val next_code_pos_prfstep: thm -> proofstep
  val add_next_code_pos_prfstep_ctxt: thm -> Proof.context -> Proof.context
  val add_next_code_pos_prfstep: thm -> theory -> theory
  val add_next_code_pos_direct_prfstep_ctxt:
      thm -> Proof.context -> Proof.context
  val add_next_code_pos_direct_prfstep: thm -> theory -> theory
  val ac_shadow_mod: proofstep

  val add_sep_logic_proofsteps: theory -> theory
end;

structure Sep_Logic : SEP_LOGIC =
struct

val assnT = @{typ assn}
val heapT = @{typ heap}
val addrsT = @{typ "nat set"}
val pheapT = @{typ pheap}
val emp = @{term emp}

(* Deconstruct A ==>_A B into (A, B). *)
fun dest_entail t =
    case t of
        Const (@{const_name entails}, _) $ A $ B => (A, B)
      | _ => raise AUTO2T ("dest_entail: unexpected t.", [t])

(* Given pair of assertions (A, B), form the assertion A * B. *)
fun mk_star (A, B) =
    Const (@{const_name times}, assnT --> assnT --> assnT) $ A $ B

(* Deconstruct h |= P into (h, P). *)
fun dest_mod t =
    case t of
        Const (@{const_name models}, _) $ h $ P => (h, P)
      | _ => raise AUTO2T ("dest_mod: unexpected t.", [t])

(* Given pheap h and assertion P, form the proposition h |= P. *)
fun mk_mod (h, P) =
    Const (@{const_name models}, assnT --> pheapT --> boolT) $ h $ P

(* Given term h |= P, apply conversion on P. *)
val mod_assn_conv = Conv.arg_conv

(* Given theorem (h, as) |= P, return the pair of terms (h, as). *)
fun heap_of_mod_th mod_th =
    mod_th |> prop_of' |> dest_mod |> fst |> dest_binop |> snd

(* Whether t is of the form \<up>(b). *)
fun is_pure_assn t =
    case t of
        Const (@{const_name pure_assn}, _) $ _ => true
      | _ => false

(* Given t of form t1 * ... * tn, check whether any of them is of the
   form \<up>(b).
 *)
fun has_pure_assn thy t =
    let
      val ac_info = Nat_Arith.times_ac_on_typ thy assnT
      val ts = ACUtil.dest_ac_total ac_info t
    in
      exists is_pure_assn ts
    end

(* Given t of form t1 * ... * tn, remove those ti that are pure
   assertions and return the product of the remaining terms.
 *)
fun strip_pure_assn thy t =
    let
      val ac_info = Nat_Arith.times_ac_on_typ thy assnT
    in
      t |> ACUtil.dest_ac_total ac_info
        |> filter_out is_pure_assn
        |> ACUtil.list_ac_l ac_info
    end

(* Normalization function for assertions. *)
fun normalize_assn_cv ctxt ct =
    let
      val thy = Thm.theory_of_cterm ct
      val ac_info = Nat_Arith.times_ac_on_typ thy assnT
      fun pure_ord (t, s) = not (is_pure_assn t) andalso is_pure_assn s
      val rewr_distrib_ex =
          Conv.every_conv (
            map (Conv.try_conv o rewr_obj_eq o obj_sym) [
              @{thm ex_distrib_star}, @{thm ex_distrib_star_l}])

      fun distrib_ex ctxt ct =
          Conv.top_conv (K rewr_distrib_ex) ctxt ct

      fun within_ex_assn cv ctxt ct =
          case Thm.term_of ct of
              Const (@{const_name ex_assn}, _) $ _ =>
              Conv.binder_conv ((within_ex_assn cv) o snd) ctxt ct
            | _ => cv ct
    in
      Conv.every_conv [
        distrib_ex ctxt,
        within_ex_assn (ACUtil.normalize_assoc_l ac_info) ctxt,
        within_ex_assn (ACUtil.normalize_unit ac_info) ctxt,
        within_ex_assn (ACUtil.normalize_comm_l ac_info pure_ord) ctxt] ct
    end

val mod_cv_thms =
    [@{thm mod_pure'}, @{thm mod_pure_star_dist}, @{thm mod_ex_dist},
     @{thm mod_ex_distrib_star}]

(* Normalize a statement of the form h |= P, which can appear as
   either fact or goal. Begin by normalizing P, then use various
   rewriting rules for mod.
 *)
fun normalize_mod_cv ctxt ct =
    let
      val mod_cv =
          Conv.every_conv (map (Conv.try_conv o rewr_obj_eq) mod_cv_thms)
    in
      Conv.every_conv [
        mod_assn_conv (normalize_assn_cv ctxt),
        Conv.top_conv (K mod_cv) ctxt] ct
    end

(* Proofsteps normalizing assertions. *)
fun normalize_mod_cv_prfstep nm pat =
    prfstep_custom
        nm [WithProp pat] PRIORITY_URGENT
        (fn ((id, _), ths) => fn _ => fn {ctxt, ...} =>
            let
              val th = the_single ths
              val th' =
                  if is_neg (prop_of' th) then
                    apply_to_thm' (Conv.arg_conv (normalize_mod_cv ctxt)) th
                  else
                    apply_to_thm' (normalize_mod_cv ctxt) th
            in
              if not (Thm.prop_of th aconv Thm.prop_of th') then
                [Update.thm_update (id, th')]
              else []
            end)

val normalize_mod_cv_prfsteps =
    let
      fun pos_step th = normalize_mod_cv_prfstep
                            (name_of_thm th ^ "@norm")
                            (th |> prop_of' |> HOLogic.dest_eq |> fst)
      fun neg_step th =
          normalize_mod_cv_prfstep
              (name_of_thm th ^ "@negnorm")
              (th |> prop_of' |> HOLogic.dest_eq |> fst |> get_neg)
    in
      map pos_step mod_cv_thms @ map neg_step mod_cv_thms
    end

fun forward_ent_prfstep ent_th =
    let
      val (A, _) = dest_entail (prop_of' ent_th)
      val pat = mk_mod (Var (("h", 0), pheapT),
                        mk_star (A, Var (("Ru", 0), assnT)))
      val name = name_of_thm ent_th ^ "@ent"
      val descs = [WithFact pat]
      fun prfstep_fn ((id, _), ths) _ {ctxt, ...} =
          let
            val res_th = ([ent_th, the_single ths] MRS @{thm entailsD'})
                             |> apply_to_thm' (normalize_mod_cv ctxt)
          in
            [Update.thm_update (id, res_th)]
          end
    in
      prfstep_custom name descs PRIORITY_ADD prfstep_fn
    end

fun add_forward_ent_prfstep_ctxt ent_th ctxt =
    ctxt |> add_prfstep_ctxt (forward_ent_prfstep ent_th)

(* Here item1 is a DISJ item of form A ==>_A B, where A and B may
   contain schematic variables. Match pattern h |= A * Ru with item2,
   and produce h |= B * Ru for each match.
 *)
fun frame_entail_fn rtype {ctxt, ...} {id, tname, prop = th1, ...} item2 =
    let
      val (_, subs) = Logic_ProofSteps.dest_tname_of_disj tname
    in
      if length subs > 1 then [] else
      let
        val (A, _) = dest_entail (the_single subs)
        val pat = mk_mod (Var (("h", 0), pheapT),
                          mk_star (A, Var (("Ru", 0), assnT)))
        val insts = get_insts (PropMatch pat) item2 rtype (id, fo_init)
        fun inst_to_updt ((id', _), th) =
            let
              val th' = ([th1, th] MRS @{thm entailsD'})
                            |> apply_to_thm' (normalize_mod_cv ctxt)
            in
              [Update.thm_update (id', th')]
            end
      in
        maps inst_to_updt insts
      end
    end

val frame_entail =
    {name = "frame_entail",
     args = [TypedMatch (TY_DISJ, @{term_pat "entails ?A ?B"}),
             PropMatch @{term_pat "?h |= ?P"}],
     priority = PRIORITY_ADD,
     func = TwoStep frame_entail_fn}

fun dest_hoare_triple t =
    case t of
        Const (@{const_name hoare_triple}, _) $ P $ c $ Q => (P, c, Q)
      | _ => raise AUTO2 "dest_hoare_triple"

fun is_bind_cmd t =
    case t of
        Const (@{const_name bind}, _) $ _ $ _ => true
      | _ => false

fun dest_bind t =
    case t of
        Const (@{const_name bind}, _) $ c1 $ rest => (c1, rest)
      | _ => raise AUTO2 "dest_cmd"

(* CODE_POS items indicate current position in the program. Here tname
   is the tuple (h, as, c), where (h, as) is the current heap and c is
   the first of the remaining commands.
 *)
val TY_CODE_POS = "CODE_POS"

(* CODE_POS_MATCH item indicate current position together with a hoare
   triple (possibly with schematic variables; either from existing
   theorem or induction hypothesis). The tname is (h, as, c,
   is_success, P, Q), where is_success is a boolean term indicating
   whether the current command is known to be successful, and (P, Q)
   are the pre/post-condition of the hoare triple.
 *)
val TY_CODE_POS_MATCH = "CODE_POS_MATCH"

(* SUCCESS_RUN items indicate successful execution of a single
   command. Here tname is the tuple (h, as, c, vars ...), where vars
   are the new variables in the post-condition (may be none). prop is
   the conjunction of pre-condition, success_run fact, and
   post-condition.
 *)
val TY_SUCCESS_RUN = "SUCCESS_RUN"

fun output_code_pos_fn ctxt (tname, th) =
    let
      val is_bind = th |> conj_left_th |> prop_of' |> strip_comb |> snd |> hd
                       |> is_bind_cmd
    in
      "CODE_POS " ^ (if is_bind then "" else "(last) ") ^
      (tname |> pretty_term ctxt |> str)
    end

fun output_code_pos_match_fn ctxt (tname, _) =
    "CODE_POS_MATCH " ^ (tname |> pretty_term ctxt |> str)

fun output_success_run_fn ctxt (tname, _) =
    "SUCCESS_RUN " ^ (tname |> pretty_term ctxt |> str)

(* Common matcher for CODE_POS, CODE_POS_MATCH, and SUCCESS_RUN. When
   pattern is a tuple of n terms, match the first n terms of tname.
 *)
val code_pos_typed_matcher =
    let
      (* Check pat contains at least as many terms as tname. *)
      fun pre_match pat {tname, ...} tbl =
          let
            val pats = HOLogic.strip_tuple pat
            val tnames = HOLogic.strip_tuple tname
          in
            if length pats > length tnames then false
            else forall (Matcher.pre_match tbl)
                        (pats ~~ take (length pats) tnames)
          end

      (* Use equalities to convert prop to prop'. *)
      fun match pat {tname, prop, ...} (tbl as {ctxt, ...}) (id, inst) =
          let
            val pats = HOLogic.strip_tuple pat
            val tnames = take (length pats) (HOLogic.strip_tuple tname)
            val pairs = map (pair false) (pats ~~ tnames)

            val insts = Matcher.rewrite_match_list tbl pairs (id, inst)
            fun process_inst (inst, ths) =
                let
                  val obj_eqs = map (obj_sym o to_obj_eq) ths
                  val prop' = prop |> apply_to_thm (
                        Conv.every_conv (map (rewr_obj_eq_top ctxt) obj_eqs))
                in
                  (inst, prop')
                end
          in
            map process_inst insts
          end
    in
      {pre_match = pre_match, match = match}
    end

(* Find definition for a given procedure among the theorems
   sep_proc_defs. Return NONE or SOME (c == c').
 *)
fun find_proc_def ctxt c =
    let
      val ths = Named_Theorems.get ctxt @{named_theorems sep_proc_defs}
      fun rewr_cv th = if is_meta_eq_thm th then Conv.rewr_conv th
                       else rewr_obj_eq th
    in
      SOME (Conv.first_conv (map rewr_cv ths) (cert ctxt c))
      handle CTERM _ => NONE
    end

(* To prove facts of form heap_preserving c (as initial goal), try to
   expand c, then use definition of heap_preserving.
 *)
val heap_preservingI =
    prfstep_custom
        "heap_preservingI"
        [WithGoal @{term_pat "heap_preserving ?c"}]
        PRIORITY_SHADOW
        (fn ((id, _), ths) => fn items => fn {ctxt, ...} =>
            let
              val th = the_single ths
              val c = th |> prop_of' |> get_neg |> Term.dest_comb |> snd
              val th' =
                  case find_proc_def ctxt c of
                      NONE => th
                    | SOME eq =>
                      th |> apply_to_thm' (
                        Conv.arg_conv (Conv.arg_conv (Conv.rewr_conv eq)))
              val th_res =
                  th' |> apply_to_thm' (
                    Conv.arg_conv (rewr_obj_eq @{thm heap_preserving_def}))
            in
              [Update.thm_update (id, th_res),
               Update.ShadowItem {id = id, item = the_single items}]
            end)

(* Given heap_preserving c, conclude h = h' from effect c h h' r. *)
fun heap_preserving_effectD presv_th =
    let
      val name = (name_of_thm presv_th) ^ "effectD"
      val pat_c = presv_th |> prop_of' |> Term.dest_comb |> snd
      val cT = fastype_of pat_c |> dest_Type |> snd |> the_single
      val pat =
          Const (@{const_name effect},
                 Type ("Heap", [cT]) --> heapT --> heapT --> cT --> boolT) $
                pat_c $ Var (("h", 0), heapT) $ Var (("h'", 0), heapT) $
                Var (("r", 0), cT)
      fun prfstep_fn ((id, _), ths) _ _ =
          let
            val res_th =
                [presv_th, the_single ths] MRS @{thm heap_preserving_effectD}
          in
            [Update.thm_update (id, res_th)]
          end
    in
      prfstep_custom name [WithFact pat] PRIORITY_ADD prfstep_fn
    end

(* Add the heap_preserving_effectD proofstep (for proving future
   heap_preserving results).
 *)
fun add_heap_preserving_thm presv_th ctxt =
    let
      val prfstep = heap_preserving_effectD presv_th
    in
      ctxt |> add_prfstep_ctxt prfstep
    end

(* Given theorem of form ~<P> c <Q>, attempt to expand the definition
   of c, using find_proc_def to lookup definitions.
 *)
fun rewrite_hoare_triple_goal ctxt th =
    let
      val (_, c, _) = dest_hoare_triple (get_neg (prop_of' th))
    in
      case find_proc_def ctxt c of
          NONE => th
        | SOME eq =>
          th |> apply_to_thm' (
            Conv.arg_conv (Conv.arg1_conv (Conv.rewr_conv eq)))
    end

(* Given fact of form h |= P, normalize, then use apply_exists when
   necessary.
 *)
fun mod_fact_ritems ctxt mod_th =
    let
      val mod_th' = apply_to_thm' (normalize_mod_cv ctxt) mod_th
      val nms = Update.get_apply_exists_nms mod_th'
    in
      if length nms = 0 then ([], mod_th')
      else Update.apply_exists_ritems mod_th' ctxt nms
    end

val init_code_pos =
    prfstep_custom
        "init_code_pos"
        [WithProp @{term_pat "~<?P> ?c <?Q>"}]
        PRIORITY_ADD
        (fn ((id, _), ths) => fn _ => fn {ctxt, ...} =>
            let
              (* First step, replace c by its definition in goal. *)
              val th = rewrite_hoare_triple_goal ctxt (the_single ths)

              val ex_th = th RS @{thm hoare_tripleI}
              val nms = map Name.internal ["h", "as", "\<sigma>", "r"]
              val (ritems, res_th) = Update.apply_exists_ritems ex_th ctxt nms

              (* The pair is (h_, as_) |= P and what is to be placed
                 into the CODE_POS item.
               *)
              val (modP_th, code_pos_th) =
                  (conj_left_th res_th, conj_right_th res_th)

              val (_, c, _) = dest_hoare_triple (get_neg (prop_of' th))
              val is_bind = is_bind_cmd c
              val c1 = if is_bind then fst (dest_bind c) else c

              val (h_t, as_t) = heap_of_mod_th modP_th
              val tname = HOLogic.mk_tuple [h_t, as_t, c1]

              val (ritems_P, modP_th') = mod_fact_ritems ctxt modP_th
              val ritems' = ritems @ ritems_P @
                            [Update.thm_to_ritem modP_th',
                             Fact (TY_CODE_POS, tname, code_pos_th)]
            in
              [Update.AddItems {id = id, raw_items = ritems'}]
            end)

(* Find heap preserving theorem for a command c, return NONE or SOME
   (heap_preserving c).
 *)
fun find_heap_preserving_th ctxt c =
    let
      val ths = Named_Theorems.get ctxt @{named_theorems sep_heap_presv_thms}
      fun process_th th =
          let
            val pat = th |> prop_of' |> Term.dest_comb |> snd
            val inst = pattern_fo_match ctxt (pat, c)
          in
            SOME (th |> subst_thm ctxt inst)
          end
          handle Pattern.MATCH => NONE
    in
      get_first process_th ths
    end

(* Produce the next CODE_POS item, as well as new variables and facts. *)
fun next_code_pos_ritems ctxt code_pos_th mod_th hoare_th =
    let
      val (run_th, all_th) =
          (conj_left_th code_pos_th, conj_right_th code_pos_th)

      (* Find current command, decompose into c1 or c1 ; c2 ... ; cn. *)
      val cur_cmd = run_th |> prop_of' |> strip_comb |> snd |> hd
      val is_bind = is_bind_cmd cur_cmd
      val c1 = if is_bind then fst (dest_bind cur_cmd) else cur_cmd
      val heap_preserve_opt = find_heap_preserving_th ctxt c1

      val (P, _, _) = dest_hoare_triple (prop_of' hoare_th)

      (* Get (h, as) |= emp * R from (h, as) |= R. *)
      fun mult_emp_left th =
          th |> apply_to_thm' ((mod_assn_conv o rewr_obj_eq o obj_sym)
                               @{thm assn_one_left})

      (* When conclusion is of the form (h, as) |= Q * emp, reduce to
         (h, as) |= Q.
       *)
      fun reduce_emp_right th =
          th |> apply_to_thm (
            (concl_conv o HOLogic.Trueprop_conv o Conv.try_conv o
             mod_assn_conv o rewr_obj_eq) @{thm mult_1_right})

      (* Given theorem of form h |= Q & b_1 & ... & b_k, return the
         mod portion h |= Q. We assume that portion is the left-most
         assertion.
       *)
      fun get_mod_part th =
          let
            val ths = split_conj_th th
          in
            if length ths > 1 then get_mod_part (hd ths)
            else the_single ths
          end

      val mod_th' = if P aconv emp then mult_emp_left mod_th else mod_th
      val (h_t, as_t) = heap_of_mod_th mod_th'
    in
      (* Case where the CODE_POS item has a composite command do { c1;
         c2 ; ... ; cn } (intermediate step).
       *)
      if is_bind then let
        val ex_th = [hoare_th, mod_th', run_th] MRS @{thm hoare_tripleE''}
        val ex_th' = if is_none heap_preserve_opt then ex_th
                     else [the (heap_preserve_opt), ex_th]
                              MRS @{thm hoare_tripleE''_preserve}

        (* Below we will use r_, h_, and as_ to denote the new
           variables.
         *)
        val nms = if is_some heap_preserve_opt then [Name.internal "r"]
                  else map Name.internal ["r", "h", "as"]
        val (ritems, res_th) = Update.apply_exists_ritems ex_th' ctxt nms

        (* Output res_th has three parts:

           - run_rest_th: run (c2 ; ... ; cn) (Some h_) \sigma r

           - modQ_th: (h_, as_) |= Q * P'

           - success_th: success c1 h as h_ as_ r_

         *)
        val (run_rest_th, modQ_th, success_th) =
            the_triple (split_conj_th res_th)
        val modQ_th = reduce_emp_right modQ_th

        (* Extract c2 ; ... ; cn *)
        val rest_c = run_rest_th |> prop_of' |> strip_comb |> snd |> hd
        val next_is_bind = is_bind_cmd rest_c
        val rest_c1 = if next_is_bind then fst (dest_bind rest_c) else rest_c

        (* Extract (h_, as_) (or just (h, as) if heap preserving). *)
        val (next_h_t, next_as_t) = heap_of_mod_th modQ_th

        (* Use success_th to update all_th. *)
        val next_all_th = [success_th, all_th] MRS @{thm success_run_next}

        (* Form tname and prop of the new CODE_POS item. *)
        val tname = HOLogic.mk_tuple [next_h_t, next_as_t, rest_c1]
        val next_code_pos_th = [run_rest_th, next_all_th] MRS @{thm conjI}

        (* ritems for modQ_th. *)
        val (ritems_Q, modQ_th') = mod_fact_ritems ctxt modQ_th

        (* success_run item. vars are the new data variables introduced. *)
        val vars = maps (fn ritem => case ritem of Fact ("VAR", v, _) => [v]
                                                 | _ => [])
                        ritems_Q
        val tname_run = HOLogic.mk_tuple (h_t :: as_t :: c1 :: vars)
        val prop_run =
            [mod_th', [success_th, get_mod_part modQ_th'] MRS @{thm conjI}]
                MRS @{thm conjI}
        val success_run_ritem = Fact (TY_SUCCESS_RUN, tname_run, prop_run)
        val next_code_pos_ritem = Fact (TY_CODE_POS, tname, next_code_pos_th)
      in
        (modQ_th', ritems @ ritems_Q @ [success_run_ritem, next_code_pos_ritem])
      end
      (* Case where the command is not composite (last step). *)
      else let
        val ex_th = [hoare_th, mod_th', run_th] MRS @{thm hoare_tripleE'}
        val ex_th' = if is_none heap_preserve_opt then ex_th
                     else [the (heap_preserve_opt), ex_th]
                              MRS @{thm hoare_tripleE'_preserve}

        (* Below we will use h_ and as_ to denote the new variables. *)
        val nms = if is_some heap_preserve_opt then []
                  else map Name.internal ["h", "as"]
        val (ritems, res_th) = Update.apply_exists_ritems ex_th' ctxt nms

        (* The pair is:

           - modQ_th: (h_, as_) |= Q * P'

           - rest_th: \sigma = Some h_ & success_run c h as h_ as_ r

         *)
        val (modQ_th, rest_th) = (conj_left_th res_th, conj_right_th res_th)
        val modQ_th = reduce_emp_right modQ_th

        (* \sigma = Some h_ & success_run c h as h_ as_ r ==> ... *)
        val vars = [Var (("h_", 0), heapT), Var (("as_", 0), addrsT)]
        val all_th' = all_th |> apply_to_thm (to_meta_all_conv ctxt)
                             |> fold Thm.forall_elim (map (cert ctxt) vars)
                             |> apply_to_thm to_meta_imp_conv
        val Q_goal =
            (rest_th RS all_th')
                |> apply_to_thm' (Conv.arg_conv (normalize_mod_cv ctxt))

        (* ritems for modQ_th. *)
        val (ritems_Q, modQ_th') = mod_fact_ritems ctxt modQ_th

        (* success_run item. *)
        val success_th = conj_right_th rest_th
        val vars = maps (fn ritem => case ritem of Fact ("VAR", v, _) => [v]
                                                 | _ => [])
                        ritems_Q
        val tname_run = HOLogic.mk_tuple (h_t :: as_t :: c1 :: vars)
        val prop_run =
            [mod_th', [success_th, get_mod_part modQ_th'] MRS @{thm conjI}]
                MRS @{thm conjI}
        val success_run_ritem = Fact (TY_SUCCESS_RUN, tname_run, prop_run)
      in
        (modQ_th',
         ritems @ ritems_Q @ [success_run_ritem, Update.thm_to_ritem Q_goal])
      end
    end

(* Matching a CODE_POS_MATCH item with tname (h, as, c, false, P, Q)
   to propositions (h, as) |= P * Ru (or R if P is emp), and produce
   the next CODE_POS and SUCCESS_RUN items.
 *)
fun match_code_pos_fn rtype {ctxt, ...} item1 item2 =
    let
      val thy = Proof_Context.theory_of ctxt
      val {id, tname, prop, ...} = item1
      val (h_t, as_t) = the_pair (take 2 (HOLogic.strip_tuple tname))
      val (hoare_th, code_pos_th) = (conj_left_th prop, conj_right_th prop)
      val (P, _, _) = dest_hoare_triple (prop_of' hoare_th)
    in
      if has_pure_assn thy P then []
      else let
        val P_pat = if P aconv emp then Var (("R", 0), assnT)
                    else mk_star (P, Var (("Ru", 0), assnT))
        val mod_pat = mk_mod (HOLogic.mk_tuple [h_t, as_t], P_pat)
        val insts = get_insts (PropMatch mod_pat) item2 rtype (id, fo_init)
        fun inst_to_updt ((id', _), mod_th) =
            let
              val (_, ritems) =
                  next_code_pos_ritems ctxt code_pos_th mod_th hoare_th
            in
              Update.AddItems {id = id', raw_items = ritems}
            end
      in
        map inst_to_updt insts
      end
    end

val match_code_pos =
    {name = "match_code_pos",
     args = [TypedMatch (TY_CODE_POS_MATCH, @{term_pat "(?h, ?as, ?c, False)"}),
             PropMatch @{term_pat "(?h, ?as) |= ?P"}],
     priority = PRIORITY_ADD,
     func = TwoStep match_code_pos_fn}

(* Given CODE_POS item with parameters (h, as, c), where c can be
   rewritten as c1 ; c2 ; ... ; cn (for example, using rewriting rules
   for if or case), update c to c1 and modify the prop accordingly.
 *)
val dest_bind_code_pos =
    prfstep_custom
        "dest_bind_code_pos"
        [WithItem (TY_CODE_POS, @{term_pat "(?h, ?as, bind ?c ?c')"})]
        PRIORITY_SHADOW
        (fn ((id, _), ths) => fn items => fn _ =>
            let
              val th = the_single ths
              val (run_th, _) = (conj_left_th th, conj_right_th th)
              val new_c = run_th |> prop_of' |> strip_comb |> snd |> hd
              val new_is_bind = is_bind_cmd new_c
              val new_c1 = if new_is_bind then fst (dest_bind new_c) else new_c
              val {tname, ...} = the_single items
              val (h_t, as_t, _) = the_triple (HOLogic.strip_tuple tname)
              val tname' = HOLogic.mk_tuple [h_t, as_t, new_c1]

              val ritem = Fact (TY_CODE_POS, tname', th)
            in
              [Update.AddItems {id = id, raw_items = [ritem]},
               Update.ShadowItem {id = id, item = the_single items}]
            end)

(* Here item1 is a DISJ item of form <P> c <Q>, where P, c, and Q may
   contain schematic variables. item2 is a CODE_POS item (h, as,
   c1). Match pattern c with c1, and produce a CODE_POS_MATCH item of
   form (h, as, P) containing the instantiated hoare triple as well as
   theorems from item2.
 *)
fun disj_match_code_pos_fn rtype _ {id, tname, prop = th1, ...} item2 =
    let
      val (_, subs) = Logic_ProofSteps.dest_tname_of_disj tname
      val (tbl as {lat, ...}) = RewriteTable.table_of_rtype rtype
      val thy = RewriteTable.theory_of tbl
      val _ = assert (length subs = 1)
                     "disj_match_code_pos_fn: unexpected DISJ."
      val (_, c, _) = dest_hoare_triple (the_single subs)
      val {id = id', tname = tname2, prop = th2, ...} = item2
      val (h_t, as_t, c1) = the_triple (HOLogic.strip_tuple tname2)
      val id'' = BoxID.merge_boxes lat (id, id')
      val insts = (Matcher.rewrite_match tbl (c, c1) (id'', fo_init))
                      |> RewriteTable.replace_id_for_type rtype
      fun process_inst ((id''', inst), eq_th) =
          let
            (* Substitute and rewrite command to c1. *)
            val th1' =
                th1 |> subst_thm_thy thy inst
                    |> apply_to_thm' (Conv.arg1_conv (Conv.rewr_conv eq_th))
            val (P', _, Q') = dest_hoare_triple (prop_of' th1')
            val new_tname =
                HOLogic.mk_tuple [h_t, as_t, c1, term_of_bool false, P', Q']
            val new_prop = [th1', th2] MRS @{thm conjI}
            val ritem = Fact (TY_CODE_POS_MATCH, new_tname, new_prop)
          in
            [Update.AddItems {id = id''', raw_items = [ritem]}]
          end
    in
      maps process_inst insts
    end

(* Note we will be matching the instantiations of ?c and ?c' in the
   proofstep, so they may take different values in the pre-filter.
 *)
val disj_match_code_pos =
    {name = "disj_match_code_pos",
     args = [TypedMatch (TY_DISJ, @{term_pat "<?P> ?c <?Q>"}),
             TypedMatch (TY_CODE_POS, @{term_pat "(?h, ?as, ?c')"})],
     priority = PRIORITY_ADD,
     func = TwoStep disj_match_code_pos_fn}

(* Match a proposition <P> c <Q> (without schematic variables) with a
   CODE_POS item (h, as, c). Produce CODE_POS_MATCH item of form (h,
   as, P) (similar to disj_match_code_pos).
 *)
val prop_match_code_pos =
    prfstep_custom
        "prop_match_code_pos"
        [WithFact @{term_pat "<?P> ?c::?'a Heap <?Q>"},
         WithItem (TY_CODE_POS, @{term_pat "(?h, ?as, ?c::?'a Heap)"})]
        PRIORITY_ADD
        (fn ((id, inst), ths) => fn _ => fn _ =>
            let
              val P = lookup_inst inst "P"
              val Q = lookup_inst inst "Q"
              val h_t = lookup_inst inst "h"
              val as_t = lookup_inst inst "as"
              val c = lookup_inst inst "c"
              val tname =
                  HOLogic.mk_tuple [h_t, as_t, c, term_of_bool false, P, Q]
              val prop = ths MRS @{thm conjI}
              val ritem = Fact (TY_CODE_POS_MATCH, tname, prop)
            in
              [Update.AddItems {id = id, raw_items = [ritem]}]
            end)

(* item1 is CODE_POS_MATCH item with tname (h, as, c, false, P, Q),
   item2 is SUCCESS_RUN item with tname (h, as, c). If the
   pre-condition contained in the SUCCESS_RUN item matches P
   (disregarding pure assertions), convert the former item to (h, as,
   c, true, P, Q). Otherwise discard the former item (this case to be
   implemented).
 *)
val convert_code_pos_match =
    prfstep_custom
        "convert_code_pos_match"
        [WithItem (TY_CODE_POS_MATCH,
                   @{term_pat "(?h, ?as, ?c, False, ?P, ?Q)"}),
         WithItem (TY_SUCCESS_RUN, @{term_pat "(?h, ?as, ?c)"})]
        PRIORITY_SHADOW
        (fn ((id, inst), ths) => fn items => fn _ =>
            let
              val tname = HOLogic.mk_tuple (
                    (map (lookup_inst inst) ["h", "as", "c"]) @
                    [term_of_bool true] @
                    (map (lookup_inst inst) ["P", "Q"]))
              val (th1, th2) = the_pair ths
              val new_prop =
                  [conj_left_th th1, conj_right_th th2] MRS @{thm conjI}
              val ritem = Fact (TY_CODE_POS_MATCH, tname, new_prop)
            in
              [Update.AddItems {id = id, raw_items = [ritem]},
               Update.ShadowItem {id = id, item = hd items}]
            end)

(* Given ex_th of form EX v1 v2 ... vn. h |= P, instantiate the
   variables v_i and equate them to existing variables in base_th,
   using precision theorems (sep_prec_thms).

   For example, if base_th is h |= os_list l p and ex_th is EX
   l'. os_list l' p & length l' = 3, then return the theorem os_list l
   p & length l = 3.
 *)
fun use_prec_thms (tbl as {ctxt, ...}) base_th ex_th =
    let
      val nms = Update.get_apply_exists_nms ex_th

      (* Find body of existence theorem, same code as in apply_exists. *)
      fun dest_one_abs nm t =
          case t of
              Const("HOL.Ex", _) $ Abs (_, T, body) =>
              let
                val (nm', body') = Term.dest_abs (nm, T, body)
                val _ = assert (nm = nm') "use_prec_thms: name clash"
              in
                ((nm, T), body')
              end
            | _ => raise AUTO2 "use_prec_thms: not exists statement."

      fun dest_all_abs nms t =
          case nms of
              [] => ([], t)
            | nm :: rest =>
              let
                val (var, t') = dest_one_abs nm t
                val (vars, t'') = dest_all_abs rest t'
              in
                (var :: vars, t'')
              end

      val (vars, new_prop) = ex_th |> prop_of' |> dest_all_abs nms
                                   |> apsnd HOLogic.mk_Trueprop
      val new_th = new_prop |> cert ctxt |> Thm.assume
      val base_th' = base_th RS @{thm mod_star_trueI}

      (* Use precision theorem prec_th to generate equalities between
         new variables in new_th and original variables in base_th,
         then perform replacement to original variables in new_th to
         obtain result new_th'.
       *)
      fun apply_prec_thm prec_th new_th =
          let
            val (prem1, prem2) = prec_th |> Thm.prems_of |> the_pair
            val pairs = [(true, (prem1, Thm.prop_of base_th')),
                         (true, (prem2, Thm.prop_of new_th))]
            val insts = Matcher.rewrite_match_list tbl pairs ([], fo_init)

            (* eq_ths: prem1(inst) == base_th', prem2(inst) == new_th. *)
            fun process_inst ((_, inst), eq_ths) =
                let
                  val (eq1, eq2) = the_pair eq_ths
                  val base_th'' = Thm.equal_elim (meta_sym eq1) base_th'
                  val new_th' = Thm.equal_elim (meta_sym eq2) new_th
                in
                  prec_th |> subst_thm ctxt inst
                          |> fold Thm.elim_implies [base_th'', new_th']
                end

            val eqs = map process_inst insts
          in
            new_th |> apply_to_thm (
              Conv.every_conv (map (rewr_obj_eq_top ctxt o obj_sym) eqs))
          end

      val sep_prec_thms =
          Named_Theorems.get ctxt @{named_theorems sep_prec_thms}
      val new_th' = fold apply_prec_thm sep_prec_thms new_th

      (* Check that all new variables in new_th' are replaced. *)
      val _ = assert (not (occurs_frees (map Free vars) (Thm.prop_of new_th')))
                     "use_prec_thms: failed to remove all new vars."
    in
      (* Remove assumptions involving original variables. Similar to
         handler for apply_exists.
       *)
      new_th' |> Thm.implies_intr (cert ctxt new_prop)
              |> fold (ex_elim ctxt) (rev (map Free vars))
              |> Thm.elim_implies ex_th
    end

(* Match a CODE_POS_MATCH item with tname (h, as, c, true, P, Q) to
   propositions (h, as) |= P * Ru (or R if P is emp), and produce the
   proposition (h, as) |= Q * Ru.
 *)
fun match_code_pos_success_fn rtype {ctxt, ...} item1 item2 =
    let
      val thy = Proof_Context.theory_of ctxt
      val tbl = RewriteTable.table_of_rtype rtype
      val {id, tname, prop, ...} = item1
      val tnames = HOLogic.strip_tuple tname
      val (hoare_th, success_ths) = (conj_left_th prop, conj_right_th prop)
      val (success_th, post_th) =
          (conj_left_th success_ths, conj_right_th success_ths)
      val (h_t, as_t) = the_pair (take 2 tnames)
      val (P, _, _) = dest_hoare_triple (prop_of' hoare_th)

      (* Get (h, as) |= emp * R from (h, as) |= R. *)
      fun mult_emp_left th =
          th |> apply_to_thm' ((mod_assn_conv o rewr_obj_eq o obj_sym)
                               @{thm assn_one_left})
    in
      if has_pure_assn thy P then []
      else let
        val P_pat = if P aconv emp then Var (("R", 0), assnT)
                    else mk_star (P, Var (("Ru", 0), assnT))
        val mod_pat = mk_mod (HOLogic.mk_tuple [h_t, as_t], P_pat)
        val insts = get_insts (PropMatch mod_pat) item2 rtype (id, fo_init)
        fun process_inst ((id'', inst), mod_th) =
            let
              val mod_th' = if P aconv emp then mult_emp_left mod_th else mod_th
              val hoare_th' = subst_thm ctxt inst hoare_th
              val res_th =
                  [hoare_th', mod_th', success_th] MRS @{thm hoare_triple_mp}
              val mod_cv = Conv.try_conv (rewr_obj_eq @{thm mod_ex_dist})
              val res_th' =
                  res_th |> apply_to_thm' (mod_assn_conv (
                                              normalize_assn_cv ctxt))
                         |> apply_to_thm' (Conv.top_conv (K mod_cv) ctxt)
                         |> use_prec_thms tbl post_th
                         |> apply_to_thm' (normalize_mod_cv ctxt)
                         |> apply_to_thm (to_obj_conv ctxt)
            in
              Update.thm_update (id'', res_th')
            end
      in
        map process_inst insts
      end
    end

val match_code_pos_success =
    {name = "match_code_pos_success",
     args = [TypedMatch (TY_CODE_POS_MATCH, @{term_pat "(?h, ?as, ?c, True)"}),
             PropMatch @{term_pat "(?h, ?as) |= ?P"}],
     priority = PRIORITY_ADD,
     func = TwoStep match_code_pos_success_fn}

(* Match a CODE_POS_MATCH item with hoare triple <P * \<up>(b)> c <Q>
   with proposition b, resulting in a new CODE_POS_MATCH item
   (shadowing the original one) with hoare triple <P> c <Q>. Only work
   in the case where there are no schematic variables in b.
 *)
fun match_pure_assn_gen (nm, pat, norm_th) =
    prfstep_custom
        nm [WithItem (TY_CODE_POS_MATCH, pat), WithFact @{term_pat "?b::bool"}]
        PRIORITY_SHADOW
        (fn ((id, inst), ths) => fn items => fn _ =>
            if has_vars (lookup_inst inst "b") then []
            else let
              val (th1, th2) = the_pair ths
              val (hoare_th, success_ths) =
                  (conj_left_th th1, conj_right_th th1)
              val hoare_th' = hoare_th |> apply_to_thm' (rewr_obj_eq norm_th)
                                       |> apply_to_thm to_meta_imp_conv
                                       |> Thm.elim_implies th2
              val (P', _, Q') = dest_hoare_triple (prop_of' hoare_th')
              val tname = HOLogic.mk_tuple (
                    map (lookup_inst inst) ["h", "as", "c", "s"] @ [P', Q'])
              val new_prop = [hoare_th', success_ths] MRS @{thm conjI}
              val ritem = Fact (TY_CODE_POS_MATCH, tname, new_prop)
            in
              [Update.AddItems {id = id, raw_items = [ritem]},
               Update.ShadowItem {id = id, item = hd items}]
            end)

val match_pure_assn =
    match_pure_assn_gen (
      "match_pure_assn",
      @{term_pat "(?h, ?as, ?c, ?s, ?P * \<up>(?b), ?Q)"},
      @{thm norm_pre_pure_iff})

val match_pure_assn' =
    match_pure_assn_gen (
      "match_pure_assn'",
      @{term_pat "(?h, ?as, ?c, ?s, \<up>(?b), ?Q)"},
      @{thm norm_pre_pure_iff_sng})

(* Given a CODE_POS_MATCH item with tname (h, as, c, is_success, P,
   Q), where P contains schematic variables. Let P' be the spacial
   (non-pure) part of P. Match with propositions (h, as) |= P' * Ru,
   and produce instantiated version of CODE_POS_MATCH.
 *)
fun match_code_pos_heap_fn rtype {ctxt, ...} item1 item2 =
    let
      val thy = Proof_Context.theory_of ctxt
      val {id, tname, prop, ...} = item1
      val (hoare_th, success_ths) = (conj_left_th prop, conj_right_th prop)
      val (P, _, _) = dest_hoare_triple (prop_of' hoare_th)
    in
      if not (has_vars P) then []
      else if not (has_pure_assn thy P) then []
      else let
        val P' = strip_pure_assn thy P
        val _ = assert (not (P' aconv emp)) "match_code_pos_heap_fn"

        val tnames = HOLogic.strip_tuple tname
        val (h_t, as_t, c, is_success) = the_quadruple (take 4 tnames)

        val P_pat = mk_star (P', Var (("Ru", 0), assnT))
        val mod_pat = mk_mod (HOLogic.mk_tuple [h_t, as_t], P_pat)
        val insts = get_insts (PropMatch mod_pat) item2 rtype (id, fo_init)
        fun process_inst ((id'', inst), _) =
            let
              val hoare_th' = subst_thm ctxt inst hoare_th
              val (P'', _, Q'') = dest_hoare_triple (prop_of' hoare_th')
              val tname' = HOLogic.mk_tuple [h_t, as_t, c, is_success, P'', Q'']
              val prop' = [hoare_th', success_ths] MRS @{thm conjI}
              val ritem = Fact (TY_CODE_POS_MATCH, tname', prop')
            in
              [Update.AddItems {id = id'', raw_items = [ritem]},
               Update.ShadowItem {id = id'', item = item1}]
            end
      in
        maps process_inst insts
      end
    end

val match_code_pos_heap =
    {name = "match_code_pos_heap",
     args = [TypedMatch (TY_CODE_POS_MATCH,
                         @{term_pat "(?h, ?as, ?c, ?s, ?P * \<up>(?b), ?Q)"}),
             PropMatch @{term_pat "(?h, ?as) |= ?P'"}],
     priority = PRIORITY_SHADOW,
     func = TwoStep match_code_pos_heap_fn}

(* Given eq_emp_th of form P = emp, where P is a pattern containing
   only type schematic variables. Match the pre-condition of a
   CODE_POS_MATCH item with P * P' (after instantiating P with type
   variables), producing new pre-condition P'.
 *)
fun match_code_pos_emp_fn eq_emp_th rtype {ctxt, ...} item =
    let
      val thy = Proof_Context.theory_of ctxt
      val tbl = RewriteTable.table_of_rtype rtype
      val {id, tname, prop, ...} = item
      val (hoare_th, success_ths) = (conj_left_th prop, conj_right_th prop)
      val (P, _, _) = dest_hoare_triple (prop_of' hoare_th)
      val ac_info = Nat_Arith.times_ac_on_typ thy assnT
      val Ps = ACUtil.dest_ac_l ac_info P

      (* Decomposition on the eq_emp_th side. *)
      val (f_th, _) = Term.strip_comb (eq_emp_th |> dest_eq_thm |> fst)

      val (h_t, as_t, c, is_success) =
          the_quadruple (take 4 (HOLogic.strip_tuple tname))

      fun match_Pi Pi =
          if not (Term.aconv_untyped (Term.head_of Pi, f_th)) then []
          else let
            val f = Term.head_of Pi
            val tyenv = pattern_match_ty ctxt (fastype_of f_th, fastype_of f)
            val eq_emp_th' = subst_thm ctxt (tyenv, Vartab.empty) eq_emp_th
            val lhs = eq_emp_th' |> dest_eq_thm |> fst
            val insts =
                (Matcher.rewrite_match_head tbl (Pi, lhs) (id, fo_init))
                    |> RewriteTable.replace_id_for_type rtype
            fun process_inst ((id', inst), _) =
                let
                  val cv_on_P = apply_to_thm' o Conv.fun2_conv o
                                Conv.arg_conv
                  val hoare_th' =
                      hoare_th |> subst_thm ctxt inst
                               |> cv_on_P (rewr_obj_eq_top ctxt eq_emp_th')
                               |> cv_on_P (ACUtil.normalize_unit ac_info)
                  val success_ths' =
                      success_ths |> subst_thm ctxt inst
                  val prop' = [hoare_th', success_ths'] MRS @{thm conjI}
                  val (P', _, Q') = dest_hoare_triple (prop_of' hoare_th')
                  val tname' =
                      HOLogic.mk_tuple [h_t, as_t, c, is_success, P', Q']
                  val ritem = Fact (TY_CODE_POS_MATCH, tname', prop')
                in
                  [Update.AddItems {id = id', raw_items = [ritem]},
                   Update.ShadowItem {id = id', item = item}]
                end
          in
            maps process_inst insts
          end
    in
      maps match_Pi Ps
    end

fun add_match_code_pos_emp_prfstep_ctxt eq_emp_th ctxt =
    let
      val name = (name_of_thm eq_emp_th) ^ "@match_code_pos_emp"
      val prfstep =
          {name = name,
           args = [TypedMatch (TY_CODE_POS_MATCH, @{term_pat "(?h, ?as)"})],
           priority = PRIORITY_SHADOW,
           func = OneStep (match_code_pos_emp_fn eq_emp_th)}
    in
      ctxt |> add_prfstep_ctxt prfstep
           |> add_fixed_sc_ctxt (name, 1)
    end

fun add_match_code_pos_emp_prfstep eq_emp_th =
    map_theory_proofsteps (add_match_code_pos_emp_prfstep_ctxt eq_emp_th)

fun match_code_pos_create_case_gen (nm, pat) =
    prfstep_custom
        nm [WithItem (TY_CODE_POS_MATCH, pat)]
        PRIORITY_ADD
        (fn ((id, inst), _) => fn _ => fn {ctxt, ...} =>
            if has_vars (lookup_inst inst "P") then [] else
            let
              val thy = Proof_Context.theory_of ctxt
              val ac_info = Nat_Arith.times_ac_on_typ thy assnT
              val ts = (lookup_inst inst "P")
                           |> ACUtil.dest_ac_total ac_info
                           |> filter is_pure_assn
            in
              if length ts = 0 then []
              else let
                val t = ts |> hd |> Term.dest_comb |> snd |> HOLogic.mk_Trueprop
              in
                [Update.AddBoxes {
                    id = id, inits = [Update.InitAssum t], cbs = []}]
              end
            end)

fun add_match_code_pos_create_case_ctxt hoare_th ctxt =
    let
      val name = (name_of_thm hoare_th) ^ "@case"
      val (_, pat_c, _) = dest_hoare_triple (prop_of' hoare_th)
      val pat = HOLogic.mk_tuple [
            Var (("h", 0), heapT), Var (("as", 0), addrsT), pat_c,
            Var (("s", 0), boolT), Var (("P", 0), assnT)]
      val prfstep = match_code_pos_create_case_gen (name, pat)
    in
      ctxt |> add_prfstep_ctxt prfstep
           |> add_fixed_sc_ctxt (name, 1)
    end

fun add_match_code_pos_create_case hoare_th =
    map_theory_proofsteps (add_match_code_pos_create_case_ctxt hoare_th)

(* Given hoare triple theorem <P> c <Q>, match with CODE_POS item (h,
   as, c), to produce CODE_POS_MATCH item with tname (h, as, c, false,
   P, Q).
 *)
fun next_code_pos_prfstep hoare_th =
    let
      val (_, pat_c, _) = dest_hoare_triple (prop_of' hoare_th)
      val name = (name_of_thm hoare_th) ^ "@match_code_pos"
      val code_pos_pat = HOLogic.mk_tuple [
            Var (("h", 0), heapT), Var (("as", 0), addrsT), pat_c]
      val descs = [WithItem (TY_CODE_POS, code_pos_pat)]
      fun prfstep_fn ((id, inst), ths) _ {ctxt, ...} =
          let
            val h_t = lookup_inst inst "h"
            val as_t = lookup_inst inst "as"
            val c = subst_term_norm inst pat_c
            val hoare_th' = subst_thm ctxt inst hoare_th
            val (P', _, Q') = dest_hoare_triple (prop_of' hoare_th')
            val new_tname =
                HOLogic.mk_tuple [h_t, as_t, c, term_of_bool false, P', Q']
            val new_prop = [hoare_th', the_single ths] MRS @{thm conjI}
            val ritem = Fact (TY_CODE_POS_MATCH, new_tname, new_prop)
          in
            [Update.AddItems {id = id, raw_items = [ritem]}]
          end
    in
      prfstep_custom name descs PRIORITY_ADD prfstep_fn
    end

(* Given hoare_th of the form <?P> ?c <?Q>, produce proofstep matching
   item1 with CODE_POS (?h, ?as, ?c) and item2 with proposition (?h,
   ?as) |= ?P * ?Ru. Also, if the command is not heap preserving,
   produce proofstep matching with SUCCESS_RUN (?h, ?as, ?c) and (?h,
   ?as) |= ?P * ?ru.
 *)
fun add_next_code_pos_prfstep_ctxt hoare_th =
    add_prfstep_ctxt (next_code_pos_prfstep hoare_th)

fun add_next_code_pos_prfstep hoare_th =
    map_theory_proofsteps (add_next_code_pos_prfstep_ctxt hoare_th)

(* Proofstep for moving to next code position. Here hoare_th is the
   hoare triple <P> c <Q>, item1 is the CODE_POS item with parameters
   (h, as, c), and item2 gives the proposition (h, as) |= P * P'.
 *)
fun next_code_pos_direct_prfstep hoare_th =
    let
      val (P, c, _) = dest_hoare_triple (prop_of' hoare_th)
      val h_pat = Var (("h", 0), heapT)
      val as_pat = Var (("as", 0), addrsT)
      val P_pat = if P aconv emp then Var (("R", 0), assnT)
                  else mk_star (P, Var (("Ru", 0), assnT))
      val code_pos_pat = HOLogic.mk_tuple [h_pat, as_pat, c]
      val mod_pat = mk_mod (HOLogic.mk_tuple [h_pat, as_pat], P_pat)

      val name = (name_of_thm hoare_th) ^ "@next_code_pos"
      val descs = [WithItem (TY_CODE_POS, code_pos_pat), WithFact mod_pat]
      fun prfstep_fn ((id, _), ths) items {ctxt, ...} =
          let
            val (code_pos_th, mod_th) = the_pair ths
            val (modQ_th, ritems) =
                next_code_pos_ritems ctxt code_pos_th mod_th hoare_th
          in
            [Update.AddItems {
                id = id, raw_items = ritems @ [Update.thm_to_ritem modQ_th]},
             Update.ShadowItem {id = id, item = hd items}]
          end
    in
      (name, descs, prfstep_custom name descs PRIORITY_SHADOW prfstep_fn)
    end

fun add_next_code_pos_direct_prfstep_ctxt hoare_th ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val (name, descs, prfstep) = next_code_pos_direct_prfstep hoare_th
      val (_, _, Q) = dest_hoare_triple (prop_of' hoare_th)
      val _ = writeln (name ^ "\n" ^ (string_of_descs thy descs) ^
                       "\nConsequence: " ^ (Q |> pretty_term ctxt |> str) ^
                       " (* remainder)")
    in
      ctxt |> add_prfstep_ctxt prfstep
           |> add_fixed_sc_ctxt (name, 1)
    end

fun add_next_code_pos_direct_prfstep hoare_th =
    map_theory_proofsteps (add_next_code_pos_direct_prfstep_ctxt hoare_th)

val ac_shadow_mod =
    prfstep_custom
        "ac_shadow_mod"
        [WithItem (TY_PROP, @{term_pat "?h |= ?A"}),
         WithItem (TY_PROP, @{term_pat "?h |= ?A"})]
        PRIORITY_URGENT
        (fn ((id, _), _) => fn items => fn _ =>
            let
              val (item1, item2) = the_pair items
              val item_to_shadow =
                  if #uid item1 > #uid item2 then item1 else item2
            in
              [Update.ShadowItem {id = id, item = item_to_shadow}]
            end)

val add_sep_logic_proofsteps =
    fold ItemIO_Data.add_item_type [
      (TY_CODE_POS, SOME output_code_pos_fn),
      (TY_CODE_POS_MATCH, SOME output_code_pos_match_fn),
      (TY_SUCCESS_RUN, SOME output_success_run_fn)

    ] #> fold ItemIO_Data.add_typed_matcher [
      (TY_CODE_POS, code_pos_typed_matcher),
      (TY_CODE_POS_MATCH, code_pos_typed_matcher),
      (TY_SUCCESS_RUN, code_pos_typed_matcher)

    ] #> fold add_prfstep (
      normalize_mod_cv_prfsteps @ [
      frame_entail, heap_preservingI,
      init_code_pos, match_code_pos, dest_bind_code_pos,
      disj_match_code_pos, prop_match_code_pos, convert_code_pos_match,
      match_code_pos_success, match_pure_assn, match_pure_assn',
      match_code_pos_heap, ac_shadow_mod

    ]) #> fold add_fixed_sc (
      map (rpair 1) [
        "init_code_pos", "match_code_pos", "dest_bind_code_pos",
        "convert_code_pos_match", "match_pure_assn", "match_pure_assn'",
        "match_code_pos_heap"
    ])

end

val _ = Theory.setup Sep_Logic.add_sep_logic_proofsteps
val add_match_code_pos_emp_prfstep = Sep_Logic.add_match_code_pos_emp_prfstep
val add_next_code_pos_prfstep = Sep_Logic.add_next_code_pos_prfstep
val add_next_code_pos_direct_prfstep =
    Sep_Logic.add_next_code_pos_direct_prfstep
