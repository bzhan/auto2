(* Core (logic) proofsteps. *)

signature LOGIC_PROOFSTEPS =
sig
  (* General logic *)
  val shadow_prop_item: proofstep
  val shadow_term_item: proofstep
  val eq_elim_prfstep: proofstep

  val exists_elim: box_id * thm -> Proof.context -> Update.raw_update list
  val extract_new_vars: Proof.context -> term list -> (string * typ) list
  val form_exists_prop: ((string * typ) * term) list -> term -> term
  val CHOOSE: string -> pre_scripts
  val CHOOSES: string list -> pre_scripts
  val add_logic_proofsteps: theory -> theory

  (* DISJ items. *)
  val TY_DISJ: string
  val dest_tname_of_disj: term -> (bool * bool) * term list
  val imp_to_disj_cv: conv
  val to_disj_cv: conv
  val not_ex_cv: Proof.context -> conv
  val normalize_disj_cv: Proof.context -> conv
  val forall_elim_sch: thm -> thm
  val analyze_disj_th: Proof.context -> thm -> bool * int * thm
  val disj_intro_gen: string * prfstep_descriptor list -> proofstep
  val disj_intro_prfsteps: proofstep list
  val output_disj_fn: item_output
  val disj_typed_matcher: item_matcher
  val disj_prop_matcher: item_matcher

  val match_update_prfsteps: proofstep list
  val match_one_sch_prfstep: proofstep
  val disj_create_case_prfstep: proofstep
  val disj_shadow_prfstep: proofstep
  val not_ex_forall_cv: Proof.context -> conv
  val disj_rewrite_not_all_prfstep: proofstep
  val disj_split_conj_prfstep: proofstep
  val disj_use_vardef_prfstep: proofstep
  val add_disj_proofsteps: theory -> theory

  (* TERM_DEF *)
  val TY_TERM_DEF: string
  val CHOOSE_FUN_N: int -> string -> pre_scripts
  val match_term_def_prfstep: proofstep
  val add_term_def_proofsteps: theory -> theory
end;

structure Logic_ProofSteps : LOGIC_PROOFSTEPS =
struct

(* Shadowing based on equivalence. For both PROP and TERM items,
   shadowing is based on subterm equivalence, skipping any Not (~) at
   head.
 *)
fun shadow_item_fn rtype _ item1 item2 =
    let
      val (tbl as {lat, ...}) = RewriteTable.table_of_rtype rtype
      val id = merged_id lat [item1, item2]
      val (tname1, tname2) = (get_tname item1, get_tname item2)
      val equiv_ids =
          if fastype_of tname1 = boolT andalso is_neg tname1 andalso
             fastype_of tname2 = boolT andalso is_neg tname2 then
            (RewriteTable.subequiv_info tbl id (get_neg tname1, get_neg tname2))
                |> RewriteTable.replace_id_for_type' rtype |> map fst
                |> max_partial (BoxID.is_eq_ancestor lat)
          else
            (RewriteTable.subequiv_info tbl id (tname1, tname2))
                |> RewriteTable.replace_id_for_type' rtype |> map fst
                |> max_partial (BoxID.is_eq_ancestor lat)
      val item_to_shadow =
          if #uid item1 > #uid item2 then item1 else item2
      fun process_id id' =
          Update.ShadowItem {id = id', item = item_to_shadow}
    in
      map process_id equiv_ids
    end

val shadow_prop_item =
    {name = "shadow_prop",
     args = [TypedMatch (TY_PROP, @{term_pat "?A::bool"}),
             TypedMatch (TY_PROP, @{term_pat "?B::bool"})],
     priority = PRIORITY_URGENT,
     func = TwoStep shadow_item_fn}

val shadow_term_item =
    {name = "shadow_term",
     args = [TypedMatch (TY_TERM, @{term_pat "?A::?'a"}),
             TypedMatch (TY_TERM, @{term_pat "?B::?'a"})],
     priority = PRIORITY_URGENT,
     func = TwoStep shadow_item_fn}

(* Given equality A = B between booleans and proposition A, B, ~A, ~B,
   derive the other side of the equality (or its negation) and shadow
   the equality.
 *)
fun eq_elim_fn rtype _ (item1 as {id, prop, ...}) item2 =
    let
      val (A, B) = HOLogic.dest_eq (prop_of' prop)
      fun inst_t t = get_insts (PropMatch t) item2 rtype (id, fo_init)
      val (inst_A, inst_B) = (inst_t A, inst_t B)
      val (inst_nA, inst_nB) = (inst_t (get_neg A), inst_t (get_neg B))

      (* All the process_inst functions follow the same pattern, up to
         transform function f for prop.
       *)
      fun elim_shadow f ((id', _), th) =
          [Update.thm_update (
              id', Thm.equal_elim (make_trueprop_eq (f prop)) th),
           Update.ShadowItem {id = id', item = item1}]

      val process_inst_A = elim_shadow to_meta_eq
      val process_inst_B = elim_shadow (meta_sym o to_meta_eq)
      val process_inst_nA = elim_shadow (make_neg_eq o to_meta_eq)
      val process_inst_nB = elim_shadow (make_neg_eq o meta_sym o to_meta_eq)
    in
      maps process_inst_A inst_A @ maps process_inst_B inst_B @
      maps process_inst_nA inst_nA @ maps process_inst_nB inst_nB
    end

val eq_elim_prfstep =
    {name = "eq_elim",
     args = [TypedMatch (TY_EQ, @{term_pat "((?A::bool), ?B)"}),
             PropMatch @{term_pat "?C::bool"}],
     priority = PRIORITY_SHADOW,
     func = TwoStep eq_elim_fn}

(* Given an assumption of the form EX x. A, we produce an assumption A
   with x in A replaced by a free variable. To avoid name collisions,
   when the update is produced x is replaced by an "internal" free
   variable, with suffix '_'. When the update is applied, that
   internal free variable is replaced by a fresh variable as
   determined by the context. We produce at most two variables at a
   time.
 *)
fun exists_elim (id, th) ctxt =
    let
      val nms = Update.get_apply_exists_nms th
    in
      Update.apply_exists (id, th) ctxt (take 2 nms)
    end

(* Given a list of terms, where each term contains exactly one new
   variable that does not appear in ctxt or the previous terms, return
   the list of new variables as a list.
 *)
fun extract_new_vars ctxt ts =
    case ts of
        [] => []
      | t :: ts' =>
        let
          val vars = Term.add_frees t []
          val new_vars =
              filter_out (fn (nm, _) => Variable.is_fixed ctxt nm) vars
        in
          if length new_vars = 1 then
            let
              val (nm, T) = the_single new_vars
              val ctxt' = ctxt |> declare_free_term (Free (nm, T))
            in
              (nm, T) :: extract_new_vars ctxt' ts'
            end
          else
            raise AUTO2 "extract_new_vars: number of new variables is not 1."
        end

(* Form the exists proposition. conds_spec is a list of pairs ((nm,
   T), cond), where Free (nm, T) is the new variable appearing in
   cond.
 *)
fun form_exists_prop conds_spec concl =
    case conds_spec of
        [] => concl
      | ((nm, T), cond) :: rest =>
        let
          val concl' = form_exists_prop rest concl
        in
          if Free (nm, T) aconv cond then
            HOLogic.mk_exists (nm, T, concl')
          else
            case cond of
                Const ("Set.member", _) $ _ $ S =>
                let
                  val setT = HOLogic.mk_setT T
                  val bexT = setT --> (T --> boolT) --> boolT
                in
                  Const ("Set.Bex", bexT) $ S $ absfree (nm, T) concl'
                end
              | _ =>
                HOLogic.mk_exists (nm, T, HOLogic.mk_conj (cond, concl'))
        end

fun read_choose_str str ctxt =
    let
      val ts = read_term ctxt ("(" ^ str ^ ")") |> HOLogic.strip_tuple
      val (conds, concl) = split_last ts
      val new_vars = extract_new_vars ctxt conds

      (* Exist proposition to prove. *)
      val ex_prop =
          HOLogic.mk_Trueprop (form_exists_prop (new_vars ~~ conds) concl)

      (* Check the variable names are new, and add to ctxt. *)
      val _ = assert (not (exists (Variable.is_fixed ctxt) (map fst new_vars)))
                     "CHOOSE: variable name(s) already used."
    in
      (new_vars, ex_prop)
    end

fun CHOOSE str ctxt =
    let
      val (new_vars, ex_prop) = read_choose_str str ctxt
      fun choose_callback ((id, th), {ctxt, ...}) =
          Update.apply_exists (id, th) ctxt (map fst new_vars)
    in
      [Script_Task {inits = [Update.InitAssum (get_neg' ex_prop)], subs = [],
                    cb = choose_callback, end_vars = map Free new_vars}]
    end

fun CHOOSES strs =
    case strs of
        [str] => CHOOSE str
      | str :: rest => (CHOOSE str) THEN (CHOOSES rest)
      | _ => raise AUTO2 "CHOOSES: empty argument"

val add_logic_proofsteps =
    fold add_prfstep [
      shadow_prop_item, shadow_term_item, eq_elim_prfstep

    ] #> fold add_fixed_sc [
      ("eq_elim", 1)

    ] #> fold add_prfstep_custom [
      ("exists_elim",
       [WithFact @{term_pat "EX x. ?A x"}],
       PRIORITY_ADD,
       fn ((id, _), ths) => fn _ => fn {ctxt, ...} =>
          exists_elim (id, the_single ths) ctxt),

      ("not_forall_elim",
       [WithGoal @{term_pat "!x. ?P x"}],
       PRIORITY_ADD,
       fn ((id, _), ths) => fn _ => fn {ctxt, ...} =>
          let
            val th = ths |> the_single
                         |> apply_to_thm' (rewr_obj_eq @{thm HOL.not_all})
          in
            exists_elim (id, th) ctxt
          end),

      ("bex_elim",
       [WithFact @{term_pat "Bex ?S ?P"}],
       PRIORITY_ADD,
       fn ((id, _), ths) => fn _ => fn {ctxt, ...} =>
          let
            val th = ths |> the_single
                         |> apply_to_thm' (rewr_obj_eq @{thm Bex_def'})
          in
            exists_elim (id, th) ctxt
          end),

      ("not_ball_elim",
       [WithGoal @{term_pat "Ball ?S ?P"}],
       PRIORITY_ADD,
       fn ((id, _), ths) => fn _ => fn {ctxt, ...} =>
          let
            val cv = (Conv.arg_conv (rewr_obj_eq @{thm Ball_def'}))
                         then_conv (rewr_obj_eq @{thm HOL.not_all})
            val th = ths |> the_single |> apply_to_thm' cv
          in
            exists_elim (id, th) ctxt
          end)

    ] #> fold add_gen_prfstep [
      ("shadow_exists",
       [WithFact @{term_pat "EX x. (?P::(?'a => bool)) x"},
        WithFact @{term_pat "(?P::(?'a => bool)) ?x"},
        ShadowFirst]),

      ("shadow_not_forall",
       [WithGoal @{term_pat "!x. (?P::(?'a => bool)) x"},
        WithGoal @{term_pat "(?P::(?'a => bool)) ?x"},
        ShadowFirst]),

      ("shadow_exists2",
       [WithFact @{term_pat "EX x y. (?P::(?'a => ?'b => bool)) x y"},
        WithFact @{term_pat "(?P::(?'a => ?'b => bool)) ?x ?y"},
        ShadowFirst]),

      ("shadow_not_forall2",
       [WithGoal @{term_pat "!x y. (?P::(?'a => ?'b => bool)) x y"},
        WithGoal @{term_pat "(?P::(?'a => ?'b => bool)) ?x ?y"},
        ShadowFirst])
    ]

(* Disjunctive mutable states. *)
val TY_DISJ = "DISJ"

(* Given a theorem in the form of a disjunction, possibly containing
   schematic variables, return the corresponding DISJ item. Here sz
   specifies number of terms in the disjunction.
 *)
fun disj_to_update is_active match_prem (id, sz, th) =
    if Thm.prop_of th aconv prop_False then
      Update.ResolveBox {id = id, th = th}
    else if sz = 1 andalso not (has_vars (Thm.prop_of th)) then
      Update.AddItems {
        id = id, raw_items = [Fact (TY_PROP, prop_of' th, th)]}
    else let
      val subs = ACUtil.dest_ac_r disj_ac (prop_of' th)
      val _ = assert (length subs >= sz)
                     "disj_to_update: not enough terms in th."
      val (prev, last) = chop (sz - 1) subs
      val subs' = prev @ [ACUtil.list_ac_r disj_ac last]
      val tname = HOLogic.mk_tuple (
            map term_of_bool [is_active, match_prem] @ subs')
    in
      Update.AddItems {id = id, raw_items = [Fact (TY_DISJ, tname, th)]}
    end

(* Deconstruct the tname of a DISJ item. *)
fun dest_tname_of_disj tname =
    case HOLogic.strip_tuple tname of
        is_active :: match_prem :: rest =>
        ((bool_of_term is_active, bool_of_term match_prem), rest)
      | _ => raise AUTO2
                   "dest_tname_of_disj: too few terms in tname of DISJ item."

(* Convert term of form A_1 --> ... --> A_n to ~A_1 | ... | ~A_(n-1) |
   A_n, cancelling any double negations.
 *)
fun imp_to_disj_cv ct =
    case Thm.term_of ct of
        Const ("HOL.implies", _) $ _ $ _ =>
        ((rewr_obj_eq @{thm imp_conv_disj})
             then_conv (Conv.arg1_conv (
                           Conv.try_conv (rewr_obj_eq nn_cancel_th)))
             then_conv (Conv.arg_conv imp_to_disj_cv)) ct
      | _ => Conv.all_conv ct

(* Convert term of form ~(A_1 & ... & A_n) to ~A_1 | ... | ~A_n,
   cancelling any double negations.
 *)
fun not_conj_to_disj_cv ct =
    case Thm.term_of ct of
        Const ("HOL.Not", _) $ (Const ("HOL.conj", _) $ _ $ _) =>
        ((rewr_obj_eq @{thm de_Morgan_conj})
             then_conv (Conv.arg1_conv (
                           Conv.try_conv (rewr_obj_eq nn_cancel_th)))
             then_conv (Conv.arg_conv not_conj_to_disj_cv)) ct
      | _ => Conv.try_conv (rewr_obj_eq nn_cancel_th) ct

(* Convert A_1 --> ... --> A_n to ~A_1 | ... | ~A_(n-1) | A_n. Convert
   ~(A_1 & ... & A_n) to ~A_1 | ... | ~A_n. Eliminate any double
   negations.
 *)
fun to_disj_cv ct =
    case Thm.term_of ct of
        Const ("HOL.implies", _) $ _ $ _ => imp_to_disj_cv ct
      | Const ("HOL.Not", _) $ _ =>
        ((Conv.arg_conv (ACUtil.normalize_assoc_r conj_ac))
             then_conv not_conj_to_disj_cv) ct
      | _ => ACUtil.normalize_assoc_r disj_ac ct

(* Convert term of form ~ (EX x y. P x y) to !x y. ~ P x y (arbitrary
   number of existence quantifiers).
 *)
fun not_ex_cv ctxt ct =
    case Thm.term_of ct of
        Const ("HOL.Not", _) $ (Const ("HOL.Ex", _) $ Abs _) =>
        ((rewr_obj_eq @{thm HOL.not_ex})
             then_conv (Conv.binder_conv (not_ex_cv o snd) ctxt)) ct
      | _ => Conv.all_conv ct

(* Convert to a (object) forall fact. ct must begin with ~EX or ALL to
   be transformed.
 *)
fun to_forall_cv ctxt ct =
    case Thm.term_of ct of
        Const ("HOL.Not", _) $ (Const ("HOL.Ex", _) $ Abs _) =>
        ((Conv.arg_conv (normalize_exs_conv ~1 ctxt))
             then_conv (not_ex_cv ctxt)) ct
      | Const ("HOL.Not", _) $ (Const ("Set.Bex", _) $ _ $ _) =>
        ((Conv.arg_conv (normalize_exs_conv ~1 ctxt))
             then_conv (not_ex_cv ctxt)) ct
      | Const ("HOL.All", _) $ Abs _ => normalize_alls_conv ~1 ctxt ct
      | Const ("Set.Ball", _) $ _ $ _ => normalize_alls_conv ~1 ctxt ct
      | _ => Conv.all_conv ct

(* Apply cv on the body of !x y z. ... .*)
fun forall_body_conv cv ctxt ct =
    case Thm.term_of ct of
        Const ("HOL.All", _) $ Abs _ =>
        Conv.binder_conv (fn (_, ctxt) => forall_body_conv cv ctxt) ctxt ct
      | _ => cv ct

(* Full conversion into normal form for disjunctions, with forall
   quantifications outside, and disjunctions in the body. This should
   work with unambigous output even of there are schematic variables
   in the body.
 *)
fun normalize_disj_cv ctxt =
    (to_forall_cv ctxt) then_conv (forall_body_conv to_disj_cv ctxt)

(* Convert theorems of form !!x y. P x y into P ?x ?y (arbitrary
   number of quantifiers).
 *)
fun forall_elim_sch th =
    let
      val thy = Thm.theory_of_thm th
    in
      case Thm.prop_of th of
          Const ("Pure.all", _) $ Abs (nm, T, _) =>
          th |> Thm.forall_elim (cert_thy thy (Var ((nm, 0), T)))
             |> forall_elim_sch
        | _ => th
    end

(* Given a theorem th, return equivalent theorem in disjunctive form,
   with possible schematic variables. Also return whether th is
   "active", that is, whether it is originally a conjunctive goal or
   disjunctive fact, as opposed to implications.
 *)
fun analyze_disj_th ctxt th =
    let
      val th' = th |> apply_to_thm' (to_forall_cv ctxt)
                   |> apply_to_thm (to_meta_all_conv ctxt)
                   |> forall_elim_sch
      val prop = prop_of' th'
      val th'' = apply_to_thm' to_disj_cv th'
    in
      case prop of
          Const ("HOL.disj", _) $ _ $ _ =>
          (true, length (ACUtil.dest_ac_total disj_ac prop), th'')
        | Const ("HOL.Not", _) $ (Const ("HOL.conj", _) $ _ $ _) =>
          (true, length (ACUtil.dest_ac_total conj_ac (get_neg prop)), th'')
        | _ =>
          (false, length (fst (strip_obj_imp prop)) + 1, th'')
    end

(* Template for proofsteps constructing DISJ items from propositions. *)
fun disj_intro_gen (name, desc) =
    prfstep_custom
        name desc PRIORITY_SHADOW
        (fn ((id, _), ths) => fn items => fn {ctxt, ...} =>
            let
              val (is_active, sz, disj_th) =
                  analyze_disj_th ctxt (the_single ths)
            in
              [disj_to_update is_active true (id, sz, disj_th),
               Update.ShadowItem {id = id, item = the_single items}]
            end)

(* Introduction rules for DISJ. *)
val disj_intro_prfsteps = map disj_intro_gen [
      ("conj_goal_intro", [WithProp @{term_pat "~(?A & ?B)"}]),
      ("disj_state_intro", [WithProp @{term_pat "?A | ?B"}]),
      ("imp_disj_state_intro", [WithProp @{term_pat "?A --> ?B"}]),
      ("forall_fact_intro", [WithProp @{term_pat "!x. ?P x"}]),
      ("ball_fact_intro", [WithProp @{term_pat "Ball ?S ?P"}]),
      ("exists_goal_intro", [WithProp @{term_pat "~ (EX x. ?P x)"}]),
      ("bex_goal_intro", [WithProp @{term_pat "~ (Bex ?S ?P)"}])]

fun output_disj_fn ctxt (tname, _) =
    let
      val ((is_active, match_prem), subs) = dest_tname_of_disj tname
    in
      "DISJ " ^ (if is_active then "(active) " else "") ^
      (if match_prem then "(match prem) " else "") ^
      (subs |> pretty_terms ctxt |> str)
    end

(* Pre-matching function for DISJ items. There are only three possible
   patterns to consider: ?C | ?D, ?C = ?D, and ?C. No rewriting is
   needed for pre-matching. Matching is not implemented.
 *)
val disj_typed_matcher =
    let
      val pat_or = @{term_pat "?C | ?D"}
      val pat_eq = @{term_pat "?C = ?D"}
      val pat_single = @{term_pat "?C::bool"}

      fun pre_match pat {tname, ...} {ctxt, ...} =
          let
            val (_, subs) = dest_tname_of_disj tname
          in
            if pat aconv pat_single then true
            else if pat aconv pat_or then length subs >= 2
            else if pat aconv pat_eq then
              length subs = 1 andalso is_eq_term (the_single subs)
            else if length subs > 1 then false
            else
              let val _ = pattern_fo_match ctxt (pat, the_single subs) in true
              end handle Pattern.MATCH => false
          end

      fun match _ _ _ _ =
          raise AUTO2 "disj_typed_matcher: matching not implemented."
    in
      {pre_match = pre_match, match = match}
    end

(* Matching a DISJ item (possibly containing schematic variables) with
   a forall or not exists statement.
 *)
val disj_prop_matcher =
    let
      fun pre_match pat {tname, ...} _ =
          let
            val ((_, match_prem), _) = dest_tname_of_disj tname
          in
            if not match_prem then false else
            case pat of
                Const ("HOL.disj", _) $ _ $ _ => not (has_vars tname)
              | Const ("HOL.implies", _) $ _ $ _ => not (has_vars tname)
              | Const ("HOL.Not", _) $ (Const ("HOL.conj", _) $ _ $ _) =>
                not (has_vars tname)
              | Const ("HOL.All", _) $ Abs _ => has_vars tname
              | Const ("Set.Ball", _) $ _ $ _ => has_vars tname
              | Const ("HOL.Not", _) $ (Const ("HOL.Ex", _) $ Abs _) =>
                has_vars tname
              | Const ("HOL.Not", _) $ (Const ("Set.Bex", _) $ _ $ _) =>
                has_vars tname
              | _ => false
          end

      (* Given t in forall-disj form, return the list of types in the
         forall abstractions, followed by the number of terms in the
         disjunction.
       *)
      fun strip_forall_disj t =
          case t of
              Const ("HOL.All", _) $ Abs (_, T, body) =>
              let
                val (allc, disjc) = strip_forall_disj body
              in
                (T :: allc, disjc)
              end
            | Const ("HOL.disj", _) $ _ $ B =>
              let
                val (allc, disjc) = strip_forall_disj B
              in
                (allc, disjc + 1)
              end
            | _ => ([], 1)

      (* Returns the body under forall. *)
      fun strip_forall t =
          case t of
              Const ("HOL.All", _) $ Abs (_, _, body) => strip_forall body
            | _ => t

      (* Given th: t(var) == u(var), form !nm. t(nm) == u(nm). *)
      fun abstract_forall_rule ctxt ((nm, T), var) th =
          let
            val all_const = Const ("HOL.All", (T --> boolT) --> boolT)
          in
            th |> Thm.abstract_rule nm (cert ctxt var)
               |> Thm.combination (Thm.reflexive (cert ctxt all_const))
          end

      fun match pat {tname, prop = th, ...} (tbl as {ctxt, ...})
                (id, (tyinst, inst)) =
          let
            val ((_, match_prem), subs) = dest_tname_of_disj tname
            val thy = Proof_Context.theory_of ctxt
          in
            if not match_prem then []
            else let
              val pat_eq = normalize_disj_cv ctxt (cert ctxt pat)
              val pat' = rhs_of pat_eq
              val (allc, disjc) = strip_forall_disj pat'
              val vars = Term.add_vars tname []
              val var_tys = map snd vars
            in
              if length allc <> length vars orelse disjc <> length subs orelse
                 not (Type.could_matches (rev allc, var_tys))
              then [] else
              let
                (* First step: match and instantiate types. *)
                val allc = map (Envir.subst_type tyinst) allc
                val tyinst' =
                    fold (Sign.typ_match thy) (rev allc ~~ var_tys) tyinst
                val pat'' = Envir.subst_term_types tyinst' pat'

                (* Second step: get fresh free variables and
                   substitute them into both pattern and term.
                 *)
                val vars' = map (fn ((nm, _), T) => (nm, T)) vars
                val bd_vars = map Free (Variable.variant_frees ctxt [] vars')
                val sch_vars = map Var vars
                val tname' =
                    Term.subst_atomic (sch_vars ~~ bd_vars) (prop_of' th)
                val pat''' = Term.subst_bounds (bd_vars, strip_forall pat'')

                (* Find matches between pattern and term, both with bd_vars. *)
                val insts' = Matcher.rewrite_match_ac_bd
                                 disj_ac tbl bd_vars (pat''', tname')
                                 (id, (tyinst', inst))

                fun process_inst ((id', inst'), eq_th) =
                    (* eq_th: pat'''(s) == tname'(s), pat_eq: pat == pat'. *)
                    let
                      val pat_eq' = subst_thm ctxt inst' pat_eq
                      (* eq_th': between pat' and forall version of th. *)
                      val eq_th' = fold (abstract_forall_rule ctxt)
                                        (vars' ~~ bd_vars) eq_th
                      val eq_th'' = (transitive_list [pat_eq', eq_th'])
                                        |> meta_sym |> make_trueprop_eq
                      val forall_th =
                          th |> fold Thm.forall_intr (map (cert ctxt) sch_vars)
                             |> apply_to_thm (to_obj_conv ctxt)
                    in
                      ((id', inst'), Thm.equal_elim eq_th'' forall_th)
                    end
              in
                map process_inst insts'
              end
              handle Type.TYPE_MATCH => []
            end
          end
    in
      {pre_match = pre_match, match = match}
    end

(* Reduce a disjunction p_1 | ... | t | ... | p_n by matching ~t with
   the second item. If the disjunction contains schematic variables, t
   must have either zero or the largest number of schematic variables.
 *)
fun match_update_fn
        rtype (st as {ctxt, ...}) (item1 as {tname = tname1, ...}) item2 =
    let
      val {id, prop, ...} = item1
      val thy = Status.theory_of st
      val ((is_active, _), subs) = dest_tname_of_disj tname1
      fun count_var t = length (Term.add_vars t [])
      val max_nvar = fold (curry Int.max) (map count_var subs) 0

      (* Match the negation of subs[i] with th2. For each match,
         instantiate in prop all schematic variables in t, so that t
         becomes ~th2. Then remove t from prop in the instantiated
         version.
       *)
      fun get_matches i =
          if length subs > 1 andalso
             is_property_prem thy (get_neg (nth subs i)) then []
          else if not (is_pattern (nth subs i)) then []
          else let
            val t = nth subs i
            val nvar = count_var (nth subs i)
            fun process_inst ((id', inst), th) =
                if nvar > 0 andalso nvar < max_nvar andalso
                   not (i = 0 andalso forall (fn (_, (_, t)) => Term.is_Free t)
                                             (Vartab.dest (snd inst)))
                then []
                else let
                  val prop' =
                      prop |> subst_thm_thy thy inst
                           |> apply_to_thm (rewr_obj_eq_top ctxt (to_eqF_th th))
                           |> apply_to_thm' (ACUtil.normalize_unit disj_ac)
                  val shadow_updt = if count_var (nth subs i) > 0 then [] else
                                    [Update.ShadowItem {id = id', item = item1}]
                  val reduce_count =
                      subs |> map (subst_term_norm inst)
                           |> filter (fn t => t aconv (get_neg (prop_of' th)))
                           |> length
                  val new_len = length subs - reduce_count
                in
                  [disj_to_update is_active false (id', new_len, prop')] @
                  shadow_updt
                end
          in
            if i > 0 andalso nvar > 0 andalso nvar < max_nvar then []
            else (get_insts (PropMatch (get_neg t)) item2 rtype (id, fo_init))
                     |> maps process_inst
          end
    in
      maps get_matches (0 upto (length subs - 1))
    end

val match_update_prfsteps = [
  {name = "disj_match_update",
   args = [TypedMatch (TY_DISJ, @{term_pat "?C::bool"}),
           PropMatch @{term_pat "?A::bool"}],
   priority = PRIORITY_SHADOW,
   func = TwoStep match_update_fn}
]

(* For DISJ items with a single term, of form f p1 ... pn, match t
   against each of p_i.
 *)
fun match_one_sch_fn rtype (st as {tbl, ...}) {id, tname, prop = th1, ...}
                     item2 =
    let
      val thy = Status.theory_of st
      val (_, subs) = dest_tname_of_disj tname
    in
      if length subs > 1 then [] else
      let
        val t = the_single subs
        val (_, args) = Term.strip_comb t
        fun count_var t = length (Term.add_vars t [])
        val nvar = count_var t

        fun get_matches i =
            if count_var (nth args i) < nvar then [] else
            let
              val arg = nth args i
              val insts = get_insts (TypedMatch (TY_TERM, arg)) item2 rtype
                                    (id, fo_init)
              fun inst_to_updt ((id', inst), _) =
                  let
                    val th1' = subst_thm_thy thy inst th1
                    val prop' = prop_of' th1'
                  in
                    if is_eq_term prop' andalso
                       RewriteTable.is_equiv id' tbl (HOLogic.dest_eq prop')
                    then [] else [Update.thm_update (id', th1')]
                  end
            in
              maps inst_to_updt insts
            end
      in
        maps get_matches (0 upto (length args - 1))
      end
    end

val match_one_sch_prfstep =
    {name = "match_one_sch",
     args = [TypedMatch (TY_DISJ, @{term_pat "?C::bool"}),
             TypedMatch (TY_TERM, @{term_pat "?A"})],
     priority = PRIORITY_ADD,
     func = TwoStep match_one_sch_fn}

(* For active case, create box checking the next case. *)
fun disj_create_case_fn rtype {ctxt, ...} {id, tname, ...} =
    if not (RewriteTable.is_single_rtype rtype) then [] else
    if has_vars tname then [] else
    let
      val ((is_active, _), subs) = dest_tname_of_disj tname
    in
      if not is_active then []
      else if length subs = 1 then []
      else let
        val stmt = subs |> hd |> get_neg |> cert ctxt
                        |> normalize_alls_conv ~1 ctxt |> rhs_of
        val (vars, body) = strip_obj_all_var stmt
        val (assums, concl) = strip_obj_imp body
        val inits = map Update.InitVar vars @
                    map (Update.InitAssum o HOLogic.mk_Trueprop) assums @
                    [Update.InitAssum (HOLogic.mk_Trueprop (get_neg concl))]
      in
        [Update.AddBoxes {id = id, inits = inits, cbs = []}]
      end
    end

val disj_create_case_prfstep =
    {name = "disj_create_case",
     args = [TypedMatch (TY_DISJ, @{term_pat "?C | ?D"})],
     priority = PRIORITY_ADD,
     func = OneStep disj_create_case_fn}

(* item1 dominates item2 if the disjunctive terms in item1 is a subset
   of that for item2.
 *)
fun disj_shadow_fn rtype _ (item1 as {tname = tname1, ...})
                   (item2 as {tname = tname2, ...}) =
    if not (RewriteTable.is_single_rtype rtype) then [] else
    let
      val {lat, ...} = RewriteTable.table_of_rtype rtype
      val id = merged_id lat [item1, item2]
      val ((is_active1, match_prem1), subs1) = dest_tname_of_disj tname1
      val ((is_active2, match_prem2), subs2) = dest_tname_of_disj tname2
    in
      if (not is_active1 andalso is_active2) then []
      else if (not match_prem1 andalso match_prem2) then []
      else if subset (op aconv) (subs1, subs2) then
        [Update.ShadowItem {id = id, item = item2}]
      else []
    end

val disj_shadow_prfstep =
    {name = "disj_shadow",
     args = [TypedMatch (TY_DISJ, @{term_pat "?C | ?D"}),
             TypedMatch (TY_DISJ, @{term_pat "?C | ?D"})],
     priority = PRIORITY_SHADOW,
     func = TwoStep disj_shadow_fn}

(* Move "not" inside exists and foralls. *)
fun not_ex_forall_cv ctxt ct =
    case Thm.term_of ct of
        @{const Not} $ (Const ("HOL.Ex", _) $ Abs _) =>
        (* ~ EX x. P x to ALL x. ~ P x. *)
        ((rewr_obj_eq @{thm HOL.not_ex})
             then_conv (Conv.binder_conv (not_ex_forall_cv o snd) ctxt)) ct
      | @{const Not} $ (Const ("HOL.All", _) $ Abs _) =>
        (* ~ ALL x. P x to EX x. ~ P x. *)
        ((rewr_obj_eq @{thm HOL.not_all})
             then_conv (Conv.binder_conv (not_ex_forall_cv o snd) ctxt)) ct
      | @{const Not} $ (Const ("HOL.conj", _) $ A $ _) =>
        (* ~ (x < y & C) to x < y --> ~C. *)
        if is_order A then
          ((rewr_obj_eq @{thm not_conj_to_imp})
               then_conv (Conv.arg_conv (not_ex_forall_cv ctxt))) ct
        else Conv.all_conv ct
      | @{const Not} $ (Const ("HOL.implies", _) $ A $ _) =>
        (* ~ (x < y --> C) to x < y & ~C. *)
        if is_order A then
          ((rewr_obj_eq @{thm not_imp})
               then_conv (Conv.arg_conv (not_ex_forall_cv ctxt))) ct
        else Conv.all_conv ct
      | @{const Not} $ (Const ("HOL.Not", _) $ _) =>
        (* ~ ~ A to A. *)
        ((rewr_obj_eq nn_cancel_th) then_conv (not_ex_forall_cv ctxt)) ct
      | @{const Not} $ (Const (@{const_name less}, _) $ _ $ _) =>
        (Conv.try_conv (rewr_obj_eq @{thm not_less})) ct
      | @{const Not} $ (Const (@{const_name less_eq}, _) $ _ $ _) =>
        (Conv.try_conv (rewr_obj_eq @{thm not_le})) ct
      | _ => Conv.all_conv ct

(* Rewrite part of DISJ item that is ~ALL. *)
fun disj_rewrite_not_all rtype {ctxt, ...} {id, tname, prop, ...} =
    if not (RewriteTable.is_single_rtype rtype) then [] else
    if not (has_vars tname) then [] else
    let
      val ((is_active, match_prem), subs) = dest_tname_of_disj tname
      fun rewrite_not_all ct =
          case Thm.term_of ct of
              @{const Not} $ (Const ("HOL.All", _) $ Abs _) =>
              not_ex_forall_cv ctxt ct
            | _ => Conv.all_conv ct
      val prop' =
          apply_to_thm' (ACUtil.ac_subterms_conv disj_ac rewrite_not_all) prop
    in
      if Thm.prop_of prop aconv Thm.prop_of prop' then []
      else [disj_to_update is_active match_prem (id, length subs, prop')]
    end

val disj_rewrite_not_all_prfstep =
    {name = "disj_rewrite_not_all",
     args = [TypedMatch (TY_DISJ, @{term_pat "?C::bool"})],
     priority = PRIORITY_ADD,
     func = OneStep disj_rewrite_not_all}

(* Split conjunction (or not disj) within DISJ. *)
fun disj_split_conj rtype _ (item as {id, tname, prop, ...}) =
    if not (RewriteTable.is_single_rtype rtype) then [] else
    if not (has_vars tname) then [] else
    let
      val ((is_active, match_prem), subs) = dest_tname_of_disj tname
      fun is_conj t =
          case t of
              Const ("HOL.conj", _) $ _ $ _ => true
            | Const ("HOL.Not", _) $ (Const ("HOL.disj", _) $ _ $ _) => true
            | _ => false
    in
      case find_first is_conj subs of
          NONE => []
        | SOME t =>
          let
            val len = length subs
            val cv =
                if len = 1 then
                  Conv.try_conv (rewr_obj_eq @{thm de_Morgan_disj})
                else
                  Conv.every_conv [
                    ACUtil.swap_assoc_to_l len disj_ac,
                    ACUtil.move_outmost disj_ac t,
                    Conv.arg_conv (
                      Conv.try_conv (rewr_obj_eq @{thm de_Morgan_disj})),
                    rewr_obj_eq @{thm disj_conj_distribL},
                    Conv.binop_conv (ACUtil.swap_assoc_to_r len disj_ac)]
            val props = prop |> apply_to_thm' cv |> split_conj_th
            val shadow_updt =
                if match_prem then []
                else [Update.ShadowItem {id = id, item = item}]
          in
            shadow_updt @
            map (fn th => disj_to_update
                              is_active match_prem (id, length subs, th)) props
          end
    end

val disj_split_conj_prfstep =
    {name = "disj_split_conj",
     args = [TypedMatch (TY_DISJ, @{term_pat "?C::bool"})],
     priority = PRIORITY_NORM,
     func = OneStep disj_split_conj}

fun disj_use_vardef rtype {ctxt, ...} (item as {id, tname, prop, ...}) =
    if not (RewriteTable.is_single_rtype rtype) then [] else
    if not (has_vars tname) then [] else
    let
      val ((is_active, match_prem), subs) = dest_tname_of_disj tname
      fun is_vardef t =
          case t of
              Const ("HOL.eq", _) $ Var _ $ _ => true
            | Const ("HOL.eq", _) $ _ $ Var _ => true
            | _ => false
    in
      if length subs = 1 then [] else
      case find_first (is_vardef o get_neg) subs of
          NONE => []
        | SOME t =>
          let
            val len = length subs
            val (_, (t1, t2)) = dest_binop (get_neg t)
            val (is_left, var) =
                if Term.is_Var t1 then (true, t1) else (false, t2)
            val cv = Conv.every_conv [
                  ACUtil.swap_assoc_to_l len disj_ac,
                  ACUtil.move_outmost disj_ac t,
                  (if not is_left then
                     Conv.arg_conv (
                       Conv.arg_conv (rewr_obj_eq @{thm HOL.eq_commute}))
                   else Conv.all_conv),
                  rewr_obj_eq @{thm disj_comms(1)},
                  rewr_obj_eq @{thm disj_not1}]
            val prop' =
                prop |> apply_to_thm' cv
                     |> Thm.forall_intr (cert ctxt var)
                     |> apply_to_thm (to_obj_conv ctxt)
                     |> apply_to_thm' (rewr_obj_eq @{thm use_vardef})
                     |> apply_to_thm' (ACUtil.swap_assoc_to_r (len-1) disj_ac)
          in
            [Update.ShadowItem {id = id, item = item},
             disj_to_update is_active match_prem (id, length subs - 1, prop')]
          end
    end

val disj_use_vardef_prfstep =
    {name = "disj_use_vardef",
     args = [TypedMatch (TY_DISJ, @{term_pat "?C | ?D"})],
     priority = PRIORITY_NORM,
     func = OneStep disj_use_vardef}

val add_disj_proofsteps =
    fold ItemIO_Data.add_item_type [
      (TY_DISJ, SOME output_disj_fn)

    ] #> fold ItemIO_Data.add_typed_matcher [
      (TY_DISJ, disj_typed_matcher)

    ] #> fold ItemIO_Data.add_prop_matcher [
      (TY_DISJ, disj_prop_matcher)

    ] #> fold add_prfstep (
      disj_intro_prfsteps @
      match_update_prfsteps @
      [match_one_sch_prfstep, disj_create_case_prfstep, disj_shadow_prfstep,
       disj_rewrite_not_all_prfstep, disj_split_conj_prfstep,
       disj_use_vardef_prfstep]

    ) #> fold add_fixed_sc (
      map (rpair 1) [
        "conj_goal_intro", "disj_state_intro", "imp_disj_state_intro",
        "forall_fact_intro", "ball_fact_intro", "exists_goal_intro",
        "bex_goal_intro", "disj_match_update", "disj_split_conj",
        "disj_use_vardef"
    ])

(* TERM_DEF *)
val TY_TERM_DEF = "TERM_DEF"
fun term_def_updt (id, (pat, th)) =
    let
      val ritem = Fact (TY_TERM_DEF, HOLogic.mk_prod (pat, Thm.prop_of th), th)
    in
      [Update.AddItems {id = id, raw_items = [ritem]}]
    end

fun match_term_def_fn rtype {ctxt, ...} item1 item2 =
    let
      val {id, tname, prop, ...} = item1
      val (pat, _) = HOLogic.dest_prod tname
      val insts =
          get_insts (TypedMatch (TY_TERM, pat)) item2 rtype (id, fo_init)

      fun process_inst ((id, inst), _) =
          Update.thm_update (id, subst_thm ctxt inst prop)
    in
      map process_inst insts
    end

val match_term_def_prfstep =
    {name = "match_term_def",
     args = [TypedMatch (TY_TERM_DEF, @{term_pat "?a"}),
             TypedMatch (TY_TERM, @{term_pat "?t"})],
     priority = PRIORITY_ADD,
     func = TwoStep match_term_def_fn}

fun CHOOSE_FUN_N n str ctxt =
    let
      val (new_vars, ex_prop) = read_choose_str str ctxt
      val _ = assert (length new_vars = 1)
                     "CHOOSE_FUN_N: only permit defining one function."

      (* Given a theorem about function f, for example

         !x. P (f x) & !y. Q (f x y),

         extract the properties of successive applications of f,
         returning them as term_def items. In the example above, the
         result would be [(f ?x, P (f ?x)), (f ?x ?y1), Q (f ?x ?y1)].
       *)
      fun prop_f_to_updt ctxt count id (f, prop_f_th) =
          case prop_of' prop_f_th of
              Const ("HOL.All", _) $ Abs (nm, T, _) =>
              let
                val sch_var = Var ((nm, count), T)
                val (ths, next) =
                    prop_f_th |> apply_to_thm (Conv.rewr_conv (
                                                  meta_sym @{thm atomize_all}))
                              |> Thm.forall_elim (cert ctxt sch_var)
                              |> split_conj_th |> split_last
                val pat = f $ sch_var
                fun to_updt th = term_def_updt (id, (pat, th))
              in
                if count = n - 1 then
                  maps to_updt (ths @ [next])
                else
                  maps to_updt ths @
                  prop_f_to_updt ctxt (count + 1) id (pat, next)
              end
            | _ => raise AUTO2 "CHOOSE_FUN_N: wrong form of prop_f_th."

      fun choose_callback ((id, th), {ctxt, ...}) =
          let
            val (ritems, th) =
                Update.apply_exists_ritems th ctxt (map fst new_vars)

            (* When choosing function F, this is the theorem !x. P (F i). *)
            val prop_f_th = th |> split_conj_th |> List.last
            val f = Free (the_single new_vars)
          in
            Update.AddItems {
              id = id, raw_items = ritems @ [Update.thm_to_ritem th]} ::
            prop_f_to_updt ctxt 0 id (f, prop_f_th)
          end
    in
      [Script_Task {inits = [Update.InitAssum (get_neg' ex_prop)], subs = [],
                    cb = choose_callback, end_vars = map Free new_vars}]
    end

val add_term_def_proofsteps =
    fold ItemIO_Data.add_item_type [
      (TY_TERM_DEF, NONE)

    ] #> fold ItemIO_Data.add_typed_matcher [
      (TY_TERM_DEF, ItemIO_Data.univ_matcher)

    ] #> add_prfstep match_term_def_prfstep

end  (* structure Logic_ProofSteps. *)

val _ = Theory.setup Logic_ProofSteps.add_logic_proofsteps
val _ = Theory.setup Logic_ProofSteps.add_disj_proofsteps
val _ = Theory.setup Logic_ProofSteps.add_term_def_proofsteps
val TY_DISJ = Logic_ProofSteps.TY_DISJ
val CHOOSE = Logic_ProofSteps.CHOOSE
val CHOOSES = Logic_ProofSteps.CHOOSES
val CHOOSE_FUN_N = Logic_ProofSteps.CHOOSE_FUN_N
val CHOOSE_FUN = CHOOSE_FUN_N 1
val CHOOSE_FUN2 = CHOOSE_FUN_N 2
