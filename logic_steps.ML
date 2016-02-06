(* Core (logic) proofsteps. *)

signature LOGIC_PROOFSTEPS =
sig
  val shadow_prop_item: proofstep
  val shadow_term_item: proofstep

  val exists_elim: box_id * thm -> Proof.context -> Update.raw_update list
  val normalize_pred_comm_conv: conv
  val swap_forall_imps_conv: int -> conv
  val swap_foralls_imps_conv: int list -> Proof.context -> conv
  val swap_ex_conjs_conv: int -> conv
  val swap_exs_conjs_conv: int list -> Proof.context -> conv
  val extract_vars: term list -> term list * int list
  val OBTAIN_FORALL: string -> pre_scripts
  val CHOOSE: string -> pre_scripts
  val CHOOSES: string list -> pre_scripts
  val not_ex_forall_cv: Proof.context -> conv
  val add_logic_proofsteps: theory -> theory

  val TY_DISJ: string
  val TY_DISJ_ACTIVE: string
  val imp_to_disj_cv: conv
  val to_disj_cv: Proof.context -> conv
  val not_ex_cv: Proof.context -> conv
  val forall_elim_sch: thm -> thm
  val analyze_disj_th: Proof.context -> thm -> bool * thm
  val disj_intro_gen: string * prfstep_descriptor list -> proofstep
  val disj_intro_prfsteps: proofstep list
  val disj_matcher: item_matcher

  val match_update_prfsteps: proofstep list
  val match_rewrite_prfsteps: proofstep list
  val add_match_one_sch_prfsteps: string * term -> theory -> theory
  val disj_create_case_prfstep: proofstep
  val disj_shadow_prfsteps: proofstep list
  val add_disj_proofsteps: theory -> theory
end;

structure Logic_ProofSteps : LOGIC_PROOFSTEPS =
struct

(* Shadowing based on equivalence. *)
fun shadow_item_fn is_subequiv rtype _ item1 item2 =
    let
      val (tbl as {lat, ...}) = RewriteTable.table_of_rtype rtype
      val id = merged_id lat [item1, item2]
      val (tname1, tname2) = (get_tname item1, get_tname item2)
      val equiv_fun = if is_subequiv then RewriteTable.subequiv_info
                      else RewriteTable.equiv_info
      val equiv_ids = (equiv_fun tbl id (tname1, tname2))
                          |> RewriteTable.replace_id_for_type' rtype |> map fst
                          |> max_partial (BoxID.is_eq_ancestor lat)
      val item_to_shadow =
          if #sc item1 < #sc item2 then item2 else item1
      fun process_id id' =
          Update.ShadowItem {id = id', item = item_to_shadow}
    in
      map process_id equiv_ids
    end

val shadow_prop_item =
    {name = "shadow_prop",
     args = [TypedMatch (TY_PROP, @{term_pat "?A::bool"}),
             TypedMatch (TY_PROP, @{term_pat "?B::bool"})],
     res_types = [Update.SHADOW_ITEM],
     func = TwoStep (shadow_item_fn false)}

val shadow_term_item =
    {name = "shadow_term",
     args = [TypedMatch (TY_TERM, @{term_pat "?A"}),
             TypedMatch (TY_TERM, @{term_pat "?B"})],
     res_types = [Update.SHADOW_ITEM],
     func = TwoStep (shadow_item_fn true)}

(* Given an assumption of the form EX x. A, we produce an assumption A
   with x in A replaced by a free variable. To avoid name collisions,
   when the update is produced x is replaced by an "internal" free
   variable, with suffix '_'. When the update is applied, that
   internal free variable is replaced by a fresh variable as
   determined by the context.
 *)
fun exists_elim (id, th) ctxt =
    let
      val nm = case prop_of' th of
                   Const ("HOL.Ex", _) $ Abs (nm, _, _) => Name.internal nm
                 | _ => raise AUTO2 "exists_elim: unexpected inst for A"
    in
      Update.apply_exists (id, th) ctxt [nm]
    end

(* Normalize order of existence and forall statements. *)
fun normalize_pred_comm_conv ct =
    let
      val cv = Conv.try_conv (
            Conv.first_conv (map rewr_obj_eq [@{thm ex_comm}, @{thm all_comm}]))
      val th = cv ct
    in
      if Term_Ord.termless (Thm.prop_of th |> Logic.dest_equals) then th
      else Conv.all_conv ct
    end

(* Given ct of the form !x. P1 --> P2 --> ... --> Pn --> Q x,
   rewriting it to P1 --> P2 --> ... --> Pn --> !x. Q x. Here n
   specifies the number of imps to move out.
*)
fun swap_forall_imps_conv n =
    if n = 0 then Conv.all_conv
    else (rewr_obj_eq @{thm swap_forall_imp})
             then_conv (Conv.arg_conv (swap_forall_imps_conv (n-1)))

(* Given ct of the form !v1 ... vn. P1 --> ... --> Pk --> Q, rewrite
   it to one with i0 imps before foralls, i1 imps after !v1, ...,
   i_{n-1} imps after !v_{n-1}, and remaining ones after !vn, where
   [i0, i1, ..., i_{n-1}] is the given list counts.
 *)
fun swap_foralls_imps_conv counts ctxt ct =
    case counts of
        [] => Conv.all_conv ct
      | n :: ns =>
        case Thm.term_of ct of
            Const (@{const_name HOL.All}, _) $ Abs _ =>
            let
              val ns' = map (fn n' => n' + n) ns
            in
              ((Conv.binder_conv ((swap_foralls_imps_conv ns') o snd) ctxt)
                   then_conv (swap_forall_imps_conv n)) ct
            end
          | _ => raise AUTO2 "swap_foralls_imps_conv: not enough foralls."

(* Similar to swap_forall_imps_conv, for EX and &. *)
fun swap_ex_conjs_conv n =
    if n = 0 then Conv.all_conv
    else (rewr_obj_eq @{thm swap_ex_conj})
             then_conv (Conv.arg_conv (swap_ex_conjs_conv (n-1)))

(* Similar to swap_foralls_imps_conv, for EX and &. *)
fun swap_exs_conjs_conv counts ctxt ct =
    case counts of
        [] => Conv.all_conv ct
      | n :: ns =>
        case Thm.term_of ct of
            Const (@{const_name HOL.Ex}, _) $ Abs _ =>
            let
              val ns' = map (fn n' => n' + n) ns
            in
              ((Conv.binder_conv ((swap_exs_conjs_conv ns') o snd) ctxt)
                   then_conv (swap_ex_conjs_conv n)) ct
            end
          | _ => raise AUTO2 "swap_exs_conjs_conv: not enough exists."

(* Extract from a mixed list of variables and conditions the list of
   variables, and the number of conditions in front of each
   variable. For example: C1 v1 C2 C3 v2 C4 would return ([v1, v2],
   [1, 2]). This is used in OBTAIN_FORALL and CHOOSE below.
 *)
fun extract_vars conds =
    case conds of
        cond :: conds' =>
        let
          val (vars', counts') = extract_vars conds'
        in
          if Term.is_Free cond then
            (cond :: vars', 0 :: counts')
          else
            (vars', if counts' = [] then [] else (hd counts' + 1) :: tl counts')
        end
      | _ => ([], [])

fun OBTAIN_FORALL str ctxt =
    let
      val ts = Syntax.read_term ctxt ("(" ^ str ^ ")") |> HOLogic.strip_tuple
      val (conds, concl) = split_last ts
      val (vars, counts) = extract_vars conds
      val nms = map (fst o Term.dest_Free) vars
      val _ = assert (not (exists (Variable.is_fixed ctxt) nms))
                     ("OBTAIN_FORALL: variable name(s) already used.")
      fun obtain_forall_callback (id, th) =
          let
            val ctxt' = ctxt |> fold declare_free_term vars
            val th' = apply_to_thm (
                  Conv.arg_conv (swap_foralls_imps_conv counts ctxt')) th
          in
            [Update.thm_update (id, th')]
          end
      val assums = map HOLogic.mk_Trueprop (filter_out Term.is_Free conds)
      val concls = [HOLogic.mk_Trueprop concl]
    in
      [Script_Task {vars = vars, assums = assums, subs = [], concls = concls,
                    cb = obtain_forall_callback, end_vars = []}]
    end

fun CHOOSE str ctxt =
    let
      val ts = Syntax.read_term ctxt ("(" ^ str ^ ")") |> HOLogic.strip_tuple
      val (vars, counts) = extract_vars ts

      (* Form proposition EX [vars]. [conds]. *)
      val cond = ts |> filter_out Term.is_Free
                    |> ACUtil.list_ac conj_ac
      val dest_vars = map Term.dest_Free vars
      fun mk_exists' (nm, T) cond = HOLogic.mk_exists (nm, T, cond)
      val ex_cond = cond |> fold mk_exists' (rev dest_vars)
                         |> HOLogic.mk_Trueprop

      (* Check the variable names are new, and add to ctxt. *)
      val nms = map fst dest_vars
      val _ = assert (not (exists (Variable.is_fixed ctxt) nms))
                     ("CHOOSE: variable name(s) already used.")

      val ctxt' = ctxt |> fold declare_free_term vars
      val eq_th = Conv.arg_conv (swap_exs_conjs_conv counts ctxt')
                                (cert ctxt' ex_cond)
      val ex_cond' = rhs_of eq_th
      fun choose_callback (id, th) =
          let
            val th' = Thm.equal_elim (meta_sym eq_th) th
          in
            Update.apply_exists (id, th') ctxt' nms
          end
    in
      [Script_Task {vars = [], assums = [], subs = [], concls = [ex_cond'],
                    cb = choose_callback, end_vars = vars}]
    end

fun CHOOSES strs =
    case strs of
        [str] => CHOOSE str
      | str :: rest => (CHOOSE str) THEN (CHOOSES rest)
      | _ => raise AUTO2 "CHOOSES: empty argument"

(* Move "not" inside exists and foralls. *)
fun not_ex_forall_cv ctxt ct =
    case Thm.term_of ct of
        @{const Not} $ (Const ("HOL.Ex", _) $ _) =>
        (* ~ EX x. P x to ALL x. ~ P x. *)
        ((rewr_obj_eq @{thm HOL.not_ex})
             then_conv (Conv.binder_conv (not_ex_forall_cv o snd) ctxt)) ct
      | @{const Not} $ (Const ("HOL.All", _) $ _) =>
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

val add_logic_proofsteps =
    fold add_prfstep [
      shadow_prop_item, shadow_term_item

    ] #> fold add_prfstep_custom [
      ("exists_elim",
       [WithFact @{term_pat "EX x. ?A x"}],
       [Update.ADD_ITEMS],
       fn ((id, _), ths) => fn _ => fn {ctxt, ...} =>
          exists_elim (id, the_single ths) ctxt),

      ("not_forall_elim",
       [WithGoal @{term_pat "!x. ?P x"}],
       [Update.ADD_ITEMS],
       fn ((id, _), ths) => fn _ => fn {ctxt, ...} =>
          let
            val cv = Conv.arg_conv (rewr_obj_eq @{thm HOL.not_all})
            val th = ths |> the_single |> apply_to_thm cv
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
        ShadowFirst])

    ] #> fold add_prfstep_pre_conv [
      ("rewrite_not_ex", [WithTerm @{term_pat "~ (EX x. ?P x)"}],
       not_ex_forall_cv)

    ] #> add_conv_normalizer ("normalize_pred", normalize_pred_comm_conv)

(* Disjunctive mutable states. *)
val dest_disj_prop = ACUtil.dest_ac disj_ac o prop_of'
fun dest_disj_subterms thy th =
    if length (dest_disj_prop th) = 1 then Subterms.triv_subterms (prop_of' th)
    else Subterms.dest_subterms thy false (prop_of' th)
val TY_DISJ = "DISJ"
val TY_DISJ_ACTIVE = "DISJ_ACTIVE"
fun TY_DISJ_of is_active = if is_active then TY_DISJ_ACTIVE else TY_DISJ
fun get_DISJ_is_active ty_str =
    case ty_str of "DISJ" => false | "DISJ_ACTIVE" => true
                   | _ => raise AUTO2 "get_DISJ_is_active: wrong ty_str."

fun disj_to_update is_active (id, th) =
    if Thm.prop_of th aconv prop_False then
      Update.ResolveBox {id = id, th = th}
    else
      let
        val subs = dest_disj_prop th
        val ty_str = if length subs = 1 andalso not (has_vars (Thm.prop_of th))
                     then TY_PROP else TY_DISJ_of is_active
        val tname = HOLogic.mk_tuple subs
      in
        Update.AddItems {id = id, raw_items = [Fact (ty_str, tname, th)]}
      end

(* Convert term of form A_1 --> ... --> A_n to ~A_1 | ... | ~A_(n-1) |
   A_n. Note each A_i remains the same.
 *)
fun imp_to_disj_cv ct =
    case Thm.term_of ct of
        Const ("HOL.implies", _) $ _ $ _ =>
        (rewr_obj_eq @{thm imp_conv_disj}
                          then_conv (Conv.arg_conv imp_to_disj_cv)) ct
      | _ => Conv.all_conv ct

(* Convert proposition of form A_1 --> ... --> A_n to ~A_1 | ... |
   ~A_(n-1) | A_n. Expand any ~A_i of form ~(A_i1 & ... & A_in) using
   de Morgan's law. This converts any statements of form A | B, ~(A &
   B), and A --> B to disjunction form.
 *)
fun to_disj_cv ctxt =
    let
      val cv_imp = Conv.arg_conv imp_to_disj_cv
      val cv_deMorgan = rewr_obj_eq_top @{thm de_Morgan_conj} ctxt
      val cv_nn = rewr_obj_eq_top nn_cancel_th ctxt
      val cv_assoc = Conv.arg_conv (ACUtil.normalize_assoc disj_ac)
      val cv_comm = Conv.arg_conv (ACUtil.normalize_cu disj_ac)
    in
      cv_imp then_conv cv_deMorgan then_conv cv_nn then_conv cv_assoc
             then_conv cv_comm
    end

(* Convert term of form ~ (EX x y. P x y) to !x y. ~ P x y (arbitrary
   number of existence quantifiers).
 *)
fun not_ex_cv ctxt ct =
    case Thm.term_of ct of
        Const ("HOL.Not", _) $ (Const ("HOL.Ex", _) $ _) =>
        ((rewr_obj_eq @{thm HOL.not_ex})
             then_conv (Conv.binder_conv (not_ex_cv o snd) ctxt))
            ct
      | _ => Conv.all_conv ct

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
      val th' = th |> apply_to_thm (Conv.arg_conv (not_ex_cv ctxt))
                   |> apply_to_thm (to_meta_all_conv ctxt)
                   |> forall_elim_sch
      val is_active =
          case prop_of' th' of
              Const ("HOL.Not", _) $ (Const ("HOL.conj", _) $ _ $ _) => true
            | Const ("HOL.disj", _) $ _ $ _ => true
            | _ => false
      val disj_th = apply_to_thm (to_disj_cv ctxt) th'
    in
      (is_active, disj_th)
    end

(* Template for proofsteps constructing DISJ / DISJ_ACTIVE items from
   propositions.
 *)
fun disj_intro_gen (name, desc) =
    prfstep_custom
        name desc [Update.ADD_ITEMS]
        (fn ((id, _), ths) => fn _ => fn {ctxt, ...} =>
            let
              val (is_active, disj_th) = analyze_disj_th ctxt (the_single ths)
            in
              [disj_to_update is_active (id, disj_th)]
            end)

(* Introduction rules for DISJ / DISJ_ACTIVE. *)
val disj_intro_prfsteps = map disj_intro_gen [
      ("conj_goal_intro",
       [WithGoal @{term_pat "?A & ?B"},
        Filter (canonical_split_filter @{const_name conj} "A" "B")]),
      ("disj_state_intro",
       [WithFact @{term_pat "?A | ?B"},
        Filter (canonical_split_filter @{const_name disj} "A" "B")]),
      ("imp_disj_state_intro", [WithFact @{term_pat "?A --> ?B"}]),
      ("forall_fact_intro", [WithFact @{term_pat "!x. ?P x"}]),
      ("exists_goal_intro", [WithFact @{term_pat "~ (EX x. ?P x)"}])]

(* Pre-matching function for DISJ / DISJ_ACTIVE items. There are only
   three possible patterns to consider: ?C | ?D, ?C = ?D, and ?C. No
   rewriting is needed for pre-matching. Matching is not implemented.
 *)
val disj_matcher =
    let
      val pat_or = @{term_pat "?C | ?D"}
      val pat_eq = @{term_pat "?C = ?D"}
      val pat_single = @{term_pat "?C::bool"}

      fun pre_match pat {tname, ...} {ctxt, ...} =
          let
            val subs = HOLogic.strip_tuple tname
          in
            if pat aconv pat_or then length subs >= 2
            else if pat aconv pat_eq then
              length subs = 1 andalso is_eq_term tname
            else if pat aconv pat_single then length subs = 1
            else if length subs > 1 then false
            else let val _ = pattern_fo_match ctxt (pat, tname) in true end
                 handle Pattern.MATCH => false
          end

      fun match _ _ _ _ =
          raise AUTO2 "disj_matcher: matching not implemented."
    in
      {pre_match = pre_match, match = match}
    end

(* Reduce a disjunction p_1 | ... | t | ... | p_n by matching ~t with
   the second item. If the disjunction contains schematic variables, t
   must have either zero or the largest number of schematic variables.
 *)
fun match_update_fn rtype (st as {ctxt, ...}) item1 item2 =
    let
      val {id, ty_str, tname, prop, ...} = item1
      val is_active = get_DISJ_is_active ty_str
      val thy = Status.theory_of st
      fun count_var t = length (Term.add_vars t [])
      val subs = HOLogic.strip_tuple tname
      val max_nvar = fold (curry Int.max) (map count_var subs) 0

      (* Match the negation of subs[i] with th2. For each match,
         instantiate in prop all schematic variables in t, so that t
         becomes ~th2. Then remove t from prop in the instantiated
         version.
       *)
      fun get_matches i =
          if count_var (nth subs i) > 0 andalso
             count_var (nth subs i) < max_nvar then [] else
          let
            val t = nth subs i
            val insts =
                get_insts (PropMatch (get_neg t)) item2 rtype (id, fo_init)
            fun process_inst ((id', inst), th) =
                let
                  val teqF = to_meta_eq (to_eqF_th th)
                  val prop_inst = prop |> subst_thm_thy thy inst
                  val (prop_inst', subs') = dest_disj_subterms thy prop_inst
                  val base_equivs = map (Thm.reflexive o cert ctxt) subs'
                  val equivs = take i base_equivs @ [teqF] @
                               drop (i+1) base_equivs
                  val prop_equiv =
                      (Subterms.build_equiv ctxt equivs prop_inst')
                          |> apply_to_rhs (ACUtil.normalize_unit disj_ac)
                          |> make_trueprop_eq
                  val prop_new = Thm.equal_elim prop_equiv prop_inst
                  val shadow_updt = if count_var (nth subs i) > 0 then [] else
                                    [Update.ShadowItem {id = id', item = item1}]
                in
                  [disj_to_update is_active (id', prop_new)] @ shadow_updt
                end
          in
            maps process_inst insts
          end
    in
      maps get_matches (0 upto (length subs - 1))
    end

fun match_update_templ (is_active, is_resolve) =
    let
      val name = "disj_match_update" ^ (if is_active then "@active" else "") ^
                 (if is_resolve then "@resolve" else "")
      val arg1_pat = if is_resolve then @{term_pat "?C::bool"}
                     else @{term_pat "?C | ?D"}
      val res_types =
          if is_resolve then [Update.SHADOW_ITEM, Update.RESOLVE_BOX]
          else [Update.SHADOW_ITEM, Update.ADD_ITEMS]
    in
      {name = name,
       args = [TypedMatch (TY_DISJ_of is_active, arg1_pat),
               PropMatch @{term_pat "?A::bool"}],
       res_types = res_types,
       func = TwoStep match_update_fn}
    end

val match_update_prfsteps = map match_update_templ [
      (false, false), (false, true), (true, false), (true, true)]

(* When the disj has one equality term (with schematic variables), use
   it as a bidirectional rewriting rule.
 *)
fun match_rewrite_fn rtype st {id, prop = th1, ...} item2 =
    let
      val thy = Status.theory_of st
      val (lhs, rhs) = th1 |> prop_of' |> HOLogic.dest_eq

      val lhs_vars = map Var (Term.add_vars lhs [])
      val rhs_vars = map Var (Term.add_vars rhs [])
      val insts =
          (if subset (op aconv) (rhs_vars, lhs_vars) then
             get_insts (TypedMatch (TY_TERM, lhs)) item2 rtype (id, fo_init)
           else []) @
          (if subset (op aconv) (lhs_vars, rhs_vars) then
             get_insts (TypedMatch (TY_TERM, rhs)) item2 rtype (id, fo_init)
           else [])

      fun inst_to_updt ((id', inst), _) =
          Update.thm_update (id', subst_thm_thy thy inst th1)
    in
      map inst_to_updt insts
    end

fun match_rewrite_templ is_active =
    {name = "match_rewrite" ^ (if is_active then "@active" else ""),
     args = [TypedMatch (TY_DISJ_of is_active, @{term_pat "?C = ?D"}),
             TypedMatch (TY_TERM, @{term_pat "?A"})],
     res_types = [Update.ADD_ITEMS],
     func = TwoStep match_rewrite_fn}

val match_rewrite_prfsteps = map match_rewrite_templ [true, false]

(* When the disj has one term containing one schematic variable, match
   with all variables of the same type.
 *)
fun match_one_sch_fn rtype {lat, ctxt, ...} {id, prop = th1, ...}
                     {id = id', tname, ...} =
    if not (RewriteTable.is_single_rtype rtype) then [] else
    let
      val stmt = prop_of' th1
      val sch_var = Var (the_single (Term.add_vars stmt []))
    in
      if fastype_of sch_var <> fastype_of tname then []
      else let
        val id'' = BoxID.merge_boxes lat (id, id')
        val th' = th1 |> Thm.forall_intr (cert ctxt sch_var)
                      |> Thm.forall_elim (cert ctxt tname)
      in
        [Update.thm_update (id'', th')]
      end
    end

fun match_one_sch_templ nm pat is_active =
    {name = "match_one_sch_" ^ nm ^ (if is_active then "@active" else ""),
     args = [TypedMatch (TY_DISJ_of is_active, pat),
             TypedMatch (TY_VAR, @{term_pat "?FREE"})],
     res_types = [Update.ADD_ITEMS],
     func = TwoStep match_one_sch_fn}

fun add_match_one_sch_prfsteps (nm, pat) =
    fold add_prfstep (map (match_one_sch_templ nm pat) [true, false])

(* For active case, create box checking the next case. *)
fun disj_create_case_fn rtype _ {id, tname, ty_str, ...} =
    if not (RewriteTable.is_single_rtype rtype) then [] else
    if has_vars tname then [] else
    let
      val _ = assert (ty_str = TY_DISJ_ACTIVE) "disj_concl_active: wrong type."
      val subs = HOLogic.strip_tuple tname
    in
      if length subs = 1 then []
      else [Update.AddBoxes {id = id, vars = [],
                             assums = [HOLogic.mk_Trueprop (hd subs)],
                             concls = [], cb = Update.null_callback}]
    end

val disj_create_case_prfstep =
    {name = "disj_create_case",
     args = [TypedMatch (TY_DISJ_ACTIVE, @{term_pat "?C | ?D"})],
     res_types = [Update.ADD_BOXES],
     func = OneStep disj_create_case_fn}

(* item1 dominates item2 if the disjunctive terms in item1 is a subset
   of that for item2.
 *)
fun disj_shadow_fn rtype _ item1 item2 =
    if not (RewriteTable.is_single_rtype rtype) then [] else
    let
      val {lat, ...} = RewriteTable.table_of_rtype rtype
      val id = merged_id lat [item1, item2]
    in
      if subset (op aconv) (apply2 (HOLogic.strip_tuple o get_tname)
                                   (item1, item2)) then
        [Update.ShadowItem {id = id, item = item2}]
      else []
    end

fun disj_shadow_templ (suffix, ty_str1, ty_str2) =
    {name = "disj_shadow" ^ suffix,
     args = [TypedMatch (ty_str1, @{term_pat "?C | ?D"}),
             TypedMatch (ty_str2, @{term_pat "?C | ?D"})],
     res_types = [Update.SHADOW_ITEM],
     func = TwoStep disj_shadow_fn}

val disj_shadow_prfsteps = map disj_shadow_templ [
      ("", TY_DISJ, TY_DISJ), ("@active", TY_DISJ_ACTIVE, TY_DISJ_ACTIVE),
      ("@mixed", TY_DISJ_ACTIVE, TY_DISJ)]

val add_disj_proofsteps =
    fold ItemIO_Data.add_item_type [
      (TY_DISJ, NONE), (TY_DISJ_ACTIVE, NONE)

    ] #> fold ItemIO_Data.add_typed_matcher [
      (TY_DISJ, disj_matcher), (TY_DISJ_ACTIVE, disj_matcher)

    ] #> fold add_prfstep (
      disj_intro_prfsteps @
      match_update_prfsteps @ match_rewrite_prfsteps @
      [disj_create_case_prfstep] @
      disj_shadow_prfsteps

    ) #> fold add_fixed_sc (
      map (rpair 1) [
        "conj_goal_intro", "disj_state_intro", "imp_disj_state_intro",
        "forall_fact_intro", "exists_goal_intro", "disj_match_update",
        "disj_match_update@active"
    ])

end  (* structure Logic_ProofSteps. *)

val _ = Theory.setup Logic_ProofSteps.add_logic_proofsteps
val _ = Theory.setup Logic_ProofSteps.add_disj_proofsteps
val OBTAIN_FORALL = Logic_ProofSteps.OBTAIN_FORALL
val CHOOSE = Logic_ProofSteps.CHOOSE
val CHOOSES = Logic_ProofSteps.CHOOSES
