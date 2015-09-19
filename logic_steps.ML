(* Core (logic) proofsteps. *)

signature LOGIC_PROOFSTEPS =
sig
  val shadow_item: bool -> proofstep_fn
  val add_logic_proofsteps: theory -> theory
  val normalize_pred_comm: conv

  val TY_DISJ: string
  val TY_DISJ_ACTIVE: string
  val imp_to_disj_cv: conv
  val to_disj_cv: Proof.context -> conv
  val not_ex_cv: Proof.context -> conv
  val forall_elim_sch: thm -> thm
  val analyze_disj_th: Proof.context -> thm -> bool * thm
  val disj_intro_gen: string * prfstep_descriptor list -> proofstep

  val disj_to_update: bool -> box_id * thm -> Update.raw_update
  val disj_update_gen:
      (box_id -> rewrite_type -> thm * box_item -> (box_id * thm) list) *
      string * (term -> bool) * pre_filter -> proofstep list
  val disj_self_update_gen:
      (box_id -> rewrite_type -> thm -> (box_id * thm) list) *
      string * (term -> bool) -> proofstep list
  val eq_update:
      box_id -> rewrite_type -> thm * box_item -> (box_id * thm) list
  val match_update_fn: proofstep_fn
  val match_update: string * (term -> bool) * string -> proofstep list
  val disj_create_case: proofstep_fn
  val disj_shadow: proofstep_fn
  val add_disj_proofsteps: theory -> theory
end;

structure Logic_ProofSteps : LOGIC_PROOFSTEPS =
struct

(* Shadowing based on equivalence. *)
fun shadow_item is_subequiv items rtype {lat, ...} =
    let
      val id = merged_id rtype items
      val (item1, item2) = the_pair items
      val (tname1, tname2) = (get_single_tname item1, get_single_tname item2)
      val equiv_fun = if is_subequiv then RewriteTable.subequiv_info
                      else RewriteTable.equiv_info
      val tbl = RewriteTable.table_of_rtype rtype
      val equiv_ids = (equiv_fun tbl id (tname1, tname2))
                          |> RewriteTable.replace_id_for_type' rtype |> map fst
                          |> max_partial (BoxID.is_eq_ancestor lat)
      fun process_id id' =
          if id' = id_of_item item1 then
            Update.ShadowItem {id = id', item = hd items}
          else Update.ShadowItem {id = id', item = nth items 1}
    in
      map process_id equiv_ids
    end
val shadow_prop_filt = replicate 2 {ty_str = TY_PROP, pre_filt = no_prereq_fn}
val shadow_term_filt = replicate 2 {ty_str = TY_TERM, pre_filt = no_prereq_fn}

(* Given an assumption of the form EX x. A, we produce an assumption A
   with x in A replaced by a free variable. To avoid name collisions,
   when the update is produced x is replaced by an "internal" free
   variable, with suffix '_'. When the update is applied, that
   internal free variable is replaced by a fresh variable as
   determined by the context.
 *)
val exists_elim =
    prfstep_custom
        @{theory} "exists_elim"
        [WithFact @{term_pat "EX x. ?A x"}]
        [Update.ADD_ITEMS]
        (fn ((id, inst), ths) => fn {tbl, ctxt, ...} =>
            let
              val (nm, T, body) =
                  case lookup_inst inst "A" of
                      Abs (nm, T, body) => (Name.internal nm, T, body)
                    | _ => raise AUTO2 "exists_elim: unexpected inst for A"

              (* Whether A is the body of a trivial exists statement. *)
              val detect_trivial =
                  case Term.subst_bound (Var (("u_",0), T), body) of
                      Const ("HOL.eq", _) $ A $ B =>
                      if has_vars A andalso has_vars B then false else
                      let
                        val (pat, trm) = if has_vars A then (A, B) else (B, A)
                        val insts = (fo_table_match id tbl (pat, trm))
                                        |> filter (fn ((id', _), _) => id = id')
                      in
                        length insts <> 0
                      end
                    | _ => false
            in
              if detect_trivial then []
              else Update.apply_exists (id, the_single ths) ctxt [nm]
            end)

(* Normalize order of existence and forall statements. *)
fun normalize_pred_comm ct =
    let
      val cv = Conv.try_conv (
            Conv.first_conv (map rewr_obj_eq [@{thm ex_comm}, @{thm all_comm}]))
      val th = cv ct
    in
      if Term_Ord.termless (Thm.prop_of th |> Logic.dest_equals) then th
      else Conv.all_conv ct
    end

val add_logic_proofsteps =
    fold add_prfstep [
      {name = "shadow_prop", filt = shadow_prop_filt,
       res_types = [Update.SHADOW_ITEM], func = shadow_item false},
      {name = "shadow_term", filt = shadow_term_filt,
       res_types = [Update.SHADOW_ITEM], func = shadow_item true},
      exists_elim

    ] #> fold add_eq_th_normalizer [
      @{thm exists_split}, @{thm exists_split'}

    ] #> add_conv_normalizer ("normalize_pred", normalize_pred_comm)

(* Disjunctive mutable states. *)
val disj_ac = the (lookup_ac_data @{theory} @{const_name disj})
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
      in
        Update.AddItems {id = id, raw_items = [Fact (ty_str, subs, th)]}
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
      val cv_assoc = Conv.arg_conv (ACUtil.rearrange_assoc disj_ac)
    in
      cv_imp then_conv cv_deMorgan then_conv cv_nn then_conv cv_assoc
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

fun disj_intro_gen (name, desc) =
    prfstep_custom
        @{theory} name desc [Update.ADD_ITEMS]
        (fn ((id, _), ths) => fn {ctxt, ...} =>
            let
              val (is_active, disj_th) = analyze_disj_th ctxt (the_single ths)
            in
              [disj_to_update is_active (id, disj_th)]
            end)

(* A generic function for disj_update. Input a function f which takes
   a term t and tries to justify ~t using rtype and item. The output
   of f is a list of (id', th) pairs, where th is of form ~t.
 *)
fun disj_update_gen_fn f items rtype (st as {ctxt, ...}) =
    let
      val ((item1 as {id = id1, ...}), item2) = the_pair items
      val is_active = get_DISJ_is_active (get_ty_str item1)
      val sval = get_thm item1
      val thy = Status.theory_of st
      val tbl = RewriteTable.table_of_rtype rtype

      (* For each t, find rewrites of t to False using rtype and
         item. Convert to meta_eq and add t == t if necessary.
       *)
      fun get_rewrs t =
          if has_vars t then []
          else let
            val prop = t |> HOLogic.mk_Trueprop
            val t_th = prop |> assume_thm ctxt
            fun process_resolve (id', contra_th) =
                (id', contra_th |> Thm.implies_intr (cert ctxt prop)
                                |> rewrite_thm_from_contra_form
                                |> to_eqF_th |> to_meta_eq)
            val all_rewrs = map process_resolve (f id1 rtype (t_th, item2))
          in
            if exists (fn (id', _) => id' = id1) all_rewrs then all_rewrs
            else (id1, Thm.reflexive (cert ctxt t)) :: all_rewrs
          end

      val (sval', subs) = dest_disj_subterms thy sval
      val ac_len = length subs
      fun no_new_rewrs rewrs = (length rewrs = 1 andalso
                                Thm.is_reflexive (snd (hd rewrs)))
      val rewrs_subs = map get_rewrs subs
    in
      if forall no_new_rewrs rewrs_subs then [] else
      (RewriteTable.merge_simp_infos tbl rewrs_subs)
          |> map (apsnd (fn equivs => Subterms.build_equiv ctxt equivs sval'))
          |> map (apsnd (apply_to_rhs (ACUtil.rearrange_subterms disj_ac)))
          |> RewriteTable.reduce_simp_info tbl
          |> map (apsnd (fn eq_th =>
                            Thm.equal_elim (make_trueprop_eq eq_th) sval))
          |> filter (fn (_, th') => length (dest_disj_prop th') < ac_len)
          |> maps (fn (id, th) => [disj_to_update is_active (id, th),
                                   Update.ShadowItem {id = id, item = item1}])
    end

fun disj_update_gen (f, name, filt1, filt2) =
    let
      fun pre_filt1 _ {tname, ...} = exists filt1 tname
      fun filt is_active =
          [{ty_str = TY_DISJ_of is_active, pre_filt = pre_filt1}, filt2]
      fun res is_active =
          {name = name ^ (if is_active then "@active" else ""),
           filt = filt is_active,
           res_types = [
             Update.ADD_ITEMS, Update.RESOLVE_BOX, Update.SHADOW_ITEM],
           func = disj_update_gen_fn f}
    in
      map res [true, false]
    end

(* A generic function for disj_self_update. Input a function f which
   takes a term t and tries to justify ~t using rtype. The output of f
   is a list of (id', th) pairs, where th is of form ~t.
 *)
fun disj_self_update_gen_fn f items rtype (st as {ctxt, ...}) =
    let
      val (item as {id, ...}) = the_single items
      val is_active = get_DISJ_is_active (get_ty_str item)
      val sval = get_thm item
      val thy = Status.theory_of st
      val tbl = RewriteTable.table_of_rtype rtype

      (* For each t, find rewrites of t to False using rtype. Convert
         to meta_eq and add t == t if necessary.
       *)
      fun get_rewrs t =
          if has_vars t then []
          else let
            val prop = t |> HOLogic.mk_Trueprop
            val t_th = prop |> assume_thm ctxt
            fun process_resolve (id', contra_th) =
                (id', contra_th |> Thm.implies_intr (cert ctxt prop)
                                |> rewrite_thm_from_contra_form
                                |> to_eqF_th |> to_meta_eq)
            val all_rewrs = map process_resolve (f id rtype t_th)
          in
            if exists (fn (id', _) => id' = id) all_rewrs then all_rewrs
            else (id, Thm.reflexive (cert ctxt t)) :: all_rewrs
          end

      val (sval', subs) = dest_disj_subterms thy sval
      val ac_len = length subs
      fun no_new_rewrs rewrs = (length rewrs = 1 andalso
                                Thm.is_reflexive (snd (hd rewrs)))
      val rewrs_subs = map get_rewrs subs
    in
      if forall no_new_rewrs rewrs_subs then [] else
      rewrs_subs
          |> RewriteTable.merge_simp_infos tbl
          |> map (apsnd (fn equivs => Subterms.build_equiv ctxt equivs sval'))
          |> map (apsnd (apply_to_rhs (ACUtil.rearrange_subterms disj_ac)))
          |> RewriteTable.reduce_simp_info tbl
          |> map (apsnd (fn eq_th =>
                            Thm.equal_elim (make_trueprop_eq eq_th) sval))
          |> filter (fn (_, th') => length (dest_disj_prop th') < ac_len)
          |> maps (fn (id, th) => [disj_to_update is_active (id, th),
                                   Update.ShadowItem {id = id, item = item}])
    end

fun disj_self_update_gen (f, name, filt) =
    let
      fun pre_filt _ {tname, ...} = exists filt tname
      fun filt is_active =
          [{ty_str = TY_DISJ_of is_active, pre_filt = pre_filt}]
      fun res is_active =
          {name = name ^ (if is_active then "@active" else ""),
           filt = filt is_active,
           res_types = [
             Update.ADD_ITEMS, Update.RESOLVE_BOX, Update.SHADOW_ITEM],
           func = disj_self_update_gen_fn f}
    in
      map res [true, false]
    end

(* Simplest case: simply match ~th with item. *)
fun eq_update id rtype (th, item) =
    let
      val negt = Thm.prop_of th |> get_neg'
      val insts = get_insts [ItemIO_Data.univ_matcher] [negt] [item] rtype
      val {lat, ...} = RewriteTable.table_of_rtype rtype
      fun process_inst ((id', _), ths) =
          (BoxID.merge_boxes lat (id, id'),
           if is_neg (prop_of' th) then
             [th, the_single ths] MRS @{thm contra_triv}
           else [the_single ths, th] MRS @{thm contra_triv})
    in
      map process_inst insts
    end

(* Next simplest case: match a term with the largest number of
   schematic variables with item.
 *)
fun match_update_fn items rtype (st as {lat, ctxt, ...}) =
    let
      val (item1, item2) = the_pair items
      val is_active = get_DISJ_is_active (get_ty_str item1)
      val id = merged_id rtype items
      val sval = get_thm item1
      val thy = Status.theory_of st
      val subs = get_tname item1
      fun count_var t = length (Term.add_vars t [])
      val max_nvar = fold (curry Int.max) (map count_var subs) 0

      (* Match the negation of subs[i] with th2. For each match,
          instantiate in sval all schematic variables in t, so that t
          becomes ~th2. Then remove t from sval in the instantiated
          version.
       *)
      fun get_matches i =
          if count_var (nth subs i) < max_nvar then [] else
          let
            val t = nth subs i
            val negt = HOLogic.mk_Trueprop (get_neg t)
            val insts =
                get_insts [ItemIO_Data.univ_matcher] [negt] [item2] rtype
            fun process_inst ((id', inst), ths) =
                let
                  val teqF = to_meta_eq (to_eqF_th (the_single ths))
                  val sval_inst = sval |> subst_thm_thy thy inst
                  val (sval_inst', subs') = dest_disj_subterms thy sval_inst
                  val base_equivs = map (Thm.reflexive o cert ctxt) subs'
                  val equivs = take i base_equivs @ [teqF] @
                               drop (i+1) base_equivs
                  val sval_equiv =
                      (Subterms.build_equiv ctxt equivs sval_inst')
                          |> apply_to_rhs (ACUtil.rearrange_subterms disj_ac)
                          |> make_trueprop_eq
                  val sval_new = Thm.equal_elim sval_equiv sval_inst
                in
                  disj_to_update
                      is_active (BoxID.merge_boxes lat (id, id'), sval_new)
                end
          in
            map process_inst insts
          end
    in
      maps get_matches (0 upto (length subs - 1))
    end

fun match_update (name, filt, ty_str2) =
    let
      fun pre_filt1 _ {tname, ...} = exists filt tname
      fun filt is_active =
          [{ty_str = TY_DISJ_of is_active, pre_filt = pre_filt1},
           {ty_str = ty_str2, pre_filt = no_prereq_fn}]
      fun res is_active =
          {name = name ^ (if is_active then "@active" else ""),
           filt = filt is_active,
           res_types = [Update.ADD_ITEMS, Update.RESOLVE_BOX],
           func = match_update_fn}
    in
      map res [true, false]
    end

(* When the disj has one equality term (with schematic variables), use
   it as a bidirectional rewriting rule.
 *)
fun match_rewrite_fn items rtype (st as {tbl, ...}) =
    let
      val (item1, item2) = the_pair items
      val id = merged_id rtype items
      val sval = get_thm item1
      val thy = Status.theory_of st
      val (lhs, rhs) = sval |> prop_of' |> HOLogic.dest_eq
      fun insts t = (ItemIO_Data.term_match t item2 tbl (id, fo_init))
                        |> RewriteTable.replace_id_for_type rtype
      fun inst_to_updt ((id, inst), _) =
          Update.thm_update thy (id, subst_thm_thy thy inst sval)
      val lhs_vars = map Var (Term.add_vars lhs [])
      val rhs_vars = map Var (Term.add_vars rhs [])
      val match_sides =
          (if subset (op aconv) (rhs_vars, lhs_vars) then [lhs] else []) @
          (if subset (op aconv) (lhs_vars, rhs_vars) then [rhs] else [])
    in
      map inst_to_updt (maps insts match_sides)
    end

val match_rewrite =
    let
      fun filt1 _ {tname, ...} =
          length tname = 1 andalso is_eq_term (the_single tname)
      fun res is_active =
          {name = "match_rewrite" ^ (if is_active then "@active" else ""),
           filt = [{ty_str = TY_DISJ_of is_active, pre_filt = filt1},
                   {ty_str = TY_TERM, pre_filt = no_prereq_fn}],
           res_types = [Update.ADD_ITEMS],
           func = match_rewrite_fn}
    in
      map res [true, false]
    end

(* For active case, create box checking the next case. *)
fun disj_create_case items rtype _ =
    if not (RewriteTable.is_single_rtype rtype) then [] else
    if has_vars (prop_of' (get_thm (the_single items))) then [] else
    let
      val (item as {id, tname, ...}) = the_single items
      val _ = assert (get_ty_str item = TY_DISJ_ACTIVE)
                     "disj_concl_active: wrong type."
    in
      if length tname = 1 then []
      else [Update.AddBoxes {id = id, vars = [],
                             assums = [HOLogic.mk_Trueprop (hd tname)],
                             concls = [], cb = Update.null_callback}]
    end
val disj_create_case_filt = [{ty_str = TY_DISJ_ACTIVE, pre_filt = no_prereq_fn}]

(* sval1 dominates sval2 if the disjunctive terms in sval1 is a subset
   of that for sval2.
 *)
fun disj_shadow items rtype _ =
    if not (RewriteTable.is_single_rtype rtype) then [] else
    let
      val id = merged_id rtype items
    in
      if subset (op aconv) (apply2 get_tname (the_pair items))
      then [Update.ShadowItem {id = id, item = nth items 1}] else []
    end
val disj_shadow_filt = replicate 2 {ty_str = TY_DISJ, pre_filt = no_prereq_fn}
val disj_shadow_active_filt =
    replicate 2 {ty_str = TY_DISJ_ACTIVE, pre_filt = no_prereq_fn}
val disj_shadow_mixed_filt = [
  {ty_str = TY_DISJ_ACTIVE, pre_filt = no_prereq_fn},
  {ty_str = TY_DISJ, pre_filt = no_prereq_fn}]

val add_disj_proofsteps =
    fold add_prfstep (
      (* Update proofsteps. *)
      disj_update_gen (eq_update, "disj_update", K true, ItemIO_Data.univ_filt)
      @ match_update ("disj_match_update", K true, "") @ match_rewrite @

      (* Introducing proofsteps. *)
      map disj_intro_gen [
        ("conj_goal_intro",
         [WithGoal @{term_pat "?A & ?B"},
          Filter (canonical_split_filter @{const_name conj} "A" "B")]),
        ("disj_state_intro",
         [WithFact @{term_pat "?A | ?B"},
          Filter (canonical_split_filter @{const_name disj} "A" "B")]),
        ("imp_disj_state_intro", [WithFact @{term_pat "?A --> ?B"}]),
        ("forall_fact_intro", [WithFact @{term_pat "!x. ?P x"}]),
        ("exists_goal_intro", [WithFact @{term_pat "~ (EX x. ?P x)"}])] @

      (* Case creation and shadowing. *)
      [{name = "disj_create_case", filt = disj_create_case_filt,
        res_types = [Update.ADD_BOXES], func = disj_create_case},
       {name = "disj_shadow", filt = disj_shadow_filt,
        res_types = [Update.SHADOW_ITEM], func = disj_shadow},
       {name = "disj_shadow_active", filt = disj_shadow_active_filt,
        res_types = [Update.SHADOW_ITEM], func = disj_shadow},
       {name = "disj_shadow_mixed", filt = disj_shadow_mixed_filt,
        res_types = [Update.SHADOW_ITEM], func = disj_shadow}

    ]) #> fold add_fixed_sc (
      map (rpair 1) [
        "conj_goal_intro", "disj_state_intro", "imp_disj_state_intro",
        "forall_fact_intro", "exists_goal_intro",
        "disj_update", "disj_update@active"
    ])

end  (* structure Logic_ProofSteps. *)

val _ = Theory.setup Logic_ProofSteps.add_logic_proofsteps
val _ = Theory.setup Logic_ProofSteps.add_disj_proofsteps
