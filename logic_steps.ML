(* Core (logic) proofsteps. *)

signature LOGIC_PROOFSTEPS =
sig
  (* General logic *)
  val shadow_prop_item: proofstep
  val shadow_term_item: proofstep
  val eq_elim_prfstep: proofstep

  val exists_elim: box_id * thm -> Proof.context -> raw_update list
  val exists_elim_prfstep: proofstep
  val CHOOSE: string -> pre_scripts
  val CHOOSES: string list -> pre_scripts
  val add_logic_proofsteps: theory -> theory

  (* AC for conj and disj *)
  val conj_ac: ac_inst_info
  val disj_ac: ac_inst_info

  (* Some normalization conversions *)
  val imp_to_disj_cv: conv
  val not_conj_to_disj_cv: conv
  val to_disj_cv: conv
  val not_imp_to_conj_cv: conv
  val not_disj_to_conj_cv: conv
  val to_conj_cv: conv
  val not_ex_cv: Proof.context -> conv

  (* DISJ items. *)
  val TY_DISJ: string
  val disj_to_ritems: term -> int * thm -> raw_item list
  val disj_to_update: term -> box_id * int * thm -> raw_update
  val dest_tname_of_disj: term list -> term * term list
  val normalize_disj_cv: Proof.context -> conv
  val forall_elim_sch: thm -> thm
  val analyze_disj_th: Proof.context -> thm -> term * int * thm
  val output_disj_fn: item_output
  val disj_typed_matcher: item_matcher
  val disj_prop_matcher: item_matcher

  val add_priority_term: string -> theory -> theory
  val ac_disj_conv: int -> conv -> conv
  val to_disj_terms: term -> term list
  val reduce_disj_True: conv
  val match_update_prfstep: proofstep
  val match_one_sch_prfstep: proofstep
  val disj_match_iff_prfstep: proofstep
  val disj_create_case_prfstep: proofstep
  val disj_shadow_prfstep: proofstep
  val add_disj_proofsteps: theory -> theory

  (* Normalizers *)
  val split_conj_gen_th: thm -> thm list
  val eq_normalizer: normalizer
  val property_normalizer: normalizer
  val disj_normalizer: normalizer
  val add_disj_normalizers: theory -> theory

  (* TERM_DEF *)
  val TY_TERM_DEF: string
  val CHOOSE_FUN_N: int -> string -> pre_scripts
  val match_term_def_prfstep: proofstep
  val add_term_def_proofsteps: theory -> theory
end;

functor Logic_ProofSteps(Base:UTIL_BASE) : LOGIC_PROOFSTEPS =
struct

structure UtilLogic = UtilLogic(Base)
structure ACUtil = ACUtil(Base)
structure Property_Data = Property_Data(Base)
structure RewriteTable = RewriteTable(Base)
structure Matcher = Matcher(Base)
structure BoxItem = BoxItem(Base)
structure ItemIO_Data = ItemIO_Data(Base)
structure Update = Update(Base)
structure Normalizer = Normalizer(Base)
structure ProofStep = ProofStep(Base)
structure ProofStep_Data = ProofStep_Data(Base)
structure Script = Script(Base)
open Base
open UtilLogic
open ACUtil
open ProofStep
open ProofStep_Data
open Script

fun boolVar s = Var ((s, 0), boolT)

(* Shadowing based on equivalence. For both PROP and TERM items,
   shadowing is based on subterm equivalence, skipping any Not (~) at
   head.
 *)
fun shadow_item_fn rtype _ item1 item2 =
    let
      val (tbl as {lat, ...}) = RewriteTable.table_of_rtype rtype
      val id = BoxItem.merged_id lat [item1, item2]
      val (tname1, tname2) = (the_single (BoxItem.get_tname item1),
                              the_single (BoxItem.get_tname item2))
                             handle List.Empty => raise AUTO2 "shadow_item_fn"
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
          ShadowItem {id = id', item = item_to_shadow}
    in
      map process_id equiv_ids
    end

val shadow_prop_item =
    {name = "shadow_prop",
     args = [TypedMatch (TY_PROP, boolVar "A"),
             TypedMatch (TY_PROP, boolVar "B")],
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
      val (A, B) = dest_eq (prop_of' prop)
      fun inst_t t = get_insts (PropMatch t) item2 rtype (id, fo_init)
      val (inst_A, inst_B) = (inst_t A, inst_t B)
      val (inst_nA, inst_nB) = (inst_t (get_neg A), inst_t (get_neg B))

      (* All the process_inst functions follow the same pattern, up to
         transform function f for prop.
       *)
      fun elim_shadow f ((id', _), th) =
          [Update.thm_update (
              id', Thm.equal_elim (make_trueprop_eq (f prop)) th),
           ShadowItem {id = id', item = item1}]

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
     args = [TypedMatch (TY_EQ, mk_eq (boolVar "A", boolVar "B")),
             PropMatch (boolVar "C")],
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
      Update.apply_exists (id, th) ctxt nms
    end

fun exists_elim_fn rtype {ctxt, ...} {id, prop, ...} =
    if not (RewriteTable.is_single_rtype rtype) then []
    else let
      val t = prop_of' prop
    in
      if is_ex t then
        exists_elim (id, prop) ctxt
      else if is_neg t andalso is_all (dest_not t) then
        let
          val th = prop |> apply_to_thm' (rewr_obj_eq not_all_th)
        in
          exists_elim (id, th) ctxt
        end
      else if is_bex t then
        let
          val th = prop |> apply_to_thm' (rewr_obj_eq Bex_def_th)
        in
          exists_elim (id, th) ctxt
        end
      else if is_neg t andalso is_ball (dest_not t) then
        let
          val cv = (Conv.arg_conv (rewr_obj_eq Ball_def_th))
                       then_conv (rewr_obj_eq not_all_th)
          val th = prop |> apply_to_thm' cv
        in
          exists_elim (id, th) ctxt
        end
      else []
    end

val exists_elim_prfstep =
    {name = "exists_elim",
     args = [TypedMatch (TY_PROP, boolVar "A")],
     priority = PRIORITY_ADD,
     func = OneStep exists_elim_fn}

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
            mk_exists (nm, T, concl')
          else
            case cond of
                Const (c, _) $ _ $ S =>
                if c = Mem_name then
                  let
                    val bexT = (mk_setT T) --> (T --> boolT) --> boolT
                  in
                    Const (Bex_name, bexT) $ S $ Term.absfree (nm, T) concl'
                  end
                else mk_exists (nm, T, mk_conj (cond, concl'))
              | _ => mk_exists (nm, T, mk_conj (cond, concl'))
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
            let
              val _ = trace_t_ctxt ctxt "At" t
              val _ = if length new_vars = 0 then tracing "No new variables"
                      else trace_tlist_ctxt
                               ctxt "New variables:" (map Free new_vars)
            in
              raise AUTO2 "extract_new_vars: number of new variables is not 1."
            end
        end

fun read_choose_str str ctxt =
    let
      val ts = str |> split_commas |> Syntax.read_terms ctxt
      val (conds, concl) = split_last ts
      val new_vars = extract_new_vars ctxt conds

      (* Exist proposition to prove. *)
      val ex_prop = mk_Trueprop (form_exists_prop (new_vars ~~ conds) concl)

      (* Check the variable names are new in ctxt. *)
      val _ = assert (not (exists (Variable.is_fixed ctxt) (map fst new_vars)))
                     "CHOOSE: variable name(s) already used."
      val _ = check_new_vars ctxt (map fst new_vars) ex_prop
    in
      (new_vars, ex_prop)
    end

fun CHOOSE str ctxt =
    let
      val (new_vars, ex_prop) = read_choose_str str ctxt
      fun choose_callback ((id, th), {ctxt, ...}) =
          Update.apply_exists (id, th) ctxt (map fst new_vars)
    in
      [Script_Task {inits = [InitAssum (get_neg' ex_prop)], subs = [],
                    cb = choose_callback, end_vars = map Free new_vars}]
    end

fun CHOOSES strs =
    case strs of
        [str] => CHOOSE str
      | str :: rest => (CHOOSE str) THEN (CHOOSES rest)
      | _ => raise AUTO2 "CHOOSES: empty argument"

val add_logic_proofsteps =
    fold add_prfstep [
      shadow_prop_item, shadow_term_item, eq_elim_prfstep, exists_elim_prfstep

    ] #> fold add_fixed_sc [
      ("eq_elim", 1)
    ]

val conj_ac =
    the (ACUtil.constr_ac_info_acu
             {assoc_th = conj_assoc_th, comm_th = conj_commute_th,
              unitl_th = conj_unitL_th} @{theory} (Free ("P", boolT)))

val disj_ac =
    the (ACUtil.constr_ac_info_acu
             {assoc_th = disj_assoc_th, comm_th = disj_commute_th,
              unitl_th = disj_unitL_th} @{theory} (Free ("P", boolT)))

(* Convert term of form A_1 --> ... --> A_n to ~A_1 | ... | ~A_(n-1) |
   A_n, canceling any double negations.
 *)
fun imp_to_disj_cv ct =
    if is_imp (Thm.term_of ct) then
      Conv.every_conv [rewr_obj_eq imp_conv_disj_th,
                       Conv.arg1_conv try_nn_cancel_cv,
                       Conv.arg_conv imp_to_disj_cv] ct
    else
      try_nn_cancel_cv ct

(* Convert term of form ~(A_1 & ... & A_n) to ~A_1 | ... | ~A_n,
   canceling any double negations.
 *)
fun not_conj_to_disj_cv ct =
    if is_neg (Thm.term_of ct) andalso is_conj (dest_not (Thm.term_of ct)) then
      Conv.every_conv [rewr_obj_eq de_Morgan_conj_th,
                       Conv.arg1_conv try_nn_cancel_cv,
                       Conv.arg_conv not_conj_to_disj_cv] ct
    else
      try_nn_cancel_cv ct

(* Convert disjunctions in disj, not_conj, or imp form to
   disjunctions.
 *)
fun to_disj_cv ct =
    let
      val t = Thm.term_of ct
    in
      if is_imp t then imp_to_disj_cv ct
      else if is_neg t andalso is_conj (dest_not t) then
        ((Conv.arg_conv (ACUtil.normalize_assoc_r conj_ac))
             then_conv not_conj_to_disj_cv) ct
      else if is_disj t then
        ACUtil.normalize_assoc_r disj_ac ct
      else if is_neg t andalso is_neg (dest_not t) then
        try_nn_cancel_cv ct
      else
        Conv.all_conv ct
    end

(* Convert term of form ~(A_1 --> ... --> A_n) to A_1 & ... & A_(n-1)
   & A_n, canceling any double negations.
 *)
fun not_imp_to_conj_cv ct =
    if is_neg (Thm.term_of ct) andalso is_imp (dest_not (Thm.term_of ct)) then
      Conv.every_conv [rewr_obj_eq not_imp_th,
                       Conv.arg_conv not_imp_to_conj_cv] ct
    else
      try_nn_cancel_cv ct

(* Convert term of form ~(A_1 | ... | A_n) to ~A_1 & ... & ~A_n,
   canceling any double negations.
 *)
fun not_disj_to_conj_cv ct =
    if is_neg (Thm.term_of ct) andalso is_disj (dest_not (Thm.term_of ct)) then
      Conv.every_conv [rewr_obj_eq de_Morgan_disj_th,
                       Conv.arg1_conv try_nn_cancel_cv,
                       Conv.arg_conv not_disj_to_conj_cv] ct
    else
      try_nn_cancel_cv ct

(* Convert conjunctions in not_disj, conj, or not_imp form to
   conjunctions.
 *)
fun to_conj_cv ct =
    let
      val t = Thm.term_of ct
    in
      if is_neg t andalso is_imp (dest_not t) then
        not_imp_to_conj_cv ct
      else if is_neg t andalso is_disj (dest_not t) then
        ((Conv.arg_conv (ACUtil.normalize_assoc_r disj_ac))
             then_conv not_disj_to_conj_cv) ct
      else if is_conj t then
        ACUtil.normalize_assoc_r conj_ac ct
      else if is_neg t andalso is_neg (dest_not t) then
        try_nn_cancel_cv ct
      else
        Conv.all_conv ct
    end

(* Convert term of form ~ (EX x y. P x y) to !x y. ~ P x y (arbitrary
   number of existence quantifiers).
 *)
fun not_ex_cv ctxt ct =
    let
      val t = Thm.term_of ct
    in
      if is_neg t andalso is_ex (dest_not t) then
        ((rewr_obj_eq not_ex_th)
             then_conv (Conv.binder_conv (not_ex_cv o snd) ctxt)) ct
      else
        Conv.all_conv ct
    end

(* Disjunctive mutable states. *)
val TY_DISJ = "DISJ"

(* Given a theorem in the form of a disjunction, possibly containing
   schematic variables, return the corresponding DISJ item. Here sz
   specifies number of terms in the disjunction.
 *)
fun disj_to_ritems disj_head (sz, th) =
    if sz = 1 then
      if has_vars (Thm.prop_of th) then
        let
          fun th_to_ritem th =
              Fact (TY_DISJ, [disj_head, prop_of' th], th)
        in
          map th_to_ritem (th |> apply_to_thm' to_conj_cv
                              |> split_conj_th)
        end
      else
        [Fact (TY_PROP, [prop_of' th], th)]
    else let
      val subs = ACUtil.dest_ac_r disj_ac (prop_of' th)
      val _ = assert (length subs >= sz)
                     "disj_to_update: not enough terms in th."
      val (prev, last) = chop (sz - 1) subs
      val subs' = prev @ [ACUtil.list_ac_r disj_ac last]
      val tname = disj_head :: subs'
    in
      [Fact (TY_DISJ, tname, th)]
    end

fun disj_to_update disj_head (id, sz, th) =
    if Thm.prop_of th aconv pFalse then
      ResolveBox {id = id, th = th}
    else
      AddItems {id = id, raw_items = disj_to_ritems disj_head (sz, th)}

(* Deconstruct the tname of a DISJ item. *)
fun dest_tname_of_disj tname =
    case tname of
        disj_head :: rest => (disj_head, rest)
      | _ => raise AUTO2 "dest_tname_of_disj: too few terms in tname."

(* Convert to a (object) forall fact. ct must begin with ~EX or ALL to
   be transformed.
 *)
fun to_forall_cv ctxt ct =
    let
      val t = Thm.term_of ct
    in
      if is_neg t andalso (is_ex (dest_not t) orelse is_bex (dest_not t)) then
        ((Conv.arg_conv (normalize_exs_conv ~1 ctxt))
             then_conv (not_ex_cv ctxt)) ct
      else if is_all t orelse is_ball t then
        normalize_alls_conv ~1 ctxt ct
      else
        Conv.all_conv ct
    end

(* Apply cv on the body of !x y z. ... .*)
fun forall_body_conv cv ctxt ct =
    if is_all (Thm.term_of ct) then
      Conv.binder_conv (fn (_, ctxt) => forall_body_conv cv ctxt) ctxt ct
    else
      cv ct

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
          let
            val var_nms = map fst (Term.add_var_names (Thm.prop_of th) [])
            val nm' = if member (op =) var_nms nm then
                        singleton (Name.variant_list var_nms) nm
                      else nm
          in
            th |> Thm.forall_elim (cert_thy thy (Var ((nm', 0), T)))
               |> forall_elim_sch
          end
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

      (* Head operator, and expected number of terms in the DISJ item. *)
      val (head, len) =
          if is_disj prop then
            (disj, length (ACUtil.dest_ac_total disj_ac prop))
          else if is_neg prop andalso is_conj (dest_not prop) then
            (conj, length (ACUtil.dest_ac_total conj_ac (get_neg prop)))
          else
            (imp, length (fst (strip_obj_imp prop)) + 1)
    in
      (head, len, apply_to_thm' to_disj_cv th')
    end

fun is_active_head disj_head = (not (disj_head aconv imp))

fun output_disj_fn ctxt (tname, _) =
    let
      val (disj_head, subs) = dest_tname_of_disj tname
    in
      if disj_head aconv disj then
        (foldr1 mk_disj subs) |> pretty_term ctxt |> str
      else if disj_head aconv conj then
        (foldr1 mk_conj (map get_neg subs))
            |> get_neg |> pretty_term ctxt |> str
      else if disj_head aconv imp then
        (foldr1 mk_imp (subs |> split_last |> apfst (map get_neg)
                             |> apsnd single |> (op @)))
            |> pretty_term ctxt |> str
      else
        raise AUTO2 "output_disj_fn: unexpected disj_head."
    end

(* Pre-matching function for DISJ items. There are only three possible
   patterns to consider: ?C | ?D, ?C = ?D, and ?C. No rewriting is
   needed for pre-matching. Matching is not implemented.
 *)
val disj_typed_matcher =
    let
      val pat_or = mk_disj (boolVar "C", boolVar "D")
      val pat_eq = mk_eq (boolVar "C", boolVar "D")
      val pat_single = boolVar "C"

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
            val has_vars = exists has_vars tname
          in
            if is_neg pat andalso is_ex (dest_not pat) then has_vars
            else if is_neg pat andalso is_bex (dest_not pat) then has_vars
            else if is_all pat orelse is_ball pat then has_vars
            else if is_disj pat then not has_vars
            else if is_imp pat then not has_vars
            else if is_neg pat andalso is_conj (dest_not pat) then not has_vars
            else false
          end

      (* Given t in forall-disj form, return the list of types in the
         forall abstractions, followed by the number of terms in the
         disjunction.
       *)
      fun strip_forall_disj t =
          case t of
              Const (c, _) $ Abs (_, T, body) =>
              if c <> All_name then ([], 1) else
              let
                val (allc, disjc) = strip_forall_disj body
              in
                (T :: allc, disjc)
              end
            | Const (c, _) $ _ $ B =>
              if c <> Disj_name then ([], 1) else
              let
                val (allc, disjc) = strip_forall_disj B
              in
                (allc, disjc + 1)
              end
            | _ => ([], 1)

      (* Returns the body under forall. *)
      fun strip_forall t =
          case t of
              Const (c, _) $ Abs (_, _, body) =>
              if c = All_name then strip_forall body else t
            | _ => t

      (* Given th: t(var) == u(var), form !nm. t(nm) == u(nm). *)
      fun abstract_forall_rule ctxt ((nm, T), var) th =
          let
            val all_const = Const (All_name, (T --> boolT) --> boolT)
          in
            th |> Thm.abstract_rule nm (cert ctxt var)
               |> Thm.combination (Thm.reflexive (cert ctxt all_const))
          end

      fun match pat item (tbl as {ctxt, ...}) (id, (tyinst, inst)) =
          let
            val {tname, prop = th, ...} = item
            val (_, subs) = dest_tname_of_disj tname
            val thy = Proof_Context.theory_of ctxt
            val vars = fold Term.add_vars tname []
          in
            let
              val pat_eq = normalize_disj_cv ctxt (cert ctxt pat)
              val pat' = rhs_of pat_eq
              val (allc, disjc) = strip_forall_disj pat'
              val var_tys = map snd vars
            in
              if length allc <> length vars then []
              else if disjc > length subs then []
              else if not (Type.could_matches (rev allc, var_tys))
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
                val insts' = Matcher.rewrite_match_ac_bd true
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

structure PriorityTermData =
Theory_Data (
  type T = string list
  val empty = []
  val extend = I;
  val merge = Library.merge (op =)
)

fun is_priority_term thy t =
    case Term.head_of t of
        Const (nm, _) => member (op =) (PriorityTermData.get thy) nm
      | _ => false

fun add_priority_term str thy =
    let
      val _ = writeln ("Add priority_term " ^ str)
    in
      PriorityTermData.map (cons str) thy
    end

(* Given ct in the form p_1 | ... | p_n, apply cv to each of p_i. *)
fun ac_disj_conv n cv ct =
    if n = 1 then cv ct
    else if is_disj (Thm.term_of ct) then
      ((Conv.arg1_conv cv)
           then_conv (Conv.arg_conv (ac_disj_conv (n-1) cv))) ct
    else if n < 0 then cv ct  (* indicate apply cv until the end *)
    else raise AUTO2 "ac_disj_conv"

fun to_disj_terms t =
    if is_imp t then
      get_neg (dest_arg1 t) :: to_disj_terms (dest_arg t)
    else if is_neg t andalso is_conj (dest_not t) then
      to_disj_terms (get_neg (dest_arg1 (dest_not t))) @
      to_disj_terms (get_neg (dest_arg (dest_not t)))
    else if is_disj t then
      to_disj_terms (dest_arg1 t) @ to_disj_terms (dest_arg t)
    else if is_neg t andalso is_neg (dest_not t) then
      to_disj_terms (dest_not (dest_not t))
    else [t]

(* Assume ct is a disjunction, associating to the right. *)
fun reduce_disj_True ct =
    if is_disj (Thm.term_of ct) then
      ((rewr_obj_eq disj_True1_th)
           else_conv ((Conv.arg_conv reduce_disj_True)
                          then_conv (rewr_obj_eq disj_True2_th))) ct
    else
      Conv.all_conv ct

(* Handles also the case where pat is in not-conj or imp form. *)
fun match_prop rtype (id, item2) pat =
    let
      val disj_pats = to_disj_terms pat

      (* th is pat'(inst), where pat' is one of the disjunctive terms
         of pat.
       *)
      fun process_inst ((id, inst), th) =
          let
            val {ctxt, ...} = RewriteTable.table_of_rtype rtype
            (* Construct the theorem pat'(inst) == True. *)
            val to_eqT_cv =
                th |> apply_to_thm' (rewr_obj_eq (obj_sym eq_True_th))
                   |> rewr_obj_eq |> Conv.try_conv
            (* Rewrite pat(inst) using the above, then rewrite to True. *)
            val pat_eqT =
                pat |> cert ctxt |> to_disj_cv
                    |> subst_thm ctxt inst
                    |> apply_to_rhs (ac_disj_conv ~1 to_eqT_cv)
                    |> apply_to_rhs reduce_disj_True
                    |> to_obj_eq
            val patT = apply_to_thm' (rewr_obj_eq eq_True_th) pat_eqT
          in
            ((id, inst), patT)
          end
    in
      get_insts (PropMatch pat) item2 rtype (id, fo_init) @
      (if length disj_pats > 1 then
         map process_inst (maps (match_prop rtype (id, item2)) disj_pats)
       else [])
    end

(* Reduce a disjunction p_1 | ... | t | ... | p_n by matching ~t with
   the second item. If the disjunction contains schematic variables, t
   must have either zero or the largest number of schematic variables.
 *)
fun match_update_fn rtype {ctxt, ...} item1 item2 =
    let
      val {id, prop, tname = tname1, ...} = item1
      val thy = Proof_Context.theory_of ctxt
      val (disj_head, subs) = dest_tname_of_disj tname1
      fun count_var t = length (Term.add_vars t [])
      val max_nvar = fold (curry Int.max) (map count_var subs) 0
      val has_priority_term = exists (is_priority_term thy) (map get_neg subs)

      val (NO_MATCH, FREE_ONLY, YES_MATCH) = (0, 1, 2)

      (* Test whether to perform matching on pattern. *)
      fun test_do_match (i, sub, nvar) =
          let
            val nsub = get_neg sub
          in
            if not (is_pattern sub) then NO_MATCH
            else if length subs > 1 andalso
                    Property_Data.is_property_prem thy nsub then NO_MATCH
            else if has_priority_term andalso
                    not (is_priority_term thy nsub) then NO_MATCH
            else if nvar = 0 orelse nvar = max_nvar then YES_MATCH
            else if i > 0 then NO_MATCH else FREE_ONLY
          end

      (* Match the negation of subs[i] with th2. For each match,
         instantiate in prop all schematic variables in t, so that t
         becomes ~th2. Then remove t from prop in the instantiated
         version.
       *)
      fun get_matches i =
          let
            val t = nth subs i
            val nvar = count_var t
            val do_match = test_do_match (i, t, nvar)
            fun process_inst ((id', inst), th) =
                if do_match = FREE_ONLY andalso
                   not (forall (fn (_, (_, t)) => Term.is_Free t)
                               (Vartab.dest (snd inst))) then []
                else let
                  val cv = th |> to_eqF_th |> rewr_obj_eq
                              |> Conv.try_conv |> ac_disj_conv (length subs)
                  val prop' = prop |> subst_thm_thy thy inst
                                   |> apply_to_thm' cv
                  val unit_count =
                      prop' |> prop_of' |> dest_ac_r disj_ac
                            |> filter (fn t => t aconv bFalse) |> length
                  val _ = assert (unit_count > 0)
                                 "disj_match_update: cannot find term."
                  val prop'' =
                      prop' |> apply_to_thm' (ACUtil.normalize_unit disj_ac)
                  val shadow_updt = if nvar > 0 then [] else
                                    [ShadowItem {id = id', item = item1}]
                  val new_len = length subs - unit_count
                in
                  [disj_to_update disj_head (id', new_len, prop'')] @
                  shadow_updt
                end
          in
            if do_match = NO_MATCH then []
            else t |> get_neg |> match_prop rtype (id, item2)
                   |> maps process_inst
          end
    in
      maps get_matches (0 upto (length subs - 1))
    end

val match_update_prfstep =
    {name = "disj_match_update",
     args = [TypedMatch (TY_DISJ, boolVar "C"),
             PropMatch (boolVar "A")],
     priority = PRIORITY_SHADOW,
     func = TwoStep match_update_fn}

(* For DISJ items with a single term, of form f p1 ... pn, match t
   against each of p_i.
 *)
fun match_one_sch_fn rtype {tbl, ...} item1 item2 =
    let
      val {id, tname, prop = th1, ...} = item1
      val thy = RewriteTable.theory_of tbl
      val (_, subs) = dest_tname_of_disj tname
    in
      if length subs > 1 then [] else
      if is_eq_term (the_single subs) andalso
         fastype_of (dest_arg (the_single subs)) = boolT then [] else
      let
        val t = the_single subs
        val args = dest_args t
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
                       RewriteTable.is_equiv id' tbl (dest_eq prop')
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
    {name = "disj_match_one_sch",
     args = [TypedMatch (TY_DISJ, boolVar "C"),
             TypedMatch (TY_TERM, @{term_pat "?A"})],
     priority = PRIORITY_ADD,
     func = TwoStep match_one_sch_fn}

fun disj_match_iff_fn rtype {ctxt, ...} {id, prop, ...} =
    if not (RewriteTable.is_single_rtype rtype) then [] else
    let
      val cv = (to_obj_conv ctxt) then_conv (Trueprop_conv imp_to_disj_cv)
      val forward = prop |> equiv_forward_th |> apply_to_thm cv
      val backward = prop |> equiv_backward_th |> apply_to_thm cv
    in
      [disj_to_update imp (id, 2, forward),
       disj_to_update imp (id, 2, backward)]
    end

val disj_match_iff_prfstep =
    {name = "disj_match_iff",
     args = [TypedMatch (TY_DISJ, mk_eq (boolVar "A", boolVar "B"))],
     priority = PRIORITY_ADD,
     func = OneStep disj_match_iff_fn}

(* For active case, create box checking the next case. *)
fun disj_create_case_fn rtype {ctxt, ...} {id, tname, ...} =
    if not (RewriteTable.is_single_rtype rtype) then [] else
    if exists has_vars tname then [] else
    let
      val (disj_head, subs) = dest_tname_of_disj tname
    in
      if not (is_active_head disj_head) then []
      else if length subs = 1 then []
      else let
        val stmt = subs |> hd |> get_neg |> cert ctxt
                        |> normalize_alls_conv ~1 ctxt |> rhs_of
        val (vars, body) = strip_obj_all_var stmt
        val (assums, concl) = strip_obj_imp body
        val inits = map InitVar vars @
                    map (InitAssum o mk_Trueprop) assums @
                    [InitAssum (mk_Trueprop (get_neg concl))]
      in
        [AddBoxes {id = id, inits = inits, cbs = []}]
      end
    end

val disj_create_case_prfstep =
    {name = "disj_create_case",
     args = [TypedMatch (TY_DISJ, mk_disj (boolVar "C", boolVar "D"))],
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
      val id = BoxItem.merged_id lat [item1, item2]
      val (disj_head1, subs1) = dest_tname_of_disj tname1
      val (disj_head2, subs2) = dest_tname_of_disj tname2
    in
      if not (is_active_head disj_head1) andalso
         is_active_head disj_head2 then []
      else if subset (op aconv) (subs1, subs2) then
        [ShadowItem {id = id, item = item2}]
      else []
    end

val disj_shadow_prfstep =
    {name = "disj_shadow",
     args = [TypedMatch (TY_DISJ, mk_disj (boolVar "C", boolVar "D")),
             TypedMatch (TY_DISJ, mk_disj (boolVar "C", boolVar "D"))],
     priority = PRIORITY_SHADOW,
     func = TwoStep disj_shadow_fn}

val add_disj_proofsteps =
    fold ItemIO_Data.add_item_type [
      (TY_DISJ, SOME (drop 1), SOME output_disj_fn)

    ] #> fold ItemIO_Data.add_typed_matcher [
      (TY_DISJ, disj_typed_matcher)

    ] #> fold ItemIO_Data.add_prop_matcher [
      (TY_DISJ, disj_prop_matcher)

    ] #> fold add_prfstep (
      [match_update_prfstep, match_one_sch_prfstep, disj_match_iff_prfstep,
       disj_create_case_prfstep, disj_shadow_prfstep]

    ) #> fold add_fixed_sc (
      map (rpair 1) [
        "disj_match_update"
    ])

(* Generalized form of splitting A & B. Also deal with cases ~(A | B)
   and ~(A --> B).
 *)
fun split_conj_gen_th th =
    th |> apply_to_thm' to_conj_cv
       |> split_conj_th

fun eq_normalizer _ ritem =
    case ritem of
        Handler _ => [ritem]
      | Fact (ty_str, _, th) =>
        if ty_str <> "PROP" then [ritem]
        else if is_eq_term (prop_of' th) then
          let
            val (lhs, rhs) = dest_eq (prop_of' th)
          in
            if is_if rhs then [Fact (TY_EQ_IF, [lhs, rhs], th)]
            else [Fact (TY_EQ, [lhs, rhs], th)]
          end
        else [ritem]

fun property_normalizer ctxt ritem =
    case ritem of
        Handler _ => [ritem]
      | Fact (ty_str, _, th) =>
        if ty_str <> "PROP" then [ritem]
        else let
          val thy = Proof_Context.theory_of ctxt
          val prop' = prop_of' th
        in
          if Property_Data.is_property_const thy prop' then
            [Fact (TY_PROPERTY, [prop'], th)]
          else [ritem]
        end

fun disj_normalizer ctxt ritem =
    case ritem of
        Handler _ => [ritem]
      | Fact (ty_str, _, th) =>
        if ty_str <> "PROP" then [ritem]
        else let
          val t = prop_of' th
        in
          if is_neg t andalso is_conj (dest_not t) orelse
             is_disj t orelse is_imp t orelse
             is_all t orelse is_ball t orelse
             is_neg t andalso is_ex (dest_not t) orelse
             is_neg t andalso is_bex (dest_not t)
          then
            let
              val (disj_head, sz, disj_th) = analyze_disj_th ctxt th
            in
              disj_to_ritems disj_head (sz, disj_th)
            end
          else [ritem]
        end

val add_disj_normalizers =
    Normalizer.add_th_normalizer (
      "split_conj_gen", (K split_conj_gen_th)

    ) #> fold Normalizer.add_normalizer [
      ("eq", eq_normalizer),
      ("property", property_normalizer),
      ("disj", disj_normalizer)
    ]

(* TERM_DEF *)
val TY_TERM_DEF = "TERM_DEF"
fun term_def_updt (id, (pat, th)) =
    let
      val ritem = Fact (TY_TERM_DEF, [pat, Thm.prop_of th], th)
    in
      [AddItems {id = id, raw_items = [ritem]}]
    end

fun match_term_def_fn rtype {ctxt, ...} item1 item2 =
    let
      val {id, tname, prop, ...} = item1
      val (pat, _) = the_pair tname
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

      (* Also zero indices *)
      fun split_conj_th' th =
          if is_conj (prop_of' th) then
            Drule.zero_var_indexes (th RS conjunct1_th) ::
            split_conj_th (Drule.zero_var_indexes (th RS conjunct2_th))
          else [th]

      (* Given a theorem about function f, for example

         !x. P (f x) & !y. Q (f x y),

         extract the properties of successive applications of f,
         returning them as term_def items. In the example above, the
         result would be [(f ?x, P (f ?x)), (f ?x ?y1), Q (f ?x ?y1)].
       *)
      fun prop_f_to_updt ctxt count id (f, prop_f_th) =
          case prop_of' prop_f_th of
              Const (c, _) $ Abs (nm, T, _) =>
              if c = All_name then
                let
                  val sch_var = Var ((nm, count), T)
                  val (ths, next) =
                      prop_f_th |> apply_to_thm (Conv.rewr_conv (
                                                    meta_sym atomize_all_th))
                                |> Thm.forall_elim (cert ctxt sch_var)
                                |> split_conj_th' |> split_last
                  val pat = f $ sch_var
                  fun to_updt th = term_def_updt (id, (pat, th))
                in
                  if count = n - 1 then
                    maps to_updt (ths @ [next])
                  else
                    maps to_updt ths @
                    prop_f_to_updt ctxt (count + 1) id (pat, next)
                end
              else raise AUTO2 "CHOOSE_FUN_N: wrong form of prop_f_th."
            | _ => raise AUTO2 "CHOOSE_FUN_N: wrong form of prop_f_th."

      fun choose_callback ((id, th), {ctxt, ...}) =
          let
            val (ritems, th) =
                Update.apply_exists_ritems th ctxt (map fst new_vars)

            (* When choosing function F, this is the theorem !x. P (F i). *)
            val prop_f_th = th |> split_conj_th' |> List.last
            val f = Free (the_single new_vars)
          in
            AddItems {id = id, raw_items = ritems @ [Update.thm_to_ritem th]} ::
            prop_f_to_updt ctxt 0 id (f, prop_f_th)
          end
    in
      [Script_Task {inits = [InitAssum (get_neg' ex_prop)], subs = [],
                    cb = choose_callback, end_vars = map Free new_vars}]
    end

val add_term_def_proofsteps =
    fold ItemIO_Data.add_item_type [
      (TY_TERM_DEF, NONE, NONE)

    ] #> fold ItemIO_Data.add_typed_matcher [
      (TY_TERM_DEF, ItemIO_Data.univ_matcher)

    ] #> add_prfstep match_term_def_prfstep

end  (* structure Logic_ProofSteps. *)
