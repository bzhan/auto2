(* Core (logic) proofsteps. *)

signature LOGIC_PROOFSTEPS =
sig
  (* General logic *)
  val shadow_prop_item: proofstep
  val shadow_term_item: proofstep
  val eq_elim_prfstep: proofstep
  val cong_on_ineq_prfstep: proofstep

  val exists_elim_prfstep: proofstep
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
  val disj_to_ritems: bool -> term -> int * thm -> raw_item list
  val disj_to_update:
      bool -> term -> box_id * int option * int * thm -> raw_update
  val dest_tname_of_disj: cterm list -> term * cterm list
  val is_match_prem_only: box_item -> bool
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
  val split_conj_gen_th: Proof.context -> thm -> thm list
  val eq_normalizer: normalizer
  val property_normalizer: normalizer
  val disj_normalizer: normalizer
  val logic_thm_update: Proof.context -> box_id * thm -> raw_update
  val add_disj_normalizers: theory -> theory

  (* TERM_DEF *)
  val TY_TERM_DEF: string
  val term_def_updt: box_id * (term * thm) -> raw_update list
  val match_term_def_prfstep: proofstep
  val add_term_def_proofsteps: theory -> theory
end;

functor Logic_ProofSteps(Base:UTIL_BASE) : LOGIC_PROOFSTEPS =
struct

structure UtilLogic = UtilLogic(Base)
structure ACUtil = ACUtil(Base)
structure Property = Property(Base)
structure RewriteTable = RewriteTable(Base)
structure Matcher = Matcher(Base)
structure BoxItem = BoxItem(Base)
structure ItemIO = ItemIO(Base)
structure Update = Update(Base)
structure Normalizer = Normalizer(Base)
structure ProofStep = ProofStep(Base)
structure ProofStep_Data = ProofStep_Data(Base)
open Base
open UtilLogic
open ProofStep
open ProofStep_Data

fun boolVar s = Var ((s, 0), boolT)

(* Shadowing based on equivalence. For both PROP and TERM items,
   shadowing is based on subterm equivalence, skipping any Not (~) at
   head.
 *)
fun shadow_item_fn rtype _ item1 item2 =
    if #sc item1 = 0 andalso #sc item2 = 0 then []
    else let
      val (tbl as {lat, ...}) = RewriteTable.table_of_rtype rtype
      val id = BoxItem.merged_id lat [item1, item2]
      val _ = assert (forall (BoxItem.match_ty_strs [TY_TERM, TY_PROP])
                             [item1, item2])
                     "shadow_item_fn"
      val (tname1, tname2) =
          (the_single (#tname item1), the_single (#tname item2))
          handle List.Empty => raise AUTO2 "shadow_item_fn"
      val (t1, t2) = (Thm.term_of tname1, Thm.term_of tname2)

      val equiv_ids =
          if fastype_of t1 = boolT andalso is_neg t1 andalso
             fastype_of t2 = boolT andalso is_neg t2 then
            (RewriteTable.subequiv_info
                 tbl id (get_cneg tname1, get_cneg tname2))
                |> RewriteTable.replace_id_for_type' rtype |> map fst
                |> max_partial (BoxID.is_eq_ancestor lat)
          else
            (RewriteTable.subequiv_info tbl id (tname1, tname2))
                |> RewriteTable.replace_id_for_type' rtype |> map fst
                |> max_partial (BoxID.is_eq_ancestor lat)
      val item_to_shadow =
          if #sc item1 > #sc item2 orelse
             (#sc item1 = #sc item2 andalso #uid item1 > #uid item2) then item1
          else item2
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
          let
            val th = Thm.equal_elim (make_trueprop_eq (f prop)) th
          in
            [AddItems {id = id', sc = SOME 1,
                       raw_items = [Update.thm_to_ritem th]},
             ShadowItem {id = id', item = item1}]
          end

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

(* Given goal A = B, find rewrites of A and B to terms of the form
   f(a_1, ..., a_n) and g(b_1, ..., b_n), where all but one of the
   pairs a_i and b_i are equal. Reduce the equality goal to the goal
   a_i = b_i for that i.
 *)
fun cong_on_ineq_fn rtype _ {id, prop, ...} =
    let
      val (cA, cB) = cprop_of' prop |> get_cneg |> dest_binop_cargs
      val (A, B) = apply2 Thm.term_of (cA, cB)
      val (tbl as {ctxt, ...}) = RewriteTable.table_of_rtype rtype

      fun process_A_equiv (id', eq_A) =
          let
            val A' = rhs_of eq_A
            val (f, argsA') = Term.strip_comb A'
            fun process_i i =
                let
                  val ty_i = fastype_of (nth argsA' i)
                  val args_pat = (take i argsA') @ [Var (("x",0), ty_i)] @
                                 (drop (i + 1) argsA')
                  val pat = Term.list_comb (f, args_pat)
                  val insts =
                      (Matcher.rewrite_match tbl (pat, cB) (id', fo_init))
                          |> RewriteTable.replace_id_for_type rtype

                  fun process_inst ((id'', inst), eq_B) =
                      let
                        val tx = lookup_inst inst "x"
                        val cv = Conv.every_conv [
                              Conv.arg1_conv (Conv.rewr_conv (meta_sym eq_A)),
                              Conv.arg_conv (Conv.rewr_conv eq_B),
                              to_obj_eq_cv]
                        val cong_th =
                            (eq_cong_th i tx A' ctxt)
                                |> apply_to_thm (concl_conv cv)
                                |> apply_to_thm (Conv.arg1_conv to_obj_eq_cv)
                                |> backward_th
                      in
                        Update.thm_update (id'', prop RS cong_th)
                      end
                in
                  map process_inst insts
                end
          in
            (* Test only when f is a free variable (not a constant). *)
            if Term.is_Free f then
              maps process_i (0 upto (length argsA' - 1))
            else []
          end
    in
      (* Due to symmetry, only need to process one side. *)
      if Term_Ord.termless (A, B) then
        let
          val A_equivs = (RewriteTable.get_head_equiv tbl cA)
                             |> maps snd
                             |> RewriteTable.merge_box_with_info tbl id
        in
          maps process_A_equiv A_equivs
        end
      else []
    end

val cong_on_ineq_prfstep =
    {name = "cong_on_ineq",
     args = [TypedMatch (TY_PROP, @{term_pat "?A ~= ?B"})],
     priority = PRIORITY_ADD,
     func = OneStep cong_on_ineq_fn}

(* Given an assumption of the form EX x. A, we produce an assumption A
   with x in A replaced by a free variable. To avoid name collisions,
   when the update is produced x is replaced by an "internal" free
   variable, with suffix '_'. When the update is applied, that
   internal free variable is replaced by a fresh variable as
   determined by the context. We produce at most two variables at a
   time.
 *)
fun exists_elim_fn rtype {ctxt, ...} {id, prop, ...} =
    if not (RewriteTable.is_single_rtype rtype) then [] else
    let
      val t = prop_of' prop
    in
      if not (is_ex t orelse is_bex t orelse
              (is_neg t andalso is_all (dest_not t)) orelse
              (is_neg t andalso is_ball (dest_not t))) then [] else
      let
        val th = prop |> apply_to_thm' (normalize_exs_conv (~1) ctxt)
        val nms = Update.get_apply_exists_nms th
      in
        Update.apply_exists (id, th) ctxt nms
      end
    end

val exists_elim_prfstep =
    {name = "exists_elim",
     args = [TypedMatch (TY_PROP, boolVar "A")],
     priority = PRIORITY_ADD,
     func = OneStep exists_elim_fn}

val add_logic_proofsteps =
    fold add_prfstep [
      shadow_prop_item, shadow_term_item, eq_elim_prfstep, cong_on_ineq_prfstep,
      exists_elim_prfstep
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
    if is_neg (Thm.term_of ct) andalso
       is_conj (dest_not (Thm.term_of ct)) then
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
    let
      fun helper ct =
          if is_neg (Thm.term_of ct) andalso
             is_imp (dest_not (Thm.term_of ct)) then
            Conv.every_conv [rewr_obj_eq not_imp_th,
                             Conv.arg_conv helper] ct
          else
            try_nn_cancel_cv ct
    in
      (helper then_conv try_nn_cancel_cv) ct
    end

(* Convert term of form ~(A_1 | ... | A_n) to ~A_1 & ... & ~A_n,
   canceling any double negations.
 *)
fun not_disj_to_conj_cv ct =
    let
      fun helper ct =
          if is_neg (Thm.term_of ct) andalso
             is_disj (dest_not (Thm.term_of ct)) then
            Conv.every_conv [rewr_obj_eq de_Morgan_disj_th,
                             Conv.arg1_conv try_nn_cancel_cv,
                             Conv.arg_conv helper] ct
          else
            try_nn_cancel_cv ct
    in
      (helper then_conv try_nn_cancel_cv) ct
    end

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
fun disj_to_ritems prem_only disj_head (sz, th) =
    if sz = 1 then
      if has_vars (Thm.prop_of th) then
        let
          fun th_to_ritem th =
              Fact (TY_DISJ,
                    [term_of_bool prem_only, disj_head, prop_of' th], th)
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
      val tname = term_of_bool prem_only :: disj_head :: subs'
    in
      [Fact (TY_DISJ, tname, th)]
    end

fun disj_to_update prem_only disj_head (id, sc, sz, th) =
    if Thm.prop_of th aconv pFalse then
      ResolveBox {id = id, th = th}
    else
      AddItems {id = id, sc = sc,
                raw_items = disj_to_ritems prem_only disj_head (sz, th)}

(* Deconstruct the tname of a DISJ item. *)
fun dest_tname_of_disj tname =
    case tname of
        _ :: disj_head :: rest => (Thm.term_of disj_head, rest)
      | _ => raise AUTO2 "dest_tname_of_disj: too few terms in tname."

(* Determine whether the item is for matching premises only (from the
   first entry in tname.
 *)
fun is_match_prem_only {tname, ...} =
    bool_of_term (Thm.term_of (hd tname))

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
    (to_forall_cv ctxt)
        then_conv (forall_body_conv to_disj_cv ctxt)
        then_conv (reduce_boolify ctxt)

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
      (head, len, th' |> apply_to_thm' to_disj_cv
                      |> apply_to_thm (reduce_boolify ctxt))
    end

fun is_active_head disj_head = (not (disj_head aconv imp))

fun output_disj_fn ctxt (ts, _) =
    let
      val (disj_head, subs) = (hd (tl ts), tl (tl ts))
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
            val (_, csubs) = dest_tname_of_disj tname
            val subs = map Thm.term_of csubs
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
            val has_vars = exists has_vars (map Thm.term_of tname)
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
            (* Note this may not be the length of subs, but is the
               relevant value here.
             *)
            val len = length (ACUtil.dest_ac_r disj_ac (prop_of' th))
            val thy = Proof_Context.theory_of ctxt
            val vars = fold Term.add_vars (map Thm.term_of tname) []
          in
            let
              val pat_eq =
                  normalize_disj_cv ctxt (RewriteTable.tbl_cert tbl pat)
              val pat' = rhs_of pat_eq
              val (allc, disjc) = strip_forall_disj pat'
              val var_tys = map snd vars
            in
              if length allc <> length vars then []
              else if disjc > len then []
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
                val subst = map (cert ctxt) sch_vars ~~ map (cert ctxt) bd_vars
                val th' = subst_thm_atomic subst th
                val ctname' = cprop_of' th'
                val pat''' = Term.subst_bounds (bd_vars, strip_forall pat'')

                (* Find matches between pattern and term, both with bd_vars. *)
                val insts' = Matcher.rewrite_match_ac_bd
                                 true disj_ac tbl bd_vars (pat''', ctname')
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
    if is_neg t andalso exists (is_ex orf is_bex) (strip_conj (dest_not t)) then
      true
    else if exists (is_all orf is_ball) (strip_disj t) then
      true
    else
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
            val to_eqT_cv = (th RS eq_True_th) |> rewr_obj_eq |> Conv.try_conv
            (* Rewrite pat(inst) using the above, then rewrite to True. *)
            val pat_eqT =
                pat |> cert ctxt |> to_disj_cv
                    |> subst_thm ctxt inst
                    |> apply_to_thm (reduce_boolify ctxt)
                    |> apply_to_rhs (ac_disj_conv ~1 to_eqT_cv)
                    |> apply_to_rhs reduce_disj_True
                    |> to_obj_eq
            val patT = pat_eqT RS eq_True_inv_th
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
    if is_match_prem_only item1 then [] else
    let
      val {id, prop, tname = tname1, ...} = item1
      val thy = Proof_Context.theory_of ctxt
      val (disj_head, csubs) = dest_tname_of_disj tname1
      val subs = map Thm.term_of csubs
      fun count_var t = length (Term.add_vars t [])
      val max_nvar = fold (curry Int.max) (map count_var subs) 0
      val has_priority_term = exists (is_priority_term thy) (map get_neg subs)

      val (NO_MATCH, FREE_ONLY, SLOW_MATCH, YES_MATCH) = (0, 1, 2, 3)
      (* Test whether to perform matching on pattern. *)
      fun test_do_match (i, sub, nvar) =
          if max_nvar = 0 then YES_MATCH
          else let
            val nsub = get_neg sub
          in
            if not (is_pattern sub) then NO_MATCH
            else if length subs > 1 andalso
                    Property.is_property_prem thy nsub then NO_MATCH
            else if has_priority_term andalso
                    not (is_priority_term thy nsub) then SLOW_MATCH
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
                else if length subs = 1 then
                  let
                    val prop' = prop |> subst_thm_thy thy inst
                    val prop'' = if is_neg (prop_of' prop') then
                                   [prop', th] MRS contra_triv_th
                                 else
                                   [th, prop'] MRS contra_triv_th
                  in
                    [ResolveBox {id = id', th = prop''}]
                  end
                else let
                  val cv = th |> to_eqF_th |> rewr_obj_eq
                              |> Conv.try_conv |> ac_disj_conv (length subs)
                  val prop' =
                      prop |> subst_thm_thy thy inst
                           |> apply_to_thm' (boolify_disj_conv (length subs))
                           |> apply_to_thm' cv
                  val unit_count =
                      prop' |> prop_of' |> ACUtil.dest_ac_r disj_ac
                            |> filter (fn t => t aconv bFalse) |> length
                  val _ = assert (unit_count > 0)
                                 "disj_match_update: cannot find term."
                  val prop'' =
                      prop' |> apply_to_thm' (ACUtil.normalize_unit disj_ac)
                            |> apply_to_thm (reduce_boolify ctxt)
                  val shadow_updt = if nvar > 0 then [] else
                                    [ShadowItem {id = id', item = item1}]
                  val new_len = length subs - unit_count
                  val sc = if max_nvar = 0 then 1
                           else if do_match = SLOW_MATCH then 200 else 10
                  val disj_updt = disj_to_update false disj_head
                                                 (id', SOME sc, new_len, prop'')
                in
                  disj_updt :: shadow_updt
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
      val subs = (dest_tname_of_disj tname) |> snd |> map Thm.term_of
    in
      if length subs > 1 then [] else
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
                       RewriteTable.is_equiv_t id' tbl (dest_eq prop')
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
      [disj_to_update false imp (id, NONE, 2, forward),
       disj_to_update false imp (id, NONE, 2, backward)]
    end

val disj_match_iff_prfstep =
    {name = "disj_match_iff",
     args = [TypedMatch (TY_DISJ, mk_bool_eq (boolVar "A", boolVar "B"))],
     priority = PRIORITY_ADD,
     func = OneStep disj_match_iff_fn}

(* For active case, create box checking the next case. *)
fun disj_create_case_fn rtype _ {id, tname, ...} =
    if not (RewriteTable.is_single_rtype rtype) then [] else
    if exists has_vars (map Thm.term_of tname) then [] else
    let
      val (disj_head, csubs) = dest_tname_of_disj tname
      val subs = map Thm.term_of csubs
    in
      if not (is_active_head disj_head) then []
      else if length subs = 1 then []
      else let
        val inits =
            map (fn (is_var, t) => if is_var then InitVar t
                                   else InitAssum (mk_Trueprop t))
                (extract_init_infos true (get_neg (hd subs)))
      in
        [AddBoxes {id = id, sc = NONE, inits = inits, cbs = []}]
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
      else if is_match_prem_only item1 andalso
              not (is_match_prem_only item2) then []
      else if subset (op aconvc) (subs1, subs2) then
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
    fold ItemIO.add_item_type [
      (TY_DISJ, SOME (drop 2), SOME output_disj_fn)

    ] #> fold ItemIO.add_typed_matcher [
      (TY_DISJ, disj_typed_matcher)

    ] #> fold ItemIO.add_prop_matcher [
      (TY_DISJ, disj_prop_matcher)

    ] #> fold add_prfstep (
      [match_update_prfstep, match_one_sch_prfstep, disj_match_iff_prfstep,
       disj_create_case_prfstep, disj_shadow_prfstep]
    )

(* Generalized form of splitting A & B. Also deal with cases ~(A | B)
   and ~(A --> B).
 *)
fun split_conj_gen_th ctxt th =
    th |> apply_to_thm' to_conj_cv
       |> apply_to_thm (reduce_boolify ctxt)
       |> split_conj_th

fun eq_normalizer _ ritem =
    case ritem of
        Handler _ => [ritem]
      | Fact (ty_str, _, th) =>
        if ty_str <> TY_PROP then [ritem]
        else if is_eq_term (prop_of' th) then
          let
            val (lhs, rhs) = dest_eq (prop_of' th)
          in
            [Fact (TY_EQ, [lhs, rhs], th)]
          end
        else [ritem]

fun property_normalizer ctxt ritem =
    case ritem of
        Handler _ => [ritem]
      | Fact (ty_str, _, th) =>
        if ty_str <> TY_PROP then [ritem]
        else let
          val thy = Proof_Context.theory_of ctxt
          val prop' = prop_of' th
        in
          if Property.is_property_const thy prop' then
            [Fact (TY_PROPERTY, [prop'], th)]
          else [ritem]
        end

fun disj_normalizer ctxt ritem =
    case ritem of
        Handler _ => [ritem]
      | Fact (ty_str, _, th) =>
        if ty_str <> TY_PROP then [ritem]
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
              disj_to_ritems false disj_head (sz, disj_th)
            end
          else [ritem]
        end

fun logic_thm_update ctxt (id, th) =
    let
      val t = prop_of' th
    in
      if is_all t orelse is_ball t orelse
         is_neg t andalso is_ex (dest_not t) orelse
         is_neg t andalso is_bex (dest_not t)
      then
        let
          val (disj_head, sz, disj_th) = analyze_disj_th ctxt th
          val raw_items = disj_to_ritems true disj_head (sz, disj_th)
        in
          AddItems {id = id, sc = NONE, raw_items = raw_items}
        end
      else
        Update.thm_update (id, th)
    end

val add_disj_normalizers =
    Normalizer.add_th_normalizer (
      "split_conj_gen", split_conj_gen_th

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
      [AddItems {id = id, sc = NONE, raw_items = [ritem]}]
    end

fun match_term_def_fn rtype {ctxt, ...} item1 item2 =
    let
      val {id, tname, prop, ...} = item1
      val pat = Thm.term_of (hd tname)
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

val add_term_def_proofsteps =
    fold ItemIO.add_item_type [
      (TY_TERM_DEF, NONE, NONE)

    ] #> fold ItemIO.add_typed_matcher [
      (TY_TERM_DEF, ItemIO.univ_matcher)

    ] #> add_prfstep match_term_def_prfstep

end  (* structure Logic_ProofSteps. *)
