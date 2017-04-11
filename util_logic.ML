signature UTIL_BASE =
sig
  (* Types *)
  val boolT: typ
  val mk_setT: typ -> typ

  (* Equality *)
  val dest_eq: term -> term * term
  val cdest_eq: cterm -> cterm * cterm
  val dest_eq_lhs: term -> term
  val dest_eq_rhs: term -> term
  val mk_eq: term * term -> term
  val mk_bool_eq: term * term -> term
  val is_eq_term_iff: term -> bool
  val is_eq_term_non_iff: term -> bool
  val is_eq_term: term -> bool

  (* Terms *)
  val bFalse: term
  val bTrue: term
  val Trueprop_name: string
  val Not_name: string
  val Conj_name: string
  val Disj_name: string
  val Imp_name: string
  val All_name: string
  val Ex_name: string
  val is_if: term -> bool

  (* Cterms *)
  val cTrueprop: cterm
  val cNot: cterm
  val cConj: cterm
  val cDisj: cterm

  (* Theorems for equality *)
  val to_meta_eq_cv: conv
  val to_meta_eq: thm -> thm
  val to_obj_eq_cv: conv
  val to_obj_eq: thm -> thm
  val to_obj_eq_iff: thm -> thm
  val obj_sym: thm -> thm

  (* Theorems *)
  val true_th: thm
  val nn_cancel_th: thm
  val to_contra_form_th: thm
  val to_contra_form_th': thm
  val atomize_imp_th: thm
  val atomize_all_th: thm
  val conjunct1_th: thm
  val conjunct2_th: thm
  val conjI_th: thm
  val or_intro1_th: thm
  val or_intro2_th: thm
  val iffD1_th: thm
  val iffD2_th: thm
  val inv_back_th: thm
  val sym_th: thm
  val exE_th': thm
  val eq_True_th: thm
  val eq_True_inv_th: thm
  val eq_False_th: thm
  val eq_False_th': thm
  val disj_True1_th: thm
  val disj_True2_th: thm
  val use_vardef_th: thm
  val ex_vardef_th: thm
  val imp_conv_disj_th: thm
  val de_Morgan_conj_th: thm
  val de_Morgan_disj_th: thm
  val not_ex_th: thm
  val not_all_th: thm
  val not_imp_th: thm

  (* Theorems for proofstep module *)
  val atomize_conjL_th: thm
  val atomize_conjL2_th: thm
  val backward_conv_th: thm
  val backward1_conv_th: thm
  val backward2_conv_th: thm
  val resolve_conv_th: thm

  (* Other theorems *)
  val contra_triv_th: thm

  (* AC for conj and disj *)
  val conj_assoc_th: thm
  val conj_commute_th: thm
  val conj_unitL_th: thm
  val disj_assoc_th: thm
  val disj_commute_th: thm
  val disj_unitL_th: thm

  (* Member, Ball and Bex *)
  val Mem_name: string
  val Ball_name: string
  val Bex_name: string
  val Bex_def_th: thm
  val Ball_def_th: thm
  val swap_ex_conj_th: thm
  val swap_all_implies_th: thm

  (* In logics such as TLA, deal with boolify. *)
  val reduce_boolify: Proof.context -> conv
  val boolify_disj_conv: int -> conv
end

signature UTIL_LOGIC =
sig
  (* Terms *)
  val term_of_bool: bool -> term
  val bool_of_term: term -> bool
  val Trueprop: term
  val is_Trueprop: term -> bool
  val mk_Trueprop: term -> term
  val dest_Trueprop: term -> term
  val Trueprop_conv: conv -> conv
  val pFalse: term
  val Not: term
  val mk_not: term -> term
  val dest_not: term -> term
  val is_neg: term -> bool
  val get_neg: term -> term
  val get_neg': term -> term
  val is_eq_term': term -> bool
  val conj: term
  val is_conj: term -> bool
  val mk_conj: term * term -> term
  val strip_conj: term -> term list
  val disj: term
  val is_disj: term -> bool
  val mk_disj: term * term -> term
  val strip_disj: term -> term list
  val imp: term
  val is_imp: term -> bool
  val mk_imp: term * term -> term
  val dest_imp: term -> term * term
  val strip_obj_imp: term -> term list * term
  val is_obj_all: term -> bool
  val is_all: term -> bool
  val is_ball: term -> bool
  val is_ex: term -> bool
  val is_bex: term -> bool
  val mk_exists: string * typ * term -> term
  val is_mem: term -> bool
  val mk_mem: term * term -> term
  val extract_init_infos: bool -> term -> (bool * term) list

  (* cterms *)
  val cdest_Trueprop: cterm -> cterm
  val cstrip_horn': thm -> cterm list * cterm
  val get_cneg: cterm -> cterm

  (* Theorems *)
  val is_true_th: thm -> bool
  val prop_of': thm -> term
  val cprop_of': thm -> cterm
  val concl_of': thm -> term
  val make_trueprop_eq: thm -> thm
  val assume_eq: theory -> term * term -> thm
  val apply_to_thm': conv -> thm -> thm
  val rewr_obj_eq: thm -> conv
  val rewr_obj_eq_sym: thm -> conv
  val rewr_obj_eq_top: Proof.context -> thm -> conv
  val try_nn_cancel_cv: conv
  val make_neg_eq: thm -> thm
  val rewrite_to_contra_form: conv
  val rewrite_thm_to_contra_form: thm -> thm
  val rewrite_from_contra_form: conv
  val rewrite_thm_from_contra_form: thm -> thm
  val to_obj_conv: Proof.context -> conv
  val to_obj_conv_on_horn: Proof.context -> conv
  val to_obj_conv_on_horn_th: thm -> thm
  val to_meta_imp_conv: conv
  val to_meta_imp_conv_n: int -> conv
  val to_meta_all_conv: Proof.context -> conv
  val conj_left_th: thm -> thm
  val conj_right_th: thm -> thm
  val equiv_forward_th: thm -> thm
  val equiv_backward_th: thm -> thm
  val inv_backward_th: thm -> thm
  val to_obj_eq_th: thm -> thm
  val to_obj_eq_iff_th: thm -> thm
  val obj_sym_th: thm -> thm
  val backward_th: thm -> thm
  val horn_conv: conv -> conv
  val split_conj_th: thm -> thm list
  val split_not_disj_th: thm -> thm list
  val strip_horn': thm -> term list * term
  val mk_conjs_th: thm list -> thm
  val ex_elim: Proof.context -> term -> thm -> thm
  val to_eqF_th: thm -> thm
  val normalize_exs_conv: int -> Proof.context -> conv
  val normalize_alls_conv: int -> Proof.context -> conv

  (* Wrapper around common tactics. *)
  val prove_by_tac: (Proof.context -> int -> tactic) -> Proof.context ->
                    thm list -> term -> thm
  val contra_by_tac: (Proof.context -> int -> tactic) -> Proof.context ->
                     thm list -> thm
  val prove_by_simp: Proof.context -> thm list -> term -> thm
  val contra_by_simp: Proof.context -> thm list -> thm
end;

functor UtilLogic(Base:UTIL_BASE) : UTIL_LOGIC =
struct

open Base

(* Booleans *)

fun term_of_bool b = (if b then bTrue else bFalse)

fun bool_of_term t =
    if t aconv bTrue then true
    else if t aconv bFalse then false
    else raise AUTO2 "bool_of_term: unexpected t."

(* Trueprop *)

val Trueprop = Const (Trueprop_name, boolT --> propT)

(* Returns whether the given term is Trueprop. *)
fun is_Trueprop t =
    let
      val _ = assert (fastype_of t = propT) "is_Trueprop: wrong type"
    in
      case t of Const (c, _) $ _ => c = Trueprop_name
              | _ => false
    end

fun mk_Trueprop P = Trueprop $ P

fun dest_Trueprop t =
    case t of
        Const (c, _) $ P =>
        if c = Trueprop_name then P else raise AUTO2 "dest_Trueprop"
      | _ => raise AUTO2 "dest_Trueprop"

fun Trueprop_conv cv ct =
    case Thm.term_of ct of
        Const (c, _) $ _ =>
        if c = Trueprop_name then Conv.arg_conv cv ct
        else raise CTERM ("Trueprop_conv", [ct])
      | _ => raise CTERM ("Trueprop_conv", [ct])

val pFalse = Trueprop $ bFalse

(* Not *)

val Not = Const (Not_name, boolT --> boolT)

fun mk_not P = Not $ P

fun dest_not t =
    case t of
        Const (c, _) $ P =>
        if c = Not_name then P else raise AUTO2T ("dest_not", [t])
      | _ => raise AUTO2T ("dest_not", [t])

(* Returns whether the given term is in neg form. *)
fun is_neg t =
    let
      val _ = assert (fastype_of t = boolT) "is_neg: wrong type"
    in
      case t of
          Const (c, _) $ _ => c = Not_name
        | _ => false
    end

(* Returns the negation of the given term. Avoids double negatives. *)
fun get_neg t =
    let
      val _ = assert (fastype_of t = boolT) "get_neg: wrong type"
    in
      case t of
          Const (c, _) $ P => if c = Not_name then P else Not $ t
        | _ => Not $ t
    end

(* Version of get_neg for Trueprop terms. *)
fun get_neg' t =
    let
      val _ = assert (is_Trueprop t) "get_neg': input should be a Trueprop."
    in
      t |> dest_Trueprop |> get_neg |> mk_Trueprop
    end

(* Version of is_eq_term' for Trueprop terms. *)
fun is_eq_term' t =
    let
      val _ = assert (fastype_of t = propT) "is_eq_term': wrong type"
    in
      is_Trueprop t andalso is_eq_term (dest_Trueprop t)
    end

(* Conjunction and disjunction *)

val conj = Const (Conj_name, boolT --> boolT --> boolT)
fun is_conj t = case t of Const (c, _) $ _ $ _ => c = Conj_name | _ => false
fun mk_conj (t, u) = conj $ t $ u
fun strip_conj t =
    case t of
        Const (c, _) $ A $ B =>
        if c = Conj_name then A :: strip_conj B else [t]
      | _ => [t]

val disj = Const (Disj_name, boolT --> boolT --> boolT)
fun is_disj t = case t of Const (c, _) $ _ $ _ => c = Disj_name | _ => false
fun mk_disj (t, u) = disj $ t $ u
fun strip_disj t =
    case t of
        Const (c, _) $ A $ B =>
        if c = Disj_name then A :: strip_disj B else [t]
      | _ => [t]

(* Object implication *)

val imp = Const (Imp_name, boolT --> boolT --> boolT)
fun is_imp t = case t of Const (c, _) $ _ $ _ => c = Imp_name | _ => false
fun mk_imp (t, u) = imp $ t $ u

fun dest_imp t =
    case t of
        Const (c, _) $ A $ B =>
        if c = Imp_name then (A, B) else raise AUTO2T ("dest_imp", [t])
      | _ => raise AUTO2T ("dest_imp", [t])

(* Given t of form A1 --> ... --> An, return ([A1, ..., A(n-1)], An). *)
fun strip_obj_imp t =
    case t of
        Const (c, _) $ A $ B =>
        if c = Imp_name then
          let val (As, B') = strip_obj_imp B in (A :: As, B') end
        else ([], t)
      | _ => ([], t)

fun is_obj_all t =
    case t of
        Const (c, _) $ Abs _ => c = All_name
      | _ => false

fun is_all t =
    case t of Const (c, _) $ Abs _ => (c = All_name)
            | _ => false

fun is_ball t =
    case t of Const (c, _) $ _ $ _ => (c = Ball_name)
            | _ => false

fun is_ex t =
    case t of Const (c, _) $ Abs _ => (c = Ex_name)
            | _ => false

fun is_bex t =
    case t of Const (c, _) $ _ $ _ => (c = Bex_name)
            | _ => false

fun mk_exists (x, T, P) =
    Const (Ex_name, (T --> boolT) --> boolT) $ Term.absfree (x, T) P

fun is_mem t =
    case t of Const (c, _) $ _ $ _ => (c = Mem_name)
            | _ => false

fun mk_mem (x, A) =
    let
      val T = fastype_of x
    in
      Const (Mem_name, T --> mk_setT T --> boolT) $ x $ A
    end

(* Given a term of form !x_1 ... x_k. P_1 --> ... --> P_n --> Q,
   extract the variables x_1 to x_k and the assumptions P_1 to P_n and
   ~Q. Return the results as a list of pairs (is_var, t).

   Used when creating a new box. In All and Ball bindings, the
   argument must be in Abs form (to provide a name for the new
   variable).
 *)
fun extract_init_infos_aux bInt t nms =
    if is_all t then
      case t of
          _ $ Abs (nm, T, b) =>
          let
            val nm' = if bInt andalso member (op =) nms nm then
                        singleton (Name.variant_list nms) nm
                      else nm
            val int_nm' = if bInt then Name.internal nm' else nm'
          in
            (true, (Free (int_nm', T))) ::
            extract_init_infos_aux
                bInt (Term.subst_bound (Free (int_nm', T), b)) (nm' :: nms)
          end
        | f $ arg =>
          let
            val T = fastype_of f |> domain_type |> domain_type
            val t' = f $ Abs ("x", T, arg $ Bound 0)
          in
            extract_init_infos_aux bInt t' nms
          end
        | _ => raise AUTO2 "extract_init_infos"
    else if is_ball t then
      case t of
          _ $ S $ Abs (nm, T, b) =>
          let
            val nm' = if bInt andalso member (op =) nms nm then
                        singleton (Name.variant_list nms) nm
                      else nm
            val int_nm' = if bInt then Name.internal nm' else nm'
          in
            (true, (Free (int_nm', T))) ::
            (false, mk_mem (Free (int_nm', T), S)) ::
            extract_init_infos_aux
                bInt (Term.subst_bound (Free (int_nm', T), b)) (nm' :: nms)
          end
        | f $ S $ arg =>
          let
            val T = fastype_of f |> domain_type |> dest_Type |> snd |> hd
            val t' = f $ S $ Abs ("x", T, arg $ Bound 0)
          in
            extract_init_infos_aux bInt t' nms
          end
        | _ => raise AUTO2 "extract_init_infos"
    else if is_imp t then
      (false, dest_arg1 t) :: extract_init_infos_aux bInt (dest_arg t) nms
    else if is_neg t then
      [(false, dest_not t)]
    else
      [(false, mk_not t)]

fun extract_init_infos bInt t = extract_init_infos_aux bInt t []

(* cterms *)

fun cdest_Trueprop ct =
    case Thm.term_of ct of
        Const (c, _) $ _ =>
        if c = Trueprop_name then Thm.dest_arg ct else
        raise AUTO2 "dest_Trueprop"
      | _ => raise AUTO2 "dest_Trueprop"

fun cstrip_horn' th =
    (map cdest_Trueprop (Drule.strip_imp_prems (Thm.cprop_of th)),
     cdest_Trueprop (Drule.strip_imp_concl (Thm.cprop_of th)))

fun get_cneg ct =
    let
      val t = Thm.term_of ct
      val _ = assert (fastype_of t = boolT) "get_neg: wrong type"
    in
      case t of
          Const (c, _) $ _ => if c = Not_name then Thm.dest_arg ct
                              else Thm.apply cNot ct
        | _ => Thm.apply cNot ct
    end

(* Theorems *)

fun is_true_th th = pointer_eq (th, true_th)
fun prop_of' th = dest_Trueprop (Thm.prop_of th)
fun cprop_of' th = cdest_Trueprop (Thm.cprop_of th)
fun concl_of' th = dest_Trueprop (Thm.concl_of th)

(* Given an equality between bools, make it an equality between props,
   by applying the function Trueprop to both sides.
 *)
fun make_trueprop_eq th =
    Thm.combination (Thm.reflexive cTrueprop) th

(* Assumed theorems. *)
fun assume_eq thy (t1, t2) =
    Thm.assume (cert_thy thy (mk_Trueprop (mk_eq (t1, t2))))

(* Apply cv to the statement of th, skipping Trueprop. *)
fun apply_to_thm' cv th = apply_to_thm (Trueprop_conv cv) th

(* Obtain rewriting conv from obj equality. *)
fun rewr_obj_eq eq_th = Conv.rewr_conv (to_meta_eq eq_th)

(* Obtain rewriting conv in the reverse direction from obj equality. *)
fun rewr_obj_eq_sym eq_th = Conv.rewr_conv (meta_sym (to_meta_eq eq_th))

(* Rewrite on subterms, top order. *)
fun rewr_obj_eq_top ctxt eq_th =
    Conv.top_conv (K (Conv.try_conv (rewr_obj_eq eq_th))) ctxt

(* Try to cancel terms of the form ~~A. *)
val try_nn_cancel_cv = Conv.try_conv (rewr_obj_eq nn_cancel_th)

(* Given an equality A == B, make the equality ~A == ~B. Cancel ~~ on
   both sides if exists.
 *)
fun make_neg_eq th =
    th |> Thm.combination (Thm.reflexive cNot)
       |> apply_to_lhs try_nn_cancel_cv
       |> apply_to_rhs try_nn_cancel_cv

(* If ct is of the form [...] ==> False, leave it unchanged.
   Otherwise, change [...] ==> B to [..., ~ B] ==> False and change
   [...] ==> ~ B to [..., B] ==> False.
 *)
fun rewrite_to_contra_form ct =
    let
      val (_, concl) = Logic.strip_horn (Thm.term_of ct)
      val concl' = dest_Trueprop concl
    in
      if concl' aconv bFalse then
        Conv.all_conv ct
      else if is_neg concl' then
        concl_conv (Conv.rewr_conv to_contra_form_th') ct
      else
        concl_conv (Conv.rewr_conv to_contra_form_th) ct
    end

val rewrite_thm_to_contra_form = apply_to_thm rewrite_to_contra_form

(* Rewrite ct from [...] ==> A ==> False to [...] ==> ~ A and from
   [...] ==> ~ A ==> False to [...] ==> A.
 *)
fun rewrite_from_contra_form ct =
    let
      val (prems, concl) = Logic.strip_horn (Thm.term_of ct)
      val _ = assert (concl aconv pFalse)
                     "rewrite_from_contra_form: concl should be false."
      val num_prems = length prems
      val last_prem' = dest_Trueprop (nth prems (num_prems-1))
      val to_contra_form = if is_neg last_prem' then to_contra_form_th
                           else to_contra_form_th'
    in
      concl_conv_n (num_prems-1)
                   (Conv.rewr_conv (meta_sym to_contra_form)) ct
    end

val rewrite_thm_from_contra_form = apply_to_thm rewrite_from_contra_form

(* Converts ==> to --> and !! to !. *)
fun to_obj_conv ctxt ct =
    (case Thm.term_of ct of
         Const ("Pure.imp", _) $ _ $ _ =>
         (Conv.binop_conv (to_obj_conv ctxt))
             then_conv (Conv.rewr_conv atomize_imp_th)
       | Const ("Pure.all", _) $ Abs _ =>
         (Conv.binder_conv (to_obj_conv o snd) ctxt)
             then_conv (Conv.rewr_conv atomize_all_th)
             then_conv (Trueprop_conv (
                           Conv.try_conv (rewr_obj_eq (obj_sym Ball_def_th))))
       | _ => Conv.all_conv) ct

(* When ct is of form A1 ==> ... ==> An, apply to_obj_conv to each Ai. *)
fun to_obj_conv_on_horn ctxt ct =
    (case Thm.term_of ct of
         Const ("Pure.imp", _) $ _ $ _ =>
         Conv.combination_conv (Conv.arg_conv (to_obj_conv ctxt))
                               (to_obj_conv_on_horn ctxt)
       | _ => Conv.all_conv) ct

fun to_obj_conv_on_horn_th th =
    let
      val ctxt = Proof_Context.init_global (Thm.theory_of_thm th)
    in
      apply_to_thm (to_obj_conv_on_horn ctxt) th
    end

(* Converts A1 --> ... --> An to A1 ==> ... ==> An. *)
fun to_meta_imp_conv ct =
    let
      val t = Thm.term_of ct
    in
      if is_Trueprop t andalso is_imp (dest_Trueprop t) then
        ((Conv.rewr_conv (meta_sym atomize_imp_th))
             then_conv (Conv.arg_conv to_meta_imp_conv)) ct
      else
        Conv.all_conv ct
    end

(* Convert the first n object implies to meta implies. *)
fun to_meta_imp_conv_n n ct =
    (case n of
         0 => Conv.all_conv
       | _ => (Conv.rewr_conv (meta_sym atomize_imp_th))
                  then_conv (Conv.arg_conv (to_meta_imp_conv_n (n-1)))) ct

(* Converts ! to !! on the outermost level. *)
fun to_meta_all_conv ctxt ct =
    let
      val t = Thm.term_of ct
    in
      if is_Trueprop t andalso is_obj_all (dest_Trueprop t) then
        ((Conv.rewr_conv (meta_sym atomize_all_th))
             then_conv (Conv.binder_conv (to_meta_all_conv o snd) ctxt)) ct
      else
        Conv.all_conv ct
    end

(* Modify th using imp_th, and add postfix to name (if available). *)
fun thm_RS_mod imp_th suffix th =
    (th RS imp_th) |> Drule.zero_var_indexes
                   |> update_name_of_thm th suffix

(* From A & B, obtain A. *)
val conj_left_th = thm_RS_mod conjunct1_th "@left"
(* From A & B, obtain B. *)
val conj_right_th = thm_RS_mod conjunct2_th "@right"
(* From (A::bool) = B, obtain A ==> B. *)
val equiv_forward_th = thm_RS_mod iffD1_th "@eqforward"
(* From (A::bool) = B, obtain B ==> A. *)
val equiv_backward_th = thm_RS_mod iffD2_th "@eqbackward"
(* From (A::bool) = B, obtain ~A ==> ~B. *)
val inv_backward_th = thm_RS_mod inv_back_th "@invbackward"
(* Same as to_obj_eq, except keeping names and indices. *)
fun to_obj_eq_th th = th |> to_obj_eq |> update_name_of_thm th "@obj_eq"
(* Same as to_obj_eq_iff, except keeping names and indices. *)
fun to_obj_eq_iff_th th = th |> to_obj_eq_iff |> update_name_of_thm th "@iff"
(* Same as obj_sym, except keeping names and indices. *)
fun obj_sym_th th = th |> obj_sym |> update_name_of_thm th "@sym"

(* Using cv, rewrite all assumptions and conclusion in ct. *)
fun horn_conv cv ct =
    (case Thm.term_of ct of
         @{const Pure.imp} $ _ $ _ =>
         (Conv.arg1_conv (Trueprop_conv cv))
             then_conv (Conv.arg_conv (horn_conv cv))
       | _ => Trueprop_conv cv) ct

(* From A ==> B, obtain ~B ==> ~A *)
fun backward_th th =
    let
      val ctxt = Proof_Context.init_global (Thm.theory_of_thm th)
    in
      th |> apply_to_thm (Conv.rewr_conv backward_conv_th)
         |> apply_to_thm (horn_conv try_nn_cancel_cv)
         |> apply_to_thm (reduce_boolify ctxt)
    end

(* Given th of form (P ==>) A1 & ... & An, return theorems (P ==>) A1,
   ..., (P ==>) An, where there can be zero or more premises in front.
 *)
fun split_conj_th th =
    if is_conj (prop_of' th) then
      (th RS conjunct1_th) :: (split_conj_th (th RS conjunct2_th))
    else [th]

(* Given th of form ~ (A1 | ... | An), return theorems ~ A1, ... ~ An. *)
fun split_not_disj_th th =
    let
      val t = prop_of' th
    in
      if is_neg t andalso is_disj (dest_not t) then
        (th RS or_intro1_th) :: (split_not_disj_th (th RS or_intro2_th))
      else [th]
    end

(* Similar to Logic.strip_horn, except remove Trueprop. *)
fun strip_horn' th = (Logic.strip_horn (Thm.prop_of th))
                         |> apfst (map dest_Trueprop)
                         |> apsnd dest_Trueprop

fun mk_conjs_th ths =
    case ths of
        [] => raise AUTO2 "mk_conjs_th"
      | [th] => th
      | th :: rest => [th, mk_conjs_th rest] MRS conjI_th

(* Given th of form P x ==> False, where x is the given free variable,
   obtain new theorem of form (EX x. P x) ==> False. The function is
   written so it can be applied to multiple variables with fold. For
   example, "fold (ex_elim ctxt) [x, y] (P x y ==> False) will give
   (EX y x. P x y) ==> False.
 *)
fun ex_elim ctxt freevar th =
    let
      val th' = th |> Thm.forall_intr (cert ctxt freevar)
      val head_prem = hd (Thm.prems_of exE_th')
      val inst = pattern_match ctxt (head_prem, Thm.prop_of th')
      val exE_inst = subst_thm ctxt inst exE_th'
    in
      Thm.elim_implies th' exE_inst
    end

(* Convert ~A to A = False, and A to ~A = False. *)
fun to_eqF_th th =
    th RS (if is_neg (prop_of' th) then eq_False_th else eq_False_th')

(* Normalize a single existence quantifier. Attempt to rewrite ct into
   the form Ex x. P x. This includes:

   - Ex x : S. P x to Ex x. x : S & P x.

   - A & Ex x. P x to Ex x. A & P x.
 *)
fun normalize_ex_conv ctxt ct =
    let
      val t = Thm.term_of ct
    in
      if is_ex t then
        Conv.all_conv ct
      else if is_bex t then
        rewr_obj_eq Bex_def_th ct
      else if is_neg t andalso is_all (dest_not t) then
        rewr_obj_eq not_all_th ct
      else if is_neg t andalso is_ball (dest_not t) then
        ((Conv.arg_conv (rewr_obj_eq Ball_def_th))
             then_conv (rewr_obj_eq not_all_th)
             then_conv (Conv.binder_conv
                            (K (rewr_obj_eq not_imp_th)) ctxt)) ct
      else if is_conj t then
        ((Conv.arg_conv (normalize_ex_conv ctxt))
             then_conv (rewr_obj_eq swap_ex_conj_th)) ct
      else
        Conv.no_conv ct
    end

(* Similar to normalize_ex_conv, swapping forall and implies. *)
fun normalize_all_conv ct =
    let
      val t = Thm.term_of ct
    in
      if is_all t then
        Conv.all_conv ct
      else if is_ball t then
        rewr_obj_eq Ball_def_th ct
      else if is_imp t then
        ((Conv.arg_conv normalize_all_conv)
             then_conv (rewr_obj_eq swap_all_implies_th)) ct
      else
        Conv.no_conv ct
    end

(* Move existence quantifiers to the left of ct. If the integer
   argument n is at least 0, move exactly n existence quantifiers to
   the left (throwing an error if it is not possible). Otherwise, move
   as many existence quantifiers to the left as possible.
 *)
fun normalize_exs_conv n ctxt ct =
    if n = 0 then
      Conv.all_conv ct
    else
      ((normalize_ex_conv ctxt) then_conv (
         Conv.binder_conv ((normalize_exs_conv (n-1)) o snd) ctxt)) ct
      handle CTERM _ =>
             if n > 0 then raise CTERM ("normalize_exs_conv", [ct])
             else Conv.all_conv ct

(* Similar to normalize_exs_conv. Move forall quantifiers to the front. *)
fun normalize_alls_conv n ctxt ct =
    if n = 0 then
      Conv.all_conv ct
    else
      (normalize_all_conv then_conv (
          Conv.binder_conv ((normalize_alls_conv (n-1)) o snd) ctxt)) ct
      handle CTERM _ =>
             if n > 0 then raise CTERM ("normalize_alls_conv", [ct])
             else Conv.all_conv ct

(* Generic wrapper function. tac can be arith_tac, simp_tac, etc. *)
fun prove_by_tac tac ctxt ths goal =
    let
      val goal' = Logic.list_implies (map Thm.prop_of ths, mk_Trueprop goal)
    in
      ths MRS (Goal.prove ctxt [] [] goal' (K (tac ctxt 1)))
    end

fun contra_by_tac tac ctxt ths = prove_by_tac tac ctxt ths bFalse

val prove_by_simp = prove_by_tac Simplifier.asm_full_simp_tac
val contra_by_simp = contra_by_tac Simplifier.asm_full_simp_tac

end  (* structure UtilLogic *)
