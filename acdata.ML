(* Dealing with associative-commutative operations. *)

(* Instantiated version of AC info. *)
type ac_inst_info = {
  cfhead: cterm, assoc_cv: conv, assoc_sym_cv: conv,
  comm_cv: conv, unit_val: term, unit_cv: conv,
  uinv_op: term, uinv_cv: conv, inv_op: term, inv_cv: conv}

(* Register of instantiated infos. Each ac_info_info is registered
   under its head, uinv, and inv operators (if applicable).
 *)
structure ACInstData =
Proof_Data (
  type T = ac_inst_info Termtab.table;
  fun init _ = Termtab.empty;
)

(* Generator for ac_inst_info. *)
type ac_info = theory -> term -> ac_inst_info option

(* Register of generators of ac_inst_info. *)
structure ACData =
Theory_Data (
  type T = ac_info Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge pointer_eq
)

(* Constructing ac_inst_info from a list of theorems. *)
type ac_info_full_constr = {
  assoc_th: thm,  (* (a . b) . c = a . (b . c) *)
  comm_th: thm,   (* a . b = b . a *)
  unitl_th: thm,  (* e . a = a *)
  unitr_th: thm,  (* a . e = a *)
  uinv_uinv_th: thm,   (* -(-a) = a *)
  uinv_head_th: thm,   (* -(a . b) = -a . -b (or -b . -a) *)
  uinv_unit_th: thm,   (* -e = e *)
  inv_th: thm     (* a - b = a + -b *)
}

type ac_info_au_constr = {
  assoc_th: thm, unitl_th: thm, unitr_th: thm
}

type ac_info_acu_constr = {
  assoc_th: thm, comm_th: thm, unitl_th: thm
}

signature ACUTIL =
sig
  val inst_ac_info: theory -> typ -> ac_info_full_constr -> ac_inst_info option
  val head_agrees: ac_inst_info -> term -> bool
  val head_agrees_uinv: ac_inst_info -> term -> bool
  val head_agrees_all: ac_inst_info -> term -> bool
  val get_head_ac_info: Proof.context -> term -> ac_inst_info option
  val get_head_ac_info_all: Proof.context -> term -> ac_inst_info option
  val constr_ac_info: ac_info_full_constr -> ac_info
  val constr_ac_info_au: ac_info_au_constr -> ac_info
  val constr_ac_info_acu: ac_info_acu_constr -> ac_info
  val swap_l_cv: ac_inst_info -> conv
  val swap_r_cv: ac_inst_info -> conv

  val add_ac_data: string * ac_info -> theory -> theory
  val inst_ac_infos: theory -> term -> ac_inst_info list
  val add_ac_inst_info: ac_inst_info -> Proof.context -> Proof.context
  val add_inst_ac_infos: term -> Proof.context -> Proof.context
  val clear_ac_data: theory -> theory
  val get_head_ac_info_thy_gen: bool -> theory -> term -> ac_inst_info option
  val get_head_ac_info_thy: theory -> term -> ac_inst_info option
  val get_head_ac_info_all_thy: theory -> term -> ac_inst_info option

  val has_assoc_th: ac_inst_info -> bool
  val has_comm_th: ac_inst_info -> bool
  val has_unit_th: ac_inst_info -> bool
  val has_inv_th: ac_inst_info -> bool

  val dest_ac_l: ac_inst_info -> term -> term list
  val dest_ac_r: ac_inst_info -> term -> term list
  val dest_ac_gen: bool -> ac_inst_info -> term -> term list
  val dest_ac_total: ac_inst_info -> term -> term list
  val list_ac_l: ac_inst_info -> term list -> term
  val list_ac_r: ac_inst_info -> term list -> term
  val list_ac_gen: bool -> ac_inst_info -> term list -> term
  val comb_ac_equiv: ac_inst_info -> thm list -> thm
  val normalize_assoc_l: ac_inst_info -> conv
  val normalize_assoc_r: ac_inst_info -> conv
  val normalize_assoc_gen: bool -> ac_inst_info -> conv
  val swap_assoc_to_l: int -> ac_inst_info -> conv
  val swap_assoc_to_r: int -> ac_inst_info -> conv
  val move_outmost: ac_inst_info -> term -> conv
  val normalize_unit: ac_inst_info -> conv
  val normalize_minus: ac_inst_info -> conv
  val normalize_comm_gen: ac_inst_info -> bool -> (term * term -> bool) -> conv
  val normalize_comm_l: ac_inst_info -> (term * term -> bool) -> conv
  val normalize_minus_assoc_gen: bool -> ac_inst_info -> conv
  val normalize_minus_assoc_l: ac_inst_info -> conv
  val normalize_minus_assoc_r: ac_inst_info -> conv
  val normalize_all_ac: ac_inst_info -> conv
  val ac_last_conv: ac_inst_info -> conv -> conv
end;

functor ACUtil(Base:UTIL_BASE) : ACUTIL =
struct

structure UtilLogic = UtilLogic(Base)
open Base
open UtilLogic

(* Instantiate an ac_info for a specific type T. *)
fun inst_ac_info thy T {assoc_th, comm_th, unitl_th, unitr_th,
                        uinv_uinv_th, uinv_head_th, uinv_unit_th, inv_th} =
    let
      (* Instantiate th to having argument of type T. If not possible,
         change th to true_th.
       *)
      fun inst_th th =
          if is_true_th th then true_th else
          let
            (* Extract the first argument of th, then the body type of
               that argument.
             *)
            val arg_type = th |> prop_of' |> dest_args |> hd
                              |> Term.type_of |> Term.body_type
          in
            if arg_type = T then th else
            let
              val tenv = typ_match thy (arg_type, T)
            in
              subst_thm_thy thy (tenv, Vartab.empty) th
            end
            handle Type.TYPE_MATCH => true_th
          end

      val assoc_th' = inst_th assoc_th
      val assoc_cv = if is_true_th assoc_th' then Conv.no_conv
                     else rewr_obj_eq assoc_th'
      val assoc_sym_cv = if is_true_th assoc_th' then Conv.no_conv
                         else rewr_obj_eq (obj_sym assoc_th')

      val comm_th' = inst_th comm_th
      val comm_cv = if is_true_th comm_th' then Conv.no_conv
                    else rewr_obj_eq comm_th

      val unitl_th' = inst_th unitl_th
      val unitr_th' = inst_th unitr_th
      val unit_ths = [unitl_th', unitr_th']
      val unit_cv = if is_true_th unitl_th' then Conv.no_conv
                    else Conv.first_conv (map rewr_obj_eq unit_ths)

      val uinv_uinv_th' = inst_th uinv_uinv_th
      val uinv_head_th' = inst_th uinv_head_th
      val uinv_unit_th' = inst_th uinv_unit_th
      val uinv_ths = [uinv_uinv_th', uinv_head_th', uinv_unit_th']

      val uinv_cv = if is_true_th uinv_uinv_th' then Conv.no_conv
                    else Conv.first_conv (map rewr_obj_eq uinv_ths)

      val inv_th' = inst_th inv_th
      val inv_cv = if is_true_th inv_th' then Conv.no_conv
                   else rewr_obj_eq inv_th'

      val fhead = if is_true_th assoc_th' then null_term
                  else assoc_th' |> prop_of' |> dest_arg |> dest_binop |> fst
      val cfhead = cert_thy thy fhead

      val unit_val = if is_true_th unitl_th' then null_term
                     else unitl_th' |> prop_of' |> dest_arg1 |> dest_arg1
      val uinv_op = if is_true_th uinv_uinv_th' then null_term
                    else uinv_uinv_th' |> prop_of' |> dest_arg1
                                       |> Term.dest_comb |> fst
      val inv_op = if is_true_th inv_th' then null_term
                   else inv_th' |> prop_of' |> dest_arg1 |> dest_binop |> fst
    in
      if is_true_th assoc_th' then NONE else
      SOME {cfhead = cfhead, assoc_cv = assoc_cv, assoc_sym_cv = assoc_sym_cv,
            comm_cv = comm_cv, unit_val = unit_val, unit_cv = unit_cv,
            uinv_op = uinv_op, uinv_cv = uinv_cv,
            inv_op = inv_op, inv_cv = inv_cv}
    end

fun is_binop t =
    case t of
        _ $ _ $ _ => true
      | _ => false

val (AC_NONE, AC_FHEAD, AC_UINV, AC_INV) = (0, 1, 2, 3)

(* Match (unary or binary) head of t with cfhead, uinv_op, or inv_op. *)
fun ac_analyze_head {cfhead, uinv_op, inv_op, ...} t =
    case t of
        f $ _ =>
        if f aconv uinv_op then AC_UINV
        else if not (is_binop t) then AC_NONE
        else let
          val (f, _) = dest_binop t
        in
          if f aconv Thm.term_of cfhead then AC_FHEAD
          else if f aconv inv_op then AC_INV
          else AC_NONE
        end
      | _ => AC_NONE

fun head_agrees ac_info t = (ac_analyze_head ac_info t = AC_FHEAD)
fun head_agrees_uinv ac_info t = (ac_analyze_head ac_info t = AC_UINV)
fun head_agrees_all ac_info t = (ac_analyze_head ac_info t <> AC_NONE)

fun get_head_ac_info ctxt t =
    if not (is_binop t) then NONE
    else let
      val (f, _) = dest_binop t
      val info_table = ACInstData.get ctxt
    in
      case Termtab.lookup info_table f of
          NONE => NONE
        | SOME ac_info =>
          if head_agrees ac_info t then SOME ac_info else NONE
    end

fun get_head_ac_info_all ctxt t =
    case t of
        f $ _ =>
        let
          val info_table = ACInstData.get ctxt
          val uinv_info = Termtab.lookup info_table f
        in
          if is_some uinv_info then uinv_info
          else if not (is_binop t) then NONE
          else let
            val (f2, _) = dest_binop t
          in
            Termtab.lookup info_table f2
          end
        end
      | _ => NONE

(* Constructors for ac_info. *)
fun constr_ac_info constr thy t =
    inst_ac_info thy (fastype_of t) constr

fun constr_ac_info_au {assoc_th, unitl_th, unitr_th} =
    constr_ac_info
        {assoc_th = assoc_th, comm_th = true_th,
         unitl_th = unitl_th, unitr_th = unitr_th,
         uinv_uinv_th = true_th, uinv_head_th = true_th,
         uinv_unit_th = true_th, inv_th = true_th}

fun constr_ac_info_acu {assoc_th, comm_th, unitl_th} =
    constr_ac_info
        {assoc_th = assoc_th, comm_th = comm_th,
         unitl_th = unitl_th,
         unitr_th = apply_to_thm' (Conv.arg1_conv (rewr_obj_eq comm_th))
                                  unitl_th,
         uinv_uinv_th = true_th, uinv_head_th = true_th,
         uinv_unit_th = true_th, inv_th = true_th}

(* a . (b . c) = b . (a . c) *)
fun swap_l_cv (ac_info as {assoc_cv, assoc_sym_cv, comm_cv, ...}) ct =
    if head_agrees ac_info (dest_arg (Thm.term_of ct)) then
      Conv.every_conv [assoc_sym_cv, Conv.arg1_conv comm_cv, assoc_cv] ct
    else
      comm_cv ct

(* (a . b) . c = (a . c) . b *)
fun swap_r_cv (ac_info as {assoc_cv, assoc_sym_cv, comm_cv, ...}) ct =
    if head_agrees ac_info (dest_arg1 (Thm.term_of ct)) then
      Conv.every_conv [assoc_cv, Conv.arg_conv comm_cv, assoc_sym_cv] ct
    else
      comm_cv ct

(* Add the given ac_info under the given name. *)
fun add_ac_data (nm, info) thy =
    ACData.map (Symtab.update_new (nm, info)) thy
    handle Symtab.DUP _ => raise AUTO2 "add_ac_data: info already exists."

(* Returns all the ac_inst_info instantiated from the given term. *)
fun inst_ac_infos thy t =
    let
      fun inst_info t info = the_list (info thy t)
    in
      (ACData.get thy) |> Symtab.dest |> map snd |> maps (inst_info t)
    end

fun add_ac_inst_info ac_data ctxt =
    let
      val {cfhead, uinv_op, inv_op, ...} = ac_data
      val fs = filter_out (fn t => t aconv null_term)
                          [Thm.term_of cfhead, uinv_op, inv_op]
      val updts = map (rpair ac_data) fs
    in
      ACInstData.map (fold Termtab.update updts) ctxt
    end

(* Add all ac_inst_info instantiated from t to the context. *)
fun add_inst_ac_infos t ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val inst_infos = inst_ac_infos thy t
    in
      fold add_ac_inst_info inst_infos ctxt
    end

(* Clear all AC infos. *)
val clear_ac_data = ACData.map (K Symtab.empty)

fun get_head_ac_info_thy_gen with_inv thy t =
    let
      fun filt ac_info = if with_inv then head_agrees_all ac_info t
                         else head_agrees ac_info t
      val infos = t |> inst_ac_infos thy |> filter filt
    in
      case infos of
          [] => NONE
        | [ac_info] => SOME ac_info
        | _ => raise AUTO2 "get_head_ac_info_thy"
    end

val get_head_ac_info_thy = get_head_ac_info_thy_gen false
val get_head_ac_info_all_thy = get_head_ac_info_thy_gen true

fun has_assoc_th {assoc_cv, ...} = not (pointer_eq (assoc_cv, Conv.no_conv))
fun has_comm_th {comm_cv, ...} = not (pointer_eq (comm_cv, Conv.no_conv))
fun has_unit_th {unit_cv, ...} = not (pointer_eq (unit_cv, Conv.no_conv))
fun has_inv_th {uinv_cv, ...} = not (pointer_eq (uinv_cv, Conv.no_conv))

(* Destruct t, assuming it is associated to the left. *)
fun dest_ac_l ac_info t =
    let
      fun dest t =
          if head_agrees ac_info t then
            let val (_, (a1, a2)) = dest_binop t in a2 :: dest a1 end
          else [t]
    in
      rev (dest t)
    end

(* Destruct t, assuming it is associated to the right. *)
fun dest_ac_r ac_info t =
    let
      fun dest t =
          if head_agrees ac_info t then
            let val (_, (a1, a2)) = dest_binop t in a1 :: dest a2 end
          else [t]
    in
      dest t
    end

(* Destructor for the given AC. This function preserves units. *)
fun dest_ac_gen assoc_r ac_info t =
    if assoc_r then dest_ac_r ac_info t else dest_ac_l ac_info t

(* Deconstruct for the given AC on both sides. *)
fun dest_ac_total ac_info t =
    let
      fun dest t =
          if head_agrees ac_info t then
            let val (_, (a1, a2)) = dest_binop t in dest a1 @ dest a2 end
          else [t]
    in
      dest t
    end

(* Construct f applied to ts, associated to the left. *)
fun list_ac_l {cfhead, unit_val, ...} ts =
    if ts = [] then unit_val
    else let
      fun append ts t =
          case ts of
              [] => t
            | t' :: ts' => append ts' (Thm.term_of cfhead $ t $ t')
    in
      append (tl ts) (hd ts)
    end

(* Construct f applied to ts, associated to the right. *)
fun list_ac_r {cfhead, unit_val, ...} ts =
    if ts = [] then unit_val
    else let
      fun append ts t =
          case ts of
              [] => t
            | t' :: ts' => append ts' (Thm.term_of cfhead $ t' $ t)
      val rev_ts = rev ts
    in
      append (tl rev_ts) (hd rev_ts)
    end

(* Constructor for the given AC. *)
fun list_ac_gen assoc_r ac_info ts =
    if assoc_r then list_ac_r ac_info ts else list_ac_l ac_info ts

(* Given ths: [A1 == B1, ..., An == Bn], get theorem A1...An ==
   B1...Bn. Associate to the left only.
 *)
fun comb_ac_equiv {cfhead, ...} ths =
    let
      fun binop_comb th1 th2 =
          Thm.combination (Thm.combination (Thm.reflexive cfhead) th1) th2

      (* Combine in the reverse order. *)
      fun comb ths =
          case ths of
              [] => raise AUTO2 "comb_ac_equiv: empty list"
            | [th] => th
            | [th1, th2] => binop_comb th2 th1
            | th :: ths' => binop_comb (comb ths') th
    in
      comb (rev ths)
    end

(* Normalize association with the given direction. *)
fun normalize_assoc_gen assoc_r ac_info ct =
    if not (has_assoc_th ac_info) then Conv.all_conv ct
    else let
      val assoc_cv = if assoc_r then #assoc_cv ac_info
                     else #assoc_sym_cv ac_info

      (* First rewrite into form a * (...) for assoc_r = true, or
         (...) * a for assoc_r = false, then rewrite the remaining
         parts.
       *)
      fun normalize ct =
          if head_agrees ac_info (Thm.term_of ct) then
            ((Conv.repeat_conv assoc_cv)
                 then_conv (if assoc_r then Conv.arg_conv normalize
                            else Conv.arg1_conv normalize)) ct
          else
            Conv.all_conv ct
    in
      normalize ct
    end

fun normalize_assoc_l ac_info ct = normalize_assoc_gen false ac_info ct
fun normalize_assoc_r ac_info ct = normalize_assoc_gen true ac_info ct

(* Swap ct with f associated to the right to f associated to the
   left. Consider ct as f applied to n terms (n-2 swaps are applied).
 *)
fun swap_assoc_to_l n ac_info ct =
    if n <= 2 then Conv.all_conv ct
    else repeat_n_conv (n-2) (#assoc_sym_cv ac_info) ct

(* Same as above, except swap from associating left to associating
   right.
 *)
fun swap_assoc_to_r n ac_info ct =
    if n <= 2 then Conv.all_conv ct
    else repeat_n_conv (n-2) (#assoc_cv ac_info) ct

(* Move the given u within ct to the rightmost position. Assume
   associate to the left.
 *)
fun move_outmost ac_info u ct =
    if not (has_assoc_th ac_info andalso has_comm_th ac_info) then
      raise AUTO2 "move_outmost: commutativity is not available."
    else if u aconv (Thm.term_of ct) then Conv.all_conv ct else
    if not (head_agrees ac_info (Thm.term_of ct)) then
      raise AUTO2 "move_outmost: u not found in ct."
    else let
      val (_, (a, b)) = dest_binop (Thm.term_of ct)
    in
      if u aconv b then Conv.all_conv ct
      else if head_agrees ac_info a then
        ((Conv.arg1_conv (move_outmost ac_info u))
             then_conv (swap_r_cv ac_info)) ct
      else if u aconv a then
        #comm_cv ac_info ct
      else
        raise AUTO2 "move_outmost: u not found in ct."
    end

(* In a product of a_1, a_2, ..., remove any a_i that is a unit. *)
fun normalize_unit ac_info ct =
    if not (has_unit_th ac_info) then Conv.all_conv ct
    else let
      fun normalize ct =
          if head_agrees ac_info (Thm.term_of ct) then
            ((Conv.binop_conv normalize)
                 then_conv (Conv.try_conv (#unit_cv ac_info))) ct
          else
            Conv.all_conv ct
    in
      normalize ct
    end

(* Replace a - b by a + (-b) throughout. *)
fun remove_minus ac_info ct =
    let
      fun normalize ct =
          let
            val head = ac_analyze_head ac_info (Thm.term_of ct)
          in
            if head = AC_FHEAD then
              Conv.binop_conv normalize ct
            else if head = AC_INV then
              ((#inv_cv ac_info)
                   then_conv (Conv.arg1_conv normalize)
                   then_conv (Conv.arg_conv (Conv.arg_conv normalize))) ct
            else if head = AC_UINV then
              Conv.arg_conv normalize ct
            else
              Conv.all_conv ct
          end
    in
      normalize ct
    end

(* Replace -(a + b) by -a + -b and -(-a) by a throughout. *)
fun normalize_uminus ac_info ct =
    let
      fun normalize ct =
          let
            val head = ac_analyze_head ac_info (Thm.term_of ct)
          in
            if head = AC_FHEAD then
              Conv.binop_conv normalize ct
            else if head = AC_INV then
              raise AUTO2 "normalize_uminus: should not encounter minus."
            else if head = AC_UINV then
              Conv.try_conv ((#uinv_cv ac_info) then_conv normalize) ct
            else
              Conv.all_conv ct
          end
    in
      normalize ct
    end

(* Normalize with respect to minus and uminus. *)
fun normalize_minus ac_info =
    if not (has_inv_th ac_info) then Conv.all_conv
    else (remove_minus ac_info) then_conv (normalize_uminus ac_info)

(* Rearrange subterms of ct according to the given term
   ordering. Returns theorem ct == ct'.
 *)
fun normalize_comm_gen ac_info assoc_r termless ct =
    if not (has_comm_th ac_info) then
      raise AUTO2 "normalize_comm: comm_th does not exist."
    else let
      (* If there are two terms a.b, swap if a > b. If there are at
         least three terms, in the left associate case this is
         (a.b).c, swap b and c if b > c. In the right associate case
         this is a.(b.c), swap a and b if a > b. If there is a swap,
         recursively call swap_last until the original outside term is
         swapped into position.
       *)
      fun swap_last ct =
          if head_agrees ac_info (Thm.term_of ct) then
            let
              val (_, (a1, a2)) = dest_binop (Thm.term_of ct)
            in
              if assoc_r andalso head_agrees ac_info a2 then
                (* Structure of t is a1 . a2 = a1 . (b1 . _). *)
                let
                  val (_, (b1, _)) = dest_binop a2
                in
                  if termless (b1, a1) then
                    ((swap_l_cv ac_info)
                         then_conv (Conv.arg_conv swap_last)) ct
                  else Conv.all_conv ct
                end
              else if not assoc_r andalso head_agrees ac_info a1 then
                (* Structure of t is a1 . a2 = (_ . b2) . a2. *)
                let
                  val (_, (_, b2)) = dest_binop a1
                in
                  if termless (a2, b2) then
                    ((swap_r_cv ac_info)
                         then_conv (Conv.arg1_conv swap_last)) ct
                  else Conv.all_conv ct
                end
              else
                (* Structure of t is a1 . a2. *)
                if termless (a2, a1) then #comm_cv ac_info ct
                else Conv.all_conv ct
            end
          else
            Conv.all_conv ct

      (* Full ordering. Recursively perform full ordering on all but
         the outermost, then swap outermost into position.
       *)
      fun normalize ct =
          if head_agrees ac_info (Thm.term_of ct) then
            ((if assoc_r then Conv.arg_conv normalize
              else Conv.arg1_conv normalize) then_conv swap_last) ct
          else
            Conv.all_conv ct
    in
      normalize ct
    end

fun normalize_comm_l ac_info = normalize_comm_gen ac_info false

(* Normalize all except comm. *)
fun normalize_minus_assoc_gen assoc_r ac_info =
    (normalize_minus ac_info)
        then_conv (normalize_unit ac_info)
        then_conv (normalize_assoc_gen assoc_r ac_info)

val normalize_minus_assoc_l = normalize_minus_assoc_gen false
val normalize_minus_assoc_r = normalize_minus_assoc_gen true

(* Normalize everything. *)
fun normalize_all_ac ac_info =
    (normalize_minus_assoc_l ac_info)
        then_conv (normalize_comm_l ac_info Term_Ord.termless)

(* Rewrite the last term in ct using cv. Assume associative to left. *)
fun ac_last_conv ac_info cv ct =
    if head_agrees ac_info (Thm.term_of ct) then
      Conv.arg_conv cv ct
    else cv ct

end  (* structure ACUtil. *)
