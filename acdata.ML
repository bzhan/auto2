(* Dealing with associative-commutative operations. *)

(* Starting AC info for a function 'a -> 'a -> 'a. *)
type ac_info = {fname: string, assoc_th: thm, comm_th: thm, unit_th: thm,
                uinv_th: thm, inv_th: thm}

(* Instantiated version of AC info. *)
type ac_inst_info = {
  cfhead: cterm, assoc_th: thm, comm_th: thm, unit_val: term, unit_th: thm,
  uinv_op: term, inv_op: term, uinv_th: thm, inv_th: thm}

(* Register of starting infos. *)
structure ACData =
Theory_Data (
  type T = ac_info Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge pointer_eq
)

(* Register of instantiated infos. *)
structure ACInstData =
Proof_Data (
  type T = ac_inst_info Termtab.table;
  fun init _ = Termtab.empty;
)

signature ACUTIL =
sig
  val head_agrees: ac_inst_info -> term -> bool
  val head_agrees_with_inv: ac_inst_info -> term -> bool
  val assoc_cv: ac_inst_info -> conv
  val assoc_sym_cv: ac_inst_info -> conv
  val comm_cv: ac_inst_info -> conv
  val swap_l_cv: ac_inst_info -> conv
  val swap_r_cv: ac_inst_info -> conv
  val unit_cv: ac_inst_info -> conv
  val double_inv_cv: ac_inst_info -> conv
  val distrib_inv_cv: ac_inst_info -> conv
  val unit_inv_cv: ac_inst_info -> conv
  val binop_inv_cv: ac_inst_info -> conv

  val add_ac_data: ac_info -> theory -> theory
  val lookup_ac_data: theory -> string -> ac_info option
  val clear_ac_data: theory -> theory
  val inst_ac_info: theory -> typ -> ac_info -> ac_inst_info option
  val has_assoc_th: ac_inst_info -> bool
  val has_comm_th: ac_inst_info -> bool
  val has_unit_th: ac_inst_info -> bool
  val has_inv_th: ac_inst_info -> bool

  val get_head_ac_info: theory -> term -> ac_inst_info option
  val get_head_ac_info_with_inv: theory -> term -> ac_inst_info option
  val get_head_ac_info_gen: bool -> theory -> term -> ac_inst_info option
  val get_head_ac_info_ctxt: Proof.context -> term -> ac_inst_info option
  val get_head_ac_info_ctxt_with_inv:
      Proof.context -> term -> ac_inst_info option
  val get_head_ac_info_ctxt_gen:
      bool -> Proof.context -> term -> ac_inst_info option
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
  val move_outmost2: ac_inst_info -> term * term -> conv
  val normalize_unit: ac_inst_info -> conv
  val normalize_minus: ac_inst_info -> conv
  val ac_subterms_conv: ac_inst_info -> conv -> conv
  val ac_subterms_conv_trav_uinv: ac_inst_info -> conv -> conv
end;

structure ACUtil : ACUTIL =
struct

fun head_agrees {cfhead, ...} t = (Term.head_of t aconv Thm.term_of cfhead)

(* Test whether the head of t is either the fhead or one of the
   inverse operations. In the case of uinv, the argument must be a
   binary operation agreeing with ac_info.
 *)
fun head_agrees_with_inv {cfhead, uinv_op, inv_op, ...} t =
    let
      val is_binary_fhead = member (op aconv) [Thm.term_of cfhead, inv_op]
      val (fhead, args) = Term.strip_comb t
    in
      is_binary_fhead fhead orelse
      (fhead aconv uinv_op andalso
       is_binary_fhead (Term.head_of (the_single args)))
    end

fun assoc_cv {assoc_th, ...} =
    rewr_obj_eq (assoc_th RS @{thm is_assocD})

fun assoc_sym_cv {assoc_th, ...} =
    rewr_obj_eq (obj_sym (assoc_th RS @{thm is_assocD}))

fun comm_cv {comm_th, ...} =
    rewr_obj_eq (comm_th RS @{thm is_commD})

(* Swap the leftmost two terms, assuming associative to the
   right. Also assume ct contains at least two terms.
 *)
fun swap_l_cv (ac_data as {assoc_th, comm_th, ...}) ct =
    let
      val (_, (_, B)) = dest_binop (Thm.term_of ct)
    in
      if head_agrees ac_data B then
        rewr_obj_eq ([assoc_th, comm_th] MRS @{thm ac_swap_l}) ct
      else comm_cv ac_data ct
    end

(* Swap the rightmost two terms, assuming associative to the
   left. Also assume ct contains at least two terms.
 *)
fun swap_r_cv (ac_data as {assoc_th, comm_th, ...}) ct =
    let
      val (_, (A, _)) = dest_binop (Thm.term_of ct)
    in
      if head_agrees ac_data A then
        rewr_obj_eq ([assoc_th, comm_th] MRS @{thm ac_swap_r}) ct
      else comm_cv ac_data ct
    end

(* Reduce 1 . a or a . 1 to a. *)
fun unit_cv {unit_val, unit_th, ...} ct =
    let
      val (_, (A, B)) = dest_binop (Thm.term_of ct)
    in
      if A aconv unit_val then
        rewr_obj_eq (unit_th RS @{thm is_unitD_l}) ct
      else if B aconv unit_val then
        rewr_obj_eq (unit_th RS @{thm is_unitD_r}) ct
      else Conv.no_conv ct
    end

fun double_inv_cv {uinv_th, ...} =
    rewr_obj_eq (uinv_th RS @{thm is_uinvD_double_inv})

fun distrib_inv_cv {uinv_th, ...} =
    rewr_obj_eq (uinv_th RS @{thm is_uinvD_distrib_inv})

fun unit_inv_cv {uinv_th, ...} =
    rewr_obj_eq (uinv_th RS @{thm is_uinvD_unit_inv})

fun binop_inv_cv {inv_th, ...} =
    rewr_obj_eq (inv_th RS @{thm is_invD})

(* Figure out the names of constants info should be added under
   (fname, uinv_name, and inv_name).
 *)
fun add_ac_data (info as {fname, uinv_th, inv_th, ...}) thy =
    if Symtab.defined (ACData.get thy) fname then
      raise AUTO2 ("add_ac_data: " ^ fname ^ " already defined.") else
    let
      val thy' = thy |> ACData.map (Symtab.update_new (fname, info))
    in
      if is_true_th uinv_th orelse is_true_th inv_th then thy'
      else let
        val inv_args = prop_of' inv_th |> strip_comb |> snd
        val uinv_name =
            case Term.head_of (nth inv_args 1) of
                Const (nm, _) => nm
              | _ => raise AUTO2 "add_ac_data: cannot extract uinv_name."
        val inv_name =
            case Term.head_of (nth inv_args 2) of
                Const (nm, _) => nm
              | _ => raise AUTO2 "add_ac_data: cannot extract inv_name."
      in
        thy' |> ACData.map (Symtab.update_new (uinv_name, info))
             |> ACData.map (Symtab.update_new (inv_name, info))
      end
    end

(* Returns the AC info for the given function name. *)
fun lookup_ac_data thy fnm = Symtab.lookup (ACData.get thy) fnm

(* Clear all AC infos. *)
val clear_ac_data = ACData.map (K Symtab.empty)

(* Instantiate an ac_info for a specific type T. *)
fun inst_ac_info thy T {fname, assoc_th, comm_th, unit_th, uinv_th, inv_th} =
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
            val arg_type = th |> prop_of' |> strip_comb |> snd |> hd
                              |> Term.type_of |> Term.body_type
            val tenv = typ_match thy (arg_type, T)
          in
            subst_thm_thy thy (tenv, Vartab.empty) th
          end
          handle Type.TYPE_MATCH => true_th

      val cfhead = cert_thy thy (Const (fname, T --> T --> T))
      val assoc_th' = inst_th assoc_th
      val comm_th' = inst_th comm_th
      val unit_th' = inst_th unit_th
      val unit_val = if is_true_th unit_th' then null_term
                     else unit_th' |> prop_of' |> strip_comb |> snd |> hd
      val uinv_th' = inst_th uinv_th
      val inv_th' = inst_th inv_th
      val (uinv_op, inv_op) =
          if is_true_th uinv_th' orelse is_true_th inv_th' then
            (null_term, null_term)
          else let
            val args = inv_th' |> prop_of' |> strip_comb |> snd
          in
            (nth args 1, nth args 2)
          end
    in
      if is_true_th assoc_th' then NONE else
      SOME {cfhead = cfhead, assoc_th = assoc_th', comm_th = comm_th',
            unit_val = unit_val, unit_th = unit_th', uinv_op = uinv_op,
            inv_op = inv_op, uinv_th = uinv_th', inv_th = inv_th'}
    end
    handle TYPE _ => NONE

fun has_assoc_th {assoc_th, ...} = not (is_true_th assoc_th)
fun has_comm_th {comm_th, ...} = not (is_true_th comm_th)
fun has_unit_th {unit_th, ...} = not (is_true_th unit_th)
fun has_inv_th {uinv_th, inv_th, ...} =
    not (is_true_th uinv_th orelse is_true_th inv_th)

(* Returns the instantiated AC info for the head of the given term,
   with argument type given by T.
 *)
fun get_head_ac_info_gen with_inv thy t =
    case Term.head_of t of
        Const (fnm, _) =>
        (case lookup_ac_data thy fnm of
             NONE => NONE
           | SOME (ac_info as {fname, ...}) =>
             let
               val ac_inst_info =
                   inst_ac_info thy (Term.body_type (fastype_of t)) ac_info
             in
               if is_none ac_inst_info then NONE
               else if (fnm = fname) orelse
                       (with_inv andalso has_inv_th (the ac_inst_info))
               then ac_inst_info else NONE
             end)
      | _ => NONE

val get_head_ac_info = get_head_ac_info_gen false
val get_head_ac_info_with_inv = get_head_ac_info_gen true

fun get_head_ac_info_ctxt_gen with_inv ctxt t =
    let
      val f = Term.head_of t
      val inst_tbl = ACInstData.get ctxt
    in
      case Termtab.lookup inst_tbl f of
          NONE => NONE
        | SOME (ac_info as {cfhead, ...}) =>
          if f aconv Thm.term_of cfhead orelse
             (with_inv andalso has_inv_th ac_info)
          then SOME ac_info else NONE
    end

val get_head_ac_info_ctxt = get_head_ac_info_ctxt_gen false
val get_head_ac_info_ctxt_with_inv = get_head_ac_info_ctxt_gen true

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
      val assoc_cv = if assoc_r then assoc_cv ac_info
                     else assoc_sym_cv ac_info

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
    else repeat_n_conv (n-2) (assoc_sym_cv ac_info) ct

(* Same as above, except swap from associating left to associating
   right.
 *)
fun swap_assoc_to_r n ac_info ct =
    if n <= 2 then Conv.all_conv ct
    else repeat_n_conv (n-2) (assoc_cv ac_info) ct

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
        comm_cv ac_info ct
      else
        raise AUTO2 "move_outmost: u not found in ct."
    end

(* Move u and v into the outmost position. The result should be (for
   associating to the left) a * (u * v), where a may contain zero,
   one, or more terms. u and v may be equal, in which case there must
   be two such terms in ct.
 *)
fun move_outmost2 ac_info (u, v) ct =
    let
      val length_ct = length (dest_ac_l ac_info (Thm.term_of ct))
      val assoc_cv = if length_ct > 2 then assoc_cv ac_info
                     else Conv.all_conv
    in
      ((move_outmost ac_info v)
           then_conv (Conv.arg1_conv (move_outmost ac_info u))
           then_conv assoc_cv) ct
    end

(* In a product of a_1, a_2, ..., remove any a_i that is a unit. *)
fun normalize_unit ac_info ct =
    if not (has_unit_th ac_info) then Conv.all_conv ct
    else let
      fun normalize ct =
          if head_agrees ac_info (Thm.term_of ct) then
            ((Conv.binop_conv normalize)
                 then_conv (Conv.try_conv (unit_cv ac_info))) ct
          else
            Conv.all_conv ct
    in
      normalize ct
    end

(* Replace a - b by a + (-b) throughout. *)
fun remove_minus (ac_info as {cfhead, uinv_op, inv_op, ...}) ct =
    let
      fun normalize ct =
          let
            val f = Term.head_of (Thm.term_of ct)
          in
            if f aconv (Thm.term_of cfhead) then
              Conv.binop_conv normalize ct
            else if f aconv inv_op then
              ((binop_inv_cv ac_info)
                   then_conv (Conv.arg1_conv normalize)
                   then_conv (Conv.arg_conv (Conv.arg_conv normalize))) ct
            else if f aconv uinv_op then
              Conv.arg_conv normalize ct
            else
              Conv.all_conv ct
          end
    in
      normalize ct
    end

(* Replace -(a + b) by -a + -b and -(-a) by a throughout. *)
fun normalize_uminus (ac_info as {cfhead, uinv_op, inv_op, unit_val, ...}) ct =
    let
      fun normalize ct =
          let
            val (f, args) = Term.strip_comb (Thm.term_of ct)
          in
            if f aconv (Thm.term_of cfhead) then
              Conv.binop_conv normalize ct
            else if f aconv inv_op then
              raise AUTO2 "normalize_uminus: should not encounter minus."
            else if f aconv uinv_op then
              let
                val f2 = args |> the_single |> Term.head_of
              in
                if f2 aconv (Thm.term_of cfhead) then
                  ((distrib_inv_cv ac_info)
                       then_conv (Conv.binop_conv normalize)) ct
                else if f2 aconv inv_op then
                  raise AUTO2 "normalize_uminus: should not encounter minus."
                else if f2 aconv uinv_op then
                  ((double_inv_cv ac_info) then_conv normalize) ct
                else if f2 aconv unit_val then
                  unit_inv_cv ac_info ct
                else
                  Conv.all_conv ct
              end
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

(* Apply cv to "subterms" of ct for an AC fhead. *)
fun ac_subterms_conv_gen trav_uinv (ac_info as {uinv_op, ...}) cv ct =
    if Term.head_of (Thm.term_of ct) aconv uinv_op then
      Conv.arg_conv cv ct
    else let
      fun helper ct =
          if trav_uinv andalso Term.head_of (Thm.term_of ct) aconv uinv_op then
            Conv.arg_conv helper ct
          else if head_agrees ac_info (Thm.term_of ct) then
            ((Conv.arg_conv helper) then_conv (Conv.arg1_conv helper)) ct
          else
            cv ct
    in
      helper ct
    end

val ac_subterms_conv = ac_subterms_conv_gen false
val ac_subterms_conv_trav_uinv = ac_subterms_conv_gen true

end  (* structure ACUtil. *)
