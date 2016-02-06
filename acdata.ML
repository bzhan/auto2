(* Dealing with associative-commutative operations. *)

(* Starting AC info for a function 'a -> 'a -> 'a. *)
type ac_info = {
  fname: string, assoc_r: bool, assoc_th: thm, comm_th: thm,
  unit_val: term, unit_th: thm, unitr_th: thm, uinv_name: string,
  inv_name: string, double_inv_th: thm, distr_inv_th: thm, binop_inv_th: thm,
  unit_inv_th: thm
}

(* Instantiated version of AC info. *)
type ac_inst_info = {
  cfhead: cterm, assoc_r: bool, assoc_th: thm, comm_th: thm, swap_conv: conv,
  unit_val: term, unit_th: thm, unitr_th: thm, unit_conv: conv, uinv_op: term,
  inv_op: term, double_inv_th: thm, distr_inv_th: thm, binop_inv_th: thm,
  unit_inv_th: thm}

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
Theory_Data (
  type T = ac_inst_info Termtab.table;
  val empty = Termtab.empty;
  val extend = I;
  val merge = Termtab.merge pointer_eq
)

signature ACUTIL =
sig
  val get_swap_cv: bool -> thm -> thm -> conv
  val get_unit_cv: thm -> thm -> thm -> conv
  val verify_assoc_th: string -> thm -> bool
  val verify_comm_th: string -> thm -> bool
  val verify_unit_th: string -> term * thm -> bool
  val add_ac_data: ac_info -> theory -> theory
  val lookup_ac_data: theory -> string -> ac_info option
  val clear_ac_data: theory -> theory
  val inst_ac_info: theory -> typ -> ac_info -> ac_inst_info

  val get_head_ac_info_gen: bool -> theory -> term -> ac_inst_info option
  val get_head_ac_info: theory -> term -> ac_inst_info option
  val get_head_ac_info_with_inv: theory -> term -> ac_inst_info option
  val head_agrees: ac_inst_info -> term -> bool
  val dest_ac: ac_inst_info -> term -> term list
  val list_ac: ac_inst_info -> term list -> term
  val comb_ac_equiv: ac_inst_info -> thm list -> thm
  val normalize_assoc: ac_inst_info -> conv
  val normalize_comm: ac_inst_info -> conv
  val move_outmost: ac_inst_info -> term -> conv
  val move_outmost2: ac_inst_info -> term * term -> conv
  val normalize_unit: ac_inst_info -> conv
  val normalize_cu: ac_inst_info -> conv
  val normalize_minus: ac_inst_info -> conv
  val normalize_all_ac: ac_inst_info -> conv

  val ac_subterms_conv: ac_inst_info -> conv -> conv
  val ac_subterms_conv_trav_uinv: ac_inst_info -> conv -> conv
  val normalize_assoc_full: theory -> conv
  val normalize_comm_full: theory -> conv
  val normalize_unit_full: theory -> conv
  val normalize_cu_full: theory -> conv
  val normalize_minus_full: theory -> conv
  val normalize_all_ac_full: theory -> conv

  val is_unit_allowed_var: term -> bool
  val match_multiset:
      theory -> ac_inst_info ->
      (id_inst -> term * term -> id_inst_th list) -> id_inst ->
      term list list -> term list * term list -> id_inst_ths list
  val match_seq:
      theory -> ac_inst_info ->
      (id_inst -> term * term -> id_inst_th list) -> id_inst ->
      term list list -> term list * term list -> id_inst_ths list
  val match_ac:
      theory -> ac_inst_info ->
      (id_inst -> term * term -> id_inst_th list) -> id_inst ->
      term * (term * term list list) -> id_inst_th list
end;

structure ACUtil : ACUTIL =
struct

(* Use comm_th and assoc_th to create the swapping conversion. *)
fun get_swap_cv assoc_r comm_th assoc_th =
    let
      val comm_cv = rewr_obj_eq comm_th
      val assoc_cv = rewr_obj_eq assoc_th
      val assoc_invcv = rewr_obj_eq (obj_sym assoc_th)
    in
      if assoc_r = false then
        (* (a . b) . c -> a . (b . c) -> a . (c . b) -> (a . c) . b. *)
        assoc_cv then_conv (Conv.arg_conv comm_cv) then_conv assoc_invcv
      else
        (* a . (b . c) -> (a . b) . c -> (b . a) . c -> b . (a . c). *)
        assoc_invcv then_conv (Conv.arg1_conv comm_cv) then_conv assoc_cv
    end

(* Use unit_th (1 . a = a) and either comm_th or unitr_th to create
   conversion simplifying both 1 . a and a . 1 to a.
 *)
fun get_unit_cv comm_th unit_th unitr_th =
    let
      val unit_cv = rewr_obj_eq unit_th
      val unitr_cv =
          if is_true_th unitr_th then (rewr_obj_eq comm_th) then_conv unit_cv
          else rewr_obj_eq unitr_th
    in
      unit_cv else_conv unitr_cv
    end

(* Verify assoc_th is in the form (a * b) * c = a * (b * c). *)
fun verify_assoc_th fname assoc_th =
    let
      val (lhs, rhs) = dest_eq_thm assoc_th
      val (f, (fab, c)) = dest_binop lhs
      val (f', (a, b)) = dest_binop fab
      val (nm, _) = dest_Const f
    in
      f aconv f' andalso nm = fname andalso is_Var a andalso is_Var b andalso
      is_Var c andalso rhs aconv (f $ a $ (f $ b $ c))
    end

(* Verify comm_th is in the form a . b = b . a. *)
fun verify_comm_th fname comm_th =
    let
      val (lhs, rhs) = dest_eq_thm comm_th
      val (f, (a, b)) = dest_binop lhs
      val (nm, _) = dest_Const f
    in
      nm = fname andalso is_Var a andalso is_Var b andalso rhs aconv (f $ b $ a)
    end

(* Verify unit_th is in the form 1 * a = 1. *)
fun verify_unit_th fname (unit_val, unit_th) =
    let
      val (lhs, rhs) = dest_eq_thm unit_th
      val (f, (u, a)) = dest_binop lhs
      val (nm, _) = dest_Const f
    in
      nm = fname andalso is_Var a andalso a aconv rhs andalso
      Term.aconv_untyped (u, unit_val)
    end

(* Verify unitr_th is in the form a * 1 = 1. *)
fun verify_unitr_th fname (unit_val, unitr_th) =
    let
      val (lhs, rhs) = dest_eq_thm unitr_th
      val (f, (a, u)) = dest_binop lhs
      val (nm, _) = dest_Const f
    in
      nm = fname andalso is_Var a andalso a aconv rhs andalso
      Term.aconv_untyped (u, unit_val)
    end

(* Verify double_inv_th is in the form inv (inv a) = a. *)
fun verify_double_inv_th (uinv_name, double_inv_th) =
    let
      val (lhs, rhs) = dest_eq_thm double_inv_th
      val (uinv1, (uinv2, a)) = lhs |> dest_comb |> apsnd dest_comb
      val (uinv_nm, _) = dest_Const uinv1
    in
      uinv_nm = uinv_name andalso uinv1 aconv uinv2 andalso a aconv rhs
    end

(* Verify distr_inv_th is in the form inv (a * b) = inv a * inv b. *)
fun verify_distr_inv_th fname (uinv_name, distr_inv_th) =
    let
      val (lhs, rhs) = dest_eq_thm distr_inv_th
      val (uinv, (f, (a, b))) = lhs |> dest_comb |> apsnd dest_binop
      val (uinv_nm, _) = dest_Const uinv
      val (nm, _) = dest_Const f
    in
      uinv_nm = uinv_name andalso nm = fname andalso
      rhs aconv (f $ (uinv $ a) $ (uinv $ b))
    end

(* Verify binop_inv_th is in the form a / b = a * (inv b) *)
fun verify_binop_inv_th fname (uinv_name, inv_name, binop_inv_th) =
    let
      val (lhs, rhs) = dest_eq_thm binop_inv_th
      val (inv, (a, b)) = dest_binop lhs
      val (inv_nm, _) = dest_Const inv
      val T = fastype_of lhs
      val f = Const (fname, T --> T --> T)
      val uinv = Const (uinv_name, T --> T)
    in
      inv_nm = inv_name andalso rhs aconv (f $ a $ (uinv $ b))
    end

(* Verify unit_inv_th is in the form inv 1 = 1. *)
fun verify_unit_inv_th (uinv_name, unit_val, unit_inv_th) =
    let
      val (lhs, rhs) = dest_eq_thm unit_inv_th
      val T = fastype_of lhs
      val uinv = Const (uinv_name, T --> T)
    in
      lhs = uinv $ rhs andalso Term.aconv_untyped (rhs, unit_val)
    end

(* Verify the theorems for the AC info of a function is in the right
   form.
 *)
fun add_ac_data (info as {fname, assoc_r, assoc_th, comm_th, unit_val, unit_th,
                          unitr_th, uinv_name, inv_name, double_inv_th,
                          distr_inv_th, binop_inv_th, unit_inv_th}) thy =
    if Symtab.defined (ACData.get thy) fname then
      raise AUTO2 ("add_ac_data: " ^ fname ^ " already defined.") else
    let
      val _ = assert (is_true_th assoc_th orelse verify_assoc_th fname assoc_th)
                     "add_ac_data: error in assoc_th"
      val _ = assert (is_true_th comm_th orelse verify_comm_th fname comm_th)
                     "add_ac_data: error in comm_th"
      val _ = assert (is_true_th unit_th orelse
                      verify_unit_th fname (unit_val, unit_th))
                     "add_ac_data: error in unit_th"
      val _ = assert (is_true_th unitr_th orelse
                      verify_unitr_th fname (unit_val, unitr_th))
                     "add_ac_data: error in unitr_th"
      val _ = assert (is_true_th double_inv_th orelse
                      verify_double_inv_th (uinv_name, double_inv_th))
                     "add_ac_data: error in double_inv_th"
      val _ = assert (is_true_th distr_inv_th orelse
                      verify_distr_inv_th fname (uinv_name, distr_inv_th))
                     "add_ac_data: error in distr_inv_th"
      val _ = assert (is_true_th binop_inv_th orelse
                      verify_binop_inv_th
                          fname (uinv_name, inv_name, binop_inv_th))
                     "add_ac_data: error in binop_inv_th"
      val _ = assert (is_true_th unit_inv_th orelse
                      verify_unit_inv_th (uinv_name, unit_val, unit_inv_th))
                     "add_ac_data: error in unit_inv_th"
      val _ = assert (is_true_th binop_inv_th orelse assoc_r = false)
                     "add_ac_data: ops with inverses must associate to left"
    in
      thy |> ACData.map (Symtab.update_new (fname, info))
          |> (if uinv_name = "" then I else
              ACData.map (Symtab.update_new (uinv_name, info)))
          |> (if inv_name = "" then I else
              ACData.map (Symtab.update_new (inv_name, info)))
    end

(* Returns the AC info for the given function name. *)
fun lookup_ac_data thy fnm = Symtab.lookup (ACData.get thy) fnm

(* Clear all AC infos. *)
val clear_ac_data =
    ACData.map (K Symtab.empty) #> ACInstData.map (K Termtab.empty)

(* Instantiate an ac_info for a specific type T. *)
fun inst_ac_info
        thy T {fname, assoc_r, assoc_th, comm_th, unit_val, unit_th, unitr_th,
               uinv_name, inv_name, double_inv_th, distr_inv_th, binop_inv_th,
               unit_inv_th} =
    let
      (* Instantiate th to having argument of type T. If not possible,
         change th to true_th.
       *)
      fun inst_th th =
          if is_true_th th then true_th else
          let
            val arg_type = th |> Thm.prop_of |> HOLogic.dest_Trueprop
                              |> get_arg_type
            val tenv = typ_match thy (arg_type, T)
          in
            subst_thm_thy thy (tenv, Vartab.empty) th
          end
          handle Type.TYPE_MATCH => true_th

      val cfhead = cert_thy thy (Const (fname, T --> T --> T))
      val assoc_th' = inst_th assoc_th
      val comm_th' = inst_th comm_th
      val unit_val' = if is_null_term unit_val then null_term else
                      case unit_val of Const (nm, _) => Const (nm, T)
                                     | _ => raise AUTO2 "inst_ac_info: unit_val"
      val unit_th' = inst_th unit_th
      val unitr_th' = inst_th unitr_th
      val swap_conv =
          if is_true_th assoc_th' orelse is_true_th comm_th' then Conv.all_conv
          else get_swap_cv assoc_r comm_th' assoc_th'

      val unit_conv =
          if is_true_th unit_th' orelse
             (is_true_th comm_th' andalso is_true_th unitr_th') then
            Conv.all_conv
          else
            get_unit_cv comm_th' unit_th' unitr_th'

      val uinv_op = Const (uinv_name, T --> T)
      val inv_op = Const (inv_name, T --> T --> T)
      val double_inv_th' = inst_th double_inv_th
      val distr_inv_th' = inst_th distr_inv_th
      val binop_inv_th' = inst_th binop_inv_th
      val unit_inv_th' = inst_th unit_inv_th
    in
      {cfhead = cfhead, assoc_r = assoc_r, assoc_th = assoc_th',
       comm_th = comm_th', swap_conv = swap_conv,
       unit_val = unit_val', unit_th = unit_th', unitr_th = unitr_th',
       unit_conv = unit_conv, uinv_op = uinv_op, inv_op = inv_op,
       double_inv_th = double_inv_th', distr_inv_th = distr_inv_th',
       binop_inv_th = binop_inv_th', unit_inv_th = unit_inv_th'}
    end

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
               val (ac_inst_info as {double_inv_th, ...}) =
                   inst_ac_info thy (Term.body_type (fastype_of t)) ac_info
             in
               if fnm = fname then SOME ac_inst_info
               else if with_inv andalso not (is_true_th double_inv_th) then
                 SOME ac_inst_info
               else NONE
             end)
      | _ => NONE

val get_head_ac_info = get_head_ac_info_gen false
val get_head_ac_info_with_inv = get_head_ac_info_gen true

fun head_agrees {cfhead, ...} t = (Term.head_of t aconv Thm.term_of cfhead)

(* Destructor for the given AC. This function preserves units. *)
fun dest_ac (ac_info as {assoc_r, ...}) t =
    let
      fun dest t =
          if head_agrees ac_info t then
            let
              val (_, (a1, a2)) = dest_binop t
            in
              if assoc_r then a1 :: dest a2 else a2 :: dest a1
            end
          else [t]
    in
      if assoc_r then dest t else rev (dest t)
    end

(* Constructor for the given AC. *)
fun list_ac {cfhead, assoc_r, unit_val, ...} ts =
    if ts = [] then unit_val else
    let
      val fhead = Thm.term_of cfhead
      fun append ts t =
          case ts of
              [] => t
            | t' :: ts' => if assoc_r then append ts' (fhead $ t' $ t)
                           else append ts' (fhead $ t $ t')
      val ts' = if assoc_r then rev ts else ts
    in
      append (tl ts') (hd ts')
    end

(* Given ths: [A1 == B1, ..., An == Bn], get theorem A1...An == B1...Bn. *)
fun comb_ac_equiv {cfhead, assoc_r, ...} ths =
    let
      fun binop_comb th1 th2 =
          Thm.combination (Thm.combination (Thm.reflexive cfhead) th1) th2

      (* Normal order of assoc_r, reverse order otherwise. *)
      fun comb ths =
          case ths of
              [] => raise AUTO2 "comb_ac_equiv: empty list"
            | [th] => th
            | [th1, th2] => if assoc_r then binop_comb th1 th2
                            else binop_comb th2 th1
            | th :: ths' => if assoc_r then binop_comb th (comb ths')
                            else binop_comb (comb ths') th
    in
      if assoc_r then comb ths else comb (rev ths)
    end

fun normalize_assoc (ac_info as {assoc_r, assoc_th, ...}) ct =
    if is_true_th assoc_th then Conv.all_conv ct
    else let
      val assoc_cv = if assoc_r then rewr_obj_eq assoc_th
                     else rewr_obj_eq (obj_sym assoc_th)

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

(* Rearrange subterms of ct according to term ordering. Returns
   theorem ct == ct'.
 *)
fun normalize_comm (ac_info as {assoc_r, comm_th, swap_conv, ...}) ct =
    if is_true_th comm_th orelse pointer_eq (swap_conv, Conv.all_conv)
    then Conv.all_conv ct
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
                  if Term_Ord.termless (b1, a1) then
                    (swap_conv then_conv (Conv.arg_conv swap_last)) ct
                  else Conv.all_conv ct
                end
              else if not assoc_r andalso head_agrees ac_info a1 then
                (* Structure of t is a1 . a2 = (_ . b2) . a2. *)
                let
                  val (_, (_, b2)) = dest_binop a1
                in
                  if Term_Ord.termless (a2, b2) then
                    (swap_conv then_conv (Conv.arg1_conv swap_last)) ct
                  else Conv.all_conv ct
                end
              else
                (* Structure of t is a1 . a2. *)
                if Term_Ord.termless (a2, a1) then (rewr_obj_eq comm_th) ct
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

      (* First check whether any rearrangement is necessary. *)
      val ac_subs = ct |> Thm.term_of |> dest_ac ac_info
    in
      if is_sorted Term_Ord.term_ord ac_subs then Conv.all_conv ct
      else normalize ct
    end

(* Move the given u within ct to the outmost position. If assoc_r =
   true, this means leftmost position. Otherwise, it means rightmost
   position.
 *)
fun move_outmost (ac_info as {assoc_r, comm_th, swap_conv, ...}) u ct =
    if is_true_th comm_th orelse pointer_eq (swap_conv, Conv.all_conv)
    then raise AUTO2 "move_outmost: commutativity is not available." else
    if u aconv (Thm.term_of ct) then Conv.all_conv ct else
    if not (head_agrees ac_info (Thm.term_of ct)) then
      raise AUTO2 "move_outmost: u not found in ct."
    else let
      val (_, (a, b)) = dest_binop (Thm.term_of ct)
    in
      if assoc_r then  (* Move to leftmost position *)
        if u aconv a then Conv.all_conv ct
        else if head_agrees ac_info b then
          ((Conv.arg_conv (move_outmost ac_info u)) then_conv swap_conv) ct
        else if u aconv b then
          rewr_obj_eq comm_th ct
        else
          raise AUTO2 "move_outmost: u not found in ct."
      else (* assoc_r = false. Move to rightmost position *)
        if u aconv b then Conv.all_conv ct
        else if head_agrees ac_info a then
          ((Conv.arg1_conv (move_outmost ac_info u)) then_conv swap_conv) ct
        else if u aconv a then
          rewr_obj_eq comm_th ct
        else
          raise AUTO2 "move_outmost: u not found in ct."
    end

(* Move u and v into the outmost position. The result should be (for
   assoc_r = false) a * (u * v) or (for assoc_r = true) (v * u) * a,
   where a may contain zero, one, or more terms. u and v may be equal,
   in which case there must be two such terms in ct.
 *)
fun move_outmost2 (ac_info as {assoc_r, assoc_th, ...}) (u, v) ct =
    let
      val length_ct = length (dest_ac ac_info (Thm.term_of ct))
      val assoc_cv = if length_ct > 2 then
                       if assoc_r = false then rewr_obj_eq assoc_th
                       else rewr_obj_eq (obj_sym assoc_th)
                     else Conv.all_conv
    in
      ((move_outmost ac_info v)
           then_conv (if assoc_r = false then
                        Conv.arg1_conv (move_outmost ac_info u)
                      else
                        Conv.arg_conv (move_outmost ac_info u))
           then_conv assoc_cv) ct
    end

(* In a product of a_1, a_2, ..., remove any a_i that is a unit. *)
fun normalize_unit (ac_info as {assoc_r, unit_val, unit_conv, ...}) ct =
    if pointer_eq (unit_conv, Conv.all_conv) then Conv.all_conv ct else
    let
      fun normalize ct =
          if head_agrees ac_info (Thm.term_of ct) then
            if assoc_r then
              ((Conv.arg_conv normalize) then_conv Conv.try_conv unit_conv) ct
            else
              ((Conv.arg1_conv normalize) then_conv Conv.try_conv unit_conv) ct
          else
            Conv.all_conv ct

      val ac_subs = ct |> Thm.term_of |> dest_ac ac_info
    in
      if member (op aconv) ac_subs unit_val then normalize ct
      else Conv.all_conv ct
    end

fun normalize_cu ac_info =
    normalize_unit ac_info then_conv normalize_comm ac_info

(* Replace a - b by a + (-b) throughout. *)
fun remove_minus {cfhead, uinv_op, inv_op, binop_inv_th, ...} ct =
    let
      fun normalize ct =
          let
            val f = Term.head_of (Thm.term_of ct)
          in
            if f aconv (Thm.term_of cfhead) then
              Conv.binop_conv normalize ct
            else if f aconv inv_op then
              ((rewr_obj_eq binop_inv_th)
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
fun normalize_uminus {cfhead, uinv_op, inv_op, double_inv_th, distr_inv_th,
                      unit_val, unit_inv_th, ...} ct =
    let
      val unit_inv_cv = if is_true_th unit_inv_th then Conv.all_conv
                        else rewr_obj_eq unit_inv_th
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
                  ((rewr_obj_eq distr_inv_th)
                       then_conv (Conv.binop_conv normalize)) ct
                else if f2 aconv inv_op then
                  raise AUTO2 "normalize_uminus: should not encounter minus."
                else if f2 aconv uinv_op then
                  ((rewr_obj_eq double_inv_th) then_conv normalize) ct
                else if f2 aconv unit_val then
                  unit_inv_cv ct
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
fun normalize_minus
        (ac_info as {double_inv_th, distr_inv_th, binop_inv_th, ...}) =
    if exists is_true_th [double_inv_th, distr_inv_th, binop_inv_th] then
      Conv.all_conv
    else
      (remove_minus ac_info) then_conv (normalize_uminus ac_info)

(* Perform all normalizations at top level. *)
fun normalize_all_ac ac_info =
    (normalize_minus ac_info) then_conv (normalize_assoc ac_info)
                              then_conv (normalize_cu ac_info)

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

(* Apply cv to subterms of ct. Used when fhead is non-AC. *)
fun subterms_conv cv ct =
    let
      val (cf, cargs) = Drule.strip_comb ct
    in
      comb_equiv (cf, map cv cargs)
    end

(* Recursively perform normalization using associative rules. *)
fun normalize_assoc_full thy ct =
    let
      fun normalize ct =
          case Thm.term_of ct of
              _ $ _ =>
              (case get_head_ac_info thy (Thm.term_of ct) of
                   NONE => subterms_conv normalize ct
                 | SOME ac_info =>
                   ((normalize_assoc ac_info)
                       then_conv (ac_subterms_conv ac_info normalize)) ct)
            | Abs _ => Conv.abs_conv (fn _ => normalize)
                                     (Proof_Context.init_global thy) ct
            | _ => Conv.all_conv ct
    in
      normalize ct
    end

(* Recursively perform normalization using commutative rules. *)
fun normalize_comm_full thy ct =
    let
      fun normalize ct =
          case Thm.term_of ct of
              _ $ _ =>
              (case get_head_ac_info thy (Thm.term_of ct) of
                   NONE => subterms_conv normalize ct
                 | SOME ac_info =>
                   ((ac_subterms_conv ac_info normalize)
                        then_conv (normalize_comm ac_info)) ct)
            | Abs _ => Conv.abs_conv (fn _ => normalize)
                                     (Proof_Context.init_global thy) ct
            | _ => Conv.all_conv ct
    in
      normalize ct
    end

(* Recursively perform normalization using unit rules. *)
fun normalize_unit_full thy ct =
    let
      fun normalize ct =
          case Thm.term_of ct of
              _ $ _ =>
              (case get_head_ac_info thy (Thm.term_of ct) of
                   NONE => subterms_conv normalize ct
                 | SOME ac_info =>
                   ((ac_subterms_conv ac_info normalize)
                        then_conv (normalize_unit ac_info)) ct)
            | Abs _ => Conv.abs_conv (fn _ => normalize)
                                     (Proof_Context.init_global thy) ct
            | _ => Conv.all_conv ct
    in
      normalize ct
    end

fun normalize_cu_full thy =
    normalize_unit_full thy then_conv normalize_comm_full thy

(* Recursively perform normalization using minus rules. *)
fun normalize_minus_full thy ct =
    let
      fun normalize ct =
          case Thm.term_of ct of
              _ $ _ =>
              (case get_head_ac_info_with_inv thy (Thm.term_of ct) of
                   NONE => subterms_conv normalize ct
                 | SOME ac_info =>
                   ((normalize_minus ac_info)
                        then_conv (ac_subterms_conv ac_info normalize)) ct)
            | Abs _ => Conv.abs_conv (fn _ => normalize)
                                     (Proof_Context.init_global thy) ct
            | _ => Conv.all_conv ct
    in
      normalize ct
    end

fun normalize_all_ac_full thy =
    (normalize_minus_full thy) then_conv (normalize_assoc_full thy)
                               then_conv (normalize_cu_full thy)

(* Check whether t is an uninstantiated schematic variable. *)
fun is_uninst_var inst t =
    case t of
        Var (ixn, _) => not (Vartab.defined inst ixn)
      | _ => false

(* Schematic variable allows matching with units if its name contains
   at least two characters, with the last character equal to u.
 *)
fun is_unit_allowed_var t =
    if not (Term.is_Var t) then false else
    let
      val ((nm, _), _) = Term.dest_Var t
      val nm_chars = raw_explode nm
    in
      length nm_chars >= 2 andalso List.last nm_chars = "u"
    end

(* Match two lists up to permutation. Return a list of ((id, env),
   ths) with the following property: ths are equalities from
   instantiated ts to a list us', such that after dest_ac the lists
   us' and us are permutations of each other.
 *)
fun match_multiset thy (ac_info as {unit_val, uinv_op, ...}) match_fn
                   (instsp as (_, (_, inst))) groups (ts, us) =
    if length ts = 0 then if length us = 0 then [(instsp, [])] else []
    else let
      val (t, ts') = (hd ts, tl ts)
      val range = 0 upto (length us - 1)

      (* Match with unit and consume no term in us. *)
      fun match_unit _ =
          let
            val inst_t = match_fn instsp (t, unit_val)
            fun process_inst_t (instsp', th) =
                map (apsnd (cons th))
                    (match_multiset thy ac_info match_fn instsp' groups
                                    (ts', us))
          in
            maps process_inst_t inst_t
          end

      (* Match with and consume exactly one term in us. *)
      fun match_i i =
          if i > 0 andalso (nth us (i-1)) aconv (nth us i) then [] else
          let
            val insts_t = match_fn instsp (t, nth us i)
            fun process_inst_t (instsp', th) =
                map (apsnd (cons th))
                    (match_multiset thy ac_info match_fn instsp' groups
                                    (ts', nth_drop i us))
          in
            maps process_inst_t insts_t
          end

      (* Match ts' first, then match t. Used when t is an
         uninstantiated schematic variable, and there are concrete
         terms left in ts'.
       *)
      fun swap_last _ =
          map (apsnd (split_last #> swap #> uncurry cons))
              (match_multiset thy ac_info match_fn instsp groups
                              (ts' @ [t], us))

      (* Match with a subset of us. Only for uninstantiated schematic
         variables. Currently restrict to non-empty subsets.
       *)
      fun match_subset is =
          if length is = 0 then [] else
          let
            val _ = assert (is_uninst_var inst t orelse
                            (Term.head_of t aconv uinv_op andalso
                             is_uninst_var inst (t |> Term.dest_comb |> snd)))
                           "match_subset: t should be uninstantiated."
            val cur_group = map (nth us) is
          in
            if exists (fn grp => submultiset (op aconv) (grp, cur_group))
                      groups then [] else
            let
              val fi = list_ac ac_info cur_group
              val insts_t = match_fn instsp (t, fi)
              fun process_inst_t (instsp', th) =
                  map (apsnd (cons th))
                      (match_multiset thy ac_info match_fn instsp' groups
                                      (ts', nth_drop_list is us))
            in
              maps process_inst_t insts_t
            end
          end
    in
      if Term.is_Var t then
        let
          val ((nm, i), _) = Term.dest_Var t
        in
          case Vartab.lookup inst (nm, i) of
              NONE =>
              if forall (is_uninst_var inst) ts' then
                (* The remaining ones are all uninstantiated
                   schematic variables.
                 *)
                if nm = "NUMC" orelse nm = "FREE" then
                  maps match_i range
                else if nm = "NUMCu" then
                  maps match_i range @ match_unit ()
                else if is_unit_allowed_var t then
                  maps match_subset (subsets range) @ match_unit ()
                else if length ts' = 0 then
                  match_subset range
                else
                  maps match_subset (subsets range)
              else
                swap_last ()
            | SOME (_, u') =>
              let
                val us' = dest_ac ac_info u'
                val len_us' = length us'
                val insts = match_multiset thy ac_info match_fn instsp groups
                                           (us' @ ts', us)
                fun process_inst (instsp', ths) =
                    let
                      val (th_us', th_rest) = chop len_us' ths
                      val th_u' = comb_ac_equiv ac_info th_us'
                    in
                      (instsp', th_u' :: th_rest)
                    end
              in
                map process_inst insts
              end
        end
      else if Term.head_of t aconv uinv_op andalso
              Term.is_Var (t |> Term.dest_comb |> snd) then
        let
          val ((nm, i), _) = Term.dest_Var (t |> Term.dest_comb |> snd)
        in
          case Vartab.lookup inst (nm, i) of
              NONE =>
              if forall (is_uninst_var inst) ts' then
                if length ts' = 0 then
                  match_subset range
                else if nm = "NUMC" orelse nm = "FREE" then
                  maps match_i range
                else
                  maps match_subset (subsets range)
              else
                swap_last ()
            | SOME _ =>  (* Need work *)
              maps match_i range
        end
      else
        (* If t is concrete, check whether t is equiv to unit. *)
        if t aconv unit_val then match_unit () else maps match_i range
    end

(* Match two lists, preserving permutation. Return a list of ((id,
   env), ths) with the following property: ths are equalities from
   instantiated ts to a list us', such that after dest_ac the lists
   us' and us are permutations of each other. Assume elements of ts
   are not units, so us must be at least as long as ts for there to be
   a match.
 *)
fun match_seq thy ac_info match_fn (instsp as (_, (_, inst))) groups (ts, us) =
    if length ts = 0 then if length us = 0 then [(instsp, [])] else []
    else if length ts > length us then []
    else let
      val (t, ts') = (hd ts, tl ts)

      (* Match with the head of us. *)
      fun match_next _ =
          if length us = 0 then []
          else let
            val insts_t = match_fn instsp (t, hd us)
            fun process_inst_t (instsp', th) =
                map (apsnd (cons th))
                    (match_seq thy ac_info match_fn instsp' groups (ts', tl us))
          in
            maps process_inst_t insts_t
          end

      (* Match with the next n terms in us. Only for uninstantiated
         schematic variables. Currently restrict to n > 0.
       *)
      fun match_next_n n =
          if n = 0 then [] else
          let
            val (cur_group, us') = chop n us
          in
            if length ts' > length us' then []
            else if exists (fn grp => submultiset (op aconv) (grp, cur_group))
                           groups then []
            else let
              val fi = list_ac ac_info cur_group
              val insts_t = match_fn instsp (t, fi)
              fun process_inst_t (instsp', th) =
                  map (apsnd (cons th))
                      (match_seq thy ac_info match_fn instsp' groups (ts', us'))
            in
              maps process_inst_t insts_t
            end
          end
    in
      if Term.is_Var t then
        let
          val ((nm, i), _) = Term.dest_Var t
        in
          case Vartab.lookup inst (nm, i) of
              NONE =>
              if length ts' = 0 then
                match_next_n (length us)
              else if nm = "NUMC" orelse nm = "FREE" then
                match_next ()
              else
                maps match_next_n (1 upto (length us))
            | SOME (_, u') =>
              let
                val us' = dest_ac ac_info u'
                val len_us' = length us'
                val insts = match_seq thy ac_info match_fn instsp groups
                                      (us' @ ts', us)
                fun process_inst (instsp', ths) =
                    let
                      val (th_us', th_rest) = chop len_us' ths
                      val th_u' = comb_ac_equiv ac_info th_us'
                    in
                      (instsp', th_u' :: th_rest)
                    end
              in
                map process_inst insts
              end
        end
      else
        maps match_next_n (1 upto (length us))
    end

(* Match an AC function *)
fun match_ac thy (ac_info as {comm_th, inv_op, uinv_op, binop_inv_th, ...})
             match_fn instsp (t, (u, groups)) =
    if Term.head_of t aconv inv_op then
      let
        val eq_t = rewr_obj_eq binop_inv_th (cert_thy thy t)
        val t' = rhs_of eq_t
        val instsps' = match_ac thy ac_info match_fn instsp (t', (u, groups))
        fun process_inst ((id', env'), th') =
            (* th': t'(env) == u *)
            let
              val inst_eq_t = subst_thm_thy thy env' eq_t
            in
              ((id', env'), transitive_list [inst_eq_t, th'])
            end
      in
        map process_inst instsps'
      end
    else if Term.head_of t aconv uinv_op then
      let
        val t' = t |> Term.dest_comb |> snd
        val uargs = dest_ac ac_info u
      in
        if not (exists (fn u' => Term.head_of u' aconv uinv_op) uargs) then []
        else let
          (* Let u' be the normalized version of -u, and eq_th be the
             equality between -u' and u.
           *)
          val u' = (uinv_op $ u) |> cert_thy thy
                                 |> normalize_all_ac ac_info |> rhs_of
          val eq_th = (uinv_op $ u') |> cert_thy thy |> normalize_all_ac ac_info
          val _ = assert (rhs_of eq_th aconv u) "match_ac: double neg not u."
          val instsps' = match_fn instsp (t', u')
          fun process_inst ((id', env'), th') =
              (* th': t'(env) == u', eq_th: -u' == u. Need t(env) == u *)
              let
                val op_eq = Thm.reflexive (cert_thy thy uinv_op)
                val th'' = Thm.combination op_eq th'  (* t(env) == -u' *)
              in
                ((id', env'), transitive_list [th'', eq_th])
              end
        in
          map process_inst instsps'
        end
      end
    else let
      val targs = dest_ac ac_info t
      val uargs = dest_ac ac_info u
      val instsps' =
          if is_true_th comm_th then
            match_seq thy ac_info match_fn instsp groups (targs, uargs)
          else
            match_multiset thy ac_info match_fn instsp groups (targs, uargs)

      fun process_inst (instsp', ths') =
          let
            val th' = ths' |> comb_ac_equiv ac_info
                           |> apply_to_rhs (normalize_assoc ac_info)
                           |> apply_to_rhs (normalize_cu ac_info)
            val _ = assert (rhs_of th' aconv u)
                           "match_ac_comb: u must be in normalized form."
          in
            (instsp', th')
          end
    in
      map process_inst instsps'
    end

end  (* structure ACUtil. *)
