(* Dealing with associative-commutative operations. *)

(* List of associative-commutative operations recognized by the
   rewriter.
 *)
type ac_item = {fhead: term, assoc_r: bool, unit_val: term,
                comm_thm: thm, assoc_thm: thm, unit_thm: thm, swap_conv: conv,
                unit_conv: conv}

structure ACData =
Theory_Data (
  type T = ac_item Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge pointer_eq
)

fun get_swap_cv assoc_r comm_th assoc_th =
    let
      val comm_cv = Conv.rewr_conv (to_meta_eq comm_th)
      val assoc_cv = Conv.rewr_conv (to_meta_eq assoc_th)
      val assoc_invcv = Conv.rewr_conv (to_meta_eq (obj_sym assoc_th))
    in      
      if assoc_r = false then
        (* (a . b) . c -> a . (b . c) -> a . (c . b) -> (a . c) . b. *)
        assoc_cv then_conv (Conv.arg_conv comm_cv) then_conv assoc_invcv
      else
        (* a . (b . c) -> (a . b) . c -> (b . a) . c -> b . (a . c). *)
        assoc_invcv then_conv (Conv.arg1_conv comm_cv) then_conv assoc_cv
    end

fun get_unit_cv comm_th unit_th =
    let
      val comm_cv = Conv.rewr_conv (to_meta_eq comm_th)
      val unit_cv = Conv.rewr_conv (to_meta_eq unit_th)
    in
      unit_cv else_conv (comm_cv then_conv unit_cv)
    end

fun add_ac_data {fname, assoc_r, unit_val, comm_th, assoc_th, unit_th} thy =
    if Symtab.defined (ACData.get thy) fname then
      raise AUTO2 ("add_ac_data: " ^ fname ^ " already defined.") else
    let
      (* comm_th is of the form a1 . b1 -> b1 . a1. *)
      val (comm_lhs, comm_rhs) = dest_eq_thm comm_th
      val (f, (a1, b1)) = dest_binop comm_lhs
      val (fnm, _) = dest_Const f
      val _ = assert (fnm = fname andalso is_Var a1 andalso is_Var b1
                      andalso comm_rhs aconv (f $ b1 $ a1))
                     "add_ac_data: error in comm_thm"

      (* assoc_th is of the form (a2 . b2) . c2 = a2 . (b2 . c2). *)
      val (assoc_lhs, assoc_rhs) = dest_eq_thm assoc_th
      val (f', (fab, c2)) = assoc_lhs |> dest_binop
      val (f'', (a2, b2)) = fab |> dest_binop
      val (fnm', _) = dest_Const f'
      val _ = assert (fnm' = fname andalso f' aconv f'' andalso is_Var a2
                      andalso is_Var b2 andalso is_Var c2
                      andalso assoc_rhs aconv (f' $ a2 $ (f' $ b2 $ c2)))
                     "add_ac_data: error in assoc_thm"

      (* unit_th is of the form 1 . a = a. *)
      val (unit_lhs, unit_rhs) = dest_eq_thm unit_th
      val (fu, (u, a)) = dest_binop unit_lhs
      val (fnm'', _) = dest_Const fu
      val _ = assert (fnm'' = fname andalso is_Var a andalso a aconv unit_rhs
                      andalso Term.aconv_untyped (u, unit_val))
                     "add_ac_data: error in unit_th"

      val ac_itm = {fhead = f, unit_val = unit_val, assoc_r = assoc_r,
                    comm_thm = comm_th, assoc_thm = assoc_th,
                    unit_thm = unit_th,
                    swap_conv = get_swap_cv assoc_r comm_th assoc_th,
                    unit_conv = get_unit_cv comm_th unit_th}
    in
      thy |> ACData.map (Symtab.update_new (fname, ac_itm))
    end

fun lookup_ac_data thy fnm =
    Symtab.lookup (ACData.get thy) fnm
val clear_ac_data = ACData.map (K Symtab.empty)

signature ACUTIL =
sig
  val inst_acdata_type: theory -> typ -> ac_item -> ac_item
  val get_head_ac_item: theory -> term -> ac_item option
  val get_typed_head_ac_item: theory -> term -> typ -> ac_item option
  val head_agrees: ac_item -> term -> bool
  val dest_ac: ac_item -> term -> term list
  val dest_ac_no_unit: ac_item -> term -> term list
  val list_ac: ac_item -> term list -> term
  val comb_ac_equiv: theory -> ac_item -> thm list -> thm
  val rearrange_fast: theory -> term -> term
  val rearrange_subterms: ac_item -> conv
  val rearrange_subterms_rhs: ac_item -> thm -> thm
  val rearrange_subterms_keep_unit: ac_item -> conv
  val rearrange_assoc: ac_item -> conv
  val rearrange_assoc_rhs: ac_item -> thm -> thm
  val ac_subterms_conv: ac_item -> conv -> conv
  val subterms_conv: conv -> conv
  val rearrange_ac: theory -> conv
  val rearrange_ac_thm: theory -> thm -> thm
  val rearrange_assoc_full: theory -> conv
end;

structure ACUtil : ACUTIL =
struct

(* Maps T --> T --> _ to T. *)
fun get_arg_type funT =
    case funT of Type("fun", [T, _]) => T | _ => raise AUTO2 "get_arg_type"

(* Maps Const (fnm, _) to fnm. *)
fun get_fname fhead =
    case fhead of Const (fnm, _) => fnm | _ => raise AUTO2 "get_fname"

fun inst_acdata_type
        thy T {fhead, assoc_r, unit_val, comm_thm, assoc_thm, unit_thm, ...} =
    let
      fun inst_th th =
          let
            val arg_type = th |> Thm.prop_of |> HOLogic.dest_Trueprop
                              |> get_head |> type_of |> get_arg_type
            val tenv = typ_match thy (arg_type, T)
          in
            subst_thm_thy thy (tenv, Vartab.empty) th
          end
      val fhead_tenv = typ_match thy (get_arg_type (type_of fhead), T)
      val fhead' = Envir.subst_term (fhead_tenv, Vartab.empty) fhead
      val comm_th' = inst_th comm_thm
      val assoc_th' = inst_th assoc_thm
      val unit_val' = case unit_val of
                          Const (nm, _) => Const (nm, T)
                        | _ => raise AUTO2 "inst_acdata_type: unit_val"
      val unit_th' = inst_th unit_thm
      val swap_cv' = get_swap_cv assoc_r comm_th' assoc_th'
      val unit_cv' = get_unit_cv comm_th' unit_th'
    in
      {fhead = fhead', assoc_r = assoc_r, unit_val = unit_val',
       comm_thm = comm_th', assoc_thm = assoc_th', unit_thm = unit_th',
       swap_conv = swap_cv', unit_conv = unit_cv'}
    end
    handle Type.TYPE_MATCH =>
           raise AUTO2 ("inst_acdata_type: type error " ^
                        "(T should not be schematic variable).")

fun get_head_ac_item thy t =
    case get_head t of
        Const (fnm, T) =>
        (case lookup_ac_data thy fnm of
             NONE => NONE
           | SOME ac_itm => SOME (inst_acdata_type thy (get_arg_type T) ac_itm))
      | _ => NONE


fun get_typed_head_ac_item thy t T =
    case get_head t of
        Const (fnm, _) =>
        (case lookup_ac_data thy fnm of
             NONE => NONE
           | SOME ac_itm => SOME (inst_acdata_type thy T ac_itm)
                            handle AUTO2 _ => NONE)
      | _ => NONE

fun head_agrees {fhead, ...} t =
    case get_head t of
        Const (fnm, _) => fnm = get_fname fhead
      | _ => false

fun dest_ac (ac_itm as {assoc_r, ...}) t =
    let
      fun dest t =
          if head_agrees ac_itm t then
            let val (_, (a1, a2)) = dest_binop t
            in if assoc_r then a1 :: dest a2 else a2 :: dest a1 end
          else [t]
    in
      if assoc_r then dest t else rev (dest t)
    end

fun dest_ac_no_unit (ac_itm as {unit_val, ...}) t =
    dest_ac ac_itm t |> filter_out (fn t' => t' aconv unit_val)

fun list_ac {fhead, assoc_r, unit_val, ...} ts =
    if ts = [] then unit_val else
    let
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
fun comb_ac_equiv thy {fhead, assoc_r, ...} ths =
    let
      fun binop_comb f th1 th2 =
          Thm.combination (Thm.combination (Thm.reflexive f) th1) th2
      val cf = cert_thy thy fhead
      (* Normal order of assoc_r, reverse order otherwise. *)
      fun comb ths =
          case ths of
              [] => raise AUTO2 "comb_ac_equiv: empty list"
            | [th] => th
            | [th1, th2] => if assoc_r then binop_comb cf th1 th2
                            else binop_comb cf th2 th1
            | th :: ths' => if assoc_r then binop_comb cf th (comb ths')
                            else binop_comb cf (comb ths') th
    in
      if assoc_r then comb ths else comb (rev ths)
    end

(* Simple version of rearrange. Simply produces the result (no theorem). *)
fun rearrange_fast thy t =
    case get_head_ac_item thy t of
        NONE => t
      | SOME ac_itm => t |> dest_ac_no_unit ac_itm
                         |> sort Term_Ord.term_ord
                         |> list_ac ac_itm

(* Rearrange subterms of ct according to term ordering. Returns
   theorem ct == ct'.
 *)
fun rearrange_subterms_gen
        keep_unit (ac_itm as {assoc_r, comm_thm, swap_conv, unit_val,
                              unit_conv, ...}) ct =
    let
      val comm_cv = Conv.rewr_conv (to_meta_eq comm_thm)

      (* If there are two terms a.b, swap if a > b. If there are at
         least three terms, in the left associate case this is
         (a.b).c, swap b and c if b > c. In the right associate case
         this is a.(b.c), swap a and b if a > b. If last two items is
         already in order, return trivial equality. If keep_unit is
         false, reduce 1.a and a.1 to a whenever it appears.
       *)
      fun swap_last2 ct =
          let
            val t = Thm.term_of ct
          in
            if head_agrees ac_itm t then
              let
                val (_, (a1, a2)) = dest_binop t
              in
                if assoc_r andalso head_agrees ac_itm a2 then
                  (* Structure of t is a1 . a2 = a1 . (b1 . _). *)
                  let val (_, (b1, _)) = dest_binop a2
                  in if Term_Ord.termless (b1, a1) then swap_conv ct
                     else Conv.no_conv ct end
                else if not assoc_r andalso head_agrees ac_itm a1 then
                  (* Structure of t is a1 . a2 = (_ . b2) . a2. *)
                  let val (_, (_, b2)) = dest_binop a1
                  in if Term_Ord.termless (a2, b2) then swap_conv ct
                     else Conv.no_conv ct end
                else
                  (* Structure of t is a1 . a2. *)
                  if Term_Ord.termless (a2, a1) then comm_cv ct
                  else Conv.no_conv ct
              end
            else
              Conv.no_conv ct
          end

      (* Swap the outermost item in ct into position. Assume all but
         the outermost item is arranged in order. If either the
         outermost or the remaining items is unit, reduce trivially.
       *)
      fun swap_last ct =
          let
            val swap_last' =
                swap_last2 then_conv (if assoc_r then Conv.arg_conv swap_last
                                      else Conv.arg1_conv swap_last)
          in
            if keep_unit then
              Conv.try_conv swap_last' ct
            else
              Conv.try_conv (unit_conv else_conv swap_last') ct
          end

      (* Full ordering. Recursively perform full ordering on all but
         the outermost, then swap outermost into position.
       *)
      fun rearrange ct =
          if head_agrees ac_itm (Thm.term_of ct) then
            ((if assoc_r then Conv.arg_conv rearrange
              else Conv.arg1_conv rearrange) then_conv swap_last) ct
          else
            Conv.all_conv ct

      val ac_subs = ct |> Thm.term_of |> dest_ac ac_itm
    in
      if is_sorted Term_Ord.term_ord ac_subs
         andalso (keep_unit orelse not (member (op aconv) ac_subs unit_val))
      then Conv.all_conv ct
      else rearrange ct
    end

val rearrange_subterms_keep_unit = rearrange_subterms_gen true
val rearrange_subterms = rearrange_subterms_gen false
fun rearrange_subterms_rhs ac_itm = apply_to_rhs (rearrange_subterms ac_itm)

fun rearrange_assoc (ac_itm as {assoc_r, assoc_thm, ...}) ct =
    let
      val rewr_cv =
          if assoc_r then Conv.rewr_conv (to_meta_eq assoc_thm)
          else Conv.rewr_conv (to_meta_eq (obj_sym assoc_thm))
      val arg_conv = if assoc_r then Conv.arg_conv else Conv.arg1_conv
    in
      if head_agrees ac_itm (Thm.term_of ct) then
        ((Conv.repeat_conv rewr_cv)
             then_conv (arg_conv (rearrange_assoc ac_itm))) ct
      else
        Conv.all_conv ct
    end
fun rearrange_assoc_rhs ac_itm = apply_to_rhs (rearrange_assoc ac_itm)

(* Apply cv to "subterms" of ct for an AC fhead. *)
fun ac_subterms_conv (ac_itm as {assoc_r, ...}) cv ct =
    if head_agrees ac_itm (Thm.term_of ct) then
      if assoc_r then
        ((Conv.arg_conv (ac_subterms_conv ac_itm cv))
             then_conv (Conv.arg1_conv cv)) ct
      else
        ((Conv.arg1_conv (ac_subterms_conv ac_itm cv))
             then_conv (Conv.arg_conv cv)) ct
    else
      cv ct

(* Apply cv to subterms of ct. Used when fhead is non-AC. *)
fun subterms_conv cv ct =
    let
      val (cfhead, cargs) = Drule.strip_comb ct
    in
      comb_equiv (cfhead, map cv cargs)
    end

(* Rearrange the arguments of all AC functions. Returns theorem ct ==
   ct' where ct' is the rearranged version.
 *)
fun rearrange_ac thy ct =
    let
      fun rearrange ct =
          case Thm.term_of ct of
              _ $ _ =>
              (case get_head_ac_item thy (Thm.term_of ct) of
                   NONE => subterms_conv rearrange ct
                 | SOME ac_itm =>
                   ((ac_subterms_conv ac_itm rearrange)
                        then_conv (rearrange_subterms ac_itm)) ct)
            | Abs _ => Conv.abs_conv (fn _ => rearrange)
                                     (Proof_Context.init_global thy) ct
            | _ => Conv.all_conv ct
    in
      rearrange ct
    end

fun rearrange_ac_thm thy th = apply_to_thm (rearrange_ac thy) th

fun rearrange_assoc_full thy ct =
    let
      fun rearrange ct =
          case Thm.term_of ct of
              _ $ _ =>
              (case get_head_ac_item thy (Thm.term_of ct) of
                   NONE => subterms_conv rearrange ct
                 | SOME ac_itm =>
                   ((rearrange_assoc ac_itm)
                        then_conv (ac_subterms_conv ac_itm rearrange)) ct)
            | Abs _ => Conv.abs_conv (fn _ => rearrange)
                                     (Proof_Context.init_global thy) ct
            | _ => Conv.all_conv ct
    in
      rearrange ct
    end

end  (* structure ACUtil. *)

(* Definitions of common ac data. *)
fun add_logic_ac_data thy =
    thy |> add_ac_data {fname = @{const_name disj}, assoc_r = true,
                        unit_val = @{term False}, comm_th = @{thm disj_commute},
                        assoc_th = @{thm disj_assoc},
                        unit_th = @{thm disj_false_neutral}}
        |> add_ac_data {fname = @{const_name conj}, assoc_r = true,
                        unit_val = @{term True}, comm_th = @{thm conj_commute},
                        assoc_th = @{thm conj_assoc},
                        unit_th = @{thm conj_true_neutral}}

fun add_arith_ac_data thy =
    thy |> add_ac_data {fname = @{const_name plus}, assoc_r = false,
                        unit_val = @{term 0}, comm_th = @{thm add_ac(2)},
                        assoc_th = @{thm add_ac(1)},
                        unit_th = @{thm Groups.monoid_add_class.add_0_left}}
        |> add_ac_data {fname = @{const_name times}, assoc_r = false,
                        unit_val = @{term 1}, comm_th = @{thm mult_ac(2)},
                        assoc_th = @{thm mult_ac(1)},
                        unit_th = @{thm Groups.monoid_mult_class.mult_1_left}}
        |> add_ac_data {fname = @{const_name gcd}, assoc_r = false,
                        unit_val = @{term "0::nat"},
                        comm_th = @{thm gcd_nat.commute},
                        assoc_th = @{thm gcd_nat.assoc},
                        unit_th = @{thm GCD.gcd_nat.left_neutral}}
