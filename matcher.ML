(* Matching up to equivalence (E-matching) using a rewrite table. *)

signature MATCHER =
sig
  (* Internal *)
  val is_unit_allowed_var: term -> bool
  val check_type_term:
      rewrite_table -> term * term -> id_inst -> (id_inst * term) option
  val check_type: rewrite_table -> typ * typ -> id_inst -> id_inst option
  val update_inst: term list -> indexname -> cterm -> id_inst -> id_inst_th list
  val id_eq_better: rewrite_table -> box_id * 'a -> box_id * 'a -> bool
  val inst_eq_better: rewrite_table -> (string * int) list -> id_inst_th ->
                      id_inst_th -> bool

  val ac_shift_n_to_r_cv: ac_inst_info -> int -> conv
  val ac_shift_inside_r: ac_inst_info -> int -> conv
  val ac_shift_r_to_n_cv: ac_inst_info -> int -> conv
  val ac_shift_l_to_n_cv: ac_inst_info -> int -> conv
  val ac_group_last_n_cv: ac_inst_info -> int -> conv
  val ac_group_first_n_cv: ac_inst_info -> int -> conv
  val is_uinv: ac_inst_info -> term -> bool
  val dest_uinv: term -> term
  val cdest_uinv: cterm -> cterm
  val mk_uinv_eq: ac_inst_info -> thm -> thm
  val is_multiple_term_head: term -> bool
  val is_sch_arg: ac_inst_info -> term -> bool
  val dest_sch_arg: term -> term

  val get_ac_head_equiv': rewrite_table -> ac_inst_info -> box_id * cterm ->
                          (box_id * thm) list
  val get_ac_head_equiv: rewrite_table -> ac_inst_info -> box_id * cterm ->
                         (box_id * thm) list
  val check_use_ac: ac_inst_info -> term list -> bool * int option
  val reduce_unit_t: rewrite_table -> ac_inst_info -> box_id * term ->
                     (box_id * thm) list
  val is_match_unit: ac_inst_info -> term -> bool
  val analyze_match_unit:
      ac_inst_info -> Proof.context -> Type.tyenv * Envir.tenv ->
      box_id * term -> (int * id_inst * thm) list
  val analyze_t: ac_inst_info -> rewrite_table -> id_inst -> term ->
                 (int * id_inst * thm) list
  val ac_subterm_equivs: rewrite_table -> ac_inst_info -> box_id * cterm ->
                         (box_id * thm) list

  (* THe actual matching function. These are defined together. *)
  val match_uinv: bool -> rewrite_table -> term list -> ac_inst_info ->
                  term * cterm list -> id_inst -> id_inst_th list
  val match_ac_list:
      bool -> bool -> rewrite_table -> term list -> ac_inst_info ->
      term list * cterm list -> id_inst -> id_inst_th list
  val match_ac_raw: bool -> ac_inst_info -> rewrite_table -> term list ->
                    term * cterm -> id_inst -> id_inst_th list
  val match_list: rewrite_table -> term list -> term list * cterm list ->
                  id_inst -> id_inst_ths list
  val match_comb: rewrite_table -> term list -> term * cterm -> id_inst ->
                  id_inst_th list
  val match_non_ac_head: rewrite_table -> term list -> term * cterm ->
                         id_inst -> id_inst_th list
  val match_ac_head: ac_inst_info -> rewrite_table -> term list ->
                     term * cterm -> id_inst -> id_inst_th list
  val match_non_ac_all_head_with_t:
      rewrite_table -> term list -> term * cterm -> id_inst -> id_inst_th list
  val match_ac_all_head_with_t:
      ac_inst_info -> rewrite_table -> term list -> term * cterm -> id_inst ->
      id_inst_th list
  val match_all_head: rewrite_table -> term list -> term * cterm -> id_inst ->
                      id_inst_th list
  val match: rewrite_table -> term list -> term * cterm -> id_inst ->
             id_inst_th list

  (* Defined in terms of match. *)
  val match_head: rewrite_table -> term list -> term * cterm -> id_inst ->
                  id_inst_th list
  val rewrite_match: rewrite_table -> term * cterm -> id_inst -> id_inst_th list
  val rewrite_match_head:
      rewrite_table -> term * cterm -> id_inst -> id_inst_th list
  val rewrite_match_ac_bd: bool -> ac_inst_info -> rewrite_table -> term list ->
                           term * cterm -> id_inst -> id_inst_th list
  val rewrite_match_ac: bool -> ac_inst_info -> rewrite_table -> term * cterm ->
                        id_inst -> id_inst_th list
  val rewrite_match_list: rewrite_table -> (bool * (term * cterm)) list ->
                          id_inst -> id_inst_ths list
  val rewrite_match_subset:
      rewrite_table -> term list * cterm list -> id_inst -> id_inst_ths list

  (* Prematching. *)
  val pre_match_type: rewrite_table -> typ * typ -> bool
  val pre_match_comb: rewrite_table -> term * cterm -> bool
  val pre_match_non_ac_head: rewrite_table -> term * cterm -> bool
  val pre_match_unit: ac_inst_info -> rewrite_table -> term * cterm -> bool
  val pre_match_all_head: rewrite_table -> term * cterm -> bool
  val pre_match: rewrite_table -> term * cterm -> bool
  val pre_match_head: rewrite_table -> term * cterm -> bool

  (* Heuristics for determine order of matching patterns. *)
  val literal_ac_count: theory -> term -> term list -> int
  val literal_ac_count_list: theory -> term list -> term list -> int
  val get_pattern_order: theory -> term * term -> bool
end;

functor Matcher(Base:UTIL_BASE) : MATCHER =
struct

structure UtilLogic = UtilLogic(Base)
structure ACUtil = ACUtil(Base)
structure Consts = Consts(Base)
structure RewriteTable = RewriteTable(Base)
open Base
open UtilLogic

fun compare_inst (((id1, inst1), _), ((id2, inst2), _)) =
    eq_list (op =) (id1, id2) andalso eq_env (inst1, inst2)

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

(* Match type at the top level for t and u. If there is no match,
   return NONE. Otherwise, return the updated instsp as well as t
   instantiated with the new type.
 *)
fun check_type_term tbl (t, u) (id, (tyinst, inst)) =
    let
      val (T, U) = (fastype_of t, fastype_of u)
      val thy = RewriteTable.theory_of tbl
    in
      if T = U then SOME ((id, (tyinst, inst)), t) else
      let
        val tyinst' = Sign.typ_match thy (T, U) tyinst
        val t' = Envir.subst_term_types tyinst' t
      in
        SOME ((id, (tyinst', inst)), t')
      end
    end
    handle Type.TYPE_MATCH => NONE

(* Match two types. *)
fun check_type tbl (T, U) (id, (tyinst, inst)) =
    let
      val thy = RewriteTable.theory_of tbl
      val tyinst' = if T = U then tyinst
                    else Sign.typ_match thy (T, U) tyinst
    in
      SOME (id, (tyinst', inst))
    end
    handle Type.TYPE_MATCH => NONE

(* Starting here, bd_vars is the list of free variables substituted
   for bound variables, when matching goes inside abstractions.
 *)
fun is_open bd_vars u =
    case bd_vars of
        [] => false
      | _ =>
        length (inter (op aconv) bd_vars (map Free (Term.add_frees u []))) > 0

(* Assign schematic variable with indexname ixn to u. Type of the
   schematic variable is determined by the type of u.
 *)
fun update_inst bd_vars ixn cu (id, inst) =
    let
      val u = Thm.term_of cu
    in
      if is_open bd_vars u then []
      else [((id, update_env (ixn, u) inst), Thm.reflexive cu)]
    end

(* Partial comparison using just the ID. *)
fun id_eq_better {lat, ...} (id, _) (id', _) = BoxID.is_eq_ancestor lat id id'

(* Whether the second instantiation is extraneous compared to the
   first. Currently use a fast version where instantiated terms are
   compared using aconv.
 *)
fun inst_eq_better {lat, ...} vars ((id, inst), _) ((id', inst'), _) =
    BoxID.is_eq_ancestor lat id id' andalso
    forall (fn var => lookup_instn inst var aconv lookup_instn inst' var) vars

(* Assume ct is associated to the left. Move k'th term, counting from
   the right and starting at 0, to the right-most position. That is, k
   moves to the right are performed.
 *)
fun ac_shift_n_to_r_cv ac_info k ct =
    if k <= 0 then
      Conv.all_conv ct
    else if ACUtil.head_agrees ac_info (Thm.term_of ct) then
      ((Conv.arg1_conv (ac_shift_n_to_r_cv ac_info (k-1)))
           then_conv (ACUtil.swap_r_cv ac_info)) ct
    else raise AUTO2 "ac_shift_n_to_r: unexpected input."

(* Shift the last (right-most) term inside k times. Assume ct is
   associated to the left.
 *)
fun ac_shift_inside_r ac_info k ct =
    if k <= 0 then
      Conv.all_conv ct
    else if ACUtil.head_agrees ac_info (Thm.term_of ct) then
      ((ACUtil.swap_r_cv ac_info)
           then_conv (Conv.arg1_conv (ac_shift_inside_r ac_info (k-1)))) ct
    else raise AUTO2 "ac_shift_inside_r: unexpected input."

(* Given ct of form v1 ... vk, associated to the left, move vk inward
   so that it is at position n, counting from the left starting at
   0. Since it is originally at position k-1, the number of moves
   required is k-1-n.
 *)
fun ac_shift_r_to_n_cv ac_info n ct =
    let
      val k = length (ACUtil.dest_ac_l ac_info (Thm.term_of ct))
    in
      ac_shift_inside_r ac_info (k-1-n) ct
    end

(* Shift the first (left-most) term inside k times. Assume ct is
   associated to the right. This is equivalent to moving the first
   term to position k.
 *)
fun ac_shift_l_to_n_cv ac_info k ct =
    if k <= 0 then
      Conv.all_conv ct
    else if ACUtil.head_agrees ac_info (Thm.term_of ct) then
      ((ACUtil.swap_l_cv ac_info)
           then_conv (Conv.arg_conv (ac_shift_l_to_n_cv ac_info (k-1)))) ct
    else raise AUTO2 "ac_shift_l_to_n: unexpected input."

(* Given ct of form v1 ... vk, associated to the left, use
   associativity to group the last n terms together.
 *)
fun ac_group_last_n_cv ac_info n ct =
    let
      val k = length (ACUtil.dest_ac_l ac_info (Thm.term_of ct))
      val assoc_cv = #assoc_cv ac_info
      fun helper n ct =
          if n <= 1 then Conv.all_conv ct
          else (Conv.arg1_conv (helper (n-1)) then_conv assoc_cv) ct
    in
      if k = n then Conv.all_conv ct
      else helper n ct
    end

(* Given ct of form v1 ... vk, associated to the right, use
   associativity to group the first n terms together.
 *)
fun ac_group_first_n_cv ac_info n ct =
    let
      val k = length (ACUtil.dest_ac_r ac_info (Thm.term_of ct))
      val assoc_sym_cv = #assoc_sym_cv ac_info
      fun helper n ct =
          if n <= 1 then Conv.all_conv ct
          else
            ((Conv.arg_conv (helper (n-1))) then_conv assoc_sym_cv) ct
    in
      if k = n then Conv.all_conv ct
      else helper n ct
    end

fun is_uinv {uinv_op, ...} t =
    Term.head_of t aconv (Thm.term_of uinv_op)

fun dest_uinv t =
    dest_arg t handle AUTO2 _ => raise AUTO2 "dest_uinv"

fun cdest_uinv ct =
    Thm.dest_arg ct handle CTERM _ => raise AUTO2 "cdest_uinv"

(* From a == b, make -a == -b. *)
fun mk_uinv_eq {uinv_op, ...} eq_th =
    Thm.combination (Thm.reflexive uinv_op) eq_th

fun is_multiple_term_head t =
    if not (Term.is_Var t) then false else
    let
      val ((nm, _), _) = Term.dest_Var t
      val nm_chars = raw_explode nm
    in
      length nm_chars >= 2 andalso List.last nm_chars = "l"
    end

fun is_sch_arg ac_info t =
    Term.is_Var t orelse
    (Term.is_Var (head_of t) andalso is_multiple_term_head (head_of t)) orelse
    (is_uinv ac_info t andalso Term.is_Var (dest_uinv t))

(* Given ?a or -?a, return -a. *)
fun dest_sch_arg t =
    if Term.is_Var (Term.head_of t) then t else dest_uinv t

(* Obtain list of head equivs of u whose head function belongs to the
   given AC info.
 *)
fun get_ac_head_equiv' tbl {cfhead, uinv_op, inv_op, ...} (id, cu) =
    maps (RewriteTable.get_head_equiv_with_t tbl (id, cu))
         (map Thm.term_of [cfhead, uinv_op, inv_op])

fun get_ac_head_equiv (tbl as {lat, ...}) ac_info (id, cu) =
    let
      fun equiv_eq_better (id1, th1) (id2, th2) =
          BoxID.is_eq_ancestor lat id1 id2 andalso rhs_of th1 aconv rhs_of th2

      val inv_equivs =
          if is_uinv ac_info (Thm.term_of cu) then
            map (apsnd (mk_uinv_eq ac_info))
                (get_ac_head_equiv tbl ac_info (id, cdest_uinv cu))
          else []
    in
      (inv_equivs @ get_ac_head_equiv' tbl ac_info (id, cu))
          |> max_partial equiv_eq_better
    end

(* Analyze targ and decide whether to use AC matching. Use AC matching
   under the following condition: there is at most one schematic
   argument among targ, and the corresponding schematic variable does
   not appear in other terms of targ. A schematic argument is either
   Var or -Var. If there is no commutativity, there is a further
   restriction that the schematic argument must come either first or
   last in targ.

   The return value is either:

   - (true, NONE): use AC, no schematic arguments.

   - (true, SOME i): use AC, schematic argument at position i.

   - (false, NONE): do not use AC (more than one schematic argument,
     or the sole schematic argument appears elsewhere.
 *)
fun check_use_ac ac_info targ =
    if length targ = 1 then
      (* Either of form -a, or not AC at all. *)
      (false, NONE)
    else let
      val assoc_only = not (ACUtil.has_comm_th ac_info)
      val sch_is = filter (fn i => is_sch_arg ac_info (nth targ i))
                          (0 upto (length targ - 1))
    in
      if length sch_is = 0 then
        (true, NONE)
      else if length sch_is = 1 then
        let
          val sch_i = the_single sch_is
        in
          if assoc_only then
            if sch_i = 0 orelse sch_i = length targ - 1 then
              (true, SOME sch_i)
            else (false, NONE)
          else (true, SOME sch_i)
        end
      else (false, NONE)
    end

(* Find all possible ids where there are (different) reductions of t
   by eliminating units. Return the list of ids and reductions. In
   this function, we assume that t is normalized at least with respect
   to inverses.
 *)
fun reduce_unit_t (tbl as {lat, ctxt, ...})
                  (ac_info as {cfhead, unit_val, ...}) (id, t) =
    if member (op aconv) [conj, disj]
              (Thm.term_of cfhead) then [(id, Thm.reflexive (cert ctxt t))]
    else if not (ACUtil.head_agrees ac_info t) then
      let
        val equivs = RewriteTable.equiv_info tbl id (cert ctxt t, unit_val)
      in
        if exists (fn (id', _) => id' = id) equivs then equivs
        else (id, Thm.reflexive (cert ctxt t)) :: equivs
      end
    else
      let
        val (A, B) = dest_binop_args t
        val A_equiv = reduce_unit_t tbl ac_info (id, A)
        val B_equiv = reduce_unit_t tbl ac_info (id, B)
        val equivs = BoxID.get_all_merges_info lat [A_equiv, B_equiv]
        fun process_equiv (id, th_pair) =
            (id, (ACUtil.comb_ac_equiv ac_info th_pair)
                     |> apply_to_rhs (Conv.try_conv (#unit_cv ac_info)))
      in
        map process_equiv equivs
      end

fun is_match_unit (ac_info as {unit_val, ...}) t =
    if not (ACUtil.head_agrees ac_info t) then false
    else let
      val (A, B) = dest_binop_args t
    in
      is_unit_allowed_var A orelse is_unit_allowed_var B orelse
      A aconv (Thm.term_of unit_val) orelse B aconv (Thm.term_of unit_val)
    end

val (AC_YES, AC_NO, AC_UNKNOWN) = (0, 1, 2)

fun analyze_match_unit (ac_info as {unit_val, ...}) ctxt env (id, t) =
    if not (ACUtil.head_agrees ac_info t) then []
    else let
      val (A, B) = dest_binop_args t
      fun process_var var =
          if is_unit_allowed_var var then
            let
              val (ixn, _) = Term.dest_Var var
              val env' = update_env (ixn, Thm.term_of unit_val) env
              val eq = t |> subst_term_norm env'
                         |> cert ctxt |> #unit_cv ac_info
            in
              if ACUtil.head_agrees_all ac_info (rhs_of eq) then
                [(AC_YES, (id, env'), eq)]
              else
                [(AC_UNKNOWN, (id, env'), eq)]
            end
          else []
    in
      maps process_var [A, B]
    end

(* Overall function for analyzing a pattern for AC matching. The
   functions performed are:

   - Substitute any instantiations in env into t.

   - Determine whether AC matching should be used, according to
     check_use_ac.

   - If there is commutativity, move the only pure schematic argument
     to the right.

   - TODO: when there are higher order patterns, make sure the
     arguments are in valid order.
 *)
fun analyze_t ac_info (tbl as {ctxt, ...}) (id, env) t =
    let
      val t' = subst_term_norm env t
      val ct' = cert ctxt t'
      val eq1 = ct' |> ACUtil.normalize_minus_assoc_l ac_info
      val eqs2 = reduce_unit_t tbl ac_info (id, rhs_of eq1)
      val assoc_only = not (ACUtil.has_comm_th ac_info)
      fun process_eq2 (id', eq2) =
          let
            val ct'' = Thm.rhs_of eq2
            val args = ACUtil.dest_ac_l ac_info (Thm.term_of ct'')
          in
            if length args = 1 then
              if is_uinv ac_info (the_single args) then
                (AC_NO, (id', env), transitive_list [eq1, eq2])
              else
                (AC_UNKNOWN, (id', env), transitive_list [eq1, eq2])
            else
              case check_use_ac ac_info args of
                  (true, NONE) =>
                  (AC_YES, (id', env), transitive_list [eq1, eq2])
                | (true, SOME k) =>
                  if assoc_only then
                    (AC_YES, (id', env), transitive_list [eq1, eq2])
                  else let
                    val k' = (length args) - k - 1
                    val eq3 = ac_shift_n_to_r_cv ac_info k' ct''
                  in
                    (AC_YES, (id', env), transitive_list [eq1, eq2, eq3])
                  end
                | (false, _) => (AC_NO, (id', env), Thm.reflexive ct')
          end
    in
      analyze_match_unit ac_info ctxt env (id, t') @ map process_eq2 eqs2
    end

(* Return the list of equivs of u by taking equivs of subterms. This
   always includes (id, u == u).
 *)
fun ac_subterm_equivs tbl ac_info (id, cu) =
    let
      val {lat, ...} = tbl
      val {cfhead, uinv_op, inv_op, ...} = ac_info
      val (cf, cargs) = Drule.strip_comb cu
      val f = Thm.term_of cf

      fun valid_rewrite (_, th) =
          not (ACUtil.head_agrees_all ac_info (rhs_of th))

      (* Return the list of non-AC equivalent terms for t. *)
      fun get_head_non_AC_equivs t =
          if ACUtil.head_agrees_all ac_info t then
            (RewriteTable.get_all_equiv tbl t)
                |> filter valid_rewrite
                |> RewriteTable.merge_box_with_info tbl id
                |> max_partial (id_eq_better tbl)
            handle AUTO2 "all_equiv: not found" => []
          else []

      (* Return the complete list of rewrites for t. *)
      fun get_equivs ct =
          get_head_non_AC_equivs (Thm.term_of ct) @
          ac_subterm_equivs tbl ac_info (id, ct)
    in
      if f aconv (Thm.term_of cfhead) orelse f aconv (Thm.term_of inv_op) then
        let
          val equiv_pairs = all_pairs (apply2 get_equivs (the_pair cargs))
          fun get_equiv ((id1, th1), (id2, th2)) =
              (BoxID.merge_boxes lat (id1, id2),
               Thm.combination (Thm.combination (Thm.reflexive cf) th1) th2)
        in
          map get_equiv equiv_pairs
        end
      else if f aconv (Thm.term_of uinv_op) then
        let
          val equivs = get_equivs (the_single cargs)
          fun get_equiv (id1, th1) =
              (id1, Thm.combination (Thm.reflexive uinv_op) th1)
        in
          map get_equiv equivs
        end
      else
        [(id, Thm.reflexive cu)]
    end

(* t is of the form -?A. Assign ?A to normalized form of -us. In the
   returned equality -?A(inst) == f(us). The order of associativity in
   f(us) is specified by assoc_r.
 *)
fun match_uinv assoc_r tbl bd_vars ac_info (t, cus) (id, env) =
    let
      (* Here t is -?A, inv_us = -f(us), inv_us' is the simplified
         version which will be assigned to ?A. inv_us_norm_eq is
         inv_us == inv_us'.
       *)
      val {uinv_op, ...} = ac_info
      val inv_cus = Drule.list_comb (
            uinv_op, [ACUtil.clist_ac_gen assoc_r ac_info cus])
      val inv_us_norm_eq = ACUtil.normalize_minus ac_info inv_cus
      val inv_cus' = Thm.rhs_of inv_us_norm_eq
      val insts = match tbl bd_vars (dest_uinv t, inv_cus') (id, env)

      (* eq_th: ?A == inv_us'. Need -?A == f(us). Use the chain

         -?A == -inv_us' == -inv_us (or -(-f(us)) == f(us).
       *)
      fun process_inst ((id', env'), eq_th) =
          ((id', env'),
           (transitive_list [eq_th, meta_sym inv_us_norm_eq])
               |> mk_uinv_eq ac_info
               |> apply_to_rhs (#uinv_cv ac_info))
    in
      map process_inst insts
    end

(* Given AC info for a function f, perform AC matching between f
   applied to ts (or rev ts) and f applied to us.

   If assoc_r = true, the returned equality is f(ts)(inst) == f(us).
   f is associated to the right on both sides.

   If assoc_r = false, the returned equality is f(rev ts)(inst) ==
   f(us). f is associated to the left on both sides.

   In both cases, ts is matched starting from head, and the head is
   outermost on the t-side in the returned result.
 *)
and match_ac_list is_simple assoc_r tbl bd_vars
                  (ac_info as {unit_val, ...}) (ts, cus) (id, env) =
    if length ts = 0 orelse length cus = 0 then []
    else if length ts = 1 then
      let
        val t = the_single ts
      in
        if Term.is_Var (head_of t) then
          if not (is_unit_allowed_var t) andalso
             exists (fn cu => RewriteTable.is_equiv id tbl (unit_val, cu)) cus
          then []
          else match tbl bd_vars
                     (t, ACUtil.clist_ac_gen assoc_r ac_info cus) (id, env)
        else if is_uinv ac_info t andalso Term.is_Var (dest_uinv t) then
          match_uinv assoc_r tbl bd_vars ac_info (t, cus) (id, env)
        else if length cus = 1 then
          match tbl bd_vars (t, the_single cus) (id, env)
        else []
      end
    else if not (is_sch_arg ac_info (List.last ts)) andalso
            length ts < length cus then []
    else let
      val diff_l = length ts - length cus
      val (t, ts') = (hd ts, tl ts)
      val assoc_only = not (ACUtil.has_comm_th ac_info)

      (* Filter and normalize expansion. *)
      fun process_expansion (id, th) =
          if not (ACUtil.head_agrees_all ac_info (rhs_of th)) then []
          else let
            val th' = th |> apply_to_rhs (
                  ACUtil.normalize_minus_assoc_gen assoc_r ac_info)
            val args = ACUtil.cdest_ac_gen assoc_r ac_info (Thm.rhs_of th')
          in
            if exists (fn ct =>
                          RewriteTable.is_equiv id tbl (ct, unit_val)) args
            then [] else [(id, th')]
          end

      (* Given i between 0 and length us - 1, return the list of (i,
         (id', eq1)), where eq1 is an expansion of us[i] under
         id'. The trivial expansion (i, (id, us[i] == us[i])) is
         always included in the list.
       *)
      fun expand_i i =
          if assoc_r andalso
             exists (fn ct => RewriteTable.is_equiv id tbl (ct, nth cus i))
                    (take i cus)
          then [] else
          if not assoc_r andalso
             exists (fn ct => RewriteTable.is_equiv id tbl (ct, nth cus i))
                    (drop (i+1) cus)
          then []
          else if is_simple then
            [(i, (id, Thm.reflexive (nth cus i)))]
          else let
            val cui = nth cus i
            val cui_equivs =
                if is_open bd_vars (Thm.term_of cui) then
                  [(id, Thm.reflexive cui)]
                else (id, cui) |> get_ac_head_equiv tbl ac_info
                               |> maps process_expansion
          in
            (i, (id, Thm.reflexive cui)) :: map (pair i) cui_equivs
          end

      (* Given (i, (id', eq1)), where eq1 is us[i] == v1 ... vk, find
         all (i, eq1, j, inst', eq2), where j is between 0 and k-1,
         and eq2 is an equality t[inst'] == vj (a match between t and
         vj extending the input instantiation.
       *)
      fun match_expansion (i, (id', eq1)) =
          let
            val cui' = Thm.rhs_of eq1
            val cuis' = ACUtil.cdest_ac_gen assoc_r ac_info cui'

            (* Match t with j'th term in uis'. *)
            fun match_j j =
                let
                  val cuij' = nth cuis' j
                  val insts = match tbl bd_vars (t, cuij') (id', env)
                  fun process_inst ((id'', env'), eq2) =
                      (i, eq1, j, (id'', env'), eq2)
                in
                  map process_inst insts
                end
          in
            if not (is_sch_arg ac_info (List.last ts)) andalso
               length cuis' - 1 > diff_l then []
            else if assoc_only then
              if assoc_r then match_j 0 else match_j (length cuis' - 1)
            else
              maps match_j (0 upto (length cuis' - 1))
          end

      (* Given (i, eq1, j, inst', eq2), recursively call
         match_ac_list on the remainder of the ts and us, then
         combine the equalities.
       *)
      fun process_match (i, eq1, j, (id', env'), eq2) =
          let
            val cuis' = ACUtil.cdest_ac_gen assoc_r ac_info (Thm.rhs_of eq1)

            (* The remaining terms in us. *)
            val cus' = if assoc_r then nth_drop j cuis' @ nth_drop i cus
                      else nth_drop i cus @ nth_drop j cuis'

            val match_remains =
                match_ac_list is_simple assoc_r tbl bd_vars ac_info
                              (ts', cus') (id', env')

            (* Here eq2 is t[inst'] == uij', and eq' is ts'[inst''] ==
               us'. We need the equation ts[inst''] == us. This is
               obtained by appending eq2 to the appropriate side of
               eq', shift uij' into proper position, then combine
               using eq1, finally shifting ui' into proper position.
             *)
            fun process_inst_r ((id'', env''), eq') =
                (* First assoc_r = true case. *)
                let
                  val eq_total = ACUtil.comb_ac_equiv ac_info [eq2, eq']

                  (* This part of conv moves uis'[j] to its proper
                     position, then applies eq1 in reverse to get us[i].
                   *)
                  val cv_to_u = (ac_shift_l_to_n_cv ac_info j)
                                    then_conv (Conv.rewr_conv (meta_sym eq1))
                  val rhs_cv =
                      (ac_group_first_n_cv ac_info (length cuis'))
                          then_conv (if length cus = 1 then cv_to_u
                                     else Conv.arg1_conv cv_to_u)
                          then_conv (ac_shift_l_to_n_cv ac_info i)
                in
                  ((id'', env''), eq_total |> apply_to_rhs rhs_cv)
                end

            fun process_inst_l ((id'', env''), eq') =
                (* Next, assoc_r = false case. *)
                let
                  val eq_total = ACUtil.comb_ac_equiv ac_info [eq', eq2]

                  val cv_to_u = (ac_shift_r_to_n_cv ac_info j)
                                    then_conv (Conv.rewr_conv (meta_sym eq1))
                  val rhs_cv =
                      (ac_group_last_n_cv ac_info (length cuis'))
                          then_conv (if length cus = 1 then cv_to_u
                                     else Conv.arg_conv cv_to_u)
                          then_conv (ac_shift_r_to_n_cv ac_info i)
                in
                  ((id'', env''), eq_total |> apply_to_rhs rhs_cv)
                end
          in
            if assoc_r then map process_inst_r match_remains
            else map process_inst_l match_remains
          end

      val range_i = if length cus = 0 then []
                    else if assoc_only then
                      if assoc_r then [0] else [length cus - 1]
                    else 0 upto (length cus - 1)
    in
      range_i |> maps expand_i
              |> maps match_expansion
              |> maps process_match
    end

(* Match between t and u, possibly using AC properties of the head
   function of t. We assume that t has been instantiated according to
   instsp, and also normalized with respect to minus and left
   association.
 *)
and match_ac_raw is_simple ac_info tbl bd_vars (t, cu) (instsp as (id, _)) =
    let
      val {unit_val, ...} = ac_info
      val assoc_only = not (ACUtil.has_comm_th ac_info)
      val targ = ACUtil.dest_ac_l ac_info t
      val u_eq = ACUtil.normalize_minus_assoc_r ac_info cu
      val cu' = Thm.rhs_of u_eq
      val cuarg = ACUtil.cdest_ac_r ac_info cu'

      (* u_eq: u == u', eq_th: t'(inst) == u'. *)
      fun process_inst ((id, env), eq_th) =
          ((id, env), transitive_list [eq_th, meta_sym u_eq])

      (* Swap order of associativity on the pattern side to left. *)
      fun swap_t_to_l ((id, env), eq_th) =
          ((id, env),
           apply_to_lhs (ACUtil.swap_assoc_to_l (length targ) ac_info) eq_th)

      (* Swap order of associativity on the term side to right. *)
      fun swap_u_to_r ((id, env), eq_th) =
          ((id, env),
           apply_to_rhs (ACUtil.swap_assoc_to_r (length cuarg) ac_info) eq_th)
    in
      if exists (fn carg => RewriteTable.is_equiv id tbl (carg, unit_val)) cuarg
      then []
      else if assoc_only andalso is_sch_arg ac_info (nth targ 0) then
        let
          val insts = match_ac_list is_simple false tbl bd_vars ac_info
                                    (rev targ, cuarg) instsp
        in
          map (process_inst o swap_u_to_r) insts
        end
      else
        let
          val insts = match_ac_list is_simple true tbl bd_vars ac_info
                                    (targ, cuarg) instsp
        in
          map (process_inst o swap_t_to_l) insts
        end
    end

(* Matching an order list of patterns against terms. *)
and match_list tbl bd_vars (ts, cus) instsp =
    if length ts = 0 andalso length cus = 0 then [(instsp, [])]
    else if length ts = 0 orelse length cus = 0 then []
    else let
      (* Two choices, one of which should always work (encounter no
         illegal higher-order patterns.
       *)
      fun hd_first () =
          let
            val insts_t = match tbl bd_vars (hd ts, hd cus) instsp
            fun process_inst_t (instsp', th) =
                let
                  val insts_ts' = match_list tbl bd_vars (tl ts, tl cus) instsp'
                in
                  map (apsnd (cons th)) insts_ts'
                end
          in
            maps process_inst_t insts_t
          end
      fun tl_first () =
          let
            val insts_ts' = match_list tbl bd_vars (tl ts, tl cus) instsp
            fun process_inst_ts' (instsp', ths) =
                let
                  val insts_t = match tbl bd_vars (hd ts, hd cus) instsp'
                in
                  map (apsnd (fn th => th :: ths)) insts_t
                end
          in
            maps process_inst_ts' insts_ts'
          end
    in
      hd_first () handle AUTO2 "invalid pattern" => tl_first ()
    end

(* Match a non-AC function. *)
and match_comb tbl bd_vars (t, cu) (instsp as (_, (_, inst))) =
    let
      val {ctxt, ...} = tbl
      val (tf, targs) = Term.strip_comb t
      val (cuf, cuargs) = Drule.strip_comb cu
      val uf = Thm.term_of cuf
    in
      if Term.aconv_untyped (tf, uf) then
        let
          val instsps' = match_list tbl bd_vars (targs, cuargs) instsp
          fun process_inst (instsp', ths) =
              (instsp', comb_equiv (cuf, ths))
        in
          map process_inst instsps'
        end
      else if is_Var tf then
        let
          val (ixn, _) = Term.dest_Var tf
        in
          case Vartab.lookup inst ixn of
              NONE =>
              if subset (op aconv) (targs, bd_vars) andalso
                 not (has_duplicates (op aconv) targs) then
                let
                  val cu' = cu |> Thm.term_of
                               |> fold lambda_abstract (rev targs)
                               |> cert ctxt
                in
                  map (fn (instsp', _) => (instsp', Thm.reflexive cu))
                      (update_inst bd_vars ixn cu' instsp)
                end
              else
                raise AUTO2 "invalid pattern"
            | SOME (_, tf') =>
              let
                val t' = Term.list_comb (tf', targs) |> Envir.beta_norm
              in
                match tbl bd_vars (t', cu) instsp
              end
        end
      else []
    end

(* Match t and u at head, non-AC case. *)
and match_non_ac_head tbl bd_vars (t, cu) (instsp as (_, (_, inst))) =
    let
      val {ctxt, ...} = tbl
      val u = Thm.term_of cu
    in
      if fastype_of t <> fastype_of u then [] else
      case (t, u) of
          (Var ((nm, i), _), _) =>
          (case Vartab.lookup inst (nm, i) of
               NONE => if (nm = "NUMC" orelse nm = "NUMCu") andalso
                          not (Consts.is_const_ctxt ctxt u) then []
                       else if nm = "FREE" andalso not (Term.is_Free u) then []
                       else update_inst bd_vars (nm, i) cu instsp
             | SOME (_, u') => match_non_ac_head tbl bd_vars (u', cu) instsp)
        | (Free (a, _), Free (b, _)) =>
          if a = b then [(instsp, Thm.reflexive cu)] else []
        | (Const (a, _), Const (b, _)) =>
          if a = b then [(instsp, Thm.reflexive cu)] else []
        | (_ $ _, _) => match_comb tbl bd_vars (t, cu) instsp
        | _ => []
    end

(* Here we assume that t is instantiated according to instsp, and
   satisfies the condition imposed by check_use_ac. We also assume
   that it is normalized with respect to minus and left association.
 *)
and match_ac_head ac_info tbl bd_vars (t, cu) (id, env) =
    let
      val u = Thm.term_of cu
    in
      if fastype_of t <> fastype_of u then []
      else if ACUtil.head_agrees_all ac_info t andalso
              not (ACUtil.head_agrees_all ac_info u) then []
      else let
        (* List of AC-subterm rewrites of u. *)
        val u_equivs = if is_open bd_vars u then [(id, Thm.reflexive cu)]
                       else ac_subterm_equivs tbl ac_info (id, cu)

        fun process_equiv (id', th) =
            let
              val cu' = Thm.rhs_of th
              val insts_u' =
                  match_ac_raw false ac_info tbl bd_vars (t, cu') (id', env)
            in
              (* th': t(env) == u', and th: u == u'. *)
              map (fn (inst', th') =>
                      (inst', transitive_list [th', meta_sym th])) insts_u'
            end

        (* Compare instantiations at the following indexnames. *)
        val vars = map fst (Term.add_vars t [])
      in
        (maps process_equiv u_equivs)
            |> max_partial (inst_eq_better tbl vars)
      end
    end

(* With fixed t, match non-AC with all equivalences of u. *)
and match_non_ac_all_head_with_t tbl bd_vars (t, cu) (id, env) =
    let
      val u = Thm.term_of cu
      val u_equivs =
          if is_open bd_vars u then [(id, Thm.reflexive cu)]
          else RewriteTable.get_head_equiv_with_t tbl (id, cu) t

      fun process_equiv (id', eq_u) =
          let
            val cu' = Thm.rhs_of eq_u
            val insts_u' = match_non_ac_head tbl bd_vars (t, cu') (id', env)
            fun process_inst ((id', env'), eq_th) =
                (* eq_th: t(env') == u', eq_u: u == u'. *)
                ((id', env'), transitive_list [eq_th, meta_sym eq_u])
          in
            map process_inst insts_u'
          end
    in
      maps process_equiv u_equivs
    end

(* With fixed t, match AC with all equivalences of u. *)
and match_ac_all_head_with_t ac_info tbl bd_vars (t, cu) (id, env) =
    let
      val u = Thm.term_of cu
      val u_equivs =
          if is_open bd_vars u then [(id, Thm.reflexive cu)]
          else get_ac_head_equiv tbl ac_info (id, cu)

      fun process_equiv (id', eq_u) =
          let
            val cu' = Thm.rhs_of eq_u
            val insts_u' = match_ac_head ac_info tbl bd_vars (t, cu') (id', env)
            fun process_inst ((id'', env'), eq_th) =
                (* eq_th: t(env') == u', eq_u: u == u'. *)
                ((id'', env'), transitive_list [eq_th, meta_sym eq_u])
          in
            map process_inst insts_u'
          end
    in
      maps process_equiv u_equivs
    end

(* Match t and all head equivalences of u. In this function, consider
   all equivalences of t (through analyze_t).
 *)
and match_all_head (tbl as {ctxt, ...}) bd_vars (t, u) (id, env) =
    case ACUtil.get_head_ac_info_all ctxt t of
        NONE => match_non_ac_all_head_with_t tbl bd_vars (t, u) (id, env)
      | SOME ac_info =>
        let
          val thy = RewriteTable.theory_of tbl
          val u_ac_equivs = get_ac_head_equiv tbl ac_info (id, u)
        in
          if not (is_match_unit ac_info t) andalso
             length u_ac_equivs = 0 then []
          else let
            val t_equivs = analyze_t ac_info tbl (id, env) t

            fun process_t_equiv (use_ac, (id', env'), eq_t) =
                let
                  val t' = rhs_of eq_t
                  val insts =
                      if use_ac = AC_YES then
                        match_ac_all_head_with_t
                            ac_info tbl bd_vars (t', u) (id', env')
                      else if use_ac = AC_NO then
                        match_non_ac_all_head_with_t
                            tbl bd_vars (t', u) (id', env')
                      else let  (* use_ac = AC_UNKNOWN *)
                        val _ = assert (not (t' aconv t)) "match_all_head"
                      in
                        match_all_head tbl bd_vars (t', u) (id', env')
                      end

                  fun process_inst ((id', env'), eq_th) =
                      (* eq_t: t = t', eq_th: t'(env') == u *)
                      if Thm.is_reflexive eq_t then ((id', env'), eq_th)
                      else let
                        val eq' = subst_thm_thy thy env' eq_t
                      in
                        ((id', env'), transitive_list [eq', eq_th])
                      end
                in
                  map process_inst insts
                end
          in
            maps process_t_equiv t_equivs
          end
        end

(* Match t and u, possibly by rewriting u at head. *)
and match (tbl as {ctxt, ...}) bd_vars (t, cu) (instsp as (_, (_, inst))) =
    case check_type_term tbl (t, Thm.term_of cu) instsp of
        NONE => []
      | SOME (instsp', t') =>
        case (t', Thm.term_of cu) of
            (Var ((nm, i), _), _) =>
            (case Vartab.lookup inst (nm, i) of
                 NONE => if member (op =) ["NUMC", "NUMCu", "FREE"] nm then
                           match_all_head tbl bd_vars (t', cu) instsp'
                         else
                           update_inst bd_vars (nm, i) cu instsp'
               | SOME (_, u') => match tbl bd_vars (u', cu) instsp')
          | (Abs (_, T, t'), Abs (nm, U, _)) => (
            case check_type tbl (T, U) instsp' of
                NONE => []
              | SOME (instsp'' as (_, (tyinst', _))) =>
                let
                  val (cv, cu') = Thm.dest_abs (SOME Name.uu) cu
                  val v = Thm.term_of cv
                  val t'' = Envir.subst_term_types tyinst' t'
                  val t_free = Term.subst_bound (v, t'')
                  val insts' = match tbl (v :: bd_vars) (t_free, cu') instsp''
                  fun process_inst (inst', th') =
                      (inst', Thm.abstract_rule nm cv th')
                in
                  map process_inst insts'
                end)
          | (Abs _, _) => (
            let
              val u_eq = reverse_eta_conv ctxt cu
              val cu' = Thm.rhs_of u_eq
              val insts' = match tbl bd_vars (t', cu') instsp'
              fun process_inst (inst', th') =
                  (inst', transitive_list [th', meta_sym u_eq])
            in
              map process_inst insts'
            end
            handle CTERM _ => [])
          | (_, Abs _) => (
            let
              val u_eq = Thm.eta_conversion cu
              val cu' = Thm.rhs_of u_eq
            in
              if cu aconvc cu' then []
              else let
                val insts' = match tbl bd_vars (t', cu') instsp'
                fun process_inst (inst', th') =
                    (inst', transitive_list [th', meta_sym u_eq])
              in
                map process_inst insts'
              end
            end)
          | _ => (* Free, Const, and comb case *)
            (match_all_head tbl bd_vars (t', cu) instsp')
                |> distinct compare_inst

(* Function for matching at head to export. Consider all equivalences
   of t (but not of u).
 *)
fun match_head (tbl as {ctxt, ...}) bd_vars (t, cu) (id, env) =
    case check_type_term tbl (t, Thm.term_of cu) (id, env) of
        NONE => []
      | SOME ((id, env), t) =>
        case ACUtil.get_head_ac_info_all ctxt t of
            NONE => match_non_ac_head tbl bd_vars (t, cu) (id, env)
          | SOME ac_info =>
            let
              val thy = RewriteTable.theory_of tbl
              val t_equivs = analyze_t ac_info tbl (id, env) t
              fun process_t_equiv (use_ac, (id', env'), eq_t) =
                  let
                    val t' = rhs_of eq_t
                    val insts =
                        if use_ac = AC_YES then
                          match_ac_head ac_info tbl bd_vars (t', cu) (id', env')
                        else if use_ac = AC_NO then
                          match_non_ac_head tbl bd_vars (t', cu) (id', env')
                        else let  (* use_ac = AC_UNKNOWN *)
                          val _ = assert (not (t' aconv t)) "match_head"
                        in
                          match_head tbl bd_vars (t', cu) (id', env')
                        end

                    fun process_inst ((id', env'), eq_th) =
                        (* eq_t: t == t', eq_th: t'(env') == u. *)
                        if Thm.is_reflexive eq_t then ((id', env'), eq_th)
                        else let
                          val eq' = subst_thm_thy thy env' eq_t
                        in
                          ((id', env'), transitive_list [eq', eq_th])
                        end
                  in
                    map process_inst insts
                  end
            in
              maps process_t_equiv t_equivs
            end

(* Functions for export. *)
fun rewrite_match_gen at_head tbl bd_vars (t, cu) (id, env) =
    if at_head then
      match_head tbl bd_vars (t, cu) (id, env)
    else
      match tbl bd_vars (t, cu) (id, env)

fun rewrite_match tbl (t, cu) (id, env) =
    match tbl [] (t, cu) (id, env)

fun rewrite_match_head tbl (t, cu) (id, env) =
    match_head tbl [] (t, cu) (id, env)

(* Version with bd_vars, used in disj_prop_matcher. *)
fun rewrite_match_ac_bd
        is_simple ac_info (tbl as {ctxt, ...}) bd_vars (t, cu) (id, env) =
    let
      val thy = RewriteTable.theory_of tbl
      val norm_eq = ACUtil.normalize_minus_assoc_l ac_info (cert ctxt t)
      val t' = rhs_of norm_eq
      fun process_inst ((id', env'), eq_th) =
          let
            val norm_eq' = subst_thm_thy thy env' norm_eq
          in
            ((id', env'), transitive_list [norm_eq', eq_th])
          end
      val insts =
          if is_simple then
            match_ac_raw true ac_info tbl bd_vars (t', cu) (id, env)
          else
            match_ac_head ac_info tbl bd_vars (t', cu) (id, env)
    in
      map process_inst insts
    end

(* More commonly used external version. *)
fun rewrite_match_ac is_simple ac_info tbl =
    rewrite_match_ac_bd is_simple ac_info tbl []

(* pairs is a list of (at_head, (t, u)). Match the pairs in sequence,
   and return a list of ((id, inst), ths), where ths is the list of
   equalities t(env) == u.
 *)
fun rewrite_match_list tbl pairs instsp =
    case pairs of
        [] => [(instsp, [])]
      | (at_head, (t, cu)) :: pairs' =>
        let
          val insts_t = rewrite_match_gen at_head tbl [] (t, cu) instsp
          fun process_inst_t (instsp', th) =
              let
                val insts_ts' = rewrite_match_list tbl pairs' instsp'
              in
                map (apsnd (cons th)) insts_ts'
              end
        in
          maps process_inst_t insts_t
        end

(* Given two lists of terms (ts, us), match ts with a subset of
   us. Return a list of ((id, inst), ths), where ths is the list of
   equalities t_i(env) == u_j.
 *)
fun rewrite_match_subset tbl (ts, cus) instsp =
    case ts of
        [] => [(instsp, [])]
      | t :: ts' =>
        let
          fun match_i i =
              map (pair i) (rewrite_match tbl (t, nth cus i) instsp)

          fun process_match_i (i, (instsp', th)) =
              let
                val insts_ts' =
                    rewrite_match_subset tbl (ts', nth_drop i cus) instsp'
              in
                map (apsnd (cons th)) insts_ts'
              end
        in
          (0 upto (length cus - 1))
              |> maps match_i |> maps process_match_i
        end

(* Fast function for determining whether there can be a match between
   t and u.
 *)
fun pre_match_type tbl (T, U) =
    let
      val thy = RewriteTable.theory_of tbl
      val _ = Sign.typ_match thy (T, U) Vartab.empty
    in
      true
    end
    handle Type.TYPE_MATCH => false

fun pre_match_comb tbl (t, cu) =
    let
      val (tf, targs) = Term.strip_comb t
      val (cuf, cuargs) = Drule.strip_comb cu
      val uf = Thm.term_of cuf
    in
      is_Var tf orelse (Term.aconv_untyped (tf, uf) andalso
                        length targs = length cuargs andalso
                        forall (pre_match tbl) (targs ~~ cuargs))
    end

and pre_match_non_ac_head (tbl as {ctxt, ...}) (t, cu) =
    let
      val u = Thm.term_of cu
    in
      case (t, u) of
          (Var ((nm, _), T), _) =>
          if Term.is_open u then false
          else if not (pre_match_type tbl (T, fastype_of u)) then false
          else if nm = "NUMC" orelse nm = "NUMCu" then
            Consts.is_const_ctxt ctxt u
          else if nm = "FREE" then Term.is_Free u
          else true
        | (Free (a, T), Free (b, U)) =>
          (a = b andalso pre_match_type tbl (T, U))
        | (Const (a, T), Const (b, U)) =>
          (a = b andalso pre_match_type tbl (T, U))
        | (_ $ _, _) => pre_match_comb tbl (t, cu)
        | _ => false
    end

and pre_match_unit ac_info tbl (t, cu) =
    if not (ACUtil.head_agrees ac_info t) then false
    else let
      val (A, B) = dest_binop_args t
    in
      if is_unit_allowed_var A then pre_match tbl (B, cu)
      else if is_unit_allowed_var B then pre_match tbl (A, cu)
      else false
    end

and pre_match_all_head (tbl as {ctxt, ...}) (t, cu) =
    let
      val thy = RewriteTable.theory_of tbl
      val u = Thm.term_of cu
      val tyinst = Sign.typ_match thy (fastype_of t, fastype_of u) Vartab.empty
      val t' = Envir.subst_term_types tyinst t
    in
      case ACUtil.get_head_ac_info_all ctxt t' of
          NONE =>
          if Term.is_open u then pre_match_non_ac_head tbl (t', cu)
          else let
            val u_equivs =
                (RewriteTable.get_head_equiv_with_t tbl ([], cu) t')
                    |> map snd |> map Thm.rhs_of
          in
            exists (fn cu' => pre_match_non_ac_head tbl (t', cu')) u_equivs
          end
        | SOME ac_info =>
          if Term.is_open u then ACUtil.head_agrees_all ac_info u
          else let
            val u_ac_equivs = get_ac_head_equiv tbl ac_info ([], cu)
          in
            pre_match_unit ac_info tbl (t', cu) orelse length u_ac_equivs > 0
          end
    end
    handle Type.TYPE_MATCH => false

and pre_match (tbl as {ctxt, ...}) (t, cu) =
    let
      val u = Thm.term_of cu
    in
      case (t, u) of
          (Var ((nm, _), T), _) =>
          if Term.is_open u then false
          else if not (pre_match_type tbl (T, fastype_of u)) then false
          else if member (op =) ["NUMC", "NUMCu", "FREE"] nm then
            pre_match_all_head tbl (t, cu)
          else true
        | (Abs (_, T, t'), Abs (_, U, _)) =>
          if not (pre_match_type tbl (T, U)) then false
          else let
            val (cv, cu') = Thm.dest_abs (SOME Name.uu) cu
            val t'' = subst_bound (Thm.term_of cv, t')
          in
            pre_match tbl (t'', cu')
          end
        | (Abs _, _) => (
          pre_match tbl (t, Thm.rhs_of (reverse_eta_conv ctxt cu))
          handle CTERM _ => false)
        | (_, Abs _) => (
          let val cu' = Thm.rhs_of (Thm.eta_conversion cu) in
            if u aconv Thm.term_of cu' then false
            else pre_match tbl (t, cu')
          end)
        | (Bound i, Bound j) => (i = j)
        | (_, _) => pre_match_all_head tbl (t, cu)
    end

fun pre_match_head (tbl as {ctxt, ...}) (t, cu) =
    let
      val thy = RewriteTable.theory_of tbl
      val u = Thm.term_of cu
      val tyinst = Sign.typ_match thy (fastype_of t, fastype_of u) Vartab.empty
      val t' = Envir.subst_term_types tyinst t
    in
      case ACUtil.get_head_ac_info_all ctxt t' of
          NONE => pre_match_non_ac_head tbl (t', cu)
        | SOME {cfhead, uinv_op, inv_op, ...} =>
          (* head of u agrees with ac_info, up to types. *)
          member Term.aconv_untyped (map Thm.term_of [cfhead, uinv_op, inv_op])
                 (Term.head_of u)
    end
    handle Type.TYPE_MATCH => false

(* Counts the number of literal AC matches in t. The second argument
   is the list of schematic variables that are already instantiated.
 *)
fun literal_ac_count thy t inst_vars =
    case ACUtil.get_head_ac_info_all_thy thy t of
        NONE => literal_ac_count_list thy (dest_args t) inst_vars
      | SOME ac_info =>
        let
          val targs =
              t |> cert_thy thy |> ACUtil.normalize_minus_assoc_l ac_info
                |> rhs_of |> ACUtil.dest_ac_l ac_info
          val sch_args = targs |> filter (is_sch_arg ac_info)
                               |> map dest_sch_arg
                               |> subtract (op aconv) inst_vars
          val count_top = if length sch_args >= 2 then 1 else 0
          val count_list =
              if length targs = 1 then
                (* Be careful of -t' case. *)
                literal_ac_count thy (dest_uinv t) inst_vars
              else
                literal_ac_count_list thy targs inst_vars
        in
          count_top + count_list
        end

and literal_ac_count_list thy ts inst_vars =
    if length ts = 0 then 0
    else let
      val new_vars = map Var (Term.add_vars (hd ts) [])
      val inst_vars' = merge (op aconv) (inst_vars, new_vars)
    in
      literal_ac_count thy (hd ts) inst_vars +
      literal_ac_count_list thy (tl ts) inst_vars'
    end

(* Heuristic for determining which of two patterns should be matched
   first. This takes into account of:

   - One of the patterns may not be match-able alone due to schematic
     variables in function position. That pattern should be matched
     last.

   - Minimize the number of AC functions with schematic terms that
     have to be matched literally.

   Returns true if the order should be left as is, false if the order
   should be reversed.
 *)
fun get_pattern_order thy (t1, t2) =
    let
      val _ = assert (is_pattern_list [t1, t2])
                     "get_pattern_order: invalid pattern."
    in
      (* First two cases, forced by is_pattern requirement. *)
      if not (is_pattern t2) then true
      else if not (is_pattern t1) then false
      else let
        val count1 = literal_ac_count_list thy [t1, t2] []
        val count2 = literal_ac_count_list thy [t2, t1] []
      in
        (* Next, swap only if count2 is lower. *)
        count1 <= count2
      end
    end

end  (* structure Matcher. *)
