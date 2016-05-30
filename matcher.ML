(* Matching up to equivalence (E-matching) using a rewrite table. *)

signature MATCHER =
sig
  (* Internal *)
  val is_unit_allowed_var: term -> bool
  val check_type_term:
      rewrite_table -> term * term -> id_inst -> (id_inst * term) option
  val check_type: rewrite_table -> typ * typ -> id_inst -> id_inst option
  val id_eq_better: rewrite_table -> box_id * 'a -> box_id * 'a -> bool
  val inst_eq_better: rewrite_table -> (string * int) list -> id_inst_th ->
                      id_inst_th -> bool
  val ac_shift_n_to_r_cv: ac_inst_info -> int -> conv
  val ac_shift_r_to_n_cv: ac_inst_info -> int -> conv
  val ac_shift_l_to_n_cv: ac_inst_info -> int -> conv
  val ac_group_last_n_cv: ac_inst_info -> int -> conv
  val ac_group_first_n_cv: ac_inst_info -> int -> conv
  val normalize_minus_assoc_gen: bool -> ac_inst_info -> conv
  val normalize_minus_assoc_l: ac_inst_info -> conv
  val normalize_minus_assoc_r: ac_inst_info -> conv
  val get_ac_head_equiv: rewrite_table -> ac_inst_info -> box_id * term ->
                         (box_id * thm) list
  val reduce_unit_t: rewrite_table -> ac_inst_info -> box_id * term ->
                     (box_id * thm) list
  val analyze_t: ac_inst_info -> rewrite_table -> id_inst -> term ->
                 (int * id_inst * thm) list
  val ac_subterm_equivs: rewrite_table -> ac_inst_info -> box_id * term ->
                         (box_id * thm) list
  val match_ac_list: bool -> rewrite_table -> term list -> ac_inst_info ->
                     term list * term list -> id_inst -> id_inst_th list
  val match_ac_raw: ac_inst_info -> rewrite_table -> term list ->
                    term * term -> id_inst -> id_inst_th list
  val match: rewrite_table -> term list -> term * term -> id_inst ->
             id_inst_th list
  val match_ac_head: ac_inst_info -> rewrite_table -> term list ->
                     term * term -> id_inst -> id_inst_th list
  val match_head: rewrite_table -> term list -> term * term -> id_inst ->
                  id_inst_th list

  (* Export *)
  val rewrite_match: rewrite_table -> term * term -> id_inst -> id_inst_th list
  val rewrite_match_head:
      rewrite_table -> term * term -> id_inst -> id_inst_th list
  val rewrite_match_ac_bd:
      ac_inst_info -> rewrite_table -> term list -> term * term -> id_inst ->
      id_inst_th list
  val rewrite_match_ac:
      ac_inst_info -> rewrite_table -> term * term -> id_inst -> id_inst_th list
  val rewrite_match_list: rewrite_table -> (bool * (term * term)) list ->
                          id_inst -> id_inst_ths list
  val pre_match_head: rewrite_table -> term * term -> bool
  val pre_match: rewrite_table -> term * term -> bool

  val literal_ac_count: theory -> term -> term list -> int
  val literal_ac_count_list: theory -> term list -> term list -> int
  val get_pattern_order: theory -> term * term -> bool
end;

structure Matcher : MATCHER =
struct

val refl = RewriteTable.refl

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
fun update_inst tbl bd_vars ixn u (id, (tyinsts, insts)) =
    if is_open bd_vars u then []
    else [((id, (update_env (ixn, u) (tyinsts, insts))), refl tbl u)]

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
      val assoc_cv = ACUtil.assoc_cv ac_info
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
      val assoc_sym_cv = ACUtil.assoc_sym_cv ac_info
      fun helper n ct =
          if n <= 1 then Conv.all_conv ct
          else
            ((Conv.arg_conv (helper (n-1))) then_conv assoc_sym_cv) ct
    in
      if k = n then Conv.all_conv ct
      else helper n ct
    end

fun is_uinv {uinv_op, ...} t =
    Term.head_of t aconv uinv_op

fun dest_uinv t =
    t |> Term.dest_comb |> snd

fun mk_uinv {uinv_op, ...} t =
    uinv_op $ t

(* From a == b, make -a == -b. *)
fun mk_uinv_eq ctxt {uinv_op, ...} eq_th =
    Thm.combination (Thm.reflexive (cert ctxt uinv_op)) eq_th

fun is_sch_arg ac_info t =
    Term.is_Var t orelse
    (is_uinv ac_info t andalso Term.is_Var (dest_uinv t))

(* Given ?a or -?a, return -a. *)
fun dest_sch_arg t =
    if Term.is_Var t then t else dest_uinv t

fun normalize_minus_assoc_gen assoc_r ac_info =
    (ACUtil.normalize_minus ac_info)
        then_conv (ACUtil.normalize_unit ac_info)
        then_conv (ACUtil.normalize_assoc_gen assoc_r ac_info)

val normalize_minus_assoc_l = normalize_minus_assoc_gen false
val normalize_minus_assoc_r = normalize_minus_assoc_gen true

(* Obtain list of head equivs of u whose head function belongs to the
   given AC info.
 *)
fun get_ac_head_equiv' tbl {cfhead, uinv_op, inv_op, ...} (id, u) =
    maps (RewriteTable.get_head_equiv_with_t tbl (id, u))
         [Thm.term_of cfhead, uinv_op, inv_op]

fun get_ac_head_equiv (tbl as {lat, ctxt, ...}) ac_info (id, u) =
    let
      fun equiv_eq_better (id1, th1) (id2, th2) =
          BoxID.is_eq_ancestor lat id1 id2 andalso rhs_of th1 aconv rhs_of th2

      val inv_equivs =
          if is_uinv ac_info u then
            map (apsnd (mk_uinv_eq ctxt ac_info))
                (get_ac_head_equiv tbl ac_info (id, dest_uinv u))
          else []
    in
      (inv_equivs @ get_ac_head_equiv' tbl ac_info (id, u))
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
fun check_use_ac (ac_info as {comm_th, ...}) targ =
    if length targ = 1 then
      (* Either of form -a, or not AC at all. *)
      (false, NONE)
    else let
      val assoc_only = is_true_th comm_th
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
fun reduce_unit_t (tbl as {lat, ...})
                  (ac_info as {cfhead, unit_val, ...}) (id, t) =
    if member (op aconv) [HOLogic.conj, HOLogic.disj]
              (Thm.term_of cfhead) then [(id, refl tbl t)]
    else if not (ACUtil.head_agrees ac_info t) then
      let
        val equivs = RewriteTable.equiv_info tbl id (t, unit_val)
      in
        if exists (fn (id', _) => id' = id) equivs then equivs
        else (id, refl tbl t) :: equivs
      end
    else
      let
        val (_, (A, B)) = dest_binop t
        val A_equiv = reduce_unit_t tbl ac_info (id, A)
        val B_equiv = reduce_unit_t tbl ac_info (id, B)
        val equivs = BoxID.get_all_merges_info lat [A_equiv, B_equiv]
        fun process_equiv (id, th_pair) =
            (id, (ACUtil.comb_ac_equiv ac_info th_pair)
                     |> apply_to_rhs (Conv.try_conv (ACUtil.unit_cv ac_info)))
      in
        map process_equiv equivs
      end

fun is_match_unit (ac_info as {unit_val, ...}) t =
    if not (ACUtil.head_agrees ac_info t) then false
    else let
      val (_, (A, B)) = dest_binop t
    in
      is_unit_allowed_var A orelse is_unit_allowed_var B orelse
      A aconv unit_val orelse B aconv unit_val
    end

val (AC_YES, AC_NO, AC_UNKNOWN) = (0, 1, 2)

fun analyze_match_unit (ac_info as {unit_val, ...}) ctxt env (id, t) =
    if not (ACUtil.head_agrees ac_info t) then []
    else let
      val (_, (A, B)) = dest_binop t
      fun process_var var =
          if is_unit_allowed_var var then
            let
              val (ixn, _) = Term.dest_Var var
              val env' = update_env (ixn, unit_val) env
              val eq = t |> subst_term_norm env'
                         |> cert ctxt |> ACUtil.unit_cv ac_info
            in
              if ACUtil.head_agrees_with_inv ac_info (rhs_of eq) then
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
fun analyze_t (ac_info as {comm_th, ...}) (tbl as {ctxt, ...}) (id, env) t =
    let
      val t' = subst_term_norm env t
      val ct' = cert ctxt t'
      val eq1 = ct' |> normalize_minus_assoc_l ac_info
      val eqs2 = reduce_unit_t tbl ac_info (id, rhs_of eq1)
      val assoc_only = is_true_th comm_th
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
fun ac_subterm_equivs (tbl as {lat, ctxt, ...})
                      (ac_info as {cfhead, uinv_op, inv_op, ...}) (id, u) =
    let
      val (f, args) = Term.strip_comb u
      fun valid_rewrite (_, th) =
          not (ACUtil.head_agrees_with_inv ac_info (rhs_of th))

      (* Return the list of non-AC equivalent terms for t. *)
      fun get_head_non_AC_equivs t =
          if ACUtil.head_agrees_with_inv ac_info t then
            (RewriteTable.get_all_equiv tbl t)
                |> filter valid_rewrite
                |> RewriteTable.merge_box_with_info tbl id
                |> max_partial (id_eq_better tbl)
            handle AUTO2 "all_equiv: not found" => []
          else []

      (* Return the complete list of rewrites for t. *)
      fun get_equivs t =
          get_head_non_AC_equivs t @ ac_subterm_equivs tbl ac_info (id, t)
    in
      if f aconv (Thm.term_of cfhead) orelse f aconv inv_op then
        let
          val equiv_pairs = all_pairs (apply2 get_equivs (the_pair args))
          val cf = cert ctxt f
          fun get_equiv ((id1, th1), (id2, th2)) =
              (BoxID.merge_boxes lat (id1, id2),
               Thm.combination (Thm.combination (Thm.reflexive cf) th1) th2)
        in
          map get_equiv equiv_pairs
        end
      else if f aconv uinv_op then
        let
          val equivs = get_equivs (the_single args)
          fun get_equiv (id1, th1) =
              (id1, Thm.combination (Thm.reflexive (cert ctxt uinv_op)) th1)
        in
          map get_equiv equivs
        end
      else
        [(id, refl tbl u)]
    end

(* t is of the form -?A. Assign ?A to normalized form of -us. In the
   returned equality -?A(inst) == f(us). The order of associativity in
   f(us) is specified by assoc_r.
 *)
fun match_uinv assoc_r (tbl as {ctxt, ...}) bd_vars ac_info (t, us) (id, env) =
    let
      (* Here t is -?A, inv_us = -f(us), inv_us' is the simplified
         version which will be assigned to ?A. inv_us_norm_eq is
         inv_us == inv_us'.
       *)
      val inv_us = mk_uinv ac_info (ACUtil.list_ac_gen assoc_r ac_info us)
      val inv_us_norm_eq = ACUtil.normalize_minus ac_info (cert ctxt inv_us)
      val inv_us' = rhs_of inv_us_norm_eq
      val insts = match tbl bd_vars (dest_uinv t, inv_us') (id, env)

      (* eq_th: ?A == inv_us'. Need -?A == f(us). Use the chain

         -?A == -inv_us' == -inv_us (or -(-f(us)) == f(us).
       *)
      fun process_inst ((id', env'), eq_th) =
          ((id', env'),
           (transitive_list [eq_th, meta_sym inv_us_norm_eq])
               |> mk_uinv_eq ctxt ac_info
               |> apply_to_rhs (ACUtil.double_inv_cv ac_info))
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
and match_ac_list assoc_r tbl bd_vars (ac_info as {comm_th, unit_val, ...})
                  (ts, us) (id, env) =
    if length ts = 0 orelse length us = 0 then []
    else if length ts = 1 then
      let
        val t = the_single ts
      in
        if Term.is_Var t then
          if not (is_unit_allowed_var t) andalso
             exists (fn u => RewriteTable.is_equiv id tbl (unit_val, u)) us
          then [] else
          match tbl bd_vars (t, ACUtil.list_ac_gen assoc_r ac_info us) (id, env)
        else if is_uinv ac_info t andalso Term.is_Var (dest_uinv t) then
          match_uinv assoc_r tbl bd_vars ac_info (t, us) (id, env)
        else if length us = 1 then
          match tbl bd_vars (t, the_single us) (id, env)
        else []
      end
    else if not (is_sch_arg ac_info (List.last ts)) andalso
            length ts < length us then []
    else let
      val thy = RewriteTable.theory_of tbl
      val diff_l = length ts - length us
      val (t, ts') = (hd ts, tl ts)
      val assoc_only = is_true_th comm_th

      (* Filter and normalize expansion. *)
      fun process_expansion (id, th) =
          if not (ACUtil.head_agrees_with_inv ac_info (rhs_of th)) then []
          else let
            val th' = th |> apply_to_rhs (
                  normalize_minus_assoc_gen assoc_r ac_info)
            val args = ACUtil.dest_ac_gen assoc_r ac_info (rhs_of th')
          in
            if exists (fn t => RewriteTable.is_equiv id tbl (t, unit_val)) args
            then [] else [(id, th')]
          end

      (* Given i between 0 and length us - 1, return the list of (i,
         (id', eq1)), where eq1 is an expansion of us[i] under
         id'. The trivial expansion (i, (id, us[i] == us[i])) is
         always included in the list.
       *)
      fun expand_i i =
          if assoc_r andalso
             exists (fn t => RewriteTable.is_equiv id tbl (t, nth us i))
                    (take i us)
          then [] else
          if not assoc_r andalso
             exists (fn t => RewriteTable.is_equiv id tbl (t, nth us i))
                    (drop (i+1) us)
          then [] else
          let
            val ui = nth us i
            val ui_equivs =
                if is_open bd_vars ui then [(id, refl tbl ui)]
                else (id, ui) |> get_ac_head_equiv tbl ac_info
                              |> maps process_expansion
          in
            (i, (id, Thm.reflexive (cert_thy thy ui))) ::
            map (pair i) ui_equivs
          end

      (* Given (i, (id', eq1)), where eq1 is us[i] == v1 ... vk, find
         all (i, eq1, j, inst', eq2), where j is between 0 and k-1,
         and eq2 is an equality t[inst'] == vj (a match between t and
         vj extending the input instantiation.
       *)
      fun match_expansion (i, (id', eq1)) =
          let
            val ui' = rhs_of eq1
            val uis' = ACUtil.dest_ac_gen assoc_r ac_info ui'

            (* Match t with j'th term in uis'. *)
            fun match_j j =
                let
                  val uij' = nth uis' j
                  val insts = match tbl bd_vars (t, uij') (id', env)
                  fun process_inst ((id'', env'), eq2) =
                      (i, eq1, j, (id'', env'), eq2)
                in
                  map process_inst insts
                end
          in
            if not (is_sch_arg ac_info (List.last ts)) andalso
               length uis' - 1 > diff_l then []
            else if assoc_only then
              if assoc_r then match_j 0 else match_j (length uis' - 1)
            else
              maps match_j (0 upto (length uis' - 1))
          end

      (* Given (i, eq1, j, inst', eq2), recursively call
         match_ac_list on the remainder of the ts and us, then
         combine the equalities.
       *)
      fun process_match (i, eq1, j, (id', env'), eq2) =
          let
            val uis' = ACUtil.dest_ac_gen assoc_r ac_info (rhs_of eq1)

            (* The remaining terms in us. *)
            val us' = if assoc_r then nth_drop j uis' @ nth_drop i us
                      else nth_drop i us @ nth_drop j uis'

            val match_remains =
                match_ac_list assoc_r tbl bd_vars ac_info (ts', us') (id', env')

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
                      (ac_group_first_n_cv ac_info (length uis'))
                          then_conv (if length us = 1 then cv_to_u
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
                      (ac_group_last_n_cv ac_info (length uis'))
                          then_conv (if length us = 1 then cv_to_u
                                     else Conv.arg_conv cv_to_u)
                          then_conv (ac_shift_r_to_n_cv ac_info i)
                in
                  ((id'', env''), eq_total |> apply_to_rhs rhs_cv)
                end
          in
            if assoc_r then map process_inst_r match_remains
            else map process_inst_l match_remains
          end

      val range_i = if length us = 0 then []
                    else if assoc_only then
                      if assoc_r then [0] else [length us - 1]
                    else 0 upto (length us - 1)
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
and match_ac_raw (ac_info as {comm_th, unit_val, ...}) (tbl as {ctxt, ...})
                 bd_vars (t, u) (instsp as (id, _)) =
    let
      val assoc_only = is_true_th comm_th
      val targ = ACUtil.dest_ac_l ac_info t
      val u_eq = normalize_minus_assoc_r ac_info (cert ctxt u)
      val u' = rhs_of u_eq
      val uarg = ACUtil.dest_ac_r ac_info u'

      (* u_eq: u == u', eq_th: t'(inst) == u'. *)
      fun process_inst ((id, env), eq_th) =
          ((id, env), transitive_list [eq_th, meta_sym u_eq])

      (* Swap order of associativity on the pattern side to left. *)
      fun swap_t_to_l ((id, env), eq_th) =
          ((id, env),
           eq_th |> apply_to_lhs (ACUtil.swap_assoc_to_l (length targ) ac_info))

      (* Swap order of associativity on the term side to right. *)
      fun swap_u_to_r ((id, env), eq_th) =
          ((id, env),
           eq_th |> apply_to_rhs (ACUtil.swap_assoc_to_r (length uarg) ac_info))
    in
      if exists (fn arg => RewriteTable.is_equiv id tbl (arg, unit_val)) uarg
      then []
      else if assoc_only andalso is_sch_arg ac_info (nth targ 0) then
        let
          val insts = match_ac_list false tbl bd_vars ac_info (rev targ, uarg)
                                    instsp
        in
          map (process_inst o swap_u_to_r) insts
        end
      else
        let
          val insts = match_ac_list true tbl bd_vars ac_info (targ, uarg) instsp
        in
          map (process_inst o swap_t_to_l) insts
        end
    end

(* Matching an order list of patterns against terms. *)
and match_list tbl bd_vars (ts, us) instsp =
    if ts = [] andalso us = [] then [(instsp, [])]
    else if ts = [] orelse us = [] then []
    else let
      (* Two choices, one of which should always work (encounter no
         illegal higher-order patterns.
       *)
      fun hd_first () =
          let
            val insts_t = match tbl bd_vars (hd ts, hd us) instsp
            fun process_inst_t (instsp', th) =
                let
                  val insts_ts' = match_list tbl bd_vars (tl ts, tl us) instsp'
                in
                  map (apsnd (cons th)) insts_ts'
                end
          in
            maps process_inst_t insts_t
          end
      fun tl_first () =
          let
            val insts_ts' = match_list tbl bd_vars (tl ts, tl us) instsp
            fun process_inst_ts' (instsp', ths) =
                let
                  val insts_t = match tbl bd_vars (hd ts, hd us) instsp'
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
and match_comb (tbl as {ctxt, ...}) bd_vars (t, u)
               (instsp as (_, (_, inst))) =
    let
      val (tf, targs) = Term.strip_comb t
      val (uf, uargs) = Term.strip_comb u
    in
      if Term.aconv_untyped (tf, uf) then
        let
          val instsps' = match_list tbl bd_vars (targs, uargs) instsp
          fun process_inst (instsp', ths) =
              (instsp', comb_equiv (cert ctxt uf, ths))
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
                  val u' = u |> fold lambda_abstract (rev targs)
                in
                  map (fn (instsp', _) => (instsp', refl tbl u))
                      (update_inst tbl bd_vars ixn u' instsp)
                end
              else
                raise AUTO2 "invalid pattern"
            | SOME (_, tf') =>
              let
                val t' = Term.list_comb (tf', targs) |> Envir.beta_norm
              in
                match tbl bd_vars (t', u) instsp
              end
        end
      else []
    end

(* Match t and u at head, non-AC case. *)
and match_non_ac_head tbl bd_vars (t, u) (instsp as (_, (_, inst))) =
    if fastype_of t <> fastype_of u then [] else
    case (t, u) of
        (Var ((nm, i), _), _) =>
        (case Vartab.lookup inst (nm, i) of
             NONE => if (nm = "NUMC" orelse nm = "NUMCu") andalso
                        not (is_numc u) then []
                     else if nm = "FREE" andalso not (Term.is_Free u) then []
                     else update_inst tbl bd_vars (nm, i) u instsp
           | SOME (_, u') => match_non_ac_head tbl bd_vars (u', u) instsp)
      | (Free (a, _), Free (b, _)) =>
        if a = b then [(instsp, refl tbl u)] else []
      | (Const (a, _), Const (b, _)) =>
        if a = b then [(instsp, refl tbl u)] else []
      | (_ $ _, _) => match_comb tbl bd_vars (t, u) instsp
      | _ => []

(* Here we assume that t is instantiated according to instsp, and
   satisfies the condition imposed by check_use_ac. We also assume
   that it is normalized with respect to minus and left association.
 *)
and match_ac_head ac_info tbl bd_vars (t, u) (id, env) =
    if fastype_of t <> fastype_of u then []
    else if ACUtil.head_agrees_with_inv ac_info t andalso
            not (ACUtil.head_agrees_with_inv ac_info u) then []
    else let
      (* List of AC-subterm rewrites of u. *)
      val u_equivs = if is_open bd_vars u then [(id, refl tbl u)]
                     else ac_subterm_equivs tbl ac_info (id, u)

      fun process_equiv (id', th) =
          let
            val u' = rhs_of th
            val insts_u' = match_ac_raw ac_info tbl bd_vars (t, u') (id', env)
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

(* With fixed t, match non-AC with all equivalences of u. *)
and match_non_ac_all_head_with_t tbl bd_vars (t, u) (id, env) =
    let
      val u_equivs =
          if is_open bd_vars u then [(id, refl tbl u)]
          else RewriteTable.get_head_equiv_with_t tbl (id, u) t

      fun process_equiv (id', eq_u) =
          let
            val u' = rhs_of eq_u
            val insts_u' = match_non_ac_head tbl bd_vars (t, u') (id', env)
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
and match_ac_all_head_with_t ac_info tbl bd_vars (t, u) (id, env) =
    let
      val u_equivs =
          if is_open bd_vars u then [(id, refl tbl u)]
          else get_ac_head_equiv tbl ac_info (id, u)

      fun process_equiv (id', eq_u) =
          let
            val u' = rhs_of eq_u
            val insts_u' = match_ac_head ac_info tbl bd_vars (t, u') (id', env)
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
and match_all_head tbl bd_vars (t, u) (id, env) =
    case RewriteTable.get_head_ac_info_with_inv tbl t of
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
and match (tbl as {ctxt, ...}) bd_vars (t, u) (instsp as (_, (_, inst))) =
    case check_type_term tbl (t, u) instsp of
        NONE => []
      | SOME (instsp' as (id', env'), t') =>
        case (t', u) of
            (Var ((nm, i), _), _) =>
            (case Vartab.lookup inst (nm, i) of
                 NONE => if member (op =) ["NUMC", "NUMCu", "FREE"] nm then
                           match_all_head tbl bd_vars (t', u) instsp'
                         else
                           update_inst tbl bd_vars (nm, i) u instsp'
               | SOME (_, u') => match tbl bd_vars (u', u) instsp')
          | (Abs (_, T, t'), Abs (nm, U, u')) => (
            case check_type tbl (T, U) instsp' of
                NONE => []
              | SOME (instsp'' as (_, (tyinst', _))) =>
                let
                  val bd_var = (Variable.variant_frees ctxt bd_vars [(nm, U)])
                                   |> the_single |> Free
                  val t'' = Envir.subst_term_types tyinst' t'
                  val t_free = subst_bound (bd_var, t'')
                  val u_free = subst_bound (bd_var, u')
                  val insts' = match tbl (bd_var :: bd_vars)
                                     (t_free, u_free) instsp''
                  fun process_inst (inst', th') =
                      (inst', Thm.abstract_rule nm (cert ctxt bd_var) th')
                in
                  map process_inst insts'
                end)
          | (Abs _, _) => (
            let
              val u_eq = reverse_eta_conv ctxt (cert ctxt u)
              val u' = rhs_of u_eq
              val insts' = match tbl bd_vars (t', u') instsp'
              fun process_inst (inst', th') =
                  (inst', transitive_list [th', meta_sym u_eq])
            in
              map process_inst insts'
            end
            handle CTERM _ => [])
          | (_, Abs _) => (
            let
              val u_eq = Thm.eta_conversion (cert ctxt u)
              val u' = rhs_of u_eq
            in
              if u aconv u' then []
              else let
                val insts' = match tbl bd_vars (t', u') instsp'
                fun process_inst (inst', th') =
                    (inst', transitive_list [th', meta_sym u_eq])
              in
                map process_inst insts'
              end
            end)
          | (Free _, _) => map (fn (id'', th) => ((id'', env'), th))
                               (RewriteTable.equiv_info tbl id' (t', u))
          | (Const _, _) => map (fn (id'', th) => ((id'', env'), th))
                                (RewriteTable.equiv_info tbl id' (t', u))
          | _ => (* Free, Const, and comb case *)
            match_all_head tbl bd_vars (t', u) instsp'

(* Function for matching at head to export. Consider all equivalences
   of t (but not of u).
 *)
fun match_head tbl bd_vars (t, u) (id, env) =
    case check_type_term tbl (t, u) (id, env) of
        NONE => []
      | SOME ((id, env), t) =>
        case RewriteTable.get_head_ac_info_with_inv tbl t of
            NONE => match_non_ac_head tbl bd_vars (t, u) (id, env)
          | SOME ac_info =>
            let
              val thy = RewriteTable.theory_of tbl
              val t_equivs = analyze_t ac_info tbl (id, env) t
              fun process_t_equiv (use_ac, (id', env'), eq_t) =
                  let
                    val t' = rhs_of eq_t
                    val insts =
                        if use_ac = AC_YES then
                          match_ac_head ac_info tbl bd_vars (t', u) (id', env')
                        else if use_ac = AC_NO then
                          match_non_ac_head tbl bd_vars (t', u) (id', env')
                        else let  (* use_ac = AC_UNKNOWN *)
                          val _ = assert (not (t' aconv t)) "match_head"
                        in
                          match_head tbl bd_vars (t', u) (id', env')
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
fun rewrite_match_gen at_head tbl bd_vars (t, u) (id, env) =
    if at_head then
      match_head tbl bd_vars (t, u) (id, env)
    else
      match tbl bd_vars (t, u) (id, env)

fun rewrite_match tbl (t, u) (id, env) =
    match tbl [] (t, u) (id, env)

fun rewrite_match_head tbl (t, u) (id, env) =
    match_head tbl [] (t, u) (id, env)

(* Version with bd_vars, used in disj_prop_matcher. *)
fun rewrite_match_ac_bd ac_info (tbl as {ctxt, ...}) bd_vars (t, u) (id, env) =
    let
      val thy = RewriteTable.theory_of tbl
      val norm_eq = normalize_minus_assoc_l ac_info (cert ctxt t)
      val t' = rhs_of norm_eq
      fun process_inst ((id', env'), eq_th) =
          let
            val norm_eq' = subst_thm_thy thy env' norm_eq
          in
            ((id', env'), transitive_list [norm_eq', eq_th])
          end
    in
      map process_inst (match_ac_head ac_info tbl bd_vars (t', u) (id, env))
    end

(* More commonly used external version. *)
fun rewrite_match_ac ac_info tbl = rewrite_match_ac_bd ac_info tbl []

(* pairs is a list of (at_head, (t, u)). Match the pairs in sequence,
   and return a list of ((id, inst), ths), where ths is the list of
   equalities t(env) == u.
 *)
fun rewrite_match_list tbl pairs instsp =
    case pairs of
        [] => [(instsp, [])]
      | (at_head, (t, u)) :: pairs' =>
        let
          val insts_t = rewrite_match_gen at_head tbl [] (t, u) instsp
          fun process_inst_t (instsp', th) =
              let
                val insts_ts' = rewrite_match_list tbl pairs' instsp'
              in
                map (apsnd (cons th)) insts_ts'
              end
        in
          maps process_inst_t insts_t
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

fun pre_match_comb tbl (t, u) =
    let
      val (tf, targs) = Term.strip_comb t
      val (uf, uargs) = Term.strip_comb u
    in
      is_Var tf orelse (Term.aconv_untyped (tf, uf) andalso
                        length targs = length uargs andalso
                        forall (pre_match tbl) (targs ~~ uargs))
    end

and pre_match_non_ac_head tbl (t, u) =
    case (t, u) of
        (Var ((nm, _), T), _) =>
        if Term.is_open u then false
        else if not (pre_match_type tbl (T, fastype_of u)) then false
        else if nm = "NUMC" orelse nm = "NUMCu" then is_numc u
        else if nm = "FREE" then Term.is_Free u
        else true
      | (Free (a, T), Free (b, U)) =>
        (a = b andalso pre_match_type tbl (T, U))
      | (Const (a, T), Const (b, U)) =>
        (a = b andalso pre_match_type tbl (T, U))
      | (_ $ _, _) => pre_match_comb tbl (t, u)
      | _ => false

and pre_match_unit ac_info tbl (t, u) =
    if not (ACUtil.head_agrees ac_info t) then false
    else let
      val (_, (A, B)) = dest_binop t
    in
      if is_unit_allowed_var A then pre_match tbl (B, u)
      else if is_unit_allowed_var B then pre_match tbl (A, u)
      else false
    end

and pre_match_all_head tbl (t, u) =
    let
      val thy = RewriteTable.theory_of tbl
      val tyinst = Sign.typ_match thy (fastype_of t, fastype_of u) Vartab.empty
      val t' = Envir.subst_term_types tyinst t
    in
      case RewriteTable.get_head_ac_info_with_inv tbl t' of
          NONE =>
          if Term.is_open u then pre_match_non_ac_head tbl (t', u)
          else let
            val u_equivs =
                (RewriteTable.get_head_equiv_with_t tbl ([], u) t')
                    |> map snd |> map rhs_of
          in
            exists (fn u' => pre_match_non_ac_head tbl (t', u')) u_equivs
          end
        | SOME ac_info =>
          if Term.is_open u then ACUtil.head_agrees_with_inv ac_info u
          else let
            val u_ac_equivs = get_ac_head_equiv tbl ac_info ([], u)
          in
            pre_match_unit ac_info tbl (t', u) orelse length u_ac_equivs > 0
          end
    end
    handle Type.TYPE_MATCH => false

and pre_match (tbl as {ctxt, ...}) (t, u) =
    case (t, u) of
        (Var ((nm, _), T), _) =>
        if Term.is_open u then false
        else if not (pre_match_type tbl (T, fastype_of u)) then false
        else if member (op =) ["NUMC", "NUMCu", "FREE"] nm then
          pre_match_all_head tbl (t, u)
        else true
      | (Abs (_, T, t'), Abs (nm, U, u')) =>
        if not (pre_match_type tbl (T, U)) then false
        else pre_match tbl (subst_bound (Free (nm, T), t'),
                            subst_bound (Free (nm, U), u'))
      | (Abs _, _) => (
        pre_match tbl (t, rhs_of (reverse_eta_conv ctxt (cert ctxt u)))
        handle CTERM _ => false)
      | (_, Abs _) => (
        let val u' = rhs_of (Thm.eta_conversion (cert ctxt u)) in
          if u aconv u' then false else pre_match tbl (t, u')
        end)
      | (Bound i, Bound j) => (i = j)
      | (_, _) => pre_match_all_head tbl (t, u)

fun pre_match_head tbl (t, u) =
    let
      val thy = RewriteTable.theory_of tbl
      val tyinst = Sign.typ_match thy (fastype_of t, fastype_of u) Vartab.empty
      val t' = Envir.subst_term_types tyinst t
    in
      case RewriteTable.get_head_ac_info_with_inv tbl t' of
          NONE => pre_match_non_ac_head tbl (t', u)
        | SOME {cfhead, uinv_op, inv_op, ...} =>
          (* head of u agrees with ac_info, up to types. *)
          member Term.aconv_untyped [Thm.term_of cfhead, uinv_op, inv_op]
                 (Term.head_of u)
    end
    handle Type.TYPE_MATCH => false

(* Counts the number of literal AC matches in t. The second argument
   is the list of schematic variables that are already instantiated.
 *)
fun literal_ac_count thy t inst_vars =
    case ACUtil.get_head_ac_info_with_inv thy t of
        NONE =>
        let
          val (_, args) = Term.strip_comb t
        in
          literal_ac_count_list thy args inst_vars
        end
      | SOME ac_info =>
        let
          val targs = t |> cert_thy thy |> normalize_minus_assoc_l ac_info
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
      val _ = assert (is_pattern (HOLogic.mk_tuple [t1, t2]))
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
