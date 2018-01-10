(* Difference logic on natural numbers. *)

type order_table =
     {resolved: (box_id * thm) list,
      graph: (box_id * thm) list Termtab.table Termtab.table,
      inv_graph: (box_id * thm) list Termtab.table Termtab.table}

type ineq_info = term * term * int

signature NAT_ORDER =
sig
  val eq_info: (box_id * thm) * (box_id * thm) -> bool

  val is_plus_const: term -> bool
  val is_minus_const: term -> bool
  val is_standard_ineq: term -> bool
  val dest_ineq: term -> ineq_info
  val dest_ineq_th: thm -> ineq_info
  val is_refl_ineq: thm -> bool
  val ineq_is_better: ineq_info -> ineq_info -> bool
  val info_is_better: Proof.context -> box_id * thm -> box_id * thm -> bool

  val is_box_resolved: Proof.context -> box_id -> bool
  val ineq_to_contradiction: thm -> thm
  val add_resolved: box_id * thm -> Proof.context -> Proof.context
  val retrieve_ineqs: Proof.context -> term * term -> (box_id * thm) list
  val contains_info: Proof.context -> box_id * thm -> bool
  val add_ineq_raw: box_id * thm -> Proof.context -> Proof.context
  val print_ord_info: Proof.context -> box_id * thm -> string
  val print_ineq_table: Proof.context -> unit

  val retrieve_ineqs_left: Proof.context -> term -> (box_id * thm) list
  val retrieve_ineqs_right: Proof.context -> term -> (box_id * thm) list
  val combine_ineqs: thm -> thm -> thm
  val combine_ineq_infos:
      Proof.context -> box_id * thm -> box_id * thm -> box_id * thm
  val add_ineq: box_id * thm -> Proof.context -> Proof.context

  val norm_ineq_th': thm -> thm
  val convert_const_x: thm -> thm
  val convert_const_y: thm -> thm
  val norm_ineq_th: thm -> thm
  val norm_ineq_minus_th': thm -> thm option
  val norm_ineq_minus_th: thm -> thm option
  val add_ineq_general: box_id * thm -> Proof.context -> Proof.context

  val derive_contradiction: Proof.context -> thm -> (box_id * thm) list
  val justify_neg_ineq: Proof.context -> term -> (box_id * thm) list
  val justify_ineq: Proof.context -> term -> (box_id * thm) list

  val setup_nat_order: theory -> theory
end;

structure NatOrder : NAT_ORDER =
struct

structure Data = Proof_Data
(
  type T = order_table
  fun init _ = {resolved = [], graph = Termtab.empty, inv_graph = Termtab.empty}
)

(* Compare two infos. *)
fun eq_info ((id, th), (id', th')) =
    id = id' andalso Thm.eq_thm_prop (th, th')

(* Check whether t is in the form a + n, where n is a constant. *)
fun is_plus_const t =
    UtilArith.is_plus t andalso UtilArith.is_numc (dest_arg t)

(* Check whether t is in the form a - n, where n is a constant. *)
fun is_minus_const t =
    UtilArith.is_minus t andalso UtilArith.is_numc (dest_arg t)

(* Check whether t is in the form a <= b (boolean value). *)
fun is_less_eq t =
    case t of
        Const (@{const_name less_eq}, _) $ lhs $ _ => fastype_of lhs = natT
      | _ => false

(* Check whether t is in the form a < b (boolean value). *)
fun is_less t =
    case t of
        Const (@{const_name less}, _) $ lhs $ _ => fastype_of lhs = natT
      | _ => false

(* Check whether t is an inequality in the standard form. In this
   form, t is in the form a <= b, where a and b are natural numbers,
   and at least one of them is in the form x + n, where n is a
   constant.
 *)
fun is_standard_ineq t =
    if is_less_eq t then
      let
        val (lhs, rhs) = Util.dest_binop_args t
      in
        fastype_of lhs = natT andalso
        ((is_plus_const lhs andalso not (is_plus_const rhs) andalso
          UtilArith.dest_numc (dest_arg lhs) > 0) orelse
         (is_plus_const rhs andalso not (is_plus_const lhs)))
      end
    else false

(* Assume t is in the form x + n <= y or x <= y + n, deconstruct into
   the triple (x, y, d), where d = -n in the first case and n in the
   second case.
 *)
fun dest_ineq t =
    let
      val _ = assert (is_standard_ineq t) "dest_ineq"
      val (lhs, rhs) = Util.dest_binop_args t
    in
      if is_plus_const lhs then
        (dest_arg1 lhs, rhs, ~ (UtilArith.dest_numc (dest_arg lhs)))
      else
        (lhs, dest_arg1 rhs, UtilArith.dest_numc (dest_arg rhs))
    end

fun dest_ineq_th th =
    if UtilLogic.is_Trueprop (Thm.prop_of th) andalso
       is_standard_ineq (prop_of' th) then
      dest_ineq (prop_of' th)
    else let
      val _ = trace_thm_global "th:" th
    in
      raise Fail "dest_ineq_th"
    end

(* Whether the given theorem is x + n <= x or x <= x + n (either a
   contradiction or is trivial).
 *)
fun is_refl_ineq th =
    let
      val (x, y, _) = dest_ineq_th th
    in
      x aconv y
    end

(* Whether the first inequality is better than the second. *)
fun ineq_is_better (x1, y1, d1) (x2, y2, d2) =
    x1 aconv x2 andalso y1 aconv y2 andalso d1 <= d2

(* Comparison between two (id, th) pairs. *)
fun info_is_better ctxt (id1, th1) (id2, th2) =
    BoxID.is_eq_ancestor ctxt id1 id2 andalso
    ineq_is_better (dest_ineq_th th1) (dest_ineq_th th2)

(* Whether the current id is resolved according to the list of
   resolved ids maintained in ord_tbl.
 *)
fun is_box_resolved ctxt id =
    let
      val {resolved, ...} = Data.get ctxt
    in
      exists (BoxID.is_eq_descendent ctxt id) (map fst resolved)
    end

(* Given an inequality of the form x + n <= x, where n > 0, return the
   theorem False.
 *)
fun ineq_to_contradiction th =
    let
      val (_, _, d) = dest_ineq_th th
      val _ = assert (d < 0) "ineq_to_contradiction"
    in
      [Nat_Arith.nat_less_th 0 (~d), th] MRS @{thm single_resolve}
    end

(* Add a new resolved id (with proof) to the table. *)
fun add_resolved (id, th) ctxt =
    let
      val {resolved, graph, inv_graph} = Data.get ctxt
      val (x, y, d) = dest_ineq_th th
      val _ = assert (x aconv y andalso d < 0) "add_resolved"
    in
      Data.map (K {resolved = (id, ineq_to_contradiction th) :: resolved,
                   graph = graph, inv_graph = inv_graph}) ctxt
    end

(* Returns the best inequalities between x and y. *)
fun retrieve_ineqs ctxt (x, y) =
    let
      val {graph, ...} = Data.get ctxt
    in
      case Termtab.lookup graph x of
          NONE => []
        | SOME subtbl => Termtab.lookup_list subtbl y
    end

(* Whether the table already contains the given inequality between x
   and y.
 *)
fun contains_info ctxt (id, th) =
    if is_box_resolved ctxt id then true
    else let
      val (x, y, d) = dest_ineq_th th
    in
      if x aconv y then d >= 0
      else let
        val ineqs = retrieve_ineqs ctxt (x, y)
      in
        exists (fn info => info_is_better ctxt info (id, th)) ineqs
      end
    end

fun add_edge (x, y) (id, th) graph =
    graph |> Termtab.map_default
          (x, Termtab.empty) (Termtab.cons_list (y, (id, th)))

fun remove_edge (x, y) (id, th) graph =
    graph |> Termtab.map_entry
          x (Termtab.remove_list eq_info (y, (id, th)))

(* Add the given inequality to the table. This version does not
   propagate consequences.
 *)
fun add_ineq_raw (id, th) ctxt =
    let
      val (x, y, d) = dest_ineq_th th
      val _ = assert (not (x aconv y)) "add_ineq_raw: x = y"
      val _ = assert (d < 10 andalso d > ~10) "add_ineq_raw: out of bounds"
      val ineqs = retrieve_ineqs ctxt (x, y)
      val extra_ineqs = filter (info_is_better ctxt (id, th)) ineqs
      val {resolved, graph, inv_graph} = Data.get ctxt
    in
      if exists (fn (id', th') =>
                    info_is_better ctxt (id', th') (id, th)) ineqs then
        ctxt
      else
        Data.map (K {resolved = resolved,
                     graph = graph |> add_edge (x, y) (id, th)
                                   |> fold (remove_edge (x, y)) extra_ineqs,
                     inv_graph = inv_graph |> add_edge (y, x) (id, th)
                                           |> fold (remove_edge (y, x)) extra_ineqs}) ctxt
    end

fun print_ord_info ctxt (id, th) =
    "(" ^ (BoxID.string_of_box_id id) ^ ", " ^
    (th |> prop_of' |> Syntax.string_of_term ctxt) ^ ")"

(* Print the current table of inequalties. *)
fun print_ineq_table ctxt =
    let
      val {graph, ...} = Data.get ctxt
      val ineqs = graph |> Termtab.dest |> map snd
                        |> maps Termtab.dest_list |> map snd
    in
      writeln (cat_lines (map (print_ord_info ctxt) ineqs))
    end

(* In expression x + n < y, fold n. *)
val fold_const_left =
    apply_to_thm' (Conv.arg1_conv (Conv.arg_conv Nat_Arith.nat_fold_conv))

(* In expression x < y + n, fold n. *)
val fold_const_right =
    apply_to_thm' (Conv.arg_conv (Conv.arg_conv Nat_Arith.nat_fold_conv))

(* Retrieve all inequalities whose left side is x. *)
fun retrieve_ineqs_left ctxt x =
    let
      val {graph, ...} = Data.get ctxt
    in
      case Termtab.lookup graph x of
          NONE => []
        | SOME subtbl => maps snd (Termtab.dest subtbl)
    end

(* Retrieve all inequalities whose right side is y. *)
fun retrieve_ineqs_right ctxt y =
    let
      val {inv_graph, ...} = Data.get ctxt
    in
      case Termtab.lookup inv_graph y of
          NONE => []
        | SOME subtbl => maps snd (Termtab.dest subtbl)
    end

(* Combine two inequalities. *)
fun combine_ineqs th1 th2 =
    let
      val (_, y1, d1) = dest_ineq_th th1
      val (x2, _, d2) = dest_ineq_th th2
      val _ = assert (y1 aconv x2) "combine_ineqs"
    in
      if d1 < 0 andalso d2 < 0 then
        ([th1, th2] MRS @{thm trans1}) |> fold_const_left
      else if d1 >= 0 andalso d2 >= 0 then
        ([th1, th2] MRS @{thm trans2}) |> fold_const_right
      else if d1 < 0 andalso d2 >= 0 then
        if d2 >= (~d1) then
          ([th1, th2] MRS @{thm trans3}) |> fold_const_right
        else  (* d2 < (~d1) *)
          ([Nat_Arith.nat_less_th d2 (~d1), th1, th2] MRS @{thm trans4})
              |> fold_const_left
      else  (* d1 >= 0 andalso d2 < 0 *)
        if d1 >= (~d2) then
          ([th1, th2] MRS @{thm trans5}) |> fold_const_right
        else
          ([Nat_Arith.nat_less_th d1 (~d2), th1, th2] MRS @{thm trans6})
              |> fold_const_left
    end

(* Combine two inequality infos. *)
fun combine_ineq_infos ctxt (id1, th1) (id2, th2) =
    (BoxID.merge_boxes ctxt (id1, id2), combine_ineqs th1 th2)

(* Add the given inequality to the table. Propagate consequences. *)
fun add_ineq (id, th) ctxt =
    let
      (* One step in the update process. *)
      fun update_step (to_process, ctxt) =
          case to_process of
              [] => ([], ctxt)
            | (id, th) :: rest =>
              if contains_info ctxt (id, th) then
                update_step (rest, ctxt)
              else if is_refl_ineq th then
                update_step (rest, add_resolved (id, th) ctxt)
              else let
                val (x, y, d) = dest_ineq_th th
              in
                if d >= 10 orelse d <= ~10 then update_step (rest, ctxt)
                else let
                  val prev_ineqs = retrieve_ineqs_right ctxt x
                  val next_ineqs = retrieve_ineqs_left ctxt y
                  val new_ineqs =
                      (map (fn info =>
                               combine_ineq_infos ctxt info (id, th)) prev_ineqs @
                       map (fn info =>
                               combine_ineq_infos ctxt (id, th) info) next_ineqs)
                          |> filter_out (contains_info ctxt)
                in
                  update_step (rest @ new_ineqs,
                               add_ineq_raw (id, th) ctxt)
                end
              end
    in
      snd (update_step ([(id, th)], ctxt))
    end

(* Normalize inequality to standard form. This function is able to
   process any theorem of the form a </<= b.
 *)
fun norm_ineq_th' th =
    let
      val t = prop_of' th
      val _ = assert (is_less_eq t orelse is_less t) "norm_ineq_th"
      val (lhs, rhs) = Util.dest_binop_args t
      val try_fold0 = Conv.try_conv (Conv.arg_conv Nat_Arith.nat_fold_conv0_right)
    in
      if is_less_eq t then
        if is_plus_const lhs andalso is_plus_const rhs then
          let
            val (lhs, rhs) = Util.dest_binop_args t
            val (n1, n2) = apply2 (UtilArith.dest_numc o dest_arg) (lhs, rhs)
          in
            if n1 <= n2 then
              (th RS @{thm reduce_le_plus_consts}) |> fold_const_right
            else
              ([Nat_Arith.nat_le_th n2 n1, th]
                   MRS @{thm reduce_le_plus_consts'}) |> fold_const_left
          end
        else if is_plus_const lhs then
          if UtilArith.dest_numc (dest_arg lhs) = 0 then
            th RS @{thm norm_le_lplus0}
          else th
        else if is_plus_const rhs then th
        else if is_minus_const lhs then
          th RS @{thm norm_le_lminus}
        else if is_minus_const rhs then
          th RS @{thm norm_le_rminus}
        else
          th RS @{thm norm_le}
      else  (* is_less t *)
        if is_plus_const lhs andalso is_plus_const rhs then
          let
            val (lhs, rhs) = Util.dest_binop_args t
            val (n1, n2) = apply2 (UtilArith.dest_numc o dest_arg) (lhs, rhs)
          in
            if n1 <= n2 then
              (th RS @{thm reduce_less_plus_consts}) |> fold_const_right
                                                     |> apply_to_thm' try_fold0
                                                     |> norm_ineq_th'
            else
              ([Nat_Arith.nat_le_th n2 n1, th]
                   MRS @{thm reduce_less_plus_consts'}) |> fold_const_left
                                                        |> norm_ineq_th'
          end
        else if is_plus_const lhs then
          (th RS @{thm norm_less_lplus}) |> fold_const_left
        else if is_plus_const rhs then
          (th RS @{thm norm_less_rplus}) |> fold_const_right
        else if is_minus_const lhs then
          (th RS @{thm norm_less_lminus}) |> fold_const_right
        else if is_minus_const rhs then
          (th RS @{thm norm_less_rminus}) |> fold_const_left
        else
          th RS @{thm norm_less}
    end

fun convert_const_x th =
    let
      val (x, _, d) = dest_ineq_th th
    in
      if UtilArith.is_numc x then
        let
          val xn = UtilArith.dest_numc x
        in
          if xn = 0 then th
          else if d < 0 then
            (th RS @{thm cv_const1}) |> fold_const_left
          else if d - xn < 0 then
            (th RS @{thm cv_const4}) |> fold_const_left
          else
            (th RS @{thm cv_const5}) |> fold_const_right
        end
      else th
    end

fun convert_const_y th =
    let
      val (_, y, d) = dest_ineq_th th
    in
      if UtilArith.is_numc y then
        let
          val yn = UtilArith.dest_numc y
        in
          if yn = 0 then th
          else if d < 0 andalso yn + d >= 0 then
            (th RS @{thm cv_const2}) |> fold_const_right
          else if d < 0 andalso yn + d < 0 then
            ([Nat_Arith.nat_less_th yn (~d), th] MRS @{thm cv_const3})
                |> fold_const_left
          else
            (th RS @{thm cv_const6}) |> fold_const_right
        end
      else th
    end

fun norm_ineq_th th =
    let
      val th' =
          th |> norm_ineq_th' |> convert_const_x |> convert_const_y
    in
      if is_standard_ineq (prop_of' th') then th'
      else let
        val _ = trace_thm_global "th':" th'
      in
        raise Fail "norm_ineq_th: invalid output."
      end
    end

fun norm_ineq_minus_th' th =
    let
      val t = prop_of' th
      val _ = assert (is_less_eq t orelse is_less t) "norm_ineq_minus_th"
      val (lhs, rhs) = Util.dest_binop_args t
    in
      if is_less_eq t then
        if is_minus_const lhs andalso not (is_plus_const rhs) then
          SOME (th RS @{thm norm_le})
        else if is_minus_const rhs andalso not (is_plus_const lhs) then
          SOME (th RS @{thm norm_le})
        else NONE
      else  (* is_less t *)
        if is_minus_const lhs andalso not (is_plus_const rhs) then
          SOME (th RS @{thm norm_less})
        else if is_minus_const rhs andalso not (is_plus_const lhs) then
          SOME (th RS @{thm norm_less})
        else NONE
    end

fun norm_ineq_minus_th th =
    case norm_ineq_minus_th' th of
        NONE => NONE
      | SOME th' =>
        let
          val th'' = th' |> convert_const_x |> convert_const_y
        in
          if is_standard_ineq (prop_of' th'') then SOME th''
          else let
            val _ = trace_thm_global "th'':" th''
          in
            raise Fail "norm_ineq_minus_th: invalid output."
          end
        end

(* Add any inequality in the form a </<= b to the table, by first
   converting to the normal form.
 *)
fun add_ineq_general (id, th) ctxt =
    let
      val t = prop_of' th
    in
      if is_less_eq t orelse is_less t then
        let
          val ctxt' = add_ineq (id, norm_ineq_th th) ctxt
        in
          ctxt'
        end
      else ctxt
    end

(* Deriving a contradiction from a normalized theorem using the
   table. Return a list of pairs (id, False).
 *)
fun derive_contradiction ctxt th =
    let
      val (x, y, d) = dest_ineq_th th
    in
      if x aconv y then
        if d < 0 then [([], ineq_to_contradiction th)] else []
      else let
        val ineqs = retrieve_ineqs ctxt (y, x)
        fun process_ineq (id, th') =
            let
              val (_, _, d') = dest_ineq_th th'
            in
              if d + d' < 0 then
                [(id, ineq_to_contradiction (combine_ineqs th th'))]
              else
                []
            end
      in
        maps process_ineq ineqs
      end
    end

(* Given cterm in the form ~(a </<= b), attempt to justify it using
   the table.
 *)
fun justify_neg_ineq ctxt t =
    let
      val ct' = t |> UtilLogic.get_neg
                  |> UtilLogic.mk_Trueprop |> Thm.cterm_of ctxt
      val infos = ct' |> Thm.assume |> norm_ineq_th
                      |> derive_contradiction ctxt
      fun process_info (id, th) =
          (id, th |> Thm.implies_intr ct'
                  |> apply_to_thm UtilLogic.rewrite_from_contra_form)
    in
      map process_info infos
    end

(* Given cterm in the form a </<= b, attempt to justify it using the
   table. This works by first converting the theorem into the form ~(b
   </<= a).
 *)
fun justify_ineq ctxt t =
    let
      val ct = Thm.cterm_of ctxt t
      val eq = if is_less t then
                 rewr_obj_eq (obj_sym @{thm linorder_not_le}) ct
               else
                 rewr_obj_eq (obj_sym @{thm linorder_not_less}) ct
      val infos = justify_neg_ineq ctxt (Util.rhs_of eq)

      fun process_info (id, th) =
          (id, apply_to_thm' (Conv.rewr_conv (Util.meta_sym eq)) th)
    in
      map process_info infos
    end

val null_ineq_matcher =
    let
      fun pre_match pat _ _ =
          is_less_eq pat orelse is_less pat

      fun match pat _ ctxt (id, inst) =
          if Util.has_vars pat then [] else
          if not (is_less_eq pat orelse is_less pat) then [] else
          let
            val infos = justify_ineq ctxt pat
            fun process_info (id', th) =
                ((BoxID.merge_boxes ctxt (id, id'), inst), th)
          in
            map process_info infos
          end
    in
      {pre_match = pre_match, match = match}
    end

fun ineq_to_eq_th th th' =
    let
      val (x, y, d) = dest_ineq_th th
      val (x', y', d') = dest_ineq_th th'
    in
      if x aconv y' andalso y aconv x' andalso d + d' = 0 then
        if d = 0 then
          [th, th'] MRS @{thm ineq_to_eqs1}
        else
          [th, th'] MRS @{thm Nat.le_antisym}
      else raise Fail "ineq_to_eq_th"
    end

(* For every edge from x to y, look for an edge from y to x that
   implies the equality between x and y (up to a constant factor).
 *)
fun get_new_eqs ctxt =
    let
      val {graph, ...} = Data.get ctxt
      val all_ineqs = graph |> Termtab.dest |> map snd |> maps Termtab.dest_list
                            |> map snd
      fun process_ineq (id, th) =
          let
            val (x, y, d) = dest_ineq_th th
            val ineqs = retrieve_ineqs ctxt (y, x)
            fun process_ineq' (id', th') =
                let
                  val (_, _, d') = dest_ineq_th th'
                in
                  if d + d' = 0 then
                    let
                      val eq_th = ineq_to_eq_th th th'
                      val id'' = BoxID.merge_boxes ctxt (id, id')
                      val (lhs, rhs) = Util.dest_binop_args (prop_of' eq_th)
                    in
                      if RewriteTable.is_equiv_t id'' ctxt (lhs, rhs) then []
                      else [(id'', eq_th)]
                    end
                  else []
                end
          in
            maps process_ineq' ineqs
          end
    in
      maps process_ineq all_ineqs
    end

fun nat_order_resolve_fn ictxt _ =
    let
      val ctxt = IncrContext.context_of ictxt
      val {resolved, ...} = Data.get ctxt
    in
      (get_new_eqs ctxt @ resolved)
          |> IncrContext.replace_id_for_type' ictxt
          |> map Update.thm_update
    end

val nat_order_resolve_prfstep =
    {name = "nat_order_resolve",
     args = [TypedMatch (TY_NULL, @{term_pat "A::bool"})],
     priority = PRIORITY_ADD,
     func = OneStep nat_order_resolve_fn}

fun match_fn ctxt t =
    if is_less_eq t orelse is_less t then justify_ineq ctxt t
    else []

fun resolve_fn ctxt =
    let
      val {resolved, ...} = Data.get ctxt
    in
      resolved
    end

fun add_rewrite_fn (id, th) ctxt =
    if fastype_of (Util.lhs_of th) <> natT then ctxt
    else let
      val infos = (th RS @{thm eq_to_ineqs})
                      |> UtilLogic.split_conj_th
                      |> map (pair id)
    in
      fold add_ineq_general infos ctxt
    end

fun clean_resolved id ctxt =
    let
      val {resolved, graph, inv_graph} = Data.get ctxt
      val filter_info = filter_out (BoxID.is_eq_ancestor ctxt id o fst)
      val resolved' = filter_info resolved
      val graph' =
          Termtab.map (fn _ => Termtab.map (fn _ => filter_info)) graph
      val inv_graph' =
          Termtab.map (fn _ => Termtab.map (fn _ => filter_info)) inv_graph
    in
      Data.map (K {resolved = resolved', graph = graph', inv_graph = inv_graph'}) ctxt
    end

val setup_nat_order =
    Auto2Data.add_custom_data (
      "nat_order",
      {add_term_fn = K I, add_rewrite_fn = add_rewrite_fn,
       add_fact_fn = add_ineq_general, match_fn = match_fn,
       resolve_fn = resolve_fn, clean_resolved = clean_resolved}

    ) #> fold ItemIO.add_prop_matcher [
      (TY_NULL, null_ineq_matcher)

    ] #> fold add_prfstep [
      nat_order_resolve_prfstep
    ]

end  (* NatOrder *)

(* val _ = Theory.setup NatOrder.setup_nat_order *)
