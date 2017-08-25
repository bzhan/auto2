(* Difference logic on natural numbers. *)

type order_table =
     {resolved: (box_id * thm) list,
      graph: (box_id * thm) list Termtab.table Termtab.table,
      inv_graph: (box_id * thm) list Termtab.table Termtab.table}

type ineq_info = term * term * int

signature NAT_ORDER =
sig
  val eq_info: (box_id * thm) * (box_id * thm) -> bool

  val is_plus: term -> bool
  val is_plus_const: term -> bool
  val is_standard_ineq: term -> bool
  val dest_ineq: term -> ineq_info
  val is_refl_ineq: thm -> bool
  val ineq_is_better: ineq_info -> ineq_info -> bool
  val info_is_better: box_lattice -> box_id * thm -> box_id * thm -> bool

  val is_box_resolved: box_lattice -> order_table -> box_id -> bool
  val ineq_to_contradiction: thm -> thm
  val add_resolved: box_id * thm -> order_table -> order_table
  val retrieve_ineqs: order_table -> term * term -> (box_id * thm) list
  val contains_info: box_lattice -> order_table -> box_id * thm -> bool
  val add_ineq_raw: box_lattice -> box_id * thm -> order_table -> order_table
  val print_ord_info: Proof.context -> box_id * thm -> string
  val print_ineq_table: Proof.context -> order_table -> unit

  val retrieve_ineqs_left: order_table -> term -> (box_id * thm) list
  val retrieve_ineqs_right: order_table -> term -> (box_id * thm) list
  val combine_ineqs: thm -> thm -> thm
  val combine_ineq_infos:
      box_lattice -> box_id * thm -> box_id * thm -> box_id * thm
  val add_ineq: box_lattice -> box_id * thm -> order_table -> order_table

  val norm_ineq_th: thm -> thm
  val add_ineq_general: box_lattice -> box_id * thm -> order_table -> order_table

  val derive_contradiction: order_table -> thm -> (box_id * thm) list
  val justify_neg_ineq: order_table -> cterm -> (box_id * thm) list
  val justify_ineq: order_table -> cterm -> (box_id * thm) list
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

(* Check whether t is in the form a + b. *)
fun is_plus t =
    case t of
        Const (@{const_name plus}, _) $ _ $ _ => true
      | _ => false

(* Check whether t is in the form a - b. *)
fun is_minus t =
    case t of
        Const (@{const_name minus}, _) $ _ $ _ => true
      | _ => false

(* Check whether t is in the form a + n, where n is a constant. *)
fun is_plus_const t =
    is_plus t andalso UtilArith.is_numc (dest_arg t)

(* Check whether t is in the form a - n, where n is a constant. *)
fun is_minus_const t =
    is_minus t andalso UtilArith.is_numc (dest_arg t)

(* Check whether t is in the form a <= b (boolean value). *)
fun is_less_eq t =
    case t of
        Const (@{const_name less_eq}, _) $ _ $ _ => true
      | _ => false

(* Check whether t is in the form a < b (boolean value). *)
fun is_less t =
    case t of
        Const (@{const_name less}, _) $ _ $ _ => true
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
        ((is_plus_const lhs andalso not (is_plus_const rhs)) orelse
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

(* Whether the given theorem is x + n <= x or x <= x + n (either a
   contradiction or is trivial).
 *)
fun is_refl_ineq th =
    let
      val (x, y, _) = dest_ineq (prop_of' th)
    in
      x aconv y
    end

(* Whether the first inequality is better than the second. *)
fun ineq_is_better (x1, y1, d1) (x2, y2, d2) =
    x1 aconv x2 andalso y1 aconv y2 andalso d1 <= d2

(* Comparison between two (id, th) pairs. *)
fun info_is_better lat (id1, th1) (id2, th2) =
    BoxID.is_eq_ancestor lat id1 id2 andalso
    ineq_is_better (dest_ineq (prop_of' th1)) (dest_ineq (prop_of' th2))

(* Whether the current id is resolved according to the list of
   resolved ids maintained in ord_tbl.
 *)
fun is_box_resolved lat ord_tbl id =
    let
      val {resolved, ...} = ord_tbl
    in
      exists (BoxID.is_eq_descendent lat id) (map fst resolved)
    end

(* Given an inequality of the form x + n <= x, where n > 0, return the
   theorem False.
 *)
fun ineq_to_contradiction th =
    let
      val (_, _, d) = dest_ineq (prop_of' th)
    in
      [Nat_Arith.nat_less_th 0 (~d), th] MRS @{thm single_resolve}
    end

(* Add a new resolved id (with proof) to the table. *)
fun add_resolved (id, th) ord_tbl =
    let
      val {resolved, graph, inv_graph} = ord_tbl
      val (x, y, d) = dest_ineq (prop_of' th)
      val _ = assert (x aconv y andalso d < 0) "add_resolved"
    in
      {resolved = (id, ineq_to_contradiction th) :: resolved,
       graph = graph, inv_graph = inv_graph}
    end

(* Returns the best inequalities between x and y. *)
fun retrieve_ineqs ord_tbl (x, y) =
    let
      val {graph, ...} = ord_tbl
    in
      case Termtab.lookup graph x of
          NONE => []
        | SOME subtbl => Termtab.lookup_list subtbl y
    end

(* Whether the table already contains the given inequality between x
   and y.
 *)
fun contains_info lat ord_tbl (id, th) =
    if is_box_resolved lat ord_tbl id then true
    else let
      val (x, y, d) = dest_ineq (prop_of' th)
    in
      if x aconv y then d >= 0
      else let
        val ineqs = retrieve_ineqs ord_tbl (x, y)
      in
        exists (fn info => info_is_better lat info (id, th)) ineqs
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
fun add_ineq_raw lat (id, th) ord_tbl =
    let
      val (x, y, _) = dest_ineq (prop_of' th)
      val _ = assert (not (x aconv y)) "add_ineq_raw: x = y"
      val ineqs = retrieve_ineqs ord_tbl (x, y)
      val extra_ineqs = filter (info_is_better lat (id, th)) ineqs
      val {resolved, graph, inv_graph} = ord_tbl
    in
      if exists (fn (id', th') =>
                    info_is_better lat (id', th') (id, th)) ineqs then
        ord_tbl
      else
        {resolved = resolved,
         graph = graph |> add_edge (x, y) (id, th)
                       |> fold (remove_edge (x, y)) extra_ineqs,
         inv_graph = inv_graph |> add_edge (y, x) (id, th)
                               |> fold (remove_edge (y, x)) extra_ineqs}
    end

fun print_ord_info ctxt (id, th) =
    "(" ^ (string_of_box_id id) ^ ", " ^
    (th |> prop_of' |> Syntax.string_of_term ctxt) ^ ")"

(* Print the current table of inequalties. *)
fun print_ineq_table ctxt ord_tbl =
    let
      val {graph, ...} = ord_tbl
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
fun retrieve_ineqs_left ord_tbl x =
    let
      val {graph, ...} = ord_tbl
    in
      case Termtab.lookup graph x of
          NONE => []
        | SOME subtbl => maps snd (Termtab.dest subtbl)
    end

(* Retrieve all inequalities whose right side is y. *)
fun retrieve_ineqs_right ord_tbl y =
    let
      val {inv_graph, ...} = ord_tbl
    in
      case Termtab.lookup inv_graph y of
          NONE => []
        | SOME subtbl => maps snd (Termtab.dest subtbl)
    end

(* Combine two inequalities. *)
fun combine_ineqs th1 th2 =
    let
      val (_, y1, d1) = dest_ineq (prop_of' th1)
      val (x2, _, d2) = dest_ineq (prop_of' th2)
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
fun combine_ineq_infos lat (id1, th1) (id2, th2) =
    (BoxID.merge_boxes lat (id1, id2), combine_ineqs th1 th2)

(* Add the given inequality to the table. Propagate consequences. *)
fun add_ineq lat (id, th) ord_tbl =
    let
      (* One step in the update process. *)
      fun update_step (to_process, ord_tbl) =
          case to_process of
              [] => ([], ord_tbl)
            | (id, th) :: rest =>
              if contains_info lat ord_tbl (id, th) then
                update_step (rest, ord_tbl)
              else if is_refl_ineq th then
                update_step (rest, add_resolved (id, th) ord_tbl)
              else let
                val (x, y, _) = dest_ineq (prop_of' th)
                val prev_ineqs = retrieve_ineqs_right ord_tbl x
                val next_ineqs = retrieve_ineqs_left ord_tbl y
                val new_ineqs =
                    map (fn info =>
                            combine_ineq_infos lat info (id, th)) prev_ineqs @
                    map (fn info =>
                            combine_ineq_infos lat (id, th) info) next_ineqs
              in
                update_step (new_ineqs @ rest,
                             add_ineq_raw lat (id, th) ord_tbl)
              end
    in
      snd (update_step ([(id, th)], ord_tbl))
    end

(* Normalize inequality to standard form. This function is able to
   process any theorem of the form a </<= b.
 *)
fun norm_ineq_th th =
    let
      val t = prop_of' th
      val _ = assert (is_less_eq t orelse is_less t) "norm_ineq_th"
      val (lhs, rhs) = Util.dest_binop_args t
    in
      if is_less_eq t then
        if is_plus_const lhs orelse is_plus_const rhs then th
        else if is_minus_const lhs then
          th RS @{thm norm_le_lminus}
        else if is_minus_const rhs then
          th RS @{thm norm_le_rminus}
        else
          th RS @{thm norm_le}
      else  (* is_less t *)
        if is_plus_const lhs then
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

(* Add any inequality in the form a </<= b to the table, by first
   converting to the normal form.
 *)
fun add_ineq_general lat (id, th) ord_tbl =
    add_ineq lat (id, norm_ineq_th th) ord_tbl

(* Deriving a contradiction from a normalized theorem using the
   table. Return a list of pairs (id, False).
 *)
fun derive_contradiction ord_tbl th =
    let
      val (x, y, d) = dest_ineq (prop_of' th)
      val ineqs = retrieve_ineqs ord_tbl (y, x)
      fun process_ineq (id, th') =
          let
            val (_, _, d') = dest_ineq (prop_of' th')
          in
            if d + d' < 0 then
              [(id, ineq_to_contradiction (combine_ineqs th th'))]
            else
              []
          end
    in
      maps process_ineq ineqs
    end

(* Given cterm in the form ~(a </<= b), attempt to justify it using
   the table.
 *)
fun justify_neg_ineq ord_tbl ct =
    let
      val ct' = ct |> UtilLogic.get_cneg
                   |> UtilLogic.mk_cTrueprop
      val infos = ct' |> Thm.assume |> norm_ineq_th
                      |> derive_contradiction ord_tbl
      fun process_info (id, th) =
          (id, th |> Thm.implies_intr ct'
                  |> rewrite_thm_from_contra_form)
    in
      map process_info infos
    end

(* Given cterm in the form a </<= b, attempt to justify it using the
   table. This works by first converting the theorem into the form ~(b
   </<= a).
 *)
fun justify_ineq ord_tbl ct =
    let
      val t = Thm.term_of ct

      val eq = if is_less t then
                 rewr_obj_eq (obj_sym @{thm linorder_not_le}) ct
               else
                 rewr_obj_eq (obj_sym @{thm linorder_not_less}) ct
      val infos = justify_neg_ineq ord_tbl (Thm.rhs_of eq)

      fun process_info (id, th) =
          (id, apply_to_thm' (Conv.rewr_conv (Util.meta_sym eq)) th)
    in
      map process_info infos
    end

end  (* NatOrder *)
