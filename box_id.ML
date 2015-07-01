(* Definition and functions on box_id. *)

signature BOXID =
sig
  type box_id
  val string_of_box_id: box_id -> string

  type box_lattice
  val empty: box_lattice
  val get_focus: box_lattice -> box_id
  val set_focus: box_id -> box_lattice -> box_lattice
  val num_prim_id: box_lattice -> int
  val get_parent_prim: box_lattice -> int -> box_id
  val get_ancestors_prim: box_lattice -> box_id -> int list
  val get_extras_prim: box_lattice -> box_id -> int list
  val reduce_box_id: box_lattice -> int list -> box_id
  val get_parent_at_i: box_lattice -> box_id -> int -> box_id
  val merge_boxes: box_lattice -> box_id * box_id -> box_id
  val get_all_merges: box_lattice -> box_id list list -> box_id list
  val is_eq_ancestor: box_lattice -> box_id -> box_id -> bool
  val is_eq_descendent: box_lattice -> box_id -> box_id -> bool
  val is_ancestor: box_lattice -> box_id -> box_id -> bool
  val is_descendent: box_lattice -> box_id -> box_id -> bool
  val is_box_resolved: box_lattice -> box_id -> bool
  val is_box_unresolved: box_lattice -> box_id -> bool
  val is_box_supported: box_lattice -> box_id -> bool
  val add_prim_id: box_id -> box_lattice -> int * box_lattice
  val add_resolved: box_id -> box_lattice -> box_lattice
end;

structure BoxID : BOXID =
struct

type box_id = int list
fun string_of_box_id id =
    if length id = 1 then string_of_int (hd id)
    else "(" ^ commas (map string_of_int id) ^ ")"
structure Boxidtab = Table (type key = box_id val ord = list_ord int_ord)

type box_lattice = {
  parents: box_id Inttab.table,
  focus: box_id,
  resolved: box_id list
}

val empty = {parents = Inttab.empty, focus = [], resolved = []}

fun get_focus {focus, ...} = focus
fun set_focus foc {parents, focus = _, resolved} =
    {parents = parents, focus = foc, resolved = resolved}

fun num_prim_id {parents, ...} = length (Inttab.keys parents)

fun get_parent_prim {parents, ...} prim_id = the (Inttab.lookup parents prim_id)

(* Returns the list of primitive ancestors of id. Result may not be in
   order.
 *)
fun get_ancestors_prim {parents, ...} id =
    let
      fun helper all_ids cur_ids =
          let
            val new_ids =
                (maps (fn id => the (Inttab.lookup parents id)) cur_ids)
                    |> distinct (op =) |> subtract (op =) all_ids
          in
            if length new_ids = 0 then all_ids
            else helper (all_ids @ new_ids) new_ids
          end
    in
      helper id id
    end

(* Returns the list of primitive ancestors of id that are not also
   primitive ancestors of focus. Result may not be in order.
 *)
fun get_extras_prim (lat as {focus, ...}) id =
    subtract (op =) (get_ancestors_prim lat focus) (get_ancestors_prim lat id)

(* For any {a, b} in ids where a is an ancestor of b, remove a from
   ids. Assume input is in order. Output is a valid box_id.
 *)
fun reduce_box_id lat prim_lst =
    let
      fun helper taken rest =
          case rest of
              [] => taken
            | cur :: rest' =>
              let val cur_ancestors = get_ancestors_prim lat [cur]
              in helper (cur :: subtract (op =) cur_ancestors taken) rest' end
    in
      rev (helper [] prim_lst)
    end

(* Given two ordered lists of integers without duplicates, merge them
   into a sorted list (the merge part of mergesort).
 *)
fun ordered_merge ms ns =
    case (ms, ns) of
        ([], _) => ns
      | (_, []) => ms
      | (m :: ms', n :: ns') =>
        if m < n then m :: ordered_merge ms' ns
        else if n < m then n :: ordered_merge ms ns'
        else m :: ordered_merge ms' ns'

(* Returns box_id of the immediate parent coming from expanding the
   parent of the ith primitive id in the current box_id.
 *)
fun get_parent_at_i lat id i =
    reduce_box_id lat (ordered_merge (nth_drop i id)
                                     (get_parent_prim lat (nth id i)))

(* Merge two generalized boxes. *)
fun merge_boxes lat (id1, id2) =
    let
      val merged = ordered_merge id1 id2
      val merged_len = length merged
    in
      if merged_len = length id1 then id1
      else if merged_len = length id2 then id2
      else reduce_box_id lat merged
    end

(* Returns list of ids that are all possible intersections of subsets
   of ids.
 *)
fun get_all_merges lat id_lsts =
    let
      fun merge2 ids1 ids2 =
          maps (fn id1 => map (fn id2 => merge_boxes lat (id1, id2)) ids2) ids1
               |> distinct (op =)
    in
      fold merge2 id_lsts [[]]
    end

(* Returns whether id is an ancestor / descendent of id'. *)
fun is_eq_ancestor lat id id' = (id' = merge_boxes lat (id, id'))
fun is_eq_descendent lat id id' = (id = merge_boxes lat (id, id'))
fun is_ancestor lat id id' = id <> id' andalso is_eq_ancestor lat id id'
fun is_descendent lat id id' = id <> id' andalso is_eq_descendent lat id id'

fun is_box_resolved (lat as {resolved, ...}) id =
    exists (is_eq_descendent lat id) resolved
val is_box_unresolved = not oo is_box_resolved

fun is_box_supported lat id =
    forall (fn prim_id => is_box_unresolved lat [prim_id]) id

fun add_prim_id parent_id {parents, focus, resolved} =
    let
      val prim_id = length (Inttab.keys parents)
      val parents' = Inttab.update_new (prim_id, parent_id) parents
    in
      (prim_id, {parents = parents', focus = focus, resolved = resolved})
    end

fun add_resolved id (lat as {parents, focus, resolved}) =
    {parents = parents, focus = focus,
     resolved = if exists (is_eq_descendent lat id) resolved then resolved
                else id :: filter_out (is_eq_ancestor lat id) resolved}

end  (* structure BoxID *)

structure Boxidtab = Table (type key = BoxID.box_id val ord = list_ord int_ord)
