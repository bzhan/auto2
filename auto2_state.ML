(* Current state, function for modifying the goal. *)

type auto2_frame = {prop: thm,
                    induct_stmt: term option,
                    prem_only: term list,
                    after_qed: (term list * (thm -> thm -> thm)) option}

type auto2_state = auto2_frame list

signature AUTO2_STATE =
sig
  val print_state: Proof.context -> unit
  val get_num_frame: Proof.context -> int
  val pop_head: Proof.context -> Proof.context
  val push_head: auto2_frame -> Proof.context -> Proof.context
  val map_head: (auto2_frame -> auto2_frame) -> Proof.context -> Proof.context
  val map_head_th: (thm -> thm) -> Proof.context -> Proof.context
  val set_head_th: thm -> Proof.context -> Proof.context
  val set_induct_stmt: term -> Proof.context -> Proof.context
  val add_prem_only: term -> Proof.context -> Proof.context
  val lookup_prem_only: Proof.context -> term -> bool
  val get_head: Proof.context -> auto2_frame
  val subgoal_of: thm -> cterm
end;

structure Auto2_State : AUTO2_STATE =
struct

structure Data = Proof_Data
(
  type T = auto2_state
  fun init _ = []
)

(* Print the auto2 state. *)
fun print_state ctxt =
    let
      val frames = Data.get ctxt
      val _ = tracing ("Auto2 state. Number of frames is " ^
                       (string_of_int (length frames)))
      val _ = map (trace_thm_ctxt ctxt "prop:") (map #prop frames)
    in
      ()
    end

fun get_num_frame ctxt = length (Data.get ctxt)

(* Remove the head (innermost layer) of auto2 state. *)
val pop_head =
    Data.map (fn frames =>
         case frames of
             [] => error "pop_head"
           | _ :: rest => rest)

(* Push a head layer of auto2 state. *)
fun push_head frame =
    Data.map (cons frame)

(* Change the proof state at the head of the auto2 state. *)
fun map_head f =
    Data.map (fn frames =>
         case frames of
             [] => error "map_head"
           | frame :: rest => f frame :: rest)

fun map_head_th f =
    map_head (
      fn {prop, induct_stmt, prem_only, after_qed} =>
         {prop = f prop, induct_stmt = induct_stmt, prem_only = prem_only,
          after_qed = after_qed})

fun set_head_th th = map_head_th (K th)

fun set_induct_stmt stmt =
    map_head (
      fn {prop, prem_only, after_qed, ...} =>
         {prop = prop, induct_stmt = SOME stmt, prem_only = prem_only,
          after_qed = after_qed})

fun add_prem_only stmt =
    map_head (
      fn {prop, induct_stmt, prem_only, after_qed} =>
         {prop = prop, induct_stmt = induct_stmt,
          prem_only = stmt :: prem_only, after_qed = after_qed})

fun lookup_prem_only ctxt t =
    let
      val prem_only = maps #prem_only (Data.get ctxt)
    in
      member (op aconv) prem_only t
    end

fun get_head ctxt =
    case Data.get ctxt of
      [] => raise Fail "Auto2 proof should start with @begin keyword"
    | st :: _ => st

(* Given proof state of form A ==> C (with only one subgoal A), return A *)
fun subgoal_of prop =
    prop |> Thm.cprop_of |> Drule.strip_imp_prems |> the_single
    handle List.Empty => error "subgoal_of"

end  (* structure Auto2_State *)
