(* Current state, function for modifying the goal. *)

type auto2_frame = {goals: (term * thm) list,
                    selected: int option,
                    induct_stmt: term option,
                    prem_only: term list,
                    after_qed: (term list * (thm list -> thm -> thm)) option}

type auto2_state = auto2_frame list

signature AUTO2_STATE =
sig
  val print_state: Proof.context -> unit
  val get_num_frame: Proof.context -> int
  val pop_head: Proof.context -> Proof.context
  val push_head: auto2_frame -> Proof.context -> Proof.context
  val simple_frame:
      cterm * (term list * (thm list -> thm -> thm)) option -> auto2_frame
  val multiple_frame:
      (term * cterm) list * (term list * (thm list -> thm -> thm)) option -> auto2_frame
  val map_head_th: (thm -> thm) -> Proof.context -> Proof.context
  val set_head_th: thm -> Proof.context -> Proof.context
  val set_selected: int option -> Proof.context -> Proof.context
  val set_induct_stmt: term -> Proof.context -> Proof.context
  val get_last_induct_stmt: Proof.context -> term option
  val add_prem_only: term -> Proof.context -> Proof.context
  val lookup_prem_only: Proof.context -> term -> bool
  val get_head: Proof.context -> auto2_frame
  val get_selected: Proof.context -> thm
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
fun string_of_frame ctxt frame =
    let
      val {goals, selected, ...} = frame
      val n = length goals
      fun print_i (i, (pat, th)) =
          (if selected = SOME i then "*" else " ") ^
          (pat |> Syntax.string_of_term ctxt) ^ ": " ^
          (th |> Thm.prop_of |> Syntax.string_of_term ctxt)
    in
      if n = 1 then
        goals |> the_single |> snd |> Thm.prop_of |> Syntax.string_of_term ctxt
      else cat_lines (map print_i (0 upto (n - 1) ~~ goals))
    end

fun string_of_state ctxt =
    let
      val frames = Data.get ctxt
      val _ = tracing ("Auto2 state. Number of frames is " ^
                       (string_of_int (length frames)))
    in
      cat_lines (map (string_of_frame ctxt) frames)
    end

fun print_state ctxt = tracing (string_of_state ctxt)

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

fun simple_frame (ct, after_qed) =
    {goals = [(Thm.term_of ct, Goal.protect 1 (Thm.trivial ct))],
     selected = SOME 0, induct_stmt = NONE, prem_only = [],
     after_qed = after_qed}

fun multiple_frame (goals, after_qed) =
    {goals = map (apsnd (Goal.protect 1 o Thm.trivial)) goals,
     selected = NONE, induct_stmt = NONE, prem_only = [], after_qed = after_qed}

(* Change the proof state at the head of the auto2 state. *)
fun map_head f =
    Data.map (fn frames =>
         case frames of
             [] => error "map_head"
           | frame :: rest => f frame :: rest)
  
fun map_frame_th f frame =
  let
    val {goals, selected, induct_stmt, prem_only, after_qed} = frame
  in
    case selected of
      NONE => raise Fail "map_frame_th: no proposition selected"
    | SOME i =>
      if i < 0 orelse i >= length goals then
        raise Fail "map_frame_th: unexpected selected"
      else
        {goals = nth_map i (apsnd f) goals,
         selected = selected, induct_stmt = induct_stmt, prem_only = prem_only,
         after_qed = after_qed}
  end
      
fun map_head_th f = map_head (map_frame_th f)

fun set_head_th th = map_head_th (K th)

fun set_selected sel =
    map_head (
      fn {goals, induct_stmt, prem_only, after_qed, ...} =>
         {goals = goals, selected = sel, induct_stmt = induct_stmt,
          prem_only = prem_only, after_qed = after_qed})

fun set_induct_stmt stmt =
    map_head (
      fn {goals, selected, prem_only, after_qed, ...} =>
         {goals = goals, selected = selected, induct_stmt = SOME stmt,
          prem_only = prem_only, after_qed = after_qed})

fun get_last_induct_stmt ctxt =
    let
      val frames = Data.get ctxt
    in
      get_first #induct_stmt (rev frames)
    end

fun add_prem_only stmt =
    map_head (
      fn {goals, selected, induct_stmt, prem_only, after_qed} =>
         {goals = goals, selected = selected, induct_stmt = induct_stmt,
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
fun get_selected ctxt =
    let
      val {goals, selected, ...} = get_head ctxt
    in
      case selected of
          NONE => raise Fail "get_selected: no goal is selected."
        | SOME i => snd (nth goals i)
    end

fun subgoal_of prop =
    prop |> Thm.cprop_of |> Drule.strip_imp_prems |> the_single
    handle List.Empty => error "subgoal_of"

end  (* structure Auto2_State *)
