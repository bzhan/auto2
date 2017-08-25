(* Unit test for NatOrder *)

local

  val init = {resolved = [], graph = Termtab.empty, inv_graph = Termtab.empty}
  val ts = map (fn x => Free (x, natT)) ["u", "v", "w", "x", "y", "z"]
  val ctxt = fold Util.declare_free_term ts @{context}

in

fun add_ineq lat (id, str) =
    let
      val t = Syntax.read_term ctxt str
      val th = t |> mk_Trueprop |> Thm.cterm_of ctxt |> Thm.assume
    in
      NatOrder.add_ineq lat (id, th)
    end

fun add_ineq_general lat (id, str) =
    let
      val t = Syntax.read_term ctxt str
      val th = t |> mk_Trueprop |> Thm.cterm_of ctxt |> Thm.assume
    in
      NatOrder.add_ineq_general lat (id, th)
    end

val clear = K init

fun assert_info (id, str) ord_tbl =
    let
      val t = Syntax.read_term ctxt str
      val th = t |> mk_Trueprop |> Thm.cterm_of ctxt |> Thm.assume
      val (x, y, _) = NatOrder.dest_ineq t
      val ineqs = NatOrder.retrieve_ineqs ord_tbl (x, y)
    in
      if member NatOrder.eq_info ineqs (id, th) then ord_tbl else
      let
        val _ = tracing (NatOrder.print_ord_info ctxt (id, th) ^
                         " not found.")
                handle TERM _ => raise Fail "here"
      in
        raise Fail "assert_info"
      end
    end

fun assert_box_resolved lat id ord_tbl =
    if NatOrder.is_box_resolved lat ord_tbl id then ord_tbl else
    let
      val _ = tracing (string_of_box_id id ^ " not resolved.")
    in
      raise Fail "assert_box_resolved"
    end

fun assert_justify_ineq (id, str) ord_tbl =
    let
      val t = Syntax.read_term ctxt str
      val ct = Thm.cterm_of ctxt t
      val info =
          if is_neg t then NatOrder.justify_neg_ineq ord_tbl ct
          else NatOrder.justify_ineq ord_tbl ct
    in
      if length info = 1 andalso fst (the_single info) = id andalso
         prop_of' (snd (the_single info)) aconv t then ord_tbl else
      let
        val _ = tracing (string_of_box_id id ^ " " ^
                         (Syntax.string_of_term ctxt t))
      in
        raise Fail "assert_justify_ineq"
      end
    end

(* Basic non-contradictory case. *)
val test1 =
    let
      val lat = BoxID.empty
    in
      init |> add_ineq lat ([], "x <= y + 1")
           |> add_ineq lat ([], "y <= z + 1")
           |> add_ineq lat ([], "z <= x + 1")
           |> assert_info ([], "x <= y + 1")
           |> assert_info ([], "x <= z + 2")
           |> assert_info ([], "y <= z + 1")
           |> assert_info ([], "y <= x + 2")
           |> assert_info ([], "z <= x + 1")
           |> assert_info ([], "z <= y + 2")
    end

(* Basic contradictory case. *)
val test2 =
    let
      val lat = BoxID.empty
    in
      init |> add_ineq lat ([], "x <= y + 1")
           |> add_ineq lat ([], "y <= z + 2")
           |> add_ineq lat ([], "z + 4 <= x")
           |> assert_box_resolved lat []
    end

(* Basic test for adding general inequalities. *)
val test3 =
    let
      val lat = BoxID.empty
    in
      init |> add_ineq_general lat ([], "x <= y")
           |> assert_info ([], "x <= y + 0")
           |> clear
           |> add_ineq_general lat ([], "x < y")
           |> assert_info ([], "x + 1 <= y")
           |> clear
           |> add_ineq_general lat ([], "x < y + 1")
           |> assert_info ([], "x <= y + 0")
           |> clear
           |> add_ineq_general lat ([], "x + 1 < y")
           |> assert_info ([], "x + 2 <= y")
    end

(* Test of justifying inequalities. *)
val test4 =
    let
      val lat = BoxID.empty
    in
      init |> add_ineq lat ([], "x <= y + 3")
           |> assert_justify_ineq ([], "x <= y + 3")
           |> assert_justify_ineq ([], "x <= y + 4")
           |> assert_justify_ineq ([], "x < y + 4")
           |> assert_justify_ineq ([], "~(y + 3 < x)")
           |> assert_justify_ineq ([], "~(y + 4 <= x)")
           |> assert_justify_ineq ([], "~(y + 5 <= x)")
    end

end
