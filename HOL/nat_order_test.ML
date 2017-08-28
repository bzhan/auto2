(* Unit test for NatOrder *)

local

  val ts = map (fn x => Free (x, natT)) ["u", "v", "w", "x", "y", "z"]
  val init = fold Util.declare_free_term ts @{context}

in

fun add_ineq (id, str) ctxt =
    let
      val t = Syntax.read_term ctxt str
      val th = t |> mk_Trueprop |> Thm.cterm_of ctxt |> Thm.assume
    in
      NatOrder.add_ineq (id, th) ctxt
    end

fun add_ineq_general (id, str) ctxt =
    let
      val t = Syntax.read_term ctxt str
      val th = t |> mk_Trueprop |> Thm.cterm_of ctxt |> Thm.assume
    in
      NatOrder.add_ineq_general (id, th) ctxt
    end

fun assert_info (id, str) ctxt =
    let
      val t = Syntax.read_term ctxt str
      val th = t |> mk_Trueprop |> Thm.cterm_of ctxt |> Thm.assume
      val (x, y, _) = NatOrder.dest_ineq t
      val ineqs = NatOrder.retrieve_ineqs ctxt (x, y)
    in
      if member NatOrder.eq_info ineqs (id, th) then ctxt else
      let
        val _ = tracing (NatOrder.print_ord_info ctxt (id, th) ^
                         " not found.")
                handle TERM _ => raise Fail "here"
      in
        raise Fail "assert_info"
      end
    end

fun assert_box_resolved id ctxt =
    if NatOrder.is_box_resolved ctxt id then ctxt else
    let
      val _ = tracing (BoxID.string_of_box_id id ^ " not resolved.")
    in
      raise Fail "assert_box_resolved"
    end

fun assert_justify_ineq (id, str) ctxt =
    let
      val t = Syntax.read_term ctxt str
      val info = if is_neg t then NatOrder.justify_neg_ineq ctxt t
                 else NatOrder.justify_ineq ctxt t
    in
      if length info = 1 andalso fst (the_single info) = id andalso
         prop_of' (snd (the_single info)) aconv t then ctxt else
      let
        val _ = tracing (BoxID.string_of_box_id id ^ " " ^
                         (Syntax.string_of_term ctxt t))
      in
        raise Fail "assert_justify_ineq"
      end
    end

(* Basic non-contradictory case. *)
val test1 =
    init |> add_ineq ([], "x <= y + 1")
         |> add_ineq ([], "y <= z + 1")
         |> add_ineq ([], "z <= x + 1")
         |> assert_info ([], "x <= y + 1")
         |> assert_info ([], "x <= z + 2")
         |> assert_info ([], "y <= z + 1")
         |> assert_info ([], "y <= x + 2")
         |> assert_info ([], "z <= x + 1")
         |> assert_info ([], "z <= y + 2")

(* Basic contradictory case. *)
val test2 =
    init |> add_ineq ([], "x <= y + 1")
         |> add_ineq ([], "y <= z + 2")
         |> add_ineq ([], "z + 4 <= x")
         |> assert_box_resolved []

(* Basic test for adding general inequalities. *)
val test3 =
    init |> add_ineq_general ([], "x < y + 2")
         |> assert_info ([], "x <= y + 1")
         |> add_ineq_general ([], "x < y + 1")
         |> assert_info ([], "x <= y + 0")
         |> add_ineq_general ([], "x < y")
         |> assert_info ([], "x + 1 <= y")
         |> add_ineq_general ([], "x + 1 < y")
         |> assert_info ([], "x + 2 <= y")

(* Test of justifying inequalities. *)
val test4 =
    init |> add_ineq ([], "x <= y + 3")
         |> assert_justify_ineq ([], "x <= y + 3")
         |> assert_justify_ineq ([], "x <= y + 4")
         |> assert_justify_ineq ([], "x < y + 4")
         |> assert_justify_ineq ([], "~(y + 3 < x)")
         |> assert_justify_ineq ([], "~(y + 4 <= x)")
         |> assert_justify_ineq ([], "~(y + 5 <= x)")

(* Test for justifying trivial inequalities. *)
val test5 =
    init |> assert_justify_ineq ([], "x <= x")
         |> assert_justify_ineq ([], "x <= x + 3")
         |> assert_justify_ineq ([], "(0::nat) < 1")
         |> assert_justify_ineq ([], "(1::nat) <= 1")

(* Test for adding inequalities with addition on both sides. *)
val test6 =
    init |> add_ineq_general ([], "x + 1 <= y + 1")
         |> assert_info ([], "x <= y + 0")
         |> add_ineq_general ([], "x + 1 < y + 1")
         |> assert_info ([], "x + 1 <= y")
         |> add_ineq_general ([], "x + 3 <= y + 1")
         |> assert_info ([], "x + 2 <= y")
         |> add_ineq_general ([], "x + 3 < y + 1")
         |> assert_info ([], "x + 3 <= y")

end
