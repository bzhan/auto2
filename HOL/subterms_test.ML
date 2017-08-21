(* Unit test for subterms.ML *)

local
  val ctxt = @{context}
in

val test_dest_subterms =
    let
      val ctxt' = ctxt |> fold Variable.auto_fixes [
            @{term "[a::nat, b, c]"}, @{term "[A::bool, B, C, D]"}]

      fun test (str, str', subs_str) =
          let
            val t = Syntax.read_term ctxt' str
            val t' = Proof_Context.read_term_pattern ctxt' str'
            val subs = map (Syntax.read_term ctxt') subs_str
            val (ct'', subs') = (Subterms.dest_subterms (Thm.cterm_of ctxt' t))
                                    |> apsnd (map Thm.term_of)
            val t'' = Thm.term_of ct''
          in
            if t' aconv t'' andalso eq_list (op aconv) (subs, subs') then ()
            else raise Fail "test_dest_subterms"
          end

      val test_data = [
        ("a", "a", []),
        ("a dvd b", "(?SUB::nat) dvd ?SUB1", ["a", "b"]),
        ("a * (b * c)", "(?SUB::nat) * ?SUB1", ["a", "b * c"]),
        ("(a + b) * c", "(?SUB::nat) * ?SUB1", ["a + b", "c"]),
        ("ALL a. b dvd a", "ALL (a::nat). ?SUB dvd a", ["b"]),
        ("ALL A. A & B & C", "ALL A. A & ?SUB", ["B & C"]),
        ("ALL B. A & B & C", "ALL B. ?SUB & B & ?SUB1", ["A", "C"]),
        ("ALL C. A & B & C", "ALL C. ?SUB & ?SUB1 & C", ["A", "B"]),
        ("ALL A. (A & B) & C", "ALL A. (A & ?SUB) & ?SUB1", ["B", "C"]),
        ("ALL (A::bool). (B & C) & D", "ALL (A::bool). ?SUB", ["(B & C) & D"]),
        ("ALL A. C & (ALL B. A & B & D)", "ALL A. ?SUB & (!B. A & B & ?SUB1)",
         ["C", "D"]),
        ("~ (A | B)", "~ ?SUB", ["A | B"])
      ]
    in
      map test test_data
    end

val test_get_all_subterms =
    let
      val ctxt' = ctxt |> Variable.auto_fixes @{term "[a::nat, b, c]"}

      fun test (str, subs_str) =
          let
            val t = Syntax.read_term ctxt' str
            val subs = map (Syntax.read_term ctxt') subs_str
            val subs' = (Subterms.get_all_subterms (Thm.cterm_of ctxt' t))
                            |> map Thm.term_of
          in
            if eq_list (op aconv) (subs, subs') then ()
            else raise Fail "test_get_all_subterms"
          end

      val test_data = [
        ("a * (b * c)", ["a * (b * c)", "a", "b * c", "b", "c"])
      ]
    in
      map test test_data
    end

val test_build_equiv =
    let
      fun test_raw (t, equivs) =
          let
            val eq_th = Subterms.build_equiv equivs (Thm.cterm_of ctxt t)
            val lsubs = map Util.lhs_of equivs
            val rsubs = map Util.rhs_of equivs
          in
            if Util.lhs_of eq_th aconv (Subterms.subst_subterms (t, lsubs)) andalso
               Util.rhs_of eq_th aconv (Subterms.subst_subterms (t, rsubs)) then ()
            else
              raise Fail "test_build_equiv"
          end

      val ctxt' = ctxt |> Variable.auto_fixes @{term "[a::nat, b, c]"}
      fun test (str, equivs_str) =
          let
            val t = Proof_Context.read_term_pattern ctxt' str
            val equivs = map (Thm.assume o Thm.cterm_of ctxt' o Syntax.read_term ctxt')
                             equivs_str
          in
            test_raw (t, equivs)
          end

      (* Name conflict in abs. *)
      val dvd = Const ("Rings.dvd_class.dvd", @{typ "nat => nat => bool"})
      val t = Abs ("x", natT, Abs ("x", natT, dvd $ (Bound 0) $ (Bound 1)))
      val _ = test_raw (t, [])

      (* Other tests. *)
      val test_data = [
        ("(?SUB::nat) * ?SUB1", ["a == b", "c == d"]),
        ("ALL a. a + (?SUB::nat) = 0", ["b == c"]),
        ("ALL a. a + (?SUB::nat) = 0", ["b == b"]),
        ("ALL a. a + (?SUB::nat) = 0", ["a == a"])
      ]
    in
      map test test_data
    end

end;  (* local *)
