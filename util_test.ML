(* Unit test for util.ML. *)

local

  val ctxt = @{context}

in

val test_rename_abs =
    let
      val inst =
          fo_init |> update_env (("P", 0), @{term "%x::nat. x + x = 0"})
                  |> update_env (("Q", 0), @{term "%x y::nat. x + y = 0"})

      fun test (t, res) =
          if rename_abs inst t = res then () else
          raise AUTO2T ("test_rename_abs", [rename_abs inst t, res])

      val data = [(@{term_pat "%m::nat. ?P m"}, @{term_pat "%x::nat. ?P x"}),
                  (@{term_pat "!m::nat. ?P m"}, @{term_pat "!x::nat. ?P x"}),
                  (@{term_pat "!m::nat. !n::nat. ?Q m n"},
                   @{term_pat "!x::nat. !y::nat. ?Q x y"})]
    in
      map test data
    end

fun assert_eq_prop t txt th =
    let val _ = assert (t aconv (Thm.prop_of th)) txt in th end

val test_to_obj_conv =
    let
      fun err n = "test_to_obj_conv: " ^ (string_of_int n)
      fun assert_eq th ct txt =
          let val ct' = Thm.rhs_of th
          in if ct' aconvc ct then () else raise AUTO2CT (txt, [ct']) end
      val ct1 = @{cprop "A ==> B ==> (!!(n::nat). C n) ==> D"}
      val ct2 = @{cprop "A --> B --> (!(n::nat). C n) --> D"}
      val ct3 = @{cprop "!(y::nat) (x::nat). P x y --> (!z. Q x y z)"}
      val _ = assert_eq (to_obj_conv ctxt ct1) ct2 (err 0)
      val _ = assert_eq (to_meta_imp_conv ct2)
              @{cprop "A ==> B ==> (!(n::nat). C n) ==> D"} (err 1)
      val _ = assert_eq (to_meta_all_conv ctxt ct3)
              @{cprop "!!(y::nat) (x::nat). (P x y --> (!z. Q x y z))"} (err 2)
      val _ = assert_eq (to_obj_conv_on_horn ctxt ct1)
              @{cprop "A ==> B ==> (!(n::nat). C n) ==> D"} (err 4)
    in () end

val test_normalize_exs_alls =
    let
      val ctxt' = ctxt |> fold Variable.auto_fixes [
            @{term_pat "[x::nat, y, ?x, ?y]"},
            @{term_pat "[P::(nat => bool), Q]"},
            @{term_pat "[R::(nat => nat => bool)]"},
            @{term_pat "[S::(nat set), T]"}]

      val test_exs_inf =
          test_conv ctxt' (normalize_exs_conv ~1 ctxt) "test_normalize_exs"
      val test_exs_1 =
          test_conv ctxt' (normalize_exs_conv 1 ctxt) "test_normalize_exs"
      val test_alls_inf =
          test_conv ctxt' (normalize_alls_conv ~1 ctxt) "test_normalize_alls"
      val test_alls_1 =
          test_conv ctxt' (normalize_alls_conv 1 ctxt) "test_normalize_alls"

      val test_data_exs_inf = [
        ("EX x. P x", "EX x. P x"),
        ("P y & (EX x. R x y)", "EX x. P y & R x y"),
        ("EX x. P x & (EX y. R x y)", "EX x y. P x & R x y"),
        ("EX x:S. P x", "EX x. x : S & P x"),
        ("EX x:S. EX y:T. R x y", "EX x y. x : S & y : T & R x y"),
        ("(EX x. P x) & (EX y. Q y)", "EX y. (EX x. P x) & Q y")
      ]

      val test_data_exs_1 = [
        ("EX x. P x & (EX y. R x y)", "EX x. P x & (EX y. R x y)"),
        ("EX x:S. EX y:T. R x y", "EX x. x : S & (EX y:T. R x y)")
      ]

      val test_data_alls_inf = [
        ("ALL x. P x", "ALL x. P x"),
        ("P x --> (ALL y. R x y)", "ALL y. P x --> R x y"),
        ("ALL x. P x --> (ALL y. R x y)", "ALL x y. P x --> R x y"),
        ("ALL x:S. P x", "ALL x. x : S --> P x"),
        ("ALL x:S. ALL y:T. R x y", "ALL x y. x : S --> y : T --> R x y")
      ]

      val test_data_alls_1 = [
        ("ALL x. P x --> (ALL y. R x y)", "ALL x. P x --> (ALL y. R x y)"),
        ("ALL x:S. ALL y:T. R x y", "ALL x. x : S --> (ALL y:T. R x y)")
      ]
    in
      map test_exs_inf test_data_exs_inf @ map test_exs_1 test_data_exs_1 @
      map test_alls_inf test_data_alls_inf @ map test_alls_1 test_data_alls_1
    end

val test_is_pattern =
    let
      fun test b str =
          let
            val t = read_pat ctxt str
          in
            if b = is_pattern t then ()
            else raise AUTO2CT ("test_is_pattern", [cert ctxt t])
          end

      val test_positive = ["?f", "!n. ?f n", "!m n. ?f m n",
                           "!n. ?f n < ?f (n + 1)",
                           "!n. ?f (n + 1) < ?f n", "!n. ?g (?f n) & ?g n"]
      val test_negative = ["?f ?n", "!n. ?f n n", "!n. ?f (?f n)",
                           "!n. (?f n < ?g (n + 1)) & (?f (n + 1) < ?g n)"]
    in
      map (test true) test_positive @ map (test false) test_negative
    end

end
