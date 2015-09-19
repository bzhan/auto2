(* Unit test for normalizer.ML. *)

val test_normalize =
    let
      val thy = @{theory} |> add_logic_ac_data
      val ctxt = Proof_Context.init_global thy
      fun err n = "test_normalize: " ^ (string_of_int n)
      fun test n (t, ts) =
          let
            val ritem =
                thm_to_ritem thy (assume_thm ctxt (HOLogic.mk_Trueprop t))
            val ritems' = normalize ctxt ritem
            val ts' = map (HOLogic.dest_Trueprop o Thm.prop_of o get_thm_raw)
                          ritems'
          in
            if length ts = length ts' andalso eq_set (op aconv) (ts, ts')
            then ()
            else raise AUTO2CT (err n, map (cert ctxt) ts)
          end
      val _ = test 0 (@{term "A | C | D | B"}, [@{term "A | B | C | D"}])
      val _ = test 1 (@{term "P a = True"}, [@{term "(P a)::bool"}])
      val _ = test 2 (@{term "P a = False"}, [@{term "~ (P a)"}])
      val _ = test 3 (@{term "A & B & C"},
                      [@{term "A::bool"}, @{term "B::bool"}, @{term "C::bool"}])
      val _ = test 4 (@{term "~ (A | B | C)"},
                      [@{term "~ A"}, @{term "~ B"}, @{term "~ C"}])
      val _ = test 5 (@{term "EX (x::nat) (y::nat). P x & Q y"},
                      [@{term "EX (x::nat). P x"}, @{term "EX (y::nat). Q y"}])
      val _ = test 6 (@{term "EX (y::nat) (x::nat). P x y"},
                      [@{term "EX (x::nat) (y::nat). P x y"}])
      val _ = test 7 (@{term "EX (x::nat) (y::nat). P x y"},
                      [@{term "EX (x::nat) (y::nat). P x y"}])
      val _ = test 8 (@{term "~ ~ (~ A & (~ ~ B))"},
                      [@{term "~ A"}, @{term "B::bool"}])
    in () end
