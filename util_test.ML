(* Unit test for util.ML. *)

val test_normalize_pred_comm =
    let
      fun test (ct1, ct2) =
          let
            val th = Logic_ProofSteps.normalize_pred_comm ct1
            val (ct1', ct2') = Thm.dest_equals (Thm.cprop_of th)
          in
            if ct1 aconvc ct1' andalso ct2 aconvc ct2' then ()
            else raise AUTO2CT ("test_normalize_pred_comm", [ct1', ct2'])
          end
      val _ = test (@{cterm "EX i j. ka = p ^ i & y = p ^ j"},
                    @{cterm "EX i j. ka = p ^ i & y = p ^ j"})
      val _ = test (@{cterm "EX i j. ka = p ^ j & y = p ^ i"},
                    @{cterm "EX j i. ka = p ^ j & y = p ^ i"})
      val _ = test (@{cterm "ka = p ^ j & y = p ^ i"},
                    @{cterm "ka = p ^ j & y = p ^ i"})
    in () end

fun assert_eq_prop t txt th =
    let val _ = assert (t aconv (Thm.prop_of th)) txt in th end

val test_to_obj_conv =
    let
      fun err n = "test_to_obj_conv: " ^ (string_of_int n)
      val ctxt = @{context}
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
