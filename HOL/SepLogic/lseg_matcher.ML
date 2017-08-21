
open SepUtil

(* Given term t, form the assertion emp ==> lseg [] t t *)
fun lseg_triv_th ctxt t =
    let
      val thy = Proof_Context.theory_of ctxt
      val th = @{thm lseg_empty}
      val p = th |> prop_of' |> dest_entail |> snd |> dest_arg
      val inst = Pattern.first_order_match thy (p, t) fo_init
    in
      Util.subst_thm ctxt inst th
    end

(* Given pattern of form lseg [] x y, match using emp. Consider the
   cases where x = y, or x is a schematic variable, or y is a
   schematic variable.
 *)
fun lseg_empty_matcher (tbl as {ctxt, ...}) (pat, ct) (id, inst) =
    case pat of
        Const (@{const_name lseg}, _) $ ls $ x $ y =>
        let
          val t = Thm.term_of ct
          val list_T = fastype_of ls
          val empty_list = Const (@{const_name Nil}, list_T)
          val equivs = RewriteTable.equiv_info_t tbl id (ls, empty_list)
          fun process_equiv (id', eq_th) =
              let
                (* t_triv: t ==> t * emp *)
                val t_triv = t |> entail_triv_th ctxt
                               |> apply_to_entail_r mult_emp_right

                (* Rewrite lseg ls x y to lseg [] x y. *)
                val eq_cv = Util.argn_conv 0 (Conv.rewr_conv (meta_sym eq_th))
              in
                (* lseg_th is emp ==> lseg [] x y. *)
                if Term.is_Var x andalso not (Util.has_vars y) then
                  let
                    val (ixn, _) = Term.dest_Var x
                    val inst' = Util.update_env (ixn, y) inst
                    val lseg_th = y |> lseg_triv_th ctxt
                                    |> apply_to_entail_r eq_cv
                  in
                    [((id', inst'), [t_triv, lseg_th] MRS @{thm entail_trans2})]
                  end
                else if Term.is_Var y andalso not (Util.has_vars x) then
                  let
                    val (ixn, _) = Term.dest_Var y
                    val inst' = Util.update_env (ixn, x) inst
                    val lseg_th = x |> lseg_triv_th ctxt
                                    |> apply_to_entail_r eq_cv
                  in
                    [((id', inst'), [t_triv, lseg_th] MRS @{thm entail_trans2})]
                  end
                else if not (Util.has_vars x) andalso x aconv y then
                  let
                    val lseg_th = y |> lseg_triv_th ctxt
                                    |> apply_to_entail_r eq_cv
                  in
                    [((id', inst), [t_triv, lseg_th] MRS @{thm entail_trans2})]
                  end
                else []
              end
        in
          maps process_equiv equivs
        end
      | _ => []

val _ = Theory.setup (AssnMatcher.add_assn_matcher lseg_empty_matcher)
