(* Instantiation-dependent functions *)

structure SepUtilExtra : SEP_UTIL_EXTRA =
struct

open SepUtil

fun is_case_prod t =
    case t of
        Const (@{const_name case_prod}, _) $ _ $ _ => true
      | _ => false

fun sort_by t =
    case t of
        Const (@{const_name pure_assn}, _) $ _ => 2
      | Const (@{const_name top_assn}, _) => 1
      | _ => 0

fun pure_ord (t, s) =
    if sort_by t = 0 andalso sort_by s = 0 then
      Term_Ord.term_ord (t, s) = LESS
    else
      sort_by t < sort_by s

fun normalize_times_cv ctxt ct =
    let
      val (A, B) = Util.dest_binop_args (Thm.term_of ct)
    in
      if is_ex_assn A then
        Conv.every_conv [rewr_obj_eq (obj_sym @{thm ex_distrib_star}),
                         Conv.binder_conv (normalize_times_cv o snd) ctxt] ct
      else if is_ex_assn B then
        Conv.every_conv [ACUtil.comm_cv assn_ac_info,
                         normalize_times_cv ctxt] ct
      else
        Conv.every_conv [
          ACUtil.normalize_au assn_ac_info,
          ACUtil.normalize_comm_gen assn_ac_info pure_ord,
          ACUtil.norm_combine assn_ac_info SepUtil.is_true_assn
                              (rewr_obj_eq @{thm top_assn_reduce})] ct
    end

(* Normalization function for assertions. This function pulls all EX_A
   to the front, then apply AC-rules to the inside, putting all pure
   assertions on the right.
 *)
fun normalize_assn_cv ctxt ct =
    let
      val t = Thm.term_of ct
    in
      if is_ex_assn t then
        Conv.binder_conv (normalize_assn_cv o snd) ctxt ct
      else if UtilArith.is_times t then
        Conv.every_conv [Conv.binop_conv (normalize_assn_cv ctxt),
                         normalize_times_cv ctxt] ct
      else if is_pure_assn t andalso is_conj (dest_arg t) then
        Conv.every_conv [rewr_obj_eq @{thm pure_conj},
                         normalize_assn_cv ctxt] ct
      else if is_case_prod t then
        Conv.every_conv [rewr_obj_eq @{thm case_prod_beta},
                         normalize_assn_cv ctxt] ct
      else
        Conv.all_conv ct
    end

(* Rewrite terms for an assertion *)
fun assn_rewr_terms P =
    P |> ACUtil.dest_ac assn_ac_info
      |> filter_out is_pure_assn
      |> maps (snd o Term.strip_comb)
      |> distinct (op aconv)

end  (* structure SepUtilExtra. *)
