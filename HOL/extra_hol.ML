(* Extra setup for HOL. *)

signature EXTRA_HOL =
sig
  val add_forward_arg1_prfstep_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_forward_arg1_prfstep: thm -> theory -> theory
  val add_forward_arg_prfstep_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_forward_arg_prfstep: thm -> theory -> theory
end;

structure Extra_HOL : EXTRA_HOL =
struct

fun add_forward_arg1_prfstep_cond th conds thy =
    let
      val concl = th |> concl_of' |> strip_conj |> hd
    in
      thy |> add_forward_prfstep_cond
          th ([K (WithTerm (dest_arg1 concl))] @ conds)
    end

fun add_forward_arg1_prfstep th = add_forward_arg1_prfstep_cond th []

fun add_forward_arg_prfstep_cond th conds thy =
    let
      val concl = th |> concl_of' |> strip_conj |> hd
    in
      thy |> add_forward_prfstep_cond
          th ([K (WithTerm (dest_arg concl))] @ conds)
    end

fun add_forward_arg_prfstep th = add_forward_arg_prfstep_cond th []

end  (* structure Extra_HOL *)

open Extra_HOL
