(*
  File: Auto2_Test.thy
  Author: Bohua Zhan

  Unit tests for auto2.
*)

theory Auto2_Test
  imports Auto2_Main
begin

ML_file "util_test.ML"
ML_file "rewrite_test.ML"
ML_file "matcher_test.ML"
ML_file "normalize_test.ML"
ML_file "logic_steps_test.ML"

ML_file "acdata_test.ML"

end
