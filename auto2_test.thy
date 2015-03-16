theory auto2_test
imports auto2
begin

setup {* clear_ac_data *}

ML_file "util_test.ML"
ML_file "acdata_test.ML"
ML_file "subterms_test.ML"
ML_file "rewrite_test.ML"

end
