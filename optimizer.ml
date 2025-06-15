let rec optimize : program -> program
=fun pgm -> 
  let construct_bb
  =fun pgm ->
    let ordered_pgm = List.mapi(fun idx linstr -> (idx, linstr) ) pgm in
    let bbs = basicblocks ordered_pgm in
    (ordered_pgm, bbs) in
  
  let (ordered_pgm, bbs) = construct_bb pgm in

  let cpa_in, _ = constant_propagation_analysis bbs in
  let (cf_pgm, cf_flag), _ = constant_folding cpa_in bbs ordered_pgm in
  let (ordered_pgm, bbs) = construct_bb cf_pgm in

  let rda_in, _ = reaching_definitions_analysis bbs in
  let cp_pgm, cp_flag = copy_propagation rda_in bbs ordered_pgm in
  let (ordered_pgm, bbs) = construct_bb cp_pgm in

  let aea_in, _ = available_expression_analysis bbs in
  let (_, cse_pgm), cse_flag = common_subexpression_elimination aea_in bbs ordered_pgm in
  let (ordered_pgm, bbs) = construct_bb cse_pgm in

  let _, lva_out = liveness_analysis bbs in
  let (_, dce_pgm), dce_flag = deadcode_elimination lva_out bbs ordered_pgm in
    
  if cf_flag || cp_flag || cse_flag || dce_flag then optimize dce_pgm
  else dce_pgm