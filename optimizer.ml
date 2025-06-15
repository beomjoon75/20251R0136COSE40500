module Block = struct
  type t = {
    leader : pc * linstr;
    defs : (pc * linstr) list
  }
  let create : pc * linstr -> t
  =fun def -> 
    {
      leader = def;
      defs = [def]
    }
  let add_def : pc * linstr -> t -> t
  =fun def b -> {b with defs = b.defs @ [def]}
  let modify_def : pc * linstr -> t -> t
  =fun def b ->
    let (lead_pc, _) = b.leader in
    let (curr_pc, _) = def in
    let m_defs = List.map(fun (p, l) -> if p = curr_pc then def else (p, l)) b.defs in
    if curr_pc = lead_pc then {leader = def; defs = m_defs}
    else {b with defs = m_defs}
    
  let remove_def : pc * linstr -> t -> t
  =fun def b ->
    let (lead_pc, _) = b.leader in
    let (curr_pc, _) = def in
    let m_defs = List.filter(fun (p, _) -> p <> curr_pc) b.defs in
    match m_defs with
    | [] -> create (-1, (dummy_label, SKIP))
    | hd :: _ ->
      if curr_pc = lead_pc then {leader = hd; defs = m_defs}
      else {b with defs = m_defs}    

  let get_leader : t -> pc * linstr
  =fun b -> b.leader

  let get_defs : t -> (pc * linstr) list
  =fun b -> b.defs

  let get_last_def : t -> pc * linstr
  =fun b -> List.hd(List.rev b.defs)

  let compare = Stdlib.compare
end

module BlockSet = Set.Make(Block)
module BlockMap = Map.Make(Block)

module BasicBlocks = struct
  type t = {
    blocks : BlockSet.t;
    succs : BlockSet.t BlockMap.t;
    preds : BlockSet.t BlockMap.t;
  }

  let empty = {
    blocks = BlockSet.empty;
    succs = BlockMap.empty;
    preds = BlockMap.empty;
  }

  let blocksof : t -> Block.t list
  =fun t -> BlockSet.elements t.blocks

  let succs : Block.t -> t -> BlockSet.t
  =fun b bbs -> try BlockMap.find b bbs.succs with _ -> BlockSet.empty

  let preds : Block.t -> t -> BlockSet.t
  =fun b bbs -> try BlockMap.find b bbs.preds with _ -> BlockSet.empty

  let add_block : Block.t -> t -> t
  =fun b bbs -> {bbs with blocks = BlockSet.add b bbs.blocks}

  let add_blocks : Block.t list -> t -> t
  =fun bs bbs -> bbs |> (List.fold_right add_block bs)

  let add_edge : Block.t -> Block.t -> t -> t
  =fun b1 b2 bbs ->
    bbs
    |> add_blocks [b1; b2]
    |> (fun bbs -> { bbs with succs = BlockMap.add b1 (BlockSet.add b2 (succs b1 bbs)) bbs.succs }) 
    |> (fun bbs -> { bbs with preds = BlockMap.add b2 (BlockSet.add b1 (preds b2 bbs)) bbs.preds }) 

  let remove_edge : Block.t -> Block.t -> t -> t 
  =fun n1 n2 g -> 
    g 
    |> (fun g -> { g with succs = BlockMap.add n1 (BlockSet.remove n2 (succs n1 g)) g.succs }) 
    |> (fun g -> { g with preds = BlockMap.add n2 (BlockSet.remove n1 (preds n2 g)) g.preds }) 

  let remove_succs : Block.t -> t -> t 
  =fun n g -> 
    g 
    |> BlockSet.fold (remove_edge n) (succs n g)

  let remove_preds : Block.t -> t -> t 
  =fun n g -> 
    g 
    |> BlockSet.fold (fun p -> remove_edge p n) (preds n g)

  let remove_block : Block.t -> t -> t 
  =fun n g -> 
    g 
    |> remove_succs n 
    |> remove_preds n 
    |> (fun g -> { g with blocks = BlockSet.remove n g.blocks })
  
  let modify_block : Block.t -> Block.t -> t -> t
  =fun b1 b2 bbs ->
    let preds = BlockSet.elements (preds b2 bbs) in
    let preds = List.map(fun b -> if b = b2 then b1 else b) preds in
    let succs = BlockSet.elements (succs b2 bbs) in
    let succs = List.map(fun b -> if b = b2 then b1 else b) succs in
    let bss = 
      bbs
      |> remove_block b2
      |> add_block b1
      |> (fun x -> List.fold_left(fun acc b -> add_edge b b1 acc) x preds)
      |> (fun x -> List.fold_left(fun acc b -> add_edge b1 b acc) x succs)
    in
    if Block.get_leader b1 <> (-1, (dummy_label, SKIP)) then bss
    else 
      match succs with
      | [] -> remove_block b1 bss
      | hd :: _ -> 
        bss
        |> remove_block b1
        |> (fun x -> List.fold_left(fun acc b -> add_edge b hd acc) x preds)

  let find_block : pc -> t -> Block.t
  =fun pc bbs ->
    let b_lst = BlockSet.elements bbs.blocks in
    List.find (fun b ->
      let defs = Block.get_defs b in
      List.exists (fun (p, _) -> 
        p = pc
      ) defs
    ) b_lst

  let get_entry : t -> Block.t
  =fun bbs ->
    let entries = 
      BlockSet.fold (fun n res -> 
        if BlockSet.is_empty (preds n bbs) then n::res else res 
      ) bbs.blocks [] in 
      assert (List.length entries = 1); 
      List.hd entries 
end

let basicblocks : (int * linstr) list -> BasicBlocks.t
=fun pgm ->
  let label_pc_lst = List.fold_left(fun map (pc, (label, _)) -> BatMap.add label pc map) BatMap.empty pgm in
  let entry_lst = List.fold_left(fun lst (pc, (_, instr)) ->
    match instr with
    | UJUMP l
    | CJUMP (_, l)
    | CJUMPF (_, l) -> lst @ [pc + 1; (BatMap.find l label_pc_lst)]
    | HALT -> lst @ [pc + 1]
    | _ -> lst
  ) [0] pgm in
  let leader_lst = List.sort_uniq compare entry_lst in
  let b_lst = List.fold_left(fun acc def ->
    let (curr_pc, _) = def in
    if List.mem curr_pc leader_lst then 
      Block.create def :: acc
    else
      let b = List.hd acc in
      let acc = drop 1 acc in
      let b = Block.add_def def b in
      b :: acc
  ) [] pgm in
  let bbs = List.fold_left(fun acc b -> BasicBlocks.add_block b acc) BasicBlocks.empty b_lst in
  let bbs = List.fold_left(fun acc b ->
    let (pc, (_, instr)) = Block.get_last_def b in
    match instr with
    | UJUMP l ->
      let dst = BatMap.find l label_pc_lst in
      let dst = BasicBlocks.find_block dst bbs in
      BasicBlocks.add_edge b dst acc
    | CJUMP (_, l)
    | CJUMPF (_, l) ->
      let dst1 = BatMap.find l label_pc_lst in
      let dst1 = BasicBlocks.find_block dst1 bbs in
      let dst2 = pc + 1 in
      let dst2 = BasicBlocks.find_block dst2 bbs in
      acc
      |> BasicBlocks.add_edge b dst1
      |> BasicBlocks.add_edge b dst2
    | HALT -> acc
    | _ -> 
      let dst = pc + 1 in
      let dst = BasicBlocks.find_block dst bbs in
      BasicBlocks.add_edge b dst acc
  ) bbs (BasicBlocks.blocksof bbs) in
  let entry_blk = Block.create(-2, (dummy_label, SKIP)) in
  let bbs = BasicBlocks.add_block entry_blk bbs in
  let blk = BasicBlocks.find_block 0 bbs in
  BasicBlocks.add_edge entry_blk blk bbs

  let get_var : pc * linstr -> var option
  =fun (_, (_, instr)) ->
    match instr with
    | ALLOC (x, _)
    | ASSIGNV (x, _, _, _)
    | ASSIGNC (x, _, _, _)
    | ASSIGNU (x, _, _)
    | COPY (x, _)
    | COPYC (x, _)
    | LOAD (x, _) 
    | READ x -> Some x
    | _ -> None
  let get_exp_var : pc * linstr -> var BatSet.t
  =fun (_, (_, instr)) ->
    match instr with
    | ASSIGNV (_, _, y, z) -> BatSet.add_seq (BatSeq.of_list [y; z]) BatSet.empty
    | ASSIGNC (_, _, x, _)
    | ASSIGNU (_, _, x)
    | COPY (_, x)           (* x = y *)
    | CJUMP (x, _)
    | CJUMPF (x, _)
    | STORE (_, x)
    | WRITE x -> BatSet.singleton x
    | _ -> BatSet.empty

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