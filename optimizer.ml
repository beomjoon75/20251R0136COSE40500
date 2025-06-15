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

    let reaching_definitions_analysis
    =fun bbs ->
      let blks = BasicBlocks.blocksof bbs in
      let blks = List.sort Block.compare blks in
      let all_defs = List.concat_map Block.get_defs blks in
      let gen_def = List.fold_left(fun acc def -> BatMap.add def (BatSet.singleton def) acc) BatMap.empty all_defs in
      let kill_def = List.fold_left(fun acc def ->
        let opt_var = get_var def in
        match opt_var with
        | None -> BatMap.add def BatSet.empty acc
        | Some x -> 
          let kill_set = List.fold_left(fun kill_set d ->
            if d <> def && get_var d = Some x then BatSet.add d kill_set 
            else kill_set
          ) BatSet.empty all_defs in
          BatMap.add def kill_set acc
      ) BatMap.empty all_defs in
    
      let gen_map = List.fold_left(fun gm b -> 
        let defs = Block.get_defs b in
        let rev_defs = List.rev defs in
        let (gen_set, _) = List.fold_left(fun (gs, prevd) d ->
          let rst = List.fold_left(fun acc k_d -> 
            BatSet.diff acc (BatMap.find k_d kill_def)
          ) (BatMap.find d gen_def) prevd in
          (BatSet.union gs rst, d :: prevd)
        ) (BatSet.empty, []) rev_defs in
        BlockMap.add b gen_set gm
      ) BlockMap.empty blks in
    
      let kill_map = List.fold_left(fun km b ->
        let defs = Block.get_defs b in
        let kill_set = List.fold_left(fun acc d -> BatSet.union acc (BatMap.find d kill_def)) BatSet.empty defs in
        BlockMap.add b kill_set km
      ) BlockMap.empty blks in
    
      let in_map, out_map = List.fold_left(fun (i, o) b -> 
        (BlockMap.add b BatSet.empty i, BlockMap.add b BatSet.empty o)
      ) (BlockMap.empty, BlockMap.empty) blks in
    
      let rec fix : (pc * linstr) BatSet.t BlockMap.t * (pc * linstr) BatSet.t BlockMap.t -> bool -> (pc * linstr) BatSet.t BlockMap.t * (pc * linstr) BatSet.t BlockMap.t
      =fun (in_map, out_map) flag ->
        if not flag then (in_map, out_map)
        else
          let (new_in, new_out) = List.fold_left(fun (im, om) b ->
            let preds = BasicBlocks.preds b bbs in
            let ui_set = List.fold_left(fun acc blk ->
                BatSet.union acc (BlockMap.find blk om)
            ) BatSet.empty (BlockSet.elements preds) in
            let ui = BlockMap.add b ui_set im in
            let uo_set = BatSet.union (BlockMap.find b gen_map) (BatSet.diff ui_set (BlockMap.find b kill_map)) in
            let uo = BlockMap.add b uo_set om in
            (ui, uo)
          ) (in_map, out_map) blks in
          let is_updated = new_in <> in_map || new_out <> out_map in
          fix (new_in, new_out) is_updated
      in
      fix (in_map, out_map) true

      let liveness_analysis
=fun bbs ->
  let blks = BasicBlocks.blocksof bbs in
  let blks = List.sort Block.compare blks in
  let all_defs = List.concat_map Block.get_defs blks in

  let def_set = List.fold_left(fun s d ->
    match get_var d with
    | None -> BatMap.add d BatSet.empty s
    | Some x -> BatMap.add d (BatSet.singleton x) s
  ) BatMap.empty all_defs in
  let use_set = List.fold_left(fun s d ->
    BatMap.add d (get_exp_var d) s
  ) BatMap.empty all_defs in

  let def_map, use_map = List.fold_left(fun (dm, um) b ->
    let defs = Block.get_defs b in
    let ds, us = List.fold_left(fun (ds, us) def -> 
      let u_vars = BatSet.elements (BatMap.find def use_set) in
      let us = List.fold_left(fun s x ->
        if BatSet.mem x ds then s
        else BatSet.union (BatSet.singleton x) s  
      ) us u_vars in
      let ds = BatSet.union (BatMap.find def def_set) ds in
      ds, us
    ) (BatSet.empty, BatSet.empty) defs in
    BlockMap.add b ds dm, BlockMap.add b us um
  ) (BlockMap.empty, BlockMap.empty) blks in

  let in_map, out_map = List.fold_left(fun (i, o) b -> 
    (BlockMap.add b BatSet.empty i, BlockMap.add b BatSet.empty o)
  ) (BlockMap.empty, BlockMap.empty) blks in

  let rec fix : var BatSet.t BlockMap.t * var BatSet.t BlockMap.t -> bool -> var BatSet.t BlockMap.t * var BatSet.t BlockMap.t
  =fun (in_map, out_map) flag ->
    if not flag then (in_map, out_map)
    else
      let (new_in, new_out) = List.fold_left(fun (im, om) b ->
        let ui_set = BatSet.union (BlockMap.find b use_map) (BatSet.diff (BlockMap.find b om) (BlockMap.find b def_map)) in
        let ui = BlockMap.add b ui_set im in
        
        let succs = BasicBlocks.succs b bbs in
        let uo_set = List.fold_left(fun acc blk ->
            BatSet.union acc (BlockMap.find blk im)
        ) BatSet.empty (BlockSet.elements succs) in
        let uo = BlockMap.add b uo_set om in

        (ui, uo)
      ) (in_map, out_map) blks in
      let is_updated = new_in <> in_map || new_out <> out_map in
      fix (new_in, new_out) is_updated
  in
  fix (in_map, out_map) true

  type expr = 
  | BOPV of bop * var * var
  | BOPC of bop * var * int
  | UOP of uop * var
  | LOADV of var * var

let available_expression_analysis
=fun bbs->
  let gen_expr
  =fun instr ->
    match instr with
      | ASSIGNV (_, bop, y, z) -> BatSet.singleton (BOPV(bop, y, z))
      | ASSIGNC (_, bop, y, n) -> BatSet.singleton (BOPC(bop, y, n))
      | ASSIGNU (_, uop, y) -> BatSet.singleton (UOP(uop, y))
      | LOAD (_, (y, z)) -> BatSet.singleton (LOADV(y, z))
      | _ -> BatSet.empty in
  
  let blks = BasicBlocks.blocksof bbs in
  let blks = List.sort Block.compare blks in
  let all_defs = List.concat_map Block.get_defs blks in
  let all_exprs = List.fold_left(fun s (_, (_, instr)) ->
    let e = gen_expr instr in
    BatSet.union e s
  ) BatSet.empty all_defs in

  let kill_expr
  =fun instr ->
    match instr with
    | ALLOC (x, _)
    | ASSIGNV (x, _, _, _)
    | ASSIGNC (x, _, _, _)
    | ASSIGNU (x, _, _)
    | COPY (x, _)
    | COPYC (x, _)
    | LOAD (x, _)
    | READ x ->
      List.fold_left(fun es expr ->
        let flag = 
          match expr with
          | BOPV (_, y, z) -> y = x || z = x
          | BOPC (_, y, _) 
          | UOP (_, y) -> y = x
          | LOADV (a, i) -> a = x || i = x
        in
        if flag then BatSet.add expr es
        else es
      ) BatSet.empty (BatSet.elements all_exprs)
    | _ -> BatSet.empty
  in

  let kill_def = List.fold_left(fun m def ->
    let (_, (_, instr)) = def in
    let s = kill_expr instr in
    BatMap.add def s m
  ) BatMap.empty all_defs in
  let gen_def = List.fold_left(fun m def ->
    let (_, (_, instr)) = def in
    let s = gen_expr instr in
    let s = BatSet.diff s (BatMap.find def kill_def) in
    BatMap.add def s m
  ) BatMap.empty all_defs in

  let kill_map = List.fold_left(fun m b ->
    let s = List.fold_left(fun acc def -> BatSet.union acc (BatMap.find def kill_def)) BatSet.empty (Block.get_defs b) in
    BlockMap.add b s m
  ) BlockMap.empty blks in
  let gen_map = List.fold_left(fun m b ->
    let s = List.fold_left(fun acc def ->
      BatSet.union (BatMap.find def gen_def) (BatSet.diff acc (BatMap.find def kill_def))
    ) BatSet.empty (Block.get_defs b) in
    BlockMap.add b s m
  ) BlockMap.empty blks in

  let in_map, out_map = List.fold_left(fun (i, o) b -> 
    (BlockMap.add b all_exprs i, BlockMap.add b all_exprs o)
  ) (BlockMap.empty, BlockMap.empty) blks in
  let in_map = BlockMap.add (BasicBlocks.get_entry bbs) BatSet.empty in_map in

  let rec fix : expr BatSet.t BlockMap.t * expr BatSet.t BlockMap.t -> bool -> expr BatSet.t BlockMap.t * expr BatSet.t BlockMap.t
  =fun (in_map, out_map) flag ->
    if not flag then (in_map, out_map)
    else
      let (new_in, new_out) = List.fold_left(fun (im, om) b ->
        let preds = BasicBlocks.preds b bbs in
        let ui_set = List.fold_left(fun acc blk ->
          BatSet.intersect acc (BlockMap.find blk om)
          ) all_exprs (BlockSet.elements preds) in
        let ui = BlockMap.add b ui_set im in
        
        let uo_set = BatSet.union (BlockMap.find b gen_map) (BatSet.diff ui_set (BlockMap.find b kill_map)) in
        let uo = BlockMap.add b uo_set om in
        ui, uo        
      ) (in_map, out_map) blks in
      let is_updated = new_in <> in_map || new_out <> out_map in
      fix (new_in, new_out) is_updated
  in
  fix (in_map, out_map) true

  type const_val = 
  | Bot
  | Const of int
  | Top

let const_join
=fun a b-> 
  match a, b with
  | Bot, c
  | c, Bot -> c
  | Const n, Const m -> 
    if n = m then Const n
    else Top
  | _ -> Top

let eval_binary 
=fun v1 op v2 ->
  match v1,op,v2 with
  | n1, ADD, n2 -> (n1+n2)
  | n1, SUB, n2 -> (n1-n2)
  | n1, MUL, n2 -> (n1*n2)
  | n1, DIV, n2 -> (n1/n2)
  | n1, LT, n2 -> if n1 < n2 then 1 else 0
  | n1, LE, n2 -> if n1 <= n2 then 1 else 0
  | n1, GT, n2 -> if n1 > n2 then 1 else 0
  | n1, GE, n2 -> if n1 >= n2 then 1 else 0
  | n1, EQ, n2 -> if n1 = n2 then 1 else 0
  | n1, AND, n2 -> if n1 != 0 && n2 != 0 then 1 else 0
  | n1, OR, n2 -> if n1 != 0 || n2 != 0 then 1 else 0
    
let eval_unary 
=fun op v ->
  match op, v with
  | MINUS, n -> (-n)
  | NOT, n -> if n = 0 then 1 else 0

  let cp_transfer_function
  =fun env (_, (_, instr)) ->
    let lookup
    =fun x -> try BatMap.find x env with _ -> Bot in
    match instr with
    | ASSIGNV (x, bop, y, z) ->
      let y_val = lookup y in
      let z_val = lookup z in
      let x_val = 
        match y_val, z_val with
        | Const a, Const b -> Const (eval_binary a bop b)
        | Const _, Top
        | Top, Const _
        | Top, Top -> Top
        | Bot, _
        | _, Bot -> Bot
      in
      BatMap.add x x_val env
    | ASSIGNC (x, bop, y, n) ->
      let y_val = lookup y in
      let x_val = 
        match y_val with
        | Const a -> Const (eval_binary a bop n)
        | Top -> Top
        | Bot -> Bot
      in
      BatMap.add x x_val env
    | ASSIGNU (x, uop, y) ->
      let y_val = lookup y in
      let x_val = 
        match y_val with
        | Const a -> Const (eval_unary uop a)
        | Top -> Top
        | Bot -> Bot
      in
      BatMap.add x x_val env
    | COPY (x, y) -> BatMap.add x (lookup y) env
    | COPYC (x, n) -> BatMap.add x (Const n) env

    | ALLOC (x, _)
    | LOAD (x, _)
    | READ x -> BatMap.add x Top env

    | _ -> env
  

let constant_propagation_analysis
=fun bbs ->  

  let blks = BasicBlocks.blocksof bbs in
  let blks = List.sort Block.compare blks in
  
  let env = BatMap.empty in
    let in_map, out_map = List.fold_left(fun (i, o) b -> 
    (BlockMap.add b env i, BlockMap.add b env o)
  ) (BlockMap.empty, BlockMap.empty) blks in

  let rec fix
  =fun (in_map, out_map) flag ->
    if not flag then (in_map, out_map)
    else 
      let (new_in, new_out) = List.fold_left(fun (im, om) b ->
        let preds = BasicBlocks.preds b bbs in
        let ui_env = List.fold_left(fun acc blk ->
          let b_env = BlockMap.find blk om in
          BatMap.merge(fun _ v1 v2 ->
            match v1, v2 with
            | None, None -> None
            | Some v, None
            | None, Some v -> Some v
            | Some v1, Some v2 -> Some (const_join v1 v2)
          ) acc b_env
        ) BatMap.empty (BlockSet.elements preds) in
        let ui = BlockMap.add b ui_env im in

        let uo_env = List.fold_left cp_transfer_function ui_env (Block.get_defs b) in
        let uo = BlockMap.add b uo_env om in
        ui, uo        
      ) (in_map, out_map) blks in
      let is_updated = new_in <> in_map || new_out <> out_map in
      fix (new_in, new_out) is_updated
  in
  fix (in_map, out_map) true

  let constant_folding
  =fun pgm_env bbs pgm ->
    let get_b_env 
    =fun pc ->
      let b = BasicBlocks.find_block pc bbs in
      BlockMap.find b pgm_env in
    
    let const_fold_instr
    =fun ((pc, (label, instr)), env) ->
      let flag, new_instr = 
        match instr with
        | ASSIGNV (x, bop, y, z) ->
          let y_val = BatMap.find_opt y env in
          let z_val = BatMap.find_opt z env in
          begin
            match y_val, z_val with
            | Some (Const a), Some (Const b) -> (true, COPYC (x, eval_binary a bop b))
            | Some (Const a), _ -> (true, ASSIGNC (x, bop, z, a))
            | _, Some (Const a) -> (true, ASSIGNC (x, bop, y, a))
            | _ -> (false, instr)
          end
        | ASSIGNC (x, bop, y, n) ->
          let y_val = BatMap.find_opt y env in
          begin
            match y_val with
            | Some (Const a) -> (true, COPYC (x, eval_binary a bop n))
            | _ -> (false, instr)
          end
        | ASSIGNU (x, uop, y) ->
          let y_val = BatMap.find_opt y env in
          begin
            match y_val with
            | Some (Const a) -> (true, COPYC (x, eval_unary uop a))
            | _ -> (false, instr)
          end
        | COPY (x, y) ->
          let y_val = BatMap.find_opt y env in
          begin
            match y_val with
            | Some (Const a) -> (true, COPYC (x, a))
            | _ -> (false, instr)
          end
        | _ -> (false, instr)
      in
      let env = cp_transfer_function env (pc, (label, instr)) in
      ((flag, (label, new_instr)), env)
    in
    let blks = BasicBlocks.blocksof bbs in
    let blk_leaders = List.fold_left(fun acc b -> (Block.get_leader b) :: acc) [] blks in
    List.fold_left(fun ((acc, flag), env) def ->
      let env = 
      if List.mem def blk_leaders then get_b_env (fst def) else env in
      let ((f, linstr), env) = const_fold_instr (def, env) in
      ((acc @ [linstr], flag || f), env)
      ) (([], false), BatMap.empty) pgm

      let copy_propagation
      =fun pgm_in bbs pgm ->
        let get_in_b
        =fun pc -> 
          let b = BasicBlocks.find_block pc bbs in
          BlockMap.find b pgm_in in
        
        let propagate_use
        =fun defs instr->
          let replace_variable
          =fun v ->
            let reaching_def = List.filter(fun (_, (_, instr)) ->
              match instr with
              | COPY (x, _) -> 
                if x = v then true
                else false
              | _ -> false
              ) defs in
            if List.length reaching_def = 1 then
              let (_, (_, instr)) = List.hd reaching_def in
              match instr with
              | COPY (_, x) -> x
              | _ -> v
            else v
          in
          match instr with
          | ASSIGNV (x, bop, y, z) ->
            let new_y = replace_variable y in
            let new_z = replace_variable z in
            if y <> new_y || z <> new_z then Some (ASSIGNV(x, bop, new_y, new_z))
            else None
          | ASSIGNC (x, bop, y, n) ->
            let new_y = replace_variable y in
            if y <> new_y then Some (ASSIGNC(x, bop, new_y, n))
            else None
          | ASSIGNU (x, uop, y) ->
            let new_y = replace_variable y in
            if y <> new_y then Some (ASSIGNU(x, uop, new_y))
            else None
          | COPY (x, y) ->
            let new_y = replace_variable y in
            if y <> new_y then Some (COPY(x, new_y))
            else None
          | CJUMP (x, l) ->
            let new_x = replace_variable x in
            if x <> new_x then Some (CJUMP(new_x, l))
            else None
          | CJUMPF (x, l) ->
            let new_x = replace_variable x in
            if x <> new_x then Some (CJUMPF(new_x, l))
            else None
          | STORE ((a, i), x) ->
            let new_a = replace_variable a in
            let new_i = replace_variable i in
            let new_x = replace_variable x in
            if a <> new_a || i <> new_i || x <> new_x then Some (STORE((new_a, new_i), new_x))
            else None
          | WRITE x ->
            let new_x = replace_variable x in
            if x <> new_x then Some (WRITE new_x)
            else None
          | _ -> None
        in
        let propagate_instr
        =fun (pc, (label, instr)) ->
          let in_b = get_in_b pc in
          let propagated_instr = propagate_use (BatSet.elements in_b) instr in
          match propagated_instr with
          | Some n_instr -> (true, (label, n_instr))
          | None -> (false, (label, instr))
        in
        List.fold_left(fun (acc, flag) def ->
          let (f, linstr) = propagate_instr def in
          (acc @ [linstr], flag || f)
          ) ([], false) pgm
      
  
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