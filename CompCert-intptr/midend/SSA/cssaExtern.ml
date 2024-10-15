(** Coalescing *)
open Maps
open SSA

module PosSet = Set.Make(struct
  type t = SSA.node
  let compare = compare
end)

(** debug utilities *)
let diag m =
  Printf.printf "%s\n" m;
  flush_all()

(** compute cssa value *)
let compute_cssaval_function (f : CSSA.coq_function) =
  let cssaval_hash = Hashtbl.create 16 in  
  let get_cssaval r =
    try Hashtbl.find cssaval_hash r with
    Not_found -> r
  in

  (* depth first search *)
  let sorted_nodes = Stack.create () in
  let unvisited = ref (PosSet.of_list (List.map fst (PTree.elements f.CSSA.fn_code))) in
  let rec visit pc =
    if not (PosSet.mem pc !unvisited) then ()
    else begin
      unvisited := PosSet.remove pc !unvisited;
      match PTree.get pc f.CSSA.fn_code with
      | None     -> assert false
      | Some ins ->
          List.iter visit (successors_instr ins);
          Stack.push pc sorted_nodes
    end
  in
  visit f.CSSA.fn_entrypoint;
  if not (PosSet.is_empty !unvisited) then
    diag "Warning: some not accessible nodes";

  (* node processing *)
  let rec do_node pc =
    match PTree.get pc f.CSSA.fn_code with
    | None     -> assert false
    | Some ins ->
        begin
          if PTree.get pc f.CSSA.fn_phicode <> None then
            match PTree.get pc f.CSSA.fn_parcopycode with
            | None       -> assert false
            | Some parcb ->
                do_parcopyblock parcb;
                do_instruction ins
          else
            do_instruction ins;
            match PTree.get pc f.CSSA.fn_parcopycode with
            | None       -> ()
            | Some parcb -> do_parcopyblock parcb
        end
  and do_instruction ins = match ins with
    | Iop(Op.Omove, src :: nil, dst, _) ->  Hashtbl.add cssaval_hash dst (get_cssaval src)
    | _ -> ()
  and do_parcopyblock parcb =
    List.iter
      (function CSSA.Iparcopy(src, dst) -> Hashtbl.add cssaval_hash dst (get_cssaval src))
      parcb
  in
  while not (Stack.is_empty sorted_nodes) do
    do_node (Stack.pop sorted_nodes)
  done;

  (* return cssaval function *)
  get_cssaval

(** initialize classes with phi variables *)
let initialize_classes f : (PosSet.t PTree.t * (Registers.reg , Registers.reg) Hashtbl.t) =
  let repr_hash = Hashtbl.create 27 in
  let classes =
    PTree.fold
      (fun acc pc phib ->
        List.fold_left
          (fun acc (Iphi(args,dst)) ->
            List.iter (fun r -> Hashtbl.add repr_hash r dst) (dst :: args);
            PTree.set dst (PosSet.of_list (dst :: args)) acc)
          acc
          phib)
      f.CSSA.fn_phicode
      PTree.empty in
  (classes, repr_hash)

let get_class repr classes : PosSet.t =
  match PTree.get repr classes with
  | Some cls -> cls
  | None -> PosSet.empty

(** build coalescing classes of non interfering variables *)
let build_coalescing_classes_extern f ninterfere =
  let (classes, repr_hash) = initialize_classes f in
  let regrepr r =
    try Hashtbl.find repr_hash r
    with Not_found -> r
  in
  let classes =
    PTree.fold
      (fun acc pc parcb ->
        match PTree.get pc f.CSSA.fn_phicode with
        | Some phib ->
           List.fold_left
             (fun acc (CSSA.Iparcopy(src,dst)) ->
               let repr_class = get_class src acc in
               let dst_class = PosSet.union (get_class (regrepr dst) acc) (PosSet.singleton dst)
               in
               if PosSet.for_all
                    (fun r -> PosSet.for_all (fun r' -> ninterfere r' r) dst_class)
                    repr_class
               then begin
                   PosSet.iter (fun r -> Hashtbl.add repr_hash r src) dst_class;
                   PTree.set src (PosSet.union dst_class repr_class) acc
                 end
               else acc)
             acc
             parcb
        | None -> acc)
      f.CSSA.fn_parcopycode
      classes
  in
  let classes =
    PTree.fold
      (fun acc pc parcb ->
        match PTree.get pc f.CSSA.fn_phicode with
        | Some phib -> acc
        | None ->
           List.fold_left
             (fun acc (CSSA.Iparcopy(src,dst)) ->
               let repr = Hashtbl.find repr_hash dst in
               let dst_class = get_class repr acc in
               let src_class = PosSet.union (get_class (regrepr src) acc) (PosSet.singleton src) in
               if PosSet.for_all
                    (fun r -> PosSet.for_all (fun r' -> ninterfere r' r) src_class)
                    dst_class
               then
                 begin
                   PosSet.iter (fun r -> Hashtbl.add repr_hash r repr) src_class;
                   PTree.set repr (PosSet.union src_class dst_class) acc
                 end
               else acc)
             acc
             parcb)
      f.CSSA.fn_parcopycode
      classes
  in
  (regrepr, PTree.map (fun r s -> PosSet.elements s) classes)
