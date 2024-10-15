open SSA
open Maps

let rec fuel = Datatypes.S fuel

let debugmode = false

module DomTree = struct

  let successors_map code =
    PTree.map1 SSA.successors_instr code

  open ExternSSAgen
 
  let succ_and_pred code = 
    let succ = successors_map code in
    let pred = Kildall.make_predecessors code SSA.successors_instr in
    ((fun i -> 
      match PTree.get (positive_of_int i) succ with
	None -> []
      | Some l -> List.map int_of_positive l),
     (fun i -> 
       match PTree.get (positive_of_int i) pred with
	 None -> []
       | Some l -> List.map int_of_positive l))

  let entry f =
    int_of_positive f.SSA.fn_entrypoint

  let get_max t0 =
    let elts = List.map fst (PTree.elements t0) in
    List.fold_right (fun a pc -> if Coqlib.plt a pc then pc else a) elts BinNums.Coq_xH

  let size code = 
    1+ int_of_positive (get_max code)

  let array_elements rank t =
    let n = Array.length t in
    let l = ref [] in
    for k=0 to n-1 do
      let i = rank.(n-1-k) in (* modif ici *)
      (* Printf.printf "D[%d] = %d\n" i t.(i); *)
      if t.(i) >= 0 then
	l := (positive_of_int i, positive_of_int t.(i)) :: !l
    done;
    !l

  let idom entry code = 
    let (succ,pred) = succ_and_pred code in 
    let entry = int_of_positive entry in
    let size = size code in
    let (idom,_,rank) = Dominator.dominator succ pred entry size in 
    let list_assoc_idom = array_elements rank idom in
    list_assoc_idom

  let make_test entry code = 
    let debug = false in
    let (succ,pred) = succ_and_pred code in 
    let entry = int_of_positive entry in
    if debug then
      Printf.printf "ENTRY = %d\n" entry;
    let size = size code in
    let (idom,_,_) = Dominator.dominator succ pred entry size in 
    if debug then
      for i=0 to (size-1) do
	Printf.printf "idom[%2d] = %2d\n" i idom.(i)
      done;
    let succ = Array.init size (fun _ -> []) in
    Array.iteri
      (fun u v -> (* idom(u) = v *)
	if (v = -1) then assert (u=entry)
	else succ.(v) <- u::succ.(v)) idom;
    if debug then
      Array.iteri
	(fun i s ->
	  Printf.printf " %2d ->" i;
	  List.iter (Printf.printf " %d") s;
	  print_newline ())
	succ;
    let q = Stack.create () in
    let dfs_in = Array.init size (fun  _ -> -1) in
    let dfs_out = Array.init size (fun  _ -> -1) in
    let marked = Array.init size (fun  _ -> false) in
    let count = ref 0 in
    marked.(entry) <- true;
    Stack.push entry q;
    while not (Stack.is_empty q) do
      let i = Stack.pop q in
      if dfs_in.(i) >= 0 then 
	begin
	  dfs_out.(i) <- !count; incr count
	end
      else
	begin
	  dfs_in.(i) <- !count; incr count;
	  Stack.push i q;
	  List.iter 
	    (fun j -> 
	      if not marked.(j) then
		begin
		  marked.(j) <- true;
		  Stack.push j q
		end)
	    succ.(i)
	end
    done;
    if debug then
      for i=0 to (size-1) do
	Printf.printf "itv[%2d] = [%2d, %2d]\n" i dfs_in.(i) dfs_out.(i)
      done;
    let dominates pc1 pc2 =
      let i1 = int_of_positive pc1 in
      let i2 = int_of_positive pc2 in
      i1 = i2
      ||
	( dfs_in.(i1) < dfs_in.(i2) 
	  &&
	  dfs_out.(i2) < dfs_out.(i1)) in
    dominates
    

end


type cfg = { name: string ; size:node ; entry:node ; 
	     succs: node list PTree.t ; 
             preds: node list PTree.t }

module DomTreeCFG = struct

  open ExternSSAgen
 
  let entry f = int_of_positive f.entry 

  let size f = (int_of_positive f.size) + 1

  let array_elements rank t =
    let n = Array.length t in
    let l = ref [] in
    for k=0 to n-1 do
      let i = rank.(n-1-k) in (* modif ici *)
      (* Printf.printf "D[%d] = %d\n" i t.(i); *)
      if t.(i) >= 0 then
	l := (positive_of_int i, positive_of_int t.(i)) :: !l
    done;
    !l

  let succ_and_pred f = 
    let succ = f.succs in
    let pred = f.preds in
    ((fun i -> 
      match PTree.get (positive_of_int i) succ with
	None -> []
      | Some l -> List.map int_of_positive l),
     (fun i -> 
       match PTree.get (positive_of_int i) pred with
	 None -> []
       | Some l -> List.map int_of_positive l))

  let idom f = 
    let (succ,pred) = succ_and_pred f in 
    let entry = entry f in
    let size = size f in
    let (idom,_,rank) = Dominator.dominator succ pred entry size in 
    let list_assoc_idom = array_elements rank idom in
    list_assoc_idom

  let make_test f = 
    let debug = false in
    let (succ,pred) = succ_and_pred f in 
    let entry = entry f in
    if debug then
      Printf.printf "ENTRY = %d\n" entry;
    let size = size f in
    let (idom,_,_) = Dominator.dominator succ pred entry size in 
    if debug then
      for i=0 to (size-1) do
	Printf.printf "idom[%2d] = %2d\n" i idom.(i)
      done;
    let succ = Array.init size (fun _ -> []) in
    Array.iteri
      (fun u v -> (* idom(u) = v *)
	if (v = -1) then assert (u=entry)
	else succ.(v) <- u::succ.(v)) idom;
    if debug then
      Array.iteri
	(fun i s ->
	  Printf.printf " %2d ->" i;
	  List.iter (Printf.printf " %d") s;
	  print_newline ())
	succ;
    let q = Stack.create () in
    let dfs_in = Array.init size (fun  _ -> -1) in
    let dfs_out = Array.init size (fun  _ -> -1) in
    let marked = Array.init size (fun  _ -> false) in
    let count = ref 0 in
    marked.(entry) <- true;
    Stack.push entry q;
    while not (Stack.is_empty q) do
      let i = Stack.pop q in
      if dfs_in.(i) >= 0 then 
	begin
	  dfs_out.(i) <- !count; incr count
	end
      else
	begin
	  dfs_in.(i) <- !count; incr count;
	  Stack.push i q;
	  List.iter 
	    (fun j -> 
	      if not marked.(j) then
		begin
		  marked.(j) <- true;
		  Stack.push j q
		end)
	    succ.(i)
	end
    done;
    if debug then
      for i=0 to (size-1) do
	Printf.printf "itv[%2d] = [%2d, %2d]\n" i dfs_in.(i) dfs_out.(i)
      done;
    let dominates pc1 pc2 =
      let i1 = int_of_positive pc1 in
      let i2 = int_of_positive pc2 in
      i1 = i2
      ||
	( dfs_in.(i1) < dfs_in.(i2) 
	  &&
	  dfs_out.(i2) < dfs_out.(i1)) in
    dominates
   
end

type native_cfg = { 
    native_name: string ; 
    native_size: int ;
    native_entry: int ; 
    native_succs: int list array ; 
    native_preds: int list array }

module NativeDomTreeCFG = struct

  (* open ExternSSAgen *)
 
  let entry f = f.native_entry 

  let size f = f.native_size

  let array_elements rank t =
    let n = Array.length t in
    let l = ref [] in
    for k=0 to n-1 do
      let i = rank.(n-1-k) in (* modif ici *)
      (* Printf.printf "D[%d] = %d\n" i t.(i); *)
      if t.(i) >= 0 then
	l := (i, t.(i)) :: !l
    done;
    !l

  let succ_and_pred f = 
    let succ = f.native_succs in
    let pred = f.native_preds in
    ((fun i -> succ.(i)),
     (fun i -> pred.(i)))

  let idom f = 
    let (succ,pred) = succ_and_pred f in 
    let entry = entry f in
    let size = size f in
    let (idom,_,rank) = Dominator.dominator succ pred entry size in 
    let list_assoc_idom = array_elements rank idom in
    list_assoc_idom

  let make_test f = 
    let debug = false in
    let (succ,pred) = succ_and_pred f in 
    let entry = entry f in
    if debug then
      Printf.printf "ENTRY = %d\n" entry;
    let size = size f in
    let (idom,_,_) = Dominator.dominator succ pred entry size in 
    if debug then
      for i=0 to (size-1) do
	Printf.printf "idom[%2d] = %2d\n" i idom.(i)
      done;
    let succ = Array.init size (fun _ -> []) in
    Array.iteri
      (fun u v -> (* idom(u) = v *)
	if (v = -1) then assert (u=entry)
	else succ.(v) <- u::succ.(v)) idom;
    if debug then
      Array.iteri
	(fun i s ->
	  Printf.printf " %2d ->" i;
	  List.iter (Printf.printf " %d") s;
	  print_newline ())
	succ;
    let q = Stack.create () in
    let dfs_in = Array.init size (fun  _ -> -1) in
    let dfs_out = Array.init size (fun  _ -> -1) in
    let marked = Array.init size (fun  _ -> false) in
    let count = ref 0 in
    marked.(entry) <- true;
    Stack.push entry q;
    while not (Stack.is_empty q) do
      let i = Stack.pop q in
      if dfs_in.(i) >= 0 then 
	begin
	  dfs_out.(i) <- !count; incr count
	end
      else
	begin
	  dfs_in.(i) <- !count; incr count;
	  Stack.push i q;
	  List.iter 
	    (fun j -> 
	      if not marked.(j) then
		begin
		  marked.(j) <- true;
		  Stack.push j q
		end)
	    succ.(i)
	end
    done;
    if debug then
      for i=0 to (size-1) do
	Printf.printf "itv[%2d] = [%2d, %2d]\n" i dfs_in.(i) dfs_out.(i)
      done;
    let dominates pc1 pc2 =
      let i1 = pc1 in
      let i2 = pc2 in
      i1 = i2
      ||
	( dfs_in.(i1) < dfs_in.(i2) 
	  &&
	  dfs_out.(i2) < dfs_out.(i1)) in
    dominates

end
