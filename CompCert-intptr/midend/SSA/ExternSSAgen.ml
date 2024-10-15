open Camlcoq
open BinNums
open Datatypes
open Maps
open Registers
open RTL

let ssa f = None

let map_os f = function
  | Coq_inl r -> Coq_inl (f r)
  | Coq_inr s -> Coq_inr s

let ptset_to_string f s =
  let l = Ptset.elements s in
    match l with
	[] -> "{}"
      | x::q -> Printf.sprintf "{%s%s}" (f x) 
	  (List.fold_right (fun i-> Printf.sprintf ",%s%s" (f i)) q "")

let rename_instr node rename_def rename_use = function
  | Iop(op, args, res, s) -> 
      SSA.Iop(op,List.map rename_use args, rename_def res, s)
  | Iload(chunk, addr, args, dst, s) ->
      SSA.Iload(chunk, addr, List.map rename_use args, rename_def dst, s)
  | Istore(chunk, addr, args, src, s) ->
      SSA.Istore(chunk, addr, List.map rename_use args, rename_use src, s)
  | Icall(sg, fn, args, res, s) ->
      SSA.Icall(sg, map_os rename_use fn, List.map rename_use args, rename_def res, s) 
  | Itailcall(sg, fn, args) -> 
      SSA.Itailcall(sg, map_os rename_use fn, List.map rename_use args)
  | Ibuiltin(ef, args, res, s) ->
      SSA.Ibuiltin(ef, List.map (AST.map_builtin_arg rename_use) args, AST.map_builtin_res rename_def res, s) 
  | Icond(cond, args, s1, s2) ->
      SSA.Icond(cond, List.map rename_use args, s1, s2) 
  | Ijumptable(arg, tbl) ->
      SSA.Ijumptable(rename_use arg, tbl) 
  | Ireturn None -> SSA.Ireturn None
  | Ireturn (Some arg) -> SSA.Ireturn (Some (rename_use arg))
  | Inop s -> SSA.Inop s

let int_of_positive p = (P.to_int p) - 1
  (* let i = camlint_of_positive p in *)
  (*   (Int32.to_int i) -1 *)

let rec positive_of_int n =
  if n = 0 then assert false else
  if n = 1 then Coq_xH else
  if n land 1 = 0
  then Coq_xO (positive_of_int (n lsr 1))
  else Coq_xI (positive_of_int (n lsr 1))

let positive_of_int n = positive_of_int (n+1)

let rec nat_of_int n =
  assert (n >= 0);
  if n = 0 then O else S (nat_of_int (n-1))

let rec int_of_nat n =
  match n with
    | O -> 0
    | S n -> 1+ int_of_nat n


let succ f = 
  let map = RTLdfs.successors_map f in
    fun i -> 
      match PTree.get (positive_of_int i) map with
	  None -> []
	| Some l -> List.map int_of_positive l

let succ_and_pred f = 
  let succ = RTLdfs.successors_map f in
  let pred = Kildall.make_predecessors f.RTLdfs.fn_code RTLdfs.successors_instr in
    ((fun i -> 
	match PTree.get (positive_of_int i) succ with
	    None -> []
	  | Some l -> List.map int_of_positive l),
     (fun i -> 
	match PTree.get (positive_of_int i) pred with
	    None -> []
	  | Some l -> List.map int_of_positive l))
     

let entry f =
  int_of_positive f.RTLdfs.fn_entrypoint

let size f = 
  1+ int_of_positive (RTLnorm.get_max f.RTLdfs.fn_code)

(* [find_index x l] return the position of element [x] in list [l]. 
   @raise Not_found if [x] does not appear in [l]. *)
let find_index x l = 
  let rec aux i = function
      [] -> raise Not_found
    | y::q ->
	if x=y then i 
	else aux (i+1) q in
    aux 0 l

let var_def  = function
    None -> Ptset.empty
  | Some ins ->
      match ins with
	| Iop (_,_,r,_)
	| Iload (_,_,_,r,_) 
	| Icall (_,_,_,r,_)
	| Ibuiltin (_,_,AST.BR(r),_) -> Ptset.singleton (int_of_positive r)
	| _ -> Ptset.empty

let var_defs f entry = 
  PTree.fold
    (fun map i ins ->
       match ins with
	| Iop (_,_,r,_)
	| Iload (_,_,_,r,_) 
	| Icall (_,_,_,r,_)
	| Ibuiltin (_,_,AST.BR(r),_) ->  
	    Ptmap.add ~merge:Ptset.union (int_of_positive r) (Ptset.singleton (int_of_positive i)) map
	| _ -> map)     
      f.RTLdfs.fn_code
    (List.fold_right
       (fun r -> Ptmap.add (int_of_positive r) (Ptset.singleton entry))
       f.RTLdfs.fn_params Ptmap.empty)

let all_vars f = 
  PTree.fold
    (fun set i ins ->
       let add x = Ptset.add (int_of_positive x) in
       let add_list l = List.fold_right add l in
       match ins with
	| Icall (_,Coq_inl x,l,r,_) -> add_list (x::r::l) set
	| Iop (_,l,r,_)
	| Iload (_,_,l,r,_) 
	| Istore (_,_,l,r,_) 
	| Icall (_,_,l,r,_)
	| Icond (_,l,r,_) 
	| Itailcall (_,Coq_inl r,l) -> add_list (r::l) set
	| Ibuiltin (_,l,(AST.BR r),_) -> add_list (r::AST.params_of_builtin_args l) set
	| Itailcall (_,_,l) -> add_list l set
	| Ijumptable (r,_)  
	| Ireturn (Some r) ->  add r set
	| _ -> set)     
      f.RTLdfs.fn_code
    Ptset.empty

let var_use  = function
    None -> Ptset.empty
  | Some ins ->
      match ins with
	| Icall (_,Coq_inl r,l,_,_) 
	| Itailcall (_,Coq_inl r,l) 
	| Istore (_,_,l,r,_) ->
	    List.fold_right (fun r -> Ptset.add (int_of_positive r)) (r::l) Ptset.empty
	| Iop (_,l,_,_)
	| Iload (_,_,l,_,_)
	| Icall (_,_,l,_,_) 
	| Itailcall (_,_,l)
	| Icond (_,l,_,_) ->      
	   List.fold_right (fun r -> Ptset.add (int_of_positive r)) l Ptset.empty
        | Ibuiltin (_,l,_,_) ->
           List.fold_right (fun r -> Ptset.add (int_of_positive r)) (AST.params_of_builtin_args l) Ptset.empty
	| Ijumptable (r,_)
	| Ireturn (Some r) -> Ptset.singleton (int_of_positive r)
	| _ -> Ptset.empty

(* see:  
   Cytron, Ron; Ferrante, Jeanne; Rosen, Barry K.; Wegman, Mark N.; 
   and Zadeck, F. Kenneth (1991). 
   "Efficiently computing static single assignment form and the 
   control dependence graph". 
   ACM Transactions on Programming Languages and Systems 13 (4): 451–490.*)
let place_phi_nodes n var_defs domf live =
  let place = ref Ptmap.empty in
  let place_node n v =
    place := Ptmap.add ~merge:Ptset.union n (Ptset.singleton v) !place in
  let iter_count = ref 0 in
  let has_already = Array.make n 0 in
  let work = Array.make n 0 in
  let workset = ref Ptset.empty in
    Ptmap.iter
      (fun v defs -> 
	 incr iter_count;
	 Ptset.iter 
	   (fun x -> 
	      work.(x) <- !iter_count;
	      workset := Ptset.add x !workset)
	   defs;
	 while not (Ptset.is_empty !workset) do
	   let x = Ptset.choose !workset in
	     workset := Ptset.remove x !workset;
	     Ptset.iter
	       (fun y -> 
		  if has_already.(y) < !iter_count then 
		    begin
		      if live v y then place_node y v; 
		      has_already.(y) <- !iter_count;
 		      if work.(y) < !iter_count then 
			begin
			  workset := Ptset.add y !workset;
			  work.(y) <- !iter_count
			end
		    end)
	       (domf x)
	 done)
      var_defs;
    !place

let init_map set value =
  Ptset.fold (fun x map -> Ptmap.add x value map) set Ptmap.empty

let rec length_pos = function
  | Coq_xO p0 
  | Coq_xI p0 -> Datatypes.S  (length_pos p0)
  | Coq_xH -> Datatypes.O

(* Compute the rights indexes for each variable use and def.
   See:  
   Cytron, Ron; Ferrante, Jeanne; Rosen, Barry K.; Wegman, Mark N.; 
   and Zadeck, F. Kenneth (1991). 
   "Efficiently computing static single assignment form and the 
   control dependence graph". 
   ACM Transactions on Programming Languages and Systems 13 (4): 451–490.*)
let rename n entry params code vars children preds succs phi_nodes =
  let c = ref (init_map vars 0) in
  let s = ref (init_map vars []) in
  let rename_use = Array.make n Ptmap.empty in
  let rename_def = ref Ptmap.empty in
  let rename_def_phi = ref Ptmap.empty in
    for i=0 to n-1 do
      if List.length (preds i) > 1 then
	rename_def_phi := Ptmap.add i Ptmap.empty !rename_def_phi
    done;
  let phi_nodes = 
    Ptmap.mapi 
      (fun n s -> 
	 let n_preds = List.length (preds n) in
	   Ptset.fold 
	     (fun v -> Ptmap.add v (Array.make n_preds (-1))) 
	     s 
	     Ptmap.empty) 
      phi_nodes 
  in
  let phi_nodes i =
    try Ptmap.find i phi_nodes with Not_found -> Ptmap.empty in
  let search_h = ref [] in
  let top_s i x = 
    try
      (match Ptmap.find x !s  with
	 | [] -> 
	     Printf.printf "ERROR top(s(%d)) in %d\n" x i;
	     assert false
	 | i::_ -> i)
    with Not_found -> 
      Printf.printf "ERROR s(%d) not found at node %d\n"  x i;
      assert false in
  let pop_s x = 
    try
      (match Ptmap.find x !s  with
	 | [] -> assert false
	 | _::q -> s := Ptmap.add x q !s)
    with Not_found -> assert false in
  let rec search x =
    search_h := x :: !search_h;
    let ins = PTree.get (positive_of_int x) code in
    (* def : set of variables that are defined in x *)
    let def = if x=entry then vars 
      (* at entry point, the set contains all vars *)
    else var_def ins in
      Ptmap.iter
	(fun v _ -> 
	   let xmap = 
	     try Ptmap.find x !rename_def_phi
	     with Not_found -> Ptmap.empty
	   in
	   let i = Ptmap.find v !c in
	     rename_def_phi := 
	       Ptmap.add 
		 x (Ptmap.add v i xmap) (* at point x, v |-> v_i *)
		 !rename_def_phi;
	     s := Ptmap.add v (i::(Ptmap.find v !s)) !s;
	     c := Ptmap.add v (i+1) !c)
	(phi_nodes x);
      let vars = var_use ins in
	  rename_use.(x) <-
	    Ptset.fold 
	    (fun v -> Ptmap.add v (top_s x v)) vars Ptmap.empty;
      Ptset.iter
	(fun v ->
	   let xmap = 
	     try Ptmap.find x !rename_def
	     with Not_found -> Ptmap.empty
	   in
	   let i = Ptmap.find v !c in
	     rename_def := 
	       Ptmap.add 
		 x (Ptmap.add v i xmap) 
		 !rename_def;
	     s := Ptmap.add v (i::(Ptmap.find v !s)) !s;
	     c := Ptmap.add v (i+1) !c)
	def;
      List.iter
	(fun y -> 
	   let preds = preds y in
	   let index_x = find_index x preds in
	   let phi = phi_nodes y in
	     Ptmap.iter (fun v args -> args.(index_x) <- top_s y v) phi)
	(succs x);
      List.iter search (children x);
      Ptset.iter pop_s def;
      Ptmap.iter
	(fun v _ -> pop_s v)
	(phi_nodes x)
  in
    search (entry);
    (fun i -> 
       try
	 let i = int_of_positive i in
	 let xmap = Ptmap.find i !rename_def in
	   fun v -> 
	     positive_of_int (Ptmap.find (int_of_positive v) xmap)
       with Not_found -> fun v -> assert false), 
    (fun i -> 
       try
	 let map = rename_use.(int_of_positive i) in
	   fun v -> 
	     positive_of_int (Ptmap.find (int_of_positive v) map)
       with Not_found -> fun v -> assert false),
    (Ptmap.fold
       (fun i map_phi_def ->
	  PTree.set 
	    (positive_of_int i)
	    (Ptmap.fold
	       (fun x l acc -> 
		  let xp = positive_of_int x in
		    ((xp,positive_of_int (Ptmap.find x map_phi_def)),
		     List.map (fun i -> (xp, positive_of_int i)) (Array.to_list l))
		    :: acc) (phi_nodes i) []))
       !rename_def_phi PTree.empty),
    (Datatypes.S (length_pos (positive_of_int (Ptmap.fold (fun _ -> max) !c 0))))

(* Compute the rights indexes for each variable use and def.
   See:  
   Cytron, Ron; Ferrante, Jeanne; Rosen, Barry K.; Wegman, Mark N.; 
   and Zadeck, F. Kenneth (1991). 
   "Efficiently computing static single assignment form and the 
   control dependence graph". 
   ACM Transactions on Programming Languages and Systems 13 (4): 451–490.*)
let rename_V2 n entry params code vars children preds succs phi_nodes =
  let c = ref (init_map vars 0) in
  let s = ref (init_map vars []) in
  let rename_def = ref Ptmap.empty in
  let rename_def_phi = ref Ptmap.empty in
    for i=0 to n-1 do
      if List.length (preds i) > 1 then
	rename_def_phi := Ptmap.add i Ptmap.empty !rename_def_phi
    done;
  let phi_nodes i =
    try Ptmap.find i phi_nodes with Not_found -> Ptset.empty in
  let search_h = ref [] in
  let pop_s x = 
    try
      (match Ptmap.find x !s  with
	 | [] -> assert false
	 | _::q -> s := Ptmap.add x q !s)
    with Not_found -> assert false in
  let rec search x =
    search_h := x :: !search_h;
    let ins = PTree.get (positive_of_int x) code in
    (* def : set of variables that are defined in x *)
    let def = if x=entry then vars 
      (* at entry point, the set contains all vars *)
    else var_def ins in
      Ptset.iter
	(fun v -> 
	   let xmap = 
	     try Ptmap.find x !rename_def_phi
	     with Not_found -> Ptmap.empty
	   in
	   let i = Ptmap.find v !c in
	     rename_def_phi := 
	       Ptmap.add 
		 x (Ptmap.add v i xmap) (* at point x, v |-> v_i *)
		 !rename_def_phi;
	     s := Ptmap.add v (i::(Ptmap.find v !s)) !s;
	     c := Ptmap.add v (i+1) !c)
	(phi_nodes x);
      let _ = var_use ins in
      Ptset.iter
	(fun v ->
	   let i = Ptmap.find v !c in
	     rename_def := 
	       Ptmap.add 
		 x i 
		 !rename_def;
	     s := Ptmap.add v (i::(Ptmap.find v !s)) !s;
	     c := Ptmap.add v (i+1) !c)
	def;
      List.iter search (children x);
      Ptset.iter pop_s def;
      Ptset.iter
	(fun v -> pop_s v)
	(phi_nodes x)
  in
    search (entry);
    !rename_def, 
    !rename_def_phi,
    (Datatypes.S (length_pos (positive_of_int (Ptmap.fold (fun _ -> max) !c 0))))

let ssa_function_to_function_wo_inv f = f

let remove_dead_node f =
  let succ = RTLdfs.successors_map f in
  let succ i = match PTree.get i succ with None -> [] | Some l -> l in
  let seen = ref PTree.empty in
  let has_been_seen i = match PTree.get i !seen with None -> false | Some _ -> true in
  let rec dfs v =
    seen := PTree.set v () !seen;
    List.iter (fun w -> if not (has_been_seen w) then dfs w) (succ v) in
    dfs f.RTLdfs.fn_entrypoint;
    let new_code = 
      PTree.fold
	(fun new_code n ins ->
	   if has_been_seen n then new_code else PTree.remove n new_code)
	f.RTLdfs.fn_code f.RTLdfs.fn_code in
      { RTLdfs.fn_sig = f.RTLdfs.fn_sig;
	RTLdfs.fn_params = f.RTLdfs.fn_params; 
        RTLdfs.fn_stacksize = f.RTLdfs.fn_stacksize;
	RTLdfs.fn_code = new_code;
	RTLdfs.fn_entrypoint = f.RTLdfs.fn_entrypoint;
        RTLdfs.fn_dfs = [];
      }

let output_cfg fd succ =
  Printf.printf "digraph G { node [style=rounded, shape=box] ";
  PTree.fold (fun () n ins -> 
		let i = int_of_positive n in
		let succ = succ i in
		  List.iter (Printf.printf "\"N%d\" -> \"N%d\"; " i ) succ)
    (fd.RTLdfs.fn_code) ();
  Printf.printf "}\n"


let genSSA_V2 f live = 
  let (succ,pred) = succ_and_pred f in 
  let entry = entry f in
  let size = size f in
  let (idom,is_dead,_) = Dominator.dominator succ pred entry size in 
  let pred i = List.filter (fun j -> not (is_dead j)) (pred i) in
  let domf = Dominance.dominance_frontier size pred idom is_dead in
  let var_defs = var_defs f entry in
  let is_live x i = Regset.mem (positive_of_int x) (live (positive_of_int i)) in
  let phi_nodes = place_phi_nodes size var_defs (fun i -> domf.(i)) is_live in
  let children = Dominator.make_children idom in
  let params = List.map int_of_positive f.RTLdfs.fn_params in
  let (rename_def,rename_def_phi,max_index) = rename_V2 size entry params f.RTLdfs.fn_code 
						(all_vars f) children pred succ phi_nodes in
  let ptmap_to_ptree m = Ptmap.fold 
			   (fun n i -> PTree.set (positive_of_int n) (positive_of_int i))
			   m PTree.empty in
  let def_phi = Ptmap.fold
		  (fun n m -> PTree.set (positive_of_int n) (ptmap_to_ptree m))
		  rename_def_phi PTree.empty in
  let def = ptmap_to_ptree rename_def in
    (max_index, def, def_phi)

let genSSA f live = 
  let (max, def, phi) = genSSA_V2 f live in 
    ((max, def), phi)


