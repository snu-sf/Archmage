open SSA
open SSAutils
open Maps

let debugmode = false

type reg = int
type pc = int
type operation = Op of int | OPhi of pc
type position = OpPos of SSA.node | OPhiPos of SSA.node*Datatypes.nat

type instruction = { target: reg; op: operation; args: reg list; pos:position}

type input = instruction Ptmap.t

let make target op args pos = { target=target; op=op; args=args; pos=pos}

let print_list sep f = function
    []-> ""
  | [x] -> f x
  | x::q -> List.fold_left (fun s x -> s^sep^(f x)) (f x) q

let print_instruction i =
  Printf.sprintf "X%d <- %s(%s)"
    i.target
    (match i.op with
       | Op s -> "OP"^(string_of_int s)
       | OPhi pc -> "PHI_"^(string_of_int pc))
    (print_list ", "  (Printf.sprintf "X%d") i.args)

(*
  1: j0 <- 1;
     k0 <- 1;
  2: j1 <- PHI2(j0,j4);
     k1 <- PHI2(k0,k4);
     goto 3, 4, exit;
  3: j2 <- j1 + 1;
     k2 <- k1 + 1;
     goto 5;
  4: j3 <- j1 + 2;
     k3 <- k1 + 2;
     goto 5;
  5: j4 <- PHI5(j2,j3);
     k4 <- PHI5(k2,k3);
     goto 2;
*)


module SSAvarHash = struct

  let hashtab = Hashtbl.create 17 
  let next = ref (-1) 
  let from_hash = ref Ptmap.empty
    
  let init () =
    Hashtbl.clear hashtab;
    next := -1;
    from_hash := Ptmap.empty
      
  let hash x =
    try Hashtbl.find hashtab x
    with Not_found ->
      incr next;
      Hashtbl.add hashtab x !next ;
      from_hash := Ptmap.add !next x !from_hash;
      !next
	
  let from_hash x =
    try Ptmap.find x !from_hash
    with Not_found -> assert false
      
  let show_hash () =
    Hashtbl.iter (fun _ y -> Printf.printf " _ -> %d\n" y) hashtab 

end


type expr = Operation of (operation * int list) | Param of int

let string_of_expr = function
  | Param i -> Printf.sprintf "P(X%d)" i
  | Operation (op,args) ->
    Printf.sprintf "%s[%s]"
      (match op with
      | Op s -> "OP"^(string_of_int s)
      | OPhi pc -> "PHI_"^(string_of_int pc))
      (List.fold_left (fun s i -> "X"^(string_of_int i)^" "^s) "" args)

module Graph = struct
  type t = {
    ssag_size : int;
    ssag_eqs: instruction Ptmap.t;
    ssag_rpo: int list Lazy.t;
    test_dom: node->node->bool;
    entrypoint: node
  }

  let uses eqs = 
    Ptmap.fold 
      (fun _ eq s -> List.fold_right Ptset.add eq.args s)
      eqs Ptset.empty 
      
  let defs eqs  = 
    Ptmap.fold 
      (fun _ eq def -> Ptset.add eq.target def)
      eqs Ptset.empty 

  let size g = g.ssag_size

  let eqs g = g.ssag_eqs

  let def g x =
    try Some (Ptmap.find x g.ssag_eqs)
    with Not_found -> None

  let ssa_succ f pc =
    match PTree.get pc f.fn_code with
    | None -> []
    | Some ins -> SSA.successors_instr ins

  let ssa_defs f params pc =
    if pc = f.fn_entrypoint then params
    else
      let def_code = 
	match PTree.get pc f.fn_code with
	| Some (Iop (op, args, res, s)) when not (Op.op_depends_on_memory op) -> 
	  [SSAvarHash.hash res]
	| _ -> [] in
      let def_phi = 
	match PTree.get pc f.fn_phicode with
	| None -> []
	| Some phib ->
	  List.map (fun (Iphi (_,dst)) -> SSAvarHash.hash dst) phib in
      def_phi @ def_code

  let compute_rop f params n =
    let q = Stack.create () in
    let marked = ref PTree.empty in
    let enum = Array.init n (fun _ -> -1) in
(*    Printf.printf "Expecting %d vars\n" n; *)
    let count = ref 0 in
    Stack.push f.fn_entrypoint q;
    marked := PTree.set f.fn_entrypoint () !marked;
    while not (Stack.is_empty q) do
      let pc = Stack.pop q in
      let succ = ssa_succ f pc in 
      let defs = ssa_defs f params pc in
(*      Printf.printf "  node %d defines" (ExternSSAgen.int_of_positive pc); 
      List.iter (Printf.printf " X%d") defs;
      print_newline (); flush stdout; *)
      List.iter (fun x -> enum.(!count) <- x; incr count) defs;
      List.iter 
	(fun j -> 
	  if PTree.get j !marked = None then 
	    begin
	      marked := PTree.set j () !marked;
	      Stack.push j q
	    end)
	succ
    done;
    Array.to_list enum      

  let make f dom_test eqs = 
    let defs = defs eqs in
    let uses = uses eqs in
    let all = Ptset.union uses defs in
    let params = Ptset.elements (Ptset.diff uses defs) in
    let n = Ptset.cardinal all in
    {
      ssag_size = n;
      ssag_eqs = eqs;
      ssag_rpo = lazy (compute_rop f params n);
      test_dom = dom_test ;
      entrypoint = f.fn_entrypoint
    }

  let rpo g = Lazy.force g.ssag_rpo

  let show g =
    Ptmap.iter (fun _ i -> Printf.printf "%s\n" (print_instruction i)) g.ssag_eqs;
    List.iter (Printf.printf "%2d ") (rpo g); print_newline ()
      
end

(*
let example =
  let make target op args = make target op args (OpPos BinNums.Coq_xH) in
  let eqs = List.fold_left (fun m i -> Ptmap.add i.target i m) Ptmap.empty
    [
      make 0 (Op 1) [];
      make 1 (Op 1) [];
      make 2 (OPhi 2) [0;8];
      make 3 (OPhi 2) [1;9];
      make 4 (Op 3) [2];    
      make 10 (Op 3) [11];    
      make 5 (Op 3) [3];    
      make 6 (Op 4) [2];    
      make 7 (Op 4) [3];    
      make 8 (OPhi 5) [4;6];
      make 9 (OPhi 5) [5;7];
    ] in
  Graph.make eqs
*)

(*
let _ = Graph.show example
*)

module ExprHash = struct

  let hashtab : (expr, int) Hashtbl.t = Hashtbl.create 17 
  let next = ref (-1) 

  let reset () =
    Hashtbl.clear hashtab;
    next := -1

  let hash x =
    try Hashtbl.find hashtab x
    with Not_found ->
      incr next;
      Hashtbl.add hashtab x !next ;
      !next

end


type numbering = { num: reg Ptmap.t; classes: reg list Ptmap.t; drepr: (Registers.reg * ssa_def) Ptmap.t }

let constant = function
  | Param _ -> true
  | Operation (_,[]) -> true
  | _ -> false

let instr eqs x =
  try Ptmap.find x eqs with Not_found -> failwith "no instr found"

let show_msg msg =
  if false then
    print_string msg; flush stdout

let rec find_leader g x pc = function
  | [] -> None
  | y::q ->
(*    show_msg "."; *)
    (match (instr (Graph.eqs g) y).pos with
    |  OpPos pc_y when g.Graph.test_dom pc_y pc -> Some (SSAvarHash.from_hash y,SDIop pc_y) 
    | _ -> find_leader g x pc q) 

let find_leader g x pc = 
  show_msg "find_leader";
  let res = find_leader g x pc in
  show_msg ".\n"; 
  res

let pc_of_pos = function
  | OpPos pc -> pc
  | OPhiPos (pc,_) -> pc

let def_of_pos = function
  | OpPos pc -> SDIop pc
  | OPhiPos (pc,idx) -> SDPhi (pc,idx)

let gvn_def g vn lead classe repr x =
  match Graph.def g x with
  | None -> vn.(x) <- ExprHash.hash (Param x); false
  | Some instr ->
    let pc = pc_of_pos instr.pos in
    let expr = Operation (instr.op, List.map (fun i -> vn.(i)) instr.args) in
    let temp = ExprHash.hash expr in
    classe.(temp) <- x::classe.(temp);
    (match find_leader g x pc repr.(temp) with
    | None -> 
      lead := Ptmap.add x (SSAvarHash.from_hash x,def_of_pos instr.pos) !lead;
      repr.(temp) <- x::repr.(temp)
    | Some leader ->
      lead := Ptmap.add x leader !lead);
    if vn.(x) <> temp then 
      begin
	vn.(x) <- temp;
	true
      end 
    else false

let show_vn g vn =
  if false then
    begin
      List.iter (fun _ -> Printf.printf "---") (Graph.rpo g); Printf.printf "\n X =";
      List.iter (fun x -> Printf.printf "%2d " x) (Graph.rpo g); Printf.printf "\nVN =";
      List.iter (fun x -> Printf.printf "%2d " vn.(x)) (Graph.rpo g); print_newline ()
    end


let show_gvn msg =
  if false then
    print_string msg; flush stdout

let rec gvn_iter g n vn lead classe repr =
  show_gvn ".";
  show_vn g vn;
  ExprHash.reset ();
  Array.fill repr 0 n [];
  Array.fill classe 0 n [];
  let changed = ref false in
  List.iter 
    (fun def -> 
      changed := gvn_def g vn lead classe repr def || !changed)
    (Graph.rpo g);
  if !changed then gvn_iter g n vn lead classe repr else show_vn g vn

let gvn g = 
  show_gvn "Starting gvn fixpoint solving";
  let n = Graph.size g in
  let vn = Array.init n (fun _ -> -1) in
  let repr = Array.init n (fun _ -> []) in
  let lead = ref Ptmap.empty in
  let classe = Array.init n (fun _ -> []) in
  gvn_iter g n vn lead classe repr;
  show_gvn "done\n";
  (vn, !lead, repr, classe)

(* let _ = gvn example *)

let debug_lead lead =
  for i=0 to (Array.length lead -1) do
    Printf.printf "%3d:" i;
    List.iter (Printf.printf " %d") lead.(i);
    print_newline ()
  done

let build_numbering g (vn, drepr, lead, classes0) =
  let classes = ref Ptmap.empty in
  let repr = ref Ptmap.empty in
  if debugmode then debug_lead lead;
  for i=0 to (Array.length lead -1) do
    match classes0.(i) with
    | [] -> ()
    | x::q -> 
      classes := Ptmap.add x q !classes;
      List.iter (fun y -> repr := Ptmap.add y x !repr) (x::q)
  done;
  { num = !repr; classes = !classes; drepr = drepr }

let build_equations f =
  let next = ref (-1) in
  let hashtb = Hashtbl.create 17 in
  let hash_op op =
    try Hashtbl.find hashtb op
    with Not_found ->
      incr next;
      Hashtbl.add hashtb op !next;
      !next in
  let eqs1 =
    PTree.fold
      (fun eqs pc ins ->
	 match ins with
	   | Iop (op, args, res, s) when not (Op.op_depends_on_memory op) -> 
	       let res' = SSAvarHash.hash res in
		 Ptmap.add res' 
		   { target = res';
		     args = List.map SSAvarHash.hash args;
		     op = Op (hash_op op);
		     pos = OpPos pc} eqs
	   | _ -> eqs) f.fn_code Ptmap.empty in
  let eqs2 =
    PTree.fold
      (fun eqs pc phib ->
	 fst (List.fold_left
	   (fun (eqs,i) (Iphi (args,res)) ->
	      let res' = SSAvarHash.hash res in
	      (Ptmap.add res' 
		{ target = res';
		  args = List.map SSAvarHash.hash args;
		  op = OPhi (ExternSSAgen.int_of_positive pc);
		  pos = OPhiPos (pc,i)} eqs, Datatypes.S i))
		(eqs,Datatypes.O) phib)) f.fn_phicode eqs1 in
  let _ = if debugmode then Printf.printf "EQUATIONS =\n" in
(*  let _ = if debugmode then Graph.show (Graph.make f tes eqs2) in  *)
    eqs2

let extern_gvn (f':SSA.coq_function) (register_dom_test:ssa_def->node->unit) : ssa_def PTree.t =
  let f = f' in
  let _ = if debugmode then print_string "starting extern_gvn\n" in
  SSAvarHash.init ();
  let eqs = build_equations f in
    if Ptmap.is_empty eqs then PTree.empty
    else
      let g = Graph.make f f'.SSA.fn_dom_test eqs in
      let numbering = build_numbering g (gvn g) in
      let drepr x : (Registers.reg * ssa_def) option =
	try Some (Ptmap.find (SSAvarHash.hash x) numbering.drepr)
	with Not_found -> None in
      let count_optim = ref 0 in 
      let representant = PTree.fold
			   (fun repr pc ins ->
			      match ins with
				| Iop (op, args, res, s) when not (Op.op_depends_on_memory op) -> 
 				  (match drepr res with
				  | Some (x',d') -> 
				    if x'<>res then 
				      begin
					incr count_optim;
					register_dom_test d' pc;
					PTree.set res d' repr;
				      end
				    else repr
				  | _ -> repr)
				| _ -> repr) f.fn_code PTree.empty in
      (* Printf.printf "%d\n" !count_optim; *)
      representant

let extern_gvn2 (f':SSA.coq_function) : ssa_def PTree.t =
  extern_gvn f' (fun _ _ -> ())

let extern_gvn_record_dom_test f =
  let register_dom_test_list : (node*node) list ref = ref [] in
  let register_dom_test d n =
    match d with
    | SDIop d -> register_dom_test_list := (d,n) :: !register_dom_test_list
    | _ -> assert false in
  let _ = extern_gvn f register_dom_test in
  !register_dom_test_list






