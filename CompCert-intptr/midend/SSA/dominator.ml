(* TODO
 - this is not yet the sophisticated version of Lengauer-Tarjan algorithm
 - many array accesses could be factorized 
*)


let make_children father =
  let n = Array.length father in
  let children = Array.make n Ptset.empty in
    for i=0 to n-1 do
      let f = father.(i) in
	if f>=0 then children.(f) <- Ptset.add i children.(f)
    done;
    fun i -> Ptset.elements children.(i)

(** [add v t w] adds integer [v] to the list in [t.(w)] *)
let add v t w =
  t.(w) <- v :: t.(w)
  

(* We follow 'A Fast Algorithm for Finding Dominators in a Flowgraph'
   by Lengauer and Tarjan *)
(* [r] is an entry point in [0 .. n-1] *)
(* returns (dom,_) where, dom(w) = v is the immediate dominator of w. *)
let dominator succ pred r n =
  let semi = Array.make n (-1) in
  let vertex = Array.make n (-1) in
  let label = Array.make n (-1) in
  let dom = Array.make n (-1) in
  let ancestor = Array.make n (-1) in
  let parent = Array.make n (-1) in
  let bucket = Array.make n [] in
  let nb_dfs = ref 0 in
  let nb_dead = ref 0 in
  let rec dfs v =
    semi.(v) <- !nb_dfs;
    vertex.(!nb_dfs) <- v;
    label.(v) <- v;
    incr nb_dfs;
    List.iter
      (fun w -> 
	 if semi.(w) = -1 then 
	   begin
	     parent.(w) <- v;
	     dfs w
	   end)
      (succ v) in
  let rec compress v =
    if not (ancestor.(ancestor.(v)) = -1) then
      begin
	compress ancestor.(v);
	if semi.(label.(ancestor.(v))) < semi.(label.(v)) then
	  label.(v) <- label.(ancestor.(v));
	ancestor.(v) <- ancestor.(ancestor.(v))
      end in 
  let eval v =
    if ancestor.(v) = -1 then v
    else begin
      compress v;
      label.(v)
    end in 
  let link v w = ancestor.(w) <- v in
    dfs r;
    Array.iteri
      (fun i w ->
	 if (w = -1) then begin
	   Printf.printf "Error: point %d seems not reachable !!!\n" (i+1);
	   incr nb_dead
	 end)
      semi;
    for i= !nb_dfs-1 downto 1 do 
      let w = vertex.(i) in
	List.iter 
	  (fun v -> 
	     if semi.(v) >=0 then
	       let u = eval v in 
		 if semi.(u) < semi.(w) then semi.(w) <- semi.(u))
	  (pred w);
	add w bucket vertex.(semi.(w));
	link parent.(w) w;
	List.iter 
	  (fun v ->
	     let u = eval v in
	       dom.(v) <- if semi.(u) < semi.(v) then u else parent.(w))
	    bucket.(parent.(w));
	bucket.(parent.(w)) <- []
 done;
 for i=1 to !nb_dfs-1 do
   let w = vertex.(i) in
     if w>=0 && not (dom.(w) = vertex.(semi.(w))) then
       dom.(w) <- dom.(dom.(w))
 done;
 (dom, (fun i -> semi.(i)<0), vertex)

(* TEST

module Dict = Map.Make(struct type t = string let compare = compare end)

let create_dict l =
  let idx = ref (-1) in
  let nth = Array.make (List.length l) "" in
  let dict =
    List.fold_left (fun dict s -> 
		      incr idx; 
		      nth.(!idx) <- s; 
		      Dict.add s !idx dict) Dict.empty l in
    (dict,nth)

let create_edges l =
  List.fold_left (fun dict (s,succs) -> Dict.add s succs dict) Dict.empty l

let example = 
  let (dict,nth) = create_dict ["R";"C";"F";"G";"I";"J";"K";"B";"E";"H";"A";"D";"L"] in
  let edges = create_edges ["R", ["C";"B";"A"];
			    "C", ["F";"G"];
			    "F", ["I"];
			    "G", ["I"; "J"];
			    "I", ["K"];
			    "J", ["I"];
			    "K", ["I";"R"];
			    "B", ["E"; "A"; "D"];
			    "E", ["H"];
			    "H", ["E"; "K"];
			    "A", ["D"];
			    "D", ["L"];
			    "L", ["H"]] in

  let dom = dominator 
      (fun i -> List.map (fun s -> Dict.find s dict) (Dict.find nth.(i) edges))
      (Dict.find "R" dict)
      (Dict.cardinal dict) in

    Array.iteri 
      (fun i j -> Printf.printf "%s --> %s\n" nth.(i) (if j<0 then "NONE" else nth.(j)))
      dom
*)
      
    
