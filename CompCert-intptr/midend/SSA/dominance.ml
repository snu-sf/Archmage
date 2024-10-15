(* dominance frontier set 
   See: 
   Cooper, Keith D.; Harvey, Timothy J.; and Kennedy, Ken (2001). 
   A Simple, Fast Dominance Algorithm *)
let dominance_frontier n preds idom is_dead = 
  let domf = Array.make n Ptset.empty in
    for i=0 to (n-1) do
      if not (is_dead i) then
	let preds = preds i in
	let idom_i = idom.(i) in
	  if List.length preds > 1 then
	    List.iter
	      (fun p -> 
		 let runner = ref p in
		   while !runner <> idom_i do
		     domf.(!runner) <- Ptset.add i domf.(!runner);
		     runner := idom.(!runner)
		   done
	      )
	      preds 
    done;
    domf
