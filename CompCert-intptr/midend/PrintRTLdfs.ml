open Printf
open Camlcoq
open Maps
open AST
open RTLdfs

(* Printing of RTLt code *)
let print_instruction = PrintRTL.print_instruction

let print_function pp id f =
  fprintf pp "%s(%a) {\n" (extern_atom id) PrintRTL.regs f.fn_params;
  let instrs =
    List.sort
      (fun (pc1, _) (pc2, _) -> Stdlib.compare pc2 pc1)
      (List.rev_map
        (fun (pc, i) -> (P.to_int pc, i))
        (PTree.elements f.fn_code)) in
  PrintRTL.print_succ pp f.fn_entrypoint
    (match instrs with (pc1, _) :: _ -> pc1 | [] -> -1);
  List.iter (print_instruction pp) instrs;
  fprintf pp "}\n\n"

let print_globdef pp (id, gd) =
  match gd with
  | Gfun(Internal f) -> print_function pp id f
  | _ -> ()

let print_program pp (prog: RTLdfs.program) =
  List.iter (print_globdef pp) prog.prog_defs

let destination : string option ref = ref None
let destination_drtlnorm : string option ref = ref None

let print_if dest prog =
  match !dest with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_program oc prog;
      close_out oc
