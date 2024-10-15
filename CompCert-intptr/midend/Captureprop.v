Require Import Classical.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Events.
Require Import Registers.
Require Import Floats.
Require Import Utils.
Require Import SSA. 
Require Import SSAutils. 
Require Import Utilsvalidproof.
Require Import DomCompute.
Require Import Axioms.
Require Import KildallComp.
Require Import OrderedType.
Require Import Ordered.
Require Import FSets.
Require FSetAVL.
(* Require Import Opt. *)
(* Require Import OptInv. *)
Require Import DLib.
Require Import Errors.
Require Import sflib.

(** * Domtree traversal functions *)

Definition is_capture (i: instruction) :=
  match i with
  | (Ibuiltin EF_capture ((BA p)::nil) (BR res) pc') => Some (res, p)
  | _ => None
  end.

Definition _find_capture (result: list node) (pc: node) (i: instruction) :=
  match (is_capture i) with
  | None => result
  | Some _ => pc::result
  end.

Definition find_capture_all (c: code) :=
  PTree.fold _find_capture c [].

Fixpoint find_parent (nl: list node) (parents: L.t) :=
  match nl with
  | [] => None
  | hd::tl => if (in_set hd parents)
            then Some hd
            else (find_parent tl parents)
  end.

Section CAPTUREPROP.

Variable domtree: PMap.t L.t.

Fixpoint find_capture_root_fuel (fuel:nat) (i: node) (il: list node) : node :=
  match fuel with
  | O => i
  | S fuel' =>
      let parents := (PMap.get i domtree) in
      match (find_parent il parents) with
      | None => i
      | Some i' => find_capture_root_fuel fuel' i' (filter (fun x => (negb (Pos.eqb i' x))) il)
      end
  end.

Definition find_capture_root (i: node) (il: list node) : node :=
  find_capture_root_fuel (Datatypes.length il + 1) i il.

Definition rename_reg (d s: reg) (r: reg) : reg :=
  if (Pos.eqb r s) then d else r.

Fixpoint rename_barg (d s: reg) (b: builtin_arg reg) : builtin_arg reg :=
  match b with
  | BA r => BA (rename_reg d s r)
  | BA_splitlong b1 b2 => BA_splitlong (rename_barg d s b1) (rename_barg d s b2)
  | BA_addptr b1 b2 => BA_addptr (rename_barg d s b1) (rename_barg d s b2)
  | _ => b
  end.

Fixpoint rename_bres (d s: reg) (b: builtin_res reg) : builtin_res reg :=
  match b with
  | BR r => BR (rename_reg d s r)
  | BR_splitlong b1 b2 => BR_splitlong (rename_bres d s b1) (rename_bres d s b2)
  | _ => b
  end.  

Definition subst_instr (d s: reg) (instr: instruction) :=
  let rn := rename_reg d s in
  let rnba := rename_barg d s in
  let rnbr := rename_bres d s in
  match instr with
  | Inop pc' => Inop pc'
  | Iop op args dst pc' => Iop op (map rn args) dst pc'
  | Iload chunk addr args dst pc' => Iload chunk addr (map rn args) dst pc'
  | Istore chunk addr args src pc' => Istore chunk addr (map rn args) (rn src) pc'
  | Icall sig fn args dst pc' => Icall sig fn (map rn args) dst pc'
  | Itailcall sig fn args => Itailcall sig fn (map rn args)
  | Ibuiltin ef args dst pc' => Ibuiltin ef (map rnba args) dst pc'
  | Icond cond args ifso ifnot => Icond cond (map rn args) ifso ifnot
  | Ijumptable arg tbl => Ijumptable (rn arg) tbl
  | Ireturn ret => Ireturn (option_map rn ret)
  end.

Definition subst_capture_code (d s: reg) (cpt:node) (c: code) : code :=
  PTree.map (fun pc instr =>
            if andb (in_set cpt (domtree!!pc)) (negb (Pos.eqb cpt pc))
            then subst_instr d s instr else instr) c.

(* il is list of capture pc *)
Fixpoint propagate_capture_fuel (fuel: nat) (c: code) (il: list node) :=
  match fuel with
  | O => c
  | S fuel' => match il with
              | [] => c
              | hd::tl =>
                  let pc := (find_capture_root hd tl) in (* find most dominate capture *)
                  match (PTree.get pc c) with
                  | None => c
                  | Some i => match (is_capture i) with
                             | None => c (* unreachable *)
                             | Some (d, s) =>
                                 let c' := (subst_capture_code d s pc c) in
                                 propagate_capture_fuel fuel' c' (filter (fun x => negb (Pos.eqb pc x)) il)
                             end
                  end
              end
  end.

Definition propagate_capture (c: code) (il: list node) :=
  propagate_capture_fuel (Datatypes.length il + 1) c il.

End CAPTUREPROP.

Definition transf_function (f: function) : res function :=
  match compute_dom f with
  | Some domtree =>
      let il := find_capture_all f.(fn_code) in
      let code' := propagate_capture domtree f.(fn_code) il in
      OK(mkfunction
         f.(fn_sig)
         f.(fn_params)
         f.(fn_stacksize)
         code'
         f.(fn_phicode)
         f.(fn_entrypoint)
         f.(fn_ext_params)
         f.(fn_dom_test))
  | None => Error (msg "Captureprop failure: domtree gen fail")
  end.

Definition transf_fundef (f: fundef) : res fundef :=
  AST.transf_partial_fundef transf_function f.

Definition transf_program (p: program) : res program :=
  transform_partial_program transf_fundef p.