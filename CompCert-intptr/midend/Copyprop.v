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

Require Import sflib.


(** * CSE optimisation based on GVN *)

(* Definition get_repr (f:function) (c:certif):= *)
(*   match check_GVN f c with *)
(*     | Some repr => repr *)
(*     | None => (fun x => (x,xH)) *)
(*   end. *)

(* Definition get_extern_gvn (f:function): (reg -> (reg* node)) := *)
(*   get_repr f (extern_gvn f). *)

(* Definition analysis (f: function) := ((get_extern_gvn f, f),P2Map.init true). *)

(* Definition res := ((reg -> reg*node)  (* repr(x) = (r, r_def) *) *)
(*                     * function        (* function *)                            *)
(*                    )%type. *)

(* Definition check_def (code:code) (pc:node) (x:reg) : bool := *)
(*   match code!pc with *)
(*     | Some (Iop op args dst succ) => if peq x dst then true else false *)
(*     | Some (Iload chunk addr args dst succ) => if peq x dst then true else false *)
(*     | Some (Icall sig fn args dst succ) => if peq x dst then true else false *)
(*     | Some (Ibuiltin fn args (BR dst) succ) => if peq x dst then true else false *)
(*     | _ => false *)
(*   end. *)


Definition find_mv_instr (result: option (reg*reg)) (pc: node) ins : option (reg * reg) :=
  match result with
  | None => match ins with
            | Iop Omove (src :: nil) dst _ => Some (dst,src)
            | _ => result
            end
  | _ => result
  end.

Definition find_mv_code (c: code) : option (reg * reg) :=
  PTree.fold find_mv_instr c None.

Definition remove_mv_instr (d: reg) (instr: instruction) :=
  match instr with
  | Iop Omove _ dst pc' =>
      if Pos.eqb dst d then Inop pc' else instr
  | _ => instr
  end.

Definition rename_reg (d s: reg) (r: reg) : reg :=
  if (Pos.eqb r d) then s else r.

Definition rename_fn (d s: reg) (fn: reg + ident) : reg + ident :=
  match fn with inl r => inl (rename_reg d s r) | _ => fn end.

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
  let rnf := rename_fn d s in
  let rnba := rename_barg d s in
  let rnbr := rename_bres d s in
  match instr with
  | Inop pc' => Inop pc'
  | Iop op args dst pc' => Iop op (map rn args) dst pc'
  | Iload chunk addr args dst pc' => Iload chunk addr (map rn args) dst pc'
  | Istore chunk addr args src pc' => Istore chunk addr (map rn args) (rn src) pc'
  | Icall sig fn args dst pc' => Icall sig (rnf fn) (map rn args) dst pc'
  | Itailcall sig fn args => Itailcall sig (rnf fn) (map rn args)
  | Ibuiltin ef args dst pc' => Ibuiltin ef (map rnba args) dst pc'
  | Icond cond args ifso ifnot => Icond cond (map rn args) ifso ifnot
  | Ijumptable arg tbl => Ijumptable (rn arg) tbl
  | Ireturn ret => Ireturn (option_map rn ret)
  end.

Definition elim_mv_code (d s: reg) (c: code) : code :=
  PTree.map (fun pc instr => subst_instr d s (remove_mv_instr d instr)) c.

Fixpoint find_mv_phiblock (blk: phiblock) : option (reg * reg) :=
  match blk with
  | nil => None
  | (Iphi (src::args) dst) :: blk' =>
      if forallb (Pos.eqb src) args
      then Some (dst,src)
      else find_mv_phiblock blk'
  | _ :: blk' => find_mv_phiblock blk'
  end.

Definition _find_mv_phiblock result (pc: node) blk : option (reg * reg) :=
  match result with
  | None => find_mv_phiblock blk
  | _ => result
  end.

Definition find_mv_phicode (p: phicode) : option (reg * reg) :=
  PTree.fold _find_mv_phiblock p None.

Fixpoint remove_mv_phiblock (d: reg) (blk: phiblock) :=
  match blk with
  | nil => nil  
  | (Iphi args dst) :: blk' =>
      if Pos.eqb dst d
      then remove_mv_phiblock d blk'
      else (Iphi args dst) :: remove_mv_phiblock d blk'
  end.

Definition subst_phi (d s: reg) (pins: phiinstruction) :=
  match pins with
  | Iphi args dst => Iphi (map (rename_reg d s) args) dst
  end.

Definition elim_mv_phicode (d s: reg) (p: phicode) : phicode :=
  PTree.map (fun pc blk => map (subst_phi d s) (remove_mv_phiblock d blk)) p.

Fixpoint simplify_mv (fuel: nat) (c: code) (p: phicode) : code * phicode :=
  match fuel with
  | 0 => (c, p)
  | S fuel' =>
      match find_mv_code c with
      | Some (d, s) =>
          simplify_mv fuel' (elim_mv_code d s c) (elim_mv_phicode d s p)
      | None => match find_mv_phicode p with
                | Some (d, s) =>
                    simplify_mv fuel' (elim_mv_code d s c) (elim_mv_phicode d s p)
                | None => (c,p)
                end
      end
  end.

Definition transf_function_fuel (fuel: nat) (f: function) : function :=
  let '(code', phicode') := simplify_mv fuel f.(fn_code) f.(fn_phicode) in
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    code'
    phicode'
    f.(fn_entrypoint)
    f.(fn_ext_params)
    f.(fn_dom_test).

Definition code_size (f: function) : nat :=
  PTree.fold (fun m _ blk => length blk + m) f.(fn_phicode)
  (PTree.fold (fun m _ _ => 1+m) f.(fn_code) 1%nat).

Definition transf_function (f: function) : function :=
  transf_function_fuel (code_size f) f.

Definition transf_fundef (f: fundef) : fundef :=
  AST.transf_fundef transf_function f.

Definition transf_program (p: program) : program :=
  AST.transform_program transf_fundef p.

Definition transf_function_step (f: function) : function :=
  transf_function_fuel 1 f.

Definition transf_fundef_step (f: fundef) : fundef :=
  AST.transf_fundef transf_function_step f.

Definition transf_program_step (p: program) : program :=
  AST.transform_program transf_fundef_step p.
