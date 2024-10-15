(** RTLdfs.v defines the code transformation over RTL that (i) removes
unreachable code and (ii) set the [fn_dfs] field of the function to
the list of reachable nodes in a Depth First Seach traversal order of
the CFG of the function. *)

Require Recdef.
Require Import FSets.
Require Import Coqlib.
Require Import Ordered.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Registers.
Require Import RTLdfs.
Require Import RTL.
Require Import RTLutils.
Require Import Kildall.
Require Import Utils.
Require Import Relation_Operators.

Local Open Scope error_monad_scope.

Unset Allow StrictProp.

(** * Utility functions *)
Definition not_seen_sons (code:code) (pc : node) (seen: PTree.t unit) : (list positive) * PTree.t unit := 
  match code ! pc with 
    | None => (nil, seen)
    | Some i => 
      List.fold_left (fun (ns:(list node) * PTree.t unit) j =>
        let (new,seen) := ns in
          match PTree.get j seen with
            | None => (j::new, PTree.set j tt seen)
            | Some _ => ns
          end) 
        (successors_instr i)
        (nil, seen)
  end.

Definition remove_dead (i:option instruction) (b:option unit) : option instruction :=
  match b with
    | Some _ => i
    | None => None
  end.

Fixpoint acc_succ (code:code) (workl: list node)
         (acc: res (PTree.t unit * (list positive) * (list positive)))
  : res ((list positive) * RTL.code) := 
  do acc <- acc;
    let '(seen_set,seen_list,stack) := acc in 
      match stack with 
        | nil => OK (seen_list, combine remove_dead code seen_set)
        | x::q => 
          match workl with
            | nil => Error (msg "workl too small")
            | pc::m => 
              let seen_set' := PTree.set x tt seen_set in
                let (new,seen_set) := not_seen_sons code x seen_set' in
                  acc_succ code m (OK (seen_set,x::seen_list,new++q))
          end
      end.

Definition dfs (tf: RTL.function) : res (list node * RTLdfs.code) := 
  do (res, code') <-
    (acc_succ 
      (RTL.fn_code tf)
      (map (@fst node instruction) (PTree.elements (RTL.fn_code tf))) 
      (OK (PTree.empty _,nil,(RTL.fn_entrypoint tf)::nil))) ;
    OK (rev_append res nil, code').

(** * Actual code of the transformations *)
Definition transf_function (f: RTL.function) : res RTLdfs.function :=
  do (seen,code) <- dfs f ;
    OK (RTLdfs.mkfunction
      (RTL.fn_sig f)
      (RTL.fn_params f)
      (RTL.fn_stacksize f)
      code
      (RTL.fn_entrypoint f)
      seen).

Definition transf_fundef (fd: RTL.fundef) : res RTLdfs.fundef :=
  AST.transf_partial_fundef transf_function fd.

Definition transf_program (p: RTL.program) : res RTLdfs.program :=
  transform_partial_program transf_fundef p.

(** * Well-formed dfs functions and programs *)

(** The record [wf_dfs_function] gathered all the properties ensured
by the transformation that will be used later on *)

Record wf_dfs_function (f: RTLdfs.function) : Prop := {
  fn_dfs_comp : forall j ins, (RTLdfs.fn_code f) ! j = Some ins -> In j (fn_dfs f);
  fn_dfs_reached: forall j, In j (fn_dfs f) -> (cfg (RTLdfs.fn_code f))** (RTLdfs.fn_entrypoint f) j;
  fn_dfs_norep : list_norepet (fn_dfs f)
}.

Variant wf_dfs_fundef: RTLdfs.fundef -> Prop :=
| wf_dfs_fundef_external: forall ef,
    wf_dfs_fundef (External ef)
| wf_dfs_function_internal: forall f,
    wf_dfs_function f ->
    wf_dfs_fundef (Internal f).

Definition wf_dfs_program (p: RTLdfs.program) : Prop := 
  forall f id, In (id,Gfun f) (prog_defs p) -> wf_dfs_fundef f.
