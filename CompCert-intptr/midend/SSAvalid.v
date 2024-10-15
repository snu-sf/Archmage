(** A posteriori validation of SSA transformation. *)
Require Recdef.
Require Import FSets.
Require Import Coqlib.
Require Import Ordered.
Require Import Errors.
Require Import Maps.
Require Import Lattice.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTLdfs.
Require Import RTLtyping.
Require Import Kildall.
Require Import Machregs.
Require Import Locations.
Require Import Conventions.
Require Import SSA.
Require Import SSAutils.
Require Import Integers.
Require Import Floats.
Require Import Utils.
Require Import NArith.
Require Import LightLive.
Require Import RTLdfsgen.
Require Import Bijection.
Local Open Scope string_scope.

Unset Allow StrictProp.

(** * Type and value definitions *)

Definition index := positive.       
Definition tgamma := node -> Registers.reg -> index. 
Definition ttgamma := PTree.t (PTree.t index).
Definition dft_pos := xH.
  
(** * Auxiliary checkers for some of the structural invariants of code *)

(** Checker for the uniqueness of definitions *)
Definition record_assigned_reg (t: (PTree.t (list positive))) (pc:node) (i: instruction) : (PTree.t (list positive)):=
  match i with 
    | (Iop  _ _ r _ ) 
    | (Iload _ _ _ r _ ) 
    | (Icall _ _ _ r _ ) 
    | (Ibuiltin _ _ (BR r) _ ) => 
      match t ! r with 
        | Some l => (PTree.set r (pc::l) t)
        | None => (PTree.set r (pc::nil) t)
      end
    | _ => t
  end.

Definition add_phi_assigned_reg (pc:node) (t : (PTree.t (list positive))) (phi: phiinstruction) : (PTree.t (list positive)) :=
  match phi with 
    | Iphi args dst => 
      match t ! dst with 
        | Some l => (PTree.set dst (pc::l) t)
        | None => (PTree.set dst (pc::nil) t)
      end
  end.

Definition record_assigned_reg_phi (t: (PTree.t (list positive))) (pc:node) (phib: phiblock) : (PTree.t (list positive)):=
  fold_left (add_phi_assigned_reg pc) phib t.

Definition check_unique_def (tf: SSA.function) : bool :=
  let def_code := PTree.fold record_assigned_reg (fn_code tf) (PTree.empty (list positive))
    in let def_code_phicode := PTree.fold record_assigned_reg_phi (fn_phicode tf) def_code
      in PTree.fold (fun res r _ => res && match def_code_phicode ! r with 
                                        | Some (x::y::m) => false
                                        | _ => true
                                           end) 
        def_code_phicode 
        true.


(** Checker for normalization of code and successor-closed code *)
Definition succ_is_some_instr (code: RTLdfs.code) := 
  (fun res i => res && match code ! i with
                         | Some _ => true
                         | _ => false
                       end).
  
Definition instr_is_nop (code : RTLdfs.code) (pc: node) :=
  (match code ! pc with 
     | Some (RTL.Inop _) => true         
     | _ => false
   end).

Definition check_instr_inv (code: RTLdfs.code) (entry: node) (preds: PTree.t (list positive)) (i:node) : bool := 
  match code ! i with 
    | Some instr => fold_left (succ_is_some_instr code) (RTLdfs.successors_instr instr) true
    | None => false
  end  &&
  if peq entry i then 
    instr_is_nop code i && 
    match preds!i with 
      | None => true
      | Some nil => true
      | Some (x::nil) => true
      | Some (x::y::m) => false
    end
    else 
      match preds!i with
        | None => true
        | Some nil => false
        | Some (x::nil) => true
        | Some (x::y::m) => (fold_left (fun res pc => res && (instr_is_nop code pc)) (x::y::m) true)
      end.

Definition no_pred (preds: PTree.t (list positive)) (i:node) : bool :=
  match preds!!!i with
    | nil => true
    |_ => false
  end.

Definition check_function_inv (f: RTLdfs.function) (preds: PTree.t (list positive)) : bool := 
  match (RTLdfs.fn_code f) ! (RTLdfs.fn_entrypoint f) with 
    | Some (RTL.Inop s) => 
      no_pred preds (RTLdfs.fn_entrypoint f)  &&
        PTree.fold
          (fun (res : bool) (i : node) _ => res && check_instr_inv (RTLdfs.fn_code f) (RTLdfs.fn_entrypoint f) preds i)
          (RTLdfs.fn_code f) true
    | _ => false
end.


(** Checker for the constraint: there is an instruction at every point in the code of [tf] where a phi-block stands *)
Definition check_code_at_phipoints (tf: SSA.function) : bool :=
  forall_ptree (fun pc _ => match (fn_code tf)!pc with None => false | _ => true end)
  (fn_phicode tf).


(** *  More auxiliary definitions *)
Local Open Scope error_monad_scope.

Definition get_option {A: Type} (a: option A) (m: String.string): res A := 
  match a with 
    | None => Error (msg m)
    | Some a => OK a
  end.

Definition map_os (f:positive->reg) (fn:positive + ident) : reg + ident :=
  match fn with
    | inl r => inl _ (f r)
    | inr s => inr _ s
  end.

Definition upd_list {A:Type} (l:list positive) (g:A) (m: PTree.t A) : PTree.t A :=
  fold_left (fun m p => PTree.set p g m) l m.

Definition read_gamma (g:PTree.t index) (x:Registers.reg) : index :=
  match g! x with
    | None => dft_pos
    | Some i => i
  end.

Definition is_joinpoint (preds: PTree.t (list positive)) (pc:node) : bool :=
  match preds ! pc with 
    | Some (x::y::m) => true
    | _ => false
  end.

(** * SSA Validator *)
(** The validator performs the generation of a SSA function, provided
an external, untrusted SSA generator, namely [extern_gen_ssa], that
computes all the required informations.  [extern_gen_ssa f live]
computes (i) the maximal positive index that is required to index
registers of the function RTLt code, (ii) a map that gives, for every
program point, the index that should be used to index the register
defined at that point (if any) and (iii) a similar map for phi-blocks.
This certificate will be then transmitted to the generating
validator. *)

Parameter extern_gen_ssa : RTLdfs.function -> (node -> Regset.t) -> (nat * (PTree.t index) * (PTree.t (PTree.t index))).

(** Checker for validity of computed indexes *)
Definition check_valid_index (size: nat) (defs: PTree.t index) : bool :=
  forall_ptree (fun pc i => Bij.valid_index size i) defs.

Definition check_valid_index_phis (size: nat) (phidefs: PTree.t (PTree.t index)): bool :=
  forall_ptree (fun pc phis =>
                  forall_ptree (fun r i => Bij.valid_index size i) phis)
               phidefs.

(** The validator is then run on the RTLt function, and uses the
    result of [extern_gen_ssa] to build on the fly the SSA form of the
    function.  To do so, it will rely on a global typing information
    of type [ttgamma], that it will update along the traversal of the
    RTLt code.  *)

(** Definition for the initial global typing context *) 
Definition entry_Gamma (tf : RTLdfs.function) : ttgamma :=
  PTree.set (RTLdfs.fn_entrypoint tf) (PTree.empty _) (PTree.empty (PTree.t index)).

(** [update_ctx] updates the global typing information according to
   encountered definitions. It also update the registers used in the
   code. Finally, it keeps up-to-date the list of the junctions points
   that have been visited so far. *)

Definition update_ctx (size: nat) (preds: PTree.t (list positive)) 
  (def:PTree.t index) 
  (def_phi:PTree.t (PTree.t index)) 
  (code: PTree.t RTL.instruction)
  (live: node -> Regset.t) 
  (acc: res (ttgamma * (PTree.t instruction) * list node)) (pc: node) :
  res (ttgamma * (PTree.t instruction) * list node) :=
  match acc with
    | Error msg => Error msg
    | OK (G, new_code, juncpoints) =>
      do instr <- get_option (code ! pc) "" ;     
      do g <- get_option (G ! pc) "" ; 
      let use := fun (x:reg) => Bij.pamr size (x,read_gamma g  x) in
        match instr with
          | RTL.Inop l => 
            if is_joinpoint preds l then
              do def_phi <- get_option (def_phi ! l) ""; 
              let live := live l in 
              match G ! l with
                | None => (* The junction point [l] has not been touched before *)
                  let g' := PTree.fold 
                    (fun G x i => if Regset.mem x live then PTree.set x i G else G)
                    def_phi g in
                    OK (PTree.set l g' G, 
                        PTree.set pc (Inop l) new_code,
                        l::juncpoints)
                | Some g_jun => (* The junction point [l] has already been visited before *)
                  if forall3_ptree
                    (fun x i i' o => 
                      let i := match i with None => dft_pos | Some i => i end in
                      let i' := match i' with None => dft_pos | Some i => i end in
                        match o with
                          | None => peq i i' || negb (Regset.mem x live)
                          | Some _ => true
                        end) g g_jun def_phi then
                    OK (G,
                        PTree.set pc (Inop l) new_code,
                        juncpoints)
                  else Error (msg "SSAvalid - 1") 
              end
            else
              OK (PTree.set l g G, 
                  PTree.set pc (Inop l) new_code,
                  juncpoints)
          | RTL.Ireturn None => 
            OK (G, PTree.set pc (Ireturn None) new_code, juncpoints)
          | RTL.Ijumptable arg tbl => 
              OK (upd_list tbl g G, 
                  PTree.set pc (Ijumptable (use arg) tbl) new_code,
                  juncpoints)
          | RTL.Ireturn (Some arg)  => 
              OK (G, PTree.set pc (Ireturn (Some (use arg))) new_code, juncpoints)
          | RTL.Icond cond args ifso ifno => 
              OK (upd_list (ifso::ifno::nil) g G, 
                  PTree.set pc (Icond cond (map use args) ifso ifno) new_code,
                  juncpoints)
          | RTL.Iop op args dest succ => 
            do i <- get_option (def ! pc) "" ; 
            let dest' := Bij.pamr size (dest,i) in
            if negb (Pos.eqb xH i) then
              OK (PTree.set succ (PTree.set dest i g) G,
                  PTree.set pc (Iop op (map use args) dest' succ) new_code,
                  juncpoints)
            else Error (msg "SSAvalid - 2")
          | RTL.Iload chunk addr args dest succ => 
            do i <- get_option (def ! pc) "" ; 
            let dest' := Bij.pamr size (dest,i) in
            if negb (Pos.eqb xH i) then
              OK (PTree.set succ (PTree.set dest i g) G,
                  PTree.set pc (Iload chunk addr (map use args) dest' succ) new_code,
                  juncpoints)
            else Error (msg "SSAvalid - 3")
          | RTL.Icall sig fn args dest succ => 
            do i <- get_option (def ! pc) "" ;
            let dest' := Bij.pamr size (dest,i) in
            if negb (Pos.eqb xH i) then
              OK (PTree.set succ (PTree.set dest i g) G,
                  PTree.set pc (Icall sig (map_os use fn) (map use args) dest' succ) new_code,
                  juncpoints)
            else Error (msg "SSAvalid - 4")
          | RTL.Itailcall sig fn args => 
            OK (G,
                PTree.set pc (Itailcall sig (map_os use fn) (map use args)) new_code,
                juncpoints)
          | RTL.Ibuiltin ef args (BR dest) succ => 
            do i <- get_option (def ! pc) "" ; 
              let dest' := Bij.pamr size (dest,i) in                              
              if negb (Pos.eqb xH i) then
                OK (PTree.set succ (PTree.set dest i g) G,
                    PTree.set pc (Ibuiltin ef
                                           (map (map_builtin_arg use) args)
                                           (BR dest') succ) new_code,
                    juncpoints)
              else Error (msg "SSAvalid 5")

          | RTL.Ibuiltin ef args dest succ => 
                OK (PTree.set succ g G,
                    PTree.set pc (Ibuiltin ef
                                           (map (map_builtin_arg use) args)
                                           (map_builtin_res (fun r => Bij.pamr size (r,xH)) dest) succ) new_code,
                    juncpoints)

          | RTL.Istore chunk addr args src succ => 
            OK (PTree.set succ g G,
                PTree.set pc (Istore chunk addr (map use args) (use src) succ) new_code,
                juncpoints)
        end
  end.

(** [builds_phi_block] builds phi-blocks according to def_phi,
   assuming that all predecessors of [pc] have been visited.  It will
   get the gammas, and build from them the arguments of phi-functions.
   At this stage, we know that if a variable is not assigned in
   phi-block, then all preceeding gammas agree on the index.  *)

Definition xbuild_phi_block (size: nat) (preds: list positive)
           (livepc: Regset.t) 
           (def_phi: (PTree.t index)) predspc := 
  PTree.fold
    (fun phis x xdef =>
       if Regset.mem x livepc then
         let phi_args := map (fun pc => Bij.pamr size (x,read_gamma (predspc pc) x)) preds in
         let phi_def := Bij.pamr size (x,xdef) in
         (Iphi phi_args phi_def)::phis
       else phis
    ) def_phi nil.
        
Definition build_phi_block (size:nat) (preds: PTree.t (list positive)) 
  (live: node -> Regset.t) 
  (def_phi:PTree.t (PTree.t index))
  (G:ttgamma)
  (acc: res (PTree.t phiblock)) (pc: node) : res (PTree.t phiblock) :=
  do preds <- get_option (preds ! pc) "" ; 
  do def_phi <- get_option (def_phi ! pc) "" ;
  let live := live pc in 
  let get_Gpreds : index -> (PTree.t index) := 
         (fun pc_pred => 
          match G ! pc_pred with
            | None => (* should not happen *) PTree.empty _ 
            | Some m => m
          end) in
  let new_phi_block := xbuild_phi_block size preds live def_phi get_Gpreds in
      if forall_ptree (fun x xdef => negb (Pos.eqb xH xdef)) def_phi then
        match acc with
          | Error msg => Error msg
          | OK acc => OK (PTree.set pc new_phi_block acc)
        end
        else Error (msg "SSAvalid - 7").


(** Computing dominator-test and so-called external parameters of an SSA function. *)

Require Import DomTest.
Module SSADomTest := Make PositiveNodeTree Z.
Import SSADomTest.

(* External computation of a dominance relation test for a function
   code, and an entry node in the cfg.  The relation is encoded as an
   association list (child,father).  [extern_d] needs to ensure that
   its result list is topo-sorted wrt the CFG of the code, in order
   for the checker to accept it.  *)
Axiom extern_d : node -> code -> list (node * node).

(* Validator of the dataflow constraints *)
Definition check_D_eq (entry: node) (code: code)
           (D: node -> node) (test_dom: node -> node -> bool) : bool :=
  (peq (D entry) entry) 
  && forall_ptree (fun pc spc => forallb (test_dom pc) spc) (PTree.map1 successors_instr code).
  
(* Computation of the dominance test *)
Definition compute_test_dom (entry: node) (code: code): option (node -> node -> bool) :=
  let l := extern_d entry code in 
  let D := make_D_fun l in 
  match build_succs entry l with  
      | Some sn => (* sn : D renversé sous forme de map *)
        match build_itv_map entry sn with 
            | Some itvm => (* itvm : pour chaque noeud, son intervalle *)
              let td := (fun i j => is_ancestor itvm (D j) i) in 
              if (check_D_eq entry code D td) then Some (is_ancestor itvm)
              else None
            | None => None
        end
      | None => None
  end.

(** Typechecking algorithm, that uses the information given by
   [extern_gen_ssa].  The first phase updates the global typing
   information and rename definitions and uses, using [update_ctx].
   The second phase handle phi-blocks, by synthesising them using the
   global typing information computed at the last stage.  Finally, it
   indices the function parameters.  [check_function_inv],
   [check_unique_def] and [check_code_at_phipoints] are used to check
   additional structural constraints on the code of either [f] or the
   resulting SSA function.
   
   Once the function code is type-checked, a dominator-test and
   external parameters for the function  
 *)

Definition typecheck_function (f: RTLdfs.function) (max_index:nat) 
           (def:PTree.t index) (def_phi:PTree.t (PTree.t index))
           (live:node -> Regset.t) : res SSA.function :=
  let G := entry_Gamma f in     
  let preds := (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) in
  if Bij.valid_index max_index dft_pos then
    if check_valid_index max_index def && check_valid_index_phis max_index def_phi then 
      if check_function_inv f preds then
        (match fold_left (update_ctx max_index preds def def_phi (RTLdfs.fn_code f) live) 
                         (fn_dfs f) (OK (G,PTree.empty _,nil)) with
         | Error msg => Error msg
         | OK (G,new_code,juncpoints) =>
           do phi_code <- fold_left (build_phi_block max_index preds live def_phi G) juncpoints (OK (PTree.empty _));
           match compute_test_dom (RTLdfs.fn_entrypoint f) new_code with
           | Some domtest => 
             let params:= (map (fun r => Bij.pamr max_index (r,dft_pos)) (RTLdfs.fn_params f)) in 
             let fwo := (mkfunction
                           (RTLdfs.fn_sig f)
                           params
                           (RTLdfs.fn_stacksize f)
                           new_code
                           phi_code
                           (RTLdfs.fn_entrypoint f)
                           (ext_params_list new_code phi_code params)
                           domtest
                        ) in
             if check_unique_def fwo && check_code_at_phipoints fwo
             then OK fwo
             else Errors.Error (msg "Code not in SSA") (* Function is not in SSA *)
           | None => Error (msg "Could not compute dominators")
           end
         end)
      else Error (msg "Code should be normalized")
    else Error (msg "Wrong index for definition")
  else Error (msg "Wrong maximum index")
. 

(** * Actual code of the generating validator. *)
(** The transformation uses a liveness analysis over the RTL code (see separate file). *)
Definition transf_function (f: RTLdfs.function) : res SSA.function := 
  do live <- get_option (analyze f) "Bad live analysis" ;
  let '(size, def, def_phi) := extern_gen_ssa f (fun pc => (Lin f pc (Lout live))) in 
  typecheck_function f size def def_phi (fun pc => (Lin f pc (Lout live))).

Definition transf_fundef (fd: RTLdfs.fundef) : res fundef :=
  AST.transf_partial_fundef transf_function fd.

Definition transf_program (p: RTLdfs.program) : res program :=
  transform_partial_program transf_fundef p.

