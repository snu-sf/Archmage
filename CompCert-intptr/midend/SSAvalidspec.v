(** Specification of the SSA validator, in terms of a type
    system. *)

Require Import Coq.Unicode.Utf8.
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
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import RTLdfs.
Require Import Kildall.
Require Import KildallComp.
Require Import Conventions.
Require Import SSA.
Require Import SSAutils.
Require Import SSAvalid.  
Require Import Utilsvalidproof.
Require Import LightLive.
Require Import Utils.
Require Import Classical.
Require Import Bijection.

Unset Allow StrictProp.

(** ** Well-typed instructions *)

Variant wt_eidx (size: nat) (g : reg -> index) : instruction -> Prop :=
| wt_eidx_nop: forall s,
    wt_eidx size g (Inop s)
| wt_eidx_istore: forall chk adr args src succ,
    wt_eidx size g (Istore chk adr args src succ)
| wt_eidx_itailcall: forall sig fn args,
    wt_eidx size g (Itailcall sig fn args)
| wt_eidx_icond: forall cond args ifso ifnot,
    wt_eidx size g (Icond cond args ifso ifnot)
| wt_eidx_ijumptable : forall arg tbl,
    wt_eidx size g (Ijumptable arg tbl)
| wt_eidx_ireturn: forall optr,
    wt_eidx size g (Ireturn optr)
| wt_eidx_iop : forall op args dst succ r i, 
    Bij.rmap size dst = (r,i) ->
    g r <> i ->  wt_eidx size g (Iop op args dst succ)    
| wt_eidx_iload : forall chk adr args dst succ r i, 
    Bij.rmap size dst = (r,i) ->  g r <> i ->
    wt_eidx size g (Iload chk adr args dst succ)    
| wt_eidx_icall : forall sig ros args dst succ r i, 
    Bij.rmap size dst = (r,i) ->  g r <> i ->
    wt_eidx size g (Icall sig ros args dst succ)    
| wt_eidx_ibuiltin_res: forall ef args dst succ r i, 
    Bij.rmap size dst = (r,i) ->  g r <> i ->
    wt_eidx size g (Ibuiltin ef args (BR dst) succ)
| wt_eidx_ibuiltin: forall ef args dst succ,
    (forall x, dst <> BR x) ->
    wt_eidx size g (Ibuiltin ef args dst succ)
.

Variant wt_ephi (size: nat) (g: reg -> index) : phiblock -> Prop := 
| wt_ephi_intro : forall block, 
    (forall ri r i, assigned ri block -> Bij.rmap size ri = (r,i) ->  g r <> i) ->
    wt_ephi size g block.

Definition update (rindex: reg -> index) (r:reg) (i:index) : reg -> index :=
  fun reg: reg => if (peq reg r) then i else rindex reg. 
Notation "a [ x ← v ]" := (update a x v) (at level 1, v at next level).

Notation use_ok :=
  (fun (size: nat) (args: list reg) (γ: Registers.reg -> index) =>
     (forall x, In x args -> forall r i, Bij.rmap size x = (r,i) -> γ r = i) : Prop).

Notation valid_index_ok :=
  (fun (size: nat) (args: list reg) =>
     (forall x, In x args -> forall r i, Bij.rmap size x = (r,i) -> Bij.valid_index size i = true) : Prop).

Notation valid_reg_ok :=
  (fun (size: nat) (args: list reg) =>
     (forall x, In x args -> Bij.valid_reg_ssa size x = true) : Prop).

Variant wt_instr (size: nat): (reg -> index) -> instruction -> (reg -> index) -> Prop :=
| wt_Inop: forall γ s,
    wt_instr size γ (Inop s) γ
             
| wt_Icond: forall γ cond args s1 s2,
    use_ok size args γ ->
    valid_index_ok size args ->
    valid_reg_ok size args ->
    wt_instr size γ (Icond cond args s1 s2) γ
             
| wt_Ijumptable: forall γ arg tbl,
    use_ok size (arg::nil) γ ->
    valid_index_ok size (arg::nil) ->
    valid_reg_ok size (arg::nil) ->
    wt_instr size γ (Ijumptable arg tbl) γ
             
| wt_Ireturn_some: forall γ r,
    use_ok size (r::nil) γ ->
    valid_index_ok size (r::nil) ->
    valid_reg_ok size (r::nil) ->
    wt_instr size γ (Ireturn (Some r)) γ

| wt_Ireturn_none: forall γ,
    wt_instr size γ (Ireturn None) γ
             
| wt_Iop: forall γ op args s x r i,
    use_ok size args γ  ->
    Bij.rmap size x = (r,i) ->
    valid_index_ok size (x::args) ->
    valid_reg_ok size (x::args) ->    
    wt_instr size γ (Iop op args x s) γ[r← i]
                                 
| wt_Iload: forall γ chunk addr args s x r i,
    use_ok size args γ ->
    Bij.rmap size x = (r,i) ->
    valid_index_ok size (x::args) ->
    valid_reg_ok size (x::args) ->
    wt_instr size γ (Iload chunk addr args x s) γ[r←i]
                                               
| wt_Istore: forall γ chunk addr args s src,
    use_ok size (src::args) γ ->
    valid_index_ok size (src::args) ->
    valid_reg_ok size (src::args) ->
    wt_instr size γ (Istore chunk addr args src s) γ
      
| wt_Icall_id: forall γ sig args s id x r i,
    use_ok size args γ ->
    Bij.rmap size x = (r,i) ->
    valid_index_ok size (x::args) ->
    valid_reg_ok size (x::args) ->
    wt_instr size γ (Icall sig (inr reg id) args x s) γ[r←i]
      
| wt_Icall_reg : forall γ sig args s x r i rfun,
    use_ok size (rfun::args) γ ->
    Bij.rmap size x = (r,i) ->
    valid_index_ok size (x::rfun::args) ->
    valid_reg_ok size (x::rfun::args) ->
    wt_instr size γ (Icall sig (inl ident rfun) args x s) γ[r←i]
      
| wt_Itailcall_id: forall γ sig args id,
    use_ok size args γ ->
    valid_index_ok size args ->
    valid_reg_ok size args ->
    wt_instr size γ (Itailcall sig (inr reg id) args) γ
      
| wt_Itailcall_reg: forall γ sig  args rfun,
    use_ok size (rfun::args) γ ->
    valid_index_ok size (rfun::args) ->
    valid_reg_ok size (rfun::args) ->
    wt_instr size γ (Itailcall sig (inl ident rfun) args) γ
      
| wt_Ibuiltin_res: forall γ ef args s x r i,
    use_ok size (params_of_builtin_args args) γ ->
    Bij.rmap size x = (r, i) ->
    valid_index_ok size (x::(params_of_builtin_args args)) ->
    valid_reg_ok size (x::(params_of_builtin_args args)) ->
    wt_instr size γ (Ibuiltin ef args (BR x) s) γ[r←i]

| wt_Ibuiltin: forall γ ef args s dst,
    (forall r, dst <> BR r) ->
    use_ok size (params_of_builtin_args args) γ ->
    valid_index_ok size (params_of_builtin_args args) ->
    valid_reg_ok size (params_of_builtin_args args) ->
    wt_instr size γ (Ibuiltin ef args dst s) γ
.
     
Variant is_out_node (f: function) : node -> Prop:=
| Out_tailcall: forall i sig fn args, 
    (fn_code f)!i = Some (Itailcall sig fn args) ->
    is_out_node f i
| Out_return : forall i or,
    (fn_code f)!i = Some (Ireturn or) ->
    is_out_node f i
| Out_jtable : forall i arg,
    (fn_code f)!i = Some (Ijumptable arg nil) ->
    is_out_node f i.

Variant wt_out (size: nat) (f: function) : tgamma  -> node -> Prop :=
| wt_out_node: forall (Γ:tgamma) (i :node) instr, 
    (fn_code f)!i = Some instr ->
    (wt_instr size (Γ i) instr (Γ i)) ->
    (wt_out size f Γ i).

Variant wf_init (size: nat) (f: function) (Γ:tgamma): Prop :=
| wf_init_gamma:  
    (forall p, In p (fn_params f) ->
               Bij.valid_reg_ssa size p = true
               /\ exists r, Bij.rmap size p = (r,(Γ (fn_entrypoint f)) r)) ->
    wf_init size f Γ.

(** * Typing phi-blocks *)
Section WT_PHI.
  Variable funct: SSA.function.
  Variable size: nat.

  Variant wt_phid (block:phiblock) (γ1 γ2: reg -> index) (live:Regset.t) : Prop :=
  | wt_phid_intro : forall
      (ASSIG: forall ri r i, assigned ri block -> Bij.rmap size ri = (r,i) ->  γ2 r = i)
      (VALIDI: forall ri r i, assigned ri block -> Bij.rmap size ri = (r,i) ->  Bij.valid_index size i = true)
      (VALIDR: forall ri, assigned ri block -> Bij.valid_reg_ssa size ri = true)
      (LIVE: forall ri r i, assigned ri block -> Bij.rmap size ri = (r,i) -> Regset.In r live )
      (NASSIG:forall r, 
          (forall ri i, Bij.rmap size ri = (r,i) -> not (assigned ri block)) -> 
          (γ2 r = γ1 r) \/ ~ (Regset.In r live)), 
      wt_phid block γ1 γ2 live.

  Inductive phiu (r: reg) : list reg -> (list (reg -> index)) -> Prop :=
  | phiu_nil : phiu r nil nil
  | phiu_cons: forall arg g args gl i
                      (PHIU: phiu r args gl)  
                      (RMAP: Bij.rmap size arg = (r,i))
                      (VALIDI: Bij.valid_index size i = true)
                      (VALIDR: Bij.valid_reg_ssa size arg = true)
                      (GARG: g r = i), 
      phiu r (arg::args) (g::gl).  

  Lemma phiu_nth : forall r k args gammas ri g,
      phiu r args gammas -> 
      nth_error args k = Some ri ->
      nth_error gammas k = Some g ->
      Bij.valid_reg_ssa size ri = true
      /\ exists i, Bij.rmap size ri = (r,i)
                   /\ g r = i
                   /\ Bij.valid_index size i = true.
  Proof.
    induction k; intros.
    inv H; simpl in *; inv H0. inv H1 ; eauto.
    destruct args ; simpl in * ; inv H0.
    destruct gammas ; simpl in * ; inv H1.
    inv H ; eauto.
  Qed.

  Variant wt_phiu (preds: list node) (block:phiblock) (Γ: tgamma) :=
  | wt_phiu_intro: forall
      (USES: (forall args dst r i, In (Iphi args dst) block ->
                                   Bij.rmap size dst = (r,i) -> phiu r args (map Γ preds))), 
      wt_phiu preds block Γ.

End WT_PHI.  

(** * Typing edges *)
Section WT_EDGE.
  Variable funct: SSA.function.
  Variable size: nat.

  Variant wt_edge (live: Regset.t) : tgamma -> node -> node -> Prop :=
  | wt_edge_not_jp:  forall (Γ:tgamma) (i j :node) (ins: instruction),
      forall (EDGE: is_edge funct i j)
             (INS: (fn_code funct)!i = Some ins)
             (NOPHI: (fn_phicode funct)!j = None)
             (EIDX: wt_eidx size (Γ (fn_entrypoint funct)) ins)
             (WTI: wt_instr size (Γ i) ins (Γ j)), 
        (wt_edge live Γ i j)
  | wt_edge_jp: forall (Γ:tgamma) (i j:node) (predsj: list node) (ins: instruction) (block: phiblock) (dft: positive),
      forall (EDGE: is_edge funct i j)
             (INS:  (fn_code funct)!i = Some ins)
             (PHI:  (fn_phicode funct)!j = Some block)
             (PREDS: predsj = (make_predecessors (fn_code funct) successors_instr)!!!j)
             (EIDX: wt_eidx size (Γ (fn_entrypoint funct)) ins)
             (PEIDX: wt_ephi size (Γ (fn_entrypoint funct)) block)
             (WTPHID: wt_phid size block (Γ i) (Γ j) live)
             (WTPHID: wt_phiu size predsj block Γ),
        (wt_edge live Γ i j).
  
End WT_EDGE.

(** * Well-typed functions *)
Variant wt_function (size: nat) (f: RTLdfs.function) (tf: function) (live: PMap.t Regset.t) (Γ:tgamma): Prop :=
| wt_fun_intro : forall
    (WTE: forall i j, is_edge tf i j -> wt_edge tf size (Lin f j (Lout live)) Γ i j)
    (WTO: forall i, is_out_node tf i -> wt_out size tf Γ i), 
    wt_function size f tf live Γ.

(** * Overall specification of a validated function *)
Definition normalised_function (f : RTLdfs.function) : Prop :=
  check_function_inv f (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) = true.

Definition check_function_spec (size: nat) (f: RTLdfs.function) (live: PMap.t Regset.t) (tf: SSA.function) Γ :=
  (structural_checks_spec size f tf)
  /\ (wf_init size tf Γ)
  /\ (wt_function size f tf live Γ)
  /\ (wf_live f (Lout live)).
