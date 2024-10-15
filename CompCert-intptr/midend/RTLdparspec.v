(** Specification of the RTLdpar transformation *)
Require Import Coqlib.
Require Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Switch.
Require Import Op.
Require Import Registers.
Require Import RTLpar.
Require Import RTL.
Require Import SSA CSSA SSAutils.
Require Import RTLdpar.
Require Import Kildall.
Require Import Utils.
Require Import DLib.
Unset Allow StrictProp.

(** * Specification of RTLdpar *)
Variant is_jp (jp: node) (code: code) : Prop :=
 | ijp_intro: forall l, 
                (make_predecessors code successors_instr) ! jp = Some l -> 
                length l > 1 ->
                is_jp jp code.

Inductive reach_moves (code : RTL.code) :
                      node -> node -> list (reg * reg) -> list node -> Prop := 
| reach_moves_nil : forall from to, 
                      code ! from = Some (RTL.Inop to) ->
                      reach_moves code from to nil (from::nil)
| reach_moves_cons : forall from succ to src dst mvs l,
  code ! from = Some (RTL.Iop Omove (src::nil) dst succ) ->
  reach_moves code succ to mvs l ->
  reach_moves code from to ((src,dst)::mvs) (from::l).

Lemma reach_moves_last_inop : forall code l from to mvs,
  reach_moves code from to mvs l ->
  exists last l', (rev l) = last::l' /\ code ! last = Some (RTL.Inop to).
Proof.
  induction l ; intros; invh reach_moves ; go.
  exploit IHl; eauto; intros; try invh and.
  repeat (repeat invh ex ; repeat invh and); subst.
  simpl. rewrite H0. go.
Qed.

Variant rtldpar_spec (tmp: reg) (code1: code) (pcode1: parcopycode) 
          (code2: RTL.code) (R: node -> node) (pc: node): Prop :=
| dspec_noblock : forall succ,
  code1 ! pc = Some (Inop succ) ->
  (pcode1 ! pc = None) ->
  ~ is_jp succ code1 ->
  code2 ! pc = Some (RTL.Inop succ) ->
  R pc = pc ->

  rtldpar_spec tmp code1 pcode1 code2 R pc

| dspec_block_pre : forall fresh succ parcb lnew mvs,
  code1 ! pc = Some (Inop succ) ->
  ~ is_jp pc code1 ->
  pcode1 ! pc = Some parcb ->

  code2 ! pc = Some (RTL.Inop fresh) ->
  mvs = (seq_parmoves tmp (parcb_to_moves parcb)) ->

  reach_moves code2 fresh succ mvs lnew ->

  R pc = pc ->

  rtldpar_spec tmp code1 pcode1 code2 R pc

| dspec_block_jp : forall fresh succ parcb lnew mvs rpc,
  code1 ! pc = Some (Inop succ) ->
  is_jp pc code1 ->
  pcode1 ! pc = Some parcb ->
  
  code2 ! pc = Some (RTL.Inop fresh) ->
  mvs = (seq_parmoves tmp (parcb_to_moves parcb)) ->

  reach_moves code2 fresh succ mvs (rev (rpc::lnew)) ->

  (R pc) = rpc ->

  code2 ! (R pc) = Some (RTL.Inop succ) ->
  
  rtldpar_spec tmp code1 pcode1 code2 R pc

| dspec_copy : forall ins, 
  code1 ! pc = Some ins -> 
  (forall succ, ins <> Inop succ) ->
  code2 ! pc = Some (map_pamr ins) ->
  R pc = pc ->
  rtldpar_spec tmp code1 pcode1 code2 R pc.  

Definition map_pc (pnum: PTree.t node) (pc: node) : node :=
  match pnum!pc with
  | Some pc' => pc'
  | None => 1%positive (* impossible case, never exercised *)
  end.

Variant transl_function_spec: RTLpar.function -> RTL.function -> (node -> node) -> Prop :=
| transl_function_spec_intro: forall f tf preds init max pl s incr,
    forall 
      (PREDS: preds = (make_predecessors (RTLpar.fn_code f) successors_instr))
      (INITS: (init,max,pl) = init_state f)
      (MFOLD: mfold_unit (copy_wwo_add (fresh_init f) preds (RTLpar.fn_code f) (RTLpar.fn_parcopycode f) max) (sort_pp pl) init = OK tt s incr)
      (DPARSPEC: forall pc ins, (RTLpar.fn_code f) ! pc = Some ins -> 
                                rtldpar_spec (fresh_init f)
                                             (RTLpar.fn_code f)
                                             (RTLpar.fn_parcopycode f) 
                                             (RTL.fn_code tf) 
                                             (map_pc (st_renum s)) pc),
      transl_function_spec f tf (map_pc (st_renum s)).

