(** Utility definitions and lemmas about the RTL representation *)
Require Recdef.
Require Import FSets.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Registers.
Require Import Op.
Require Import RTL.
Require Import RTLdfs.
Require Import Kildall.
Require Import KildallComp.
Require Import Utils.
Require Import Classical.

Unset Allow StrictProp.

(** * The [cfg] predicate *)
Variant cfg (code:code) (i j:RTL.node) : Prop :=
  | CFG : forall ins
    (HCFG_ins: code!i = Some ins)
    (HCFG_in : In j (successors_instr ins)),
    cfg code i j.

Inductive cfg_star (code:code) (i:RTL.node) : RTL.node -> Prop :=
| cfg_star0 : cfg_star code i i
| cfg_star1 : forall j k, cfg_star code i j -> cfg code j k -> cfg_star code i k.

Lemma cfg_star_same : forall code i j,
  cfg_star code i j <-> (cfg code)** i j.
Proof.
  split.
  induction 1.
  constructor 2.
  constructor 3 with j; auto.
  assert (forall i j, (cfg code**) i j -> forall k, cfg_star code k i -> cfg_star code k j).
    clear i j; induction 1; auto.
    intros.
    constructor 2 with x; auto.
  intros; apply H with i; auto.
  constructor 1.
Qed.

Lemma cfg_star_same_code: forall code1 code2 i,
  (forall k, cfg_star code1 i k -> code1!k = code2!k) ->
  forall j, cfg_star code1 i j -> cfg_star code2 i j.
Proof.
  induction 2.
  constructor 1.
  constructor 2 with j; auto.
  inv H1.
  rewrite H in *; auto.
  econstructor; eauto.
Qed.


Ltac simpl_succs := 
  match goal with 
    | [H1 : (RTL.fn_code ?f) ! ?pc = Some _ |- _ ] =>
      unfold successors_list, RTL.successors_map ; rewrite PTree.gmap1 ;
        (rewrite H1; simpl; auto)
  end.
  
(** * Registers that are used in the code of a RTL function *)
(** This has to be cleaned out. Cf RTL.use_instr *)

  Variant use_rtl_code (f: function) : Registers.reg -> node -> Prop := 
  | UIop: forall pc arg op args dst s, 
    (RTLdfs.fn_code f) !pc = Some (RTL.Iop op args dst s)  -> In arg args -> use_rtl_code f arg pc
  | UIload: forall pc arg chk adr args dst s,
    (RTLdfs.fn_code f) !pc = Some (RTL.Iload chk adr args dst s) -> In arg args -> use_rtl_code f arg pc
  | UIcond: forall pc arg cond args s s',
    (RTLdfs.fn_code f) !pc = Some (RTL.Icond cond args s s') -> In arg args -> use_rtl_code f arg pc 
  | UIbuiltin: forall pc arg ef args dst s,
    (RTLdfs.fn_code f) !pc = Some (RTL.Ibuiltin ef args dst s) -> In arg (params_of_builtin_args args) -> use_rtl_code f arg pc
  | UIstore: forall pc arg chk adr args src s,
    (RTLdfs.fn_code f) !pc = Some (RTL.Istore chk adr args src s) -> In arg (src::args) -> use_rtl_code f arg pc
  | UIcall: forall pc arg sig r args dst s,
    (RTLdfs.fn_code f) !pc = Some (RTL.Icall sig (inl ident r) args dst s) -> In arg (r::args) -> use_rtl_code f arg pc
  | UIcall2: forall pc arg sig id args dst s,
    (RTLdfs.fn_code f) !pc = Some (RTL.Icall sig (inr _ id) args dst s) -> In arg args -> use_rtl_code f arg pc
  | UItailcall: forall pc arg sig r args,
    (RTLdfs.fn_code f) !pc = Some (RTL.Itailcall sig (inl ident r) args) -> In arg (r::args) -> use_rtl_code f arg pc
  | UItailcall2: forall pc arg sig id args,
    (RTLdfs.fn_code f) !pc = Some (RTL.Itailcall sig (inr _ id) args) -> In arg args -> use_rtl_code f arg pc
  | UIjump: forall pc arg tbl, 
    (RTLdfs.fn_code f) !pc = Some (RTL.Ijumptable arg tbl) -> use_rtl_code f arg pc
  | UIret: forall pc arg,
    (RTLdfs.fn_code f) !pc = Some (RTL.Ireturn (Some arg)) -> use_rtl_code f arg pc.
  
  Global Hint Constructors use_rtl_code: core.
  Global Hint Extern 4 (In _ (RTL.successors_instr _)) => simpl successors_instr: core.
  Global Hint Constructors cfg: core.

  Variant join_point (jp : node) (f : function) : Prop :=
  |  jp_cons : forall l,
      forall (Hpreds : (make_predecessors (fn_code f) successors_instr) ! jp = Some l)
             (Hl : (List.length l > 1)%nat),
        join_point jp f.

  Section UDEF.

    Variable f : function.

    Variant assigned_code_spec (code:code) (pc:node) : reg -> Prop :=
    | AIop: forall op args dst succ,
        code!pc = Some (Iop op args dst succ)  ->
        assigned_code_spec code pc dst
    | AIload: forall chunk addr args dst succ,
        code!pc = Some (Iload chunk addr args dst succ) ->
        assigned_code_spec code pc dst
    | AIcall: forall sig fn args dst succ,
        code!pc = Some (Icall sig fn args dst succ) ->
        assigned_code_spec code pc dst
    | AIbuiltin: forall fn args dst succ,
        code!pc = Some (Ibuiltin fn args (BR dst) succ) ->
        assigned_code_spec code pc dst.
    Hint Constructors assigned_code_spec: core.

  End UDEF.
