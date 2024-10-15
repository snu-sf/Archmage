(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for constant propagation. *)

Require Import Coqlib Maps Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Simulation RTLD Classical PointerOp.
Require Import Values Builtins Events Memory Globalenvs Smallstep.
Require Compopts Machregs.
Require Import Op Registers RTL.
Require Import Liveness ValueDomain ValueAOp ValueAnalysis.
Require Import ConstpropOp ConstpropOpproof Constprop.
From Paco Require Import paco.

Definition match_prog (prog tprog: program) :=
  match_program (fun cu f tf => tf = transf_fundef (romem_for cu) f) eq prog tprog.

Lemma transf_program_match:
  forall prog, match_prog prog (transf_program prog).
Proof.
  intros. eapply match_transform_program_contextual. auto.
Qed.

Section PRESERVATION.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Let sem := semantics prog.
Let tsem := semantics tprog.

(** * Correctness of the code transformation *)

(** We now show that the transformed code after constant propagation
  has the same semantics as the original code. *)

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSL).

Lemma same_public: prog_public prog = prog_public tprog.
Proof. inv TRANSL. des; eauto. Qed.

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  exists cunit, Genv.find_funct tge v = Some (transf_fundef (romem_for cunit) f) /\ linkorder cunit prog.
Proof.
  intros. exploit (Genv.find_funct_match TRANSL); eauto.
  intros (cu & tf & A & B & C). subst tf. exists cu; auto.
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists cunit, Genv.find_funct_ptr tge b = Some (transf_fundef (romem_for cunit) f) /\ linkorder cunit prog.
Proof.
  intros. exploit (Genv.find_funct_ptr_match TRANSL); eauto.
  intros (cu & tf & A & B & C). subst tf. exists cu; auto.
Qed.

Lemma sig_function_translated:
  forall rm f,
  funsig (transf_fundef rm f) = funsig f.
Proof.
  intros. destruct f; reflexivity.
Qed.

Lemma init_regs_lessdef:
  forall rl vl1 vl2,
  Val.lessdef_list vl1 vl2 ->
  regs_lessdef (init_regs vl1 rl) (init_regs vl2 rl).
Proof.
  induction rl; simpl; intros.
  red; intros. rewrite Regmap.gi. auto.
  inv H. red; intros. rewrite Regmap.gi. auto.
  apply set_reg_lessdef; auto.
Qed.

Lemma transf_ros_correct:
  forall bc rs ae ros f rs' m m' (MEXT: Mem.extends m m'),
  genv_match bc ge ->
  ematch bc rs ae ->
  find_function ge (ros_to_vos m ros rs) rs = Some f ->
  regs_lessdef rs rs' ->
  exists cunit,
     find_function tge (ros_to_vos m' (transf_ros ae ros) rs') rs' = Some (transf_fundef (romem_for cunit) f)
  /\ linkorder cunit prog.
Proof.
  intros until m'; intros MEXT GE EM FF RLD. destruct ros; simpl in *.
- (* function pointer *)
  generalize (EM r); fold (areg ae r); intro VM. generalize (RLD r); intro LD.
  destruct (rs # r) eqn:RSV; try by ss.
+ des_ifs_safe. inv LD. des_ifs; try by inv VM.
* simpl. rewrite <- H1. des_ifs_safe. erewrite Mem.denormalize_extends; eauto. ss. des_ifs_safe.
  apply function_ptr_translated; auto.
* simpl. rewrite <- H1. des_ifs_safe. erewrite Mem.denormalize_extends; eauto. ss. des_ifs_safe.
  apply function_ptr_translated; auto.
+ simpl in FF. des_ifs_safe. inv LD. rename H1 into VPTR.
  assert (DEFAULT:
    exists cunit,
       find_function tge (inl _ rs'#r) rs' = Some (transf_fundef (romem_for cunit) f)
    /\ linkorder cunit prog).
  {
    simpl. apply functions_translated; auto. rewrite <- VPTR. eauto.
  }
  destruct (areg ae r); auto; try by inv VM.
  2:{ unfold ros_to_vos. rewrite <- VPTR in *. eauto. }
  rewrite <- VPTR in *. simpl in DEFAULT.
  destruct p; auto; ss; try rewrite <- VPTR; ss.
  predSpec Ptrofs.eq Ptrofs.eq_spec ofs Ptrofs.zero; intros; auto.
  2:{ inv VM. inv H1. clarify. }
  subst ofs. exploit vmatch_ptr_gl; eauto. intros LD'. inv LD'; try discriminate.
  assert (FF': Genv.find_funct ge (Vptr b Ptrofs.zero) = Some f) by ss.
  rewrite H1 in FF'. unfold Genv.symbol_address in FF'.
  simpl. rewrite symbols_preserved.
  destruct (Genv.find_symbol ge id) as [b'|]; try discriminate.
  simpl in FF'. rewrite dec_eq_true in FF'.
  apply function_ptr_translated; auto.
- (* function symbol *) 
  rewrite symbols_preserved.
  destruct (Genv.find_symbol ge i) as [b|]; try discriminate.
  apply function_ptr_translated; auto.
Qed.

Lemma const_for_result_correct:
  forall a op bc v sp m,
  const_for_result a = Some op ->
  vmatch bc v a ->
  bc sp = BCstack ->
  genv_match bc ge ->
  exists v', eval_operation_wrapper tge (Vptr sp Ptrofs.zero) op nil m = Some v' /\ Val.lessdef v v'.
Proof.
  intros. exploit ConstpropOpproof.const_for_result_correct; eauto. intros (v' & A & B).
  exists v'; split.
  rewrite <- A; apply eval_operation_wrapper_preserved. exact symbols_preserved.
  auto.
Qed.

Inductive match_pc (f: function) (rs: regset) (m: mem): nat -> node -> node -> Prop :=
  | match_pc_base: forall n pc,
      match_pc f rs m n pc pc
  | match_pc_nop: forall n pc s pcx,
      f.(fn_code)!pc = Some (Inop s) ->
      match_pc f rs m n s pcx ->
      match_pc f rs m (S n) pc pcx
  | match_pc_cond: forall n pc cond args s1 s2 pcx,
      f.(fn_code)!pc = Some (Icond cond args s1 s2) ->
      (forall b,
        eval_condition_wrapper cond rs##args m = Some b ->
        match_pc f rs m n (if b then s1 else s2) pcx) ->
      match_pc f rs m (S n) pc pcx.

Lemma match_successor_rec:
  forall f rs m bc ae,
  ematch bc rs ae ->
  forall n pc,
  match_pc f rs m n pc (successor_rec n f ae pc).
Proof.
  induction n; simpl; intros.
- apply match_pc_base.
- destruct (fn_code f)!pc as [[]|] eqn:INSTR; try apply match_pc_base.
+ eapply match_pc_nop; eauto.
+ destruct (resolve_branch (eval_static_condition c (aregs ae l))) as [b|] eqn:STATIC;
  try apply match_pc_base.
  eapply match_pc_cond; eauto. intros b' DYNAMIC.
  assert (b = b').
  { eapply resolve_branch_sound; eauto.
    rewrite <- DYNAMIC. apply eval_static_condition_wrapper_sound with bc.
    apply aregs_sound; auto. }
  subst b'. apply IHn.
Qed.

Lemma match_successor:
  forall f rs m bc ae pc,
  ematch bc rs ae -> match_pc f rs m num_iter pc (successor f ae pc).
Proof.
  intros. eapply match_successor_rec; eauto.
Qed.

Lemma builtin_arg_reduction_correct:
  forall bc sp m rs ae, ematch bc rs ae ->
  forall a v,
  eval_builtin_arg ge (fun r => rs#r) sp m a v ->
  eval_builtin_arg ge (fun r => rs#r) sp m (builtin_arg_reduction ae a) v.
Proof.
  induction 2; simpl; eauto with barg.
- specialize (H x). unfold areg. destruct (AE.get x ae); try constructor.
  + inv H. constructor.
  + inv H. constructor.
  + destruct (Compopts.generate_float_constants tt); [inv H|idtac]; constructor.
  + destruct (Compopts.generate_float_constants tt); [inv H|idtac]; constructor.
- destruct (builtin_arg_reduction ae hi); auto with barg.
  destruct (builtin_arg_reduction ae lo); auto with barg.
  inv IHeval_builtin_arg1; inv IHeval_builtin_arg2. constructor.
Qed.

Lemma builtin_arg_strength_reduction_correct:
  forall bc sp m rs ae a v c,
  ematch bc rs ae ->
  eval_builtin_arg ge (fun r => rs#r) sp m a v ->
  eval_builtin_arg ge (fun r => rs#r) sp m (builtin_arg_strength_reduction ae a c) v.
Proof.
  intros. unfold builtin_arg_strength_reduction.
  destruct (builtin_arg_ok (builtin_arg_reduction ae a) c).
  eapply builtin_arg_reduction_correct; eauto.
  auto.
Qed.

Lemma builtin_args_strength_reduction_correct:
  forall bc sp m rs ae, ematch bc rs ae ->
  forall al vl,
  eval_builtin_args ge (fun r => rs#r) sp m al vl ->
  forall cl,
  eval_builtin_args ge (fun r => rs#r) sp m (builtin_args_strength_reduction ae al cl) vl.
Proof.
  induction 2; simpl; constructor.
  eapply builtin_arg_strength_reduction_correct; eauto.
  apply IHlist_forall2.
Qed.

Lemma debug_strength_reduction_correct:
  forall bc sp m rs ae, ematch bc rs ae ->
  forall al vl,
  eval_builtin_args ge (fun r => rs#r) sp m al vl ->
  exists vl', eval_builtin_args ge (fun r => rs#r) sp m (debug_strength_reduction ae al) vl'.
Proof.
  induction 2; simpl.
- exists (@nil val); constructor.
- destruct IHlist_forall2 as (vl' & A).
  assert (eval_builtin_args ge (fun r => rs#r) sp m
             (a1 :: debug_strength_reduction ae al) (b1 :: vl'))
  by (constructor; eauto).
  destruct a1; try (econstructor; eassumption).
  destruct (builtin_arg_reduction ae (BA x)); repeat (eauto; econstructor).
Qed.

Lemma builtin_strength_reduction_correct:
  forall sp bc ae rs ef args vargs m t vres m',
  ematch bc rs ae ->
  eval_builtin_args ge (fun r => rs#r) sp m args vargs ->
  external_call ef ge vargs m t vres m' ->
  exists vargs',
     eval_builtin_args ge (fun r => rs#r) sp m (builtin_strength_reduction ae ef args) vargs'
  /\ external_call ef ge vargs' m t vres m'.
Proof.
  intros.
  assert (DEFAULT: forall cl,
    exists vargs',
       eval_builtin_args ge (fun r => rs#r) sp m (builtin_args_strength_reduction ae args cl) vargs'
    /\ external_call ef ge vargs' m t vres m').
  { exists vargs; split; auto. eapply builtin_args_strength_reduction_correct; eauto. }
  unfold builtin_strength_reduction.
  destruct ef; auto.
  exploit debug_strength_reduction_correct; eauto. intros (vargs' & P).
  exists vargs'; split; auto.
  inv H1; constructor.
Qed.

(** The proof of semantic preservation is a simulation argument
  based on "option" diagrams of the following form:
<<
                 n
       st1 --------------- st2
        |                   |
       t|                   |t or (? and n' < n)
        |                   |
        v                   v
       st1'--------------- st2'
                 n'
>>
  The left vertical arrow represents a transition in the
  original RTL code.  The top horizontal bar is the [match_states]
  invariant between the initial state [st1] in the original RTL code
  and an initial state [st2] in the transformed code.
  This invariant expresses that all code fragments appearing in [st2]
  are obtained by [transf_code] transformation of the corresponding
  fragments in [st1].  Moreover, the state [st1] must match its compile-time
  approximations at the current program point.
  These two parts of the diagram are the hypotheses.  In conclusions,
  we want to prove the other two parts: the right vertical arrow,
  which is a transition in the transformed RTL code, and the bottom
  horizontal bar, which means that the [match_state] predicate holds
  between the final states [st1'] and [st2']. *)

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
   match_stackframe_intro:
      forall res sp pc rs f rs' cu,
      linkorder cu prog ->
      regs_lessdef rs rs' ->
    match_stackframes
        (Stackframe res f sp pc rs)
        (Stackframe res (transf_function (romem_for cu) f) sp pc rs').

Inductive match_states: nat -> state -> state -> Prop :=
  | match_states_intro:
      forall s sp pc rs m f s' pc' rs' m' cu n
           (LINK: linkorder cu prog)
           (STACKS: list_forall2 match_stackframes s s')
           (PC: match_pc f rs m n pc pc')
           (REGS: regs_lessdef rs rs')
           (MEM: Mem.extends m m'),
      match_states n (State s f sp pc rs m)
                    (State s' (transf_function (romem_for cu) f) sp pc' rs' m')
  | match_states_call:
      forall s f args m s' args' m' cu
           (LINK: linkorder cu prog)
           (STACKS: list_forall2 match_stackframes s s')
           (ARGS: Val.lessdef_list args args')
           (MEM: Mem.extends m m'),
      match_states O (Callstate s f args m)
                     (Callstate s' (transf_fundef (romem_for cu) f) args' m')
  | match_states_return:
      forall s v m s' v' m'
           (STACKS: list_forall2 match_stackframes s s')
           (RES: Val.lessdef v v')
           (MEM: Mem.extends m m'),
      list_forall2 match_stackframes s s' ->
      match_states O (Returnstate s v m)
                     (Returnstate s' v' m').

Lemma match_states_succ:
  forall s f sp pc rs m s' rs' m' cu,
  linkorder cu prog ->
  list_forall2 match_stackframes s s' ->
  regs_lessdef rs rs' ->
  Mem.extends m m' ->
  match_states O (State s f sp pc rs m)
                 (State s' (transf_function (romem_for cu) f) sp pc rs' m').
Proof.
  intros. apply match_states_intro; auto. constructor.
Qed.

Lemma transf_instr_at:
  forall rm f pc i,
  f.(fn_code)!pc = Some i ->
  (transf_function rm f).(fn_code)!pc = Some(transf_instr f (analyze rm f) rm pc i).
Proof.
  intros. simpl. rewrite PTree.gmap. rewrite H. auto.
Qed.

Ltac TransfInstr :=
  match goal with
  | H1: (PTree.get ?pc (fn_code ?f) = Some ?instr),
    H2: (analyze ?rm ?f)#?pc = VA.State ?ae ?am |- _ =>
      generalize (transf_instr_at rm _ _ _ H1); unfold transf_instr; rewrite H2
  end.

(** The proof of simulation proceeds by case analysis on the transition
  taken in the source code. *)

Lemma transf_step_correct:
  forall s1 t s2,
  IStep sem s1 t s2 ->
  forall n1 s1' (SS: sound_state prog s1) (MS: match_states n1 s1 s1'),
  (exists n2, exists s2', DStep tsem s1' t s2' /\ match_states n2 s2 s2')
  \/ (exists n2, n2 < n1 /\ t = E0 /\ match_states n2 s2 s1')%nat.
Proof.
  destruct 1. generalize dependent s2. rename H into INT.
  induction 1; intros; inv MS; try InvSoundState; try (inv PC; try congruence).

- (* Inop, preserved *)
  rename pc'0 into pc. TransfInstr; intros.
  left; econstructor; econstructor; split.
  DStep_tac. eapply exec_Inop; eauto.
  eapply match_states_succ; eauto.

- (* Inop, skipped over *)
  assert (s0 = pc') by congruence. subst s0.
  right; exists n; split. lia. split. auto.
  apply match_states_intro; auto.

- (* Iop *)
  rename pc'0 into pc. TransfInstr.
  set (a := eval_static_operation op (aregs ae args)).
  set (ae' := AE.set res a ae).
  assert (VMATCH: vmatch bc v a) by (eapply eval_static_operation_wrapper_sound; eauto with va).
  assert (MATCH': ematch bc (rs#res <- v) ae') by (eapply ematch_update; eauto).
  destruct (const_for_result a) as [cop|] eqn:?; intros.
+ (* constant is propagated *)
  exploit const_for_result_correct; eauto. intros (v' & A & B).
  left; econstructor; econstructor; split.
  DStep_tac. eapply exec_Iop; eauto.
  apply match_states_intro; auto.
  eapply match_successor; eauto.
  apply set_reg_lessdef; auto.
+ (* operator is strength-reduced *)
  assert(OP:
     let (op', args') := op_strength_reduction op args (aregs ae args) in
     exists v',
        eval_operation_wrapper ge (Vptr sp0 Ptrofs.zero) op' rs ## args' m = Some v' /\
        Val.lessdef v v').
  { eapply op_strength_reduction_wrapper_correct with (ae := ae); eauto with va. }
  destruct (op_strength_reduction op args (aregs ae args)) as [op' args'].
  destruct OP as [v' [EV' LD']].
  assert (EV'': exists v'', eval_operation_wrapper ge (Vptr sp0 Ptrofs.zero) op' rs'##args' m' = Some v'' /\ Val.lessdef v' v'').
  { eapply eval_operation_wrapper_lessdef; eauto. eapply regs_lessdef_regs; eauto. }
  destruct EV'' as [v'' [EV'' LD'']].
  left; econstructor; econstructor; split.
  DStep_tac. eapply exec_Iop; eauto.
  erewrite eval_operation_wrapper_preserved. eexact EV''. exact symbols_preserved.
  apply match_states_intro; auto.
  eapply match_successor; eauto.
  apply set_reg_lessdef; auto. eapply Val.lessdef_trans; eauto.

- (* Iload *)
  rename pc'0 into pc. TransfInstr.
  set (aa := eval_static_addressing addr (aregs ae args)).
  assert (VM1: vmatch bc a aa) by (eapply eval_static_addressing_sound; eauto with va).
  set (av := loadv chunk (romem_for cu) am aa).
  assert (VM2: vmatch bc v av) by (eapply loadv_sound; eauto).
  destruct (const_for_result av) as [cop|] eqn:?; intros.
+ (* constant-propagated *)
  exploit const_for_result_correct; eauto. intros (v' & A & B).
  left; econstructor; econstructor; split.
  DStep_tac. eapply exec_Iop; eauto.
  eapply match_states_succ; eauto.
  apply set_reg_lessdef; auto.
+ (* strength-reduced *)
  assert (ADDR:
     let (addr', args') := addr_strength_reduction addr args (aregs ae args) in
     exists a',
        eval_addressing ge (Vptr sp0 Ptrofs.zero) addr' rs ## args' = Some a' /\
        Val.lessdef a a').
  { eapply addr_strength_reduction_correct with (ae := ae); eauto with va. }
  destruct (addr_strength_reduction addr args (aregs ae args)) as [addr' args'].
  destruct ADDR as (a' & P & Q).
  exploit eval_addressing_lessdef. eapply regs_lessdef_regs; eauto. eexact P.
  intros (a'' & U & V).
  assert (W: eval_addressing tge (Vptr sp0 Ptrofs.zero) addr' rs'##args' = Some a'').
  { rewrite <- U. apply eval_addressing_preserved. exact symbols_preserved. }
  exploit Mem.loadv_extends. eauto. eauto. apply Val.lessdef_trans with a'; eauto.
  intros (v' & X & Y).
  left; econstructor; econstructor; split.
  DStep_tac. eapply exec_Iload; eauto.
  eapply match_states_succ; eauto. apply set_reg_lessdef; auto.

- (* Istore *)
  rename pc'0 into pc. TransfInstr.
  assert (ADDR:
     let (addr', args') := addr_strength_reduction addr args (aregs ae args) in
     exists a',
        eval_addressing ge (Vptr sp0 Ptrofs.zero) addr' rs ## args' = Some a' /\
        Val.lessdef a a').
  { eapply addr_strength_reduction_correct with (ae := ae); eauto with va. }
  destruct (addr_strength_reduction addr args (aregs ae args)) as [addr' args'].
  destruct ADDR as (a' & P & Q).
  exploit eval_addressing_lessdef. eapply regs_lessdef_regs; eauto. eexact P.
  intros (a'' & U & V).
  assert (W: eval_addressing tge (Vptr sp0 Ptrofs.zero) addr' rs'##args' = Some a'').
  { rewrite <- U. apply eval_addressing_preserved. exact symbols_preserved. }
  exploit Mem.storev_extends. eauto. eauto. apply Val.lessdef_trans with a'; eauto. apply REGS.
  intros (m2' & X & Y).
  left; econstructor; econstructor; split.
  DStep_tac. eapply exec_Istore; eauto.
  eapply match_states_succ; eauto.

- (* Icall *)
  rename pc'0 into pc.
  exploit transf_ros_correct; eauto. intros (cu' & FIND & LINK').
  TransfInstr; intro.
  left; econstructor; econstructor; split.
  DStep_tac. eapply exec_Icall; eauto. apply sig_function_translated; auto.
  constructor; auto. constructor; auto.
  econstructor; eauto.
  apply regs_lessdef_regs; auto.

- (* Itailcall *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  exploit transf_ros_correct; try eapply H0; eauto. intros (cu' & FIND & LINK').
  TransfInstr; intro.
  left; econstructor; econstructor; split.
  DStep_tac. eapply exec_Itailcall; eauto. apply sig_function_translated; auto.
  constructor; auto.
  apply regs_lessdef_regs; auto.

- (* Ibuiltin *)
  unfold is_internal in INT. ss. des_ifs.
  rename pc'0 into pc. TransfInstr; intros.
Opaque builtin_strength_reduction.
  set (dfl := Ibuiltin ef (builtin_strength_reduction ae ef args) res pc') in *.
  set (rm := romem_for cu) in *.
  assert (DFL: (fn_code (transf_function rm f))!pc = Some dfl ->
          exists (n2 : nat) (s2' : state),
            DStep tsem
             (State s' (transf_function rm f) (Vptr sp0 Ptrofs.zero) pc rs' m'0) t s2' /\
            match_states n2
             (State s f (Vptr sp0 Ptrofs.zero) pc' (regmap_setres res vres rs) m') s2').
  {
    exploit builtin_strength_reduction_correct; eauto. intros (vargs' & P & Q).
    exploit (@eval_builtin_args_lessdef _ ge (fun r => rs#r) (fun r => rs'#r)).
    apply REGS. eauto. eexact P.
    intros (vargs'' & U & V).
    exploit external_call_mem_extends; eauto.
    intros (v' & m2' & A & B & C & D).
    econstructor; econstructor; split.
    DStep_tac. eapply exec_Ibuiltin; eauto.
    eapply eval_builtin_args_preserved. eexact symbols_preserved. eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    eapply match_states_succ; eauto.
    apply set_res_lessdef; auto.
  }
  destruct ef; auto.
  destruct res; auto.
  destruct (lookup_builtin_function name sg) as [bf|] eqn:LK; auto.
  destruct (eval_static_builtin_function ae am rm bf args) as [a|] eqn:ES; auto.
  destruct (const_for_result a) as [cop|] eqn:CR; auto.
  clear DFL. simpl in H1; red in H1; rewrite LK in H1; inv H1.
  exploit const_for_result_correct; eauto.
  eapply eval_static_builtin_function_sound; eauto.
  intros (v' & A & B).
  left; econstructor; econstructor; split.
  DStep_tac. eapply exec_Iop; eauto.
  eapply match_states_succ; eauto.
  apply set_reg_lessdef; auto.
- (* Icond, preserved *)
  rename pc'0 into pc. TransfInstr.
  set (ac := eval_static_condition cond (aregs ae args)).
  assert (C: cmatch (eval_condition_wrapper cond rs ## args m) ac)
  by (eapply eval_static_condition_wrapper_sound; eauto with va).
  rewrite H0 in C.
  generalize (cond_strength_reduction_wrapper_correct bc ae rs m EM cond args (aregs ae args) (eq_refl _)).
  destruct (cond_strength_reduction cond args (aregs ae args)) as [cond' args'].
  intros EV1 TCODE.
  left; exists O; exists (State s' (transf_function (romem_for cu) f) (Vptr sp0 Ptrofs.zero) (if b then ifso else ifnot) rs' m'); split.
  destruct (resolve_branch ac) eqn: RB.
  assert (b0 = b) by (eapply resolve_branch_sound; eauto). subst b0.
  DStep_tac. destruct b; eapply exec_Inop; eauto.
  DStep_tac. eapply exec_Icond; eauto.
  eapply eval_condition_wrapper_lessdef with (vl1 := rs##args'); eauto. eapply regs_lessdef_regs; eauto. congruence.
  eapply match_states_succ; eauto.

- (* Icond, skipped over *)
  rewrite H1 in H; inv H.
  right; exists n; split. lia. split. auto.
  econstructor; eauto.

- (* Ijumptable *)
  rename pc'0 into pc.
  assert (A: (fn_code (transf_function (romem_for cu) f))!pc = Some(Ijumptable arg tbl)
             \/ (fn_code (transf_function (romem_for cu) f))!pc = Some(Inop pc')).
  { TransfInstr.
    destruct (areg ae arg) eqn:A; auto.
    generalize (EM arg). fold (areg ae arg); rewrite A.
    intros V; inv V. replace n0 with n by congruence.
    rewrite H1. auto. }
  assert (rs'#arg = Vint n).
  { generalize (REGS arg). rewrite H0. intros LD; inv LD; auto. }
  left; exists O; exists (State s' (transf_function (romem_for cu) f) (Vptr sp0 Ptrofs.zero) pc' rs' m'); split.
  destruct A. DStep_tac. eapply exec_Ijumptable; eauto. DStep_tac. eapply exec_Inop; eauto.
  eapply match_states_succ; eauto.

- (* Ireturn *)
  unfold is_internal in INT. ss. des_ifs. TransfInstr. i.
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  left; exists O; exists (Returnstate s' (regmap_optget or Vundef rs') m2'); split.
  DStep_tac. eapply exec_Ireturn; eauto. TransfInstr; auto.
  constructor; auto.
  destruct or; simpl; auto.

- (* internal function *)
  exploit Mem.alloc_extends. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros [m2' [A B]].
  simpl. unfold transf_function.
  left; exists O; econstructor; split.
  DStep_tac. eapply exec_function_internal; simpl; eauto.
  simpl. econstructor; eauto.
  constructor.
  apply init_regs_lessdef; auto.

- (* external function *)
  unfold is_internal in INT. ss.
  exploit external_call_mem_extends; eauto.
  intros [v' [m2' [A [B [C D]]]]].
  simpl. left; econstructor; econstructor; split.
  DStep_tac. eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.

- (* return *)
  inv H4. inv H1.
  left; exists O; econstructor; split.
  DStep_tac. eapply exec_return; eauto.
  econstructor; eauto. constructor. apply set_reg_lessdef; auto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists n, exists st2, initial_state tprog st2 /\ match_states n st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto. intros (cu & FIND & LINK).
  exists O; exists (Callstate nil (transf_fundef (romem_for cu) f) nil m0); split.
  econstructor; eauto.
  apply (Genv.init_mem_match TRANSL); auto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  symmetry; eapply match_program_main; eauto.
  rewrite <- H3. apply sig_function_translated.
  constructor. auto. constructor. constructor. apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall n st1 st2 r,
  match_states n st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. inv RES. constructor.
Qed.

Lemma match_states_bsim
      s1 (EXT: is_external ge s1)
      (SOUND: sound_state prog s1)
      s2 t s2' (STEPTGT: Step tsem s2 t s2')
      n (MATCH: match_states n s1 s2)
      (SAFESRC: safe sem s1) :
    (exists n' s1', Step sem s1 t s1' /\ match_states n' s1' s2')
  \/ (~ trace_intact t /\ exists s1'' t', Star sem s1 t' s1'' /\ exists tl, t' = (trace_cut_pterm t) ** tl).
Proof.
  assert (SEQUIV: Senv.equiv tge ge) by (symmetry; eapply senv_preserved).
  unfold safe in SAFESRC. specialize (SAFESRC _ (star_refl _ _ _)). des; cycle 2; clarify.
  { inv SAFESRC; ss. }
  unfold is_external in *. inv MATCH; des_ifs; try InvSoundState; try (inv PC; try congruence).
  (* builtin *)
  - TransfInstr; i.
    assert (TI: (fn_code (transf_function (romem_for cu) f)) ! pc' = Some (Ibuiltin e (builtin_strength_reduction ae e l) b n0)).
    { des_ifs. ss. des_ifs. }
    clear H. inv STEPTGT; clarify. inv SAFESRC; clarify.
    assert (eval_builtin_args (globalenv (semantics prog)) (fun r : positive => rs # r) (Vptr sp0 Ptrofs.zero) m
                              (builtin_strength_reduction ae e l) vargs0).
    { Local Transparent builtin_strength_reduction. unfold builtin_strength_reduction.
      des_ifs; eapply builtin_args_strength_reduction_correct; eauto. }
    exploit eval_builtin_args_lessdef. eapply REGS. eauto. eapply H. i. des.

    exploit eval_builtin_args_determ; [eapply H0| |].
    { eapply eval_builtin_args_preserved; [|eapply H8]. i. eapply SEQUIV. } i. subst.

    exploit external_call_mem_extends_backward. eauto. eapply H9. eauto. eauto. i; des; cycle 1.
    { exploit UBSRC. eapply external_call_symbols_preserved; eauto. eapply senv_preserved. contradiction. }
    { right. esplits; eauto. eapply star_one. eapply exec_Ibuiltin; eauto.
      eapply external_call_symbols_preserved; eauto. }
    { left. esplits.
      - eapply exec_Ibuiltin; eauto. eapply external_call_symbols_preserved; eauto.
      - eapply match_states_succ; eauto. apply set_res_lessdef; auto. }
  (* external call *)
  - inv SAFESRC; clarify. inv STEPTGT; ss; clarify.
    exploit external_call_mem_extends_backward; try apply H8; eauto. i; des; cycle 1.
    { exploit UBSRC; eauto. eapply external_call_symbols_preserved; eauto. eapply senv_preserved. i; ss. }
    { right. esplits; eauto. eapply star_one. eapply exec_function_external.
      eapply external_call_symbols_preserved; eauto. }
    exploit exec_function_external. eapply external_call_symbols_preserved; eauto.
    i. left. esplits; eauto. econs; eauto.
Qed.

Lemma match_states_xsim n st_src0 st_tgt0 gmtgt
    (SOUND: sound_state prog st_src0)
    (MATCH: match_states n%nat st_src0 st_tgt0):
  xsim (RTL.semantics prog) (RTL.semantics tprog) gmtgt lt n%nat st_src0 st_tgt0.
Proof.
  generalize dependent st_src0. generalize dependent st_tgt0. generalize dependent n.
  pcofix CIH. i. pfold. destruct (classic (is_external ge st_src0)); cycle 1; rename H into EXT.
  (* internal *)
  - left. econs. econs.
    + i. exploit transf_step_correct; eauto. i. des; esplits; eauto;
      [eapply tr_rel_refl; eapply ev_rel_refl| | |eapply tr_rel_refl; eapply ev_rel_refl|].
      { left. split. apply plus_one. eauto. eapply semantics_receptive_at; auto. }
      { right. eapply CIH; eauto. eapply sound_step; eauto. }
      { right. eapply CIH; eauto. eapply sound_step; eauto. }   
    + i. exploit transf_final_states; eauto. i. eapply final_state_determ; eauto.
  (* external *)
  - right. econs. i. econs.
    + i. exploit match_states_bsim; eauto. i. des.
      * left. esplits; eauto; [eapply tr_rel_refl; eapply ev_rel_refl| |].
        { left. eapply plus_one. eauto. }
        { right. eapply CIH; eauto. eapply sound_step; eauto. }
      * right. esplits; eauto.
        subst. eapply tr_rel_refl. eapply ev_rel_refl.
    + i. inv FINALTGT; inv MATCH; ss.
    + i. specialize (SAFESRC _ (star_refl _ _ _)). des; cycle 2; clarify; [inv SAFESRC; ss|].
      right. inv MATCH; ss; des_ifs; inv SAFESRC; unfold ge in *; clarify.
      * InvSoundState. TransfInstr; intros.
        assert (TI: (fn_code (transf_function (romem_for cu) f)) ! pc = Some (Ibuiltin e (builtin_strength_reduction ae e l) b n0)).
        { des_ifs. ss. des_ifs. } clear H.
        assert (pc = pc').
        { inv PC; clarify. } subst.
        exploit builtin_strength_reduction_correct; eauto. intros (vargs' & P & Q).
        exploit (@eval_builtin_args_lessdef _ ge (fun r => rs#r) (fun r => rs'#r)).
        apply REGS. eauto. eexact P.
        intros (vargs'' & U & V).
        exploit external_call_mem_extends_backward_progress; eauto. i. des.
        esplits. eapply exec_Ibuiltin; eauto.
        eapply eval_builtin_args_preserved. eexact symbols_preserved. eauto.
        eapply external_call_symbols_preserved; eauto. apply senv_preserved.
      * exploit external_call_mem_extends_backward_progress; eauto.
        i. des. esplits. eapply exec_function_external; eauto.
        eapply external_call_symbols_preserved; eauto. apply senv_preserved.
Qed.

Lemma non_static_equiv l:
  Genv.non_static_glob (Genv.globalenv prog) l = Genv.non_static_glob (Genv.globalenv tprog) l.
Proof.
  Local Transparent ge tge.
  induction l; ss.
  specialize senv_preserved. ss. i. inv H. inv H1. unfold ge, tge, fundef in *.
  specialize (H a). unfold Senv.public_symbol in H. ss. erewrite H.
  specialize (H0 a). rewrite <- H0. erewrite IHl; eauto.
Qed.

Lemma transf_initial_capture S1 S2 S2' i
    (INITSRC: initial_state prog S1)
    (INITTGT: initial_state tprog S2)
    (MATCH: match_states i S1 S2)
    (CAPTGT: glob_capture tprog S2 S2'):
  exists i' S1', glob_capture prog S1 S1'
  /\ match_states i' S1' S2'
  /\ gm_improves (concrete_snapshot ge S1') (concrete_snapshot tge S2').
Proof.
  specialize senv_preserved. intros SENVEQ.
  inv CAPTGT. ss. rename m' into m2'.
  rewrite Genv.globalenv_public in CAPTURE. erewrite <- same_public in CAPTURE; eauto.
  inv MATCH. inv ARGS. inv STACKS.
  exploit non_static_equiv. instantiate (1:=AST.prog_public prog). intros EQUIV.
  assert (exists m1', Genv.capture_init_mem m0 (Genv.non_static_glob (Genv.globalenv prog) (AST.prog_public prog)) m1' /\
                     Mem.extends m1' m2').
  { clear LINK INITSRC INITTGT.
    rewrite <- EQUIV in CAPTURE. clear EQUIV. inv CAPTURE.
    remember (Genv.non_static_glob (Genv.globalenv prog) (prog_public prog)) as l. clear Heql.
    clear SENVEQ. (* move m0 after f0. *) move l before f0. revert_until f0.
    induction l; ss; i.
    { inv CAP. esplits; eauto. econs. econs. }
    inv CAP. exploit Mem.capture_extends_backward; eauto. i. des.
    exploit IHl; eauto. i. des. inv H. esplits; eauto. econs. econs; eauto. }
  des. esplits; eauto.
  - econs. eauto. rewrite Genv.globalenv_public. eauto.
  - econs; eauto. econs.
  - ii. unfold concrete_snapshot in *. inv SENVEQ. des. erewrite H3, H2. des_ifs; ss.
    eapply Mem.mext_concrete; eauto. eapply Mem.concrete_valid; eauto.
Qed.

(** The preservation of the observable behavior of the program then
  follows. *)

Theorem transf_program_correct:
  mixed_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  econs. econs.
  - apply lt_wf.
  - rr. i. exists (S a). lia.
  - econs. i. exploit transf_initial_states; eauto. i. des.
    exists st2. split.
    (* initial state *)
    + econs; eauto. eapply initial_state_determ.
    (* mixed sim *) 
    + r. ii. inversion INITSRC; subst. inversion H0; subst.
      inv ARGS. inv STACKS.
      exploit transf_initial_capture; eauto. i. des.
      exists i'%nat. exists S1'. esplits; eauto.
      apply match_states_xsim; auto.
      eapply sound_capture_initial; eauto.
  - i. apply senv_preserved.
Qed.

End PRESERVATION.
