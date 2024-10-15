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

(** Recognition of tail calls: correctness proof *)

Require Import Coqlib Maps Integers AST Linking.
Require Import CoqlibC Simulation RTLD Classical PointerOp.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL Conventions Tailcall.
From Paco Require Import paco.

(** * Syntactic properties of the code transformation *)

(** ** Measuring the number of instructions eliminated *)

(** The [return_measure c pc] function counts the number of instructions
  eliminated by the code transformation, where [pc] is the successor
  of a call turned into a tailcall.  This is the length of the
  move/nop/return sequence recognized by the [is_return] boolean function.
*)

Fixpoint return_measure_rec (n: nat) (c: code) (pc: node)
                            {struct n}: nat :=
  match n with
  | O => O
  | S n' =>
      match c!pc with
      | Some(Inop s) => S(return_measure_rec n' c s)
      | Some(Iop op args dst s) => S(return_measure_rec n' c s)
      | _ => O
      end
  end.

Definition return_measure (c: code) (pc: node) :=
  return_measure_rec niter c pc.

Lemma return_measure_bounds:
  forall f pc, (return_measure f pc <= niter)%nat.
Proof.
  intro f.
  assert (forall n pc, (return_measure_rec n f pc <= n)%nat).
    induction n; intros; simpl.
    lia.
    destruct (f!pc); try lia.
    destruct i; try lia.
    generalize (IHn n0). lia.
    generalize (IHn n0). lia.
  intros. unfold return_measure. apply H.
Qed.

Remark return_measure_rec_incr:
  forall f n1 n2 pc,
  (n1 <= n2)%nat ->
  (return_measure_rec n1 f pc <= return_measure_rec n2 f pc)%nat.
Proof.
  induction n1; intros; simpl.
  lia.
  destruct n2. extlia. assert (n1 <= n2)%nat by lia.
  simpl. destruct f!pc; try lia. destruct i; try lia.
  generalize (IHn1 n2 n H0). lia.
  generalize (IHn1 n2 n H0). lia.
Qed.

Lemma is_return_measure_rec:
  forall f n n' pc r,
  is_return n f pc r = true -> (n <= n')%nat ->
  return_measure_rec n f.(fn_code) pc = return_measure_rec n' f.(fn_code) pc.
Proof.
  induction n; simpl; intros.
  congruence.
  destruct n'. extlia. simpl.
  destruct (fn_code f)!pc; try congruence.
  destruct i; try congruence.
  decEq. apply IHn with r. auto. lia.
  destruct (is_move_operation o l); try congruence.
  destruct (Reg.eq r r1); try congruence.
  decEq. apply IHn with r0. auto. lia.
Qed.

(** ** Relational characterization of the code transformation *)

(** The [is_return_spec] characterizes the instruction sequences
  recognized by the [is_return] boolean function.  *)

Inductive is_return_spec (f:function): node -> reg -> Prop :=
  | is_return_none: forall pc r,
      f.(fn_code)!pc = Some(Ireturn None) ->
      is_return_spec f pc r
  | is_return_some: forall pc r,
      f.(fn_code)!pc = Some(Ireturn (Some r)) ->
      is_return_spec f pc r
  | is_return_nop: forall pc r s,
      f.(fn_code)!pc = Some(Inop s) ->
      is_return_spec f s r ->
      (return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
      is_return_spec f pc r
  | is_return_move: forall pc r r' s,
      f.(fn_code)!pc = Some(Iop Omove (r::nil) r' s) ->
      is_return_spec f s r' ->
      (return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
     is_return_spec f pc r.

Lemma is_return_charact:
  forall f n pc rret,
  is_return n f pc rret = true -> (n <= niter)%nat ->
  is_return_spec f pc rret.
Proof.
  induction n; intros.
  simpl in H. congruence.
  generalize H. simpl.
  caseEq ((fn_code f)!pc); try congruence.
  intro i. caseEq i; try congruence.
  intros s; intros. eapply is_return_nop; eauto. eapply IHn; eauto. lia.
  unfold return_measure.
  rewrite <- (is_return_measure_rec f (S n) niter pc rret); auto.
  rewrite <- (is_return_measure_rec f n niter s rret); auto.
  simpl. rewrite H2. lia. lia.

  intros op args dst s EQ1 EQ2.
  caseEq (is_move_operation op args); try congruence.
  intros src IMO. destruct (Reg.eq rret src); try congruence.
  subst rret. intro.
  exploit is_move_operation_correct; eauto. intros [A B]. subst.
  eapply is_return_move; eauto. eapply IHn; eauto. lia.
  unfold return_measure.
  rewrite <- (is_return_measure_rec f (S n) niter pc src); auto.
  rewrite <- (is_return_measure_rec f n niter s dst); auto.
  simpl. rewrite EQ2. lia. lia.

  intros or EQ1 EQ2. destruct or; intros.
  assert (r = rret). eapply proj_sumbool_true; eauto. subst r.
  apply is_return_some; auto.
  apply is_return_none; auto.
Qed.

(** The [transf_instr_spec] predicate relates one instruction in the
  initial code with its possible transformations in the optimized code. *)

Inductive transf_instr_spec (f: function): instruction -> instruction -> Prop :=
  | transf_instr_tailcall: forall sig ros args res s,
      f.(fn_stacksize) = 0 ->
      is_return_spec f s res ->
      transf_instr_spec f (Icall sig ros args res s) (Itailcall sig ros args)
  | transf_instr_default: forall i,
      transf_instr_spec f i i.

Lemma transf_instr_charact:
  forall f pc instr,
  f.(fn_stacksize) = 0 ->
  transf_instr_spec f instr (transf_instr f pc instr).
Proof.
  intros. unfold transf_instr. destruct instr; try constructor.
  destruct (is_return niter f n r && tailcall_is_possible s &&
            rettype_eq (sig_res s) (sig_res (fn_sig f))) eqn:B.
- InvBooleans. eapply transf_instr_tailcall; eauto. eapply is_return_charact; eauto.
- constructor.
Qed.

Lemma transf_instr_lookup:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  exists i',  (transf_function f).(fn_code)!pc = Some i' /\ transf_instr_spec f i i'.
Proof.
  intros. unfold transf_function.
  destruct (zeq (fn_stacksize f) 0).
  simpl. rewrite PTree.gmap. rewrite H. simpl.
  exists (transf_instr f pc i); split. auto. apply transf_instr_charact; auto.
  exists i; split. auto. constructor.
Qed.

(** * Semantic properties of the code transformation *)

(** ** The ``less defined than'' relation between register states *)

(** A call followed by a return without an argument can be turned
  into a tail call.  In this case, the original function returns
  [Vundef], while the transformed function can return any value.
  We account for this situation by using the ``less defined than''
  relation between values and between memory states.  We need to
  extend it pointwise to register states. *)

Lemma regs_lessdef_init_regs:
  forall params vl vl',
  Val.lessdef_list vl vl' ->
  regs_lessdef (init_regs vl params) (init_regs vl' params).
Proof.
  induction params; intros.
  simpl. red; intros. rewrite Regmap.gi. constructor.
  simpl. inv H.   red; intros. rewrite Regmap.gi. constructor.
  apply set_reg_lessdef. auto. auto.
Qed.

(** * Proof of semantic preservation *)

Definition match_prog (p tp: RTL.program) :=
  match_program (fun cu f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. apply match_transform_program; auto.
Qed.

Section PRESERVATION.

Variable prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Let sem := semantics prog.
Let tsem := semantics tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf TRANSL).

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof (Genv.find_funct_transf TRANSL).

Lemma funct_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (transf_fundef f).
Proof (Genv.find_funct_ptr_transf TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_transf TRANSL).

Lemma same_public:
  prog_public prog = prog_public tprog.
Proof. inv TRANSL. des; eauto. Qed.

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; auto. simpl. unfold transf_function.
  destruct (zeq (fn_stacksize f) 0); auto.
Qed.

Lemma stacksize_preserved:
  forall f, fn_stacksize (transf_function f) = fn_stacksize f.
Proof.
  unfold transf_function. intros.
  destruct (zeq (fn_stacksize f) 0); auto.
Qed.

Lemma find_function_translated:
  forall ros rs rs' f m m' (MLD: Mem.extends m m'),
  find_function ge (ros_to_vos m ros rs) rs = Some f ->
  regs_lessdef rs rs' ->
  find_function tge (ros_to_vos m' ros rs') rs' = Some (transf_fundef f).
Proof.
  intros until m'; destruct ros; simpl.
  intros.
  assert (rs'#r = rs#r).
  { destruct (rs#r) eqn:RSV; ss.
    - specialize (H0 r). rewrite RSV in H0. inv H0. eauto.
    - specialize (H0 r). rewrite RSV in H0. inv H0. eauto. }
      (* assert (FUNC: Genv.find_funct ge (Vptr b i) = Some f) by ss. *)
      (* exploit Genv.find_funct_inv; eauto. intros [b' EQ]. *)
      (* generalize (H0 r). rewrite EQ. intro LD. inv LD. auto. *)
  rewrite H1. destruct (rs#r) eqn:RSV; try by ss.
  { des_ifs_safe. erewrite Mem.denormalize_extends; eauto.
    apply functions_translated; auto. }
  { apply functions_translated; auto. }
  intros.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i); intros.
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

(** Consider an execution of a call/move/nop/return sequence in the
  original code and the corresponding tailcall in the transformed code.
  The transition sequences are of the following form
  (left: original code, right: transformed code).
  [f] is the calling function and [fd] the called function.
<<
     State stk f (Icall instruction)       State stk' f' (Itailcall)

     Callstate (frame::stk) fd args        Callstate stk' fd' args'
            .                                       .
            .                                       .
            .                                       .
     Returnstate (frame::stk) res          Returnstate stk' res'

     State stk f (move/nop/return seq)
            .
            .
            .
     State stk f (return instr)

     Returnstate stk res
>>
The simulation invariant must therefore account for two kinds of
mismatches between the transition sequences:
- The call stack of the original program can contain more frames
  than that of the transformed program (e.g. [frame] in the example above).
- The regular states corresponding to executing the move/nop/return
  sequence must all correspond to the single [Returnstate stk' res']
  state of the transformed program.

We first define the simulation invariant between call stacks.
The first two cases are standard, but the third case corresponds
to a frame that was eliminated by the transformation. *)

Inductive match_stackframes: list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil:
      match_stackframes nil nil
  | match_stackframes_normal: forall stk stk' res sp pc rs rs' f,
      match_stackframes stk stk' ->
      regs_lessdef rs rs' ->
      match_stackframes
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        (Stackframe res (transf_function f) (Vptr sp Ptrofs.zero) pc rs' :: stk')
  | match_stackframes_tail: forall stk stk' res sp pc rs f,
      match_stackframes stk stk' ->
      is_return_spec f pc res ->
      f.(fn_stacksize) = 0 ->
      match_stackframes
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        stk'.

(** Here is the invariant relating two states.  The first three
  cases are standard.  Note the ``less defined than'' conditions
  over values and register states, and the corresponding ``extends''
  relation over memory states. *)

Inductive match_states: state -> state -> Prop :=
  | match_states_normal:
      forall s sp pc rs m s' rs' m' f
             (STACKS: match_stackframes s s')
             (RLD: regs_lessdef rs rs')
             (MLD: Mem.extends m m'),
      match_states (State s f (Vptr sp Ptrofs.zero) pc rs m)
                   (State s' (transf_function f) (Vptr sp Ptrofs.zero) pc rs' m')
  | match_states_call:
      forall s f args m s' args' m',
      match_stackframes s s' ->
      Val.lessdef_list args args' ->
      Mem.extends m m' ->
      match_states (Callstate s f args m)
                   (Callstate s' (transf_fundef f) args' m')
  | match_states_return:
      forall s v m s' v' m',
      match_stackframes s s' ->
      Val.lessdef v v' ->
      Mem.extends m m' ->
      match_states (Returnstate s v m)
                   (Returnstate s' v' m')
  | match_states_interm:
      forall s sp pc rs m s' m' f r v'
             (STACKS: match_stackframes s s')
             (MLD: Mem.extends m m'),
      is_return_spec f pc r ->
      f.(fn_stacksize) = 0 ->
      Val.lessdef (rs#r) v' ->
      match_states (State s f (Vptr sp Ptrofs.zero) pc rs m)
                   (Returnstate s' v' m').

(** The last case of [match_states] corresponds to the execution
  of a move/nop/return sequence in the original code that was
  eliminated by the transformation:
<<
     State stk f (move/nop/return seq)  ~~  Returnstate stk' res'
            .
            .
            .
     State stk f (return instr)         ~~  Returnstate stk' res'
>>
  To preserve non-terminating behaviors, we need to make sure
  that the execution of this sequence in the original code cannot
  diverge.  For this, we introduce the following complicated
  measure over states, which will decrease strictly whenever
  the original code makes a transition but the transformed code
  does not. *)

Definition measure (st: state) : nat :=
  match st with
  | State s f sp pc rs m => (List.length s * (niter + 2) + return_measure f.(fn_code) pc + 1)%nat
  | Callstate s f args m => 0%nat
  | Returnstate s v m => (List.length s * (niter + 2))%nat
  end.

Ltac TransfInstr :=
  match goal with
  | H: (PTree.get _ (fn_code _) = _) |- _ =>
      destruct (transf_instr_lookup _ _ _ H) as [i' [TINSTR TSPEC]]; inv TSPEC
  end.

Ltac EliminatedInstr :=
  match goal with
  | H: (is_return_spec _ _ _) |- _ => inv H; try congruence
  | _ => idtac
  end.

(** The proof of semantic preservation, then, is a simulation diagram
  of the ``option'' kind. *)

Lemma transf_step_correct:
  forall s1 t s2, IStep sem s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  (exists s2', DStep tsem s1' t s2' /\ match_states s2 s2')
  \/ (measure s2 < measure s1 /\ t = E0 /\ match_states s2 s1')%nat.
Proof.
  destruct 1. generalize dependent s2. rename H into INT.
  induction 1; intros; inv MS; EliminatedInstr.

- (* nop *)
  TransfInstr. left. econstructor; split. DStep_tac.
  eapply exec_Inop; eauto. constructor; auto.
- (* eliminated nop *)
  assert (s0 = pc') by congruence. subst s0.
  right. split. simpl. lia. split. auto.
  econstructor; eauto.

- (* op *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
  exploit eval_operation_wrapper_lessdef; eauto.
  intros [v' [EVAL' VLD]].
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' (rs'#res <- v') m'); split.
  DStep_tac. eapply exec_Iop; eauto.  rewrite <- EVAL'.
  apply eval_operation_wrapper_preserved. exact symbols_preserved.
  econstructor; eauto. apply set_reg_lessdef; auto.
- (* eliminated move *)
  rewrite H1 in H. clear H1. inv H.
  right. split. simpl. lia. split. auto.
  rewrite eval_operation_no_ptr_op in H0; eauto.
  econstructor; eauto. simpl in H0. rewrite PMap.gss. congruence.

- (* load *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
  exploit eval_addressing_lessdef; eauto.
  intros [a' [ADDR' ALD]].
  exploit Mem.loadv_extends; eauto.
  intros [v' [LOAD' VLD]].
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' (rs'#dst <- v') m'); split.
  DStep_tac. eapply exec_Iload with (a := a'). eauto.  rewrite <- ADDR'.
  apply eval_addressing_preserved. exact symbols_preserved. eauto.
  econstructor; eauto. apply set_reg_lessdef; auto.

- (* store *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
  exploit eval_addressing_lessdef; eauto.
  intros [a' [ADDR' ALD]].
  exploit Mem.storev_extends. 2: eexact H1. eauto. eauto. apply RLD.
  intros [m'1 [STORE' MLD']].
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' rs' m'1); split.
  DStep_tac. eapply exec_Istore with (a := a'). eauto.  rewrite <- ADDR'.
  apply eval_addressing_preserved. exact symbols_preserved. eauto.
  destruct a; simpl in H1; try discriminate.
  econstructor; eauto.
  econstructor; eauto.

- (* call *)
  exploit find_function_translated; eauto. intro FIND'.
  TransfInstr.
+ (* call turned tailcall *)
  assert ({ m'' | Mem.free m' sp0 0 (fn_stacksize (transf_function f)) = Some m''}).
    apply Mem.range_perm_free. rewrite stacksize_preserved. rewrite H7.
    red; intros; extlia.
  destruct X as [m'' FREE].
  left. exists (Callstate s' (transf_fundef fd) (rs'##args) m''); split.
  DStep_tac. eapply exec_Itailcall; eauto. apply sig_preserved.
  constructor. eapply match_stackframes_tail; eauto. apply regs_lessdef_regs; auto.
  eapply Mem.free_right_extends; eauto.
  rewrite stacksize_preserved. rewrite H7. intros. extlia.
+ (* call that remains a call *)
  left. exists (Callstate (Stackframe res (transf_function f) (Vptr sp0 Ptrofs.zero) pc' rs' :: s')
                          (transf_fundef fd) (rs'##args) m'); split.
  DStep_tac. eapply exec_Icall; eauto. apply sig_preserved.
  constructor. constructor; auto. apply regs_lessdef_regs; auto. auto.

- (* tailcall *)
  exploit find_function_translated; eauto. intro FIND'.
  exploit Mem.free_parallel_extends; eauto. intros [m'1 [FREE EXT]].
  TransfInstr.
  left. exists (Callstate s' (transf_fundef fd) (rs'##args) m'1); split.
  DStep_tac. eapply exec_Itailcall; eauto. apply sig_preserved.
  rewrite stacksize_preserved; auto.
  constructor. auto.  apply regs_lessdef_regs; auto. auto.

- (* builtin *)
  unfold is_internal in INT. ss. des_ifs.
  TransfInstr.
  exploit (@eval_builtin_args_lessdef _ ge (fun r => rs#r) (fun r => rs'#r)); eauto.
  intros (vargs' & P & Q).
  exploit external_call_mem_extends; eauto.
  intros [v' [m'1 [A [B [C D]]]]].
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' (regmap_setres res v' rs') m'1); split.
  DStep_tac. eapply exec_Ibuiltin; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto. apply set_res_lessdef; auto.

- (* cond *)
  TransfInstr.
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) (if b then ifso else ifnot) rs' m'); split.
  DStep_tac. eapply exec_Icond; eauto.
  apply eval_condition_wrapper_lessdef with (rs##args) m; auto. apply regs_lessdef_regs; auto.
  constructor; auto.

- (* jumptable *)
  TransfInstr.
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' rs' m'); split.
  DStep_tac. eapply exec_Ijumptable; eauto.
  generalize (RLD arg). rewrite H0. intro. inv H2. auto.
  constructor; auto.

- (* return *)
  exploit Mem.free_parallel_extends; eauto. intros [m'1 [FREE EXT]].
  TransfInstr.
  left. exists (Returnstate s' (regmap_optget or Vundef rs') m'1); split.
  DStep_tac. apply exec_Ireturn; auto. rewrite stacksize_preserved; auto.
  constructor. auto.
  destruct or; simpl. apply RLD. constructor.
  auto.

- (* eliminated return None *)
  assert (or = None) by congruence. subst or.
  right. split. simpl. lia. split. auto.
  constructor. auto.
  simpl. constructor.
  eapply Mem.free_left_extends; eauto.

- (* eliminated return Some *)
  assert (or = Some r) by congruence. subst or.
  right. split. simpl. lia. split. auto.
  constructor. auto.
  simpl. auto.
  eapply Mem.free_left_extends; eauto.

- (* internal call *)
  exploit Mem.alloc_extends; eauto.
    instantiate (1 := 0). lia.
    instantiate (1 := fn_stacksize f). lia.
  intros [m'1 [ALLOC EXT]].
  assert (fn_stacksize (transf_function f) = fn_stacksize f /\
          fn_entrypoint (transf_function f) = fn_entrypoint f /\
          fn_params (transf_function f) = fn_params f).
    unfold transf_function. destruct (zeq (fn_stacksize f) 0); auto.
  destruct H0 as [EQ1 [EQ2 EQ3]].
  left. econstructor; split.
  DStep_tac. simpl. eapply exec_function_internal; eauto. rewrite EQ1; eauto.
  rewrite EQ2. rewrite EQ3. constructor; auto.
  apply regs_lessdef_init_regs. auto.

- (* external call *)
  unfold is_internal in INT. ss. des_ifs.
  exploit external_call_mem_extends; eauto.
  intros [res' [m2' [A [B [C D]]]]].
  left. exists (Returnstate s' res' m2'); split.
  DStep_tac. simpl. econstructor; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.

- (* returnstate *)
  inv H2.
+ (* synchronous return in both programs *)
  left. econstructor; split.
  DStep_tac. apply exec_return.
  constructor; auto. apply set_reg_lessdef; auto.
+ (* return instr in source program, eliminated because of tailcall *)
  right. split. unfold measure. simpl length.
  change (S (length s) * (niter + 2))%nat
   with ((niter + 2) + (length s) * (niter + 2))%nat.
  generalize (return_measure_bounds (fn_code f) pc). lia.
  split. auto.
  econstructor; eauto.
  rewrite Regmap.gss. auto.
Qed.

Lemma match_states_bsim
      s1 (EXT: is_external ge s1)
      s2 t s2' (STEPTGT: Step tsem s2 t s2')
      (MATCH: match_states s1 s2)
      (SAFESRC: safe sem s1) :
    (exists s1', Step sem s1 t s1' /\ match_states s1' s2')
    \/ (~ trace_intact t /\ exists s1'' t', Star sem s1 t' s1'' /\ exists tl, t' = (trace_cut_pterm t) ** tl).
Proof.
  assert (SEQUIV: Senv.equiv tge ge) by (symmetry; apply senv_preserved).
  unfold safe in SAFESRC. specialize (SAFESRC _ (star_refl _ _ _)). des; cycle 2; clarify.
  { inv SAFESRC. inv MATCH. inv H2; inv H4. inv STEPTGT. }
  unfold is_external in *. des_ifs.
  (* builtin *)
  - i. inv MATCH; clarify; EliminatedInstr.
    TransfInstr. inv STEPTGT; clarify. inv SAFESRC; clarify.
    exploit eval_builtin_args_lessdef; try eapply RLD; eauto. i. des.
    exploit eval_builtin_args_preserved. eapply SEQUIV. apply H8. i.
    exploit eval_builtin_args_determ. eapply H. eapply H1. i. subst.
    exploit external_call_mem_extends_backward; try eapply H9; eauto. i; des.
    + exploit external_call_symbols_preserved. apply SEQUIV. eapply CALLSRC. i.
      exploit exec_Ibuiltin; try eapply H2; eauto. i.
      left. esplits; eauto.
      econstructor; eauto. apply set_res_lessdef; auto.
    + exploit external_call_symbols_preserved. apply senv_preserved. eapply H12. i.
      exploit UBSRC; eauto. contradiction.
    + exploit external_call_symbols_preserved. apply SEQUIV. eapply CALLSRC. i.
      right. esplits; eauto. eapply star_one. econs; eauto.
  (* external *)
  - i. inv MATCH; clarify; EliminatedInstr.
    inv STEPTGT; clarify. inv SAFESRC; clarify.
    exploit external_call_symbols_preserved. apply SEQUIV. eauto. i.
    exploit external_call_mem_extends_backward; eauto. i; des; cycle 1; clarify.
    + exploit UBSRC; eauto. contradiction.
    + right. esplits; eauto. eapply star_one. econs; eauto.
    + left. esplits; eauto. econs; eauto. constructor; eauto.
Qed.

Lemma match_states_xsim st_src0 st_tgt0 gmtgt
    (MATCH: match_states st_src0 st_tgt0) :
  xsim (RTL.semantics prog) (RTL.semantics tprog) gmtgt lt (measure st_src0)%nat st_src0 st_tgt0.
Proof.
  generalize dependent st_src0. generalize dependent st_tgt0.
  pcofix CIH. i. pfold.
  destruct (classic (is_external ge st_src0)); cycle 1.
  (* not external *)
  - left. econs. econs.
    + i. exploit transf_step_correct; eauto. i. des.
      * esplits; eauto;[eapply tr_rel_refl; eapply ev_rel_refl|].
        left. split; [eapply plus_one; eauto|]. eapply semantics_receptive_at; auto.
      * esplits;[eapply tr_rel_refl; eapply ev_rel_refl| |].
        { right. esplits; eauto. }
        { right. eapply CIH; eauto. }
    + ii. eapply final_state_determ; eauto. inv FINALSRC. inv MATCH. inv H3; inv H5. econs.
  (* external *)
  - right. econs. i. econs.
    + i. exploit match_states_bsim; eauto. i. des.
      * left. esplits; eauto; [eapply tr_rel_refl; eapply ev_rel_refl|].
        left. eapply plus_one. eauto.
      * right. esplits; eauto. subst. eapply tr_rel_refl. eapply ev_rel_refl.
    + i. unfold is_external in *. des_ifs; inv FINALTGT; inv MATCH; EliminatedInstr; ss.
    (* progress *)
    + i. specialize (SAFESRC _ (star_refl _ _ _)). des; cycle 2; clarify; [inv SAFESRC; ss|].
      right. inv MATCH; EliminatedInstr; ss; des_ifs; inv SAFESRC; unfold ge in *; clarify.
      * TransfInstr.
        exploit eval_builtin_args_lessdef; try eapply RLD; eauto. i. des.
        exploit eval_builtin_args_preserved. eapply senv_preserved. apply H0. i.
        exploit external_call_symbols_preserved. apply senv_preserved. eauto. i.
        exploit external_call_mem_extends_backward_progress; eauto. i. des.
        esplits. eapply exec_Ibuiltin; eauto.
      * exploit external_call_symbols_preserved. apply senv_preserved. eauto. i.
        exploit external_call_mem_extends_backward_progress; eauto. ss. i. des.
        exploit exec_function_external; eauto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  exploit funct_ptr_translated; eauto. intro FIND.
  exists (Callstate nil (transf_fundef f) nil m0); split.
  econstructor; eauto. apply (Genv.init_mem_transf TRANSL). auto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  symmetry; eapply match_program_main; eauto.
  rewrite <- H3. apply sig_preserved.
  constructor. constructor. constructor. apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H5. inv H3. constructor.
Qed.

Lemma non_static_equiv l:
  Genv.non_static_glob (Genv.globalenv prog) l = Genv.non_static_glob (Genv.globalenv tprog) l.
Proof.
  Local Transparent ge tge.
  induction l; ss.
  specialize senv_preserved. ss. i. inv H. inv H1.
  unfold ge, tge, fundef in *.
  specialize (H a).
  unfold Senv.public_symbol in H. ss. erewrite H.
  specialize (H0 a). rewrite <- H0. erewrite IHl; eauto.
Qed.

Lemma transf_initial_capture S1 S2 S2'
    (INITSRC: initial_state prog S1)
    (INITTGT: initial_state tprog S2)
    (MATCH: match_states S1 S2)
    (CAPTGT: glob_capture tprog S2 S2'):
  exists S1', glob_capture prog S1 S1'
  /\ match_states S1' S2'
  /\ gm_improves (concrete_snapshot ge S1') (concrete_snapshot tge S2').
Proof.
  specialize senv_preserved. intros SENVEQ.
  inv CAPTGT. ss. rename m' into m2'.
  rewrite Genv.globalenv_public in CAPTURE. erewrite <- same_public in CAPTURE; eauto.
  inv MATCH. inv H5. (* dup INITSRC. inv INITSRC0. inv H3. *)
  exploit non_static_equiv. instantiate (1:=prog_public prog). intros EQUIV.
  assert (exists m1', Genv.capture_init_mem m0 (Genv.non_static_glob (Genv.globalenv prog) (prog_public prog)) m1' /\
                     Mem.extends m1' m2').
  { clear INITSRC INITTGT. rewrite <- EQUIV in CAPTURE. clear EQUIV. inv CAPTURE.
    remember (Genv.non_static_glob (Genv.globalenv prog) (prog_public prog)) as l. clear Heql.
    clear SENVEQ. move l before f0. revert_until f0.
    induction l; ss; i.
    { inv CAP. esplits; eauto. econs. econs. }
    inv CAP. exploit Mem.capture_extends_backward; eauto. i. des.
    exploit IHl; eauto. i. des. inv H. esplits; eauto. econs. econs; eauto. }
  des. inv INITSRC. esplits; eauto.
  - econs. eauto. rewrite Genv.globalenv_public. eauto.
  - econs; eauto.
  - ii. unfold concrete_snapshot in *. inv SENVEQ. des. erewrite H4, H2. des_ifs; ss.
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
      inv H10. inv H11. exploit transf_initial_capture; eauto. i. des.
      esplits; eauto. apply match_states_xsim; auto.
  - i. apply senv_preserved.
Qed.

End PRESERVATION.

