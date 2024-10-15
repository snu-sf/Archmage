(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                  Xavier Leroy, INRIA Paris                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for x86-64 generation: main proof. *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import sflib CoqlibC Simulation PointerOp MachD AsmD Classical.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm.
Require Import Asmgen Asmgenproof0 Asmgenproof1.
From Paco Require Import paco.

Definition match_prog (p: Mach.program) (tp: Asm.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Section PRESERVATION.

Variable prog: Mach.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Let sem := Mach.semantics return_address_offset prog.
Let tsem := Asm.semantics tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).

Lemma functions_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSF).

Lemma functions_transl:
  forall fb f tf,
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transf_function f = OK tf ->
  Genv.find_funct_ptr tge fb = Some (Internal tf).
Proof.
  intros. exploit functions_translated; eauto. intros [tf' [A B]].
  monadInv B. rewrite H0 in EQ; inv EQ; auto.
Qed.

(** * Properties of control flow *)

Lemma transf_function_no_overflow:
  forall f tf,
  transf_function f = OK tf -> list_length_z (fn_code tf) <= Ptrofs.max_unsigned.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x))); monadInv EQ0.
  lia.
Qed.

Lemma exec_straight_exec:
  forall fb f c ep tf tc c' rs m rs' m',
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  exec_straight tprog tf tc rs m c' rs' m' ->
  DPlus tsem (State rs m) E0 (State rs' m').
Proof.
  intros. inv H.
  eapply exec_straight_steps_1; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
Qed.

Lemma exec_straight_at:
  forall fb f c ep tf tc c' ep' tc' rs m rs' m',
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  transl_code f c' ep' = OK tc' ->
  exec_straight tprog tf tc rs m tc' rs' m' ->
  transl_code_at_pc ge (rs' PC) fb f c' ep' tf tc'.
Proof.
  intros. inv H.
  exploit exec_straight_steps_2; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
  intros [ofs' [PC' CT']].
  rewrite PC'. constructor; auto.
Qed.

(** The following lemmas show that the translation from Mach to Asm
  preserves labels, in the sense that the following diagram commutes:
<<
                          translation
        Mach code ------------------------ Asm instr sequence
            |                                          |
            | Mach.find_label lbl       find_label lbl |
            |                                          |
            v                                          v
        Mach code tail ------------------- Asm instr seq tail
                          translation
>>
  The proof demands many boring lemmas showing that Asm constructor
  functions do not introduce new labels.

  In passing, we also prove a "is tail" property of the generated Asm code.
*)

Section TRANSL_LABEL.

Remark mk_mov_label:
  forall rd rs k c, mk_mov rd rs k = OK c -> tail_nolabel k c.
Proof.
  unfold mk_mov; intros.
  destruct rd; try discriminate; destruct rs; TailNoLabel.
Qed.
Hint Resolve mk_mov_label: labels.

Remark mk_shrximm_label:
  forall n k c, mk_shrximm n k = OK c -> tail_nolabel k c.
Proof.
  intros. monadInv H; TailNoLabel.
Qed.
Hint Resolve mk_shrximm_label: labels.

Remark mk_shrxlimm_label:
  forall n k c, mk_shrxlimm n k = OK c -> tail_nolabel k c.
Proof.
  intros. monadInv H. destruct (Int.eq n Int.zero); TailNoLabel.
Qed.
Hint Resolve mk_shrxlimm_label: labels.

Remark mk_intconv_label:
  forall f r1 r2 k c, mk_intconv f r1 r2 k = OK c ->
  (forall r r', nolabel (f r r')) ->
  tail_nolabel k c.
Proof.
  unfold mk_intconv; intros. TailNoLabel.
Qed.
Hint Resolve mk_intconv_label: labels.

Remark mk_storebyte_label:
  forall addr r k c, mk_storebyte addr r k = OK c -> tail_nolabel k c.
Proof.
  unfold mk_storebyte; intros. TailNoLabel.
Qed.
Hint Resolve mk_storebyte_label: labels.

Remark loadind_label:
  forall base ofs ty dst k c,
  loadind base ofs ty dst k = OK c ->
  tail_nolabel k c.
Proof.
  unfold loadind; intros. destruct ty; try discriminate; destruct (preg_of dst); TailNoLabel.
Qed.

Remark storeind_label:
  forall base ofs ty src k c,
  storeind src base ofs ty k = OK c ->
  tail_nolabel k c.
Proof.
  unfold storeind; intros. destruct ty; try discriminate; destruct (preg_of src); TailNoLabel.
Qed.

Remark mk_setcc_base_label:
  forall xc rd k,
  tail_nolabel k (mk_setcc_base xc rd k).
Proof.
  intros. destruct xc; simpl; destruct (ireg_eq rd RAX); TailNoLabel.
Qed.

Remark mk_setcc_label:
  forall xc rd k,
  tail_nolabel k (mk_setcc xc rd k).
Proof.
  intros. unfold mk_setcc. destruct (Archi.ptr64 || low_ireg rd).
  apply mk_setcc_base_label.
  eapply tail_nolabel_trans. apply mk_setcc_base_label. TailNoLabel.
Qed.

Remark mk_jcc_label:
  forall xc lbl' k,
  tail_nolabel k (mk_jcc xc lbl' k).
Proof.
  intros. destruct xc; simpl; TailNoLabel.
Qed.

Remark mk_sel_label:
  forall xc rd r2 k c,
  mk_sel xc rd r2 k = OK c ->
  tail_nolabel k c.
Proof.
  unfold mk_sel; intros; destruct xc; inv H; TailNoLabel.
Qed.

Remark transl_cond_label:
  forall cond args k c,
  transl_cond cond args k = OK c ->
  tail_nolabel k c.
Proof.
  unfold transl_cond; intros.
  destruct cond; TailNoLabel.
  destruct (Int.eq_dec n Int.zero); TailNoLabel.
  destruct (Int64.eq_dec n Int64.zero); TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
Qed.

Remark transl_op_label:
  forall op args r k c,
  transl_op op args r k = OK c ->
  tail_nolabel k c.
Proof.
  unfold transl_op; intros. destruct op; TailNoLabel.
  destruct (Int.eq_dec n Int.zero); TailNoLabel.
  destruct (Int64.eq_dec n Int64.zero); TailNoLabel.
  destruct (Float.eq_dec n Float.zero); TailNoLabel.
  destruct (Float32.eq_dec n Float32.zero); TailNoLabel.
  destruct (normalize_addrmode_64 x) as [am' [delta|]]; TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto. eapply mk_setcc_label.
  unfold transl_sel in EQ2. destruct (ireg_eq x x0); monadInv EQ2.
  TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto. eapply mk_sel_label; eauto.
Qed.

Remark transl_load_label:
  forall chunk addr args dest k c,
  transl_load chunk addr args dest k = OK c ->
  tail_nolabel k c.
Proof.
  intros. monadInv H. destruct chunk; TailNoLabel.
Qed.

Remark transl_store_label:
  forall chunk addr args src k c,
  transl_store chunk addr args src k = OK c ->
  tail_nolabel k c.
Proof.
  intros. monadInv H. destruct chunk; TailNoLabel.
Qed.

Lemma transl_instr_label:
  forall f i ep k c,
  transl_instr f i ep k = OK c ->
  match i with Mlabel lbl => c = Plabel lbl :: k | _ => tail_nolabel k c end.
Proof.
Opaque loadind.
  unfold transl_instr; intros; destruct i; TailNoLabel.
  eapply loadind_label; eauto.
  eapply storeind_label; eauto.
  eapply loadind_label; eauto.
  eapply tail_nolabel_trans; eapply loadind_label; eauto.
  eapply transl_op_label; eauto.
  eapply transl_load_label; eauto.
  eapply transl_store_label; eauto.
  destruct s0; TailNoLabel.
  destruct s0; TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto. eapply mk_jcc_label.
Qed.

Lemma transl_instr_label':
  forall lbl f i ep k c,
  transl_instr f i ep k = OK c ->
  find_label lbl c = if Mach.is_label lbl i then Some k else find_label lbl k.
Proof.
  intros. exploit transl_instr_label; eauto.
  destruct i; try (intros [A B]; apply B).
  intros. subst c. simpl. auto.
Qed.

Lemma transl_code_label:
  forall lbl f c ep tc,
  transl_code f c ep = OK tc ->
  match Mach.find_label lbl c with
  | None => find_label lbl tc = None
  | Some c' => exists tc', find_label lbl tc = Some tc' /\ transl_code f c' false = OK tc'
  end.
Proof.
  induction c; simpl; intros.
  inv H. auto.
  monadInv H. rewrite (transl_instr_label' lbl _ _ _ _ _ EQ0).
  generalize (Mach.is_label_correct lbl a).
  destruct (Mach.is_label lbl a); intros.
  subst a. simpl in EQ. exists x; auto.
  eapply IHc; eauto.
Qed.

Lemma transl_find_label:
  forall lbl f tf,
  transf_function f = OK tf ->
  match Mach.find_label lbl f.(Mach.fn_code) with
  | None => find_label lbl tf.(fn_code) = None
  | Some c => exists tc, find_label lbl tf.(fn_code) = Some tc /\ transl_code f c false = OK tc
  end.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x))); inv EQ0.
  monadInv EQ. simpl. eapply transl_code_label; eauto. rewrite transl_code'_transl_code in EQ0; eauto.
Qed.

End TRANSL_LABEL.

(** A valid branch in a piece of Mach code translates to a valid ``go to''
  transition in the generated PPC code. *)

Lemma find_label_goto_label:
  forall f tf lbl rs m c' b ofs,
  Genv.find_funct_ptr ge b = Some (Internal f) ->
  transf_function f = OK tf ->
  rs PC = Vptr b ofs ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  exists tc', exists rs',
    goto_label tf lbl rs m = Next rs' m
  /\ transl_code_at_pc ge (rs' PC) b f c' false tf tc'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros. exploit (transl_find_label lbl f tf); eauto. rewrite H2.
  intros [tc [A B]].
  exploit label_pos_code_tail; eauto. instantiate (1 := 0).
  intros [pos' [P [Q R]]].
  exists tc; exists (rs#PC <- (Vptr b (Ptrofs.repr pos'))).
  split. unfold goto_label. rewrite P. rewrite H1. auto.
  split. rewrite Pregmap.gss. constructor; auto.
  rewrite Ptrofs.unsigned_repr. replace (pos' - 0) with pos' in Q.
  auto. lia.
  generalize (transf_function_no_overflow _ _ H0). lia.
  intros. apply Pregmap.gso; auto.
Qed.

(** Existence of return addresses *)

Lemma return_address_exists:
  forall f sg ros c v (FUNCT: Genv.find_funct (Genv.globalenv prog) v = Some (Internal f)), is_tail (Mcall sg ros :: c) f.(Mach.fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros.
  assert(TF: exists tf, transf_function f = OK tf).
  { inv TRANSF.
    exploit Genv.find_funct_inversion; eauto. i; des.
    eapply list_forall2_in_left in H0; eauto.
    des. inv H4. ss. clarify. inv H6. ss. monadInv H8. esplits; eauto.
  } des.
  intros. eapply Asmgenproof0.return_address_exists; eauto.
- intros. exploit transl_instr_label; eauto.
  destruct i; try (intros [A B]; apply A). intros. subst c0. repeat constructor.
- intros. monadInv TF.
  destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x))); inv EQ0.
  monadInv EQ. rewrite transl_code'_transl_code in EQ0.
  exists x; exists true; split; auto. unfold fn_code. repeat constructor.
- eapply transf_function_no_overflow; eauto.
Qed.

(** * Proof of semantic preservation *)

(** Semantic preservation is proved using simulation diagrams
  of the following form.
<<
           st1 --------------- st2
            |                   |
           t|                  *|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The invariant is the [match_states] predicate below, which includes:
- The PPC code pointed by the PC register is the translation of
  the current Mach code sequence.
- Mach register values and PPC register values agree.
*)

Inductive match_states: Mach.state -> Asm.state -> Prop :=
  | match_states_intro:
      forall s fb sp c ep ms m m' rs f tf tc
        (STACKS: match_stack ge s)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (MEXT: Mem.extends m m')
        (AT: transl_code_at_pc ge (rs PC) fb f c ep tf tc)
        (AG: agree ms sp rs)
        (AXP: ep = true -> rs#RAX = parent_sp s),
      match_states (Mach.State s fb sp c ms m)
                   (Asm.State rs m')
  | match_states_call:
      forall s fb ms m m' rs
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = Vptr fb Ptrofs.zero)
        (ATLR: rs RA = parent_ra s),
      match_states (Mach.Callstate s fb ms m)
                   (Asm.State rs m')
  | match_states_return:
      forall s ms m m' rs
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = parent_ra s),
      match_states (Mach.Returnstate s ms m)
                   (Asm.State rs m').

Lemma exec_straight_steps:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2,
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists rs2,
       exec_straight tprog tf c rs1 m1' k rs2 m2'
    /\ agree ms2 sp rs2
    /\ (it1_is_parent ep i = true -> rs2#RAX = parent_sp s)) ->
  exists st',
  DPlus tsem (State rs1 m1') E0 st' /\
  match_states (Mach.State s fb sp c ms2 m2) st'.
Proof.
  intros. inversion H2. subst. monadInv H7.
  exploit H3; eauto. intros [rs2 [A [B C]]].
  exists (State rs2 m2'); split.
  eapply exec_straight_exec; eauto.
  econstructor; eauto. eapply exec_straight_at; eauto.
Qed.

Lemma exec_straight_steps_goto:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c',
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  it1_is_parent ep i = false ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists jmp, exists k', exists rs2,
       exec_straight tprog tf c rs1 m1' (jmp :: k') rs2 m2'
    /\ agree ms2 sp rs2
    /\ exec_instr tge tf jmp rs2 m2' = goto_label tf lbl rs2 m2') ->
  exists st',
  DPlus tsem (State rs1 m1') E0 st' /\
  match_states (Mach.State s fb sp c' ms2 m2) st'.
Proof.
  intros. inversion H3. subst. monadInv H9.
  exploit H5; eauto. intros [jmp [k' [rs2 [A [B C]]]]].
  generalize (functions_transl _ _ _ H7 H8); intro FN.
  generalize (transf_function_no_overflow _ _ H8); intro NOOV.
  exploit exec_straight_steps_2; eauto.
  intros [ofs' [PC2 CT2]].
  exploit find_label_goto_label; eauto.
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  exists (State rs3 m2'); split.
  eapply plus_right'.
  eapply exec_straight_steps_1; eauto.
  DStep_tac. rewrite PC2. fold tge. rewrite FN. erewrite find_instr_tail; eauto.
  destruct jmp; ss. rewrite <- C in GOTO; inv GOTO.
  econstructor; eauto.
  eapply find_instr_tail. eauto.
  ss. fold tge.
  rewrite C. eexact GOTO.
  traceEq.
  econstructor; eauto.
  apply agree_exten with rs2; auto with asmgen.
  congruence.
Qed.

(** We need to show that, in the simulation diagram, we cannot
  take infinitely many Mach transitions that correspond to zero
  transitions on the PPC side.  Actually, all Mach transitions
  correspond to at least one Asm transition, except the
  transition from [Mach.Returnstate] to [Mach.State].
  So, the following integer measure will suffice to rule out
  the unwanted behaviour. *)

Definition measure (s: Mach.state) : nat :=
  match s with
  | Mach.State _ _ _ _ _ _ => 0%nat
  | Mach.Callstate _ _ _ _ => 0%nat
  | Mach.Returnstate _ _ _ => 1%nat
  end.

(** This is the simulation diagram.  We prove it by case analysis on the Mach transition. *)

Theorem step_simulation:
  forall S1 t S2, IStep sem S1 t S2 ->
  forall S1' (TCHAR: state_char tprog S1') (MS: match_states S1 S1'),
  (exists S2', DPlus tsem S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
destruct 1. generalize dependent S2. rename H into INT.  
  induction 1; intros; inv MS.

- (* Mlabel *)
  left; eapply exec_straight_steps; eauto; intros.
  monadInv TR. econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split. apply agree_nextinstr; auto. simpl; congruence.

- (* Mgetstack *)
  unfold load_stack in H.
  exploit Mem.loadv_extends; eauto. intros [v' [A B]].
  rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto. intros. simpl in TR.
  exploit loadind_correct; eauto. intros [rs' [P [Q R]]].
  exists rs'; split. eauto.
  split. eapply agree_set_mreg; eauto. congruence.
  simpl; congruence.

- (* Msetstack *)
  unfold store_stack in H.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [A B]].
  left; eapply exec_straight_steps; eauto.
  rewrite (sp_val _ _ _ AG) in A. intros. simpl in TR.
  exploit storeind_correct; eauto. intros [rs' [P Q]].
  exists rs'; split. eauto.
  split. eapply agree_undef_regs; eauto.
  simpl; intros. rewrite Q; auto with asmgen.
Local Transparent destroyed_by_setstack.
  destruct ty; simpl; intuition congruence.

- (* Mgetparam *)
  ss. fold ge in H.  
  assert (f0 = f) by congruence; subst f0.
  unfold load_stack in *.
  exploit Mem.loadv_extends. eauto. eexact H0. auto.
  intros [parent' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit lessdef_parent_sp; eauto. clear B; intros B; subst parent'.
  exploit Mem.loadv_extends. eauto. eexact H1. auto.
  intros [v' [C D]].
Opaque loadind.
  left; eapply exec_straight_steps; eauto; intros.
  assert (DIFF: negb (mreg_eq dst AX) = true -> IR RAX <> preg_of dst).
    intros. change (IR RAX) with (preg_of AX). red; intros.
    unfold proj_sumbool in H1. destruct (mreg_eq dst AX); try discriminate.
    elim n. eapply preg_of_injective; eauto.
  destruct ep; simpl in TR.
(* RAX contains parent *)
  exploit loadind_correct. eexact TR.
  instantiate (2 := rs0). rewrite AXP; eauto.
  intros [rs1 [P [Q R]]].
  exists rs1; split. eauto.
  split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto.
  simpl; intros. rewrite R; auto.
(* RAX does not contain parent *)
  monadInv TR.
  exploit loadind_correct. eexact EQ0. eauto. intros [rs1 [P [Q R]]]. simpl in Q.
  exploit loadind_correct. eexact EQ. instantiate (2 := rs1). rewrite Q. eauto.
  intros [rs2 [S [T U]]].
  exists rs2; split. eapply exec_straight_trans; eauto.
  split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto.
  simpl; intros. rewrite U; auto.

- (* Mop *)
  assert (eval_operation_wrapper tge sp op rs##args m = Some v).
    rewrite <- H. apply eval_operation_wrapper_preserved. exact symbols_preserved.
  exploit eval_operation_wrapper_lessdef. eapply preg_vals; eauto. eauto. eexact H0.
  intros [v' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  exploit transl_op_correct; eauto. intros [rs2 [P [Q R]]].
  assert (S: Val.lessdef v (rs2 (preg_of res))) by (eapply Val.lessdef_trans; eauto).
  exists rs2; split. eauto.
  split. eapply agree_set_undef_mreg; eauto.
  simpl; congruence.

- (* Mload *)
  assert (eval_addressing tge sp addr rs##args = Some a).
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  exploit transl_load_correct; eauto. intros [rs2 [P [Q R]]].
  exists rs2; split. eauto.
  split. eapply agree_set_undef_mreg; eauto. congruence.
  simpl; congruence.

- (* Mstore *)
  assert (eval_addressing tge sp addr rs##args = Some a).
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [C D]].
  left; eapply exec_straight_steps; eauto.
  intros. simpl in TR.
  exploit transl_store_correct; eauto. intros [rs2 [P Q]].
  exists rs2; split. eauto.
  split. eapply agree_undef_regs; eauto.
  simpl; congruence.

- (* Mcall *)
  ss. fold ge in H0.
  assert (f0 = f) by congruence.  subst f0.
  inv AT.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct ros as [rf|fid]; simpl in H; monadInv H5.
+ (* Indirect call *)
  assert (Mem.to_ptr (rs rf) m = Some (Vptr f' Ptrofs.zero)).
  { destruct (rs rf); ss; try discriminate; des_ifs_safe.
    2:{ eapply Ptrofs.same_if_eq in Heq; eauto. i. subst; eauto. }
    ss. des_ifs. eapply Ptrofs.same_if_eq in Heq2. rewrite Heq2. eauto. }
  assert (find_function_ptr (Genv.globalenv prog) (inl (Vptr f' Ptrofs.zero)) rs = Some f') by ss.
  clear H. rename H7 into H.
  assert (Mem.to_ptr (rs0 x0) m' = Some (Vptr f' Ptrofs.zero)).
    exploit ireg_val; eauto. i. eapply Mem.to_ptr_extends; eauto.
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  left; econstructor; split.
  apply plus_one. DStep_tac. exploit functions_transl; eauto. intros.
  rewrite <- H2. fold tge. rewrite H8. erewrite find_instr_tail; eauto. ss.
  eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. eauto.
  econstructor; eauto.
  econstructor; eauto.
  eapply agree_sp_def; eauto.
  simpl. eapply agree_exten; eauto. intros. Simplifs.
  Simplifs. unfold to_ptr. rewrite H7. eauto. rewrite <- H2. auto.
+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  left; econstructor; split.
  apply plus_one. DStep_tac. exploit functions_transl; eauto. intros.
  rewrite <- H2. fold tge. rewrite H5. erewrite find_instr_tail; eauto. ss.
  eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. unfold Genv.symbol_address. rewrite symbols_preserved. unfold ge. rewrite H. eauto.
  econstructor; eauto.
  econstructor; eauto.
  eapply agree_sp_def; eauto.
  simpl. eapply agree_exten; eauto. intros. Simplifs.
  Simplifs. rewrite <- H2. auto.

- (* Mtailcall *)
  simpl in *. fold ge in H0.
  assert (f0 = f) by congruence.  subst f0.
  inv AT.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  rewrite (sp_val _ _ _ AG) in *. unfold load_stack in *.
  exploit Mem.loadv_extends. eauto. eexact H1. auto. simpl. intros [parent' [A B]].
  exploit Mem.loadv_extends. eauto. eexact H2. auto. simpl. intros [ra' [C D]].
  exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.
  exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.
  exploit Mem.free_parallel_extends; eauto. intros [m2' [E F]].
  exploit functions_transl; eauto. intros TFUN. unfold tge in TFUN.
  assert (NEXT: nextinstr (rs0 # RSP <- (parent_sp s)) # RA <- (parent_ra s) PC = Vptr fb (Ptrofs.add ofs Ptrofs.one)).
  { transitivity (Val.offset_ptr rs0#PC Ptrofs.one). auto. rewrite <- H4. simpl. eauto. }  
  destruct ros as [rf|fid]; simpl in H; monadInv H7.
+ (* Indirect call *)
  assert (Mem.to_ptr (rs rf) m = Some (Vptr f' Ptrofs.zero)).
  { destruct (rs rf); ss; try discriminate; des_ifs_safe.
    2:{ eapply Ptrofs.same_if_eq in Heq; eauto. i. subst; eauto. }
    ss. des_ifs. eapply Ptrofs.same_if_eq in Heq2. rewrite Heq2. eauto. }
  assert (Mem.to_ptr (rs0 x0) m'0 = Some (Vptr f' Ptrofs.zero)).
  { exploit ireg_val; eauto. i. eapply Mem.to_ptr_extends; eauto. }
  generalize (code_tail_next_int _ _ _ _ NOOV H8). intro CT1.
  left; econstructor; split.
  eapply plus_left. DStep_tac. exploit functions_transl; eauto. intros.
  rewrite <- H4. fold tge. rewrite H10. erewrite find_instr_tail; eauto. ss.
  eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. replace (chunk_of_type Tptr) with Mptr in * by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
  rewrite C. rewrite A. rewrite <- (sp_val _ _ _ AG). rewrite E. eauto.
  apply star_one. DStep_tac. rewrite NEXT, TFUN. erewrite find_instr_tail; eauto. ss. eapply exec_step_internal.
  transitivity (Val.offset_ptr rs0#PC Ptrofs.one). auto. rewrite <- H4. simpl. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. eauto. traceEq.
  econstructor; eauto.
  apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
  eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
  Simplifs.
  assert ((nextinstr (rs0 # RSP <- (parent_sp s)) # RA <- (parent_ra s) x0) = rs0 x0).
  { Simplifs. rewrite Pregmap.gso; auto.
    generalize (preg_of_not_SP rf). rewrite (ireg_of_eq _ _ EQ1). congruence. }
  rewrite H10.
  assert (Mem.to_ptr (rs0 x0) m2' = Some (Vptr f' Ptrofs.zero)).
  { destruct (rs0 x0); try by ss. simpl in H9.
    destruct Archi.ptr64 eqn:SF; try by ss.
    destruct (Int64.eq i Int64.zero) eqn:NULL; try by ss.
    destruct (Mem.denormalize (Int64.unsigned i) m'0) eqn:DENO; try by ss.
    destruct p. simpl. rewrite SF, NULL.
    assert (z = 0).
    { eapply Mem.denormalize_info in DENO. des.
      assert (ZERO: Ptrofs.repr z = Ptrofs.zero).
      { eapply Ptrofs.same_if_eq. unfold Ptrofs.eq. des_ifs. }
      rewrite <- Ptrofs.unsigned_repr; try lia.
      rewrite <- Ptrofs.unsigned_repr at 1; try lia. rewrite ZERO. eauto. }
    subst. inv H9.
    assert (P2I: Mem.ptr2int f' 0 m2' = Some (Int64.unsigned i)).
    { eapply Mem.denormalize_info in DENO. des.
      unfold Mem.ptr2int. erewrite <- Mem.concrete_free; eauto. rewrite CONC. f_equal. lia. }
    exploit Mem.denormalize_perm; eauto. i. des. eapply Mem.perm_implies in H9; [|eapply perm_any_N].
    destruct (classic (fn_stacksize f > 0)); cycle 1.
    { exploit Mem.perm_free_1; try eapply E; eauto. i.
      exploit Mem.ptr2int_to_denormalize_max; eauto. 
      { unfold Ptrofs.max_unsigned, Ptrofs.modulus, two_power_nat. lia. }
      i. rewrite H13. eauto. }
    destruct (peq f' stk).
    { subst. hexploit Mem.free_range_perm; eauto. intros FPERM.
      specialize (FPERM 0). exploit FPERM; try lia. i.
      r in TCHAR. ss. r in TCHAR. exploit functions_translated; try eapply FUNCPTR; eauto. i. des.
      eapply TCHAR in H13. i. des. eapply H15 in H12. des; clarify. }
    exploit Mem.perm_free_1; try eapply E; eauto. i.
    exploit Mem.ptr2int_to_denormalize_max; eauto.
    { unfold Ptrofs.max_unsigned, Ptrofs.modulus, two_power_nat. lia. }
    i. rewrite H13. eauto. }
  unfold to_ptr. rewrite H11. eauto.
+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H8). intro CT1.
  left; econstructor; split.
  eapply plus_left. DStep_tac. rewrite <- H4. rewrite TFUN. erewrite find_instr_tail; eauto. ss. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. replace (chunk_of_type Tptr) with Mptr in * by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
  rewrite C. rewrite A. rewrite <- (sp_val _ _ _ AG). rewrite E. eauto.
  apply star_one. DStep_tac. rewrite NEXT, TFUN. erewrite find_instr_tail; eauto. ss. eapply exec_step_internal.
  transitivity (Val.offset_ptr rs0#PC Ptrofs.one). auto. rewrite <- H4. simpl. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. eauto. traceEq.
  econstructor; eauto.
  apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
  eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
  rewrite Pregmap.gss. unfold Genv.symbol_address. rewrite symbols_preserved. unfold ge. rewrite H. auto.

- (* Mbuiltin *)
  unfold is_internal in INT. simpl in INT.
  inv AT. monadInv H4.
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H3); intro NOOV.
  exploit builtin_args_match; eauto. intros [vargs' [P Q]].
  exploit external_call_mem_extends; eauto.
  intros [vres' [m2' [A [B [C D]]]]].
  left. econstructor; split. apply plus_one.
  DStep_tac. rewrite <- H1. fold tge. rewrite FN. erewrite find_instr_tail; eauto. ss.  
  eapply exec_step_builtin. eauto. eauto.
  eapply find_instr_tail; eauto.
  erewrite <- sp_val by eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  eauto.
  econstructor; eauto.
  instantiate (2 := tf); instantiate (1 := x).
  unfold nextinstr_nf, nextinstr. rewrite Pregmap.gss.
  rewrite undef_regs_other. rewrite set_res_other. rewrite undef_regs_other_2.
  rewrite <- H1. simpl. econstructor; eauto.
  eapply code_tail_next_int; eauto.
  rewrite preg_notin_charact. intros. auto with asmgen.
  auto with asmgen.
  simpl; intros. intuition congruence.
  apply agree_nextinstr_nf. eapply agree_set_res; auto.
  eapply agree_undef_regs; eauto. intros; apply undef_regs_other_2; auto.
  congruence.

- (* Mgoto *)
  simpl in *. fold ge in H.  
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H4.
  exploit find_label_goto_label; eauto. intros [tc' [rs' [GOTO [AT2 INV]]]].
  left; exists (State rs' m'); split.
  apply plus_one. DStep_tac. rewrite <- H1. exploit functions_transl; eauto; intros.
  unfold tge in H4. rewrite H4. erewrite find_instr_tail; eauto. ss. econstructor; eauto.
  eapply functions_transl; eauto.
  eapply find_instr_tail; eauto.
  simpl; eauto.
  econstructor; eauto.
  eapply agree_exten; eauto with asmgen.
  congruence.

- (* Mcond true *)
  simpl in *. fold ge in H0.  
  assert (f0 = f) by congruence. subst f0.
  exploit eval_condition_wrapper_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_steps_goto; eauto.
  intros. simpl in TR.
  destruct (transl_cond_correct tprog tf cond args _ _ rs0 m' TR)
  as [rs' [A [B C]]].
  rewrite EC in B. destruct B as [B _].
  destruct (testcond_for_condition cond); simpl in *.
(* simple jcc *)
  exists (Pjcc c1 lbl); exists k; exists rs'.
  split. eexact A.
  split. eapply agree_exten; eauto.
  simpl. rewrite B. auto.
(* jcc; jcc *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  destruct b1.
  (* first jcc jumps *)
  exists (Pjcc c1 lbl); exists (Pjcc c2 lbl :: k); exists rs'.
  split. eexact A.
  split. eapply agree_exten; eauto.
  simpl. rewrite TC1. auto.
  (* second jcc jumps *)
  exists (Pjcc c2 lbl); exists k; exists (nextinstr rs').
  split. eapply exec_straight_trans. eexact A.
  eapply exec_straight_one. simpl. rewrite TC1. auto. auto.
  split. eapply agree_exten; eauto.
  intros; Simplifs.
  simpl. rewrite eval_testcond_nextinstr. rewrite TC2.
  destruct b2; auto || discriminate.
(* jcc2 *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  destruct (andb_prop _ _ H3). subst.
  exists (Pjcc2 c1 c2 lbl); exists k; exists rs'.
  split. eexact A.
  split. eapply agree_exten; eauto.
  simpl. rewrite TC1; rewrite TC2; auto.

- (* Mcond false *)
  exploit eval_condition_wrapper_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_steps; eauto. intros. simpl in TR.
  destruct (transl_cond_correct tprog tf cond args _ _ rs0 m' TR)
  as [rs' [A [B C]]].
  rewrite EC in B. destruct B as [B _].
  destruct (testcond_for_condition cond); simpl in *.
(* simple jcc *)
  econstructor; split.
  eapply exec_straight_trans. eexact A.
  apply exec_straight_one. simpl. rewrite B. eauto. auto.
  split. apply agree_nextinstr. eapply agree_exten; eauto.
  simpl; congruence.
(* jcc ; jcc *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  destruct (orb_false_elim _ _ H1); subst.
  econstructor; split.
  eapply exec_straight_trans. eexact A.
  eapply exec_straight_two. simpl. rewrite TC1. eauto. auto.
  simpl. rewrite eval_testcond_nextinstr. rewrite TC2. eauto. auto. auto.
  split. apply agree_nextinstr. apply agree_nextinstr. eapply agree_exten; eauto.
  simpl; congruence.
(* jcc2 *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  exists (nextinstr rs'); split.
  eapply exec_straight_trans. eexact A.
  apply exec_straight_one. simpl.
  rewrite TC1; rewrite TC2.
  destruct b1. simpl in *. subst b2. auto. auto.
  auto.
  split. apply agree_nextinstr. eapply agree_exten; eauto.
  rewrite H1; congruence.

- (* Mjumptable *)
  simpl in *. fold ge in H1.  
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H6.
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H5); intro NOOV.
  set (rs1 := rs0 #RAX <- Vundef #RDX <- Vundef).
  exploit (find_label_goto_label f tf lbl rs1); eauto.
  intros [tc' [rs' [A [B C]]]].
  exploit ireg_val; eauto. rewrite H. intros LD; inv LD.
  left; econstructor; split.
  apply plus_one. DStep_tac. rewrite <- H3. fold tge. rewrite FN. erewrite find_instr_tail; eauto. ss. econstructor; eauto.
  eapply find_instr_tail; eauto.
  simpl. rewrite <- H9.  unfold Mach.label in H0; unfold label; rewrite H0. eexact A.
  econstructor; eauto.
Transparent destroyed_by_jumptable.
  apply agree_undef_regs with rs0; auto.
  simpl; intros. destruct H8. rewrite C by auto with asmgen. unfold rs1; Simplifs.
  congruence.

- (* Mreturn *)
  simpl in *. fold ge in H.  
  assert (f0 = f) by congruence. subst f0.
  inv AT.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  rewrite (sp_val _ _ _ AG) in *. unfold load_stack in *.
  replace (chunk_of_type Tptr) with Mptr in * by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
  exploit Mem.loadv_extends. eauto. eexact H0. auto. simpl. intros [parent' [A B]].
  exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.
  exploit Mem.loadv_extends. eauto. eexact H1. auto. simpl. intros [ra' [C D]].
  exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.
  exploit Mem.free_parallel_extends; eauto. intros [m2' [E F]].
  monadInv H6.
  exploit code_tail_next_int; eauto. intro CT1.
  assert (NEXT: nextinstr (rs0 # RSP <- (parent_sp s)) # RA <- (parent_ra s) PC = Vptr fb (Ptrofs.add ofs Ptrofs.one)).
  { transitivity (Val.offset_ptr rs0#PC Ptrofs.one). auto. rewrite <- H3. simpl. eauto. }
  exploit functions_transl; eauto; intros TFN. unfold tge in TFN.   
  left; econstructor; split.
  eapply plus_left. DStep_tac. rewrite <- H3. rewrite TFN. erewrite find_instr_tail; eauto. ss.
  eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. rewrite C. rewrite A. rewrite <- (sp_val _ _ _ AG). rewrite E. eauto.
  apply star_one. DStep_tac. rewrite NEXT, TFN. erewrite find_instr_tail; eauto. ss.
  eapply exec_step_internal.
  transitivity (Val.offset_ptr rs0#PC Ptrofs.one). auto. rewrite <- H3. simpl. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. eauto. traceEq.
  constructor; auto.
  apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
  eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.

- (* internal function *)
  exploit functions_translated; eauto. intros [tf [A B]]. monadInv B.
  generalize EQ; intros EQ'. monadInv EQ'.
  destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x0))); inv EQ1.
  monadInv EQ0. rewrite transl_code'_transl_code in EQ1.
  unfold store_stack in *.
  exploit Mem.alloc_extends. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros [m1' [C D]].
  exploit Mem.storev_extends. eexact D. eexact H1. eauto. eauto.
  intros [m2' [F G]].
  exploit Mem.storev_extends. eexact G. eexact H2. eauto. eauto.
  intros [m3' [P Q]].
  exploit functions_transl; eauto; intros TFN. unfold tge in TFN.  
  left; econstructor; split.
  apply plus_one. DStep_tac. rewrite ATPC, TFN. ss. econstructor; eauto.
  simpl. rewrite Ptrofs.unsigned_zero. simpl. eauto.
  simpl. rewrite C. simpl in F, P.
  replace (chunk_of_type Tptr) with Mptr in F, P by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
  rewrite (sp_val _ _ _ AG) in F. rewrite F.
  rewrite ATLR. rewrite P. eauto.
  econstructor; eauto.
  unfold nextinstr. rewrite Pregmap.gss. repeat rewrite Pregmap.gso; auto with asmgen.
  rewrite ATPC. simpl. constructor; eauto.
  unfold fn_code. eapply code_tail_next_int. simpl in g. lia.
  constructor.
  apply agree_nextinstr. eapply agree_change_sp; eauto.
Transparent destroyed_at_function_entry.
  apply agree_undef_regs with rs0; eauto.
  simpl; intros. apply Pregmap.gso; auto with asmgen. tauto.
  congruence.
  intros. Simplifs. eapply agree_sp; eauto.

- (* external function *)
  unfold is_internal in INT. simpl in INT, H. rewrite H in INT.  
  exploit functions_translated; eauto.
  intros [tf [A B]]. simpl in B. inv B.
  exploit extcall_arguments_match; eauto.
  intros [args' [C D]].
  exploit external_call_mem_extends; eauto.
  intros [res' [m2' [P [Q [R S]]]]].
  left; econstructor; split.
  apply plus_one. DStep_tac. fold tge. rewrite ATPC, A. auto. eapply exec_step_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.
  unfold loc_external_result. apply agree_set_other; auto. apply agree_set_pair; auto.
  apply agree_undef_caller_save_regs; auto. 

- (* return *)
  inv STACKS. simpl in *.
  right. split. lia. split. auto.
  econstructor; eauto. rewrite ATPC; eauto. congruence.  
Qed.

Lemma transf_initial_states:
  forall st1, Mach.initial_state prog st1 ->
  exists st2, Asm.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H. unfold ge0 in *.
  econstructor; split.
  econstructor.
  eapply (Genv.init_mem_transf_partial TRANSF); eauto.
  replace (Genv.symbol_address (Genv.globalenv tprog) (prog_main tprog) Ptrofs.zero)
     with (Vptr fb Ptrofs.zero).
  econstructor; eauto.
  constructor.
  apply Mem.extends_refl.
  split. reflexivity. simpl.
  unfold Vnullptr; destruct Archi.ptr64; congruence.
  intros. rewrite Regmap.gi. auto.
  unfold Genv.symbol_address.
  rewrite (match_program_main TRANSF).
  rewrite symbols_preserved.
  unfold ge; rewrite H1. auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> Mach.final_state st1 r -> Asm.final_state st2 r.
Proof.
  intros. inv H0. inv H. constructor. auto.
  assert (r0 = AX).
  { unfold loc_result in H1; destruct Archi.ptr64; compute in H1; congruence. }
  subst r0.
  generalize (preg_val _ _ _ AX AG). rewrite H2. intros LD; inv LD. auto.
Qed.

Lemma match_states_bsim
    s1 (EXT: Mach.is_external ge s1)
    s2 t s2' (STEPTGT: Step tsem s2 t s2')
    (MATCH: match_states s1 s2)
    (SAFESRC: safe sem s1) :
  (exists s1', Step sem s1 t s1' /\ match_states s1' s2')
\/ (~ trace_intact t /\ exists s1'' t', Star sem s1 t' s1'' /\ exists tl, t' = (trace_cut_pterm t) ** tl).
Proof.
  assert (SEQUIV: Senv.equiv tge ge) by (symmetry; apply senv_preserved).
  unfold safe in SAFESRC. specialize (SAFESRC _ (star_refl _ _ _)). des; cycle 2; clarify.
  { inv SAFESRC. inv MATCH. inv STEPTGT; clarify. }
  unfold is_external in *.
  inv MATCH; des_ifs.
  (* builtin *)
  - i. ss. destruct c; try inversion EXT. destruct i; try inversion EXT.
    inv AT. monadInv H2.
    inv STEPTGT; cycle 2.
    { rewrite <- H in H5. clarify. exploit functions_transl; try eapply H1. eauto. i.
      fold tge in H6. Eq. }
    { rewrite <- H in H5. clarify. exploit find_instr_tail; eauto. i.
      exploit functions_transl; try eapply H1. eauto. i.
      fold tge in H6. Eq. ss. }
    inv SAFESRC.
    exploit functions_transl; eauto. intro FN.
    generalize (transf_function_no_overflow _ _ H1); intro NOOV.
    exploit builtin_args_match; eauto. intros [vargs' [P Q]].
    rewrite <- H in H5. clarify.
    exploit find_instr_tail. eapply H3. i. fold tge in H6. Eq.
    determ_tac eval_builtin_args_preserved.
    fold ge in P. inversion AG. subst.
    exploit eval_builtin_args_determ. eapply P. eapply H2. i. subst.
    exploit external_call_symbols_preserved; try eapply H9. eapply SEQUIV. i.
    exploit external_call_mem_extends_backward; try eapply MEXT; eauto. i. des.
    + left. esplits; eauto.
      * econs; eauto.
      * econstructor; eauto.
        instantiate (2 := tf); instantiate (1 := x).
        unfold nextinstr_nf, nextinstr. rewrite Pregmap.gss.
        rewrite undef_regs_other. rewrite set_res_other. rewrite undef_regs_other_2.
        rewrite <- H. simpl. econstructor; eauto.
        eapply code_tail_next_int; eauto.
        rewrite preg_notin_charact. intros. auto with asmgen.
        auto with asmgen.
        simpl; intros. intuition congruence.
        apply agree_nextinstr_nf. eapply agree_set_res; auto.
        eapply agree_undef_regs; eauto. intros; apply undef_regs_other_2; auto.
        congruence.
    + exploit UBSRC; eauto. clarify.
    + right. esplits; eauto. eapply star_one. econs; eauto.
  (* external *)
  - ss. des_ifs.
    inv STEPTGT; ss; Eq; clarify.
    { exploit functions_translated; try eapply Heq. i. des. fold tge in H2. Eq. ss. }
    { exploit functions_translated; try eapply Heq. i. des. fold tge in H2. Eq. ss. }
    inv SAFESRC; clarify.
    { exploit functions_translated; try eapply H6. i. des. fold tge in H2. Eq. monadInv H0. }
    exploit functions_translated; eauto.
    intros [tf [A B]]. simpl in B. inv B.
    exploit extcall_arguments_match; eauto.
    intros [args' [C D]].
    fold ge in H6, H10. fold tge in H2. Eq.
    exploit external_call_mem_extends_backward; try eapply MEXT; eauto.
    exploit functions_translated. eapply Heq. i. des. inv H0.
    determ_tac Asm.extcall_arguments_determ. eauto. i. des.
    + left. esplits; eauto.
      * econs; eauto. eapply external_call_symbols_preserved; eauto.
      * econstructor; eauto.
        unfold loc_external_result. apply agree_set_other; auto. apply agree_set_pair; auto.
        apply agree_undef_caller_save_regs; auto.
    + exploit UBSRC; eauto.
      eapply external_call_symbols_preserved; eauto. eapply senv_preserved. clarify.
    + right. esplits; eauto. eapply star_one. econs; eauto. eapply external_call_symbols_preserved; eauto.
Qed.

Lemma match_states_xsim st_src0 st_tgt0 gmtgt
    (TCHAR: state_char tprog st_tgt0)
    (MATCH: match_states st_src0 st_tgt0) :
  xsim sem tsem gmtgt lt (measure st_src0) st_src0 st_tgt0.
Proof.
  generalize dependent st_src0. generalize dependent st_tgt0.
  pcofix CIH. i. pfold.
  destruct (classic (Mach.is_external ge st_src0)); cycle 1; rename H into EXT.
  (* internal *)
  - left. econs. econs.
    + i. exploit step_simulation; eauto. i. des.
      * esplits; eauto; [eapply tr_rel_refl; eapply ev_rel_refl| |].
        left. esplits; eauto. eapply MachD.semantics_receptive_at; auto.
        right. eapply CIH; eauto. eapply state_char_dplus; eauto.
      * esplits; eauto. eapply tr_rel_refl. eapply ev_rel_refl.
    + i. exploit transf_final_states; eauto. i. eapply final_state_determ; eauto.
  (* external *)
  - right. econs. i. econs.
    + i. exploit match_states_bsim; eauto. i. des.
      * left. esplits; eauto; [eapply tr_rel_refl; eapply ev_rel_refl| |].
        { left. eapply plus_one. eauto. }
        right. eapply CIH; eauto. eapply state_char_preservation; eauto.
      * right. esplits; eauto. subst. eapply tr_rel_refl. eapply ev_rel_refl.
    + i. inversion FINALTGT; inv MATCH; ss; des_ifs; clarify; [|Eq].
      { inv AT. rewrite H in H1. inv H1. }
    + i. specialize (SAFESRC _ (star_refl _ _ _)). des; cycle 2; clarify; [inv SAFESRC; ss|].
      right. inv MATCH; ss; des_ifs; inv SAFESRC; unfold ge in *; clarify.
      (* state *)
      * inv AT. monadInv H2.
        exploit functions_transl; eauto. intro FN.
        generalize (transf_function_no_overflow _ _ H1); intro NOOV.
        exploit builtin_args_match; eauto. intros [vargs' [P Q]].
        exploit external_call_mem_extends_backward_progress; eauto. i. des.
        exploit external_call_symbols_preserved. apply senv_preserved. eauto. i.
        eapply find_instr_tail in H3.
        inv AG. exploit eval_builtin_args_preserved; try eapply P. eapply senv_preserved. i.
        esplits. eapply exec_step_builtin; eauto. 
      (* exnteral call *)
      * exploit functions_translated; eauto.
        intros [tf [A B]]. simpl in B. inv B.
        exploit extcall_arguments_match; eauto.
        intros [args' [C D]].
        exploit external_call_symbols_preserved. apply senv_preserved. eauto. i.
        exploit external_call_mem_extends_backward_progress; eauto.
        fold ge in H3. Eq. ss. i. des.
        esplits. eapply exec_step_external; eauto.
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

Lemma same_public: prog_public prog = prog_public tprog.
Proof. inv TRANSF. des; eauto. Qed.

Lemma transf_initial_capture S1 S2 S2'
    (INITSRC: Mach.initial_state prog S1)
    (INITTGT: Asm.initial_state tprog S2)
    (MATCH: match_states S1 S2)
    (CAPTGT: Asm.glob_capture tprog S2 S2'):
  exists S1', Mach.glob_capture prog S1 S1'
  /\ match_states S1' S2'
  /\ gm_improves (Mach.concrete_snapshot ge S1') (concrete_snapshot tge S2').
Proof.
  specialize senv_preserved. intros SENVEQ.
  inv CAPTGT. ss. rename m' into m2'.
  rewrite Genv.globalenv_public in CAPTURE. erewrite <- same_public in CAPTURE; eauto.
  inv MATCH; try by inv INITSRC.
  exploit non_static_equiv. instantiate (1:=AST.prog_public prog). intros EQUIV.
  assert (exists m1', Genv.capture_init_mem m0 (Genv.non_static_glob (Genv.globalenv prog) (AST.prog_public prog)) m1'
               /\ Mem.extends m1' m2').
  { clear INITSRC INITTGT. rewrite <- EQUIV in CAPTURE. clear EQUIV. inv CAPTURE.
    remember (Genv.non_static_glob (Genv.globalenv prog) (prog_public prog)) as l. clear Heql.
    clear SENVEQ. move l before fb. revert_until fb.
    induction l; ss; i.
    { inv CAP. esplits; eauto. econs. econs. }
    inv CAP. exploit Mem.capture_extends_backward; eauto. i. des.
    exploit IHl; try eapply CAPLIST; eauto. i. des. inv H. esplits; eauto. econs. econs; eauto. }
  des. inv INITSRC. esplits; eauto.
  - econs. eauto. rewrite Genv.globalenv_public. eauto.
  - econs; eauto.
  - ii. unfold Mach.concrete_snapshot, concrete_snapshot in *. inv SENVEQ. des. erewrite H4, H2. des_ifs; ss.
    eapply Mem.mext_concrete; eauto. eapply Mem.concrete_valid; eauto.
Qed.

Theorem transf_program_correct:
  mixed_simulation (Mach.semantics return_address_offset prog) (Asm.semantics tprog).
Proof.
  econs. econs.
  - apply lt_wf.
  - rr. i. exists (1 + a)%nat. lia.
  - econs. i. exploit transf_initial_states; eauto. i. des.
    exists st2. split.
    (* initial state *)
    + econs; eauto. eapply initial_state_determ.
    (* mixed sim *) 
    + r. ii. inversion INITSRC; subst. inversion H0; subst.
      exploit transf_initial_capture;
      [eapply INITSRC|eapply H|eapply H0|eapply CAPTGT|]. i. des.
      exists (measure S1')%nat. exists S1'. esplits; eauto. apply match_states_xsim; auto.
      eapply glob_capture_char; eauto. eapply initial_state_char; eauto.
  - i. apply senv_preserved.
Qed.

End PRESERVATION.
