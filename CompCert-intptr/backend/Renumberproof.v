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

(** Postorder renumbering of RTL control-flow graphs. *)

Require Import Coqlib Maps Postorder.
Require Import AST Linking.
Require Import Simulation RTLD Classical PointerOp.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Op Registers RTL Renumber.
From Paco Require Import paco.

Definition match_prog (p tp: RTL.program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. eapply match_transform_program; eauto.
Qed.

Section PRESERVATION.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Let sem := semantics prog.
Let tsem := semantics tprog.
Let ev_rel2 := ev_rel_eq.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof (Genv.find_funct_transf TRANSL).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof (Genv.find_funct_ptr_transf TRANSL).

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof (Genv.find_symbol_transf TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_transf TRANSL).

Lemma same_public: prog_public prog = prog_public tprog.
Proof. inv TRANSL. des; eauto. Qed.

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; reflexivity.
Qed.

Lemma find_function_translated:
  forall ros rs fd,
  find_function ge ros rs = Some fd ->
  find_function tge ros rs = Some (transf_fundef fd).
Proof.
  unfold find_function; intros. destruct ros as [r|id].
  eapply functions_translated; eauto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
  eapply function_ptr_translated; eauto.
Qed.

(** Effect of an injective renaming of nodes on a CFG. *)

Section RENUMBER.

Variable f: PTree.t positive.

Hypothesis f_inj: forall x1 x2 y, f!x1 = Some y -> f!x2 = Some y -> x1 = x2.

Lemma renum_cfg_nodes:
  forall c x y i,
  c!x = Some i -> f!x = Some y -> (renum_cfg f c)!y = Some(renum_instr f i).
Proof.
  set (P := fun (c c': code) =>
              forall x y i, c!x = Some i -> f!x = Some y -> c'!y = Some(renum_instr f i)).
  intros c0. change (P c0 (renum_cfg f c0)). unfold renum_cfg.
  apply PTree_Properties.fold_rec; unfold P; intros.
  (* extensionality *)
  eapply H0; eauto. rewrite H; auto.
  (* base *)
  rewrite PTree.gempty in H; congruence.
  (* induction *)
  rewrite PTree.gsspec in H2. unfold renum_node. destruct (peq x k).
  inv H2. rewrite H3. apply PTree.gss.
  destruct f!k as [y'|] eqn:?.
  rewrite PTree.gso. eauto. red; intros; subst y'. elim n. eapply f_inj; eauto.
  eauto.
Qed.

End RENUMBER.

Definition pnum (f: function) := postorder (successors_map f) f.(fn_entrypoint).

Definition reach (f: function) (pc: node) := reachable (successors_map f) f.(fn_entrypoint) pc.

Lemma transf_function_at:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  reach f pc ->
  (transf_function f).(fn_code)!(renum_pc (pnum f) pc) = Some(renum_instr (pnum f) i).
Proof.
  intros.
  destruct (postorder_correct (successors_map f) f.(fn_entrypoint)) as [A B].
  fold (pnum f) in *.
  unfold renum_pc. destruct (pnum f)! pc as [pc'|] eqn:?.
  simpl. eapply renum_cfg_nodes; eauto.
  elim (B pc); auto. unfold successors_map. rewrite PTree.gmap1. rewrite H. simpl. congruence.
Qed.

Ltac TR_AT :=
  match goal with
  | [ A: (fn_code _)!_ = Some _ , B: reach _ _ |- _ ] =>
        generalize (transf_function_at _ _ _ A B); simpl renum_instr; intros
  end.

Lemma reach_succ:
  forall f pc i s,
  f.(fn_code)!pc = Some i -> In s (successors_instr i) ->
  reach f pc -> reach f s.
Proof.
  unfold reach; intros. econstructor; eauto.
  unfold successors_map. rewrite PTree.gmap1. rewrite H. auto.
Qed.

Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_frames_intro: forall res f sp pc rs
        (REACH: reach f pc),
      match_frames (Stackframe res f sp pc rs)
                   (Stackframe res (transf_function f) sp (renum_pc (pnum f) pc) rs).

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk'
        (STACKS: list_forall2 match_frames stk stk')
        (REACH: reach f pc),
      match_states (State stk f sp pc rs m)
                   (State stk' (transf_function f) sp (renum_pc (pnum f) pc) rs m)
  | match_callstates: forall stk f args m stk'
        (STACKS: list_forall2 match_frames stk stk'),
      match_states (Callstate stk f args m)
                   (Callstate stk' (transf_fundef f) args m)
  | match_returnstates: forall stk v m stk'
        (STACKS: list_forall2 match_frames stk stk'),
      match_states (Returnstate stk v m)
                   (Returnstate stk' v m).

Lemma step_simulation:
  forall S1 t S2, IStep sem S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', DStep tsem S1' t S2' /\ match_states S2 S2'.
Proof.
  destruct 1. generalize dependent S2. rename H into INT.
  induction 1; intros S1' MS; inv MS; try TR_AT.
(* nop *)
  econstructor; split. DStep_tac. eapply exec_Inop; eauto.
  constructor; auto. eapply reach_succ; eauto. simpl; auto.
(* op *)
  econstructor; split.
  DStep_tac. eapply exec_Iop; eauto.
  instantiate (1 := v). rewrite <- H0. apply eval_operation_wrapper_preserved. exact symbols_preserved.
  constructor; auto. eapply reach_succ; eauto. simpl; auto.
(* load *)
  econstructor; split.
  assert (eval_addressing tge sp addr rs ## args = Some a).
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  DStep_tac. eapply exec_Iload; eauto.
  constructor; auto. eapply reach_succ; eauto. simpl; auto.
(* store *)
  econstructor; split.
  assert (eval_addressing tge sp addr rs ## args = Some a).
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  DStep_tac. eapply exec_Istore; eauto.
  constructor; auto. eapply reach_succ; eauto. simpl; auto.
(* call *)
  econstructor; split.
  DStep_tac. eapply exec_Icall with (fd := transf_fundef fd); eauto.
    eapply find_function_translated; eauto.
    apply sig_preserved.
  constructor. constructor; auto. constructor. eapply reach_succ; eauto. simpl; auto.
(* tailcall *)
  econstructor; split.
  DStep_tac. eapply exec_Itailcall with (fd := transf_fundef fd); eauto.
    eapply find_function_translated; eauto.
    apply sig_preserved.
  constructor. auto.
(* builtin *)
  econstructor; split.
  DStep_tac. unfold is_internal in INT. ss. des_ifs.
  eapply exec_Ibuiltin; eauto.
    eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto. eapply reach_succ; eauto. simpl; auto.
(* cond *)
  econstructor; split.
  DStep_tac. eapply exec_Icond; eauto.
  replace (if b then renum_pc (pnum f) ifso else renum_pc (pnum f) ifnot)
     with (renum_pc (pnum f) (if b then ifso else ifnot)).
  constructor; auto. eapply reach_succ; eauto. simpl. destruct b; auto.
  destruct b; auto.
(* jumptbl *)
  econstructor; split.
  DStep_tac. eapply exec_Ijumptable; eauto. rewrite list_nth_z_map. rewrite H1. simpl; eauto.
  constructor; auto. eapply reach_succ; eauto. simpl. eapply list_nth_z_in; eauto.
(* return *)
  econstructor; split.
  DStep_tac. eapply exec_Ireturn; eauto.
  constructor; auto.
(* internal function *)
  simpl. econstructor; split.
  DStep_tac. eapply exec_function_internal; eauto.
  constructor; auto. unfold reach. constructor.
(* external function *)
  econstructor; split.
  DStep_tac. eapply exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.
(* return *)
  inv STACKS. inv H1.
  econstructor; split.
  DStep_tac. eapply exec_return; eauto.
  constructor; auto.
Qed.

Lemma match_states_bsim
      s1 (EXT: is_external ge s1)
      s2 t s2' (STEPTGT: Step tsem s2 t s2')
      (MATCH: match_states s1 s2)
      (SAFESRC: safe sem s1) :
    (exists s1', Step sem s1 t s1' /\ match_states s1' s2')
  \/ (~ trace_intact t /\ exists s1'' t', Star sem s1 t' s1'' /\ exists tl, t' = (trace_cut_pterm t) ** tl).
Proof.
  assert (SEQUIV: Senv.equiv tge ge) by (symmetry; eapply senv_preserved).
  i. unfold is_external in *. des_ifs; i; inv MATCH.
  (* builtin *)
  - inv STEPTGT; try TR_AT; Eq.
    exploit external_call_symbols_preserved; eauto. i.
    exploit exec_Ibuiltin;[eapply Heq| |eapply H|].
    { eapply eval_builtin_args_preserved. eapply SEQUIV. eauto. }
    i. left. esplits; eauto.
    econs; eauto. eapply reach_succ; eauto. ss. eauto.
  (* external call *)
  - inv STEPTGT; try TR_AT; Eq.
    exploit external_call_symbols_preserved; eauto. i.
    exploit exec_function_external. eapply H. i.
    left. esplits; eauto. econs; eauto.
Qed.

Lemma transf_initial_states:
  forall S1, RTL.initial_state prog S1 ->
  exists S2, RTL.initial_state tprog S2 /\ match_states S1 S2.
Proof.
  intros. inv H. econstructor; split.
  econstructor.
    eapply (Genv.init_mem_transf TRANSL); eauto.
    rewrite symbols_preserved. rewrite (match_program_main TRANSL). eauto.
    eapply function_ptr_translated; eauto.
    rewrite <- H3; apply sig_preserved.
  constructor. constructor.
Qed.

Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> RTL.final_state S1 r -> RTL.final_state S2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. constructor.
Qed.

Lemma non_static_equiv l:
  Genv.non_static_glob (Genv.globalenv prog) l = Genv.non_static_glob (Genv.globalenv tprog) l.
Proof.
  induction l; ss.
  specialize senv_preserved. i. unfold ge, tge in H. r in H. des.
  specialize (H0 a).
  unfold Senv.public_symbol in H0. ss. rewrite <- H0.
  specialize (H a). rewrite <- H. erewrite IHl; eauto.
Qed.

Lemma transf_initial_capture S1 S2 S2'
    (INITSRC: RTL.initial_state prog S1)
    (INITTGT: RTL.initial_state tprog S2)
    (MATCH: match_states S1 S2)
    (CAPTGT: RTL.glob_capture tprog S2 S2'):
  exists S1', RTL.glob_capture prog S1 S1' /\ match_states S1' S2'.
Proof.
  inv CAPTGT. ss. rewrite Genv.globalenv_public in CAPTURE.
  rewrite <- same_public in CAPTURE. erewrite <- non_static_equiv in CAPTURE.
  inv MATCH. inv STACKS. esplits;[|econs; econs].
  econs; eauto. rewrite Genv.globalenv_public. eauto.
Qed.
  
Lemma match_states_xsim st_src0 st_tgt0 gmtgt
    (MATCH: match_states st_src0 st_tgt0) :
  xsim (RTL.semantics prog) (RTL.semantics tprog) gmtgt lt 0%nat st_src0 st_tgt0.
Proof.
  generalize dependent st_src0. generalize dependent st_tgt0.
  pcofix CIH. i. pfold. destruct (classic (is_external ge st_src0)); cycle 1.
  (* not external *)
  - left. econs. econs.
    + i. exploit step_simulation; eauto. i. des.
      esplits; eauto; [eapply tr_rel_refl; eapply ev_rel_refl|].
      left. split; [eapply plus_one; eauto|]. eapply semantics_receptive_at; auto.
    + ii. eapply final_state_determ; eauto. inv FINALSRC. inv MATCH. inv STACKS. econs.
  (* external *)
  - right. econs. i. econs.
    + i. exploit match_states_bsim; eauto. i. des.
      * left. esplits; eauto; [eapply tr_rel_refl; eapply ev_rel_refl|].
        left. eauto. eapply plus_one. eauto.
      * right. esplits; eauto. subst. eapply tr_rel_refl. eapply ev_rel_refl.
    + ii. inv FINALTGT. inv MATCH. inv STACKS. esplits; auto. eapply star_refl. econs.
    + ss. specialize (SAFESRC _ (star_refl _ _ _)). des; cycle 2; clarify; [inv SAFESRC; ss|].
      inv MATCH; ss; des_ifs; inv SAFESRC; unfold ge in *; clarify.
      * esplits. right. esplits. eapply exec_Ibuiltin; eauto; [TR_AT; eauto| |].
        { eapply eval_builtin_args_preserved. eapply senv_preserved. eauto. }
        { eapply external_call_symbols_preserved; eauto. apply senv_preserved. }
      * right. esplits. eapply exec_function_external; eauto.
        eapply external_call_symbols_preserved; eauto. apply senv_preserved.
Qed.

Theorem transf_program_correct:
  mixed_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  econs. econs.
  - apply lt_wf.
  - rr. i. exists (S a). lia.
  - econs. i. exploit transf_initial_states; eauto. i. des.
    exists S2. split.
    (* initial state *)
    + econs; eauto. eapply initial_state_determ.
    (* mixed sim *) 
    + r. ii. exploit transf_initial_capture; eauto. i. des. esplits; eauto.
      { subst. ss. unfold concrete_snapshot. ii.
        destruct senv_preserved. des. fold tge. rewrite H4, H5.
        inv INITSRC. inv H1. inv H2. inv STACKS. ss. }
        des_ifs; eauto. apply match_states_xsim; auto.
  - i. apply senv_preserved.
Qed.

End PRESERVATION.







