Require Import Coqlib sflib CoqlibC.
Require Import Globalenvs Events.
Require Import Integers.
Require Import Smallstep Simulation.
Require Import Mach.

(** Determinacy *)

Section Determinacy.

Variable rao: function -> code -> ptrofs -> Prop.

Lemma semantics_single_events p s (INT: ~ is_external (Genv.globalenv p) s): single_events_at (semantics rao p) s.
Proof.
  red. intros. inv H; (try (exploit external_call_trace_length; eauto; intro T)); simpl; try lia; ss; des_ifs.
Qed.

Lemma semantics_receptive_at:
  forall (p: program) s (INT: ~ is_external (Genv.globalenv p) s), receptive_at (semantics rao p) s.
Proof.
  intros. constructor; simpl; intros.
  - (* receptiveness *)
    assert (t1 = E0 -> exists s2, step rao (Genv.globalenv p) s t2 s2).
    { intros. subst. inv H0. exists s1; auto. }
    inversion H; subst; auto.
    (* builtin *)
    ss. determ_tac external_call_receptive.
    econstructor; econstructor; eauto.
    (* external *)
    simpl in INT. rewrite H2 in INT.
    exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
    eexists. eapply exec_function_external; eauto.
  - red; intros; inv H; simpl; try lia; ss; des_ifs.
    eapply external_call_trace_length; eauto.
    eapply external_call_trace_length; eauto.
Qed.

Hypothesis rao_dtm: forall f c ofs ofs',
    rao f c ofs -> rao f c ofs' -> ofs = ofs'.

Lemma extcall_arguments_determ
      rs m rsp sg vs0 vs1
      (ARGS0: Mach.extcall_arguments rs m rsp sg vs0)
      (ARGS1: Mach.extcall_arguments rs m rsp sg vs1):
  vs0 = vs1.
Proof.
  generalize dependent vs1. generalize dependent vs0. generalize dependent sg.
  assert (A: forall l v1 v2,
             Mach.extcall_arg rs m rsp l v1 -> Mach.extcall_arg rs m rsp l v2 -> v1 = v2).
  { intros. inv H; inv H0; congruence. }
  assert (B: forall p v1 v2,
             Mach.extcall_arg_pair rs m rsp p v1 -> Mach.extcall_arg_pair rs m rsp p v2 -> v1 = v2).
  { intros. inv H; inv H0.
    eapply A; eauto.
    f_equal; eapply A; eauto. }
  assert (C: forall ll vl1, list_forall2 (Mach.extcall_arg_pair rs m rsp) ll vl1 ->
                       forall vl2, list_forall2 (Mach.extcall_arg_pair rs m rsp) ll vl2 -> vl1 = vl2).
  { induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; eauto. }
  intros. eapply C; eauto.
Qed.

Lemma semantics_determinate_at:
  forall (p: program) s (INT: ~ is_external (Genv.globalenv p) s), deterministic_at (semantics rao p) s.
Proof.
  intros. constructor; simpl; intros.
  - (* determinacy *)
    inv STEP0; inv STEP1; Eq; try (split; [apply match_traces_E0| intro;auto]);
      try (elim H; simpl; try rewrite H2; auto); ss.
    + exploit rao_dtm. eapply H1. eapply H14. intros. subst. auto.
    + exploit eval_builtin_args_determ. eapply H. eapply H12. intros; subst.
      ss. determ_tac external_call_determ.
    + assert (sp = sp0) by auto. rewrite H3 in *. Eq.
    + exploit extcall_arguments_determ. eapply H0. eapply H9. intros. subst.
      simpl in INT. determ_tac external_call_determ. des_ifs.
  - inv FINAL; inv STEP.
  - red; intros; inv H; simpl; try lia; ss; des_ifs.
    eapply external_call_trace_length; eauto.
    eapply external_call_trace_length; eauto.
Qed.

Lemma initial_state_determ: forall p st0 st1,
    Smallstep.initial_state (semantics rao p) st0 ->
    Smallstep.initial_state (semantics rao p) st1 -> st0 = st1.
Proof. intros. inv H; inv H0. subst ge0 ge. Eq. Qed.

Theorem final_state_determ: forall p st0 retv,
    Smallstep.final_state (semantics rao p) st0 retv ->
    Dfinal_state (semantics rao p) st0 retv.
Proof.
  econstructor; eauto.
  - intros. inv FINAL0; inv FINAL1; Eq; auto.
  - red. unfold not. intros. inv FINAL; inv H0; simpl.
Qed.

End Determinacy.

Ltac DStep_tac := esplit; [(eapply semantics_determinate_at; simpl in *; eauto)|].
