Require Import Coqlib CoqlibC Events.
Require Import Globalenvs Smallstep Simulation.
Require Import sflib CSSA.

(** Determinacy *)

Lemma semantics_single_events p s (INT: ~ is_external (Genv.globalenv p) s): single_events_at (CSSA.semantics p) s.
Proof.
  red. intros. inv H; (try (exploit external_call_trace_length; eauto; intro T)); simpl; try lia. ss. des_ifs.
Qed.

Lemma semantics_receptive_at:
  forall (p: program) s (INT: ~ is_external (Genv.globalenv p) s), receptive_at (semantics p) s.
Proof.
  intros. constructor; simpl; intros.
(* receptiveness *)
- assert (t1 = E0 -> exists s2, step (Genv.globalenv p) s t2 s2).
    intros. subst. inv H0. exists s1; auto.
  inversion H; subst; auto.
+ ss. des_ifs.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  esplits; eauto. eapply exec_Ibuiltin; eauto.
+ exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  esplits; eauto. econstructor; eauto.
(* trace length *)
- red; intros; inv H; simpl; try lia; ss; des_ifs.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
Qed.

Lemma semantics_determinate_at:
  forall (p: program) s (INT: ~ is_external (Genv.globalenv p) s), deterministic_at (semantics p) s.
Proof.
  intros. constructor; simpl; intros.
  - (* determinacy *)
    inv STEP0; inv STEP1; Eq;
      try (split; [apply match_traces_E0| intro;auto]);
      try (elim H; simpl; try rewrite H2; auto);ss.
    + ss. des_ifs.
      determ_tac eval_builtin_args_determ.
      determ_tac external_call_determ.
    + ss. determ_tac external_call_determ.
  - inv FINAL; inv STEP.
  - ii. eapply semantics_single_events; eauto.
Qed.

Lemma initial_state_determ: forall p st0 st1,
    Smallstep.initial_state (semantics p) st0 ->
    Smallstep.initial_state (semantics p) st1 -> st0 = st1.
Proof.
  intros. inv H; inv H0. subst ge0 ge. Eq.
Qed.

Theorem final_state_determ: forall p st0 retv,
    Smallstep.final_state (semantics p) st0 retv ->
    Dfinal_state (semantics p) st0 retv.
Proof.
  econstructor; eauto.
  - intros. inv FINAL0; inv FINAL1. auto.
  - red. unfold not. intros. inv FINAL; inv H0.
Qed.

Ltac DStep_tac := esplit; [(eapply semantics_determinate_at; simpl in *; eauto; des_ifs)|].
