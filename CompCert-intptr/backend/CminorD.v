Require Import Coqlib.
Require Import Values Globalenvs Events.
Require Import Smallstep Simulation.
Require Import Cminor.

(** Determinacy *)

Lemma initial_state_determ: forall p st0 st1,
    Smallstep.initial_state (semantics p) st0 ->
    Smallstep.initial_state (semantics p) st1 -> st0 = st1.
Proof.
  intros. inv H; inv H0. subst ge0 ge. Eq.
Qed.

Theorem final_state_determ: forall p st0 retv,
    Smallstep.final_state (Cminor.semantics p) st0 retv ->
    Dfinal_state (Cminor.semantics p) st0 retv.
Proof.
  econstructor; eauto.
  - intros. inv FINAL1; inv FINAL0; auto.
  - red. unfold not. intros. inv FINAL; inv H0.
Qed.

Ltac DStep_tac := esplit; [(eapply semantics_determinate; simpl in *; eauto)|].
