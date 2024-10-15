Require Import Coqlib CoqlibC sflib.
Require Import Globalenvs Events.
Require Import Smallstep Simulation.
Require Import Csharpminor.

(** Determinacy *)

Lemma semantics_single_events p s (INT: ~ Csharpminor.is_external (globalenv (Csharpminor.semantics p)) s):
  single_events_at (Csharpminor.semantics p) s.
Proof.
  red. intros. inv H; (try (exploit external_call_trace_length; eauto; intro T)); simpl; try lia; ss.
Qed.

Let eval_expr_determ:
  forall ge e le m a v, eval_expr ge e le m a v -> forall v', eval_expr ge e le m a v' -> v = v'.
Proof.
  induction 1; intros v' EV; inv EV; try congruence.
  - inv H; inv H1; congruence.
  - exploit IHeval_expr; eauto. intros; subst; Eq.
  - exploit IHeval_expr1; eauto. exploit IHeval_expr2; eauto.
    intros; subst; Eq.
  - exploit IHeval_expr; eauto. intros; subst; Eq.
Qed.

Let eval_exprlist_determ:
  forall ge e le m al vl, eval_exprlist ge e le m al vl -> forall vl', eval_exprlist ge e le m al vl' -> vl = vl'.
Proof.
  induction 1; intros vl' EV; inv EV; try congruence.
  - exploit IHeval_exprlist; eauto. intros. subst.
    exploit eval_expr_determ. eapply H3. eapply H. intros. subst; auto.
Qed.

Let alloc_variables_determ:
  forall env m vars e m1, alloc_variables env m vars e m1 -> forall e' m1', alloc_variables env m vars e' m1' -> e = e' /\ m1 = m1'.
Proof.
  induction 1; intros e' m1' EV; inv EV; f_equal; eauto. rewrite H in H8.
  inv H8. eapply IHalloc_variables; eauto.
Qed.

Lemma initial_state_determ: forall p st0 st1,
    Smallstep.initial_state (Csharpminor.semantics p) st0 ->
    Smallstep.initial_state (Csharpminor.semantics p) st1 -> st0 = st1.
Proof.
  intros. inv H; inv H0. subst ge0 ge. Eq.
Qed.

Ltac Determ :=
  try congruence;
  match goal with
  | [ |- match_traces _ E0 E0 /\ (_ -> _) ]  =>
          split; [constructor|intros _; Determ]
  | [ H: is_call_cont ?k |- _ ] =>
          contradiction || (clear H; Determ)
  | [ H1: eval_expr _ _ _ _ ?a ?v1, H2: eval_expr _ _ _ _ ?a ?v2 |- _ ] =>
          assert (v1 = v2) by (eapply eval_expr_determ; eauto);
          clear H1 H2; Determ
  | [ H1: eval_exprlist _ _ _ _ ?a ?v1, H2: eval_exprlist _ _ _ _ ?a ?v2 |- _ ] =>
          assert (v1 = v2) by (eapply eval_exprlist_determ; eauto);
          clear H1 H2; Determ
  | [ H1: alloc_variables _ _ ?vars ?e ?m1, H2: alloc_variables _ _ ?vars ?e' ?m2 |- _ ] =>
          assert (e = e' /\ m1 = m2) by (eapply alloc_variables_determ; eauto);
          clear H1 H2; Determ
  | _ => idtac
  end.

Lemma semantics_determinate_at:
  forall (p: program) s (INT: ~ is_external (Genv.globalenv p) s), deterministic_at (semantics p) s.
Proof.
  econstructor; eauto.
  - intros. simpl in *. inv STEP0; inv STEP1; Determ; subst; eauto; try by (clarify; subst; esplits; eauto).
    + determ_tac external_call_determ.
    + inv H0; inv H12; auto.
    + inv H0; inv H12; auto.
    + des; subst; eauto. erewrite H3 in H14. clarify.
    + simpl in INT.
      determ_tac external_call_determ.
  - i. inv FINAL; inv STEP.
  - unfold single_events_at. i. eapply semantics_single_events; eauto.
Qed.

Ltac simpl_case :=
  match goal with
  | [ H: match_traces _ E0 _ |- _ ] =>
    inv H; do 2 econstructor; eauto
  | [ H: match_traces _ _ E0 |- _ ] =>
    inv H; do 2 econstructor; eauto
  | _ => idtac
  end.

Lemma semantics_receptive_at:
  forall (p: program) s (INT: ~ is_external (Genv.globalenv p) s), receptive_at (semantics p) s.
Proof.
  econstructor; eauto.
  - intros. simpl in *.
    inv H; simpl_case; try (exploit external_call_receptive; eauto; intros (vres2 & m2 & EXT);
    (do 2 econstructor); eauto).
  - unfold single_events_at. i. eapply semantics_single_events; eauto.
Qed.

Theorem final_state_determ: forall p st0 retv,
    Smallstep.final_state (semantics p) st0 retv ->
    Dfinal_state (semantics p) st0 retv.
Proof.
  econstructor; eauto.
  - intros. inv FINAL1; inv FINAL0; auto.
  - red. unfold not. intros. inv FINAL; inv H0.
Qed.

Ltac DStep_tac := esplit; [(eapply semantics_determinate_at; simpl in *; eauto)|].
