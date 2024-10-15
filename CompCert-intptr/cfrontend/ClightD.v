(** Determinacy *)
Require Import Clight.
Require Import Coqlib CoqlibC sflib.
Require Import Globalenvs Events.
Require Import Smallstep Simulation.

Ltac Determ_aux EVALEXPR EVALLVAL :=
  try congruence; try Eq;
  match goal with
  | [ H: ?H1 /\ ?H2 |- _ ] => inv H; Determ_aux EVALEXPR EVALLVAL
  | [ H: ?H1 \/ ?H2 |- _ ] => inv H; Determ_aux EVALEXPR EVALLVAL
  | [ H: is_call_cont ?k |- _ ] =>
    contradiction || (clear H; Determ_aux EVALEXPR EVALLVAL)
  | [ H1: eval_expr _ _ _ _ ?a ?v1, H2: eval_expr _ _ _ _ ?a ?v2 |- _ ] =>
          assert (v1 = v2) by (eapply EVALEXPR; eauto);
          clear H1 H2; Determ_aux EVALEXPR EVALLVAL
  | [ H1: eval_lvalue _ _ _ _ ?a ?v, H2: eval_lvalue _ _ _ _ ?a ?v' |- _ ] =>
          assert (v = v') by (eapply EVALLVAL; eauto);
          clear H1 H2; Determ_aux EVALEXPR EVALLVAL
  end.

Ltac terminate H :=
  assert (False) by inv H; contradiction.

Lemma eval_expr_determ:
  forall ge e le m a v, eval_expr ge e le m a v -> forall v', eval_expr ge e le m a v' -> v = v'
with eval_lvalue_determ:
       forall ge e le m a v, eval_lvalue ge e le m a v -> forall v', eval_lvalue ge e le m a v' -> v = v'.
Proof.
  - induction 1; intros v' EV; inv EV; try Determ_aux eval_expr_determ eval_lvalue_determ;
      try terminate H; try terminate H0; try terminate H1; try terminate H2.
    exploit eval_lvalue_determ. eapply H. eauto. eauto. i. subst.
    inv H0; inv H2; Eq.
  - induction 1; intros v'' EV; inv EV; try Determ_aux eval_expr_determ eval_lvalue_determ.
    Eq; eauto. exploit eval_expr_determ. eapply H. eapply H8. intros. subst. eauto.
Qed.

Let eval_exprlist_determ:
  forall ge e le m bl tyl vl, eval_exprlist ge e le m bl tyl vl  -> forall vl', eval_exprlist ge e le m bl tyl vl' -> vl' = vl.
Proof.
  induction 1; intros v' EV; inv EV; f_equal; eauto.
  exploit eval_expr_determ. apply H. apply H6. intros. subst.
  rewrite H0 in H8. inv H8; auto.
Qed.

Let alloc_variables_determ:
  forall ge env m vars e m1, alloc_variables ge env m vars e m1 -> forall e' m1', alloc_variables ge env m vars e' m1' -> e = e' /\ m1 = m1'.
Proof.
  induction 1; intros e' m1' EV; inv EV; f_equal; eauto. rewrite H in H8. inv H8. eapply IHalloc_variables; eauto.
Qed.

Let bind_parameters_determ:
  forall ge e m params vargs m1, bind_parameters ge e m params vargs m1 -> forall m1', bind_parameters ge e m params vargs m1' -> m1 = m1'.
Proof.
  induction 1; intros m1' EV; inv EV; f_equal; eauto. Eq. replace m1 with m3 in *. eapply IHbind_parameters; eauto.
  inv H0; inv H10; try congruence; try rewrite SZ0 in *; lia.
Qed.

Lemma semantics1_single_events p s (INT: ~ is_external (semantics1 p) (globalenv (semantics1 p)) s): single_events_at (semantics1 p) s.
Proof.
  red. intros. inv H; (try (exploit external_call_trace_length; eauto; intro T)); simpl; try lia; ss.
Qed.

Lemma semantics2_single_events p s (INT: ~ is_external (semantics2 p) (globalenv (semantics2 p)) s): single_events_at (semantics2 p) s.
Proof.
  red. intros. inv H; (try (exploit external_call_trace_length; eauto; intro T)); simpl; try lia; ss.
Qed.

Lemma initial_state_determ: forall p st0 st1,
    Smallstep.initial_state (semantics1 p) st0 ->
    Smallstep.initial_state (semantics1 p) st1 -> st0 = st1.
Proof.
  intros. inv H; inv H0. subst ge0 ge. Eq.
Qed.

Ltac Determ :=
  try congruence; try Eq;
  match goal with
  | [ |- match_traces _ E0 E0 /\ (_ -> _) ]  =>
    split; [constructor|intros _; Determ]
  | [ H: ?H1 /\ ?H2 |- _ ] => inv H; Determ
  | [ H: ?H1 \/ ?H2 |- _ ] => inv H; Determ
  | [ H: is_call_cont ?k |- _ ] =>
    contradiction || (clear H; Determ)
  | [ H1: eval_expr _ _ _ _ ?a ?v1, H2: eval_expr _ _ _ _ ?a ?v2 |- _ ] =>
          assert (v1 = v2) by (eapply eval_expr_determ; eauto);
          clear H1 H2; Determ
  | [ H1: eval_lvalue _ _ _ _ ?a ?v, H2: eval_lvalue _ _ _ _ ?a ?v' |- _ ] =>
          assert (v = v') by (eapply eval_lvalue_determ; eauto);
          clear H1 H2; Determ
  | [ H1: eval_exprlist _ _ _ _ _ ?a ?v1, H2: eval_exprlist _ _ _ _ _ ?a ?v2 |- _ ] =>
          assert (v1 = v2) by (eapply eval_exprlist_determ; eauto);
          clear H1 H2; Determ
  | [ H1: alloc_variables _ _ _ ?vars ?e ?m1, H2: alloc_variables _ _ _ ?vars ?e' ?m2 |- _ ] =>
          assert (e = e' /\ m1 = m2) by (eapply alloc_variables_determ; eauto);
          clear H1 H2; Determ
  | [ H1: bind_parameters _ _ _ _ ?e ?m1, H2: bind_parameters _ _ _ _ ?e ?m2 |- _ ] =>
          assert (m1 = m2) by (eapply bind_parameters_determ; eauto);
          clear H1 H2; Determ
  | _ => idtac
  end.

Lemma semantics1_determinate_at:
  forall p s (INT: ~ is_external (semantics1 p) (globalenv (semantics1 p)) s),
  deterministic_at (semantics1 p) s.
Proof.
  econstructor; eauto.
  - intros. simpl in *. inv STEP0; inv STEP1; Determ; subst; eauto; try by (esplits; eauto); try by Eq.
    + clarify.  inv H2; inv H15; Eq; clarify; eauto.
      * rewrite SZ0 in *; lia.
      * rewrite SZ in *; lia.
    + ss. determ_tac external_call_determ.
    + inv H; inv H6. Determ. subst; eauto.
    + determ_tac external_call_determ.
  - intros. inv FINAL; inv STEP.
  - eapply semantics1_single_events. eauto.
Qed.

Lemma semantics2_determinate_at:
  forall p s (INT: ~ is_external (semantics1 p) (globalenv (semantics2 p)) s),
  deterministic_at (semantics2 p) s.
Proof.
  econstructor; eauto.
  - intros. simpl in *. inv STEP0; inv STEP1; Determ; subst; eauto; try by (esplits; eauto); try by Eq.
    + clarify.  inv H2; inv H15; Eq; clarify; eauto.
      * rewrite SZ0 in *; lia.
      * rewrite SZ in *; lia.
    + ss. determ_tac external_call_determ.
    + inv H; inv H6. Determ. subst; eauto.
    + determ_tac external_call_determ.
  - intros. inv FINAL; inv STEP.
  - eapply semantics2_single_events. eauto.
Qed.

Lemma semantics1_receptive_at:
  forall p s (INT: ~ is_external (semantics1 p) (globalenv (semantics1 p)) s),
  receptive_at (semantics1 p) s.
Proof.
  intros. unfold semantics1.
  set (ge := Clight.globalenv p). constructor; simpl; intros.
(* receptiveness *)
  assert (t1 = E0 -> exists s2, step1 ge s t2 s2).
    intros. subst. inv H0. exists s1; auto.
  inversion H; subst; auto.
  (* builtin *)
  ss.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  econstructor; econstructor; eauto.
  (* external *)
  ss.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  exists (Returnstate vres2 k m2). econstructor; eauto.
(* trace length *)
  red; simpl; intros. inv H; simpl; try lia; ss.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
Qed.

Lemma semantics2_receptive_at:
  forall p s (INT: ~ is_external (semantics2 p) (globalenv (semantics2 p)) s),
  receptive_at (semantics2 p) s.
Proof.
  intros. unfold semantics2.
  set (ge := Clight.globalenv p). constructor; simpl; intros.
(* receptiveness *)
  assert (t1 = E0 -> exists s2, step2 ge s t2 s2).
    intros. subst. inv H0. exists s1; auto.
  inversion H; subst; auto.
  (* builtin *)
  ss.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  econstructor; econstructor; eauto.
  (* external *)
  ss.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  exists (Returnstate vres2 k m2). econstructor; eauto.
(* trace length *)
  red; simpl; intros. inv H; simpl; try lia; ss.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
Qed.

Theorem final_state_determ1: forall p st0 retv,
    Smallstep.final_state (semantics1 p) st0 retv ->
    Dfinal_state (semantics1 p) st0 retv.
Proof.
  econstructor; eauto.
  - intros. inv FINAL1; inv FINAL0; Eq. auto.
  - red. unfold not. intros. inv FINAL; inv H0.
Qed.

Theorem final_state_determ: forall p st0 retv,
    Smallstep.final_state (semantics2 p) st0 retv ->
    Dfinal_state (semantics2 p) st0 retv.
Proof.
  econstructor; eauto.
  - intros. inv FINAL1; inv FINAL0; Eq. auto.
  - red. unfold not. intros. inv FINAL; inv H0.
Qed.

Ltac DStep_tac1 := esplit; [(eapply semantics1_determinate_at; simpl in *; eauto)|].
Ltac DStep_tac2 := esplit; [(eapply semantics2_determinate_at; simpl in *; eauto)|].
