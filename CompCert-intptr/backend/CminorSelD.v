Require Import Coqlib.
Require Import Globalenvs Events.
Require Import CoqlibC Smallstep Simulation.
Require Import CminorSel.

(** Determinacy *)

Lemma semantics_single_events p s (INT: ~ is_external (Genv.globalenv p) s): single_events_at (CminorSel.semantics p) s.
Proof.
  red. intros. inv H; (try (exploit external_call_trace_length; eauto; intro T)); simpl; try lia; ss.
Qed.

Lemma eval_expr_determ:
  forall ge sp e m le a v, eval_expr ge sp e m le a v -> forall v', eval_expr ge sp e m le a v' -> v' = v
with eval_exprlist_determ:
       forall ge sp e m le al vl, eval_exprlist ge sp e m le al vl -> forall vl', eval_exprlist ge sp e m le al vl' -> vl' = vl
with eval_condexpr_determ:
       forall ge sp e m le a v, eval_condexpr ge sp e m le a v  -> forall v', eval_condexpr ge sp e m le a v' -> v' = v.
Proof.
  - induction 1; intros v' EV; inv EV; try (Eq; auto); try (by determ_tac eval_exprlist_determ).
    + determ_tac eval_condexpr_determ. determ_tac eval_expr_determ.
    + determ_tac eval_expr_determ. exploit eval_expr_determ. eapply H0. eapply H6. intros; subst. auto.
    + determ_tac eval_exprlist_determ. determ_tac external_call_determ.
    + determ_tac eval_exprlist_determ. eapply external_call_deterministic; eauto.
  - induction 1; intros v' EV; inv EV; try (Eq; auto).
    determ_tac eval_exprlist_determ. determ_tac eval_expr_determ.
  - induction 1; intros v' EV; inv EV; try (Eq; auto).
    + determ_tac eval_exprlist_determ.
    + determ_tac eval_condexpr_determ. exploit eval_condexpr_determ. eapply H0. eapply H7. auto.
    + determ_tac eval_expr_determ. exploit eval_condexpr_determ. eapply H0. eapply H6. auto.
Qed.

Let eval_expr_or_symbol_determ:
  forall ge sp e m le a vf, eval_expr_or_symbol ge sp e m le a vf -> forall vf', eval_expr_or_symbol ge sp e m le a vf' -> vf = vf'.
Proof. induction 1; intros vf' EV; inv EV; try congruence. eapply eval_expr_determ; eauto. Qed.

Let eval_exitexpr_determ:
  forall ge sp e m le a n, eval_exitexpr ge sp e m le a n -> forall n', eval_exitexpr ge sp e m le a n' -> n = n'.
Proof.
  induction 1; intros vf' EV; inv EV; try congruence.
  + exploit eval_expr_determ. eapply H. eapply H4. intros. inv H1. Eq.
  + exploit eval_condexpr_determ. eapply H. eapply H6. intro; subst. eapply IHeval_exitexpr; eauto.
  + exploit eval_expr_determ. eapply H. eapply H4. intro; subst. eapply IHeval_exitexpr; eauto.
Qed.

Let eval_builtin_arg_determ:
  forall ge sp e m a v, eval_builtin_arg ge sp e m a v -> forall v', eval_builtin_arg ge sp e m a v' -> v = v'.
Proof.
  induction 1; intros vf' EV; inv EV; try congruence.
  + eapply eval_expr_determ; eauto.
  + exploit eval_expr_determ. eapply H. eapply H3.
    exploit eval_expr_determ. eapply H0. eapply H5. intros; subst; auto.
  + erewrite IHeval_builtin_arg1; eauto. erewrite IHeval_builtin_arg2; eauto.
Qed.

Let eval_builtin_args_determ:
  forall ge sp e m al vl, list_forall2 (eval_builtin_arg ge sp e m) al vl -> forall vl', list_forall2 (eval_builtin_arg ge sp e m) al vl' -> vl = vl'.
Proof.
  intros. generalize dependent al. generalize dependent vl'. induction vl; intros.
  { inv H. inv H0. simpl. auto. }
  inv H. inv H0. exploit eval_builtin_arg_determ. eapply H4. eapply H2. intros; subst. f_equal. eapply IHvl; eauto.
Qed.

Lemma initial_state_determ: forall p st0 st1,
    Smallstep.initial_state (CminorSel.semantics p) st0 ->
    Smallstep.initial_state (CminorSel.semantics p) st1 -> st0 = st1.
Proof. intros. inv H; inv H0. subst ge0 ge. Eq. Qed.

Ltac Determ :=
  repeat (try congruence;
          match goal with
          | [ |- match_traces _ E0 E0 /\ (_ -> _) ]  =>
            split; [constructor|intros _]
          | [ H: is_call_cont ?k |- _ ] =>
            contradiction || (clear H)
          | [ H1: eval_expr _ _ _ _ _ ?a ?v1, H2: eval_expr _ _ _ _ _ ?a ?v2 |- _ ] =>
            assert (v1 = v2) by (eapply eval_expr_determ; eauto);
            clear H1 H2
          | [ H1: eval_exprlist _ _ _ _ _ ?a ?v1, H2: eval_exprlist _ _ _ _ _ ?a ?v2 |- _ ] =>
            assert (v1 = v2) by (eapply eval_exprlist_determ; eauto);
            clear H1 H2
          | [ H1: eval_expr_or_symbol _ _ _ _ _ ?a ?v1, H2: eval_expr_or_symbol _ _ _ _ _ ?a ?v2 |- _ ] =>
            assert (v1 = v2) by (eapply eval_expr_or_symbol_determ; eauto);
            clear H1 H2
          | [ H1: eval_condexpr _ _ _ _ _ ?a ?v1, H2: eval_condexpr _ _ _ _ _ ?a ?v2 |- _ ] =>
            assert (v1 = v2) by (eapply eval_condexpr_determ; eauto);
            clear H1 H2
          | [ H1: eval_exitexpr _ _ _ _ _ ?a ?v1, H2: eval_exitexpr _ _ _ _ _ ?a ?v2 |- _ ] =>
            assert (v1 = v2) by (eapply eval_exitexpr_determ; eauto);
            clear H1 H2
          | _ => idtac
          end).

Lemma semantics_determinate_at:
  forall (p: program) s (INT: ~ is_external (Genv.globalenv p) s), deterministic_at (CminorSel.semantics p) s.
Proof.
  econstructor; eauto.
  - intros. simpl in *.
    inv STEP0; inv STEP1; Determ; subst; auto; try by (clarify; subst; esplits; eauto).
    + exploit eval_builtin_args_determ. eapply H. eapply H11. intros; subst.
      determ_tac external_call_determ.
    + rewrite H in H6. clarify.
    + simpl in INT. determ_tac external_call_determ.
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
  forall (p: program) s (INT: ~ is_external (Genv.globalenv p) s), receptive_at (CminorSel.semantics p) s.
Proof.
  econstructor; eauto.
  - intros. simpl in *.
    inv H; simpl_case; try (exploit external_call_receptive; eauto; intros (vres2 & m2 & EXT);
    (do 2 econstructor); eauto).
  - unfold single_events_at. i. eapply semantics_single_events; eauto.
Qed.

Theorem final_state_determ: forall p st0 retv,
    Smallstep.final_state (CminorSel.semantics p) st0 retv ->
    Dfinal_state (CminorSel.semantics p) st0 retv.
Proof.
  econstructor; eauto.
  - intros. inv FINAL1; inv FINAL0; auto.
  - red. unfold not. intros. inv FINAL; inv H0.
Qed.

Ltac DStep_tac := esplit; [(eapply semantics_determinate_at; simpl in *; eauto)|].
