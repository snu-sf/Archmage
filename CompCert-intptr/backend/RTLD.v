Require Import Coqlib CoqlibC Events.
Require Import Globalenvs Smallstep Simulation.
Require Import sflib RTL.

(** Determinacy *)

Lemma semantics_single_events p s (INT: ~ is_external (Genv.globalenv p) s): single_events_at (RTL.semantics p) s.
Proof.
  red. intros. inv H; (try (exploit external_call_trace_length; eauto; intro T)); simpl; try lia; ss; des_ifs.
Qed.

Definition ev_rel_eq (ev1 ev2: event) : Prop := ev1 = ev2.

Lemma tr_rel_eq tr :
  tr_rel (ev_rel_eq) tr tr.
Proof. ginduction tr; ss; econs; eauto; ss. Qed.

(* Definition state_event_rel (p:program) (st: Smallstep.state (semantics p)) := *)
(*   fun ev1 ev2 => *)
(*     let ge := Genv.globalenv p in *)
(*     match st with *)
(*     | State _ _ _ _ _ m => event_rel (eventval_bind ge m) ev1 ev2 *)
(*     | Callstate _ _ _ m => event_rel (eventval_bind ge m) ev1 ev2 *)
(*     | Returnstate _ _ m => event_rel (eventval_bind ge m) ev1 ev2 *)
(*     end. *)

(* Definition ev_rel (p: program) : event -> event -> Prop := *)
(*   sem_ev_rel (semantics p) (state_event_rel p). *)

(* Definition ev_rel_eq (p: program) (st: Smallstep.state (semantics p)) (ev1 ev2: event) : Prop := ((fun x => ev1 = ev2) st). *)

(* Lemma tr_rel_eq *)
(*     p st tr : *)
(*   tr_rel (RTL.semantics p) (ev_rel_eq p) st tr tr. *)
(* Proof. *)
(*   ginduction tr; ss; econs; eauto; ss. eapply IHtr. *)
(* Qed. *)

(* Definition ev_rel (p: program) (st: Smallstep.state (semantics p)) (ev1 ev2: event) : Prop := *)
(*   let ge := Genv.globalenv p in *)
(*   match st with *)
(*   | State _ _ _ _ _ m => event_rel (eventval_bind ge m) ev1 ev2 *)
(*   | Callstate _ _ _ m => event_rel (eventval_bind ge m) ev1 ev2 *)
(*   | Returnstate _ _ m => event_rel (eventval_bind ge m) ev1 ev2 *)
(*   end. *)
(* (fun (st: Smallstep.state (semantics p)) e1 e2 => e1 = e2) *)
(* (Smallstep.state L -> event -> event -> Prop) *)
Lemma semantics_determinate_at:
  forall (p: program) s (INT: ~ is_external (Genv.globalenv p) s),
    deterministic_at (semantics p) s.
Proof.
  intros. constructor; simpl; intros.
  - (* determinacy *)
    inv STEP0; inv STEP1; Eq;
      try (split; [apply match_traces_E0| intro;auto]);
      try (elim H; simpl; try rewrite H2; auto).
    + ss. des_ifs.
      determ_tac eval_builtin_args_determ. determ_tac external_call_determ.
    + ss. determ_tac external_call_determ.
    + esplits; eauto.
  - inv FINAL; inv STEP.
  - ii. eapply semantics_single_events; eauto.
Qed.

Lemma initial_state_determ: forall p st0 st1,
    Smallstep.initial_state (semantics p) st0 ->
    Smallstep.initial_state (semantics p) st1 -> st0 = st1.
Proof. intros. inv H; inv H0. subst ge0 ge. Eq. Qed.

Theorem final_state_determ: forall p st0 retv,
    Smallstep.final_state (semantics p) st0 retv ->
    Dfinal_state (semantics p) st0 retv.
Proof.
  econstructor; eauto.
  - intros. inv FINAL0; inv FINAL1. auto.
  - red. unfold not. intros. inv FINAL; inv H0.
Qed.

Ltac DStep_tac := esplit; [(eapply semantics_determinate_at; simpl in *; eauto; des_ifs)|].
