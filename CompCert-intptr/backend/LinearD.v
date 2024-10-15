Require Import Coqlib CoqlibC Events.
Require Import Globalenvs Smallstep Simulation.
Require Import sflib Linear.

(** Determinacy *)

Lemma semantics_single_events p s (INT: ~ is_external (Genv.globalenv p) s): single_events_at (Linear.semantics p) s.
Proof.
  red. intros. inv H; (try (exploit external_call_trace_length; eauto; intro T)); simpl; try lia; ss.
Qed.

Lemma semantics_receptive_at:
  forall (p: program) s (INT: ~ is_external (Genv.globalenv p) s), receptive_at (semantics p) s.
Proof.
  intros. constructor; simpl; intros.
(* receptiveness *)
  assert (t1 = E0 -> exists s2, step (Genv.globalenv p) s t2 s2).
    intros. subst. inv H0. exists s1; auto.
  inversion H; subst; auto. ss. des_ifs.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  eexists. eapply exec_Lbuiltin; eauto.
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  eexists. econs; eauto.
(* trace length *)
  red; intros; inv H; simpl; try omega.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
Qed.

Lemma semantics_determinate_at:
  forall (p: program) s (INT: ~ is_external (Genv.globalenv p) s), deterministic_at (semantics p) s.
Proof.
  intros. constructor; simpl; intros.
  - (* determinacy *)
    inv STEP0; inv STEP1; Eq; try (split; [apply match_traces_E0| intro;auto]);
      try (elim H; simpl; try rewrite H2; auto); ss.
    + ss. ss. des_ifs.
      determ_tac eval_builtin_args_determ. determ_tac external_call_determ.
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
  - intros. inv FINAL0; inv FINAL1. Eq.
  - red. unfold not. intros. inv FINAL; inv H0.
Qed.

Ltac DStep_tac := esplit; [(eapply semantics_determinate_at; simpl in *; eauto; des_ifs)|].

Require Import Memory.

Section FUNCPERM.

Variable p: program.
Let ge := Genv.globalenv p.

Definition mem_char (m: mem) :=
  forall b fd, Genv.find_funct_ptr ge b = Some fd ->
  Mem.perm m b 0 Max Nonempty
  /\ (forall ofs k p, Mem.perm m b ofs k p -> ofs = 0 /\ p = Nonempty).

Lemma capture_mem_char m b addr m'
    (CHAR: mem_char m)
    (CAP: Mem.capture m b addr m'):
  mem_char m'.
Proof.
  unfold mem_char in *. i. exploit CHAR; eauto. i. des. split.
  - erewrite <- Genv.capture_same_perm; eauto.
  - i. eapply H1. erewrite Genv.capture_same_perm; eauto.
Qed.

Lemma capture_list_mem_char m bs addrs m'
    (CHAR: mem_char m)
    (CAP: Mem.capture_list m bs addrs m'):
  mem_char m'.
Proof.
  ginduction bs; i; [inv CAP; eauto|]. inv CAP. hexploit capture_mem_char; eauto.
Qed.

Definition state_char (s: state) : Prop :=
  mem_char (state_mem s).

Lemma init_mem_mem_char m
    (INIT: Genv.init_mem p = Some m):
  mem_char m.
Proof.
  r. i. exploit Genv.init_mem_characterization_2; eauto. i. des; split; eauto.
  eapply Mem.perm_max. eauto.
Qed.

Lemma initial_state_char s
    (INIT: initial_state p s):
  state_char s.
Proof. inv INIT. ss. r. ss. eapply init_mem_mem_char; eauto. Qed.

Lemma glob_capture_char s s'
    (CHAR: state_char s)
    (GCAP: glob_capture p s s'):
  state_char s'.
Proof.
  inv GCAP. inv CAPTURE. unfold state_char in *. ss.
  eapply capture_list_mem_char; eauto.
Qed.

Lemma state_char_preservation s s' tr
    (CHAR: state_char s)
    (STEP: step ge s tr s'):
  state_char s'.
Proof.
  Local Transparent Mem.free. inv STEP; ss; unfold state_char in *; ss.
  - r. i. exploit CHAR; eauto. i. des. split.
    { unfold Mem.storev in H0. des_ifs; eapply Mem.perm_store_1; eauto. }
    i. unfold Mem.storev in H0. des_ifs; eapply H3; eapply Mem.perm_store_2; eauto.
  - r. i. exploit CHAR; eauto. i. des. split.
    2:{ i. eapply H3. eapply Mem.perm_free_3; eauto. }
    hexploit Mem.free_range_perm; eauto. intros FPERM.
    destruct (classic ((fn_stacksize f) > 0)); cycle 1.
    { eapply Mem.perm_free_1; eauto. }
    destruct (peq b0 stk); cycle 1.
    { eapply Mem.perm_free_1; eauto. }
    subst. specialize (FPERM 0). exploit FPERM; try lia. i.
    eapply H3 in H5. des; clarify.
  - r. i. exploit CHAR; eauto. i. des. split; cycle 1.
    { i. eapply H3. instantiate (1:=Max).
      eapply external_call_max_perm; eauto.
      { eapply Mem.perm_valid_block; eauto. }
      eapply Mem.perm_max; eauto. }
    assert (NM: nonempty_perm m b0 0).
    { r. split; eauto. i. exploit H3; eauto. i. des; eauto. }
    exploit ec_nonempty; eauto.
    { eapply external_call_common_spec. }
    i. r in H4. des; eauto.
  - r. i. exploit CHAR; eauto. i. des. split.
    2:{ i. eapply H2. eapply Mem.perm_free_3; eauto. }
    hexploit Mem.free_range_perm; eauto. intros FPERM.
    destruct (classic ((fn_stacksize f) > 0)); cycle 1.
    { eapply Mem.perm_free_1; eauto. }
    destruct (peq b0 stk); cycle 1.
    { eapply Mem.perm_free_1; eauto. }
    subst. specialize (FPERM 0). exploit FPERM; try lia. i.
    eapply H2 in H4. des; clarify.
  - unfold mem_char in *. i. exploit CHAR; eauto. i. des.
    assert (stk <> b).
    { hexploit Mem.fresh_block_alloc; eauto. i.
      eapply Mem.perm_valid_block in H1. ii; subst; clarify. }
    split; [eapply Mem.perm_alloc_1; eauto|].
    i. eapply H2. eapply Mem.perm_alloc_4; eauto.
  - r. i. exploit CHAR; eauto. i. des. split; cycle 1.
    { i. eapply H2. instantiate (1:=Max).
      eapply external_call_max_perm; eauto.
      { eapply Mem.perm_valid_block; eauto. }
      eapply Mem.perm_max; eauto. }
    assert (NM: nonempty_perm m b 0).
    { r. split; eauto. i. exploit H2; eauto. i. des; eauto. }
    exploit ec_nonempty; eauto.
    { eapply external_call_common_spec. }
    i. r in H3. des; eauto.
Qed.

End FUNCPERM.
