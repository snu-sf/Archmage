Require Import Coqlib sflib CoqlibC.
Require Import Events.
Require Import Integers.
Require Import Globalenvs.
Require Import Smallstep Simulation.
Require Import Asm.

Lemma semantics_single_events p s (INT: ~ is_external (Genv.globalenv p) s): single_events_at (Asm.semantics p) s.
Proof.
  red. intros. inv H; (try (exploit external_call_trace_length; eauto; intro T)); simpl; try lia; ss; des_ifs.
Qed.

Lemma semantics_receptive_at:
  forall (p: program) s (INT: ~ is_external (Genv.globalenv p) s), receptive_at (semantics p) s.
Proof.
  intros. constructor; simpl; intros.
  - (* receptiveness *)
    assert (t1 = E0 -> exists s2, step (Genv.globalenv p) s t2 s2).
    { intros. subst. inv H0. exists s1; auto. }
    inversion H; subst; auto.
    (* builtin *)
    ss. des_ifs.
    exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
    econstructor; econstructor; eauto.
    (* external *)
    simpl in INT. rewrite H2, H3 in INT.
    exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
    eexists. eapply exec_step_external; eauto.
  - red; intros; inv H; simpl; try lia; ss; des_ifs.
    eapply external_call_trace_length; eauto.
    eapply external_call_trace_length; eauto.
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
  - intros. inv FINAL0; inv FINAL1; Eq; auto.
  - red. unfold not. intros. inv FINAL; inv H0; simpl in *; Eq.
Qed.

Ltac DStep_tac := esplit; [(eapply semantics_determinate_at; simpl in *; eauto)|].

Require Import Memory.

Section FUNCPERM.

Variable p: program.  
Let ge := Genv.globalenv p.
Let sem := Asm.semantics p.

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
  ginduction bs; i; [inv CAP; eauto|].
  inv CAP. hexploit capture_mem_char; eauto.
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
Proof.
  inv INIT. ss. r. ss. eapply init_mem_mem_char; eauto.
Qed.

Lemma glob_capture_char
    s s'
    (CHAR: state_char s)
    (GCAP: glob_capture p s s'):
  state_char s'.
Proof.
  inv GCAP. inv CAPTURE. unfold state_char in *. ss.
  eapply capture_list_mem_char; eauto.
Qed.

(* move to Memory.v *)
Lemma store_mem_char
    chunk m b ofs v' m'
    (CHAR: mem_char m)
    (STORE: Mem.store chunk m b ofs v' = Some m'):
  mem_char m'.
Proof.
  r. i. exploit CHAR; eauto. i. des. split.
  { des_ifs; eapply Mem.perm_store_1; eauto. }
  i. des_ifs; eapply H1; eapply Mem.perm_store_2; eauto.
Qed.

Lemma storev_mem_char
    chunk m v v' m'
    (CHAR: mem_char m)
    (STORE: Mem.storev chunk m v v' = Some m'):
  mem_char m'.
Proof.
  unfold Mem.storev in STORE. des_ifs; eapply store_mem_char; eauto.
Qed.

Lemma alloc_mem_char
    m lo hi m' b
    (CHAR: mem_char m)
    (ALLOC: Mem.alloc m lo hi = (m', b)):
  mem_char m'.
Proof.
  unfold mem_char in *. i. exploit CHAR; eauto. i. des.
  assert (b0 <> b).
  { hexploit Mem.fresh_block_alloc; eauto. i.
    eapply Mem.perm_valid_block in H0. ii; subst; clarify. }
  split; [eapply Mem.perm_alloc_1; eauto|].
  i. eapply H1. eapply Mem.perm_alloc_4; eauto.
Qed.

Lemma free_mem_char
    m b hi m'
    (CHAR: mem_char m)
    (FREE: Mem.free m b 0 hi = Some m'):
  mem_char m'.
Proof.
  r. i. exploit CHAR; eauto. i. des. split.
  2:{ i. eapply H1. eapply Mem.perm_free_3; eauto. }
  hexploit Mem.free_range_perm; eauto. intros FPERM.
  destruct (classic (hi > 0)); cycle 1.
  { eapply Mem.perm_free_1; eauto. }
  destruct (peq b0 b); cycle 1.
  { eapply Mem.perm_free_1; eauto. }
  subst. specialize (FPERM 0). exploit FPERM; try lia. i.
  eapply H1 in H3. des; clarify.
Qed.

Lemma state_char_preservation
    s s' tr
    (CHAR: state_char s)
    (STEP: step ge s tr s'):
  state_char s'.
Proof.
  Local Transparent Mem.free.
  inv STEP; ss; unfold state_char in *; ss.
  - destruct i; ss; clarify; eauto; try by (unfold exec_load in *; des_ifs).
    + unfold exec_store in *. des_ifs. eapply storev_mem_char; eauto.
    + unfold exec_store in *. des_ifs. eapply storev_mem_char; eauto.
    + unfold exec_store in *. des_ifs. eapply storev_mem_char; eauto.
    + unfold exec_store in *. des_ifs. eapply storev_mem_char; eauto.
    + unfold exec_store in *. des_ifs. eapply storev_mem_char; eauto.
    + unfold exec_store in *. des_ifs. eapply storev_mem_char; eauto.
    + unfold exec_store in *. des_ifs. eapply storev_mem_char; eauto.
    + unfold exec_store in *. des_ifs. eapply storev_mem_char; eauto.
    + unfold goto_label in H2. des_ifs.
    + unfold goto_label in H2. des_ifs.
    + unfold goto_label in H2. des_ifs.
    + unfold goto_label in H2. des_ifs.
    + unfold exec_store in *. des_ifs. eapply storev_mem_char; eauto.
    + unfold exec_store in *. des_ifs. eapply storev_mem_char; eauto.
    + des_ifs.
      eapply store_mem_char; try eapply Heq1.
      eapply store_mem_char; try eapply Heq0.
      eapply alloc_mem_char; eauto.
    + des_ifs. eapply free_mem_char; eauto.
  - r. i. exploit CHAR; eauto. i. des. split; cycle 1.
    { i. eapply H6. instantiate (1:=Max).
      eapply external_call_max_perm; eauto.
      { eapply Mem.perm_valid_block; eauto. }
      eapply Mem.perm_max; eauto. }
    assert (NM: nonempty_perm m b0 0).
    { r. split; eauto. i. exploit H6; eauto. i. des; eauto. }
    exploit ec_nonempty; eauto.
    { eapply external_call_common_spec. }
    i. r in H7. des; eauto.
  - r. i. exploit CHAR; eauto. i. des. split; cycle 1.
    { i. eapply H5. instantiate (1:=Max).
      eapply external_call_max_perm; eauto.
      { eapply Mem.perm_valid_block; eauto. }
      eapply Mem.perm_max; eauto. }
    assert (NM: nonempty_perm m b0 0).
    { r. split; eauto. i. exploit H5; eauto. i. des; eauto. }
    exploit ec_nonempty; eauto.
    { eapply external_call_common_spec. }
    i. r in H6. des; eauto.
Qed.

Lemma state_char_star
    s s' tr
    (CHAR: state_char s)
    (STEP: star step ge s tr s'):
  state_char s'.
Proof.
  ginduction STEP; eauto. i. eapply IHSTEP. eapply state_char_preservation; eauto.
Qed.

Lemma state_char_plus
    s s' tr
    (CHAR: state_char s)
    (STEP: plus step ge s tr s'):
  state_char s'.
Proof.
  inv STEP. eapply state_char_star; try eapply H0; eauto. eapply state_char_preservation; eauto.
Qed.

Lemma state_char_dstar
    s s' tr
    (CHAR: state_char s)
    (STEP: DStar sem s tr s'):
  state_char s'.
Proof.
  ginduction STEP; eauto. i. eapply IHSTEP. inv H. eapply state_char_preservation; eauto.
Qed.

Lemma state_char_dplus
    s s' tr
    (CHAR: state_char s)
    (STEP: DPlus sem s tr s'):
  state_char s'.
Proof.
  inv STEP. eapply state_char_dstar; try eapply H0; eauto.
  inv H. eapply state_char_preservation; eauto.
Qed.

End FUNCPERM.
