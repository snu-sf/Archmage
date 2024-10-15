(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Whole-program behaviors *)

Require Import Classical.
Require Import ClassicalEpsilon.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.
Require Import Simulation.
Require Import sflib.
From Paco Require Import paco.
Require Import Coq.Relations.Relation_Operators.

Set Implicit Arguments.

Section FOREVERCOIND.

Variable L1: semantics.
 
Definition _forever_reactive2 (forever_reactive2: state L1 -> traceinf -> Prop)
  (s1: state L1) (T1: traceinf) : Prop :=
  exists s2 t T2 (INTACT: trace_intact t),
    Star L1 s1 t s2 /\ t <> E0 /\ forever_reactive2 s2 T2 /\ T1 = t *** T2.


(*     _forever_reactive2 forever_reactive2 s1 (t *** T) *)
(* . *)

Lemma forever_reactive_mon: monotone2 _forever_reactive2.
Proof. ii. inv IN. des. econs. esplits; eauto. Qed.

Hint Resolve forever_reactive_mon: paco.

Definition forever_reactive2 := paco2 _forever_reactive2 bot2.
Arguments forever_reactive2: clear implicits.

Lemma forever_reactive2_forever_reactive:
  forever_reactive2 <2= Forever_reactive L1.
Proof.
  cofix CIH. i. punfold PR. inv PR. des. pclearbot.
  eapply CIH in H1. subst. econs; eauto.
Qed.

Lemma forever_reactive_forever_reactive2:
  Forever_reactive L1 <2= forever_reactive2.
Proof.
  pcofix CIH. i. destruct PR. inv PR.
  pstep. econs. esplits; cycle 1.
  { eapply star_trans; eauto. }
  { destruct t, t0; ss. }
  { right. eapply CIH; eauto. }
  { traceEq. }
  eapply trace_intact_app; eauto.
Qed.

Variant star_clo (r: state L1 -> traceinf -> Prop)
        (s1: state L1) (T: traceinf): Prop :=
| silent_star_clo_intro
    s1' t T'
    (STAR: Star L1 s1 t s1')
    (REL: r s1' T')
    (TRACE: T = t *** T')
    (INTACT: trace_intact t).

Lemma star_clo_compatible:
  compatible2 _forever_reactive2 star_clo.
Proof.
  econs. { ii. inv IN. econs; eauto. }
  i. inv PR. inv REL. des. subst. rewrite <- Eappinf_assoc. econs. esplits.
  { eapply trace_intact_app. eapply INTACT. eapply INTACT0. }
  { eapply star_trans; eauto. }
  { ii. eapply Eapp_E0_inv in H2. des; ss. }
  2:{ traceEq. }
  econs; [eapply star_refl | | |]; eauto; ss.
Qed.

Definition _forever_silent2 (forever_silent2: state L1 ->  Prop) (s1: state L1) : Prop :=
  exists s2, Step L1 s1 E0 s2 /\ forever_silent2 s2.

Lemma forever_silent_mon: monotone1 _forever_silent2.
Proof. ii. inv IN. des. econs. esplits; eauto. Qed.

Hint Resolve forever_silent_mon: paco.

Definition forever_silent2 := paco1 _forever_silent2 bot1.
Arguments forever_silent2: clear implicits.

Lemma forever_silent2_forever_silent:
  forever_silent2 <1= Forever_silent L1.
Proof.
  cofix CIH. i. punfold PR. inv PR. des. pclearbot.
  eapply CIH in H0. subst. econs; eauto.
Qed.

Lemma forever_silent_forever_silent2:
  Forever_silent L1 <1= forever_silent2.
Proof.
  pcofix CIH. i. destruct PR.
  pstep. econs. esplits; cycle 1.
  { right. eapply CIH; eauto. }
  eauto.
Qed.

Variable index: Type.
Variable order: index -> index -> Prop.

Inductive _forever_silent_N2 (forever_silent_N2: index -> state L1 ->  Prop) : index -> L1.(state) -> Prop :=
| _forever_silent_N2_star
    s1 s2 i1 i2
    (STAR: Star L1 s1 E0 s2)
    (ORD: order i2 i1)
    (SIL: forever_silent_N2 i2 s2):
  _forever_silent_N2 forever_silent_N2 i1 s1
| _forever_silent_N2_plus
    s1 s2 i1 i2
    (STAR: Plus L1 s1 E0 s2)
    (SIL: forever_silent_N2 i2 s2):
  _forever_silent_N2 forever_silent_N2 i1 s1.

Definition forever_silent_N2 := paco2 _forever_silent_N2 bot2.
Arguments forever_silent2: clear implicits.

Lemma forever_silent_N_mon: monotone2 _forever_silent_N2.
Proof. ii. inv IN; [econs; eauto| econs 2; eauto]. Qed.

Hint Resolve forever_silent_N_mon: paco.

Lemma forever_silent_N2_forever_silent_N:
  forever_silent_N2 <2= forever_silent_N (step L1) order (globalenv L1).
Proof.
  cofix CIH. i. punfold PR. inv PR; pclearbot.
  - eapply CIH in SIL. econs; eauto.
  - eapply CIH in SIL. econs 2; eauto.
Qed.

Lemma forever_silent_N_forever_silent_N2:
  forever_silent_N (step L1) order (globalenv L1) <2= forever_silent_N2.
Proof.
  pcofix CIH. i. destruct PR.
  - pstep. econs; cycle 1; eauto.
  - pstep. econs 2; cycle 1; eauto.
Qed.

End FOREVERCOIND.

Hint Resolve forever_reactive_mon: paco.
Hint Resolve forever_silent_mon: paco.
Hint Resolve forever_silent_N_mon: paco.
Hint Resolve cpn2_wcompat: paco.

(** * Behaviors for program executions *)

(** The four possible outcomes for the execution of a program: *)
(* - Termination, with a finite trace of observable events *)
(*   and an integer value that stands for the process exit code *)
(*   (the return value of the main function). *)
(* - Divergence with a finite trace of observable events. *)
(*   (At some point, the program runs forever without doing any I/O.) *)
(* - Reactive divergence with an infinite trace of observable events. *)
(*   (The program performs infinitely many I/O operations separated *)
(*    by finite amounts of internal computations.) *)
(* - Going wrong, with a finite trace of observable events *)
(*   performed before the program gets stuck. *)
(* *)

Inductive program_behavior: Type :=
  | Terminates: trace -> int -> program_behavior
  | Partial_terminates: trace -> program_behavior
  | Diverges: trace -> program_behavior
  | Reacts: traceinf -> program_behavior
  | Goes_wrong: trace -> program_behavior.

(** Operations and relations on behaviors *)

Definition not_wrong (beh: program_behavior) : Prop :=
  match beh with
  | Terminates _ _ => True
  | Partial_terminates _ => True
  | Diverges _ => True
  | Reacts _ => True
  | Goes_wrong _ => False
  end.

Definition intact (beh: program_behavior) : Prop :=
  match beh with
  | Terminates _ _ => True
  | Partial_terminates _ => False
  | Diverges _ => True
  | Reacts _ => True
  | Goes_wrong _ => True
  end.

Definition behavior_app (t: trace) (beh: program_behavior): program_behavior :=
  match beh with
  | Terminates t1 r => Terminates (t ** t1) r
  | Partial_terminates t1 => Partial_terminates (t ** t1)
  | Diverges t1 => Diverges (t ** t1)
  | Reacts T => Reacts (t *** T)
  | Goes_wrong t1 => Goes_wrong (t ** t1)
  end.

Lemma behavior_app_assoc:
  forall t1 t2 beh,
  behavior_app (t1 ** t2) beh = behavior_app t1 (behavior_app t2 beh).
Proof.
  intros. destruct beh; simpl; f_equal; traceEq.
Qed.

Lemma behavior_app_E0:
  forall beh, behavior_app E0 beh = beh.
Proof.
  destruct beh; auto.
Qed.

Definition behavior_prefix (t: trace) (beh: program_behavior) : Prop :=
  exists beh', beh = behavior_app t beh'.


Variant _trinf_rel (evr: event -> event -> Prop) (trinf_rel: traceinf -> traceinf -> Prop) : traceinf -> traceinf -> Prop :=
| trinf_rel_intro
    es et trs trt
    (EVR: evr es et)
    (TIR: trinf_rel trs trt):
  _trinf_rel evr trinf_rel (Econsinf es trs) (Econsinf et trt).

Definition trinf_rel evr : _ -> _ -> Prop := paco2 (_trinf_rel evr) bot2.

Lemma trinf_rel_mon ev_rel:
  monotone2 (_trinf_rel ev_rel).
Proof. ii. inv IN; econs; eauto. Qed.

Hint Unfold trinf_rel.
Hint Resolve trinf_rel_mon: paco.

Lemma trinf_rel_refl pm t:
  trinf_rel (ev_rel pm) t t.
Proof.
  revert t. pcofix CIH. i. pfold.
  destruct t. econs; [eapply ev_rel_refl|]. right. eauto.
Qed.

Lemma trinf_rel_app
    ev_rel tr1 tr1' tr2 tr2'
    (TR1: tr_rel ev_rel tr1 tr1')
    (TR2: trinf_rel ev_rel tr2 tr2') :
  trinf_rel ev_rel (tr1 *** tr2) (tr1' *** tr2').
Proof.
  ginduction TR1; ss; i. pfold. econs; eauto. left. eapply IHTR1; eauto.
Qed.

Lemma trinf_rel_div_l
    ev_rel t t1 t2
    (TRREL: trinf_rel ev_rel (t1 *** t2) t):
  exists t1' t2', t = t1' *** t2' /\
             tr_rel ev_rel t1 t1' /\
             trinf_rel ev_rel t2 t2'.
Proof.
  ginduction t1; ss.
  - i. exists E0. exists t. esplits; traceEq. econs.
  - i. punfold TRREL. inv TRREL. pclearbot. exploit IHt1; eauto. i. des.
    subst. exists (et :: t1'). exists t2'. ss. esplits; eauto. econs; eauto.
Qed.

Lemma trinf_rel_div_r
    ev_rel t t1' t2'
    (TRREL: trinf_rel ev_rel t (t1' *** t2')):
  exists t1 t2, t = t1 *** t2 /\
           tr_rel ev_rel t1 t1' /\
           trinf_rel ev_rel t2 t2'.
Proof.
  ginduction t1'; ss.
  - i. exists E0. exists t. esplits; traceEq. econs.
  - i. punfold TRREL. inv TRREL. pclearbot. exploit IHt1'; eauto. i. des.
    subst. exists (es :: t1). exists t2. ss. esplits; eauto. econs; eauto.
Qed.

Definition pimap := (positive -> option Z).
Definition pimap' := option pimap.

(* eq *)
Definition behav_rel (pm: pimap) (beh1 beh2: program_behavior) : Prop :=
  match beh1, beh2 with
  | Terminates t1 i1, Terminates t2 i2 => tr_rel (ev_rel pm) t1 t2 /\ i1 = i2
  | Partial_terminates t1, Partial_terminates t2 => tr_rel (ev_rel pm) t1 t2
  | Diverges t1, Diverges t2 => tr_rel (ev_rel pm) t1 t2
  | Reacts t1, Reacts t2 => trinf_rel (ev_rel pm) t1 t2
  | Goes_wrong t1, Goes_wrong t2 => tr_rel (ev_rel pm) t1 t2
  | _, _ => False
  end.

Lemma behav_rel_refl pm beh: behav_rel pm beh beh.
Proof.
  destruct beh; ss; eauto.
  - split; eauto. eapply tr_rel_refl. eapply ev_rel_refl.
  - eapply tr_rel_refl. eapply ev_rel_refl.
  - eapply tr_rel_refl. eapply ev_rel_refl.
  - eapply trinf_rel_refl.
  - eapply tr_rel_refl. eapply ev_rel_refl.
Qed.

Definition program_observation : Type := pimap' * program_behavior.
(* name: (block -> option z) * program_behavior = program_observation *)

Definition behavior_improves (pm: pimap) (beh1 beh2: program_behavior) :=
  (behav_rel pm beh1 beh2
   \/ (exists t t', beh1 = Goes_wrong t /\ tr_rel (ev_rel pm) t t' /\ behavior_prefix t' beh2)
   \/ (exists t' t, beh2 = Partial_terminates t' /\ tr_rel (ev_rel pm) t t' /\ behavior_prefix t beh1)).

Definition gm_improves' (pm1 pm2: pimap') : Prop :=
  match pm1, pm2 with
  | Some pim1, Some pim2 => gm_improves pim1 pim2
  | _, None => True
  | None, Some _ => False
  end.
  
Definition observation_improves (obs1 obs2: program_observation) : Prop :=
  let pm1 := fst obs1 in let pm2 := fst obs2 in
  let beh1 := snd obs1 in let beh2 := snd obs2 in
  (match pm2 with
   | Some pim2 => behavior_improves pim2 beh1 beh2
   | None => True
   end) /\ (gm_improves' pm1 pm2).

Lemma observation_improves_refl:
  forall obs, observation_improves obs obs.
Proof.
  i. destruct obs; ss; r; ss. destruct p; ss. split; [|ii; eauto].
  left. eapply behav_rel_refl.
Qed.

Lemma prefix_tr_rel pim beh1 beh2 t
    (BREL: behav_rel pim beh1 beh2)
    (PREF : behavior_prefix t beh1):
  exists t', tr_rel (ev_rel pim) t t' /\ behavior_prefix t' beh2.
Proof.
  r in PREF. des. subst. unfold behav_rel in BREL.
  des_ifs; unfold behavior_app in Heq; des_ifs.
  - des. exploit tr_rel_div_l; eauto. i. des. subst.
    exists t1'. esplits; eauto. rr. exists (Terminates t2' i0). ss.
  - exploit tr_rel_div_l; eauto. i. des. subst.
    exists t1'. esplits; eauto. rr. exists (Partial_terminates t2'). ss.
  - exploit tr_rel_div_l; eauto. i. des. subst.
    exists t1'. esplits; eauto. rr. exists (Diverges t2'). ss.
  - exploit trinf_rel_div_l; eauto. i. des. subst.
    exists t1'. esplits; eauto. rr. exists (Reacts t2'). ss.
  - exploit tr_rel_div_l; eauto. i. des. subst.
    exists t1'. esplits; eauto. rr. exists (Goes_wrong t2'). ss.
Qed.

Lemma prefix_tr_rel_r pim beh1 beh2 t'
    (BREL: behav_rel pim beh1 beh2)
    (PREF : behavior_prefix t' beh2):
  exists t, tr_rel (ev_rel pim) t t' /\ behavior_prefix t beh1.
Proof.
  r in PREF. des. subst. unfold behav_rel in BREL.
  des_ifs; unfold behavior_app in Heq; des_ifs.
  - des. exploit tr_rel_div_r; eauto. i. des. subst.
    exists t1'. esplits; eauto. rr. exists (Terminates t2' i0). ss.
  - exploit tr_rel_div_r; eauto. i. des. subst.
    exists t1'. esplits; eauto. rr. exists (Partial_terminates t2'). ss.
  - exploit tr_rel_div_r; eauto. i. des. subst.
    exists t1'. esplits; eauto. rr. exists (Diverges t2'). ss.
  - exploit trinf_rel_div_r; eauto. i. des. subst.
    exists t0. esplits; eauto. rr. exists (Reacts t2). ss.
  - exploit tr_rel_div_r; eauto. i. des. subst.
    exists t1'. esplits; eauto. rr. exists (Goes_wrong t2'). ss.
Qed.

Lemma evval_rel_trans
    pm1 pm2 ev1 ev2 ev3
    (IMP: gm_improves pm1 pm2)
    (EV1: evval_rel pm1 ev1 ev2)
    (EV2: evval_rel pm2 ev2 ev3):
  evval_rel pm2 ev1 ev3.
Proof.
  unfold evval_rel in *. destruct ev1; ss; subst; destruct ev3; ss; try by des_ifs.
  - des_ifs. des. split; eauto. unfold to_int_ev in *. des_ifs.
  - des_ifs. des. split; eauto. unfold to_int_ev in *. des_ifs.
    + unfold eventval_bind in EV2. clarify. exploit IMP; eauto. i; clarify.
    + exploit IMP; eauto. i; clarify.
Qed.

Lemma evval_rel_list_trans
    pm1 pm2 ev1 ev2 ev3
    (IMP: gm_improves pm1 pm2)
    (EV1: Forall2 (evval_rel pm1) ev1 ev2)
    (EV2: Forall2 (evval_rel pm2) ev2 ev3):
  Forall2 (evval_rel pm2) ev1 ev3.
Proof.
  ginduction EV1; ii; [inv EV2; econs|].
  i. inv EV2. econs; eauto. eapply evval_rel_trans; eauto.
Qed.

Lemma ev_rel_trans
    pm1 pm2 ev1 ev2 ev3
    (IMP: gm_improves pm1 pm2)
    (EV1: ev_rel pm1 ev1 ev2)
    (EV2: ev_rel pm2 ev2 ev3):
  ev_rel pm2 ev1 ev3.
Proof.
  destruct ev1; ss; subst; [inv EV2; eauto| | | | ].
  - des_ifs. ss. des; subst; eauto. splits; eauto.
    + eapply evval_rel_list_trans; eauto.
    + eapply evval_rel_trans; eauto.
  - des_ifs. ss. des; subst; eauto. splits; eauto.
    eapply evval_rel_trans; eauto.
  - des_ifs. ss. des; subst; eauto. splits; eauto.
    eapply evval_rel_trans; eauto.
  - des_ifs. ss. des; subst; eauto. splits; eauto.
    eapply evval_rel_list_trans; eauto.
Qed.

Lemma tr_rel_trans
    pm1 pm2 ev1 ev2 ev3
    (IMP: gm_improves pm1 pm2)
    (TR1: tr_rel (ev_rel pm1) ev1 ev2)
    (TR2: tr_rel (ev_rel pm2) ev2 ev3):
  tr_rel (ev_rel pm2) ev1 ev3.
Proof.
  ginduction TR1; ss. ii. inv TR2. econs; eauto.
  { eapply ev_rel_trans; eauto. }
  exploit IHTR1; eauto.
Qed.

Lemma tr_rel_trans'
    pm ev1 ev2 ev3
    (TR1: tr_rel (ev_rel pm) ev1 ev2)
    (TR2: tr_rel (ev_rel pm) ev2 ev3):
  tr_rel (ev_rel pm) ev1 ev3.
Proof.
  ginduction TR1; ss. ii. inv TR2. econs; eauto.
  eapply ev_rel_trans; eauto. { rr; eauto. }
  exploit IHTR1; eauto.
Qed.

Lemma trinf_rel_trans
    pm1 pm2 ev1 ev2 ev3
    (IMP: gm_improves pm1 pm2)
    (TR1: trinf_rel (ev_rel pm1) ev1 ev2)
    (TR2: trinf_rel (ev_rel pm2) ev2 ev3):
  trinf_rel (ev_rel pm2) ev1 ev3.
Proof.
  revert_until IMP. revert ev1 ev2 ev3. pcofix CIH. ii.
  pfold. punfold TR1. inv TR1. punfold TR2. inv TR2. pclearbot. econs.
  { eapply ev_rel_trans; eauto. }
  right. eapply CIH; eauto.
Qed.

Lemma observation_improves_trans:
  forall obs1 obs2 obs3,
  observation_improves obs1 obs2 -> observation_improves obs2 obs3 ->
  observation_improves obs1 obs3.
Proof.
  i. destruct obs1 as [pm1 beh1]. destruct obs2 as [pm2 beh2]. destruct obs3 as [pm3 beh3].
  split; ss; cycle 1.
  { inv H; inv H0. ss. clear - H2 H3. unfold gm_improves' in *. des_ifs.
    unfold gm_improves in *. i. eapply H3; eauto. }
  inv H; inv H0. ss. unfold behavior_improves in *. destruct pm3; ss. des_ifs.
  destruct pm1; ss. rename p into pm3. rename p0 into pm2. rename p1 into pm1. des.
  - left. unfold behav_rel in *. des_ifs.
    + split; des; subst; eauto. eapply tr_rel_trans; eauto.
    + eapply tr_rel_trans; eauto.
    + eapply tr_rel_trans; eauto.
    + eapply trinf_rel_trans; eauto.
    + eapply tr_rel_trans; eauto.
  - right. left. exists t.
    assert (exists t'', tr_rel (ev_rel pm3) t' t'' /\ behavior_prefix t'' beh3).
    { eapply prefix_tr_rel; eauto. }
    des. esplits; eauto. eapply tr_rel_trans; eauto.
  - right. right.
    subst. ss. des_ifs. exists t0. exists t. esplits; eauto. eapply tr_rel_trans; eauto.
  - right. left.
    subst. unfold behav_rel in H1. des_ifs. exists t0. exists t'. esplits; eauto. eapply tr_rel_trans; eauto.
  - right. left. rewrite H1 in *. rewrite H in *. r in H6. des.
    unfold behavior_app in H6. destruct beh'; ss. inv H6.
    unfold behavior_prefix in H4.
    exists t0. des. exploit tr_rel_div_l. eapply H0. i. des.
    exists t1'. esplits; eauto.
    { eapply tr_rel_trans; eauto. }
    subst. erewrite behavior_app_assoc. rr. esplits; eauto.
  - clarify.
  - right. right. exists t'.
    assert (exists t0, tr_rel (ev_rel pm3) t0 t' /\ behavior_prefix t0 beh1).
    { exploit prefix_tr_rel_r; eauto. i. des. exists t0. esplit; eauto.
      eapply tr_rel_trans; eauto. }
    des. esplits; eauto.
  - right. unfold behavior_prefix in *. subst. des. clarify.
    assert (PREF: trace_prefix t'0 t \/ trace_prefix t t'0).
    { assert ((exists t1 t2, t'0 ** t1 = t ** t2) \/ exists t1 t2, t'0 *** t1 = t *** t2).
      { unfold behavior_app in *. des_ifs; eauto. }
      des.
      - clear -H. ginduction t'0; ss.
        + i. left. unfold trace_prefix. exists t. traceEq.
        + i. destruct t; ss.
          { right. r. esplits; eauto; traceEq. }
          inv H. exploit IHt'0; eauto. i. des.
          { left. r. r in H. des. subst. exists t3. esplits; eauto; traceEq. }
          right. r. r in H. des. subst. exists t3. esplits; eauto; traceEq.
      - clear -H. ginduction t'0; ss.
        + i. left. unfold trace_prefix. exists t. traceEq.
        + i. destruct t; ss.
          { right. r. esplits; eauto; traceEq. }
          inv H. exploit IHt'0; eauto. i. des.
          { left. r. r in H. des. subst. exists t3. esplits; eauto; traceEq. }
          right. r. r in H. des. subst. exists t3. esplits; eauto; traceEq. }
    des.
    + unfold trace_prefix in PREF. des. subst.
      exploit tr_rel_div_l; eauto. i. des; subst.
      left. exists t0. exists t1'. esplits; eauto.
      * eapply tr_rel_trans; eauto.
      * instantiate (1:= Partial_terminates t2'). ss.
    + unfold trace_prefix in PREF. des. subst.
      exploit tr_rel_div_r; eauto. i. des; subst.
      right. exists t'. exists t1'. esplits; eauto.
      * eapply tr_rel_trans; eauto.
      * instantiate (1:= Goes_wrong t2'). ss.
  - right. right.
    rewrite H1, H in *. r in H4. des.
    unfold behavior_app in H4. destruct beh'; ss. inv H4.
    r in H6. des.
    exists t'. exploit tr_rel_div_r. eapply H5. i. des.
    exists t1'. esplits; eauto.
    { eapply tr_rel_mon in H1; cycle 1. eapply ev_rel_mon; eauto.
      eapply tr_rel_trans'; eauto. }
    subst. erewrite behavior_app_assoc. rr. esplits; eauto.
Qed.

Lemma observation_improves_bot pm1 pm2 beh (IMP: gm_improves' pm1 pm2):
  observation_improves (pm1, (Goes_wrong E0)) (pm2, beh).
Proof.
  r. ss. split; eauto. des_ifs. right. left. esplits; eauto; [instantiate (1:=E0); econs|].
  r. exists beh. erewrite behavior_app_E0; auto.
Qed.

Lemma observation_improves_app
    pm1 pm2 beh1 beh2 t1 t2
    (OIMP: observation_improves (Some pm1, beh1) (Some pm2, beh2))
    (TRREL: tr_rel (ev_rel pm2) t1 t2) :
  observation_improves (Some pm1, behavior_app t1 beh1) (Some pm2, behavior_app t2 beh2).
Proof.
  red. ss. destruct OIMP as [OIMP IMP]. split; eauto; ss. unfold behavior_improves in *. des.
  - left. unfold behav_rel in OIMP. des_ifs; ss.
    + des; split; auto. eapply tr_rel_app; eauto.
    + eapply tr_rel_app; eauto.
    + eapply tr_rel_app; eauto.
    + eapply trinf_rel_app; eauto.
    + eapply tr_rel_app; eauto.
  - right. left. subst; ss.
    exists (t1 ** t). exists (t2 ** t'). esplits; eauto.
    { eapply tr_rel_app; eauto. }
    r in OIMP1. des. subst. r. exists beh'. erewrite behavior_app_assoc; eauto.
  - right. right. subst; ss.
    exists (t2 ** t'). exists (t1 ** t). esplits; eauto.
    { eapply tr_rel_app; eauto. }
    r in OIMP1. des. subst. r. exists beh'. erewrite behavior_app_assoc; eauto.
Qed.

(** Associating behaviors to programs. *)

Section PROGRAM_BEHAVIORS.

Variable L: semantics.

Inductive state_behaves (s: state L): program_behavior -> Prop :=
  | state_terminates: forall t s' r (INTACT: trace_intact t),
      Star L s t s' ->
      final_state L s' r ->
      state_behaves s (Terminates t r)
  | state_partial_terminates
      t s'
      (STAR: Star L s t s')
      (PTERM: ~trace_intact t) :
      state_behaves s (Partial_terminates (trace_cut_pterm t))
  | state_diverges: forall t s' (INTACT: trace_intact t),
      Star L s t s' -> Forever_silent L s' ->
      state_behaves s (Diverges t)
  | state_reacts: forall T,
      Forever_reactive L s T ->
      state_behaves s (Reacts T)
  | state_goes_wrong: forall t s' (INTACT: trace_intact t),
      Star L s t s' ->
      Nostep L s' ->
      (forall r, ~final_state L s' r) ->
      state_behaves s (Goes_wrong t).

Inductive program_observes: (option (positive -> option Z)) * program_behavior -> Prop :=
  | program_runs: forall s s' mp beh,
      initial_state L s -> initial_capture L s s' -> initial_pimap L s' = mp -> state_behaves s' beh ->
      program_observes (Some mp, beh)
  | program_goes_initially_wrong:
      (forall s, ~initial_state L s) ->
      program_observes (Some (fun _ => None), (Goes_wrong E0))
  | program_goes_initially_capture_wrong: forall s,
       initial_state L s -> (forall s', ~ initial_capture L s s') -> 
      program_observes (None, (Partial_terminates E0)).

Lemma state_behaves_app:
  forall s1 t s2 beh (INTACT: trace_intact t),
  Star L s1 t s2 -> state_behaves s2 beh -> state_behaves s1 (behavior_app t beh).
Proof.
  intros.
  inv H0; simpl; try (by econstructor; eauto; try (eapply star_trans; eauto); try eapply trace_intact_app; eauto).
  - replace (t ** trace_cut_pterm t0) with (trace_cut_pterm (t ** t0)); cycle 1.
    { apply trace_cut_pterm_intact_app; auto. }
    econs; eauto. eapply star_trans; eauto.
    { intros INTACT1. apply PTERM.
      apply trace_intact_app_rev in INTACT1. des. auto. }
  - econs; eauto. eapply star_forever_reactive; eauto.
Qed.

(** * Existence of behaviors *)

(*   The proof requires classical logic: the axiom of excluded middle *)
(*   and an axiom of description. *)

(** The most difficult part of the proof is to show the existence *)
(*   of an infinite trace in the case of reactive divergence. *)

Section TRACEINF_REACTS.

Variable s0: state L.

Hypothesis reacts:
  forall s1 t1 (INTACT: trace_intact t1), Star L s0 t1 s1 ->
  exists s2, exists t2, <<INTACT: trace_intact t2>> /\ Star L s1 t2 s2 /\ t2 <> E0.

Lemma reacts':
  forall s1 t1 (INTACT: trace_intact t1), Star L s0 t1 s1 ->
  { s2 : state L & { t2 : trace | <<INTACT: trace_intact t2>> /\ Star L s1 t2 s2 /\ t2 <> E0 } }.
Proof.
  intros.
  destruct (constructive_indefinite_description _ (reacts INTACT H)) as [s2 A].
  destruct (constructive_indefinite_description _ A) as [t2 [B C]].
  exists s2; exists t2; auto.
Qed.

CoFixpoint build_traceinf' (s1: state L) (t1: trace) (INTACT0: trace_intact t1) (ST: Star L s0 t1 s1) : traceinf' :=
  match reacts' INTACT0 ST with
  | existT s2 (exist t2 (conj INTACT1 (conj A B))) =>
      Econsinf' t2
                (build_traceinf' (trace_intact_app _ _ INTACT0 INTACT1) (star_trans ST A (eq_refl _)))
                B
  end.

Lemma reacts_forever_reactive_rec:
  forall s1 t1 (INTACT0: trace_intact t1) (ST: Star L s0 t1 s1),
  Forever_reactive L s1 (traceinf_of_traceinf' (build_traceinf' INTACT0 ST)).
Proof.
  cofix COINDHYP; intros.
  rewrite (unroll_traceinf' (build_traceinf' INTACT0 ST)). simpl.
  destruct (reacts' INTACT0 ST) as [s2 [t2 [INTACT1 [A B]]]].
  rewrite traceinf_traceinf'_app.
  econstructor. eauto. eexact A. auto. apply COINDHYP.
Qed.

Lemma reacts_forever_reactive:
  exists T, Forever_reactive L s0 T.
Proof.
  eexists (traceinf_of_traceinf' (build_traceinf' _ (star_refl (step L) (globalenv L) s0))).
  apply reacts_forever_reactive_rec.
Unshelve.
  ii. eauto. (* TODO: (trace_intact E0) make this lemma? *)
Qed.

End TRACEINF_REACTS.

Lemma diverges_forever_silent:
  forall s0,
  (forall s1 t1 (INTACT: trace_intact t1), Star L s0 t1 s1 -> exists s2, Step L s1 E0 s2) ->
  Forever_silent L s0.
Proof.
  cofix COINDHYP; intros.
  destruct (H s0 E0) as [s1 ST]. { ii. eauto. } constructor.
  econstructor. eexact ST. apply COINDHYP.
  intros. eapply H. { eauto. } eapply star_left; eauto.
Qed.

Lemma state_behaves_exists:
  forall s, exists beh, state_behaves s beh.
Proof.
  intros s0.
  destruct (classic (forall s1 t1 (INTACT: trace_intact t1), Star L s0 t1 s1 -> exists s2, exists t2, <<INTACT: trace_intact t2>> /\ Step L s1 t2 s2)).
  {
(* 1 Divergence (silent or reactive) *)
  destruct (classic (exists s1, exists t1, (<<BEHAV: trace_intact t1>>) /\ Star L s0 t1 s1 /\
                       (forall s2 t2 (INTACT: trace_intact t2), Star L s1 t2 s2 ->
                        exists s3, Step L s2 E0 s3))).
  {
(* 1.1 Silent divergence *)
  destruct H0 as [s1 [t1 [BEHAV [A B]]]].
  exists (Diverges t1); econstructor; eauto.
  apply diverges_forever_silent; auto.
  }
  {
(* 1.2 Reactive divergence *)
  destruct (@reacts_forever_reactive s0) as [T FR].
  intros.
  generalize (not_ex_all_not _ _ H0 s1). intro A; clear H0.
  generalize (not_ex_all_not _ _ A t1). intro B; clear A.
  apply not_and_or in B. des; ss; eauto.
  destruct (not_and_or _ _ B). contradiction.
  destruct (not_all_ex_not _ _ H0) as [s2 C]; clear H0.
  destruct (not_all_ex_not _ _ C) as [t2 D]; clear C.
  destruct (imply_to_and _ _ D) as [INTACT0 TMP]; clear D. rename TMP into D.
  destruct (imply_to_and _ _ D) as [E F]; clear D.
  destruct (H s2 (t1 ** t2)) as [s3 [t3 G]]. apply trace_intact_app; eauto. eapply star_trans; eauto.
  des.
  exists s3; exists (t2 ** t3); split.
  apply trace_intact_app; eauto. split.
  eapply star_right; eauto.
  red; intros. destruct (app_eq_nil t2 t3 H0). subst. elim F. exists s3; auto.
  exists (Reacts T); econstructor; eauto.
  }
  }
  {
(* 2 Termination (normal or by going wrong) *)
  destruct (not_all_ex_not _ _ H) as [s1 A]; clear H.
  destruct (not_all_ex_not _ _ A) as [t1 B]; clear A.
  destruct (imply_to_and _ _ B) as [INTACT TMP]; clear B. rename TMP into B.
  destruct (imply_to_and _ _ B) as [C D]; clear B.
  destruct (classic (exists r, final_state L s1 r)) as [[r FINAL] | NOTFINAL].
  {
(* 2.1 Normal termination *)
  exists (Terminates t1 r); econstructor; eauto.
  }
  destruct (classic (exists s2 t2, Step L s1 t2 s2)).
  {
(* 2.2 Partial Termination *)
    des.
    destruct (classic (trace_intact t2)).
    { exfalso. eauto. }
    exists (Partial_terminates (t1 ** (trace_cut_pterm t2))).
    replace (t1 ** trace_cut_pterm t2) with (trace_cut_pterm (t1 ** t2)); cycle 1.
    { apply trace_cut_pterm_intact_app; auto. }
    econs; eauto.
    { eapply star_trans; eauto. apply star_one. eauto. }
    intros INTACT1. apply H0.
    apply trace_intact_app_rev in INTACT1. des. auto.
  }
  {
(* 2.3 Going wrong *)
  exists (Goes_wrong t1); econstructor; eauto. red. intros.
  generalize (not_ex_all_not _ _ D s'); intros.
  generalize (not_ex_all_not _ _ H0 t); intros.
  apply not_and_or in H1. des; eauto.
  }
  }
Qed.

Theorem program_observes_exists:
  exists obs, program_observes obs.
Proof.
  destruct (classic (exists s, initial_state L s)) as [[s0 INIT] | NOTINIT].
(* 1. Initial state is defined. *)
- destruct (classic (exists s', initial_capture L s0 s')) as [[s0' INITC] | NOTINITC].
+ destruct (state_behaves_exists s0') as [beh SB].
  eexists. econs; eauto.
  (* exists (Some (initial_pimap L s0', beh)); econstructor; eauto. *)
+ exists (None, Partial_terminates E0). econs 3; eauto.
(* 2. Initial state is undefined *)
- exists (Some (fun _ => None), Goes_wrong E0). apply program_goes_initially_wrong.
  intros. eapply not_ex_all_not; eauto.
Qed.

End PROGRAM_BEHAVIORS.

(** * Forward simulations and program behaviors *)


(** * Backward simulations and program behaviors *)

Section BACKWARD_SIMULATIONS.

Context L1 L2 index order (S: NOSTUTTER.bsim_properties L1 L2 index order).

(* rlx = false is right? *)
Variable pim : positive -> option Z.

Let match_states : index -> L1.(state) -> L2.(state) -> Prop := NOSTUTTER.bsim L1 L2 pim order.

Lemma match_states_final s1 s2 i retv
    (FINAL: final_state L2 s2 retv)
    (MATCH: match_states i s1 s2)
    (SAFE: safe L1 s1) :
  exists s1', (<<STEPS: Star L1 s1 E0 s1'>>) /\ (<<FINAL: final_state L1 s1' retv>>).
Proof.
  punfold MATCH. inv MATCH. hexploit STEP; auto.
  i. inv H; clarify. hexploit FINAL0; eauto.
Qed.

Lemma match_states_simulation
    s1 s2 s2' i t'
    (STEP: Step L2 s2 t' s2')
    (MATCH: match_states i s1 s2)
    (SAFE: safe L1 s1):
  (exists s1' t i',
   ((tr_rel (ev_rel pim) t t') /\
    (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ order i' i)) /\
    (match_states i' s1' s2')))
\/ (exists s1' t,
   (~trace_intact t') /\
   (Star L1 s1 t s1') /\
   (exists tl, tr_rel (ev_rel pim) t (trace_cut_pterm t' ** tl))).
Proof.
  punfold MATCH. inv MATCH. hexploit STEP0; auto.
  i. inv H; clarify. hexploit STEP1; eauto. i. destruct H; des_safe.
  - inv H0; pclearbot; left; esplits; eauto.
  - right. esplits; eauto.
Qed.

Lemma match_states_progress s1 s2 i
      (SAFE: safe L1 s1)
      (MATCH: match_states i s1 s2) :
  (exists retv, <<FINAL: final_state L2 s2 retv>>)
\/ (exists t s2', <<STEP: Step L2 s2 t s2'>>).
Proof.
  punfold MATCH. inv MATCH. hexploit STEP; auto. i. inv H; clarify.
Qed.

Definition safe_along_behavior (s: state L1) (b: program_behavior) : Prop :=
  forall t1 s' b2 (INTACT: trace_intact t1), Star L1 s t1 s' -> b = behavior_app t1 b2 ->
     (exists r, final_state L1 s' r)
  \/ (exists t2, exists s'', Step L1 s' t2 s'').

Remark safe_along_safe:
  forall s b, safe_along_behavior s b -> safe L1 s.
Proof.
  intros; red; intros. eapply H; eauto. { ss. } symmetry; apply behavior_app_E0.
Qed.

Remark star_safe_along:
  forall s b t1 s' b2 (INTACT: trace_intact t1),
  safe_along_behavior s b ->
  Star L1 s t1 s' -> b = behavior_app t1 b2 ->
  safe_along_behavior s' b2.
Proof.
  intros; red; intros. eapply H. all: cycle 1. eapply star_trans; eauto.
  subst. rewrite behavior_app_assoc. eauto.
  eapply trace_intact_app; eauto.
Qed.

Remark not_safe_along_behavior:
  forall s b,
  ~ safe_along_behavior s b ->
  exists t, exists s', <<INTACT: trace_intact t>> /\
     behavior_prefix t b
  /\ Star L1 s t s'
  /\ Nostep L1 s'
  /\ (forall r, ~(final_state L1 s' r)).
Proof.
  intros.
  destruct (not_all_ex_not _ _ H) as [t1 A]; clear H.
  destruct (not_all_ex_not _ _ A) as [s' B]; clear A.
  destruct (not_all_ex_not _ _ B) as [b2 C]; clear B.
  destruct (imply_to_and _ _ C) as [INTACT TMP]; clear C. rename TMP into C.
  destruct (imply_to_and _ _ C) as [D E]; clear C.
  destruct (imply_to_and _ _ E) as [F G]; clear E.
  destruct (not_or_and _ _ G) as [P Q]; clear G.
  exists t1; exists s'.
  split; eauto.
  split. exists b2; auto.
  split. auto.
  split. red; intros; red; intros. elim Q. exists t; exists s'0; auto.
  intros; red; intros. elim P. exists r; auto.
Qed.

Lemma backward_simulation_star:
  forall s2 t' s2' (INTACT: trace_intact t'), Star L2 s2 t' s2' ->
  forall i s1 b, match_states i s1 s2 -> (forall t, tr_rel (ev_rel pim) t t' -> safe_along_behavior s1 (behavior_app t b)) ->
  (exists s1' t i',
   ((tr_rel (ev_rel pim) t t') /\
    (Star L1 s1 t s1') /\
    (match_states i' s1' s2'))).
Proof.
  induction 2; i.
  { exists s1, E0, i. esplits; eauto.
    - econs.
    - eapply star_refl. }
  subst. exploit trace_intact_app_rev; eauto. i. des.
  exploit match_states_simulation; eauto.
  { specialize (H3 (t1 ** t2)). hexploit H3; eauto.
    eapply tr_rel_refl. eapply ev_rel_refl. i. eapply safe_along_safe; eauto. }
  i. subst. destruct H1; cycle 1.
  { des. exfalso. eapply H1. i. des; eauto. }
  des.
  - exploit IHstar; eauto.
    { i. specialize (H3 (t ** t0)). hexploit H3.
      { eapply tr_rel_app; eauto. }
      i. instantiate (1:=b). erewrite behavior_app_assoc in H7.
      eapply star_safe_along; try eapply H7; cycle 1.
      { eapply plus_star. eauto. }
      { eauto. }
      { erewrite <- tr_rel_intact.
        3:{ eapply H1. }
        { eauto. }
        { ii. split; ii; subst; ss. unfold ev_rel, event_rel in ER. des_ifs. } } }
    i. des.
    esplits; cycle 2.
    { eauto. }
    { eapply tr_rel_app; eauto. }
    { eapply plus_star. eapply plus_star_trans; eauto. }
  - exploit IHstar; eauto.
    { i. specialize (H3 (t ** t0)). hexploit H3.
      { eapply tr_rel_app; eauto. }
      i. instantiate (1:=b). erewrite behavior_app_assoc in H8.
      eapply star_safe_along; try eapply H8; cycle 1.
      { eauto. }
      { eauto. }
      { erewrite <- tr_rel_intact.
        3:{ eapply H1. }
        { eauto. }
        { ii. split; ii; subst; ss. unfold ev_rel, event_rel in ER. des_ifs. } } }
    i. des.
    esplits; cycle 2.
    { eauto. }
    { eapply tr_rel_app; eauto. }
    { eapply star_trans; eauto. }
Qed.

Lemma backward_simulation_plus:
  forall s2 t' s2' (INTACT: trace_intact t'), Plus L2 s2 t' s2' ->
  forall i s1 b, match_states i s1 s2 -> (forall t, tr_rel (ev_rel pim) t t' -> safe_along_behavior s1 (behavior_app t b)) ->
  (exists s1' t i',
   ((tr_rel (ev_rel pim) t t') /\
    (Star L1 s1 t s1') /\
    (match_states i' s1' s2'))).
Proof.
  i.
  assert (SAFE: safe L1 s1).
  { specialize (H1 t'). eapply safe_along_safe.
    eapply H1. eapply tr_rel_refl. eapply ev_rel_refl. }
  inv H.
  hexploit match_states_simulation; eauto.
  eapply trace_intact_app_rev in INTACT. i. destruct H; cycle 1.
  { des; clarify. }
  des.
  - exploit plus_star; eauto. i.
    assert (trace_intact t).
    { erewrite <- tr_rel_intact; cycle 1; eauto. i.
      destruct ev1, ev2; ss. }
    hexploit backward_simulation_star; try apply H3; eauto.
    { i. eapply star_safe_along; cycle 1; eauto.
      instantiate (1:=b). specialize (H1 (t ** t0)).
      erewrite behavior_app_assoc in H1. eapply  H1. eapply tr_rel_app; eauto. }
    i. des. esplits; [| | eauto].
    + eapply tr_rel_app; eauto.
    + eapply star_trans; eauto.
  - assert (trace_intact t).
    { erewrite <- tr_rel_intact; cycle 1; eauto. i.
      destruct ev1, ev2; ss. }
    hexploit backward_simulation_star; try apply H3; eauto.
    { i. eapply star_safe_along; cycle 1; eauto.
      instantiate (1:=b). specialize (H1 (t ** t0)).
      erewrite behavior_app_assoc in H1. eapply  H1. eapply tr_rel_app; eauto. }
    i. des. esplits; [| | eauto].
    + eapply tr_rel_app; eauto.
    + eapply star_trans; eauto.
Qed.

Lemma backward_simulation_star_pterm:
  forall s2 t' s2' (PTERM: ~trace_intact t'), Star L2 s2 t' s2' ->
  forall i s1 b , match_states i s1 s2 ->
  (forall t, tr_rel (ev_rel pim) t t' -> safe_along_behavior s1 (behavior_app (trace_cut_pterm t) b)) ->
  (exists s1' t, <<STAR: Star L1 s1 t s1'>> /\ <<SUB: exists tl, tr_rel (ev_rel pim) t (trace_cut_pterm t' ** tl)>>).
Proof.
  induction 2; intros.
  { contradict PTERM. ss. }
  subst. hexploit match_states_simulation; eauto.
  { specialize (H3 (t1 ** t2)). eapply safe_along_safe; eauto. eapply H3.
    eapply tr_rel_refl. eapply ev_rel_refl. }
  i. destruct H1.
  2:{ des.
      subst. esplits; eauto. (* rewrite E0_left. *)
      rewrite trace_cut_pterm_pterm_app; eauto. }
  des.
  - destruct (classic (trace_intact t)).
    2: { destruct (trace_cut_pterm_split t) as [t3 SPLIT]. esplits; eauto.
      { eapply plus_star. eauto. }
      rewrite SPLIT.
      assert (~ trace_intact t1).
      { ii. eapply H6. erewrite <- tr_rel_intact; try eapply H1; eauto.
        i. destruct ev1, ev2; ss. }
      erewrite trace_cut_pterm_pterm_app; eauto. instantiate (1:=t3).
      eapply tr_rel_app; eauto.
      - eapply tr_rel_cut_pterm; eauto.
        { i. destruct ev1, ev2; ss. }
      - eapply tr_rel_refl. eapply ev_rel_refl. }
    assert (trace_intact t1).
    { clear - H1 H6. ii. eapply H6. clear H6. ginduction H1; ss. ii. des.
      - subst. destruct x; ss; eauto.
      - eapply IHForall2 in H0. eauto. }
    hexploit IHstar; eauto.
    { ii. eapply PTERM. eapply trace_intact_app; auto. }
    { i.
      specialize (H3 (t ** t0)). hexploit H3; eauto.
      { eapply tr_rel_app; eauto. }
      rewrite trace_cut_pterm_intact_app; auto. i.
      eapply star_safe_along.
      3:{ eapply plus_star. eauto. }
      { eauto. }
      { eauto. }
      rewrite <- behavior_app_assoc. eauto. }
    i. des. esplits.
    { eapply plus_star. eapply plus_star_trans. eapply H4. eapply STAR. eauto. }
    rewrite trace_cut_pterm_intact_app; auto.
    erewrite Eapp_assoc. eapply tr_rel_app; eauto.
  - destruct (classic (trace_intact t)).
    2: { destruct (trace_cut_pterm_split t) as [t3 SPLIT]. esplits; eauto.
      rewrite SPLIT.
      assert (~ trace_intact t1).
      { ii. eapply H7. erewrite <- tr_rel_intact; try eapply H1; eauto.
        i. destruct ev1, ev2; ss. }
      erewrite trace_cut_pterm_pterm_app; eauto. instantiate (1:=t3).
      eapply tr_rel_app; eauto.
      - eapply tr_rel_cut_pterm; eauto.
        { i. destruct ev1, ev2; ss. }
      - eapply tr_rel_refl. eapply ev_rel_refl. }
    assert (trace_intact t1).
    { clear - H1 H7. erewrite tr_rel_intact; eauto. i. destruct ev1, ev2; ss. }
    hexploit IHstar; eauto.
    { ii. eapply PTERM. eapply trace_intact_app; auto. }
    { i.
      specialize (H3 (t ** t0)). hexploit H3; eauto.
      { eapply tr_rel_app; eauto. }
      rewrite trace_cut_pterm_intact_app; auto. i.
      eapply star_safe_along; cycle 2; eauto.
      rewrite <- behavior_app_assoc. eauto. }
    i. des. esplits.
    { eapply star_trans; eauto. }
    rewrite trace_cut_pterm_intact_app; auto.
    erewrite Eapp_assoc. eapply tr_rel_app; eauto.
Qed.

Lemma backward_simulation_forever_silent:
  forall i s1 s2,
  Forever_silent L2 s2 -> match_states i s1 s2 -> safe L1 s1 ->
  Forever_silent L1 s1.
Proof.
  assert (forall i s1 s2,
         Forever_silent L2 s2 -> match_states i s1 s2 -> safe L1 s1 ->
         forever_silent_N (step L1) order (globalenv L1) i s1).
  { i. (* eapply forever_silent_forever_silent2 in H. *) eapply forever_silent_N2_forever_silent_N.
    revert_until match_states. pcofix CIH. i.
    inv H0. punfold H1. inv H1. specialize (STEP H2). inv STEP; clarify.
    exploit STEP0; eauto. i. inv H0; cycle 1.
    { des_safe. exfalso. eapply PTERM. ii. clarify. }
    destruct H1 as [st_src1 [tr [i1 [TRREL [OSTAR MATCH]]]]].
    pclearbot. inv TRREL. inv OSTAR.
    - r in H0. pfold. econs 2; eauto. right. eapply CIH; cycle 1; eauto.
      eapply star_safe; eauto. eapply plus_star; eauto.
    - des_safe. pfold. econs; eauto. right. eapply CIH; cycle 1; eauto.
      eapply star_safe; eauto. }
  intros. eapply forever_silent_N_forever; eauto. eapply NOSTUTTER.bsim_order_wf; eauto.
Qed.

CoFixpoint trinf_fix {X} (f:X -> (event * X)) (x: X) : traceinf :=
  let '(e,x') := f x in Econsinf e (trinf_fix f x').

Lemma trinf_unfold
    (tr: traceinf):
  tr = match tr with Econsinf e tr' => Econsinf e tr' end.
Proof.
  destruct tr; ss.
Qed.

Lemma trinf_fix_unfold
    X (f:X -> (event * X)) (x: X):
  trinf_fix f x = let '(e,x') := f x in Econsinf e (trinf_fix f x').
Proof.
  rewrite trinf_unfold at 1. simpl. des_ifs.
Qed.

Definition _trinf_fix_gen {X} f : trace * X -> event * (trace * X) :=
  fun '(tr,x) =>
    match tr with
    | [] => f x
    | e::tr' => (e,(tr',x))
    end.

Definition trinf_fix_gen {X} (f: X -> (event * (trace * X))) (x: X) : traceinf :=
  trinf_fix (_trinf_fix_gen f) ([],x).

Lemma trinf_fix_gen_unfold X f x:
  @trinf_fix_gen X f x
  = let '(e, (tr, x')) := f x in (e::tr) *** trinf_fix_gen f x'.
Proof.
  unfold trinf_fix_gen.
  rewrite trinf_fix_unfold at 1. unfold _trinf_fix_gen at 1.
  destruct (f x) as [e [tr x']]. clear x.
  ss. f_equal.
  induction tr; eauto.
  ss. rewrite trinf_fix_unfold at 1. ss.
  f_equal. eauto.
Qed.

Variant _trinf_clos {X} (R: X -> trace -> X -> Prop) (trinf_clos: X -> traceinf -> Prop) : X -> traceinf -> Prop :=
| trinf_clos_intro
    tr inf x x'
    (REL: R x tr x')
    (INF: trinf_clos x' inf):
  _trinf_clos R trinf_clos x (tr *** inf).

Definition trinf_clos {X} R x inf := paco2 (@_trinf_clos X R) bot2 x inf.

Lemma trinf_clos_mon X R:
  monotone2 (@_trinf_clos X R).
Proof. ii. inv IN; econs; eauto. Qed.

Hint Unfold trinf_clos.
Hint Resolve trinf_clos_mon: paco.

Definition non_E0 {X} (R: X -> trace -> X -> Prop) :=
  fun x tr x' => tr <> E0 /\ R x tr x'.

Definition _trinf_clos_coind X (R: X -> trace -> X -> Prop) (STEP: forall x, exists tr x', non_E0 R x tr x') (x: X) : event * (trace * X).
Proof.
  specialize (STEP x). rename STEP into e.
  repeat (eapply constructive_indefinite_description in e; destruct e). destruct n.
  destruct x0.
  { exfalso. apply H. eauto. }
  exact (e, (x0, x1)).
Defined.

Lemma trinf_clos_coind {X} (R: X -> trace -> X -> Prop)
    (STEP: forall x, exists tr x', non_E0 R x tr x') x:
  exists inf: traceinf, trinf_clos (non_E0 R) x inf.
Proof.
  exists (trinf_fix_gen (_trinf_clos_coind STEP) x).
  revert x. pcofix CIH. i.
  rewrite trinf_fix_gen_unfold.
  unfold _trinf_clos_coind at 1.
  repeat (destruct (constructive_indefinite_description _ _); des).
  destruct n, x0.
  { exfalso. apply n. eauto. }
  pstep. econs; cycle 1; rr; eauto with paco.
Qed.

Definition bsfr_state : Type :=
  { '(i,s1,s2,T2) |
    match_states i s1 s2 /\
    Forever_reactive L2 s2 T2 /\
    forall T1, trinf_rel (ev_rel pim) T1 T2 -> safe_along_behavior s1 (Reacts T1) }.

Definition bsfr: bsfr_state -> trace -> bsfr_state -> Prop :=
  fun '(exist (i,s1,s2,T2) _) tr1 '(exist (i',s1',s2',T2') _) =>
    exists tr2,
    T2 = tr2 *** T2' /\
    tr_rel (ev_rel pim) tr1 tr2 /\
    trace_intact tr1 /\ Star L1 s1 tr1 s1'.
         
Lemma backward_simulation_forever_reactive_step
    (x: bsfr_state):
  exists tr1 x', non_E0 bsfr x tr1 x'.
Proof.
  cut (exists tr1 i' s1' s2' T2', tr1 <> E0 /\
       exists PF, bsfr x tr1 (exist _ (i',s1',s2',T2') PF)).
  { i. des. unfold non_E0. esplits; eauto. }
  destruct x as [[[[i s1] s2] T2] [MATCH [REACT SAFE]]]. simpl.
  inv REACT. hexploit backward_simulation_star; eauto.
  { i. specialize (SAFE (t0 *** T)). hexploit SAFE; i.
    { eapply trinf_rel_app; eauto. eapply trinf_rel_refl. }
    instantiate (1:=Reacts T). ss. }
  i. des.
  assert (t0 <> E0).
  { destruct t0; ss. inv H2. clarify. }
  esplits; eauto.
  { i. specialize (SAFE (t0 *** T1)).
    hexploit SAFE; i.
    { eapply trinf_rel_app; eauto. }
    eapply star_safe_along; try eapply H3; eauto.
    { erewrite <- tr_rel_intact; eauto. ii. destruct ev1, ev2; ss. } }
  erewrite <- tr_rel_intact; eauto. ii. destruct ev1, ev2; ss.
Qed.

Lemma backward_simulation_forever_reactive
    i s1 s2 T2
    (MATCH: match_states i s1 s2)
    (REACT: Forever_reactive L2 s2 T2)
    (SAFE: forall T1, trinf_rel (ev_rel pim) T1 T2 -> safe_along_behavior s1 (Reacts T1)) :
  exists T1, trinf_rel (ev_rel pim) T1 T2 /\ Forever_reactive L1 s1 T1.
Proof.
  assert (INF:= trinf_clos_coind backward_simulation_forever_reactive_step
                (exist _ (i,s1,s2,T2) (conj MATCH (conj REACT SAFE)))).
  des. exists inf. split.
  { revert_until match_states. pcofix CIH. i.
    punfold INF. inv INF. destruct REL as [NE REL].
    destruct x' as [[[[i' s1'] s2'] T2'] [MATCH' [REACT' SAFE']]].
    ss. pclearbot. des. subst.
    clear i s1 s2 MATCH SAFE REACT REL1 REL2.
    move tr before CIH. revert_until tr. induction tr; i.
    { exfalso. apply NE. eauto. }
    inv REL0. pstep. s. econs; eauto.
    destruct tr; inv H3; eauto.
    left. eapply IHtr; ii; ss; eauto.
    econs; eauto. }
  { eapply forever_reactive2_forever_reactive.
    revert_until match_states. pcofix CIH. i.
    punfold INF. inv INF. destruct REL as [NE REL].
    destruct x' as [[[[i' s1'] s2'] T2'] [MATCH' [REACT' SAFE']]].
    ss. pclearbot. des. subst.
    pstep. econs. esplits; eauto. }
Qed.

Lemma backward_simulation_state_behaves:
  forall i s1 s2 beh2,
  match_states i s1 s2 -> state_behaves L2 s2 beh2 ->
  exists pim1 beh1, state_behaves L1 s1 beh1 /\ observation_improves (Some pim1, beh1) (Some pim, beh2).
Proof.
  intros. destruct (classic (forall beh1, behav_rel pim beh1 beh2 -> (safe_along_behavior s1 (behavior_app E0 beh1)))).
(* 1. Safe along *)  
- pose (beh2_ := beh2).
  inv H0.
  (* termination *)
  + exploit backward_simulation_star; eauto.
    { instantiate (1:= Terminates E0 r). i. specialize (H1 (behavior_app t0 (Terminates E0 r))).
      hexploit H1.
      { r. ss. esplits; eauto. traceEq. }
      i. ss. }
    i. des. hexploit match_states_final; eauto.
    { eapply safe_along_safe. eapply star_safe_along; try eapply H4; eauto.
      - erewrite <- tr_rel_intact; eauto. i. destruct ev1, ev2; ss.
      - instantiate (1:= Terminates E0 r).
        specialize (H1 (Terminates t0 r)). hexploit H1; eauto.
        { r. ss. }
        i; ss. traceEq. }
    i. des. subst. exists pim. exists (Terminates t0 r). splits.
    2:{ rr. ss. esplits; eauto. econs; eauto. ss. rr. eauto. }
    econs; try eapply FINAL.
    2:{ eapply star_trans; eauto. traceEq. }
    erewrite <- tr_rel_intact; eauto. i. destruct ev1, ev2; ss.
  (* partial termination *)
  + exploit backward_simulation_star_pterm; eauto.
    { instantiate (1:= Partial_terminates E0).
      i. specialize (H1 (Partial_terminates (trace_cut_pterm t0))).
      hexploit H1; eauto.
      { r. eapply tr_rel_cut_pterm; eauto. i. destruct ev1, ev2; ss. }
      ss. traceEq. }
    i. des. generalize (state_behaves_exists L1 s1'); intro T. des.
    destruct (classic (trace_intact tl)).
    * exists pim. exists (behavior_app t0 beh). esplits; eauto.
      { eapply state_behaves_app; eauto.
        erewrite <- tr_rel_intact; cycle 2; eauto.
        2:{ i. destruct ev1, ev2; ss. }
        eapply trace_intact_app; eauto. eapply trace_cut_pterm_intact. }
      r. ss. split; ii; ss. right. right.
      exploit tr_rel_div_r; eauto. i. des. subst.
      exists (trace_cut_pterm t). exists t1'. esplits; eauto. erewrite behavior_app_assoc; eauto.
      r. esplits; eauto.
    * exists pim. exists (Partial_terminates (trace_cut_pterm t0)). esplits.
      { econs; eauto. ii. eapply H0. erewrite <- tr_rel_intact in H2; cycle 2.
        { eauto. }
        2:{ ii. destruct ev1, ev2; ss. }
        eapply trace_intact_app_rev in H2. des; eauto. }
      r. ss. esplits; ii; ss. r. right. right.
      exploit tr_rel_div_r; eauto. i. des. subst.
      exists (trace_cut_pterm t). exists t1'. esplits; eauto.
      erewrite trace_cut_pterm_intact_app.
      2:{ erewrite <- tr_rel_intact; eauto.
          - eapply trace_cut_pterm_intact.
          - ii. destruct ev1, ev2; ss. }
      r. exists (Partial_terminates (trace_cut_pterm t2')). ss.
  (* diverges *)
  + exploit backward_simulation_star; eauto.
    { instantiate (1:= Diverges E0). i. specialize (H1 (behavior_app t0 (Diverges E0))).
      hexploit H1.
      { r. ss. esplits; eauto. traceEq. }
      i. ss. }
    i. des. exploit backward_simulation_forever_silent; eauto.
    { specialize (H1 (Diverges t0)). hexploit H1; eauto.
      i. ss. eapply safe_along_safe. eapply star_safe_along; try eapply H4; eauto.
      - erewrite <- tr_rel_intact; eauto. ii. destruct ev1, ev2; ss.
      - instantiate (1:= Diverges E0). ss. traceEq. }
    i. exists pim. exists (Diverges t0). esplits; eauto.
    2:{ r. ss. split; ii; eauto. econs. ss. }
    econs; eauto. erewrite <- tr_rel_intact; eauto. ii. destruct ev1, ev2; ss.
  (* reacts *)
  + exploit backward_simulation_forever_reactive; eauto.
    { i. specialize (H1 (Reacts T1)). ss. eapply H1; eauto. }
    i. des. exists pim. exists (Reacts T1). esplits; eauto.
    2:{ econs; eauto; ss. r. ss. left. eauto. }
    econs; eauto.
  (* goes wrong *)
  + exploit backward_simulation_star; eauto.
    { instantiate (1:= Goes_wrong E0). i. specialize (H1 (behavior_app t0 (Goes_wrong E0))).
      hexploit H1.
      { r. ss. esplits; eauto. traceEq. }
      i. ss. }
    i. des. exploit match_states_progress; eauto.
    { specialize (H1 (Goes_wrong t0)).
      hexploit H1; eauto. i. ss.
      hexploit star_safe_along; try eapply H5; eauto; cycle 1.
      { instantiate (1:= Goes_wrong E0). ss. traceEq. }
      { i. eapply safe_along_safe; eauto. }
      erewrite <- tr_rel_intact; eauto. ii. destruct ev1, ev2; ss. }
    i. des.
    * eapply H4 in FINAL. clarify.
    * exfalso. eapply H3. eauto.
(* 2. Not safe along *)      
- eapply not_all_ex_not in H1. des. eapply imply_to_and in H1. des.
  rewrite behavior_app_E0 in *.
  exploit not_safe_along_behavior; eauto.
  intros [t [s1' [INTACT [PREF [STEPS [NOSTEP NOFIN]]]]]].
  exists pim. exists (Goes_wrong t); split.
  econstructor; eauto.
  r. split; [|ss].
  + right. left. ss.
    assert (exists t', tr_rel (ev_rel pim) t t' /\ behavior_prefix t' beh2).
    { eapply prefix_tr_rel; eauto. }
    des. exists t; exists t'; auto.
Qed.

End BACKWARD_SIMULATIONS.

Theorem backward_simulation_observation_improves:
  forall L1 L2, NOSTUTTER.backward_simulation L1 L2 ->
  forall obs2, program_observes L2 obs2 ->
  exists obs1, program_observes L1 obs1 /\ observation_improves obs1 obs2.
Proof.
  intros L1 L2 S obs2 H. destruct S as [index order S]. inv H.
- (* L2's initial state is defined. *)
  destruct (classic (exists s1, initial_state L1 s1)) as [[s1 INIT] | NOINIT].
+ (* L1's initial state is defined too. *)
  exploit (NOSTUTTER.bsim_match_initial_states S); eauto. i. des.
  exploit backward_simulation_state_behaves; eauto.
  i. des. esplits.
  { econs; eauto. }
  r. ss. inv H2. split; eauto.
+ (* L1 has no initial state *)
  exists (Some (fun _ => None), Goes_wrong E0); split.
  apply program_goes_initially_wrong.
  intros; red; intros. elim NOINIT; exists s0; auto.
  eapply observation_improves_bot. r. i; clarify.
- (* L2 has no initial state *)
  exists (Some (fun _ => None), Goes_wrong E0); split.
  apply program_goes_initially_wrong.
  intros; red; intros.
  exploit (NOSTUTTER.bsim_initial_states_exist S); eauto. intros [s2 INIT2].
  elim (H0 s2); auto.
  eapply observation_improves_refl.
- (* L2 has no captured initial state *)
  specialize (program_observes_exists L1). i. des.
  (* exists (None, Partial_terminates E0); split. *)
  (* eapply program_goes_initially_capture_wrong; eauto. *)
  exists obs. esplits; eauto.
  r. ss. split; auto. r. des_ifs.
Qed.

Set Implicit Arguments.

(** * Big-step semantics and program behaviors *)

Section BIGSTEP_BEHAVIORS.

Variable B: bigstep_semantics.
Variable L: semantics.
Hypothesis sound: bigstep_sound B L.

(* Lemma behavior_bigstep_terminates: *)
(*   forall t r, *)
(*   bigstep_terminates B t r -> program_behaves L (Terminates t r). *)
(* Proof. *)
(*   (* intros. exploit (bigstep_terminates_sound sound); eauto. *) *)
(*   (* intros [s1 [s2 [P [Q [R INTACT]]]]]. *) *)
(*   (* econstructor; eauto. econstructor; eauto. *) *)
(* Qed. *)

(* Lemma behavior_bigstep_diverges: *)
(*   forall T, *)
(*   bigstep_diverges B T -> *)
(*   program_behaves L (Reacts T) *)
(*   \/ exists t, program_behaves L (Diverges t) /\ traceinf_prefix t T. *)
(* Proof. *)
(*   intros. exploit (bigstep_diverges_sound sound); eauto. intros [s1 [P Q]]. *)
(*   (* exploit forever_silent_or_reactive; eauto. intros [X | [t [s' [T' [X [Y [Z INTACT]]]]]]]. *) *)
(*   (* left. econstructor; eauto. constructor; auto. *) *)
(*   (* right. exists t; split. econstructor; eauto. econstructor; eauto. exists T'; auto. *) *)
(* Qed. *)

End BIGSTEP_BEHAVIORS.
