Require Import ModSem.
Require Import Skeleton.
Require Import ClightPlusgen.
Require Import hardening.
(* Require Import main. *)
(* From compcert Require Import Linking. *)

Definition _hardening : Clight.program := hardening.prog.

Definition hardening : Errors.res Mod.t :=
  compile _hardening "hardening".

Definition hardening_sk : Sk.t :=
  match hardening with
  | Errors.OK md => md.(Mod.sk)
  | Errors.Error _ => Sk.unit
  end.

Definition _msk : Errors.res Sk.t :=
  mem_skel _hardening.

Theorem msk_hardening: exists msk, _msk = Errors.OK msk.
Proof.
  unfold _msk, _hardening. vm_compute (mem_skel _). eauto.
Qed.

Theorem valid_hardening: exists p, hardening = Errors.OK p.
Proof.
  unfold hardening, _hardening. unfold prog. eauto.
Qed.
