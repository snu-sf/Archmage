Require Import ModSem.
Require Import Skeleton.
Require Import ClightPlusgen.
Require Import xorlist.
Require Import main.
From compcert Require Import Linking.

Definition _xor : option Clight.program := link main.prog xorlist.prog.

Definition xor : Errors.res Mod.t :=
    match _xor with
    | Some xor => compile xor "xorlist"
    | None => Errors.Error [Errors.MSG "no link"]
    end.

Definition xor_sk : Sk.t :=
  match xor with
  | Errors.OK md => md.(Mod.sk)
  | Errors.Error _ => Sk.unit
  end.

Definition _msk : Errors.res Sk.t :=
    match _xor with
    | Some xor => mem_skel xor
    | None => Errors.Error [Errors.MSG "no link"]
    end.

Theorem msk_xor: exists msk, _msk = Errors.OK msk.
Proof.
  unfold _msk, _xor.
  eassert (link prog xorlist.prog = _).
  { vm_compute (link _ _). eauto. }
  rewrite H. clear H. destruct Ctypes.link_build_composite_env. destruct a.
  vm_compute (mem_skel _). eauto.
Qed.

Theorem valid_xor: exists p, xor = Errors.OK p.
Proof.
  unfold xor, _xor.
  eassert (link prog xorlist.prog = _).
  { vm_compute (link _ _). eauto. }
  rewrite H. clear H. destruct Ctypes.link_build_composite_env. destruct a. eauto.
Qed.

