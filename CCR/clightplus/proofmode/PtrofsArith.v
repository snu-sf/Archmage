Require Import CoqlibCCR.
Require Import ProofMode.
From Coq Require Import Program.
From compcert Require Import Values Integers Clightdefs.

  Lemma ptrofs_max : Archi.ptr64 = true -> Int64.max_unsigned = Ptrofs.max_unsigned.
  Proof. des_ifs_safe. Qed.

  Lemma mkint64_eq' x y : Int64.unsigned x = Int64.unsigned y -> x = y.
  Proof. i. destruct x. destruct y. apply Int64.mkint_eq. et. Qed.

  Local Open Scope Z_scope.

  Lemma lxor_size a b
    :
      0 ≤ a ≤ Ptrofs.max_unsigned
      -> 0 ≤ b ≤ Ptrofs.max_unsigned
      -> 0 ≤ Z.lxor a b ≤ Ptrofs.max_unsigned.
  Proof.
    i. change Ptrofs.max_unsigned with (2 ^ 64 - 1) in *.
    assert (I1: 0 ≤ a < 2 ^ 64) by nia.
    assert (I2: 0 ≤ b < 2 ^ 64) by nia.
    assert (0 ≤ Z.lxor a b < 2 ^ 64); try nia.
    destruct (Coqlib.zeq a 0);
    destruct (Coqlib.zeq b 0); clarify.
    2: split.
    - rewrite Z.lxor_0_r. nia.
    - rewrite Z.lxor_nonneg. nia.
    - des.
      rewrite Z.log2_lt_pow2 in I3; try nia.
      rewrite Z.log2_lt_pow2 in I0; try nia.
      destruct (Coqlib.zeq (Z.lxor a b) 0); try nia.
      rewrite Z.log2_lt_pow2; cycle 1.
      + assert (0 ≤ Z.lxor a b); try nia. rewrite Z.lxor_nonneg. nia.
      + eapply Z.le_lt_trans; try apply Z.log2_lxor; try nia.
  Qed.

  Lemma int64_ptrofs_xor_comm p1 p2 : Int64.xor (Ptrofs.to_int64 p1) (Ptrofs.to_int64 p2) = Ptrofs.to_int64 (Ptrofs.xor p1 p2).
  Proof.
    i. unfold Ptrofs.to_int64, Ptrofs.xor, Int64.xor.
    do 2 try rewrite Int64.unsigned_repr.
    2,3: change Int64.max_unsigned with Ptrofs.max_unsigned; apply Ptrofs.unsigned_range_2.
    rewrite Ptrofs.unsigned_repr; et.
    apply lxor_size; apply Ptrofs.unsigned_range_2.
  Qed.

Create HintDb ptrArith.

Hint Unfold Vptrofs Int64.xor Ptrofs.to_int64 : ptrArith.
Hint Rewrite ptrofs_max Ptrofs.unsigned_repr Int64.unsigned_repr : ptrArith.
Hint Resolve Ptrofs.unsigned_range_2 : ptrArith.