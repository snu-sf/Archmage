Require Import CoqlibCCR.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import Any.
Require Import ModSem.
Require Import ModSemE.
Require Import ClightPlusMemRA.
Require Import ClightPlusMem1.
From compcert Require Export Ctypes Values AST Memdata Integers.

Set Implicit Arguments.

Section SPEC.

  Context `{@GRA.inG Mem.t Σ}.

  Definition main_body : list val -> itree hEs val :=
    fun _ => ;;;Ret (Vint (Int.repr 21)).

  Definition main_spec : fspec :=
    (mk_simple
      (fun '() => (
        (ord_top),
        (fun varg => ⌜varg = (@nil val)↑⌝ ** Vnullptr (≃_m_null) Vnullptr),
        (fun _ => ⌜True⌝)
    )))%I.

End SPEC.


Section SMOD.

  Context `{@GRA.inG Mem.t Σ}.

  Definition mainSbtb: list (gname * fspecbody) :=
    [("main", mk_specbody main_spec (cfunU main_body))].

End SMOD.