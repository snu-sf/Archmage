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
Require Import xorlistall0.
Require Import xorlist1.
Require Import main1.
(* From compcert Require Export Ctypes Values AST Memdata Integers. *)

Set Implicit Arguments.
Section SMOD.

  Context `{@GRA.inG Mem.t Σ}.

  Definition SxorAllSem : SModSem.t := {|
    SModSem.fnsems := firstn 2 xorlist1.xorSbtb ++ main1.mainSbtb ++ drop 2 xorlist1.xorSbtb ;
    SModSem.mn := "xorlist";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}.

  Definition SxorAll : SMod.t := {|
    SMod.get_modsem := fun _ => SxorAllSem;
    SMod.sk := xor_sk;
  |}.

  Definition xorAllWrapped stb : Mod.t := (SMod.to_tgt stb) SxorAll.

  Definition xorAll : Mod.t := SMod.to_src SxorAll.

End SMOD.
