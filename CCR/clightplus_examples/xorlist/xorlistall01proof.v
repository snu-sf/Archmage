Require Import CoqlibCCR.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import SimModSem.
Require Import PCM.
Require Import HoareDef.
Require Import STB.
Require Import ClightPlusSkel ClightPlusExprgen ClightPlusgen.
Require Import ClightPlusMemRA ClightPlusMem0 ClightPlusMem1 ClightPlusMemAux.
Require Import CProofMode CIProofMode.
Require Import xorlist.
Require Import xorlistall0.
Require Import xorlistall1.
Require Import xorlist1.
Require Import PtrofsArith.
From Coq Require Import Program.
From compcert Require Import Clightdefs.

Require Import ClightPlusMem01Proof.
Require Import xorlist01proof.
Require Import main01proof.

Section PROOF.

  Import ClightPlusMem1.

  Context `{@GRA.inG Mem.t Σ}.

  Variable GlobalStb : Sk.t -> gname -> option fspec.
  Hypothesis MEMINCL : forall sk, stb_incl (to_stb MemStb) (GlobalStb sk).
  Hypothesis STBINCL : forall sk, stb_incl (to_stb xorStb) (GlobalStb sk).

  Variable xorlink : Clight.program.
  Variable xormod : Mod.t.
  Hypothesis VALID_link : xorlistall0._xor = Some xorlink.
  Hypothesis VALID_comp : compile xorlink "xorlist" = Errors.OK xormod.
  Let mfsk : Sk.t := [("malloc", Gfun (F:=Clight.fundef) (V:=type) (Ctypes.External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)); ("free", Gfun (Ctypes.External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default))].

  Theorem correct : refines2 [ClightPlusMem0.Mem mfsk; xormod] [ClightPlusMem1.Mem mfsk; xorlistall1.xorAllWrapped GlobalStb].
  Proof.
    eapply adequacy_local_strong_l. econs; cycle 1.
    { simpl map. econs; [econs; refl|].
      unfold xor_sk, xor. rewrite VALID_link. rewrite VALID_comp. et. }
    i. econs.
    { apply correct_mod; et. inv SKINCL. inv H3. ss. }
    econs; [|ss].
    hexploit sim_delete_tl; et. { inv SKINCL. inv H3. et. } i. rename H0 into sim_delete_tl.
    hexploit sim_delete_hd; et. { inv SKINCL. inv H3. et. } i. rename H0 into sim_delete_hd.
    hexploit sim_add_hd; et. { inv SKINCL. inv H3. et. } i. rename H0 into sim_add_hd.
    hexploit sim_add_tl; et. { inv SKINCL. inv H3. et. } i. rename H0 into sim_add_tl.
    hexploit sim_main; et. { inv SKINCL. inv H3. et. } { inv SKINCL. et. }  i. rename H0 into sim_main.
    eassert (_xor = _).
    { unfold _xor. vm_compute (Linking.link _ _). reflexivity. }
    rewrite H0 in *. clear H0. destruct Ctypes.link_build_composite_env. destruct a.
    inversion VALID_link. clear VALID_link. subst.
    clear a.
    set (compile _ _) in VALID_comp.
    eassert (r = Errors.OK _).
    { reflexivity. }
    rewrite H0 in *. clear r H0.
    inversion VALID_comp. clear VALID_comp. subst. ss.
    econstructor 1 with (wf := xorlist01proof.wf) (le := top2); et; ss; cycle 1.
    { eexists. econs. apply to_semantic. iIntros. et. }
    (* each functions has simulation relation *)
    unfold get_ce. simpl prog_comp_env.
    econs. { apply sim_add_hd. }
    econs. { apply sim_add_tl. }
    econs. { apply sim_main. }
    econs. { apply sim_delete_hd. }
    econs. { apply sim_delete_tl. }
    econs.
    Unshelve. exact tt.
  Qed.

End PROOF.