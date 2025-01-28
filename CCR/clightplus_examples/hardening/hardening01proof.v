Require Import CoqlibCCR.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import SimModSem.
Require Import PCM.
Require Import HoareDef.
Require Import STB.
Require Import HTactics ProofMode.
Require Import HSim IProofMode.
Require Import ClightPlusSkel ClightPlusExprgen ClightPlusgen.
Require Import ClightPlusMemRA ClightPlusMem0 ClightPlusMem1 ClightPlusMemAux.
Require Import CProofMode CIProofMode.
Require Import hardening.
Require Import hardening0.
Require Import hardening1.

(* Require Import xorlist. *)
(* Require Import xorlistall0. *)
(* Require Import xorlist1. *)
Require Import PtrofsArith.
From Coq Require Import Program.
From compcert Require Import Memory Clightdefs.


Section LEMMA.

  Lemma f_bind_ret_r E R A (s : A -> itree E R)
    : (fun a => ` x : R <- (s a);; Ret x) = s.
  Proof. apply func_ext. i. apply bind_ret_r. Qed.

  Lemma decode_encode_ofs i : decode_val Mint64 (encode_val Mint64 (Vptrofs i)) = Vptrofs i.
  Proof.
    pose proof (decode_encode_val_general (Vptrofs i) Mint64 Mint64).
    unfold Vptrofs in *. des_ifs.
  Qed.

  Lemma decode_encode_item i : decode_val Mint64 (encode_val Mint64 (Vlong i)) = Vlong i.
  Proof. apply (decode_encode_val_general (Vlong i) Mint64 Mint64). Qed.

  Lemma decode_encode_null : decode_val Mint64 (encode_val Mint64 Vnullptr) = Vnullptr.
  Proof. rewrite (decode_encode_val_general Vnullptr Mint64 Mint64). et. Qed.

  Lemma null_zero i : Vptrofs i = Vnullptr -> i = Ptrofs.zero.
  Proof.
    unfold Vptrofs, Vnullptr. des_ifs. i.
    apply (f_equal (fun v: val => match v with Vlong i => i | _ => Int64.zero end)) in H.
    rewrite <- (Ptrofs.of_int64_to_int64 Heq i). rewrite H. et.
  Qed.

  Context `{eventE -< eff}.

  Lemma cast_ptrofs i : cast_to_ptr (Vptrofs i) = Ret (Vptrofs i).
  Proof. des_ifs. Qed.

  Lemma cast_long i : Archi.ptr64 = true -> cast_to_ptr (Vlong i) = Ret (Vlong i).
  Proof. ss. Qed.

End LEMMA.

Section PROOF.

  Import ClightPlusMem1.

  Context `{@GRA.inG Mem.t Σ}.

  Variable GlobalStb : Sk.t -> gname -> option fspec.
  Hypothesis STBINCL : forall sk, stb_incl (to_stb hardeningStb) (GlobalStb sk).
  Hypothesis MEMINCL : forall sk, stb_incl (to_stb MemStb) (GlobalStb sk).


  Definition wf : _ -> Any.t * Any.t -> Prop :=
    @mk_wf
      _
      unit
      (fun _ st_src st_tgt => ⌜True⌝)%I.

  Let mfsk : Sk.t := [("malloc", Gfun (F:=Clight.fundef) (V:=type) (Ctypes.External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)); ("free", Gfun (Ctypes.External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default))].

  Section SIMFUNS.
  Variable hardening_mod : Mod.t.
  (* Hypothesis VALID_link : xorlistall0._xor = Some xorlink. *)
  Hypothesis VALID: hardening = Errors.OK hardening_mod.
  Let ce := Maps.PTree.elements (prog_comp_env prog).

  Variable sk: Sk.t.
  (* TODO: How to encapsulate fuction info? *)
  Hypothesis SKINCL : Sk.le (hardening_mod.(Mod.sk)) sk.
  Hypothesis SKWF : Sk.wf sk.

  Ltac unfold_comp optsrc EQ :=
    unfold optsrc, compile, get_sk in EQ;
    destruct Coqlib.list_norepet_dec; clarify; des_ifs; ss;
    repeat match goal with
          | H: Coqlib.list_norepet _ |- _ => clear H
          | H: forallb _ _ = true |- _ => clear H
          | H: forallb _ _ && _ = true |- _ => clear H
          | H: Ctypes.prog_main _ = _ |- _ => clear H
          end.

  Lemma encode_sim:
    sim_fnsem wf top2
      ("encode", fun_to_tgt "hardening" (GlobalStb sk) (mk_pure encode_spec))
      ("encode", cfunU (decomp_func sk ce f_encode)).
  Proof.
    Local Opaque encode_val.
    Local Opaque cast_to_ptr.
    unfold_comp hardening VALID.
    econs; ss. red.

    (* get_composite ce e. *)
    dup SKINCL. rename SKINCL0 into SKINCLENV.
    apply incl_incl_env in SKINCLENV.
    unfold incl_env in SKINCLENV.
    pose proof sk_incl_gd as SKINCLGD.

    apply isim_fun_to_tgt; auto.
    unfold f_encode. i; ss.
    unfold decomp_func, function_entry_c. ss.

    let H := fresh "HIDDEN" in
    set (H := hide 1).
    
    iIntros "[INV PRE]". des_ifs_safe. ss.
    iDestruct "PRE" as "[[% PRE] %]".
    des. clarify. hred_r.

    rename i0 into iptr, v into ptr.

    unhide. remove_tau. unhide. remove_tau. unhide. remove_tau.

    iPoseProof ((@live_cast_ptr_ofs _ _ Es) with "PRE") as "#->".

    hred_r.

    iApply isim_apc. iExists (Some (20%nat : Ord.t)).

    iApply isim_ccallU_capture1; ss; oauto.
    iSplitL "INV PRE".
    { iFrame. }
    iIntros (st_src5 st_tgt5 i0) "[INV [LIVE RELT]]".

    hred_r. remove_tau. unhide. des_ifs. hred_r. remove_tau.
    rewrite ptrofs_cast_ptr. hred_r. rewrite cast_long; eauto.
    hred_r. unfold Vptrofs. des_ifs_safe.
    hred_r. remove_tau. unhide. remove_tau.
    rewrite cast_long; eauto.
    hred_r. hred_l. hred_l.
    iApply isim_choose_src.

    iExists _. iApply isim_ret.
    iSplitR "INV LIVE RELT".
    { ss. }

    iFrame. iSplit; ss.
    iExists (Ptrofs.to_int64 i0). iFrame. unfold Val.xorl. ss.
  Qed.
    
  Lemma decode_sim:
    sim_fnsem wf top2
      ("decode", fun_to_tgt "hardening" (GlobalStb sk) (mk_pure decode_spec))
      ("decode", cfunU (decomp_func sk ce f_decode)).
  Proof.
    Local Opaque encode_val.
    Local Opaque cast_to_ptr.
    unfold_comp hardening VALID.
    econs; ss. red.

    (* get_composite ce e. *)
    dup SKINCL. rename SKINCL0 into SKINCLENV.
    apply incl_incl_env in SKINCLENV.
    unfold incl_env in SKINCLENV.
    pose proof sk_incl_gd as SKINCLGD.

    apply isim_fun_to_tgt; auto.
    unfold f_decode. i; ss.
    unfold decomp_func, function_entry_c. ss.

    let H := fresh "HIDDEN" in
    set (H := hide 1).
    
    iIntros "[INV PRE]". des_ifs_safe. ss.
    iDestruct "PRE" as "[% %]".
    des. clarify. hred_r.

    unhide. remove_tau. unhide. remove_tau. des_ifs_safe.

    rewrite cast_long; eauto. rewrite cast_long; eauto.
    hred_r. rewrite cast_long; eauto. hred_r. remove_tau. unhide. remove_tau.
    rewrite cast_long; eauto. hred_r.
    iApply isim_apc. iExists (Some (0%nat : Ord.t)).
    hred_l.
    
    iApply isim_choose_src.
    iExists _. iApply isim_ret.
    iSplitL "INV".
    { ss. }
    esplits; eauto.
  Qed.

  Lemma bar_sim:
    sim_fnsem wf top2
      ("bar", fun_to_tgt "hardening" (GlobalStb sk) (mk_pure bar_spec))
      ("bar", cfunU (decomp_func sk ce f_bar)).
  Proof.
    Local Opaque encode_val.
    Local Opaque cast_to_ptr.
    unfold_comp hardening VALID.
    econs; ss. red.

    (* get_composite ce e. *)
    dup SKINCL. rename SKINCL0 into SKINCLENV.
    apply incl_incl_env in SKINCLENV.
    unfold incl_env in SKINCLENV.
    pose proof sk_incl_gd as SKINCLGD.

    apply isim_fun_to_tgt; auto.
    unfold f_bar. i; ss.
    unfold decomp_func, function_entry_c. ss.

    let H := fresh "HIDDEN" in
    set (H := hide 1).

    iIntros "[INV PRE]". des_ifs_safe. ss.
    iDestruct "PRE" as "[[[PRE'' PRE] PRE'] %]".
    iDestruct "PRE''" as "[[% %] RELT]".
    des. clarify. hred_r.

    unhide. remove_tau. unhide. remove_tau. unhide. remove_tau.

    exploit SKINCLENV.
    { instantiate (2:= "decode"). unfold _hardening, prog, mkprogram. des_ifs_safe. ss.
      right. left. eauto. }
    i. des. r in x0. rewrite x0. hred_r. des_ifs_safe.
    rewrite cast_long; eauto. rewrite cast_long; eauto. hred_r.
    replace (Init.Nat.pred (Pos.to_nat (Pos.of_succ_nat blk))) with blk by nia.

    exploit SKINCLGD; eauto.
    { unfold _hardening, prog, mkprogram. des_ifs_safe. ss.
      right. left. eauto. }
    i. rewrite x1. hred_r.

    iApply isim_apc. iExists (Some (20%nat : Ord.t)).
    iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. unfold hardeningStb. unseal "stb". ss. }
      { instantiate (1:=(_,_)). ss. eapply OrdArith.lt_from_nat. lia. }
      { ss. } }
    instantiate (1:=19). eapply Ord.S_lt. hred_r.

    iSplitR "PRE PRE' RELT".
    { iSplit; ss. }
    iIntros. des. clarify.
    iExists _. iSplitR "PRE PRE' RELT"; eauto.
    hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau. des_ifs_safe.
    hred_r.
    iPoseProof (live_has_offset_ofs with "PRE'") as "[PRE' PRE_ofs]".
    iApply isim_ccallU_load; ss; oauto.
    iPoseProof (equiv_dup with "RELT") as "RELT1".
    iDestruct "RELT1" as "[RELT RELT1]".
    iSplitL "PRE PRE_ofs RELT".
    { iSplitR "PRE PRE_ofs RELT"; ss. iExists _. iSplitL "PRE PRE_ofs RELT".
      { iPoseProof (equiv_dup with "RELT") as "RELT'".
        iDestruct "RELT'" as "[RELT1 RELT2]".
        iCombine "RELT1 PRE" as "PTO".
        iPoseProof (equiv_point_comm with "PTO") as "PTO'".
        iFrame. instantiate (1:=i). unfold Vptrofs. des_ifs_safe.
        iCombine "RELT2 PRE_ofs" as "LIVE".
        iPoseProof (_equiv_has_offset_comm with "LIVE") as "LIVE". iFrame. }
      iSplits; eauto. }

    iIntros (st_src1 st_tgt1) "[INV PRE]". unfold Vptrofs. des_ifs_safe.
    hred_r. rewrite decode_encode_item. rewrite cast_long; eauto. hred_r.
    hred_l.
    iApply isim_choose_src.

    iExists _. iApply isim_ret.
    iFrame.
    iPoseProof (equiv_dup with "RELT1") as "RELT1".
    iDestruct "RELT1" as "[RELT RELT1]".
    iSplitL "PRE RELT RELT1"; eauto.
    iSplitR "PRE RELT1"; eauto.
    iPoseProof (equiv_sym with "RELT1") as "RELT1".
    iCombine "RELT1 PRE" as "PRE".
    iPoseProof (equiv_point_comm with "PRE") as "PRE". eauto.
  Qed.

  Ltac ord_tac := eapply OrdArith.lt_from_nat; eapply Nat.lt_succ_diag_r.
  
  Lemma foo_sim:
    sim_fnsem wf top2
      ("foo", fun_to_tgt "hardening" (GlobalStb sk) (mk_pure foo_spec))
      ("foo", cfunU (decomp_func sk ce f_foo)).
  Proof.
    Local Opaque encode_val.
    Local Opaque cast_to_ptr.
    unfold_comp hardening VALID.
    econs; ss. red.

    (* get_composite ce e. *)
    dup SKINCL. rename SKINCL0 into SKINCLENV.
    apply incl_incl_env in SKINCLENV.
    unfold incl_env in SKINCLENV.
    pose proof sk_incl_gd as SKINCLGD.

    apply isim_fun_to_tgt; auto.
    unfold f_foo. i; ss.
    unfold decomp_func, function_entry_c. ss.

    let H := fresh "HIDDEN" in
    set (H := hide 1).

    iIntros "[INV PRE]". des_ifs_safe. ss.
    
    iDestruct "PRE" as "[PRE %]".
    iDestruct "PRE" as (v0) "[PRE PRE']".
    iDestruct "PRE" as "[[% %] PRE]".

    des. clarify. hred_r.

    unhide. remove_tau. unhide. remove_tau. unhide. remove_tau.
    iPoseProof (points_to_is_ptr with "PRE") as "#->".
    hred_r.
    iApply isim_apc. iExists (Some (40%nat : Ord.t)).
    iPoseProof (live_has_offset_ofs with "PRE'") as "[PRE' PRE_ofs]".
    iApply isim_ccallU_store; ss; oauto.
    iSplitL "PRE PRE_ofs".
    { iSplitR "PRE PRE_ofs"; ss.
      iExists (encode_val Mint64 v0). 
      iFrame. iSplits; ss. destruct v0; ss. }
    iIntros (st_src1 st_tgt1) "[INV' PRE]". unfold Vptrofs. des_ifs_safe.
    hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau. unhide. remove_tau.

    hexploit SKINCLENV.
    { instantiate (2:= "encode"). unfold _hardening, prog, mkprogram. des_ifs_safe. ss.
      left. eauto. }
    i. des. rewrite H0. hred_r.
    iPoseProof ((@point_cast_ptr _ _ Es) with "PRE") as "#->".
    hred_r. rewrite cast_long; eauto. hred_r. des_ifs_safe.
    replace (Init.Nat.pred (Pos.to_nat (Pos.of_succ_nat blk))) with blk by nia.

    hexploit SKINCLGD; eauto.
    { unfold _hardening, prog, mkprogram. des_ifs_safe. ss.
      left. eauto. }
    i. rewrite H1. hred_r. ss. hred_r.

    (* iApply isim_apc. iExists (Some (20%nat : Ord.t)). *)
    iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. unfold hardeningStb. unseal "stb". ss. }
      { instantiate (1:=(_ , _ , _ , _, _ , _)). ss. eapply OrdArith.lt_from_nat. lia. }
      { ss. } }
    instantiate (1:=19). eapply OrdArith.lt_from_nat. lia. hred_r. ss.
    iSplitL "PRE'".
    { ss. iSplit; ss. iSplit; ss. iFrame. eauto. }
    iIntros (st_src2 st_tgt2 ret_src ret_tgt) "[INV'' [PRE' %]]".
    iDestruct "PRE'" as (iptr) "[[% ILIVE] RELT]".
    rewrite H4. iExists _. iSplitR; ss.

    hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau. unhide. remove_tau. unhide. remove_tau.

    hexploit SKINCLENV.
    { instantiate (2:= "bar"). unfold _hardening, prog, mkprogram. des_ifs_safe. ss.
      right. right. left. et. }
    i. des. rewrite H5. hred_r.
    rewrite cast_long; eauto. hred_r. rewrite cast_long; eauto. hred_r. des_ifs_safe.
    replace (Init.Nat.pred (Pos.to_nat (Pos.of_succ_nat blk0))) with blk0 by nia.

    hexploit SKINCLGD; eauto.
    { unfold _hardening, prog, mkprogram. des_ifs_safe. ss. right. right. eauto. }
    i. rewrite H3. hred_r.

    iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. unfold hardeningStb. unseal "stb". ss. }
      { instantiate (1:=(_ , _ , _ , _, _ , _, _, _ , _)). ss. eapply OrdArith.lt_from_nat. lia. }
      { ss. } }
    instantiate (1:=18). eapply OrdArith.lt_from_nat. lia.
    ss.
    iSplitL "ILIVE PRE RELT".
    { ss. iSplit; ss. iSplit; ss. iFrame. iSplits; eauto.
      rewrite Int64.xor_assoc. rewrite Int64.xor_idem. rewrite Int64.xor_zero. eauto. }
    iIntros (st_src3 st_tgt3 ret_src ret_tgt) "[INV''' [[[% PRE'] PRE''] %]]". subst.
    iExists _. iSplit; eauto.

    hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau.

    rewrite cast_long; eauto. hred_r.
    hred_l.
    
    iApply isim_choose_src.
    iExists _. iApply isim_ret. iSplits; eauto.
    Unshelve. ss. ss.
  Qed.
    
  End SIMFUNS.

End PROOF.
