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
Require Import CProofMode CIProofMode.
Require Import main.
Require Import main1.
Require Import xorlistall0.
Require Import xorlist1.
Require Import PtrofsArith.
From Coq Require Import Program.
From compcert Require Import Clightdefs.

Section PROOF.

  Import ClightPlusMemRA.
  Import ClightPlusMem1.
  Local Opaque Val.subl.

  Context `{@GRA.inG Mem.t Σ}.

  Variable GlobalStb : Sk.t -> gname -> option fspec.
  Hypothesis MEMINCL : forall sk, stb_incl (to_stb MemStb) (GlobalStb sk).
  Hypothesis STBINCL : forall sk, stb_incl (to_stb xorStb) (GlobalStb sk).


  Definition wf : _ -> Any.t * Any.t -> Prop :=
    @mk_wf
      _
      unit
      (fun _ st_src st_tgt => ⌜True⌝)%I.
  Let mfsk : Sk.t := [("malloc", Gfun (F:=Clight.fundef) (V:=type) (Ctypes.External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)); ("free", Gfun (Ctypes.External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default))].

  Section SIMFUNS.
  Variable xorlink : Clight.program.
  Variable xormod : Mod.t.
  Hypothesis VALID_link : xorlistall0._xor = Some xorlink.
  Hypothesis VALID_comp : compile xorlink "xorlist" = Errors.OK xormod.
  Let ce := Maps.PTree.elements (prog_comp_env xorlink).

  Variable sk: Sk.t.
  (* TODO: How to encapsulate fuction info? *)
  Hypothesis SKINCL1 : Sk.le (xormod.(Mod.sk)) sk.
  Hypothesis SKINCL2 : Sk.le mfsk sk.
  Hypothesis SKWF : Sk.wf sk.

  Lemma sim_main :
    sim_fnsem wf top2
      ("main", fun_to_tgt "xorlist" (GlobalStb sk) (mk_specbody main_spec (cfunU main_body)))
      ("main", cfunU (decomp_func sk ce f_main)).
  Proof.
    eassert (_xor = _).
    { unfold _xor. vm_compute (Linking.link _ _). reflexivity. }
    rewrite H0 in *. clear H0. destruct Ctypes.link_build_composite_env. destruct a.
    inversion VALID_link. clear VALID_link. subst.
    clear a. simpl in ce.
    set (compile _ _) in VALID_comp.
    eassert (r = Errors.OK _). { reflexivity. }
    rewrite H0 in *. clear r H0.
    inversion VALID_comp. clear VALID_comp. subst.
    econs; ss. red.

    (* current state: 1 *)
    get_composite ce e.

    dup SKINCL1. rename SKINCL0 into SKINCLENV1.
    apply incl_incl_env in SKINCLENV1.
    unfold incl_env in SKINCLENV1.
    dup SKINCL2. rename SKINCL0 into SKINCLENV2.
    apply incl_incl_env in SKINCLENV2.
    unfold incl_env in SKINCLENV2.
    pose proof sk_incl_gd as SKINCLGD.

    apply isim_fun_to_tgt; auto.
    unfold f_main, main_body. i; ss.
    unfold decomp_func, function_entry_c. ss.
    let H := fresh "HIDDEN" in
    set (H := hide 1).

    iIntros "[INV PRE]". des_ifs_safe. ss.
    iDestruct "PRE" as "[[% NULL] %]".
    des. clarify. hred_r. hred_l.

    iApply isim_apc. iExists (Some (10%nat : Ord.t)).

    iApply isim_ccallU_salloc; ss; oauto.
    iSplitL "INV"; iFrame.
    { iPureIntro. ss. }
    iIntros (st_src0 st_tgt0 vaddr m b) "[INV [[% hd_point] hd_alloc]]".
    des. clarify. hred_r.

    iApply isim_ccallU_salloc; ss; oauto.
    iSplitL "INV"; iFrame.
    { iPureIntro. ss. }
    iIntros (st_src1 st_tgt1 vaddr0 m0 b0) "[INV [[% tl_point] tl_alloc]]".
    des. clarify. hred_r.

    unhide. remove_tau. unhide. remove_tau. unhide. remove_tau.
    destruct Archi.ptr64 eqn:?; clarify. hred_r.

    iPoseProof (live_trivial_offset with "hd_alloc") as "[hd_alloc hd_equiv]"; et.
    iPoseProof (live_trivial_offset with "tl_alloc") as "[tl_alloc tl_equiv]"; et.
    iCombine "hd_equiv hd_point" as "hd".
    iPoseProof (equiv_point_comm with "hd") as "hd_point".
    iCombine "tl_equiv tl_point" as "tl".
    iPoseProof (equiv_point_comm with "tl") as "tl_point".
    iPoseProof (sub_null_r with "hd_alloc") as "%". rename H4 into hd_sub_r.
    iPoseProof (sub_null_r with "tl_alloc") as "%". rename H4 into tl_sub_r.
    iPoseProof (live_has_offset with "hd_alloc") as "[hd_alloc hd_ofs]"; et.

    iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV hd_point hd_ofs"; iFrame.
    { iExists _,_. iFrame. iPureIntro. ss. unfold Mptr. des_ifs. ss. split; ss. exists 0. ss. }
    iIntros (st_src2 st_tgt2) "[INV hd_point]".
    unfold Mptr. rewrite Heqb1.
    hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau.

    rewrite Heqb1. hred_r.
    iPoseProof (live_has_offset with "tl_alloc") as "[tl_alloc tl_ofs]"; et.
    iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV tl_point tl_ofs"; iFrame.
    { iExists _,_. iFrame. iPureIntro. ss. unfold Mptr. des_ifs. ss. split; ss. exists 0. ss. }
    iIntros (st_src3 st_tgt3) "[INV tl_point]".
    unfold Mptr. rewrite Heqb1. hred_r.
    remove_tau. unhide. remove_tau. unhide. remove_tau.
    unhide. remove_tau. unhide. remove_tau.

    hexploit SKINCLENV1.
    { instantiate (2:="add_hd"). et. }
    i. des. ss. rewrite FIND. rename FIND into add_hd_loc.
    hred_r. unfold __Node, ident. des_ifs_safe.

    replace (pred _) with blk by nia. move SKINCL1 at bottom.
    erewrite SKINCLGD; et; [|ss; et].
    hred_r. ss.
    iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. unfold xorStb. unseal "stb". ss. }
      { ss. des_ifs_safe. destruct p0. ss. }
      { ss. des_ifs_safe. destruct p0. ss. } }
    { instantiate (1:=5). oauto. }
    iPoseProof (live_has_offset with "hd_alloc") as "[hd_alloc hd_alloc_ofs]".
    iPoseProof (live_has_offset with "tl_alloc") as "[tl_alloc tl_alloc_ofs]".
    iSplitR "hd_alloc tl_alloc".
    { iFrame.
      instantiate (2:= (Vptr b Ptrofs.zero, Vptr b0 Ptrofs.zero, Int64.repr (Int.signed (Int.repr 3)), [])). ss.
      iSplit; et. iSplit; et. unfold full_xorlist.
      iExists _, _, _, _, _, _.
      iPoseProof (equiv_dup with "NULL") as "[? ?]".
      iFrame. iPureIntro. splits; try exists 0; ss. }
    iIntros (st_src4 st_tgt4 ret_src ret_tgt) "[INV POST]".
    ss. iDestruct "POST" as "[[% X] %]".
    clarify. iExists _. iSplit; et.
    hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau.

    hexploit SKINCLENV1.
    { instantiate (2:="add_tl"). et. }
    i. des. ss. rewrite FIND. rename FIND into add_tl_loc.
    hred_r. unfold __Node, ident. des_ifs_safe.

    replace (pred _) with blk0 by nia. move SKINCL1 at bottom.
    erewrite SKINCLGD; et; [|ss; et]. hred_r. ss.
    iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. unfold xorStb. unseal "stb". ss. }
      { ss. des_ifs_safe. destruct p0. ss. }
      { ss. des_ifs_safe. destruct p0. ss. } }
    { instantiate (1:=4). oauto. }
    iSplitR "hd_alloc tl_alloc".
    { iFrame.
      instantiate (2:= (Vptr b Ptrofs.zero, Vptr b0 Ptrofs.zero, Int64.repr (Int.signed (Int.repr 7)), _)). ss.
      iSplit; et. }
    iIntros (st_src5 st_tgt5 ret_src ret_tgt) "[INV POST]".
    ss. iDestruct "POST" as "[[% X] %]".
    clarify. iExists _. iSplit; et.
    hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau.
    unhide. remove_tau.

    hexploit SKINCLENV1.
    { instantiate (2:="delete_hd"). et. }
    i. des. ss. rewrite FIND. rename FIND into delete_hd_loc.
    hred_r. unfold __Node, ident. des_ifs_safe.

    replace (pred _) with blk1 by nia. move SKINCL1 at bottom.
    erewrite SKINCLGD; et; [|ss; et]. hred_r. ss.
    iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. unfold xorStb. unseal "stb". ss. }
      { ss. des_ifs_safe. destruct p. ss. }
      { ss. des_ifs_safe. destruct p. ss. } }
    { instantiate (1:=3). oauto. }
    iSplitR "hd_alloc tl_alloc".
    { iFrame.
      instantiate (2:= (Vptr b Ptrofs.zero, Vptr b0 Ptrofs.zero, _)). ss.
      iSplit; et. }
    iIntros (st_src6 st_tgt6 ret_src ret_tgt) "[INV POST]".
    ss. iDestruct "POST" as "[[% X] %]".
    clarify. iExists _. iSplit; et.
    hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau.
    unfold sem_mul_c. hred_r. rewrite Heqb1. hred_r.
    remove_tau. unhide. remove_tau.
    unhide. remove_tau. unhide. remove_tau.

    set (("delete_tl", Gfun _)) in *.

    hexploit (SKINCLENV1 (fst p) (snd p)).
    { right. right. right. right. clearbody p. destruct p. ss. et. }
    i. des. unfold p in FIND. ss. rewrite FIND. rename FIND into delete_tl_loc.
    hred_r. unfold __Node, ident. des_ifs_safe.

    replace (pred _) with blk2 by nia. move SKINCL1 at bottom.
    erewrite SKINCLGD.
    5:{ eapply SKINCL1. instantiate (1:=(snd p)). instantiate (1:=(fst p)). clearbody p. destruct p. do 4 right. ss. et. }
    all: et. 2:{ ss. } unfold p. ss. hred_r. ss.
    iApply isim_ccallU_pure; et.
    { eapply fn_has_spec_in_stb; et.
      { eapply STBINCL. stb_tac. unfold xorStb. unseal "stb". ss. }
      { ss. des_ifs_safe. destruct p0. ss. }
      { ss. des_ifs_safe. destruct p0. ss. } }
    { instantiate (1:=2). oauto. }
    iSplitR "hd_alloc tl_alloc".
    { iFrame.
      instantiate (2:= (Vptr b Ptrofs.zero, Vptr b0 Ptrofs.zero, _)). ss.
      iSplit; et. }
    iIntros (st_src7 st_tgt7 ret_src ret_tgt) "[INV POST]".
    ss. iDestruct "POST" as "[[% X] %]".
    clarify. iExists _. iSplit; et.
    hred_r. remove_tau. unhide. remove_tau. unhide. remove_tau.
    unfold sem_mul_c. hred_r. rewrite Heqb1. hred_r.
    remove_tau. unhide. remove_tau.
    unhide. remove_tau. unhide. remove_tau.

    unfold full_xorlist.
    iDestruct "X" as (md m1 hd tl ofs ofs1) "[[[[[[D C] %] B] A] %] ?]".

    iApply isim_ccallU_sfree; ss; oauto.
    des. clarify.
    iEval (replace (Vptr b Ptrofs.zero) with (Val.subl (Vptr b Ptrofs.zero) (Vptrofs Ptrofs.zero))) in "hd_alloc".
    iEval (replace (Vptr b0 Ptrofs.zero) with (Val.subl (Vptr b0 Ptrofs.zero) (Vptrofs Ptrofs.zero))) in "tl_alloc".
    iPoseProof (live_trivial with "hd_alloc") as "%".
    iPoseProof (live_trivial with "tl_alloc") as "%".
    iPoseProof (points_to_trivial with "D") as "%".
    iPoseProof (points_to_trivial with "B") as "%".
    iEval (replace (Val.subl (Vptr b Ptrofs.zero) (Vptrofs Ptrofs.zero)) with (Vptr b Ptrofs.zero)) in "D".
    iEval (replace (Val.subl (Vptr b0 Ptrofs.zero) (Vptrofs Ptrofs.zero)) with (Vptr b0 Ptrofs.zero)) in "B".
    assert (m = md).
    { destruct m. destruct md. ss. clarify. f_equal. apply proof_irr. }
    assert (m0 = m1).
    { destruct m0. destruct m1. ss. clarify. f_equal. apply proof_irr. }
    clarify. iSplitL "INV B tl_alloc"; iFrame.
    { iExists _,_,_. iFrame. iPureIntro.
      des. rewrite encode_val_length. unfold size_chunk_nat.
      change (size_chunk Mptr) with 8%Z in *. splits; et. }
    iIntros (st_src8 st_tgt8) "INV".
    hred_r.

    iApply isim_ccallU_sfree; ss; oauto.
    iSplitL "INV D hd_alloc"; iFrame.
    { iExists _,_,_. iFrame. iPureIntro.
      des. rewrite encode_val_length. unfold size_chunk_nat.
      change (size_chunk Mptr) with 8%Z in *. splits; et. }
    iIntros (st_src9 st_tgt9) "INV".
    hred_r. hred_l.
    iApply isim_ret. iFrame. iSplit; ss.
  Qed.

  End SIMFUNS.

End PROOF.
