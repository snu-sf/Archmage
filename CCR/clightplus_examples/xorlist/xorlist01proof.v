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
Require Import xorlist.
Require Import xorlistall0.
Require Import xorlist1.
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
  Hypothesis STBINCL : forall sk, stb_incl (to_stb xorStb) (GlobalStb sk).
  Hypothesis MEMINCL : forall sk, stb_incl (to_stb MemStb) (GlobalStb sk).


  Definition wf : _ -> Any.t * Any.t -> Prop :=
    @mk_wf
      _
      unit
      (fun _ st_src st_tgt => ⌜True⌝)%I.

  Let mfsk : Sk.t := [("malloc", Gfun (F:=Clight.fundef) (V:=type) (Ctypes.External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)); ("free", Gfun (Ctypes.External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default))].

  Section SIMFUNS.
  Variable xorlink : Clight.program.
  (* Variable xormod : Mod.t. *)
  Hypothesis VALID_link : xorlistall0._xor = Some xorlink.
  (* Hypothesis VALID_comp : compile xorlink "xorlist" = Errors.OK xormod. *)
  Let ce := Maps.PTree.elements (prog_comp_env xorlink).

  Variable sk: Sk.t.
  (* TODO: How to encapsulate fuction info? *)
  (* Hypothesis SKINCL1 : Sk.le (xormod.(Mod.sk)) sk. *)
  Hypothesis SKINCL : Sk.le mfsk sk.
  Hypothesis SKWF : Sk.wf sk.

  Lemma sim_add_tl :
    sim_fnsem wf top2
      ("add_tl", fun_to_tgt "xorlist" (GlobalStb sk) (mk_pure add_tl_spec))
      ("add_tl", cfunU (decomp_func sk ce f_add_tl)).
  Proof.
    Local Opaque encode_val.
    Local Opaque cast_to_ptr.
    eassert (_xor = _).
    { unfold _xor. vm_compute (Linking.link _ _). reflexivity. }
    rewrite H0 in *. clear H0. destruct Ctypes.link_build_composite_env. destruct a.
    inversion VALID_link. clear VALID_link. subst.
    clear a. simpl in ce.
    econs; ss. red.

    (* current state: 1 *)
    get_composite ce e.

    dup SKINCL. rename SKINCL0 into SKINCLENV.
    apply incl_incl_env in SKINCLENV.
    unfold incl_env in SKINCLENV.
    pose proof sk_incl_gd as SKINCLGD.

    apply isim_fun_to_tgt; auto.
    unfold f_add_hd. i; ss.
    unfold decomp_func, function_entry_c. ss.
    let H := fresh "HIDDEN" in
    set (H := hide 1).

    iIntros "[INV PRE]". des_ifs_safe. ss.
    iDestruct "PRE" as "[[% PRE] %]".
    des. clarify. hred_r.
    rename v into hd_hdl, v0 into tl_hdl, l into lfull, i into item.

    (* node* entry = (node* ) malloc(sizeof(node)) start *)
    unhide. hred_r. unhide. remove_tau. unhide. remove_tau.

    hexploit SKINCLENV.
    { instantiate (2:="malloc"). et. }
    i. des. ss. rewrite H0. rename H0 into malloc_loc.
    hred_r. unfold __Node, ident. des_ifs_safe.
    rewrite cast_ptrofs.
    rename Heq1 into ptr64. rename Heq0 into get_co.
    clear Heq e. hred_r.

    replace (pred _) with blk by nia.
    erewrite SKINCLGD; et; [|ss; et].
    hred_r. ss.
    iApply isim_apc. iExists (Some (20%nat : Ord.t)).
    rewrite co_co_sizeof.

    iApply isim_ccallU_malloc; ss; oauto.
    iSplitL "INV"; iFrame.
    { iPureIntro. ss. }
    iIntros (st_src0 st_tgt0 p_new m_new) "[INV [[% new_point] new_ofs]]".
    change (Z.to_nat _) with 16.
    rename H0 into m_new_size.

    hred_r. unhide. remove_tau.
    iPoseProof ((@live_cast_ptr _ _ Es) with "new_ofs") as "%".
    rewrite H0. rename H0 into new_cast_ptr.
    (* node* entry = (node* ) malloc(sizeof(node)) end *)

    hred_r. unhide. remove_tau. unhide. remove_tau.

    unfold full_xorlist.
    iDestruct "PRE" as (m_hd_hdl m_tl_hdl hd tl ofs_hd_hdl ofs_tl_hdl)
      "[[[[[[hd_hdl_point hd_hdl_ofs] %] tl_hdl_point] tl_hdl_ofs] %] LIST]".
    des. clarify.
    rename H0 into hd_hdl_sz.
    rename H1 into tl_hdl_sz.
    rename H2 into tl_hdl_align.
    rename H3 into hd_hdl_align.
    iPoseProof (rev_xorlist with "LIST") as "LIST".
    set (rev lfull) as l'. replace lfull with (rev l') by now unfold l'; rewrite rev_involutive; et.
    clearbody l'. clear lfull.
    rename l' into lfull.

    (* node* hd = *hd_handler start *)
    iPoseProof (points_to_is_ptr with "hd_hdl_point") as "%".
    rewrite H0. rename H0 into hd_hdl_ptr. hred_r.

    iPoseProof (xorlist_tl_deen with "LIST") as "%". rename H0 into hd_deen.
    iPoseProof (xorlist_tl_not_Vundef with "LIST") as "%". rename H0 into hd_notundef.
    iPoseProof (_has_offset_dup with "hd_hdl_ofs") as "[hd_hdl_ofs hd_hdl_ofs_ofs]".
    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hd_hdl_point hd_hdl_ofs_ofs"; iFrame.
    { iExists _. iFrame. iPureIntro. rewrite encode_val_length. splits; et. apply Memory.Mem.encode_val_change_check_false. }
    iIntros (st_src1 st_tgt1) "[INV hd_hdl_point]".
    rewrite hd_deen.
    (* node* hd = *hd_handler end *)

    hred_r. unhide. remove_tau. unhide. remove_tau.

    (* node* tl = *tl_handler start *)
    iPoseProof (points_to_is_ptr with "tl_hdl_point") as "%".
    rewrite H0. rename H0 into tl_hdl_is_point. hred_r.

    iPoseProof (xorlist_hd_deen with "LIST") as "%". rename H0 into tl_deen.
    iPoseProof (xorlist_hd_not_Vundef with "LIST") as "%". rename H0 into tl_notundef.
    iPoseProof (_has_offset_dup with "tl_hdl_ofs") as "[tl_hdl_ofs tl_hdl_ofs_ofs]".
    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV tl_hdl_point tl_hdl_ofs_ofs"; iFrame.
    { iExists _. iFrame. iPureIntro. rewrite encode_val_length. splits; et. apply Memory.Mem.encode_val_change_check_false. }
    iIntros (st_src2 st_tgt2) "[INV tl_hdl_point]".
    rewrite tl_deen.
    (* node* tl = *tl_handler end *)

    hred_r. unhide. remove_tau. unhide. remove_tau.

    (* entry->item = item start *)
    iPoseProof (points_to_is_ptr with "new_point") as "%".
    rewrite H0. rename H0 into new_is_point. hred_r. rewrite new_is_point. hred_r.

    unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
    replace (Coqlib.align 0 _) with 0%Z by et.
    replace (Ptrofs.repr 0) with Ptrofs.zero by et.
    iPoseProof (add_null_r with "new_ofs") as "%".
    rewrite H0. rename H0 into new_add_r. rewrite cast_long; et. hred_r.

    replace (points_to _ _ _ _) with (points_to p_new m_new (repeat Undef 8 ++ repeat Undef 8) 1) by reflexivity.
    iPoseProof (points_to_split with "new_point") as "[new_point_item new_point_key]".
    iPoseProof (sub_null_r with "new_ofs") as "%". rename H0 into new_sub_r.
    iPoseProof (live_has_offset with "new_ofs") as "[new_ofs new_ofs_ofs]".

    iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV new_point_item new_ofs_ofs"; iFrame.
    { iExists _, _. iFrame. ss. iPureIntro. split; et. exists 0. ss. }
    iIntros (st_src3 st_tgt3) "[INV new_point_item]".
    (* entry->item = item end *)

    hred_r. unhide. remove_tau.
    (* if (hd == NULL) start *)
    replace (Vlong (Int64.repr _)) with Vnullptr by et.

    destruct lfull.
    (* case: nil list *)
    {
      ss.
      iDestruct "LIST" as "[NULL_hd NULL_tl]".
      iPoseProof (equiv_sym with "NULL_tl") as "NULL_tl". iPoseProof (null_equiv with "NULL_tl") as "%". subst.

      iApply isim_ccallU_cmp_ptr0; ss; oauto.
      iSplitL "INV"; iFrame.
      iIntros (st_src4 st_tgt4) "INV".
      (* if (hd == NULL) end *)

      hred_r. des_ifs_safe. clear Heq.
      unhide. hred_r. unhide. remove_tau.

      (* entry->link = 0 start *)
      rewrite new_is_point. hred_r. rewrite new_is_point. hred_r.

      unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
      replace (Coqlib.align _ _) with 8%Z by et.
      replace (Vlong (Int64.repr _)) with Vnullptr by et.
      iPoseProof (live_has_offset with "new_ofs") as "[new_ofs new_ofs_ofs]".
      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV new_point_key new_ofs_ofs"; iFrame.
      { iExists _,_. iFrame. iSplit; cycle 1. { iApply _has_offset_slide. iFrame. } { iPureIntro. split; ss. exists 1. ss. } }
      iIntros (st_src5 st_tgt5) "[INV new_point_key]".
      (* entry->link = 0 end *)

      hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau. unhide. remove_tau.

      (* hd_handler = *tl_handler = entry start *)
      rewrite new_cast_ptr. hred_r. unhide. remove_tau.
      rewrite tl_hdl_is_point. hred_r. rewrite new_cast_ptr. hred_r.
      iPoseProof (_has_offset_dup with "tl_hdl_ofs") as "[tl_hdl_ofs tl_hdl_ofs_ofs]".

      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV tl_hdl_point tl_hdl_ofs_ofs"; iFrame.
      { iExists _,_. iFrame. rewrite encode_val_length. iPureIntro. ss. }
      iIntros (st_src7 st_tgt7) "[INV tl_hdl_point]".

      hred_r. unhide. remove_tau. rewrite hd_hdl_ptr. hred_r.
      rewrite new_cast_ptr. hred_r.
      iPoseProof (_has_offset_dup with "hd_hdl_ofs") as "[hd_hdl_ofs hd_hdl_ofs_ofs]".

      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV hd_hdl_point hd_hdl_ofs_ofs"; iFrame.
      { iExists _,_. iFrame. rewrite encode_val_length. iPureIntro. ss. }
      iIntros (st_src8 st_tgt8) "[INV hd_hdl_point]".

      hred_r. remove_tau. hred_l. iApply isim_choose_src.
      iExists _. iApply isim_ret. iFrame. iSplit; ss. iSplit; ss.
      iCombine "new_point_item new_point_key" as "new_point".
      iPoseProof (points_to_collect with "new_point") as "new_point".

      iExists _,_,_,_,_,_. iFrame.
      iSplit; ss.
      change Vnullptr with (Vptrofs Ptrofs.zero) at 3 4.
      iPoseProof (equiv_refl_live with "new_ofs") as "[new_ofs new_equiv]".
      iPoseProof (equiv_dup with "NULL_tl") as "[? ?]".
      iExists _,_,_. iFrame. rewrite Ptrofs.xor_zero_l. iFrame.
      iSplit; ss.
    }
    ss. destruct v; clarify.
    iDestruct "LIST" as (i_prev i_next m_hd) "[[[[% prev_addr] tl_ofs] tl_point] LIST]".
    rename H0 into m_hd_size.
    iPoseProof (sub_null_r with "tl_ofs") as "%". rename H0 into tl_sub_r.

    (* if (hd == NULL) start *)

    iApply isim_ccallU_cmp_ptr3; ss; oauto.
    iSplitL "INV tl_ofs".
    { rewrite tl_sub_r. iFrame. iPureIntro. red. rewrite m_hd_size. ss. }
    iIntros (st_src4 st_tgt4) "[INV tl_ofs]".
    (* if (hd == NULL) end *)

    hred_r. des_ifs_safe. clear Heq. unhide. hred_r. unhide. remove_tau. unhide. remove_tau.

    (* entry->link = (intptr_t)hd start *)
    iPoseProof ((@live_cast_ptr_ofs _ _ Es) with "tl_ofs") as "%".
    rewrite H0. hred_r. rename H0 into hd_cast_ptr.

    iApply isim_ccallU_capture1; ss; oauto.
    iSplitL "INV tl_ofs"; iFrame.
    iIntros (st_src5 st_tgt5 i_hd) "[INV [tl_ofs tl_addr]]".

    hred_r. unhide. remove_tau.

    rewrite new_is_point. hred_r.
    rewrite new_is_point. hred_r.
    unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
    rewrite cast_ptrofs. hred_r.
    replace (Coqlib.align _ _) with 8%Z by et.
    iPoseProof (live_has_offset with "new_ofs") as "[new_ofs new_ofs_ofs]".

    iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV new_point_key new_ofs_ofs"; iFrame.
    { iExists _,_. iFrame. iSplit; cycle 1.
      { iApply _has_offset_slide. ss. }
      { iPureIntro. split; ss. exists 1. ss. } }
    iIntros (st_src6 st_tgt6) "[INV new_point_key]".
    (* entry->link = (intptr_t)hd end *)

    hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau.

    (* hd->link = hd->link ^ (intptr_t)entry start *)
    rewrite new_cast_ptr. hred_r.
    iApply isim_ccallU_capture1; ss; oauto.
    iSplitL "INV new_ofs"; iFrame.
    { rewrite new_sub_r. et. }
    iIntros (st_src7 st_tgt7 i_new) "[INV [new_ofs new_addr]]".

    hred_r. unhide. remove_tau.

    iPoseProof (points_to_is_ptr with "tl_point") as "%".
    rewrite H0. rename H0 into hd_ptr.
    hred_r. rewrite hd_ptr. hred_r.
    unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
    replace (Coqlib.align _ _) with 8%Z by et.

    rewrite hd_ptr. hred_r. rewrite hd_ptr. hred_r.
    rewrite co_co_members. ss. hred_r.
    replace (Coqlib.align _ _) with 8%Z by et.

    iPoseProof (points_to_split with "tl_point") as "[tl_point_item tl_point_key]".
    iPoseProof (live_has_offset_ofs with "tl_ofs") as "[tl_ofs tl_ofs_ofs]".
    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV tl_point_key tl_ofs_ofs".
    { iFrame. iExists _. iSplit.
      { iApply _has_offset_slide. ss. }
      { iPureIntro. splits; ss. exists 1. ss. } }
    iIntros (st_src8 st_tgt8) "[INV tl_point_key]".

    unfold Mptr. rewrite ptr64.
    rewrite decode_encode_ofs. hred_r.
    rewrite cast_ptrofs.
    rewrite cast_ptrofs. hred_r.
    des_ifs_safe.

    hred_r. rewrite cast_long; et. hred_r.
    iPoseProof (live_has_offset_ofs with "tl_ofs") as "[tl_ofs tl_ofs_ofs]".
    iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV tl_point_key tl_ofs_ofs".
    { iFrame. iExists _,_. iFrame. iSplit. 2:{ iApply _has_offset_slide. et. }
      iPureIntro. split; ss. exists 1. ss. }
    iIntros (st_src9 st_tgt9) "[INV tl_point_key]".
    (* hd->link = hd->link ^ (intptr_t)entry end *)

    hred_r. unhide. remove_tau.

    (* *hd_handler = entry start *)
    rewrite tl_hdl_is_point. hred_r.
    rewrite new_cast_ptr. hred_r.
    iPoseProof (_has_offset_dup with "tl_hdl_ofs") as "[tl_hdl_ofs tl_hdl_ofs_ofs]".
    iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV tl_hdl_point tl_hdl_ofs_ofs".
    { iFrame. iExists _,_. iFrame. iPureIntro.
      rewrite encode_val_length. ss. }
    iIntros (st_src10 st_tgt10) "[INV tl_hdl_point]".
    (* *hd_handler = entry end *)

    (* prove post condition *)
    hred_r. remove_tau. hred_l. iApply isim_choose_src.
    iExists _. iApply isim_ret.
    iFrame. iSplit; ss. iSplit; ss.
    iCombine "new_point_item new_point_key" as "new_point".
    iCombine "tl_point_item tl_point_key" as "tl_point".
    iPoseProof (points_to_collect with "new_point") as "new_point".
    iPoseProof (points_to_collect with "tl_point") as "tl_point".
    iPoseProof (null_equiv with "prev_addr") as "%".
    assert (i_prev = Ptrofs.zero).
    { unfold Vptrofs, Vnullptr in *.
      destruct Archi.ptr64 eqn:?. 2:{ clarify. }
      apply (f_equal (fun v => match v with Vlong i => i | _ => Int64.zero end)) in H0.
      apply (f_equal Ptrofs.of_int64) in H0. rewrite Ptrofs.of_int64_to_int64 in H0; et. }
    clear H0. clarify.

    iExists _,_,_,_,_,_. iFrame. iSplit; ss.
    rewrite <- (rev_involutive ((rev lfull ++ _) ++ _)).
    iApply rev_xorlist. rewrite rev_app_distr.
    change (rev [Vlong item]) with [Vlong item].
    ss. rewrite rev_app_distr.
    change (rev [Vlong i]) with [Vlong i].
    ss. rewrite new_sub_r.
    iExists _,_,_. iFrame. rewrite Ptrofs.xor_zero_l. iFrame. iSplit; ss.
    rewrite <- Heq0.

    iPoseProof (equiv_dup with "tl_addr") as "[tl_addr tl_addr']".
    iCombine "tl_addr' tl_point" as "tl_point".
    iPoseProof (equiv_point_comm with "tl_point") as "tl_point".
    iPoseProof (equiv_dup with "tl_addr") as "[tl_addr tl_addr']".
    iCombine "tl_addr' tl_ofs" as "tl_ofs". rewrite tl_sub_r.
    iPoseProof (equiv_live_comm with "tl_ofs") as "tl_ofs".
    iPoseProof (equiv_sym with "tl_addr") as "tl_addr".
    iExists _,_,_. iFrame.
    instantiate (1:=i_next).
    replace (Vptrofs (Ptrofs.xor _ _)) with (Vlong (Int64.xor i0 i1)).
    - iFrame. iSplit; ss. rewrite rev_involutive. iApply xorlist_hd_prev_replace. iFrame. iApply equiv_sym. et.
    - unfold Vptrofs in *. des_ifs. f_equal.
      rewrite int64_ptrofs_xor_comm. f_equal. rewrite Ptrofs.xor_commut.
      f_equal. rewrite Ptrofs.xor_zero_l. et.
  Qed.

  Lemma sim_add_hd :
    sim_fnsem wf top2
      ("add_hd", fun_to_tgt "xorlist" (GlobalStb sk) (mk_pure add_hd_spec))
      ("add_hd", cfunU (decomp_func sk ce f_add_hd)).
  Proof.
    Local Opaque encode_val.
    Local Opaque cast_to_ptr.
    eassert (_xor = _).
    { unfold _xor. vm_compute (Linking.link _ _). reflexivity. }
    rewrite H0 in *. clear H0. destruct Ctypes.link_build_composite_env. destruct a.
    inversion VALID_link. clear VALID_link. subst.
    clear a. simpl in ce.
    econs; ss. red.

    (* current state: 1 *)
    get_composite ce e.

    dup SKINCL. rename SKINCL0 into SKINCLENV.
    apply incl_incl_env in SKINCLENV.
    unfold incl_env in SKINCLENV.
    pose proof sk_incl_gd as SKINCLGD.

    apply isim_fun_to_tgt; auto.
    unfold f_add_hd. i; ss.
    unfold decomp_func, function_entry_c. ss.
    let H := fresh "HIDDEN" in
    set (H := hide 1).

    iIntros "[INV PRE]". des_ifs_safe. ss.
    iDestruct "PRE" as "[[% PRE] %]".
    des. clarify. hred_r.
    rename v into hd_hdl, v0 into tl_hdl, l into lfull, i into item.

    (* node* entry = (node* ) malloc(sizeof(node)) start *)
    unhide. hred_r. unhide. remove_tau. unhide. remove_tau.

    hexploit SKINCLENV.
    { instantiate (2:="malloc"). et. }
    i. des. ss. rewrite H0. rename H0 into malloc_loc.
    hred_r. unfold __Node, ident. des_ifs_safe.
    rewrite cast_ptrofs.
    rename Heq1 into ptr64. rename Heq0 into get_co.
    clear Heq e. hred_r.

    replace (pred _) with blk by nia.
    erewrite SKINCLGD; et; [|ss; et].
    hred_r. ss.
    iApply isim_apc. iExists (Some (20%nat : Ord.t)).
    rewrite co_co_sizeof.

    iApply isim_ccallU_malloc; ss; oauto.
    iSplitL "INV"; iFrame.
    { iPureIntro. ss. }
    iIntros (st_src0 st_tgt0 p_new m_new) "[INV [[% new_point] new_ofs]]".
    change (Z.to_nat _) with 16.
    rename H0 into m_new_size.

    hred_r. unhide. remove_tau.
    iPoseProof ((@live_cast_ptr _ _ Es) with "new_ofs") as "%".
    rewrite H0. rename H0 into new_cast_ptr.
    (* node* entry = (node* ) malloc(sizeof(node)) end *)

    hred_r. unhide. remove_tau. unhide. remove_tau.

    unfold full_xorlist.
    iDestruct "PRE" as (m_hd_hdl m_tl_hdl hd tl ofs_hd_hdl ofs_tl_hdl)
      "[[[[[[hd_hdl_point hd_hdl_ofs] %] tl_hdl_point] tl_hdl_ofs] %] LIST]".
    des. clarify.
    rename H0 into hd_hdl_sz.
    rename H1 into tl_hdl_sz.
    rename H2 into tl_hdl_align.
    rename H3 into hd_hdl_align.

    (* node* hd = *hd_handler start *)
    iPoseProof (points_to_is_ptr with "hd_hdl_point") as "%".
    rewrite H0. rename H0 into hd_hdl_ptr. hred_r.

    iPoseProof (xorlist_hd_deen with "LIST") as "%". rename H0 into hd_deen.
    iPoseProof (xorlist_hd_not_Vundef with "LIST") as "%". rename H0 into hd_notundef.
    iPoseProof (_has_offset_dup with "hd_hdl_ofs") as "[hd_hdl_ofs hd_hdl_ofs_ofs]".
    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hd_hdl_point hd_hdl_ofs_ofs"; iFrame.
    { iExists _. iFrame. iPureIntro. rewrite encode_val_length. splits; et. apply Memory.Mem.encode_val_change_check_false. }
    iIntros (st_src1 st_tgt1) "[INV hd_hdl_point]".
    rewrite hd_deen.
    (* node* hd = *hd_handler end *)

    hred_r. unhide. remove_tau. unhide. remove_tau.

    (* node* tl = *tl_handler start *)
    iPoseProof (points_to_is_ptr with "tl_hdl_point") as "%".
    rewrite H0. rename H0 into tl_hdl_is_point. hred_r.

    iPoseProof (xorlist_tl_deen with "LIST") as "%". rename H0 into tl_deen.
    iPoseProof (xorlist_tl_not_Vundef with "LIST") as "%". rename H0 into tl_notundef.
    iPoseProof (_has_offset_dup with "tl_hdl_ofs") as "[tl_hdl_ofs tl_hdl_ofs_ofs]".
    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV tl_hdl_point tl_hdl_ofs_ofs"; iFrame.
    { iExists _. iFrame. iPureIntro. rewrite encode_val_length. splits; et. apply Memory.Mem.encode_val_change_check_false. }
    iIntros (st_src2 st_tgt2) "[INV tl_hdl_point]".
    rewrite tl_deen.
    (* node* tl = *tl_handler end *)

    hred_r. unhide. remove_tau. unhide. remove_tau.

    (* entry->item = item start *)
    iPoseProof (points_to_is_ptr with "new_point") as "%".
    rewrite H0. rename H0 into new_is_point. hred_r. rewrite new_is_point. hred_r.

    unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
    replace (Coqlib.align 0 _) with 0%Z by et.
    replace (Ptrofs.repr 0) with Ptrofs.zero by et.
    iPoseProof (add_null_r with "new_ofs") as "%".
    rewrite H0. rename H0 into new_add_r. rewrite cast_long; et. hred_r.

    replace (points_to _ _ _ _) with (points_to p_new m_new (repeat Undef 8 ++ repeat Undef 8) 1) by reflexivity.
    iPoseProof (points_to_split with "new_point") as "[new_point_item new_point_key]".
    iPoseProof (sub_null_r with "new_ofs") as "%". rename H0 into new_sub_r.
    iPoseProof (live_has_offset with "new_ofs") as "[new_ofs new_ofs_ofs]".

    iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV new_point_item new_ofs_ofs"; iFrame.
    { iExists _, _. iFrame. ss. iPureIntro. split; et. exists 0. ss. }
    iIntros (st_src3 st_tgt3) "[INV new_point_item]".
    (* entry->item = item end *)

    hred_r. unhide. remove_tau.
    (* if (hd == NULL) start *)
    replace (Vlong (Int64.repr _)) with Vnullptr by et.

    destruct lfull.
    (* case: nil list *)
    {
      ss.
      iDestruct "LIST" as "[NULL_tl NULL_hd]".
      iPoseProof (equiv_sym with "NULL_hd") as "NULL_hd". iPoseProof (null_equiv with "NULL_hd") as "%". subst.

      iApply isim_ccallU_cmp_ptr0; ss; oauto.
      iSplitL "INV"; iFrame.
      iIntros (st_src4 st_tgt4) "INV".
      (* if (hd == NULL) end *)

      hred_r. des_ifs_safe. clear Heq.
      unhide. hred_r. unhide. remove_tau.

      (* entry->link = 0 start *)
      rewrite new_is_point. hred_r. rewrite new_is_point. hred_r.

      unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
      replace (Coqlib.align _ _) with 8%Z by et.
      replace (Vlong (Int64.repr _)) with Vnullptr by et.
      iPoseProof (live_has_offset with "new_ofs") as "[new_ofs new_ofs_ofs]".

      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV new_point_key new_ofs_ofs"; iFrame.
      { iExists _,_. iFrame. iSplit; cycle 1.  { iApply _has_offset_slide. et. } { iPureIntro. split; ss. exists 1. ss. } }
      iIntros (st_src5 st_tgt5) "[INV new_point_key]".
      (* entry->link = 0 end *)

      hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau. unhide. remove_tau.

      (* hd_handler = *tl_handler = entry start *)
      rewrite new_cast_ptr. hred_r. unhide. remove_tau.
      rewrite tl_hdl_is_point. hred_r. rewrite new_cast_ptr. hred_r.
      iPoseProof (_has_offset_dup with "tl_hdl_ofs") as "[tl_hdl_ofs tl_hdl_ofs_ofs]".

      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV tl_hdl_point tl_hdl_ofs_ofs"; iFrame.
      { iExists _,_. iFrame. rewrite encode_val_length. iPureIntro. ss. }
      iIntros (st_src7 st_tgt7) "[INV tl_hdl_point]".

      hred_r. unhide. remove_tau. rewrite hd_hdl_ptr. hred_r.
      rewrite new_cast_ptr. hred_r.
      iPoseProof (_has_offset_dup with "hd_hdl_ofs") as "[hd_hdl_ofs hd_hdl_ofs_ofs]".

      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV hd_hdl_point hd_hdl_ofs_ofs"; iFrame.
      { iExists _,_. iFrame. rewrite encode_val_length. iPureIntro. ss. }
      iIntros (st_src8 st_tgt8) "[INV hd_hdl_point]".

      hred_r. remove_tau. hred_l. iApply isim_choose_src.
      iExists _. iApply isim_ret. iFrame. iSplit; ss. iSplit; ss.
      iCombine "new_point_item new_point_key" as "new_point".
      iPoseProof (points_to_collect with "new_point") as "new_point".

      iExists _,_,_,_,_,_. iFrame.
      iSplit; ss.
      change Vnullptr with (Vptrofs Ptrofs.zero) at 3 4.
      iPoseProof (equiv_refl_live with "new_ofs") as "[new_ofs new_equiv]".
      iPoseProof (equiv_dup with "NULL_hd") as "[? ?]".
      iExists _,_,_. iFrame. rewrite Ptrofs.xor_zero_l. iFrame.
      iSplit; ss.
    }
    ss. destruct v; clarify.
    iDestruct "LIST" as (i_prev i_next m_hd) "[[[[% prev_addr] hd_ofs] hd_point] LIST]".
    rename H0 into m_hd_size.
    iPoseProof (sub_null_r with "hd_ofs") as "%". rename H0 into hd_sub_r.

    (* if (hd == NULL) start *)

    iApply isim_ccallU_cmp_ptr3; ss; oauto.
    iSplitL "INV hd_ofs".
    { rewrite hd_sub_r. iFrame. iPureIntro. red. rewrite m_hd_size. ss. }
    iIntros (st_src4 st_tgt4) "[INV hd_ofs]".
    (* if (hd == NULL) end *)

    hred_r. des_ifs_safe. clear Heq. unhide. hred_r. unhide. remove_tau. unhide. remove_tau.

    (* entry->link = (intptr_t)hd start *)
    iPoseProof ((@live_cast_ptr_ofs _ _ Es) with "hd_ofs") as "%".
    rewrite H0. hred_r. rename H0 into hd_cast_ptr.

    iApply isim_ccallU_capture1; ss; oauto.
    iSplitL "INV hd_ofs"; iFrame.
    iIntros (st_src5 st_tgt5 i_hd) "[INV [hd_ofs hd_addr]]".

    hred_r. unhide. remove_tau.

    rewrite new_is_point. hred_r.
    rewrite new_is_point. hred_r.
    unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
    rewrite cast_ptrofs. hred_r.
    replace (Coqlib.align _ _) with 8%Z by et.
    iPoseProof (live_has_offset with "new_ofs") as "[new_ofs new_ofs_ofs]".

    iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV new_point_key new_ofs_ofs"; iFrame.
    { iExists _,_. iFrame. iSplit; cycle 1.
      { iApply _has_offset_slide. ss. }
      { iPureIntro. split; ss. exists 1. ss. } }
    iIntros (st_src6 st_tgt6) "[INV new_point_key]".
    (* entry->link = (intptr_t)hd end *)

    hred_r. unhide. remove_tau. unhide. hred_r. unhide. remove_tau.

    (* hd->link = hd->link ^ (intptr_t)entry start *)
    rewrite new_cast_ptr. hred_r.
    iApply isim_ccallU_capture1; ss; oauto.
    iSplitL "INV new_ofs"; iFrame.
    { rewrite new_sub_r. et. }
    iIntros (st_src7 st_tgt7 i_new) "[INV [new_ofs new_addr]]".

    hred_r. unhide. remove_tau.

    iPoseProof (points_to_is_ptr with "hd_point") as "%".
    rewrite H0. rename H0 into hd_ptr.
    hred_r. rewrite hd_ptr. hred_r.
    unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
    replace (Coqlib.align _ _) with 8%Z by et.

    rewrite hd_ptr. hred_r. rewrite hd_ptr. hred_r.
    rewrite co_co_members. ss. hred_r.
    replace (Coqlib.align _ _) with 8%Z by et.

    iPoseProof (points_to_split with "hd_point") as "[hd_point_item hd_point_key]".
    iPoseProof (live_has_offset_ofs with "hd_ofs") as "[hd_ofs hd_ofs_ofs]".
    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hd_point_key hd_ofs_ofs".
    { iFrame. iExists _. iSplit.
      { iApply _has_offset_slide. ss. }
      { iPureIntro. splits; ss. exists 1. ss. } }
    iIntros (st_src8 st_tgt8) "[INV hd_point_key]".

    unfold Mptr. rewrite ptr64.
    rewrite decode_encode_ofs. hred_r.
    rewrite cast_ptrofs.
    rewrite cast_ptrofs. hred_r.
    des_ifs_safe.

    hred_r. rewrite cast_long; et. hred_r.
    iPoseProof (live_has_offset_ofs with "hd_ofs") as "[hd_ofs hd_ofs_ofs]".
    iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV hd_point_key hd_ofs_ofs".
    { iFrame. iExists _,_. iFrame. iSplit. 2:{ iApply _has_offset_slide. et. }
      iPureIntro. split; ss. exists 1. ss. } 
    iIntros (st_src9 st_tgt9) "[INV hd_point_key]".
    (* hd->link = hd->link ^ (intptr_t)entry end *)

    hred_r. unhide. remove_tau.

    (* *hd_handler = entry start *)
    rewrite hd_hdl_ptr. hred_r.
    rewrite new_cast_ptr. hred_r.
    iPoseProof (_has_offset_dup with "hd_hdl_ofs") as "[hd_hdl_ofs hd_hdl_ofs_ofs]".
    iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV hd_hdl_point hd_hdl_ofs_ofs".
    { iFrame. iExists _,_. iFrame. iPureIntro.
      rewrite encode_val_length. ss. }
    iIntros (st_src10 st_tgt10) "[INV hd_hdl_point]".
    (* *hd_handler = entry end *)

    (* prove post condition *)
    hred_r. remove_tau. hred_l. iApply isim_choose_src.
    iExists _. iApply isim_ret.
    iFrame. iSplit; ss. iSplit; ss.
    iCombine "new_point_item new_point_key" as "new_point".
    iCombine "hd_point_item hd_point_key" as "hd_point".
    iPoseProof (points_to_collect with "new_point") as "new_point".
    iPoseProof (points_to_collect with "hd_point") as "hd_point".
    iPoseProof (null_equiv with "prev_addr") as "%".
    assert (i_prev = Ptrofs.zero).
    { unfold Vptrofs, Vnullptr in *.
      destruct Archi.ptr64 eqn:?. 2:{ clarify. }
      apply (f_equal (fun v => match v with Vlong i => i | _ => Int64.zero end)) in H0.
      apply (f_equal Ptrofs.of_int64) in H0. rewrite Ptrofs.of_int64_to_int64 in H0; et. }
    clear H0. clarify.

    iExists _,_,_,_,_,_. iFrame. iSplit; ss.
    iExists _,_,_. iFrame. rewrite Ptrofs.xor_zero_l. rewrite new_sub_r.
    iFrame. iSplit; ss.
    rewrite <- Heq0.

    iPoseProof (equiv_dup with "hd_addr") as "[hd_addr hd_addr']".
    iCombine "hd_addr' hd_point" as "hd_point".
    iPoseProof (equiv_point_comm with "hd_point") as "hd_point".
    iPoseProof (equiv_dup with "hd_addr") as "[hd_addr hd_addr']".
    iCombine "hd_addr' hd_ofs" as "hd_ofs". rewrite hd_sub_r.
    iPoseProof (equiv_live_comm with "hd_ofs") as "hd_ofs".
    iPoseProof (equiv_sym with "hd_addr") as "hd_addr".
    iExists _,_,_. iFrame.
    instantiate (1:=i_next).
    replace (Vptrofs (Ptrofs.xor _ _)) with (Vlong (Int64.xor i0 i1)).
    - iFrame. iSplit; ss. iApply xorlist_hd_prev_replace. iFrame. iApply equiv_sym. iFrame.
    - unfold Vptrofs in *. des_ifs. f_equal.
      rewrite int64_ptrofs_xor_comm. f_equal. rewrite Ptrofs.xor_commut.
      f_equal. rewrite Ptrofs.xor_zero_l. et.
  Qed.

  Lemma sim_delete_tl :
    sim_fnsem wf top2
      ("delete_tl", fun_to_tgt "xorlist" (GlobalStb sk) (mk_pure delete_tl_spec))
      ("delete_tl", cfunU (decomp_func sk ce f_delete_tl)).
  Proof.
    Local Opaque encode_val.
    eassert (_xor = _).
    { unfold _xor. vm_compute (Linking.link _ _). reflexivity. }
    rewrite H0 in *. clear H0. destruct Ctypes.link_build_composite_env. destruct a.
    inversion VALID_link. clear VALID_link. subst.
    clear a. simpl in ce.
    econs; ss. red.

    (* current state: 1 *)
    get_composite ce e.

    dup SKINCL. rename SKINCL0 into SKINCLENV.
    apply incl_incl_env in SKINCLENV.
    unfold incl_env in SKINCLENV.
    pose proof sk_incl_gd as SKINCLGD.

    apply isim_fun_to_tgt; auto.
    unfold f_delete_hd. i; ss.
    unfold decomp_func, function_entry_c. ss.
    let H := fresh "HIDDEN" in
    set (H := hide 1).

    iIntros "[INV PRE]". des_ifs_safe. ss.
    iDestruct "PRE" as "[[% PRE] %]". unfold full_xorlist.
    iDestruct "PRE"
      as (m_hd_hdl m_tl_hdl hd_old tl_old ofs_hd_hdl ofs_tl_hdl)
      "[[[[[[hd_hdl_point hd_hdl_ofs] %] tl_hdl_point] tl_hdl_ofs] %] LIST]".
    iPoseProof (rev_xorlist with "LIST") as "LIST".
    clarify. hred_r. unhide. hred_r. unhide. remove_tau.
    rename v into hd_handler.  rename v0 into tl_handler.
    set (rev l) as l'. replace l with (rev l') by now unfold l'; rewrite rev_involutive; et.
    clearbody l'. clear l.
    rename l' into linput. des. clarify.
    rename H0 into tl_hdl_align.
    rename H1 into hd_hdl_align.
    rename H2 into hd_hdl_sz.
    rename H3 into tl_hdl_sz.


    (* current state: 2 *)
    unhide. hred_r. unhide. remove_tau.

    (* node hd_old = *hdH start *)
    iPoseProof (points_to_is_ptr with "tl_hdl_point") as "%". rewrite H0. rename H0 into tl_hdl_ptr.
    hred_r. iApply isim_apc. iExists (Some (20%nat : Ord.t)).

    iPoseProof (xorlist_hd_deen with "LIST") as "%". rename H0 into tl_deen.
    iPoseProof (xorlist_hd_not_Vundef with "LIST") as "%". rename H0 into tl_notundef.
    iPoseProof (_has_offset_dup with "tl_hdl_ofs") as "[tl_hdl_ofs tl_hdl_ofs_ofs]".
    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV tl_hdl_point tl_hdl_ofs_ofs"; iFrame.
    { iExists _. iFrame. iPureIntro. rewrite encode_val_length. splits; et. apply Memory.Mem.encode_val_change_check_false. }
    iIntros (st_src0 st_tgt0) "[INV tl_hdl_point]".
    rewrite tl_deen.
    (* node hd_old = *hdH end *)

    (* if (hd_old != NULL) start *)
    hred_r. unhide. remove_tau. unhide. remove_tau.
    change Archi.ptr64 with true. hred_r.
    change (Vlong (Int64.repr _)) with Vnullptr.
    destruct linput as [|v lnext].
    (* case: nil list *)
    {
      ss.
      iDestruct "LIST" as "[NULL_hd NULL_tl]".
      iPoseProof (null_equiv with "NULL_hd") as "%". subst.
      iPoseProof (equiv_sym with "NULL_tl") as "H". iPoseProof (null_equiv with "H") as "%". subst.
      iApply isim_ccallU_cmp_ptr0; ss; oauto.
      iSplitL "INV"; iFrame.
      iIntros (st_src1 st_tgt1) "INV".

      hred_r. destruct (Int.eq) eqn:?; ss; clarify. clear Heqb.
      (* if (hd_old != NULL) end *)

      unhide. hred_r. unhide. remove_tau. change Archi.ptr64 with true. ss.
      change Vnullptr with (Vptrofs Ptrofs.zero).
      rewrite ptrofs_cast_ptr. hred_r.

      (* prove post condition *)
      hred_l. iApply isim_choose_src.
      iExists _. iApply isim_ret.
      iFrame. iSplit; ss. iSplit; ss.
      iExists _,_,_,_,_,_. iFrame. iSplit; ss.
    }
    (* case: not nil list *)
    ss. destruct v; try solve [iDestruct "LIST" as "[]"]. rename i into tl_item.
    iDestruct "LIST" as (i_tl_next i_tl_prev m_tl_old) "[[[[% tl_next_equiv] tl_ofs] tl_point] LIST]". rename H0 into m_tl_size.
    iPoseProof (sub_null_r with "tl_ofs") as "%". rename H0 into tl_sub_r.

    (* node* hd_new = (node* )hd_old->link start *)

    iApply isim_ccallU_cmp_ptr4; ss; oauto.
    rewrite tl_sub_r.
    iSplitL "INV tl_ofs"; iFrame.
    { iPureIntro. red. rewrite m_tl_size. change (size_chunk Mptr) with 8%Z. change (Ptrofs.unsigned Ptrofs.zero) with 0%Z. nia. }
    iIntros (st_src1 st_tgt1) "[INV tl_ofs]".
    hred_r. destruct (Int.eq) eqn: ?; ss; clarify. clear Heqb.
    (* if (hd_old != NULL) end *)

    unhide. hred_r. unhide. remove_tau.

    (* item = hd_old->item start *)
    iPoseProof (points_to_is_ptr with "tl_point") as "%". rewrite H0. rename H0 into tl_is_ptr. hred_r. rewrite tl_is_ptr. hred_r.
    unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
    iPoseProof (points_to_split with "tl_point") as "[tl_point_item tl_point_key]".
    change Archi.ptr64 with true. hred_r.
    change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs Ptrofs.zero). iPoseProof (add_null_r with "tl_ofs") as "%". rewrite H0. rename H0 into tl_add_null.
    iPoseProof (live_has_offset with "tl_ofs") as "[tl_ofs tl_ofs_ofs]".
    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV tl_point_item tl_ofs_ofs"; iFrame.
    { iExists _. iFrame. iPureIntro. rewrite encode_val_length. splits; et. exists 0. ss. }
    iIntros (st_src2 st_tgt2) "[INV tl_point_item]". rewrite decode_encode_item.
    (* item = hd_old->item end *)

    hred_r. unhide. remove_tau. unhide. remove_tau.

    (* hd_new = (node* )hd_old->link start *)
    rewrite tl_is_ptr. hred_r. rewrite tl_is_ptr. hred_r.
    unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss.
    change Archi.ptr64 with true. hred_r.
    change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs (Ptrofs.repr 8)).
    iPoseProof (live_has_offset with "tl_ofs") as "[tl_ofs tl_ofs_ofs]".
    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV tl_point_key tl_ofs_ofs"; iFrame.
    { iExists _. iSplit. { iApply _has_offset_slide. et. } iPureIntro. rewrite encode_val_length. splits; et. exists 1. ss. }
    iIntros (st_src3 st_tgt3) "[INV tl_point_key]". change Mptr with Mint64. rewrite decode_encode_ofs.
    (* hd_new = (node* )hd_old->link end *)

    (* hdH* = hd_new start *)
    hred_r. rewrite ptrofs_cast_ptr. hred_r. unhide. remove_tau. unhide. remove_tau.
    rewrite tl_hdl_ptr. hred_r. rewrite ptrofs_cast_ptr. hred_r.
    iPoseProof (_has_offset_dup with "tl_hdl_ofs") as "[tl_hdl_ofs tl_hdl_ofs_ofs]".
    iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV tl_hdl_point tl_hdl_ofs_ofs"; iFrame.
    { iExists _,_. iFrame. iPureIntro. rewrite encode_val_length. et. }
    iIntros (st_src4 st_tgt4) "[INV tl_hdl_point]".
    (* hdH* = hd_new end *)

    (* if (hd_new == NULL) start *)
    hred_r. unhide. remove_tau. unhide. remove_tau.
    change Archi.ptr64 with true. hred_r.
    replace (Vlong (Int64.repr _)) with Vnullptr by et.
    iPoseProof (null_equiv with "tl_next_equiv") as "%".
    assert (i_tl_next = Ptrofs.zero).
    { unfold Vptrofs, Vnullptr in *.
      destruct Archi.ptr64 eqn:?. 2:{ clarify. }
      apply (f_equal (fun v => match v with Vlong i => i | _ => Int64.zero end)) in H0.
      apply (f_equal Ptrofs.of_int64) in H0. rewrite Ptrofs.of_int64_to_int64 in H0; et. }
    subst. clear H0. rewrite Ptrofs.xor_zero_l.

    destruct lnext.
    (* case: delete from singleton list *)
    -
      ss. iDestruct "LIST" as "[tl_equiv NULL_next]".
      iPoseProof (equiv_sym with "NULL_next") as "H". iPoseProof (null_equiv with "H") as "%". rewrite H0. clear H0 i_tl_prev.
      iApply isim_ccallU_cmp_ptr0; ss; oauto.
      iSplitL "INV"; iFrame.
      iIntros (st_src5 st_tgt5) "INV".
      hred_r. des_ifs_safe. clear Heq. unhide. remove_tau.
      (* if (hd_new == NULL) end *)

      (* tlH* = NULL start *)
      iPoseProof (points_to_is_ptr with "hd_hdl_point") as "%". rewrite H0. rename H0 into hd_hdl_ptr.
      hred_r. change Archi.ptr64 with true. hred_r.
      rewrite cast_long; et. hred_r.
      iPoseProof (_has_offset_dup with "hd_hdl_ofs") as "[hd_hdl_ofs hd_hdl_ofs_ofs]".

      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV hd_hdl_point hd_hdl_ofs_ofs"; iFrame.
      { iExists _,_. iFrame. iPureIntro. rewrite encode_val_length; et. }
      iIntros (st_src6 st_tgt6) "[INV hd_hdl_point]".
      (* tlH* = NULL end *)

      hred_r. unhide. remove_tau.

      (* free(hd_old) start *)
      hexploit SKINCLENV.
      { instantiate (2:="free"). et. }
      i. des. ss. rewrite H0. rename H0 into free_loc. hred_r.

      iPoseProof ((@point_cast_ptr _ _ Es) with "tl_point_item") as "%".
      rewrite H0. rename H0 into tl_old_cast. hred_r. des_ifs_safe. clear e.

      replace (pred _) with blk by nia.
      erewrite SKINCLGD; et; [|ss; et]. hred_r.

      iCombine "tl_point_item tl_point_key" as "tl_point".
      replace (Val.addl tl_old (Vlong _))
        with (Val.addl tl_old (Vptrofs (Ptrofs.repr (strings.length (inj_bytes (encode_int 8 (Int64.unsigned tl_item))))))) by et.
      iPoseProof (points_to_collect with "tl_point") as "tl_point".

      iApply isim_ccallU_mfree; ss; oauto.
      iSplitL "INV tl_point tl_ofs"; iFrame.
      { iExists _,_. iFrame. ss. }
      iIntros (st_src7 st_tgt7) "INV".
      (* free(hd_old) end *)

      hred_r. unhide. remove_tau. change Archi.ptr64 with true. ss.
      rewrite cast_long; et. hred_r.


      (* prove post condition *)
      hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret. iFrame. iSplit; ss. iSplit; ss. iExists _,_,_,_,_,_. iFrame; ss.

    (* case: list length is more than 1 *)
    - ss. destruct v; clarify.
      iDestruct "LIST" as (i_tl i_tl_pp m_tl_prev) "[[[[% tl_equiv] tl_prev_ofs] tl_prev_point] LIST]". rename H0 into m_tl_prev_size. rename i into tl_prev_item.
      iPoseProof (sub_null_r with "tl_prev_ofs") as "%". rename H0 into tl_prev_sub_r.

      (* node* hd_new = (node* )hd_old->link start *)

      iApply isim_ccallU_cmp_ptr3; ss; oauto.
      rewrite tl_prev_sub_r.
      iSplitL "INV tl_prev_ofs"; iFrame.
      { iPureIntro. red. rewrite m_tl_prev_size. change (Ptrofs.unsigned Ptrofs.zero) with 0%Z. change (size_chunk Mptr) with 8%Z. nia. }
      iIntros (st_src5 st_tgt5) "[INV tl_prev_ofs]".
      (* if (hd_new == NULL) end *)

      hred_r. des_ifs_safe. clear Heq. unhide. hred_r. unhide. remove_tau.

      (* link = (node* )hd_new->link start *)
      iPoseProof (points_to_is_ptr with "tl_prev_point") as "%". rewrite H0. rename H0 into tl_prev_is_ptr. hred_r. rewrite tl_prev_is_ptr. hred_r.
      iPoseProof (points_to_split with "tl_prev_point") as "[tl_prev_point_item tl_prev_point_key]".
      change (strings.length _) with 8. ss.

      unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss.
      change Archi.ptr64 with true. hred_r.
      change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs (Ptrofs.repr 8)).
      iPoseProof (live_has_offset with "tl_prev_ofs") as "[tl_prev_ofs tl_prev_ofs_ofs]".
      iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV tl_prev_point_key tl_prev_ofs_ofs"; iFrame.
      { iExists _. iSplit. { iApply _has_offset_slide. et. } iPureIntro. rewrite encode_val_length. splits; et. exists 1. ss. }
      iIntros (st_src6 st_tgt6) "[INV tl_prev_point_key]".
      change Mptr with Mint64. rewrite decode_encode_ofs.
      (* hd_new = (node* )hd_old->link end *)

      hred_r. unhide. remove_tau. unhide. remove_tau.

      (* hd_new->link = link ^ (intptr_t)hd_old start *)
      iPoseProof ((@point_cast_ptr _ _ Es) with "tl_point_item") as "%".
      rewrite H0. rename H0 into tl_old_cast. hred_r.

      iApply isim_ccallU_capture1; ss; oauto.
      iSplitL "INV tl_ofs"; iFrame.
      { rewrite tl_sub_r. et. }
      iIntros (st_src7 st_tgt7 i) "[INV [tl_ofs tl_equiv']]".

      iCombine "tl_equiv' tl_equiv" as "tl_equiv". iPoseProof (capture_unique with "tl_equiv") as "%". clarify. iDestruct "tl_equiv" as "[_ tl_equiv]".

      hred_r. unhide. remove_tau.
      rewrite tl_prev_is_ptr. hred_r. rewrite tl_prev_is_ptr. hred_r.
      unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members.
      ss. change Archi.ptr64 with true. hred_r.
      do 2 rewrite ptrofs_cast_ptr. hred_r. des_ifs_safe.
      hred_r. rewrite cast_long; et. hred_r.

      change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs (Ptrofs.repr 8)).
      iPoseProof (live_has_offset with "tl_prev_ofs") as "[tl_prev_ofs tl_prev_ofs_ofs]".
      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV tl_prev_point_key tl_prev_ofs_ofs"; iFrame.
      { iExists _,_. iFrame. iSplit. 2:{ iApply _has_offset_slide. et. }
        iPureIntro. rewrite encode_val_length. split; ss. exists 1. ss. }
      iIntros (st_src8 st_tgt8) "[INV tl_prev_point_key]".
      (* hd_new->link = link ^ (intptr_t)hd_old end *)

      hred_r. unhide. remove_tau.

      (* free(hd_old) start *)
      hexploit SKINCLENV.
      { instantiate (2:="free"). et. }
      i. des. ss. rewrite H0. rename H0 into free_loc. hred_r.
      rewrite tl_old_cast. hred_r.
      destruct (Ptrofs.eq_dec) eqn:?; clarify. clear e Heqs.
      replace (pred _) with blk by nia.
      erewrite SKINCLGD; et; [|ss; et]. hred_r.

      iCombine "tl_point_item tl_point_key" as "tl_point".
      iPoseProof (points_to_collect with "tl_point") as "tl_point".

      iApply isim_ccallU_mfree; ss; oauto.
      rewrite tl_sub_r.
      iSplitL "INV tl_point tl_ofs"; iFrame.
      { iExists _,_. iFrame. iPureIntro. ss. }
      iIntros (st_src12 st_tgt12) "INV".
      (* free(hd_old) end *)

      hred_r. unhide. remove_tau. change Archi.ptr64 with true. ss.
      rewrite cast_long; et. hred_r.

      (* prove post condition *)
      hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret. iFrame. iSplit; ss. rewrite last_last. iSplit; ss.
      change 8%Z with (Z.of_nat (strings.length (encode_val Mint64 (Vlong tl_prev_item)))).
      iCombine "tl_prev_point_item tl_prev_point_key" as "tl_prev_point".  iPoseProof (points_to_collect with "tl_prev_point") as "tl_prev_point".
      iExists _,_,_,_,_,_. iFrame. iSplit; ss.
      rewrite removelast_last. rewrite <- (rev_involutive (rev lnext ++ _)).
      iApply rev_xorlist. rewrite rev_app_distr. rewrite rev_involutive.
      change (rev [Vlong tl_prev_item]) with [Vlong tl_prev_item]. ss.
      iExists _,_,_. iFrame. rewrite Ptrofs.xor_zero_l.
      iSplit; ss. replace (Vlong (Int64.xor i i0)) with (Vptrofs i_tl_pp); et.
      clear - Heq Heq0. unfold Vptrofs in *. des_ifs. f_equal.
      rewrite int64_ptrofs_xor_comm.
      rewrite Ptrofs.xor_commut.
      rewrite <- Ptrofs.xor_assoc.
      rewrite Ptrofs.xor_idem.
      rewrite Ptrofs.xor_zero_l. et.
  Qed.

  Lemma sim_delete_hd :
    sim_fnsem wf top2
      ("delete_hd", fun_to_tgt "xorlist" (GlobalStb sk) (mk_pure delete_hd_spec))
      ("delete_hd", cfunU (decomp_func sk ce f_delete_hd)).
  Proof.
    Local Opaque encode_val.
    eassert (_xor = _).
    { unfold _xor. vm_compute (Linking.link _ _). reflexivity. }
    rewrite H0 in *. clear H0. destruct Ctypes.link_build_composite_env. destruct a.
    inversion VALID_link. clear VALID_link. subst.
    clear a. simpl in ce.
    econs; ss. red.

    (* current state: 1 *)
    get_composite ce e.

    dup SKINCL. rename SKINCL0 into SKINCLENV.
    apply incl_incl_env in SKINCLENV.
    unfold incl_env in SKINCLENV.
    pose proof sk_incl_gd as SKINCLGD.

    apply isim_fun_to_tgt; auto.
    unfold f_delete_hd. i; ss.
    unfold decomp_func, function_entry_c. ss.
    let H := fresh "HIDDEN" in
    set (H := hide 1).

    iIntros "[INV PRE]". des_ifs_safe. ss.
    iDestruct "PRE" as "[[% PRE] %]". unfold full_xorlist.
    iDestruct "PRE"
      as (m_hd_hdl m_tl_hdl hd_old tl_old ofs_hd_hdl ofs_tl_hdl)
      "[[[[[[hd_hdl_point hd_hdl_ofs] %] tl_hdl_point] tl_hdl_ofs] %] LIST]".
    clarify. hred_r. unhide. hred_r. unhide. remove_tau.
    rename v into hd_handler.  rename v0 into tl_handler.
    rename l into linput.
    des. clarify.
    rename H0 into tl_hdl_align.
    rename H1 into hd_hdl_align.
    rename H2 into hd_hdl_sz.
    rename H3 into tl_hdl_sz.

    (* current state: 2 *)
    unhide. hred_r. unhide. remove_tau.

    (* node hd_old = *hdH start *)
    iPoseProof (points_to_is_ptr with "hd_hdl_point") as "%". rewrite H0. rename H0 into hd_hdl_ptr.
    hred_r. iApply isim_apc. iExists (Some (20%nat : Ord.t)).
    iPoseProof (xorlist_hd_deen with "LIST") as "%". rename H0 into hd_deen.
    iPoseProof (xorlist_hd_not_Vundef with "LIST") as "%". rename H0 into hd_notundef.
    iPoseProof (_has_offset_dup with "hd_hdl_ofs") as "[hd_hdl_ofs hd_hdl_ofs_ofs]".
    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hd_hdl_point hd_hdl_ofs_ofs"; iFrame.
    { iExists _. iFrame. iPureIntro. rewrite encode_val_length. splits; et. apply Memory.Mem.encode_val_change_check_false. }
    iIntros (st_src0 st_tgt0) "[INV hd_hdl_point]".
    rewrite hd_deen.
    (* node hd_old = *hdH end *)

    (* if (hd_old != NULL) start *)
    hred_r. unhide. remove_tau. unhide. remove_tau.
    change Archi.ptr64 with true. hred_r.
    change (Vlong (Int64.repr _)) with Vnullptr.
    destruct linput as [|v lnext].
    (* case: nil list *)
    {
      ss.
      iDestruct "LIST" as "[NULL_tl NULL_hd]".
      iPoseProof (null_equiv with "NULL_tl") as "%". subst.
      iPoseProof (equiv_sym with "NULL_hd") as "H". iPoseProof (null_equiv with "H") as "%". subst.
      iApply isim_ccallU_cmp_ptr0; ss; oauto.
      iSplitL "INV"; iFrame.
      iIntros (st_src1 st_tgt1) "INV".

      hred_r. destruct (Int.eq) eqn:?; ss; clarify. clear Heqb.
      (* if (hd_old != NULL) end *)

      unhide. hred_r. unhide. remove_tau. change Archi.ptr64 with true. ss.
      change Vnullptr with (Vptrofs Ptrofs.zero).
      rewrite ptrofs_cast_ptr. hred_r.

      (* prove post condition *)
      hred_l. iApply isim_choose_src.
      iExists _. iApply isim_ret.
      iFrame. iSplit; ss. iSplit; ss.
      iExists _,_,_,_,_,_. iFrame. iSplit; ss.
    }
    (* case: not nil list *)
    ss. destruct v; try solve [iDestruct "LIST" as "[]"]. rename i into hd_item.
    iDestruct "LIST" as (i_hd_prev i_hd_next m_hd_old) "[[[[% hd_prev_equiv] hd_ofs] hd_point] LIST]". rename H0 into m_hd_size.
    iPoseProof (sub_null_r with "hd_ofs") as "%". rename H0 into hd_sub_r.

    (* node* hd_new = (node* )hd_old->link start *)

    iApply isim_ccallU_cmp_ptr4; ss; oauto.
    rewrite hd_sub_r.
    iSplitL "INV hd_ofs"; iFrame.
    { iPureIntro. red. rewrite m_hd_size. change (size_chunk Mptr) with 8%Z. change (Ptrofs.unsigned Ptrofs.zero) with 0%Z. nia. }
    iIntros (st_src1 st_tgt1) "[INV hd_ofs]".
    hred_r. destruct (Int.eq) eqn: ?; ss; clarify. clear Heqb.
    (* if (hd_old != NULL) end *)

    unhide. hred_r. unhide. remove_tau.

    (* item = hd_old->item start *)
    iPoseProof (points_to_is_ptr with "hd_point") as "%". rewrite H0. rename H0 into hd_is_ptr. hred_r. rewrite hd_is_ptr. hred_r.
    unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss. hred_r.
    iPoseProof (points_to_split with "hd_point") as "[hd_point_item hd_point_key]".
    change Archi.ptr64 with true. hred_r.
    change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs Ptrofs.zero). iPoseProof (add_null_r with "hd_ofs") as "%". rewrite H0. rename H0 into hd_add_null.
    iPoseProof (live_has_offset with "hd_ofs") as "[hd_ofs hd_ofs_ofs]".

    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hd_point_item hd_ofs_ofs"; iFrame.
    { iExists _. iFrame. iPureIntro. rewrite encode_val_length. splits; et. exists 0. ss. }
    iIntros (st_src2 st_tgt2) "[INV hd_point_item]". rewrite decode_encode_item.
    (* item = hd_old->item end *)

    hred_r. unhide. remove_tau. unhide. remove_tau.

    (* hd_new = (node* )hd_old->link start *)
    rewrite hd_is_ptr. hred_r. rewrite hd_is_ptr. hred_r.
    unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss.
    change Archi.ptr64 with true. hred_r.
    change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs (Ptrofs.repr 8)).
    iPoseProof (live_has_offset with "hd_ofs") as "[hd_ofs hd_ofs_ofs]".
    iApply isim_ccallU_load; ss; oauto.
    iSplitL "INV hd_point_key hd_ofs_ofs"; iFrame.
    { iExists _. iSplit. { iApply _has_offset_slide. et. } iPureIntro. rewrite encode_val_length. splits; et. exists 1. ss. }
    iIntros (st_src3 st_tgt3) "[INV hd_point_key]". change Mptr with Mint64. rewrite decode_encode_ofs.
    (* hd_new = (node* )hd_old->link end *)

    (* hdH* = hd_new start *)
    hred_r. rewrite ptrofs_cast_ptr. hred_r. unhide. remove_tau. unhide. remove_tau.
    rewrite hd_hdl_ptr. hred_r. rewrite ptrofs_cast_ptr. hred_r.
    iPoseProof (_has_offset_dup with "hd_hdl_ofs") as "[hd_hdl_ofs hd_hdl_ofs_ofs]".
    iApply isim_ccallU_store; ss; oauto.
    iSplitL "INV hd_hdl_point hd_hdl_ofs_ofs"; iFrame.
    { iExists _,_. iFrame. iPureIntro. rewrite encode_val_length. et. }
    iIntros (st_src4 st_tgt4) "[INV hd_hdl_point]".
    (* hdH* = hd_new end *)

    (* if (hd_new == NULL) start *)
    hred_r. unhide. remove_tau. unhide. remove_tau.
    change Archi.ptr64 with true. hred_r.
    replace (Vlong (Int64.repr _)) with Vnullptr by et.
    iPoseProof (null_equiv with "hd_prev_equiv") as "%".
    assert (i_hd_prev = Ptrofs.zero).
    { unfold Vptrofs, Vnullptr in *.
      destruct Archi.ptr64 eqn:?. 2:{ clarify. }
      apply (f_equal (fun v => match v with Vlong i => i | _ => Int64.zero end)) in H0.
      apply (f_equal Ptrofs.of_int64) in H0. rewrite Ptrofs.of_int64_to_int64 in H0; et. }
    subst. clear H0. rewrite Ptrofs.xor_zero_l.

    destruct lnext.
    (* case: delete from singleton list *)
    -
      ss. iDestruct "LIST" as "[tl_equiv NULL_next]".
      iPoseProof (equiv_sym with "NULL_next") as "H". iPoseProof (null_equiv with "H") as "%". rewrite H0. clear H0 i_hd_next.
      iApply isim_ccallU_cmp_ptr0; ss; oauto.
      iSplitL "INV"; iFrame.
      iIntros (st_src5 st_tgt5) "INV".
      hred_r. des_ifs_safe. clear Heq. unhide. remove_tau.
      (* if (hd_new == NULL) end *)

      (* tlH* = NULL start *)
      iPoseProof (points_to_is_ptr with "tl_hdl_point") as "%". rewrite H0. rename H0 into tl_hdl_ptr.
      hred_r. change Archi.ptr64 with true. hred_r.
      rewrite cast_long; et. hred_r.
      iPoseProof (_has_offset_dup with "tl_hdl_ofs") as "[tl_hdl_ofs tl_hdl_ofs_ofs]".

      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV tl_hdl_point tl_hdl_ofs_ofs"; iFrame.
      { iExists _,_. iFrame. iPureIntro. rewrite encode_val_length; et. }
      iIntros (st_src6 st_tgt6) "[INV tl_hdl_point]".
      (* tlH* = NULL end *)

      hred_r. unhide. remove_tau.

      (* free(hd_old) start *)
      hexploit SKINCLENV.
      { instantiate (2:="free"). et. }
      i. des. ss. rewrite H0. rename H0 into free_loc. hred_r.

      iPoseProof ((@point_cast_ptr _ _ Es) with "hd_point_item") as "%".
      rewrite H0. rename H0 into hd_old_cast. hred_r. des_ifs_safe. clear e.

      replace (pred _) with blk by nia.
      erewrite SKINCLGD; et; [|ss; et]. hred_r.

      iCombine "hd_point_item hd_point_key" as "hd_point".
      replace (Val.addl tl_old (Vlong _))
        with (Val.addl tl_old (Vptrofs (Ptrofs.repr (strings.length (inj_bytes (encode_int 8 (Int64.unsigned hd_item))))))) by et.
      iPoseProof (points_to_collect with "hd_point") as "hd_point".

      iApply isim_ccallU_mfree; ss; oauto.
      iSplitL "INV hd_point hd_ofs"; iFrame.
      { iExists _,_. iFrame. ss. }
      iIntros (st_src7 st_tgt7) "INV".
      (* free(hd_old) end *)

      hred_r. unhide. remove_tau. change Archi.ptr64 with true. ss.
      rewrite cast_long; et. hred_r.

      (* prove post condition *)
      hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret. iFrame. iSplit; ss. iSplit; ss. iExists _,_,_,_,_,_. iFrame; ss.

    (* case: list length is more than 1 *)
    - ss. destruct v; clarify.
      iDestruct "LIST" as (i_hd i_hd_nn m_hd_next) "[[[[% hd_equiv] hd_next_ofs] hd_next_point] LIST]". rename H0 into m_hd_next_size. rename i into hd_next_item.
      iPoseProof (sub_null_r with "hd_next_ofs") as "%". rename H0 into hd_next_sub_r.

      (* node* hd_new = (node* )hd_old->link start *)

      iApply isim_ccallU_cmp_ptr3; ss; oauto.
      rewrite hd_next_sub_r.
      iSplitL "INV hd_next_ofs"; iFrame.
      { iPureIntro. red. rewrite m_hd_next_size. change (Ptrofs.unsigned Ptrofs.zero) with 0%Z. change (size_chunk Mptr) with 8%Z. nia. }
      iIntros (st_src5 st_tgt5) "[INV hd_next_ofs]".
      (* if (hd_new == NULL) end *)

      hred_r. des_ifs_safe. clear Heq. unhide. hred_r. unhide. remove_tau.

      (* link = (node* )hd_new->link start *)
      iPoseProof (points_to_is_ptr with "hd_next_point") as "%". rewrite H0. rename H0 into hd_next_is_ptr. hred_r. rewrite hd_next_is_ptr. hred_r.
      iPoseProof (points_to_split with "hd_next_point") as "[hd_next_point_item hd_next_point_key]".
      change (strings.length _) with 8. ss.

      unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members. ss.
      change Archi.ptr64 with true. hred_r.
      change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs (Ptrofs.repr 8)).

      iPoseProof (live_has_offset with "hd_next_ofs") as "[hd_next_ofs hd_next_ofs_ofs]".
      iApply isim_ccallU_load; ss; oauto.
      iSplitL "INV hd_next_point_key hd_next_ofs_ofs"; iFrame.
      { iExists _. iSplit. { iApply _has_offset_slide. et. } iPureIntro. rewrite encode_val_length. splits; et. exists 1. ss. }
      iIntros (st_src6 st_tgt6) "[INV hd_next_point_key]".
      change Mptr with Mint64. rewrite decode_encode_ofs.
      (* hd_new = (node* )hd_old->link end *)

      hred_r. unhide. remove_tau. unhide. remove_tau.

      (* hd_new->link = link ^ (intptr_t)hd_old start *)
      iPoseProof ((@point_cast_ptr _ _ Es) with "hd_point_item") as "%".
      rewrite H0. rename H0 into hd_old_cast. hred_r.

      iApply isim_ccallU_capture1; ss; oauto.
      iSplitL "INV hd_ofs"; iFrame.
      { rewrite hd_sub_r. et. }
      iIntros (st_src7 st_tgt7 i) "[INV [hd_ofs hd_equiv']]".

      iCombine "hd_equiv' hd_equiv" as "hd_equiv". iPoseProof (capture_unique with "hd_equiv") as "%". clarify. iDestruct "hd_equiv" as "[_ hd_equiv]".

      hred_r. unhide. remove_tau.
      rewrite hd_next_is_ptr. hred_r. rewrite hd_next_is_ptr. hred_r.
      unfold __Node, ident. rewrite get_co. hred_r. rewrite co_co_members.
      ss. change Archi.ptr64 with true. hred_r.
      do 2 rewrite ptrofs_cast_ptr. hred_r. des_ifs_safe.
      hred_r. rewrite cast_long; et. hred_r.

      change (Vptrofs (Ptrofs.repr (Coqlib.align _ _))) with (Vptrofs (Ptrofs.repr 8)).
      iPoseProof (live_has_offset with "hd_next_ofs") as "[hd_next_ofs hd_next_ofs_ofs]".
      iApply isim_ccallU_store; ss; oauto.
      iSplitL "INV hd_next_point_key hd_next_ofs_ofs"; iFrame.
      { iExists _,_. iFrame. iSplit. 2:{ iApply _has_offset_slide. et. }
        iPureIntro. rewrite encode_val_length. split; ss. exists 1. ss. }
      iIntros (st_src8 st_tgt8) "[INV hd_next_point_key]".
      (* hd_new->link = link ^ (intptr_t)hd_old end *)

      hred_r. unhide. remove_tau.

      (* free(hd_old) start *)
      hexploit SKINCLENV.
      { instantiate (2:="free"). et. }
      i. des. ss. rewrite H0. rename H0 into free_loc. hred_r.
      rewrite hd_old_cast. hred_r.
      destruct (Ptrofs.eq_dec) eqn:?; clarify. clear e Heqs.
      replace (pred _) with blk by nia.
      erewrite SKINCLGD; et; [|ss; et]. hred_r.

      iCombine "hd_point_item hd_point_key" as "hd_point".
      iPoseProof (points_to_collect with "hd_point") as "hd_point".

      iApply isim_ccallU_mfree; ss; oauto.
      rewrite hd_sub_r.
      iSplitL "INV hd_point hd_ofs"; iFrame.
      { iExists _,_. iFrame. iPureIntro. ss. }
      iIntros (st_src12 st_tgt12) "INV".
      (* free(hd_old) end *)

      hred_r. unhide. remove_tau. change Archi.ptr64 with true. ss. rewrite cast_long; et. hred_r.

      (* prove post condition *)
      hred_l. iApply isim_choose_src. iExists _.
      iApply isim_ret. iFrame. iSplit; ss. iSplit; ss.
      change 8%Z with (Z.of_nat (strings.length (encode_val Mint64 (Vlong hd_next_item)))).
      iCombine "hd_next_point_item hd_next_point_key" as "hd_next_point".  iPoseProof (points_to_collect with "hd_next_point") as "hd_next_point".
      iExists _,_,_,_,_,_. iFrame. iSplit; ss.
      iExists _,_,_. iFrame. rewrite Ptrofs.xor_zero_l.
      iSplit; ss. replace (Vlong (Int64.xor i i0)) with (Vptrofs i_hd_nn); et.
      clear - Heq Heq0. unfold Vptrofs in *. des_ifs. f_equal.
      rewrite int64_ptrofs_xor_comm.
      rewrite Ptrofs.xor_commut.
      rewrite <- Ptrofs.xor_assoc.
      rewrite Ptrofs.xor_idem.
      rewrite Ptrofs.xor_zero_l. et.
  Qed.

  End SIMFUNS.

End PROOF.

