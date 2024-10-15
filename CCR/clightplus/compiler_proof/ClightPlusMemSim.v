From compcert Require Import Globalenvs Smallstep AST Integers Events Behaviors Errors Memory Values Maps.
Require Import CoqlibCCR.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import ClightPlusMem0.

Require Import ClightPlusSkel ClightPlusExprgen.
Require Import ClightPlusMatchEnv.
Require Import ClightPlusLenvSim.

From compcert Require Import Clight Clightdefs.

Set Implicit Arguments.


Section MEM.

  Lemma nth_error_map A B (f: A -> B) k l
    :
    nth_error (List.map f l) k = option_map f (nth_error l k).
  Proof.
    revert k. induction l; ss; i.
    { destruct k; ss. }
    { destruct k; ss. }
  Qed.

  Import List.

  Local Transparent load_skenv.

  Local Open Scope positive.

  Lemma map_blk_local_region :
    forall sk tge blk
      (ALLOCED : Pos.of_succ_nat (length sk) <= blk),
      (<<ALLOCMAP: tge.(Genv.genv_next) <= map_blk sk tge blk>>).
  Proof.
    i. red. unfold map_blk.
    set (Z.add _ _) as t1.
    assert (t1 > 0)%Z by now unfold t1; nia.
    destruct t1 eqn: E3; try nia.
    des_ifs; try rewrite Pos.leb_le in Heq; try rewrite Pos.leb_gt in Heq; try nia.
  Qed.

  Lemma map_blk_global_region :
    forall sk tge blk
      (SRC_GLOBAL: not (Pos.of_succ_nat (length sk) <= blk))
      (MGE : match_ge sk tge),
      (<<TGT_GLOBAL: map_blk sk tge blk < tge.(Genv.genv_next)>>).
  Proof.
    i. inv MGE. red. unfold map_blk. des_ifs; try nia.
    - eapply Genv.genv_symb_range. et.
    - apply load_skenv_wf in WFSK. unfold SkEnv.wf in WFSK. apply WFSK in Heq. apply MGE0 in Heq. clarify.
    - assert (H0: (Init.Nat.pred (Pos.to_nat blk) < length sk)%nat) by nia.
      apply nth_error_Some in H0. unfold load_skenv in Heq. ss. uo. des_ifs.
  Qed.

  Local Open Scope Z.

  Lemma map_blk_inj :
    forall sk tge b1 b2 (MGE: match_ge sk tge),
    map_blk sk tge b1 = map_blk sk tge b2 -> b1 = b2.
  Proof.
    i. dup H. rename H0 into T.
    unfold map_blk in H.
    destruct (le_dec _ _) in H;
     destruct (le_dec _ _) in H.
    - set (Z.add _ _) as t1 in H. set (Z.add _ _) as t2 in H.
      assert (t1 > 0) by now unfold t1; nia.
      assert (t2 > 0) by now unfold t2; nia.
      destruct t1 eqn: E3; destruct t2 eqn: E4; try nia.
    - eapply map_blk_global_region in n; et. apply map_blk_local_region with (tge := tge) in l. red in n. red in l. nia.
    - eapply map_blk_global_region in n; et. apply map_blk_local_region with (tge := tge) in l. red in n. red in l. nia.
    - inv MGE.
      assert (H0: (Init.Nat.pred (Pos.to_nat b1) < length sk)%nat) by nia.
      assert (H1: (Init.Nat.pred (Pos.to_nat b2) < length sk)%nat) by nia.
      apply nth_error_Some in H0.
      apply nth_error_Some in H1.
      destruct (nth_error _) eqn: T1 in H0; clarify.
      destruct (nth_error _) eqn: T2 in H1; clarify.
      clear H0 H1.
      destruct (SkEnv.blk2id _ _) eqn: H0 in H.
      2:{ unfold load_skenv in *. ss. uo. des_ifs. }
      destruct (SkEnv.blk2id _ _) eqn: H1 in H.
      2:{ unfold load_skenv in *. ss. uo. des_ifs. }
      clear T1 T2.
      apply load_skenv_wf in WFSK. red in WFSK. unfold SkEnv.wf in WFSK.
      apply WFSK in H0. apply WFSK in H1.
      dup H0. dup H1.
      apply MGE0 in H2. apply MGE0 in H3. des_ifs; clarify.
      destruct (Pos.eq_dec (ident_of_string s) (ident_of_string s0)); cycle 1.
      + hexploit Genv.global_addresses_distinct; et. clarify.
      + apply ident_of_string_injective in e. subst.
        set (Some _) as t1 in H0.
        set (Some _) as t2 in H1.
        assert (t1 = t2) by now rewrite <- H0; et.
        unfold t1, t2 in H. clearbody t1 t2. clarify.
        nia.
  Qed.

  Lemma map_val_inj :
    forall sk tge v1 v2 (MGE: match_ge sk tge),
    <<INJ: map_val sk tge v1 = map_val sk tge v2 -> v1 = v2>>.
  Proof. i. red. unfold map_val. i. des_ifs. f_equal. eapply map_blk_inj; et. Qed.

  Lemma map_memval_inj :
    forall sk tge mv1 mv2 (MGE: match_ge sk tge),
    <<INJ: map_memval sk tge mv1 = map_memval sk tge mv2 -> mv1 = mv2>>.
  Proof. i. red. unfold map_memval. i. des_ifs. f_equal. eapply map_val_inj; et. Qed.

  Local Transparent Mem.alloc.
  Local Transparent Mem.free.
  Local Transparent Mem.load.
  Local Transparent Mem.store.
  Local Transparent Mem.loadbytes.
  Local Transparent Mem.storebytes.


  Lemma match_mem_free m tm b lo hi m' sk tge
        (SMEM: Mem.free m b lo hi = Some m')
        (MGE: match_ge sk tge)
        (MM_PRE: match_mem sk tge m tm)
    :
    exists tm',
        (<<TMEM: Mem.free tm (map_blk sk tge b) lo hi = Some tm'>>) /\
        (<<MM_POST: match_mem sk tge m' tm'>>).
  Proof.
    inv MM_PRE. unfold Mem.free in *. eexists. split.
    - des_ifs. exfalso. apply n. unfold Mem.range_perm, Mem.perm in *.
      i. rewrite <- MEM_PERM. et.
    - des_ifs. unfold Mem.unchecked_free. econs; et.
      ss. i. set (Pos.eq_dec b b0) as x. destruct x.
      + subst. repeat rewrite PMap.gss. repeat rewrite MEM_PERM. et.
      + rewrite PMap.gso by et.
        assert (map_blk sk tge b <> map_blk sk tge b0).
        { red. i. apply n. apply map_blk_inj in H; et. }
        rewrite PMap.gso; et.
  Qed.

  Lemma _match_mem_free_list m tm l m' sk tge
        (SMEM: Mem.free_list m l = Some m')
        (MGE: match_ge sk tge)
        (MM_PRE: match_mem sk tge m tm)
    :
    exists tm',
        (<<TMEM: Mem.free_list tm (map (fun '(b, lo, hi) => (map_blk sk tge b, lo, hi)) l) = Some tm'>>) /\
        (<<MM_POST: match_mem sk tge m' tm'>>).
  Proof.
    depgen m. revert m' tm. induction l; i; ss; clarify.
    - eexists; et.
    - des_ifs_safe. hexploit match_mem_free; et. i. des. rewrite TMEM.
      hexploit IHl; et.
  Qed.

  Import Permutation.

  Lemma mem_eq m m' : m.(Mem.nextblock) = m'.(Mem.nextblock) -> m.(Mem.mem_contents) = m'.(Mem.mem_contents) -> m.(Mem.mem_concrete) = m'.(Mem.mem_concrete) -> m.(Mem.mem_access) = m'.(Mem.mem_access) -> m = m'.
  Proof.
    i. destruct m, m'. ss. subst.
    assert (access_max = access_max0) by apply proof_irr.
    assert (nextblock_noaccess = nextblock_noaccess0) by apply proof_irr.
    assert (contents_default = contents_default0) by apply proof_irr.
    assert (nextblocks_logical = nextblocks_logical0) by apply proof_irr.
    assert (valid_address_bounded = valid_address_bounded0) by apply proof_irr.
    assert (no_concrete_overlap = no_concrete_overlap0) by apply proof_irr.
    assert (concrete_align = concrete_align0) by apply proof_irr.
    assert (weak_valid_address_range = weak_valid_address_range0) by apply proof_irr.
    subst. et.
  Qed.

  Lemma free_list_same m m' m'' l :
    Mem.free_list m l = Some m' ->
    m.(Mem.nextblock) = m''.(Mem.nextblock) ->
    m.(Mem.mem_contents) = m''.(Mem.mem_contents) ->
    m.(Mem.mem_concrete) = m''.(Mem.mem_concrete) ->
    (forall b, PMap.get b m.(Mem.mem_access) = PMap.get b m''.(Mem.mem_access)) ->
    exists m''', Mem.free_list m'' l = Some m''' /\
    m'.(Mem.nextblock) = m'''.(Mem.nextblock) /\
    m'.(Mem.mem_contents) = m'''.(Mem.mem_contents) /\
    m'.(Mem.mem_concrete) = m'''.(Mem.mem_concrete) /\
    forall b, PMap.get b m'.(Mem.mem_access) = PMap.get b m'''.(Mem.mem_access).
  Proof.
    ginduction l; i; ss; clarify. { esplits; et. }
    des_ifs; cycle 1.
    - unfold Mem.free in *. des_ifs. exfalso. apply n.
      unfold Mem.range_perm, Mem.perm. i. rewrite <- H3.
      eapply r; et.
    - unfold Mem.free in *. des_ifs. eapply IHl; et.
      unfold Mem.unchecked_free. ss.
      i. destruct (dec b b0). { subst. rewrite !PMap.gss. rewrite H3. et. }
      rewrite !PMap.gso; et.
  Qed.

  Lemma free_list_permutation m m' l l' :
    Mem.free_list m l = Some m' ->
    Permutation l l' ->
    exists m'', Mem.free_list m l' = Some m''
    /\ m'.(Mem.nextblock) = m''.(Mem.nextblock)
    /\ m'.(Mem.mem_contents) = m''.(Mem.mem_contents)
    /\ m'.(Mem.mem_concrete) = m''.(Mem.mem_concrete)
    /\ (forall b, PMap.get b m'.(Mem.mem_access) = PMap.get b m''.(Mem.mem_access)).
  Proof.
    i. revert m m' H. induction H0; ss; i; clarify.
    - esplits; et.
    - des_ifs. apply IHPermutation. et.
    - des_ifs_safe. destruct (Mem.free m b) eqn:?; cycle 1.
      + unfold Mem.free in Heqo. des_ifs. exfalso. apply n.
        unfold Mem.range_perm, Mem.perm. i. unfold Mem.free in *.
        des_ifs. unfold Mem.range_perm, Mem.perm in r.
        hexploit r; et. i. unfold Mem.unchecked_free in H1. ss.
        destruct (dec b b0); cycle 1. { rewrite Maps.PMap.gso in H1; et. }
        subst. rewrite Maps.PMap.gss in H1.
        destruct Coqlib.zle; destruct Coqlib.zlt; ss; inv H1.
      + destruct (Mem.free m2 b0) eqn:?; cycle 1.
        * unfold Mem.free in Heqo0. des_ifs. exfalso. apply n.
          unfold Mem.range_perm, Mem.perm. i. unfold Mem.free in *.
          des_ifs. unfold Mem.unchecked_free. ss.
          destruct (dec b b0); cycle 1.
          { rewrite Maps.PMap.gso; et. apply r1. et. }
          subst. unfold Mem.range_perm, Mem.perm, Mem.unchecked_free in r0. ss.
          rewrite !Maps.PMap.gss in *.
          unfold Mem.range_perm, Mem.perm, Mem.unchecked_free in r1.
          hexploit r1; et. i.
          destruct Coqlib.zle; destruct Coqlib.zlt; ss.
          hexploit r0; et. i.
          destruct Coqlib.zle; destruct Coqlib.zlt; ss; try nia.
        * hexploit free_list_same. 1: et.
          { instantiate (1:=m3). unfold Mem.free in *. des_ifs. }
          { unfold Mem.free in *. des_ifs. }
          { unfold Mem.free in *. des_ifs. }
          { unfold Mem.free in *. des_ifs. i. ss.
            destruct (dec b b1).
            { subst. rewrite !PMap.gss. destruct (dec b0 b1).
              { subst. rewrite !PMap.gss. extensionalities.
                do 2 destruct Coqlib.zle; do 2 destruct Coqlib.zlt; ss; et. }
              rewrite (@PMap.gso _ _ b0); et.
              rewrite (@PMap.gso _ _ b0); et.
              rewrite PMap.gss. et. }
            rewrite PMap.gso; et. destruct (dec b0 b1).
            { subst. rewrite !PMap.gss. rewrite PMap.gso; et. }
            rewrite !PMap.gso; et. }
          i. des. esplits; et.
    - hexploit IHPermutation1; et. i. des.
      hexploit IHPermutation2; et. i. des.
      esplits; et.
      { rewrite <- H6. et. }
      { rewrite <- H7. et. }
      { rewrite <- H8. et. }
      i. rewrite <- H9. et.
  Qed.

  Lemma match_mem_free_list m tm m' sk ge tge ce tce e te
        (SMEM: Mem.free_list m (List.map (map_fst (fun b => (b, 0%Z))) (ClightPlusExprgen.blocks_of_env ce e)) = Some m')
        (EQ1: tce = ge.(genv_cenv))
        (EQ2: tge = ge.(genv_genv))
        (MGE: match_ge sk tge)
        (ME: match_e sk tge e te)
        (MCE: match_ce ce tce)
        (MM_PRE: match_mem sk tge m tm)
    :
    exists tm',
        (<<TMEM: Mem.free_list tm (blocks_of_env ge te) = Some tm'>>) /\
        (<<MM_POST: match_mem sk tge m' tm'>>).
  Proof.
    hexploit _match_mem_free_list; et. i. des.
    unfold ClightPlusExprgen.blocks_of_env in TMEM.
    rewrite (map_map (ClightPlusExprgen.block_of_binding ce)) in TMEM.
    erewrite <- match_block_of_binding in TMEM; et.
    set (map _ _) as l in TMEM.
    set (blocks_of_env ge te) as l'.
    assert (Permutation l l'); cycle 1.
    { hexploit free_list_permutation; et. i. des.
      esplits; et. inv MM_POST. econs; et.
      { rewrite <- H1. et. }
      { rewrite <- H2. et. }
      { i. rewrite <- H4. et. }
      { rewrite <- H3. et. } }
    unfold l, l'. clearbody l l'.
    unfold blocks_of_env.
    rewrite map_map. clear - MCE ME MGE.
    set (fun _ => _) as f.
    assert (f = (block_of_binding ge) ∘ (map_env_entry sk tge)).
    { unfold f, block_of_binding, map_env_entry. extensionalities. des_ifs_safe. destruct p. ss. clarify. }
    rewrite H. rewrite <- map_map.
    apply Permutation_map. inv ME. apply NoDup_Permutation; cycle 2.
    { i. rewrite ME0. refl. }
    { apply FinFun.Injective_map_NoDup; et. red. i. unfold map_env_entry in H0. des_ifs_safe. hexploit map_blk_inj; et. i. clarify. eapply NoDup_map_inv; et. }
    { hexploit (PTree.elements_keys_norepet te). i. rewrite <- CoqlibC.NoDup_norepet in H0. apply NoDup_map_inv in H0. et. }
  Qed.

  Lemma match_mem_getN f (c d: ZMap.t memval) n p
    (MM: forall i mv, c !! i = mv -> d !! i = f mv)
  :
    Mem.getN n p d = map f (Mem.getN n p c).
  Proof.
    revert p. induction n; i; ss.
    rewrite IHn. f_equal. erewrite <- MM; try reflexivity.
  Qed.


  Lemma match_proj_bytes sk tge l : proj_bytes (map (map_memval sk tge) l) = proj_bytes l.
  Proof. induction l; ss. rewrite IHl. destruct a; ss. Qed.

  Lemma match_proj_frag_none sk tge l : proj_fragment (map (map_memval sk tge) l) = None <-> proj_fragment l = None.
  Proof. induction l; ss. des_ifs. all: destruct IHl; hexploit H0; et; hexploit H; et; clarify. Qed.

  Lemma match_proj_frag_Some sk tge l mvl (MATCH_GE: match_ge sk tge) : proj_fragment (map (map_memval sk tge) l) = Some (map (map_memval sk tge) mvl) <-> proj_fragment l = Some mvl.
  Proof.
    revert mvl. induction l; ss.
    - split; i; ss; clarify. destruct mvl; clarify.
    - des_ifs.
      + split; i; ss; clarify.
        * f_equal. destruct mvl; ss; clarify. eapply (CoqlibC.list_map_injective (map_memval sk tge)).
          { i. eapply map_memval_inj; et. }
          ss. f_equal; et. f_equal. assert (Some l1 = Some mvl); clarify. rewrite <- IHl. et.
        * f_equal. ss. f_equal. assert (Some l0 = Some (map (map_memval sk tge) l1)); clarify. rewrite IHl. et.
      + split; i; ss; clarify. destruct mvl; ss; clarify. specialize (IHl mvl).
        destruct IHl. hexploit H; et. clarify.
      + split; i; ss; clarify. specialize (IHl l0). destruct IHl. hexploit H0; clarify.
  Qed.

  Lemma match_check_value n q v sk tge l
        (MGE: match_ge sk tge)
    : check_value n (map_val sk tge v) q (map (map_memval sk tge) l) = check_value n v q l.
  Proof.
    revert q v l. induction n; i.
    - ss. des_ifs.
    - ss. des_ifs. ss. clarify. rewrite IHn. repeat f_equal.
      destruct v; destruct v1; ss.
      destruct (Val.eq (Vptr b i) (Vptr b0 i0));
        destruct (Val.eq _ _); ss; clarify.
      apply map_blk_inj in H1; et. subst. clarify.
  Qed.

  Lemma decode_map_comm sk tge chunk l
        (MGE: match_ge sk tge)
    :
      decode_val chunk (map (map_memval sk tge) l) = map_val sk tge (decode_val chunk l).
  Proof.
    induction l.
    - ss. unfold decode_val. des_ifs.
    - ss. unfold decode_val. destruct a.
      + ss. des_ifs.
      + ss. rewrite match_proj_bytes. des_ifs.
      + rewrite <- match_proj_bytes with (sk := sk) (l := Fragment v q n :: l) (tge := tge). des_ifs.
        * unfold proj_value. rewrite <- match_check_value with (sk := sk) at 1; et.
          des_ifs; ss; clarify. destruct v; et.
        * unfold proj_value. rewrite <- match_check_value with (sk := sk) at 1; et.
          des_ifs; ss; clarify. destruct v; et.
        * unfold proj_value. rewrite <- match_check_value with (sk := sk) at 1; et.
          des_ifs; ss; clarify.
  Qed.

  Require Import ClightPlusMemAux.

  Lemma match_is_frag_mv sk ge mvl : existsb is_frag_mv (map (map_memval sk ge) mvl) = existsb is_frag_mv mvl.
  Proof. induction mvl; ss. rewrite IHmvl. destruct a; ss. Qed.

  Lemma match_is_byte_mv sk ge mvl : existsb is_byte_mv (map (map_memval sk ge) mvl) = existsb is_byte_mv mvl.
  Proof. induction mvl; ss. rewrite IHmvl. destruct a; ss. Qed.

  Lemma match_is_long_mv sk ge mvl : existsb is_long_mv (map (map_memval sk ge) mvl) = existsb is_long_mv mvl.
  Proof. induction mvl; ss. rewrite IHmvl. destruct a; ss. destruct v; ss. Qed.

  Lemma match_is_ptr_mv sk ge mvl : existsb is_ptr_mv (map (map_memval sk ge) mvl) = existsb is_ptr_mv mvl.
  Proof. induction mvl; ss. rewrite IHmvl. destruct a; ss. destruct v; ss. Qed.

  Lemma match_bytes_not_pure sk ge mvl : bytes_not_pure (List.map (map_memval sk ge) mvl) = bytes_not_pure mvl.
  Proof.
    unfold bytes_not_pure in *. unfold proj_fragment_byte_mixed, proj_fragment_mixed in *.
    rewrite match_is_frag_mv. rewrite match_is_byte_mv. rewrite match_is_long_mv. rewrite match_is_ptr_mv. et.
  Qed.

  Lemma match_ptr2int m tm sk tge b z
    (MM: match_mem sk tge m tm)
  :
    Mem.ptr2int (map_blk sk tge b) z tm = Mem.ptr2int b z m.
  Proof. unfold Mem.ptr2int. inv MM. rewrite <- MEM_CONC. et. Qed.

  Lemma zindex_surj p : exists z, p = ZIndexed.index z.
  Proof.
    destruct p.
    - exists (Zneg p). et.
    - exists (Zpos p). et.
    - exists 0%Z. et.
  Qed.

  Lemma encode_match_comm chunk sk tge v : encode_val chunk (map_val sk tge v) = map (map_memval sk tge) (encode_val chunk v).
  Proof. destruct v; ss; des_ifs. Qed.

  Lemma setN_inside x l i c
      (IN_RANGE: (i <= x)%Z /\ (x < i + Z.of_nat (length l))%Z)
    :
      exists entry, nth_error l (Z.to_nat (x - i)%Z) = Some entry /\ ZMap.get x (Mem.setN l i c) = entry.
  Proof.
    assert (Z.to_nat (x - i)%Z < length l)%nat by nia.
    apply nth_error_Some in H. destruct (nth_error _ _) eqn: E in H; clarify.
    eexists; split; et. clear H. depgen x. revert i c m. induction l; i; ss; try nia.
    destruct (Nat.eq_dec (Z.to_nat (x - i)) 0).
    - rewrite e in *. ss. clarify. assert (x = i) by nia. rewrite H in *.
      rewrite Mem.setN_outside; try nia. apply ZMap.gss.
    - change (a :: l) with ([a] ++ l) in E. rewrite nth_error_app2 in E; ss; try nia.
      replace (Z.to_nat (x - i) - 1)%nat with (Z.to_nat (x - (i + 1))) in E by nia.
      eapply IHl; et. nia.
  Qed.

  Lemma match_mem_alloc m tm b lo hi m' sk tge
        (SMEM: Mem.alloc m lo hi = (m', b))
        (MGE: match_ge sk tge)
        (MM_PRE: match_mem sk tge m tm)
    :
    exists tm',
        (<<TMEM: Mem.alloc tm lo hi = (tm', map_blk sk tge b)>>) /\
        (<<MM_POST: match_mem sk tge m' tm'>>).
  Proof.
    inv MM_PRE. unfold Mem.alloc in *. clarify. eexists. split.
    - rewrite <- NBLK. red. f_equal.
    - red. econs.
      + ss. nia.
      + ss. rewrite NBLK. unfold map_blk. des_ifs; try nia.
      + i. ss. destruct (Pos.eq_dec (Mem.nextblock m) b).
        * rewrite <- e in *. rewrite NBLK. rewrite PMap.gss in *.
          destruct (zindex_surj ofs). rewrite H0 in *. rewrite H.
          change (_ !! _) with (ZMap.get x (ZMap.init Undef)) in H.
          rewrite ZMap.gi in H. subst. et.
        * rewrite PMap.gso in *; et. rewrite NBLK. red. red in n. revert n. i.
          apply n. eapply map_blk_inj; et.
      + i. ss. destruct (Pos.eq_dec (Mem.nextblock m) b).
        * rewrite <- e in *. rewrite NBLK in *. do 2 rewrite PMap.gss. et.
        * do 2 try rewrite PMap.gso; et. rewrite NBLK. red. red in n. revert n. i.
          apply n. eapply map_blk_inj; et.
      + ss.
  Qed.

  Lemma match_mem_store m tm m' chunk b ofs v sk tge
        (SMEM: Mem.store chunk m b ofs v = Some m')
        (MGE: match_ge sk tge)
        (MM_PRE: match_mem sk tge m tm)
    :
      exists tm',
        <<TMEM: Mem.store chunk tm (map_blk sk tge b) ofs (map_val sk tge v) = Some tm'>> /\
        <<MM_POST: match_mem sk tge m' tm'>>.
  Proof.
    inv MM_PRE. unfold Mem.store in *.
    des_ifs.
    - eexists; split; et. econs; ss. i. destruct (zindex_surj ofs0). rewrite encode_match_comm.
      destruct (Pos.eq_dec b b0);
        destruct ((x <? ofs) || (x >=? ofs + Z.of_nat (length (encode_val chunk v))))%Z eqn: e1.
      + rewrite e in *. rewrite PMap.gss in *.
        rewrite H0 in *. pose proof Mem.setN_outside. unfold ZMap.get in *.
        rewrite H1 in H; try nia. rewrite H1; et. rewrite map_length. nia.
      + rewrite e in *. rewrite PMap.gss in *. rewrite H0 in *.
        edestruct setN_inside;[|des; unfold ZMap.get in *; rewrite H2 in H]; try nia. rewrite H in *.
        edestruct setN_inside;[|des; unfold ZMap.get in *; rewrite H4]; try (rewrite map_length; nia).
        clear -H1 H3. rewrite nth_error_map in H3. rewrite H1 in H3. ss. clarify.
      + assert (map_blk sk tge b <> map_blk sk tge b0).
        { red. i. apply n. erewrite map_blk_inj; et. }
        rewrite PMap.gso; et. rewrite PMap.gso in H; et.
      + assert (map_blk sk tge b <> map_blk sk tge b0).
        { red. i. apply n. erewrite map_blk_inj; et. }
        rewrite PMap.gso; et. rewrite PMap.gso in H; et.
    - exfalso. apply n. unfold Mem.valid_access in *. des. split; et. unfold Mem.range_perm in *. i. unfold Mem.perm in *.
      rewrite <- MEM_PERM. et.
  Qed.

  Lemma match_mem_loadbytes m tm blk ofs n l sk tge
        (SMEM: Mem.loadbytes m blk ofs n = Some l)
        (MM: match_mem sk tge m tm)
    :
        Mem.loadbytes tm (map_blk sk tge blk) ofs n = Some (map (map_memval sk tge) l).
  Proof.
    inv MM. unfold Mem.loadbytes in *. des_ifs_safe. ss. clarify.
    des_ifs.
    - f_equal. erewrite match_mem_getN; et.
    - exfalso. apply n0. unfold Mem.range_perm in *. i. unfold Mem.perm in *.
      rewrite <- MEM_PERM. et.
  Qed.

  Lemma match_mem_storebytes m tm m' blk ofs l sk tge
        (SMEM: Mem.storebytes m blk ofs l = Some m')
        (MGE: match_ge sk tge)
        (MM_PRE: match_mem sk tge m tm)
    :
      exists tm',
        <<TMEM: Mem.storebytes tm (map_blk sk tge blk) ofs (map (map_memval sk tge) l) = Some tm'>> /\
        <<MM_POST: match_mem sk tge m' tm'>>.
  Proof.
    inv MM_PRE. unfold Mem.storebytes in *. des_ifs.
    - eexists; split; et. econs; ss. i. destruct (zindex_surj ofs0). rewrite H0 in *.
      destruct (Pos.eq_dec blk b);
        destruct ((x <? ofs) || (x >=? ofs + Z.of_nat (length l)))%Z eqn: e1.
      + rewrite e in *. rewrite PMap.gss in *.
        pose proof Mem.setN_outside. unfold ZMap.get in *.
        rewrite H1 in H; try nia. rewrite H1; et. rewrite map_length. nia.
      + rewrite e in *. rewrite PMap.gss in *.
        edestruct setN_inside;[|des; unfold ZMap.get in *; rewrite H2 in H]; try nia. rewrite H in *.
        edestruct setN_inside;[|des; unfold ZMap.get in *; rewrite H4]; try (rewrite map_length; nia).
        clear -H1 H3. rewrite nth_error_map in H3. rewrite H1 in H3. ss. clarify.
      + assert (map_blk sk tge blk <> map_blk sk tge b).
        { red. i. apply n. erewrite map_blk_inj; et. }
        rewrite PMap.gso; et. rewrite PMap.gso in H; et.
      + assert (map_blk sk tge blk <> map_blk sk tge b).
        { red. i. apply n. erewrite map_blk_inj; et. }
        rewrite PMap.gso; et. rewrite PMap.gso in H; et.
    - exfalso. apply n. unfold Mem.range_perm in *. i. unfold Mem.perm in *.
      rewrite <- MEM_PERM. eapply r. rewrite map_length in H. nia.
  Qed.

  Lemma match_mem_denormalize sk tge m tm z b ofs
      (SMEM: Mem.denormalize z m = Some (b, ofs))
      (MGE: match_ge sk tge)
      (MM_PRE: match_mem sk tge m tm)
    :
      Mem.denormalize z tm = Some (map_blk sk tge b, ofs).
  Proof.
    unfold Mem.denormalize in SMEM. apply PTree.gselectf in SMEM.
    des. destruct Mem.denormalize eqn:?; cycle 1.
    - unfold Mem.denormalize in Heqo. apply PTree.gselectnf in Heqo.
      exfalso. apply Heqo. inv MM_PRE. rewrite MEM_CONC in SMEM.
      esplits; et. unfold Mem.denormalize_aux in *.
      unfold Mem.is_valid, Mem.addr_is_in_block in *.
      rewrite <- MEM_CONC. rewrite NBLK. rewrite <- MEM_PERM.
      des_ifs; cycle 1. { bsimpl. clarify. }
      symmetry in Heq0. bsimpl. des. rewrite Heq3 in Heq0.
      rewrite Heq4 in Heq0. ss. bsimpl.
      unfold map_blk in Heq0 at 2.
      destruct le_dec; try nia. des_ifs; try nia.
      destruct (Coqlib.plt b (Pos.of_succ_nat (List.length sk))).
      { unfold Coqlib.Plt in p1. hexploit (@map_blk_global_region sk tge b); et.
        nia. symmetry in Heq0. rewrite Pos.ltb_ge in Heq0.
        i. red in H. nia. }
      rewrite Pos2Z.inj_ltb in Heq0.
      unfold Coqlib.Plt in n.
      unfold map_blk in Heq0. destruct le_dec; try nia.
      des_ifs; try nia.
      rewrite Pos2Z.inj_ltb in Heq2. nia.
    - unfold Mem.denormalize_aux in SMEM0. des_ifs. bsimpl. des.
      rewrite <- Mem.addr_in_block_iff in Heq1.
      unfold Mem.is_valid in *.
      unfold Mem.denormalize in Heqo. apply PTree.gselectf in Heqo.
      des. unfold Mem.denormalize_aux in Heqo0.
      des_ifs. bsimpl. des. rewrite <- Mem.addr_in_block_iff in Heq4.
      pose proof (tm.(Mem.no_concrete_overlap) z).
      red in H. hexploit H. 1: et.
      + inv Heq1. inv MM_PRE. des.
        replace ((Mem.mem_access m) !! b) with ((Mem.mem_access tm) !! (map_blk sk tge b)) in PERM by et.
        rewrite MEM_CONC in CONCRETE. econs; et.
      + i. rewrite H0 in *. inv MM_PRE. rewrite MEM_CONC in *.
        rewrite Heq in Heq2. clarify.
  Qed.

  Lemma match_mem_denormalize_rev sk tge m tm z b ofs
      (TMEM: Mem.denormalize z tm = Some (map_blk sk tge b, ofs))
      (MGE: match_ge sk tge)
      (MM_PRE: match_mem sk tge m tm)
    :
      Mem.denormalize z m = Some (b, ofs).
  Proof.
    unfold Mem.denormalize in TMEM. apply PTree.gselectf in TMEM.
    des. unfold Mem.denormalize_aux, Mem.addr_is_in_block in *.
    des_ifs; bsimpl; clarify. des. unfold Mem.denormalize.
    destruct PTree.select eqn:?.
    - apply PTree.gselectf in Heqo.
      des. unfold Mem.denormalize_aux in *.
      des_ifs; bsimpl; clarify. des.
      inv MM_PRE. rewrite <- MEM_CONC in Heq.
      unfold Mem.addr_is_in_block in Heq1.
      pose proof (m.(Mem.no_concrete_overlap) z).
      red in H. hexploit H.
      { rewrite Mem.addr_in_block_iff. apply Heq6. }
      { rewrite Mem.addr_in_block_iff.
        unfold Mem.addr_is_in_block.
        rewrite Heq. rewrite MEM_PERM. des_ifs. }
      i. subst. rewrite Heq in Heq4. clarify.
    - apply PTree.gselectnf in Heqo. exfalso. apply Heqo.
      inv MM_PRE. rewrite <- MEM_CONC in Heq. rewrite <- MEM_PERM in Heq1.
      esplits; et. unfold Mem.denormalize_aux, Mem.addr_is_in_block. des_ifs.
      bsimpl. unfold Mem.is_valid in *. rewrite NBLK in Heq0. clear -Heq Heq0 INITIALIZED MGE.
      unfold map_blk in Heq0 at 2.
      destruct le_dec; try nia. des_ifs; try nia.
      destruct (Coqlib.plt b (Pos.of_succ_nat (List.length sk))).
      { unfold Coqlib.Plt in p0. hexploit (@map_blk_global_region sk tge b); et.
        nia. rewrite Pos.ltb_ge in Heq.
        i. red in H. nia. }
      rewrite Pos2Z.inj_ltb in Heq0.
      unfold Coqlib.Plt in n.
      unfold map_blk in Heq0. destruct le_dec; try nia.
      des_ifs; try nia.
      rewrite Pos2Z.inj_ltb in Heq. nia.
  Qed.

  Lemma match_to_ptr m tm sk tge v vp
    (MM: match_mem sk tge m tm)
    (MGE: match_ge sk tge)
    (SVAL: Mem.to_ptr v m = Some vp)
  :
    Mem.to_ptr (map_val sk tge v) tm = Some (map_val sk tge vp).
  Proof.
    unfold Mem.to_ptr in SVAL. des_ifs.
    - ss. des_ifs.
    - hexploit match_mem_denormalize; et. i. unfold Mem.to_ptr.
      ss. rewrite H. des_ifs.
  Qed.

  Lemma match_to_int m tm sk tge v vi
    (MM: match_mem sk tge m tm)
    (MGE: match_ge sk tge)
    (SVAL: Mem.to_int v m = Some vi)
  :
    Mem.to_int (map_val sk tge v) tm = Some vi.
  Proof.
    unfold Mem.to_int in SVAL. des_ifs.
    ss. des_ifs.
    - hexploit match_ptr2int; et. i. rewrite H in Heq. clarify.
    - hexploit match_ptr2int; et. i. rewrite H in Heq. clarify.
  Qed.

  Lemma match_valid_pointer m tm sk tge z b
    (MM: match_mem sk tge m tm)
  :
    Mem.valid_pointer tm (map_blk sk tge b) z = Mem.valid_pointer m b z.
  Proof.
    unfold Mem.valid_pointer. do 2 destruct Mem.perm_dec; ss; exfalso.
    - unfold Mem.perm, Mem.perm_order' in *. destruct (_ !! _) eqn:? in p; clarify.
      inv MM. rewrite <- MEM_PERM in Heqy. rewrite Heqy in n. clarify.
    - unfold Mem.perm, Mem.perm_order' in *. destruct (_ !! _) eqn:? in p; clarify.
      inv MM. rewrite MEM_PERM in Heqy. rewrite Heqy in n. clarify.
  Qed.

  Lemma match_to_ptr_val m tm sk tge v b ofs
    (MM: match_mem sk tge m tm)
    (MGE: match_ge sk tge)
    (SVAL: IntPtrRel.to_ptr_val m v = Vptr b ofs)
  :
    IntPtrRel.to_ptr_val tm (map_val sk tge v) = Vptr (map_blk sk tge b) ofs.
  Proof.
    unfold IntPtrRel.to_ptr_val in *. destruct (Mem.to_ptr _ tm) eqn:?; destruct (Mem.to_ptr _ m) eqn:?; ss; clarify.
    - hexploit match_to_ptr; et. i. clarify.
    - hexploit match_to_ptr; et. i. clarify.
  Qed.

  Lemma match_to_int_val m tm sk tge v i
    (MM: match_mem sk tge m tm)
    (MGE: match_ge sk tge)
    (SVAL: IntPtrRel.to_int_val m v = Vlong i)
  :
    IntPtrRel.to_int_val tm (map_val sk tge v) = Vlong i.
  Proof.
    unfold IntPtrRel.to_int_val in *. destruct (Mem.to_int _ tm) eqn:?; destruct (Mem.to_int _ m) eqn:?; ss; clarify.
    - hexploit match_to_int; et. i. rewrite H in Heqo. clarify.
    - hexploit match_to_int; et. i. rewrite H in Heqo. clarify.
  Qed.

  Lemma match_normalize_check sk tge chunk mvl: match_ge sk tge ->
    Mem.normalize_check chunk mvl = Mem.normalize_check chunk (map (map_memval sk tge) mvl).
  Proof.
    i. unfold Mem.normalize_check. des_ifs; f_equal.
    - unfold Mem.is_mixed_mvs. f_equal.
      + induction mvl; ss. rewrite IHmvl. f_equal.
        destruct a; ss. destruct v; ss.
      + f_equal. induction mvl; ss. rewrite IHmvl. f_equal.
        destruct a; ss. destruct v; ss.
    - unfold Mem.is_mixed_mvs. f_equal.
      + induction mvl; ss. rewrite IHmvl. f_equal.
        destruct a; ss. destruct v; ss.
      + f_equal. induction mvl; ss. rewrite IHmvl. f_equal.
        destruct a; ss. destruct v; ss.
  Qed.

  Lemma match_normalize_mvs sk tge m tm chunk mvl: match_ge sk tge -> match_mem sk tge m tm -> List.map (map_memval sk tge) (Mem.normalize_mvs chunk m mvl) = Mem.normalize_mvs chunk tm (List.map (map_memval sk tge) mvl).
  Proof.
    i. unfold Mem.normalize_mvs. destruct chunk; et.
    - erewrite <- match_normalize_check; et. des_ifs.
      do 2 rewrite map_map. f_equal.
      extensionalities. destruct H1; ss.
      destruct Mem.to_int eqn:?.
      + eapply match_to_int in Heqo; et. rewrite Heqo.
        des_ifs. unfold Mem.to_int in Heqo. des_ifs; ss.
        * apply nth_error_In in Heq0. unfold rev_if_be_mv in Heq0.
          des_ifs. apply in_rev in Heq0. unfold inj_bytes in Heq0.
          apply in_map_iff in Heq0. des. clarify.
        * apply nth_error_In in Heq0. unfold rev_if_be_mv in Heq0.
          des_ifs. apply in_rev in Heq0. unfold inj_bytes in Heq0.
          apply in_map_iff in Heq0. des. clarify.
        * des_ifs. ss.
          apply nth_error_In in Heq0. unfold rev_if_be_mv in Heq0.
          des_ifs. apply in_rev in Heq0. unfold inj_bytes in Heq0.
          apply in_map_iff in Heq0. des. clarify.
      + des_ifs. destruct v; clarify. ss.
        erewrite match_ptr2int in Heq0; et. des_ifs.
    - erewrite <- match_normalize_check; et. des_ifs.
      do 2 rewrite map_map. f_equal.
      extensionalities. destruct H1; ss.
      destruct Mem.to_int eqn:?.
      + eapply match_to_int in Heqo; et. rewrite Heqo.
        des_ifs. unfold Mem.to_int in Heqo. des_ifs; ss.
        * apply nth_error_In in Heq0. unfold rev_if_be_mv in Heq0.
          des_ifs. apply in_rev in Heq0. unfold inj_bytes in Heq0.
          apply in_map_iff in Heq0. des. clarify.
        * apply nth_error_In in Heq0. unfold rev_if_be_mv in Heq0.
          des_ifs. apply in_rev in Heq0. unfold inj_bytes in Heq0.
          apply in_map_iff in Heq0. des. clarify.
        * des_ifs. ss.
          apply nth_error_In in Heq0. unfold rev_if_be_mv in Heq0.
          des_ifs. apply in_rev in Heq0. unfold inj_bytes in Heq0.
          apply in_map_iff in Heq0. des. clarify.
      + des_ifs. destruct v; clarify. ss.
        erewrite match_ptr2int in Heq0; et. des_ifs.
  Qed.

  Lemma match_mem_load m tm chunk b ofs v sk tge
        (SMEM: Mem.load chunk m b ofs = Some v)
        (MGE: match_ge sk tge)
        (MM: match_mem sk tge m tm)
    :
        Mem.load chunk tm (map_blk sk tge b) ofs = Some (map_val sk tge v).
  Proof.
    inv MM. unfold Mem.load in *.
    des_ifs.
    - f_equal. erewrite match_mem_getN; et. rewrite <- decode_map_comm; et.
      f_equal. erewrite match_normalize_mvs; et. econs; et.
    - exfalso. apply n. unfold Mem.valid_access in *. des. split; et. unfold Mem.range_perm in *. i. unfold Mem.perm in *.
      rewrite <- MEM_PERM. et.
  Qed.

  Lemma match_capture m tm sk tge b addr tm'
    (MM: match_mem sk tge m tm)
    (MGE: match_ge sk tge)
    (TCAP: Mem.capture tm (map_blk sk tge b) addr tm')
  :
    exists m', match_mem sk tge m' tm' /\ Mem.capture m b addr m'.
  Proof.
    dup TCAP. inv TCAP. inv MM.
    assert (Mem.valid_block m b).
    { unfold Mem.valid_block in *. rewrite NBLK in VALID. clear - INITIALIZED MGE VALID.
      unfold map_blk in VALID at 2.
      destruct le_dec; try nia. des_ifs; try nia.
      destruct (Coqlib.plt b (Pos.of_succ_nat (List.length sk))).
      { unfold Coqlib.Plt in p0. hexploit (@map_blk_global_region sk tge b); et.
        nia. unfold Coqlib.Plt in *. nia. }
      unfold Coqlib.Plt in *.
      unfold map_blk in VALID. destruct le_dec; try nia.
      des_ifs; try nia. }
    rewrite <- MEM_CONC in *.
    destruct ((Mem.mem_concrete m) ! b) eqn:E.
    - hexploit PREVADDR; et. i. des. clarify. exists m. split.
      + assert (tm = tm') by now apply mem_eq; et. rewrite <- H0. econs; et.
      + econs; et. { i. clarify. } { i. rewrite E in H0. clarify. }
    - hexploit CAPTURED; et. i.
      assert (exists mem, mem.(Mem.mem_contents) = m.(Mem.mem_contents) /\ mem.(Mem.mem_access) = m.(Mem.mem_access) /\ mem.(Mem.nextblock) = m.(Mem.nextblock) /\ mem.(Mem.mem_concrete) = PTree.set b addr m.(Mem.mem_concrete)).
      { econs. instantiate (1:= Mem.mkmem _ _ _ _ _ _ _ _ _ _ _ _). ss. }
      Unshelve. all: cycle 1.
      + apply m.(Mem.access_max).
      + apply m.(Mem.nextblock_noaccess).
      + apply m.(Mem.contents_default).
      + i. unfold Coqlib.Plt in *. destruct (Pos.eq_dec b0 b). { subst. clarify. }
        rewrite Maps.PTree.gso; et. apply m.(Mem.nextblocks_logical). et.
      + i. inv IN_BLOCK. destruct (Pos.eq_dec bo b); cycle 1.
        { rewrite Maps.PTree.gso in CONCRETE; et.
          eapply m.(Mem.valid_address_bounded). econs; et. }
        subst. rewrite Maps.PTree.gss in CONCRETE. clarify.
        des. rewrite MEM_PERM in PERM. eapply tm'.(Mem.valid_address_bounded).
        econs; et. 2:{ rewrite <- ACCESS. exists perm. et. }
        rewrite H0. rewrite Maps.PTree.gss. et.
      + i. red. i. inv H1. inv H2. des. destruct (Pos.eq_dec x b); cycle 1.
        * rewrite Maps.PTree.gso in CONCRETE; et.
          destruct (Pos.eq_dec y b); cycle 1.
          { rewrite Maps.PTree.gso in CONCRETE0; et.
            pose proof (m.(Mem.no_concrete_overlap)). red in H1. eapply H1.
            all: econs; et. }
          subst. rewrite Maps.PTree.gss in CONCRETE0. clarify.
          rewrite MEM_PERM in PERM.
          rewrite MEM_PERM in PERM0.
          rewrite ACCESS in PERM.
          rewrite ACCESS in PERM0.
          pose proof (tm'.(Mem.no_concrete_overlap)). red in H1. hexploit H1.
          { econs; et. rewrite H0. rewrite Maps.PTree.gss. et. }
          { rewrite MEM_CONC in CONCRETE. econs.
            { rewrite H0. rewrite Maps.PTree.gso; et. ii. hexploit map_blk_inj; et. }
            { et. } nia. }
          i. eapply map_blk_inj; et.
        * subst. rewrite Maps.PTree.gss in CONCRETE. clarify.
          destruct (Pos.eq_dec y b).
          { subst. rewrite Maps.PTree.gss in CONCRETE0. clarify. }
          rewrite Maps.PTree.gso in CONCRETE0; et.
          rewrite MEM_PERM in PERM.
          rewrite MEM_PERM in PERM0.
          rewrite ACCESS in PERM.
          rewrite ACCESS in PERM0.
          pose proof (tm'.(Mem.no_concrete_overlap)). red in H1. hexploit H1.
          { rewrite MEM_CONC in CONCRETE0. econs.
            { rewrite H0. rewrite Maps.PTree.gso; et. ii. hexploit map_blk_inj; et. }
            { et. } nia. }
          { econs. 2:{ exists perm0. et. } { rewrite H0. rewrite Maps.PTree.gss. et. } nia. }
          i. eapply map_blk_inj; et.
      + i. destruct (Pos.eq_dec b b0); cycle 1.
        { rewrite Maps.PTree.gso in CADDR; et. eapply m.(Mem.concrete_align); et. }
        subst. rewrite Maps.PTree.gss in CADDR. clarify.
        eapply tm'.(Mem.concrete_align); et. rewrite H0. rewrite Maps.PTree.gss; et.
        rewrite <- ACCESS. rewrite <- MEM_PERM. et.
      + i. destruct (Pos.eq_dec b b0); cycle 1.
        { rewrite Maps.PTree.gso in CADDR; et. eapply m.(Mem.weak_valid_address_range); et. }
        subst. rewrite Maps.PTree.gss in CADDR. clarify.
        eapply tm'.(Mem.weak_valid_address_range); et. rewrite H0. rewrite Maps.PTree.gss; et.
        rewrite <- ACCESS. red. unfold Mem._valid_pointer. rewrite <- MEM_PERM. et.
      + i. des. exists mem. split; cycle 1.
        { econs; et. i. rewrite E in H5. clarify. }
        econs.
        * rewrite H3. et.
        * rewrite H3. rewrite <- NEXTBLOCK. et.
        * rewrite H1. rewrite <- CONTENTS. et.
        * rewrite H2. rewrite <- ACCESS. et.
        * rewrite H4. rewrite H0. i.
          destruct (Pos.eq_dec b b0); [subst; rewrite !Maps.PTree.gss|rewrite !Maps.PTree.gso]; et.
          ii. hexploit map_blk_inj; et.
  Qed.


End MEM.