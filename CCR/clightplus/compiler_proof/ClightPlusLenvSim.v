From compcert Require Import Maps Clight Clightdefs.
From ExtLib Require Import Data.List.
Require Import CoqlibCCR.
Require Import PCM.
Require Import AList.

Require Import ClightPlusMatchEnv.
Require Import ClightPlusExprgen.

Set Implicit Arguments.

Section LENV.

  Lemma match_update_le sk ge le tle o v
        (MLE: match_le sk ge le tle)
    :
      match_le sk ge (set_opttemp_alist o v le) (set_opttemp o (map_val sk ge v) tle).
  Proof.
    destruct o; ss. econs. i. inv MLE. destruct (Pos.eq_dec i id).
    - subst. rewrite alist_add_find_eq in H. clarify.
      rewrite PTree.gss. et.
    - rewrite alist_add_find_neq in H; et. rewrite PTree.gso; et.
  Qed.


  Lemma match_sizeof ty ce tce
      (MCE: match_ce ce tce)
    :
      Ctypes.sizeof tce ty = ClightPlusExprgen.sizeof ce ty.
  Proof.
    induction ty; ss.
    - rewrite IHty. et.
    - destruct (tce ! i) eqn:?; destruct alist_find eqn:?.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + eapply cenv_match_none in Heqo0; et. clarify.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + et.
    - destruct (tce ! i) eqn:?; destruct alist_find eqn:?.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + eapply cenv_match_none in Heqo0; et. clarify.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + et.
  Qed.

  Lemma match_alignof_blockcopy ty ce tce
      (MCE: match_ce ce tce)
    :
      Ctypes.alignof_blockcopy tce ty = ClightPlusExprgen.alignof_blockcopy ce ty.
  Proof.
    induction ty; ss.
    - destruct (tce ! i) eqn:?; destruct alist_find eqn:?.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + eapply cenv_match_none in Heqo0; et. clarify.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + et.
    - destruct (tce ! i) eqn:?; destruct alist_find eqn:?.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + eapply cenv_match_none in Heqo0; et. clarify.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + et.
  Qed.

  Lemma match_alignof ty ce tce
      (MCE: match_ce ce tce)
    :
      Ctypes.alignof tce ty = ClightPlusExprgen.alignof ce ty.
  Proof.
    induction ty; ss.
    - rewrite IHty. et.
    - destruct (tce ! i) eqn:?; destruct alist_find eqn:?.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + eapply cenv_match_none in Heqo0; et. clarify.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + et.
    - destruct (tce ! i) eqn:?; destruct alist_find eqn:?.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + eapply cenv_match_none in Heqo0; et. clarify.
      + eapply cenv_match_some in Heqo0; et. clarify.
      + et.
  Qed.

  Lemma match_block_of_binding tce ce ge
        (EQ1: tce = ge.(genv_cenv))
        (MCE: match_ce ce tce)
    :
        Clight.block_of_binding ge = (map_fst (fun b => (b, 0%Z))) ∘ (block_of_binding ce).
  Proof.
    unfold Clight.block_of_binding, block_of_binding.
    extensionalities. des_ifs_safe. ss. f_equal. erewrite match_sizeof; et.
  Qed.

  Lemma bind_parameter_temps_exists_if_same_length
        params args tle0
        (LEN: List.length params = List.length args)
    :
      exists tle, (<<BIND: bind_parameter_temps params args tle0 = Some tle>>).
  Proof.
    depgen args. depgen tle0. clear. induction params; i; ss; clarify.
    { exists tle0. des_ifs. }
    destruct args; ss; clarify. destruct a. eauto.
  Qed.

  Lemma bind_parameter_temps_exists
        sk defs base params sle rvs (tle0: temp_env)
        (BIND_SRC: bind_parameter_temps params rvs base = Some sle)
    :
      exists tle, (<<BIND_TGT: bind_parameter_temps params (List.map (map_val sk defs) rvs) tle0
                      = Some tle>>).
  Proof.
    eapply bind_parameter_temps_exists_if_same_length; eauto.
    rewrite ! map_length. clear -BIND_SRC. depgen base. revert sle.  depgen rvs. depgen params.
    induction params; i; ss; des_ifs.
    ss. f_equal. eapply IHparams; eauto.
  Qed.

  Lemma bind_parameter_temps_exists_if_same_length'
        params args tle0
        (LEN: List.length params = List.length args)
    :
      exists tle, (<<BIND: Clight.bind_parameter_temps params args tle0 = Some tle>>).
  Proof.
    depgen args. depgen tle0. clear. induction params; i; ss; clarify.
    { exists tle0. des_ifs. }
    destruct args; ss; clarify. destruct a. eauto.
  Qed.

  Lemma match_bind_parameter_temps
        sk tge params sle rvs sbase tbase
        (BIND_SRC: bind_parameter_temps params rvs sbase = Some sle)
        (MLE: match_le sk tge sbase tbase)
    :
      exists tle, (<<BIND_TGT: Clight.bind_parameter_temps params (List.map (map_val sk tge) rvs) tbase
                      = Some tle>>)
                  /\ (<<MLE: match_le sk tge sle tle>>).
  Proof.
    hexploit (bind_parameter_temps_exists_if_same_length' params (List.map (map_val sk tge) rvs) tbase).
    - rewrite ! map_length. clear -BIND_SRC. depgen sbase.
      revert sle. depgen rvs. depgen params.
      induction params; i; ss; des_ifs.
      ss. f_equal. eapply IHparams; eauto.
    - i. des. eexists; split; et. red. depgen sbase. depgen sle. depgen rvs. revert tbase tle. depgen params.
      induction params; i; ss; des_ifs. simpl in Heq. clarify.
      eapply IHparams. 2:et. 1:et.
      inv MLE. econs.
      i. destruct (dec id i). { subst. rewrite alist_add_find_eq in H. clarify. rewrite Maps.PTree.gss. et. }
      rewrite Maps.PTree.gso; et. rewrite alist_add_find_neq in H; et.
  Qed.

End LENV.

Section ENV.

  Lemma match_update_e sk tge e te i blk t
        (MLE: match_e sk tge e te)
    :
      match_e sk tge (alist_add i (blk, t) e) (Maps.PTree.set i (map_blk sk tge blk, t) te).
  Proof.
    inv MLE. econs; et.
    { apply alist_add_nodup. et. }
    split; i.
    - destruct a. apply Maps.PTree.elements_complete in H.
      rewrite in_map_iff. destruct (Pos.eq_dec p i).
      + subst. rewrite Maps.PTree.gss in H. clarify.
        exists (i, (blk, t)). split; et. ss. et.
      + rewrite Maps.PTree.gso in H; et. apply Maps.PTree.elements_correct in H.
        apply ME in H. apply in_map_iff in H. des. eexists; split; et.
        destruct x. destruct p1. simpl in H. clarify.
        eapply alist_find_some.
        rewrite alist_add_find_neq; et.
        apply alist_find_some_iff; et.
    - destruct a. rewrite in_map_iff in H. des. destruct x. destruct p1.
      simpl in H. clarify. apply Maps.PTree.elements_correct.
      destruct (Pos.eq_dec p i).
      + subst. rewrite Maps.PTree.gss in *. eapply alist_find_some_iff in H0.
        * rewrite alist_add_find_eq in H0. clarify.
        * apply alist_add_nodup. et.
      + rewrite Maps.PTree.gso; et.
        apply Maps.PTree.elements_complete.
        rewrite ME.
        change ((_, (_,_))) with (map_env_entry sk tge (p, (b, t0))).
        apply in_map.
        eapply alist_find_some_iff in H0; cycle 1.
        { apply alist_add_nodup. et. }
        rewrite alist_add_find_neq in H0; et.
        apply alist_find_some in H0. et.
  Qed.

End ENV.
