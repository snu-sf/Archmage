Require Import Classical.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import PointerOp Simulation SSAD sflib.
Require Import Smallstep.
Require Import Op.
Require Import Events.
Require Import Registers.
Require Import Floats.
Require Import Utils.
Require Import SSA. 
Require Import SSAutils. 
Require Import SSAinv. 
Require Import Utilsvalidproof.
Require Import DomCompute.
Require Import Axioms.
Require Import KildallComp.
Require Import OrderedType.
Require Import Ordered.
Require Import FSets.
Require FSetAVL.
Require Import Dsd.
(* Require Import OptInv. *)
Require Import Copyprop.
(* Require Import GVNoptProp. *)
Require Import DLib.

Require Import Linking.
Require Import Classical.
From Paco Require Import paco.

(* Require Opt. *)
(* Require OptInv. *)

Require Import sflib.
(* Require Import Simulation. *)

Unset Allow StrictProp.

(** * Correctness of the optimization *)
Section PRESERVATION.

  Definition match_prog (p: SSA.program) (tp: SSA.program) :=
    match_program (fun cu f tf => tf = transf_fundef f) eq p tp.

  Lemma transf_program_match:
   forall p, match_prog p (transf_program p).
  Proof.
   intros; subst.
   eapply match_transform_program_contextual; auto.
  Qed.

  Lemma fold_find_mv_instr_some: forall l d s,
    fold_left (fun a p => find_mv_instr a (fst p) (snd p)) l None = Some (d, s) ->
    exists pc pc', In (pc, (Iop Omove (s :: nil) d pc')) l.
  Proof.
    induction l; ss. i. destruct a eqn:Ea; ss.
    destruct i; ss; try (apply IHl in H; des; exists pc, pc'; eauto; fail).
    destruct o; ss; try (apply IHl in H; des; exists pc, pc'; eauto; fail).
    destruct l0.
    - apply IHl in H. des. exists pc, pc'; eauto.
    - destruct l0; ss.
      + assert (forall l, fold_left (fun a p => find_mv_instr a (fst p) (snd p))
                          l (Some (r, r0)) = Some (r, r0)).
        { induction l0; ss. }
        rewrite H0 in H. inv H. eauto.
      + apply IHl in H. des; eauto.
  Qed.

  Lemma fold_find_mv_instr_none: forall l d s,
    fold_left (fun a p => find_mv_instr a (fst p) (snd p)) l None = None ->
    forall pc pc', ~ In (pc, (Iop Omove (s :: nil) d pc')) l.
  Proof.
    assert (forall l d s, fold_left
                            (fun a p => find_mv_instr a (fst p) (snd p))
                            l (Some (d, s)) = None -> False).
    { induction l; ss. }
    induction l; ss. ii. des.
    - destruct a; ss. clarify.
      apply H in H0; eauto.
    - destruct a; ss. destruct i; ss; try eapply IHl in H0; eauto.
      destruct o; ss; try eapply IHl in H0; eauto.
      destruct l0; ss; try eapply IHl in H0; eauto.
      destruct l0; ss; try eapply IHl in H0; eauto.
  Qed.

  Lemma find_mv_exists: forall c d s,
    find_mv_code c = Some (d, s) ->
    exists pc pc', c ! pc = Some (Iop Omove (s :: nil) d pc').
  Proof.
    unfold find_mv_code. i. rewrite PTree.fold_spec in H.
    apply fold_find_mv_instr_some in H. des.
    apply PTree.elements_complete in H. eauto.
  Qed.

  Lemma fold_find_mv_phiinstr_some: forall l d s,
    fold_left (fun a p => _find_mv_phiblock a (fst p) (snd p)) l None = Some (d, s) ->
    exists pc phib, (In (pc, phib) l /\
                     exists args, In (Iphi (s :: args) d) phib
                                  /\ forall a, In a args -> a = s).
  Proof.
    induction l; ss. i. destruct a eqn:Ea; ss.
    destruct (find_mv_phiblock p) eqn:PFIND.
    - assert (forall l d s,
              fold_left (fun a p => _find_mv_phiblock a (fst p) (snd p)) l (Some (d, s))
                = Some (d, s)).
      { induction l0; ss. } destruct p0. rewrite H0 in H. clarify.
      assert (forall p d s, find_mv_phiblock p = Some (d, s) ->
                            exists args, In (Iphi (s :: args) d) p /\
                                         forall a, In a args -> a = s).
      { induction p0; ss. i. flatten H.
        - apply IHp0 in H. des. exists args; split; eauto.
        - exists l1; split; eauto. i. rewrite forallb_forall in Eq1. apply Eq1 in H.
          apply Pos.eqb_eq in H. auto.
        - apply IHp0 in H. des. exists args; split; eauto.  }
      apply H in PFIND. des. exists n, p; eauto.
    - apply IHl in H. des. exists pc, phib; eauto.
  Qed.

  Lemma fold_find_mv_phiinstr_none: forall l d s,
    fold_left (fun a p => _find_mv_phiblock a (fst p) (snd p)) l None = None ->
    forall pc phib, ~ (In (pc, phib) l /\
                       exists args, (In (Iphi (s :: args) d)) phib
                                     /\ forall a, In a args -> a = s).
  Proof.
    assert (FOLDSN: forall l d s, fold_left
                    (fun a p => _find_mv_phiblock a (fst p) (snd p))
                    l (Some (d, s)) = None -> False).
    { induction l; ss. }
    assert (FORALLF: forall l s,
                     forallb (Pos.eqb s) l = false -> exists t, In t l /\ t <> s).
    { induction l; ss. i. apply andb_false_elim in H. destruct H.
      exists a; split; eauto. apply Pos.eqb_neq in e. ii.
      symmetry in H. apply e in H; ss.
      apply IHl in e. des. exists t; split; eauto. }
    assert (FINDCORR: forall phib s d args,
                      In (Iphi (s :: args) d) phib ->
                      forallb (Pos.eqb s) args = true ->
                      exists s' d', find_mv_phiblock phib = Some (s', d')).
      { induction phib; ss. i. des.
        - rewrite H. rewrite H0. eauto.
        - apply IHphib in H. des. destruct a; ss. destruct l; ss.
          + eauto.
          + flatten. eauto. eauto.
          + auto. }
    induction l; ss.
    - ii. des; auto.
    - ii. destruct a; ss. des.
      + clarify.
        eapply FINDCORR in H1; eauto. des; ss. rewrite H1 in H.
        apply FOLDSN in H; auto. rewrite forallb_forall. i.
        apply H2 in H0. clarify. rewrite Pos.eqb_eq; ss.
      + destruct (find_mv_phiblock p) eqn:FINDP; ss.
        * destruct p0. apply FOLDSN in H. destruct H.
        * eapply IHl in H. apply H. split.
          eauto. eauto.
  Qed.

  Lemma find_mv_phicode_exists: forall p d s,
    find_mv_phicode p = Some (d, s) ->
    exists pc phib args, p ! pc = Some phib /\
    In (Iphi (s :: args) d) phib /\
    forallb (Pos.eqb s) args = true.
  Proof.
  assert (forall l d s,
          fold_left (fun a p => _find_mv_phiblock a (fst p) (snd p))
          l None = Some (d, s) ->
          exists pc phib args, In (pc, phib) l /\
          In (Iphi (s :: args) d) phib /\
          forallb (Pos.eqb s) args).
  { induction l; ss. i. destruct a eqn:Ea; ss.
    destruct (find_mv_phiblock p) eqn:Epfind.
    - destruct p0; ss.
      assert (forall l, fold_left (fun a p => _find_mv_phiblock a (fst p) (snd p))
              l (Some (r, r0)) = Some (d, s) -> r = d /\ r0 = s).
      { induction l0; ss. i; clarify; ss. }
      specialize (H0 _ H); des; clarify.
      revert p Epfind. induction p; ss. i.
      destruct a. destruct l0.
      + apply IHp in Epfind. des; clarify; repeat eexists; eauto.
      + flatten Epfind.
        * repeat eexists; eauto.
        * apply IHp in Epfind. des; clarify; repeat eexists; eauto.
    - apply IHl in H. des. exists pc, phib, args; eauto.
  }
  unfold find_mv_phicode. i. rewrite PTree.fold_spec in H0. apply H in H0. des.
  apply PTree.elements_complete in H0. repeat eexists; eauto.
  Qed.

  Lemma find_mv_not_same: forall f d s,
    wf_ssa_function f ->
    find_mv_code (fn_code f) = Some (d, s) ->
    d <> s.
  Proof.
    ii. apply find_mv_exists in H0. des. inversion H.
    assert (use_code f s pc). econstructor; eauto.
    assert (assigned_code_spec (fn_code f) pc s). subst. econstructor; eauto.
    eauto.
  Qed.

  Lemma elim_mv_code_spec : forall c c' pc ins d s,
    c ! pc = Some ins ->
    c' = elim_mv_code d s c ->
    c' ! pc = Some ins \/
    match ins with
    | Inop pc' => c' ! pc = Some (Inop pc')
    | Iop Omove _ dst pc' =>
      (dst = d /\ c' ! pc = Some (Inop pc')) \/
      exists args', c' ! pc = Some (Iop Omove args' dst pc')
    | Iop op _ dst pc' =>
      exists args', c' ! pc = Some (Iop op args' dst pc')
    | Iload chunk addr args dst pc' =>
      exists args', c' ! pc =
      Some (Iload chunk addr args' dst pc')
    | Istore chunk addr args src pc' =>
      exists args' src', c' ! pc =
      Some (Istore chunk addr args' src' pc')
    | Icall sig ros args res pc' =>
      exists ros' args', c' ! pc =
      Some (Icall sig ros' args' res pc')
    | Itailcall sig ros args =>
      exists ros' args', c' ! pc = Some (Itailcall sig ros' args')
    | Ibuiltin ef args res pc' =>
      exists args', c' ! pc = Some (Ibuiltin ef args' res pc')
    | Icond cond args ifso ifnot =>
      exists args', c' ! pc = Some (Icond cond args' ifso ifnot)
    | Ijumptable arg tbl =>
      exists arg', c' ! pc = Some (Ijumptable arg' tbl)
    | Ireturn optarg => exists optarg', c' ! pc = Some (Ireturn optarg')
  end.
  Proof.
    unfold elim_mv_code. i. subst. rewrite PTree.gmap. rewrite H; ss.
    destruct ins; ss; eauto.
    destruct o; ss; eauto. destruct (r =? d)%positive eqn:Erd.
    pose proof Erd as Erd'. rewrite Pos.eqb_eq in Erd'. ss; auto.
    ss. right. right. eauto.
  Qed.

  Lemma fn_code_elim_mv: forall c c' pc ins' d s,
    c' = elim_mv_code d s c ->
    c' ! pc = Some ins' ->
    exists ins, c ! pc = Some ins.
  Proof.
    i. destruct (c ! pc) eqn:Ec; eauto.
    subst. unfold elim_mv_code in H0. rewrite PTree.gmap in H0.
    rewrite Ec in H0. ss.
  Qed.

  Lemma elim_mv_code_spec' : forall c c' pc ins' d s,
    c' = elim_mv_code d s c ->
    c' ! pc = Some ins' ->
    c ! pc = Some ins' \/
    match ins' with
    | Inop pc' =>
      c ! pc = Some (Inop pc') \/
      exists args', c ! pc = Some (Iop Omove args' d pc')
    | Iop op args dst pc' =>
      exists args', c ! pc = Some (Iop op args' dst pc')
    | Iload chunk addr args dst pc' =>
      exists args', c ! pc = Some (Iload chunk addr args' dst pc')
    | Istore chunk addr args src pc' =>
      exists args' src', c ! pc = Some (Istore chunk addr args' src' pc')
    | Icall sig ros args res pc' =>
      exists ros' args', c ! pc = Some (Icall sig ros' args' res pc')
    | Itailcall sig ros args =>
      exists ros' args', c ! pc = Some (Itailcall sig ros' args')
    | Ibuiltin ef args res pc' =>
      exists args', c ! pc = Some (Ibuiltin ef args' res pc')
    | Icond cond args ifso ifnot =>
      exists args', c ! pc = Some (Icond cond args' ifso ifnot)
    | Ijumptable arg tbl =>
      exists arg', c ! pc = Some (Ijumptable arg' tbl)
    | Ireturn optarg => exists optarg', c ! pc = Some (Ireturn optarg')
  end.
  Proof.
    i. eapply fn_code_elim_mv in H0 as Hcins; eauto. des.
    eapply elim_mv_code_spec in Hcins as Hc'; eauto. des.
    - clarify. auto.
    - destruct ins; des; ss; clarify; eauto.
    destruct o; des; ss; clarify; eauto.
  Qed.

  Lemma assigned_code_spec_elim_mv: forall f d s pc r,
    wf_ssa_function f ->
    assigned_code_spec (elim_mv_code d s (fn_code f)) pc r ->
    assigned_code_spec (fn_code f) pc r.
  Proof.
    i. inv H0; edestruct elim_mv_code_spec'; eauto; ss; des;
    assert (assigned_code_spec (fn_code f) pc r) by eauto; eauto.
  Qed.

  Lemma assigned_code_spec_elim_mv': forall f d s pc r,
    wf_ssa_function f ->
    r <> d ->
    assigned_code_spec (fn_code f) pc r ->
    assigned_code_spec (elim_mv_code d s (fn_code f)) pc r.
  Proof.
    i. inv H1; edestruct elim_mv_code_spec; eauto; ss; des;
    eauto using assigned_code_spec.
    destruct op; des; eauto using assigned_code_spec. congruence.
  Qed.

  Lemma assigned_phi_spec_elim_mv: forall f d s pc r,
    wf_ssa_function f ->
    assigned_phi_spec (elim_mv_phicode d s (fn_phicode f)) pc r ->
    assigned_phi_spec (fn_phicode f) pc r.
  Proof.
    unfold elim_mv_phicode. i. inv H0. rewrite PTree.gmap in H1.
    destruct ((fn_phicode f) ! pc) eqn:Ephiblock; ss.
    inv H1. destruct H2 as [args H3].
    econstructor; eauto. remember (map _ _). apply in_split in H3.
    des. clarify. apply map_eq_app in H3. des; clarify.
    apply map_eq_cons in H1. des; clarify. destruct a. ss. inv H0.
    assert (Hin: forall r p ins, In ins (remove_mv_phiblock r p) -> In ins p).
    { induction p0; ss. destruct a; ss. i. flatten H0; ss; auto. intuition. }
    exists l. eapply Hin. rewrite H3. rewrite in_app. right; auto.
  Qed.

  Lemma assigned_phi_spec_elim_mv': forall f d s pc r,
    wf_ssa_function f ->
    r <> d ->
    assigned_phi_spec (fn_phicode f) pc r ->
    assigned_phi_spec (elim_mv_phicode d s (fn_phicode f)) pc r.
  Proof.
    i. inv H1; ss. des; ss. econstructor.
    unfold elim_mv_phicode. rewrite PTree.gmap. rewrite H2. ss.
    exists (map (rename_reg d s) args).
    apply in_split in H3. des. clarify.
    assert (forall l1 l2 d, remove_mv_phiblock d (l1 ++ l2) =
    remove_mv_phiblock d l1 ++ remove_mv_phiblock d l2).
    { induction l0; ss. i. destruct a; ss. flatten. rewrite IHl0. reflexivity. }
    rewrite H1. rewrite in_map_iff. exists (Iphi args r). split.
    reflexivity. apply in_app_iff. right.
    unfold remove_mv_phiblock. flatten; eauto.
    rewrite Pos.eqb_eq in Eq; congruence.
  Qed.

  Lemma phi_prop_elim_mv: forall f d s pc p',
    wf_ssa_function f ->
    (elim_mv_phicode d s (fn_phicode f)) ! pc = Some p' ->
    NoDup p' /\
    forall r args args', In (Iphi args r) p' ->
    In (Iphi args' r) p' -> args = args'.
  Proof.
    i. inv H. inv fn_ssa.
    clear fn_ssa_params fn_strict fn_use_def_code fn_wf_block fn_normalized
    fn_phicode_inv fn_code_reached fn_code_closed fn_entry fn_entry_pred
    fn_ext_params_complete fn_dom_test_correct H.
    assert (Hphib: exists phib, (fn_phicode f) ! pc = Some phib).
    { unfold elim_mv_phicode in H0. rewrite PTree.gmap in H0.
    destruct (fn_phicode f) ! pc; eauto. }
    des. eapply H1 in Hphib as Hphibnodup; eauto.
    assert (Hpreserve: forall p p', NoDup p /\
    (forall r args args', In (Iphi args r) p ->
    In (Iphi args' r) p ->
    args = args') ->
    p' = map (subst_phi d s) (remove_mv_phiblock d p) ->
    NoDup p' /\
    (forall r args args', In (Iphi args r) p' ->
    In (Iphi args' r) p' ->
    args = args')).
    { induction p; ss.
    - i. clarify.
    - i. destruct a; ss. flatten H2.
    + eapply IHp; eauto. des. inv H. split; auto. i. eauto.
    + assert (forall pb l0 l l',
    remove_mv_phiblock d pb = l ++ Iphi l0 r :: l' ->
    In (Iphi l0 r) pb).
    { induction pb; ss; i. destruct l1; ss. destruct a; ss.
    flatten H0. apply IHpb in H3. right; auto.
    destruct l1.
    - simpl in H3. inv H3. left; auto.
    - inv H3. apply IHpb in H6. right; auto. }
    ss; des; split.
    * clarify. constructor.
    intros contra. rewrite in_map_iff in contra. des.
    destruct x. ss. inv contra. inv H. apply in_split in contra0. des.
    specialize (H3 _ _ _ _ contra0). specialize (H4 r l l0).
    assert (l = l0); auto. subst. auto.
    exploit IHp. split. inv H; auto. i. eauto. reflexivity.
    i. des. auto.
    * assert (Hpres: forall d s r phiblock args,
    (r =? d)%positive = false ->
    In (Iphi args r)
    (map (subst_phi d s) (remove_mv_phiblock d phiblock)) ->
    exists args', In (Iphi args' r) phiblock).
    { intros d0 s0 r2 phiblock; revert d0 s0.
    induction phiblock; ss. i. destruct a; ss. flatten H6.
    - destruct (IHphiblock _ _ _ H5 H6). exists x. right; eauto.
    - ss. des.
    + inv H6. exists l0. left. auto.
    + destruct (IHphiblock _ _ _ H5 H6). exists x. right. eauto. }
    i. clarify; ss. des.
    inv H5. inv H6. reflexivity.
    inv H5. inv H. specialize (Hpres _ _ _ _ _ Eq H6). des.
    exploit H4. left; reflexivity. right; apply Hpres. i. subst. intuition.
    inv H6. inv H. specialize (Hpres _ _ _ _ _ Eq H5). des.
    exploit H4. left; reflexivity. right; apply Hpres. i. subst. intuition.
    eapply IHp. inv H. split. auto. i. eapply H4; eauto.
    reflexivity. apply H5. apply H6. }
    unfold elim_mv_phicode in H0. rewrite PTree.gmap in H0. rewrite Hphib in H0.
    ss. inv H0. eapply Hpreserve; eauto.
  Qed.

  Lemma elim_mv_preserve_unique_def_spec: forall f f' c p d s,
    wf_ssa_function f ->
    (fn_code f) = c ->
    (fn_phicode f) = p ->
    find_mv_code c = Some (d, s) \/ find_mv_phicode p = Some (d, s) ->
    f' = mkfunction
    (fn_sig f)
    (fn_params f)
    (fn_stacksize f)
    (elim_mv_code d s c)
    (elim_mv_phicode d s p)
    (fn_entrypoint f)
    (fn_ext_params f)
    (fn_dom_test f) ->
    unique_def_spec f'.
  Proof.
    i. repeat split.
    - i. clarify; ss. eapply assigned_code_spec_elim_mv in H4, H5; eauto.
    inv H. inv fn_ssa. specialize (H r pc pc'). des; eauto.
    - i. clarify; ss. eapply assigned_phi_spec_elim_mv in H4, H5; eauto.
    inv H. inv fn_ssa. specialize (H r pc pc'). des; eauto.
    - ii. clarify; ss. eapply assigned_code_spec_elim_mv in H4; eauto.
    eapply assigned_phi_spec_elim_mv in H5; eauto.
    inv H. inv fn_ssa. specialize (H r pc pc').
    des; eapply H3 in H5; eauto.
    - ii. clarify; ss. eapply assigned_phi_spec_elim_mv in H4; eauto.
    eapply assigned_code_spec_elim_mv in H5; eauto.
    inv H. inv fn_ssa. specialize (H r pc pc').
    des; eapply H6 in H4; eauto.
    - eapply phi_prop_elim_mv; eauto. clarify; eauto.
    - eapply phi_prop_elim_mv; eauto. clarify; eauto.
  Qed.

  Lemma cfg_elim_mv: forall f f' c p d s,
    (fn_code f) = c ->
    (fn_phicode f) = p ->
    f' = mkfunction
    (fn_sig f)
    (fn_params f)
    (fn_stacksize f)
    (elim_mv_code d s c)
    (elim_mv_phicode d s p)
    (fn_entrypoint f)
    (fn_ext_params f)
    (fn_dom_test f) ->
    (forall i j, cfg f i j <-> cfg f' i j).
  Proof.
    split; i; clarify.
    - inv H2. exploit elim_mv_code_spec; eauto; i; des;
    try (econstructor; eauto; fail);
    destruct ins; eauto; des; try (econstructor; eauto; fail).
    destruct o; des; econstructor; eauto.
    - inv H2. exploit elim_mv_code_spec'; eauto; i; des;
    try (econstructor; eauto; fail);
    destruct ins; eauto; des; try (econstructor; eauto; fail).
  Qed.

  Lemma fn_entrypoint_elim_mv: forall f f' c p d s,
    (fn_code f) = c ->
    (fn_phicode f) = p ->
    f' = mkfunction
    (fn_sig f)
    (fn_params f)
    (fn_stacksize f)
    (elim_mv_code d s c)
    (elim_mv_phicode d s p)
    (fn_entrypoint f)
    (fn_ext_params f)
    (fn_dom_test f) ->
    (fn_entrypoint f) = (fn_entrypoint f').
  Proof.
    i; ss; clarify; eauto.
  Qed.

  Lemma reached_elim_mv: forall f f' c p d s,
    (fn_code f) = c ->
    (fn_phicode f) = p ->
    f' = mkfunction
    (fn_sig f)
    (fn_params f)
    (fn_stacksize f)
    (elim_mv_code d s c)
    (elim_mv_phicode d s p)
    (fn_entrypoint f)
    (fn_ext_params f)
    (fn_dom_test f) ->
    (forall i, reached f i <-> reached f' i).
  Proof.
    split; intros.
    erewrite <- (fn_entrypoint_elim_mv f); eauto.
    apply star_eq with (cfg f); eauto.
    intros; erewrite <- cfg_elim_mv; eauto.
    apply star_eq with (cfg f'); auto.
    intros a b; erewrite <- cfg_elim_mv; eauto.
    erewrite <- (fn_entrypoint_elim_mv f) in *; eauto.
  Qed. 

  Lemma exit_exit : forall f f' c p d s pc,
    (fn_code f) = c ->
    (fn_phicode f) = p ->
    f' = mkfunction
    (fn_sig f)
    (fn_params f)
    (fn_stacksize f)
    (elim_mv_code d s c)
    (elim_mv_phicode d s p)
    (fn_entrypoint f)
    (fn_ext_params f)
    (fn_dom_test f) ->
    exit f pc <-> exit f' pc.
  Proof.
    split.
    - intros.
    assert (Hins: exists ins, (fn_code f) ! pc = Some ins).
    { unfold exit in *.
    flatten NOSTEP; eauto.
    inv H2; go. } 
    destruct Hins as [ins0 Hins0].
    assert (exists ins, (fn_code f') ! pc = Some ins).
    { clarify; ss. unfold elim_mv_code. rewrite PTree.gmap. rewrite Hins0.
    ss. eauto. }
    destruct H3 as [ins Hins].
    unfold exit in *; rewrite Hins in *; rewrite Hins0 in *. clarify; ss.
    exploit elim_mv_code_spec. apply Hins0. auto. i; des.
    + rewrite H in Hins; inv Hins. auto.
    + destruct ins0; ss; des; clarify.
    - intros.
    assert (Hins: exists ins, (fn_code f') ! pc = Some ins).
    { unfold exit in *.
    flatten NOSTEP; eauto.
    inv H; go. }
    destruct Hins as [ins0 Hins0].
    unfold exit in *; rewrite Hins0 in *. clarify; ss.
    exploit elim_mv_code_spec'; eauto. i; des.
    + rewrite H; ss.
    + destruct ins0; des; ss; clarify; rewrite H; eauto.
  Qed.

  Lemma ssapath_elim_mv: forall f f' c p d s,
    (fn_code f) = c ->
    (fn_phicode f) = p ->
    f' = mkfunction
    (fn_sig f)
    (fn_params f)
    (fn_stacksize f)
    (elim_mv_code d s c)
    (elim_mv_phicode d s p)
    (fn_entrypoint f)
    (fn_ext_params f)
    (fn_dom_test f) ->
    (forall i j p, SSApath f i p j <-> SSApath f' i p j).
  Proof.
    split.
    - induction 1; go.
      econstructor 2 with s2; auto.
      inversion STEP.
      + assert (cfg f' pc pc')
        by (rewrite <- cfg_elim_mv; eauto; econstructor; eauto).
        inv H0.
        econstructor; eauto.
        rewrite <- reached_elim_mv; auto.
        go.
      + assert (Hins: exists ins, (fn_code f) ! pc = Some ins).
        { unfold exit in *.
        flatten NOSTEP; eauto.
        inv H; go. }
        destruct Hins as [ins0 Hins0].
        assert (exists ins, (fn_code f') ! pc = Some ins).
        { clarify. ss. unfold elim_mv_code. rewrite PTree.gmap. rewrite Hins0.
        ss. eauto. }
        des. econstructor; eauto.
      * rewrite reached_elim_mv in CFG; eauto.
      * eapply (exit_exit f); eauto.
    - induction 1; go.
      econstructor 2 with s2; auto.
      inversion STEP.
      + assert (cfg f pc pc') by (rewrite cfg_elim_mv; eauto; econstructor; eauto).
        inv H. econstructor; eauto; ss.
        rewrite reached_elim_mv; eauto. ss; eauto.
      + assert (Hins: exists ins, (fn_code f') ! pc = Some ins).
        { unfold exit in *.
        flatten NOSTEP; eauto.
        inv H; go. } 
        destruct Hins as [ins0 Hins0].
        assert (exists ins, (fn_code f) ! pc = Some ins).
        { clarify; ss. unfold elim_mv_code in Hins0. rewrite PTree.gmap in Hins0.
        destruct ((fn_code f) ! pc); ss. eauto. }
        des. econstructor; eauto. rewrite reached_elim_mv; eauto.
        eapply exit_exit; eauto.
  Qed.

  Lemma dom_elim_mv: forall f f' c p d s,
    (fn_code f) = c ->
    (fn_phicode f) = p ->
    f' = mkfunction
    (fn_sig f)
    (fn_params f)
    (fn_stacksize f)
    (elim_mv_code d s c)
    (elim_mv_phicode d s p)
    (fn_entrypoint f)
    (fn_ext_params f)
    (fn_dom_test f) ->
    (forall n m, dom f n m <-> dom f' n m).
  Proof.
    split; i.
    - inv H2. constructor. constructor.
      + apply star_eq with (cfg f); auto. intros i j.
        erewrite cfg_elim_mv; eauto.
      + i. apply PATH. rewrite ssapath_elim_mv; eauto.
    - inversion H2. constructor. constructor.
      + apply star_eq with (cfg f'); auto. intros i j.
        erewrite <- cfg_elim_mv; eauto.
        clarify.
      + i. apply PATH. clarify. rewrite <- ssapath_elim_mv; eauto.
  Qed.

  Lemma successors_elim_mv: forall f f' d s pc,
    f' = mkfunction
    (fn_sig f)
    (fn_params f)
    (fn_stacksize f)
    (elim_mv_code d s (fn_code f))
    (elim_mv_phicode d s (fn_phicode f))
    (fn_entrypoint f)
    (fn_ext_params f)
    (fn_dom_test f) ->
    (successors f) ! pc = (successors f') ! pc.
  Proof.
    i. unfold successors. repeat rewrite PTree.gmap1. unfold option_map.
    destruct (fn_code f) ! pc eqn:Efpc.
    - clarify; ss. eapply elim_mv_code_spec in Efpc as Ef'pc; eauto; des; clarify.
      + rewrite Ef'pc; ss.
      + destruct i; des; ss; try rewrite Ef'pc; ss.
        destruct o; des; ss; try rewrite Ef'pc; ss. rewrite Ef'pc0; ss.
    - destruct (fn_code f') ! pc eqn:Ef'pc; ss.
      eapply elim_mv_code_spec' in Ef'pc; ss; eauto; des.
      rewrite Efpc in Ef'pc; ss. destruct i; des; rewrite Efpc in *; discriminate.
      clarify.
  Qed. 

  Lemma make_predecessors_elim_mv: forall f f' d s,
    f' = mkfunction
    (fn_sig f)
    (fn_params f)
    (fn_stacksize f)
    (elim_mv_code d s (fn_code f))
    (elim_mv_phicode d s (fn_phicode f))
    (fn_entrypoint f)
    (fn_ext_params f)
    (fn_dom_test f) ->
    (Kildall.make_predecessors (fn_code f') successors_instr) =
    (Kildall.make_predecessors (fn_code f) successors_instr).
  Proof.
    intros.
    eapply same_successors_same_predecessors. i.
    eapply successors_elim_mv in H. unfold successors in *; eauto.
  Qed.

  Lemma join_point_elim_mv: forall f f' d s j,
    f' = mkfunction
    (fn_sig f)
    (fn_params f)
    (fn_stacksize f)
    (elim_mv_code d s (fn_code f))
    (elim_mv_phicode d s (fn_phicode f))
    (fn_entrypoint f)
    (fn_ext_params f)
    (fn_dom_test f) ->
    join_point j f <-> join_point j f'.
  Proof.
    split; intros.
    - inversion H0.
      erewrite @same_successors_same_predecessors with 
          (m2:= (fn_code f'))
          (f2:= successors_instr) in Hpreds; eauto.
      + econstructor; eauto.
      + i; eapply successors_elim_mv in H; unfold successors in *; eauto.
    - inversion H0.
      erewrite @same_successors_same_predecessors with 
          (m2:= (fn_code f))
          (f2:= successors_instr) in Hpreds; eauto.
      + econstructor; eauto.
      + generalize (successors_elim_mv f).
        unfold successors. intros Hsuccs i. 
        rewrite <- Hsuccs at 1; eauto.
  Qed.

  Lemma successors_list_elim_mv: forall f f' d s pc,
    f' = mkfunction
    (fn_sig f)
    (fn_params f)
    (fn_stacksize f)
    (elim_mv_code d s (fn_code f))
    (elim_mv_phicode d s (fn_phicode f))
    (fn_entrypoint f)
    (fn_ext_params f)
    (fn_dom_test f) ->
    (Kildall.successors_list (successors f) pc) =
    (Kildall.successors_list (successors f') pc).
  Proof.
    unfold Kildall.successors_list. i. erewrite successors_elim_mv; eauto.
  Qed.

  Lemma use_exists_def : forall f x u,
    use f x u -> exists d, def f x d.
  Proof.
    intros.
    destruct (classic (exists pc, assigned_code_spec (fn_code f) pc x)).
    destruct H0 ; eauto.
    destruct (classic (exists pc, assigned_phi_spec (fn_phicode f) pc x)).
    destruct H1 ; eauto.
    exists (fn_entrypoint f) ; eauto.
    econstructor ; eauto.
    econstructor 2 ; eauto.
  Qed.  
  
  Lemma path_first : forall f p pc pc',
    SSApath f (Dom.PState pc) p (Dom.PState pc') ->
    pc <> pc' ->
    exists pc'', exists p', exists p'',
      SSApath f (Dom.PState pc) p' (Dom.PState pc'') /\
      ~ In pc' p' /\
      pc'' <> pc' /\
      Dom.path_step (cfg f) (exit f) (fn_entrypoint f)
                    (Dom.PState pc'') pc'' (Dom.PState pc') /\
      p = p'++(pc''::p'').
  Proof.
    induction p ; intros; inv H. 
    congruence.
    assert (a = pc) by (inv STEP; auto). inv H.
    destruct s2.
    destruct (peq pc0 pc').
    (* peq *)
    inv e.  exists pc. exists nil. exists p.
    split; eauto.  econstructor ; eauto.
    (* diff *)
    exploit IHp ; eauto. intros [pc'' [p'  [p'' [Hp' [Hpc'' [Hdiff [Hnotin Happ]]]]]]].
    exists pc''. exists (pc::p'). exists p''.
    split ; auto.
    econstructor ; eauto. 
    split ; auto.
    intro Hcont. inv Hcont. congruence. elim Hpc'' ; auto.
    split. intro Hcont. inv Hcont. congruence.
    split ; eauto. simpl. rewrite Happ ; auto.
    exploit (@Dom.path_from_ret_nil node); eauto. intros Heq ; subst. 
    inv PATH.
  Qed.

  Lemma no_infinite_loop: forall f pc,
    wf_ssa_function f ->
    reached f pc ->
    join_point pc f ->
    (forall pc', In pc' (Kildall.successors_list
                (Kildall.make_predecessors (fn_code f) successors_instr) pc) ->
    dom f pc pc') ->
    False.
  Proof.
    i. apply (Dom.reached_path _ (exit f)) in H0 as HPATH. des.
    remember (Datatypes.length p) as len. revert f pc H H0 p HPATH H1 H2 Heqlen.
    induction len; ss.
    - i. symmetry in Heqlen. apply length_zero_iff_nil in Heqlen. clarify.
      inv HPATH. eapply fn_entrypoint_inv; eauto.
    - i. eapply path_first in HPATH as Hf; eauto. des. inv Hf2. inv STEP.
      assert (dom f pc pc''). apply H2.
      eapply Kildall.make_predecessors_correct_1; eauto.
      inv H4. congruence. apply PATH in Hf as Hi. auto.
      ii; clarify. eapply fn_entrypoint_inv; eauto.
  Qed.

  Lemma no_phi_use_def: forall f s,
    wf_ssa_function f ->
    find_mv_phicode (fn_phicode f) = Some (s, s) ->
    False.
  Proof.
    i. eapply find_mv_phicode_exists in H0. des.
    eapply no_infinite_loop; eauto.
    - apply fn_phicode_code in H0; auto. des; eauto.
    - eapply assigned_phi_spec_join_point; eauto.
    - i. eapply assigned_phi_spec_join_point in H as Hjoin; eauto.
      eapply make_predecessors_some in H3 as Hsome; eauto.
      2:{ unfold make_preds. unfold Kildall.successors_list in *.
          destruct (Kildall.make_predecessors (fn_code f) successors_instr) ! pc
            eqn:PREDS.
          ss. rewrite PREDS. auto. inv H3. }
      des.
      assert (Hu: use_phicode f s pc').
      { eapply index_pred_instr_some in Hsome as Hin; eauto.
        2:{ eapply make_predecessors_correct2; eauto. }
        des. econstructor; eauto.
        eapply index_pred_some_nth in Hin as Hnth; eauto.
        inv H. eapply fn_wf_block in H1; eauto.
        eapply nth_error_some_same_length in H1; eauto. des. rewrite H1.
        apply nth_error_some_in in H1. inv H1; clarify; ss.
        rewrite forallb_forall in H2. apply H2 in H. rewrite Pos.eqb_eq in H.
        clarify. }
      assert (Hu': use f s pc') by eauto using use. inv H; eauto.
  Qed.

  Lemma no_phi_use_def' : forall f pc pc' phib args src dst,
    wf_ssa_function f ->
    (fn_phicode f) ! pc = Some phib ->
    In (Iphi args dst) phib ->
    (forall r, In r args -> r = src) ->
    def f src pc' ->
    dom f pc pc' ->
    False.
  Proof.
    i. pose proof fn_phicode_code; eauto. eapply H5 in H as PCCODE; eauto.
    clear H5. des. eapply no_infinite_loop; eauto.
    eapply phicode_joinpoint; eauto.
    i. eapply make_predecessors_some in H5 as PC'CODE; eauto.
    2:{ unfold make_preds. unfold Kildall.successors_list in *.
        destruct (Kildall.make_predecessors _ _) ! pc eqn:PREDSPC; ss.
        eauto. } des.
    eapply make_predecessors_correct2 in H5 as HIN; eauto.
    eapply index_pred_instr_some in HIN as PC'SOME; eauto. des.
    eapply (Dom.dom_trans peq). eauto.
    eapply fn_strict; eauto. econstructor 2; eauto. econstructor; eauto.
    eapply index_pred_some_nth in PC'SOME.
    eapply nth_error_some_same_length in PC'SOME. des. rewrite PC'SOME.
    eapply nth_error_in in PC'SOME. eapply H2 in PC'SOME; inv PC'SOME; clarify.
    exploit fn_wf_block; eauto.
  Qed.


  Lemma use_code_d_elim_mv: forall f f' d s pc,
    d <> s ->
    f' = mkfunction
    (fn_sig f)
    (fn_params f)
    (fn_stacksize f)
    (elim_mv_code d s (fn_code f))
    (elim_mv_phicode d s (fn_phicode f))
    (fn_entrypoint f)
    (fn_ext_params f)
    (fn_dom_test f) ->
    use_code f' d pc -> False.
  Proof.
    assert (Hnotin: forall l d s, d <> s -> ~ In d (map (rename_reg d s) l)).
    { induction l; ss. ii. destruct H0. unfold rename_reg in *. flatten H0.
      clarify. rewrite Pos.eqb_neq in Eq; eauto. eapply IHl; eauto. }
    assert (Hnotinbarg: forall a d s, d <> s ->
                        ~ In d (params_of_builtin_arg (rename_barg d s a))).
    { induction a; ss.
      - ii. des; eauto. unfold rename_reg in H0; flatten H0.
        rewrite Pos.eqb_neq in Eq; congruence.
      - ii. rewrite in_app_iff in H0; des.
        + eapply IHa1; eauto.
        + eapply IHa2; eauto.
      - ii. rewrite in_app_iff in H0; des.
        + eapply IHa1; eauto.
        + eapply IHa2; eauto. }
    assert (Hnotin': forall l d s, d <> s ->
                     ~ In d (params_of_builtin_args (map (rename_barg d s) l))).
    { induction l; ss. ii. rewrite in_app_iff in H0; des.
      - apply Hnotinbarg in H0; eauto.
      - eapply IHl; eauto. }
    i. clarify; ss.
    inv H1; ss; eapply elim_mv_code_spec' in H0 as Hf; des; eauto;
    unfold elim_mv_code in *; rewrite PTree.gmap in *; rewrite Hf in *; ss;
    try (apply in_split in H2; des; clarify;
        unfold subst_instr in *; clarify; try destruct op; clarify; flatten H0;
        eapply Hnotin; eauto; try rewrite H3; try rewrite H0;
        rewrite in_app_iff; eauto);
    try (clarify; try rewrite <- H0 in *; eapply Hnotin' in H2; eauto).
    unfold rename_reg in H0; flatten H0. rewrite Pos.eqb_neq in Eq; eauto.
    clarify. rewrite <- H3 in H2; eapply Hnotin in H2; eauto.
    clarify. unfold rename_reg in H0; flatten H0. rewrite Pos.eqb_neq in Eq; eauto.
    clarify. eapply Hnotin in H2; eauto.
    clarify. unfold rename_reg in H2; flatten H2. rewrite Pos.eqb_neq in Eq; eauto.
    clarify. destruct ros'; ss; clarify. unfold rename_reg in H1.
    flatten H1; ss; rewrite Pos.eqb_neq in Eq; eauto.
    clarify. unfold rename_reg in H2; flatten H2. rewrite Pos.eqb_neq in Eq; eauto.
    clarify. destruct ros'; ss; clarify. unfold rename_reg in H1.
    flatten H1; ss; rewrite Pos.eqb_neq in Eq; eauto.
    clarify. unfold rename_reg in H0; flatten H0. rewrite Pos.eqb_neq in Eq; eauto.
    clarify. unfold rename_reg in H0; flatten H0. rewrite Pos.eqb_neq in Eq; eauto.
    clarify. unfold rename_reg in H0; flatten H0. rewrite Pos.eqb_neq in Eq; eauto.
    clarify. unfold rename_reg in H0; flatten H0.
    destruct optarg'; clarify. ss. flatten H0; clarify.
    rewrite Pos.eqb_neq in Eq; eauto.
  Qed.

  Lemma use_reg_elim_mv: forall f f' d s pc,
    d <> s ->
    f' = mkfunction
    (fn_sig f)
    (fn_params f)
    (fn_stacksize f)
    (elim_mv_code d s (fn_code f))
    (elim_mv_phicode d s (fn_phicode f))
    (fn_entrypoint f)
    (fn_ext_params f)
    (fn_dom_test f) ->
    use f' d pc -> False.
  Proof.
    i. inv H1.
    - eapply use_code_d_elim_mv in H2; eauto.
    - inv H2; ss.
      unfold elim_mv_phicode in PHIB; rewrite PTree.gmap in PHIB.
      destruct (fn_phicode f) ! pc0 eqn:Efpc; ss. inv PHIB.
      assert (forall phib args dst, In (Iphi args dst) (map (subst_phi d s) phib) ->
                                    nth_error args k = Some d ->
                                    False).
      { induction phib; ss. i. des.
        - destruct a. ss. inv H0. apply nth_error_split in H1. des.
          assert (forall l, In d (map (rename_reg d s) l) -> False).
          { induction l0; ss. i; des.
            - unfold rename_reg in H2. flatten H2.
              rewrite Pos.eqb_neq in Eq; congruence.
            - eauto. }
          eapply H2. rewrite H1; eauto. rewrite in_app_iff. right; eauto.
        - eauto. }
      eauto.
  Qed.

  Lemma use_code_indep_elim_mv: forall f f' c p d s,
    wf_ssa_function f ->
    (fn_code f) = c ->
    (fn_phicode f) = p ->
    find_mv_code c = Some (d, s) \/ find_mv_phicode p = Some (d, s) ->
    f' = mkfunction
    (fn_sig f)
    (fn_params f)
    (fn_stacksize f)
    (elim_mv_code d s c)
    (elim_mv_phicode d s p)
    (fn_entrypoint f)
    (fn_ext_params f)
    (fn_dom_test f) ->
    (forall x u, use_code f' x u ->
     x <> d /\ x <> s ->
     use_code f x u).
  Proof.
    assert (Hin: forall l d s x, x <> s -> In x (map (rename_reg d s) l) -> In x l).
    { induction l; ss. ii. des; clarify. left. unfold rename_reg in *. flatten.
      right; eauto. }
    assert (Hinb: forall l d s x, x <> s ->
                  In x (params_of_builtin_args (map (rename_barg d s) l)) ->
                  In x (params_of_builtin_args l)).
    { 
      assert (forall a d s x, x <> s ->
                              In x (params_of_builtin_arg (rename_barg d s a)) ->
                              In x (params_of_builtin_arg a)).
      { induction a; ss; i.
        - des; eauto. unfold rename_reg in H0. flatten H0; eauto.
        - apply in_app_iff. apply in_app_iff in H0; des; eauto.
        - apply in_app_iff. apply in_app_iff in H0; des; eauto. }
      induction l; ss. ii. apply in_app_iff. apply in_app_iff in H1. des; eauto. }
    i; clarify; destruct H5.
    inv H4; ss; eapply elim_mv_code_spec' in H3 as Hf; eauto;
    destruct Hf as [Hf | [args' Hf]];
      try (unfold elim_mv_code in *; rewrite PTree.gmap in *; rewrite Hf in *;
           ss; inv H3); try eauto using use_code.
    - destruct op; flatten H6; inv H6; econstructor; eauto.
    - destruct Hf. eapply elim_mv_code_spec' in H3 as Hf; eauto.
      eapply UIstore; eauto. destruct Hf. clarify.
      unfold elim_mv_code in H3; rewrite PTree.gmap in *; rewrite H4 in *; ss.
      inv H3. destruct H5. unfold rename_reg in H3. flatten H3; clarify.
      left; auto. right; eauto.
    - destruct Hf. eapply elim_mv_code_spec' in H3 as Hf; eauto. destruct Hf.
      + clarify. eapply UIcall; eauto.
      + unfold elim_mv_code in H3; rewrite PTree.gmap in *; rewrite H4 in H3; ss;
          inv H3.
        destruct args'; ss. inv H8. eapply UIcall; eauto.
        destruct H5. constructor 1. unfold rename_reg in H3. flatten H3; eauto.
        constructor 2; eauto.
    - destruct Hf as [args'' Hf]. unfold elim_mv_code in H3.
      rewrite PTree.gmap in H3; rewrite Hf in H3; ss; inv H3. destruct args'; ss.
      inv H6. eapply UItailcall; eauto.
      destruct H5. unfold rename_reg in *. flatten H3; eauto. constructor 1; eauto.
      constructor 2; eauto.
    - destruct Hf. eapply elim_mv_code_spec' in H3 as Hf; eauto. destruct Hf.
      + clarify. eapply UIcall2; eauto.
      + unfold elim_mv_code in H3; rewrite PTree.gmap in *; rewrite H4 in H3; ss;
          inv H3.
        destruct args'; ss. inv H8. eapply UIcall2; eauto.
    - destruct Hf as [args'' Hf]. unfold elim_mv_code in H3.
      rewrite PTree.gmap in H3; rewrite Hf in H3; ss; inv H3. destruct args'; ss.
      inv H6. eapply UItailcall2; eauto.
    - eapply UIjump; eauto. rewrite H5; eauto.
    - eapply UIjump; eauto. assert (rename_reg d s args' = args').
      { unfold rename_reg. flatten; eauto. rewrite Pos.eqb_eq in Eq; clarify.
        unfold rename_reg in *; eauto. flatten H1. }
      rewrite H3; eauto.
    - rewrite H5. eauto using use_code.
    - destruct args'; ss. inv H5. unfold rename_reg in *. flatten; ss.
      eauto using use_code.
  Qed.

  Lemma use_indep_elim_mv: forall f f' c p d s,
    wf_ssa_function f ->
    (fn_code f) = c ->
    (fn_phicode f) = p ->
    find_mv_code c = Some (d, s) \/ find_mv_phicode p = Some (d, s) ->
    f' = mkfunction
    (fn_sig f)
    (fn_params f)
    (fn_stacksize f)
    (elim_mv_code d s c)
    (elim_mv_phicode d s p)
    (fn_entrypoint f)
    (fn_ext_params f)
    (fn_dom_test f) ->
    (forall x u, x <> d -> x <> s -> use f' x u -> use f x u).
  Proof.
    i. inv H6.
    - eapply use_code_indep_elim_mv in H7; eauto. econstructor; eauto.
    - inv H7; ss.
      unfold elim_mv_phicode in PHIB. rewrite PTree.gmap in PHIB.
      destruct (fn_phicode f) ! pc eqn:EFPHI; ss. inv PHIB.
      assert (forall p' args dst,
              In (Iphi args dst) (map (subst_phi d s) (remove_mv_phiblock d p')) ->
              nth_error args k = Some x ->
              exists args',
              args = map (rename_reg d s) args' /\
              In (Iphi args' dst) p' /\
              nth_error args' k = Some x).
      { induction p'; ss. i. destruct a; ss. flatten H0.
        - eapply IHp' in H0; eauto. destruct H0. exists x0. des; eauto.
        - ss. destruct H0.
          + inv H0. exists l. split; ss. split. left; ss.
            assert (forall l k, nth_error (map (rename_reg d s) l) k = Some x ->
                                nth_error l k = Some x).
            { induction l0; ss. i. destruct k0; ss.
              - inv H0. unfold rename_reg in *. flatten.
              - eauto. }
            eauto.
          + eapply IHp' in H0; eauto. des; eauto.  }
      eapply H0 in KARG as KARG'; eauto.
      destruct KARG' as [args' [Hargs' [Hin Hn]]].
      econstructor 2. econstructor.
      apply EFPHI. apply Hin. apply Hn.
      erewrite <- make_predecessors_elim_mv; eauto. ss. apply KPRED.
  Qed.

  Lemma def_indep_elim_mv: forall f f' c p d s,
    wf_ssa_function f ->
    (fn_code f) = c ->
    (fn_phicode f) = p ->
    find_mv_code c = Some (d, s) \/ find_mv_phicode p = Some (d, s) ->
    f' = mkfunction
        (fn_sig f)
        (fn_params f)
        (fn_stacksize f)
        (elim_mv_code d s c)
        (elim_mv_phicode d s p)
        (fn_entrypoint f)
        (fn_ext_params f)
        (fn_dom_test f) ->
    (forall x u, x <> d -> x <> s -> def f' x u -> def f x u).
  Proof.
  i. inv H6.
  - ss. inversion H7; ss.
    + econstructor. econstructor. auto.
    + destruct H0 as [pc Huse].
      eapply use_indep_elim_mv in Huse; eauto.
      econstructor. econstructor 2; eauto.
      ii. eapply assigned_phi_spec_elim_mv' in H0. apply H1 in H0; eauto.
      eauto. eauto.
      ii. eapply assigned_code_spec_elim_mv' in H0. apply H3 in H0; eauto.
      eauto. eauto.
  - eapply assigned_code_spec_elim_mv in H7; eauto.
  - eapply assigned_phi_spec_elim_mv in H7; eauto.
  Qed.

  Lemma elim_mv_same_reg: forall f c p pc phib s args,
    wf_ssa_function f ->
    c = fn_code f ->
    p = fn_phicode f ->
    p ! pc = Some phib ->
    In (Iphi (s :: args) s) phib ->
    forallb (Pos.eqb s) args = true ->
    forall pc', c ! pc' = (elim_mv_code s s c) ! pc' /\
    forall pc'', pc'' <> pc -> p ! pc'' = (elim_mv_phicode s s p) ! pc''.
  Proof.
    assert (Hrrss: forall s r, rename_reg s s r = r).
    { unfold rename_reg; i; flatten; ss. rewrite Pos.eqb_eq in Eq; eauto. }
    assert (Hrrss': forall l s, map (rename_reg s s) l = l).
    { induction l; ss. i. rewrite Hrrss. rewrite IHl; eauto. }
    assert (Hrfss: forall s r, rename_fn s s r = r).
    { unfold rename_fn. destruct r; ss. rewrite Hrrss; eauto. }
    assert (Hrbss: forall barg s, rename_barg s s barg = barg).
    { induction barg; ss.
      - i; rewrite Hrrss; auto.
      - i; rewrite IHbarg1; rewrite IHbarg2; auto.
      - i; rewrite IHbarg1; rewrite IHbarg2; auto. }
    assert (Hrbss': forall l s, map (rename_barg s s) l = l).
    { induction l; ss. i; rewrite IHl. rewrite Hrbss; eauto. }
    assert (Hss: forall i s, subst_instr s s i = i).
    { i. unfold subst_instr.
      destruct i; ss; try rewrite Hrrss'; eauto; try rewrite Hrrss; eauto;
        try rewrite Hrfss; eauto; try rewrite Hrbss'; eauto.
      destruct o; ss. rewrite Hrrss; eauto.  }
    assert (Hspss: forall phib s, map (subst_phi s s) phib = phib).
    { induction phib; ss. i; rewrite IHphib. unfold subst_phi.
      destruct a; rewrite Hrrss'; ss. }
    i. split.
    - clarify. unfold elim_mv_code. rewrite PTree.gmap.
      destruct (fn_code f) ! pc' eqn:FPC'; ss.
      rewrite Hss.
      destruct i; ss. destruct o; ss. flatten; ss.
      rewrite Pos.eqb_eq in Eq; clarify.
      assert (Ha: assigned_code_spec (fn_code f) pc' s) by eauto.
      eapply assigned_code_and_phi in Ha; eauto. destruct Ha.
    - i. unfold elim_mv_phicode. rewrite PTree.gmap.
      destruct (p ! pc'') eqn:PPC''; ss. rewrite Hspss.
      assert (forall phib s, (forall args, ~ In (Iphi args s) phib) ->
              remove_mv_phiblock s phib = phib).
      { induction phib0; ss. i. destruct a; ss. flatten.
        - rewrite Pos.eqb_eq in Eq; clarify. exfalso; eapply H6; left; auto.
        - erewrite IHphib0; eauto. }
      rewrite H6; auto. ii. clarify.
      assert (def f s pc'') by eauto using def.
      assert (def f s pc) by eauto using def. eapply ssa_def_unique in H0; eauto.
  Qed.

  Lemma use_phicode_exists: forall f pc phib args s d,
    wf_ssa_function f ->
    (fn_phicode f) ! pc = Some phib ->
    In (Iphi (s :: args) d) phib ->
    forallb (Pos.eqb s) args = true ->
    exists pc', use f s pc'.
  Proof.
    i. assert (join_point pc f). { eapply assigned_phi_spec_join_point; eauto. }
    inv H3. destruct l; ss; try lia. destruct l; ss; try lia.
    exists p; econstructor 2. econstructor; eauto. instantiate (1 := 0); ss.
    unfold index_pred. unfold Kildall.successors_list.
    rewrite Hpreds. unfold Utils.get_index; ss. flatten; ss.
  Qed.

  Lemma def_s_elim_mv: forall f f' c p d s,
    wf_ssa_function f ->
    (fn_code f) = c ->
    (fn_phicode f) = p ->
    find_mv_code c = Some (d, s) \/ find_mv_phicode p = Some (d, s) ->
    f' = mkfunction
    (fn_sig f)
    (fn_params f)
    (fn_stacksize f)
    (elim_mv_code d s c)
    (elim_mv_phicode d s p)
    (fn_entrypoint f)
    (fn_ext_params f)
    (fn_dom_test f) ->
    d <> s ->
    forall pc, def f' s pc -> def f s pc.
  Proof.
    i. inv H5.
    - inv H6; ss.
      + econstructor. econstructor. auto.
      + des.
        * eapply find_mv_exists in H2; eauto. des.
          assert (use f s pc0) by (econstructor; eauto using use_code).
          econstructor. econstructor 2; eauto.
          ii. eapply assigned_phi_spec_elim_mv' in H6; eauto. eapply H1; eauto.
          ii. eapply assigned_code_spec_elim_mv' in H6; eauto. eapply H3; eauto.
        * eapply find_mv_phicode_exists in H2; eauto. des.
          eapply use_phicode_exists in H5; eauto. des.
          econstructor. econstructor 2; eauto.
          ii. eapply assigned_phi_spec_elim_mv' in H7; eauto. eapply H1; eauto.
          ii. eapply assigned_code_spec_elim_mv' in H7; eauto. eapply H3; eauto.
    - ss. inv H6; eapply elim_mv_code_spec' in H0; ss; des; eauto using def.
    - ss. inv H6.
      unfold elim_mv_phicode in H0. rewrite PTree.gmap in H0; ss.
      destruct (fn_phicode f) ! pc eqn:FPHI; ss. destruct H1.
      econstructor 3. econstructor; eauto. inv H0.
      apply map_in_some in H1 as Hi; auto. destruct Hi as [ins [Hi Hs]].
      destruct ins; ss. inv Hs.
      assert (Hr: forall l args, In (Iphi args s) (remove_mv_phiblock d l) ->
                  exists args', In (Iphi args' s) l).
      { induction l0; ss. destruct a; ss. i. flatten H0; ss.
        - apply IHl0 in H0; des; eauto.
        - destruct H0; ss. inv H0. eauto. apply IHl0 in H0; des; eauto. }
      apply Hr in Hi. destruct Hi. eauto.
  Qed.

  Lemma use_code_s_elim_mv: forall f f' c p d s,
    wf_ssa_function f ->
    (fn_code f) = c ->
    (fn_phicode f) = p ->
    find_mv_code c = Some (d, s) \/ find_mv_phicode p = Some (d, s) ->
    f' = mkfunction
        (fn_sig f)
        (fn_params f)
        (fn_stacksize f)
        (elim_mv_code d s c)
        (elim_mv_phicode d s p)
        (fn_entrypoint f)
        (fn_ext_params f)
        (fn_dom_test f) ->
    d <> s ->
    forall pc, use_code f' s pc -> use_code f s pc \/ use_code f d pc.
  Proof.
    assert (Hds: forall d s x, rename_reg d s x = s -> x = s \/ x = d).
    { unfold rename_reg. i; flatten. flatten H. rewrite Pos.eqb_eq in Eq; clarify.
      right; auto. rewrite Pos.eqb_neq in Eq; clarify; left; auto. }
    assert (Hds': forall l d s, In s (map (rename_reg d s) l) ->
                                In s l \/ In d l).
    { induction l; ss. i. des. apply Hds in H; des; clarify; auto.
      apply IHl in H; eauto. des; eauto. }
    assert (Hbds: forall ba d s,
            In s (params_of_builtin_arg (rename_barg d s ba)) ->
            In s (params_of_builtin_arg ba) \/ In d (params_of_builtin_arg ba)).
    { induction ba; ss. i. des; eauto. apply Hds in H; des; clarify; eauto.
      i. apply in_app_iff in H; des.
      apply IHba1 in H; des; ss; repeat rewrite in_app_iff; eauto.
      apply IHba2 in H; des; ss; repeat rewrite in_app_iff; eauto.
      i. apply in_app_iff in H; des.
      apply IHba1 in H; des; ss; repeat rewrite in_app_iff; eauto.
      apply IHba2 in H; des; ss; repeat rewrite in_app_iff; eauto. }
    assert (Hbds': forall l d s,
            In s (params_of_builtin_args (map (rename_barg d s) l)) ->
            In s (params_of_builtin_args l) \/ In d (params_of_builtin_args l)).
    { induction l; ss. i. apply in_app_iff in H; des.
      - apply Hbds in H; des; eauto.
        left; apply in_app_iff; eauto. right; apply in_app_iff; eauto.
      - apply IHl in H; des.
        left; apply in_app_iff; eauto. right; apply in_app_iff; eauto. }
    assert (Hfds: forall f d s, rename_fn d s f = inl s ->
                                f = inl s \/ f = inl d).
    { i; destruct f; ss. inv H; eauto. apply Hds in H1; des; clarify; eauto.
      left; unfold rename_reg; flatten. }
    i; clarify; ss.
    inv H5; ss; eapply elim_mv_code_spec' in H0 as F'PC; try destruct F'PC; eauto;
        try (left; econstructor; eauto using use_code; fail);
        try destruct H3 as [args' FPC];
        unfold elim_mv_code in *; rewrite PTree.gmap in *;
          try rewrite FPC in *; ss; inv H0;
          try (apply Hds' in H1; des; 
            try (left; eauto using use_code; fail);
            try (right; eauto using use_code; fail));
          try (apply Hbds' in H1; des;
            try (right; eauto using use_code; fail);
            try (left; eauto using use_code; fail)).
    - destruct op; ss; inv H5; try (apply Hds' in H1; des; 
        try (right; eauto using use_code; fail);
        try (left; eauto using use_code)).
      flatten H3; ss. inv H3. apply Hds' in H1; destruct H1.
      left; eauto using use_code.
      right; eauto using use_code.
    - destruct FPC as [src' FPC]. rewrite FPC in *; ss. inv H5.
      destruct H1. apply Hds in H0; destruct H0; clarify.
      left; eauto using use_code. right; eauto using use_code.
      apply Hds' in H0; destruct H0.
      left; eauto using use_code. right; eauto using use_code.
    - destruct FPC as [src' FPC]. rewrite FPC in *; ss. inv H5.
      destruct H1. clarify. apply Hfds in H3; destruct H3; clarify.
      left; eauto using use_code. right; eauto using use_code. destruct args'.
      apply Hds' in H0; destruct H0.
      left; eauto using use_code. right; eauto using use_code.
      unfold rename_fn in H3. inv H3.
    - destruct FPC as [src' FPC]. rewrite FPC in *; ss. inv H5.
      destruct H1. clarify. apply Hfds in H3; destruct H3; clarify.
      left; eauto using use_code. right; eauto using use_code. destruct args'.
      apply Hds' in H0; destruct H0.
      left; eauto using use_code. right; eauto using use_code.
      unfold rename_fn in H3. inv H3.
    - destruct FPC as [src' FPC]. rewrite FPC in *; ss. inv H5.
      apply Hds' in H1; destruct H1; clarify. destruct args'.
      left; eauto using use_code. left; eauto using use_code. destruct args'.
      right; eauto using use_code. right; eauto using use_code.
    - destruct FPC as [src' FPC]. rewrite FPC in *; ss. inv H5.
      apply Hds' in H1; destruct H1; clarify. destruct args'.
      left; eauto using use_code. left; eauto using use_code. destruct args'.
      right; eauto using use_code. right; eauto using use_code.
    - destruct H1. rewrite H0 in *. ss. inv H5.
      rewrite H3. apply Hds in H3; des;
      try (left; clarify; eauto using use_code; fail);
      try (right; clarify; eauto using use_code).
    - destruct H1 as [args' H1]. unfold option_map in H5.
      destruct args'; ss. rewrite H1 in H5. inv H5. rewrite H3.
      apply Hds in H3; destruct H3; clarify.
      left; eauto using use_code.
      right; eauto using use_code.
      rewrite H1 in H5; inv H5.
  Qed.

  Lemma use_s_elim_mv: forall f f' c p d s,
    wf_ssa_function f ->
    (fn_code f) = c ->
    (fn_phicode f) = p ->
    find_mv_code c = Some (d, s) \/ find_mv_phicode p = Some (d, s) ->
    f' = mkfunction
        (fn_sig f)
        (fn_params f)
        (fn_stacksize f)
        (elim_mv_code d s c)
        (elim_mv_phicode d s p)
        (fn_entrypoint f)
        (fn_ext_params f)
        (fn_dom_test f) ->
    d <> s ->
    forall pc, use f' s pc -> use f s pc \/ use f d pc.
  Proof.
    assert (Hds: forall d s x, rename_reg d s x = s -> x = s \/ x = d).
    { unfold rename_reg. i; flatten. flatten H. rewrite Pos.eqb_eq in Eq; clarify.
      right; auto. rewrite Pos.eqb_neq in Eq; clarify; left; auto. }
    assert (Hds': forall l d s, In s (map (rename_reg d s) l) ->
                                In s l \/ In d l).
    { induction l; ss. i. des. apply Hds in H; des; clarify; auto.
      apply IHl in H; eauto. des; eauto. }
    assert (Hbds: forall ba d s,
            In s (params_of_builtin_arg (rename_barg d s ba)) ->
            In s (params_of_builtin_arg ba) \/ In d (params_of_builtin_arg ba)).
    { induction ba; ss. i. des; eauto. apply Hds in H; des; clarify; eauto.
      i. apply in_app_iff in H; des.
      apply IHba1 in H; des; ss; repeat rewrite in_app_iff; eauto.
      apply IHba2 in H; des; ss; repeat rewrite in_app_iff; eauto.
      i. apply in_app_iff in H; des.
      apply IHba1 in H; des; ss; repeat rewrite in_app_iff; eauto.
      apply IHba2 in H; des; ss; repeat rewrite in_app_iff; eauto. }
    assert (Hbds': forall l d s,
            In s (params_of_builtin_args (map (rename_barg d s) l)) ->
            In s (params_of_builtin_args l) \/ In d (params_of_builtin_args l)).
    { induction l; ss. i. apply in_app_iff in H; des.
      - apply Hbds in H; des; eauto.
        left; apply in_app_iff; eauto. right; apply in_app_iff; eauto.
      - apply IHl in H; des.
        left; apply in_app_iff; eauto. right; apply in_app_iff; eauto. }
    assert (Hfds: forall f d s, rename_fn d s f = inl s ->
                                f = inl s \/ f = inl d).
    { i; destruct f; ss. inv H; eauto. apply Hds in H1; des; clarify; eauto.
      left; unfold rename_reg; flatten. }
    i; clarify; ss.
    inv H5.
    - eapply use_code_s_elim_mv in H0; eauto.
      des; try (left; econstructor; eauto; fail); right; econstructor; eauto.
    - remember (mkfunction
                (fn_sig f)
                (fn_params f)
                (fn_stacksize f)
                (elim_mv_code d s (fn_code f))
                (elim_mv_phicode d s (fn_phicode f))
                (fn_entrypoint f)
                (fn_ext_params f)
                (fn_dom_test f)) as f'.
      inv H0; ss. destruct (fn_phicode f) ! pc0 eqn:FPC0; ss.
      unfold elim_mv_phicode in PHIB; rewrite PTree.gmap in PHIB;
      rewrite FPC0 in PHIB; ss; inv PHIB.
      assert (Hpds: forall phib d s args dst,
                    In (Iphi args dst)
                    (map (subst_phi d s) (remove_mv_phiblock d phib)) ->
                    nth_error args k = Some s ->
                    exists args', In (Iphi args' dst) phib /\
                    (nth_error args' k = Some s \/ nth_error args' k = Some d)).
      { induction phib; ss; i. destruct a. flatten H0; ss.
        - rewrite Pos.eqb_eq in Eq; clarify. apply IHphib in H0; eauto.
          destruct H0; eauto. destruct H0 as [Hi [Hs | Hd]];
            exists x; split; eauto.
        - destruct H0.
          + inv H0.
            assert (forall l k, nth_error (map (rename_reg d0 s0) l) k = Some s0 ->
                    nth_error l k = Some s0 \/ nth_error l k = Some d0).
            { induction l0; ss; i. destruct k0; ss.
              destruct k0; ss. inv H0.
              apply Hds in H5; des; clarify; eauto;
                unfold rename_reg; flatten; auto.
              apply IHl0 in H0; des; eauto. }
            apply H0 in H1. destruct H1; exists l; eauto.
          + apply IHphib in H0; eauto. destruct H0; eauto.
            destruct H0 as [Hi [Hs | Hd]]; exists x; split; eauto. }
      eapply Hpds in ASSIG; eauto. destruct ASSIG as [args' [Hi [Hs | Hd]]].
      left; econstructor 2; econstructor; eauto.
      erewrite <- make_predecessors_elim_mv; eauto. ss. apply KPRED.
      right; econstructor 2; econstructor; eauto.
      erewrite <- make_predecessors_elim_mv; eauto. ss. apply KPRED.
      unfold elim_mv_phicode in PHIB; rewrite PTree.gmap in PHIB;
        rewrite FPC0 in *; ss; congruence.
  Qed.

  Lemma all_dom: forall f pc pc'' phib s d args,
    wf_ssa_function f ->
    (fn_phicode f) ! pc = Some phib ->
    In (Iphi (s :: args) d) phib ->
    (forall pc',
    In pc' (Kildall.successors_list
            (Kildall.make_predecessors (fn_code f) successors_instr) pc) ->
    dom f pc'' pc') ->
    dom f pc'' pc.
  Proof.
    i.
    assert (reached f pc).
    { apply fn_phicode_code in H0; auto. des. apply fn_code_reached in H0; auto. }
    econstructor; eauto. i.
    assert (exists pc',
            In pc' (Kildall.successors_list
                    (Kildall.make_predecessors (fn_code f) successors_instr) pc) /\
            In pc' p).
    { apply path_first in H4. des. clarify. inv H7. inv STEP. exists pc''0.
      split. eapply Kildall.make_predecessors_correct_1 in HCFG_ins; eauto.
      apply in_app_iff. right; auto.
      ii. eapply no_assigned_phi_spec_fn_entrypoint; eauto. econstructor; eauto.
      clarify. }
    des. apply H2 in H5. inv H5; auto.
    eapply Dom.in_path_split_app in H6; eauto; try apply Pos.eq_dec. des.
    apply PATH in H6. clarify. apply in_app_iff. left; auto.
  Qed.

  Lemma all_phi_dom: forall f pc phib s d args pc',
    wf_ssa_function f ->
    (fn_phicode f) ! pc = Some phib ->
    In (Iphi (s :: args) d) phib ->
    forallb (Pos.eqb s) args = true ->
    def f s pc' ->
    dom f pc' pc.
  Proof.
    i. assert (reached f pc).
    { apply fn_phicode_code in H0; auto. des. apply fn_code_reached in H0; auto. }
    eapply all_dom; eauto. i.
    assert (use f s pc'0).
    { econstructor 2.
      unfold Kildall.successors_list in H5.
      remember (Kildall.make_predecessors (fn_code f) successors_instr) ! pc.
      destruct o; ss.
      apply in_get_index_some in H5. des.
      econstructor; eauto.
      2:{ unfold index_pred. unfold Kildall.successors_list. rewrite <- Heqo.
          apply H5. }
      assert (index_pred (Kildall.make_predecessors (fn_code f) successors_instr)
              pc'0 pc = Some k).
      { unfold index_pred. unfold Kildall.successors_list. rewrite <- Heqo. auto. }
      apply index_pred_some in H6. inv H. unfold block_nb_args in fn_wf_block.
      eapply fn_wf_block in H0; eauto. rewrite H0 in H6.
      apply nth_error_Some in H6. destruct (nth_error (s :: args) k) eqn:NTH; ss.
      assert (forall l k r, forallb (Pos.eqb s) l = true ->
                            nth_error (s :: l) k = Some r ->
                            r = s).
      { induction l0; ss. i. destruct k0; ss. inv H7. auto.
        destruct k0; ss. i. destruct k0; ss. inv H7. auto.
        apply andb_prop in H. des. eapply IHl0 in H8; eauto.
        rewrite Pos.eqb_eq in H; clarify; apply H7. }
      apply H in NTH; eauto. clarify. }
    inv H; eauto.
  Qed.

  Lemma elim_mv_preserve_fn_strict: forall f f' c p d s,
    wf_ssa_function f ->
    (fn_code f) = c ->
    (fn_phicode f) = p ->
    find_mv_code c = Some (d, s) \/ find_mv_phicode p = Some (d, s) ->
    f' = mkfunction
    (fn_sig f)
    (fn_params f)
    (fn_stacksize f)
    (elim_mv_code d s c)
    (elim_mv_phicode d s p)
    (fn_entrypoint f)
    (fn_ext_params f)
    (fn_dom_test f) ->
    forall x u d, use f' x u -> def f' x d -> dom f' d u.
  Proof.
    i. rewrite <- dom_elim_mv; eauto.
    case_eq (d =? s)%positive; i.
    - rewrite Pos.eqb_eq in H6; clarify. des.
      apply find_mv_not_same in H2; congruence.
      apply no_phi_use_def in H2; destruct H2; auto.
    - case_eq (x =? d)%positive; i.
      + rewrite Pos.eqb_eq in H7; clarify. rewrite Pos.eqb_neq in H6.
        eapply use_reg_elim_mv in H4; eauto. inv H4.
      + case_eq (x =? s)%positive; i.
        * rewrite Pos.eqb_eq in H8; clarify.
          rewrite Pos.eqb_neq in H6; ss. clear H7.
          assert (def f s d0). { eapply def_s_elim_mv; eauto. }
          eapply use_s_elim_mv in H4; eauto. destruct H4 as [Hus | Hus].
          inv H; eauto.
          des.
          eapply find_mv_exists in H2; eauto. des.
          assert (def f d pc) by eauto using def.
          assert (use f s pc). { econstructor. econstructor; eauto. }
          eapply Dom.dom_trans. apply Pos.eq_dec.
          inv H. eapply fn_strict in H0; eauto.
          inv H. eapply fn_strict in H1; eauto.
          eapply find_mv_phicode_exists in H2; eauto. des.
          assert (def f d pc) by eauto.
          assert (dom f d0 pc).
          { eapply all_phi_dom; eauto. }
          inv H; eapply Dom.dom_trans; eauto.
          apply Pos.eq_dec. eapply fn_strict; eauto.
        * rewrite Pos.eqb_neq in H8, H7.
          eapply use_indep_elim_mv in H4; eauto.
          eapply def_indep_elim_mv in H5; eauto. inv H; eauto.
  Qed.

  Lemma elim_mv_preserve_wf_ssa_function: forall f f' c p d s,
    wf_ssa_function f ->
    (fn_code f) = c ->
    (fn_phicode f) = p ->
    find_mv_code c = Some (d, s) \/ find_mv_phicode p = Some (d, s) ->
    f' = mkfunction
        (fn_sig f)
        (fn_params f)
        (fn_stacksize f)
        (elim_mv_code d s c)
        (elim_mv_phicode d s p)
        (fn_entrypoint f)
        (fn_ext_params f)
        (fn_dom_test f) ->
    wf_ssa_function f'.
  Proof.
  i. constructor.
  - eapply elim_mv_preserve_unique_def_spec; eauto.
  - split.
    + ii. clarify. eapply assigned_code_spec_elim_mv in H5; eauto.
      inv H. apply fn_ssa_params in H4. apply H4 in H5. auto.
    + ii. clarify. eapply assigned_phi_spec_elim_mv in H5; eauto.
      inv H. apply fn_ssa_params in H4. apply H4 in H5. auto.
  - eapply elim_mv_preserve_fn_strict; eauto.
  - i. clarify. apply assigned_code_spec_elim_mv in H5; auto.
    destruct (classic (d = s)).
    + clarify. des. apply find_mv_not_same in H2; auto.
      destruct (classic (x = s)).
      * apply no_phi_use_def in H2; destruct H2; auto.
      * eapply use_code_indep_elim_mv in H4; eauto. inv H; eauto.
    + destruct (classic (x = d)).
      * clarify. eapply use_reg_elim_mv; eauto. econstructor; eauto.
      * destruct (classic (x = s)).
        clarify. eapply use_code_s_elim_mv in H4; eauto.
        destruct H4 as [Hs | Hd].
        inv H; eauto. des.
        { eapply find_mv_exists in H2. des.
          assert (def f d pc0) by eauto.
          assert (dom f pc0 pc).
          inv H. eapply fn_strict; eauto. econstructor; eauto.
          assert (use f s pc0). econstructor; eauto using use_code.
          assert (def f s pc) by eauto. assert (dom f pc pc0) by (inv H; eauto).
          apply Dom.dom_antisym in H8; eauto. clarify. inv H; eauto.
          apply Pos.eq_dec. }
        { eapply find_mv_phicode_exists in H2; eauto. des.
          assert (def f d pc0) by eauto.
          assert (dom f pc0 pc).
          inv H. eapply fn_strict; eauto. econstructor; eauto.
          assert (def f s pc) by eauto.
          eapply all_phi_dom in H8; eauto.
          apply Dom.dom_antisym in H8; eauto; try apply Pos.eq_dec. clarify.
          assert (join_point pc f). eapply assigned_phi_spec_join_point; eauto.
          inversion H8. destruct l; ss. lia.
          destruct (classic (p = pc)).
          - clarify. assert (exists ins, (fn_code f) ! pc = Some ins).
            { inv H5; eauto. }
            des. assert (NINOP: forall n, ins <> (Inop n)).
            { i. inv H5; rewrite H10 in H9; inv H9; eauto; ii; inv H5. }
            eapply ssa_not_Inop_not_phi in NINOP; eauto.
            eapply make_predecessors_correct2; eauto. unfold make_preds.
            unfold Kildall.successors_list. rewrite Hpreds. eauto.
          - assert (use_phicode f s p). econstructor; eauto.
            2:{ unfold index_pred. unfold Kildall.successors_list.
                rewrite Hpreds. unfold Utils.get_index. ss. flatten. auto. } ss.
            assert (use f s p). econstructor 2. eauto.
            assert (dom f pc p). inv H; eauto. eapply no_infinite_loop; eauto.
            inv H5; eapply wf_ssa_reached; eauto.
            i. assert (use_phicode f s pc').
            { eapply make_predecessors_some in H13 as Hs; eauto. des.
              edestruct index_pred_instr_some. apply Hs.
              eapply make_predecessors_correct2; eauto.
              econstructor; eauto. apply index_pred_some_nth in H14.
              inv H. unfold block_nb_args in fn_wf_block.
              eapply fn_wf_block in H2; eauto.
              eapply nth_error_some_same_length in H2; eauto. des.
              rewrite H2. apply nth_error_in in H2.
              rewrite forallb_forall in H4. inv H2; eauto.
              apply H4 in H. rewrite Pos.eqb_eq in H. clarify.
              unfold make_preds. unfold Kildall.successors_list.
              destruct (Kildall.make_predecessors _ _) ! pc eqn:KPC; ss.
              inv Hpreds. rewrite KPC. eauto. }
            assert (use f s pc'). econstructor 2; eauto.
            assert (def f s pc) by eauto. inv H; eauto. }
          eapply use_code_indep_elim_mv in H4; eauto. inv H; eauto.
  - unfold block_nb_args. i. erewrite make_predecessors_elim_mv; clarify. ss.
    unfold elim_mv_phicode in H4; rewrite PTree.gmap in H4.
    destruct (fn_phicode f) ! pc eqn:Efphi; ss. inv H4.
    assert (forall phib,
            In (Iphi args x) (map (subst_phi d s) (remove_mv_phiblock d phib)) ->
            exists args',
            In (Iphi args' x) phib /\ args = map (rename_reg d s) args').
    { induction phib; ss. destruct a; ss. flatten; i.
      - eapply IHphib in H0. des; eauto.
      - ss. destruct H0.
        + inv H0. exists l; eauto.
        + apply IHphib in H0. des; eauto. }
    apply H0 in H5. destruct H5 as [args' Hargs'].
    assert (forall l, Datatypes.length l = Datatypes.length (map (rename_reg d s) l)).
    { induction l; ss. rewrite IHl; eauto. }
    destruct Hargs'. clarify. rewrite <- H1 at 1.
    inv H. unfold block_nb_args in fn_wf_block.
    eapply fn_wf_block; eauto.
  - i. inv H. rewrite <- join_point_elim_mv in H4; eauto. ss.
    eapply fn_normalized in H4; eauto.
    + eapply elim_mv_code_spec in H4; eauto; des; eauto.
    + erewrite successors_list_elim_mv; eauto.
  - inv H. i. erewrite <- join_point_elim_mv; eauto. ss. split.
    + i. apply fn_phicode_inv in H.
      unfold elim_mv_phicode; rewrite PTree.gmap; destruct (fn_phicode f) ! jp; ss.
    + i. apply fn_phicode_inv.
      unfold elim_mv_phicode in H; rewrite PTree.gmap in H;
      destruct (fn_phicode f) ! jp eqn:Efjp; ss.
  - i.
    rewrite <- reached_elim_mv; eauto. clarify; ss.
    eelim elim_mv_code_spec'; eauto. destruct ins; i; des; eauto.
  - intros pc pc' instr Hi Hj.
    assert (cfg f pc pc')
    by (rewrite cfg_elim_mv; eauto; econstructor; eauto).
    inv H4.
    exploit fn_code_closed; eauto.
    intros [ii HH]; ss.
    eapply elim_mv_code_spec in HH; des; destruct ii; eauto;
    try destruct o; des; ss; eauto.
  - exploit fn_entry; eauto.
    intros [s' Hs].
    exists s'; erewrite fn_entrypoint_elim_mv; eauto.
    exploit (elim_mv_code_spec); eauto; ss. i. clarify. des; eauto.
  - clarify; intros pc; rewrite <- cfg_elim_mv; auto;
    erewrite fn_entrypoint_elim_mv; eauto; ss.
    apply fn_entry_pred; auto.
  - i. inv H4.
    + ss. inv H; eauto.
    + ss.
      destruct (classic (d = s)).
      * clarify. des. eapply find_mv_not_same in H2; congruence.
        apply no_phi_use_def in H2; destruct H2; eauto.
      * destruct H5 as [pc Hu].
        destruct (classic (r = d)).
        clarify. eapply use_reg_elim_mv in Hu; eauto. destruct Hu.
        destruct (classic (r = s)).
        clarify. assert (exists pc', use f s pc').
        { des. eapply find_mv_exists in H2. des.
          exists pc0; econstructor. eauto using use_code.
          eapply find_mv_phicode_exists in H2. des.
          assert (join_point pc0 f). inversion H. apply fn_phicode_inv.
          intros contra. rewrite contra in *; discriminate.
          inv H5. destruct l; ss; try lia. destruct l; ss; try lia.
          exists p. econstructor 2. econstructor; eauto.
          2:{ unfold index_pred. unfold Kildall.successors_list. rewrite Hpreds.
              unfold Utils.get_index. ss. flatten; eauto. } ss. }
        destruct H3 as [pc' Hus].
        inversion H. apply fn_ext_params_complete.
        econstructor 2; eauto.
        ii. eapply assigned_phi_spec_elim_mv' in H. eapply H6; eauto.
        eauto. eauto.
        ii. eapply assigned_code_spec_elim_mv' in H. eapply H7; eauto.
        eauto. eauto.
        eapply use_indep_elim_mv in Hu; eauto.
        inversion H. apply fn_ext_params_complete.
        econstructor 2; eauto.
        ii. eapply assigned_phi_spec_elim_mv' in H. eapply H6; eauto.
        eauto. eauto.
        ii. eapply assigned_code_spec_elim_mv' in H. eapply H7; eauto.
        eauto. eauto.
  - clarify; i; ss. erewrite <- dom_elim_mv; eauto; ss.
    eapply fn_dom_test_correct; eauto. eapply reached_elim_mv; eauto.
    Unshelve. eauto. eauto. eauto. eauto.
  Qed.

  Lemma simplify_mv_preserve_wf_ssa_function: forall fuel f f' c' p',
    wf_ssa_function f ->
    simplify_mv fuel (fn_code f) (fn_phicode f) = (c', p') ->
    f' = mkfunction
         f.(fn_sig)
         f.(fn_params)
         f.(fn_stacksize)
         c'
         p'
         f.(fn_entrypoint)
         f.(fn_ext_params)
         f.(fn_dom_test) ->
    wf_ssa_function f'.
  Proof.
  induction fuel; ss.
  - i. clarify. destruct f; eauto.
  - i. destruct (find_mv_code (fn_code f)) eqn:Efind.
  + destruct p.
  remember (mkfunction (fn_sig f)
  (fn_params f)
  (fn_stacksize f)
  (elim_mv_code r r0 (fn_code f))
  (elim_mv_phicode r r0 (fn_phicode f))
  (fn_entrypoint f)
  (fn_ext_params f)
  (fn_dom_test f)) as f0.
  eapply elim_mv_preserve_wf_ssa_function in Heqf0 as Hf0wf; eauto.
  eapply IHfuel; eauto. subst; ss. apply H0. subst; ss.
  + destruct (find_mv_phicode (fn_phicode f)) eqn:Ephifind.
  * destruct p.
  remember (mkfunction (fn_sig f)
  (fn_params f)
  (fn_stacksize f)
  (elim_mv_code r r0 (fn_code f))
  (elim_mv_phicode r r0 (fn_phicode f))
  (fn_entrypoint f)
  (fn_ext_params f)
  (fn_dom_test f)) as f0.
  eapply elim_mv_preserve_wf_ssa_function in Heqf0 as Hf0wf; eauto.
  eapply IHfuel; eauto. subst; ss. apply H0. subst; ss.
  * clarify; eauto. destruct f; eauto.
  Qed.

  Lemma transf_function_preserve_wf_ssa_function : forall (f:function),
  wf_ssa_function f -> wf_ssa_function (transf_function f).
  Proof.
  unfold transf_function. i. unfold transf_function_fuel.
  destruct (simplify_mv _ _ _) eqn:Esim.
  eapply simplify_mv_preserve_wf_ssa_function; eauto.
  Qed.

End PRESERVATION.

Section CORRECTNESS_STEP.

  Definition match_prog_step (p: SSA.program) (tp: SSA.program) :=
    match_program (fun cu f tf => tf = transf_fundef_step f) eq p tp.

  Lemma transf_program_step_match:
   forall p, match_prog_step p (transf_program_step p).
  Proof.
   intros; subst.
   eapply match_transform_program_contextual; auto.
  Qed.

  Variable prog: program.
  Variable tprog: program.
  Hypothesis TRANSL : match_prog_step prog tprog.
  Hypothesis HWF : wf_ssa_program prog.

  Fixpoint repeatn {A} (f: A -> A) (n: nat) a :=
    match n with
    | 0 => a
    | S n' => f (repeatn f n' a)
    end.

  Lemma repeatn_distributive: forall A (f: A -> A) n m a,
    repeatn f (m + n) a = repeatn f m (repeatn f n a).
  Proof.
    induction m; ss. i. rewrite IHm. eauto.
  Qed.
  
  Lemma fold_find_mv_instr_xelements: forall c p1 p2 o,
    fold_left (fun a (p: positive * instruction) => find_mv_instr a (fst p) (snd p))
    (PTree.xelements c p1 nil) o =
    fold_left (fun a (p: positive * instruction) => find_mv_instr a (fst p) (snd p))
    (PTree.xelements c p2 nil) o.
  Proof.
    induction c.
    - ss.
    - i. destruct o0.
      + destruct p. rewrite 2 PTree.xelements_node. destruct o; s.
        * rewrite 2 fold_left_app. erewrite IHc1; eauto. ss.
          erewrite (IHc2 c2 _ _ p1~1%positive). eauto.
        * rewrite 2 fold_left_app.
          erewrite (IHc1 c1 _ _ p1~0%positive); eauto.
      + rewrite 2 PTree.xelements_node. destruct o; s.
        * rewrite 2 fold_left_app. erewrite IHc1; eauto. ss.
          erewrite (IHc2 c2 _ _ p1~1%positive). eauto.
        * rewrite 2 fold_left_app.
          erewrite (IHc1 c1 _ _ p1~0%positive); eauto.
    Unshelve. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto. eauto.
  Qed.

  Lemma find_mv_code_spec: forall c1 o c2,
    find_mv_code (PTree.Node c1 o c2) =
      let findc1 := find_mv_code c1 in
      match findc1 with
      | Some (d, s) => Some (d, s)
      | None => match o with
                | Some ins => match ins with
                              | Iop Omove (src :: nil) dst _ => Some (dst, src)
                              | _ => find_mv_code c2
                              end
                | None => find_mv_code c2
                end
      end.
  Proof.
    assert (forall l d s,
            fold_left (fun a p => find_mv_instr a (fst p) (snd p)) l (Some (d, s))
              = Some (d, s)).
    { induction l; ss. }
    i. destruct (find_mv_code c1) eqn:FINDC1.
    - ss. destruct p. unfold find_mv_code in *. rewrite PTree.fold_spec in *.
      unfold PTree.elements in *. rewrite PTree.xelements_node.
      destruct o.
      + ss. rewrite fold_left_app. erewrite fold_find_mv_instr_xelements.
        rewrite FINDC1. ss.
      + ss. rewrite fold_left_app. erewrite (fold_find_mv_instr_xelements c1).
        rewrite FINDC1. ss.
    - ss. unfold find_mv_code in *. repeat rewrite PTree.fold_spec in *.
      unfold PTree.elements in *. rewrite PTree.xelements_node. destruct o; ss.
      + rewrite fold_left_app; s. erewrite (fold_find_mv_instr_xelements c1).
        rewrite FINDC1. ss. destruct i; ss; try eapply fold_find_mv_instr_xelements.
        destruct o; ss; try eapply fold_find_mv_instr_xelements.
        destruct l; ss; try eapply fold_find_mv_instr_xelements.
        destruct l; ss; try eapply fold_find_mv_instr_xelements.
      + rewrite fold_left_app; s. erewrite (fold_find_mv_instr_xelements c1).
        rewrite FINDC1. eapply fold_find_mv_instr_xelements.
  Qed.

  Lemma transf_function_fuel_repeatn: forall f n,
    transf_function_fuel n f = repeatn (transf_function_fuel 1) n f.
  Proof.
    i. induction n.
    - destruct f; ss.
    - ss. rewrite <- IHn. unfold transf_function_fuel.
      destruct (simplify_mv n (fn_code f) (fn_phicode f)) eqn:ESIMPLN.
      assert (forall f n,
              simplify_mv (S n) (fn_code f) (fn_phicode f) =
              let (cn, pn) := simplify_mv n (fn_code f) (fn_phicode f) in
              simplify_mv 1 cn pn).
      { i. revert f0. induction n0.
        - i; ss.
        - i. s.
          destruct (find_mv_code (fn_code f0)) eqn:EFINDC.
          + destruct p0.
            specialize (IHn0 (mkfunction
                              (fn_sig f0)
                              (fn_params f0)
                              (fn_stacksize f0)
                              (elim_mv_code r r0 (fn_code f0))
                              (elim_mv_phicode r r0 (fn_phicode f0))
                              (fn_entrypoint f0)
                              (fn_ext_params f0)
                              (fn_dom_test f0))). ss.
          + destruct (find_mv_phicode (fn_phicode f0)) eqn:EFINDP.
            destruct p0. specialize (IHn0 (mkfunction
                                    (fn_sig f0)
                                    (fn_params f0)
                                    (fn_stacksize f0)
                                    (elim_mv_code r r0 (fn_code f0))
                                    (elim_mv_phicode r r0 (fn_phicode f0))
                                    (fn_entrypoint f0)
                                    (fn_ext_params f0)
                                    (fn_dom_test f0))). ss.
            rewrite EFINDC, EFINDP. ss. }
      rewrite H. s. rewrite ESIMPLN. ss.
  Qed.

  Lemma transf_function_fuel_commute: forall m n f,
    transf_function_fuel n (transf_function_fuel m f) =
      transf_function_fuel m (transf_function_fuel n f).
  Proof.
    induction n; ss.
    - i. unfold transf_function_fuel. ss. destruct (simplify_mv m _ _). ss.
    - i. rewrite transf_function_fuel_repeatn. ss.
      rewrite <- transf_function_fuel_repeatn. rewrite IHn.
      rewrite (transf_function_fuel_repeatn _ (S n)). ss.
      rewrite <- transf_function_fuel_repeatn.
      assert (forall o f, transf_function_fuel 1 (transf_function_fuel o f)
                          = transf_function_fuel o (transf_function_fuel 1 f)).
      { induction o; ss. i. unfold transf_function_fuel; flatten; ss. clarify.
        flatten Eq; flatten Eq2; ss. i.
        rewrite (transf_function_fuel_repeatn _ (S o)). ss.
        rewrite <- transf_function_fuel_repeatn.
        rewrite (transf_function_fuel_repeatn _ (S o)). ss.
        rewrite <- transf_function_fuel_repeatn. rewrite IHo; ss. }
      rewrite H. auto.
  Qed.

  Definition count_mv_instrs (n: nat) (pc: positive) ins : nat :=
    match ins with
    | Iop Omove (src :: nil) dst _ => S n
    | _ => n
    end.

  Definition num_mv_instrs (c: code) :=
    PTree.fold count_mv_instrs c 0.
  
  Lemma fold_left_accumulator: forall l n,
    fold_left (fun a p => count_mv_instrs a (fst p) (snd p)) l n 
    = fold_left (fun a p => count_mv_instrs a (fst p) (snd p)) l 0 + n.
  Proof.
    induction l; ss. destruct a. ss.
    unfold count_mv_instrs at 2; ss. unfold count_mv_instrs at 3; ss.
    destruct i; ss. destruct o; ss. destruct l0; ss. destruct l0; ss.
    i. rewrite IHl. rewrite (IHl 1). lia.
  Qed.

  Lemma num_mv_instrs_bounded: forall c,
    num_mv_instrs c < PTree.fold (fun m _ _ => 1 + m) c 1.
  Proof.
    assert (forall l n, fold_left (fun a (_: positive * instruction) => S a) l (S n)
                        = fold_left (fun a (_: positive * instruction) => S a) l 1 + n).
    { induction l; ss. rewrite IHl. i. rewrite (IHl (S n)). lia. }
    i. unfold num_mv_instrs. rewrite 2 PTree.fold_spec.
    generalize (PTree.elements c).
    induction l; ss. rewrite H. destruct a. destruct i; ss; try lia.
    destruct o; try lia. destruct l0; try lia. destruct l0; try lia.
    rewrite fold_left_accumulator. lia.
  Qed.

  Lemma elim_mv_code_none: forall c d s,
    find_mv_code c = None ->
    find_mv_code (elim_mv_code d s c) = None.
  Proof.
    unfold find_mv_code. i. rewrite PTree.fold_spec in *.
    destruct (fold_left _ (PTree.elements (elim_mv_code d s c)) None)
      eqn:FOLD; auto. destruct p.
    apply fold_find_mv_instr_some in FOLD. des.
    apply PTree.elements_complete in FOLD. unfold elim_mv_code in FOLD.
    rewrite PTree.gmap in FOLD. destruct (c ! pc) eqn:CPC; ss.
    inv FOLD. destruct i; ss. destruct o; ss. flatten H2; ss. inv H1.
    destruct l; ss. inv H2. destruct l; ss. clear H3.
    apply PTree.elements_correct in CPC.
    eapply fold_find_mv_instr_none in H. apply H in CPC. destruct CPC.
  Qed.

  Lemma num_mv_instrs_correct: forall c, num_mv_instrs c = 0 <-> find_mv_code c = None.
  Proof.
    induction c; ss. split.
    - unfold num_mv_instrs, find_mv_code. rewrite 2 PTree.fold_spec.
      generalize (PTree.elements (PTree.Node c1 o c2)). induction l; ss.
      destruct a. destruct i; ss. destruct o0; ss. destruct l0; ss.
      destruct l0; ss. i. rewrite fold_left_accumulator in H. lia.
    - unfold num_mv_instrs, find_mv_code. rewrite 2 PTree.fold_spec.
      generalize (PTree.elements (PTree.Node c1 o c2)). induction l; ss.
      destruct a. destruct i; ss. destruct o0; ss. destruct l0; ss.
      destruct l0; ss. i.
      assert (forall l d s,
              fold_left (fun a p => find_mv_instr a (fst p) (snd p)) l (Some (d, s))
              = Some (d, s)).
      { induction l0; ss. }
      rewrite H0 in H. inv H.
  Qed.

  Lemma xelements_comm: forall A (m: PTree.t A) i k,
    PTree.xelements m i k = PTree.xelements m i nil ++ k.
  Proof.
    induction m; ss. destruct o; ss. i. rewrite IHm1. rewrite (IHm1 _ (_ :: _)).
    rewrite <- List.app_assoc. rewrite (IHm2 _ k). rewrite List.app_comm_cons. ss.
    i. rewrite IHm2. rewrite PTree.xelements_append. ss.
  Qed.

  Lemma num_mv_instrs_dec: forall c f,
    c = fn_code f ->
    match (num_mv_instrs c) with
    | 0 => num_mv_instrs (fn_code (transf_function_fuel 1 f)) = 0
    | S n => num_mv_instrs (fn_code (transf_function_fuel 1 f)) <= n
    end.
  Proof.
    i. flatten.
    - unfold transf_function_fuel, simplify_mv. pose proof num_mv_instrs_correct as H0.
      edestruct H0 as [H1 H2]. rewrite H1; ss.
      destruct (find_mv_phicode (fn_phicode f)).
      + destruct p; ss. rewrite H0. apply elim_mv_code_none. apply H1. clarify.
      + ss. clarify.
      + clarify.
    - unfold transf_function_fuel. unfold simplify_mv.
      destruct (find_mv_code (fn_code f)) eqn:FIND.
      + destruct p; ss. apply find_mv_exists in FIND. des. rewrite <- H in *.
        unfold num_mv_instrs. rewrite PTree.fold_spec.
        unfold elim_mv_code. unfold PTree.map.
        assert (forall c d s p p' p'' n,
                let f := (fun (p: positive) ins =>
                subst_instr d s (remove_mv_instr d ins)) in
                let f' := (fun (pi : positive * instruction) =>
                ((fst pi), subst_instr d s (remove_mv_instr d (snd pi)))) in
                let f'' := (fun a p => count_mv_instrs a (fst p) (snd p)) in
                fold_left f'' ((PTree.xelements (PTree.xmap f c p) p' nil)) n
                  = fold_left f'' (List.map f' (PTree.xelements c p'' nil)) n).
        { induction c0. ss. destruct o; ss.
          - i. rewrite xelements_comm. rewrite fold_left_app.
            rewrite IHc0_1 with (p'' := p''~0%positive); eauto.
            rewrite (xelements_comm _ c0_1 p''~0%positive ((_ :: _))).
            rewrite list_append_map. ss. rewrite fold_left_app.
            rewrite IHc0_2 with (p'' := p''~1%positive); eauto.
          - i. rewrite xelements_comm. rewrite fold_left_app.
            erewrite (IHc0_1 c0_1); eauto. erewrite (IHc0_2 c0_2); eauto.
            rewrite (xelements_comm _ c0_1 p''~0%positive (PTree.xelements _ _ nil)).
            rewrite list_append_map. rewrite fold_left_app. ss. }
        unfold PTree.elements. erewrite H0. eapply PTree.xelements_correct in FIND.
        apply in_split in FIND. des. rewrite FIND. rewrite map_app. ss.
        flatten; ss. 2: { rewrite Pos.eqb_neq in Eq0; ss. }
        rewrite fold_left_app. ss. unfold num_mv_instrs in Eq.
        rewrite PTree.fold_spec in Eq. unfold PTree.elements in Eq. rewrite FIND in Eq.
        rewrite fold_left_app in Eq. ss.
        remember (fold_left _ l1 0) as l1c. rewrite fold_left_accumulator in Eq.
        rewrite fold_left_accumulator.
        assert (forall l2,
                let f := (fun a p => count_mv_instrs a (fst p) (snd p)) in
                let f' :=
                  (fun (pi: positive * instruction) =>
                    (fst pi, subst_instr r r0 (remove_mv_instr r (snd pi)))) in
                fold_left f (map f' l2) 0 <= fold_left f l2 0).
        { induction l0; ss. rewrite fold_left_accumulator.
          destruct a; s. destruct i; ss; try lia. destruct o; ss; try lia.
          flatten; ss; try lia. rewrite (fold_left_accumulator _ 1). lia.
          rewrite (fold_left_accumulator _ 1). lia. }
        ss. specialize (H1 l1) as Hl1. specialize (H1 l2) as Hl2. lia.
      + apply num_mv_instrs_correct in FIND. clarify. lia.
  Qed.

  Lemma find_elim_mv_code: forall c d s, find_mv_code c = None ->
    find_mv_code (elim_mv_code d s c) = None.
  Proof.
    unfold find_mv_code. i. rewrite PTree.fold_spec in *.
    destruct (fold_left _ (PTree.elements (elim_mv_code d s c)) None)
      eqn:FOLD; auto. destruct p.
    apply fold_find_mv_instr_some in FOLD. des.
    apply PTree.elements_complete in FOLD. unfold elim_mv_code in FOLD.
    rewrite PTree.gmap in FOLD. destruct (c ! pc) eqn:CPC; ss.
    inv FOLD. destruct i; ss. destruct o; ss. flatten H2; ss.
    inv H1. destruct l; ss. inv H2. destruct l; ss. clear H3.
    apply PTree.elements_correct in CPC.
    eapply fold_find_mv_instr_none in H. apply H in CPC. destruct CPC.
  Qed.

  Lemma find_transf_function_fuel_repeatn: forall f n,
    find_mv_code (fn_code f) = None ->
    find_mv_code (fn_code (transf_function_fuel n f)) = None.
  Proof.
    intros f n; revert f; induction n; ss.
    i. rewrite transf_function_fuel_repeatn. ss.
    rewrite <- transf_function_fuel_repeatn. unfold transf_function_fuel at 1.
    flatten. unfold simplify_mv in Eq. flatten Eq.
    - rewrite IHn in Eq0; eauto. discriminate.
    - ss. apply find_elim_mv_code. eauto.
    - ss.
  Qed.

  Lemma transf_function_fuel_code_idempotent: forall f n,
    (PTree.fold (fun m _ _ => 1+m) f.(fn_code) 1%nat) <= n ->
    find_mv_code (fn_code (transf_function_fuel n f)) = None.
  Proof.
    i. assert (num_mv_instrs (fn_code f) <= n).
    { pose proof num_mv_instrs_bounded. specialize (H0 (fn_code f)). lia. }
    clear H. revert f H0. induction n; ss. i. inv H0.
    apply num_mv_instrs_correct; ss. i. inv H0.
    - rewrite H1. rewrite transf_function_fuel_repeatn. ss.
      rewrite <- transf_function_fuel_repeatn.
      rewrite transf_function_fuel_commute. apply IHn.
      pose proof num_mv_instrs_dec. specialize (H (fn_code f) f).
      rewrite H1 in H. auto.
    - rewrite transf_function_fuel_repeatn. ss.
      rewrite <- transf_function_fuel_repeatn.
      unfold transf_function_fuel at 1. unfold simplify_mv. flatten.
      flatten Eq; ss. apply find_elim_mv_code; auto. apply find_elim_mv_code; auto.
  Qed.

  Definition phisize (p: phicode) :=
    PTree.fold (fun m _ (blk: phiblock) => Datatypes.length blk + m) p 0.
  
  Lemma fold_left_accumulator_phi: forall l n,
    let f := (fun a (p: positive * phiblock) => Datatypes.length (snd p) + a) in
    fold_left f l n = fold_left f l 0 + n.
  Proof.
    induction l; ss. destruct a; ss. i. rewrite IHl.
    rewrite (IHl (Datatypes.length p0 + 0)). lia.
  Qed.

  Lemma phisize_0: forall p,
    phisize p = 0 -> find_mv_phicode p = None.
  Proof.
    unfold find_mv_phicode, phisize. i. rewrite PTree.fold_spec in *. revert H.
    generalize (PTree.elements p). induction l; ss. destruct a; ss. i.
    rewrite fold_left_accumulator_phi in H. destruct (Datatypes.length p1) eqn:LP1; ss.
    - destruct p1; ss. apply IHl. lia.
    - lia.
  Qed.

  Lemma find_mv_phicode_repeatn: forall f n,
    find_mv_code (fn_code f) = None ->
    find_mv_phicode (fn_phicode f) = None ->
    transf_function_fuel n f = f.
  Proof.
    induction n; ss.
    - i. unfold transf_function_fuel. ss. destruct f; ss.
    - i. rewrite transf_function_fuel_repeatn. ss.
      rewrite <- transf_function_fuel_repeatn. rewrite IHn; ss.
      unfold transf_function_fuel. ss. rewrite H, H0. destruct f; ss.
  Qed.

  Lemma phisize_spec: forall (p: phicode),
    phisize p =
    match p with
    | (PTree.Node p1 o p2) => match o with
                              | Some l => Datatypes.length l + phisize p1 + phisize p2
                              | None => phisize p1 + phisize p2
                              end
    | PTree.Leaf => 0
    end.
  Proof.
    induction p; ss.
    remember (fun m (p: positive) (blk: phiblock) => Datatypes.length blk + m) as f.
    assert (forall m pos l, f m pos l = f 0 pos l + m).
    { induction l; ss. clarify; ss. clarify; ss. rewrite IHl; lia. }
    assert (forall p pos n, PTree.xfold f pos p n = PTree.xfold f pos p 0 + n).
    { induction p; ss. destruct o0; ss. i. rewrite (IHp3 p3); eauto.
      rewrite IHp4; eauto. erewrite (IHp4 p4 _ _ _ (f _ _ _)).
      rewrite H. rewrite (H (PTree.xfold _ _ _ _)). rewrite 2 Nat.add_assoc.
      apply f_equal2_plus; ss. rewrite Nat.add_assoc. apply f_equal2_plus; ss.
      i. erewrite IHp4; eauto. erewrite (IHp4 p4 _ _ _ (PTree.xfold _ _ _ _)).
      rewrite <- Nat.add_assoc. apply f_equal2_plus; ss. eauto. }
    assert (forall pos p, PTree.xfold f pos p 0 = phisize p).
    { intros pos p0; revert pos; induction p0; ss. unfold phisize. unfold PTree.fold.
      ss. destruct o0; ss.
      - i. rewrite H0. rewrite <- Heqf. rewrite H. rewrite IHp0_2; ss.
        rewrite IHp0_1; ss. rewrite H0. rewrite IHp0_2; ss. rewrite H0.
        rewrite IHp0_1; ss. clarify; ss. lia.
      - i. rewrite H0. rewrite <- Heqf. rewrite IHp0_2; ss.
        rewrite IHp0_1; ss. rewrite H0. rewrite IHp0_2; ss.
        rewrite IHp0_1; ss. }
    destruct o; ss.
    - unfold phisize at 1. unfold PTree.fold. ss. clarify.
      rewrite H0. rewrite H1. rewrite H0. rewrite H1. lia.
    - unfold phisize at 1. unfold PTree.fold. ss. clarify.
      rewrite H0. rewrite H1. rewrite H0. rewrite H1. lia.
  Unshelve. auto. auto. auto. auto.  
  Qed.

  Lemma phisize_list: forall p,
    phisize p = fold_left (fun acc elem => acc + Datatypes.length (snd elem))
                          (PTree.elements p) 0.
  Proof.
    unfold phisize. i. rewrite PTree.fold_spec.
    generalize (PTree.elements p); ss. induction l; ss.
    destruct a; ss.
    remember (fun a (p2: positive * phiblock) => Datatypes.length (snd p2) + a) as f.
    remember (fun acc elem => acc + Datatypes.length (snd elem)) as f'.
    enough (forall l n, fold_left f l n = fold_left f l 0 + n).
    enough (forall l n, fold_left f' l n = fold_left f' l 0 + n).
    rewrite H. rewrite (H0 l (Datatypes.length p1)). lia.
    induction l0; ss. i. rewrite IHl0. rewrite (IHl0 (f' 0 a)).
    destruct a; ss. clarify. ss. lia.
    induction l0; ss. i. rewrite (IHl0 (f n a)). rewrite (IHl0 (f 0 a)).
    destruct a; ss. clarify; ss. lia.
  Qed.

  Lemma phisize_elim_mv_phicode: forall d s p,
    phisize (elim_mv_phicode d s p) =
      fold_left (fun acc elem => acc + Datatypes.length elem)
                (map (fun elem => map (subst_phi d s) (remove_mv_phiblock d (snd elem)))
                     (PTree.elements p)) 0.
  Proof.
    unfold elim_mv_phicode. i. unfold phisize. rewrite PTree.fold_spec.
    remember (fun a (p0: positive * phiblock) => Datatypes.length (snd p0) + a) as f.
    remember (fun _ blk => map (subst_phi d s) (remove_mv_phiblock d blk)) as f'.
    remember (fun acc elem => acc + Datatypes.length elem) as f''.
    remember (fun elem => map (subst_phi d s) (remove_mv_phiblock d (snd elem))) as f'''.
    unfold PTree.elements. generalize 1%positive at 1. generalize 1%positive.
    unfold PTree.map. generalize 1%positive. generalize p.
    induction p0. ss.
    assert (forall l n, fold_left f l n = fold_left f l 0 + n).
    { induction l; ss. i. rewrite IHl. rewrite (IHl (f 0 a)). destruct a; ss.
      clarify; ss. lia. }
    assert (forall l n, fold_left f'' l n = fold_left f'' l 0 + n).
    { induction l; ss. i. rewrite IHl. rewrite (IHl (f'' 0 a)). destruct a; ss.
      clarify; ss. lia. clarify; ss. lia. }
    i. rewrite PTree.xelements_node. s. destruct o; ss.
    - rewrite map_app. rewrite fold_left_app.
      rewrite xelements_comm. rewrite fold_left_app. rewrite H. rewrite H0. ss.
      rewrite H. rewrite H0. rewrite (IHp0_2 _ p1~1%positive).
      rewrite (IHp0_1 _ p1~0%positive). clarify; ss. lia.
    - rewrite map_app. rewrite fold_left_app.
      rewrite xelements_comm. rewrite fold_left_app. rewrite H. rewrite H0. ss.
      rewrite (IHp0_2 _ p1~1%positive).
      rewrite (IHp0_1 _ p1~0%positive). clarify; ss.
  Qed.
  
  Lemma phisize_dec: forall c p p' f,
    c = fn_code f ->
    p = fn_phicode f ->
    p' = fn_phicode (transf_function_fuel 1 f) ->
    match (find_mv_code c) with
    | Some (d, s) => phisize p' <= phisize p
    | None => match (find_mv_phicode p) with
              | Some (d, s) => phisize p' < phisize p
              | None => phisize p = phisize p'
              end
    end.
  Proof.
    remember (fun acc (elem: list phiinstruction)
              => acc + Datatypes.length elem) as f'.
    remember (fun acc (elem: positive * list phiinstruction)
              => acc + Datatypes.length (snd elem)) as f''.
    assert (forall l n, fold_left f' l n = fold_left f' l 0 + n).
    { induction l; ss. i. clarify. rewrite IHl. rewrite (IHl (0 + _)). lia. }
    assert (forall l n, fold_left f'' l n = fold_left f'' l 0 + n).
    { induction l; ss. i. clarify. rewrite IHl. rewrite (IHl (0 + _)). lia. }
    i. unfold transf_function_fuel in H3. ss. clarify. flatten.
    - ss. rewrite phisize_elim_mv_phicode. rewrite phisize_list.
      generalize (PTree.elements (fn_phicode f)).
      induction l; ss. clarify.
      rewrite H. rewrite H0. destruct a; ss. clarify. ss.
      assert (forall pb,
              Datatypes.length (map (subst_phi r r0) (remove_mv_phiblock r pb))
              <= Datatypes.length pb).
      { induction pb; ss. destruct a; ss. flatten; ss; try lia. }
      specialize (H1 p0). lia.
    - ss. rewrite phisize_elim_mv_phicode. rewrite phisize_list.
      unfold find_mv_phicode in Eq0. rewrite PTree.fold_spec in Eq0.
      remember (PTree.elements (fn_phicode f)). clear Heql. revert Eq0.
      induction l; ss. i. destruct a; ss.
      destruct (find_mv_phiblock p1) eqn:FINDP1.
      + destruct p2; ss.
        remember (fun acc elem => acc + Datatypes.length elem) as f'.
        remember (fun acc elem => acc + Datatypes.length (snd elem)) as f''.
        remember (fun elem => map (subst_phi _ _) (remove_mv_phiblock _ _)) as fr.
        assert (forall l, fold_left f' (map fr l) 0 <= fold_left f'' l 0).
        { induction l0; ss. destruct a; ss. rewrite H. rewrite H0.
          enough (f' 0 (fr (p2, p3)) <= f'' 0 (p2, p3)). lia.
          clarify; ss. generalize p3. induction p4; ss. flatten; ss. lia. lia. }
        rewrite H. rewrite H0.
        enough (Datatypes.length (map (subst_phi r r0) (remove_mv_phiblock r p1))
                < Datatypes.length p1). specialize (H1 l); lia.
        remember (fun a p => _find_mv_phiblock a _ _) as ffind.
        assert (forall l, fold_left ffind l (Some (r1, r2)) = Some (r, r0) ->
                (r1, r2) = (r, r0)).
        { induction l0; ss. i. clarify; ss. destruct a; ss. clarify. }
        apply H2 in Eq0; ss. clear H2. clarify.
        revert FINDP1. generalize p1. induction p2; ss. destruct a; ss.
        destruct l0; ss.
        * flatten. i. apply IHp2 in FINDP1. lia. ss. i.
          apply IHp2 in FINDP1. lia.
        * flatten. i. clarify. generalize p2. induction p3; ss. flatten; ss. lia.
          lia. i. clarify. rewrite Pos.eqb_neq in Eq1. exfalso; apply Eq1; ss.
          i. apply IHp2 in FINDP1; ss. lia.
          i. ss. apply IHp2 in FINDP1. lia.
      + apply IHl in Eq0. rewrite H. rewrite (H0 l).
        enough (Datatypes.length (map (subst_phi r r0) (remove_mv_phiblock r p1))
                <= Datatypes.length p1). lia.
        generalize p1. induction p2; ss. flatten; ss. lia. lia.
    - ss.
  Qed.

  Lemma phisize_dec': forall c p p' f n m d s d' s',
    c = fn_code f ->
    p = fn_phicode f ->
    phisize p = n + m ->
    find_mv_code (fn_code f) = None ->
    find_mv_phicode (fn_phicode f) = Some (d, s) ->
    p' = fn_phicode (transf_function_fuel m f) ->
    find_mv_phicode p' = Some (d', s') ->
    phisize p' <= n.
  Proof.
    intros c p p' f n m; revert c p p' f n; induction m; ss.
    - i. clarify. lia.
    - i. rewrite transf_function_fuel_repeatn in H4. ss.
      rewrite <- transf_function_fuel_repeatn in H4.
      pose proof phisize_dec as DEC. eapply DEC in H4 as DEC'; eauto.
      rewrite find_transf_function_fuel_repeatn in DEC'; eauto. flatten DEC'.
      + assert (phisize (fn_phicode (transf_function_fuel m f)) <= S n).
        { replace (n + S m) with (S n + m) in H1 by lia. eapply IHm in H1; eauto. }
        lia.
      + unfold transf_function_fuel at 1 in H4. unfold simplify_mv in H4.
        rewrite find_transf_function_fuel_repeatn in H4; ss. rewrite Eq in H4.
        ss. clarify.
  Qed.

  Lemma strong_ind: forall (P: nat -> Prop),
                    (forall m, (forall k, k < m -> P k) -> P m) -> 
                    forall n, P n.
  Proof.
    i. enough (H0: forall p, p <= n -> P p). apply H0. lia.
    induction n; ss. i. inv H0. apply H; try lia. i. inv H0.
    apply H. i. apply IHn; lia. apply IHn; lia.
  Qed.

  Lemma transf_function_fuel_phicode_idempotent: forall f m,
    find_mv_code (fn_code f) = None ->
    phisize (fn_phicode f) <= m ->
    find_mv_phicode (fn_phicode (transf_function_fuel m f)) = None.
  Proof.
    intros f. remember (phisize (fn_phicode f)).
    assert (phisize (fn_phicode f) <= n) by lia. clear Heqn.
    revert f H. induction n; ss.
    - i. inv H. apply phisize_0 in H3.
      rewrite find_mv_phicode_repeatn; ss.
    - i. destruct (find_mv_phicode (fn_phicode f)) eqn:FINDPF.
      + destruct p; ss. destruct m; try lia. assert (n <= m) by lia.
        rewrite transf_function_fuel_repeatn. ss.
        rewrite <- transf_function_fuel_repeatn. rewrite transf_function_fuel_commute.
        unfold transf_function_fuel at 2. ss. rewrite H0, FINDPF.
        remember (mkfunction _ _ _ _ _ _ _ _) as f'. eapply IHn; eauto.
        enough (phisize (fn_phicode f') < phisize (fn_phicode f)). lia.
        pose proof (phisize_dec).
        specialize (H3 (fn_code f) (fn_phicode f) (fn_phicode f') f).
        rewrite H0, FINDPF in H3. apply H3; auto. unfold transf_function_fuel.
        ss. rewrite H0, FINDPF. clarify. clarify. apply find_elim_mv_code. auto.
      + rewrite find_mv_phicode_repeatn; auto.
  Qed.

  Lemma transf_function_commute: forall f fuel,
    code_size f <= fuel ->
    transf_function f = repeatn (transf_function_fuel 1) fuel f.
  Proof.
    i. revert f H. induction fuel.
    - i. ss. unfold transf_function. inv H. rewrite H1.
      unfold transf_function_fuel. ss. destruct f; ss.
    - i. inv H.
      + unfold transf_function.
        apply transf_function_fuel_repeatn.
      + ss. rewrite <- IHfuel; auto.
        assert (forall f, find_mv_code (fn_code (transf_function f)) = None).
        { unfold transf_function. i. eapply transf_function_fuel_code_idempotent.
          unfold code_size. repeat rewrite PTree.fold_spec.
          assert (forall (l: list (positive * list phiinstruction)) n,
                  n <= fold_left (fun a p => Datatypes.length (snd p) + a) l n).
          { induction l; ss. destruct a. ss. i.
            specialize (IHl (Datatypes.length l0 + n)). lia. }
          apply H. }
        assert (forall f, find_mv_phicode (fn_phicode (transf_function f)) = None).
        { i. unfold transf_function. unfold code_size.
          assert (COMM: forall p n,
                        let f := (fun m (p: positive) (blk: list phiinstruction) =>
                                    Datatypes.length blk + m) in
                        (PTree.fold f p n) = (PTree.fold f p 0) + n).
          { ss. i. rewrite 2 PTree.fold_spec. unfold PTree.elements.
            generalize 1%positive. revert n. induction p; ss.
            destruct o; ss.
            - i. rewrite xelements_comm. rewrite 2 fold_left_app.
              rewrite IHp1; auto. ss. rewrite IHp2; auto.
              erewrite (IHp2 p2 _ _ (Datatypes.length l + _)). lia.
            - i. rewrite xelements_comm. rewrite 2 fold_left_app.
              erewrite IHp2; auto. erewrite (IHp2 p2 _ _ (fold_left _ _ 0)).
              rewrite (IHp1 p1); auto. lia. }
          rewrite COMM. remember (PTree.fold _ _ 1).
          remember (PTree.fold (fun m (p: positive) (blk: list phiinstruction) =>
                                Datatypes.length blk + m) (fn_phicode f0) 0) as m.
          rewrite transf_function_fuel_repeatn. rewrite repeatn_distributive.
          rewrite <- 2 transf_function_fuel_repeatn.
          apply transf_function_fuel_phicode_idempotent.
          apply transf_function_fuel_code_idempotent. rewrite Heqn. lia.
          rewrite Heqm. replace (PTree.fold _ _ 0) with (phisize (fn_phicode f0)).
          assert (forall f n,
                  (phisize (fn_phicode (transf_function_fuel n f))) <= 
                  phisize (fn_phicode f)).
          { intros f1 n0; revert f1; induction n0; ss.
            i. rewrite transf_function_fuel_repeatn. ss.
            rewrite <- transf_function_fuel_repeatn. pose proof phisize_dec as DEC.
            remember (transf_function_fuel n0 f1) as NF.
            assert (phisize (fn_phicode (transf_function_fuel 1 NF)) <=
                    phisize (fn_phicode NF)).
            specialize (DEC (fn_code NF)
                            (fn_phicode NF)
                            (fn_phicode (transf_function_fuel 1 NF)) NF). flatten DEC.
            eapply DEC; eauto. exploit DEC; eauto. i; lia. exploit DEC; eauto.
            i; lia. clarify. specialize (IHn0 f1); lia. }
          eapply H0; eauto.
          unfold phisize; ss. }
        unfold transf_function_fuel. unfold simplify_mv. rewrite H. rewrite H0.
        destruct (transf_function f); ss.
    Unshelve. auto. auto. auto. auto.
  Qed.

  Let ge := Genv.globalenv prog.
  Let tge := Genv.globalenv tprog.

  (* Let ev_rel2 := ev_rel_eq. *)

  Lemma match_prog_step_wf_ssa : wf_ssa_program tprog.
  Proof. 
    red. intros.
    red in HWF.
    inv TRANSL.
    intuition. revert H0 H HWF.
    induction 1; intros.
    - inv H.
    - inv H1.      
      + inv H. inv H4.
        destruct f1 ; simpl in * ; try constructor; auto.
        exploit (HWF (Internal f) id); eauto.
        destruct a1, g; simpl in * ; try congruence. 
        left. inv H; simpl in *; auto. 
        intros. inv H4; auto.
        unfold transf_function_step. unfold transf_function_fuel. ss.
        flatten. flatten Eq.
        * eapply elim_mv_preserve_wf_ssa_function; eauto.
        * eapply elim_mv_preserve_wf_ssa_function; eauto.
        * destruct f; eauto.
      + eapply IHlist_forall2; eauto.
  Qed.

  Lemma symbols_preserved:
    forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof.
    eapply (Genv.find_symbol_transf TRANSL).
  Qed. 

  Lemma funct_ptr_translated:
    forall (b: Values.block) (f: fundef),
      Genv.find_funct_ptr ge b = Some f ->
      Genv.find_funct_ptr tge b = Some (transf_fundef_step f).
  Proof.
    apply (Genv.find_funct_ptr_transf TRANSL).
  Qed. 

  Lemma functions_translated:
    forall (v: val) (f: fundef),
      Genv.find_funct ge v = Some f ->
      Genv.find_funct tge v = Some (transf_fundef_step f).
  Proof.
    apply (Genv.find_funct_transf TRANSL).
  Qed. 

  Lemma sig_preserved:
    forall f, funsig (transf_fundef_step f) = funsig f.
  Proof.
    destruct f; simpl; auto. unfold transf_function_step; ss.
    destruct f. unfold transf_function_fuel. ss. flatten; ss.
  Qed.

  Lemma find_function_translated:
    forall m ros rs f,
      find_function ge (ros_to_vos m ros rs) rs = Some f ->
      find_function tge (ros_to_vos m ros rs) rs = Some (transf_fundef_step f).
  Proof.
    intros until f; destruct ros; simpl. des_ifs.
    { apply functions_translated; auto. }
    { apply functions_translated; auto. }
    rewrite symbols_preserved. destruct (Genv.find_symbol ge i); intro.
    { apply funct_ptr_translated; auto. }
    discriminate.
  Qed.

  Lemma fn_params_translated : forall (f:function), 
    fn_params f = fn_params (transf_function_step f).
  Proof.
    intros ; unfold transf_function_step, transf_function_fuel ; simpl; auto.
    flatten. ss.
  Qed.

  Lemma fn_entrypoint_translated : forall (f:function),
    fn_entrypoint f = fn_entrypoint (transf_function_step f).
  Proof.
    intros ; unfold transf_function_step, transf_function_fuel ; simpl; auto.
    flatten; ss.
  Qed.

  Lemma senv_equiv : Senv.equiv ge tge.
  Proof.
    apply (Genv.senv_transf TRANSL).
  Qed.

  Lemma join_point_transf_function_step: forall j f,
    join_point j f <-> join_point j (transf_function_step f).
  Proof.
    i. unfold transf_function_step. unfold transf_function_fuel. ss.
    flatten. flatten Eq; ss.
    - split; ss. rewrite join_point_elim_mv; ss; eauto.
      rewrite <- join_point_elim_mv; ss; eauto. 
    - split; ss. rewrite join_point_elim_mv; ss; eauto.
      rewrite <- join_point_elim_mv; ss; eauto.
    - destruct f; ss.
  Qed.

  Lemma make_predecessors_transf_function_step: forall f,
    Kildall.make_predecessors (fn_code f) successors_instr =
      Kildall.make_predecessors (fn_code (transf_function_step f)) successors_instr.
  Proof.
    i. unfold transf_function_step, transf_function_fuel. ss.
    flatten. flatten Eq; ss.
    erewrite <- make_predecessors_elim_mv; ss. ss.
    erewrite <- make_predecessors_elim_mv; ss. ss.
  Qed.

  Definition equiv_regset_except_d (rs rs': regset) (d: reg) :=
    forall r, r <> d -> rs # r = rs' # r.

  Variant match_functions:
    function -> regset -> function -> regset -> node -> Prop :=
  | match_id (f: function) (rs: regset) (pc: node)
             (NOTFOUND: find_mv_code (fn_code f) = None)
             (NOTFOUND': find_mv_phicode (fn_phicode f) = None) :
      match_functions f rs f rs pc
  | match_code (f: function) (rs rs': regset) (d s: reg) (pc: node)
               (FOUND: find_mv_code (fn_code f) = Some (d, s))
               (EQUIV: equiv_regset_except_d rs rs' d) :
      match_functions f rs (transf_function_step f) rs' pc
  | match_phicode (f: function) (rs rs': regset) (d s: reg) (pc: node)
                  (NOTFOUND: find_mv_code (fn_code f) = None)
                  (FOUND: find_mv_phicode (fn_phicode f) = Some (d, s))
                  (EQUIV: equiv_regset_except_d rs rs' d)
                  (PHIINV: forall pc' phib args,
                           (fn_phicode f) ! pc' = Some phib ->
                           In (Iphi args d) phib ->
                           (forall r, In r args -> r = s) ->
                           dom f pc' pc ->
                           d <> s ->
                           rs # d = rs # s) :
      match_functions f rs (transf_function_step f) rs' pc.

  Inductive match_stackframes : list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil: match_stackframes nil nil
  | match_stackframes_cons: 
    forall res (f:function) sp pc rs rs' st st' pred sig fn args
      (STACK: (match_stackframes st st'))
      (WFF: wf_ssa_function f)
      (MATCH: match_functions f rs (transf_function_step f) rs' pc)
      (PREDINFO: (fn_code f) ! pred = Some (Icall sig fn args res pc)),
      match_stackframes
      ((Stackframe res f sp pc rs) :: st)
      ((Stackframe res (transf_function_step f) sp pc rs') :: st').
      
  Variant match_states: state -> state -> Prop :=
  | match_states_intro:
      forall st st' sp pc rs rs' m f
        (SINV:s_inv ge (State st f sp pc rs m))
        (STACK: match_stackframes st st')
        (MATCH: match_functions f rs (transf_function_step f) rs' pc),
        match_states (State st f sp pc rs m)
                     (State st' (transf_function_step f) sp pc rs' m)
  | match_states_call:
      forall s st f args m
        (SINV:s_inv ge (Callstate s f args m))
        (STACK: match_stackframes s st),
        match_states (Callstate s f args m)
                     (Callstate st (transf_fundef_step f) args m)
  | match_states_return:
    forall s st v m 
        (SINV:s_inv ge (Returnstate s v m))
        (STACK: match_stackframes s st),
        match_states (Returnstate s v m) (Returnstate st v m).

  Lemma transf_initial_states:
    forall st1, initial_state prog st1 ->
                exists st2, initial_state tprog st2 /\ match_states st1 st2.
  Proof.
    intros. inversion H.
    exploit @funct_ptr_translated ; eauto. intros. 
    econstructor; split.
    - econstructor.
      assert (MEM: (Genv.init_mem tprog) = Some m0)
        by (eapply (Genv.init_mem_transf TRANSL); eauto).
      + apply MEM ; auto.
      + replace (prog_main tprog) with (prog_main prog).
        rewrite symbols_preserved; eauto.
        symmetry; eapply match_program_main; eauto.
      + eauto.
      + rewrite <- H3. apply sig_preserved; auto.
    - eapply match_states_call; eauto.
      + constructor.
        eapply Genv.find_funct_ptr_prop; eauto.
        constructor.
      + constructor.
  Qed.

  Lemma transf_final_states:
    forall st1 st2 r,
      match_states st1 st2 -> final_state st1 r -> final_state st2 r.
  Proof.
    intros. inv H0. inv H. 
    inv STACK.
    constructor.
  Qed.

  Lemma transf_function_step_phicode_phicode: forall f pc phib,
    (fn_phicode f) ! pc = Some phib ->
    exists phib', (fn_phicode (transf_function_step f)) ! pc = Some phib' /\
                  phib' = match (find_mv_code (fn_code f)) with
                          | Some (d, s) =>
                              map (subst_phi d s) (remove_mv_phiblock d phib)
                          | None =>
                              match (find_mv_phicode (fn_phicode f)) with
                              | Some (d, s) =>
                                  map (subst_phi d s) (remove_mv_phiblock d phib)
                              | None => phib
                              end
                          end.
  Proof.
    i. unfold transf_function_step, transf_function_fuel; ss.
    flatten; ss.
    - unfold elim_mv_phicode. rewrite PTree.gmap. rewrite H. ss.
      eexists; eauto.
    - unfold elim_mv_phicode. rewrite PTree.gmap. rewrite H. ss.
      eexists; eauto.
    - eauto.
  Qed.

  Lemma transf_function_step_spec : forall f pc ins,
    (fn_code f) ! pc = Some ins ->
    let c' := fn_code (transf_function_step f) in
    c' ! pc = Some ins \/
    match ins with
    | Inop pc' => c' ! pc = Some (Inop pc')
    | Iop Omove _ dst pc' =>
      c' ! pc = Some (Inop pc') \/
      exists args', c' ! pc = Some (Iop Omove args' dst pc')
    | Iop op _ dst pc' =>
      exists args', c' ! pc = Some (Iop op args' dst pc')
    | Iload chunk addr args dst pc' =>
      exists args', c' ! pc = Some (Iload chunk addr args' dst pc')
    | Istore chunk addr args src pc' =>
      exists args' src', c' ! pc = Some (Istore chunk addr args' src' pc')
    | Icall sig ros args res pc' =>
      exists ros' args', c' ! pc = Some (Icall sig ros' args' res pc')
    | Itailcall sig ros args =>
      exists ros' args', c' ! pc = Some (Itailcall sig ros' args')
    | Ibuiltin ef args res pc' =>
      exists args', c' ! pc = Some (Ibuiltin ef args' res pc')
    | Icond cond args ifso ifnot =>
      exists args', c' ! pc = Some (Icond cond args' ifso ifnot)
    | Ijumptable arg tbl =>
      exists arg', c' ! pc = Some (Ijumptable arg' tbl)
    | Ireturn optarg => exists optarg', c' ! pc = Some (Ireturn optarg')
    end.
  Proof.
    i. unfold transf_function_step, transf_function_fuel in c'. ss.
    destruct (find_mv_code (fn_code f)) eqn:FINDC.
    - destruct p; ss. subst c'. eapply elim_mv_code_spec in H; eauto. des.
      + left; eauto.
      + right. destruct ins; ss. destruct o; ss. des. left; eauto. right; eauto.
    - destruct (find_mv_phicode (fn_phicode f)) eqn:FINDPC.
      + destruct p; ss. subst c'. eapply elim_mv_code_spec in H; eauto. des.
        * left; eauto.
        * right. destruct ins; ss. destruct o; ss. des. left; eauto. right; eauto.
      + ss. subst c'; left; ss.
  Qed.

  Lemma transf_function_step_spec_simple : forall f pc ins d s,
    (fn_code f) ! pc = Some ins ->
    (find_mv_code (fn_code f) = None ->
      find_mv_phicode (fn_phicode f) = None ->
      (fn_code (transf_function_step f)) ! pc = Some ins) /\
    (find_mv_code (fn_code f) = Some (d, s) \/
      find_mv_code (fn_code f) = None /\
      find_mv_phicode (fn_phicode f) = Some (d, s) ->
      (fn_code (transf_function_step f)) ! pc = 
    Some (subst_instr d s (remove_mv_instr d ins))).
  Proof.
    unfold transf_function_step, transf_function_fuel; ss. split.
    - i. rewrite H0, H1. ss.
    - i. des.
      + rewrite H0. ss. unfold elim_mv_code. rewrite PTree.gmap. rewrite H; ss.
      + rewrite H0, H1; ss. unfold elim_mv_code. rewrite PTree.gmap. rewrite H; ss.
  Qed.

  Lemma phi_store_spec_for_moves : forall f pc pc' phib k rs args d s,
    wf_ssa_function f ->
    (fn_phicode f) ! pc = Some phib ->
    In (Iphi args d) phib ->
    (forall r, In r args -> r = s) ->
    index_pred (Kildall.make_predecessors (fn_code f) successors_instr) pc' pc
      = Some k ->
    d <> s ->
    (phi_store k phib rs) # d = rs # s.
  Proof.
    i. eapply (fn_ssa f H) in H0 as PHI. revert PHI.
    assert (forall args r, In (Iphi args r) phib
            -> exists a, nth_error args k = Some a).
    { i. eapply nth_error_some_same_length.
      eapply index_pred_some_nth; eauto. eapply (fn_wf_block f H); eauto. }
    revert H5. revert H1 H2. generalize phib. induction phib0.
    - i. inv H1.
    - i. destruct a eqn:EA; ss. des.
      + clarify. exploit H5. left; eauto. i. des. rewrite H1.
        apply nth_error_in in H1. apply H2 in H1; clarify.
        rewrite PMap.gss. eauto.
      + clarify. exploit H5. left; eauto. i; des. rewrite H6.
        rewrite PMap.gso. eapply IHphib0; eauto. split.
        inv PHI; eauto.
        i. eapply PHI0; eauto.
        ii. clarify. inv PHI.
        enough (l = args). clarify; intuition.
        eapply PHI0; eauto.
  Qed.
  
  Lemma phi_store_spec_for_irrelevant : forall f pc phib r rs k,
    wf_ssa_function f ->
    (fn_phicode f) ! pc = Some phib ->
    ~ def f r pc ->
    (phi_store k phib rs) # r = rs # r.
  Proof.
    i. assert (forall args, ~ In (Iphi args r) phib).
    { ii. eapply H1; eauto. }
    revert H2. generalize phib as phib'. induction phib'; ss.
    flatten.
    i. rewrite PMap.gso; eauto. ii; clarify; ss. eapply H2; eauto.
    i. eauto.
  Qed.

  Lemma phi_store_eq_ds: forall f pc phib k rs rs' r d s,
    wf_ssa_function f ->
    (fn_phicode f) ! pc = Some phib ->
    (forall r, r <> d -> rs # r = rs' # r) ->
    r <> d ->
    d <> s ->
    rs # d = rs # s ->
    (phi_store k phib rs) # r 
    = (phi_store k (map (subst_phi d s) (remove_mv_phiblock d phib)) rs') # r.
  Proof.
    i. eapply (fn_ssa f H) in H0. induction phib; ss.
    - eauto.
    - destruct a as [args1 dst1].
      flatten.
      + rewrite Pos.eqb_eq in Eq0; clarify.
        rewrite PMap.gso; eauto. eapply IHphib; eauto. des. inv H0. split; eauto.
      + ss. assert (nth_error (map (rename_reg d s) args1) k
                    = Some (rename_reg d s r0)).
        { revert Eq. revert k. generalize args1 as l. induction l; ss.
          - i. destruct k; ss.
          - i. destruct k; ss.
            + inv Eq. ss.
            + eauto. }
        rewrite H5. destruct (peq dst1 r).
        * clarify. repeat rewrite PMap.gss; eauto.
          destruct (peq r0 s).
          clarify. unfold rename_reg. flatten; ss.
          rewrite Pos.eqb_eq in Eq1; clarify. eapply H1; eauto.
          destruct (peq r0 d).
          clarify. rewrite H4. unfold rename_reg. flatten; ss. eapply H1; eauto.
          rewrite Pos.eqb_neq in Eq1; clarify.
          unfold rename_reg; flatten; ss. rewrite Pos.eqb_eq in Eq1; clarify.
          eapply H1; eauto.
        * repeat rewrite PMap.gso; eauto.
          eapply IHphib; eauto. des. inv H0. split; eauto.
      + rewrite Pos.eqb_eq in Eq0; clarify. eapply IHphib; eauto.
        des. inv H0; eauto.
      + rewrite Pos.eqb_neq in Eq0. ss.
        assert (nth_error (map (rename_reg d s) args1) k = None).
        { revert k Eq. generalize args1 as l. induction l; ss.
          destruct k; ss. destruct l; ss. eauto. }
        rewrite H5. eapply IHphib; eauto. des. inv H0. eauto.
  Qed.

  Lemma phi_store_irrelevant : forall f pc pc' phib k rs rs' r d s,
    wf_ssa_function f ->
    (fn_phicode f) ! pc' = Some phib ->
    (fn_code f) ! pc = Some (Inop pc') ->
    index_pred (Kildall.make_predecessors (fn_code f) successors_instr) pc pc'
      = Some k ->
    (forall r, r <> d -> rs # r = rs' # r) ->
    d <> s ->
    r <> d ->
    ~ use_phicode f d pc ->
    (phi_store k phib rs) # r =
      (phi_store k (map (subst_phi d s) (remove_mv_phiblock d phib)) rs') # r.
  Proof.
    i. eapply (fn_ssa f) in H0 as PHIINV; eauto. des.
    pose proof fn_phiargs.
    assert (forall args x,
              In (Iphi args x) phib -> exists arg, nth_error args k = Some arg).
    { i. exploit fn_phiargs; eauto. }
    assert (forall args r, ~ (In (Iphi args r) phib /\ nth_error args k = Some d)).
    { ii. des. eapply H6; eauto. econstructor; eauto. }
    clear H7 H0 H6.
    induction phib; ss.
    - eauto.
    - destruct a as [args dst].
      exploit H8; eauto. i; des. rewrite H0.
      flatten.
      + rewrite Pos.eqb_eq in Eq; clarify.
        rewrite PMap.gso; eauto. eapply IHphib; eauto. inv PHIINV; eauto.
        ii. des. eapply H9; eauto.
      + ss. assert (nth_error (map (rename_reg d s) args) k
                    = Some (rename_reg d s arg)).
        { revert H0; generalize k; generalize args as l. induction l; ss.
          - destruct k0; ss.
          - i. destruct k0; ss. inv H0; ss. eauto. }
        rewrite H6. destruct (peq r dst).
        { clarify. repeat rewrite PMap.gss. unfold rename_reg.
          flatten. rewrite Pos.eqb_eq in Eq0; clarify. exfalso; eapply H9; eauto.
          eapply H3; eauto. ii; clarify. rewrite Pos.eqb_neq in Eq0; clarify. }
        { repeat rewrite PMap.gso; eauto. eapply IHphib; eauto.
          inv PHIINV; eauto. ii; des. eapply H9; eauto. }
  Qed.

  Lemma code_preserved_irrelevant: forall f pc d s ins,
    wf_ssa_function f ->
    ~ use_code f d pc ->
    ~ assigned_code_spec (fn_code f) pc d ->
    (fn_code f) ! pc = Some ins ->
    ins = subst_instr d s (remove_mv_instr d ins).
  Proof.
    i. assert ((remove_mv_instr d ins) = ins).
    { destruct ins; ss. destruct o; ss. flatten; ss.
      rewrite Pos.eqb_eq in Eq; clarify; exfalso; eapply H1; eauto. }
    rewrite H3.
    assert (forall l, ~ In d l -> map (rename_reg d s) l = l).
    { induction l; ss. i. rewrite IHl; eauto. unfold rename_reg.
      flatten; ss. rewrite Pos.eqb_eq in Eq; clarify; ss. exfalso; eauto. }
    destruct ins; ss; try (rewrite H4; ss; ii; eapply H0; eauto using use_code).
    rewrite H4. unfold rename_reg; flatten. rewrite Pos.eqb_eq in Eq; clarify.
    exfalso; eapply H0; eauto using use_code.
    ii; eapply H0; eauto using use_code.
    unfold rename_fn. flatten.
    unfold rename_reg at 1. flatten; ss.
    rewrite Pos.eqb_eq in Eq0; clarify.
    exfalso; eapply H0; eauto using use_code.
    rewrite H4; eauto. ii; eapply H0; eauto using use_code.
    rewrite H4; eauto. ii; eapply H0; eauto using use_code.
    unfold rename_fn. flatten; ss.
    unfold rename_reg at 1. flatten; ss. rewrite Pos.eqb_eq in Eq0; clarify.
    exfalso; eapply H0; eauto using use_code.
    rewrite H4; eauto. ii; eapply H0; eauto using use_code.
    rewrite H4; eauto. ii; eapply H0; eauto using use_code.
    assert (forall l, ~ In d (params_of_builtin_args l)
                      -> map (rename_barg d s) l = l).
    { induction l0; ss. i. rewrite IHl0; ss.
      assert (forall a, ~ In d (params_of_builtin_arg a) -> rename_barg d s a = a).
      { induction a0; ss. unfold rename_reg. flatten; ss.
        rewrite Pos.eqb_eq in Eq; clarify. i; exfalso; eauto.
        i. rewrite IHa0_1, IHa0_2; ss; ii; eapply H6; rewrite in_app_iff; eauto.
        i. rewrite IHa0_1, IHa0_2; ss; ii; eapply H6; rewrite in_app_iff; eauto. }
      rewrite H6; eauto. ii. eapply H5; rewrite in_app_iff; eauto.
      ii; eapply H5; rewrite in_app_iff; eauto. }
    rewrite H5; ss. ii; eapply H0; eauto using use_code.
    unfold rename_reg; flatten; ss. rewrite Pos.eqb_eq in Eq; clarify.
    exfalso; eapply H0; eauto using use_code.
    destruct o; ss. unfold rename_reg; flatten; ss; rewrite Pos.eqb_eq in *; clarify.
    exfalso; eapply H0; eauto using use_code.
  Qed.

  Lemma value_list_preserved_for_equiv_regsets: forall args rs rs' d,
    equiv_regset_except_d rs rs' d ->
    ~ In d args ->
    rs ## args = rs' ## args.
  Proof.
    induction args; ss.
    i. erewrite IHargs; eauto. enough (rs # a = rs' # a); eauto.
    rewrite H1; eauto.
  Qed.

  Lemma value_list_preserved_for_ds_eq: forall args (rs rs': regset) d s,
    equiv_regset_except_d rs rs' d ->
    rs # d = rs # s ->
    d <> s ->
    rs' ## (map (rename_reg d s) args) = rs ## args.
  Proof.
    induction args; ss. i.
    erewrite IHargs; eauto. destruct (peq a d).
    - clarify. unfold rename_reg. flatten; ss.
      enough (rs' # s = rs # d). rewrite H2; eauto.
      erewrite <- H; eauto. rewrite Pos.eqb_neq in Eq; clarify.
    - unfold rename_reg; flatten; ss. rewrite Pos.eqb_eq in Eq; clarify.
      rewrite H; eauto.
  Qed.

  Lemma eval_builtin_args_preserved_for_equiv_regset:
    forall args rs rs' d s vargs m sp,
    equiv_regset_except_d rs rs' d ->
    ~ In d (params_of_builtin_args args) ->
    d <> s ->
    eval_builtin_args ge (fun r => rs # r) sp m args vargs <->
    eval_builtin_args tge (fun r => rs' # r) sp m (map (rename_barg d s) args) vargs.
  Proof.
    assert (RNBAPRES: forall arg d s, ~ In d (params_of_builtin_arg arg) ->
                                      rename_barg d s arg = arg).
    { induction arg; ss.
      - i. destruct (peq x d).
        + clarify; exfalso; eauto.
        + unfold rename_reg; flatten; ss. rewrite Pos.eqb_eq in Eq; clarify.
      - i. rewrite IHarg1, IHarg2; ss.
        ii. exploit H. rewrite in_app_iff. right; eauto. ss.
        ii. exploit H. rewrite in_app_iff. left; eauto. ss.
      - i. rewrite IHarg1, IHarg2; ss.
        ii. exploit H. rewrite in_app_iff. right; eauto. ss.
        ii. exploit H. rewrite in_app_iff. left; eauto. ss. }
    assert (EQUIVBARG: forall arg d sp m barg rs rs',
                              equiv_regset_except_d rs rs' d ->
                              ~ In d (params_of_builtin_arg arg) ->
                              eval_builtin_arg ge (fun r => rs # r) sp m arg barg <->
                              eval_builtin_arg ge (fun r => rs' # r) sp m arg barg).
    { induction arg; ss; split; ii; try (inv H1; econstructor; eauto).
      - destruct (peq d x); clarify. exfalso; eauto.
        inv H1. rewrite H; eauto. econstructor; eauto.
      - destruct (peq d x); clarify. exfalso; eauto.
        inv H1. rewrite <- H; eauto. econstructor; eauto.
      - eapply IHarg1 in H4; eauto. ii; exploit H; eauto.
        ii; eapply H0; rewrite in_app_iff; left; eauto.
      - eapply IHarg2 in H6; eauto. ii; exploit H; eauto.
        ii; eapply H0; rewrite in_app_iff; right; eauto.
      - eapply IHarg1 in H4; eauto. ii; eapply H0; rewrite in_app_iff; left; eauto.
      - eapply IHarg2 in H6; eauto. ii; eapply H0; rewrite in_app_iff; right; eauto.
      - eapply IHarg1 in H4; eauto. ii; exploit H; eauto.
        ii; eapply H0; rewrite in_app_iff; left; eauto.
      - eapply IHarg2 in H6; eauto. ii; exploit H; eauto.
        ii; eapply H0; rewrite in_app_iff; right; eauto.
      - eapply IHarg1 in H4; eauto. ii; eapply H0; rewrite in_app_iff; left; eauto.
      - eapply IHarg2 in H6; eauto. ii; eapply H0; rewrite in_app_iff; right; eauto. }
    induction args; ss.
    - split; i; inv H2; econstructor; eauto.
    - split.
      + i. inv H2. econstructor; eauto.
        * eapply eval_builtin_arg_preserved. eapply symbols_preserved.
          rewrite RNBAPRES. eapply EQUIVBARG; eauto. ii; exploit H; eauto.
          ii; eapply H0; rewrite in_app_iff; left; eauto.
          ii; eapply H0; rewrite in_app_iff; left; eauto.
        * eapply IHargs; eauto. ii; eapply H0; rewrite in_app_iff; right; eauto.
      + i. inv H2. econs; eauto.
        * eapply eval_builtin_arg_preserved in H5.
          revert H5. rewrite RNBAPRES. i. 
          rewrite EQUIVBARG in H5; eauto. ii; exploit H; eauto.
          ii; eapply H0; rewrite in_app_iff; left; eauto.
          ii; eapply H0; rewrite in_app_iff; left; eauto.
          i. exploit symbols_preserved; eauto.
        * eapply IHargs; eauto. ii; eapply H0; rewrite in_app_iff; right; eauto.
  Qed.
  
  Lemma eval_builtin_args_preserved_for_ds_eq:
    forall args rs rs' d s vargs m sp,
    equiv_regset_except_d rs rs' d ->
    d <> s ->
    rs # d = rs # s ->
    eval_builtin_args ge (fun r => rs # r) sp m args vargs <->
    eval_builtin_args tge (fun r => rs' # r) sp m (map (rename_barg d s) args) vargs.
  Proof.
    assert (EQUIVBARG:
            forall arg d s sp m barg rs rs',
            equiv_regset_except_d rs rs' d ->
            d <> s ->
            rs # d = rs # s ->
            eval_builtin_arg ge (fun r => rs # r) sp m arg barg <->
            eval_builtin_arg tge (fun r => rs' # r) sp m (rename_barg d s arg) barg).
    { induction arg; ss; split; ii; try (inv H2; econstructor; eauto; fail).
      - destruct (peq d x).
        + clarify. unfold rename_reg; flatten; ss. inv H2.
          rewrite H1. rewrite H; eauto. econstructor; eauto.
          rewrite Pos.eqb_neq in Eq; clarify.
        + unfold rename_reg; flatten; ss. rewrite Pos.eqb_eq in Eq; clarify.
          inv H2. rewrite H; eauto. econstructor; eauto.
      - destruct (peq d x).
        + clarify. unfold rename_reg in H2; flatten H2; ss. inv H2.
          rewrite <- H; eauto. rewrite <- H1. econstructor; eauto.
          rewrite Pos.eqb_neq in Eq; clarify.
        + unfold rename_reg in H2; flatten H2; ss. rewrite Pos.eqb_eq in Eq; clarify.
          inv H2. rewrite <- H; eauto. econstructor; eauto.
      - inv H2. econstructor; eauto. unfold Senv.symbol_address in *.
        flatten H7; ss. rewrite symbols_preserved; rewrite Eq; ss.
      - inv H2. econstructor; eauto. unfold Senv.symbol_address in *.
        flatten H7; ss. rewrite <- symbols_preserved; rewrite Eq; ss.
      - eapply eval_builtin_arg_preserved. eapply symbols_preserved.
        inv H2. econstructor; eauto.
      - eapply eval_builtin_arg_preserved. symmetry. eapply symbols_preserved.
        inv H2. econstructor; eauto.
      - inv H2; econs; eauto; try eapply IHarg1; eauto; eapply IHarg2; eauto.
      - inv H2; econs; eauto; try eapply IHarg1; eauto; eapply IHarg2; eauto.
      - inv H2; econs; eauto; try eapply IHarg1; eauto; eapply IHarg2; eauto.
      - inv H2; econs; eauto; try eapply IHarg1; eauto; eapply IHarg2; eauto. }
    induction args; ss.
    - split; i; inv H2; econstructor; eauto.
    - split; i.
      + inv H2; econstructor; eauto. eapply EQUIVBARG; eauto. eapply IHargs; eauto.
      + inv H2; econs; eauto. eapply EQUIVBARG; eauto. eapply IHargs; eauto.
  Qed.

  Lemma s_inv_eq_ds: forall f d s st sp pc rs m pc' pc'0,
    (fn_code f) ! pc' = Some (Iop Omove (s :: nil) d pc'0) ->
    s_inv ge (State st f sp pc rs m) ->
    dom f pc' pc ->
    pc' <> pc ->
    rs # d = rs # s.
  Proof.
    i. inv H0. exploit SINV; eauto.
    econstructor; eauto.
    i. inv H0. inv H5. ss. inv EVAL. ss.
  Qed.

  Require Import Simulation.
  
  Section STEPSIM.

  Definition tsem := SSA.semantics tprog.

  Variables st_init_tgt st_init_tgt1: tsem.(Smallstep.state).
  Hypothesis INIT1: tsem.(Smallstep.initial_state) st_init_tgt.
  Hypothesis ICAP1: tsem.(Smallstep.initial_capture) st_init_tgt st_init_tgt1.
  Definition gmtgt : ident -> option Z := tsem.(initial_pimap) st_init_tgt1.

  Lemma step_simulation:
    forall S1 t S2, IStep (SSA.semantics prog) S1 t S2 ->
    forall S1' (IBIND: ge_binded_state tge S1' gmtgt), match_states S1 S1' ->
    exists S2', DStep (SSA.semantics tprog) S1' t S2' /\ match_states S2 S2'.
  Proof.
    assert (Hwf1: forall s f sp pc rs m, s_inv ge (State s f sp pc rs m) ->
                  wf_ssa_function f) by (intros s f sp pc rs m H; inv H; auto).
    destruct 1. generalize dependent S2. rename H into INT. unfold is_internal in INT.
    induction 1; intros S1' IBIND MS.
    - inv MS. exists (State st' (transf_function_step f) sp pc' rs' m); split.
      + apply transf_function_step_spec in H as Hstep.
        des; eauto; DStep_tac.
        all : eapply exec_Inop_njp; eauto; rewrite <- join_point_transf_function_step; ss.
      + econstructor; eauto. eapply SSAinv.subj_red; eauto. econs; eauto.
        inv MATCH.
        rewrite <- 2 H3 in *. econstructor 1; eauto.
        econstructor; eauto.
        econstructor 3; eauto. i.
        eapply PHIINV; eauto. eapply (@Dom.sdom_dom_pred node peq); eauto.
        econstructor; eauto. ii; clarify. eapply H0. eapply (fn_phicode_inv); eauto.
        intros contra; rewrite contra in *; discriminate.
        econstructor; eauto.
    
    - (* Inop jnp *)
      inv MS. eapply transf_function_step_phicode_phicode in H1 as HTFPHI. des.
      exists (State st' (transf_function_step f) sp pc' (phi_store k phib' rs') m).
      split.
      + apply transf_function_step_spec in H; des; eauto.
        all: DStep_tac; eapply exec_Inop_jp; eauto;
          try (rewrite <- join_point_transf_function_step; eauto);
          rewrite <- make_predecessors_transf_function_step; eauto.
      + inv MATCH.
        * rewrite <- H5 in *. rewrite NOTFOUND in *. rewrite NOTFOUND' in *.
          econstructor; eauto. eapply SSAinv.subj_red; eauto. econs; eauto.
          rewrite <- H5. econstructor; eauto.
        * rewrite FOUND in *. econstructor; eauto. eapply SSAinv.subj_red; eauto.
          econstructor 2; eauto. econs; eauto. i.
          destruct (classic (use_phicode f d pc)).
          { ii. eapply phi_store_eq_ds; eauto.
            ii; clarify; apply find_mv_not_same in FOUND; eauto.
            eapply find_mv_exists in FOUND. des.
            eapply s_inv_eq_ds; eauto.
            exploit fn_strict; eauto. econstructor 2; eauto.
            ii; clarify. }
          { ii. eapply phi_store_irrelevant; eauto. ii; clarify.
            eapply find_mv_not_same; eauto. }
        * rewrite NOTFOUND in *; rewrite FOUND in *.
          econstructor; eauto. eapply SSAinv.subj_red; eauto. econs; eauto.
          econstructor 3; eauto.
          destruct (classic (use_phicode f d pc)).
          { ii. eapply phi_store_eq_ds; eauto. ii; clarify.
            eapply no_phi_use_def; eauto.
            eapply find_mv_phicode_exists in FOUND as FOUND'; des.
            eapply PHIINV; eauto. i. inv H5; eauto.
            rewrite forallb_forall in FOUND'1. eapply FOUND'1 in H6.
            rewrite Pos.eqb_eq in H6; eauto.
            eapply fn_strict; eauto. econstructor 2; eauto.
            ii; clarify; eapply no_phi_use_def; eauto. }
          { ii. eapply phi_store_irrelevant; eauto.
            ii; clarify; eapply no_phi_use_def; eauto. }
          i. destruct (peq pc'0 pc').
          { clarify. erewrite phi_store_spec_for_moves; eauto.
            erewrite phi_store_spec_for_irrelevant; eauto. ii.
            eapply no_phi_use_def'; eauto. }
          { erewrite phi_store_spec_for_irrelevant; eauto.
            erewrite phi_store_spec_for_irrelevant; eauto.
            eapply PHIINV; eauto. eapply (@Dom.sdom_dom_pred node peq); eauto.
            econstructor; eauto. econstructor; eauto.
            ii. eapply no_phi_use_def'; eauto.
            ii. eapply unique_def_spec_def. eauto. eauto.
            econstructor 3; eauto. ii; clarify. }

    - (* Iop *)
      inv MS. inv MATCH.
      + exists (State st' (transf_function_step f) sp pc' rs' # res <- v m).
        split. rewrite <- 2 H3. DStep_tac. eapply exec_Iop; eauto.
        erewrite eval_operation_wrapper_preserved; eauto.
        eapply symbols_preserved; eauto. rewrite <- H3 at 1.
        econstructor 1; eauto. eapply SSAinv.subj_red; eauto.
        rewrite <- H3 in *. econstructor; eauto. rewrite <- H3 in *. econstructor 1; eauto.
      + exploit transf_function_step_spec_simple; eauto. i. des.
        exploit H2; eauto. i. clear H1 H2.
        destruct (classic (use_code f d pc)).
        { eapply find_mv_exists in FOUND as PCDEFD. des.
          assert (dom f pc0 pc). eapply fn_strict; eauto. econstructor; eauto.
          exists (State st' (transf_function_step f) sp pc' rs' # res <- v m).
          split.
          - DStep_tac.
            assert (remove_mv_instr d (Iop op args res pc') = Iop op args res pc').
            unfold remove_mv_instr. destruct op; ss. flatten; ss.
            rewrite Pos.eqb_eq in Eq; clarify; ss.
            exfalso; eapply fn_use_def_code; eauto. rewrite H4 in H3.
            eapply exec_Iop; eauto. unfold subst_instr in H3.
            assert (pc0 <> pc). ii; clarify.
            inv H4; try rewrite PCDEFD in *; clarify. ss.
            flatten H5; clarify. rewrite Pos.eqb_neq in Eq; clarify.
            erewrite value_list_preserved_for_ds_eq.
            erewrite eval_operation_wrapper_preserved; eauto.
            eapply symbols_preserved; eauto. eauto.
            eapply s_inv_eq_ds; eauto.
            ii; clarify; exploit find_mv_not_same; eauto.
          - econstructor; eauto. eapply SSAinv.subj_red; eauto. econs; eauto.
            econstructor; eauto. ii. destruct (peq r res).
            clarify. rewrite 2 PMap.gss; eauto. rewrite 2 PMap.gso; eauto. }
        { destruct (classic (def f d pc)).
          { exists (State st' (transf_function_step f) sp pc' rs' m).
            eapply find_mv_exists in FOUND as FOUND'; eauto. des.
            assert (def f d pc0). econstructor; eauto.
            eapply def_def_eq in H4 as EQ. 3:{ eapply H2. } clarify; ss. split.
            DStep_tac. eapply exec_Inop_njp; eauto.
            flatten H3; ss. rewrite Pos.eqb_neq in Eq; clarify.
            rewrite <- join_point_transf_function_step. ii.
            eapply fn_normalized in H; eauto. rewrite FOUND' in H; discriminate.
            eapply successors_instr_succs in FOUND'. des; eauto.
            unfold Kildall.successors_list; rewrite FOUND'. eauto. ss; eauto.
            econstructor; eauto. eapply SSAinv.subj_red; eauto. econs; eauto.
            econstructor 2; eauto. ii.
            rewrite PMap.gso; eauto. eauto. }
          { exploit code_preserved_irrelevant; eauto. i. rewrite <- H4 in H3.
            exists (State st' (transf_function_step f) sp pc' rs' # res <- v m).
            split. DStep_tac. eapply exec_Iop; eauto.
            erewrite eval_operation_wrapper_preserved.
            erewrite <- value_list_preserved_for_equiv_regsets; eauto.
            ii; eapply H1; econstructor; eauto.
            eapply symbols_preserved; eauto.
            econstructor; eauto. eapply SSAinv.subj_red; eauto. econs; eauto.
            econstructor; eauto. ii. destruct (peq r res).
            clarify; rewrite 2 PMap.gss; eauto.
            rewrite 2 PMap.gso; eauto. } }
      + exists (State st' (transf_function_step f) sp pc' rs' # res <- v m).
        exploit transf_function_step_spec_simple; eauto. i. des.
        exploit H2; eauto. i; clear H1 H2. split.
        destruct (classic (use_code f d pc)).
        { assert (remove_mv_instr d (Iop op args res pc') = Iop op args res pc').
          { unfold remove_mv_instr. flatten; ss. rewrite Pos.eqb_eq in Eq0; clarify.
            eapply find_mv_phicode_exists in FOUND; des.
            exfalso; eapply assigned_code_and_phi; eauto. } rewrite H2 in H3. clear H2.
          eapply find_mv_phicode_exists in FOUND as PHIMOVE; des.
          DStep_tac. eapply exec_Iop; eauto.
          unfold subst_instr in H3.
          erewrite value_list_preserved_for_ds_eq.
          erewrite eval_operation_wrapper_preserved; eauto.
          eapply symbols_preserved; eauto. eauto.
          eapply PHIINV; eauto. rewrite forallb_forall in PHIMOVE1; i; eauto.
          inv H2; eauto. eapply PHIMOVE1 in H4; rewrite Pos.eqb_eq in H4; eauto.
          eapply fn_strict; eauto. econstructor; eauto.
          all: ii; clarify; eapply no_phi_use_def; eauto. }
        { eapply find_mv_phicode_exists in FOUND; eauto; des.
          exploit code_preserved_irrelevant; eauto. ii.
          exploit assigned_code_and_phi; eauto. i. rewrite <- H2 in H3.
          DStep_tac; eapply exec_Iop; eauto.
          erewrite value_list_preserved_for_equiv_regsets.
          erewrite eval_operation_wrapper_preserved; eauto.
          eapply symbols_preserved; eauto. ii; erewrite EQUIV; eauto.
          ii; eapply H1; eauto. econstructor; eauto. }
        econstructor; eauto. eapply SSAinv.subj_red; eauto. econs; eauto.
        econstructor 3; eauto. ii.
        destruct (peq r res);
          clarify; [erewrite 2 PMap.gss | erewrite 2 PMap.gso]; eauto.
        ii. destruct (peq d res); clarify.
        exploit assigned_code_and_phi; eauto. i; ss.
        destruct (peq s0 res); clarify.
        exploit no_phi_use_def'; eauto; ss.
        eapply (@Dom.sdom_dom_pred node peq); eauto. econstructor; eauto.
        ii; clarify. exploit fn_normalized; eauto.
        eapply fn_phicode_inv; eauto. ii; rewrite H1 in *; clarify.
        unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
        rewrite H; ss; eauto. i; rewrite H in *; eauto; clarify.
        econstructor; eauto. rewrite 2 PMap.gso; ss.
        exploit PHIINV; eauto.
        eapply (@Dom.sdom_dom_pred node peq); eauto. econstructor; eauto.
        ii; clarify. exploit fn_normalized; eauto.
        eapply fn_phicode_inv; eauto. ii; rewrite H1 in *; clarify.
        unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
        rewrite H; ss; eauto. i; rewrite H in *; eauto; clarify.
        econstructor; eauto.
    
    - (* Iload *)
      inv MS. exists (State st' (transf_function_step f) sp pc' rs' # dst <- v m).
      inv MATCH.
      + rewrite <- H4 in *. exploit transf_function_step_spec_simple; eauto.
        i; des. exploit H2; eauto. clear H2 H3. i. split.
        DStep_tac. eapply exec_Iload; eauto. erewrite eval_addressing_preserved; eauto.
        eapply symbols_preserved.
        econstructor 1; eauto. eapply SSAinv.subj_red; eauto. econs 4; eauto.
        rewrite <- H4; econstructor; eauto.
      + exploit transf_function_step_spec_simple; eauto.
        i; des. exploit H3; eauto. clear H2 H3. i.
        eapply find_mv_exists in FOUND as TFCODE; des.
        split. ss.
        DStep_tac. eapply exec_Iload; eauto. erewrite eval_addressing_preserved.
        destruct (classic (use_code f d pc)).
        { erewrite value_list_preserved_for_ds_eq; eauto. inv SINV.
          eapply s_inv_eq_ds; eauto.
          exploit fn_strict; eauto. econstructor; eauto. ii. subst pc0.
          rewrite H in *; clarify.
          ii. exploit find_mv_not_same; eauto. }
        { exploit code_preserved_irrelevant; eauto. ii.
          exploit assigned_code_unique. eauto. eauto. econstructor. eapply TFCODE.
          i; subst pc. rewrite TFCODE in *; clarify. i. ss. rewrite <- H4 in H2.
          inv H4. rewrite <- 2 H6. erewrite value_list_preserved_for_equiv_regsets.
          eauto. ii; rewrite EQUIV; eauto. ii; eapply H3; eauto using use_code. }
        eapply symbols_preserved.
        econstructor; eauto. eapply SSAinv.subj_red; eauto. econs 4; eauto.
        econstructor 2; eauto. ii.
        destruct (peq r dst);
          clarify; [erewrite 2 PMap.gss | erewrite 2 PMap.gso]; eauto.
      + exploit transf_function_step_spec_simple; eauto.
        i; des. exploit H3; eauto. clear H2 H3. i.
        eapply find_mv_phicode_exists in FOUND as PHIMOVE; des.
        split. destruct (classic (use_code f d pc)).
        { ss. DStep_tac. eapply exec_Iload; eauto.
          erewrite value_list_preserved_for_ds_eq.
          erewrite eval_addressing_preserved; eauto.
          eapply symbols_preserved; eauto. eauto.
          eapply PHIINV; eauto. rewrite forallb_forall in PHIMOVE1; i; eauto.
          inv H4; eauto. eapply PHIMOVE1 in H5; rewrite Pos.eqb_eq in H5; eauto.
          eapply fn_strict; eauto. econstructor; eauto.
          ii; clarify; eapply no_phi_use_def; eauto.
          ii; clarify; eapply no_phi_use_def; eauto. }
        { exploit code_preserved_irrelevant; eauto. ii.
          exploit assigned_code_and_phi; eauto. i. rewrite <- H4 in H2.
          DStep_tac; eapply exec_Iload; eauto.
          erewrite value_list_preserved_for_equiv_regsets.
          erewrite eval_addressing_preserved; eauto.
          eapply symbols_preserved; eauto. ii; erewrite EQUIV; eauto.
          ii; eapply H3; eauto using use_code. }
        econstructor; eauto. eapply SSAinv.subj_red; eauto. econs 4; eauto.
        econstructor 3; eauto. ii.
        destruct (peq r dst);
          clarify; [erewrite 2 PMap.gss | erewrite 2 PMap.gso]; eauto.
        ii. destruct (peq d dst); clarify.
        exploit assigned_code_and_phi; eauto. i; ss.
        assert (pc' <> pc'0).
        { ii; clarify. exploit fn_normalized; eauto.
          eapply fn_phicode_inv; eauto. ii; rewrite H3 in *; clarify.
          unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
          rewrite H; ss; eauto. i; rewrite H in *; eauto; clarify. }
        destruct (peq s0 dst); clarify.
        exploit no_phi_use_def'; eauto; ss.
        eapply (@Dom.sdom_dom_pred node peq); eauto.
        econstructor; eauto. econstructor; eauto.
        rewrite 2 PMap.gso; eauto.
        exploit PHIINV; eauto. eapply (@Dom.sdom_dom_pred node peq); eauto.
        econstructor; eauto. econstructor; eauto.
    
    - (* Istore *)
      inv MS. exists (State st' (transf_function_step f) sp pc' rs' m').
      inv MATCH.
      + rewrite <- H4 in *. split. rewrite H4 in H.
        DStep_tac; eapply exec_Istore; eauto.
        erewrite eval_addressing_preserved; eauto. eapply symbols_preserved.
        econstructor; eauto. eapply SSAinv.subj_red; eauto. econs; eauto.
        rewrite <- H4. econstructor; eauto.
      + exploit transf_function_step_spec_simple; eauto.
        i; des. exploit H3; eauto. clear H2 H3. i.
        eapply find_mv_exists in FOUND as TFCODE; des.
        destruct (classic (use_code f d pc)).
        { split. ss.
          DStep_tac; eapply exec_Istore; eauto. erewrite eval_addressing_preserved.
          erewrite value_list_preserved_for_ds_eq; eauto.
          eapply s_inv_eq_ds; eauto.
          exploit fn_strict; eauto. econstructor; eauto. ii. subst pc0.
          rewrite H in *; clarify.
          ii. exploit find_mv_not_same; eauto. eapply symbols_preserved.
          destruct (peq src d); ss.
          - clarify. unfold rename_reg; flatten. rewrite <- EQUIV.
            erewrite <- s_inv_eq_ds; eauto.
            exploit fn_strict; eauto. econstructor; eauto.
            ii; subst pc. rewrite H in *; clarify.
            ii; exploit find_mv_not_same; eauto.
            rewrite Pos.eqb_neq in Eq; clarify.
          - unfold rename_reg; flatten; ss. rewrite Pos.eqb_eq in Eq; clarify.
            rewrite <- EQUIV; ss.
          - econstructor; eauto. eapply SSAinv.subj_red; eauto. econs; eauto.
            econstructor; eauto. }
        { exploit code_preserved_irrelevant; eauto. ii.
          exploit assigned_code_unique. eauto. eauto. econstructor. eapply TFCODE.
          i; subst pc. rewrite TFCODE in *; clarify. i. ss. rewrite <- H4 in H2.
          split. DStep_tac; eapply exec_Istore; eauto. erewrite eval_addressing_preserved.
          erewrite value_list_preserved_for_equiv_regsets; eauto.
          ii; rewrite EQUIV; eauto. ii; eapply H3; eauto using use_code.
          eapply symbols_preserved. rewrite <- EQUIV; eauto. ii; clarify.
          eapply H3; eauto using use_code.
          econstructor; eauto. eapply SSAinv.subj_red; eauto. econs; eauto.
          econstructor 2; eauto. }
      + exploit transf_function_step_spec_simple; eauto.
        i; des. exploit H3; eauto. clear H2 H3. i.
        eapply find_mv_phicode_exists in FOUND as PHIMOVE; des.
        split. destruct (classic (use_code f d pc)).
        { ss. DStep_tac. eapply exec_Istore; eauto.
          erewrite value_list_preserved_for_ds_eq.
          erewrite eval_addressing_preserved; eauto.
          eapply symbols_preserved; eauto. eauto.
          eapply PHIINV; eauto. rewrite forallb_forall in PHIMOVE1; i; eauto.
          inv H4; eauto. eapply PHIMOVE1 in H5; rewrite Pos.eqb_eq in H5; eauto.
          eapply fn_strict; eauto. econstructor; eauto.
          ii; clarify; eapply no_phi_use_def; eauto.
          ii; clarify; eapply no_phi_use_def; eauto.
          destruct (peq src d).
          { clarify. unfold rename_reg. flatten; ss. rewrite <- EQUIV; eauto.
            exploit PHIINV; eauto. i. inv H4; ss. rewrite forallb_forall in PHIMOVE1.
            eapply PHIMOVE1 in H5; rewrite Pos.eqb_eq in H5; eauto.
            exploit fn_strict; eauto. econstructor; eauto.
            ii; clarify; exploit no_phi_use_def; eauto.
            intros ds; rewrite <- ds; eauto.
            ii; clarify; exploit no_phi_use_def; eauto.
            rewrite Pos.eqb_neq in Eq; clarify. }
          { unfold rename_reg. flatten; ss. rewrite Pos.eqb_eq in Eq; clarify.
            rewrite <- EQUIV; eauto. } }
        { exploit code_preserved_irrelevant; eauto. ii.
          exploit assigned_code_and_phi; eauto. i. rewrite <- H4 in H2. clear H4.
          DStep_tac; eapply exec_Istore; eauto.
          erewrite value_list_preserved_for_equiv_regsets.
          erewrite eval_addressing_preserved; eauto.
          eapply symbols_preserved; eauto. ii; erewrite EQUIV; eauto.
          ii; eapply H3; eauto using use_code.
          rewrite <- EQUIV; eauto. ii; clarify; eapply H3; eauto using use_code. }
        econstructor; eauto. eapply SSAinv.subj_red; eauto. econs; eauto.
        econstructor 3; eauto. ii.
        assert (pc' <> pc'0).
        { ii; clarify. exploit fn_normalized; eauto.
          eapply fn_phicode_inv; eauto. ii; rewrite H3 in *; clarify.
          unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
          rewrite H; ss; eauto. i; rewrite H in *; eauto; clarify. }
        exploit PHIINV; eauto. eapply (@Dom.sdom_dom_pred node peq); eauto.
        econstructor; eauto. econstructor; eauto.

    - (* Icall *)
      inv MS. inv MATCH.
      + exists (Callstate (Stackframe res (transf_function_step f) sp pc' rs' :: st')
                        (transf_fundef_step fd) rs' ## args m).
        rewrite <- H3 in *. split.
        * rewrite <- H3. DStep_tac. eapply exec_Icall; eauto.
          erewrite find_function_translated; eauto. eapply sig_preserved.
        * econstructor; eauto. eapply SSAinv.subj_red; eauto. econs; eauto.
          rewrite H3 at 2. econstructor; eauto. rewrite <- H3 in *; econstructor; eauto.
      + exploit transf_function_step_spec_simple; eauto.
        i; des. exploit H2; eauto. clear H1 H2. i.
        eapply find_mv_exists in FOUND as TFCODE; des. ss.
        exists (Callstate (Stackframe res (transf_function_step f) sp pc' rs' :: st')
                          (transf_fundef_step fd)
                          rs' ## (map (rename_reg d s0) args) m). 
        destruct (classic (use_code f d pc)).
        { split.
          - DStep_tac. eapply exec_Icall; eauto.
            + erewrite find_function_translated; eauto.
              { destruct ros.
                - destruct (peq d r).
                  + clarify. unfold rename_fn, rename_reg in *. rewrite Pos.eqb_refl in *.
                    ss.
                    repeat rewrite <- EQUIV; eauto.
                    erewrite <- s_inv_eq_ds; eauto.
                    exploit fn_strict; eauto. econstructor; eauto.
                    ii; subst pc0. rewrite H in *; clarify.
                    ii; clarify; exploit find_mv_not_same; eauto.
                    ii; clarify; exploit find_mv_not_same; eauto.
                  + unfold rename_fn, rename_reg. flatten.
                    * eapply Pos.eqb_eq in Eq; clarify.
                    * ss. repeat rewrite <- EQUIV; eauto.
                - ss. }
            + eapply sig_preserved.
          - erewrite value_list_preserved_for_ds_eq. econstructor 2; eauto.
            eapply SSAinv.subj_red; eauto. econs; eauto.
            econstructor; eauto. econstructor 2; eauto. eauto. eapply s_inv_eq_ds; eauto.
            exploit fn_strict; eauto. econstructor; eauto.
            ii; subst pc0; clarify. ii; exploit find_mv_not_same; eauto. }
        { split. DStep_tac. eapply exec_Icall; eauto.
          erewrite find_function_translated; eauto.
          { destruct ros.
            - destruct (peq d r).
              + clarify. exploit H2; eauto using use_code; ss.
              + unfold rename_fn, rename_reg. flatten.
                * eapply Pos.eqb_eq in Eq; clarify.
                * ss. repeat rewrite <- EQUIV; eauto.
            - ss. }
          eapply sig_preserved.
          exploit code_preserved_irrelevant; eauto. ii.
          exploit assigned_code_unique. eauto. eauto. econstructor. eauto.
          ii; subst pc0. clarify. i. ss. inv H3. rewrite <- 2 H6.
          exploit value_list_preserved_for_equiv_regsets; eauto.
          2:{ i. rewrite <- H3. econstructor 2; eauto.
              eapply SSAinv.subj_red; eauto. econs; eauto.
              econstructor; eauto. econstructor 2; eauto. }
          ii. destruct ros; eapply H2; eauto using use_code. }
      + exploit transf_function_step_spec_simple; eauto; i; des.
        exploit H2; eauto; i. clear H1 H2. ss.
        exists (Callstate (Stackframe res (transf_function_step f) sp pc' rs' :: st')
                          (transf_fundef_step fd)
                          rs' ## (map (rename_reg d s0) args) m).
        eapply find_mv_phicode_exists in FOUND as MVPHI; des.
        destruct (classic (use_code f d pc)).
        * split. DStep_tac. eapply exec_Icall; eauto.
          erewrite find_function_translated; eauto.
          destruct ros.
          { destruct (peq d r).
            - clarify. unfold rename_fn, rename_reg in *. rewrite Pos.eqb_refl in *. ss.
              repeat rewrite <- EQUIV; eauto.
              erewrite <- PHIINV; eauto. i. inv H2; eauto.
              rewrite forallb_forall in MVPHI1; eapply MVPHI1 in H4.
              rewrite Pos.eqb_eq in H4; clarify.
              exploit fn_strict; eauto. econstructor; eauto.
              all : ii; clarify; exploit no_phi_use_def; eauto.
            - unfold rename_fn, rename_reg. flatten.
              + eapply Pos.eqb_eq in Eq; clarify.
              + ss. repeat rewrite <- EQUIV; eauto. }
            { ss. }
            eapply sig_preserved.
            assert (rs # d = rs # s0).
            { eapply PHIINV; eauto. ii. inv H2; ss. rewrite forallb_forall in MVPHI1.
              eapply MVPHI1 in H4; rewrite Pos.eqb_eq in H4; clarify.
              exploit fn_strict; eauto. econstructor; eauto.
              ii; clarify; exploit no_phi_use_def; eauto. }
            erewrite value_list_preserved_for_ds_eq; eauto.
            econstructor; eauto. eapply SSAinv.subj_red; eauto. econs; eauto.
            econstructor; eauto. econstructor 3; eauto.
            ii; clarify; exploit no_phi_use_def; eauto.
        * split.
          { DStep_tac. eapply exec_Icall; eauto. erewrite find_function_translated; eauto.
            destruct ros.
            - destruct (peq d r).
              + clarify. exploit H1; eauto using use_code; ss.
              + unfold rename_fn, rename_reg. flatten.
                * eapply Pos.eqb_eq in Eq; clarify.
                * ss.
                  repeat rewrite <- EQUIV; eauto.
            - ss.
            - eapply sig_preserved. }
          { exploit code_preserved_irrelevant; eauto. ii.
            exploit assigned_code_and_phi; eauto. ii. inv H2; ss. rewrite <- 2 H6.
            exploit value_list_preserved_for_equiv_regsets; eauto.
            2:{ i. rewrite <- H2. econstructor; eauto.
                eapply SSAinv.subj_red; eauto. econs; eauto. econstructor; eauto.
                econstructor 3; eauto. ii. exploit PHIINV; eauto.
                eapply (@Dom.sdom_dom_pred node peq); eauto.
                econstructor; eauto. ii; subst pc'0.
                exploit fn_normalized; eauto. exploit fn_phicode_inv; eauto.
                i. rewrite H11. ii. rewrite H12 in H4; clarify.
                unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
                rewrite H; ss. left; ss. i; clarify. econstructor; eauto. }
            ii; eapply H1. destruct ros; eauto using use_code. }
    
    - (* Itailcall *)
      inv MS. inv MATCH.
      + exists (Callstate st' (transf_fundef_step fd) rs' ## args m').
        rewrite <- H4 in *. split.
        * rewrite <- H4. DStep_tac. eapply exec_Itailcall; eauto.
          erewrite find_function_translated; eauto. eapply sig_preserved.
        * econstructor; eauto. eapply SSAinv.subj_red; eauto. econs; eauto.
      + exploit transf_function_step_spec_simple; eauto.
        i; des. exploit H3; eauto. clear H1 H3. i.
        eapply find_mv_exists in FOUND as TFCODE; des. ss.
        exists (Callstate st' (transf_fundef_step fd)
                          rs' ## (map (rename_reg d s0) args) m').
        destruct (classic (use_code f d pc)).
        { split. DStep_tac. eapply exec_Itailcall; eauto.
          erewrite find_function_translated; eauto.
          { destruct ros.
            - destruct (peq d r).
              + clarify. unfold rename_fn, rename_reg in *. rewrite Pos.eqb_refl in *. ss.
                repeat rewrite <- EQUIV; eauto.
                erewrite <- s_inv_eq_ds; eauto.
                exploit fn_strict; eauto. econstructor; eauto.
                ii; subst pc0. rewrite H in *; clarify.
                all: ii; clarify; exploit find_mv_not_same; eauto.
              + unfold rename_fn, rename_reg. flatten.
                * eapply Pos.eqb_eq in Eq; clarify.
                * ss. repeat rewrite <- EQUIV; eauto.
            - ss. }
          eapply sig_preserved.
          unfold transf_function_step, transf_function_fuel. flatten; ss.
          erewrite value_list_preserved_for_ds_eq; eauto. econstructor 2; eauto.
          eapply SSAinv.subj_red; eauto. econs; eauto. eapply s_inv_eq_ds; eauto.
          exploit fn_strict; eauto. econstructor; eauto.
          ii; subst pc0; clarify. ii; exploit find_mv_not_same; eauto. }
        { split. DStep_tac. eapply exec_Itailcall; eauto.
          erewrite find_function_translated; eauto.
          { destruct ros.
            - destruct (peq d r).
              + clarify. exploit H3; eauto using use_code; ss.
              + unfold rename_fn, rename_reg. flatten.
                * eapply Pos.eqb_eq in Eq; clarify.
                * ss. repeat rewrite <- EQUIV; eauto.
            - ss. }
          eapply sig_preserved.
          unfold transf_function_step, transf_function_fuel; flatten; ss.
          exploit code_preserved_irrelevant; eauto. ii.
          exploit assigned_code_unique. eauto. eauto. econstructor. eauto.
          ii; subst pc0. clarify. i. ss. inv H4. rewrite <- 2 H7.
          erewrite value_list_preserved_for_equiv_regsets; eauto. econstructor 2; eauto.
          eapply SSAinv.subj_red; eauto.
          erewrite <- value_list_preserved_for_equiv_regsets; eauto.
          econs; eauto.
          all: ii; destruct ros; eapply H3; eauto using use_code. }
      + exploit transf_function_step_spec_simple; eauto; i; des.
        exploit H3; eauto; i. clear H1 H3. ss.
        exists (Callstate st' (transf_fundef_step fd)
                          rs' ## (map (rename_reg d s0) args) m').
        eapply find_mv_phicode_exists in FOUND as MVPHI; des.
        destruct (classic (use_code f d pc)).
        * split. DStep_tac. eapply exec_Itailcall; eauto.
          erewrite find_function_translated; eauto.
          { destruct ros.
            - destruct (peq d r).
              + clarify. unfold rename_fn, rename_reg in *. rewrite Pos.eqb_refl in *. ss.
                repeat rewrite <- EQUIV; eauto.
                erewrite <- PHIINV; eauto. i. inv H3; eauto.
                rewrite forallb_forall in MVPHI1; eapply MVPHI1 in H5.
                rewrite Pos.eqb_eq in H5; clarify.
                exploit fn_strict; eauto. econstructor; eauto.
                all : ii; clarify; exploit no_phi_use_def; eauto.
              + unfold rename_fn, rename_reg. flatten.
                * eapply Pos.eqb_eq in Eq; clarify.
                * ss. repeat rewrite <- EQUIV; eauto.
            - ss. }
          eapply sig_preserved.
          unfold transf_function_step, transf_function_fuel. flatten; ss.
          erewrite value_list_preserved_for_ds_eq; eauto. econstructor 2; eauto.
          eapply SSAinv.subj_red; eauto. econs; eauto.
          eapply PHIINV; eauto. ii. inv H3; ss. rewrite forallb_forall in MVPHI1.
          eapply MVPHI1 in H5; rewrite Pos.eqb_eq in H5; clarify.
          exploit fn_strict; eauto. econstructor; eauto.
          all : ii; clarify; exploit no_phi_use_def; eauto.
        * split.
          { DStep_tac. eapply exec_Itailcall; eauto.
            erewrite find_function_translated; eauto.
            destruct ros.
            - destruct (peq d r).
              + clarify. exploit H1; eauto using use_code; ss.
              + unfold rename_fn, rename_reg. flatten.
                * eapply Pos.eqb_eq in Eq; clarify.
                * ss. repeat rewrite <- EQUIV; eauto.
            - ss.
            - eapply sig_preserved.
            - unfold transf_function_step, transf_function_fuel; flatten; ss. }
          { exploit code_preserved_irrelevant; eauto. ii.
            exploit assigned_code_and_phi; eauto. ii. inv H3; ss. rewrite <- 2 H7.
            exploit value_list_preserved_for_equiv_regsets; eauto.
            2:{ i. rewrite <- H3. econstructor; eauto.
                eapply SSAinv.subj_red; eauto. econs; eauto. }
            ii; eapply H1. destruct ros; eauto using use_code. }
      
    - (* Ibuiltin *)
      inv MS. 
      exists (State st' (transf_function_step f) sp pc'
                    (regmap_setres res vres rs') m').
      inv MATCH.
      + rewrite <- H4 in *. split.
        * rewrite <- H4. DStep_tac. eapply exec_Ibuiltin; eauto.
          eapply eval_builtin_args_preserved. eapply symbols_preserved.
          eapply H0. eapply external_call_symbols_preserved; eauto.
          eapply senv_equiv.
        * econstructor; eauto. eapply SSAinv.subj_red; eauto. econs; eauto.
          rewrite <- H4. econstructor; eauto.
      + exploit transf_function_step_spec_simple; eauto; i; des.
        exploit H3; eauto; i. clear H2 H3. ss.
        eapply find_mv_exists in FOUND as MVCODE; des. split.
        * DStep_tac. eapply exec_Ibuiltin; eauto.
          2:{ eapply external_call_symbols_preserved. eapply senv_equiv.
              eapply H1. }
          destruct (classic (use_code f d pc)).
          { eapply eval_builtin_args_preserved_for_ds_eq; eauto.
            ii; exploit find_mv_not_same; eauto. exploit s_inv_eq_ds; eauto.
            exploit fn_strict; eauto. econstructor; eauto.
            ii; subst pc0; ss. clarify. }
          { eapply eval_builtin_args_preserved_for_equiv_regset; eauto.
            ii; eapply H2; eauto using use_code.
            ii; exploit find_mv_not_same; eauto. }
        * econstructor; eauto. eapply SSAinv.subj_red; eauto. econs; eauto.
          econstructor 2; eauto. destruct res; ss. ii.
          destruct (peq r x).
          { clarify. rewrite 2 PMap.gss; eauto. }
          { rewrite 2 PMap.gso; eauto. }
      + exploit transf_function_step_spec_simple; eauto; i; des.
        exploit H3; eauto; i. clear H2 H3. ss.
        eapply find_mv_phicode_exists in FOUND as MVPHI; des. split.
        * destruct (classic (use_code f d pc)).
          { DStep_tac. eapply exec_Ibuiltin; eauto.
            eapply eval_builtin_args_preserved_for_ds_eq; eauto.
            ii; clarify; exploit no_phi_use_def; eauto.
            exploit PHIINV; eauto. ii. inv H3; ss. rewrite forallb_forall in MVPHI1.
            eapply MVPHI1 in H5; rewrite Pos.eqb_eq in H5; clarify; ss.
            exploit fn_strict; eauto. econstructor; eauto.
            ii; clarify; exploit no_phi_use_def; eauto.
            eapply external_call_symbols_preserved; eauto. eapply senv_equiv; eauto. }
          { DStep_tac. eapply exec_Ibuiltin; eauto.
            eapply eval_builtin_args_preserved_for_equiv_regset; eauto.
            ii; eapply H2; eauto using use_code.
            ii; clarify; exploit no_phi_use_def; eauto.
            eapply external_call_symbols_preserved; eauto. eapply senv_equiv; eauto. }
        * econstructor; eauto. eapply SSAinv.subj_red; eauto. econs; eauto.
          econstructor 3; eauto. destruct res; ss. ii.
          destruct (peq r x).
          { clarify. rewrite 2 PMap.gss; eauto. } { rewrite 2 PMap.gso; eauto. }
          ii. assert (dom f pc'0 pc).
          { eapply (@Dom.sdom_dom_pred node peq); eauto. econstructor; eauto.
            ii; subst pc'0. exploit fn_normalized; eauto. exploit fn_phicode_inv; eauto.
            intros JF; rewrite JF. ii. rewrite H8 in H2; clarify.
            unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
            rewrite H; ss. eauto. i; clarify. econstructor; eauto. }
          ii. destruct res; ss. destruct (peq x d).
          { clarify. exploit assigned_code_and_phi; eauto; ss. }
          destruct (peq x s0).
          { clarify. exploit no_phi_use_def'; eauto. ss. }
          rewrite 2 PMap.gso; eauto.
          exploit PHIINV; eauto. exploit PHIINV; eauto.

    - (* Icond, true *)
      inv MS. exists (State st' (transf_function_step f) sp ifso rs' m).
      split.
      + inv MATCH.
        * rewrite <- H3 in *. rewrite H3 in H. DStep_tac.
          eapply exec_Icond_true; eauto.
        * exploit transf_function_step_spec_simple; eauto.
          i; des. exploit H2; eauto; i; ss. clear H1 H2.
          eapply find_mv_exists in FOUND as MVCODE; des.
          assert (pc <> pc0).
          { ii; subst pc0. clarify. }
          DStep_tac. eapply exec_Icond_true; eauto.
          destruct (classic (use_code f d pc)).
          { erewrite value_list_preserved_for_ds_eq; eauto.
            exploit s_inv_eq_ds; eauto. exploit fn_strict; eauto. econstructor; eauto.
            ii; exploit find_mv_not_same; eauto. }
          { exploit code_preserved_irrelevant; eauto. ii. exploit assigned_code_unique.
            eauto. eauto. econstructor; eauto. ss.
            i. inv H4. rewrite <- 2 H6.
            erewrite value_list_preserved_for_equiv_regsets; eauto.
            ii; rewrite EQUIV; eauto.
            ii; eapply H2; eauto using use_code. }
        * exploit transf_function_step_spec_simple; eauto.
          i; des; exploit H2; eauto; i; ss; clear H1 H2.
          eapply find_mv_phicode_exists in FOUND as MVPHI; des.
          DStep_tac. eapply exec_Icond_true; eauto.
          destruct (classic (use_code f d pc)).
          { erewrite value_list_preserved_for_ds_eq; eauto.
            exploit PHIINV; eauto. i. inv H2; ss. rewrite forallb_forall in MVPHI1.
            eapply MVPHI1 in H4; rewrite Pos.eqb_eq in H4; clarify.
            exploit fn_strict; eauto. econstructor; eauto.
            ii; clarify; exploit no_phi_use_def; eauto. 
            ii; clarify; exploit no_phi_use_def; eauto. }
          { exploit code_preserved_irrelevant; eauto. ii.
            exploit assigned_code_and_phi; eauto.
            i. inv H2. rewrite <- 2 H5.
            erewrite value_list_preserved_for_equiv_regsets; eauto.
            ii; rewrite EQUIV; eauto.
            ii; eapply H1; eauto using use_code. }
      + inv MATCH.
        * econstructor; eauto.
          eapply SSAinv.subj_red; eauto. rewrite <- H3 in *. eapply exec_Icond_true; eauto.
          rewrite <- 2 H3 in *. econs; eauto.
        * econs; eauto.
          eapply SSAinv.subj_red; eauto. eapply exec_Icond_true; eauto.
          econs; eauto.
        * econs; eauto.
          eapply SSAinv.subj_red; eauto. eapply exec_Icond_true; eauto.
          econs 3; eauto. ii.
          exploit PHIINV; eauto. eapply (@Dom.sdom_dom_pred node peq); eauto.
          econstructor; eauto. ii; subst ifso. exploit fn_normalized; eauto.
          exploit fn_phicode_inv; eauto.
          intros JF; rewrite JF; intros PHI; rewrite PHI in *; clarify.
          unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
          rewrite H; ss. eauto. i; clarify. econstructor; eauto.
      
    - (* Icond, false *)
      inv MS. exists (State st' (transf_function_step f) sp ifnot rs' m).
      split.
      + inv MATCH.
        * rewrite <- H3 in *. rewrite H3 in H. DStep_tac.
          eapply exec_Icond_false; eauto.
        * exploit transf_function_step_spec_simple; eauto.
          i; des. exploit H2; eauto; i; ss. clear H1 H2.
          eapply find_mv_exists in FOUND as MVCODE; des.
          assert (pc <> pc0).
          { ii; subst pc0. clarify. }
          DStep_tac. eapply exec_Icond_false; eauto.
          destruct (classic (use_code f d pc)).
          { erewrite value_list_preserved_for_ds_eq; eauto.
            exploit s_inv_eq_ds; eauto. exploit fn_strict; eauto. econstructor; eauto.
            ii; exploit find_mv_not_same; eauto. }
          { exploit code_preserved_irrelevant; eauto. ii. exploit assigned_code_unique.
            eauto. eauto. econstructor; eauto. ss.
            i. inv H4. rewrite <- 2 H6.
            erewrite value_list_preserved_for_equiv_regsets; eauto.
            ii; rewrite EQUIV; eauto.
            ii; eapply H2; eauto using use_code. }
        * exploit transf_function_step_spec_simple; eauto.
          i; des; exploit H2; eauto; i; ss; clear H1 H2.
          eapply find_mv_phicode_exists in FOUND as MVPHI; des.
          DStep_tac. eapply exec_Icond_false; eauto.
          destruct (classic (use_code f d pc)).
          { erewrite value_list_preserved_for_ds_eq; eauto.
            exploit PHIINV; eauto. i. inv H2; ss. rewrite forallb_forall in MVPHI1.
            eapply MVPHI1 in H4; rewrite Pos.eqb_eq in H4; clarify.
            exploit fn_strict; eauto. econstructor; eauto.
            ii; clarify; exploit no_phi_use_def; eauto. 
            ii; clarify; exploit no_phi_use_def; eauto. }
          { exploit code_preserved_irrelevant; eauto. ii.
            exploit assigned_code_and_phi; eauto.
            i. inv H2. rewrite <- 2 H5.
            erewrite value_list_preserved_for_equiv_regsets; eauto.
            ii; rewrite EQUIV; eauto.
            ii; eapply H1; eauto using use_code. }
      + inv MATCH.
        * econstructor; eauto.
          eapply SSAinv.subj_red; eauto. rewrite <- H3 in *. eapply exec_Icond_false; eauto.
          rewrite <- 2 H3 in *. econs; eauto.
        * econs; eauto.
          eapply SSAinv.subj_red; eauto. eapply exec_Icond_false; eauto.
          econs; eauto.
        * econs; eauto.
          eapply SSAinv.subj_red; eauto. eapply exec_Icond_false; eauto.
          econs 3; eauto. ii.
          exploit PHIINV; eauto. eapply (@Dom.sdom_dom_pred node peq); eauto.
          econstructor; eauto. ii; subst ifnot. exploit fn_normalized; eauto.
          exploit fn_phicode_inv; eauto.
          intros JF; rewrite JF; intros PHI; rewrite PHI in *; clarify.
          unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
          rewrite H; ss. eauto. i; clarify. econstructor; eauto.  

    - (* Ijumptable *)
      inv MS. exists (State st' (transf_function_step f) sp pc' rs' m).
      split.
      + inv MATCH.
        * rewrite <- 2 H4 in *. DStep_tac. eapply exec_Ijumptable; eauto.
        * eapply find_mv_exists in FOUND as MVCODE; des.
          exploit transf_function_step_spec_simple. eapply H. i; des.
          exploit H3; eauto; i; ss; clear H2 H3.
          destruct (classic (use_code f d pc)).
          { DStep_tac. eapply exec_Ijumptable; eauto. destruct (peq d arg).
            { clarify. unfold rename_reg; flatten; ss.
              - rewrite <- EQUIV; eauto.
                exploit s_inv_eq_ds; eauto. exploit fn_strict; eauto.
                econstructor; eauto.
                ii; subst pc0; clarify. i. rewrite <- H3; ss.
                ii; exploit find_mv_not_same; eauto.
              - rewrite Pos.eqb_neq in Eq; clarify. }
            { unfold rename_reg; flatten.
              - rewrite Pos.eqb_eq in Eq; clarify.
              - rewrite <- EQUIV; eauto. } }
          { DStep_tac. eapply exec_Ijumptable; eauto. unfold rename_reg; flatten.
            - rewrite Pos.eqb_eq in Eq; clarify. exfalso; eapply H2; eauto using use_code.
            - rewrite Pos.eqb_neq in Eq. rewrite <- EQUIV; eauto. }
        * exploit transf_function_step_spec_simple; eauto.
          i; des; exploit H3; eauto; i; ss; clear H2 H3.
          eapply find_mv_phicode_exists in FOUND as MVPHI; des.
          DStep_tac. eapply exec_Ijumptable; eauto.
          destruct (classic (use_code f d pc)).
          { destruct (peq d arg).
            { clarify. unfold rename_reg; flatten; ss.
              - rewrite <- EQUIV; eauto.
                exploit PHIINV; eauto. i. inv H3; ss. rewrite forallb_forall in MVPHI1.
                eapply MVPHI1 in H5; rewrite Pos.eqb_eq in H5; clarify.
                exploit fn_strict; eauto. econstructor; eauto.
                ii; clarify; exploit no_phi_use_def; eauto. i; rewrite <- H3; ss.
                ii; clarify; exploit no_phi_use_def; eauto.
              - rewrite Pos.eqb_neq in Eq; clarify.  }
            { unfold rename_reg; flatten.
              - rewrite Pos.eqb_eq in Eq; clarify.
              - rewrite <- EQUIV; eauto. } }
          { exploit code_preserved_irrelevant; eauto. ii.
            exploit assigned_code_and_phi; eauto.
            i. inv H3. rewrite <- 2 H6. rewrite <- EQUIV; eauto.
            ii; clarify; eapply H2; eauto using use_code. }
      + inv MATCH.
        * econs; eauto. eapply SSAinv.subj_red; eauto.
          rewrite <- H4 in *. econs 11; eauto. rewrite <- 2 H4 in *. econs; eauto.
        * econs; eauto. eapply SSAinv.subj_red; eauto. econs 11; eauto.
          econstructor 2; eauto.
        * econs; eauto. eapply SSAinv.subj_red; eauto. econs 11; eauto.
          econstructor 3; eauto. ii.
          exploit PHIINV; eauto. eapply (@Dom.sdom_dom_pred node peq); eauto.
          econstructor; eauto. ii; subst pc'0. exploit fn_normalized; eauto.
          exploit fn_phicode_inv; eauto.
          intros JF; rewrite JF; intros PHI; rewrite PHI in *; clarify.
          unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
          rewrite H; ss. eapply list_nth_z_in; eauto. i; clarify. econstructor; eauto.
          ss. eapply list_nth_z_in; eauto.
          
    - (* Ireturn *)
      inv MS. inv MATCH.
      + exists (Returnstate st' (regmap_optget or Vundef rs') m').
        rewrite <- 2 H3 in *. split.
        * DStep_tac. eapply exec_Ireturn; eauto.
        * econstructor; eauto. eapply SSAinv.subj_red; eauto. econs; eauto.
      + eapply find_mv_exists in FOUND as MVCODE; des.
        exploit transf_function_step_spec_simple. eapply H. eauto; i; des.
        exploit H2; eauto; i; ss; clear H1 H2.
        exists (Returnstate st'
                            (regmap_optget (option_map (rename_reg d s0) or) Vundef rs')
                            m').
        split.
        * DStep_tac. eapply exec_Ireturn; eauto.
          unfold transf_function_step, transf_function_fuel; flatten; ss.
        * destruct (classic (use_code f d pc)).
          { inv H1; clarify. unfold rename_reg; flatten; ss.
            exploit s_inv_eq_ds; eauto. exploit fn_strict; eauto.
            econstructor; eauto using use_code.
            ii; subst pc0; clarify. i. rewrite Pos.eqb_refl.
            rewrite <- EQUIV. rewrite <- H.
            econstructor; eauto. eapply SSAinv.subj_red; eauto.
            exploit exec_Ireturn; eauto.
            ii; clarify; exploit find_mv_not_same; eauto. }
          { destruct or; ss. unfold rename_reg; flatten; ss.
            - rewrite Pos.eqb_eq in Eq; clarify; exfalso;
                eapply H1; eauto using use_code.
            - rewrite Pos.eqb_neq in Eq. rewrite <- EQUIV; eauto.
              econstructor; eauto. eapply SSAinv.subj_red; eauto.
              exploit exec_Ireturn. eapply H. all: eauto.
            - econs; eauto. eapply SSAinv.subj_red; eauto.
              exploit exec_Ireturn. eapply H. all: eauto. }
      + eapply find_mv_phicode_exists in FOUND as MVPHI; des.
        exploit transf_function_step_spec_simple. eapply H. eauto; i; des.
        exploit H2; eauto; i; ss; clear H1 H2.
        exists (Returnstate st'
                            (regmap_optget (option_map (rename_reg d s0) or) Vundef rs')
                            m').
        split.
        * DStep_tac. eapply exec_Ireturn; eauto.
          unfold transf_function_step, transf_function_fuel; flatten; ss.
        * destruct or; ss.
          { destruct (classic (use_code f d pc)).
            { inv H1; clarify. unfold rename_reg; flatten; ss.
              exploit PHIINV; eauto. i. inv H; ss. rewrite forallb_forall in MVPHI1.
              eapply MVPHI1 in H1; rewrite Pos.eqb_eq in H1; clarify.
              exploit fn_strict; eauto. econstructor; eauto using use_code.
              ii; clarify; exploit no_phi_use_def; eauto.
              i. rewrite <- EQUIV. rewrite <- H. econstructor; eauto.
              eapply SSAinv.subj_red; eauto. exploit exec_Ireturn.
              eapply H2. all: eauto.
              ii; clarify; exploit no_phi_use_def; eauto.
              rewrite Pos.eqb_neq in Eq; clarify. }
            { unfold rename_reg; flatten; ss.
              - rewrite Pos.eqb_eq in Eq; clarify; exfalso;
                  eapply H1; eauto using use_code.
              - rewrite Pos.eqb_neq in Eq. rewrite <- EQUIV; eauto.
                econstructor; eauto. eapply SSAinv.subj_red; eauto.
                exploit exec_Ireturn. eapply H. all: eauto. } }
          { econstructor; eauto. eapply SSAinv.subj_red; eauto.
            clear H3. exploit exec_Ireturn; eauto. }

    - (* internal *)
      ss. inv MS.
      exists (State st (transf_function_step f) (Vptr stk Ptrofs.zero)
                    (fn_entrypoint (transf_function_step f))
                    (init_regs args (fn_params (transf_function_step f))) m').
      split.
      + DStep_tac. eapply exec_function_internal; eauto.
        unfold transf_function_step, transf_function_fuel; flatten; ss.
      + assert (fn_entrypoint (transf_function_step f) = fn_entrypoint f).
        { unfold transf_function_step, transf_function_fuel; flatten; ss. }
        assert (fn_params (transf_function_step f) = fn_params f).
        { unfold transf_function_step, transf_function_fuel; flatten; ss. }
        rewrite H0, H1. clear H0 H1. econstructor; eauto.
        eapply SSAinv.subj_red; eauto. econs; eauto.
        assert (transf_function_step f = transf_function_step f) by auto.
        unfold transf_function_step at 2 in H0.
        unfold transf_function_fuel in H0. ss. flatten H0.
        * econstructor 2; eauto. ii; ss.
        * econstructor 3; eauto. ii; ss.
          ii. eapply Dom.dom_entry in H4. clarify.
          exploit no_assigned_phi_spec_fn_entrypoint; eauto. inv SINV; inv WFF; ss.
          i; ss. eapply Pos.eq_dec.
        * rewrite H0. destruct f; ss. econstructor 1; eauto.
        
    - (* external *)
      inv MS. exists (Returnstate st res m'). split.
      DStep_tac. eapply exec_function_external; eauto.
      eapply external_call_symbols_preserved; eauto. eapply senv_equiv.
      econstructor; eauto. eapply SSAinv.subj_red; eauto. econs; eauto. 

    - (* return *)
      inv MS. inv STACK. eexists. split.
      DStep_tac. eapply exec_return.
      econstructor; eauto. eapply SSAinv.subj_red; eauto. econs; eauto.
      inv MATCH.
      + rewrite <- 2 H1 in *. econstructor; eauto.
      + econstructor 2; eauto. ii. destruct (peq r res).
        clarify. rewrite 2 PMap.gss; eauto.
        rewrite 2 PMap.gso; eauto.
      + econstructor 3; eauto.
        * ii. destruct (peq r res).
          clarify. rewrite 2 PMap.gss; eauto. rewrite 2 PMap.gso; eauto.
        * ii. eapply find_mv_phicode_exists in FOUND as MVPHI; des; eauto.
          assert (pc' = pc0). { eapply def_def_eq; eauto. } clarify.
          destruct (peq res d).
          { clarify. exploit assigned_code_and_phi; eauto. ss. }
          destruct (peq res s0).
          { clarify. exploit no_phi_use_def'. eauto. eapply MVPHI. eauto.
            i. inv H; ss. rewrite forallb_forall in MVPHI1. eapply MVPHI1 in H4.
            rewrite Pos.eqb_eq in H4; ss. eauto.
            eapply (@Dom.sdom_dom_pred node peq); eauto.
            econstructor; eauto. ii; subst pc0; clarify.
            exploit fn_normalized; eauto. exploit fn_phicode_inv; eauto.
            intros JP; rewrite JP; ii. rewrite H in MVPHI; clarify.
            unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
            rewrite PREDINFO; ss. eauto. i; clarify. econstructor; eauto. ss. }
          rewrite 2 PMap.gso; eauto.
    Unshelve. all: eauto.
  Qed.


  (* Lemma transl_step_correct:
    forall s1 t s2,
      step ge s1 t s2 ->
      step ge s1 t s2 ->
      forall s1' (MS: match_states s1 s1'),
      exists s2', step tge s1' t s2' /\ match_states s2 s2'.
  Proof.
    assert (Hwf1: forall s f sp pc rs m, s_inv ge (State s f sp pc rs m) ->
                  wf_ssa_function f) by (intros s f sp pc rs m H; inv H; auto).
    
    induction 1; intros; inv MS; auto.
    - (* Inop not jnp *)
      exists (State st' (transf_function_step f) sp pc' rs' m); split.
      + eapply exec_Inop_njp; eauto. apply transf_function_step_spec in H as Hstep.
        des; eauto. rewrite <- join_point_transf_function_step; ss.
      + econstructor; eauto. eapply SSAinv.subj_red; eauto.
        inv MATCH.
        rewrite <- 2 H4 in *. econstructor 1; eauto.
        econstructor; eauto.
        econstructor 3; eauto. i.
        eapply PHIINV; eauto. eapply (@Dom.sdom_dom_pred node peq); eauto.
        econstructor; eauto. ii; clarify. eapply H0. eapply (fn_phicode_inv); eauto.
        intros contra; rewrite contra in *; discriminate.
        econstructor; eauto.

    - (* Inop jnp *)
      eapply transf_function_step_phicode_phicode in H1 as HTFPHI. des.
      exists (State st' (transf_function_step f) sp pc' (phi_store k phib' rs') m).
      split.
      + eapply exec_Inop_jp; eauto.
        apply transf_function_step_spec in H; des; eauto.
        rewrite <- join_point_transf_function_step; eauto.
        rewrite <- make_predecessors_transf_function_step; eauto.
      + inv MATCH.
        * rewrite <- H6 in *. rewrite NOTFOUND in *. rewrite NOTFOUND' in *.
          econstructor; eauto. eapply SSAinv.subj_red; eauto.
          rewrite <- H6. econstructor; eauto.
        * rewrite FOUND in *. econstructor; eauto. eapply SSAinv.subj_red; eauto.
          econstructor 2; eauto. i.
          destruct (classic (use_phicode f d pc)).
          { ii. eapply phi_store_eq_ds; eauto.
            ii; clarify; apply find_mv_not_same in FOUND; eauto.
            eapply find_mv_exists in FOUND. des.
            eapply s_inv_eq_ds; eauto.
            exploit fn_strict; eauto. econstructor 2; eauto.
            ii; clarify. }
          { ii. eapply phi_store_irrelevant; eauto. ii; clarify.
            eapply find_mv_not_same; eauto. }
        * rewrite NOTFOUND in *; rewrite FOUND in *.
          econstructor; eauto. eapply SSAinv.subj_red; eauto.
          econstructor 3; eauto.
          destruct (classic (use_phicode f d pc)).
          { ii. eapply phi_store_eq_ds; eauto. ii; clarify.
            eapply no_phi_use_def; eauto.
            eapply find_mv_phicode_exists in FOUND as FOUND'; des.
            eapply PHIINV; eauto. i. inv H6; eauto.
            rewrite forallb_forall in FOUND'1. eapply FOUND'1 in H7.
            rewrite Pos.eqb_eq in H7; eauto.
            eapply fn_strict; eauto. econstructor 2; eauto.
            ii; clarify; eapply no_phi_use_def; eauto. }
          { ii. eapply phi_store_irrelevant; eauto.
            ii; clarify; eapply no_phi_use_def; eauto. }
          i. destruct (peq pc'0 pc').
          { clarify. erewrite phi_store_spec_for_moves; eauto.
            erewrite phi_store_spec_for_irrelevant; eauto. ii.
            eapply no_phi_use_def'; eauto. }
          { erewrite phi_store_spec_for_irrelevant; eauto.
            erewrite phi_store_spec_for_irrelevant; eauto.
            eapply PHIINV; eauto. eapply (@Dom.sdom_dom_pred node peq); eauto.
            econstructor; eauto. econstructor; eauto.
            ii. eapply no_phi_use_def'; eauto.
            ii. eapply unique_def_spec_def. eauto. eauto.
            econstructor 3; eauto. ii; clarify. }

    - (* Iop *)
      inv MATCH.
      + exists (State st' (transf_function_step f) sp pc' rs' # res <- v m).
        split. rewrite <- 2 H4. eapply exec_Iop; eauto.
        erewrite eval_operation_wrapper_preserved; eauto.
        eapply symbols_preserved; eauto. rewrite <- H4 at 1.
        econstructor 1; eauto. eapply SSAinv.subj_red; eauto.
        rewrite <-  H4 in *. econstructor; eauto.
      + exploit transf_function_step_spec_simple; eauto. i. des.
        exploit H3; eauto. i. clear H2 H3. 
        destruct (classic (use_code f d pc)).
        { eapply find_mv_exists in FOUND as PCDEFD. des.
          assert (dom f pc0 pc). eapply fn_strict; eauto. econstructor; eauto.
          exists (State st' (transf_function_step f) sp pc' rs' # res <- v m).
          split.
          - assert (remove_mv_instr d (Iop op args res pc') = Iop op args res pc').
            unfold remove_mv_instr. destruct op; ss. flatten; ss.
            rewrite Pos.eqb_eq in Eq; clarify; ss.
            exfalso; eapply fn_use_def_code; eauto. rewrite H5 in H4. 
            eapply exec_Iop; eauto. unfold subst_instr in H4.
            assert (pc0 <> pc). ii; clarify.
            inv H2; try rewrite PCDEFD in *; clarify. ss.
            flatten H5; clarify. rewrite Pos.eqb_neq in Eq; clarify.
            erewrite value_list_preserved_for_ds_eq.
            erewrite eval_operation_wrapper_preserved; eauto.
            eapply symbols_preserved; eauto. eauto.
            eapply s_inv_eq_ds; eauto.
            ii; clarify; exploit find_mv_not_same; eauto.
          - econstructor; eauto. eapply SSAinv.subj_red; eauto.
            econstructor; eauto. ii. destruct (peq r res).
            clarify. rewrite 2 PMap.gss; eauto. rewrite 2 PMap.gso; eauto.  }
        { destruct (classic (def f d pc)).
          { exists (State st' (transf_function_step f) sp pc' rs' m).
            eapply find_mv_exists in FOUND as FOUND'; eauto. des.
            assert (def f d pc0). econstructor; eauto.
            eapply def_def_eq in H5 as EQ. 3:{ eapply H3. } clarify; ss. split.
            eapply exec_Inop_njp; eauto.
            flatten H4; ss. rewrite Pos.eqb_neq in Eq; clarify.
            rewrite <- join_point_transf_function_step. ii.
            eapply fn_normalized in H; eauto. rewrite FOUND' in H; discriminate.
            eapply successors_instr_succs in FOUND'. des; eauto.
            unfold Kildall.successors_list; rewrite FOUND'. eauto. ss; eauto.
            econstructor; eauto. eapply SSAinv.subj_red; eauto.
            econstructor 2; eauto. ii.
            rewrite PMap.gso; eauto. eauto. }
          { exploit code_preserved_irrelevant; eauto. i. rewrite <- H5 in H4.
            exists (State st' (transf_function_step f) sp pc' rs' # res <- v m).
            split. eapply exec_Iop; eauto. erewrite eval_operation_wrapper_preserved.
            erewrite <- value_list_preserved_for_equiv_regsets; eauto.
            ii; eapply H2; econstructor; eauto.
            eapply symbols_preserved; eauto.
            econstructor; eauto. eapply SSAinv.subj_red; eauto.
            econstructor; eauto. ii. destruct (peq r res).
            clarify; rewrite 2 PMap.gss; eauto.
            rewrite 2 PMap.gso; eauto. } }
      + exists (State st' (transf_function_step f) sp pc' rs' # res <- v m).
        exploit transf_function_step_spec_simple; eauto. i. des.
        exploit H3; eauto. i; clear H2 H3. split.
        destruct (classic (use_code f d pc)).
        { assert (remove_mv_instr d (Iop op args res pc') = Iop op args res pc').
          { unfold remove_mv_instr. flatten; ss. rewrite Pos.eqb_eq in Eq0; clarify.
            eapply find_mv_phicode_exists in FOUND; des.
            exfalso; eapply assigned_code_and_phi; eauto. } rewrite H3 in H4. clear H3.
          eapply find_mv_phicode_exists in FOUND as PHIMOVE; des.
          eapply exec_Iop; eauto. unfold subst_instr in H4.
          erewrite value_list_preserved_for_ds_eq.
          erewrite eval_operation_wrapper_preserved; eauto.
          eapply symbols_preserved; eauto. eauto.
          eapply PHIINV; eauto. rewrite forallb_forall in PHIMOVE1; i; eauto.
          inv H3; eauto. eapply PHIMOVE1 in H5; rewrite Pos.eqb_eq in H5; eauto.
          eapply fn_strict; eauto. econstructor; eauto.
          ii; clarify; eapply no_phi_use_def; eauto.
          ii; clarify; eapply no_phi_use_def; eauto. }
        { eapply find_mv_phicode_exists in FOUND; eauto; des.
          exploit code_preserved_irrelevant; eauto. ii.
          exploit assigned_code_and_phi; eauto. i. rewrite <- H3 in H4.
          eapply exec_Iop; eauto.
          erewrite value_list_preserved_for_equiv_regsets.
          erewrite eval_operation_wrapper_preserved; eauto.
          eapply symbols_preserved; eauto. ii; erewrite EQUIV; eauto.
          ii; eapply H2; eauto. econstructor; eauto. }
        econstructor; eauto. eapply SSAinv.subj_red; eauto.
        econstructor 3; eauto. ii.
        destruct (peq r res);
          clarify; [erewrite 2 PMap.gss | erewrite 2 PMap.gso]; eauto.
        ii. destruct (peq d res); clarify.
        exploit assigned_code_and_phi; eauto. i; ss.
        destruct (peq s0 res); clarify.
        exploit no_phi_use_def'; eauto; ss.
        eapply (@Dom.sdom_dom_pred node peq); eauto. econstructor; eauto.
        ii; clarify. exploit fn_normalized; eauto.
        eapply fn_phicode_inv; eauto. ii; rewrite H2 in *; clarify.
        unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
        rewrite H; ss; eauto. i; rewrite H in *; eauto; clarify.
        econstructor; eauto. rewrite 2 PMap.gso; ss.
        exploit PHIINV; eauto.
        eapply (@Dom.sdom_dom_pred node peq); eauto. econstructor; eauto.
        ii; clarify. exploit fn_normalized; eauto.
        eapply fn_phicode_inv; eauto. ii; rewrite H2 in *; clarify.
        unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
        rewrite H; ss; eauto. i; rewrite H in *; eauto; clarify.
        econstructor; eauto.

    - (* Iload *)
      exists (State st' (transf_function_step f) sp pc' rs' # dst <- v m).
      inv MATCH.
      + rewrite <- H5 in *. exploit transf_function_step_spec_simple; eauto.
        i; des. exploit H3; eauto. clear H3 H4. i. split.
        eapply exec_Iload; eauto. erewrite eval_addressing_preserved; eauto.
        eapply symbols_preserved.
        econstructor 1; eauto. eapply SSAinv.subj_red; eauto.
        rewrite <- H5; econstructor; eauto.
      + exploit transf_function_step_spec_simple; eauto.
        i; des. exploit H4; eauto. clear H3 H4. i.
        eapply find_mv_exists in FOUND as TFCODE; des.
        split. ss. eapply exec_Iload; eauto. erewrite eval_addressing_preserved.
        destruct (classic (use_code f d pc)).
        { erewrite value_list_preserved_for_ds_eq; eauto. inv SINV.
          eapply s_inv_eq_ds; eauto.
          exploit fn_strict; eauto. econstructor; eauto. ii. subst pc0.
          rewrite H in *; clarify.
          ii. exploit find_mv_not_same; eauto. }
        { exploit code_preserved_irrelevant; eauto. ii.
          exploit assigned_code_unique. eauto. eauto. econstructor. eapply TFCODE.
          i; subst pc. rewrite TFCODE in *; clarify. i. ss. rewrite <- H5 in H3.
          inv H5. rewrite <- 2 H7. erewrite value_list_preserved_for_equiv_regsets.
          eauto. ii; rewrite EQUIV; eauto. ii; eapply H4; eauto using use_code. }
        eapply symbols_preserved.
        econstructor; eauto. eapply SSAinv.subj_red; eauto.
        econstructor 2; eauto. ii.
        destruct (peq r dst);
          clarify; [erewrite 2 PMap.gss | erewrite 2 PMap.gso]; eauto.
      + exploit transf_function_step_spec_simple; eauto.
        i; des. exploit H4; eauto. clear H3 H4. i.
        eapply find_mv_phicode_exists in FOUND as PHIMOVE; des.
        split. destruct (classic (use_code f d pc)).
        { ss. eapply exec_Iload; eauto.
          erewrite value_list_preserved_for_ds_eq.
          erewrite eval_addressing_preserved; eauto.
          eapply symbols_preserved; eauto. eauto.
          eapply PHIINV; eauto. rewrite forallb_forall in PHIMOVE1; i; eauto.
          inv H5; eauto. eapply PHIMOVE1 in H6; rewrite Pos.eqb_eq in H6; eauto.
          eapply fn_strict; eauto. econstructor; eauto.
          ii; clarify; eapply no_phi_use_def; eauto.
          ii; clarify; eapply no_phi_use_def; eauto. }
        { exploit code_preserved_irrelevant; eauto. ii.
          exploit assigned_code_and_phi; eauto. i. rewrite <- H5 in H3.
          eapply exec_Iload; eauto.
          erewrite value_list_preserved_for_equiv_regsets.
          erewrite eval_addressing_preserved; eauto.
          eapply symbols_preserved; eauto. ii; erewrite EQUIV; eauto.
          ii; eapply H4; eauto using use_code. }
        econstructor; eauto. eapply SSAinv.subj_red; eauto.
        econstructor 3; eauto. ii.
        destruct (peq r dst);
          clarify; [erewrite 2 PMap.gss | erewrite 2 PMap.gso]; eauto.
        ii. destruct (peq d dst); clarify.
        exploit assigned_code_and_phi; eauto. i; ss.
        assert (pc' <> pc'0).
        { ii; clarify. exploit fn_normalized; eauto.
          eapply fn_phicode_inv; eauto. ii; rewrite H4 in *; clarify.
          unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
          rewrite H; ss; eauto. i; rewrite H in *; eauto; clarify. }
        destruct (peq s0 dst); clarify.
        exploit no_phi_use_def'; eauto; ss.
        eapply (@Dom.sdom_dom_pred node peq); eauto.
        econstructor; eauto. econstructor; eauto.
        rewrite 2 PMap.gso; eauto.
        exploit PHIINV; eauto. eapply (@Dom.sdom_dom_pred node peq); eauto.
        econstructor; eauto. econstructor; eauto.
    
    - (* Istore *)
      exists (State st' (transf_function_step f) sp pc' rs' m').
      inv MATCH.
      + rewrite <- H5 in *. split.
        eapply exec_Istore; eauto. rewrite <- H5; eauto.
        erewrite eval_addressing_preserved; eauto. eapply symbols_preserved.
        econstructor; eauto. eapply SSAinv.subj_red; eauto.
        rewrite <- H5. econstructor; eauto.
      + exploit transf_function_step_spec_simple; eauto.
        i; des. exploit H4; eauto. clear H3 H4. i.
        eapply find_mv_exists in FOUND as TFCODE; des.
        destruct (classic (use_code f d pc)).
        { split. ss. eapply exec_Istore; eauto. erewrite eval_addressing_preserved.
          erewrite value_list_preserved_for_ds_eq; eauto.
          eapply s_inv_eq_ds; eauto.
          exploit fn_strict; eauto. econstructor; eauto. ii. subst pc0.
          rewrite H in *; clarify.
          ii. exploit find_mv_not_same; eauto. eapply symbols_preserved.
          destruct (peq src d); ss.
          - clarify. unfold rename_reg; flatten. rewrite <- EQUIV.
            erewrite <- s_inv_eq_ds; eauto.
            exploit fn_strict; eauto. econstructor; eauto.
            ii; subst pc. rewrite H in *; clarify.
            ii; exploit find_mv_not_same; eauto.
            rewrite Pos.eqb_neq in Eq; clarify.
          - unfold rename_reg; flatten; ss. rewrite Pos.eqb_eq in Eq; clarify.
            rewrite <- EQUIV; ss.
          - econstructor; eauto. eapply SSAinv.subj_red; eauto. econstructor; eauto. }
        { exploit code_preserved_irrelevant; eauto. ii.
          exploit assigned_code_unique. eauto. eauto. econstructor. eapply TFCODE.
          i; subst pc. rewrite TFCODE in *; clarify. i. ss. rewrite <- H5 in H3.
          split. eapply exec_Istore; eauto. erewrite eval_addressing_preserved.
          erewrite value_list_preserved_for_equiv_regsets; eauto.
          ii; rewrite EQUIV; eauto. ii; eapply H4; eauto using use_code.
          eapply symbols_preserved. rewrite <- EQUIV; eauto. ii; clarify.
          eapply H4; eauto using use_code.
          econstructor; eauto. eapply SSAinv.subj_red; eauto.
          econstructor 2; eauto. }
      + exploit transf_function_step_spec_simple; eauto.
        i; des. exploit H4; eauto. clear H3 H4. i.
        eapply find_mv_phicode_exists in FOUND as PHIMOVE; des.
        split. destruct (classic (use_code f d pc)).
        { ss. eapply exec_Istore; eauto.
          erewrite value_list_preserved_for_ds_eq.
          erewrite eval_addressing_preserved; eauto.
          eapply symbols_preserved; eauto. eauto.
          eapply PHIINV; eauto. rewrite forallb_forall in PHIMOVE1; i; eauto.
          inv H5; eauto. eapply PHIMOVE1 in H6; rewrite Pos.eqb_eq in H6; eauto.
          eapply fn_strict; eauto. econstructor; eauto.
          ii; clarify; eapply no_phi_use_def; eauto.
          ii; clarify; eapply no_phi_use_def; eauto.
          destruct (peq src d).
          { clarify. unfold rename_reg. flatten; ss. rewrite <- EQUIV; eauto.
            exploit PHIINV; eauto. i. inv H5; ss. rewrite forallb_forall in PHIMOVE1.
            eapply PHIMOVE1 in H6; rewrite Pos.eqb_eq in H6; eauto.
            exploit fn_strict; eauto. econstructor; eauto.
            ii; clarify; exploit no_phi_use_def; eauto.
            intros ds; rewrite <- ds; eauto.
            ii; clarify; exploit no_phi_use_def; eauto.
            rewrite Pos.eqb_neq in Eq; clarify. }
          { unfold rename_reg. flatten; ss. rewrite Pos.eqb_eq in Eq; clarify.
            rewrite <- EQUIV; eauto. } }
        { exploit code_preserved_irrelevant; eauto. ii.
          exploit assigned_code_and_phi; eauto. i. rewrite <- H5 in H3. clear H5.
          eapply exec_Istore; eauto.
          erewrite value_list_preserved_for_equiv_regsets.
          erewrite eval_addressing_preserved; eauto.
          eapply symbols_preserved; eauto. ii; erewrite EQUIV; eauto.
          ii; eapply H4; eauto using use_code.
          rewrite <- EQUIV; eauto. ii; clarify; eapply H4; eauto using use_code. }
        econstructor; eauto. eapply SSAinv.subj_red; eauto.
        econstructor 3; eauto. ii.
        assert (pc' <> pc'0).
        { ii; clarify. exploit fn_normalized; eauto.
          eapply fn_phicode_inv; eauto. ii; rewrite H4 in *; clarify.
          unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
          rewrite H; ss; eauto. i; rewrite H in *; eauto; clarify. }
        exploit PHIINV; eauto. eapply (@Dom.sdom_dom_pred node peq); eauto.
        econstructor; eauto. econstructor; eauto.

    - (* Icall *)
      inv MATCH.
      + exists (Callstate (Stackframe res (transf_function_step f) sp pc' rs' :: st')
                        (transf_fundef_step fd) rs' ## args m).
        rewrite <- H4 in *. split.
        * rewrite <- H4. eapply exec_Icall; eauto.
          erewrite find_function_translated; eauto. eapply sig_preserved.
        * econstructor; eauto. eapply SSAinv.subj_red; eauto. rewrite H4 at 2.
          econstructor; eauto. rewrite <- H4 in *; econstructor; eauto.
      + exploit transf_function_step_spec_simple; eauto.
        i; des. exploit H3; eauto. clear H1 H3. i.
        eapply find_mv_exists in FOUND as TFCODE; des. ss.
        exists (Callstate (Stackframe res (transf_function_step f) sp pc' rs' :: st')
                          (transf_fundef_step fd)
                          rs' ## (map (rename_reg d s0) args) m). 
        destruct (classic (use_code f d pc)).
        { split. eapply exec_Icall; eauto.
          erewrite find_function_translated; eauto.
          { destruct ros.
            - destruct (peq d r).
              + clarify. unfold rename_fn, rename_reg in *. rewrite Pos.eqb_refl in *.
                simpl ros_to_vos in *.
                repeat rewrite <- EQUIV; eauto.
                erewrite <- s_inv_eq_ds; eauto.
                exploit fn_strict; eauto. econstructor; eauto.
                ii; subst pc0. rewrite H in *; clarify.
                ii; clarify; exploit find_mv_not_same; eauto.
                ii; clarify; exploit find_mv_not_same; eauto.
              + unfold rename_fn, rename_reg. flatten.
                * eapply Pos.eqb_eq in Eq; clarify.
                * simpl ros_to_vos in *.
                  repeat rewrite <- EQUIV; eauto.
            - ss. }
          eapply sig_preserved.
          erewrite value_list_preserved_for_ds_eq. econstructor 2; eauto.
          eapply SSAinv.subj_red; eauto. econstructor; eauto.
          econstructor 2; eauto. eauto. eapply s_inv_eq_ds; eauto.
          exploit fn_strict; eauto. econstructor; eauto.
          ii; subst pc0; clarify. ii; exploit find_mv_not_same; eauto. }
        { split. eapply exec_Icall; eauto.
          erewrite find_function_translated; eauto.
          { destruct ros.
            - destruct (peq d r).
              + clarify. exploit H3; eauto using use_code; ss.
              + unfold rename_fn, rename_reg. flatten.
                * eapply Pos.eqb_eq in Eq; clarify.
                * simpl ros_to_vos in *.
                  repeat rewrite <- EQUIV; eauto.
            - ss. }
          eapply sig_preserved.
          exploit code_preserved_irrelevant; eauto. ii.
          exploit assigned_code_unique. eauto. eauto. econstructor. eauto.
          ii; subst pc0. clarify. i. ss. inv H4. rewrite <- 2 H7.
          exploit value_list_preserved_for_equiv_regsets; eauto.
          2:{ i. rewrite <- H4. econstructor 2; eauto.
              eapply SSAinv.subj_red; eauto. econstructor; eauto.
              econstructor 2; eauto. }
          ii. destruct ros; eapply H3; eauto using use_code. }
      + exploit transf_function_step_spec_simple; eauto; i; des.
        exploit H3; eauto; i. clear H1 H3. ss.
        exists (Callstate (Stackframe res (transf_function_step f) sp pc' rs' :: st')
                          (transf_fundef_step fd)
                          rs' ## (map (rename_reg d s0) args) m).
        eapply find_mv_phicode_exists in FOUND as MVPHI; des.
        destruct (classic (use_code f d pc)).
        * split. eapply exec_Icall; eauto. erewrite find_function_translated; eauto.
          destruct ros.
          { destruct (peq d r).
            - clarify. unfold rename_fn, rename_reg in *. rewrite Pos.eqb_refl in *.
              simpl ros_to_vos in *.
              repeat rewrite <- EQUIV; eauto.
              erewrite <- PHIINV; eauto. i. inv H3; eauto.
              rewrite forallb_forall in MVPHI1; eapply MVPHI1 in H5.
              rewrite Pos.eqb_eq in H5; clarify.
              exploit fn_strict; eauto. econstructor; eauto.
              all : ii; clarify; exploit no_phi_use_def; eauto.
            - unfold rename_fn, rename_reg. flatten.
              + eapply Pos.eqb_eq in Eq; clarify.
              + simpl ros_to_vos in *. repeat rewrite <- EQUIV; eauto. }
            { ss. }
            eapply sig_preserved.
            assert (rs # d = rs # s0).
            { eapply PHIINV; eauto. ii. inv H3; ss. rewrite forallb_forall in MVPHI1.
              eapply MVPHI1 in H5; rewrite Pos.eqb_eq in H5; clarify.
              exploit fn_strict; eauto. econstructor; eauto.
              ii; clarify; exploit no_phi_use_def; eauto. }
            erewrite value_list_preserved_for_ds_eq; eauto.
            econstructor; eauto. eapply SSAinv.subj_red; eauto.
            econstructor; eauto. econstructor 3; eauto.
            ii; clarify; exploit no_phi_use_def; eauto.
        * split.
          { eapply exec_Icall; eauto. erewrite find_function_translated; eauto.
            destruct ros.
            - destruct (peq d r).
              + clarify. exploit H1; eauto using use_code; ss.
              + unfold rename_fn, rename_reg. flatten.
                * eapply Pos.eqb_eq in Eq; clarify.
                * simpl ros_to_vos in *.
                  repeat rewrite <- EQUIV; eauto.
            - ss.
            - eapply sig_preserved. }
          { exploit code_preserved_irrelevant; eauto. ii.
            exploit assigned_code_and_phi; eauto. ii. inv H3; ss. rewrite <- 2 H7.
            exploit value_list_preserved_for_equiv_regsets; eauto.
            2:{ i. rewrite <- H3. econstructor; eauto.
                eapply SSAinv.subj_red; eauto. econstructor; eauto.
                econstructor 3; eauto. ii. exploit PHIINV; eauto.
                eapply (@Dom.sdom_dom_pred node peq); eauto.
                econstructor; eauto. ii; subst pc'0.
                exploit fn_normalized; eauto. exploit fn_phicode_inv; eauto.
                i. rewrite H12. ii. rewrite H13 in H5; clarify.
                unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
                rewrite H; ss. left; ss. i; clarify. econstructor; eauto. }
            ii; eapply H1. destruct ros; eauto using use_code. }
    
    - (* Itailcall *)
      inv MATCH.
      + exists (Callstate st' (transf_fundef_step fd) rs' ## args m').
        rewrite <- H5 in *. split.
        * rewrite <- H5. eapply exec_Itailcall; eauto.
          erewrite find_function_translated; eauto. eapply sig_preserved.
        * econstructor; eauto. eapply SSAinv.subj_red; eauto.
      + exploit transf_function_step_spec_simple; eauto.
        i; des. exploit H4; eauto. clear H1 H4. i.
        eapply find_mv_exists in FOUND as TFCODE; des. ss.
        exists (Callstate st' (transf_fundef_step fd)
                          rs' ## (map (rename_reg d s0) args) m').
        destruct (classic (use_code f d pc)).
        { split. eapply exec_Itailcall; eauto.
          erewrite find_function_translated; eauto.
          { destruct ros.
            - destruct (peq d r).
              + clarify. unfold rename_fn, rename_reg in *. rewrite Pos.eqb_refl in *.
                simpl ros_to_vos in *.
                repeat rewrite <- EQUIV; eauto.
                erewrite <- s_inv_eq_ds; eauto.
                exploit fn_strict; eauto. econstructor; eauto.
                ii; subst pc0. rewrite H in *; clarify.
                all: ii; clarify; exploit find_mv_not_same; eauto.
              + unfold rename_fn, rename_reg. flatten.
                * eapply Pos.eqb_eq in Eq; clarify.
                * simpl ros_to_vos in *.
                  repeat rewrite <- EQUIV; eauto.
            - ss. }
          eapply sig_preserved.
          unfold transf_function_step, transf_function_fuel. flatten; ss.
          erewrite value_list_preserved_for_ds_eq; eauto. econstructor 2; eauto.
          eapply SSAinv.subj_red; eauto. eapply s_inv_eq_ds; eauto.
          exploit fn_strict; eauto. econstructor; eauto.
          ii; subst pc0; clarify. ii; exploit find_mv_not_same; eauto. }
        { split. eapply exec_Itailcall; eauto.
          erewrite find_function_translated; eauto.
          { destruct ros.
            - destruct (peq d r).
              + clarify. exploit H4; eauto using use_code; ss.
              + unfold rename_fn, rename_reg. flatten.
                * eapply Pos.eqb_eq in Eq; clarify.
                * simpl ros_to_vos in *.
                  repeat rewrite <- EQUIV; eauto.
            - ss. }
          eapply sig_preserved.
          unfold transf_function_step, transf_function_fuel; flatten; ss.
          exploit code_preserved_irrelevant; eauto. ii.
          exploit assigned_code_unique. eauto. eauto. econstructor. eauto.
          ii; subst pc0. clarify. i. ss. inv H5. rewrite <- 2 H8.
          erewrite value_list_preserved_for_equiv_regsets; eauto. econstructor 2; eauto.
          eapply SSAinv.subj_red; eauto.
          erewrite <- value_list_preserved_for_equiv_regsets; eauto.
          all: ii; destruct ros; eapply H4; eauto using use_code. }
      + exploit transf_function_step_spec_simple; eauto; i; des.
        exploit H4; eauto; i. clear H1 H4. ss.
        exists (Callstate st' (transf_fundef_step fd)
                          rs' ## (map (rename_reg d s0) args) m').
        eapply find_mv_phicode_exists in FOUND as MVPHI; des.
        destruct (classic (use_code f d pc)).
        * split. eapply exec_Itailcall; eauto.
          erewrite find_function_translated; eauto.
          { destruct ros.
            - destruct (peq d r).
              + clarify. unfold rename_fn, rename_reg in *. rewrite Pos.eqb_refl in *.
                simpl ros_to_vos in *.
                repeat rewrite <- EQUIV; eauto.
                erewrite <- PHIINV; eauto. i. inv H4; eauto.
                rewrite forallb_forall in MVPHI1; eapply MVPHI1 in H6.
                rewrite Pos.eqb_eq in H6; clarify.
                exploit fn_strict; eauto. econstructor; eauto.
                all : ii; clarify; exploit no_phi_use_def; eauto.
              + unfold rename_fn, rename_reg. flatten.
                * eapply Pos.eqb_eq in Eq; clarify.
                * simpl ros_to_vos in *. repeat rewrite <- EQUIV; eauto.
            - ss. }
          eapply sig_preserved.
          unfold transf_function_step, transf_function_fuel. flatten; ss.
          erewrite value_list_preserved_for_ds_eq; eauto. econstructor 2; eauto.
          eapply SSAinv.subj_red; eauto.
          
          eapply PHIINV; eauto. ii. inv H4; ss. rewrite forallb_forall in MVPHI1.
          eapply MVPHI1 in H6; rewrite Pos.eqb_eq in H6; clarify.
          exploit fn_strict; eauto. econstructor; eauto.
          all : ii; clarify; exploit no_phi_use_def; eauto.
        * split.
          { eapply exec_Itailcall; eauto. erewrite find_function_translated; eauto.
            destruct ros.
            - destruct (peq d r).
              + clarify. exploit H1; eauto using use_code; ss.
              + unfold rename_fn, rename_reg. flatten.
                * eapply Pos.eqb_eq in Eq; clarify.
                * simpl ros_to_vos in *.
                  repeat rewrite <- EQUIV; eauto.
            - ss.
            - eapply sig_preserved.
            - unfold transf_function_step, transf_function_fuel; flatten; ss. }
          { exploit code_preserved_irrelevant; eauto. ii.
            exploit assigned_code_and_phi; eauto. ii. inv H4; ss. rewrite <- 2 H8.
            exploit value_list_preserved_for_equiv_regsets; eauto.
            2:{ i. rewrite <- H4. econstructor; eauto.
                eapply SSAinv.subj_red; eauto. }
            ii; eapply H1. destruct ros; eauto using use_code. }
      
    - (* Ibuiltin *)
      exists (State st' (transf_function_step f) sp pc'
                    (regmap_setres res vres rs') m').
      inv MATCH.
      + rewrite <- H5 in *. split.
        * rewrite <- H5. eapply exec_Ibuiltin; eauto.
          eapply eval_builtin_args_preserved. eapply symbols_preserved.
          eapply H0. eapply external_call_symbols_preserved; eauto.
          eapply senv_equiv.
        * econstructor; eauto. eapply SSAinv.subj_red; eauto.
          rewrite <- H5. econstructor; eauto.
      + exploit transf_function_step_spec_simple; eauto; i; des.
        exploit H4; eauto; i. clear H3 H4. ss.
        eapply find_mv_exists in FOUND as MVCODE; des. split.
        * eapply exec_Ibuiltin; eauto.
          2:{ eapply external_call_symbols_preserved. eapply senv_equiv.
              eapply H1. }
          destruct (classic (use_code f d pc)).
          { eapply eval_builtin_args_preserved_for_ds_eq; eauto.
            ii; exploit find_mv_not_same; eauto. exploit s_inv_eq_ds; eauto.
            exploit fn_strict; eauto. econstructor; eauto.
            ii; subst pc0; ss. clarify. }
          { eapply eval_builtin_args_preserved_for_equiv_regset; eauto.
            ii; eapply H3; eauto using use_code.
            ii; exploit find_mv_not_same; eauto. }
        * econstructor; eauto. eapply SSAinv.subj_red; eauto.
          econstructor 2; eauto. destruct res; ss. ii.
          destruct (peq r x).
          { clarify. rewrite 2 PMap.gss; eauto. }
          { rewrite 2 PMap.gso; eauto. }
      + exploit transf_function_step_spec_simple; eauto; i; des.
        exploit H4; eauto; i. clear H3 H4. ss.
        eapply find_mv_phicode_exists in FOUND as MVPHI; des. split.
        * destruct (classic (use_code f d pc)).
          { eapply exec_Ibuiltin; eauto.
            eapply eval_builtin_args_preserved_for_ds_eq; eauto.
            ii; clarify; exploit no_phi_use_def; eauto.
            exploit PHIINV; eauto. ii. inv H4; ss. rewrite forallb_forall in MVPHI1.
            eapply MVPHI1 in H6; rewrite Pos.eqb_eq in H6; clarify; ss.
            exploit fn_strict; eauto. econstructor; eauto.
            ii; clarify; exploit no_phi_use_def; eauto.
            eapply external_call_symbols_preserved; eauto. eapply senv_equiv; eauto. }
          { eapply exec_Ibuiltin; eauto.
            eapply eval_builtin_args_preserved_for_equiv_regset; eauto.
            ii; eapply H3; eauto using use_code.
            ii; clarify; exploit no_phi_use_def; eauto.
            eapply external_call_symbols_preserved; eauto. eapply senv_equiv; eauto. }
        * econstructor; eauto. eapply SSAinv.subj_red; eauto.
          econstructor 3; eauto. destruct res; ss. ii.
          destruct (peq r x).
          { clarify. rewrite 2 PMap.gss; eauto. } { rewrite 2 PMap.gso; eauto. }
          ii. assert (dom f pc'0 pc).
          { eapply (@Dom.sdom_dom_pred node peq); eauto. econstructor; eauto.
            ii; subst pc'0. exploit fn_normalized; eauto. exploit fn_phicode_inv; eauto.
            intros JF; rewrite JF. ii. rewrite H9 in H3; clarify.
            unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
            rewrite H; ss. eauto. i; clarify. econstructor; eauto. }
          ii. destruct res; ss. destruct (peq x d).
          { clarify. exploit assigned_code_and_phi; eauto; ss. }
          destruct (peq x s0).
          { clarify. exploit no_phi_use_def'; eauto. ss. }
          rewrite 2 PMap.gso; eauto.
          exploit PHIINV; eauto. exploit PHIINV; eauto.

    - (* Icond, true *)
      exists (State st' (transf_function_step f) sp ifso rs' m).
      split.
      + inv MATCH.
        * rewrite <- H4 in *. eapply exec_Icond_true; eauto. rewrite <- H4; eauto.
        * exploit transf_function_step_spec_simple; eauto.
          i; des. exploit H3; eauto; i; ss. clear H2 H3.
          eapply find_mv_exists in FOUND as MVCODE; des.
          assert (pc <> pc0).
          { ii; subst pc0. clarify. }
          eapply exec_Icond_true; eauto.
          destruct (classic (use_code f d pc)).
          { erewrite value_list_preserved_for_ds_eq; eauto.
            exploit s_inv_eq_ds; eauto. exploit fn_strict; eauto. econstructor; eauto.
            ii; exploit find_mv_not_same; eauto. }
          { exploit code_preserved_irrelevant; eauto. ii. exploit assigned_code_unique.
            eauto. eauto. econstructor; eauto. ss.
            i. inv H5. rewrite <- 2 H7.
            erewrite value_list_preserved_for_equiv_regsets; eauto.
            ii; rewrite EQUIV; eauto.
            ii; eapply H3; eauto using use_code. }
        * exploit transf_function_step_spec_simple; eauto.
          i; des; exploit H3; eauto; i; ss; clear H2 H3.
          eapply find_mv_phicode_exists in FOUND as MVPHI; des.
          eapply exec_Icond_true; eauto.
          destruct (classic (use_code f d pc)).
          { erewrite value_list_preserved_for_ds_eq; eauto.
            exploit PHIINV; eauto. i. inv H3; ss. rewrite forallb_forall in MVPHI1.
            eapply MVPHI1 in H5; rewrite Pos.eqb_eq in H5; clarify.
            exploit fn_strict; eauto. econstructor; eauto.
            ii; clarify; exploit no_phi_use_def; eauto. 
            ii; clarify; exploit no_phi_use_def; eauto. }
          { exploit code_preserved_irrelevant; eauto. ii.
            exploit assigned_code_and_phi; eauto.
            i. inv H3. rewrite <- 2 H6.
            erewrite value_list_preserved_for_equiv_regsets; eauto.
            ii; rewrite EQUIV; eauto.
            ii; eapply H2; eauto using use_code. }
      + econstructor; eauto. eapply SSAinv.subj_red; eauto.
        inv MATCH.
        * rewrite <- 2 H4 in *. econstructor; eauto.
        * econstructor 2; eauto.
        * econstructor 3; eauto. ii.
          exploit PHIINV; eauto. eapply (@Dom.sdom_dom_pred node peq); eauto.
          econstructor; eauto. ii; subst ifso. exploit fn_normalized; eauto.
          exploit fn_phicode_inv; eauto.
          intros JF; rewrite JF; intros PHI; rewrite PHI in *; clarify.
          unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
          rewrite H; ss. eauto. i; clarify. econstructor; eauto.
      
    - (* Icond, false *)
      exists (State st' (transf_function_step f) sp ifnot rs' m).
      split.
      + inv MATCH.
        * rewrite <- H4 in *. eapply exec_Icond_false; eauto. rewrite <- H4; eauto.
        * exploit transf_function_step_spec_simple; eauto.
          i; des. exploit H3; eauto; i; ss. clear H2 H3.
          eapply find_mv_exists in FOUND as MVCODE; des.
          assert (pc <> pc0).
          { ii; subst pc0. clarify. }
          eapply exec_Icond_false; eauto.
          destruct (classic (use_code f d pc)).
          { erewrite value_list_preserved_for_ds_eq; eauto.
            exploit s_inv_eq_ds; eauto. exploit fn_strict; eauto. econstructor; eauto.
            ii; exploit find_mv_not_same; eauto. }
          { exploit code_preserved_irrelevant; eauto. ii. exploit assigned_code_unique.
            eauto. eauto. econstructor; eauto. ss.
            i. inv H5. rewrite <- 2 H7.
            erewrite value_list_preserved_for_equiv_regsets; eauto.
            ii; rewrite EQUIV; eauto.
            ii; eapply H3; eauto using use_code. }
        * exploit transf_function_step_spec_simple; eauto.
          i; des; exploit H3; eauto; i; ss; clear H2 H3.
          eapply find_mv_phicode_exists in FOUND as MVPHI; des.
          eapply exec_Icond_false; eauto.
          destruct (classic (use_code f d pc)).
          { erewrite value_list_preserved_for_ds_eq; eauto.
            exploit PHIINV; eauto. i. inv H3; ss. rewrite forallb_forall in MVPHI1.
            eapply MVPHI1 in H5; rewrite Pos.eqb_eq in H5; clarify.
            exploit fn_strict; eauto. econstructor; eauto.
            ii; clarify; exploit no_phi_use_def; eauto. 
            ii; clarify; exploit no_phi_use_def; eauto. }
          { exploit code_preserved_irrelevant; eauto. ii.
            exploit assigned_code_and_phi; eauto.
            i. inv H3. rewrite <- 2 H6.
            erewrite value_list_preserved_for_equiv_regsets; eauto.
            ii; rewrite EQUIV; eauto.
            ii; eapply H2; eauto using use_code. }
      + econstructor; eauto. eapply SSAinv.subj_red; eauto.
        inv MATCH.
        * rewrite <- 2 H4 in *. econstructor; eauto.
        * econstructor 2; eauto.
        * econstructor 3; eauto. ii.
          exploit PHIINV; eauto. eapply (@Dom.sdom_dom_pred node peq); eauto.
          econstructor; eauto. ii; subst ifnot. exploit fn_normalized; eauto.
          exploit fn_phicode_inv; eauto.
          intros JF; rewrite JF; intros PHI; rewrite PHI in *; clarify.
          unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
          rewrite H; ss. eauto. i; clarify. econstructor; eauto.

    - (* Ijumptable *)
      exists (State st' (transf_function_step f) sp pc' rs' m).
      split.
      + inv MATCH.
        * rewrite <- 2 H5 in *. eapply exec_Ijumptable; eauto.
        * eapply find_mv_exists in FOUND as MVCODE; des.
          exploit transf_function_step_spec_simple. eapply H. i; des.
          exploit H4; eauto; i; ss; clear H3 H4.
          destruct (classic (use_code f d pc)).
          { eapply exec_Ijumptable; eauto. destruct (peq d arg).
            { clarify. unfold rename_reg; flatten; ss.
              - rewrite <- EQUIV; eauto.
                exploit s_inv_eq_ds; eauto. exploit fn_strict; eauto.
                econstructor; eauto.
                ii; subst pc0; clarify. i. rewrite <- H4; ss.
                ii; exploit find_mv_not_same; eauto.
              - rewrite Pos.eqb_neq in Eq; clarify.  }
            { unfold rename_reg; flatten.
              - rewrite Pos.eqb_eq in Eq; clarify.
              - rewrite <- EQUIV; eauto. } }
          { eapply exec_Ijumptable; eauto. unfold rename_reg; flatten.
            - rewrite Pos.eqb_eq in Eq; clarify. exfalso; eapply H3; eauto using use_code.
            - rewrite Pos.eqb_neq in Eq. rewrite <- EQUIV; eauto. }
        * exploit transf_function_step_spec_simple; eauto.
          i; des; exploit H4; eauto; i; ss; clear H3 H4.
          eapply find_mv_phicode_exists in FOUND as MVPHI; des.
          eapply exec_Ijumptable; eauto.
          destruct (classic (use_code f d pc)).
          { destruct (peq d arg).
            { clarify. unfold rename_reg; flatten; ss.
              - rewrite <- EQUIV; eauto.
                exploit PHIINV; eauto. i. inv H4; ss. rewrite forallb_forall in MVPHI1.
                eapply MVPHI1 in H6; rewrite Pos.eqb_eq in H6; clarify.
                exploit fn_strict; eauto. econstructor; eauto.
                ii; clarify; exploit no_phi_use_def; eauto. i; rewrite <- H4; ss.
                ii; clarify; exploit no_phi_use_def; eauto.
              - rewrite Pos.eqb_neq in Eq; clarify.  }
            { unfold rename_reg; flatten.
              - rewrite Pos.eqb_eq in Eq; clarify.
              - rewrite <- EQUIV; eauto. } }
          { exploit code_preserved_irrelevant; eauto. ii.
            exploit assigned_code_and_phi; eauto.
            i. inv H4. rewrite <- 2 H7. rewrite <- EQUIV; eauto.
            ii; clarify; eapply H3; eauto using use_code. }
      + econstructor; eauto. eapply SSAinv.subj_red; eauto.
        inv MATCH.
        * rewrite <- 2 H5 in *. econstructor; eauto.
        * econstructor 2; eauto.
        * econstructor 3; eauto. ii.
          exploit PHIINV; eauto. eapply (@Dom.sdom_dom_pred node peq); eauto.
          econstructor; eauto. ii; subst pc'0. exploit fn_normalized; eauto.
          exploit fn_phicode_inv; eauto.
          intros JF; rewrite JF; intros PHI; rewrite PHI in *; clarify.
          unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
          rewrite H; ss. eapply list_nth_z_in; eauto. i; clarify. econstructor; eauto.
          ss. eapply list_nth_z_in; eauto.
          
    - (* Ireturn *)
      inv MATCH.
      + exists (Returnstate st' (regmap_optget or Vundef rs') m').
        rewrite <- 2 H4 in *. split.
        * eapply exec_Ireturn; eauto.
        * econstructor; eauto. eapply SSAinv.subj_red; eauto.
      + eapply find_mv_exists in FOUND as MVCODE; des.
        exploit transf_function_step_spec_simple. eapply H. eauto; i; des.
        exploit H3; eauto; i; ss; clear H2 H3.
        exists (Returnstate st'
                            (regmap_optget (option_map (rename_reg d s0) or) Vundef rs')
                            m').
        split.
        * eapply exec_Ireturn; eauto.
          unfold transf_function_step, transf_function_fuel; flatten; ss.
        * destruct or; ss.
          { destruct (classic (use_code f d pc)).
            { inv H2; clarify. unfold rename_reg; flatten; ss.
              exploit s_inv_eq_ds; eauto. exploit fn_strict; eauto.
              econstructor; eauto using use_code.
              ii; subst pc0; clarify. i. rewrite <- EQUIV. rewrite <- H.
              econstructor; eauto. eapply SSAinv.subj_red; eauto.
              ii; clarify; exploit find_mv_not_same; eauto.
              rewrite Pos.eqb_neq in Eq; clarify. }
            { unfold rename_reg; flatten; ss.
              - rewrite Pos.eqb_eq in Eq; clarify; exfalso;
                  eapply H2; eauto using use_code.
              - rewrite Pos.eqb_neq in Eq. rewrite <- EQUIV; eauto.
                econstructor; eauto. eapply SSAinv.subj_red; eauto. } }
          { econstructor; eauto. eapply SSAinv.subj_red; eauto. }
      + eapply find_mv_phicode_exists in FOUND as MVPHI; des.
        exploit transf_function_step_spec_simple. eapply H. eauto; i; des.
        exploit H3; eauto; i; ss; clear H2 H3.
        exists (Returnstate st'
                            (regmap_optget (option_map (rename_reg d s0) or) Vundef rs')
                            m').
        split.
        * eapply exec_Ireturn; eauto.
          unfold transf_function_step, transf_function_fuel; flatten; ss.
        * destruct or; ss.
          { destruct (classic (use_code f d pc)).
            { inv H2; clarify. unfold rename_reg; flatten; ss.
              exploit PHIINV; eauto. i. inv H; ss. rewrite forallb_forall in MVPHI1.
              eapply MVPHI1 in H2; rewrite Pos.eqb_eq in H2; clarify.
              exploit fn_strict; eauto. econstructor; eauto using use_code.
              ii; clarify; exploit no_phi_use_def; eauto.
              i. rewrite <- EQUIV. rewrite <- H. econstructor; eauto.
              eapply SSAinv.subj_red; eauto. ii; clarify; exploit no_phi_use_def; eauto.
              rewrite Pos.eqb_neq in Eq; clarify. }
            { unfold rename_reg; flatten; ss.
              - rewrite Pos.eqb_eq in Eq; clarify; exfalso;
                  eapply H2; eauto using use_code.
              - rewrite Pos.eqb_neq in Eq. rewrite <- EQUIV; eauto.
                econstructor; eauto. eapply SSAinv.subj_red; eauto. } }
          { econstructor; eauto. eapply SSAinv.subj_red; eauto. }

    - (* internal *)
      ss.
      exists (State st (transf_function_step f) (Vptr stk Ptrofs.zero)
                    (fn_entrypoint (transf_function_step f))
                    (init_regs args (fn_params (transf_function_step f))) m').
      split.
      + eapply exec_function_internal; eauto.
        unfold transf_function_step, transf_function_fuel; flatten; ss.
      + assert (fn_entrypoint (transf_function_step f) = fn_entrypoint f).
        { unfold transf_function_step, transf_function_fuel; flatten; ss. }
        assert (fn_params (transf_function_step f) = fn_params f).
        { unfold transf_function_step, transf_function_fuel; flatten; ss. }
        rewrite H1, H2. clear H1 H2. econstructor; eauto.
        eapply SSAinv.subj_red; eauto.
        assert (transf_function_step f = transf_function_step f) by auto.
        unfold transf_function_step at 2 in H1.
        unfold transf_function_fuel in H1. ss. flatten H1.
        * econstructor 2; eauto. ii; ss.
        * econstructor 3; eauto. ii; ss.
          ii. eapply Dom.dom_entry in H5. clarify.
          exploit no_assigned_phi_spec_fn_entrypoint; eauto. inv SINV; inv WFF; ss.
          i; ss. eapply Pos.eq_dec.
        * rewrite H1. destruct f; ss. econstructor 1; eauto.
        
    - (* external *)
      exists (Returnstate st res m'). split.
      eapply exec_function_external; eauto.
      eapply external_call_symbols_preserved; eauto. eapply senv_equiv.
      econstructor; eauto. eapply SSAinv.subj_red; eauto. 

    - (* return *)
      inv STACK. eexists. split.
      eapply exec_return.
      econstructor; eauto. eapply SSAinv.subj_red; eauto.
      inv MATCH.
      + rewrite <- 2 H2 in *. econstructor; eauto.
      + econstructor 2; eauto. ii. destruct (peq r res).
        clarify. rewrite 2 PMap.gss; eauto.
        rewrite 2 PMap.gso; eauto.
      + econstructor 3; eauto.
        * ii. destruct (peq r res).
          clarify. rewrite 2 PMap.gss; eauto. rewrite 2 PMap.gso; eauto.
        * ii. eapply find_mv_phicode_exists in FOUND as MVPHI; des; eauto.
          assert (pc' = pc0). { eapply def_def_eq; eauto. } clarify.
          destruct (peq res d).
          { clarify. exploit assigned_code_and_phi; eauto. ss. }
          destruct (peq res s0).
          { clarify. exploit no_phi_use_def'. eauto. eapply MVPHI. eauto.
            i. inv H0; ss. rewrite forallb_forall in MVPHI1. eapply MVPHI1 in H5.
            rewrite Pos.eqb_eq in H5; ss. eauto.
            eapply (@Dom.sdom_dom_pred node peq); eauto.
            econstructor; eauto. ii; subst pc0; clarify.
            exploit fn_normalized; eauto. exploit fn_phicode_inv; eauto.
            intros JP; rewrite JP; ii. rewrite H0 in MVPHI; clarify.
            unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
            rewrite PREDINFO; ss. eauto. i; clarify. econstructor; eauto. ss. }
          rewrite 2 PMap.gso; eauto.
    Unshelve. eauto. eauto. eauto.
  Qed. *)


  Lemma match_states_bsim
      s1
      (EXT: SSA.is_external ge s1)
      s2 t s2'
      (IBIND: ge_binded_state tge s2 gmtgt)
      (STEPTGT: Step (SSA.semantics tprog) s2 t s2')
      (MATCH: match_states s1 s2)
      (SAFESRC: safe (SSA.semantics prog) s1)
  :
    (exists s1', Step (SSA.semantics prog) s1 t s1' /\ match_states s1' s2')
    \/ (~ trace_intact t /\ exists s1'' t', Step (SSA.semantics prog) s1 t' s1''
       /\ exists tl, t' = Eapp (trace_cut_pterm t) tl).
  Proof.
    assert (Hwf1: forall s f sp pc rs m, s_inv ge (State s f sp pc rs m) ->
      wf_ssa_function f) by (intros s f sp pc rs m H; inv H; auto).
    assert (SEQUIV: Senv.equiv tge ge) by (symmetry; eapply senv_equiv).
    unfold safe in SAFESRC. specialize (SAFESRC _ (star_refl _ _ _)). des; cycle 2; clarify.
    { inv SAFESRC; ss. }
    unfold SSA.is_external in *. inv MATCH; des_ifs.
    - inv MATCH0.
      + inv STEPTGT; rewrite <- H1 in *; clarify.
        left. esplits; eauto. econs; eauto.
        eapply eval_builtin_args_preserved in H9 as HT; eauto using symbols_preserved.
        eapply external_call_symbols_preserved in H10 as HTC; eauto.
        rewrite H1 at 2. econs; eauto.
        eapply SSAinv.subj_red; eauto. econs; eauto.
        eapply eval_builtin_args_preserved. i. rewrite symbols_preserved; eauto.
        unfold tge. ss. eapply H9.
        eapply external_call_symbols_preserved; eauto.
        rewrite <- H1. econs; eauto.
      + exploit transf_function_step_spec_simple; i; des; eauto.
        exploit H0; i; des; eauto. clear H H0.
        eapply find_mv_exists in FOUND as FOUND'; des. inv STEPTGT; clarify.
        left.
        destruct (classic (use_code f d pc)).
        * assert (eval_builtin_args ge (fun r => rs # r) sp m l vargs).
          { exploit eval_builtin_args_preserved_for_ds_eq.
            eauto. ii; exploit find_mv_not_same; eauto.
            eapply s_inv_eq_ds; eauto. exploit fn_strict; eauto. econs; eauto.
            ii; clarify. i. rewrite H0. eauto. }
          assert (external_call e ge vargs m t vres m').
          { exploit external_call_symbols_preserved; eauto. }
          esplits; eauto. econs; eauto. econs; eauto.
          eapply SSAinv.subj_red; eauto. econs; eauto. econs; eauto.
          ii. induction b; ss; eauto.
          destruct (peq r x); clarify.
          repeat rewrite PMap.gss; eauto. repeat rewrite PMap.gso; eauto.
        * assert (eval_builtin_args ge (fun r => rs # r) sp m l vargs).
          { exploit eval_builtin_args_preserved_for_equiv_regset; eauto.
            ii; eapply H; eauto using use_code. ii; exploit find_mv_not_same; eauto.
            i. rewrite H0. eauto. }
          assert (external_call e ge vargs m t vres m').
          { exploit external_call_symbols_preserved; eauto. }
          esplits; eauto. econs; eauto. econs; eauto.
          eapply SSAinv.subj_red; eauto. econs; eauto. econs; eauto.
          ii. induction b; ss; eauto.
          destruct (peq r x); clarify.
          repeat rewrite PMap.gss; eauto. repeat rewrite PMap.gso; eauto.
      + exploit transf_function_step_spec_simple; i; des; eauto.
        exploit H0; i; des; eauto. clear H H0.
        eapply find_mv_phicode_exists in FOUND as FOUND'; des. inv STEPTGT; clarify.
        left. destruct (classic (use_code f d pc)).
        * assert (eval_builtin_args ge (fun r => rs # r) sp m l vargs).
          { exploit eval_builtin_args_preserved_for_ds_eq.
            eauto. ii; clarify; exploit no_phi_use_def; eauto.
            rewrite H0 in FOUND; eauto.
            exploit PHIINV; eauto. i. inv H0; eauto.
            eapply forallb_forall in FOUND'1; eauto. eapply Pos.eqb_eq in FOUND'1; clarify.
            exploit fn_strict; eauto. econs; eauto.
            ii; clarify. exploit no_phi_use_def; eauto. i. rewrite H0. eauto. }
          assert (external_call e ge vargs m t vres m').
          { exploit external_call_symbols_preserved; eauto. }
          esplits; eauto. econs; eauto. econs; eauto.
          eapply SSAinv.subj_red; eauto. econs; eauto.
          econs 3; eauto.
          { induction b; ss. ii. destruct (peq x r).
            - clarify. repeat rewrite PMap.gss; eauto.
            - repeat rewrite PMap.gso; eauto. }
          ii. assert (dom f pc' pc).
          { eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto.
            ii; clarify. exploit fn_normalized; eauto. exploit fn_phicode_inv; eauto.
            intros JF; rewrite JF. ii. rewrite H7 in H2; clarify.
            unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
            rewrite Heq; ss. eauto. i; clarify. econstructor; eauto. }
          induction b; exploit PHIINV; i; eauto. ss.
          destruct (peq x d).
          { clarify. exploit assigned_code_and_phi; eauto; ss. }
          destruct (peq x s).
          { clarify. exploit no_phi_use_def'; eauto. ss. }
          rewrite 2 PMap.gso; eauto.
        * assert (eval_builtin_args ge (fun r => rs # r) sp m l vargs).
          { exploit eval_builtin_args_preserved_for_equiv_regset; eauto.
            ii; eapply H; eauto using use_code.
            ii; clarify; exploit no_phi_use_def; eauto.
            rewrite H0 in FOUND; eauto. i. rewrite H0. eauto. }
          assert (external_call e ge vargs m t vres m').
          { exploit external_call_symbols_preserved; eauto. }
          esplits; eauto. econs; eauto. econs; eauto.
          eapply SSAinv.subj_red; eauto. econs; eauto.
          econs 3; eauto.
          { induction b; ss. ii. destruct (peq x r).
            - clarify. repeat rewrite PMap.gss; eauto.
            - repeat rewrite PMap.gso; eauto. }
          ii. assert (dom f pc' pc).
          { eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto.
            ii; clarify. exploit fn_normalized; eauto. exploit fn_phicode_inv; eauto.
            intros JF; rewrite JF. ii. rewrite H7 in H2; clarify.
            unfold Kildall.successors_list, successors. rewrite PTree.gmap1.
            rewrite Heq; ss. eauto. i; clarify. econstructor; eauto. }
          induction b; exploit PHIINV; i; eauto. ss.
          destruct (peq x d).
          { clarify. exploit assigned_code_and_phi; eauto; ss. }
          destruct (peq x s).
          { clarify. exploit no_phi_use_def'; eauto. ss. }
          rewrite 2 PMap.gso; eauto.
    - inv SAFESRC; des; des_ifs. inv STEPTGT; des; des_ifs; clarify.
      left; esplits; eauto. econs; eauto.
      eapply external_call_symbols_preserved in H6; eauto.
      econs; eauto. eapply SSAinv.subj_red; eauto.
      econs. eapply external_call_symbols_preserved; eauto.
  Qed.

  Lemma match_states_xsim
      st_src0 st_tgt0 (IBIND: ge_binded_state tge st_tgt0 gmtgt) (MATCH: match_states st_src0 st_tgt0):
    xsim (SSA.semantics prog) (SSA.semantics tprog) (fun _ => None) lt 0%nat st_src0 st_tgt0.
  Proof.
    assert (Hwf1: forall s f sp pc rs m, s_inv ge (State s f sp pc rs m) ->
    wf_ssa_function f) by (intros s f sp pc rs m H; inv H; auto).
    generalize dependent st_src0. generalize dependent st_tgt0.
    pcofix CIH. i. pfold.
    destruct (classic (SSA.is_external ge st_src0)); cycle 1.
    (* not external *)
    - left. econs. econs.
      + i. exploit step_simulation; eauto. i. des; esplits; eauto.
        { eapply tr_rel_eq. }
        left. split.
        { eapply plus_one; eauto. }
        { eapply semantics_receptive_at; auto. }
        right. eapply CIH; eauto.
        { inv H0. ss. eapply ge_binded_state_step; eauto. }
      + ii. eapply final_state_determ; eauto.
        inv FINALSRC. inv MATCH. inv STACK. econs.
      (* + eauto. *)
    (* external *)
    - right. econs; eauto. i. econs; eauto.
      + i. exploit match_states_bsim; eauto. i. des.
        * left. esplits; eauto.
          { eapply tr_rel_eq. }
          left. eapply plus_one. eauto.
          right. eapply CIH; eauto.
          { ss. eapply ge_binded_state_step; eauto. }
        * right. esplits; eauto.
          { eapply star_one. eauto. }
          { subst. eapply tr_rel_eq. }
      + ii. inv FINALTGT. inv MATCH. unfold SSA.is_external in H. ss.
      + i. specialize (SAFESRC _ (star_refl _ _ _)). des; cycle 2; clarify.
        { inv SAFESRC; ss. }
        right. inv MATCH; ss; des_ifs; inv SAFESRC; unfold ge in *; clarify.
        * inv MATCH0.
          { esplits. rewrite <- 2 H2. eapply exec_Ibuiltin; eauto.
            eapply eval_builtin_args_preserved in H9; eauto.
            i; exploit symbols_preserved; eauto.
            eapply external_call_symbols_preserved in H10; eauto.
            eapply senv_equiv. }
          { exploit transf_function_step_spec_simple; eauto; i; des.
            exploit H1; eauto; i; des. clear H0 H1.
            eapply find_mv_exists in FOUND as FOUND'; des. ss. esplits; eauto.
            destruct (classic (use_code f d pc)).
            - eapply exec_Ibuiltin; eauto.
              eapply eval_builtin_args_preserved_for_ds_eq; eauto.
              ii; clarify; exploit find_mv_not_same; eauto.
              eapply s_inv_eq_ds; eauto. exploit fn_strict; eauto. econs; eauto.
              ii; clarify.
              eapply external_call_symbols_preserved; eauto.
              eapply senv_equiv; eauto.
            - eapply exec_Ibuiltin; eauto.
              eapply eval_builtin_args_preserved_for_equiv_regset; eauto.
              ii; eapply H0; eauto using use_code.
              ii; clarify; exploit find_mv_not_same; eauto.
              eapply external_call_symbols_preserved; eauto. eapply senv_equiv. }
          { exploit transf_function_step_spec_simple; eauto; i; des.
            exploit H1; eauto; i; des. clear H0 H1.
            eapply find_mv_phicode_exists in FOUND as FOUND'; des. ss. esplits; eauto.
            destruct (classic (use_code f d pc)).
            - eapply exec_Ibuiltin; eauto.
              eapply eval_builtin_args_preserved_for_ds_eq; eauto.
              ii; clarify; exploit no_phi_use_def; eauto.
              eapply PHIINV; eauto. i. inv H1; eauto.
              eapply forallb_forall in FOUND'1; eauto. rewrite Pos.eqb_eq in FOUND'1; eauto.
              exploit fn_strict; eauto. econs; eauto.
              ii; clarify; exploit no_phi_use_def; eauto.
              eapply external_call_symbols_preserved; eauto.
              eapply senv_equiv; eauto.
            - eapply exec_Ibuiltin; eauto.
              eapply eval_builtin_args_preserved_for_equiv_regset; eauto.
              ii; eapply H0; eauto using use_code.
              ii; clarify; exploit no_phi_use_def; eauto.
              eapply external_call_symbols_preserved; eauto. eapply senv_equiv. }
        * esplits; econs. eapply external_call_symbols_preserved; eauto. eapply senv_equiv.
          (* Unshelve. econs. *)
  Qed.

  End STEPSIM.
  
  Lemma same_public:
    prog_public prog = prog_public tprog.
  Proof. inv TRANSL. des; eauto. Qed.

  Lemma non_static_equiv l:
    Genv.non_static_glob (Genv.globalenv prog) l = Genv.non_static_glob (Genv.globalenv tprog) l.
  Proof.
    induction l; ss.
    unfold Genv.public_symbol. rewrite symbols_preserved. unfold ge.
    des_ifs.
    - rewrite IHl. eauto.
    - rewrite Genv.globalenv_public in *. rewrite same_public in Heq. clarify.
    - rewrite Genv.globalenv_public in *. rewrite same_public in Heq. clarify.
Qed.

  Lemma transf_initial_capture
    S1 S2 S2'
    (INITSRC: SSA.initial_state prog S1)
    (INITTGT: SSA.initial_state tprog S2)
    (MATCH: match_states S1 S2)
    (CAPTGT: SSA.glob_capture tprog S2 S2'):
  exists S1',
    SSA.glob_capture prog S1 S1' /\ match_states S1' S2'.
  Proof.
    inv CAPTGT. ss.
    rewrite Genv.globalenv_public in CAPTURE.
    rewrite <- same_public in CAPTURE. erewrite <- non_static_equiv in CAPTURE.
    inv MATCH. inv STACK.
    esplits.
    - econs; eauto. rewrite Genv.globalenv_public. eauto.
    - econs; eauto.
      + inv SINV. econs; eauto.
      + econs.
  Qed.

  Lemma match_states_concrete
      s1 s2
      (MATCH: match_states s1 s2):
    (Mem.mem_concrete (state_mem s1)) = (Mem.mem_concrete (state_mem s2)).
  Proof. inv MATCH; ss. Qed.
  
  Theorem transf_program_step_correct:
    mixed_simulation (SSA.semantics prog) (SSA.semantics tprog).
  Proof.
    econs. econs.
    - apply lt_wf.
    - rr. i. exists (S a). lia.
    - econs. i. exploit transf_initial_states; eauto. i. des.
      exists st2. split.
      (* initial state *)
      + econs; eauto. eapply initial_state_determ.
      (* mixed sim *) 
      + r. ii. exploit transf_initial_capture; eauto. i. des. esplits; eauto.
        { subst. ss. rr. i. unfold SSA.concrete_snapshot in *.
          destruct senv_equiv. des. erewrite H5, H4; eauto.
          erewrite <- match_states_concrete; eauto. }
        exploit match_states_xsim; eauto.
        { eapply initial_capture_binded; eauto. }
        i. instantiate (1:=0).
        eapply xsim_mon_rel in H3; eauto; cycle 1.
        { instantiate (1:=gmtgt0). ii. clarify. }
        { instantiate (1:= fun x => x). ii. eauto. }
        ss.
    - i. apply senv_equiv.
  Qed.

End CORRECTNESS_STEP.

Section CORRECTNESS.

  Variable prog: program.
  Variable tprog: program.
  Hypothesis TRANSL : match_prog prog tprog.
  Hypothesis HWF : wf_ssa_program prog.

  Lemma match_prog_wf_ssa : wf_ssa_program tprog.
  Proof. 
    red. intros.
    red in HWF.
    inv TRANSL.
    intuition. revert H0 H HWF.
    induction 1; intros.
    - inv H.
    - inv H1.      
      + inv H. inv H4.
        destruct f1 ; simpl in * ; try constructor; auto.
        exploit (HWF (Internal f) id); eauto.
        destruct a1, g; simpl in * ; try congruence. 
        left. inv H; simpl in *; auto. 
        intros. inv H4; auto.
        apply transf_function_preserve_wf_ssa_function; auto.
      + eapply IHlist_forall2; eauto.
  Qed.

  Lemma tprog_transf: tprog = transf_program prog.
  Proof.
    assert (FORALL2_MAP: forall prog l l',
            list_forall2
              (match_ident_globdef
                (fun (_: AST.program fundef unit) (f tf: fundef) =>
                  tf = transf_fundef f) eq prog) l l' ->
            l' = map (fun (idg: ident * globdef fundef unit) => 
                      let (id, g) := idg in
                      match g with
                      | Gfun f => (id, Gfun (transf_fundef f))
                      | Gvar v => (id, Gvar v)
                      end) l).
    { induction l; ss.
      - i. inv H. auto.
      - i. destruct l'; ss.
        + inv H.
        + inv H. destruct a; ss. destruct g; ss.
          * destruct p; ss. destruct g; ss.
            -- inv H3; ss. clarify. inv H0. apply IHl in H5. rewrite H5. clarify.
            -- inv H3; ss. inv H0.
          * destruct p; ss. destruct g; ss.
            -- inv H3; ss. inv H0; ss.
            -- inv H3; ss. clarify. inv H0; ss. apply IHl in H5. rewrite H5.
               inv H2. auto. }
    inv TRANSL. apply FORALL2_MAP in H as H'.
    destruct prog; ss. destruct tprog; ss. destruct H0; clarify.
  Qed.
  
  Definition program_length (p: program) :=
    List.list_max (map (code_size)
                       (fold_left (fun m ig => match (snd ig) with
                                               | Gfun (Internal f) => f :: m
                                               | _ => m
                                               end) (prog_defs p) nil)).

  Lemma transf_program_repeatn:
    exists n, transf_program prog = repeatn transf_program_step n prog.
  Proof.
    exists (program_length prog). unfold transf_program, transf_program_step.
    unfold transform_program; ss.
    assert (forall n p,
            repeatn transf_program_step n p =
            mkprogram ((repeatn (map (transform_program_globdef transf_fundef_step))
                        n (prog_defs p))) (prog_public p) (prog_main p)).
    { induction n; ss. i; destruct p; ss. i. rewrite IHn. ss. }
    rewrite H.
    assert (forall fuel, (program_length prog) <= fuel ->
            map (transform_program_globdef transf_fundef) (prog_defs prog)
            = repeatn (map (transform_program_globdef (transf_fundef_step)))
              fuel (prog_defs prog)).
    { assert (forall f n (l: list (ident * globdef fundef unit)),
              repeatn (map f) n l = (map (repeatn f n) l)).
      { induction n; ss. i. induction l; ss. rewrite <- IHl; ss.
        induction l; ss. rewrite IHn. ss.
        rewrite IHn. ss. rewrite <- IHn. rewrite IHl. ss. }
      intros fuel. rewrite H0. unfold program_length.
      generalize (prog_defs prog). induction l; ss.
      destruct a; ss. destruct g; ss.
      - (* Gfun *)
        destruct f; ss.
        + i. remember (fun m ig => _) as f'.
          assert (forall l l', fold_left f' l l' = fold_left f' l nil ++ l').
          { induction l0; ss. i. rewrite IHl0. rewrite (IHl0 (f' nil a)).
            destruct a; ss. enough (f' l' (i0, g) = f' nil (i0, g) ++ l').
            rewrite H2. rewrite List.app_assoc. ss. destruct g; ss.
            - destruct f0; clarify; ss.
            - clarify; ss. }
          rewrite H2 in H1. rewrite map_app in H1. ss.
          rewrite list_max_le in H1.
          rewrite Forall_app in H1. des. inversion H3.
          rewrite IHl. remember (transform_program_globdef transf_fundef_step).
          assert (forall n, repeatn p n (i, Gfun (Internal f)) =
                            (i, Gfun (Internal (repeatn (transf_function_fuel 1) n f)))).
          { induction n; ss. rewrite IHn. clarify; ss. }
          rewrite H8. erewrite transf_function_commute; ss. rewrite list_max_le. ss.
        + i. rewrite <- IHl. remember (transform_program_globdef transf_fundef_step).
          enough (forall n,
                  repeatn p n (i, (Gfun (External e))) = (i, (Gfun (External e)))).
          rewrite H2. ss.
          induction n; ss. rewrite IHn. clarify; ss. ss.
      - (* Gvar *)
        i. rewrite <- IHl.
        enough (forall n,
                (repeatn (transform_program_globdef transf_fundef_step) n (i, Gvar v))
                = (i, Gvar v)).
        rewrite H2. ss.
        induction n; ss. rewrite IHn. unfold transform_program_globdef. ss. ss. }
    erewrite H0; ss.
  Qed.

(** * Semantics preservation *)

End CORRECTNESS.
