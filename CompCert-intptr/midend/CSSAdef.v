Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Dom.
Require Import Op.
Require Import SSA.
Require Import SSAutils.
Require Import Utils.
Require Import CSSA.
Require Import DLib.
Require Import RTLpargen.
Require Import CSSAutils.
Require Import Registers.

Lemma def_code_correct_aux :
  forall elems r r0 ins defs (pc : node),
  In (pc, ins) elems ->
  NoDup (map fst elems) ->
  defined_var ins = Some r0 ->
  r0 = r ->
  (forall pc' ins' r', pc' <> pc ->
    In (pc', ins') elems ->
    defined_var ins' = Some r' ->
    r' <> r) ->
  (fold_right
    (fun p a =>
      match defined_var (snd p) with
      | Some r0 => PTree.set r0 (fst p) a
      | None => a
      end) defs elems) ! r = Some pc.
Proof.
  induction elems; intros.
  go.
  simpl. flatten.
  + rewrite PTree.gsspec. flatten.
    - destruct a. simpl in *.
      case_eq(peq n pc); intros; auto.
      destruct H; go.
      symmetry in e.
      contradict e.
      apply H3 with (pc' := n) (ins' := i); auto.
    - destruct a. simpl in *.
      case_eq(peq pc n0); intros; auto.
      destruct H; go.
      eapply IHelems; go. inv H0; auto.
      destruct H; go.
      eapply IHelems; go. inv H0; auto.
  + eapply IHelems; go.
    inv H; go.
    inv H0; auto.
Qed.

Lemma def_code_correct :
  forall f r defs pc,
  wf_cssa_function f ->
  assigned_code_spec (fn_code f) pc r ->
  (compute_code_def f defs) ! r = Some pc.
Proof.
  intros f r defs pc WF Hassign.
  unfold compute_code_def.
  rewrite PTree.fold_spec.
  rewrite <- fold_left_rev_right.
  inv Hassign;
  match goal with
  | [ H : (fn_code f) ! pc = Some ?i |- _ ] =>
      apply def_code_correct_aux with (r0 := r) (ins := i); go;
      [ rewrite <- in_rev; apply PTree.elements_correct; auto
      | rewrite map_rev;
        apply nodups_rev;
        rewrite rev_involutive;
        assert(list_norepet (map fst (PTree.elements (fn_code f))))
          by (apply PTree.elements_keys_norepet);
        apply list_norepet_NoDup; auto
      | intros pc' ins' r' Hneq Hin Hdef;
        rewrite <- in_rev in Hin;
        assert(Hins : (fn_code f) ! pc' = Some ins')
          by (apply PTree.elements_complete; auto);
        assert(Hassign1: assigned_code_spec (fn_code f) pc r) by go;
        assert(Hassign2: assigned_code_spec (fn_code f) pc' r')
          by (destruct ins'; try (destruct b) ; go);
        unfold not; intros Habsurd;
        rewrite Habsurd in *;
        induction WF; induction fn_cssa;
        apply Hneq;
        assert((assigned_code_spec (fn_code f) pc r ->
           assigned_code_spec (fn_code f) pc' r -> pc = pc'))
          by (eapply H; eauto);
        intuition eauto ]
  | _ => idtac
  end.
Qed.

Lemma nodef_code_correct_aux :
  forall elems r defs,
  NoDup (map fst elems) ->
  (forall (pcins : node * instruction) r',
    In pcins elems ->
    defined_var (snd pcins) = Some r' ->
    r' <> r) ->
  (fold_right
    (fun p a =>
      match defined_var (snd p) with
      | Some r0 => PTree.set r0 (fst p) a
      | None => a
      end) defs elems) ! r = defs ! r.
Proof.
  induction elems; intros.
  go. simpl. flatten.
  + rewrite PTree.gso.
    - apply IHelems. inv H; auto.
      go.
    - unfold not; intros.
      assert(r0 <> r).
      eapply H0; go.
      congruence.
  + eapply IHelems; go.
    inv H; auto.
Qed.

Lemma nodef_code_correct :
  forall f r defs,
  wf_cssa_function f ->
  (forall pc, ~ assigned_code_spec (fn_code f) pc r) ->
  (compute_code_def f defs) ! r = defs ! r.
Proof.
  intros f r defs WF Hnotassign.
  unfold compute_code_def.
  rewrite PTree.fold_spec.
  rewrite <- fold_left_rev_right.
  apply nodef_code_correct_aux.
  + rewrite map_rev;
    apply nodups_rev;
    rewrite rev_involutive;
    assert(list_norepet (map fst (PTree.elements (fn_code f))))
      by (apply PTree.elements_keys_norepet);
    apply list_norepet_NoDup; auto.
  + intros.
    rewrite <- in_rev in H.
    destruct pcins.
    apply PTree.elements_complete in H.
    unfold not; intros Heq. rewrite Heq in *.
    assert(Hassign: assigned_code_spec (fn_code f) n r).
    { destruct i; try destruct b ; go. }
    contradict Hassign. eauto.
Qed.

Lemma def_notin_parcb_correct:
  forall parcb r (pc : node) a,
  (forall src, ~ In (Iparcopy src r) parcb) ->
  (fold_right
    (fun p a =>
      match p with
      | Iparcopy src dst => PTree.set dst pc a
      end)
    a parcb) ! r = a ! r.
Proof.
  induction parcb; intros; simpl; auto.
  flatten.
  rewrite PTree.gsspec. flatten.
  + rewrite <- e in *.
    specialize (H r0).
    exfalso. apply H. constructor; auto.
  + apply IHparcb. intros.
    specialize (H src); go.
Qed.

Lemma def_in_parcb_correct:
  forall parcb r (pc : node) a,
  (exists src, In (Iparcopy src r) parcb) ->
  (fold_right
    (fun p a =>
      match p with
      | Iparcopy src dst => PTree.set dst pc a
      end)
    a parcb) ! r = Some pc.
Proof.
  induction parcb; intros; simpl.
  + destruct H. contradiction.
  + flatten.
    rewrite PTree.gsspec. flatten.
    apply IHparcb. destruct H.
    inv H; try congruence. eauto.
Qed.

Lemma nodef_parc_correct_aux :
  forall elems r defs,
  (forall (pc : node) parcb src,
    In (pc, parcb) elems ->
    ~ In (Iparcopy src r) parcb) ->
  (fold_right
    (fun pcparcb a =>
      fold_left
        (fun a p =>
          match p with
          | Iparcopy src dst => PTree.set dst (fst pcparcb) a
          end)
        (snd pcparcb) a)
    defs elems) ! r = defs ! r.
Proof.
  induction elems; intros. go.
  simpl.
  rewrite <- fold_left_rev_right.
  rewrite def_notin_parcb_correct; go.
  intros.
  destruct a; simpl.
  rewrite <- in_rev.
  eapply H; go.
Qed.

Lemma def_parc_correct_aux :
  forall elems r defs parcb (pc : node),
  (In (pc, parcb) elems) ->
  (NoDup (map fst elems)) ->
  (exists src, In (Iparcopy src r) parcb) ->
  (forall src parcb' pc', pc' <> pc ->
    In (pc', parcb') elems ->
    ~ In (Iparcopy src r) parcb') ->
  (fold_right
    (fun pcparcb a =>
      fold_left
        (fun a p =>
          match p with
          | Iparcopy src dst => PTree.set dst (fst pcparcb) a
          end)
        (snd pcparcb) a)
    defs elems) ! r = Some pc.
Proof.
  induction elems; intros.
  go.
  simpl in *.
  destruct a as [pc0 parcb0].
  case_eq(In_dst_parcb r parcb0); intros Hin.
  + exploit In_dst_parcb_true; eauto; intros Hinr.
    case_eq(peq pc0 pc); intros.
    - rewrite e in *.
      destruct H; go.
      rewrite <- fold_left_rev_right.
      rewrite def_in_parcb_correct; go.
      destruct Hinr as [src Hinr]. exists src.
      simpl. rewrite <- in_rev. auto.
      inv H0.
      assert(In pc (map fst elems)).
      eapply In_Infst_parcb; eauto.
      congruence.
    - destruct H; go.
      rewrite <- fold_left_rev_right.
      rewrite def_notin_parcb_correct; go.
      eapply IHelems; eauto.
      inv H0; auto.
      intros. simpl. rewrite <- in_rev. go.
  + assert(Hnotinr: forall src, ~ In (Iparcopy src r) parcb0).
    eapply In_dst_parcb_false; eauto.
    case_eq(peq pc0 pc); intros.
    - rewrite e in *.
      destruct H; go.
      destruct H1. specialize (Hnotinr x). congruence.
      rewrite <- fold_left_rev_right.
      rewrite def_notin_parcb_correct; go.
      eapply IHelems; eauto.
      inv H0; auto.
      intros. simpl. rewrite <- in_rev. go.
    - destruct H; go.
      rewrite <- fold_left_rev_right.
      rewrite def_notin_parcb_correct; go.
      eapply IHelems; eauto.
      inv H0; auto.
      intros. simpl. rewrite <- in_rev. go.
Qed.

Lemma def_parcode_correct :
  forall f r defs pc,
  wf_cssa_function f ->
  assigned_parcopy_spec (fn_parcopycode f) pc r ->
  (compute_parc_def f defs) ! r = Some pc.
Proof.
  intros f r defs pc WF Hnotassign.
  unfold compute_parc_def.
  rewrite PTree.fold_spec.
  rewrite <- fold_left_rev_right.
  inv Hnotassign.
  eapply def_parc_correct_aux; eauto.
  + rewrite <- in_rev.
    apply PTree.elements_correct. auto.
  + rewrite map_rev;
    apply nodups_rev;
    rewrite rev_involutive;
    assert(list_norepet (map fst (PTree.elements (fn_parcopycode f))))
      by (apply PTree.elements_keys_norepet);
    apply list_norepet_NoDup; auto.
  + intros src parcb' pc' Hneq Hin.
    rewrite <- in_rev in Hin.
    apply PTree.elements_complete in Hin.
    unfold not; intros Hinparc. destruct H0 as [src0 Hinparcb].
    assert(Hassignpc: assigned_parcopy_spec (fn_parcopycode f) pc r)
      by go.
    assert(Hassignpc': assigned_parcopy_spec (fn_parcopycode f) pc' r)
      by go.
    contradict Hneq.
    induction WF; induction fn_cssa.
    specialize (H r pc pc').
    intuition auto.
Qed.

Lemma nodef_parcode_correct :
  forall f r defs,
  wf_cssa_function f ->
  (forall pc, ~ assigned_parcopy_spec (fn_parcopycode f) pc r) ->
  (compute_parc_def f defs) ! r = defs ! r.
Proof.
  intros f r defs WF Hnotassign.
  unfold compute_parc_def.
  rewrite PTree.fold_spec.
  rewrite <- fold_left_rev_right.
  apply nodef_parc_correct_aux.
  intros.
  rewrite <- in_rev in H.
  specialize (Hnotassign pc).
  unfold not; intros.
  apply Hnotassign.
  apply PTree.elements_complete in H.
  go.
Qed.

(* phis *)

Lemma def_notin_phib_correct:
  forall phib r (pc : node) a,
  (forall args, ~ In (Iphi args r) phib) ->
  (fold_right
    (fun p a =>
      match p with
      | Iphi args dst => PTree.set dst pc a
      end)
    a phib) ! r = a ! r.
Proof.
  induction phib; intros; simpl; auto.
  flatten.
  rewrite PTree.gsspec. flatten.
  + rewrite <- e in *.
    specialize (H l).
    exfalso. apply H. constructor; auto.
  + apply IHphib. intros.
    specialize (H args); go.
Qed.

Lemma def_in_phib_correct:
  forall phib r (pc : node) a,
  (exists args, In (Iphi args r) phib) ->
  (fold_right
    (fun p a =>
      match p with
      | Iphi args dst => PTree.set dst pc a
      end)
    a phib) ! r = Some pc.
Proof.
  induction phib; intros; simpl.
  + destruct H. contradiction.
  + flatten.
    rewrite PTree.gsspec. flatten.
    apply IHphib. destruct H.
    inv H; try congruence. eauto.
Qed.

Lemma nodef_phib_correct_aux :
  forall elems r defs,
  (forall (pc : node) phib args,
    In (pc, phib) elems ->
    ~ In (Iphi args r) phib) ->
  (fold_right
    (fun pcphib a =>
      fold_left
        (fun a p =>
          match p with
          | Iphi args dst => PTree.set dst (fst pcphib) a
          end)
        (snd pcphib) a)
    defs elems) ! r = defs ! r.
Proof.
  induction elems; intros. go.
  simpl.
  rewrite <- fold_left_rev_right.
  rewrite def_notin_phib_correct; go.
  intros.
  destruct a; simpl.
  rewrite <- in_rev.
  eapply H; go.
Qed.

Lemma def_phi_correct_aux :
  forall elems r defs phib (pc : node),
  (In (pc, phib) elems) ->
  (NoDup (map fst elems)) ->
  (exists args, In (Iphi args r) phib) ->
  (forall args phib' pc', pc' <> pc ->
    In (pc', phib') elems ->
    ~ In (Iphi args r) phib') ->
  (fold_right
    (fun pcphib a =>
      fold_left
        (fun a p =>
          match p with
          | Iphi args dst => PTree.set dst (fst pcphib) a
          end)
        (snd pcphib) a)
    defs elems) ! r = Some pc.
Proof.
  induction elems; intros.
  go.
  simpl in *.
  destruct a as [pc0 phib0].
  case_eq(In_dst_phib r phib0); intros Hin.
  + exploit In_dst_phib_true; eauto; intros Hinr.
    case_eq(peq pc0 pc); intros.
    - rewrite e in *.
      destruct H; go.
      rewrite <- fold_left_rev_right.
      rewrite def_in_phib_correct; go.
      destruct Hinr as [args Hinr]. exists args.
      simpl. rewrite <- in_rev. auto.
      inv H0.
      assert(In pc (map fst elems)).
      eapply In_Infst_phib; eauto.
      congruence.
    - destruct H; go.
      rewrite <- fold_left_rev_right.
      rewrite def_notin_phib_correct; go.
      eapply IHelems; eauto.
      inv H0; auto.
      intros. simpl. rewrite <- in_rev. go.
  + assert(Hnotinr: forall args, ~ In (Iphi args r) phib0).
    eapply In_dst_phib_false; eauto.
    case_eq(peq pc0 pc); intros.
    - rewrite e in *.
      destruct H; go.
      destruct H1. specialize (Hnotinr x). congruence.
      rewrite <- fold_left_rev_right.
      rewrite def_notin_phib_correct; go.
      eapply IHelems; eauto.
      inv H0; auto.
      intros. simpl. rewrite <- in_rev. go.
    - destruct H; go.
      rewrite <- fold_left_rev_right.
      rewrite def_notin_phib_correct; go.
      eapply IHelems; eauto.
      inv H0; auto.
      intros. simpl. rewrite <- in_rev. go.
Qed.

Lemma def_phicode_correct :
  forall f r defs pc,
  wf_cssa_function f ->
  assigned_phi_spec (fn_phicode f) pc r ->
  (compute_phi_def f defs) ! r = Some pc.
Proof.
  intros f r defs pc WF Hnotassign.
  unfold compute_phi_def.
  rewrite PTree.fold_spec.
  rewrite <- fold_left_rev_right.
  inv Hnotassign.
  eapply def_phi_correct_aux; eauto.
  + rewrite <- in_rev.
    apply PTree.elements_correct. auto.
  + rewrite map_rev;
    apply nodups_rev;
    rewrite rev_involutive;
    assert(list_norepet (map fst (PTree.elements (fn_phicode f))))
      by (apply PTree.elements_keys_norepet);
    apply list_norepet_NoDup; auto.
  + intros src phib' pc' Hneq Hin.
    rewrite <- in_rev in Hin.
    apply PTree.elements_complete in Hin.
    unfold not; intros Hinphi. destruct H0 as [args0 Hinphib].
    assert(Hassignpc: assigned_phi_spec (fn_phicode f) pc r)
      by go.
    assert(Hassignpc': assigned_phi_spec (fn_phicode f) pc' r)
      by go.
    contradict Hneq.
    induction WF; induction fn_cssa.
    specialize (H r pc pc').
    intuition auto.
Qed.

Lemma nodef_phicode_correct :
  forall f r defs,
  wf_cssa_function f ->
  (forall pc, ~ assigned_phi_spec (fn_phicode f) pc r) ->
  (compute_phi_def f defs) ! r = defs ! r.
Proof.
  intros f r defs WF Hnotassign.
  unfold compute_phi_def.
  rewrite PTree.fold_spec.
  rewrite <- fold_left_rev_right.
  apply nodef_phib_correct_aux.
  intros.
  rewrite <- in_rev in H.
  specialize (Hnotassign pc).
  unfold not; intros.
  apply Hnotassign.
  apply PTree.elements_complete in H.
  go.
Qed.

(* NOTE:
    on veut réutiliser tout ça pour se donner une liste des ext-params.
    + On considère l'ensemble des trucs utilisés (avec notre fonction use),
      on est sûr qu'on les a tous (c'est prouvé).
    + Ensuite, on parcours tout ça, et on garde que ceux qui sont définis
      au point d'entrée.
    + On obtient tous les ext-params. 
*)
Lemma compute_def_correct :
  forall f r d,
  wf_cssa_function f ->
  CSSA.def f r d ->
  compute_def f (get_all_def f) r = d.
Proof.
  intros f r d WF Hdef.
  unfold compute_def. unfold get_all_def.
  inv Hdef.
  + flatten. inv H;
    [ exploit fn_cssa_params; eauto | idtac]; intros;
    try (rewrite nodef_parcode_correct in Eq; intuition auto);
    try (rewrite nodef_phicode_correct in Eq; intuition auto);
    try (rewrite nodef_code_correct in Eq; intuition auto);
    try (rewrite PTree.gempty in Eq);
    try congruence.
  + rewrite nodef_parcode_correct; auto.
    rewrite nodef_phicode_correct; auto.
    rewrite def_code_correct with (pc := d); auto.
    induction WF; induction fn_cssa.
    intros. specialize (H r pc d). intuition eauto.
    induction WF; induction fn_cssa.
    intros. specialize (H r pc d). intuition eauto.
  + rewrite nodef_parcode_correct; auto.
    rewrite def_phicode_correct with (pc := d); auto.
    induction WF; induction fn_cssa.
    intros. specialize (H r pc d). intuition eauto.
  + rewrite def_parcode_correct with (pc := d); auto.
Qed.

Lemma nodef_none :
  forall f r,
  wf_cssa_function f ->
  (forall pc, ~ assigned_phi_spec (fn_phicode f) pc r) ->
  (forall pc, ~ assigned_parcopy_spec (fn_parcopycode f) pc r) ->
  (forall pc, ~ assigned_code_spec (fn_code f) pc r) ->
  (get_all_def f) ! r = None.
Proof.
  intros f r WF Hnotphi Hnotparc Hnotcode.
  unfold compute_def.
  unfold get_all_def.
  rewrite nodef_parcode_correct; auto.
  rewrite nodef_phicode_correct; auto.
  rewrite nodef_code_correct; auto.
  rewrite PTree.gempty; auto.
Qed.

Lemma code_def_not_none :
  forall f r pc,
  wf_cssa_function f ->
  assigned_code_spec (fn_code f) pc r ->
  (get_all_def f) ! r <> None.
Proof.
  intros f r pc WF Hdefcode.
  unfold get_all_def.
  assert (forall pc, ~ assigned_phi_spec (fn_phicode f) pc r).
  { intros. induction WF. induction fn_cssa.
    specialize (H r pc0 pc). intuition.  }
  assert (forall pc, ~ assigned_parcopy_spec (fn_parcopycode f) pc r).
  { intros. induction WF. induction fn_cssa.
    specialize (H r pc0 pc). intuition.  }
  rewrite nodef_parcode_correct; auto.
  rewrite nodef_phicode_correct; auto.
  erewrite def_code_correct; eauto.
  congruence.
Qed.

Lemma phi_def_not_none :
  forall f r pc,
  wf_cssa_function f ->
  assigned_phi_spec (fn_phicode f) pc r ->
  (get_all_def f) ! r <> None.
Proof.
  intros f r pc WF Hdefcode.
  unfold get_all_def.
  assert (forall pc, ~ assigned_parcopy_spec (fn_parcopycode f) pc r).
  { intros. induction WF. induction fn_cssa.
    specialize (H r pc0 pc). intuition.  }
  rewrite nodef_parcode_correct; auto.
  erewrite def_phicode_correct; eauto.
  congruence.
Qed.

Lemma parc_def_not_none :
  forall f r pc,
  wf_cssa_function f ->
  assigned_parcopy_spec (fn_parcopycode f) pc r ->
  (get_all_def f) ! r <> None.
Proof.
  intros f r pc WF Hdefcode.
  unfold get_all_def.
  erewrite def_parcode_correct; eauto.
  congruence.
Qed.

Lemma Infst_rtreenode :
  forall (l : list (reg * positive)) r n,
  In (r, n) l ->
  In r (map fst l).
Proof.
  induction l; go; intros.
  simpl in *. destruct H; go.
Qed.

Lemma Infst_rtreenode_exists :
  forall (l : list (reg * positive)) r,
  In r (map fst l) ->
  exists n,
  In (r, n) l.
Proof.
  induction l; go; intros.
  simpl in *. destruct H; go.
  destruct a; simpl in *; go.
  exploit IHl; eauto; intros.
  destruct H0. exists x. auto.
Qed.

Lemma not_none_in :
  forall (rtree : PTree.t positive) r,
  rtree ! r <> None ->
  In r (map fst (PTree.elements rtree)).
Proof.
  intros.
  case_eq (rtree ! r); try congruence; intros.
  exploit PTree.elements_correct; eauto; intros.
  eapply Infst_rtreenode; eauto.
Qed.

Lemma none_not_in :
  forall (rtree : PTree.t positive) r,
  rtree ! r = None ->
  ~ In r (map fst (PTree.elements rtree)).
Proof.
  intros.
  case_eq (rtree ! r); try congruence; intros.
  unfold not; intros.
  exploit Infst_rtreenode_exists; eauto; intros Hin.
  destruct Hin.
  exploit PTree.elements_complete; eauto; intros.
  congruence.
Qed.

Lemma compute_def_in_correct :
  forall f r d,
  wf_cssa_function f ->
  CSSA.def f r d ->
  In r (map fst (PTree.elements (get_all_def f)))
  \/ SSARegSet.In r (get_ext_params f (get_all_def f)).
Proof.
  intros.
  inv H0.
  + right.
    inv H1.
    - unfold get_ext_params.
      apply SSARegSet.union_3.
      unfold param_set.
      exploit In_fold_right_add1; eauto.
    - unfold get_ext_params.
      apply SSARegSet.union_2.
      apply SSARegSet.diff_3.
      destruct H0. eapply search_used_correct; eauto.
      unfold def_set.
      unfold not; intros.
      exploit In_fold_right_add3; eauto; intros Hin.
      destruct Hin as [Hin | Hin]. inv Hin.
      contradict Hin.
      apply none_not_in.
      apply nodef_none; auto.
  + left.
    apply not_none_in.
    eapply code_def_not_none; eauto.
  + left.
    apply not_none_in.
    eapply phi_def_not_none; eauto.
  + left.
    apply not_none_in.
    eapply parc_def_not_none; eauto.
Qed.

