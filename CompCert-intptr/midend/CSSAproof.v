(** Proof of CSSApargen transformation *)

Require Recdef.
Require Import FSets.
Require Import Coqlib.
Require Import Ordered.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import PointerOp Simulation SSAD CSSAD sflib.
Require Import Smallstep.
Require Import CSSA.
Require Import SSA.
Require Import SSAutils.
Require Import CSSAgen.
Require Import Kildall.
Require Import Conventions.
Require Import Utils.
Require Import NArith.
Require Import Events.
Require Import Permutation.
Require Import KildallComp.
Require Import DLib.
Require Import CSSAgenspec.
Require Import CSSAutils.
Require Import Classical.
From Paco Require Import paco.

Unset Allow StrictProp.

Ltac sz := unfold Plt, Ple in * ; (zify; lia).

(** * Reasoning about monadic computations *)
Remark bind_inversion:
  forall (A B: Type) (f: mon A) (g: A -> mon B)
         (y: B) (s1 s3: state) (i: state_incr s1 s3),
  bind f g s1 = OK y s3 i ->
  exists x, exists s2, exists i1, exists i2,
  f s1 = OK x s2 i1 /\ g x s2 = OK y s3 i2.
Proof.
  intros until i. unfold bind. destruct (f s1); intros.
  discriminate.
  exists a; exists s'; exists s.
  destruct (g a s'); inv H.
  exists s0; auto.
Qed.

Ltac monadInv1 H :=
  match type of H with
  | (OK _ _ _ = OK _ _ _) =>
      inversion H; clear H; try subst
  | (Error _ _ = OK _ _ _) =>
      discriminate
  | (ret _ _ = OK _ _ _) =>
      inversion H; clear H; try subst
  | (error _ _ = OK _ _ _) =>
      discriminate
  | (bind ?F ?G ?S = OK ?X ?S' ?I) =>
      let x := fresh "x" in (
      let s := fresh "s" in (
      let i1 := fresh "INCR" in (
      let i2 := fresh "INCR" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion _ _ F G X S S' I H) as [x [s [i1 [i2 [EQ1 EQ2]]]]];
      clear H;
      try (monadInv1 EQ2)))))))
  end.

Ltac monadInv H :=
  match type of H with
  | (ret _ _ = OK _ _ _) => monadInv1 H
  | (error _ _ = OK _ _ _) => monadInv1 H
  | (bind ?F ?G ?S = OK ?X ?S' ?I) => monadInv1 H
  | (bind2 ?F ?G ?S = OK ?X ?S' ?I) => monadInv1 H
  | (?F _ _ _ _ _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); try monadInv1 H
  | (?F _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  end.

(** Utility lemmas *)
Lemma Plt_neq :
  forall (r1 r2 : reg),
  Plt r1 r2 ->
  r1 <> r2.
Proof.
  intros.
  assert (r1 <> r2) by auto with coqlib.
  congruence.
Qed.

Global Hint Resolve Plt_neq: core.

Lemma nth_error_nil_notSome_node :
  forall k,
  nth_error (nil:list node) k = None.
Proof.
  induction k; auto.
Qed.

Lemma nth_error_nil_notSome_reg :
  forall k,
  nth_error (nil:list reg) k = None.
Proof.
  induction k; auto.
Qed.

Global Hint Resolve nth_error_nil_notSome_node
  nth_error_nil_notSome_reg: core.

Lemma notIn_notnth:
  forall k (nodes: list node) pc,
  ~ In pc nodes ->
  nth_error nodes k <> Some pc.
Proof.
  induction k; intros.
  + simpl. flatten.
    intro. elim H.
    inv H0. go. 
  + simpl. flatten.
    apply IHk.
    intro Hcont. elim H ; go. 
Qed.

Lemma nth_In_reg:
  forall k (regs: list reg) r,
  nth_error regs k = Some r ->
  In r regs.
Proof.
  induction k; intros; simpl in *;
  flatten regs; go.
Qed.

Global Hint Resolve nth_In_reg: core.

Lemma nth_In_node:
  forall k (nodes: list node) pc,
  nth_error nodes k = Some pc ->
  In pc nodes.
Proof.
  induction k; intros; simpl in *;
    flatten regs; go. 
Qed.

Global Hint Resolve nth_In_node: core.

(** Kildall lemmas *)

Lemma add_successors_other :
  forall l pred from pc,
  ~ In pc l ->
  pred !!! pc = (add_successors pred from l) !!! pc.
Proof.
  induction l; intros.
  + simpl in *. congruence.
  + simpl in *.
    case_eq (peq a pc); intros.
    - rewrite e in *.
      intuition.
    - assert (~ In pc l) by intuition.
      replace (pred !!! pc) with
        ((PTree.set a (from :: pred !!! a) pred)
          !!! pc).
      eapply IHl; eauto.
      unfold successors_list in *.
      rewrite PTree.gso; auto.
Qed.

Lemma add_successors_notfrom :
  forall l pred from pc pc',
  ~ In pc' (pred !!! pc) ->
  pc' <> from ->
  ~ In pc' ((add_successors pred from l) !!! pc).
Proof.
  induction l; intros.
  + simpl in *. congruence.
  + simpl in *.
    unfold successors_list.
    flatten; go.
    flatten Eq; go.
    assert(Eqsuccs:
      (add_successors (PTree.set a (from :: l1) pred)
        from l) !!! pc = l0).
    { unfold successors_list; go. }
    rewrite <- Eqsuccs.
    apply IHl; auto.
    { case_eq (peq a pc); intros.
      - rewrite e in *.
        unfold successors_list.
        rewrite PTree.gss.
        unfold not; intros HIn.
        inv HIn; auto.
        apply H.
        unfold successors_list.
        go.
      - unfold successors_list.
        rewrite PTree.gso; auto.
    }
    assert(Eqsuccs:
      (add_successors (PTree.set a (from :: nil) pred)
        from l) !!! pc = l0).
    { unfold successors_list; go. }
    rewrite <- Eqsuccs.
    apply IHl; auto.
    { case_eq (peq a pc); intros.
      - rewrite e in *.
        unfold successors_list.
        rewrite PTree.gss.
        unfold not; intros HIn.
        inv HIn; auto.
      - unfold successors_list.
        rewrite PTree.gso; auto.
    }
Qed.

Lemma not_in_foldelems :
  forall pc pc' elems predinit,
  ~ In pc' (map fst elems) ->
  ~ In pc' (predinit !!! pc) ->
  ~ In pc' (fold_right
      (fun pcins pred =>
        add_successors pred (fst pcins)
          (successors_instr (snd pcins)))
      predinit elems) !!! pc.
Proof.
  intro pc.
  induction elems; intros.
  + simpl. auto.
  + simpl in *.
    apply add_successors_notfrom; go.
    eapply IHelems; eauto.
Qed.

Lemma nodups_in_preds_aux :
  forall pc elems predinit,
  (forall pcins,
    In pcins elems -> 
    In pc (successors_instr (snd pcins)) ->
    (successors_instr (snd pcins)) = pc :: nil) ->
  (forall elt, In elt elems ->
    ~ In (fst elt) (predinit !!! pc)) ->
  NoDup (map fst elems) ->
  NoDup (predinit !!! pc) ->
  NoDup
    (List.fold_right
      (fun pcins pred =>
        add_successors pred (fst pcins)
          (successors_instr (snd pcins)))
      predinit elems) !!! pc.
Proof.
  intro pc.
  induction elems; intros.
  + simpl. auto.
  + simpl.
    case_eq (in_dec peq pc (successors_instr (snd a)));
      intros.
    - assert (Succs: successors_instr (snd a) = pc :: nil)
        by auto.
      rewrite Succs.
      simpl.
      unfold successors_list.
      rewrite PTree.gss.
      simpl in H1.
      constructor.
      inv H1.
      apply not_in_foldelems; eauto.
      apply IHelems; auto.
      inv H1; auto.
    - rewrite <- add_successors_other; go.
      apply IHelems; go.
      inv H1; auto.
Qed.

Lemma nodups_in_preds :
  forall l f preds pc,
  wf_ssa_function f ->
  preds = make_predecessors (fn_code f) successors_instr ->
  (fn_phicode f) ! pc <> None ->
  preds ! pc = Some (l : list node) ->
  ~ In pc l ->
  NoDup (pc :: l).
Proof.
  intros.
  constructor; auto.
  assert(EQ: preds !!! pc = l).
  unfold successors_list; go.
  rewrite <- EQ.
  rewrite H0.
  unfold make_predecessors.
  rewrite PTree.fold_spec.
  rewrite <- List.fold_left_rev_right.
  apply nodups_in_preds_aux; intros.
  { rewrite <- in_rev in H4.
    destruct pcins.
    simpl in *.
    assert ((fn_code f) ! p = Some i).
    apply PTree.elements_complete. auto.
    assert (JP: join_point pc f).
    induction H. apply fn_phicode_inv. auto.
    assert (Insuccs: In pc (succs f p)).
    unfold successors.
    unfold successors_list. flatten.
    { rewrite PTree.gmap1 in Eq.
      rewrite H6 in Eq.
      simpl in *. go. }
    { rewrite PTree.gmap1 in Eq.
      rewrite H6 in Eq.
      simpl in *. congruence. }
    assert ((fn_code f) ! p = Some (Inop pc)).
    induction H.
    apply fn_normalized; auto.
    assert(RW: i = Inop pc).
    congruence.
    rewrite RW. auto.
  }
  { unfold successors_list. flatten ; auto.
    assert((PTree.empty (list positive)) ! pc = None).
    apply PTree.gempty. congruence. }
  { rewrite map_rev.
    cut (NoDup (rev (rev (map fst
      (PTree.elements (fn_code f))))));
      intros.
    apply nodups_rev.
    auto.
    rewrite rev_involutive.
    assert (list_norepet
      (map fst (PTree.elements (fn_code f)))).
    apply PTree.elements_keys_norepet.
    apply list_norepet_NoDup; auto. }
  { unfold successors_list; flatten.
    assert ((PTree.empty (list positive)) ! pc = None).
    apply PTree.gempty. congruence.
    constructor. }
Qed.

Lemma in_successors_if_succofpred :
  forall f pc l k n i,
  (fn_code f) ! n = Some i ->
  (make_predecessors (fn_code f) successors_instr) 
    ! pc = Some l ->
  nth_error l k = Some n ->
  In pc ((successors f) !!! n).
Proof.
  intros.
  unfold successors_list.
  unfold successors.
  rewrite PTree.gmap1.
  unfold option_map.
  rewrite H.
  apply make_predecessors_correct2
    with (code := (fn_code f)) (n0 := n).
  auto.
  assert((make_predecessors (fn_code f) successors_instr)
    !!! pc = l).
  unfold successors_list. flatten.
  unfold make_preds.
  rewrite H2.
  eapply nth_In_node; eauto.
Qed.

Lemma inop_is_not_in_two_preds :
  forall f l pred pc pc',
  (make_predecessors (fn_code f) successors_instr)
    ! pc' = Some l ->
  pc <> pc' ->
  (fn_code f) ! pred = Some (Inop pc) ->
  ~ In pred l.
Proof.
  intros.
  assert(preds: (make_predecessors (fn_code f) successors_instr)
    !!! pc' = l).
  unfold successors_list. flatten.
  rewrite <- preds.
  apply make_predecessors_correct2_aux
    with (i := Inop pc).
  auto.
  simpl. intuition.
Qed.

(** get_maxreg correctness *)

Lemma ple_foldmaxreg_init :
  forall l m n,
  Ple m n ->
  Ple
    m
    (List.fold_left (fun m r' => Pos.max m (r' : reg))
      l n).
Proof.
  induction l; intros.
  simpl. auto.
  simpl.
  apply Ple_trans with
    (Pos.max m  a); auto.
  apply Pos.le_max_l.
  apply IHl.
  apply Pos.max_le_compat.
  auto. apply Ple_refl.
Qed.

Lemma max_reg_in_list_correct_aux :
  forall l (r : reg) m,
  In r l ->
  Ple r
    (List.fold_left (fun m r' => Pos.max m r') l m).
Proof.
  induction l; intros.
  inv H.
  simpl in *.
  destruct H.
  + rewrite H in *.
    eapply ple_foldmaxreg_init; eauto.
    apply Pos.le_max_r.
  + auto.
Qed.

Lemma max_reg_in_list_correct :
  forall l r,
  In r l ->
  Ple r (max_reg_in_list l).
Proof.
  unfold max_reg_in_list.
  intros.
  apply max_reg_in_list_correct_aux.
  auto.
Qed.

Lemma max_reg_in_Icall_inl  :
  forall r args res x y,
  Ple r
    (get_max_reg_in_ins (Icall x (inl r) args res y)).
Proof.
  intros.
  unfold get_max_reg_in_ins.
  apply max_reg_in_list_correct.
  constructor. auto.
Qed.

Lemma max_reg_in_Itailcall_inl :
  forall r args sig,
  Ple r
    (get_max_reg_in_ins (Itailcall sig (inl r) args)).
Proof.
  intros.
  unfold get_max_reg_in_ins.
  apply max_reg_in_list_correct.
  constructor. auto.
Qed.

Lemma max_reg_in_Icall_args :
  forall ros args arg res sig y,
  In arg args ->
  Ple arg
    (get_max_reg_in_ins (Icall sig ros args res y)).
Proof.
  intros.
  unfold get_max_reg_in_ins.
  flatten; apply max_reg_in_list_correct.
  + constructor 2.
    constructor 2.
    auto.
  + constructor 2.
    auto.
Qed.

Lemma max_reg_in_Itailcall_args :
  forall ros args arg sig,
  In arg args ->
  Ple arg
    (get_max_reg_in_ins (Itailcall sig ros args)).
Proof.
  intros.
  unfold get_max_reg_in_ins.
  flatten; apply max_reg_in_list_correct.
  + constructor 2.
    auto.
  + auto.
Qed.

Lemma max_reg_in_Iop_args :
  forall op args arg res pc,
  In arg args ->
  Ple arg
    (get_max_reg_in_ins (Iop op args res pc)).
Proof.
  intros.
  unfold get_max_reg_in_ins.
  flatten; apply max_reg_in_list_correct.
  constructor 2. auto.
Qed.

Lemma max_reg_in_Iload_args :
  forall chunk addr args arg dst pc,
  In arg args ->
  Ple arg
    (get_max_reg_in_ins (Iload chunk addr args dst pc)).
Proof.
  intros.
  unfold get_max_reg_in_ins.
  flatten; apply max_reg_in_list_correct.
  constructor 2. auto.
Qed.

Lemma max_reg_in_Istore_args  :
  forall chunk addr args arg src pc,
  In arg args ->
  Ple arg
    (get_max_reg_in_ins (Istore chunk addr args src pc)).
Proof.
  intros.
  unfold get_max_reg_in_ins.
  flatten; apply max_reg_in_list_correct.
  constructor 2. auto.
Qed.

Lemma max_reg_in_Istore_src :
  forall chunk addr args src pc,
  Ple src
    (get_max_reg_in_ins (Istore chunk addr args src pc)).
Proof.
  intros.
  unfold get_max_reg_in_ins.
  flatten; apply max_reg_in_list_correct.
  constructor. auto.
Qed.

Lemma max_reg_in_Ibuiltin_args :
  forall ef args arg res pc,
  In arg (params_of_builtin_args args) ->
  Ple arg
    (get_max_reg_in_ins (Ibuiltin ef args res pc)).
Proof.
  intros.
  unfold get_max_reg_in_ins.
  flatten; apply max_reg_in_list_correct.
  eapply in_or_app.
  right; go.
Qed.

Lemma max_reg_in_Icond_args :
  forall cond args arg ifso ifnot,
  In arg args ->
  Ple arg
    (get_max_reg_in_ins (Icond cond args ifso ifnot)).
Proof.
  intros.
  unfold get_max_reg_in_ins.
  flatten; apply max_reg_in_list_correct.
  auto.
Qed.

Lemma max_reg_in_Ijumptable_arg :
  forall arg tbl,
  Ple arg
    (get_max_reg_in_ins (Ijumptable arg tbl)).
Proof.
  intros.
  unfold get_max_reg_in_ins.
  flatten; apply max_reg_in_list_correct.
  constructor. auto.
Qed.

Lemma max_reg_in_Ireturn_r :
  forall r,
  Ple r
    (get_max_reg_in_ins (Ireturn (Some r))).
Proof.
  intros.
  unfold get_max_reg_in_ins.
  flatten; apply max_reg_in_list_correct.
  constructor. auto.
Qed.

Lemma max_reg_in_phi_dst :
  forall dst args,
  Ple dst (get_max_reg_in_phiins (Iphi args dst)).
Proof.
  intros.
  unfold get_max_reg_in_phiins.
  apply max_reg_in_list_correct.
  simpl. auto.
Qed.

Lemma max_reg_in_phi_arg :
  forall dst args arg,
  In arg args ->
  Ple arg (get_max_reg_in_phiins (Iphi args dst)).
Proof.
  intros.
  unfold get_max_reg_in_phiins.
  apply max_reg_in_list_correct.
  simpl. auto.
Qed.

Lemma ple_foldmaxphi_init :
  forall l m n,
  Ple m n ->
  Ple
    m
    (List.fold_left (fun m phi => Pos.max m
      (get_max_reg_in_phiins phi))
      l n).
Proof.
  induction l; intros.
  simpl. auto.
  simpl.
  apply Ple_trans with
    (Pos.max m (get_max_reg_in_phiins a)); auto.
  apply Pos.le_max_l.
  apply IHl.
  apply Pos.max_le_compat.
  auto. apply Ple_refl.
Qed.

Lemma max_reg_in_phib_dst_aux :
  forall phib dst args init,
  In (Iphi args dst) phib ->
  Ple (get_max_reg_in_phiins (Iphi args dst))
    (List.fold_left (fun m phiins => Pos.max m
      (get_max_reg_in_phiins phiins))
      phib init).
Proof.
  induction phib; intros.
  + inv H.
  + simpl in *.
    destruct H.
    - rewrite H in *.
      simpl in *.
      apply ple_foldmaxphi_init.
      apply Pos.le_max_r.
    - auto.
Qed.

Lemma max_reg_in_phib_dst :
  forall phib dst args,
  In (Iphi args dst) phib ->
  Ple (get_max_reg_in_phiins (Iphi args dst))
    (get_max_reg_in_phib phib).
Proof.
  intros.
  unfold get_max_reg_in_phib.
  apply max_reg_in_phib_dst_aux.
  auto.
Qed.

Lemma ple_foldmaxphib_init :
  forall l m n,
  Ple m n ->
  Ple
    m
    (List.fold_left
      (fun m (pphib : positive * phiblock) => Pos.max m
        (get_max_reg_in_phib (snd pphib)))
      l n).
Proof.
  induction l; intros.
  simpl. auto.
  simpl.
  apply Ple_trans with
    (Pos.max m (get_max_reg_in_phib (snd a))); auto.
  apply Pos.le_max_l.
  apply IHl.
  apply Pos.max_le_compat.
  auto. apply Ple_refl.
Qed.

Lemma ple_foldmaxins_init :
  forall l m n,
  Ple m n ->
  Ple
    m
    (List.fold_left
      (fun m (pcins : positive * instruction) => Pos.max m
        (get_max_reg_in_ins (snd pcins)))
      l n).
Proof.
  induction l; intros.
  simpl. auto.
  simpl.
  apply Ple_trans with
    (Pos.max m (get_max_reg_in_ins (snd a))); auto.
  apply Pos.le_max_l.
  apply IHl.
  apply Pos.max_le_compat.
  auto. apply Ple_refl.
Qed.

Lemma max_reg_in_phicode_aux :
  forall elems init pphib (pc:positive) phib,
  In pphib elems ->
  pphib = (pc, phib) ->
  Ple (get_max_reg_in_phib phib)
    (fold_left
      (fun m p =>
        Pos.max m (get_max_reg_in_phib (snd p)))
    elems init).
Proof.
  induction elems; intros.
  + inv H.
  + simpl in *.
    destruct H.
    - rewrite H in *.
      simpl in *.
      apply ple_foldmaxphib_init.
      destruct pphib. simpl.
      assert (p0 = phib) by congruence.
      rewrite H1 in *.
      apply Pos.le_max_r.
    - eauto.
Qed.

Lemma max_reg_in_code_aux :
  forall elems pcins (pc:positive) ins init,
  In pcins elems ->
  pcins = (pc, ins) ->
  Ple (get_max_reg_in_ins ins)
    (fold_left 
        (fun m p => Pos.max m (get_max_reg_in_ins (snd p)))
      elems init).
Proof.
  induction elems; intros.
  + inv H.
  + simpl in *.
    destruct H.
    - rewrite H in *.
      simpl in *.
      apply ple_foldmaxins_init.
      destruct pcins. simpl.
      assert (i = ins) by congruence.
      rewrite H1 in *.
      apply Pos.le_max_r.
    - eauto.
Qed.

Lemma max_reg_in_phicode :
  forall phicode pc phib,
  phicode ! pc = Some phib ->
  Ple (get_max_reg_in_phib phib)
    (get_max_reg_in_phicode phicode).
Proof.
  intros.
  unfold get_max_reg_in_phicode.
  rewrite PTree.fold_spec.
  eapply max_reg_in_phicode_aux; eauto.
  apply PTree.elements_correct; eauto.
Qed.

Lemma max_reg_in_code :
  forall code pc ins,
  code ! pc = Some ins ->
  Ple (get_max_reg_in_ins ins)
    (get_max_reg_in_code code).
Proof.
  intros.
  unfold get_max_reg_in_code.
  rewrite PTree.fold_spec.
  eapply max_reg_in_code_aux; eauto.
  apply PTree.elements_correct; eauto.
Qed.

Lemma max_reg_correct_phicode :
  forall f,
  Ple (get_max_reg_in_phicode (fn_phicode f))
    (get_maxreg f).
Proof.
  intros.
  unfold get_maxreg.
  apply Ple_trans with
    (Pos.max (get_max_reg_in_phicode (fn_phicode f))
      (max_reg_in_list (fn_params f))).
  apply Pos.le_max_l.
  apply Pos.le_max_r.
Qed.

Lemma max_reg_correct_code :
  forall f,
  Ple (get_max_reg_in_code (fn_code f))
    (get_maxreg f).
Proof.
  intros.
  unfold get_maxreg.
  apply Pos.le_max_l.
Qed.

(** wf_ssa lemmas for transformation *)

Lemma wf_unique_def_phib_aux :
  forall phib,
  NoDup phib ->
  (forall (r : reg) (args0 args' : list reg),
    In (Iphi args0 r) phib ->
    In (Iphi args' r) phib -> args0 = args') ->
  unique_def_phib_spec phib.
Proof.
  induction phib; go; intros.
  destruct a.
  constructor; intros.
  + simpl in *.
    unfold not; intros.
    rewrite H2 in *.
    inv H.
    assert (l = args').
    eapply H0; eauto.
    congruence.
  + inv H.
    eapply IHphib; eauto.
Qed.

Lemma wf_unique_def_phib :
  forall phib f pc,
  SSA.wf_ssa_function f ->
  (fn_phicode f) ! pc = Some phib ->
  unique_def_phib_spec phib.
Proof.
  intros.
  induction H.
  unfold unique_def_spec in *.
  repeat destruct fn_ssa as [_ fn_ssa].
  assert (Hwf: NoDup phib
    /\ (forall r args0 args',
          In (Iphi args0 r) phib ->
          In (Iphi args' r) phib ->
          args0 = args')).
  eauto.
  destruct Hwf.
  apply wf_unique_def_phib_aux; auto.
Qed.

Lemma notinpredspc :
  forall f pc preds phib,
  normalized_jp f ->
  (fn_phicode f) ! pc = Some phib ->
  (make_predecessors (fn_code f) successors_instr)
    ! pc = Some preds ->
  ~ In pc preds.
Proof.
  intros.
  unfold not; intros.
  assert ((fn_phicode f) ! pc = None).
  unfold normalized_jp in H.
  eapply H; eauto.
  congruence. congruence.
Qed.

(** The transformation verifies the specification *)

(* Lemmas with properties of CSSApargen.v functions *)
Lemma initialize_phi_block_correct :
  forall x pc s s' INCR,
  initialize_phi_block pc s = OK x s' INCR ->
  (st_phicode s') ! pc = Some nil.
Proof.
  intros. unfold initialize_phi_block in H.
  flatten H.
  simpl. apply PTree.gss.
Qed.

Lemma initialize_parcopy_block_correct :
  forall x pc s s' INCR,
  initialize_parcopy_block pc s = OK x s' INCR ->
  (st_parcopycode s') ! pc = Some nil.
Proof.
  intros. unfold initialize_parcopy_block in H.
  flatten H.
  simpl. apply PTree.gss.
Qed.

Lemma initialize_parcopy_block_correct2 :
  forall pc' x pc s s' INCR,
  initialize_parcopy_block pc' s = OK x s' INCR ->
  (st_parcopycode s) ! pc = Some nil ->
  (st_parcopycode s') ! pc = Some nil.
Proof.
  intros.
  case_eq (peq pc pc'); intros.
  + unfold initialize_parcopy_block in H.
    flatten H. simpl.
    apply PTree.gss.
  + unfold initialize_parcopy_block in H.
    flatten H. simpl.
    rewrite PTree.gso; auto.
Qed.

Lemma initialize_parcopy_blocks_correct_aux :
  forall l x pc s s' INCR,
  initialize_parcopy_blocks l s = OK x s' INCR ->
  (st_parcopycode s) ! pc = Some nil ->
  (st_parcopycode s') ! pc = Some nil.
Proof.
  induction l; intros; simpl in *.
  inv H. auto.
  simpl in H.
  monadInv H.
  assert ((st_parcopycode s0) ! pc = Some nil).
  eapply initialize_parcopy_block_correct2; eauto.
  eauto.
Qed.

Lemma initialize_parcopy_blocks_correct :
  forall l x pc s s' INCR,
  initialize_parcopy_blocks l s = OK x s' INCR ->
  In pc l ->
  (st_parcopycode s') ! pc = Some nil.
Proof.
  induction l; intros.
  go.
  simpl in *.
  monadInv H.
  destruct H0; go.
  rewrite H in *.
  assert ((st_parcopycode s0) ! pc = Some nil).
  eapply initialize_parcopy_block_correct; eauto.
  eapply initialize_parcopy_blocks_correct_aux; eauto.
Qed.

Global Hint Resolve initialize_parcopy_blocks_correct: core.

Lemma initialize_parcopy_blocks_correct_parcother :
  forall l x pc s s' INCR,
  initialize_parcopy_blocks l s = OK x s' INCR ->
  ~ In pc l ->
  (st_parcopycode s) ! pc = (st_parcopycode s') ! pc.
Proof.
  induction l; intros.
  + simpl in H. unfold ret in H.
    assert (s = s') by congruence.
    congruence.
  + simpl in *.
    monadInv H.
    replace ((st_parcopycode s') ! pc)
      with ((st_parcopycode s0) ! pc).
    unfold initialize_parcopy_block in EQ.
    replace (st_parcopycode s0)
      with (PTree.set a nil (st_parcopycode s)).
    rewrite PTree.gso. auto. auto.
    destruct s0; simpl; congruence.
    eapply IHl; eauto.
Qed.

Lemma initialize_parcopy_blocks_correct_other :
  forall l u s s' INCR,
  initialize_parcopy_blocks l s = OK u s' INCR ->
  st_phicode s = st_phicode s'.
Proof.
  induction l; intros.
  + unfold initialize_parcopy_blocks in H.
    unfold ret in H. congruence.
  + simpl in *.
    monadInv H.
    replace (st_phicode s) with (st_phicode s0).
    eauto.
    unfold initialize_parcopy_block in EQ.
    destruct s0; simpl; congruence.
Qed.

Inductive gen_new_regs_spec (maxreg : positive)
    (fs_init : positive)
    : positive -> list reg -> list reg -> Prop :=
| gen_new_regs_spec_nil:
    forall (GNRSPECinitnil: Plt maxreg fs_init),
    gen_new_regs_spec maxreg fs_init fs_init
      nil nil
| gen_new_regs_spec_cons:
    forall arg args arg' args' fs_max
    (GNRSPECinit: arg' = fs_init)
    (GNRSPECold: Ple arg maxreg)
    (GNRSPECfresh: Plt maxreg arg')
    (GNRSPECrec:
      gen_new_regs_spec maxreg (Pos.succ fs_init) fs_max
        args args'),
    gen_new_regs_spec maxreg fs_init fs_max
      (arg :: args) (arg' :: args').

Lemma gen_new_regs_spec_incr :
  forall maxreg fs_init fs_max args args',
  gen_new_regs_spec maxreg fs_init fs_max
    args args' ->
  Ple fs_init fs_max.
Proof.
  intros.
  induction H; intros.
  apply Ple_refl.
  apply Ple_trans with (Pos.succ fs_init).
  apply Ple_succ.
  assumption.
Qed.

Global Hint Resolve gen_new_regs_spec_incr: core.

Lemma gen_new_regs_spec_ple_arg_maxreg :
  forall maxreg fs_init fs_max args args',
  gen_new_regs_spec maxreg fs_init fs_max
    args args' ->
  forall k arg,
    nth_error args k = Some arg ->
  Ple arg maxreg.
Proof.
  intros until args'.
  intro H. induction H; intros.
  + destruct k; simpl in *; unfold Specif.error in *;
      congruence.
  + destruct k; simpl in *; unfold value in *; go.
Qed.

Lemma gen_new_regs_spec_plt_maxreg_arg' :
  forall maxreg fs_init fs_max args args',
  gen_new_regs_spec maxreg fs_init fs_max
    args args' ->
  forall k arg',
    nth_error args' k = Some arg' ->
  Plt maxreg arg'.
Proof.
  intros until args'.
  intro H. induction H; intros.
  + destruct k; simpl in *; unfold Specif.error in *;
      congruence.
  + destruct k; simpl in *; unfold value in *; go.
Qed.

Lemma gen_new_regs_spec_max_in :
  forall maxreg fs_init fs_max args args',
  gen_new_regs_spec maxreg fs_init fs_max
    args args' ->
  (forall arg', In arg' args' -> Plt arg' fs_max).
Proof.
  intros until args'.
  intro H.
  induction H; intros arg0' Inargs'. inv Inargs'.
  simpl in *.
  destruct Inargs' as [EQ | Inargs'].
  + rewrite <- EQ.
    assert (Plt arg' fs_max). (* Coq needs help *)
    rewrite GNRSPECinit.
    apply Plt_Ple_trans with (Pos.succ fs_init).
    apply Plt_succ.
    eapply gen_new_regs_spec_incr; eauto.
    auto.
  + eauto.
Qed.

Lemma gen_new_regs_spec_min_in :
  forall maxreg fs_init fs_max args args',
  gen_new_regs_spec maxreg fs_init fs_max
    args args' ->
  (forall arg', In arg' args' -> Ple fs_init arg').
Proof.
  intros until args'.
  intro H.
  induction H; intros arg0' Inargs'. inv Inargs'.
  simpl in *.
  destruct Inargs' as [EQ | Inargs'].
  + rewrite <- EQ.
    assert (Ple fs_init arg'). (* Coq needs help *)
    rewrite GNRSPECinit.
    apply Ple_refl.
    auto.
  + assert (Ple (Pos.succ fs_init) arg0') by eauto.
    apply Ple_trans with (Pos.succ fs_init).
    apply Ple_succ.
    auto.
Qed.

Global Hint Resolve gen_new_regs_spec_min_in: core.

Lemma gen_new_regs_spec_nthNotNonefromNotNone :
  forall maxreg fs_init fs_max args args',
  gen_new_regs_spec maxreg fs_init fs_max
    args args' ->
  forall k,
  nth_error args k <> None
  -> nth_error args' k <> None.
Proof.
  intros until args'. intro H. induction H.
  + intros. auto.
  + intros.
    destruct k; simpl in *.
    - unfold value in *. congruence.
    - eauto.
Qed.

Global Hint Resolve gen_new_regs_spec_nthNotNonefromNotNone: core.

Lemma gen_new_regs_spec_nthNotNonetoNotNone :
  forall maxreg fs_init fs_max args args',
  gen_new_regs_spec maxreg fs_init fs_max
    args args' ->
  forall k,
  nth_error args' k <> None
  -> nth_error args k <> None.
Proof.
  intros until args'. intro H. induction H.
  + intros. auto.
  + intros.
    destruct k; simpl in *.
    - unfold value in *. congruence.
    - eauto.
Qed.

Global Hint Resolve gen_new_regs_spec_nthNotNonetoNotNone: core.

Lemma gen_new_regs_correct :
  forall args s s' args' INCR maxreg,
  (Plt maxreg (next_fresh_reg s)) ->
  (forall arg, In arg args -> Ple arg maxreg) ->
  gen_new_regs args s = OK args' s' INCR ->
  gen_new_regs_spec maxreg (next_fresh_reg s)
    (next_fresh_reg s') args args'.
Proof.
  induction args; intros.
  + simpl in *.
    unfold ret in *.
    assert (RW: args' = nil) by congruence.
    rewrite RW in *.
    assert (RW2: s = s') by congruence.
    rewrite RW2 in *.
    apply gen_new_regs_spec_nil.
    auto.
  + simpl in *.
    monadInv H1.
    assert (EQfs: x =  (next_fresh_reg s)).
    { unfold gen_newreg in EQ. go. }
    apply gen_new_regs_spec_cons; auto.
    - assert (Plt maxreg x). (* Coq needs help *)
      rewrite EQfs. auto.
      auto.
    - assert (NextFs: Pos.succ (next_fresh_reg s) =
        (next_fresh_reg s0)).
      unfold gen_newreg in EQ. go.
      rewrite NextFs.
      apply IHargs with (INCR := INCR2); auto.
      rewrite <- NextFs.
      apply Plt_Ple_trans with (next_fresh_reg s);
        auto.
      apply Ple_succ.
Qed.

Global Hint Resolve gen_new_regs_correct: core.

Lemma gen_new_regs_correct_parcode :
  forall args s args' s' INCR,
  gen_new_regs args s = OK args' s' INCR ->
  st_parcopycode s = st_parcopycode s'.
Proof.
  induction args; intros.
  + unfold gen_new_regs in *.
    unfold ret in *.
    congruence.
  + simpl in *.
    monadInv H.
    unfold gen_newreg in *.
    replace (st_parcopycode s) with (st_parcopycode s0).
    eapply IHargs; eauto.
    go.
Qed.

Global Hint Resolve gen_new_regs_correct_parcode: core.

Lemma gen_new_regs_correct_phicode :
  forall args s args' s' INCR,
  gen_new_regs args s = OK args' s' INCR ->
  st_phicode s = st_phicode s'.
Proof.
  induction args; intros.
  + unfold gen_new_regs in *.
    unfold ret in *.
    congruence.
  + simpl in *.
    monadInv H.
    unfold gen_newreg in *.
    replace (st_phicode s) with (st_phicode s0).
    eapply IHargs; eauto.
    go.
Qed.

Global Hint Resolve gen_new_regs_correct_phicode: core.

Lemma add_parcopies_correct_fresh :
  forall parcopies copy_nodes s u s' INCR,
  add_parcopies parcopies copy_nodes s = OK u s' INCR ->
  (next_fresh_reg s) = (next_fresh_reg s').
Proof.
  induction parcopies; intros.
  + simpl in *. destruct copy_nodes; unfold ret in *;
      unfold error in *; congruence.
  + simpl in *.
    destruct copy_nodes; unfold error in *; try congruence.
    monadInv H.
    replace (next_fresh_reg s') with (next_fresh_reg s0).
    eapply IHparcopies; eauto.
    unfold add_parcopy in EQ0.
    flatten EQ0. auto.
Qed.

Global Hint Resolve add_parcopies_correct_fresh: core.

Lemma add_parcopies_correct_phicode :
  forall parcopies copy_nodes s u s' INCR,
  add_parcopies parcopies copy_nodes s = OK u s' INCR ->
  st_phicode s = st_phicode s'.
Proof.
  induction parcopies; intros.
  + simpl in *. destruct copy_nodes; unfold ret in *;
      unfold error in *; congruence.
  + simpl in *.
    destruct copy_nodes; unfold error in *; try congruence.
    monadInv H.
    replace (st_phicode s') with (st_phicode s0).
    eapply IHparcopies; eauto.
    unfold add_parcopy in EQ0.
    flatten EQ0. auto.
Qed.

Global Hint Resolve add_parcopies_correct_phicode: core.

Inductive add_parcopies_spec (pcode1 : parcopycode) :
  list parcopy -> list node
    -> parcopycode ->
  Prop :=
| add_parcopies_spec_nil:
    add_parcopies_spec pcode1 nil nil pcode1
| add_parcopies_spec_cons:
    forall pc parcb pcode2 parcopy copy_nodes
      parcopies
    (APSPECparcb: pcode2 ! pc = Some parcb)
    (APSPECnodup:  ~ In pc copy_nodes)
    (APSPECrec:
      add_parcopies_spec pcode1 parcopies copy_nodes
        pcode2),
    add_parcopies_spec pcode1 (parcopy :: parcopies)
      (pc :: copy_nodes)
      (PTree.set pc (parcopy :: parcb) pcode2).

Lemma add_parcopies_spec_correct_other :
  forall pcode1 parcopies copy_nodes pcode2,
  add_parcopies_spec pcode1 parcopies copy_nodes pcode2 ->
  forall pc,
  ~ In pc copy_nodes ->
  pcode1 ! pc = pcode2 ! pc.
Proof.
  intros until pcode2.
  intro H. induction H; auto; intros.
  simpl in *.
  assert (pc <> pc0).
  auto.
  rewrite PTree.gso.
  auto. auto.
Qed.

Global Hint Resolve add_parcopies_spec_correct_other: core.

Lemma add_parcopies_k_notSomefromNone :
  forall parcode1 parcopies copy_nodes parcode2,
  add_parcopies_spec parcode1 parcopies
    copy_nodes parcode2 ->
  forall pc,
  parcode2 ! pc <> None -> parcode1 ! pc <> None.
Proof.
  intros until parcode2. intro H. induction H; intros.
  auto.
  case_eq (peq pc pc0); intros.
  + rewrite e in *.
    rewrite PTree.gss in H0.
    apply IHadd_parcopies_spec. congruence.
  + rewrite PTree.gso in H0; auto.
Qed.

Lemma add_parcopies_k :
  forall pcode1 parcopies copy_nodes pcode2,
  add_parcopies_spec pcode1 parcopies copy_nodes pcode2 ->
  forall k pred parcopy parcb,
  nth_error copy_nodes k = Some pred ->
  nth_error parcopies k = Some parcopy ->
  pcode1 ! pred = Some parcb ->
  pcode2 ! pred = Some (parcopy :: parcb).
Proof.
  intros until pcode2.
  intro H.
  induction H; intros.
  generalize nth_error_nil_notSome_node; intros; congruence.
  case_eq (peq pc pred); intros.
  + rewrite e in *.
    rewrite PTree.gss.
    destruct k.
    - simpl in *. unfold value in *.
      replace (pcode1 ! pred) with (pcode2 ! pred) in H2.
      congruence.
      symmetry. eauto.
    - simpl in *.
      assert (nth_error copy_nodes k <> Some pred).
      apply notIn_notnth; auto.
      assert (nth_error copy_nodes k = Some pred)
        by auto. (* Coq needs help *)
      congruence.
  + rewrite PTree.gso; auto.
    destruct k.
    - simpl in *. unfold value in *. congruence.
    - simpl in *.
      apply IHadd_parcopies_spec with (k := k); auto.
Qed.

Lemma add_parcopies_pred_exist_parcb :
  forall pcode1 parcopies copy_nodes pcode2,
  add_parcopies_spec pcode1 parcopies copy_nodes pcode2 ->
  forall pred (parcb parcb0 : parcopyblock),
  In pred copy_nodes ->
  pcode1 ! pred = Some parcb0 ->
  exists parcb,
  pcode2 ! pred = Some parcb.
Proof.
  intros until pcode2. intro H. induction H; intros.
  exists parcb0; auto.
  case_eq (peq pred pc); intros.
  + rewrite e in *.
    rewrite PTree.gss.
    exists (parcopy :: parcb). auto.
  + inv H0. congruence.
    rewrite PTree.gso; auto.
    eauto.
Qed.

Lemma add_parcopies_nth_notNonetonotNone :
  forall pcode1 parcopies copy_nodes pcode2,
  add_parcopies_spec pcode1 parcopies copy_nodes pcode2 ->
  forall k,
  nth_error copy_nodes k <> None ->
  nth_error parcopies k <> None.
Proof.
  intros until pcode2. intro H. induction H; intros.
  + destruct k; simpl in *; intros;
      unfold Specif.error in H; congruence.
  + destruct k; simpl in *; intros.
    - unfold value in *; congruence.
    - auto.
Qed.

Global Hint Resolve add_parcopies_nth_notNonetonotNone: core.

Lemma add_parcopies_correct :
  forall copy_nodes s parcopies u s' INCR,
  NoDup copy_nodes ->
  add_parcopies parcopies copy_nodes s = OK u s' INCR ->
  add_parcopies_spec (st_parcopycode s) parcopies copy_nodes
    (st_parcopycode s').
Proof.
  induction copy_nodes; intros s parcopies u s' INCR HNoDups H.
  + simpl in H.
    destruct parcopies.
    unfold add_parcopies in H; unfold ret in H.
    assert (RW: s = s') by congruence.
    rewrite RW.
    constructor.
    unfold add_parcopies in H; unfold error in H; congruence.
  + simpl in H.
    destruct parcopies.
    unfold add_parcopies in H; unfold error in H; try congruence.
    monadInv H.
    assert ((st_parcopycode s0) ! a <> None).
    unfold add_parcopy in EQ0.
    flatten EQ0.
    case_eq ((st_parcopycode s0) ! a); intros; try congruence.
    replace (st_parcopycode s') with
      (PTree.set a (p :: p0) (st_parcopycode s0)).
    eapply add_parcopies_spec_cons; eauto.
    inv HNoDups. auto.
    eapply IHcopy_nodes; eauto.
    inv HNoDups. auto.
    unfold add_parcopy in EQ0.
    flatten EQ0. simpl. congruence.
Qed.

Global Hint Resolve add_parcopies_correct: core.

Inductive build_parcopies_spec :
  list reg -> list reg -> list parcopy -> Prop :=
| build_parcopies_spec_nil:
    build_parcopies_spec nil nil nil
| build_parcopies_spec_cons:
    forall arg arg' args args' parcopies,
    build_parcopies_spec args args' parcopies ->
    build_parcopies_spec (arg :: args) (arg' :: args')
      (Iparcopy arg arg' :: parcopies).

Lemma build_parcopies_correct:
  forall args args' s parcopies s' INCR,
  build_parcopies args args' s = OK parcopies s' INCR ->
  build_parcopies_spec args args' parcopies.
Proof.
  induction args; intros; simpl in *; flatten H;
    unfold error in H; try congruence.
  + unfold ret in H. go.
  + monadInv H. go.
Qed.

Global Hint Resolve build_parcopies_correct: core.

Lemma build_parcopies_nth:
  forall args args' parcopies,
  build_parcopies_spec args args' parcopies ->
  forall k arg arg',
  nth_error args k = Some arg ->
  nth_error args' k = Some arg' ->
  nth_error parcopies k = Some (Iparcopy arg arg').
Proof.
  intros until parcopies. intro H. induction H; intros.
  + assert (nth_error (nil:list reg) (k:nat) = None).
    auto. congruence.
  + destruct k; simpl in *.
    - unfold value in *. congruence.
    - eauto.
Qed.

Global Hint Resolve build_parcopies_nth: core.

Lemma build_parcopies_nth_revargs:
  forall args args' parcopies,
  build_parcopies_spec args args' parcopies ->
  forall k,
  nth_error parcopies k <> None ->
  nth_error args k <> None.
Proof.
  intros until parcopies. intro H. induction H; intros.
  + destruct k; simpl in *; unfold Specif.error in H;
    congruence.
  + destruct k; simpl in *.
    - unfold value in *. congruence.
    - eauto.
Qed.

Global Hint Resolve build_parcopies_nth_revargs: core.

Lemma build_parcopies_correct_phicode:
  forall args args' s parcopies s' INCR,
  build_parcopies args args' s = OK parcopies s' INCR ->
  st_phicode s = st_phicode s'.
Proof.
  induction args; intros.
  + unfold build_parcopies in H.
    flatten H. unfold ret in H.
    congruence. unfold error in H. congruence.
  + simpl in *. flatten H.
    unfold error in H. congruence.
    monadInv H. eauto.
Qed.

Global Hint Resolve build_parcopies_correct_phicode: core.

Lemma build_parcopies_correct_fresh:
  forall args args' s parcopies s' INCR,
  build_parcopies args args' s = OK parcopies s' INCR ->
  (next_fresh_reg s) = (next_fresh_reg s').
Proof.
  induction args; intros.
  + unfold build_parcopies in H.
    flatten H. unfold ret in H.
    congruence. unfold error in H. congruence.
  + simpl in *. flatten H.
    unfold error in H. congruence.
    monadInv H. eauto.
Qed.

Global Hint Resolve build_parcopies_correct_fresh: core.

Lemma build_parcopies_correct_parcopycode:
  forall args args' s parcopies s' INCR,
  build_parcopies args args' s = OK parcopies s' INCR ->
  st_parcopycode s = st_parcopycode s'.
Proof.
  induction args; intros.
  + unfold build_parcopies in H.
    flatten H. unfold ret in H.
    congruence. unfold error in H. congruence.
  + simpl in *. flatten H.
    unfold error in H. congruence.
    monadInv H. eauto.
Qed.

Global Hint Resolve build_parcopies_correct_parcopycode: core.

Variant add_parcopy_spec (pc : node): reg -> reg -> parcopycode -> parcopycode -> Prop :=
| add_parcopy_spec_intro:
    forall dst' dst parcode parcb,
    parcode ! pc = Some parcb ->
    add_parcopy_spec pc dst' dst
      parcode (PTree.set pc
        ((Iparcopy dst' dst) :: parcb) parcode).

Lemma add_parcopy_correct:
  forall dst' dst pc s u s' INCR,
  add_parcopy (Iparcopy dst' dst) pc s = OK u s' INCR ->
  add_parcopy_spec pc dst' dst
    (st_parcopycode s) (st_parcopycode s').
Proof.
  intros.
  unfold add_parcopy in H.
  flatten H; go.
Qed.

Global Hint Resolve add_parcopy_correct: core.

Lemma add_parcopy_correct_phicode:
  forall dst' dst pc s u s' INCR,
  add_parcopy (Iparcopy dst' dst) pc s = OK u s' INCR ->
  st_phicode s = st_phicode s'.
Proof.
  intros. unfold add_parcopy in H. flatten H. auto.
Qed.

Global Hint Resolve add_parcopy_correct_phicode: core.

Lemma add_parcopy_correct_fresh:
  forall dst' dst pc s u s' INCR,
  add_parcopy (Iparcopy dst' dst) pc s = OK u s' INCR ->
  (next_fresh_reg s) = (next_fresh_reg s').
Proof.
  intros. unfold add_parcopy in H. flatten H. auto.
Qed.

Global Hint Resolve add_parcopy_correct_fresh: core.

Lemma add_new_phi_correct_fresh:
  forall dst' args' pc s u s' INCR,
  add_new_phi dst' args' pc s = OK u s' INCR ->
  (next_fresh_reg s) =  (next_fresh_reg s').
Proof.
  intros.
  unfold add_new_phi in H.
  flatten H. auto.
Qed.

Global Hint Resolve add_new_phi_correct_fresh: core.

Lemma add_new_phi_correct_parcode:
  forall dst' args' pc s u s' INCR,
  add_new_phi dst' args' pc s = OK u s' INCR ->
  st_parcopycode s = st_parcopycode s'.
Proof.
  intros.
  unfold add_new_phi in H.
  flatten H. auto.
Qed.

Global Hint Resolve add_new_phi_correct_parcode: core.

Lemma add_new_phi_correct_phicodeNotNone:
  forall dst' args' pc s u s' INCR,
  add_new_phi dst' args' pc s = OK u s' INCR ->
  (st_phicode s) ! pc <> None.
Proof.
  intros.
  unfold add_new_phi in H.
  flatten H.
Qed.

Global Hint Resolve add_new_phi_correct_phicodeNotNone: core.

Variant add_new_phi_spec (pc : node) : reg -> list reg -> phicode -> phicode -> Prop :=
| add_new_phi_spec_intro:
    forall dst' args' phicode phib',
      phicode ! pc = Some phib' ->
      add_new_phi_spec pc dst' args'
                       phicode
                       (PTree.set pc (Iphi args' dst' :: phib') phicode).

Lemma add_new_phi_correct:
  forall dst' args' pc s u s' INCR,
  add_new_phi dst' args' pc s = OK u s' INCR ->
  add_new_phi_spec pc dst' args'
    (st_phicode s) (st_phicode s').
Proof.
  intros.
  unfold add_new_phi in H.
  flatten H; go.
Qed.

Global Hint Resolve add_new_phi_correct: core.

Inductive handle_phi_block_spec (maxreg: positive)
  (preds : list node) (pc : node)
  : phiblock -> positive -> positive ->
    phicode -> phicode ->
    parcopycode -> parcopycode ->
    Prop :=
| handle_phi_block_spec_nil:
    forall phicode parcode fs_init,
    handle_phi_block_spec maxreg preds pc
      nil fs_init fs_init
      phicode phicode
      parcode parcode
| handle_phi_block_spec_cons:
    forall args dst args' dst'
      block
      fs_init fs_next fs_last
      parcopies
      parcode1 parcode2 parcode3 parcode4
      phicode1 phicode2 phicode3

    (PBSPECargsfresh:
      (forall arg, In arg args -> Ple arg maxreg))
    (PBSPECdst_old: Ple dst maxreg)
    (PBSPECfs_init_fresh:  Plt maxreg fs_init)

    (PBSPECnewreg: dst' = fs_init)
    (PBSPECgen_new_regs:
      gen_new_regs_spec maxreg (Pos.succ fs_init) fs_next
        args args')

    (PBSPECrec:
      handle_phi_block_spec maxreg preds pc
        block fs_next fs_last
        phicode1 phicode2 parcode1 parcode2)

    (PBSPECparcopies:
      build_parcopies_spec args args' parcopies)
    (PBSPECadd_parcopy:
      add_parcopy_spec pc dst' dst parcode2 parcode3)
    (PBSPECadd_parcopies:
      add_parcopies_spec parcode3 parcopies preds parcode4)
    (PBSPECnew_phi:
      add_new_phi_spec pc dst' args' phicode2 phicode3),

    handle_phi_block_spec maxreg preds pc
      (Iphi args dst :: block) fs_init fs_last
      phicode1 phicode3
      parcode1 parcode4.

Lemma handle_phi_block_spec_incr :
  forall maxreg preds pc block fs_init fs_last
    phicode1 phicode2 parcode1 parcode2,
  handle_phi_block_spec maxreg preds pc
    block fs_init fs_last phicode1 phicode2
      parcode1 parcode2 ->
  Ple fs_init fs_last.
Proof.
  intros. induction H.
  apply Ple_refl.
  apply Ple_trans with fs_next; auto.
  apply Ple_trans with (Pos.succ fs_init); eauto.
  apply Ple_succ.
Qed.

Global Hint Resolve handle_phi_block_spec_incr: core.

Lemma handle_phi_block_spec_ple_init_arg :
  forall maxreg preds pc block fs_init fs_last
    phicode1 phicode2 parcode1 parcode2,
  handle_phi_block_spec maxreg preds pc
    block fs_init fs_last
    phicode1 phicode2 parcode1 parcode2 ->
  forall arg' args' dst' phib',
  phicode1 ! pc = Some nil ->
  phicode2 ! pc = Some phib' ->
  In (Iphi args' dst') phib' ->
  In arg' args' ->
  Ple fs_init arg'.
Proof.
  intros until parcode2.
  intro H; induction H; intros.
  + assert (RW: phib' = nil) by congruence.
    rewrite RW in *.
    inv H1.
  + apply Ple_trans with (Pos.succ fs_init).
    apply Ple_succ.
    inv PBSPECnew_phi.
    rewrite PTree.gss in H1.
    assert (RW: Iphi args' fs_init :: phib'0 = phib')
      by congruence.
    rewrite <- RW in *.
    inv H2; go.
    apply Ple_trans with fs_next; eauto.
Qed.

Lemma handle_phi_block_spec_ple_init_dst :
  forall maxreg preds pc block fs_init fs_last
    phicode1 phicode2 parcode1 parcode2,
  handle_phi_block_spec maxreg preds pc
    block fs_init fs_last
    phicode1 phicode2 parcode1 parcode2 ->
  forall args' dst' phib',
  phicode1 ! pc = Some nil ->
  phicode2 ! pc = Some phib' ->
  In (Iphi args' dst') phib' ->
  Ple fs_init dst'.
Proof.
  intros until parcode2.
  intro H; induction H; intros.
  + assert (RW: phib' = nil) by congruence.
    rewrite RW in *.
    inv H1.
  + inv PBSPECnew_phi.
    rewrite PTree.gss in H1.
    assert (RW: Iphi args' fs_init :: phib'0 = phib')
      by congruence.
    rewrite <- RW in *.
    inv H2; go.
    assert (EQdst: fs_init = dst'0) by congruence.
    rewrite EQdst.
    apply Ple_refl.
    apply Ple_trans with fs_next; eauto.
    apply Ple_trans with (Pos.succ fs_init).
    apply Ple_succ.
    eauto.
Qed.

Ltac normalize_new_phi :=
  match goal with
  | [ H: ((PTree.set ?pc (Iphi ?args'0 ?dst'0 :: ?phib'0)
          ?phicode) ! ?pc =
          Some (Iphi ?args' ?dst' :: ?phib'))
    |- _ ] =>
      rewrite PTree.gss in H;
      assert (EQ1: args' = args'0) by congruence;
      assert (EQ2: dst' = dst'0) by congruence;
      assert (EQ3: phib' = phib'0) by congruence;
      rewrite EQ1 in *; rewrite EQ2 in *;
      rewrite EQ3 in *
  | _ => idtac
  end.

Lemma handle_phi_block_spec_plt_arg :
  forall maxreg preds pc block fs_next fs_last
    phicode1 phicode2 parcode1 parcode2,
  handle_phi_block_spec maxreg preds pc
    block fs_next fs_last
    phicode1 phicode2 parcode1 parcode2 ->
  phicode1 ! pc = Some nil ->
  forall phib' dst' args' (arg':reg)
    args'' arg'' arg' dst'',
  phicode2 ! pc = Some (Iphi args' dst' :: phib') ->
  In (Iphi args'' dst'') phib' ->
  In arg' args' ->
  In arg'' args'' ->
  Plt arg' arg''.
Proof.
  intros.
  induction H; try congruence.
  apply Plt_Ple_trans with fs_next;
    inv PBSPECnew_phi; normalize_new_phi.
  eapply gen_new_regs_spec_max_in; eauto.
  eapply handle_phi_block_spec_ple_init_arg; eauto.
Qed.

Lemma handle_phi_block_spec_plt_dst :
  forall maxreg preds pc block fs_next fs_last
    phicode1 phicode2 parcode1 parcode2,
  handle_phi_block_spec maxreg preds pc
    block fs_next fs_last
    phicode1 phicode2 parcode1 parcode2 ->
  phicode1 ! pc = Some nil ->
  forall phib' dst' args' (arg':reg)
    args'' dst'',
  phicode2 ! pc = Some (Iphi args' dst' :: phib') ->
  In (Iphi args'' dst'') phib' ->
  Plt dst' dst''.
Proof.
  intros.
  induction H; try congruence.
  apply Plt_Ple_trans with fs_next;
    inv PBSPECnew_phi; normalize_new_phi.
  apply Plt_Ple_trans with (Pos.succ fs_init).
  apply Plt_succ.
  eapply gen_new_regs_spec_incr; eauto.
  eapply handle_phi_block_spec_ple_init_dst; eauto.
Qed.

Lemma handle_phi_block_spec_fresh1 :
  forall maxreg preds pc block fs_next fs_last
    phicode1 phicode2 parcode1 parcode2,
  handle_phi_block_spec maxreg preds pc
    block fs_next fs_last
    phicode1 phicode2 parcode1 parcode2 ->
  forall arg' k phib' dst' args',
  phicode1 ! pc = Some nil ->
  phicode2 ! pc = Some (Iphi args' dst' :: phib') ->
  forall (args'' : list reg) (arg'' dst'' : reg),
  In (Iphi args'' dst'') phib' ->
  nth_error args'' k = Some arg'' ->
  nth_error args' k = Some arg' ->
  arg' <> arg''.
Proof.
  intros.
  assert (Plt arg' arg'').
  assert (In arg'' args'').
  eauto.
  eapply handle_phi_block_spec_plt_arg; eauto.
  auto.
Qed.

Lemma handle_phi_block_spec_fresh2 :
  forall maxreg preds pc block fs_next fs_last
    phicode1 phicode2 parcode1 parcode2,
  handle_phi_block_spec maxreg preds pc
    block fs_next fs_last
    phicode1 phicode2 parcode1 parcode2 ->
  forall phib' dst' args',
  phicode1 ! pc = Some nil ->
  phicode2 ! pc = Some (Iphi args' dst' :: phib') ->
  forall (args'' : list reg) (arg'' dst'' : reg),
  In (Iphi args'' dst'') phib' ->
  dst' <> dst''.
Proof.
  intros.
  assert (Plt dst' dst'').
  eapply handle_phi_block_spec_plt_dst; eauto.
  auto.
Qed.

Lemma handle_phi_block_spec_fresh3 :
  forall maxreg preds pc,
  NoDup (pc :: preds) ->
  forall block fs_next fs_last
    phicode1 phicode2 parcode1 parcode2,
  handle_phi_block_spec maxreg preds pc
    block fs_next fs_last
    phicode1 phicode2 parcode1 parcode2 ->
  forall arg' k phib' dst' args',
  phicode1 ! pc = Some nil ->
  phicode2 ! pc = Some (Iphi args' dst' :: phib') ->
  forall args'' dst'',
  In (Iphi args'' dst'') phib' ->
  nth_error args' k = Some arg' ->
  arg' <> dst''.
Proof.
  intros.
  assert (Plt arg' dst'').
  inv H0; go.
  inv PBSPECnew_phi; normalize_new_phi.
  apply Plt_Ple_trans with fs_next0.
  eapply gen_new_regs_spec_max_in; eauto.
  eauto.
  eapply handle_phi_block_spec_ple_init_dst; eauto.
  auto.
Qed.

Lemma handle_phi_block_spec_exists_phib' :
  forall maxreg preds pc block fs_next fs_last
    phicode1 phicode2 parcode1 parcode2 phib,
  handle_phi_block_spec maxreg preds pc
    block fs_next fs_last
    phicode1 phicode2 parcode1 parcode2 ->
  phicode1 ! pc = Some phib ->
  exists phib',
  phicode2 ! pc = Some phib'.
Proof.
  intros.
  induction H.
  exists phib; auto.
  inv PBSPECnew_phi.
  exists (Iphi args' fs_init :: phib').
  rewrite PTree.gss. auto.
Qed.

Lemma handle_phi_block_spec_exists_parcb' :
  forall maxreg preds pc block fs_next fs_last
    phicode1 phicode2 parcode1 parcode2,
  NoDup (pc :: preds) ->
  handle_phi_block_spec maxreg preds pc
    block fs_next fs_last
    phicode1 phicode2 parcode1 parcode2 ->
  parcode1 ! pc = Some nil ->
  exists parcb',
  parcode2 ! pc = Some parcb'.
Proof.
  intros until parcode2. intros HNoDups H. induction H.
  exists nil; auto.
  intros.
  exploit IHhandle_phi_block_spec; auto.
  intros.
  destruct H1 as [parcb' H1].
  assert (EQparcother: parcode3 ! pc = parcode4 ! pc).
  eapply add_parcopies_spec_correct_other; eauto.
  inv HNoDups; auto.
  inv PBSPECadd_parcopy.
  rewrite PTree.gss in EQparcother.
  exists (Iparcopy fs_init dst :: parcb).
  auto.
Qed.

Lemma handle_phi_block_spec_exists_parcb :
  forall maxreg preds pc block fs_next fs_last
    phicode1 phicode2 parcode1 parcode2 pred,
  NoDup (pc :: preds) ->
  handle_phi_block_spec maxreg preds pc
    block fs_next fs_last
    phicode1 phicode2 parcode1 parcode2 ->
  In pred preds ->
  parcode1 ! pred = Some nil ->
  exists parcb,
  parcode2 ! pred = Some parcb.
Proof.
  intros until pred. intros HNoDups H. induction H.
  exists nil; auto.
  intros.
  exploit IHhandle_phi_block_spec; auto.
  intros.
  destruct H2 as [parcb H2].
  assert (EQparc: parcode2 ! pred = parcode3 ! pred).
  inv PBSPECadd_parcopy. rewrite PTree.gso; auto.
  inv HNoDups; auto. congruence.
  rewrite EQparc in *.
  eapply add_parcopies_pred_exist_parcb; eauto.
Qed.

Lemma handle_phi_block_spec_preserves_parcother :
  forall maxreg preds pc block fs_next fs_last
    phicode1 phicode2 parcode1 parcode2,
  handle_phi_block_spec maxreg preds pc
    block fs_next fs_last
    phicode1 phicode2 parcode1 parcode2 ->
  forall pc',
  NoDup (pc :: preds) ->
  pc' <> pc ->
  ~ In pc' preds ->
  parcode1 ! pc' = parcode2 ! pc'.
Proof.
  intros until parcode2.
  intro H. induction H; intros.
  + auto.
  + replace (parcode4 ! pc') with (parcode3 ! pc').
    replace (parcode3 ! pc') with (parcode2 ! pc').
    auto.
    inv PBSPECadd_parcopy. rewrite PTree.gso; auto.
    eauto.
Qed.

Lemma handle_phi_block_spec_preserves_phibother :
  forall maxreg preds pc block fs_next fs_last
    phicode1 phicode2 parcode1 parcode2,
  handle_phi_block_spec maxreg preds pc
    block fs_next fs_last
    phicode1 phicode2 parcode1 parcode2 ->
  forall pc',
  pc' <> pc ->
  phicode1 ! pc' = phicode2 ! pc'.
Proof.
  intros until parcode2.
  intro H. induction H; intros.
  + auto.
  + replace (phicode3 ! pc') with (phicode2 ! pc').
    auto.
    inv PBSPECnew_phi.
    rewrite PTree.gso; auto.
Qed.

Lemma handle_phi_block_correct :
  forall maxreg preds pc,
  NoDup (pc :: preds) ->
  forall block s u s' INCR,
  (forall args dst, In (Iphi args dst) block
    -> Ple dst maxreg) ->
  (forall args dst, In (Iphi args dst) block ->
    forall arg, In arg args -> Ple arg maxreg) ->
  (Plt maxreg (next_fresh_reg s)) ->
  handle_phi_block preds block pc s = OK u s' INCR ->
  handle_phi_block_spec maxreg preds pc
    block (next_fresh_reg s) (next_fresh_reg s')
    (st_phicode s) (st_phicode s')
    (st_parcopycode s) (st_parcopycode s').
Proof.
  intros maxreg preds pc HNoDups.
  induction block; intros s u s' INCR
    Hnotfreshdst Hnotfresharg Hfresh Hphib.
  + simpl in Hphib. unfold ret in Hphib.
    go.
  + unfold handle_phi_block in Hphib.
    destruct a.
    monadInv Hphib.
    fold handle_phi_block in EQ0.

    (* Some renames to keep things bearable *)
    rename r into dst.
    rename l into args.
    rename x0 into args'.
    rename x1 into u'.
    rename x2 into parcopies.
    rename x into dst'.
    rename x3 into u''.
    rename x4 into u'''.

    (* Steps (in order):

      States:
        s --> s0 --> s1 --> s2 --> s3 --> s4 --> s5 --> s'
          (1)    (2)    (3)    (4)    (5)    (6)    (7)

      (1) builds [dst']
      (2) builds [args']
      (3) induction hypothesis
      (4) builds [parcopies] from [args] and [args']
      (5) adds [Iparcopy dst' dst] to [parcb'] in [pc]
      (6) adds [parcopies] in predecessors
      (7) adds [Iphi args' dst'] in [pc]

    *)
    assert (Hdst': dst' = next_fresh_reg s).
    unfold gen_newreg in EQ. congruence.

    assert (freshs0: Plt maxreg (next_fresh_reg s0)).
    apply Plt_Ple_trans with  (next_fresh_reg s).
    auto.
    inversion INCR0; auto.

    assert (Hnew_regs_spec:
      gen_new_regs_spec maxreg
        (next_fresh_reg s0)  (next_fresh_reg s1)
        args args').
    eapply gen_new_regs_correct; eauto.

    assert (freshs1: Plt maxreg (next_fresh_reg s1)).
    apply Plt_Ple_trans with (next_fresh_reg s0).
    auto.
    inversion INCR2; auto.

    assert(IHspec:
      handle_phi_block_spec maxreg preds pc block
        (next_fresh_reg s1)  (next_fresh_reg s2)
        (st_phicode s1) (st_phicode s2)
        (st_parcopycode s1) (st_parcopycode s2)).
    eapply IHblock; eauto.

    case_eq ((st_phicode s2) ! pc); intros. (* not None *)

    assert (Hbuild_parcopies_spec:
      build_parcopies_spec args args' parcopies)
      by eauto.

    assert (Hadd_parcopy_spec:
      add_parcopy_spec pc dst' dst
      (st_parcopycode s3) (st_parcopycode s4))
      by eauto.

    inversion HNoDups.
    assert (Hadd_parcopies_spec:
      add_parcopies_spec
        (st_parcopycode s4)
        parcopies preds
        (st_parcopycode s5))
      by eauto.

    assert (Hadd_new_phi_spec:
      add_new_phi_spec pc dst' args'
      (st_phicode s5) (st_phicode s'))
      by eauto.
    { apply handle_phi_block_spec_cons
        with (args' := args')
          (dst' := dst')
          (fs_next := (next_fresh_reg s1))
          (parcopies := parcopies)
          (parcode2 := st_parcopycode s2)
          (parcode3 := st_parcopycode s4)
          (phicode2 := st_phicode s2); eauto.

      - unfold gen_newreg in EQ. go.
      - assert (s2s'fs: (next_fresh_reg s') =
           (next_fresh_reg s2)).
        { symmetry.
          replace  (next_fresh_reg s')
            with  (next_fresh_reg s5).
          replace  (next_fresh_reg s5)
            with (next_fresh_reg s4).
          replace  (next_fresh_reg s4)
            with  (next_fresh_reg s3).
          eauto. eauto. eauto. eauto. }
        rewrite s2s'fs.
        assert (ss1parcode: st_parcopycode s =
          st_parcopycode s1).
        { replace (st_parcopycode s1)
            with (st_parcopycode s0).
          eauto. unfold gen_newreg in EQ. go.
          eauto. }
        rewrite ss1parcode.
        assert (ss1phicode: st_phicode s =
          st_phicode s1).
        { replace (st_phicode s1) with (st_phicode s0).
          eauto. unfold gen_newreg in EQ. go.
          eauto. }
        rewrite ss1phicode.
        auto.
      - replace (st_parcopycode s2)
          with (st_parcopycode s3).
        auto.
        symmetry. eauto.
      - replace (st_parcopycode s')
          with (st_parcopycode s5); eauto.
      - replace (st_phicode s2) with
          (st_phicode s3).
        replace (st_phicode s3) with
          (st_phicode s4).
        replace (st_phicode s4) with
          (st_phicode s5).
        auto.
        symmetry. eauto.
        symmetry. eauto.
        symmetry. eauto. }
    assert (s2s5phicode: st_phicode s2 = st_phicode s5).
    { replace (st_phicode s2) with (st_phicode s3).
      replace (st_phicode s3) with (st_phicode s4).
      eauto. symmetry. eauto.
      symmetry.
      eapply build_parcopies_correct_phicode; eauto. }
    rewrite s2s5phicode in H.
    assert ((st_phicode s5) ! pc <> None) by eauto.
    congruence.
Qed.

Lemma handle_phi_block_spec_equiv_phib :
  forall maxreg preds pc,
  NoDup (pc :: preds) ->
  forall phib fs_init fs_last
    phicode1 phicode2 parcode1 parcode2
    k pred,
  handle_phi_block_spec maxreg preds pc
    phib fs_init fs_last
    phicode1 phicode2
    parcode1 parcode2 ->
  forall parcb parcb' phib',
  parcode1 ! pc = Some nil ->
  phicode1 ! pc = Some nil ->
  parcode2 ! pc = Some parcb' ->
  phicode2 ! pc = Some phib' ->
  nth_error preds k = Some pred ->
  parcode1 ! pred = Some nil ->
  parcode2 ! pred = Some parcb ->
  equiv_phib_spec maxreg k phib parcb phib' parcb'.
Proof.
  intros until pc. intro HNoDups.
  intros until pred. intro H.
  assert (Horig:
    handle_phi_block_spec maxreg preds pc
      phib fs_init fs_last
      phicode1 phicode2 parcode1 parcode2)
    by auto. (* conserve H *)

  induction H; intros.
  { replace parcb with (nil:parcopyblock).
    replace parcb' with (nil:parcopyblock).
    replace phib' with (nil:phiblock).
    apply equiv_phib_spec_nil.
    congruence.
    congruence.
    congruence. }
  case_eq (nth_error args k);
  case_eq (nth_error args' k).
  {
    intros arg' nth_args' arg nth_args.
    inv PBSPECnew_phi.
    replace phib' with
      (Iphi args' fs_init :: phib'0) in *.
    inv PBSPECadd_parcopy.
    set (parcode3 := PTree.set pc
      (Iparcopy fs_init dst :: parcb0) parcode2) in *.
    replace parcb' with
      (Iparcopy fs_init dst :: parcb0) in *.
    {
      case_eq (parcode3 ! pred); intros.
      + assert (parcode4 ! pred =
          Some (Iparcopy arg arg' :: l)).
        eapply add_parcopies_k; eauto.
        assert (RW: parcb = Iparcopy arg arg' :: l)
          by congruence.
        rewrite RW.
        assert (parcode2 ! pred = Some l).
        { unfold parcode3 in *. rewrite PTree.gso in H9.
          auto. inv HNoDups.
          assert (In pred preds) by eauto.
          congruence. }
        apply equiv_phib_spec_cons; auto.
        - intros.
          eapply handle_phi_block_spec_fresh1; eauto.
        - intros.
          assert (fs_init <> dst'').
          eapply handle_phi_block_spec_fresh2; eauto.
          auto.
        - intros.
          eapply handle_phi_block_spec_fresh3; eauto.
        - eapply gen_new_regs_spec_ple_arg_maxreg;
            eauto.
        - eapply gen_new_regs_spec_plt_maxreg_arg';
            eauto.
      + assert (parcode3 ! pred <> None).
        eapply add_parcopies_k_notSomefromNone; eauto.
        assert (parcode4 ! pred = Some parcb)
          by auto. (* Coq needs help *)
        congruence.
        congruence.
    }
    assert (parc3parc4: parcode3 ! pc = parcode4 ! pc).
    inv HNoDups. eauto.
    unfold parcode3 in parc3parc4.
    rewrite PTree.gss in parc3parc4.
    congruence.
    rewrite PTree.gss in H3. congruence.
  }
  { intros.
    assert (nth_error args k <> None).
    congruence.
    assert (nth_error args' k <> None).
    eauto.
    congruence. }
  { intros.
    assert (nth_error args' k <> None).
    congruence.
    assert (nth_error args k <> None).
    eauto.
    congruence. }
  { intros.
    assert (nth_error preds k <> None) by congruence.
    assert (nth_error parcopies k <> None) by eauto.
    assert (nth_error args k <> None) by eauto.
    congruence. }
Qed.

Lemma equiv_phib_spec_plt_maxreg_phib'dst :
  forall maxreg k phib parcb phib' parcb',
  equiv_phib_spec maxreg k phib parcb phib' parcb' ->
  forall args' dst',
  In (Iphi args' dst') phib' ->
  Plt maxreg dst'.
Proof.
  intros until parcb'.
  intro H. induction H; intros args'' dst'' HIn.
  + inv HIn.
  + simpl in *.
    destruct HIn; try congruence; eauto.
Qed.

Lemma equiv_phib_spec_plt_maxreg_phib'arg :
  forall maxreg k phib parcb phib' parcb',
  equiv_phib_spec maxreg k phib parcb phib' parcb' ->
  forall arg' args' dst',
  In (Iphi args' dst') phib' ->
  nth_error args' k = Some arg' ->
  Plt maxreg arg'.
Proof.
  intros until parcb'.
  intro H. induction H;
    intros arg'' args'' dst'' HIn Hnth.
  + inv HIn.
  + simpl in *.
    destruct HIn; try congruence; eauto.
Qed.

Lemma equiv_phib_spec_parcbdst_inphib' :
  forall maxreg k phib parcb phib' parcb',
  equiv_phib_spec maxreg k phib parcb phib' parcb' ->
  forall arg arg',
  In (Iparcopy arg arg') parcb ->
  exists args' dst',
  nth_error args' k = Some arg' /\
  In (Iphi args' dst') phib'.
Proof.
  intros until parcb'.
  intro H. induction H; intros arg'' arg''' HIn.
  + inv HIn.
  + simpl in *.
    destruct HIn.
    - go.
    - assert (Hrec: exists args'0 dst'0,
        nth_error args'0 k = Some arg''' /\
          In (Iphi args'0 dst'0) phib').
      eauto.
      destruct Hrec as [args'0 [dst'0 [Hr1 Hr2]]].
      exists args'0. exists dst'0.
      split; auto.
Qed.

Lemma equiv_phib_spec_parcb'src_inphib' :
  forall maxreg k phib parcb phib' parcb',
  equiv_phib_spec maxreg k phib parcb phib' parcb' ->
  forall dst dst',
  In (Iparcopy dst' dst) parcb' ->
  exists args',
  In (Iphi args' dst') phib'.
Proof.
  intros until parcb'.
  intro H. induction H; intros dst''' dst'' HIn.
  + inv HIn.
  + simpl in *.
    destruct HIn.
    - go.
    - assert (Hrec: exists args'0,
        In (Iphi args'0 dst'') phib').
      eauto.
      destruct Hrec as [args'0 HInphidst].
      exists args'0.
      auto.
Qed.

Lemma equiv_phib_spec_parcb'dst_inphib :
  forall maxreg k phib parcb phib' parcb',
  equiv_phib_spec maxreg k phib parcb phib' parcb' ->
  forall dst dst',
  In (Iparcopy dst' dst) parcb' ->
  exists args,
  In (Iphi args dst) phib.
Proof.
  intros until parcb'.
  intro H. induction H; intros dst''' dst'' HIn.
  + inv HIn.
  + simpl in *.
    destruct HIn.
    - go.
    - assert (Hrec: exists args'0,
        In (Iphi args'0 dst''') phib).
      eauto.
      destruct Hrec as [args'0 HInphidst].
      exists args'0.
      auto.
Qed.

Lemma equiv_phib_spec_ple_phibdst_maxreg :
  forall maxreg k phib parcb phib' parcb',
  equiv_phib_spec maxreg k phib parcb phib' parcb' ->
  forall args dst,
  In (Iphi args dst) phib ->
  Ple dst maxreg.
Proof.
  intros until parcb'.
  intro H. induction H; intros args0 dst0 HIn.
  + inv HIn.
  + simpl in *.
    destruct HIn; go.
Qed.

Lemma equiv_phib_spec_correct :
  forall maxreg k phib parcb phib' parcb',
  unique_def_phib_spec phib ->
  equiv_phib_spec maxreg k phib parcb phib' parcb' ->
  equiv_phib maxreg k phib parcb phib' parcb'.
Proof.
  intros until parcb'.
  intros Hunique_def H.
  induction H.
  constructor.
  constructor 2; auto; intros.
  + assert (Plt maxreg  dst'').
    eapply equiv_phib_spec_plt_maxreg_phib'dst; eauto.
    assert (Plt arg  dst'').
    apply Ple_Plt_trans with maxreg; auto.
    auto.
  + assert (HIn:
      exists args' dst',
      nth_error args' k = Some dst'' /\
      In (Iphi args' dst') phib').
    eapply equiv_phib_spec_parcbdst_inphib'; eauto.
    destruct HIn as [args'0 [dst'0 HIn]].
    destruct HIn.
    assert (Plt maxreg dst'').
    eapply equiv_phib_spec_plt_maxreg_phib'arg; eauto.
    assert (Plt arg  dst'').
    apply Ple_Plt_trans with maxreg; auto.
    auto.
  + assert (HIn:
      exists args' dst',
      nth_error args' k = Some dst'' /\
      In (Iphi args' dst') phib').
    eapply equiv_phib_spec_parcbdst_inphib'; eauto.
    destruct HIn as [args'0 [dst'0 HIn]].
    destruct HIn.
    eauto.
  + assert (HIn: exists args'0,
      In (Iphi args'0 arg'') phib').
    eapply equiv_phib_spec_parcb'src_inphib'; eauto.
    destruct HIn as [args'0 HIn].
    assert (arg'' <> dst') by eauto.
    auto.
  + assert (HIn: exists args'0,
      In (Iphi args'0 dst'') phib).
    eapply equiv_phib_spec_parcb'dst_inphib; eauto.
    destruct HIn as [args'0 HIn].
    assert (Plt dst'' dst').
    apply Ple_Plt_trans with maxreg.
    eapply equiv_phib_spec_ple_phibdst_maxreg; eauto.
    auto.
    assert (dst'' <> dst') by eauto.
    auto.
  + assert (HIn: exists args0,
      In (Iphi args0 dst'') phib).
    eapply equiv_phib_spec_parcb'dst_inphib; eauto.
    destruct HIn as [args'0 HIn].
    inv Hunique_def.
    eauto.
  + inv Hunique_def.
    eauto.
Qed.


Lemma nodupnth_get_index :
  forall l pc k,
  NoDup l ->
  nth_error l k = Some pc ->
  get_index l pc = Some k.
Proof.
  induction l; intros.
  + destruct k; simpl in *.
    unfold Specif.error in *; congruence.
    unfold Specif.error in *; congruence.
  + destruct k; simpl in *; intros.
    - unfold value in *.
      assert (RW: a = pc) by congruence.
      rewrite RW in *.
      unfold get_index.
      simpl.
      flatten.
    - assert (get_index l pc = Some k).
      inv H. auto.
      assert (HIn: In pc l) by eauto.
      inv H.
      unfold get_index in *.
      simpl in *.
      flatten.
      assert (EQ1: 1 = 0 + 1) by auto.
      assert (EQ2: (S k) = k + 1) by lia.
      rewrite EQ1. rewrite EQ2.
      apply get_index_acc_inv. auto.
Qed.

Lemma index_pred_from_nth :
  forall l pc k pc' preds,
  NoDup (pc :: l) ->
  preds ! pc = Some l ->
  nth_error l k = Some pc' ->
  index_pred preds pc' pc = Some k.
Proof.
  intros.
  unfold index_pred.
  unfold successors_list.
  flatten.
  apply nodupnth_get_index; auto.
  inv H ; go.
Qed.

Lemma handle_phi_block_spec_from_handle_phi_block :
  forall f pc preds s1 s s0 s2 x x0 u
    INCR INCR1 INCR2 phib,
  (make_predecessors (fn_code f) successors_instr) ! pc = Some preds ->
  wf_ssa_function f ->
  Plt (get_maxreg f) (next_fresh_reg s1) ->
  initialize_phi_block pc s1 = OK x s INCR ->
  initialize_parcopy_blocks (pc :: preds) s = OK x0 s0 INCR1 ->
  normalized_jp f ->
  (fn_phicode f) ! pc = Some phib ->
  handle_phi_block preds phib pc s0 = OK u s2 INCR2 ->
  handle_phi_block_spec (get_maxreg f) preds pc
    phib
    (next_fresh_reg s0)
    (next_fresh_reg s2)
    (st_phicode s0) (st_phicode s2)
    (st_parcopycode s0) (st_parcopycode s2).
Proof.
    intros.
    eapply handle_phi_block_correct; eauto.
    + eapply nodups_in_preds; eauto; try congruence.
      eapply notinpredspc; eauto.
    + intros.
      apply Ple_trans with
        (get_max_reg_in_phiins (Iphi args dst)).
      apply max_reg_in_phi_dst.
      apply Ple_trans with
        (get_max_reg_in_phib phib).
      apply max_reg_in_phib_dst. auto.
      apply Ple_trans with
        (get_max_reg_in_phicode (fn_phicode f)).
      eapply max_reg_in_phicode; eauto.
      apply max_reg_correct_phicode.
    + intros.
      apply Ple_trans with
        (get_max_reg_in_phiins (Iphi args dst)).
      apply max_reg_in_phi_arg. auto.
      apply Ple_trans with
        (get_max_reg_in_phib phib).
      apply max_reg_in_phib_dst. auto.
      apply Ple_trans with
        (get_max_reg_in_phicode (fn_phicode f)).
      eapply max_reg_in_phicode; eauto.
      apply max_reg_correct_phicode.
    + apply Plt_Ple_trans with
        (next_fresh_reg s).
      apply Plt_Ple_trans with
        (next_fresh_reg s1).
      auto.
      inversion INCR; auto.
      inversion INCR1; auto.
Qed.

Lemma copy_node_cssagen_spec_parcode_other :
  forall f pc s1 s2 incr pc' phib preds,
  wf_ssa_function f ->
  normalized_jp f ->
  copy_node
    (make_predecessors (fn_code f) successors_instr)
    (fn_code f) (fn_phicode f) pc s1
    = OK tt s2 incr ->
  (fn_phicode f) ! pc = Some phib ->
  (make_predecessors (fn_code f) successors_instr)
    ! pc = Some preds ->
  pc' <> pc ->
  ~ In pc' preds ->
  Plt (get_maxreg f) (next_fresh_reg s1) ->
  (st_parcopycode s1) ! pc' = (st_parcopycode s2) ! pc'.
Proof.
  intros until preds.
  intros WF Norm_jp H Hphib Hpreds Hpcpc' HnotIn Hfresh.
  unfold copy_node in H.
  flatten H.
  + monadInv H.
    assert ((make_predecessors (fn_code f) successors_instr)
      ! pc = Some l) by auto. (* Coq needs help *)
    assert (RW: l = preds) by congruence.
    rewrite RW in *.
    simpl. unfold not; intros.
    replace ((st_parcopycode s2) ! pc')
      with ((st_parcopycode s0) ! pc').
    replace ((st_parcopycode s0) ! pc')
      with ((st_parcopycode s) ! pc').
    unfold initialize_phi_block in EQ; go.
    eapply initialize_parcopy_blocks_correct_parcother;
      eauto.
    unfold not; intros HInpc'.
    inv HInpc'; auto.
    assert(Hb:
      handle_phi_block_spec (get_maxreg f) preds pc
        phib
        (next_fresh_reg s0)
        (next_fresh_reg s2)
        (st_phicode s0) (st_phicode s2)
        (st_parcopycode s0) (st_parcopycode s2)).
    eapply handle_phi_block_spec_from_handle_phi_block;
      eauto.
    eapply handle_phi_block_spec_preserves_parcother; eauto.
    eapply nodups_in_preds; eauto; try congruence.
    eapply notinpredspc; eauto.
  + unfold error in H. go.
Qed.

Lemma copy_node_cssagen_spec_phicode_other :
  forall f pc s1 s2 u incr pc' phib preds,
  wf_ssa_function f ->
  normalized_jp f ->
  copy_node
    (make_predecessors (fn_code f) successors_instr)
    (fn_code f) (fn_phicode f) pc s1
    = OK u s2 incr ->
  (fn_phicode f) ! pc = Some phib ->
  (make_predecessors (fn_code f) successors_instr)
    ! pc = Some preds ->
  pc' <> pc ->
  Plt (get_maxreg f) (next_fresh_reg s1) ->
  (st_phicode s1) ! pc' = (st_phicode s2) ! pc'.
Proof.
  intros until preds.
  intros WF Norm_jp H Hphib Hpreds Hpcpc' Hfresh.
  unfold copy_node in H.
  flatten H.
  + monadInv H.
    assert ((make_predecessors (fn_code f) successors_instr)
      ! pc = Some l) by auto. (* Coq needs help *)
    assert (RW: l = preds) by congruence.
    rewrite RW in *.
    replace ((st_phicode s2) ! pc')
      with ((st_phicode s) ! pc').
    unfold initialize_phi_block in EQ.
    replace (st_phicode s) with
      (PTree.set pc nil (st_phicode s1)).
    rewrite PTree.gso; auto.
    go.
    replace ((st_phicode s2) ! pc')
      with ((st_phicode s0) ! pc').
    replace (st_phicode s0)
      with (st_phicode s).
    auto.
    eapply initialize_parcopy_blocks_correct_other; eauto.
    assert(Hb:
      handle_phi_block_spec (get_maxreg f) preds pc
        phib
        (next_fresh_reg s0)
        (next_fresh_reg s2)
        (st_phicode s0) (st_phicode s2)
        (st_parcopycode s0) (st_parcopycode s2)).
    eapply handle_phi_block_spec_from_handle_phi_block;
      eauto.
    eapply handle_phi_block_spec_preserves_phibother;
      eauto.
  + unfold error in H. go.
Qed.

Lemma copy_node_cssagenspec_other :
  forall f s1 pc k s2 pc' incr phib,
  cssa_spec
    (get_maxreg f)
    (make_predecessors (fn_code f) successors_instr)
    (fn_code f)
    (fn_phicode f) (st_phicode s1)
    (st_parcopycode s1)
    pc k ->
  wf_ssa_function f ->
  normalized_jp f ->
  Plt (get_maxreg f) (next_fresh_reg s1) ->
  copy_node
    (make_predecessors (fn_code f) successors_instr)
    (fn_code f) (fn_phicode f) pc' s1
    = OK tt s2 incr ->
  (fn_phicode f) ! pc = Some phib ->
  pc <> pc' ->
  cssa_spec
    (get_maxreg f)
    (make_predecessors (fn_code f) successors_instr)
    (fn_code f)
    (fn_phicode f) (st_phicode s2)
    (st_parcopycode s2)
    pc k.
Proof.
  intros until phib.
  intros H WF Norm_jp Hfresh Hcopy_node Hpcpc'.
  inv H; go.
  case_eq ((fn_phicode f) ! pc'); intros.
  case_eq (
    (make_predecessors (fn_code f) successors_instr) ! pc');
    intros.
  assert (~ In pc' l).
  { unfold not; intros.
    assert((fn_phicode f) ! pc' = None).
    unfold normalized_jp in Norm_jp.
    eapply Norm_jp; go.
    congruence. congruence. }
  assert (~ In pc l).
  { unfold not; intros.
    assert((fn_phicode f) ! pc = None).
    unfold normalized_jp in Norm_jp.
    eapply Norm_jp; go.
    congruence. congruence. }
  assert(EQ1: (st_parcopycode s1) ! pred =
    (st_parcopycode s2) ! pred).
  apply copy_node_cssagen_spec_parcode_other
    with (pc := pc') (f := f)
    (incr := incr) (phib := p) (preds := l); go.
  { unfold not; intros EQpredpc'.
    rewrite EQpredpc' in *.
    assert (Nthpc': nth_error (
      (make_predecessors (fn_code f)
        successors_instr) !!! pc : list positive) k =
      Some pc').
    eapply index_pred_some_nth; eauto.
    unfold successors_list in Nthpc'.
    flatten Nthpc'.
    assert(In pc' l0).
    eapply nth_In_node; eauto.
    assert ((fn_phicode f) ! pc' = None).
    unfold normalized_jp in Norm_jp.
    eapply Norm_jp; go.
    congruence. congruence.
    assert (nth_error (nil : list node) k = None).
    apply nth_error_nil_notSome_node.
    assert (nth_error (nil : list node) k = Some pc').
    auto. congruence. }
  eapply inop_is_not_in_two_preds; eauto.
  assert(EQ2: (st_parcopycode s1) ! pc =
    (st_parcopycode s2) ! pc).
  eapply copy_node_cssagen_spec_parcode_other; eauto.
  assert(EQ3: (st_phicode s1) ! pc =
    (st_phicode s2) ! pc).
  eapply copy_node_cssagen_spec_phicode_other; eauto.
  rewrite EQ1 in *.
  rewrite EQ2 in *.
  rewrite EQ3 in *.
  go.
  { induction WF.
    assert(JP: join_point pc' f).
    apply fn_phicode_inv.
    congruence.
    inv JP.
    congruence. }
  { unfold copy_node in Hcopy_node.
    flatten Hcopy_node. unfold ret in *.
    assert (RW: s1 = s2) by congruence.
    rewrite RW in *.
    go. }
Qed.

Lemma copy_node_cssagenspec_other_mfold :
  forall f,
  wf_ssa_function f ->
  normalized_jp f ->
  forall l s1 pc k s2 u incr,
  cssa_spec
    (get_maxreg f)
    (make_predecessors (fn_code f) successors_instr)
    (fn_code f)
    (fn_phicode f) (st_phicode s1)
    (st_parcopycode s1)
    pc k ->
  mfold_unit (copy_node
    (make_predecessors (fn_code f) successors_instr)
    (fn_code f) (fn_phicode f))
    l s1 = OK u s2 incr ->
  ~ In pc l ->
  Plt (get_maxreg f) (next_fresh_reg s1) ->
  cssa_spec
    (get_maxreg f)
    (make_predecessors (fn_code f) successors_instr)
    (fn_code f)
    (fn_phicode f) (st_phicode s2)
    (st_parcopycode s2)
    pc k.
Proof.
  intros f WF Norm_jp.
  induction l; intros until incr;
    intros Hspec H Hnotin Hplt.
  + simpl in *. unfold ret in *.
    assert (EQ: s1 = s2) by  congruence.
    rewrite EQ in *. auto.
  + case_eq ((fn_phicode f) ! pc); intros.
    simpl in *.
    monadInv H.
    assert(Hstep:
      cssa_spec
        (get_maxreg f)
        (make_predecessors (fn_code f) successors_instr)
        (fn_code f)
        (fn_phicode f) (st_phicode s)
        (st_parcopycode s)
        pc k).
    destruct x.
    eapply copy_node_cssagenspec_other; eauto.
    eapply IHl; eauto.
    apply Plt_Ple_trans with (next_fresh_reg s1).
    auto. inversion INCR; auto.
    go.
Qed.

Lemma copy_node_cssagenspec :
  forall f pc s1 s2 incr k,
    wf_ssa_function f ->
    normalized_jp f ->
    Plt (get_maxreg f) (next_fresh_reg s1) ->
    copy_node
      (make_predecessors (fn_code f) successors_instr)
      (fn_code f) (fn_phicode f) pc s1
      = OK tt s2 incr ->
    cssa_spec
      (get_maxreg f)
      (make_predecessors (fn_code f) successors_instr)
      (fn_code f)
      (fn_phicode f) (st_phicode s2)
      (st_parcopycode s2)
      pc k.
Proof.
  intros until k. intros WF Norm_jp Pltmaxregfresh H.
  case_eq ((fn_phicode f) ! pc); go; intro phib; intros.
  unfold copy_node in H.
  flatten H.
  + assert (~ In pc l).
    eapply notinpredspc; eauto.
    monadInv H.
    set (preds :=
      make_predecessors (fn_code f) successors_instr)
      in *.
    case_eq (nth_error l k); intros.
    {
      assert(Hb:
        handle_phi_block_spec (get_maxreg f) l pc
          phib
          (next_fresh_reg s0)
          (next_fresh_reg s2)
          (st_phicode s0) (st_phicode s2)
          (st_parcopycode s0) (st_parcopycode s2)).
      eapply handle_phi_block_spec_from_handle_phi_block;
        eauto.

      assert (phib_init: (st_phicode s0) ! pc = Some nil).
      replace (st_phicode s0) with (st_phicode s).
      eapply initialize_phi_block_correct; eauto.
      eapply initialize_parcopy_blocks_correct_other; eauto.

      assert (parcb'_init:
        (st_parcopycode s0) ! pc = Some nil)
        by eauto.

      assert (parcb_init:
        (st_parcopycode s0) ! n = Some nil)
        by eauto.

      assert (HEphib': exists phib',
        (st_phicode s2) ! pc = Some phib').
      eapply handle_phi_block_spec_exists_phib'; eauto.
      assert (HEparcb': exists parcb',
        (st_parcopycode s2) ! pc = Some parcb').
      eapply handle_phi_block_spec_exists_parcb'; eauto.
      eapply nodups_in_preds; eauto. congruence.
      assert (HEparcb: exists parcb,
        (st_parcopycode s2) ! n = Some parcb).
      eapply handle_phi_block_spec_exists_parcb; eauto.
      eapply nodups_in_preds; eauto. congruence.
      destruct HEphib' as [phib' Hphib'].
      destruct HEparcb' as [parcb' Hparcb'].
      destruct HEparcb as [parcb Hparcb].
      apply cssa_spec_jp_pred_k
        with (pred := n) (phib := phib) (phib' := phib')
             (parcb := parcb) (parcb' := parcb'); auto.

      induction WF.
      apply fn_normalized. apply fn_phicode_inv. go.
      assert (codepred: exists i, (fn_code f) ! n = Some i).
      eapply make_predecessors_some; go.
      destruct codepred as [i codepred].
      eapply in_successors_if_succofpred; eauto.

      eapply index_pred_from_nth; eauto.
      eapply nodups_in_preds; eauto. congruence.

      apply handle_phi_block_spec_equiv_phib
        with (preds := l) (pc := pc)
        (fs_init :=  (next_fresh_reg s0))
        (fs_last :=  (next_fresh_reg s2))
        (phicode1 := st_phicode s0)
        (phicode2 := st_phicode s2)
        (parcode1 := st_parcopycode s0)
        (parcode2 := st_parcopycode s2)
        (pred := n); auto.
      eapply nodups_in_preds; eauto.
      congruence.
    }
    eapply cssa_spec_jp_invalid_k; eauto.
  + unfold error in H. go.
Qed.

Lemma mfold_copy_node_correct :
  forall f,
  wf_ssa_function f ->
  normalized_jp f ->
  forall l pc
    u s s' incr k,
  mfold_unit (copy_node
    (make_predecessors (fn_code f) successors_instr)
    (fn_code f) (fn_phicode f))
    l s = OK u s' incr ->
  Plt (get_maxreg f) (next_fresh_reg s) ->
  NoDup l ->
  In pc l ->
  cssa_spec (get_maxreg f)
    (make_predecessors (fn_code f) successors_instr)
    (fn_code f) (fn_phicode f)
    (st_phicode s') (st_parcopycode s') pc k.
Proof.
  intros f WF Norm_jp.
  induction l; intros.
  + inv H2.
  + simpl in *.
    monadInv H.
    destruct H2.
    - rewrite H in *.
      assert (Hstep:
        cssa_spec (get_maxreg f)
          (make_predecessors (fn_code f) successors_instr)
          (fn_code f) (fn_phicode f)
          (st_phicode s0) (st_parcopycode s0) pc k).
      destruct x.
      apply copy_node_cssagenspec with
        (s1 := s) (incr := INCR); go.
      inv H1.
      eapply copy_node_cssagenspec_other_mfold; eauto.
      apply Plt_Ple_trans with (next_fresh_reg s).
      auto. inversion INCR; auto.
    - apply IHl with
        (u := u) (s := s0) (incr := INCR0); auto.
      apply Plt_Ple_trans with (next_fresh_reg s).
      auto. inversion INCR; auto.
      inv H1; auto.
Qed.

(** ** Normalisations validators proofs *)
Lemma inops_checker_correct :
  forall f,
  wf_ssa_function f ->
  check_jp_inops f = true ->
  inop_in_jp f.
Proof.
  intros f WF CHECK.
  unfold inop_in_jp.
  intros.
  unfold check_jp_inops in CHECK.
  rewrite forallb_forall in CHECK.
  exploit (CHECK pc).
  case_eq ((fn_phicode f) ! pc); try congruence; intros.
  assert (In (pc, p) (PTree.elements (fn_phicode f))).
  apply PTree.elements_correct; auto.
  eapply In_Infst_phib; eauto.
  intros.
  unfold check_inop_jp in H0.
  flatten H0; auto.
  exists n; auto.
Qed.

Lemma normalisation_checker_correct_aux :
  forall f,
  check_joinpoints f = true ->
  forall pc succ,
  (fn_code f) ! pc = Some (Inop succ) ->
  (fn_phicode f) ! succ <> None ->
  (fn_phicode f) ! pc = None.
Proof.
  intros f CHECK pc succ codepc phisucc.
  unfold check_joinpoints in CHECK.
  rewrite forallb_forall in CHECK.
  exploit (CHECK pc).
  assert (In (pc, Inop succ) (PTree.elements (fn_code f))).
  apply PTree.elements_correct; auto.
  eapply In_Infst; eauto.
  intros.
  unfold check_node in H.
  flatten H; auto.
Qed.

Lemma In_nth_error : forall l (pc : node),
  In pc l ->
  exists k, nth_error l k = Some pc.
Proof.
  induction l; intros.
  inv H.
  simpl in *.
  destruct H.
  + exists 0. simpl. unfold value. congruence.
  + cut (exists k : nat, nth_error l k = Some pc); auto.
    intros HE. destruct HE as [k nthk].
    exists (S k). simpl. auto.
Qed.

Lemma normalisation_checker_correct :
  forall f,
  wf_ssa_function f ->
  check_joinpoints f = true ->
  normalized_jp f.
Proof.
  intros f WF CHECK.
  unfold normalized_jp.
  intros pc preds phipc mkpreds pred Inpred.
  eapply normalisation_checker_correct_aux; eauto.
  induction WF.
  apply fn_normalized.
  apply fn_phicode_inv. auto.
  assert (H: exists i, (fn_code f) ! pred = Some i).
  eapply make_predecessors_some; eauto.
  destruct H.
  assert (nthk: exists k, nth_error preds k = Some pred).
  apply In_nth_error; auto.
  destruct nthk.
  eapply in_successors_if_succofpred; eauto.
Qed.

(** ** Proof of the transformation specification *)
Lemma transl_function_charact:
  forall f tf,
  wf_ssa_function f ->
  transl_function f = Errors.OK tf ->
  tr_function f tf.
Proof.
  intros f tf WF H.
  unfold transl_function in H.
  case_eq (init_state f) ; intros.
  rewrite H0 in *.
  case_eq (mfold_unit
    (copy_node
      (make_predecessors (fn_code f) successors_instr)
      (fn_code f) (fn_phicode f))
    l s); intros.
  { rewrite H1 in H.  congruence. }
  { rewrite H1 in H. flatten H.
    repeat rewrite andb_true_iff in Eq.
    destruct Eq as [[Hcheckjps Hcheckinops] Hcheckentry].
    eapply tr_function_intro ; eauto.
    apply normalisation_checker_correct; auto.
    destruct u. eauto.
    unfold entry_point_not_jp_pred in *; flatten Hcheckentry.
    apply inops_checker_correct; auto.
  }
Qed.

Lemma transl_function_spec_ok : forall f tf,
  normalized_jp f ->
  tr_function f tf ->
  transl_function_spec f tf.
Proof.
  intros f tf Norm_jp H.
  inv H.
  econstructor; go; intros; simpl.
  + unfold init_state in H0.
    assert (RW: lp = map fst (PTree.elements (fn_code f)))
      by congruence.
    assert (HNoDups: NoDup lp).
    assert (list_norepet lp).
    rewrite RW in *.
    apply PTree.elements_keys_norepet.
    apply list_norepet_NoDup; auto.

    eapply mfold_copy_node_correct; eauto.
    unfold init_state in *.
    assert (RWinitreg: next_fresh_reg init =
      Pos.succ (get_maxreg f))
      by go.
    rewrite RWinitreg. simpl.
    apply Plt_succ.
    rewrite RW in *.
    assert (In (pc, ins) (PTree.elements (fn_code f))).
    apply PTree.elements_correct. auto.
    eapply In_Infst; eauto.
  + eapply wf_unique_def_phib; eauto.
Qed.

Require Import Linking.

Section PRESERVATION.

  Definition match_prog (p: SSA.program) (tp: CSSA.program) :=
    match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq p tp.

  
  Lemma transf_program_match:
    forall p tp, transl_program p = Errors.OK tp -> match_prog p tp.
  Proof.
    intros. apply match_transform_partial_program; auto.
  Qed.

  Section CORRECTNESS.

    Variable prog: SSA.program.
    Variable tprog: CSSA.program.
    Hypothesis TRANSF_PROG: match_prog prog tprog.
    Hypothesis WF_PROG : wf_ssa_program prog.
    
    Let ge := Genv.globalenv prog.
    Let tge := Genv.globalenv tprog.

    Let sem := SSA.semantics prog.
    Let tsem := CSSA.semantics tprog.
    
    Lemma symbols_preserved:
      forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
    Proof.
      apply (Genv.find_symbol_transf_partial TRANSF_PROG). 
    Qed.

    Variant match_regset (max_reg: positive) : SSA.regset -> SSA.regset -> Prop :=
    | mrg_intro : forall rs rs',
        (forall r, (Ple r max_reg) -> rs# r = rs'# r) ->
        match_regset max_reg rs rs'.

    Inductive match_stackframes :
      list stackframe -> list CSSA.stackframe -> Prop :=
    | match_stackframes_nil: match_stackframes nil nil
    | match_stackframes_cons:
        forall res f sp pc rs rs' s tf ts
               (STACK : (match_stackframes s ts ))
               (SPEC: (transl_function f = Errors.OK tf))
               (WFF: wf_ssa_function f)
               (MREG: match_regset (get_maxreg f) rs rs'),
          match_stackframes
            ((Stackframe res f sp pc rs) :: s)
            ((CSSA.Stackframe res tf sp pc rs') :: ts).

    Hint Constructors match_stackframes: core.

    Set Implicit Arguments.
    
    Variant match_states: SSA.state -> CSSA.state -> Prop :=
    | match_states_intro:
        forall s ts sp pc rs rs' m f tf
               (SPEC: transl_function f = Errors.OK tf)
               (STACK: match_stackframes s ts)
               (WFF: wf_ssa_function f)
               (MREG: match_regset (get_maxreg f) rs rs'),
          match_states (State s f sp pc rs m)
                       (CSSA.State ts tf sp pc rs' m)
    | match_states_call:
        forall s ts f tf args m
               (SPEC: transl_fundef f = Errors.OK tf)
               (STACK: match_stackframes s ts)
               (WFF: wf_ssa_fundef f),
          match_states (Callstate s f args m)
                       (CSSA.Callstate ts tf args m)
    | match_states_return:
        forall s ts v m
               (STACK: match_stackframes s ts ),
          match_states (Returnstate s v m)
                       (CSSA.Returnstate ts v m).
    Hint Constructors match_states: core.

Lemma function_ptr_translated: forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf
    /\ transl_fundef f = Errors.OK tf.
Proof.
  apply (Genv.find_funct_ptr_transf_partial); eauto.
Qed.

Lemma sig_fundef_translated: forall f tf,
    wf_ssa_fundef f ->
    transl_fundef f = Errors.OK tf ->
    CSSA.funsig tf = SSA.funsig f.
Proof.
  intros f tf. intros.
  case_eq f; intros.
  - rewrite H1 in H0.
    simpl in *. Errors.monadInv H0.
    eapply transl_function_charact in EQ ; eauto.
    inv EQ.
    simpl; auto.
    inv H. auto.
  - rewrite H1 in H0. go.
Qed.

Lemma transf_initial_states:  forall st1,
    initial_state prog st1 ->
    exists st2, CSSA.initial_state tprog st2
                /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated ; eauto. intros [tf [Hfind Htrans]].
  econstructor; split.
  - econstructor.
    assert (MEM: (Genv.init_mem tprog) = Some m0) by (eapply (Genv.init_mem_transf_partial TRANSF_PROG); eauto).
    + apply MEM ; auto.
    + replace (prog_main tprog) with (prog_main prog). rewrite symbols_preserved; eauto.
      symmetry; eapply match_program_main; eauto.
    + eauto.
    + rewrite <- H3. apply sig_fundef_translated; auto.
      unfold wf_ssa_program in WF_PROG.
      eapply Genv.find_funct_ptr_prop ; eauto.  
  - eapply match_states_call  ; eauto.
    eapply Genv.find_funct_ptr_prop ; eauto.  
Qed.

Lemma transf_final_states: forall st1 st2 r,
    match_states st1 st2 ->
    final_state st1 r  ->
    CSSA.final_state st2 r.
Proof.
  intros. inv H0. inv H.
  inv STACK.
  constructor.
Qed.

Lemma instructions_preserved:  forall f tf,
  transl_function f = Errors.OK tf ->
  CSSA.fn_code tf = fn_code f.
Proof.
  intros.
  unfold transl_function in H.
  flatten H; go.
Qed.

Lemma no_new_joinpoints: forall f tf,
  transl_function f = Errors.OK tf ->
  forall pc,
    CSSA.join_point pc tf ->
    join_point pc f.
Proof.
  intros.
  inv H0.
  apply jp_cons with l; auto.
  rewrite same_successors_same_predecessors
    with (f2 := successors_instr)
         (m2 := CSSA.fn_code tf).
  rewrite Hpreds; auto.
  intros.
  erewrite PTree.gmap1.
  erewrite PTree.gmap1.
  unfold option_map.
  case_eq ((fn_code f) ! i); intros.
  + rewrite instructions_preserved with f tf.
    rewrite H0; eauto.
    congruence.
  + case_eq ((CSSA.fn_code tf) ! i); intros; auto.
    rewrite instructions_preserved with f tf in H1.
    congruence. auto.
Qed.

Lemma join_points_preserved: forall f tf,
  transl_function f = Errors.OK tf ->
  forall pc,
    join_point pc f ->
    CSSA.join_point pc tf.
Proof.
  intros.
  inv H0.
  econstructor; go.
  assert (CSSA.fn_code tf = fn_code f).
  apply instructions_preserved; auto.
  go.
Qed.

Lemma registers_equal: forall rs rs' args max_reg,
    (forall r, In r args -> Ple r max_reg) ->
    match_regset max_reg rs rs' ->
    rs' ## args = rs ## args.
Proof.
  intros.
  inv H0.
  induction args; eauto.
  simpl.
  erewrite IHargs; go.
  erewrite H1; go.
Qed.

Lemma functions_translated: forall (v: val) (f: SSA.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf
    /\ transl_fundef f = Errors.OK tf.
Proof.
  apply (Genv.find_funct_transf_partial); eauto.
Qed.

Lemma spec_ros_r_find_function: forall rs rs' f r m,
  rs # r = rs' # r ->
  SSA.find_function ge (SSA.ros_to_vos m (inl _ r) rs) rs = Some f ->
  exists tf,
     CSSA.find_function tge (CSSA.ros_to_vos m (inl _ r) rs') rs' = Some tf
  /\ transl_fundef f = Errors.OK tf.
Proof.
  intros. simpl in H0. des_ifs.
- ss. rewrite <- H. des_ifs.
  exploit (functions_translated (Vptr b (Ptrofs.repr z))); eauto. ss. des_ifs.
- ss. rewrite <- H. des_ifs.
  exploit (functions_translated (Vptr b (Ptrofs.zero))); eauto.
Qed.

Lemma spec_ros_id_find_function: forall rs rs' f id m,
  SSA.find_function ge (SSA.ros_to_vos m (inr _ id) rs) rs = Some f ->
  exists tf,
     CSSA.find_function tge (SSA.ros_to_vos m (inr _ id) rs') rs' = Some tf
  /\ transl_fundef f = Errors.OK tf.
Proof.
  intros.
  simpl in *.
  case_eq (Genv.find_symbol ge id) ; intros.
  rewrite H0 in H.
  rewrite symbols_preserved in * ; eauto ; rewrite H0 in *.
  exploit function_ptr_translated; eauto.
  rewrite H0 in H ; inv H.
Qed.

Lemma stacksize_preserved: forall f tf,
  transl_function f = Errors.OK tf ->
  fn_stacksize f = CSSA.fn_stacksize tf.
Proof.
  intros.
  unfold transl_function in H.
  flatten H; go.
Qed.

(** ** parallel block evaluation simplification lemmas *)
Lemma parcopy_store_other : forall rs r parcb,
  (forall src dst, In (Iparcopy src dst) parcb -> r <> dst) ->
  rs !! r = (parcopy_store parcb rs) !! r.
Proof.
  intros rs r parcb.
  induction parcb; go.
  intros.
  simpl. destruct a.
  rewrite PMap.gso; go.
Qed.

Lemma copy_out_of_parcb :
  forall (rs : SSA.regset) (parcb : parcopyblock) (src dst : reg),
  (forall src' dst', In (CSSA.Iparcopy src' dst') parcb -> src <> dst') ->
  parcopy_store (CSSA.Iparcopy src dst :: parcb) rs =
    (parcopy_store parcb rs)# dst <- ((parcopy_store parcb rs) # src).
Proof.
  intros.
  simpl.
  assert (rs !! src =
    (parcopy_store parcb rs) !! src).
  eapply parcopy_store_other; go.
  go.
Qed.

Lemma copy_out_of_phib : forall (rs : SSA.regset) (phib : phiblock)
    (src dst : reg) (args : list reg) (k : nat),
    (forall args' dst', In (Iphi args' dst') phib -> src <> dst') ->
    nth_error args k = Some src ->
    phi_store k (Iphi args dst :: phib) rs =
    (phi_store k phib rs)# dst <- ((phi_store k phib rs) # src).
Proof.
  intros. simpl.
  case_eq (nth_error args k); intros; go.
  assert (EQ: r = src) by congruence.
  rewrite EQ in *.
  assert (rs !! src = (phi_store k phib rs) !! src).
  eapply phi_store_other; go.
  go.
Qed.

(** ** equiv_phib inductive predicate consequences *)
Lemma equiv_phib_fresh_parcb :  forall maxreg k phib parcb phib' parcb' src dst
  (EQ_PHIB: equiv_phib maxreg k phib parcb phib' parcb')
  (IN_parcb: In (Iparcopy src dst) parcb),
  Plt maxreg dst.
Proof.
  intros.
  induction EQ_PHIB; go.
  simpl in IN_parcb.
  destruct IN_parcb; go.
Qed.

Lemma equiv_phib_fresh_phib'2 : forall maxreg k phib parcb phib' parcb' args dst
  (EQ_PHIB: equiv_phib maxreg k phib parcb phib' parcb')
  (IN_parcb: In (Iphi args dst) phib'),
  Plt maxreg dst.
Proof.
  intros.
  induction EQ_PHIB; go.
  simpl in IN_parcb.
  destruct IN_parcb; go.
Qed.

Lemma equiv_phib_nth : forall maxreg k phib phib' parcb parcb',
  equiv_phib maxreg k phib parcb phib' parcb' ->
  forall args dst, In (Iphi args dst) phib'
    -> exists arg, nth_error args k = Some arg.
Proof.
  intros maxreg k phib phib' parcb parcb' H.
  induction H.
  { intros. contradiction. }
  intros args0 dst0 IH_IN.
  simpl in *.
  destruct IH_IN.
  exists arg'. congruence.
  apply IHequiv_phib with (dst := dst0).
  auto.
Qed.

Lemma equiv_phib_parcsrc_phib'dst :
  forall maxreg k phib phib' parcb parcb',
  equiv_phib maxreg k phib parcb phib' parcb' ->
  forall src dst,
  In (Iparcopy src dst) parcb' ->
  exists args, In (Iphi args src) phib'.
Proof.
  intros maxreg k phib phib' parcb parcb' EQ_PHIB.
  induction EQ_PHIB; intros src dst0 In_src; go.
  simpl in *.
  destruct In_src.
  - go.
  - assert (Exists_args:
      exists args0, In (Iphi args0 src) phib') by eauto.
    destruct Exists_args as [args0 In_args_phib'].
    exists args0. auto.
Qed.

Lemma equiv_phib_args_k_notnone : forall maxreg k phib parcb phib' parcb' args dst,
  equiv_phib maxreg k phib parcb phib' parcb' ->
  In (Iphi args dst) phib'
  -> nth_error args k <> None.
Proof.
  intros maxreg k phib parcb phib' parcb' args dst H.
  induction H. auto.
  intro HIn.
  inv HIn; go.
Qed.

Lemma reg_Ple_Plt_not_eq : forall maxreg (r1 r2 : reg),
  Ple r1 maxreg ->
  Plt maxreg r2 ->
  r1 <> r2.
Proof.
  intros.
  simpl in *.
  assert (Plt r1 r2); auto with coqlib.
  apply Ple_Plt_trans with maxreg; auto with coqlib.
Qed.

Hint Resolve equiv_phib_fresh_parcb equiv_phib_fresh_phib'2
  equiv_phib_nth equiv_phib_args_k_notnone
  reg_Ple_Plt_not_eq: core.

Hint Resolve parc_dst_in: core.

Definition phib_dst (phiins : phiinstruction) :=
  match phiins with
  | Iphi args dst => dst
  end.

Lemma in_phib_dst_exists_args : forall dst phib,
  In dst (map phib_dst phib) ->
  exists args, In (Iphi args dst) phib.
Proof.
  induction phib; intros.
  { simpl in H. contradiction. }
  simpl in *.
  destruct a.
  case_eq (peq r dst); intros.
  + rewrite e in *. go.
  + simpl in H.
    destruct H. congruence.
    assert (IN_phib: exists args, In (Iphi args dst) phib).
    auto. destruct IN_phib as [src IN_parcb].
    eauto.
Qed.

Lemma in_phib_dst_in : forall args dst phib,
  In (Iphi args dst) phib ->
  In dst (map phib_dst phib).
Proof.
  induction phib; auto; intros.
  simpl in *.
  destruct H; [left | right]; go.
Qed.

Lemma in_phib_dst_simul :
  forall rs (phib : phiblock) (r : reg) (k : nat) args arg,
  NoDup (map phib_dst phib) ->
  In (Iphi args r) phib ->
  (forall args' dst', In (Iphi args' dst') phib
    -> nth_error args' k <> None) ->
  nth_error args k = Some arg ->
  (phi_store k phib rs) !! r = rs !! arg.
Proof.
  induction phib; intros r k args arg HNoDup H.
  { simpl in H. contradiction. }
  simpl in *.
  destruct a.
  case_eq (nth_error l k); intros.
  + simpl in *.
    case_eq (peq r r0); intros.
    - rewrite e in *.
      rewrite PMap.gss.
      destruct H; go.
      inv HNoDup.
      assert (In r0 (map phib_dst phib)).
      eapply in_phib_dst_in; eauto.
      contradiction.
    - rewrite PMap.gso; auto.
      destruct H; go.
      inv HNoDup.
      eapply IHphib; eauto.
  + simpl in *. inv HNoDup.
    destruct H. congruence. eauto.
Qed.

Lemma in_parcb_dst_simul : forall rs (r : reg) (parcb : parcopyblock) src,
  NoDup (map parc_dst parcb) ->
  In (Iparcopy src r) parcb ->
  (parcopy_store parcb rs) !! r = rs !! src.
Proof.
  induction parcb; intros.
  { simpl in H. contradiction. }
  simpl in *.
  destruct a.
  destruct H0.
  + assert (EQ1: r0 = src) by congruence.
    assert (EQ2: r1 = r) by congruence.
    rewrite EQ1 in *. rewrite EQ2 in *.
    inv H.
    apply PMap.gss.
  + inv H.
    rewrite PMap.gso; auto.
    unfold not in *; intros. go.
Qed.

Lemma equiv_phib_nodups_parcb_dst :
  forall maxreg k phib parcb phib' parcb',
  equiv_phib maxreg k phib parcb phib' parcb' ->
  NoDup (map parc_dst parcb).
Proof.
  intros.
  induction H; go.
  simpl.
  constructor; go.
  unfold not; intros.
  assert(Exists_src: exists src,
    In (Iparcopy src arg') parcb).
  apply in_parcb_dst_exists_src; auto.
  destruct Exists_src as [src in_src_parcb'].
  assert (arg' <> arg'); go.
Qed.

Hint Resolve equiv_phib_nodups_parcb_dst: core.

Lemma equiv_phib_nodups_phib'_dst : forall maxreg k phib parcb phib' parcb',
  equiv_phib maxreg k phib parcb phib' parcb' ->
  NoDup (map phib_dst phib').
Proof.
  intros.
  induction H; go.
  simpl.
  constructor; go.
  unfold not; intros.
  assert(Exists_args': exists args',
    In (Iphi args' dst') phib').
  apply in_phib_dst_exists_args; auto.
  destruct Exists_args' as [src in_src_parcb'].
  assert (dst' <> dst'); go.
Qed.

Hint Resolve equiv_phib_nodups_phib'_dst: core.

Lemma equiv_phib_spec_rev: forall maxreg k phib parcb phib' parcb',
  equiv_phib maxreg k phib parcb phib' parcb' ->
  equiv_phib_spec maxreg k phib parcb phib' parcb'.
Proof.
  intros; induction H; go.
Qed.

Lemma equiv_phib_nodups_parcb'_dst : forall maxreg k phib parcb phib' parcb',
  unique_def_phib_spec phib ->
  equiv_phib maxreg k phib parcb phib' parcb' ->
  NoDup (map parc_dst parcb').
Proof.
  intros until parcb'. intros Hwf H.
  induction H; go.
  simpl.
  constructor; go.
  unfold not; intros.
  assert(Exists_src: exists src,
    In (Iparcopy src dst) parcb').
  apply in_parcb_dst_exists_src; auto.
  destruct Exists_src as [src in_src_parcb'].
  assert (equiv_phib_spec maxreg k phib parcb phib' parcb').
  apply equiv_phib_spec_rev; auto.
  assert (dst <> dst); auto.
  assert (exists args0,
    In (Iphi args0 dst) phib).
  eapply equiv_phib_spec_parcb'dst_inphib; eauto.
  eauto.
  inv Hwf. auto.
Qed.

Hint Resolve equiv_phib_nodups_parcb'_dst: core.

Lemma parcb_not_in : forall r parcb,
  ~ In r (map parc_dst parcb) ->
  forall src dst,
  In (Iparcopy src dst) parcb ->
  r <> dst.
Proof.
  induction parcb; go; intros.
  simpl in *.
  destruct H0.
  - rewrite H0 in *. go.
  - intuition. go.
Qed.

Hint Resolve parcb_not_in: core.

Lemma phi_store_emulation : forall rs rs' k phib parcb phib' parcb' maxreg,
  match_regset maxreg rs rs' ->
  unique_def_phib_spec phib ->
  equiv_phib maxreg k phib parcb phib' parcb' ->
  forall r,
  Ple r maxreg ->
  (phi_store k phib rs) !! r =
  (parcopy_store parcb'
    (phi_store k phib'
      (parcopy_store parcb rs'))) !! r.
Proof.
  intros rs rs' k phib parcb phib' parcb' maxreg MREG
    WFphib EQ_PHIB.
  induction EQ_PHIB.
  - simpl. inv MREG. eapply H; go.
  - intros. symmetry.
    inv WFphib.
    assert (r <> dst'). eauto.
    assert (r <> arg'). eauto.
    set (rec_simuled_store :=
      (parcopy_store parcb'
        (phi_store k phib'
          (parcopy_store parcb rs')))) in *.
    rewrite copy_out_of_parcb; go.
    rewrite copy_out_of_phib with
      (parcopy_store (Iparcopy arg arg' :: parcb) rs')
      phib' arg' dst' args' k; go.
    rewrite copy_out_of_parcb; go.
    case_eq (peq r dst); intros; go.
    + rewrite e in *.
      symmetry. simpl.
      case_eq (nth_error args k); go; intros.
      rewrite PMap.gss.
      assert (R_EQ: r0 = arg) by go.
      rewrite R_EQ in *.
      repeat rewrite PMap.gss.
      rewrite <- parcopy_store_other; go.
      rewrite PMap.gss.
      rewrite <- phi_store_other; go.
      rewrite PMap.gss.
      rewrite <- parcopy_store_other; go.
      inv MREG. auto.
    + symmetry. simpl.
      case_eq (nth_error args k); go; intros.
      rewrite PMap.gso; auto.
      rewrite IHEQ_PHIB; auto.
      unfold rec_simuled_store.
      case_eq (in_dec peq r (map parc_dst parcb')); intros.
      {
        assert (Exists_src: exists src,
          In (Iparcopy src r) parcb').
        apply in_parcb_dst_exists_src; auto.
        destruct Exists_src as [src In_src_r_parcb'].
        rewrite in_parcb_dst_simul with (src := src); go.
        symmetry.
        rewrite PMap.gso; go.
        rewrite in_parcb_dst_simul with (src := src); go.
        rewrite PMap.gso.

        assert (Exists_args'': exists args'',
          In (Iphi args'' src) phib').
        eapply equiv_phib_parcsrc_phib'dst; eauto.
        destruct Exists_args'' as [args'' In_args''src].
        assert (Exists_arg'': exists arg'',
          nth_error args'' k = Some arg'').
        eapply equiv_phib_nth; go.
        destruct Exists_arg'' as [arg'' arg''kargs''].
        rewrite in_phib_dst_simul
          with (arg := arg'') (args := args''); go.
        rewrite <- parcopy_store_other; go.
        rewrite PMap.gso.
        symmetry.
        rewrite in_phib_dst_simul
          with (arg := arg'') (args := args''); go.
        assert (arg' <> arg'') by go. go.
        assert (dst' <> src) by go. go.
      }
      {
        rewrite <- parcopy_store_other.
        rewrite <- phi_store_other; go.
        rewrite <- parcopy_store_other; go.
        symmetry.
        repeat rewrite PMap.gso; auto.
        rewrite <- parcopy_store_other.
        rewrite PMap.gso; auto.
        rewrite <- phi_store_other; go.
        rewrite PMap.gso; auto.
        rewrite <- parcopy_store_other; go.
        apply parcb_not_in; auto.
        apply parcb_not_in; auto.
      }
Qed.

(** ** (index_preds preds pc) injectivity *)
Lemma get_index_acc_le_k : forall l pc acc k,
  get_index_acc l pc acc = Some k ->
  acc <= k.
Proof.
  induction l; go.
  intros. simpl in *. flatten H; go.
  assert (acc + 1 <= k).
  eauto. lia.
Qed.

Lemma index_acc_inj : forall l pc1 pc2 k p,
  get_index_acc l pc1 p = Some k ->
  get_index_acc l pc2 p = Some k ->
  pc1 = pc2.
Proof.
  induction l; intros pc1 pc2 k p H H0.
  go.
  simpl in H. simpl in H0.
  flatten H; flatten H0; go.
  + assert (k + 1 <= k).
    eapply get_index_acc_le_k; eauto.
    lia.
  + assert (k + 1 <= k).
    eapply get_index_acc_le_k; eauto.
    lia.
Qed.

Lemma index_preds_pc_inj : forall f pc1 pc2 succ k preds,
  preds = make_predecessors (fn_code f) successors_instr ->
  index_pred preds pc1 succ = Some k ->
  index_pred preds pc2 succ = Some k ->
  pc1 = pc2.
Proof.
  intros.
  unfold index_pred in *.
  case_eq (preds !!! succ); intros.
  + unfold get_index in *.
    rewrite H2 in *. inv H0. 
  + rewrite H2 in *.
    eapply index_acc_inj; eauto.
Qed.

Lemma get_preds_some : forall preds (pc : node) lpreds,
  preds ! pc = Some lpreds ->
  preds !!! pc = lpreds.
Proof.
  induction lpreds; intros;
  unfold successors_list;
  rewrite H; auto.
Qed.

Lemma match_regset_args : forall args maxreg rs rs',
  match_regset maxreg rs rs' ->
  (forall arg, In arg args -> Ple arg maxreg) ->
  rs' ## args = rs ## args.
Proof.
  induction args; go.
  intros.
  simpl.
  erewrite IHargs; eauto.
  inv H.
  rewrite H1; auto.
Qed.

Lemma senv_preserved:
  Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
Proof.
  apply (Genv.senv_transf_partial TRANSF_PROG).
Qed.

Lemma same_public:
  prog_public prog = prog_public tprog.
Proof. inv TRANSF_PROG. des; eauto. Qed.

(** ** Proving the transformation *)
Lemma transl_step_correct:
  forall s1 t s2,
  IStep sem s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2',
  DStep tsem s1' t s2' /\ match_states s2 s2'.
Proof.
  destruct 1. generalize dependent s2. rename H into INT.
  induction 1; intros; inv MS; auto;
  match goal with
  | [H : transl_fundef (Internal ?f) = _ |- _ ] => idtac
  | [H : transl_fundef (External ?f) = _ |- _ ] => idtac
  | [  |- context [CSSA.Returnstate ?ts ?vres ?m]] =>
      idtac
  | _ =>
      (exploit transl_function_charact ; eauto; intros);
      (exploit transl_function_spec_ok ; eauto; intros)
  end;
  match goal with
  | [SPEC: transl_function_spec ?f ?tf |- _ ] =>
    inv SPEC
  | _ => try (generalize (wf_ssa f) ; intros HWF)
  end;
  match goal with
  | [Htr : tr_function ?f ?tf |- normalized_jp ?f ]
      => inv Htr; auto
  | _ => idtac
  end.
  (* inop without block *)
  { exists (CSSA.State ts tf sp pc' rs' m). split; auto.
    DStep_tac.
    { exploit instructions_preserved; eauto. i. rewrite H2 in Heq. clarify. }
    econstructor 1 ; eauto.
    - erewrite instructions_preserved; eauto.
    - intuition.
      apply H0.
      eapply no_new_joinpoints; eauto. }
  (* inop with phi-block *)
  {
    set (preds := make_predecessors
      (fn_code f) successors_instr) in *.
    assert (CSSA_SPEC: cssa_spec
      (get_maxreg f)
      preds
      (fn_code f) (fn_phicode f)
      (CSSA.fn_phicode tf) (fn_parcopycode tf) pc' k).
    assert(codepc': exists i, (fn_code f) ! pc' = Some i).
    { induction WFF.
      eapply fn_code_closed; go. }
    destruct codepc' as [i codepc']. eauto.

    inv CSSA_SPEC; try congruence.
    {
      assert (nth_error (preds !!! pc' : list positive) k =
        Some pc).
      eapply index_pred_some_nth; eauto.
      assert (preds !!! pc' = (lpreds : list positive)).
      apply get_preds_some. auto.
      assert (nth_error (lpreds : list positive) k = None)
        by auto. (* some magic for Coq *)
      congruence.
    }

    exists (CSSA.State ts tf sp pc'
      (parcopy_store parcb'
        (phi_store k phib'
          (parcopy_store parcb rs')))
      m).
    split.
    + assert (EQ_PC_PRED: pc = pred).
      eapply index_preds_pc_inj; eauto.
      rewrite EQ_PC_PRED in *.
      DStep_tac.
      { exploit instructions_preserved; eauto. i. rewrite H1 in Heq. clarify. }
      eapply CSSA.exec_Inop_jp; eauto.
      - erewrite instructions_preserved; eauto.
      - eapply join_points_preserved; eauto.
      - unfold get_preds.
        unfold CSSA.get_preds.
        erewrite instructions_preserved; eauto.
    + apply match_states_intro; go.
      constructor; intros.
      assert (PHIBS_EQ: phib0 = phib) by congruence.
      rewrite PHIBS_EQ in *.
      eapply phi_store_emulation; eauto.
      eapply equiv_phib_spec_correct; eauto.
  }
  (* iop *)
  { exists (CSSA.State ts tf sp pc' (rs' # res <- v) m).
    split.
    + DStep_tac.
      { exploit instructions_preserved; eauto. i. rewrite H2 in Heq. clarify. }
      econstructor; eauto.
      assert ((CSSA.fn_code tf) ! pc =
        Some (Iop op args res pc')).
      erewrite instructions_preserved; eauto; simpl; eauto.
      eauto.
      assert (REGS_EQ: rs' ## args = rs ## args).
      { eapply registers_equal; intros; eauto.
        apply Ple_trans with
          (get_max_reg_in_ins
            (Iop op args res pc')).
        apply max_reg_in_Iop_args; auto.
        apply Ple_trans with
          (get_max_reg_in_code (fn_code f)).
        eapply max_reg_in_code; eauto.
        apply max_reg_correct_code.
      }
      rewrite REGS_EQ.
      erewrite eval_operation_wrapper_preserved; eauto.
      eapply symbols_preserved.
    + constructor; eauto.  constructor.
      inv MREG.  intros.
      rewrite PMap.gsspec.  rewrite PMap.gsspec.
      destruct peq; eauto.  }
  (* iload *)
  { exists (CSSA.State ts tf sp pc' (rs' # dst <- v) m).
    split.
    + DStep_tac.
      { exploit instructions_preserved; eauto. i. rewrite H3 in Heq. clarify. }
      eapply CSSA.exec_Iload; eauto.
      assert ((CSSA.fn_code tf) ! pc =
        Some (Iload chunk addr args dst pc')).
      erewrite instructions_preserved; eauto; simpl; eauto.
      eauto.
      assert (REGS_EQ: rs' ## args = rs ## args).
      { eapply registers_equal; eauto; intros.
        apply Ple_trans with
          (get_max_reg_in_ins
            (Iload chunk addr args dst pc')).
        apply max_reg_in_Iload_args; auto.
        apply Ple_trans with
          (get_max_reg_in_code (fn_code f)).
        eapply max_reg_in_code; eauto.
        apply max_reg_correct_code.
      }
      rewrite REGS_EQ.
      erewrite eval_addressing_preserved; eauto.
      eapply symbols_preserved.
    + constructor; eauto. constructor.
      inv MREG. intros.
      rewrite PMap.gsspec. rewrite PMap.gsspec.
      destruct peq; eauto.  }
  (* istore *)
  { exists (CSSA.State ts tf sp pc' rs' m').
    split.
    + DStep_tac.
      { exploit instructions_preserved; eauto. i. rewrite H3 in Heq. clarify. }
      eapply CSSA.exec_Istore; eauto.
      assert ((CSSA.fn_code tf) ! pc =
        Some (Istore chunk addr args src pc')).
      { erewrite instructions_preserved; eauto; simpl; eauto. }
      eauto.
      assert (REGS_EQ: rs' ## args = rs ## args).
      { eapply registers_equal; eauto; intros.
        apply Ple_trans with
          (get_max_reg_in_ins
            (Istore chunk addr args src pc')).
        apply max_reg_in_Istore_args; auto.
        apply Ple_trans with
          (get_max_reg_in_code (fn_code f)).
        eapply max_reg_in_code; eauto.
        apply max_reg_correct_code.
      }
      rewrite REGS_EQ.
      erewrite eval_addressing_preserved; eauto.
      eapply symbols_preserved.
      inv MREG. rewrite <- H3. auto.
      apply Ple_trans with
        (get_max_reg_in_ins
          (Istore chunk addr args src pc')).
      apply max_reg_in_Istore_src; auto.
      apply Ple_trans with
        (get_max_reg_in_code (fn_code f)).
      eapply max_reg_in_code; eauto.
      apply max_reg_correct_code.
    + constructor; eauto. }
  (* icall *)
  {
    assert (WFfd: wf_ssa_fundef fd).
    {
      unfold wf_ssa_program in WF_PROG.
      assert (ID: exists id,
        In (id, Gfun fd) (prog_defs prog)).
      unfold find_function in H0.
      unfold Genv.find_funct in H0.
      flatten H0;
        apply Genv.find_funct_ptr_inversion
          with (b := b); auto.
      destruct ID as [id Infd].
      apply WF_PROG with id.
      auto.
    }
    assert (RW: rs' ## args = rs ## args).
    { assert(Pleargs: forall arg, In arg args ->
        Ple arg (get_maxreg f)); intros.
      apply Ple_trans with
        (get_max_reg_in_ins (Icall (funsig fd)
          ros args res pc')).
      apply max_reg_in_Icall_args; auto.
      apply Ple_trans with
        (get_max_reg_in_code (fn_code f)).
      eapply max_reg_in_code; eauto.
      apply max_reg_correct_code.
      eapply match_regset_args; eauto.
    }

    destruct ros.
    - assert(Htfd: exists tfd,
        CSSA.find_function tge (CSSA.ros_to_vos m (inl _ r) rs') rs' = Some tfd
        /\ transl_fundef fd = Errors.OK tfd).
      apply spec_ros_r_find_function
        with (rs := rs); auto.
      assert (Ple  r (get_maxreg f)).
      {
        apply Ple_trans with
          (get_max_reg_in_ins (Icall (funsig fd)
            (inl r) args res pc')).
        apply max_reg_in_Icall_inl.
        repeat constructor; auto. (* Coq… *)
        apply Ple_trans with
          (get_max_reg_in_code (fn_code f)).
        eapply max_reg_in_code; eauto.
        apply max_reg_correct_code.
      }
      inv MREG; auto.

      destruct Htfd as [tfd Hfindtfd].
      exists (CSSA.Callstate
        (CSSA.Stackframe res tf sp pc' rs' :: ts)
        tfd (rs'## args) m).
      split.
      + DStep_tac;
        try by (exploit instructions_preserved; eauto; i; rewrite H2 in Heq; clarify).      apply CSSA.exec_Icall
          with (sig := CSSA.funsig tfd)
            (ros := inl r); eauto.
        { erewrite instructions_preserved; eauto; simpl;
            eauto.
          assert (CSSA.funsig tfd = funsig fd).
          apply sig_fundef_translated.
          auto.
          destruct Hfindtfd. auto.
          go. }
        destruct Hfindtfd. auto.
      + rewrite RW in *.
        apply match_states_call.
        destruct Hfindtfd. auto.
        go.
        auto.
    - assert(Htfd: exists tfd,
        CSSA.find_function tge (CSSA.ros_to_vos m (inr i) rs') rs' = Some tfd
        /\ transl_fundef fd = Errors.OK tfd).
      apply spec_ros_id_find_function
        with (rs := rs); auto.
      destruct Htfd as [tfd Htfd].
      exists (CSSA.Callstate
        (CSSA.Stackframe res tf sp pc' rs' :: ts)
        tfd (rs'## args) m).
      split.
      + DStep_tac.
        { exploit instructions_preserved; eauto. i. rewrite H2 in Heq. clarify. }
        { exploit instructions_preserved; eauto. i. rewrite H2 in Heq. clarify. }
        apply CSSA.exec_Icall
          with (sig := CSSA.funsig tfd)
            (ros := inr i); eauto.
        erewrite instructions_preserved; eauto.
        assert (EQfdtfd: CSSA.funsig tfd = funsig fd).
        apply sig_fundef_translated.
        auto.
        destruct Htfd. auto.
        rewrite EQfdtfd. auto.
        destruct Htfd. auto.
      + rewrite RW in *.
        apply match_states_call.
        destruct Htfd. auto.
        go.
        auto.
  }
  (* itailcall *)
  { 
    assert (WFfd: wf_ssa_fundef fd).
    {
      unfold wf_ssa_program in WF_PROG.
      assert (ID: exists id,
        In (id, Gfun fd) (prog_defs prog)).
      unfold find_function in H0.
      unfold Genv.find_funct in H0.
      flatten H0;
        apply Genv.find_funct_ptr_inversion
          with (b := b); auto.
      destruct ID as [id Infd].
      apply WF_PROG with id.
      auto.
    }
    assert (RW: rs' ## args = rs ## args).
    { assert(Pleargs: forall arg, In arg args ->
        Ple arg (get_maxreg f)); intros.
      apply Ple_trans with
        (get_max_reg_in_ins (Itailcall (funsig fd)
          ros args)).
      apply max_reg_in_Itailcall_args; auto.
      apply Ple_trans with
        (get_max_reg_in_code (fn_code f)).
      eapply max_reg_in_code; eauto.
      apply max_reg_correct_code.
      eapply match_regset_args; eauto.
    }

    destruct ros.
    - assert(Htfd: exists tfd,
        CSSA.find_function tge (CSSA.ros_to_vos m (inl _ r) rs') rs' = Some tfd
        /\ transl_fundef fd = Errors.OK tfd).
      apply spec_ros_r_find_function
        with (rs := rs); auto.
      assert (Ple r (get_maxreg f)).
      {
        apply Ple_trans with
          (get_max_reg_in_ins (Itailcall (funsig fd)
            (inl r) args)).
        apply max_reg_in_Itailcall_inl.
        repeat constructor; auto. (* Coq… *)
        apply Ple_trans with
          (get_max_reg_in_code (fn_code f)).
        eapply max_reg_in_code; eauto.
        apply max_reg_correct_code.
      }
      inv MREG; auto.

      destruct Htfd as [tfd Hfindtfd].
      exists (CSSA.Callstate
        ts tfd rs'## args m').
      split.
      + DStep_tac; try by (exploit instructions_preserved; eauto; i; rewrite H3 in Heq; clarify).
        apply CSSA.exec_Itailcall
          with (sig := CSSA.funsig tfd)
            (ros := inl r); eauto.
        { erewrite instructions_preserved; eauto; simpl;
            eauto.
          assert (CSSA.funsig tfd = funsig fd).
          apply sig_fundef_translated.
          auto.
          destruct Hfindtfd. auto.
          go. }
        destruct Hfindtfd. auto.
        rewrite <- stacksize_preserved with (f := f);
          auto.
      + rewrite RW in *.
        apply match_states_call.
        destruct Hfindtfd. auto.
        go.
        auto.
    - assert(Htfd: exists tfd,
        CSSA.find_function tge (CSSA.ros_to_vos m (inr i) rs') rs' = Some tfd
        /\ transl_fundef fd = Errors.OK tfd).
      apply spec_ros_id_find_function
        with (rs := rs); auto.
      destruct Htfd as [tfd Htfd].
      exists (CSSA.Callstate
        ts tfd (rs'## args) m').
      split.
      + DStep_tac.
        { exploit instructions_preserved; eauto. i. rewrite H3 in Heq. clarify. }
        { exploit instructions_preserved; eauto. i. rewrite H3 in Heq. clarify. }
        apply CSSA.exec_Itailcall
          with (sig := CSSA.funsig tfd)
            (ros := inr i); eauto.
        erewrite instructions_preserved; eauto.
        assert (EQfdtfd: CSSA.funsig tfd = funsig fd).
        apply sig_fundef_translated.
        auto.
        destruct Htfd. auto.
        rewrite EQfdtfd. auto.
        destruct Htfd. auto.
        rewrite <- stacksize_preserved with (f := f);
          auto.
      + rewrite RW in *.
        apply match_states_call.
        destruct Htfd. auto.
        go.
        auto.
  }
  (* ibuiltin *)
  { exists (CSSA.State ts tf sp pc' (regmap_setres res vres rs') m').
    split.
    + DStep_tac.
      { unfold is_internal in INT. ss. des_ifs.
        exploit instructions_preserved; eauto. i. rewrite H in Heq. clarify. }
      eapply CSSA.exec_Ibuiltin with (vargs:= vargs); eauto.
      * assert ((CSSA.fn_code tf) ! pc =  Some (Ibuiltin ef args res pc')).
        { erewrite instructions_preserved; eauto; simpl; eauto. }
        eauto.
      * eapply eval_builtin_args_preserved with (ge1:= ge); eauto.
        eapply symbols_preserved.
        assert (forall r, In r (params_of_builtin_args args) -> rs !! r = rs' !! r).
        { inv MREG.
          intros.
          eapply max_reg_in_code in H; eauto.
          apply H3.
          apply Ple_trans with
              (get_max_reg_in_ins
                 (Ibuiltin ef args res pc')).
          apply max_reg_in_Ibuiltin_args; auto.
          apply Ple_trans with
              (get_max_reg_in_code (fn_code f)); auto.
          apply max_reg_correct_code.
        }
        revert H0 H3. clear.
        { induction 1 ; intros; go.
          constructor.
          - revert H H3. clear.
            induction 1 ; intros ; go.
            + rewrite H3; go.
            + constructor.
              * eapply IHeval_builtin_arg1; eauto.
                intros. eapply H3; eauto. simpl in *.
                rewrite app_ass.
                eapply in_app_or in H1.
                eapply in_or_app. intuition.
              * eapply IHeval_builtin_arg2; eauto.
                intros. eapply H3; eauto. simpl in *.
                rewrite app_ass.
                eapply in_app_or in H1.
                eapply in_or_app. intuition.
            + constructor.
              * eapply IHeval_builtin_arg1; eauto.
                intros. eapply H3; eauto. simpl in *.
                rewrite app_ass.
                eapply in_app_or in H1.
                eapply in_or_app. intuition.
              * eapply IHeval_builtin_arg2; eauto.
                intros. eapply H3; eauto. simpl in *.
                rewrite app_ass.
                eapply in_app_or in H1.
                eapply in_or_app. intuition.
          - eapply IHlist_forall2; eauto.
            intros. eapply H3; eauto.
            simpl. eapply in_or_app. intuition.
        }        
      * eapply external_call_symbols_preserved; eauto.
        apply senv_preserved.                
    + constructor; eauto.
      constructor. inv MREG. intros.
      destruct res ; auto.
      simpl.
      rewrite PMap.gsspec. rewrite PMap.gsspec.
      destruct peq; eauto.
  }

  (* ifso *)
  { exists (CSSA.State ts tf sp ifso rs' m).
    split.
    + DStep_tac.
      { exploit instructions_preserved; eauto. i. rewrite H2 in Heq. clarify. }
      eapply CSSA.exec_Icond_true; eauto.
      assert ((CSSA.fn_code tf) ! pc =
        Some (Icond cond args ifso ifnot)).
      { erewrite instructions_preserved; eauto; simpl;
        eauto. }
      eauto.
      assert (REGS_EQ: rs' ## args = rs ## args).
      { eapply registers_equal; eauto; intros.
        apply Ple_trans with
          (get_max_reg_in_ins
            (Icond cond args ifso ifnot)).
        apply max_reg_in_Icond_args; auto.
        apply Ple_trans with
          (get_max_reg_in_code (fn_code f)).
        eapply max_reg_in_code; eauto.
        apply max_reg_correct_code.
      }
      rewrite REGS_EQ.
      auto.
    + constructor; eauto. }
  (* ifnot *)
  { exists (CSSA.State ts tf sp ifnot rs' m).
    split.
    + DStep_tac.
      { exploit instructions_preserved; eauto. i. rewrite H2 in Heq. clarify. }
      eapply CSSA.exec_Icond_false; eauto.
      assert ((CSSA.fn_code tf) ! pc =
        Some (Icond cond args ifso ifnot)).
      { erewrite instructions_preserved; eauto; simpl;
        eauto. }
      eauto.
      assert (REGS_EQ: rs' ## args = rs ## args).
      { eapply registers_equal; eauto; intros.
        apply Ple_trans with
          (get_max_reg_in_ins
            (Icond cond args ifso ifnot)).
        apply max_reg_in_Icond_args; auto.
        apply Ple_trans with
          (get_max_reg_in_code (fn_code f)).
        eapply max_reg_in_code; eauto.
        apply max_reg_correct_code.
      }
      rewrite REGS_EQ.
      auto.
    + constructor; eauto.
  }
  (* ijumptable *)
  { exists (CSSA.State ts tf sp pc' rs' m).
    split.
    + DStep_tac.
      { exploit instructions_preserved; eauto. i. rewrite H3 in Heq. clarify. }
      eapply CSSA.exec_Ijumptable; eauto.
      assert ((CSSA.fn_code tf) ! pc =
        Some (Ijumptable arg tbl)).
      { erewrite instructions_preserved; eauto; simpl;
        eauto. }
      eauto.
      inv MREG. rewrite <- H3. congruence.
      apply Ple_trans with
        (get_max_reg_in_ins
          (Ijumptable arg tbl)).
      apply max_reg_in_Ijumptable_arg; auto.
      apply Ple_trans with
        (get_max_reg_in_code (fn_code f)).
      eapply max_reg_in_code; eauto.
      apply max_reg_correct_code.
    + constructor; eauto. }
  (* ireturn *)
  { exists (CSSA.Returnstate ts
      (regmap_optget or Vundef rs') m').
    split.
    + DStep_tac.
      { exploit instructions_preserved; eauto. i. rewrite H2 in Heq. clarify. }
      eapply CSSA.exec_Ireturn; eauto.
      assert ((CSSA.fn_code tf) ! pc =
        Some (Ireturn or)).
      { erewrite instructions_preserved; eauto; simpl; eauto. }
      eauto.
      erewrite <- stacksize_preserved; eauto.
    + destruct or; simpl; eauto.
      inv MREG. rewrite H2. auto.
      apply Ple_trans with
        (get_max_reg_in_ins
          (Ireturn (Some r))).
      apply max_reg_in_Ireturn_r; auto.
      apply Ple_trans with
        (get_max_reg_in_code (fn_code f)).
      eapply max_reg_in_code; eauto.
      apply max_reg_correct_code.
  }
  (* internal *)
  { 
    destruct tf as [tf | tf].
    exists (CSSA.State ts tf (Vptr stk Ptrofs.zero)
      tf.(CSSA.fn_entrypoint)
      (init_regs args (CSSA.fn_params tf))
      m').
    split.
    + DStep_tac.
      eapply CSSA.exec_function_internal.
      erewrite <- stacksize_preserved; eauto.
      simpl in SPEC.
      unfold Errors.bind in SPEC.
      flatten SPEC.
    + simpl in *. 
      unfold Errors.bind in SPEC.
      flatten SPEC.
      replace (CSSA.fn_entrypoint tf)
        with (fn_entrypoint f).
      apply match_states_intro; eauto.
      induction WFF. auto.
      econstructor; eauto; intros.
      replace (CSSA.fn_params tf)
        with (fn_params f); auto.
      unfold transl_function in Eq.
      flatten Eq. simpl. auto.
      unfold transl_function in Eq.
      flatten Eq. simpl. auto.
    + simpl in SPEC.
      unfold Errors.bind in SPEC.
      flatten SPEC.
  }
  (* external *)
  { inv SPEC.
    exists (CSSA.Returnstate ts res m').
    split.
    + DStep_tac.
      eapply CSSA.exec_function_external.
      eapply external_call_symbols_preserved; eauto.
      apply senv_preserved. 
    + econstructor; eauto.
  }
  (* return state *)
  {
    inv STACK.
    exists (CSSA.State ts0 tf sp pc
      (rs' # res <- vres) m).
    split.
    + DStep_tac.
      eapply CSSA.exec_return.
    + econstructor; eauto.
      econstructor; intros.
      inv MREG.
      case_eq (peq res r); intros.
      - rewrite e in *.
        rewrite PMap.gss; auto.
        rewrite PMap.gss; auto.
      - rewrite PMap.gso; auto.
        rewrite PMap.gso; auto.
  }
Qed.

Lemma match_states_bsim
      s1
      (EXT: is_external ge s1)
      s2 t s2'
      (STEPTGT: Step tsem s2 t s2')
      (MATCH: match_states s1 s2)
      (SAFESRC: safe sem s1)
  :
    (exists s1', Step sem s1 t s1' /\ match_states s1' s2').
Proof.
  assert (SEQUIV: Senv.equiv tge ge) by (symmetry; apply senv_preserved).
  unfold safe in SAFESRC. specialize (SAFESRC _ (star_refl _ _ _)). des; cycle 2; clarify.
  { inv SAFESRC. inv MATCH. ss. }
  unfold is_external in *. des_ifs.
  (* builtin *)
  - i. inv MATCH; clarify.
    exploit instructions_preserved; eauto. i.
    inv STEPTGT; rewrite H in *; clarify. inv SAFESRC; clarify.
    esplits; eauto.
    + eapply SSA.exec_Ibuiltin.
      { eauto. }
      2:{ eapply external_call_symbols_preserved; eauto. }
      assert (forall r, In r (params_of_builtin_args l) -> rs' !! r = rs !! r).
      { symmetry.
        inv MREG.
        intros.
        eapply max_reg_in_code in H11; eauto.
        apply H1.
        apply Ple_trans with
          (get_max_reg_in_ins
             (Ibuiltin e l b n)).
        apply max_reg_in_Ibuiltin_args; auto.
        apply Ple_trans with
          (get_max_reg_in_code (fn_code f)); auto.
        apply max_reg_correct_code. }
      eapply eval_builtin_args_preserved with (ge1:=tge).
      { i. symmetry. eapply senv_preserved. }
      revert H9 H0. clear.
      { induction 1; i; go.
        constructor.
        - revert H H0. clear.
          induction 1; i; go.
          + rewrite H0; go.
          + constructor.
            * eapply IHeval_builtin_arg1; eauto.
              intros. eapply H1; eauto. simpl in *.
              rewrite app_ass.
              eapply in_app_or in H2.
              eapply in_or_app. intuition.
            * eapply IHeval_builtin_arg2; eauto.
              intros. eapply H1; eauto. simpl in *.
              rewrite app_ass.
              eapply in_app_or in H2.
              eapply in_or_app. intuition.
          + constructor.
            * eapply IHeval_builtin_arg1; eauto.
              intros. eapply H1; eauto. simpl in *.
              rewrite app_ass.
              eapply in_app_or in H2.
              eapply in_or_app. intuition.
            * eapply IHeval_builtin_arg2; eauto.
              intros. eapply H1; eauto. simpl in *.
              rewrite app_ass.
              eapply in_app_or in H2.
              eapply in_or_app. intuition.
        - eapply IHlist_forall2; eauto.
          intros. eapply H0; eauto.
          simpl. eapply in_or_app. intuition. }
    + constructor; eauto.
      constructor. inv MREG. intros.
      destruct b; auto.
      simpl.
      rewrite PMap.gsspec. rewrite PMap.gsspec.
      destruct peq; eauto.
  (* external call *)
  - i. inv MATCH; clarify. inv SPEC.
    inv STEPTGT; clarify. inv SAFESRC; clarify.
    ss. exists (SSA.Returnstate stack res m').
    split.
    + eapply SSA.exec_function_external.
      eapply external_call_symbols_preserved; eauto.
    + econstructor; eauto.
Qed.

Lemma match_states_xsim
    st_src0 st_tgt0 gmtgt
    (MATCH: match_states st_src0 st_tgt0) :
  xsim (SSA.semantics prog) (CSSA.semantics tprog) gmtgt lt 0%nat st_src0 st_tgt0.
Proof.
  generalize dependent st_src0. generalize dependent st_tgt0.
  pcofix CIH. i. pfold.
  destruct (classic (is_external ge st_src0)); cycle 1.
  (* not external *)
  - left. econs. econs.
    + i. exploit transl_step_correct; eauto. i. des.
      * esplits; eauto.
        { eapply tr_rel_refl. eapply ev_rel_refl. }
        left. split.
        { eapply plus_one; eauto. }
        { eapply SSAD.semantics_receptive_at; auto. }
    + ii. eapply final_state_determ; eauto.
      inv FINALSRC. inv MATCH. ss. inv STACK. econs.
  (* external *)
  - right. econs. i. econs.
    + i. exploit match_states_bsim; eauto. i. des.
      left. esplits; eauto.
      { eapply tr_rel_refl. eapply ev_rel_refl. }
      left. eapply plus_one. eauto.
    + i. unfold is_external in *.
      des_ifs; inv FINALTGT; inv MATCH; ss.
    (* progress *)
    + i.
      specialize (SAFESRC _ (star_refl _ _ _)). des; cycle 2; clarify.
      { inv SAFESRC; ss. }
      right. inv MATCH; ss; des_ifs; inv SAFESRC; unfold ge in *; clarify.
      * exploit instructions_preserved; eauto. i.
        esplits. eapply CSSA.exec_Ibuiltin; eauto.
        { rewrite H0; eauto. }
        2:{ eapply external_call_symbols_preserved. apply senv_preserved. eauto. }
        eapply eval_builtin_args_preserved with (ge1:= ge); eauto.
        eapply symbols_preserved.
        assert (forall r, In r (params_of_builtin_args l) -> rs !! r = rs' !! r).
        { inv MREG.
          intros.
          eapply max_reg_in_code in H8; eauto.
          apply H1.
          apply Ple_trans with
              (get_max_reg_in_ins
                 (Ibuiltin e l b n)).
          apply max_reg_in_Ibuiltin_args; auto.
          apply Ple_trans with
              (get_max_reg_in_code (fn_code f)); auto.
          apply max_reg_correct_code.
        }
        revert H9 H1. clear.
        { induction 1 ; intros; go.
          constructor.
          - revert H H1. clear.
            induction 1 ; intros ; go.
            + rewrite H1; go.
            + constructor.
              * eapply IHeval_builtin_arg1; eauto.
                intros. eapply H1; eauto. simpl in *.
                rewrite app_ass.
                eapply in_app_or in H2.
                eapply in_or_app. intuition.
              * eapply IHeval_builtin_arg2; eauto.
                intros. eapply H1; eauto. simpl in *.
                rewrite app_ass.
                eapply in_app_or in H2.
                eapply in_or_app. intuition.
            + constructor.
              * eapply IHeval_builtin_arg1; eauto.
                intros. eapply H1; eauto. simpl in *.
                rewrite app_ass.
                eapply in_app_or in H2.
                eapply in_or_app. intuition.
              * eapply IHeval_builtin_arg2; eauto.
                intros. eapply H1; eauto. simpl in *.
                rewrite app_ass.
                eapply in_app_or in H2.
                eapply in_or_app. intuition.
          - eapply IHlist_forall2; eauto.
            intros. eapply H1; eauto.
            simpl. eapply in_or_app. intuition. }
      * i. inv SPEC.
        esplits. eapply CSSA.exec_function_external.
        eapply external_call_symbols_preserved with (ge1:=ge); eauto.
        unfold ge. eapply senv_preserved.
Qed.

Lemma non_static_equiv l:
  Genv.non_static_glob (Genv.globalenv prog) l = Genv.non_static_glob (Genv.globalenv tprog) l.
Proof.
  induction l; ss.
  specialize senv_preserved. i. unfold ge, tge in H. r in H. des.
  specialize (H0 a).
  unfold Senv.public_symbol in H0. ss. rewrite <- H0.
  specialize (H a). rewrite <- H. erewrite IHl; eauto.
Qed.

Lemma transf_initial_capture
    S1 S2 S2'
    (INITSRC: SSA.initial_state prog S1)
    (INITTGT: CSSA.initial_state tprog S2)
    (MATCH: match_states S1 S2)
    (CAPTGT: CSSA.glob_capture tprog S2 S2'):
  exists S1',
    SSA.glob_capture prog S1 S1'
  /\ match_states S1' S2'
  /\ gm_improves (SSA.concrete_snapshot ge S1') (CSSA.concrete_snapshot tge S2').
Proof.
  specialize senv_preserved. intros SENVEQ. inv CAPTGT. ss.
  rewrite Genv.globalenv_public in CAPTURE.
  rewrite <- same_public in CAPTURE. erewrite <- non_static_equiv in CAPTURE.
  inv MATCH. inv STACK.
  esplits.
  - econs; eauto. rewrite Genv.globalenv_public. eauto.
  - econs; eauto.
  - ii. unfold CSSA.concrete_snapshot, SSA.concrete_snapshot in *.
    inv SENVEQ. des. erewrite H1, H0. des_ifs; ss.
Qed.

Theorem transf_program_correct:
  mixed_simulation (SSA.semantics prog) (CSSA.semantics tprog).
Proof.
  econs. econs.
  - apply lt_wf.
  - rr. i. exists (S a). lia.
  - econs. i. exploit transf_initial_states; eauto. i. des.
    exists st2. split.
    (* initial state *)
    + econs; eauto. eapply initial_state_determ.
    (* mixed sim *) 
    + r. ii. inversion INITSRC; subst. inversion H0; subst.
      inv STACK.
      exploit transf_initial_capture; eauto.
      i. des.
      exists 0%nat. exists S1'. esplits; eauto.
      apply match_states_xsim; auto.
  - i. apply senv_preserved.
Qed.

End CORRECTNESS.
  
End PRESERVATION.
