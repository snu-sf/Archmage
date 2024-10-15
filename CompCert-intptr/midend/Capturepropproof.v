Require Import Classical.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
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
Require Import Captureprop.
Require Import Copypropproof.
Require Import IntPtrRel.
(* Require Import GVNoptProp. *)
Require Import DLib.

Require Import Linking.

(* Require Opt. *)
(* Require OptInv. *)
Require Import Errors.
From Paco Require Import paco.
Require Import sflib.
Require Import SSAD.
Require Import IntPtrRef.

Unset Allow StrictProp.

Definition match_prog (p: SSA.program) (tp: SSA.program) :=
  match_program (fun cu f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. eapply match_transform_partial_program_contextual; eauto.
Qed.

(* Step optimization definitions which correspond to one substitution *)
Definition propagate_capture_step domtree (cl : code * list node) :=
  let (c, il) := cl in
  match il with
    | nil => (c, nil)
    | cpt :: tl =>
      let root := (find_capture_root domtree cpt tl) in
      match c ! root with
      | Some i => match (is_capture i) with
                  | Some (d, s) => (subst_capture_code domtree d s root c,
                    filter (fun x => negb (Pos.eqb root x)) il)
                  | None => (c, nil)
                  end
      | None => (c, nil)
      end
    end.

Definition transf_function_step (fl : function * list node) :=
  let (f, il) := fl in
    match compute_dom f with
    | Some domtree =>
        let (c', il') := propagate_capture_step domtree (f.(fn_code), il) in
        OK ((mkfunction (fn_sig f) (fn_params f) (fn_stacksize f) c' (fn_phicode f)
        (fn_entrypoint f) (fn_ext_params f) (fn_dom_test f)), il')
    | None => Error (msg "Captureprop failure: domtree gen fail")
    end.

Local Open Scope error_monad_scope.

Definition transf_fundef_step (fdl : fundef * list node) :
  res (fundef * list node) :=
  let (fd, il) := fdl in
    match fd with
    | Internal f =>
      do (tf, il') <- transf_function_step (f, il); OK ((Internal tf), il')
    | External f =>
      OK ((External f), il)
    end.

Definition transf_globdef_step (idgil: (ident * globdef fundef unit) * list node) :=
  match idgil with
  | (id, Gfun f, il) =>
    do (tf, il') <- transf_fundef_step (f, il); OK ((id, Gfun tf), il')
  | (id, Gvar v, il) => OK ((id, Gvar v), il)
  end.

Fixpoint transf_globdefs_step (l: list (ident * globdef fundef unit)) (ll: list (list node)) :=
  match l, ll with
  | idg :: l', il :: ll' =>
      do (idg', il') <- transf_globdef_step (idg, il);
      do (l'', ll'') <- transf_globdefs_step l' ll';
      OK (idg' :: l'', il' :: ll'')
  | _, _ => OK (l, ll)
  end.

Definition transf_program_step (pill : SSA.program * (list (list node))) :
  res (SSA.program * list (list node)) :=
  let (p, ill) := pill in
  do (gl', ill') <- transf_globdefs_step p.(prog_defs) ill;
  OK (mkprogram gl' p.(prog_public) p.(prog_main), ill').

Fixpoint repeatn_monad {A} (f : A -> res A) (n : nat) a :=
  match n with
  | O => OK a
  | S n' => do fa <- f a; repeatn_monad f n' fa
  end.

Definition root_capture (root : node) (l : list node) domtree :=
  match l with
  | nil => False
  | hd :: tl => root = find_capture_root domtree hd tl
  end.

Definition change_code (f : function) (c : code) :=
  mkfunction (fn_sig f) (fn_params f) (fn_stacksize f) c
    (fn_phicode f) (fn_entrypoint f) (fn_ext_params f) (fn_dom_test f).

Lemma subst_capture_code_spec : forall c pc i t d s hd tl,
  c ! pc = Some i ->
  (subst_capture_code t d s (find_capture_root t hd tl) c) ! pc =
  match (in_set (find_capture_root t hd tl) t # pc) with
  | true => if Pos.eqb pc (find_capture_root t hd tl) then Some i else Some (subst_instr d s i)
  | false => Some i
  end.
Proof.
  ii. unfold subst_capture_code. rewrite PTree.gmap. rewrite H. ss. flatten; ss.
  rewrite Pos.eqb_eq in Eq1; clarify. rewrite negb_true_iff in Eq.
  rewrite Pos.eqb_neq in Eq; clarify.
  rewrite negb_false_iff in Eq. rewrite Pos.eqb_eq in Eq; clarify.
  rewrite Pos.eqb_neq in Eq1; clarify.
Qed.

Lemma subst_capture_code_spec' : forall f f' tree d s pc i root,
  (fn_code f) ! pc = Some i ->
  f' = change_code f ((subst_capture_code tree d s root) (fn_code f)) ->
  (fn_code f') ! pc = Some i \/
  (fn_code f') ! pc = Some (subst_instr d s i) /\ in_set root (tree # pc) /\ root <> pc.
Proof.
  ii. destruct f; ss. unfold subst_capture_code in H0. inv H0. ss.
  rewrite PTree.gmap. rewrite H. ss. flatten; ss. eapply andb_true_iff in Eq. des.
  eapply negb_true_iff in Eq0. eapply Pos.eqb_neq in Eq0; clarify. right; eauto.
  left; eauto.
Qed.

Lemma transf_program_step_len_preserved : forall defs1 pub1 main1 ll1 defs2 pub2 main2 ll2,
  transf_program_step (mkprogram defs1 pub1 main1, ll1) =
    OK (mkprogram defs2 pub2 main2, ll2) ->
  Datatypes.length defs1 = Datatypes.length defs2 /\ Datatypes.length ll1 = Datatypes.length ll2.
Proof.
  assert (GLOBDEFS : forall l ll l' ll', transf_globdefs_step l ll = OK (l', ll') ->
    Datatypes.length l = Datatypes.length l' /\ Datatypes.length ll = Datatypes.length ll').
  { induction l; ii. simpl in H. inv H; eauto.
    destruct ll. inv H. eauto. unfold transf_globdefs_step in H. monadInv H.
    fold transf_globdefs_step in EQ1. eapply IHl in EQ1; eauto. des; simpl; eauto. }
  induction defs1; i.
  - ss. inv H. eauto.
  - induction ll1.
    + simpl in H. inv H; eauto.
    + monadInv H. monadInv EQ. destruct a. destruct g.
      * flatten EQ0; monadInv EQ0; monadInv EQ1; try inv EQ0;
          eapply GLOBDEFS in EQ; des; split; simpl; eauto.
      * split; simpl; eapply GLOBDEFS in EQ; simpl; des; eauto.
Qed.

Lemma repeatn_monad_def_dist : forall n a l, repeatn_monad transf_globdef_step (S n) (a, l) =
  do (ta, tl) <- transf_globdef_step (a, l); repeatn_monad transf_globdef_step n (ta, tl).
Proof.
  i. unfold repeatn_monad. unfold bind. flatten.
  - destruct p. simpl bind2. eauto.
  - ss.
Qed.

Lemma repeatn_monad_dist : forall n a1 defs1 l1 ll1 pub1 main1,
  Datatypes.length defs1 = Datatypes.length ll1 ->
  repeatn_monad transf_program_step n (mkprogram (a1 :: defs1) pub1 main1, l1 :: ll1)
  = do (a2, l2) <- repeatn_monad transf_globdef_step n (a1, l1);
    do (p2, ll2) <- repeatn_monad transf_program_step n (mkprogram defs1 pub1 main1, ll1);
    OK ((mkprogram (a2 :: (prog_defs p2)) (prog_public p2) (prog_main p2)), l2 :: ll2).
Proof.
  assert (REPEATN : forall n p l, repeatn_monad transf_program_step (S n) (p, l) =
    do (tp, tl) <- transf_program_step (p, l); repeatn_monad transf_program_step n (tp, tl)).
  { unfold repeatn_monad. i. destruct (transf_program_step (p, l)) eqn:STEP.
    - simpl bind. destruct p0. ss.
    - ss. }
  assert (ONEDEF : forall d1 pub1 main1 l1 ll1,
    transf_program_step (mkprogram (d1 :: nil) pub1 main1, l1 :: ll1) =
      do (d2, l2) <- transf_globdef_step (d1, l1);
      OK (mkprogram (d2 :: nil) pub1 main1, l2 :: ll1)).
  { i. unfold transf_program_step. simpl prog_defs.
    destruct (transf_globdefs_step (d1 :: nil) (l1 :: ll1)) eqn:D1. destruct p.
    unfold transf_globdefs_step in D1. monadInv D1. inv EQ1. ss; rewrite EQ. ss.
    unfold transf_globdefs_step in D1. unfold bind2 in D1. flatten D1. unfold bind2.
    flatten; unfold fundef in *; rewrite Eq in Eq0; inv Eq0. }
  assert (GLOBDEFS_LEN : forall l1 l2 l3 l4, transf_globdefs_step l1 l2 = OK (l3, l4) ->
    Datatypes.length l1 = Datatypes.length l3 /\ Datatypes.length l2 = Datatypes.length l4).
  { induction l1; i. inv H. eauto. destruct l2. inv H. eauto.
    unfold transf_globdefs_step in H. fold transf_globdefs_step in H. monadInv H.
    exploit IHl1; eauto. i; des; split; s; eauto. }
  assert (ERRMSG : forall e1 e2 defs ll def l,
    transf_globdefs_step defs ll = Error e1 -> transf_globdef_step (def, l) = Error e2 -> e1 = e2).
  { induction defs; i. inv H. destruct ll. inv H.
    unfold transf_globdefs_step in H. fold transf_globdefs_step in H. unfold bind2 in H. flatten H.
    eapply IHdefs; eauto. unfold transf_globdef_step in Eq, H0. flatten Eq.
    unfold bind2 in Eq, H0. flatten Eq. unfold transf_fundef_step in Eq5, Eq4. flatten Eq5.
    unfold bind2 in Eq5, Eq4. flatten Eq5. unfold transf_function_step in Eq2, Eq1. flatten Eq2. }
  intros n a1 defs1. revert n a1. remember (Datatypes.length defs1) as len.
  symmetry in Heqlen. assert (Datatypes.length defs1 <= len) by lia. rewrite <- Heqlen. clear Heqlen.
  generalize dependent defs1. induction len.
  - i. inv H. rewrite H2 in H0. symmetry in H0; apply length_zero_iff_nil in H0, H2; clarify.
    assert (repeatn_monad transf_program_step n (mkprogram nil pub1 main1, nil) =
      OK ((mkprogram nil pub1 main1), nil)).
    { generalize n as n0; induction n0; ss. } rewrite H. simpl. clear H.
    induction n; i.
    + s. eauto.
    + rewrite REPEATN. rewrite ONEDEF. rewrite repeatn_monad_def_dist.
      destruct (transf_globdef_step (a1, l1)) eqn:A1; cycle 1. eauto.
      destruct p. unfold bind2 at 2 4. simpl bind2. rewrite IHn. eauto.
  - i. destruct defs1.
    + assert (repeatn_monad transf_program_step n (mkprogram nil pub1 main1, ll1) =
        OK ((mkprogram nil pub1 main1), ll1)).
      { generalize n as n0; induction n0; ss. } rewrite H1. clear H1.
      simpl.
      induction n; i. simpl. eauto. rewrite REPEATN. rewrite ONEDEF. rewrite repeatn_monad_def_dist.
      destruct (transf_globdef_step (a1, l1)) eqn:A1; cycle 1. eauto.
      destruct p. unfold bind2 at 2 4. simpl bind2. rewrite IHn. eauto. eauto.
    + simpl in H. generalize dependent defs1. generalize dependent p. induction n.
      * i. simpl. eauto.
      * i. rewrite REPEATN. destruct ll1. inv H0. rewrite IHlen; eauto; try lia.
        unfold transf_program_step at 1. simpl prog_defs; simpl prog_public; simpl prog_main.
        unfold transf_globdefs_step. fold transf_globdefs_step. rewrite repeatn_monad_def_dist.
        destruct (transf_globdef_step (a1, l1)) eqn:A1; cycle 1. ss.
        destruct p0. unfold bind2 at 3. unfold bind2 at 7.
        rewrite repeatn_monad_def_dist. destruct (transf_globdef_step (p, l)) eqn:PTRANS; cycle 1.
        s. unfold bind2. flatten; eauto. revert PTRANS Eq. generalize p l p0 l0 e e0.
        generalize n. induction n0; i. simpl in Eq. inv Eq. rewrite repeatn_monad_def_dist in Eq.
        unfold bind2 in Eq. flatten Eq. exploit IHn0; eauto. unfold transf_globdef_step in Eq0, PTRANS.
        unfold bind2 in PTRANS, Eq0. flatten PTRANS. unfold transf_fundef_step in Eq5, Eq2.
        flatten Eq2. unfold bind2 in Eq5, Eq2. flatten Eq5. unfold transf_function_step in Eq3, Eq1.
        flatten Eq1. eauto. destruct p1. unfold bind2 at 4. unfold bind2 at 8.
        rewrite REPEATN. unfold transf_program_step at 2.
        simpl prog_defs; simpl prog_public; simpl prog_main.
        destruct (transf_globdefs_step defs1 ll1) eqn:DEFSTRANS. destruct p2.
        unfold bind2 at 4. unfold bind2 at 3. unfold bind2 at 2. unfold bind2 at 1.
        unfold bind2 at 6. unfold bind2 at 5. eapply GLOBDEFS_LEN in DEFSTRANS as LEN. des.
        rewrite (IHn p0 l0 (l2 :: l4)). rewrite IHlen; eauto. lia. inv H0. lia. lia. s. inv H0. lia.
        s. unfold bind2 at 3. flatten; s. unfold bind2; flatten; eauto.
        revert Eq0. revert DEFSTRANS. generalize n p0 l0. induction n0; i; eauto. inv Eq0.
        rewrite repeatn_monad_def_dist in Eq0. symmetry in Eq0. unfold bind2 in Eq0; flatten Eq0.
        { exploit IHn0; eauto.  } exploit ERRMSG; eauto. i; eauto. clarify.
        unfold bind2. flatten; cycle 1. revert DEFSTRANS Eq0. generalize n ll1 p0 l0. induction n0.
        i. inv Eq0. i. rewrite repeatn_monad_def_dist in Eq0. unfold bind2 in Eq0. flatten Eq0.
        eapply IHn0; eauto. exploit ERRMSG; eauto; i; clarify.
        revert DEFSTRANS Eq. generalize n ll1 p1 l2. induction n0.
        i. inv Eq. i. rewrite repeatn_monad_def_dist in Eq. unfold bind2 in Eq. flatten Eq.
        eapply IHn0; eauto. exploit ERRMSG; eauto; i; clarify.
Qed.

Lemma find_capture_all_NoDup : forall c clist, clist = find_capture_all c ->
  list_norepet clist.
Proof.
  i. unfold find_capture_all in H. rewrite PTree.fold_spec in H. unfold _find_capture in H.
  exploit PTree.elements_keys_norepet. instantiate (1 := c). i.
  remember (PTree.elements c) as celems. clear Heqcelems. generalize dependent clist.
  induction celems.
  - i. clarify.
  - i. destruct a. ss. flatten H.
    + remember (fun a p => _) as f. enough (forall l1 l2, fold_left f l1 l2 = fold_left f l1 nil ++ l2).
      rewrite H1 in H. rewrite H. eapply list_norepet_append_commut. ss. econs.
      ii. rewrite Heqf in H2. inv H0. revert H2 H5. generalize celems. induction celems0.
      { ss. }
      { ss. i. rewrite H1 in H2. eapply in_app in H2. des.
        - exploit IHcelems0; eauto.
        - destruct a. ss. flatten H2. inv H2; eauto. inv H2; eauto. }
      inv H0. revert H5. generalize celems as l. induction l.
      { i; ss. }
      { i; ss. rewrite H1. eapply list_norepet_append_commut. destruct a; ss. flatten.
        - ss. econs. inv H5. revert H2. generalize l. induction l0; ss; ii.
          rewrite H1 in H. rewrite in_app_iff in H; des.
          + exploit IHl0; eauto.
          + destruct a; ss. flatten H; inv H; eauto.
          + inv H5; eauto.
        - ss. exploit IHl; inv H5; eauto. }
      induction l1; ss. i. rewrite IHl1. remember (f nil a) as res.
      rewrite Heqf in Heqres. flatten Heqres.
      * rewrite (IHl1 res). remember (f l2 a) as res'. rewrite Heqf in Heqres'. rewrite Eq0 in Heqres'.
        rewrite Heqres'. rewrite Heqres. remember (fold_left f l1 nil). rewrite <- app_assoc. eauto.
      * rewrite (IHl1 res). remember (f l2 a) as res'. rewrite Heqf in Heqres'. rewrite Eq0 in Heqres'.
        rewrite Heqres'. rewrite Heqres. remember (fold_left f l1 nil). rewrite <- app_assoc. eauto.
    + inv H0; eauto.
Qed.

Lemma filter_preserved : forall l r, ~ In r l -> filter (fun x => negb (Pos.eqb r x)) l = l.
Proof.
  induction l; ss; ii. flatten.
  - rewrite IHl; eauto.
  - rewrite negb_false_iff in Eq. rewrite Pos.eqb_eq in Eq. exploit H; eauto; ss.
Qed.

Lemma root_capture_in : forall root l t, list_norepet l -> root_capture root l t -> In root l.
Proof.
  assert (forall l d t n, find_parent l (t # d) = Some n -> In n l).
  { induction l; ss; ii. flatten H; eauto. }
  i. destruct l as [ | hd tl]; ss.
  unfold find_capture_root in H1. remember (Datatypes.length tl) as len. generalize dependent tl.
  revert hd root t. induction len.
  - i. symmetry in Heqlen; eapply length_zero_iff_nil in Heqlen; clarify. left; ss.
  - i. ss. flatten H; clarify; eauto. eapply H in Eq as IN.
    eapply in_split in IN; des. clarify. rewrite filter_app.
    rewrite (filter_preserved l1); cycle 1.
    { rewrite app_comm_cons in H0. eapply list_norepet_append_commut in H0. inv H0.
      ii; eapply H3; eapply in_app_iff; right; eauto. }
    ss. rewrite Pos.eqb_refl; ss. rewrite filter_preserved; cycle 1.
    { rewrite app_comm_cons in H0. eapply list_norepet_append_commut in H0. inv H0.
      ii; eapply H3; eapply in_app_iff; left; eauto. }
    destruct l1. ss.
    + destruct l2.
      * right. left. destruct len; ss.
      * exploit (IHlen n); eauto. inv H0; eauto.
    + repeat rewrite <- app_comm_cons in *.
      assert (len = Datatypes.length (n0 :: l1 ++ l2)).
      { ss. rewrite app_length in *; ss. lia. }
      eapply (IHlen n) in H1. des.
      * right. constructor 2. eapply in_app_iff; right; left. eapply H1.
      * right. inv H1.
        { econs; eauto. }
        { eapply in_app_iff in H2; des.
          - constructor 2; eapply in_app_iff; left; eauto.
          - constructor 2; eapply in_app_iff; right; eauto. }
      * inv H0. inv H5. eapply list_norepet_append_commut in H3. inv H3.
        econs; eauto.
        { ii. inv H0.
          - eapply H2; eapply in_app_iff; right; eauto.
          - eapply H5; eapply in_app_iff in H1; des; eapply in_app_iff; eauto. }
        econs; eauto.
        { ii. eapply in_app_iff in H0; des; eapply H2; eapply in_app_iff; eauto. }
        eapply list_norepet_append_commut; eauto.
      * eauto.
Qed.

Lemma propagate_capture_step_spec : forall t c1 hd1 tl1 c2 l2 root i d s,
  list_norepet (hd1 :: tl1) ->
  propagate_capture_step t (c1, hd1 :: tl1) = (c2, l2) ->
  root = find_capture_root t hd1 tl1 ->
  c1 ! root = Some i -> is_capture i = Some (d, s) ->
  Datatypes.length l2 = Datatypes.length tl1 /\ list_norepet l2.
Proof.
  i. unfold propagate_capture_step in H0. clarify. rewrite H2 in H0. rewrite H3 in H0.
  inv H0. remember (find_capture_root t hd1 tl1) as root.
  assert (In root (hd1 :: tl1)).
  { exploit root_capture_in; eauto. }
  apply in_split in H0. des.
  flatten.
  - rewrite negb_true_iff in Eq. eapply Pos.eqb_neq in Eq.
    destruct l1.
    + inv H0. rewrite <- H4 in Eq; clarify.
    + inv H0. rewrite H5 in H. rewrite app_comm_cons in H. eapply list_norepet_append_commut in H.
      inv H. rewrite filter_app. ss. repeat rewrite filter_preserved; cycle 1.
      ii; eapply H4; eapply in_app_iff; left; eauto.
      ii; eapply H4; eapply in_app_iff; right; eauto.
      rewrite Pos.eqb_refl. ss.
      repeat rewrite app_length. ss. split.
      * lia.
      * exploit list_norepet_append_commut; eauto.
  - rewrite negb_false_iff in Eq. eapply Pos.eqb_eq in Eq; subst hd1.
    destruct l1; cycle 1.
    + inv H0. inv H. exfalso; eapply H4; eapply in_app_iff; right; eauto.
    + inv H0. rewrite filter_preserved; inv H; eauto.
Qed.

Lemma compute_dom_preserved : forall f t d s root,
  compute_dom f = Some t ->
  compute_dom (change_code f (subst_capture_code t d s root (fn_code f))) = Some t.
Proof.
  i. unfold compute_dom in *. ss. unfold DS.fixpoint, DS.fixpoint_from in *.
  remember (subst_capture_code t d s root (fn_code f)) as c'.
  enough (DS.step (fn_code f) successors_instr (transfer f) =
    DS.step c' successors_instr (transfer (change_code f c'))).
  rewrite <- H0. eauto.
  unfold transfer. fold (transfer f). apply extensionality.
  i. unfold DS.step. flatten; ss.
  - clarify. unfold subst_capture_code in Eq2. rewrite PTree.gmap in Eq2.
    rewrite Eq1 in Eq2. ss. inv Eq2. destruct i; flatten; ss.
  - clarify. unfold subst_capture_code in Eq2. rewrite PTree.gmap in Eq2.
    rewrite Eq1 in Eq2. ss.
  - clarify. unfold subst_capture_code in Eq2. rewrite PTree.gmap in Eq2.
    rewrite Eq1 in Eq2. ss.
Qed.

Lemma repeatn_monad_transf_globdef_step : forall f i t n,
  compute_dom f = Some t ->
  n >= Datatypes.length (find_capture_all (fn_code f)) ->
  repeatn_monad transf_globdef_step n (i, Gfun (Internal f), find_capture_all (fn_code f))
  = OK (i, Gfun (Internal (change_code f (propagate_capture t (fn_code f) (find_capture_all (fn_code f))))), nil).
Proof.
  i. remember (find_capture_all (fn_code f)) as caplist.
  eapply find_capture_all_NoDup in Heqcaplist as HNOREPET.
  (* rewrite Heqcaplist at 2. *)
  clear Heqcaplist.
  (* remember (Datatypes.length caplist) as len. assert (len >= Datatypes.length caplist) by lia. clear Heqlen. *)
  generalize dependent caplist. generalize dependent f. induction n.
  - i. assert (caplist = nil). eapply length_zero_iff_nil; eauto; try lia. clarify.
    ss. unfold propagate_capture. ss. destruct f; ss.
  - i. rewrite repeatn_monad_def_dist. unfold bind2; flatten; cycle 1.
    { simpl in Eq. rewrite H in Eq. destruct caplist. simpl in Eq. inv Eq.
      flatten Eq; simpl in Eq; inv Eq. }
    unfold transf_globdef_step in Eq. unfold bind2 in Eq. flatten Eq.
    unfold transf_fundef_step in Eq1. unfold bind2 in Eq1. flatten Eq1.
    unfold transf_function_step in Eq. rewrite H in Eq. flatten Eq.
    destruct caplist. inv Eq0. rewrite IHn; eauto. s. lia.
    rewrite IHn; eauto. simpl. unfold change_code. simpl.
    enough (forall t c1 c2 hd tl l,
      list_norepet (hd :: tl) -> propagate_capture_step t (c1, hd :: tl) = (c2, l) ->
      propagate_capture t c2 l = propagate_capture t c1 (hd :: tl)).
    erewrite H1; eauto.
    i. pose proof H2 as H2'. unfold propagate_capture_step in H2. flatten H2.
    + unfold propagate_capture at 2. simpl propagate_capture_fuel.
      rewrite Eq. rewrite Eq1. remember (if (negb _) then _ else _) as l'.
      eapply propagate_capture_step_spec in H2'; eauto.
      unfold propagate_capture. des. rewrite <- H2'. eauto.
    + unfold propagate_capture at 2. simpl. rewrite Eq; rewrite Eq1.
      unfold propagate_capture. ss.
    + unfold propagate_capture. ss. rewrite Eq. ss.
    + unfold propagate_capture_step in Eq0. flatten Eq0; try (destruct f; eauto; fail).
      eapply compute_dom_preserved; eauto.
    + pose proof Eq0 as Eq0'. unfold propagate_capture_step in Eq0. flatten Eq0; try (ss; lia; fail).
      eapply propagate_capture_step_spec in Eq0'; eauto. des; eauto. unfold node in *. rewrite Eq0'.
      ss; lia.
    + pose proof Eq0 as Eq0'. unfold propagate_capture_step in Eq0. flatten Eq0; try econs.
      eapply propagate_capture_step_spec in Eq0'; eauto. des; eauto.
Qed.

(* match_prog definitions for step optimization *)
Definition match_prog_step (p: program) (tp: program) :=
  match_program (fun cu f tf => exists l l', transf_fundef_step (f, l) = OK (tf, l')) eq p tp.

Lemma transf_program_step_match p tp l tl :
  Datatypes.length l = Datatypes.length (prog_defs p) ->
  transf_program_step (p, l) = OK (tp, tl) -> match_prog_step p tp.
Proof.
  unfold transf_program_step; i. monadInv H0.
  red. unfold match_program, match_program_gen. split; auto.
  revert x EQ H. generalize l tl. clear l tl. generalize (prog_defs p).
  induction l; intros.
  - monadInv EQ. constructor.
  - destruct a. destruct g as [f | v].
    + destruct l0.
      * inv H.
      * pose proof EQ as EQ'. monadInv EQ. monadInv EQ0.
        constructor; auto. split; auto. econstructor 1. eapply linkorder_refl.
        exists l0, x1. unfold transf_globdefs_step in EQ'. fold transf_globdefs_step in EQ'.
        monadInv EQ'. unfold transf_globdef_step in EQ0. monadInv EQ0. eauto.
        eapply IHl; eauto.
    + destruct l0.
      * inv H.
      * monadInv EQ. constructor; auto. split; auto. constructor; auto. destruct v.
        econs; auto.
        eapply IHl; eauto.
Qed.

Section PRESERVATION.
  Lemma assigned_code_spec_subst_capture_code : forall c pc r t d s hd tl,
    assigned_code_spec (subst_capture_code t d s (find_capture_root t hd tl) c) pc r ->
    assigned_code_spec c pc r.
  Proof.
    ii. inv H; unfold subst_capture_code in H0; rewrite PTree.gmap in H0;
      destruct (c ! pc) eqn:EPC; ss; inv H0; destruct i; flatten H1; clarify; ss;
      try inv H1; eauto.
  Qed.

  Lemma cfg_subst_capture_code : forall f f' t d s hd tl,
    wf_ssa_function f -> 
    f' = change_code f (subst_capture_code t d s (find_capture_root t hd tl) (fn_code f)) ->
    (forall i j, cfg f i j <-> cfg f' i j).
  Proof.
    split; i; clarify.
    - inv H1. econstructor. ss. unfold subst_capture_code.
      rewrite PTree.gmap. rewrite HCFG_ins. ss. destruct (in_set _ _ && _).
      + destruct ins; auto.
      + auto.
    - inv H1; ss. unfold subst_capture_code in HCFG_ins.
      rewrite PTree.gmap in HCFG_ins. destruct (fn_code f) ! i eqn:EI.
      + ss. inv HCFG_ins. destruct (in_set _ _ && _).
        econstructor; eauto. destruct i0; auto.
        econstructor; eauto.
      + inv HCFG_ins.
  Qed.

  Lemma reached_subst_capture_code : forall f f' t d s hd tl,
    wf_ssa_function f ->
    f' = change_code f (subst_capture_code t d s (find_capture_root t hd tl) (fn_code f)) ->
    (forall i, Dom.reached (cfg f) (fn_entrypoint f) i
      <-> Dom.reached (cfg f') (fn_entrypoint f') i).
  Proof.
    split; i.
    - rewrite H0; ss. apply star_eq with (cfg f); eauto. ii.
      rewrite cfg_subst_capture_code in H2; eauto.
    - ss. apply star_eq with (cfg f'). ii.
      rewrite cfg_subst_capture_code; eauto. clarify; eauto.
  Qed.

  Lemma exit_subst_capture_code : forall f f' t d s hd tl,
    wf_ssa_function f -> 
    f' = change_code f (subst_capture_code t d s (find_capture_root t hd tl) (fn_code f)) ->
    (forall i, exit f i <-> exit f' i).
  Proof.
    split; i.
    - unfold exit in *. flatten H1; ss; clarify; ss; unfold subst_capture_code;
        rewrite PTree.gmap; rewrite Eq; ss; destruct (in_set _ _ && _); eauto.
    - unfold exit in *. flatten H1; ss; clarify; ss; unfold subst_capture_code in Eq;
        rewrite PTree.gmap in Eq; destruct (fn_code f) ! i eqn:EFI; clarify; ss;
        inv Eq; flatten H2; destruct i0; ss; inv H1; auto.
  Qed.

  Lemma path_subst_capture_code : forall f f' t d s hd tl,
    wf_ssa_function f -> 
    f' = change_code f (subst_capture_code t d s (find_capture_root t hd tl) (fn_code f)) ->
    (forall i j p, SSApath f i p j <-> SSApath f' i p j).
  Proof.
    split.
    - induction 1; go. econstructor 2 with s2; auto. inversion STEP.
      + econstructor; eauto. rewrite <- reached_subst_capture_code; eauto.
        rewrite <- cfg_subst_capture_code; eauto.
      + econstructor; eauto.
        * rewrite reached_subst_capture_code in CFG; eauto.
        * rewrite <- exit_subst_capture_code; eauto.
    - induction 1; eauto.
      + constructor.
      + inv STEP; ss.
        * econstructor; eauto. econstructor; eauto.
          exploit reached_subst_capture_code; eauto. ii. rewrite H0; eauto.
          rewrite cfg_subst_capture_code; eauto.
        * econstructor; eauto. econstructor; eauto.
          exploit reached_subst_capture_code; eauto. ii. rewrite H0; eauto.
          rewrite exit_subst_capture_code; eauto.
  Qed.

  Lemma dom_subst_capture_code : forall f f' t d s hd tl,
    wf_ssa_function f ->
    f' = change_code f (subst_capture_code t d s (find_capture_root t hd tl) (fn_code f)) ->
    (forall i j, dom f i j <-> dom f' i j).
  Proof.
    split; i.
    - inversion H1. constructor. constructor.
      + rewrite <- reached_subst_capture_code; eauto.
      + ii. exploit path_subst_capture_code; eauto. ii. rewrite <- H5 in H4.
        clarify; ss. auto.
    - inv H1. constructor. ss. constructor.
      + exploit reached_subst_capture_code; eauto. ii. ss. rewrite H0. eapply RPC'.
      + ii. exploit path_subst_capture_code; eauto. ii. ss.
        apply PATH; auto. rewrite <- H1; eauto.
  Qed.

  Lemma make_predecessors_subst_capture_code : forall f t d s hd tl,
    wf_ssa_function f ->
    (Kildall.make_predecessors (fn_code f) successors_instr) =
    (Kildall.make_predecessors
      (subst_capture_code t d s (find_capture_root t hd tl) (fn_code f)) successors_instr).
  Proof.
    ii.
    eapply same_successors_same_predecessors. i. repeat rewrite PTree.gmap1.
    destruct (fn_code f) ! i eqn:EI; destruct (subst_capture_code _ _ _ _ _) ! i eqn:EI';
    s; unfold subst_capture_code in EI'; rewrite PTree.gmap in EI'; rewrite EI in EI'; ss.
    inv EI'. flatten. destruct i0; ss.
  Qed.

  Lemma successors_subst_capture_code : forall f f' t d s hd tl pc,
    wf_ssa_function f ->
    f' = change_code f (subst_capture_code t d s (find_capture_root t hd tl) (fn_code f)) ->
    (successors f) ! pc = (successors f') ! pc.
  Proof.
    intros f0 f'0 t d s hd tl pc Hwf Hf'. unfold successors. clarify.
    repeat rewrite PTree.gmap1. destruct (fn_code f0) ! pc eqn:EPC.
    eapply subst_capture_code_spec in EPC as EPC'. flatten EPC'; ss;
    rewrite EPC'; ss; destruct i; ss. ss.
    unfold subst_capture_code; rewrite PTree.gmap; rewrite EPC; ss.
  Qed.
  
  Lemma use_code_subst_capture_code : forall f f' t d s hd tl pc x i,
    wf_ssa_function f ->
    f' = change_code f (subst_capture_code t d s (find_capture_root t hd tl) (fn_code f)) ->
    (fn_code f) ! (find_capture_root t hd tl) = Some i -> is_capture i = Some (d, s) ->
    (forall n d, reached f n -> in_set d t # n = true -> dom f d n) ->
    (* (forall pc' pc'', in_set pc' t # pc'' = true -> pc' <> pc'') -> *)
    use_code f' x pc -> use_code f x pc \/ (x = d /\ use_code f s pc /\ sdom f (find_capture_root t hd tl) pc).
  Proof.
    assert (Hrn: forall x a s d, rename_reg d s a = x -> a = x \/ x = d /\ a = s).
    { ii. unfold rename_reg in H. flatten H; auto. rewrite Pos.eqb_eq in Eq; clarify; auto. }
    assert (Hin: forall x d s l, In x (map (rename_reg d s) l) -> In x l \/ x = d /\ In s l).
    { induction l; auto. ii. ss. des. apply Hrn in H; des; clarify; auto. intuition. }
    assert (Hbin: forall x d s a, In x (params_of_builtin_arg (rename_barg d s a)) ->
            In x (params_of_builtin_arg a) \/ x = d /\ In s (params_of_builtin_arg a)).
    { induction a; ss; ii. des; auto. apply Hrn in H; des; auto.
      all: apply in_app_iff in H; des;
      [ exploit IHa1; eauto; i; des; [left; apply in_app_iff; left; auto | right; auto;
      split; auto; apply in_app_iff; left; auto] |
      exploit IHa2; eauto; i; des; [left; apply in_app_iff; right; auto | right; split; auto;
      apply in_app_iff; right; auto ]]. }
    assert (Hbins: forall x d s l, In x (params_of_builtin_args (map (rename_barg d s) l))
            -> In x (params_of_builtin_args l) \/ x = d /\ In s (params_of_builtin_args l)).
    { induction l; auto. ii. ss. apply in_app_iff in H; des.
      - apply Hbin in H; des. left; apply in_app_iff; left; auto. right; split; auto.
        apply in_app_iff; left; auto.
      - exploit IHl; eauto. i; des; intuition; auto. }
    (* assert (Hrnf: forall x d s f, rename_fn d s f = inl x ->
            f = inl x \/ x = d /\ f = inl s).
    { ii. destruct f; ss; inv H. destruct (Pos.eq_dec r s); clarify; auto.
      right; unfold rename_reg; split; flatten; auto. apply Pos.eqb_neq in Eq; clarify.
      left; unfold rename_reg; flatten; clarify. apply Pos.eqb_eq in Eq; clarify. } *)
    ii. clarify. pose proof H4 as H'.

    inv H4; unfold subst_capture_code in H0; ss; rewrite PTree.gmap in H0;
    destruct (fn_code f) ! pc eqn:EPC; try discriminate; ss; inv H0;
    destruct (in_set _ _ && _ _) eqn:Eq; try (clarify; left; eauto using use_code; fail);
    try destruct i0; clarify;
    apply andb_true_iff in Eq; destruct Eq as [Eq Eq']; apply H3 in Eq as DOM; eauto;
    try (inv H6; try apply Hin in H5; try apply Hbins in H5; des;
        [left; eauto using use_code |
        clarify; right; split; auto; split; auto; eauto using use_code; constructor; auto;
        ii; clarify; rewrite negb_true_iff in Eq'; rewrite Pos.eqb_neq in Eq'; clarify]; fail).
    + inv H6. des.
      * apply Hrn in H5.
        des; clarify; [left; eauto using use_code | right; split; auto; split; auto].
        eauto using use_code. econs; eauto. ii; subst pc; rewrite H1 in EPC; inv EPC; ss.
      * apply Hin in H5. des;
        [ left; eauto using use_code | clarify; right; split; auto; split; auto ].
        eauto using use_code. econs; eauto. ii; subst pc; rewrite H1 in EPC; inv EPC; ss.
    + inv H6. des.
      * clarify. 
        (* apply Hrnf in H7. des. destruct s2; inv H7. *)
        left; eauto using use_code.
        (* clarify. right; split; auto; split; auto.
        eauto using use_code. econs; eauto. ii; subst pc; rewrite H1 in EPC; inv EPC; ss. *)
      * apply Hin in H5; des.
        (* destruct s2; inv H7. *)
        left; eauto using use_code. clarify.
        (* destruct s2; inv H7. *)
        right; split; auto; split; auto; eauto using use_code.
        econs; eauto. ii; subst pc; rewrite H1 in EPC; inv EPC; ss.
    + inv H6. des; clarify.
      * left; eauto using use_code.
      * apply Hin in H5; des. eauto using use_code.
        clarify. right; splits; auto; auto. eauto using use_code.
        econs; eauto. ii; subst pc; rewrite H1 in EPC; inv EPC; ss.
    (* + inv H5. des. apply Hin in H5. des. destruct s2; inv H7.
      left; eauto using use_code. destruct s2; inv H7.
      clarify; right; split; auto; split; auto; eauto using use_code.
      econs; eauto. ii; subst pc; rewrite H1 in EPC; inv EPC; ss. *)
    (* + inv H6. apply Hin in H5. des. destruct s1; inv H7; left; eauto using use_code.
      destruct s1; inv H7; right; split; auto; split; auto; eauto using use_code.
      econs; eauto. ii; subst pc; rewrite H1 in EPC; inv EPC; ss. *)
    + inv H5. destruct (Pos.eq_dec r s). clarify. unfold rename_reg. flatten.
      right; split; auto; split; auto; eauto using use_code.
      econs; eauto. ii; subst pc; rewrite H1 in EPC; inv EPC; ss.
      apply Pos.eqb_neq in Eq0; clarify. left; unfold rename_reg; flatten; clarify.
      apply Pos.eqb_eq in Eq0; clarify. eauto using use_code.
    + inv H5. destruct o; ss. inv H4. destruct (Pos.eq_dec r s). clarify.
      unfold rename_reg. flatten. right; split; auto; split; auto; eauto using use_code.
      econs; eauto. ii; subst pc; rewrite H1 in EPC; inv EPC; ss.
      apply Pos.eqb_neq in Eq0; clarify. left; unfold rename_reg; flatten; clarify.
      apply Pos.eqb_eq in Eq0; clarify. eauto using use_code.
  Qed.

  Lemma use_subst_capture_code : forall f f' t d s hd tl pc x i,
    wf_ssa_function f ->
    f' = change_code f (subst_capture_code t d s (find_capture_root t hd tl) (fn_code f)) ->
    (fn_code f) ! (find_capture_root t hd tl) = Some i -> is_capture i = Some (d, s) ->
    (forall n d, reached f n -> in_set d t # n = true -> dom f d n) ->
    (* (forall pc' pc'', in_set pc' t # pc'' = true -> pc' <> pc'') -> *)
    use f' x pc -> use f x pc \/ (x = d /\ use f s pc /\ sdom f (find_capture_root t hd tl) pc).
  Proof.
    ii. inv H4.
    eapply use_code_subst_capture_code in H5; des; eauto using use.
    inv H5; ss. rewrite <- make_predecessors_subst_capture_code in KPRED; ss.
    left; econstructor 2. econstructor; eauto.
  Qed.

  Lemma def_subst_capture_code : forall f f' t d s hd tl pc x i,
    wf_ssa_function f ->
    f' = change_code f (subst_capture_code t d s (find_capture_root t hd tl) (fn_code f)) ->
    (fn_code f) ! (find_capture_root t hd tl) = Some i -> is_capture i = Some (d, s) ->
    (forall n d, reached f n -> in_set d t # n = true -> dom f d n) ->
    (* (forall pc' pc'', in_set pc' t # pc'' = true -> pc' <> pc'') -> *)
    def f' x pc -> def f x pc.
  Proof.
    ii. inv H4.
    - ss. inv H5. ss. constructor; auto. ss. constructor. constructor 2.
      des. eapply use_subst_capture_code in H0; eauto. des; ss.
      + exists pc; eauto.
      + clarify. destruct i; ss. destruct e; ss. destruct l; ss. destruct b0; ss.
        destruct l; ss. destruct b; ss. inv H2. eapply subst_capture_code_spec in H1 as Hs.
        flatten Hs; exploit H6; ss; econstructor 4; eauto.
      + auto.
      + ii. inv H5;
        eapply subst_capture_code_spec in H7 as Hs; flatten Hs; exploit H6; ss;
        eauto using assigned_code_spec.
    - ss. apply assigned_code_spec_subst_capture_code in H5. constructor; eauto.
    - ss. eauto using def.
  Qed.

  Lemma subst_capture_code_preserve_wf_ssa_function : forall f t d s hd tl i,
    wf_ssa_function f ->
    (forall n d, reached f n -> in_set d t # n = true -> dom f d n) ->
    (* (forall pc' pc'', in_set pc' t # pc'' = true -> pc' <> pc'') -> *)
    (fn_code f) ! (find_capture_root t hd tl) = Some i -> is_capture i = Some (d, s) ->
    wf_ssa_function 
      (change_code f (subst_capture_code t d s (find_capture_root t hd tl) (fn_code f))).
  Proof.
    intros f0 t d s hd tl i Hwf Hdom Hcpt. constructor.
    - econstructor; eauto. repeat split; ii; ss.
      + eapply assigned_code_spec_subst_capture_code in H0, H1.
        exploit assigned_code_unique. eauto. eauto. eapply H0. eauto.
      + exploit def_def_eq. eauto. eauto. econstructor 3; eapply H0. eauto.
      + eapply assigned_code_spec_subst_capture_code in H0. 
        exploit assigned_code_and_phi; eauto.
      + eapply assigned_code_spec_subst_capture_code in H1.
        exploit assigned_code_and_phi; eauto.
      + ii; ss. inv Hwf. inv fn_ssa; eauto. 
    - ii; ss. split.
      + ii. apply assigned_code_spec_subst_capture_code in H1; eauto.
        inv Hwf. exploit fn_ssa_params; eauto. ii. des. eapply H2; eauto.
      + ii. exploit fn_ssa_params; eauto. ii; intuition. eapply H4; eauto.
    - ii. rewrite <- dom_subst_capture_code; eauto.
      eapply def_subst_capture_code in H1 as HDEF; eauto.
      eapply use_subst_capture_code in H0; eauto. des.
      + exploit fn_strict; eauto.
      + clarify. remember (find_capture_root t hd tl) as root.
        destruct i; ss. destruct e, l; ss. destruct b0, l, b; ss. inv H.
        exploit def_def_eq. eauto. eauto. econstructor 2. econstructor 4; eauto.
        ii; clarify. inv H3; ss.
    - ii. apply assigned_code_spec_subst_capture_code in H1.
      eapply use_code_subst_capture_code in H0; eauto; des.
      exploit fn_use_def_code; eauto. clarify. inv H3. exploit NEQ; ii; ss.
      destruct i; inv H. flatten H3; eapply def_def_eq; eauto.
    - unfold block_nb_args. ss. ii. rewrite <- make_predecessors_subst_capture_code; eauto.
      exploit fn_wf_block; eauto.
    - ii; ss. inv H0. ss.
      erewrite <- make_predecessors_subst_capture_code in Hpreds; eauto.
      unfold Kildall.successors_list in H1.
      erewrite <- successors_subst_capture_code in H1; eauto.
      destruct (successors f0) ! pc eqn:FPC. exploit (fn_normalized f0); eauto.
      econstructor; eauto. unfold Kildall.successors_list; rewrite FPC; eauto.
      i. unfold subst_capture_code; rewrite PTree.gmap; rewrite H0; flatten; ss. inv H1.
    - split; ss. ii.
      inv H0; ss. rewrite <- make_predecessors_subst_capture_code in Hpreds; eauto.
      exploit fn_phicode_inv; eauto; ii. des. elim H0; eauto. econstructor; eauto.
      ii. exploit fn_phicode_inv; eauto; ii. des. elim H2; eauto. ii.
      econstructor; eauto. ss. erewrite <-make_predecessors_subst_capture_code; eauto.
    - ss. ii. exploit reached_subst_capture_code; eauto. ii; ss. rewrite <- H1.
      destruct (fn_code f0) ! pc eqn:EPC; eauto. exploit wf_ssa_reached; eauto.
      unfold subst_capture_code in H0; rewrite PTree.gmap in H0; rewrite EPC in H0; ss.
    - ss. ii. unfold subst_capture_code in *. rewrite PTree.gmap in *; ss.
      destruct (fn_code f0) ! pc eqn:EPC; ss; inv H0; destruct i0; flatten H1;
      exploit fn_code_closed; eauto; ii; des; eexists; rewrite H0; ss.
    - ss. exploit fn_entry; eauto. ii. des. unfold subst_capture_code.
      rewrite PTree.gmap. rewrite H0. ss. exists s0; flatten; eauto.
    - ii; ss. rewrite <- cfg_subst_capture_code in H0; eauto.
      exploit fn_entry_pred; eauto.
    - ii. inv H0; ss. exploit fn_ext_params_complete; eauto. des.
      eapply use_subst_capture_code in H1; des; eauto.
      + exploit fn_ext_params_complete; eauto. econstructor 2; eauto.
        ii. eelim H3; eauto. inv H0; eapply subst_capture_code_spec in H4; flatten H4;
        ss; eauto using assigned_code_spec.
      + clarify. destruct i; inv H. flatten H4; eapply subst_capture_code_spec in Hcpt;
        flatten Hcpt; eelim H3; eauto.
    - ii; ss. exploit dom_subst_capture_code; eauto. ii. rewrite <- H2.
      exploit reached_subst_capture_code; eauto. ii. rewrite <- H3 in H0.
      exploit fn_dom_test_correct; eauto; ss.
  Qed.

End PRESERVATION.

(** * Correctness of the optimization *)
Section FUNCTION_STEP.

  Variables f f' : function.
  Variables il il' : list node.
  Hypothesis WF : wf_ssa_function f.
  Hypothesis STEP : OK (f', il') = transf_function_step (f, il).

  Lemma transf_function_step_phicode :
    fn_phicode f' = fn_phicode f.
  Proof.
    unfold transf_function_step in STEP. flatten STEP. destruct f; ss.
  Qed.

  Lemma transf_function_step_spec :
    f = f' /\ il' = nil \/
    exists domtree root d s pc' hd tl,
    compute_dom f = Some domtree /\
    il = hd :: tl /\
    find_capture_root domtree hd tl = root /\
    il' = filter (fun x => negb (Pos.eqb root x)) il /\
    (fn_code f) ! root = Some (Ibuiltin EF_capture ((BA s) :: nil) (BR d) pc') /\
    f' = change_code f (subst_capture_code domtree d s root (fn_code f)).
  Proof.
    unfold transf_function_step in STEP. flatten STEP. destruct il.
    - left; destruct f; ss. inv Eq0; ss.
    - unfold propagate_capture_step in Eq0. flatten Eq0.
      + destruct i; inv Eq2. flatten H0. right.
        exists t, (find_capture_root t n l0), r, r0, n0, n, l0; ss.
      + left; destruct f; ss.
      + left; destruct f; ss.
  Qed.

  Lemma transf_function_step_instr_spec : forall i pc,
    (fn_code f) ! pc = Some i ->
    (fn_code f') ! pc = Some i \/
    exists root d s pc' domtree,
      compute_dom f = Some domtree /\
      root <> pc /\
      root_capture root il domtree /\
      in_set root (domtree !! pc) /\
      (fn_code f) ! root = Some (Ibuiltin EF_capture ((BA s) :: nil) (BR d) pc') /\
      (fn_code f') ! pc = Some (subst_instr d s i).
  Proof.
    pose proof transf_function_step_spec; des; clarify; eauto. i.
    remember (find_capture_root domtree hd tl) as root.
    destruct (fn_code (change_code f (subst_capture_code domtree d s root (fn_code f)))) ! pc
      eqn : PC; unfold change_code, subst_capture_code in PC; simpl in PC;
      rewrite PTree.gmap in PC; rewrite H0 in PC; simpl in PC. inv PC. flatten; eauto.
    right. exists (find_capture_root domtree hd tl), d, s, pc', domtree; s. 
    rewrite andb_true_iff in Eq; des. rewrite negb_true_iff in Eq0.
    splits; eauto. ii; clarify; rewrite Pos.eqb_neq in Eq0; clarify. inv PC.
  Qed.

  Lemma transf_function_step_make_predecessors :
    (Kildall.make_predecessors (fn_code f) successors_instr) =
    (Kildall.make_predecessors (fn_code f') successors_instr).
  Proof.
    eapply same_successors_same_predecessors. i. repeat rewrite PTree.gmap1.
    destruct (fn_code f) ! i eqn:EI.
    - pose proof transf_function_step_instr_spec; des; clarify.
      ss. exploit H; eauto; i; des. rewrite H0; ss. rewrite H5. destruct i0; ss.
    - pose proof transf_function_step_spec; des; clarify. rewrite EI; ss.
      unfold change_code; ss. unfold subst_capture_code; flatten.
      rewrite PTree.gmap. rewrite EI; ss.
  Qed.

  Lemma transf_function_step_join_point : forall pc,
    join_point pc f <-> join_point pc f'.
  Proof.
    split; i.
    - inv H. econs. rewrite <- transf_function_step_make_predecessors; eauto. ss.
    - inv H. econs. rewrite transf_function_step_make_predecessors; eauto. ss.
  Qed.

  Lemma transf_function_preserve_wf_ssa_function :
    wf_ssa_function f'.
  Proof.
    unfold transf_function_step in STEP.
    destruct (compute_dom f) eqn:DOMTREE; try inv STEP. flatten H0; try destruct f; ss.
    exploit subst_capture_code_preserve_wf_ssa_function; eauto. i.
    exploit compute_dom_correct; eauto.
  Qed.

End FUNCTION_STEP.

Section CORRECTNESS_STEP.

  Variables prog tprog: program.
  Variable ll tll: list (list node).
  Let ge := Genv.globalenv prog.
  Let tge := Genv.globalenv tprog.
  (* Let ev_rel2 := ev_rel tprog. *)
  Hypothesis WF: wf_ssa_program prog.
  Hypothesis STEP: match_prog_step prog tprog.

  Lemma transf_program_step_wf_ssa: wf_ssa_program tprog.
  Proof.
    red. intros.
    red in WF.
    (* inv STEP. monadInv H1. ss. remember (prog_defs prog) as defs. clear Heqdefs. *)
    (* generalize dependent ll. generalize dependent tll. clear ge tge. generalize dependent x. *)
    (* induction defs; i. *)
    (* - simpl in EQ. inv EQ. inv H. *)
    (* - destruct a. destruct g. *)
      (* + unfold transf_globdefs_step in EQ. fold transf_globdefs_step in EQ. flatten EQ. *)
        (* * inv H; eauto. clarify; eauto. *)
        (* * monadInv EQ. destruct f; eauto using wf_ssa_fundef. *)
          (* unfold transf_globdef_step in EQ0. monadInv EQ0. inv H. *)
          (* { inv H0. exploit WF; eauto. } *)
          (* { exploit IHdefs; eauto. } *)
      (* + destruct x. inv H. destruct p. destruct ll0; inv EQ. inv H. *)
        (* clarify. exploit WF; eauto. monadInv H1. inv H. clarify. eauto. *)
    (* Qed. *)
    inv STEP. intuition. revert H0 H WF.
    induction 1; intros.
    - inv H.
    - inv H1.
      + inv H. inv H4. des.
        destruct f1.
        * unfold transf_fundef_step in H7. monadInv H7. constructor.
          destruct a1, g. simpl in H. simpl in H1. clarify. exploit WF; eauto. i.
          inv H. eapply transf_function_preserve_wf_ssa_function; eauto. inv H.
        * monadInv H7. constructor.
      + eapply IHlist_forall2; eauto.
  Qed.

  Lemma function_ptr_translated: forall v f,
    Genv.find_funct_ptr ge v = Some f ->
    exists tf l l', transf_fundef_step (f, l) = OK (tf, l') /\
      Genv.find_funct_ptr tge v = Some tf.
  Proof.
    i. eapply @Genv.find_funct_ptr_match in H; eauto. des. eexists; eexists; eauto.
  Qed.

  Lemma symbols_preserved:
    forall id,
    Genv.find_symbol tge id = Genv.find_symbol ge id.
  Proof (Genv.find_symbol_match STEP).

  Lemma sig_preserved : forall f tf l l',
    transf_fundef_step (f, l) = OK (tf, l') -> funsig f = funsig tf.
  Proof.
    i. destruct f; destruct tf; ss; monadInv H.
    - flatten EQ; eauto.
    - destruct e0; eauto.
  Qed.

  Lemma stacksize_preserved : forall f tf l l',
    transf_function_step (f, l) = OK (tf, l') -> fn_stacksize f = fn_stacksize tf.
  Proof.
    i. destruct f; destruct tf; ss; flatten H.
  Qed.

  Lemma find_function_translated:
    forall ros rs rs' f m m' (MEMCHAR: mem_char prog m),
      concrete_extends m m' -> (forall arg, val_intptr m' (rs # arg) (rs' # arg)) ->
      find_function ge (ros_to_vos m ros rs) rs = Some f ->
    exists tf l l', transf_fundef_step (f, l) = OK (tf, l') /\
      find_function tge (ros_to_vos m' ros rs') rs = Some tf.
  Proof.
    unfold find_function. i. destruct ros; simpl ros_to_vos in H1.
    - specialize (H0 r). flatten H1; try (inv H1; fail).
      + eapply @Genv.find_funct_match in H1; eauto; des.
        inv H0; clarify.
      + eapply @Genv.find_funct_match in H1; eauto; des. simpl ros_to_vos.
        inv H0; clarify. exploit denormalize_concrete_extends; eauto; i.
        rewrite H0; eauto.
      + exploit MEMCHAR; eauto.
        { ss. des_ifs. eauto. }
        intros (NE & NE').
        eapply @Genv.find_funct_match in H1; eauto; des. simpl ros_to_vos.
        inv H0.
        * ss; clarify; eauto.
        * ss; clarify; eauto.
        (* * flatten; eauto. exfalso; eapply n. rewrite <- concrete_extends_same_perm; eauto. *)
        * flatten; eauto; flatten Eq.
          { unfold Genv.find_funct in H1. flatten H1. clarify.
            exploit Int64.eq_spec; i. rewrite Eq3 in H0. clarify. clear Eq3.
            (* rewrite Ptrofs.unsigned_zero in p. *)
            simpl in H8. unfold Mem.ptr2int_v in H8. rewrite Ptrofs.unsigned_zero in H8.
            destruct (Mem.ptr2int b 0 m') eqn:BINT; cycle 1; try by clarify.
            rewrite Eq1 in H8.
            exploit Mem.ptr2int_not_nullptr64_max; eauto.
            { unfold Mem._weak_valid_pointer. eapply concrete_extends_perm_implies in NE; eauto. }
            - split. lia. unfold Ptrofs.max_unsigned, Ptrofs.modulus.
              unfold Ptrofs.wordsize, Wordsize_Ptrofs.wordsize; flatten; ss.
            - i. exploit Int64.eq_spec; i. rewrite H0 in H4.
              inv H8. flatten H9; clarify. exploit proof_irr. i.
              rewrite H5 in H4. exfalso; eapply H4; eauto. }
          { simpl in H8. unfold Mem.ptr2int_v in H8. flatten H8.
            eapply Mem.ptr2int_to_denormalize_max in Eq; eauto; cycle 1.
            { exploit Ptrofs.unsigned_range_2; eauto. }
            { ss. des_ifs_safe. rewrite Ptrofs.unsigned_zero.
              eapply concrete_extends_perm_implies; eauto. }
            eapply Mem.denormalize_info in Eq as INFO; des. rewrite Int64.unsigned_repr in Eq4.
            2:{ unfold Int64.max_unsigned, Ptrofs.max_unsigned in *.
                erewrite <- Ptrofs.modulus_eq64; eauto. lia. }
            rewrite Eq4 in Eq; clarify. rewrite Ptrofs.repr_unsigned; eauto. }
          unfold Genv.find_funct in H1; flatten H1; clarify.
          simpl in H8. unfold Mem.ptr2int_v in H8. flatten H8. rewrite Ptrofs.unsigned_zero in Eq.
          eapply Mem.ptr2int_to_denormalize_max in Eq as DENOM; eauto.
          2:{ rewrite <- Ptrofs.unsigned_zero at 2 3. eapply Ptrofs.unsigned_range_2. }
          2:{ eapply concrete_extends_perm_implies; eauto. }
          des_safe. rewrite Int64.unsigned_repr in Eq4; clarify.
          eapply Mem.denormalize_info in DENOM. des.
          unfold Ptrofs.max_unsigned, Int64.max_unsigned in *.
          erewrite <- Ptrofs.modulus_eq64; eauto. lia.
    - flatten H1. eapply function_ptr_translated in H1; eauto; des.
      esplits; eauto. simpl. rewrite symbols_preserved. rewrite Eq0. eauto.
  Qed.

  Lemma senv_preserved:
    Senv.equiv ge tge.
  Proof (Genv.senv_match STEP).

  Lemma val_intptr_same_concrete m m' v v'
    (SME: (Mem.mem_concrete m) = (Mem.mem_concrete m')):
    val_intptr m v v' <-> val_intptr m' v v'.
  Proof.
    split; i.
    { inv H; eauto using val_intptr; unfold Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in *.
      - econs; eauto. rewrite SME in H1. eauto.
      - econs; eauto. rewrite SME in H1. eauto. }
    inv H; eauto using val_intptr; unfold Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in *.
    - econs; eauto. rewrite <- SME in H1. eauto.
    - econs; eauto. rewrite <- SME in H1. eauto.
  Qed.
  
  Lemma val_intptr_extended_concrete m m' v v'
    (EXT: forall b addr, (Mem.mem_concrete m) !b = Some addr -> (Mem.mem_concrete m') ! b = Some addr):
    val_intptr m v v' -> val_intptr m' v v'.
  Proof.
    i. inv H; eauto using val_intptr; unfold Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in H1.
    - econs; eauto. destruct ((Mem.mem_concrete m) ! b) eqn: CONC.
      2:{ inv H1. }
      rewrite H0 in H1. inv H1. simpl. unfold Mem.ptr2int. eapply EXT in CONC.
      rewrite CONC, H0. eauto.
    - econs; eauto. destruct ((Mem.mem_concrete m) ! b) eqn: CONC.
      2:{ inv H1. }
      rewrite H0 in H1. inv H1. simpl. unfold Mem.ptr2int. eapply EXT in CONC.
      rewrite CONC, H0. eauto.
  Qed.

  Lemma concrete_extends_val_intptr : forall m m',
    concrete_extends m m' -> (forall v v', val_intptr m v v' -> val_intptr m' v v').
  Proof.
    i; inv H; exploit val_intptr_extended_concrete; eauto.
  Qed.
    
  Inductive match_registers : regset -> regset -> mem -> Prop :=
  | mr_reg: forall rs rs' m
      (ARG : forall arg, val_intptr m (rs # arg) (rs' # arg)),
    match_registers rs rs' m.

  (* Inductive match_functions : function -> regset -> function -> regset -> mem -> node -> Prop :=
  | mf_same f rs rs' m pc : match_functions f rs f rs' m pc
  | mf_subst f f' l l' domtree root d s rs rs' pc' m pc
    (DOMTREE : compute_dom f = Some domtree)
    (STEP : transf_function_step (f, l) = OK (f', l'))
    (* (ROOTCPT : find_capture_root domtree hd tl = root) *)
    (* (FILTER : l' = filter (fun x => negb (Pos.eqb root x)) l) *)
    (SUBST : f' = change_code f (subst_capture_code domtree d s root (fn_code f)))
    (CAPT : (fn_code f) ! root = Some (Ibuiltin EF_capture (BA s :: nil) (BR d) pc'))
    (INSTR : forall i, (fn_code f) ! pc = Some i ->
              (fn_code f') ! pc = Some i
              \/ (fn_code f') ! pc = Some (subst_instr d s i) /\ pc <> root /\ dom f root pc)
    (DSEQUIV : in_set root (domtree !! pc) -> pc <> root ->
               val_intptr m (rs # d) (rs # s) /\ val_intptr m (rs' # d) (rs' # s)) :
    match_functions f rs f' rs' m pc. *)
  (* Lemma transf_function_step_inv : forall f1 l1 f2 l2 domtree d s,
    compute_dom f1 = Some domtree ->
    transf_function_step (f1, l1) = OK (f2, l2) ->
  Inductive capture_in : node -> list node -> Prop :=
  | capin root l :  *)

  Inductive match_stackframes :
    list stackframe -> list stackframe -> mem -> node -> reg -> reg -> Prop :=
  | match_stackframes_nil: forall m' root d s, match_stackframes nil nil m' root d s
  | match_stackframes_same : forall f domtree st st' rs rs' m' res sp pc root d s root' d' s'
      (WFF : wf_ssa_function f)
      (DOMTREE : compute_dom f = Some domtree)
      (STACK : match_stackframes st st' m' root' d' s')
      (REGS : match_registers rs rs' m'),
      match_stackframes
        ((Stackframe res f sp pc rs) :: st) ((Stackframe res f sp pc rs') :: st') m' root d s
  | match_stackframes_cons:
    forall f f' l l' st st' m' res sp pc rs rs'
      pred sig fn args root root' d s domtree root'' d' s'
      (WFF : wf_ssa_function f)
      (STEP : transf_function_step (f, l) = OK (f', l'))
      (DOMTREE : compute_dom f = Some domtree)
      (ROOT : root_capture root l domtree)
      (* (FILTER : l' = filter (fun x => negb (Pos.eqb root x)) l) *)
      (* (ROOT : l = hd :: tl /\ root = find_capture_root domtree hd tl) *)
      (CAPT : (fn_code f) ! root = Some (Ibuiltin EF_capture (BA s :: nil) (BR d) root'))
      (DSEQUIV :
          sdom f root pc ->
        val_intptr m' (rs # s) (rs # d) /\ val_intptr m' (rs' # s) (rs' # d))
      (STACK: match_stackframes st st' m' root'' d' s')
      (MATCHREGS : match_registers rs rs' m')
      (PREDINFO : (fn_code f) ! pred = Some (Icall sig fn args res pc)),
      match_stackframes
        ((Stackframe res f sp pc rs) :: st)
        ((Stackframe res f' sp pc rs') :: st') m' root d s.

  Variant match_states: SSA.state -> SSA.state -> Prop :=
  | match_states_same :
    forall f st st' sp pc rs rs' m m' domtree root d s
      (WF : wf_ssa_function f)
      (DOMTREE : compute_dom f = Some domtree)
      (STACK : match_stackframes st st' m' root d s)
      (REGS : forall arg, val_intptr m' (rs # arg) (rs' # arg))
      (EXTENDS : concrete_extends m m'),
    match_states (State st f sp pc rs m) (State st' f sp pc rs' m')
  | match_states_rename :  
    forall f f' st st' sp pc rs rs' m m' domtree l l' (root : node) s d root'
      root'' d'' s''
      (WF : wf_ssa_function f)
      (STACK : match_stackframes st st' m' root'' d'' s'')
      (REGS : forall arg, val_intptr m' (rs # arg) (rs' # arg))
      (DOMTREE : compute_dom f = Some domtree)
      (STEP : OK (f', l') = transf_function_step (f, l))
      (ROOT : root_capture root l domtree)
      (FINFO : f' = change_code f (subst_capture_code domtree d s root (fn_code f)))
      (CAPT : (fn_code f) ! root = Some (Ibuiltin EF_capture (BA s :: nil) (BR d) root'))
      (DSEQUIV : sdom f root pc ->
                val_intptr m' (rs # s) (rs # d) /\ val_intptr m' (rs' # s) (rs' # d))
      (EXTENDS : concrete_extends m m'),
      match_states (State st f sp pc rs m) (State st' f' sp pc rs' m')
  | match_state_call:
    forall f f' l l' st st' args args' m m' root d s
      (WF: wf_ssa_fundef f)
      (STACK: match_stackframes st st' m' root d s)
      (STEP: OK (f', l') = transf_fundef_step (f, l))
      (EXTENDS: concrete_extends m m')
      (BIND: val_intptrist m' args args'),
    match_states (Callstate st f args m)
                (Callstate st' f' args' m')
  | match_states_return:
    forall st st' m m' v v' root d s
      (STACK : match_stackframes st st' m' root d s)
      (EXTENDS : concrete_extends m m')
      (BIND : val_intptr m' v v'),
    match_states (Returnstate st v m) (Returnstate st' v' m').

  Lemma transf_initial_states:
    forall S1, initial_state prog S1 ->
    exists S2, initial_state tprog S2 /\ match_states S1 S2.
  Proof.
    intros. inv H.
    eapply function_ptr_translated in H2 as TF; des. 
    econstructor; split.
    econstructor.
    - eapply (Genv.init_mem_match STEP); eauto.
    - rewrite symbols_preserved. rewrite (match_program_main STEP). eauto.
    - subst tge. eauto.
    - exploit sig_preserved; eauto; i; clarify. rewrite <- H; ss.
    - econs; eauto. destruct f; eauto. red in WF.
      eapply Genv.find_funct_ptr_inversion in H2; des; eauto. econs.
      econs; eauto. eapply concrete_ext_refl; eauto. econs; eauto.
    Unshelve. eauto. all: eapply 1%positive.
  Qed.

  Require Import Simulation.

  (* TODO: Prove these lemmas *)
  Lemma val_intptr_phi_store : forall m rs rs' k phib arg,
    (forall arg, val_intptr m (rs # arg) (rs' # arg)) ->
    val_intptr m (phi_store k phib rs) # arg (phi_store k phib rs') # arg.
  Proof.
    intros m rs rs' k phib; revert m rs rs' k; induction phib; eauto. i. ss. flatten; eauto. 
    destruct (peq arg r).
    - clarify. repeat rewrite PMap.gss. eauto.
    - repeat rewrite PMap.gso; eauto.
  Qed.

  Lemma phi_store_irrelevant : forall f pc phib r rs k,
    wf_ssa_function f ->
    (fn_phicode f) ! pc = Some phib ->
    ~ assigned_phi_spec (fn_phicode f) pc r ->
    (phi_store k phib rs) # r = rs # r.
  Proof.
    ii. assert (forall args, ~ In (Iphi args r) phib). { ii. eapply H1. econs; eauto. }
    revert H2. generalize phib as b. induction b; ss. i.
    flatten. rewrite PMap.gso; eauto. ii; clarify. eapply H2; eauto.
    eapply IHb; eauto.
  Qed.

  Lemma val_intptr_match_stackframes : forall m m' st st' root d s,
    match_stackframes st st' m root d s ->
    (forall v v', val_intptr m v v' -> val_intptr m' v v') ->
    match_stackframes st st' m' root d s.
  Proof.
    i. induction st.
    - inv H. econs.
    - inv H.
      + econs 2; eauto. inv REGS; econs; i; eauto.
      + econs; eauto. i; des.
        exploit DSEQUIV; i; des; eauto.
        econs; eauto. i. inv MATCHREGS. eauto.
  Qed.

  (* TODO: Consult about these lemmas *)
  Lemma val_intptr_trans : forall m v1 v2 v3,
    val_intptr m v1 v2 -> val_intptr m v2 v3 -> val_intptr m v1 v3.
  Proof.
    i. inv H; inv H0; try econs; eauto.
  Qed.

  Lemma val_intptrist_trans : forall m l1 l2 l3,
    val_intptrist m l1 l2 -> val_intptrist m l2 l3 -> val_intptrist m l1 l3.
  Proof.
    i. induction l1.
    - inv H. inv H0. econs.
    - inv H. inv H0. econs. eapply val_intptr_trans; eauto. eauto.
  Qed.

  Lemma eval_operation_wrapper_binded
    m m' vl vl' sp op v (genv : Genv.t fundef unit)
    (CONCEXT: concrete_extends m m')
    (BIND: val_intptrist m' vl vl')
    (EVAL: PointerOp.eval_operation_wrapper genv sp op vl m = Some v)
    :
    exists v',
      <<EVAL2: PointerOp.eval_operation_wrapper genv sp op vl' m' = Some v'>>
    /\ <<VIND': val_intptr m' v v'>>.
  Proof. exploit IntPtrRef.eval_operation_wrapper_binded; eauto. Qed.

  Lemma eval_condition_wrapper_binded
    m m' vl vl' cond b
    (CONCEXT: concrete_extends m m')
    (BIND: val_intptrist m' vl vl')
    (COND: PointerOp.eval_condition_wrapper cond vl m = Some b):
    PointerOp.eval_condition_wrapper cond vl' m' = Some b.
  Proof.
    unfold PointerOp.eval_condition_wrapper in *. des_ifs.
    - eapply eval_condition_join_binded; eauto.
    - eapply eval_condition_binded_no_ptr_binary; eauto.
  Qed.

  Lemma eval_addressing_binded
    addr sp vl1 vl2 m1 v1 (genv : Genv.t fundef unit)
    (* (CONCEXT: concrete_extends m1 m2) *)
    (BIND: val_intptrist m1 vl1 vl2)
    (EVAL: eval_addressing genv sp addr vl1 = Some v1)
    :
    exists v2, <<EVAL: eval_addressing genv sp addr vl2 = Some v2>>
        /\ <<BIND: val_intptr m1 v1 v2>>.
  Proof. eapply IntPtrRef.eval_addressing_binded; eauto. Qed.
  
  (* move to IntPtrRel.v *)
  Lemma loadv_concrete_extends :
    forall chunk m1 m2 addr1 addr2 v1,
    concrete_extends m1 m2 ->
    Mem.loadv chunk m1 addr1 = Some v1 ->
    val_intptr m2 addr1 addr2 ->
    exists v2, Mem.loadv chunk m2 addr2 = Some v2 /\ val_intptr m2 v1 v2.
  Proof.
    i. Local Transparent Mem.loadv. unfold Mem.loadv in H0. destruct addr1; ss; des_ifs.
    - inv H1. exploit denormalize_concrete_extends; eauto. i. des.
      unfold Mem.loadv. ss. des_ifs. eapply load_concrete_extends; eauto.
    - inv H1; ss.
      + ss. eapply load_concrete_extends; eauto.
      + unfold Mem.loadv. ss. des_ifs_safe. exploit Mem.load_valid_access; eauto. i. inv H1.
        r in H2. specialize (H2 (Ptrofs.unsigned i)). exploit H2.
        { destruct chunk; ss; lia. }
        i. eapply Mem.perm_implies in H1. 2:{ eapply perm_any_N. }
        rewrite <- Mem.valid_pointer_nonempty_perm in H1.
        exploit Mem.ptr2int_to_denormalize; eauto.
        { eapply Ptrofs.unsigned_range_2. }
        { rewrite Mem.valid_pointer_nonempty_perm in *. eapply concrete_extends_perm_implies; eauto. }
        i. exploit Mem.denormalize_info; eauto. i. des. rewrite Int64.unsigned_repr; cycle 1.
        { unfold Ptrofs.max_unsigned, Int64.max_unsigned in *. rewrite <- Ptrofs.modulus_eq64; eauto. lia. }
        rewrite H5. des_ifs.
        { exfalso. unfold Int64.eq in Heq1. des_ifs. unfold Ptrofs.max_unsigned in CRANGE0.
          rewrite Ptrofs.modulus_eq64 in CRANGE0; eauto. rewrite Int64.unsigned_repr in e; cycle 1.
          { unfold Int64.max_unsigned. lia. }
          rewrite Int64.unsigned_zero in e. subst. lia. }
        eapply load_concrete_extends; eauto.
        erewrite Ptrofs.unsigned_repr; eauto.
  Qed.

  (* move to IntPtrRel.v *)
  Theorem storev_concrete_extends:
    forall chunk m1 m2 addr1 v1 m1' addr2 v2, concrete_extends m1 m2 ->
    Mem.storev chunk m1 addr1 v1 = Some m1' ->
    val_intptr m2 addr1 addr2 ->
    val_intptr m2 v1 v2 ->
    exists m2',
      Mem.storev chunk m2 addr2 v2 = Some m2'
      /\ concrete_extends m1' m2'.
  Proof.
    i. Local Transparent Mem.storev. unfold Mem.storev in H0. des_ifs.
    - inv H1. exploit denormalize_concrete_extends; eauto. i. des.
      unfold Mem.storev. des_ifs. eapply store_concrete_extends; eauto.
    - inv H1; ss.
      + ss. eapply store_concrete_extends; eauto.
      + des_ifs_safe. exploit Mem.store_valid_access_3; eauto. i. inv H1.
        r in H3. specialize (H3 (Ptrofs.unsigned i)). exploit H3.
        { destruct chunk; ss; lia. }
        i. eapply Mem.perm_implies in H1. 2:{ eapply perm_any_N. }
        rewrite <- Mem.valid_pointer_nonempty_perm in H1.
        exploit Mem.ptr2int_to_denormalize; eauto.
        { eapply Ptrofs.unsigned_range_2. }
        { rewrite Mem.valid_pointer_nonempty_perm in *. eapply concrete_extends_perm_implies; eauto. }
        i. exploit Mem.denormalize_info; eauto. i. des. rewrite Int64.unsigned_repr; cycle 1.
        { unfold Ptrofs.max_unsigned, Int64.max_unsigned in *. rewrite <- Ptrofs.modulus_eq64; eauto. lia. }
        rewrite H6. eapply store_concrete_extends; eauto.
  Qed.

  Lemma free_concrete_extends:
    forall m1 m2 b lo hi m1', concrete_extends m1 m2 -> Mem.free m1 b lo hi = Some m1' ->
    exists m2',
      Mem.free m2 b lo hi = Some m2'
      /\ concrete_extends m1' m2'.
  Proof. i. eapply IntPtrRel.free_concrete_extends; eauto. Qed.

  Lemma alloc_concrete_extends:
    forall m1 m2 b lo hi m1', concrete_extends m1 m2 -> Mem.alloc m1 lo hi = (m1', b) ->
    exists m2',
      Mem.alloc m2 lo hi = (m2', b)
      /\ concrete_extends m1' m2'.
  Proof. i. eapply IntPtrRel.alloc_concrete_extends; eauto. Qed.
  
  Lemma free_val_intptr: forall m1 m2 b lo hi v1 v2,
    Mem.free m1 b lo hi = Some m2 -> val_intptr m1 v1 v2 -> val_intptr m2 v1 v2.
  Proof. i. eapply IntPtrRel.free_val_intptr; eauto. Qed.
  
  Lemma storev_val_intptr : forall m1 m2 chunk addr v v1 v2,
    Mem.storev chunk m1 addr v = Some m2 -> val_intptr m1 v1 v2 <-> val_intptr m2 v1 v2.
  Proof.
    i. exploit Mem.storev_concrete; eauto. i. exploit val_intptr_same_concrete; eauto.
  Qed.

  Lemma alloc_val_intptr :
    forall m1 m2 b lo hi v1 v2, Mem.alloc m1 lo hi = (m2, b) ->
      val_intptr m1 v1 v2 -> val_intptr m2 v1 v2.
  Proof. i. eapply IntPtrRel.alloc_val_intptr; eauto. Qed.

  (* Lemma find_function_binded : forall m rs rs' genv ros, *)
  (*   (forall arg, val_intptr m (rs # arg) (rs' # arg)) -> *)
  (*   find_function genv ros rs = find_function genv ros rs'. *)

  Lemma eval_builtin_arg_val_intptr :
    forall (a :(builtin_arg reg)) v1 (ge : Genv.t fundef unit) e1 e2 sp m1 m2,
      (forall a, val_intptr m2 (e1 a) (e2 a)) -> concrete_extends m1 m2 ->
      eval_builtin_arg ge e1 sp m1 a v1 ->
    exists v2, eval_builtin_arg ge e2 sp m2 a v2 /\ val_intptr m2 v1 v2.
  Proof.
    i. ginduction H1; ii; try by (esplits; eauto; econs).
    - exploit loadv_concrete_extends; eauto.
      { eapply val_intptr_refl. }
      i. des. esplits; eauto. econs; eauto.
    - esplits; eauto; [econs|]. eapply val_intptr_refl.
    - exploit loadv_concrete_extends; eauto.
      { eapply val_intptr_refl. }
      i. des. esplits; eauto. econs; eauto.
    - esplits; eauto; [econs|]. eapply val_intptr_refl.
    - exploit IHeval_builtin_arg1; try eapply H1_; eauto. i. des.
      exploit IHeval_builtin_arg2; try eapply H1_0; eauto. i. des.
      esplits; eauto. econs; eauto. unfold Val.longofwords. des_ifs_safe.
      destruct vhi; try by econs. destruct vlo; try by econs.
      inv H2; inv H4. eapply val_intptr_refl.
    - des_ifs_safe.
      exploit IHeval_builtin_arg1; try eapply H1_; eauto. i. des.
      exploit IHeval_builtin_arg2; try eapply H1_0; eauto. i. des.
      esplits; eauto; [econs; eauto|]. des_ifs_safe. eapply addl_bind; eauto.
  Qed.

  Lemma eval_builtin_args_val_intptr :
    forall (al : list (builtin_arg reg)) vl1 (ge : Genv.t fundef unit) e1 e2 sp m1 m2,
      (forall a, val_intptr m2 (e1 a) (e2 a)) -> concrete_extends m1 m2 ->
      eval_builtin_args ge e1 sp m1 al vl1 ->
    exists vl2, eval_builtin_args ge e2 sp m2 al vl2 /\ val_intptrist m2 vl1 vl2.
  Proof.
    i. ginduction H1; ss; ii.
    - esplits; eauto; econs.
    - exploit IHlist_forall2; try eapply H2; eauto. i. des.
      exploit eval_builtin_arg_val_intptr; eauto. i. des.
      esplits; eauto.
      + econs; eauto.
      + econs; eauto.
  Qed.

  Lemma external_call_concrete_extends :
    forall ef ge vargs m1 t vres m2 m1' vargs' (INT: ~ is_external_ef ef) gmtgt (TINIT: ge_binded ge m1' gmtgt),
    external_call ef ge vargs m1 t vres m2 ->
    concrete_extends m1 m1' ->
    val_intptrist m1' vargs vargs' ->
    exists vres', exists t', exists m2',
      tr_rel (ev_rel gmtgt) t t'
    /\ external_call ef ge vargs' m1' t' vres' m2'
    /\ val_intptr m2' vres vres'
    /\ concrete_extends m2 m2'.
  Proof.
    i. exploit external_call_spec; eauto. i.
    exploit (ec_mem_concrete_extends); eauto. i. des. esplits; eauto.
  Qed.

  Lemma external_call_concrete_extends_backward :
    forall ef ge vargs m1 t' vres' m2' m1' vargs' (EXT: is_external_ef ef) gmtgt (TINIT: ge_binded ge m1' gmtgt),
    external_call ef ge vargs' m1' t' vres' m2' -> concrete_extends m1 m1' ->
    val_intptrist m1' vargs vargs' ->
    (exists t vres m2,
      <<TRREL: tr_rel (ev_rel gmtgt) t t'>>
    /\ <<CALLSRC: external_call ef ge vargs m1 t vres m2>>
    /\ <<RETV: val_intptr m2' vres vres'>>
    /\ <<MEM: concrete_extends m2 m2'>>
    /\ <<PRIV: Mem.unchanged_on (loc_out_of_bounds m1) m1' m2'>>)
    \/ <<UBSRC: (forall t vres m2, ~ external_call ef ge vargs m1 t vres m2)>>
    \/ (<<PTERM: ~trace_intact t'>> /\
       exists t vres1 m21,
         <<CALLSRC: external_call ef ge vargs m1 t vres1 m21>> /\
         <<SUB: exists tl, tr_rel (ev_rel gmtgt) t (Eapp (trace_cut_pterm t') tl)>>).
  Proof.
    i. eapply external_call_spec_backward in EXT. exploit ec_concrete_extends_backward; eauto.
  Qed.

  Lemma external_call_binds :
    forall ef ge vargs m1 t vres m2,
    external_call ef ge vargs m1 t vres m2 ->
    (forall b caddr, m1.(Mem.mem_concrete) ! b = Some caddr -> m2.(Mem.mem_concrete) ! b = Some caddr).
  Proof. i. eapply ec_binds; eauto. eapply external_call_common_spec. Qed.

  Lemma external_call_binds' :
    forall ef ge vargs m1 t vres m2,
    external_call ef ge vargs m1 t vres m2 ->
    forall v1 v2, val_intptr m1 v1 v2 -> val_intptr m2 v1 v2.
  Proof.
    i. inv H0; econs; eauto; unfold Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in *; flatten H2; 
    exploit external_call_binds; eauto; i; rewrite H0; eauto.
  Qed.

  Lemma eval_builtin_arg_rename_barg' : forall ge rs sp m a v d s,
    val_intptr m (rs # s) (rs # d) ->
    eval_builtin_arg ge (fun r => rs # r) sp m a v ->
    exists v',
      eval_builtin_arg ge (fun r => rs # r) sp m (rename_barg d s a) v' /\
      val_intptr m v v'.
  Proof.
    induction a; ss; i; try (inv H0; eexists; split; try econs; eauto using val_intptr_refl; fail).
    - destruct (peq x s).
      + clarify. unfold rename_reg. rewrite Pos.eqb_refl.
        inv H0. eexists; split; eauto. econs.
      + unfold rename_reg. rewrite <- Pos.eqb_neq in n. rewrite n.
        eexists; split; eauto; try econs. eapply val_intptr_refl.
    - inv H0. exploit IHa1; eauto; i; des. exploit IHa2; eauto; i; des.
      eexists. split. econs; eauto. unfold Val.longofwords.
      inv H1; inv H4; eauto using val_intptr_refl; try econs.
    - inv H0. exploit IHa1; eauto; i; des. exploit IHa2; eauto; i; des.
      eexists. split. econs; eauto. flatten; [ eapply addl_bind | eapply add_bind ]; eauto.
      all : eapply concrete_ext_refl.
  Qed.
  
  Lemma init_regs_val_intptr : forall m args args' vl arg,
    val_intptrist m args args' ->
    val_intptr m (init_regs args vl) # arg (init_regs args' vl) # arg.
  Proof.
    intros m args args' vl; revert m args args'; induction vl; ss; i.
    - repeat rewrite PMap.gi; econs.
    - flatten.
      + repeat rewrite PMap.gi; econs.
      + inv H.
      + inv H.
      + destruct (peq a arg); clarify.
        { repeat rewrite PMap.gss. inv H; eauto. }
        { repeat rewrite PMap.gso; eauto. eapply IHvl; inv H; eauto. }
  Qed.

  Lemma senv_preserved_ge_bind
      g tg m gm
      (IBIND : ge_binded tg m gm)
      (SEQ : Senv.equiv g tg):
    ge_binded g m gm.
  Proof.
    unfold ge_binded in *. i. destruct SEQ. des.
    rewrite <- H1 in H0. rewrite <- H2 in H. eapply IBIND; eauto.
  Qed.

  Section STEPSIM.

  Variables st_init_tgt st_init_tgt1: (SSA.semantics tprog).(state).
  Hypothesis INIT1: (SSA.semantics tprog).(initial_state) st_init_tgt.
  Hypothesis ICAP1: (SSA.semantics tprog).(initial_capture) st_init_tgt st_init_tgt1.
  Definition gmtgt : ident -> option Z := (SSA.semantics tprog).(initial_pimap) st_init_tgt1.
  
  Lemma step_simulation:
    forall S1 t S2 (STC: state_char prog S1), IStep (SSA.semantics prog) S1 t S2 ->
    forall S1' (IBIND: ge_binded_state tge S1' gmtgt), match_states S1 S1' ->
    exists t' S2', tr_rel (ev_rel gmtgt) t t' /\ DStep (SSA.semantics tprog) S1' t' S2' /\ match_states S2 S2'.
  Proof.
    assert (VALIST : forall rs rs' m, (forall arg, val_intptr m rs # arg rs' # arg) ->
            forall args, val_intptrist m (rs ## args) (rs' ## args)).
    { i. induction args; eauto. econs. econs; eauto. }
    assert (RENAME : forall d s, rename_reg d s s = d).
    { i. unfold rename_reg. flatten; eauto. rewrite Pos.eqb_neq in Eq; clarify. }
    assert (RENAMEN : forall r r' r'', r <> r' -> rename_reg r'' r' r = r).
    { i. unfold rename_reg. flatten; eauto. rewrite Pos.eqb_eq in Eq; clarify. }
    assert (VALIST' : forall m rs d s args, val_intptr m (rs # s) (rs # d) ->
            val_intptrist m rs ## args rs ## (map (rename_reg d s) args)).
    { i. induction args; ss; i. econs. econs; eauto. destruct (peq a s).
      clarify. rewrite RENAME; eauto. rewrite RENAMEN; eauto. eapply val_intptr_refl. }
    destruct 2. generalize dependent S2. rename H into INT. unfold is_internal in INT.
    induction 1; intros S1' IBIND MS.
    - (* Inop njp *)
      inv MS.
      + eexists. eexists. splits;[econs | |]. DStep_tac2. econs; eauto. econs; eauto.
      + eexists. eexists; splits;[econs | |]. eapply (transf_function_step_instr_spec _ _ _ _ _ STEP0) in H as H'. des.
        * DStep_tac2. econs; eauto. ii. eapply transf_function_step_join_point in H1; eauto.
        * DStep_tac2. econs; eauto. ii. eapply transf_function_step_join_point in H1; eauto.
        * econs; eauto. i; des; eauto. eapply DSEQUIV. econs.
          eapply (@Dom.sdom_dom_pred node peq). eapply H1. eauto. econs; eauto. ii; clarify.
    - (* Inop jp *)
      inv MS.
      + eexists. eexists; splits;[econs | |]. DStep_tac2. econstructor 2; eauto. econs; eauto.
        i; eapply val_intptr_phi_store; eauto.
      + eexists. eexists; splits;[econs | |]. eapply (transf_function_step_instr_spec _ _ _ _ _ STEP0) in H as H'. des.
        * DStep_tac2. econstructor 2; eauto.
          rewrite <- transf_function_step_join_point; eauto.
          exploit transf_function_step_make_predecessors; eauto. i. rewrite <- H3. eauto.
        * DStep_tac2. econstructor 2; eauto.
          rewrite <- transf_function_step_join_point; eauto.
          exploit transf_function_step_make_predecessors; eauto. i. rewrite <- H3. eauto.
        * econs; eauto. i. exploit val_intptr_phi_store; eauto.
          i. exploit DSEQUIV; i. econs. eapply (@Dom.sdom_dom_pred node peq); eauto.
          econs; eauto. ii; clarify. des. split.
          { repeat erewrite phi_store_irrelevant; eauto.
            ii. exploit unique_def_elim1; eauto. inv WF0; eauto. ii.
            eapply (@Dom.sdom_not_dom node peq); eauto. exploit fn_strict; eauto.
            econs. eapply UIbuiltin; eauto. ss; eauto. }
          { repeat erewrite phi_store_irrelevant; eauto.
            ii. exploit unique_def_elim1; eauto. inv WF0; eauto.
            ii. eapply (@Dom.sdom_not_dom node peq); eauto. exploit fn_strict; eauto.
            econs. eapply UIbuiltin; eauto. ss; eauto. }
    - (* Iop *)
      inv MS.
      + erewrite PointerOp.eval_operation_wrapper_preserved in H0.
        eapply eval_operation_wrapper_binded in H0 as EXISTS; eauto; des.
        eexists. eexists. splits;[econs | |]. DStep_tac2. econstructor 3; eauto.
        econs; eauto. i. destruct (peq arg res); clarify.
        { repeat rewrite PMap.gss; eauto. } { repeat rewrite PMap.gso; eauto. }
        i. exploit symbols_preserved; eauto.
      + erewrite PointerOp.eval_operation_wrapper_preserved in H0.
        eapply eval_operation_wrapper_binded in H0 as EXISTS; eauto; des.
        eapply subst_capture_code_spec' in H as H'; eauto. des.
        * eexists. eexists. splits;[econs | |]. DStep_tac2; try rewrite Heq in H'; inv H'.
          econstructor 3. eapply H2. eapply EVAL2.
          econs; eauto. i. destruct (peq arg res); clarify.
          { repeat rewrite PMap.gss; eauto. } { repeat rewrite PMap.gso; eauto. }
          i. exploit DSEQUIV; i. econs. eapply (@Dom.sdom_dom_pred node peq); eauto.
          econs; eauto. ii; clarify. des. split.
          { replace (rs # res <- v) # d with rs # d; eauto. destruct (peq res s0).
            - clarify. assert (sdom f root pc).
              { econs. eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto.
                ii; clarify. }
              assert (def f s0 pc). econs; eauto. exploit (@Dom.sdom_not_dom node peq).
              eapply H4. exploit fn_strict; eauto. econs. eapply UIbuiltin; eauto. ss. eauto.
              i; ss.
            - rewrite PMap.gso; eauto.
            - rewrite PMap.gso; eauto. ii; clarify. def_def f res root pc; i; clarify. }
          { rewrite (@PMap.gso _ d). destruct (peq res s0).
            - clarify. assert (sdom f root pc).
              { econs. eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto.
                ii; clarify. }
              assert (def f s0 pc). econs; eauto. exploit (@Dom.sdom_not_dom node peq).
              eapply H4. exploit fn_strict; eauto. econs. eapply UIbuiltin; eauto. ss. eauto.
              i; ss.
            - rewrite PMap.gso; eauto.
            - ii; clarify. def_def f res root pc; i; clarify. }
        * eapply eval_operation_wrapper_binded in EVAL2 as EXISTS'; eauto; des.
          ss. eexists. eexists. splits;[econs | |]. DStep_tac2. econstructor 3. eapply H'. ss. eapply EVAL0.
          econs; eauto. i. destruct (peq arg res); clarify.
          { repeat rewrite PMap.gss; eauto. eapply val_intptr_trans; eauto. }
          { repeat rewrite PMap.gso; eauto. }
          i. exploit DSEQUIV; i. econs. eapply (@Dom.sdom_dom_pred node peq); eauto.
          econs; eauto. ii; clarify. des; split.
          { rewrite (@PMap.gso _ d); eauto. destruct (peq res s0).
            - clarify. assert (sdom f root pc).
              { econs. eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto.
                ii; clarify. }
              assert (def f s0 pc). econs; eauto. exploit (@Dom.sdom_not_dom node peq).
              eapply H4. exploit fn_strict; eauto. econs. eapply UIbuiltin; eauto. ss. eauto.
              i; ss.
            - rewrite PMap.gso; eauto.
            - ii; clarify. def_def f res root pc; i; clarify. }
          { rewrite (@PMap.gso _ d); eauto. destruct (peq res s0).
            - clarify. assert (sdom f root pc).
              { econs. eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto.
                ii; clarify. }
              assert (def f s0 pc). econs; eauto. exploit (@Dom.sdom_not_dom node peq).
              eapply H4. exploit fn_strict; eauto. econs. eapply UIbuiltin; eauto. ss. eauto.
              i; ss.
            - rewrite PMap.gso; eauto.
            - ii; clarify. def_def f res root pc; i; clarify. }
          exploit concrete_ext_refl; eauto. destruct (classic (use_code f s0 pc)).
          { eapply VALIST'. eapply DSEQUIV; eauto. econs; eauto.
            eapply compute_dom_correct in H'0; eauto. }
          { assert (~ In s0 args). ii; eapply H1; econs; eauto. revert H2; generalize args.
            induction args0; ss; i. econs; eauto. econs; eauto. destruct (peq a s0).
            clarify. exfalso; eapply H2; eauto. rewrite RENAMEN; eauto. eapply val_intptr_refl. }
        * i; exploit symbols_preserved; eauto.
    - (* Iload *)
      inv MS.
      + eapply eval_addressing_binded in H0 as EVAL'; des; eauto.
        eapply loadv_concrete_extends in EXTENDS as LOAD; des; eauto.
        eexists. eexists. splits;[econs | |]. DStep_tac2. econstructor 4; eauto.
        erewrite eval_addressing_preserved. eapply EVAL. eapply symbols_preserved.
        econs; eauto. i. destruct (peq arg dst); clarify.
        { repeat rewrite PMap.gss; eauto. } { repeat rewrite PMap.gso; eauto. }
      + eapply subst_capture_code_spec' in H as INSTR'; des; eauto.
        * eapply eval_addressing_binded in H0 as EVAL'; des; eauto.
          eapply loadv_concrete_extends in EXTENDS as LOAD; des; eauto.
          eexists. eexists. splits;[econs | |]. DStep_tac2; try rewrite Heq in INSTR'; inv INSTR'.
          econstructor 4; eauto.
          erewrite eval_addressing_preserved. eapply EVAL. eapply symbols_preserved.
          econs; eauto. i. destruct (peq arg dst); clarify.
          { repeat rewrite PMap.gss; eauto. } { repeat rewrite PMap.gso; eauto. }
          i. exploit DSEQUIV; i. econs. eapply (@Dom.sdom_dom_pred node peq); eauto.
          econs; eauto. ii; clarify. des. split.
          { rewrite (@PMap.gso _ d). destruct (peq dst s0).
            - clarify. assert (sdom f root pc).
              { econs. eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto. ii; clarify. }
              assert (def f s0 pc). econs; eauto. exploit (@Dom.sdom_not_dom node peq).
              eapply H2. exploit fn_strict; eauto. econs. eapply UIbuiltin; eauto. ss. eauto.
              i; ss. inv H5. exploit (@Dom.dom_antisym node peq); eauto. i; clarify. ss.
            - rewrite PMap.gso; eauto.
            - ii; clarify. def_def f dst root pc; i; clarify. }
          { rewrite (@PMap.gso _ d). destruct (peq dst s0).
            - clarify. assert (sdom f root pc).
              { econs. eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto. ii; clarify. }
              assert (def f s0 pc). econs; eauto. exploit (@Dom.sdom_not_dom node peq).
              eapply H2. exploit fn_strict; eauto. econs. eapply UIbuiltin; eauto. ss. eauto.
              i; ss. inv H5. exploit (@Dom.dom_antisym node peq); eauto. i; clarify. ss.
            - rewrite PMap.gso; eauto.
            - ii; clarify. def_def f dst root pc; i; clarify. }
        * eapply eval_addressing_binded in H0 as EVAL'; des; eauto.
          eapply eval_addressing_binded in EVAL; des.
          eapply loadv_concrete_extends in EXTENDS as LOAD; des; eauto.
          eapply loadv_concrete_extends in LOAD; des; eauto.
          eexists. eexists. splits;[econs | |]. DStep_tac2; try rewrite Heq in INSTR'; inv INSTR'.
          econstructor 4. eapply H3. erewrite eval_addressing_preserved.
          eapply EVAL0. eapply symbols_preserved. eapply LOAD.
          econs; eauto. i. destruct (peq arg dst); clarify.
          { repeat rewrite PMap.gss; eauto. eapply val_intptr_trans; eauto. }
          { repeat rewrite PMap.gso; eauto. }
          i. exploit DSEQUIV; i. econs. eapply (@Dom.sdom_dom_pred node peq); eauto.
          econs; eauto. ii; clarify. des. split.
          { rewrite (@PMap.gso _ d). destruct (peq dst s0).
            - clarify. assert (sdom f root pc).
              { econs. eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto. ii; clarify. }
              assert (def f s0 pc). econs; eauto. exploit (@Dom.sdom_not_dom node peq).
              eapply H2. exploit fn_strict; eauto. econs. eapply UIbuiltin; eauto. ss. eauto.
              i; ss. inv H5. exploit (@Dom.dom_antisym node peq); eauto. i; clarify. ss.
            - rewrite PMap.gso; eauto.
            - ii; clarify. def_def f dst root pc; i; clarify. }
          { rewrite (@PMap.gso _ d). destruct (peq dst s0).
            - clarify. assert (sdom f root pc).
              { econs. eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto. ii; clarify. }
              assert (def f s0 pc). econs; eauto. exploit (@Dom.sdom_not_dom node peq).
              eapply H2. exploit fn_strict; eauto. econs. eapply UIbuiltin; eauto. ss. eauto.
              i; ss. inv H5. exploit (@Dom.dom_antisym node peq); eauto. i; clarify. ss.
            - rewrite PMap.gso; eauto.
            - ii; clarify. def_def f dst root pc; i; clarify. }
          eapply concrete_ext_refl.
          destruct (classic (use_code f s0 pc)).
          { eapply VALIST'. eapply DSEQUIV; eauto. econs; eauto.
            eapply compute_dom_correct; eauto. }
          { assert (~ In s0 args). ii. eapply H2. econstructor 2; eauto.
            revert H3; generalize args.
            induction args0; ss; i. econs; eauto. econs; eauto. destruct (peq a0 s0).
            clarify. exfalso; eapply H3; eauto. rewrite RENAMEN; eauto. eapply val_intptr_refl. }
    - (* Istore *)
      inv MS.
      + eapply eval_addressing_binded in H0 as EVAL'; des; eauto.
        eapply storev_concrete_extends in H1; des; eauto.
        eexists. eexists. splits;[econs | |]. DStep_tac2. econstructor 5; eauto.
        erewrite eval_addressing_preserved. eapply EVAL. eapply symbols_preserved.
        econs; eauto. eapply val_intptr_match_stackframes. eapply STACK. i.
        erewrite <- storev_val_intptr; eauto. i. erewrite <- storev_val_intptr; eauto. 
      + remember (change_code f (subst_capture_code domtree d s0 root (fn_code f))) as f'.
        eapply subst_capture_code_spec' in H as INSTR'; eauto; des.
        * eapply eval_addressing_binded in H0 as EVAL'; des; eauto.
          eapply storev_concrete_extends in H1; des; eauto.
          eexists. eexists. splits;[econs | |]. DStep_tac2; try rewrite Heq in INSTR'; inv INSTR'.
          econstructor 5; eauto.
          erewrite eval_addressing_preserved. eapply EVAL. eapply symbols_preserved.
          econs; eauto. eapply val_intptr_match_stackframes. eapply STACK.
          i. erewrite <- storev_val_intptr; eauto. i. erewrite <- storev_val_intptr; eauto. 
          clarify; eauto.
          i. exploit DSEQUIV; eauto. econs.
          eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto. ii; clarify. i; des. split;
          eapply val_intptr_same_concrete with m'0; eauto; exploit Mem.storev_concrete; eauto.
        * assert (exists a', eval_addressing (globalenv (SSA.semantics tprog)) sp
                  addr (rs' ## (map (rename_reg d s0) args)) = Some a' /\ val_intptr m'0 a a').
          { exploit eval_addressing_binded; eauto. i; des.
            rewrite (eval_addressing_preserved (globalenv (SSA.semantics tprog))) in EVAL.
            exploit eval_addressing_binded; i; des. 3:{ exists v0; eauto. }
            2:{ erewrite <- eval_addressing_preserved in H0. eapply H0. 
                i; exploit symbols_preserved; eauto. }
            eapply val_intptrist_trans. eapply VALIST; eauto.
            eapply VALIST'. exploit DSEQUIV; i; des; eauto. econs.
            eapply compute_dom_correct; eauto. ii; clarify. i; exploit symbols_preserved; eauto. }
          des. eapply storev_concrete_extends in H1; i; des.
          eexists. eexists. splits;[econs | |]. DStep_tac2. econstructor 5; eauto.
          econs; eauto. eapply val_intptr_match_stackframes. eapply STACK.
          i; erewrite <- storev_val_intptr; eauto. i; erewrite <- storev_val_intptr; eauto.
          i. exploit DSEQUIV; i. econs. eapply (@Dom.sdom_dom_pred node peq); eauto.
          econs; eauto. ii; clarify. des.
          split; erewrite <- storev_val_intptr; i; eauto. eauto. eauto.
          destruct (peq src s0). 
          { clarify. rewrite RENAME. exploit DSEQUIV. econs. eapply compute_dom_correct; eauto.
            ii; clarify. i; des; eauto. eapply val_intptr_trans; eauto. }
          { rewrite RENAMEN; eauto.  }
    - (* Icall *)
      inv MS.
      + eapply find_function_translated in H0 as FIND; des; cycle 1; eauto.
        erewrite sig_preserved in H; eauto.
        eexists. eexists. splits;[econs | |].
        { DStep_tac2. econstructor 6; eauto. }
        econs; eauto. eapply find_function_prop; eauto.
        exploit match_stackframes_same; i; eauto. econs; eauto.
      + remember (change_code f (subst_capture_code domtree d s0 root (fn_code f))) as f'.
        eapply subst_capture_code_spec' in H as INSTR'; eauto; des.
        * eapply find_function_translated in H0 as FIND; des; cycle 1; eauto.
          erewrite sig_preserved in INSTR'; simpl in INSTR'; eauto.
          eexists. eexists. splits;[econs | |].
          { DStep_tac2. econstructor 6; eauto. }
          econs; eauto. eapply find_function_prop; eauto.
          (* eapply transf_function_step_spec in STEP0 as HS. des; eauto.
          { clarify. rewrite <- HS. econs; eauto. econs; eauto. } *)
          econs; eauto.
          i; des. exploit DSEQUIV; i; eauto. econs.
          eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto. ii; clarify.
          econs; eauto.
        * eapply find_function_translated in H0 as FIND; des; cycle 1; eauto.
          erewrite sig_preserved in INSTR'; simpl in INSTR'; eauto.
          eexists. eexists. splits;[econs | |].
          { DStep_tac2. econstructor 6; eauto. }
          econs; eauto. eapply find_function_prop; eauto.
          (* eapply transf_function_step_spec in STEP0 as HS; eauto. des; eauto.
          { clarify. rewrite <- HS. econs; eauto. econs; eauto. } *)
          econs; eauto. i. exploit DSEQUIV; i; eauto. econs.
          eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto. ii; clarify.
          econs; eauto.
          eapply val_intptrist_trans. eapply VALIST. i; eauto. eapply VALIST'.
          exploit DSEQUIV; i; des; eauto. econs.
          eapply compute_dom_correct; eauto. ii; clarify.
    - (* Itailcall *)
      inv MS.
      + eapply find_function_translated in H0 as FIND; cycle 1; eauto. des.
        eapply free_concrete_extends in H2 as EXISTS; des; eauto.
        eexists. eexists. splits;[econs | |].
        { DStep_tac2. econstructor 7; eauto. exploit sig_preserved; eauto. }
        econs; eauto. eapply find_function_prop; eauto.
        eapply val_intptr_match_stackframes; eauto.
        i; exploit free_val_intptr; eauto. eapply VALIST; eauto using free_val_intptr.
      + remember (change_code f (subst_capture_code domtree d s0 root (fn_code f))) as f'.
        eapply subst_capture_code_spec' in H as INSTR'; des; eauto.
        * eapply find_function_translated in H0 as FIND; cycle 1; eauto. des.
          erewrite sig_preserved in INSTR'; eauto.
          eapply free_concrete_extends in H2; des; eauto.
          eexists. eexists. splits;[econs | |].
          { DStep_tac2. econstructor 7; eauto.
          erewrite <- stacksize_preserved; eauto. }
          econs; eauto. eapply find_function_prop; eauto.
          eapply val_intptr_match_stackframes; eauto using free_val_intptr.
          eapply VALIST; eauto using free_val_intptr.
        * eapply find_function_translated in H0 as FIND; cycle 1; eauto. des.
          simpl in INSTR'. erewrite sig_preserved in INSTR'; eauto.
          eapply free_concrete_extends in H2; des; eauto.
          eexists. eexists. splits;[econs | |].
          { DStep_tac2. econstructor 7; eauto.
            erewrite <- stacksize_preserved; eauto. }
          econs; eauto. eapply find_function_prop; eauto.
          eapply val_intptr_match_stackframes; eauto using free_val_intptr.
          eapply val_intptrist_trans. eapply VALIST; eauto using free_val_intptr.
          eapply VALIST'; eauto. exploit DSEQUIV; i; des; eauto using free_val_intptr.
          econs. eapply compute_dom_correct; eauto. ii; clarify.
    - (* Ibuiltin *)
      inv MS.
      + exploit eval_builtin_args_val_intptr; eauto; i; des. eapply REGS.
        eapply external_call_concrete_extends in H1 as TFEX; eauto; des.
        eexists; eexists. esplits.
        { eapply TFEX. }
        DStep_tac2; try (unfold is_internal in INT; ss; des_ifs; fail).
        econstructor 8; eauto. eapply eval_builtin_args_preserved in H2; eauto.
        i; exploit symbols_preserved; eauto.
        eapply external_call_symbols_preserved in TFEX0; eauto. 
        eapply (Genv.senv_match STEP); eauto.
        econs; eauto. eapply val_intptr_match_stackframes; eauto. i.
        exploit external_call_binds'; eauto; i.
        i. induction res; ss; exploit external_call_binds'; eauto. i.
        destruct (peq arg x). { clarify; repeat rewrite PMap.gss; eauto. }
        { repeat rewrite PMap.gso; eauto. }
        { ss. des_ifs. }
        { unfold ge_binded_state in IBIND. ss. ss. fold ge.
          ii. destruct senv_preserved.  des.
          erewrite <- H7 in H4. erewrite <- H6 in H5.
          eapply IBIND; eauto. }
      + remember (change_code f (subst_capture_code domtree d s0 root (fn_code f))) as f'.
        eapply subst_capture_code_spec' in H as INSTR'; eauto; des.
        * exploit eval_builtin_args_val_intptr; eauto; i; des. eapply REGS.
          eapply external_call_concrete_extends in H1 as TFEX; eauto; des.
          eexists; eexists. esplits.
          { eapply TFEX. }
          DStep_tac2; try (unfold is_internal in INT; ss; des_ifs; fail).
          econstructor 8; eauto. eapply eval_builtin_args_preserved in H2; eauto.
          i; exploit symbols_preserved; eauto.
          eapply external_call_symbols_preserved in TFEX0; eauto. 
          eapply (Genv.senv_match STEP); eauto.
          econs; eauto. eapply val_intptr_match_stackframes; eauto; i;
            exploit external_call_binds'; eauto.
          i. induction res; ss; exploit external_call_binds'; eauto. i.
          destruct (peq arg x). { clarify; repeat rewrite PMap.gss; eauto. }
          { repeat rewrite PMap.gso; eauto. }
          i. exploit DSEQUIV. econs. eapply (@Dom.sdom_dom_pred node peq); eauto.
          econs; eauto. ii; clarify; ss. rewrite CAPT in INT; exploit INT; eauto. econs; eauto.
          i; des. induction res; ss; eapply external_call_binds' in TFEX0 as T'; eauto;
            eapply external_call_binds' in H5 as T''; eauto.
          destruct (peq s0 x).
          { clarify. assert (use f x root). econs; econstructor 4; eauto; ss. eauto.
            assert (def f x pc). econs. econs 4; eauto.
            assert (dom f pc root). exploit fn_strict; eauto.
            assert (dom f root pc). eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto.
            exploit (@Dom.dom_antisym node peq); eauto. i; clarify.
            rewrite CAPT in INT; exploit INT; ss. }
          { repeat rewrite PMap.gso; eauto; ii; clarify; def_def f x root pc; i; clarify;
              rewrite CAPT in INT; exploit INT; ss. }
          { ss. des_ifs. }
          { unfold ge_binded_state in IBIND. ss. ss.
            eapply ge_binded_senv_equiv; eauto. eapply senv_preserved. }
        * assert (exists vargs',
                  eval_builtin_args tge (fun r => rs' # r) sp m'0
                  (map (rename_barg d s0) args) vargs' /\ val_intptrist m'0 vargs vargs').
          { exploit eval_builtin_args_val_intptr; i; des; eauto. eapply REGS.
            eapply eval_builtin_args_preserved in H0 as H0'.
            2:{ i; eapply symbols_preserved. }
            eapply eval_builtin_args_preserved in H2; try eapply symbols_preserved.
            revert H2 H3. generalize args vl2 vargs. induction args0; ss; i. 
            inv H2. exists nil; split; try econs; eauto.
            destruct vl0. inv H2. inv H2. destruct vargs0. inv H3.
            eapply eval_builtin_arg_rename_barg' in H7 as H'. des.
            exploit IHargs0; eauto; i; des. inv H3; eauto.
            exists (v' :: vargs'). split; eauto.
            - econs; eauto.
            - econs; eauto. inv H3. eapply val_intptr_trans. eapply H10. eauto.
            - exploit DSEQUIV; i; des; eauto. econs; eauto.
              eapply compute_dom_correct; eauto. }
          des. ss. des_ifs_safe. exploit external_call_concrete_extends; try eapply H1; eauto.
          { unfold ge_binded_state in IBIND. ss. ss.
            eapply ge_binded_senv_equiv; eauto. eapply senv_preserved. }
          i. des.
          eexists; eexists. splits.
          { eapply H. }
          DStep_tac2. econs; eauto.
          eapply external_call_symbols_preserved in H4; eauto. eapply senv_preserved.
          
          econs; eauto.
          { eapply val_intptr_match_stackframes; eauto.
            i; eapply external_call_binds'; eauto. }
          { i. induction res; ss; eauto using external_call_binds'.
            destruct (peq arg x). clarify; repeat rewrite PMap.gss; eauto.
            repeat rewrite PMap.gso; eauto using external_call_binds'. }
          { ss. des_ifs. }
          i. exploit DSEQUIV; i; des; eauto. econs.
          eapply (@Dom.sdom_dom_pred node peq); eauto.
          econs; eauto. ii; clarify; ss.
          induction res; ss; eauto using external_call_binds'.
          destruct (peq s0 x).
          { assert (use f x root). econs; econstructor 4; eauto; ss. eauto.
            assert (def f x pc). econs. econs 4; eauto.
            assert (dom f pc root). exploit fn_strict; eauto.
            assert (dom f root pc). clarify. eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto.
            clarify.
            exploit (@Dom.dom_antisym node peq); eauto. i; clarify.  }
          { assert (ROOT': root_capture root (n :: l1) domtree) by ss. clear ROOT.
            repeat rewrite PMap.gso; eauto; ii; clarify; eauto using external_call_binds'.
            def_def f x root pc; i; clarify. def_def f x root pc; i; clarify. }
    - (* Icond true *)
      inv MS.
      + eexists. eexists. splits; [econs| |]. DStep_tac2. econstructor 9; eauto.
        erewrite <- eval_condition_wrapper_binded; eauto. econs; eauto.
      + remember (change_code f (subst_capture_code domtree d s0 root (fn_code f))) as f'.
        eapply subst_capture_code_spec' in H as INSTR'; des; eauto.
        * eexists. eexists. splits; [econs| |]. DStep_tac2. econstructor 9; eauto.
          erewrite <- eval_condition_wrapper_binded; eauto.
          econs; eauto. i. exploit DSEQUIV; eauto.
          econs. eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto. ii; clarify.
        * eexists. eexists. splits; [econs| |]. DStep_tac2. econstructor 9; eauto.
          eapply eval_condition_wrapper_binded. eauto.
          (* eapply eval_condition_wrapper_binded; eauto. *)
          eapply val_intptrist_trans. eapply VALIST. i; eauto.
          eapply VALIST'; eauto. exploit DSEQUIV; i; des; eauto.
          econs; eauto. eapply compute_dom_correct; eauto.
          eauto.
          econs; eauto. i.  exploit DSEQUIV; eauto.
          econs. eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto. ii; clarify.
    - (* Icond false *)
      inv MS.
      + eexists. eexists. splits; [econs| |]. DStep_tac2. econstructor 10; eauto.
        eapply eval_condition_wrapper_binded; eauto. eauto. econs; eauto.
      + remember (change_code f (subst_capture_code domtree d s0 root (fn_code f))) as f'.
        eapply subst_capture_code_spec' in H as INSTR'; des; eauto.
        * eexists. eexists. splits; [econs| |]. DStep_tac2. econstructor 10; eauto.
          eapply eval_condition_wrapper_binded; eauto.
          econs; eauto. i. exploit DSEQUIV; eauto.
          econs. eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto. ii; clarify.
        * eexists. eexists. splits; [econs| |]. DStep_tac2. econstructor 10; eauto.
          eapply eval_condition_wrapper_binded. eauto.
          (* erewrite <- eval_condition_wrapper_binded; eauto. *)
          eapply val_intptrist_trans. eapply VALIST. i; eauto.
          eapply VALIST'; eauto. exploit DSEQUIV; i; des; eauto.
          econs; eauto. eapply compute_dom_correct; eauto.
          eauto.
          econs; eauto. i.  exploit DSEQUIV; eauto.
          econs. eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto. ii; clarify.
    - (* Ijumptbl *)
      inv MS.
      + eexists. eexists. splits; [econs| |]. DStep_tac2. econstructor 11; eauto.
        specialize (REGS arg); inv REGS;
          try rewrite H0 in *; inv H3; try inv H2; eauto. econs; eauto.
      + remember (change_code f (subst_capture_code domtree d s0 root (fn_code f))) as f'.
        eapply subst_capture_code_spec' in H as INSTR'; des; eauto.
        * eexists. eexists. splits; [econs| |]. DStep_tac2. econstructor 11; eauto.
          specialize (REGS arg); inv REGS;
            try rewrite H0 in *; inv H3; try inv H2; eauto. econs; eauto.
          i. exploit DSEQUIV; i; des; split; eauto.
          eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto. ss.
          eapply list_nth_z_in; eauto. ii; clarify.
        * eexists. eexists. splits; [econs| |]. DStep_tac2. econstructor 11; eauto.
          specialize (REGS arg); inv REGS;
            try rewrite H0 in *; inv H3; try inv H2; eauto.
          destruct (peq arg s0).
          { clarify. rewrite RENAME. exploit DSEQUIV; i; des; eauto.
            econs. eapply compute_dom_correct; eauto. ii; clarify.
            rewrite <- H4 in H3. inv H3. eauto. }
          { rewrite RENAMEN; eauto. }
          econs; eauto. i. exploit DSEQUIV; i; des; eauto. econs.
          eapply compute_dom_correct; eauto. ii; clarify.
    - (* Ireturn *)
      inv MS.
      + eapply free_concrete_extends in H0 as FREE; des; eauto.
        eexists. eexists. splits; [econs| |]. DStep_tac2. econstructor 12; eauto. econs; eauto.
        eapply val_intptr_match_stackframes; eauto. i. eapply free_val_intptr; eauto.
        destruct or; ss; eauto using val_intptr.
        eapply free_val_intptr; eauto.
      + remember (change_code f (subst_capture_code domtree d s0 root (fn_code f))) as f'.
        eapply subst_capture_code_spec' in H as INSTR'; des; eauto.
        * eapply free_concrete_extends in H0 as FREE; des; eauto.
          eexists. eexists. splits; [econs| |]. DStep_tac2. econstructor 12; eauto.
          erewrite <- stacksize_preserved; eauto.
          econs; eauto. eapply val_intptr_match_stackframes; eauto.
          i. eapply free_val_intptr; eauto. destruct or; ss; eauto using val_intptr.
          eapply free_val_intptr; eauto.
        * eapply free_concrete_extends in H0 as FREE; des; eauto.
          eexists. eexists. splits; [econs| |]. DStep_tac2. econstructor 12; eauto.
          erewrite <- stacksize_preserved; eauto.
          econs; eauto. eapply val_intptr_match_stackframes; eauto.
          i. eapply free_val_intptr; eauto. destruct or; ss; eauto using val_intptr.
          destruct (peq r s0).
          { clarify. rewrite RENAME. exploit DSEQUIV; i; des; eauto.
            econs; eauto. eapply compute_dom_correct; eauto.
            eapply free_val_intptr; eauto. eapply val_intptr_trans; eauto. }
          { rewrite RENAMEN; eauto. eapply free_val_intptr; eauto. }
    - (* Callstate internal *)
      inv MS. eapply alloc_concrete_extends in EXTENDS; des; eauto.
      pose proof STEP0 as STEP0'. inv STEP0; symmetry in H1; monadInv H1.
      eexists; eexists. splits; [econs| |]. DStep_tac2. econstructor 13. erewrite <- stacksize_preserved; eauto.
      unfold transf_fundef_step in STEP0'. symmetry in STEP0'. monadInv STEP0'.
      symmetry in EQ0. eapply transf_function_step_spec in EQ0; eauto. des.
      + clarify. destruct (compute_dom x) eqn:COMX; ss. econs 1; eauto. inv WF0; eauto.
        eapply val_intptr_match_stackframes; eauto.
        i. eapply alloc_val_intptr; eauto.
        i. exploit init_regs_val_intptr; i; eauto. eapply alloc_val_intptr; eauto.
      + enough (SSA.fn_params x = SSA.fn_params f). rewrite H0.
        enough (SSA.fn_entrypoint x = SSA.fn_entrypoint f). rewrite H1. econs 2; eauto.
        inv WF0; eauto.
        eapply val_intptr_match_stackframes; eauto. i; eapply alloc_val_intptr; eauto.
        i. exploit init_regs_val_intptr; i; eauto. eapply alloc_val_intptr; eauto.
        destruct l; ss. inv EQ1. eauto.
        i. exploit (@Dom.entry_sdom node peq); eauto. ss.
        clarify. destruct f; ss. inv EQ3; ss.
      + inv WF0; eauto.
    - (* Callstate external *)
      inv MS. destruct f'. inv STEP0. inv STEP0.
      exploit external_call_concrete_extends; i; des.
      { ss. eauto. }
      5:{ eexists; eexists. splits; cycle 1.
          - DStep_tac2. econs; eauto.
          - econs; eauto. eapply val_intptr_match_stackframes; eauto. i.
            eapply external_call_binds'; eauto.
          - revert H0. instantiate (1:= t). i. eapply H0. }
      { ss. }
      eapply external_call_symbols_preserved in H; eauto. eapply senv_preserved.
      eauto. eauto.
    - (* Returnstate *) 
      inv MS. inv STACK.
      + clarify. eexists; eexists. splits;[econs| |]. DStep_tac2. econs.
        econs; eauto. i. destruct (peq arg res); clarify.
        repeat rewrite PMap.gss; eauto. repeat rewrite PMap.gso; eauto.
        inv REGS; eauto.
      + exploit transf_function_step_spec; i; des; eauto.
        * clarify. eexists; eexists. splits;[econs| |]. DStep_tac2. econs. econs; eauto. 
          i. destruct (peq arg res); clarify.
          repeat rewrite PMap.gss; eauto.
          repeat rewrite PMap.gso; eauto. inv MATCHREGS; eauto.
          (* inv STEP0. rewrite COMF' in H0; inv H0. *)
        * clarify. eexists; eexists. splits; [econs| |]. DStep_tac2. econs. econs; eauto.
          i. destruct (peq arg res); clarify.
          repeat rewrite PMap.gss; eauto. repeat rewrite PMap.gso; eauto.
          inv MATCHREGS; eauto. inv ROOT. rewrite CAPT in H3; inv H3. ss.
          i. inv ROOT. rewrite CAPT in H3. inv H3. destruct (peq s1 res).
          { clarify. assert (def f res pred); eauto.
            assert (use f res (find_capture_root domtree hd tl)). econs.
            exploit UIbuiltin; eauto. ss. eauto.
            exploit (@Dom.dom_antisym node peq). exploit fn_strict; eauto.
            eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto.
            ii; subst pred. rewrite CAPT in PREDINFO. inv PREDINFO. }
          { repeat rewrite PMap.gso; eauto; ii; clarify;
              def_def f res (find_capture_root domtree hd tl) pred; i; clarify. }
    Unshelve. all: auto.
  Qed.

  Lemma extcall_capture_sem_val_intptr : forall ge v m1 t vr m2,
    extcall_capture_sem ge (v :: nil) m1 t vr m2 -> trace_intact t ->
    val_intptr m2 v vr.
  Proof.
    i. inv H; try (exploit H0; ss; eauto; ss; fail).
    - inv CAPTURE. flatten.
      + econs; eauto. unfold Mem.to_int, Mem.ptr2int_v, Mem.ptr2int. flatten.
        flatten Eq0. destruct (Mem.mem_concrete m1) ! b eqn:M1B.
        * exploit PREVADDR; eauto. i; des; clarify. rewrite <- H1 in Eq2.
          rewrite M1B in Eq2. inv Eq2. eauto.
        * exploit CAPTURED; eauto; i. rewrite H in Eq2. rewrite PTree.gss in Eq2. inv Eq2.
          eauto.
        * flatten Eq0. destruct (Mem.mem_concrete m1) ! b eqn:M1B.
          { exploit PREVADDR; i; des; clarify. rewrite <- H1 in Eq1. rewrite M1B in Eq1.
            inv Eq1. }
          { exploit CAPTURED; i; clarify. rewrite H in Eq1; rewrite PTree.gss in Eq1.
            inv Eq1. }
      + econs; eauto. unfold Mem.to_int, Mem.ptr2int_v, Mem.ptr2int. flatten.
        flatten Eq0. destruct (Mem.mem_concrete m1) ! b eqn:M1B.
        * exploit PREVADDR; eauto. i; des; clarify.
        * exploit CAPTURED; eauto; i. rewrite H in Eq2. rewrite PTree.gss in Eq2. inv Eq2.
          eauto.
        * flatten Eq0. destruct (Mem.mem_concrete m1) ! b eqn:M1B.
          { exploit PREVADDR; i; des; clarify. }
          { exploit CAPTURED; i; clarify. }
    - econs.
  Qed.

  Lemma match_states_bsim
      s1
      (EXT: SSA.is_external ge s1)
      (STC: state_char prog s1)
      s2 t' s2'
      (IBIND: ge_binded_state tge s2 gmtgt)
      (STEPTGT: Step (SSA.semantics tprog) s2 t' s2')
      (MATCH: match_states s1 s2)
      (SAFESRC: safe (SSA.semantics prog) s1) :
    (exists t s1', tr_rel (ev_rel gmtgt) t t' /\ Step (SSA.semantics prog) s1 t s1' /\ match_states s1' s2')
     \/
    (~ trace_intact t'
       /\ exists s1'' t, Step (SSA.semantics prog) s1 t s1''
       /\ exists tl, tr_rel (ev_rel gmtgt) t (Eapp (trace_cut_pterm t') tl)).
  Proof.
    assert (SEQUIV: Senv.equiv tge ge) by (symmetry; eapply senv_preserved).
    unfold safe in SAFESRC. specialize (SAFESRC _ (star_refl _ _ _)). des; cycle 2; clarify.
    { inv SAFESRC; ss. }
    unfold SSA.is_external in *. des_ifs.
    - inv MATCH.
      + inv SAFESRC; des; des_ifs. inv STEPTGT; des; des_ifs; clarify.
        exploit external_call_concrete_extends_backward; i; des; try eapply EXTENDS; eauto; cycle 1.
        * eapply external_call_symbols_preserved in CALLSRC; eauto using symbols_preserved.
          left; esplits; eauto.
          econs; eauto.
          econs; eauto. eapply val_intptr_match_stackframes; eauto.
          i; eauto using external_call_binds'.
          i. induction b; ss; eauto using external_call_binds'.
          destruct (peq x arg). clarify. repeat rewrite PMap.gss; eauto.
          repeat rewrite PMap.gso; eauto using external_call_binds'.
        * eapply external_call_symbols_preserved in H9; eauto using senv_preserved.
          eapply UBSRC in H9; ss.
        * right. esplits; eauto.
          eapply exec_Ibuiltin. eauto. eapply H8.
          eapply external_call_symbols_preserved; eauto.
        * exploit eval_builtin_args_val_intptr; eauto. eapply REGS. i. des.
          exploit eval_builtin_args_preserved. eapply symbols_preserved. eapply H. i.
          exploit eval_builtin_args_determ. eapply H1. eapply H11. i; clarify.
      + inv SAFESRC; des; des_ifs.
        eapply transf_function_step_instr_spec in H7 as INS; eauto. des.
        * inv STEPTGT; des; des_ifs.
          exploit external_call_concrete_extends_backward; i; des; eauto; cycle 1.
          { eapply external_call_symbols_preserved in CALLSRC; eauto using symbols_preserved.
            destruct (classic (trace_intact t')).
            - assert (INTACT: trace_intact t0).
              { ii. eapply H. clear - H0 TRREL. ginduction TRREL; ss. i. des; subst.
                - inv H. eauto.
                - right. eauto. }
              left; esplits; eauto. econs; eauto.
              econs; eauto. eapply val_intptr_match_stackframes; eauto.
              i; eauto using external_call_binds'.
              i. induction b; ss; eauto using external_call_binds'.
              destruct (peq x arg). clarify. repeat rewrite PMap.gss; eauto.
              repeat rewrite PMap.gso; eauto using external_call_binds'.
              i. destruct (peq root pc).
              { clarify. ss. repeat rewrite (@PMap.gss _ d).
                repeat rewrite PMap.gso; ii; clarify;
                  try (exploit fn_use_def_code; eauto;
                    exploit UIbuiltin; eauto; ss; eauto; fail).
                inv H8. inv H3. inv H5. inv H11. inv H5. inv H3.
                split; exploit extcall_capture_sem_val_intptr; i; try eapply INTACT; eauto.
                eapply concrete_extends_val_intptr. eapply MEM. eauto.
                eapply extcall_capture_sem_val_intptr in H12; eauto. }
              { exploit DSEQUIV; eauto; i; des.
                econs; eauto. eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto.
                induction b ; ss; eauto using external_call_binds'.
                destruct (peq x s); clarify.
                { exploit (@Dom.dom_antisym node peq).
                  eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto.
                  exploit fn_strict; eauto. econs. exploit UIbuiltin. eapply CAPT.
                  ss. left; eauto. eauto. i; clarify. }
                { assert (d <> x). { ii; clarify. def_def f x root pc. }
                  repeat rewrite PMap.gso; eauto using external_call_binds'. } }
            - right. split; eauto.
              specialize (trace_cut_pterm_split t0). i. des.
              esplits.
              + eapply exec_Ibuiltin. eapply H7. eapply H8. eapply CALLSRC.
              + instantiate (1:=t1). rewrite H0. eapply tr_rel_app.
                { eapply tr_rel_cut_pterm; eauto. ii. destruct ev1, ev2; ss. }
                eapply tr_rel_refl. eapply ev_rel_refl. }
          { eapply external_call_symbols_preserved in H9; eauto using senv_preserved.
            eapply UBSRC in H9; ss. }
          { right. esplits; eauto. eapply exec_Ibuiltin. eauto. eapply H8.
            eapply external_call_symbols_preserved; eauto. }
          exploit eval_builtin_args_val_intptr; eauto; i; des. eapply REGS.
          exploit eval_builtin_args_determ. eapply H.
          eapply eval_builtin_args_preserved in H11; eauto.
          i; exploit symbols_preserved; eauto. i; clarify.
        * inv STEPTGT; des; des_ifs. destruct l0; simpl in INS1, ROOT. ss.
          rewrite <- INS1 in ROOT; subst root0.
          exploit external_call_concrete_extends_backward; i; des; eauto; cycle 1.
          { eapply external_call_symbols_preserved in CALLSRC; eauto using symbols_preserved.
            destruct (classic (trace_intact t')).
            - left; esplits; eauto. econs; eauto.
              econs; eauto. eapply val_intptr_match_stackframes; eauto.
              i; eauto using external_call_binds'.
              i. induction b; ss; eauto using external_call_binds'.
              destruct (peq x arg). clarify. repeat rewrite PMap.gss; eauto.
              repeat rewrite PMap.gso; eauto using external_call_binds'.
              i. destruct (peq root pc).
              { clarify. }
              { exploit DSEQUIV; eauto; i; des.
                econs; eauto. eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto.
                induction b ; ss; eauto using external_call_binds'.
                destruct (peq x s); try subst s.
                { rewrite CAPT in INS3; inv INS3. exploit (@Dom.dom_antisym node peq).
                  eapply (@Dom.sdom_dom_pred node peq); eauto. econs; eauto.
                  exploit fn_strict; eauto. econs. exploit UIbuiltin. eapply CAPT.
                  ss. left; eauto. eauto. i; clarify. }
                { assert (d <> x). { ii; subst d. def_def f x root pc. }
                  repeat rewrite PMap.gso; eauto using external_call_binds'. } }
            - right. split; eauto.
              specialize (trace_cut_pterm_split t0). i. des.
              esplits.
              + eapply exec_Ibuiltin. eapply H7. eapply H8. eapply CALLSRC.
              + instantiate (1:=t1). rewrite H0. eapply tr_rel_app.
                { eapply tr_rel_cut_pterm; eauto. ii. destruct ev1, ev2; ss. }
                eapply tr_rel_refl. eapply ev_rel_refl. }
          { eapply external_call_symbols_preserved in H9; eauto using senv_preserved.
            eapply UBSRC in H9; ss. }
          { right. esplits; eauto. eapply exec_Ibuiltin. eauto. eapply H8.
            eapply external_call_symbols_preserved; eauto. }
          (* exploit eval_builtin_arg_rename_barg'; eauto. *)
          exploit eval_builtin_args_val_intptr; eauto; i; des. eapply REGS.
          eapply eval_builtin_args_preserved in H11; cycle 1.
          i; exploit symbols_preserved; intros P; rewrite <- P; eauto.
          eapply val_intptrist_trans; eauto.
          revert H H11. generalize l vargs0 vl2. induction l1; ss; i. 
          inv H11. inv H. econs.
          destruct vl0. inv H. inv H. destruct vargs1. inv H11. inv H11.
          eapply eval_builtin_arg_rename_barg' in H4 as H'. des.
          exploit eval_builtin_arg_determ. eauto. subst ge. eapply H3.
          i; clarify. econs; eauto. exploit DSEQUIV; i; des; eauto.
          econs; eauto. eapply compute_dom_correct; eauto.
          rewrite CAPT in INS3; inv INS3. eauto.
    - inv MATCH. inv SAFESRC; des; des_ifs. inv STEPTGT; des; des_ifs; clarify. inv STEP0.
      exploit external_call_concrete_extends_backward; i; des; eauto.
      + eapply external_call_symbols_preserved in CALLSRC; eauto using symbols_preserved.
        left; esplits; eauto. econs; eauto.
        econs; eauto. eapply val_intptr_match_stackframes; eauto.
        i; eauto using external_call_binds'.
      + eapply external_call_symbols_preserved in H5; eauto using senv_preserved.
        exploit UBSRC; eauto. ss.
      + right. esplits; eauto.
        exploit external_call_symbols_preserved; eauto.
        eapply exec_function_external; eauto.
        (* Unshelve. all: eauto. *)
  Qed.
  
  Opaque transf_function_step.

  Lemma match_states_xsim st_src0 st_tgt0 (STC: state_char prog st_src0) (IBIND: ge_binded_state tge st_tgt0 gmtgt) (MATCH: match_states st_src0 st_tgt0) :
    xsim (SSA.semantics prog) (SSA.semantics tprog) gmtgt lt 0%nat st_src0 st_tgt0.
  Proof.
    generalize dependent st_src0. generalize dependent st_tgt0.
    pcofix CIH. i. pfold.
    destruct (classic (SSA.is_external ge st_src0)); cycle 1.
    (* not external *)
    - left. econs. econs.
      + i. exploit step_simulation; eauto. i. des. esplits. 
        { instantiate (1:=t'). ss. }
        { left. split.
          - eapply plus_one; eauto.
          - eapply semantics_receptive_at; auto. }
        right. eapply CIH.
        {  inv H1. eapply ge_binded_state_step; eauto. }
        { eapply state_char_preservation; eauto. }
        eauto.
      + ii. eapply final_state_determ; eauto.
        inv FINALSRC. inv MATCH. inv STACK. inv BIND. econs.
      (* + eauto. *)
    (* external *)
    - right. econs; eauto. i. econs; eauto.
      + i. exploit match_states_bsim; try eapply STEPTGT; eauto.
        i. des.
        * left. esplits; eauto. left.
          eapply plus_one. eauto.
          right. eapply CIH; eauto.
          { eapply ge_binded_state_step; eauto. }
          { eapply state_char_preservation; eauto. }
        * right. esplits; eauto. eapply star_one; eauto.
      + ii. inv FINALTGT. inv MATCH. unfold SSA.is_external in H. ss.
      + i. specialize (SAFESRC _ (star_refl _ _ _)). des; cycle 2; clarify.
        { inv SAFESRC; ss. }
        right. inv MATCH; ss; des_ifs; inv SAFESRC; unfold ge in *; clarify.
        * exploit eval_builtin_args_val_intptr; i; des; eauto. eapply REGS.
          eapply eval_builtin_args_preserved in H0; i; cycle 1.
          exploit symbols_preserved; eauto.
          eapply external_call_symbols_preserved in H10; try eapply senv_preserved.
          exploit ec_concrete_extends_backward_progress.
          { eapply external_call_spec_backward; eauto. }
          eauto. eauto. eauto. eauto. i. des.
          esplits. eapply exec_Ibuiltin; eauto.
        * eapply transf_function_step_instr_spec in STEP0 as INSTR'; des; eauto.
          { eapply eval_builtin_args_preserved in H9; cycle 1.
            i; exploit symbols_preserved; eauto.
            exploit eval_builtin_args_val_intptr; i; des; eauto. eapply REGS.
            exploit ec_concrete_extends_backward_progress.
            { eapply external_call_spec_backward; eauto. }
            2:{ eauto. }
            2:{ eauto. }
            2:{ eauto. }
            erewrite <- ge_binded_senv_equiv.
            2:{ symmetry. eapply senv_preserved. }
            unfold ge_binded_state in IBIND. ss. eauto. i. des.
            esplits. eapply exec_Ibuiltin; eauto.
            eapply external_call_symbols_preserved. eapply senv_preserved.
            eapply CALLTGT. }
          { destruct l. simpl in INSTR'1; ss. simpl in INSTR'1, ROOT.
            rewrite DOMTREE in INSTR'. inversion INSTR'; subst domtree0.
            rewrite <- ROOT in INSTR'1. subst root0.
            rewrite CAPT in INSTR'3. inversion INSTR'3. subst s0 d0 pc'.
            eapply eval_builtin_args_preserved in H9; cycle 1.
            i; exploit symbols_preserved; eauto.
            exploit eval_builtin_args_val_intptr; i; des; eauto. eapply REGS.
            enough (exists vl2',
              eval_builtin_args tge (fun r => rs' # r) sp m' (map (rename_barg d s) l0) vl2'
              /\ val_intptrist m' vl2 vl2'). des.
            exploit ec_concrete_extends_backward_progress; i; des.
            { eapply external_call_spec_backward; eauto. }
            5:{ esplits. eapply exec_Ibuiltin; eauto. }
            { unfold ge_binded_state in IBIND. ss. eauto. }
            eapply external_call_symbols_preserved; eauto. eapply senv_preserved.
            eauto.
            eapply val_intptrist_trans; eauto.
            revert H0. generalize l0 vl2. induction l1; ss; i.
            - inv H0. eexists; split; try econs.
            - destruct vl0; inv H0. eapply eval_builtin_arg_rename_barg' in H5; des.
              exploit IHl1; eauto; i; des.
              exists (v' :: vl2'). split; econs; eauto.
              exploit DSEQUIV; i; des; eauto. econs; eauto.
              eapply compute_dom_correct; eauto. }
        * exploit ec_concrete_extends_backward_progress; i; des.
          6:{ esplits. econs. eapply CALLTGT. }
          { eapply external_call_spec_backward; eauto. }
          { unfold ge_binded_state in IBIND. ss. eauto. }
          { eapply external_call_symbols_preserved; eauto using senv_preserved. }
          { eauto. }
          eauto.
      (* + ii. inv FINALTGT. inv MATCH. unfold SSA.is_external in H. ss. *)
      (* + ss. *)
  Qed.

  End STEPSIM.
  
  Lemma same_public:
    prog_public prog = prog_public tprog.
  Proof. inv STEP. des; eauto. Qed.

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

  (* move to Memory.v *)
  (* Lemma capture_list_bind *)
          
  Lemma transf_initial_capture
    S1 S2 S2'
    (INITSRC: SSA.initial_state prog S1)
    (INITTGT: SSA.initial_state tprog S2)
    (MATCH: match_states S1 S2)
    (CAPTGT: SSA.glob_capture tprog S2 S2'):
  exists S1',
    SSA.glob_capture prog S1 S1'
  /\ match_states S1' S2'
  /\ gm_improves (concrete_snapshot ge S1') (concrete_snapshot tge S2').
  Proof.
    inv CAPTGT. ss.
    rewrite Genv.globalenv_public in CAPTURE.
    rewrite <- same_public in CAPTURE. erewrite <- non_static_equiv in CAPTURE.
    inv MATCH. inv STACK. inv BIND. inv CAPTURE.
    assert (exists m0', Genv.capture_init_mem m0 (Genv.non_static_glob (Genv.globalenv prog) (prog_public prog)) m0'
                 /\ concrete_extends m0' m').
    { remember (prog_public prog) as lst. clear Heqlst. clear - EXTENDS CAP.
      ginduction lst; ss; i.
      - inv CAP. esplits; eauto. econs; eauto. econs; eauto.
      - destruct (Genv.public_symbol (Genv.globalenv prog) a) eqn:PSYMB.
        2:{ exploit IHlst; eauto. }
        destruct (Genv.find_symbol (Genv.globalenv prog) a) eqn:PFIND.
        2:{ exploit IHlst; eauto. }
        i. inv CAP.
        exploit capture_concrete_extends; eauto. i. des. exploit IHlst; eauto. i. des.
        inv H. esplits; eauto. econs; eauto. econs; eauto. }
    des. esplits.
    - econs; eauto. rewrite Genv.globalenv_public. eauto.
    - econs; eauto; econs.
    - unfold concrete_snapshot. ii.
      specialize senv_preserved. intros SENVEQ.
      inv SENVEQ. des. erewrite H3, H2. des_ifs; ss. inv H0.
      eapply extended_concrete; eauto.
    Unshelve. all: eauto.
  Qed.

  Theorem transf_program_step_correct : 
    mixed_simulation (SSA.semantics prog) (SSA.semantics tprog).
  Proof.
    econs. econs.
    - apply lt_wf.
    - rr. i. exists (S a). lia.
    - econs. i. exploit transf_initial_states; eauto. i. des.
      exists S2. split.
      (* initial state *)
      + econs; eauto. eapply initial_state_determ.
      (* mixed sim *) 
      + r. ii. exploit transf_initial_capture; eauto. i. des. esplits; eauto.
        { ss. subst. ss. }
        subst. eapply match_states_xsim; eauto.
        { eapply glob_capture_char; eauto. eapply initial_state_char; eauto. }
        r. r. i. unfold gmtgt. ss. unfold concrete_snapshot. ss. split.
        { fold tge. rewrite H4, H5. ss. }
        inv CAPTGT. fold tge in CAPTURE.
        assert (In b (Genv.non_static_glob tge (Genv.genv_public tge))).
        { assert (In id (Genv.genv_public tge)).
          { unfold Genv.public_symbol in H4. rewrite H5 in H4.
            destruct in_dec in H4; ss. }
          remember (Genv.genv_public tge) as l.
          clear - H6 H4 H5. ginduction l; ss; i; des; subst; eauto.
          - rewrite H4, H5. ss. eauto.
          - exploit IHl; eauto. i. des_ifs. des_ifs; eauto. }
        inv CAPTURE. ss.
        exploit Mem.capture_list_concrete; eauto. i. des. exists addr.
        fold tge. rewrite H4, H5. eauto.
    - i. apply senv_preserved.
  Qed.

End CORRECTNESS_STEP.

(* Note: behavioral refinement proof of the whole optimization is in Complements.v *)
Section CORRECTNESS.

  Variable prog: program.
  Variable tprog: program.
  Hypothesis MATCH : match_prog prog tprog.
  Hypothesis HWF : wf_ssa_program prog.
  Let ge := Genv.globalenv prog.
  Let tge := Genv.globalenv tprog.

  (* Showing that the whole optimization process is equivalent to multiple steps *)
  Fixpoint empty_node_list {A} (l : list A) : list (list node) :=
    match l with
    | nil => nil
    | hd :: tl => nil :: empty_node_list tl
    end.

  Fixpoint capture_node_list (l : list (ident * globdef fundef unit)) :=
    match l with
    | (id, Gfun (Internal f)) :: l'=>
      match compute_dom f with
      | Some domtree => find_capture_all f.(fn_code) :: capture_node_list l'
      | None => nil :: capture_node_list l'
      end
    | _ :: l' => nil :: capture_node_list l'
    | nil => nil
    end.

  Definition max_capt_len (p: program) : nat :=
    list_max (map (@Datatypes.length node) (capture_node_list (prog_defs p))).

  Lemma match_prog_repeatn : 
    exists n, OK (tprog, empty_node_list (prog_defs tprog)) =
      repeatn_monad transf_program_step n (prog, capture_node_list (prog_defs prog)).
  Proof.
    ii. exists (max_capt_len prog). unfold max_capt_len.
    remember (list_max _). assert (n <= n) by lia. rewrite Heqn in H at 1.
    apply list_max_le in H. clear Heqn. rename H into HLE. inv MATCH. des.
    destruct prog; destruct tprog; ss. rewrite H0. rewrite H1. clear H0 H1.
    remember (mkprogram prog_defs prog_public prog_main) as p. rewrite Heqp.
    revert n HLE. revert H. clear Heqp. generalize prog_defs0 as l'. generalize prog_defs as l.
    induction l; ss; i. inv H. induction n; ss; eauto.
    destruct l' as [ | a' l']. inv H. inv H. destruct a. destruct a' as [i' g'].
    inv H3. simpl in H; subst i'. simpl in H0; inv H0.
    destruct f1.
    - unfold transf_fundef, transf_function, transf_partial_fundef in H1.
      monadInv H1. flatten E. rewrite repeatn_monad_dist. erewrite <- IHl; eauto; cycle 1.
      inv HLE; eauto. unfold fundef in *. simpl.
      inv HLE. exploit repeatn_monad_transf_globdef_step; eauto. i. rewrite H0. ss.
      generalize l as l0; induction l0; ss; i. flatten; ss; try lia.
    - inv H1. rewrite repeatn_monad_dist. erewrite <- IHl; eauto; cycle 1. inv HLE; eauto.
      ss. generalize n. induction n0; ss; eauto.
      generalize l as l0; induction l0; ss; i. flatten; ss; try lia.
    - inv H. ss. rewrite repeatn_monad_dist. erewrite <- IHl; eauto; cycle 1. inv HLE; eauto.
      ss. generalize n. induction n0; ss; eauto.
      generalize l as l0; induction l0; ss; i. flatten; ss; try lia.
  Qed.
  
  Lemma match_prog_wf_ssa : wf_ssa_program tprog.
  Proof.
    pose proof match_prog_repeatn; des.
    remember (capture_node_list (prog_defs prog)) as l.
    assert (Datatypes.length l = Datatypes.length (prog_defs prog)).
    { rewrite Heql. generalize (prog_defs prog). induction l0; ss; i. flatten; ss; try lia. }
    clear Heql. clear MATCH.
    generalize dependent prog. generalize tprog, l.
    induction n.
    - ss. i. monadInv H; auto.
    - i. unfold repeatn_monad in H. symmetry in H. monadInv H.
      fold (repeatn_monad transf_program_step n x) in EQ0. destruct x.
      symmetry in EQ0. eapply IHn in EQ0; eauto.
      eapply transf_program_step_wf_ssa; eauto.
      eapply transf_program_step_match; eauto.
      unfold transf_program_step in EQ. monadInv EQ. simpl. revert H0 EQ1.
      generalize (prog_defs prog0) l0 l1 x. induction l2; ss; i.
      + inv EQ1. exploit length_zero_iff_nil; eauto.
      + destruct l3; try inv H0. monadInv EQ1. exploit IHl2; eauto. i; simpl; lia.
  Unshelve. all: eauto.
  Qed.

End CORRECTNESS.
