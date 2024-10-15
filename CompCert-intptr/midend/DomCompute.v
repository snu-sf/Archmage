(** Algorithm for computing dominance relation with a dataflow analysis *)
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Registers.
Require Import Utils.
Require Import RTL. 
Require Import Dom.
Require Import SSA. 
Require Import SSAutils.
Require Import Kildall.
Require Import Lattice.
Require Import DLib.

Unset Allow StrictProp.

(** * The Semilattice of node sets *)
Module L <: SEMILATTICE.

  Definition t: Type := option (PTree.t unit).
  Definition eq: t -> t -> Prop := @eq _.
  Definition eq_refl: forall x, eq x x := @refl_equal _.
  Definition eq_sym: forall x y, eq x y -> eq y x := @sym_eq _.
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := @trans_eq _.
   
  Fixpoint eqtu (a b: PTree.t unit) : bool := 
    match a, b with 
    | PTree.Leaf , PTree.Leaf  => true
    | PTree.Node l1 o1 r1, PTree.Node l2 o2 r2 => 
      match o1, o2 with 
      | Some _, Some _ => eqtu l1 l2 && eqtu r1 r2
      | None , None => eqtu l1 l2 && eqtu r1 r2
      | _ , _ => false
      end
    | _ , _ => false
    end.
 
  Lemma eqtu_correct : forall x y, eqtu x y = true -> @Logic.eq _ x y.
  Proof. 
    induction x; intros.
    - destruct y; auto.
      simpl in H. congruence.
    - destruct y. inv H. 
      destruct o, o0; try (solve [inv H]).
      + destruct u, u0; try (solve [inv H]).
        inv H. 
        rewrite andb_true_iff in H1. inv H1.
        erewrite (IHx1 x1) ; eauto.
        erewrite (IHx2 x2) ; eauto.
      + inv H.
        rewrite andb_true_iff in H1. inv H1.
        erewrite (IHx1 x1); eauto.
        erewrite (IHx2 x2); eauto.
  Qed.
    
  Definition beq (x y:t) : bool :=
    match x, y with
      | None, None => true
      | Some x, Some y => eqtu x y
      | _, _ => false
    end.

  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    destruct x ; destruct y ; simpl ; try congruence; intros.
    apply eqtu_correct in H.
    congruence.
  Qed.

  Variant ge_ : t -> t -> Prop :=
  | ge0 : forall x, ge_ x None
  | ge1 : forall x y,
      (forall n t, PTree.get n x = Some t -> PTree.get n y = Some t) ->
      ge_ (Some x) (Some y).
  
  Lemma ge_refl: forall x y, eq x y -> ge_ x y.
  Proof. 
    unfold eq; intros; subst.
    destruct y; constructor; auto.
  Qed.

  Lemma ge_trans: forall x y z, ge_ x y -> ge_ y z -> ge_ x z.
  Proof.
    unfold eq; intros; subst.
    inv H; inv H0; constructor.
    auto. 
  Qed.

  Definition bot: t := None.
  Lemma ge_bot: forall x, ge_ x bot.
  Proof. unfold bot; constructor. Qed.

  Definition lub (x y:t) : t :=
    match x, y with
      | None, y => y
      | x, None => x
      | Some x, Some y =>
        Some (PTree.combine (fun x y => match x,y with
                                          | Some _, Some _ => Some tt 
                                          | _, _ => None
                                        end) x y)
    end.

  Lemma ge_lub_left: forall x y, ge_ (lub x y) x.
  Proof.
    unfold lub; intros.    
    destruct x; destruct y; constructor; auto.
    intros n t2; rewrite PTree.gcombine; auto.
    case_eq (t0!n); case_eq (t1!n); intros; try congruence.
    destruct u0; destruct t2; auto.
  Qed.

  Lemma ge_lub_right: forall x y, ge_ (lub x y) y.
  Proof.
    unfold lub; intros.    
    destruct x; destruct y; constructor; auto.
    intros n t2; rewrite PTree.gcombine; auto.
    case_eq (t0!n); case_eq (t1!n); intros; try congruence.
    destruct u; destruct t2; auto.
  Qed.

  Definition ge := ge_.

End L.

(** * Dataflow analysis for computing the dominance relation *)
Definition in_set (n:node) (s:L.t) : bool :=
  match s with
    | None => true
    | Some s => 
      match s!n with
        | None => false
        | Some _ => true
      end
  end.

Definition transfer (f: function) (pc: node) (before: L.t) : L.t :=
  match before with
    | None => None 
    | Some s => Some (PTree.set pc tt s)
  end.

Module DS := Dataflow_Solver(L)(NodeSetForward).

Definition singleton (n:node) : L.t := Some (PTree.set n tt (PTree.empty _)).

Definition compute_dom (f: function): option (PMap.t L.t) :=
  DS.fixpoint f.(fn_code) successors_instr (transfer f)
                          (f.(fn_entrypoint))
                          (singleton f.(fn_entrypoint)).

(** * Correctness of the algorithm *)
Section correctness.

Variable f: function.
Variable mdom : PMap.t L.t.
Variable compute_some: compute_dom f = Some mdom.

Notation entry := (fn_entrypoint f).
Notation code := (fn_code f).
Notation pstate := (@pstate node).

Inductive path : list node -> pstate -> Prop :=
| path0: path nil (PState entry)
| path1: forall p pc i pc'
                (PATH: path p (PState pc))
                (INS: code!pc = Some i)
                (CFG : reached f pc)
                (STEP: In pc' (successors_instr i)), 
    path (pc::p) (PState pc')
| path2: forall p pc i
                (PATH: path p (PState pc))
                (INS: code!pc = Some i)
                (CFG : reached f pc)
                (NOSTEP : successors_instr i = nil),
    path (pc::p) PStop.

Lemma in_set_ge : forall n s1 s2,
  in_set n s2 = true ->
  L.ge s2 s1 ->
  in_set n s1 = true.
Proof.
  intros.
  inv H0; simpl in *; auto.
  generalize H; clear H;
    case_eq (x!n); try congruence; intros.
  rewrite (H1 _ _ H); auto.
Qed.

Lemma in_set_singleton : forall n n',
  in_set n' (singleton n) = true -> n=n'.
Proof.
  unfold in_set, singleton; intros n n'.
  rewrite PTree.gsspec.
  destruct peq; auto.
  rewrite PTree.gempty; congruence.
Qed.

Lemma in_set_transfer : forall d n s,
  in_set d (transfer f n s) = true ->
  d = n \/ in_set d s = true.
Proof.
  destruct s; simpl; auto.
  rewrite PTree.gsspec; destruct peq; auto.
Qed.

Lemma compute_dom_correct_aux : 
  forall p n, path p n ->
    match n with
      | PStop => True
      | PState n =>
        forall d, in_set d mdom!!n = true -> In d p \/ d=n
    end.
Proof.
  unfold compute_dom in *.
  induction 1; simpl; intros; auto.
  exploit @DS.fixpoint_entry; eauto; intros.
  exploit in_set_ge; eauto; intros.
  exploit in_set_singleton; eauto.
  assert (L.ge mdom!!pc' (transfer f pc mdom!!pc)).
  { eapply DS.fixpoint_solution; eauto.
    intros. reflexivity. 
  }
  exploit successors_instr_succs; eauto.
  destruct 1 as [s [Hs1 Hs2]].
  
  exploit in_set_ge; eauto; intros.
  exploit in_set_transfer; eauto; destruct 1; auto.
  elim IHpath with d; auto.
Qed.

Lemma SSA_path_this_path_aux1 : forall n1 p n2,
  SSApath f n1 p n2 ->
  forall p', path p' n1 -> path (rev_append p p') n2.
Proof.
  simpl. 
  induction 1; simpl; intros; auto.
  destruct t.
  - simpl.
    inv H.
    inv STEP. inv STEP0.
    econstructor; eauto.
    destruct ((fn_code f) ! pc) eqn: Heq; unfold exit in *; rewrite Heq in *; go.
    econstructor; eauto. flatten NOSTEP; go.
  - apply IHpath.
    destruct s2.
    inv STEP. inv STEP0.
    econstructor; eauto.
    inv STEP.
    destruct ((fn_code f) ! pc) eqn: Heq; unfold exit in *; rewrite Heq in *; go.
    econstructor; eauto. flatten NOSTEP; go. 
Qed.

Lemma SSA_path_this_path : forall p n,
  SSApath f (PState entry) p n -> path (rev p) n.
Proof.
  intros.
  generalize (SSA_path_this_path_aux1 (PState entry) p n H nil).
  rewrite rev_alt; intros.
  apply H0; constructor.
Qed.

Theorem compute_dom_correct : forall n d,
  reached f n -> in_set d mdom!!n = true -> SSA.dom f d n.
Proof.
  intros.
  destruct (peq d n).
  subst; constructor.
  constructor 2; auto.
  intros.
  exploit SSA_path_this_path; eauto; intros.
  exploit compute_dom_correct_aux; eauto.
  simpl; intros.
  exploit H3; eauto.
  destruct 1; try intuition.
  rewrite in_rev; auto.
Qed.

End correctness.
