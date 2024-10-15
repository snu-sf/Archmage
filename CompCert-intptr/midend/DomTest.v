Require Import Coqlib.
Require Import Maps.
Require Import Classical.

Require Import Utils.
Require Import Relation_Operators.
Require Import Relations.Relation_Definitions.
Require Import DLib.
Require Import Dom.

Unset Allow StrictProp.

(* Will be replaced during extraction by [let rec fuel = S fuel] *)
Axiom fuel : nat.

Module Type NODE_TREE.
  Parameter node : Type.
  Parameter peq : forall x y:node, {x=y}+{x<>y}.

  Parameter tree : Type -> Type.
  Parameter get : forall {A:Type}, node -> tree A -> option A.
  Parameter set : forall {A:Type}, node -> A -> tree A -> tree A.
  Parameter empty : forall A:Type, tree A.
  Arguments get [A].
  Arguments set [A].

  Parameter gsspec:
    forall (A: Type) (i j: node) (x: A) (m: tree A),
    get i (set j x m) = if peq i j then Some x else get i m.
  Parameter gempty:
    forall (A: Type) (i: node), get i (empty A) = None.
End NODE_TREE.

Module Type INT.
  Parameter t : Type.
  Parameter int_zero : t.
  Parameter int_succ : t -> option t.
  Parameter int_le : t -> t -> Prop.
  Parameter int_lt : t -> t -> Prop.
  Parameter int_le_dec : forall (x y :t), {int_le x y}+{int_lt y x}.
  Parameter int_le_refl : forall i, int_le i i.
  Parameter int_le_trans : forall i1 i2 i3,
  int_le i1 i2 -> int_le i2 i3 -> int_le i1 i3.
  Parameter int_le_lt_trans : forall i1 i2 i3,
  int_le i1 i2 -> int_lt i2 i3 -> int_lt i1 i3.
  Parameter int_lt_le_trans : forall i1 i2 i3,
  int_lt i1 i2 -> int_le i2 i3 -> int_lt i1 i3.
  Parameter int_lt_le : forall i1 i2,
  int_lt i1 i2 -> int_le i1 i2.
  Parameter int_le_not_lt : forall i1 i2,
  int_le i1 i2 -> ~ int_lt i2 i1.
  Parameter int_lt_succ : forall i i', int_succ i = Some i' -> int_lt i i'.

  Lemma int_le_succ : forall i i', int_succ i = Some i' -> int_le i i'.
  Proof.
    auto using int_lt_le, int_lt_succ. 
  Qed.
  Global Hint Resolve int_le_refl int_le_trans int_le_lt_trans 
    int_lt_le_trans int_lt_le int_le_succ int_lt_succ: core.
End INT.

Module Make (NT:NODE_TREE) (I:INT).
Import NT I.


Section DomTestAbstract.

Variable entry: node.
Variable cfg : node -> node -> Prop.
Variable exit : node -> Prop.

Notation reached := (reached cfg entry).
Notation path := (path cfg exit entry).
Notation dom := (dom cfg exit entry).
Notation pstate := (@pstate node).

Section Dspec.

Variable D : node -> node.

(* [Dstar i] : set of D*(i) *)
Inductive Dstar : node -> node -> Prop :=
| D_refl : forall i, Dstar i i
| D_trans: forall i j
                  (TRANS: Dstar i j),
             Dstar i (D j).

Record D_spec := { 
   D_entry : D entry = entry 
;  D_cfg   : forall i j,  cfg i j -> Dstar i (D j) 
}.

Lemma Dstar_eq : forall pc, D pc = pc -> forall j, Dstar pc j -> j = pc.
Proof.
  induction 2; intros; go.
  specialize (IHDstar H).
  congruence. 
Qed.

Lemma Dstar_trans: forall a b c, 
                     Dstar a b ->
                     Dstar b c ->
                     Dstar a c.
Proof.
  induction 2 ; intros; go.
Qed.

Lemma Dstar_left: forall pc d, 
                    Dstar pc d ->
                    d = pc \/ Dstar (D pc) d.
Proof.
  induction 1 ; intros; go.
  intuition; eauto.
  - subst. right; go.
  - right; go.
Qed.
  
Inductive path' : list node -> pstate -> Prop :=
| path0: path' nil (PState entry)
| path1: forall p pc pc'
  (PATH: path' p (PState pc))
  (REACHED : reached pc)
  (CFG: cfg pc pc'), 
  path' (pc::p) (PState pc')
| path2: forall p pc 
  (PATH: path' p (PState pc))
  (REACHED : reached pc)
  (EXIT: exit pc),
  path' (pc::p) PStop.

Lemma path_path'_aux1 : forall n1 p n2,
  path n1 p n2 ->
  forall p', path' p' n1 -> path' (rev_append p p') n2.
Proof.
  induction 1; simpl; intros; auto.
  destruct t0.
  - simpl. inv H. inv STEP; go.
  - apply IHpath. 
    destruct s2; inv STEP; go.
Qed.

Lemma path_path' : forall p n,
  path (PState entry) p n -> path' (rev p) n.
Proof.
  intros.
  generalize (path_path'_aux1 (PState entry) p n H nil).
  rewrite rev_alt; intros.
  apply H0; constructor.
Qed.

Lemma D_eq_correct_aux :
  D_spec ->
  forall i p, path' p i ->
                 match i with 
                     | PStop => True
                     | PState n =>
                       (forall d, Dstar (D n) d -> In d p) \/ D n = n
                 end.
Proof.
  intros EQ.
  induction 1; intros; go.
  - exploit D_entry; eauto. 
  - destruct IHpath' as [IHpath'| IHpath'].
    + exploit D_cfg; eauto. 
      intros Hcase.
      eapply Dstar_left in Hcase; eauto.  
      { destruct Hcase as [Hcase' | Hcase'].
        - left. intros. 
          eapply Dstar_left in H0. invh or; go.
        - exploit  IHpath'; eauto. intros Hin.
          left. intros.
          exploit (Dstar_trans (D pc) (D pc') d); eauto.
      }            
    + exploit D_cfg; eauto. 
      intros Hcase.
      left. intros.
      exploit Dstar_eq; eauto.
      intros Heq. rewrite Heq in *. 
      exploit Dstar_eq; eauto. go.
Qed.
    
Lemma D_spec_correct :
  D_spec ->
  forall i j, Dstar i j -> reached i ->  dom j i.
Proof.
  intros EQ i j DSTAR REACHED.
  destruct (classic (dom j i)) as [? | Hcont]; auto.
  exploit (@not_dom_path_wo node peq); eauto. intros (p & Hp & Hnotin).
  eapply path_path' in Hp.
  exploit D_eq_correct_aux; eauto. simpl.
  intros HOK. inv HOK.
  - eapply Dstar_left in DSTAR; eauto.
    inv DSTAR; go.
    eelim Hnotin; eauto. 
    eapply in_rev; eauto. 
  - exploit Dstar_eq; eauto. intros Heq; rewrite Heq.
    econstructor; eauto.
Qed.

End Dspec.

Section DomTestImplem.

Definition sons_map : Type := tree (list node).

Definition sons (s:sons_map) (n:node) : list node :=
  match get n s with
    | Some l => l
    | None => nil
  end.

Record itv := { pre: t; post: t }.

Section sons.
Variable sons : node -> list node.

Record state := { itvm: tree itv; next: t }.

Fixpoint build_itv_rec (n:node) (st:state) (fuel:nat) : option state :=
  match fuel with
    | O => None
    | S fuel =>
      match int_succ st.(next) with 
        | None => None
        | Some next' =>
          let pre_n := st.(next) in
          match
            fold_left (fun ost s => 
                         match ost with
                           | None => None
                           | Some st => build_itv_rec s st fuel
                         end) 
                      (sons n)
                      (Some {| itvm := st.(itvm); next := next' |}) 
          with
            | None => None
            | Some st => 
              let itv_n := {| pre := pre_n; post := st.(next) |} in
              match int_succ st.(next) with 
                | None => None
                | Some next' =>
                  Some {| itvm := set n itv_n st.(itvm); next := next' |}
              end
          end
      end
  end.

Definition build_itv : option state :=
  build_itv_rec entry {| itvm := empty _; next := int_zero |} (S fuel).

Inductive InSubTree (r:node) : node -> Prop :=
| InSubTree_root: InSubTree r r
| InSubTree_sons: forall n s
  (IT: InSubTree s n)
  (IS: In s (sons r)),
  InSubTree r n.

Unset Elimination Schemes.
Inductive NoRepetTreeN (r:node) : nat -> Prop :=
| NoRepetTreeN0: NoRepetTreeN r O
| NoRepetTreeN_sons: forall k
  (NTR1: forall s, In s (sons r) -> NoRepetTreeN s k)
  (NTR2: forall s, In s (sons r) -> ~ InSubTree s r)
  (NTR3: forall s1 s2 n, 
           In s1 (sons r) -> InSubTree s1 n ->
           In s2 (sons r) -> InSubTree s2 n -> s1=s2)
  (NTR4: list_norepet (sons r)),
  NoRepetTreeN r (S k).
Set Elimination Schemes.

Definition itv_Incl (i1 i2:itv) : Prop :=
  int_le i2.(pre) i1.(pre) /\ int_le i1.(post) i2.(post).

Lemma fold_build_itv_rec_None : forall k l,
        fold_left
          (fun (ost : option state) (s0 : node) =>
             match ost with
               | Some st0 => build_itv_rec s0 st0 k
               | None => None
             end) l None = None.
Proof.
  induction l; simpl; auto. 
Qed.

Lemma build_itv_rec_prop0 : forall k n0 st st',
  build_itv_rec n0 st k = Some st' ->
  int_le st.(next) st'.(next).
Proof.
  induction k; simpl; intros n0 st st' Heq; try congruence.
  flatten Heq; simpl.
  assert (
      forall l st st',
        fold_left
          (fun (ost : option state) (s0 : node) =>
             match ost with
               | Some st0 => build_itv_rec s0 st0 k
               | None => None
             end) l (Some st) = Some st' -> int_le (next st) (next st')).
  { clear Eq; induction l; simpl; intros st1 st2 Hs.
    - inv Hs; apply int_le_refl.
    - destruct (build_itv_rec a st1 k) eqn:E.
      + apply IHl in Hs.
        apply IHk in E.
        eauto.
      + rewrite fold_build_itv_rec_None in Hs; congruence. }
  apply H in Eq0.
  simpl in Eq0.
  eauto. 
Qed.

Lemma fold_build_itv_rec_prop0 : forall k l st st',
        fold_left
          (fun (ost : option state) (s0 : node) =>
             match ost with
               | Some st0 => build_itv_rec s0 st0 k
               | None => None
             end) l (Some st) = Some st' ->
  int_le st.(next) st'.(next).
Proof.
  induction l; simpl.
  - intros.
    inv H; go.
  - intros.
    destruct (build_itv_rec a st k) eqn:E.
    + apply IHl in H.
      generalize (build_itv_rec_prop0 _ _ _ _ E).
      eauto.
    + rewrite fold_build_itv_rec_None in H; congruence. 
Qed.

Lemma build_itv_rec_prop1 : forall k n0 st st',
  build_itv_rec n0 st k = Some st' ->
  forall n, get n st.(itvm) = get n st'.(itvm) \/ InSubTree n0 n.
Proof.
  induction k; simpl; intros n0 st st' Heq; try congruence.
  flatten Heq; simpl.
  rewrite gsspec; flatten.
  - subst; go.
  - assert (
      forall l st st',
        incl l (sons n0) ->
        fold_left
          (fun (ost : option state) (s0 : node) =>
             match ost with
               | Some st0 => build_itv_rec s0 st0 k
               | None => None
             end) l (Some st) = Some st' -> 
        get n (itvm st) = get n (itvm st') \/ InSubTree n0 n).
  { clear Eq; induction l; simpl; intros st1 st2 Hi Hs.
    - inv Hs; go.
    - destruct (build_itv_rec a st1 k) eqn:E.
      + apply IHl in Hs; eauto with datatypes.
        destruct Hs; auto.
        rewrite <- H.
        destruct (IHk _ _ _ E n); go.
      + rewrite fold_build_itv_rec_None in Hs; congruence. }
  apply H in Eq0; auto with datatypes.
Qed.

Lemma fold_build_itv_rec_prop1 : forall k l st st',
        fold_left
          (fun (ost : option state) (s0 : node) =>
             match ost with
               | Some st0 => build_itv_rec s0 st0 k
               | None => None
             end) l (Some st) = Some st' ->
  forall n, get n st.(itvm) = get n st'.(itvm) \/ 
     exists n0, In n0 l /\ InSubTree n0 n.
Proof.
  induction l; simpl.
  - go.
  - intros.
    destruct (build_itv_rec a st k) eqn:E.
    + destruct (IHl _ _ H n).
      * rewrite <- H0.
        destruct (build_itv_rec_prop1 _ _ _ _ E n); auto.
        go.
      * destruct H0 as (n0 & N1 & N2); go.
    +  rewrite fold_build_itv_rec_None in H; congruence. 
Qed.


Lemma build_itv_rec_prop2 : forall it k n0 st st' n,
  build_itv_rec n0 st k = Some st' ->
  NoRepetTreeN n0 k ->
  InSubTree n0 n ->
  get n st'.(itvm) = Some it ->
  int_le st.(next) it.(pre) /\ int_lt it.(post) st'.(next).
Proof.
  induction k; simpl; intros n0 st st' n Heq Hnr HIn Hit; try congruence.
  flatten Heq.
  inv Hit.
  rewrite gsspec in H0; flatten H0; simpl.
  - split.
    + apply int_le_refl.
    + apply int_lt_succ; auto.
  - inv HIn; try congruence.
    assert (Hfold1: forall l st st' i0,
              list_norepet l ->
              (forall s1 s2 n, 
                       In s1 l -> InSubTree s1 n ->
                       In s2 l -> InSubTree s2 n -> s1=s2) ->
              fold_left
                (fun ost s =>
                   match ost with
                     | Some st => build_itv_rec s st k
                     | None => None
                   end) l (Some st) = Some st' ->
              forall s0, In s0 l -> InSubTree s0 n -> 
                         NoRepetTreeN s0 k ->
                         get n (itvm st') = Some it ->
                         int_succ (next st') = Some i0 ->
                         int_le (next st) (pre it) /\ int_lt (post it) i0).
    { clear IT IS Eq H0.
      induction l; simpl.
      - intuition.
      - intros st1 st2 i1 Hn Hd Hf s1.
        destruct (build_itv_rec a st1 k) as [st0|] eqn:E;
          [idtac|rewrite fold_build_itv_rec_None in Hf; congruence].
        destruct 1; subst; intros Hi Hno Hitv.
        + destruct (fold_build_itv_rec_prop1 _ _ _ _ Hf n).
          * rewrite <- H in Hitv.
            exploit IHk; eauto.
            apply fold_build_itv_rec_prop0 in Hf.
            destruct 1; split; eauto.
          * destruct H as (n2 & N1 & N2).
            assert (s1=n2).
            { apply Hd with n; auto. }
            inv Hn; intuition.
        + apply build_itv_rec_prop0 in E.
          intros.
          assert (HT:int_le (next st0) (pre it) /\ int_lt (post it) i1).
          { inv Hn; eapply IHl; eauto. }          
          destruct HT; split; eauto. }
    inv Hnr; exploit Hfold1; eauto.
    simpl.
    destruct 1; eauto.
Qed.

Lemma fold_build_itv_rec_prop2: forall k n it l st st',
              list_norepet l ->
              (forall s1 s2 n, 
                       In s1 l -> InSubTree s1 n ->
                       In s2 l -> InSubTree s2 n -> s1=s2) ->
              fold_left
                (fun ost s =>
                   match ost with
                     | Some st => build_itv_rec s st k
                     | None => None
                   end) l (Some st) = Some st' ->
              forall s0, In s0 l -> InSubTree s0 n -> 
                         NoRepetTreeN s0 k ->
                         get n (itvm st') = Some it ->
                         int_le (next st) (pre it) /\ int_lt (post it) (next st').
Proof.
  induction l; simpl.
  - intuition.
  - intros st1 st2 Hn Hd Hf s1.
    destruct (build_itv_rec a st1 k) as [st0|] eqn:E;
      [idtac|try rewrite fold_build_itv_rec_None in Hf; try congruence].
    destruct 1; subst; intros Hi Hno Hitv.
    + destruct (fold_build_itv_rec_prop1 _ _ _ _ Hf n).
      * rewrite <- H in Hitv.
        exploit build_itv_rec_prop2; eauto.
        apply fold_build_itv_rec_prop0 in Hf.
        destruct 1; split; eauto.
      * destruct H as (n2 & N1 & N2).
        assert (s1=n2).
        { apply Hd with n; auto. }
        inv Hn; intuition.
    + apply build_itv_rec_prop0 in E.
      assert (HT:int_le (next st0) (pre it) /\ int_lt (post it) (next st2)).
      { inv Hn; eapply IHl; eauto. }          
      destruct HT; split; eauto. 
Qed.

(* TODO : build a nice induction principle 
Lemma build_itv_rec_ind : forall (R:node->state->state->Prop),
   ....
  forall k n st st', build_itv_rec n st k = Some st' -> R n st st'.
*)

Lemma build_itv_rec_prop4 : forall k n0 st st',
  build_itv_rec n0 st k = Some st' ->
  int_lt st.(next) st'.(next).
Proof.
  induction k; simpl; intros n0 st st' Heq; try congruence.
  flatten Heq.
  simpl.
  assert (Hfold1: forall l st st',
              fold_left
                (fun ost s =>
                   match ost with
                     | Some st => build_itv_rec s st k
                     | None => None
                   end) l (Some st) = Some st' ->
              int_le (next st) (next st')).
  { induction l; simpl.
    - intros.
      inv H; auto.
    - intros.
      destruct (build_itv_rec a st0 k) eqn:E.
      + apply IHl in H.
        apply IHk in E.
        eauto.
      + rewrite fold_build_itv_rec_None in H; congruence. }
  apply Hfold1 in Eq0.
  simpl in Eq0.
  eauto.
Qed.

Lemma fold_build_itv_rec_prop4 : forall k l st st',
              fold_left
                (fun ost s =>
                   match ost with
                     | Some st => build_itv_rec s st k
                     | None => None
                   end) l (Some st) = Some st' ->
              int_le (next st) (next st').
Proof.
  induction l; simpl; intros.
  - inv H; auto.
  - destruct (build_itv_rec a st k) eqn:E.
    + apply IHl in H.
      apply build_itv_rec_prop4 in E.
      eauto.
    + rewrite fold_build_itv_rec_None in H; congruence. 
Qed.

Lemma build_itv_rec_prop5 : forall k it n0 st st' n,
  build_itv_rec n0 st k = Some st' ->
  (forall it, get n (itvm st) = Some it -> int_lt it.(pre) it.(post)) ->
  get n st'.(itvm) = Some it ->
  int_lt it.(pre) it.(post).
Proof.
  induction k; simpl; intros it n0 st st' n Heq Hold Hit; try congruence.
  flatten Heq.
  inv Hit.
  rewrite gsspec in H0; flatten H0; simpl.
  - apply fold_build_itv_rec_prop4 in Eq0.
    simpl in Eq0; eauto.
  - assert (Hfold1: forall l st st',
              fold_left
                (fun ost s =>
                   match ost with
                     | Some st => build_itv_rec s st k
                     | None => None
                   end) l (Some st) = Some st' ->
              (forall it, get n (itvm st) = Some it -> int_lt it.(pre) it.(post)) ->
               get n (itvm st') = Some it ->
               int_lt it.(pre) it.(post)).
    { clear Eq H0.
      induction l; simpl.
      - intros.
        inv H; auto.
      - intros st1 st2 Hf Hold' Hn.
        destruct (build_itv_rec a st1 k) as [st0|] eqn:E;
          [idtac|rewrite fold_build_itv_rec_None in Hf; congruence].
        apply IHl in Hf; auto.
        intros; eapply IHk with (1:=E); eauto. }
    apply Hfold1 in Eq0; eauto.
Qed.

Lemma fold_build_itv_rec_prop5 : forall l k st st' it n,
              fold_left
                (fun ost s =>
                   match ost with
                     | Some st => build_itv_rec s st k
                     | None => None
                   end) l (Some st) = Some st' ->
              (forall it, get n (itvm st) = Some it -> int_lt it.(pre) it.(post)) ->
               get n (itvm st') = Some it ->
               int_lt it.(pre) it.(post).
Proof.
  induction l; simpl.
  - intros.
    inv H; auto.
  - intros k st1 st2 it n Hf Hn.
    destruct (build_itv_rec a st1 k) as [st0|] eqn:E;
          [idtac|rewrite fold_build_itv_rec_None in Hf; congruence].
    intros.
    eapply IHl in Hf; eauto.
    intros; eapply build_itv_rec_prop5 with (1:=E); eauto. 
Qed.

Lemma fold_build_itv_rec_prop6: forall k n1 n2 it1 it2 l st st',
     list_norepet l ->
     (forall s1 s2 n, 
              In s1 l -> InSubTree s1 n ->
              In s2 l -> InSubTree s2 n -> s1=s2) ->
     (forall n it, get n (itvm st) = Some it -> int_lt it.(pre) it.(post)) ->
     fold_left
       (fun ost s =>
          match ost with
            | Some st => build_itv_rec s st k
            | None => None
          end) l (Some st) = Some st' ->
     forall s1 s2, 
       In s1 l -> 
       InSubTree s1 n1 -> 
       NoRepetTreeN s1 k ->
       get n1 (itvm st') = Some it1 ->
       In s2 l -> 
       InSubTree s2 n2 -> 
       NoRepetTreeN s2 k ->
       get n2 (itvm st') = Some it2 ->
       itv_Incl it1 it2 -> s1=s2.
Proof.
  induction l; simpl.
  - intuition.
  - intros st st' H H0 Hlt H1 s1 s2 Hin1 Hst1 Hnr1 Hit1 Hin2 Hst2 Hnr2 Hit2 Hin.
    destruct (build_itv_rec a st k) as [st0|] eqn:E.
    + destruct Hin1; destruct Hin2; try congruence; subst.
      * assert (int_le st.(next) it1.(pre) /\ int_lt it1.(post) st0.(next)).
        { eapply build_itv_rec_prop2; eauto.
          exploit fold_build_itv_rec_prop1; eauto.
          destruct 1 as [He|(n4 & Hi1 & He)]; [rewrite He; auto|idtac].
          assert (s1=n4) by (eapply H0; eauto).
          inv H; intuition. }
        assert (int_le st0.(next) it2.(pre) /\ int_lt it2.(post) st'.(next)).
        { eapply fold_build_itv_rec_prop2 with (3:=H1); eauto.
          - inv H; auto.  }
        destruct Hin; destruct H2; destruct H4.
        assert (int_lt it1.(pre) it1.(post)). 
        { eapply fold_build_itv_rec_prop5; eauto.
          intros; eapply build_itv_rec_prop5; eauto. }
        assert (int_lt (next st0) (post it1)) by eauto.
        eelim int_le_not_lt; eauto.
      * assert (int_le st.(next) it2.(pre) /\ int_lt it2.(post) st0.(next)).
        { eapply build_itv_rec_prop2; eauto.
          exploit fold_build_itv_rec_prop1; eauto.
          destruct 1 as [He|(n4 & Hi1 & He)]; [rewrite He; auto|idtac].
          assert (s2=n4) by (eapply H0; eauto).
          inv H; intuition. }
        assert (int_le st0.(next) it1.(pre) /\ int_lt it1.(post) st'.(next)).
        { eapply fold_build_itv_rec_prop2 with (3:=H1); eauto.
          inv H; auto. }         
        destruct Hin; destruct H3; destruct H4.
        assert (int_lt it1.(pre) it1.(post)). 
        { eapply fold_build_itv_rec_prop5; eauto.
          intros; eapply build_itv_rec_prop5; eauto. }
        assert (int_lt (next st0) (post it2)) by eauto.
        eelim int_le_not_lt; eauto.
      * { apply IHl with st0 st'; eauto.
          - inv H; auto.
          - intros; eapply build_itv_rec_prop5; eauto. }
    + rewrite fold_build_itv_rec_None in H1; congruence.
Qed.

Lemma fold_build_itv_rec_prop7: forall k l st st',
    list_norepet l ->
    (forall s1 s2 n, 
             In s1 l -> InSubTree s1 n ->
             In s2 l -> InSubTree s2 n -> s1=s2) ->
    (forall n it, get n (itvm st) = Some it -> int_lt it.(pre) it.(post)) ->
    fold_left
      (fun ost s =>
         match ost with
           | Some st => build_itv_rec s st k
           | None => None
         end) l (Some st) = Some st' ->
    forall s0, In s0 l ->
               exists st0 st0',
               build_itv_rec s0 st0 k = Some st0' /\
               (forall n it, get n (itvm st0) = Some it -> int_lt it.(pre) it.(post)) /\
               forall n, InSubTree s0 n -> 
                         get n st0'.(itvm) = get n st'.(itvm).
Proof.
  induction l; simpl.
  - intuition.
  - intros st1 st2 Hn Hd Hi Hf s0.
    destruct (build_itv_rec a st1 k) as [st0|] eqn:E;
      [idtac|rewrite fold_build_itv_rec_None in Hf; congruence].
    destruct 1; subst.
    + econstructor; econstructor; split; [eauto|split; eauto].
      intros.
      exploit fold_build_itv_rec_prop1; eauto.
      destruct 1 as [T|(n0 & Hii & T)]; [exact T|idtac].
      assert (n0=s0) by eauto.
      inv Hn; intuition.
    + edestruct IHl with st0 st2 s0 as (st3 & st3' & S1 & S2); eauto.
      * inv Hn; auto.
      * intros; eapply build_itv_rec_prop5; eauto.
Qed.

Lemma build_itv_rec_prop7 : forall k n0 st st' n1 n2 it2 it1,
  build_itv_rec n0 st k = Some st' ->
  (forall n it, get n (itvm st) = Some it -> int_lt it.(pre) it.(post)) ->
  NoRepetTreeN n0 k ->
  InSubTree n0 n1 ->
  InSubTree n0 n2 ->
  get n1 st'.(itvm) = Some it1 ->
  get n2 st'.(itvm) = Some it2 ->
  itv_Incl it1 it2 -> InSubTree n2 n1.  
Proof.
  induction k; simpl; try congruence.
  intros n0 st st' n1 n2 it2 it1. 
  flatten.
  intros Hs Hit Hnr Hi1 Hi2 Hit1 Hit2 Hin; inv Hs; simpl in *.
  rewrite gsspec in Hit2.
  flatten Hit2; auto.
  rewrite gsspec in Hit1.
  flatten Hit1.
  - simpl in *.
    inv Hi2; try (elim n; congruence).
    inv Hnr.
    destruct fold_build_itv_rec_prop2 with (3:=Eq0) (s0:=s0) (7:=Hit2); auto.
    destruct Hin; simpl in *.
    eelim int_le_not_lt; eauto.
  - inv Hi2; try (elim n; congruence).
    inv Hi1; try (elim n; congruence).
    assert (s1=s0).
    { inv Hnr.
      eapply fold_build_itv_rec_prop6 with (4:=Eq0); eauto. }
    subst.
    inv Hnr.
    edestruct fold_build_itv_rec_prop7 with (4:=Eq0) (5:=IS) as (st0 & st0' & S1 & S2 & S3);
      eauto.
    rewrite <- S3 in Hit1; auto.
    rewrite <- S3 in Hit2; auto.
    eauto.
Qed.

Lemma build_itv_correct : 
  NoRepetTreeN entry (S fuel) ->
  forall st, build_itv = Some st ->
  forall n1 n2 itv1 itv2,
    get n1 st.(itvm) = Some itv1 ->
    get n2 st.(itvm) = Some itv2 ->
    itv_Incl itv1 itv2 -> InSubTree n2 n1.
Proof.
  intros Hn st Heq n1 n2 itv1 itv2 Hi1 Hi2 Hin.
  unfold build_itv in *.
  apply build_itv_rec_prop7 with (1:=Heq) (6:=Hi1) (7:=Hi2); auto.
  - simpl.
    intros nit; rewrite gempty; congruence.
  - generalize Hi1.
    exploit build_itv_rec_prop1; eauto.
    destruct 1 as [T|T]; 
      [rewrite <- T; simpl; rewrite gempty; congruence|auto].
  - generalize Hi2.
    exploit build_itv_rec_prop1; eauto.
    destruct 1 as [T|T]; 
      [rewrite <- T; simpl; rewrite gempty; congruence|auto].
Qed.

End sons.

Definition build_itv_map (sn:tree (list node)) : option (tree itv) :=
  match build_itv (sons sn) with
    | None => None
    | Some st => Some st.(itvm)
  end.

Theorem build_itv_map_correct : forall (sn:tree (list node)),
  NoRepetTreeN (sons sn) entry (S fuel) ->
  forall itvm, build_itv_map sn = Some itvm ->
  forall n1 n2 itv1 itv2,
    get n1 itvm = Some itv1 ->
    get n2 itvm = Some itv2 ->
    itv_Incl itv1 itv2 -> InSubTree (sons sn) n2 n1.
Proof.
  intros.
  unfold build_itv_map in *.
  flatten H0.
  eapply build_itv_correct; eauto.
Qed.

Definition in_set (n:node) (s:tree unit) : bool :=
  match get n s with
    | None => false
    | Some _ => true
  end.

Definition add_set (n:node) (s:tree unit) : tree unit :=
  set n tt s.

Definition build_succs_list D seen m :=
  fold_left
    (fun st (nd:node*node) => 
       match st with
         | None => None
         | Some (seen, sm) =>
           let (n,d) := nd in
           if peq n d then None
           else if in_set d seen && negb (in_set n seen)
                then Some (add_set n seen, set d (n :: sons sm d) sm)
                else None
       end)
    D
    (Some (seen,m)).

Lemma NoRepetTreeN_S_k_k : forall sons k s,
  NoRepetTreeN sons s (S k) ->
  NoRepetTreeN sons s k.
Proof.
  induction k; intros; go.
  inv H; econstructor; eauto.
Qed.
Hint Resolve NoRepetTreeN_S_k_k: core.


Lemma sons_set : forall s0 s n m,
  sons (set s0 (n :: sons m s0) m) s =
  if peq s0 s then n :: sons m s else sons m s.
Proof.
  unfold sons; intros.
  rewrite gsspec; flatten.
Qed.

Lemma In_sons_set : forall s0 p n m s,
  In s0 (sons (set p (n :: sons m p) m) s)
  -> 
  ( In s0 (sons m s)
   \/
    (s0=n /\ s=p)).
Proof.
  intros.
  rewrite sons_set in H.
  flatten H; auto.
  destruct H; go.
Qed.

Lemma InSubTree_sons_nil : forall m n p,
  InSubTree (sons m) n p -> sons m n = nil -> n=p.
Proof.
  induction 1; auto.
  intros E; rewrite E in IS; elim IS.
Qed.

Lemma InSubTree_add : forall m p s0 s n,
  (forall s, InSubTree (sons m) s s0 -> s=s0) ->
  InSubTree (sons (set p (s0 :: sons m p) m)) s n ->
  sons m s0 = nil ->
  InSubTree (sons m) s n \/ (n = s0 /\ InSubTree (sons m) s p).
Proof.
  intros m p s0 s n Hn Hin Hd.
  induction Hin; go.
  apply In_sons_set in IS.
  destruct IS as [IS|(? & ?)]; subst.
  - destruct IHHin as [HHin|(? & HHin)]; subst; go.
  - destruct IHHin as [HHin|(? & HHin)]; subst; go.
    exploit InSubTree_sons_nil; eauto.
    go.
Qed.

Lemma add_NoRepetTree: forall k p m n,
  (forall s, InSubTree (sons m) s n -> s=n) ->
  sons m n = nil ->
  p<>n ->
  (forall s, NoRepetTreeN (sons m) s k) ->
  forall s, NoRepetTreeN (sons (set p (n :: sons m p) m)) s k.
Proof.
  induction k; intros p m n Hi Hnil Hd Hnr s.
  - go.
  - constructor.
    + intros s0 Hi0; apply IHk; auto. 
    + intros s0 Hii. 
      apply In_sons_set in Hii.
      specialize Hnr with s; inv Hnr.
      intros His.      
      apply InSubTree_add in His; auto.
      destruct Hii as [|(Hii1 & Hii2)]; destruct His as [|(His1 & His2)]; subst.
      * eelim NTR2; eauto.
      * rewrite Hnil in H; inv H.
      * exploit InSubTree_sons_nil; eauto.
      * congruence.
    + intros s1 s2 n0 His1 Hin1 His2 Hin2.
      apply In_sons_set in His1.
      apply In_sons_set in His2.
      apply InSubTree_add in Hin1; auto.
      apply InSubTree_add in Hin2; auto.
      specialize Hnr with s; inv Hnr.
      destruct His1 as [His1|(His1 & His1')]; 
      destruct His2 as [His2|(His2 & His2')]; try congruence.
      * { destruct Hin1 as [Hin1|(Hin1 & Hin1')]; subst.
          - destruct Hin2 as [Hin2|(Hin2 & Hin2')]; subst.
            + eauto.
            + assert (s1=n) by eauto.
              clear Hin1; subst.
              assert (s=n) by (apply Hi; go).
              subst; rewrite Hnil in His2; elim His2.
          - destruct Hin2 as [Hin2|(Hin2 & Hin2')]; subst.
            + assert (s2=n) by eauto.
              clear Hin2; subst.
              assert (s=n) by (apply Hi; go).
              subst; rewrite Hnil in His2; elim His2.
            + eauto. }              
      * subst.
        { destruct Hin2 as [|(Hin2 & Hin2')]; subst.
          - exploit InSubTree_sons_nil; eauto.
            intros; subst.
            destruct Hin1 as [|(Hin1 & Hin1')]; auto.
            eelim NTR2; eauto.
          - exploit InSubTree_sons_nil; eauto.
            intuition. }
      * subst.
        { destruct Hin1 as [|(Hin1 & Hin1')]; subst.
          - exploit InSubTree_sons_nil; eauto.
            intros; subst.
            symmetry; destruct Hin2 as [|(Hin2 & Hin2')]; auto.
            eelim NTR2; eauto.
          - exploit InSubTree_sons_nil; eauto.
            intuition. }
    + rewrite sons_set.
      specialize Hnr with s; inv Hnr.
      flatten; auto.
      subst.
      constructor; auto.
      intro; elim Hd; apply Hi.
      go.
Qed.

Unset Elimination Schemes.
Inductive topo_sorted : list (node*node) -> Prop :=
 | topo_sorted_nil: topo_sorted nil
 | topo_sorted_cons: forall n d l
   (TS1: topo_sorted l)
   (TS2: forall d', ~ In (d,d') l),
   topo_sorted ((n,d)::l).
Set Elimination Schemes.

Lemma build_succs_list_none : forall l,
  fold_left
    (fun (st : option (tree unit * sons_map)) (nd : node * node) =>
       match st with
         | Some (seen, sm) =>
           let (n, d) := nd in
           if peq n d
           then None
           else
             if in_set d seen && negb (in_set n seen)
             then Some (add_set n seen, set d (n :: sons sm d) sm)
             else None
         | None => None
       end) l None = None.
Proof.
  induction l; simpl; go.
Qed.

Lemma build_succs_list_no_repet_aux: forall k l seen m seen' m',
  (forall n, NoRepetTreeN (sons m) n k) ->
  list_norepet (map fst l) ->
  (forall n d, In (n,d) l -> forall s, InSubTree (sons m) s n -> s=n) ->
  (forall n d, In (n,d) l -> sons m n = nil) ->
  (forall n d, In (n,d) l -> d<>n) ->
  topo_sorted l ->
  build_succs_list l seen m = Some (seen',m') ->
  (forall n, NoRepetTreeN (sons m') n k).
Proof.
  induction l; simpl; 
  intros seen m seen' m' Hn Hln Hd Hnil Hdiff Hs Heq n.
  inv Heq; auto.
  destruct a as (s,p); simpl in *.
  unfold build_succs_list in Heq.
  simpl in Heq.
  flatten Heq; try (rewrite build_succs_list_none in *; congruence).
  eapply IHl with (7:=Heq); clear IHl.
  - apply add_NoRepetTree; eauto.
  - inv Hln; auto.
  - intros.
    destruct InSubTree_add with (2:=H0); eauto.
    destruct H1; subst.
    inv Hln.
    elim H4.
    replace s with (fst (s,d)) by auto.
    apply in_map; auto.
  - intros n1 d Hin.
    rewrite sons_set.
    inv Hs; flatten; subst; eauto.
    eelim TS2; eauto.
  - eauto.
  - inv Hs; auto.
Qed.

Lemma sons_ptree_empty : forall n,
  sons (empty (list node)) n = nil.
Proof.
  simpl; intros n.
  unfold sons. 
  rewrite gempty.
  auto.
Qed.

Definition build_succs (D:list (node*node)) : option (tree (list node)) := 
  let seen := set entry tt (empty _) in
  match build_succs_list D seen (empty _) with
      | None => None
      | Some (_,sn) => Some sn
  end.

Lemma build_succs_list_Some_list_norepet : forall l seen m seen' m',
  build_succs_list l seen m = Some (seen',m') ->
  list_norepet (map fst l) /\ (forall n d, In (n,d) l -> get n seen = None) /\
  topo_sorted l.
Proof.
  unfold build_succs_list; induction l; simpl.
  repeat split; go.
  intros seen m seen' m' Hes.
  flatten Hes; try (rewrite build_succs_list_none in *; congruence).
  exploit IHl; eauto.
  intros (IH1 & IH2 & IH3); clear IHl.
  repeat split.
  - constructor; auto.
    simpl.
    intro.
    exploit list_in_map_inv; eauto.
    intros ((n',d) & E1 & E2); subst.
    exploit IH2; eauto.
    simpl; unfold add_set; rewrite gsspec; flatten.
  - intros n2 d; destruct 1.
    * inv H.
      apply andb_prop in Eq0.
      destruct Eq0; unfold in_set in *.
      flatten H0.
      inv H0.
    * exploit IH2; eauto.
      unfold add_set; rewrite gsspec; flatten.
  - constructor; auto.
    intros d' Hin.
    exploit IH2; eauto.
    unfold add_set.
    rewrite gsspec; flatten.
    apply andb_prop in Eq0.
    destruct Eq0; unfold in_set in *.
    flatten H.
Qed.

Lemma build_succs_Some_list_norepet : forall l m,
  build_succs l = Some m -> list_norepet (map fst l).
Proof.
  unfold build_succs; intros.
  flatten H.
  apply build_succs_list_Some_list_norepet in Eq.
  intuition.
Qed.

Lemma build_succs_Some_topo_sorted : forall l m,
  build_succs l = Some m -> topo_sorted l.
Proof.
  unfold build_succs; intros.
  flatten H.
  apply build_succs_list_Some_list_norepet in Eq.
  intuition.
Qed.

Lemma build_succs_list_Some_diff : forall l seen m seen' m',
  build_succs_list l seen m = Some (seen',m') ->
  forall n d, In (n,d) l -> d<>n.
Proof.
  unfold build_succs_list; induction l; simpl; go.
  intros seen m seen' m' Hes.
  flatten Hes; try (rewrite build_succs_list_none in *; congruence).
  intros n2 d H.
  destruct H.
  - inv H; auto.
  - eapply IHl; eauto.
Qed.

Lemma build_succs_Some_diff : forall l m,
  build_succs l = Some m -> 
  forall n d, In (n,d) l -> d<>n.
Proof.
  unfold build_succs; intros.
  flatten H.
  eapply build_succs_list_Some_diff; eauto.
Qed.

Theorem build_succs_no_repet : forall D sn,
  build_succs D = Some sn ->
  NoRepetTreeN (sons sn) entry (S fuel).
Proof.
  intros D0 sn; unfold build_succs.
  flatten.
  intros T; inv T.
  exploit build_succs_list_no_repet_aux; eauto.
  - intros n; econstructor; intros; rewrite sons_ptree_empty in *; 
    simpl in *; intuition.
    constructor.
  - eapply build_succs_Some_list_norepet.
    unfold build_succs.
    rewrite Eq; eauto.
  - intros n d H s Hi.
    inv Hi; auto.
    rewrite sons_ptree_empty in *.
    elim IS.
  - intros; rewrite sons_ptree_empty; auto.
  - eapply build_succs_Some_diff; eauto.
    unfold build_succs.
    rewrite Eq; eauto.
  - eapply build_succs_Some_topo_sorted.
    unfold build_succs.
    rewrite Eq; eauto.
Qed.

Definition itv_incl (i1 i2:itv) : bool :=
  if int_le_dec i2.(pre) i1.(pre) then
    if int_le_dec i1.(post) i2.(post) then true
    else false
  else false.

Lemma itv_incl_spec : forall i1 i2,
  itv_incl i1 i2 = true -> itv_Incl i1 i2.
Proof.
  unfold itv_incl, itv_Incl.
  intros i1 i2; flatten.
  go.
Qed.

Definition is_ancestor (itvm: tree itv) (n1 n2:node) : bool :=
  match get n1 itvm, get n2 itvm with
    | Some itv1, Some itv2 => itv_incl itv2 itv1
    | _, _ => false
  end.

Definition tree_from_assoc (l:list (node*node)) : tree node :=
  fold_left (fun m nd => set (fst nd) (snd nd) m) l (empty _).

Lemma tree_from_assoc_aux2 : forall l m (n d:node),
  get n m = Some d ->
  (forall d, ~ In (n,d) l) ->
  get n (fold_left (fun m nd => set (fst nd) (snd nd) m) l m) = Some d.
Proof.
  induction l; simpl; auto.
  intros m n d Hm Hi.
  apply IHl.
  - destruct a; simpl.
    rewrite gsspec; flatten.
    subst; eelim Hi; eauto.
  - intros d0 Hi0.
    elim Hi with d0; auto.
Qed.

Lemma tree_from_assoc_aux3 : forall l m (n d:node),
  In (n,d) l ->
  list_norepet (map fst l) ->
  get n (fold_left (fun m nd => set (fst nd) (snd nd) m) l m) = Some d.
Proof.
  induction l; simpl; intuition.
  - inv H0.
    apply tree_from_assoc_aux2.
    + simpl.
      inv H1. rewrite gsspec; flatten.
    + inv H1.
      intros d' Hi; elim H3.
      replace n with (fst (n,d')); auto.
      apply in_map; auto.
  - apply IHl; auto.
    inv H0; auto.
Qed.

Lemma tree_from_assoc_prop2 : forall l,
  list_norepet (map fst l) ->
  forall n d,
    In (n,d) l ->
    get n (tree_from_assoc l) = Some d.
Proof.
  unfold tree_from_assoc; intros.
  apply tree_from_assoc_aux3; auto.
Qed.


Definition make_D_fun (l:list (node*node)) : node -> node :=
  let m := tree_from_assoc l in
  (fun n => match get n m with
              | None => n
              | Some d => d
            end).

Lemma build_succs_list_Some_tree : forall l seen m seen' m',
  build_succs_list l seen m = Some (seen',m') ->
  forall i j,
    In j (sons m' i) -> In (j,i) l \/ In j (sons m i).
Proof.
  unfold build_succs_list; induction l; simpl;
  intros seen m seen' m' Hes.
  inv Hes; auto.
  flatten Hes; try (rewrite build_succs_list_none in *; congruence).
  generalize (IHl _ _ _ _ Hes); clear IHl Hes; intros Hl.
  intros i j Hin.
  edestruct Hl; eauto.
  rewrite sons_set in H.
  flatten H; eauto.
  destruct H; go.
Qed.

Lemma build_succs_correct_tree_aux : forall l sn,
  build_succs l = Some sn ->
  forall i j,
    In j (sons sn i) -> In (j,i) l.
Proof.
  unfold build_succs.
  intros l sn.
  flatten.
  intros.
  inv H.
  exploit build_succs_list_Some_tree; eauto.
  destruct 1; auto.
  rewrite sons_ptree_empty in H.
  elim H.
Qed.

Lemma build_succs_correct_tree : forall l sn,
  build_succs l = Some sn ->
  forall i j,
    In j (sons sn i) -> make_D_fun l j = i.
Proof.
  intros.
  unfold make_D_fun.
  rewrite tree_from_assoc_prop2 with l j i; auto.
  eapply build_succs_Some_list_norepet; eauto.
  eapply build_succs_correct_tree_aux; eauto.
Qed.

End DomTestImplem.

Section dom_test_results.

Variable l: list (node*node).
Let D := make_D_fun l.
Variable sn : tree (list node).
Hypothesis sn_eq : build_succs l = Some sn.
Variable itvm : tree itv.
Hypothesis itvm_eq : build_itv_map sn = Some itvm.

Lemma in_sons_D : forall i j,  In j (sons sn i) -> D j = i.
Proof.
  intros. eapply build_succs_correct_tree; eauto.
Qed.

Lemma InSubTree_Dstar : forall i j, InSubTree (sons sn) i j -> Dstar D j i.
Proof.
  induction 1; go.
  exploit in_sons_D; eauto.
  intros; subst.
  go.
Qed.

Lemma is_ancestor_spec : forall i j,
  is_ancestor itvm j i = true -> Dstar D i j .
Proof.
  unfold is_ancestor; intros.
  flatten H.
  apply itv_incl_spec in H.
  assert (InSubTree (sons sn) j i).
  { eapply build_itv_map_correct; eauto.
    eapply build_succs_no_repet; eauto. }    
  eapply InSubTree_Dstar; eauto.
Qed.

End dom_test_results.

End DomTestAbstract.

End Make.

Module PositiveNodeTree <: NODE_TREE.
  Definition node : Type := positive.
  Definition peq : forall x y:node, {x=y}+{x<>y} := peq.

  Definition tree : Type -> Type := PTree.t.
  Definition get : forall {A:Type}, node -> tree A -> option A := PTree.get.
  Definition set : forall {A:Type}, node -> A -> tree A -> tree A := PTree.set.
  Definition empty : forall A:Type, tree A := PTree.empty.

  Lemma gsspec:
    forall (A: Type) (i j: node) (x: A) (m: tree A),
    get i (set j x m) = if peq i j then Some x else get i m.
  Proof PTree.gsspec. 
  Lemma gempty:
    forall (A: Type) (i: node), get i (empty A) = None.
  Proof PTree.gempty.
End PositiveNodeTree.

Module Z <: INT.

  Local Open Scope Z_scope.
  Definition t : Type := Z.
  Definition int_zero : t := 0.
  Definition int_succ : t -> option t := fun x => Some (x+1).
  Definition int_le : t -> t -> Prop := Z.le.
  Definition int_lt : t -> t -> Prop := Z.lt.
  Lemma int_le_dec : forall (x y :t), {int_le x y}+{int_lt y x}.
  Proof.
    intros x y.
    destruct (Z_le_dec x y).
    - left; auto.
    - right; unfold int_lt; lia.
  Defined.
  Lemma int_le_refl : forall i, int_le i i.
  Proof. unfold int_le; intros; lia. Qed.
  Lemma int_le_trans : forall i1 i2 i3,
  int_le i1 i2 -> int_le i2 i3 -> int_le i1 i3.
  Proof. unfold int_le; intros; lia. Qed.

  Lemma int_le_lt_trans : forall i1 i2 i3,
  int_le i1 i2 -> int_lt i2 i3 -> int_lt i1 i3.
  Proof. unfold int_le, int_lt; intros; lia. Qed.

  Lemma int_lt_le_trans : forall i1 i2 i3,
  int_lt i1 i2 -> int_le i2 i3 -> int_lt i1 i3.
  Proof. unfold int_le, int_lt; intros; lia. Qed.

  Lemma int_lt_le : forall i1 i2,
  int_lt i1 i2 -> int_le i1 i2.
  Proof. unfold int_le, int_lt; intros; lia. Qed.

  Lemma int_le_not_lt : forall i1 i2,
  int_le i1 i2 -> ~ int_lt i2 i1.
  Proof. unfold int_le, int_lt; intros; lia. Qed.

  Lemma int_lt_succ : forall i i', int_succ i = Some i' -> int_lt i i'.
  Proof. unfold int_succ, int_lt; intros. inv H; lia. Qed.

  Lemma int_le_succ : forall i i', int_succ i = Some i' -> int_le i i'.
  Proof.
    auto using int_lt_le, int_lt_succ. 
  Qed.
  Global Hint Resolve int_le_refl int_le_trans int_le_lt_trans 
    int_lt_le_trans int_lt_le int_le_succ int_lt_succ: core.
End Z.


