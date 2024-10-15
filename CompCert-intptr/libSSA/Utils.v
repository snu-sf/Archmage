(** Utility lemmas, tactics *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import Floats.
Require Import Integers.
Require Ascii.
Require String.
Require Import Relation_Operators.
Require Psatz.
Require Import Permutation.
Require Import List.

(** * Tactics *)
Ltac exploit_dstr x := 
  let Hnew := fresh "Htmp"
    in  exploit x ; eauto ; intros Hnew  ; destruct Hnew as [] ; intuition.

Ltac boolInv :=
  match goal with
  | [ H: _ && _ = true |- _ ] => 
      destruct (andb_prop _ _ H); clear H; boolInv
  | [ H: proj_sumbool _ = true |- _ ] =>
      generalize (proj_sumbool_true _ H); clear H; 
      let EQ := fresh in (intro EQ; try subst; boolInv)
  | _ =>
      idtac
  end.

Ltac revert_arith :=
  repeat
    (match goal with
       | H : Z |- _ => generalize dependent H
       | H : positive |- _ => generalize dependent H
       | H : N   |- _ => generalize dependent H
       | H : nat  |- _ => generalize dependent H
       | H : context[?X] |- _ => match type of X with
          			   | nat => generalize dependent H
                               	   | Z => generalize dependent H
			           | N => generalize dependent H
                          	   | positive => generalize dependent H
				 end
     end	
    ) ; clear ; intros.

Ltac lia := 
  (try revert_arith) ; zify ; unfold Z.succ in * ; Psatz.lia.

(* To be used when building error messages *)
(* Eval compute in (Ascii false false false false true true false false). *)
Fixpoint get_digits (z:Z) (p:positive) : list nat :=
  match p with 
    | xH => nil
    | xO p | xI p =>  
      let digit := (z - ((z/10)*10))%Z in       
        match digit with 
          | Zpos d => (nat_of_P d)::(get_digits (z/10) p)
          | Z0 => O::(get_digits (z/10) p)
          | _ => nil
        end
  end.

Fixpoint rm_zeros l := 
  match l with 
    | nil => nil 
    | O::m => rm_zeros m
    | x::m =>  l
  end.

Definition encode_ascii (n: nat) := (n + 48)%nat.

Fixpoint digits l := 
   match l with 
     | nil => String.EmptyString 
     | d::m => String.String (Ascii.ascii_of_nat (encode_ascii d)) (digits m)
   end.
 
Definition pos_to_string (p:positive) : String.string :=
  let ldigits := rm_zeros (rev (get_digits (Zpos p) p)) in
    digits ldigits.

(** * Utilities on the [option] type *)
Definition get_opt {A B:Type} (f:A->B) (x:option A) : option B :=
  match x with
    | None => None
    | Some a => Some (f a)
  end.

Lemma option_map_some: forall A B (f:A->B) x i, 
 option_map f x = Some i -> exists i', x = Some i'.
Proof.
  intros.
  destruct x; inv H; eauto.
Qed.

Global Hint Resolve option_map_some : core.

(** * Properties about [PTree] *)
Require Import DLib.

Lemma PTree_xfold_none : forall (A B:Type) (f:A->positive->B->A) (m:PTree.t B) (x:A) p',
  (forall p, m!p = None) ->
  PTree.xfold f p' m x = x.
Proof.
  induction m; simpl; intros; auto.
  generalize (H xH); simpl; intros; subst.
  rewrite IHm1.
  rewrite IHm2; auto.
  intros; generalize (H (xI p)); simpl; auto.
  intros; generalize (H (xO p)); simpl; auto.
Qed.
  
Lemma ptree_set_permut: forall r  r0 r1 (v0 v1:val) t ,
  r0 <> r1 ->
  Maps.PTree.get  r (Maps.PTree.set r0 v0 (Maps.PTree.set r1 v1 t)) = 
  Maps.PTree.get r (Maps.PTree.set r1 v1 (Maps.PTree.set r0 v0 t)).
Proof.
  induction r; intros; destruct r0; destruct r1; destruct t; simpl;
    try rewrite <- (gleaf A i); auto; try apply IHr; congruence.
Qed.

Lemma ptree_setset: forall r dst (v1 v2:val) t,
Maps.PTree.get dst (Maps.PTree.set r v2 (Maps.PTree.set r v1 t)) = 
Maps.PTree.get dst (Maps.PTree.set r v2 t).
Proof.
  induction r; intros; destruct dst; destruct t; simpl;
    try rewrite <- (gleaf A i); auto; try apply IHr; congruence.
Qed.
  

Definition forall_ptree {A:Type} (f:positive->A->bool) (m:Maps.PTree.t A) : bool :=
  Maps.PTree.fold (fun (res: bool) (i: positive) (x: A) => res && f i x) m true.

Remark ptree_forall:
  forall (A: Type) (f: positive -> A -> bool) (m: Maps.PTree.t A),
  Maps.PTree.fold (fun (res: bool) (i: positive) (x: A) => res && f i x) m true = true ->
  forall i x, Maps.PTree.get i m = Some x -> f i x = true.
Proof.
  intros.
  set (f' := fun (res: bool) (i: positive) (x: A) => res && f i x).
  set (P := fun (m: Maps.PTree.t A) (res: bool) =>
              res = true -> Maps.PTree.get i m = Some x -> f i x = true).
  assert (P m true).
  rewrite <- H. fold f'. apply Maps.PTree_Properties.fold_rec.
  unfold P; intros. rewrite <- H1 in H4. auto. 
  red; intros. rewrite Maps.PTree.gempty in H2. discriminate.
  unfold P; intros. unfold f' in H4. boolInv. 
  rewrite Maps.PTree.gsspec in H5. destruct (peq i k). 
  subst. inv H5. auto.
  apply H3; auto. 
  red in H1. auto. 
Qed.

Lemma forall_ptree_true:
  forall (A: Type) (f: positive -> A -> bool) (m: Maps.PTree.t A),
    forall_ptree f m = true ->
    forall i x, Maps.PTree.get i m = Some x -> f i x = true.
Proof.
  apply ptree_forall.
Qed.

(** * PTrees over pairs of positive *)
Require Maps2.

Module P2Map : MAP with Definition elt := (positive * positive)%type :=
  Maps2.MakeProdMap PMap PMap.

Notation "a #2 b" := (P2Map.get b a) (at level 1).
Notation "a ##2 b" := (List.map (fun r => P2Map.get r a) b) (at level 1).
Notation "a #2 b <- c" := (P2Map.set b c a) (at level 1, b at next level).
Notation "a !!2 b" := (P2Map.get b a) (at level 1).
Notation p2eq :=  P2Map.elt_eq.

(** * Getting the index of an element in a list *)
Fixpoint get_index_acc (l:list positive) (a:positive) (acc: nat) : option nat :=
  match l with 
    | nil => None
    | x::m =>
      if (peq x a) 
      then Some acc
      else get_index_acc m a (acc+1)
  end.

Definition get_index (l:list positive) (a:positive) :=
  get_index_acc l a O.

(** The [nth_okp] predicate *)

Inductive nth_okp {A:Type}: nat -> list A -> Prop :=
  | nth_okp_headO : forall l e, nth_okp 0 (e::l)
  | nth_okp_headS : forall l e n, nth_okp n l -> nth_okp (S n) (e::l).

Lemma nth_okp_exists {A:Type}: forall (l: list A) k, 
  nth_okp k l -> exists v, nth_error l k = Some v.
Proof.
  induction l; intros.
  inv H. 
  destruct k. exists a ; auto.
  simpl in *.  inv H. eapply IHl ; eauto.
Qed.

Lemma nth_okp_length : forall (A B:Type) k (l1:list A),
  nth_okp k l1 -> forall  (l2:list B), length l1 = length l2 -> nth_okp k l2.
Proof.
  induction 1; destruct l2; try constructor; simpl; try congruence.
  inv H0; auto.
Qed.

(** Utility lemmas about [get_index_acc] and [get_index] *)

Lemma get_index_acc_progress: forall (l: list positive) (a b:positive) acc k,
  b <> a ->
  get_index_acc (b::l) a acc = Some k ->
  get_index_acc l a (acc+1) = Some k.
Proof.
  induction l; intros.
  inv H0.
  destruct (peq b a). 
  elim H ; auto.
  inv H2.
  simpl in *. 
  destruct (peq b a0).
  elim H ; auto.
  auto. 
Qed.

Lemma get_index_acc_ge_acc: forall l e acc k, 
  get_index_acc l e acc = Some k ->
  ge k acc.
Proof.
  induction l; intros.
  inv H. 
  simpl in H.
  destruct (peq a e).  inv H; auto.
  assert (IHl' := IHl e (acc+1)%nat k H). 
  lia.
Qed.

Lemma get_index_acc_inv2 : forall l a (acc acc' :nat) x,
  get_index_acc l a (acc+acc') = Some (x+acc')%nat ->
  get_index_acc l a acc = Some x.
Proof.
  induction l; intros.
  inv H. simpl in *.
  destruct (peq a a0). inv H. 
  assert (acc = x) by lia. inv H1; auto. 
  assert (Hacc : (acc+acc'+1)%nat = (acc+1+acc')%nat) by lia.
  rewrite Hacc in *. 
  eapply IHl; eauto.
Qed.

Lemma get_index_some_sn: forall l a e k acc,
  a <> e ->
  get_index_acc (a :: l) e acc = Some ((k+1)%nat) ->
  get_index_acc l e acc = Some k.
Proof.
  destruct l; intros.
  simpl in H0.
  case_eq (peq a e) ; intros; ((rewrite peq_false in H0 ; auto); inv H0). 
  eapply get_index_acc_progress in H0; auto.
  eapply get_index_acc_inv2; eauto.
Qed.  
  
Lemma get_index_some_in: forall l e k, 
  get_index l e = Some k ->
  In e l.
Proof.
  induction l; intros.
  - inv H.
  - destruct (peq a e); intros. 
    + subst. constructor; auto.
    + right.
      destruct k. 
      * unfold get_index in *.
        simpl in H. rewrite peq_false in H; auto. 
        eapply get_index_acc_ge_acc in H. inv H.
      * eapply IHl with (k:= k); eauto.
        replace (Datatypes.S k) with ((k+1)%nat) in *.   
        eapply get_index_some_sn ;  eauto.
        lia.
Qed.

Lemma get_index_acc_inv : forall l a (acc acc' :nat) x,
  get_index_acc l a acc = Some x ->
  get_index_acc l a (acc+acc') = Some (x+acc')%nat.
Proof.
  induction l; intros.
  inv  H.
  simpl in *.  
  case_eq (peq a a0); intros.
  rewrite H0 in H.
  inversion H. auto.
  rewrite H0 in H. 
  assert ( (acc + acc' + 1)%nat = (acc + 1 + acc')%nat) by lia.  
  rewrite H1.
  eapply IHl  ; eauto.
Qed.
  
Lemma in_get_index_some: forall l a, 
  In a l -> exists k, get_index l a = Some k.
Proof.
  induction l ; intros.
  inv H.
  inv H. exists O. unfold get_index.  simpl.
  rewrite peq_true ; auto.
  assert (Ha0 := IHl a0 H0). 
  destruct Ha0.
  unfold get_index in *. 
  unfold get_index_acc.  
  case_eq (peq a a0); intros. 
  exists O ; auto.
  generalize (get_index_acc_progress l a0 a 0 (x+1)) ; intros.
  exists (x+1)%nat. eapply H2 ; eauto.
  simpl. rewrite H1.
  eapply get_index_acc_inv with (acc:= O); eauto.
Qed.  

Lemma get_index_some : forall l pc k, 
  get_index l pc = Some k ->
  (k < length l)%nat.
Proof.
  induction l ; intros.
  inv H.
  destruct k ; simpl in * ;  auto. lia.
  destruct (peq a pc). inv e.
  unfold get_index in * ; simpl in *.
  rewrite peq_true in H ; eauto. inv H.
  unfold get_index in *.
  replace (Datatypes.S k) with (k+1)%nat in *; try lia.
  eapply get_index_some_sn in H ; eauto.
  exploit IHl ; eauto. intros. lia. 
Qed.

Lemma get_index_nth_error: forall pc l k, 
  get_index l pc = Some k ->
  nth_error l k = Some pc.
Proof.
  induction l; intros.
  inv H. unfold get_index in H.
  destruct (peq a pc). simpl in *.  inv e; auto. rewrite peq_true in H ; auto. inv H. auto.
  destruct k. simpl in H. rewrite peq_false in H ; auto.
  eapply get_index_acc_ge_acc in H ; eauto. inv H.
  replace (Datatypes.S k) with (k+1)%nat in H; try lia.
  eapply get_index_some_sn  in H ; eauto. 
Qed.

Lemma get_index_acc_nth_okp_aux : forall pc l k k',
  get_index_acc l pc k' = Some (k'+k)%nat -> nth_okp k l.
Proof.
  induction l; simpl.
  congruence.
  intros; destruct peq.
  assert (k=O).
    inversion H. lia.
  subst; constructor.
  destruct k.
  constructor.
  replace (k' + Datatypes.S k)%nat with ((k'+1)+k)%nat in * by lia.
  constructor 2; eauto.
Qed.

Lemma get_index_acc_nth_okp : forall pc l k,
  get_index l pc = Some k -> nth_okp k l.
Proof.
  unfold get_index; intros.
  apply get_index_acc_nth_okp_aux with pc O.
  simpl; auto.
Qed.

Lemma in_tl_in_cons: forall (A:Type) (l: list A) (a e:A), 
  In e l -> In e (a::l).
Proof.
  intros; constructor 2; auto.
Qed.

Lemma in_hd_in_cons: forall (A:Type) (l: list A) (a:A), 
  In a (a::l).
Proof.
  intros; constructor ; auto.
Qed.

Global Hint Resolve in_tl_in_cons: core.
Global Hint Resolve in_hd_in_cons: core.

Lemma app_cons_nil : forall (A:Type) (l l': list A) (n1 n2 : A), 
  n1 :: nil = l ++ n2 :: l' ->
  (l = nil) /\ (l' = nil).
Proof.
  intros.
  destruct l.
  intuition.
  simpl in H. inv H ; auto.
  simpl in H.
  inv H.
  eelim app_cons_not_nil ; eauto.
Qed.

Lemma in_nth_error_some : forall (A: Type) (l: list A) (a: A), 
  In a l -> 
  (exists k, nth_error l k = Some a).
Proof.
  induction l ; intros; inv H.
  exists O ; auto. 
  eelim IHl ; eauto ; intros.
  exists (S x) ; auto. 
Qed.

Lemma nth_error_nil_some {A: Type} : forall k (e: A), 
  nth_error nil k = Some e -> False.
Proof.
  intros.
  destruct k ; simpl in H ; inv H.
Qed.

Lemma nth_error_some_in: forall (A:Type), forall k (l:list A) r,
  nth_error l k = Some r -> In r l.
Proof.
  induction k; intros; destruct l; simpl in *.
  - inv H.
  - inv H; auto.
  - inv H.
  - right; auto.
Qed.

Lemma nth_error_some_same_length {A B: Type}: forall (l1: list A) (l2: list B) k e, 
  nth_error l1 k = Some e ->
  List.length l1 = List.length l2 ->
  exists e, nth_error l2 k = Some e.
Proof.
  induction l1; intros.
  destruct k ; simpl in * ; inv H.
  destruct k ; simpl in *. 
  destruct l2 ; simpl in *; try congruence.
  inv H0. inv H. eauto.
  destruct l2 ; simpl in *; try congruence.
  inv H0. eauto.  
Qed.
  
Lemma map_in_some {A B :Type} : forall (f:A -> B) l b, 
  In b (map f l) -> 
  exists a, In a l /\ f a = b.
Proof.
  induction l ; intros ; inv H.
  exists a ;  intuition.
  elim (IHl b) ; eauto. 
  intros. exists x ; intuition.
Qed.

Lemma list_map_nth_some {A B : Type} : forall (f: A -> B) l a k, 
  nth_error l k = Some a ->
  nth_error (map f l) k = Some (f a).
Proof.
  induction l ; intros.
  destruct k in H; inv H.
  destruct k.  simpl in *. inv H ; auto.
  simpl in *; eauto. 
Qed.

Lemma fold_left_inv {A : Type} : forall (f: A -> bool) (l: list A) (a : A) (res0:bool), 
    fold_left (fun (res : bool) (i : A) => res && f i) (a::l) res0 = 
    (f a) && fold_left (fun (res : bool) (i : A) => res && f i) l res0.
Proof.
  induction l ; intros.
  simpl. rewrite andb_comm; auto. 
  simpl.
  rewrite <- IHl ; eauto.  simpl. 
  assert (res0 && f a0 && f a = res0 && f a && f a0) by ring. 
  rewrite H. auto.
Qed.    

Lemma list_forall {A: Type}: forall (f: A -> bool) (l: list A), 
  fold_left (fun (res : bool) (i : A) => res && f i) l true = true ->
  forall (i : A), In i l -> f i = true.
Proof. 
  induction l ; intros.
  inv H0.
  rewrite fold_left_inv in H. 
  simpl in H. 
  case_eq (f a); intros. 
  inv H0. auto. rewrite H1 in *.  
  rewrite andb_true_l in H. eapply IHl ; eauto.
  rewrite H1 in *.  boolInv. inv H2. 
Qed. 

Fixpoint forall_list2 {A:Type} (f:A->A->bool) (l1 l2: list A) : bool :=
  match l1, l2 with
    | nil, nil => true
    | a1::q1, a2::q2 => f a1 a2 && (forall_list2 f q1 q2)
    | _, _ => false
  end.


(** * Lemmas about [positive] *)

Lemma Ple_Plt_trans:
  forall (p q r: positive), Ple p q -> Plt q r -> Plt p r.
Proof.
  unfold Plt, Ple; intros.
  zify ; lia.
Qed.

Lemma Ple_Plt_succ: forall p1 p2,
  Ple p1 p2 -> Plt p1 (Pos.succ p2).
Proof.
  intros.
  eapply Ple_Plt_trans ; eauto.
  eapply Plt_succ; eauto.
Qed.


(** * The [inclist] predicate *)
Inductive inclist {A:Type} : list A -> list A -> Prop:=
| inclist_nil : forall l, inclist nil l
| inclist_cons1: forall l1 l2 b, inclist l1 l2 -> inclist l1 (b::l2)
| inclist_cons2: forall l1 l2 a, inclist l1 (a::l2) -> inclist (a::l1) (a::l2).

Lemma inclist_refl {A:Type} : forall (l: list A), inclist l l.
Proof.
  induction l; intros.
  constructor.
  constructor 3. constructor ; auto.
Qed.

Lemma inclist_cons_in {A:Type} : forall l1 l2 (a:A),
  inclist (a :: l2) l1 -> In a l1.
Proof.
  induction l1; intros; inv H.
  - exploit IHl1; eauto with datatypes.
  - auto with datatypes. 
Qed.


Lemma inclist_indu : forall A l2 l1 (a:A), 
  inclist (a::l1) l2 -> inclist l1 l2.
Proof.
  induction l2; intros; inv H.
  exploit IHl2; eauto; intros.
  constructor; auto.
  auto.
Qed.

(** * The [alln] predicate *)
Inductive alln {A:Type} (n:A) : list A -> Prop:=
| alln_nil : alln n nil
| alln_cons: forall m, alln n m -> alln n (n::m).

(** * Additional definitions and properties of lists *)

Lemma list_nth_z_tonat {A: Type} : forall  (l : list A) (n: Z)  (a: A),
list_nth_z l n = Some a ->
n = Z0 \/ (exists p, n = Zpos p).
Proof.
  induction l ; intros.
  inv H. 

  simpl in H.
  destruct (zeq n 0). 
  inv e; auto.
  destruct n; eauto.  
  simpl in H. exploit IHl ; eauto; intros.
  destruct H0.
  lia. 
  destruct H0; inv H0. 
Qed.
  
Lemma arith_utils: forall (n:Z) (n1: nat) , 
   Z.to_nat n = Datatypes.S n1 ->
   n1 =  (Z.to_nat (Z.pred n)) .
Proof.
  induction n; intros.
  inv H. 
  rewrite Z2Nat.inj_pred. rewrite H.
  lia. 
  inv H.
Qed.

Local Open Scope Z_scope.

Lemma arith_utils2: forall (n:Z) (n1: nat)  , 
  n > 0 ->
  n1 =  (Z.to_nat (Z.pred n)) ->
  Z.to_nat n = Datatypes.S n1.
Proof.
  induction n; intros.
  - inv H.
  - rewrite Z2Nat.inj_pred in H0.
    subst. 
    erewrite Nat.lt_succ_pred with O _ ; eauto.
    destruct p; (simpl; lia).
  - inv H.
Qed.
  
Lemma list_nth_z_nth_error {A: Type} : forall  (l : list A) (n: Z) (a: A),
list_nth_z l n = Some a ->
nth_error l (Z.to_nat n) = Some a.
Proof.
  induction l ; intros.
  inv H.
  exploit @list_nth_z_tonat ; eauto.
  intros.
  destruct H0. inv H0.
  simpl in * ; auto.  
  destruct H0. 
  
  simpl in H. case_eq (zeq n 0) ; intros.
  inv H. inv e.
  rewrite H1 in *.
  exploit IHl ; eauto.
  intros.
  case_eq (Z.to_nat n); intros.
  inv H3.  inv H5.  lia.
  simpl. 
  exploit arith_utils; eauto.
  intros. rewrite H4 ; auto.
Qed.

Lemma nth_error_list_nth_z {A: Type} : forall  (l : list A) (n: Z) (a: A),
n >= 0 ->
nth_error l (Z.to_nat n) = Some a ->
list_nth_z l n = Some a.
Proof.
  induction l ; intros.
  eelim @nth_error_nil_some ; eauto.
  destruct n.
  simpl in * ; auto.
  case_eq (Z.to_nat (Zpos p) ) ; intros.
  inv H1. lia. rewrite H1 in *. simpl in H0.
  case_eq (Zpos p); intros. inv H2. 
  exploit arith_utils ; eauto.
  intros.
  exploit arith_utils2 ; eauto. 
  lia. intros.
  inv H3 ; auto.
  exploit (IHl (Z.pred (Zpos p0))) ; eauto. 
  unfold Z.pred ; lia.
  simpl in *. lia. 
Qed.

Lemma list_nth_z_ge0 {A: Type} : forall (l: list A) (n:Z) (a: A), 
  list_nth_z l n = Some a ->
  n >= 0.
Proof.
  induction l; intros; auto. 
  destruct n ; try lia.
  simpl in H. inv H.
  simpl in H.
  case_eq (zeq n 0) ; intros; rewrite H0 in *. 
  inversion e ; auto.
  lia.
  assert (HH:= IHl (Z.pred n) a0 H) ; eauto.
  unfold Z.pred in * ; lia.
Qed.  

Local Close Scope Z_scope.

Lemma list_norepet_app: forall A (l1:list A), list_norepet l1 -> 
  forall l2, list_norepet l2 -> 
    (forall x, In x l1 -> In x l2 -> False) ->
    list_norepet (l1++l2).
Proof.
  induction 1; simpl; intros; auto.
  constructor; eauto with arith.
  intro.
  rewrite (in_app _ _ _) in H3.
  intuition; eauto with datatypes.
Qed.

Lemma list_norepet_rev: forall A (l:list A), list_norepet l -> list_norepet (rev l).
Proof.
  induction 1; simpl.
  constructor.
  apply list_norepet_app; auto.
  repeat constructor.
  simpl; auto.  
  simpl; intuition; subst.
  elim H; apply In_rev; auto.
Qed.

Section FORALL1.

Variable A: Type.
Variable P: A -> Prop.

Inductive list_forall1: list A -> Prop :=
  | list_forall1_nil: list_forall1 nil 
  | list_forall1_cons: forall a al, P a -> list_forall1 al -> list_forall1 (a :: al).


End FORALL1.

Set Implicit Arguments.


Section forall3_ptree.

  Variable A B: Type.
  Variable f: positive -> option A -> option A -> option B -> bool.
  Hypothesis f_none_none: forall p x, f p None None x = true.

  Fixpoint xforall3_l (m : PTree.t A) (m3 : PTree.t B) (i : positive) : bool :=
      match m with
      | PTree.Leaf => true
      | PTree.Node l o r =>
        match m3 with
          | PTree.Leaf =>
            f (PTree.prev i) o None None &&
            (xforall3_l l PTree.Leaf (xO i)) &&
            (xforall3_l r PTree.Leaf (xI i))
          | PTree.Node l3 o3 r3 =>
            f (PTree.prev i) o None o3 &&
            (xforall3_l l l3 (xO i)) &&
            (xforall3_l r r3 (xI i))
        end
      end.

  Lemma xgforall3_l :
    forall i m m3 j,
      xforall3_l m m3 j = true ->
      f (PTree.prev (PTree.prev_append i j)) (PTree.get i m) None (PTree.get i m3) = true.
  Proof.
    induction i; intros; destruct m; destruct m3; simpl in *; auto;
      repeat rewrite andb_true_iff in *.
    - replace (@None B) with (@PTree.get B i PTree.Leaf).
      apply IHi; intuition.
      apply PTree.gempty.
    - apply IHi; intuition.
    - replace (@None B) with (@PTree.get B i PTree.Leaf).
      apply IHi; intuition.
      apply PTree.gempty.
    - apply IHi; intuition.
    - intuition.
    - intuition.
  Qed.

  Fixpoint xforall3_r (m : PTree.t A) (m3 : PTree.t B) (i : positive) : bool :=
      match m with
      | PTree.Leaf => true
      | PTree.Node l o r =>
        match m3 with
          | PTree.Leaf =>
            (f (PTree.prev i) None o None) &&
            (xforall3_r l PTree.Leaf (xO i)) &&
            (xforall3_r r PTree.Leaf (xI i))
          | PTree.Node l3 o3 r3 =>
            (f (PTree.prev i) None o o3) &&
            (xforall3_r l l3 (xO i)) &&
            (xforall3_r r r3 (xI i))
        end
      end.

  Lemma xgforall3_r :
    forall i m m3 j,
      xforall3_r m m3 j = true ->
      f (PTree.prev (PTree.prev_append i j)) None (PTree.get i m) (PTree.get i m3) = true.
  Proof.
    induction i; intros; destruct m; destruct m3; simpl in *; auto;
      repeat rewrite andb_true_iff in *.
    - replace (@None B) with (@PTree.get B i PTree.Leaf).
      apply IHi; intuition.
      apply PTree.gempty.
    - apply IHi; intuition.
    - replace (@None B) with (@PTree.get B i PTree.Leaf).
      apply IHi; intuition.
      apply PTree.gempty.
    - apply IHi; intuition.
    - intuition.
    - intuition.
  Qed.

  Fixpoint xforall3_ptree (m1 m2 : PTree.t A) (m3: PTree.t B) (i : positive) {struct m1} : bool :=
    match m1 with
    | PTree.Leaf => xforall3_r m2 m3 i
    | PTree.Node l1 o1 r1 =>
        match m2 with
        | PTree.Leaf => xforall3_l m1 m3 i
        | PTree.Node l2 o2 r2 =>
          match m3 with
            | PTree.Leaf =>
              (xforall3_ptree l1 l2 PTree.Leaf (xO i)) &&
              (f (PTree.prev i) o1 o2 None) &&
              (xforall3_ptree r1 r2 PTree.Leaf (xI i))
            | PTree.Node l3 o3 r3 =>
              (xforall3_ptree l1 l2 l3 (xO i)) &&
              (f (PTree.prev i) o1 o2 o3) &&
              (xforall3_ptree r1 r2 r3 (xI i))
          end
        end
    end.

  Lemma xgforall3_ptree :
    forall i m1 m2 m3 j,
      xforall3_ptree m1 m2 m3 j = true ->
      f (PTree.prev (PTree.prev_append i j)) (PTree.get i m1) (PTree.get i m2) (PTree.get i m3) = true.
  Proof.
    induction i; intros; destruct m1; destruct m2; destruct m3; simpl in *; auto;
      repeat rewrite andb_true_iff in *.
    - replace (@None B) with (@PTree.get B i PTree.Leaf) by apply PTree.gempty.
      apply xgforall3_r; intuition.
    - apply xgforall3_r; intuition.
    - replace (@None B) with (@PTree.get B i PTree.Leaf) by apply PTree.gempty.
      apply xgforall3_l; intuition.
    - apply xgforall3_l; intuition.
    - replace (@None B) with (@PTree.get B i PTree.Leaf) by apply PTree.gempty.
      apply IHi; intuition.
    - apply IHi; intuition.
    - replace (@None B) with (@PTree.get B i PTree.Leaf) by apply PTree.gempty.
      apply xgforall3_r; intuition.
    - apply xgforall3_r; intuition.
    - replace (@None B) with (@PTree.get B i PTree.Leaf) by apply PTree.gempty.
      apply xgforall3_l; intuition.
    - apply xgforall3_l; intuition.
    - replace (@None B) with (@PTree.get B i PTree.Leaf) by apply PTree.gempty.
      apply IHi; intuition.
    - apply IHi; intuition.
    - intuition.
    - intuition.
    - intuition.
    - intuition.
    - intuition.
    - intuition.
  Qed.

  Definition forall3_ptree (m1 m2 : PTree.t A) (m3: PTree.t B) : bool :=
    xforall3_ptree m1 m2 m3 xH.

  Lemma gforall3_ptree :
    forall m1 m2 m3, forall3_ptree m1 m2 m3 = true ->
      forall i, f i (PTree.get i m1) (PTree.get i m2) (PTree.get i m3) = true.
  Proof.
    unfold forall3_ptree; intros.
    replace (f i) with (f (PTree.prev (PTree.prev i))).
    eapply xgforall3_ptree; eauto.
    rewrite PTree.prev_involutive. auto. 
  Qed.

End forall3_ptree.
Arguments forall3_ptree [A B].

  Section COMBINE.
    Import PTree.
    Variable A B C: Type.
    Variable f: option A -> option B -> option C.
    Hypothesis f_none_none: f None None = None.

  Fixpoint xcombine_l (m : t A) {struct m} : t C :=
      match m with
      | Leaf => Leaf
      | Node l o r => Node' (xcombine_l l) (f o None) (xcombine_l r)
      end.

  Lemma xgcombine_l :
          forall (m: t A) (i : positive),
          get i (xcombine_l m) = f (get i m) None.
    Proof.
      induction m; intros; simpl.
      repeat rewrite gleaf. auto.
      rewrite gnode'. destruct i; simpl; auto.
    Qed.

  Fixpoint xcombine_r (m : t B) {struct m} : t C :=
      match m with
      | Leaf => Leaf
      | Node l o r => Node' (xcombine_r l) (f None o) (xcombine_r r)
      end.

  Lemma xgcombine_r :
          forall (m: t B) (i : positive),
          get i (xcombine_r m) = f None (get i m).
    Proof.
      induction m; intros; simpl.
      repeat rewrite gleaf. auto.
      rewrite gnode'. destruct i; simpl; auto.
    Qed.

  Fixpoint combine (m1:t A) (m2 : t B) {struct m1} : t C :=
    match m1 with
    | Leaf => xcombine_r m2
    | Node l1 o1 r1 =>
        match m2 with
        | Leaf => xcombine_l m1
        | Node l2 o2 r2 => Node' (combine l1 l2) (f o1 o2) (combine r1 r2)
        end
    end.

  Theorem gcombine:
      forall m1 m2 (i: positive),
      get i (combine m1 m2) = f (get i m1) (get i m2).
  Proof.
    induction m1; intros; simpl.
    rewrite gleaf. apply xgcombine_r.
    destruct m2; simpl.
    rewrite gleaf. rewrite <- xgcombine_l. auto. 
    repeat rewrite gnode'. destruct i; simpl; auto.
  Qed.

  End COMBINE.
Arguments combine [A B C].

(** * Relational operators *)

Notation "R **" := (@clos_refl_trans _ R) (at level 30).
Lemma Rstar_refl : forall A R (i:A), R** i i.
Proof. constructor 2. Qed.

Lemma Rstar_R : forall A (R:A->A->Prop) (i j:A), R i j -> R** i j.
Proof. constructor 1; auto. Qed.
  
Lemma Rstar_trans : forall A (R:A->A->Prop) (i j k:A), 
  R** i j -> R** j k -> R** i k.
Proof. intros A R i j k; constructor 3 with j; auto. Qed.

Global Hint Resolve Rstar_trans Rstar_refl Rstar_R: core.
 
Lemma star_eq : forall A (R1 R2:A->A->Prop),
  (forall i j, R1 i j -> R2 i j) ->
  forall i j, R1** i j -> R2** i j.
Proof.
  induction 2.
  econstructor 1; eauto.
  econstructor 2; eauto.
  econstructor 3; eauto.
Qed.

