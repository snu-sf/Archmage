(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Pair enconding for positive of bounded size (D. Pichardie) *)

Require Import Coqlib.
Require Import Registers.

Require Import List.
Require Import Lia.
Require Import Bool.

Require Import FunInd.

Open Scope nat_scope.

Fixpoint pos2list (p:positive) : list bool :=
  match p with
    | xH => nil
    | xO p => false :: pos2list p
    | xI p => true :: pos2list p
  end.

Fixpoint list2pos (l:list bool) : positive :=
  match l with
    | nil => xH
    | false :: l => xO (list2pos l)
    | true :: l => xI (list2pos l)
  end.

Lemma list2pos_pos2list : forall p, list2pos (pos2list p) = p.
Proof.
  induction p; simpl; try rewrite IHp; auto.
Qed.

Lemma pos2list_list2pos : forall l, pos2list (list2pos l) = l.
Proof.
  induction l; simpl; auto.
  destruct a; simpl; try rewrite IHl; auto.
Qed.

Fixpoint fill (n:nat) (l:list bool) : list bool :=
  match n with
    | O => l
    | S n => false :: fill n l 
  end.

Lemma length_fill : forall n l, length (fill n l) = n + length l.
Proof.
  induction n; simpl; auto.
Qed.  

Definition complete (n:nat) (l:list bool) : list bool :=
  fill (n - length l) l.

Lemma length_complete : forall n l,
  length l <= n -> length (complete n l) = n.
Proof.
  intros; unfold complete.
  rewrite length_fill.
  lia.
Qed.

Fixpoint remove_first_zeros (l:list bool) : list bool :=
  match l with
    | nil => nil
    | false::l => remove_first_zeros l
    | _ => l
  end.

Lemma remove_first_zeros_fill : forall n l,
  remove_first_zeros (fill n (true::l)) = true::l.
Proof.
  induction n; simpl; intros; auto.
Qed.

Lemma remove_first_zeros_complete : forall n l,
  remove_first_zeros (complete n (true::l)) = true::l.
Proof.
  unfold complete; intros; apply remove_first_zeros_fill.
Qed.

Lemma remove_first_zeros_fill_nil : forall n,
  remove_first_zeros (fill n nil) = nil.
Proof.
  induction n; simpl; intros; auto.
Qed.

Lemma remove_first_zeros_complete_nil : forall n,
  remove_first_zeros (complete n nil) = nil.
Proof.
  unfold complete; intros; apply remove_first_zeros_fill_nil.
Qed.

Lemma list2pos_not_xH : forall l,
  list2pos l = xH -> forall x, In x l -> x = false.
Proof.
  induction l; simpl; intuition.
  destruct a; subst; try congruence.
  destruct a; subst; try congruence.
Qed.

Lemma In_l_In_fill : forall n l x, In x l -> In x (fill n l).
Proof.  
  induction n; simpl; intuition.
Qed.

Definition encode (n:nat) (p:positive) : list bool := 
  if Reg.eq p xH then (complete n nil)
    else (complete n (true :: (pos2list (Pos.pred p)))).

Definition decode (n:nat) (l:list bool) : positive :=
  match remove_first_zeros l with
    | true :: l => Pos.succ (list2pos l)
    | _ => xH
  end.

Lemma decode_encode : forall n p, decode n (encode n p) = p.
Proof.
  unfold encode, decode; intros.
  destruct Reg.eq.
  rewrite remove_first_zeros_complete_nil; auto.
  rewrite remove_first_zeros_complete; auto.
  rewrite list2pos_pos2list.
  destruct (Psucc_pred p); intuition.
Qed.

Function log_lower (p:positive) (n:nat) {struct n} : bool :=
  match p, n with
    | xH, _ => true
    | xO p, S n => log_lower p n
    | xI p, S n => log_lower p n
    | _, _ => false
  end.

Lemma log_lower_length_pos2list : forall p n,
  log_lower p n = true -> length (pos2list p) <= n.
Proof.
  intros p n.
  functional induction (log_lower p n); intros; simpl; try congruence; try lia.
  apply IHb in H; lia.
  apply IHb in H; lia.
Qed.


Lemma log_lower_Pdouble_minus_one : forall p n,
  log_lower p n = true -> log_lower (Pdouble_minus_one p) (S n) = true.
Proof.
  intros p n.
  functional induction (log_lower p n); intros; simpl; try congruence; try lia.
  case_eq (Pdouble_minus_one p0); intros; auto.
  rewrite H0 in IHb; simpl in IHb; auto.
  rewrite H0 in IHb; simpl in IHb; auto.
Qed.

Lemma log_lower_pred : forall p n,
  log_lower p n = true -> log_lower (Pos.pred p) n = true.
Proof.
  intros p n.
  functional induction (log_lower p n); intros; simpl; try congruence; try lia.
  destruct n; auto.
  case_eq (Pdouble_minus_one p0); intros; auto.
  generalize (log_lower_Pdouble_minus_one _ _ H); rewrite H0; simpl; auto.
  generalize (log_lower_Pdouble_minus_one _ _ H); rewrite H0; simpl; auto.
Qed.

Lemma length_encode : forall n p, 
  log_lower p n = true -> length (encode (S n) p) = S n.
Proof.
  unfold encode; intros.
  destruct Reg.eq.
  unfold complete; rewrite length_fill.
  simpl; lia.
  unfold complete; rewrite length_fill.
  assert (length (true :: pos2list (Pos.pred p)) <= S n).
  generalize (log_lower_pred _ _ H); intros.
  generalize (log_lower_length_pos2list _ _ H0).
  simpl; lia.
  lia.
Qed.

Lemma remove_first_zeros_nil : forall n l,
  length l = n ->
  remove_first_zeros l = nil ->
  fill n nil = l.
Proof.
  induction n; destruct l; simpl; intros; try congruence.
  destruct b; try congruence.
  rewrite (IHn l); auto.
Qed.

Lemma length_remove_first_zeros : forall l,
  length l >= length (remove_first_zeros l).
Proof.
  induction l; simpl; auto.
  destruct a; simpl; lia.
Qed.

Lemma remove_first_zeros_not_nil : forall n l l0,
  length l = n + S (length l0) ->
  remove_first_zeros l = true :: l0 ->
  fill n (true :: l0) = l.
Proof.
  induction n; destruct l; simpl; intros; try congruence.
  destruct b; try congruence.
  generalize (length_remove_first_zeros l); rewrite H0; simpl.
  intros; apply False_ind; lia.
  destruct b; try congruence.
  inversion H0; clear H0; subst.
  apply False_ind; lia.
  rewrite (IHn l l0); auto.
Qed.

Lemma remove_first_zeros_not_false : forall l l0,
  remove_first_zeros l <> false :: l0.
Proof.
  induction l; simpl; try congruence.
  destruct a; simpl; try congruence.
Qed.

Lemma encode_decode : forall n l,
  length l = n ->
  encode n (decode n l) = l.
Proof.
  unfold encode, decode; intros.
  case_eq (remove_first_zeros l); intros.
  destruct Reg.eq.
  unfold complete; apply remove_first_zeros_nil; auto.
  simpl; lia.
  intuition.
  destruct b.
  destruct Reg.eq.
  elim Psucc_not_one with (1:=e).
  rewrite Pos.pred_succ.
  rewrite pos2list_list2pos.
  unfold complete; apply remove_first_zeros_not_nil; auto.
  generalize (length_remove_first_zeros l).
  rewrite H0.
  simpl; lia.
  destruct Reg.eq.
  elim remove_first_zeros_not_false with l l0; auto.
  intuition.
Qed.

Fixpoint split (n:nat) (l:list bool) : (list bool) * (list bool) :=
  match n with
    | O => (nil,l)
    | S n => 
      match l with
        | nil => (nil,nil) (* cas impossible *)
        | b::l => let (l1,l2) := split n l in (b::l1,l2)
      end
  end.

Lemma split_concat : forall n l1 l2,
  length l1 = n -> 
  split n (app l1 l2) = (l1,l2).
Proof.
  induction n; destruct l1; simpl; intros; auto; try congruence.
  rewrite IHn; auto.
Qed.

Lemma concat_split : forall n l,
  l = app (fst (split n l)) (snd (split n l)).
Proof.
  induction n; destruct l; simpl; intros; auto; try congruence.
  case_eq (split n l); intros l1 l2 HH.
  simpl.
  generalize (IHn l); rewrite HH; intros.
  rewrite H; auto with arith.
Qed.

Lemma length_fst_split : forall n l,
  (n <= length l)%nat -> length (fst (split n l)) = n.
Proof.
  induction n; destruct l; simpl; intros; auto; try congruence.
  lia.
  generalize (IHn l); destruct (split n l); simpl; intros.
  lia.
Qed.

Definition toPair (n:nat) (p:positive) : positive * positive :=
  let (l1,l2) := split n (pos2list p) in
    (decode n l1, list2pos l2).

Definition fromPair (n:nat) (p1_p2:positive*positive) : positive :=
  let (p1,p2) := p1_p2 in
    list2pos (app (encode n p1) (pos2list p2)).

Fixpoint app_positive (p1 p2:positive) : positive :=
  match p1 with
    | xH => p2
    | xO p1 => xO (app_positive p1 p2)
    | xI p1 => xI (app_positive p1 p2)
  end.

Lemma app_positive_prop : forall l1 l2,
  app_positive (list2pos l1) (list2pos l2) = list2pos (app l1 l2).
Proof.
  induction l1; simpl; intros; auto.
  destruct a; simpl; congruence.
Qed.

Fixpoint fill_positive (n:nat) (p:positive) : positive :=
  match n with
    | O => p
    | S n => xO (fill_positive n p)
  end.

Lemma fill_positive_prop : forall n l,
  fill_positive n (list2pos l) = list2pos (fill n l).
Proof.
  induction n; simpl; intros; congruence.
Qed.

Fixpoint length_positive (p:positive) : nat :=
  match p with
    | xH => O
    | xO p => S (length_positive p)
    | xI p => S (length_positive p)
  end.

Lemma length_positive_prop : forall l,
  length_positive (list2pos l) = length l.
Proof.
  induction l; simpl; auto.
  destruct a; simpl; try congruence.
Qed.

Definition complete_positive (n:nat) (p:positive) : positive :=
  fill_positive (n - length_positive p) p.

Definition encode_positive (n:nat) (p:positive) : positive := 
  if Reg.eq p xH then (complete_positive n xH)
    else (complete_positive n (xI (Pos.pred p))).

Definition fromPair_V2 (n:nat) (p1_p2:positive*positive) : positive :=
  let (p1,p2) := p1_p2 in
    app_positive (encode_positive n p1) p2.

Lemma fromPair_V2_prop : forall n p,
  fromPair_V2 n p = fromPair n p.
Proof.
  intros n [p1 p2]; unfold fromPair, fromPair_V2.
  rewrite <- app_positive_prop.
  unfold encode_positive, encode.
  destruct Reg.eq;
  unfold complete, complete_positive;
  rewrite <- fill_positive_prop; rewrite <- length_positive_prop; simpl;
  repeat rewrite list2pos_pos2list; auto.
Qed.

Lemma toPair_fromPair : forall n p1 p2,
  log_lower p1 n = true ->
  toPair (S n) (fromPair (S n) (p1,p2)) = (p1,p2).
Proof.
  unfold toPair, fromPair; intros.
  rewrite pos2list_list2pos.
  rewrite split_concat.
  rewrite decode_encode.
  rewrite list2pos_pos2list; auto.
  apply length_encode; auto.
Qed.

Function log_greater (p:positive) (n:nat) {struct n} : bool :=
  match n, p with
    | O, _ => true
    | S n, xO p => log_greater p n
    | S n, xI p => log_greater p n
    | _, _ => false
  end.

Lemma log_greater_length_pos2list : forall p n,
  log_greater p n = true -> n <= length (pos2list p).
Proof.
  intros p n.
  functional induction (log_greater p n); simpl; intros; try lia; try congruence.
  apply IHb in H; lia.
  apply IHb in H; lia.
Qed.

Lemma log_greater_length_pos2list_inv : forall n p,
  n <= length (pos2list p) -> log_greater p n = true.
Proof.
  induction n; destruct p; simpl; intros; auto with arith.
  apply False_ind; lia.
Qed.

Lemma log_lower_length_pos2list_inv : forall n p,
  length (pos2list p) <= n -> log_lower p n = true.
Proof.
  induction n; destruct p; simpl; intros; auto with arith.
  apply False_ind; lia.
  apply False_ind; lia.
Qed.

Fixpoint not_all_one (p:positive) : bool :=
  match p with
    | xH => true
    | xO p => true
    | xI p => not_all_one p
  end.

Lemma log_lower_implies_log_greater : forall p1 p2 n,
  log_lower p1 n = true ->
  log_greater (fromPair (S n) (p1,p2)) (S n) = true.
Proof.
  unfold fromPair; intros.
  apply log_greater_length_pos2list_inv.
  rewrite pos2list_list2pos.
  unfold encode.
  destruct Reg.eq; rewrite app_length.
  rewrite length_complete; simpl; lia.
  rewrite length_complete; simpl; try lia.
  assert (length (pos2list (Pos.pred p1)) <= n).
  apply log_lower_length_pos2list.
  apply log_lower_pred; auto.
  lia.
Qed.

Lemma length_pos2list_Psucc : forall p,
  length (pos2list (Pos.succ p)) <= S (length (pos2list p)).
Proof.
  induction p; simpl; try lia.
Qed.

Lemma fromPair_toPair : forall n p,
  log_greater p n = true -> fromPair n (toPair n p) = p.
Proof.
  unfold toPair, fromPair; intros.
  case_eq (split n (pos2list p)); intros l1 l2 L.
  rewrite pos2list_list2pos.
  rewrite encode_decode.
  generalize (concat_split n (pos2list p)); rewrite L; simpl; intros.
  rewrite <- H0.
  rewrite list2pos_pos2list; auto.
  generalize (length_fst_split n (pos2list p)); rewrite L; simpl; intros.
  apply H0.
  apply log_greater_length_pos2list; auto.
Qed.

(* Mapping RTLphi registers to indexed RTL registers *)
Module Type RTL_SSA_MAPPING.

  Definition index := positive.
  Definition size := nat.

  Parameter rmap : size -> reg -> reg * index.
  Parameter pamr : size -> reg * index -> reg.
  Parameter valid_index : size -> index -> bool.
  Parameter valid_reg_ssa : size -> reg -> bool.

  Parameter from_valid_index_to_valid_reg_ssa : forall size i,
    valid_index size i = true -> 
    forall r, valid_reg_ssa size (pamr size (r,i)) = true.
  Parameter from_valid_reg_ssa_to_valid_index : forall size ri,
    valid_reg_ssa size ri = true -> valid_index size (snd (rmap size ri)) = true.

  Parameter INJ' : forall size r1 i1 r2 i2, 
    valid_index size i1 = true ->
    valid_index size i2 = true ->
    pamr size (r1,i1) = pamr size (r2,i2) ->
    (r1,i1) = (r2,i2).

  Parameter INJ : forall size r1 r2, 
    valid_reg_ssa size r1 = true ->
    valid_reg_ssa size r2 = true ->
    rmap size r1 = rmap size r2 ->
    r1 = r2.

  Parameter BIJ1 : forall size r i,
    valid_index size i = true -> rmap size (pamr size (r,i)) = (r,i).

  Parameter BIJ2 : forall size ri,
    valid_reg_ssa size ri = true -> pamr size (rmap size ri) = ri.

End RTL_SSA_MAPPING.

Module Bij : RTL_SSA_MAPPING.

  Definition index := positive.
  Definition size := nat.

  Definition rmap size r :=
    let (i,r) := toPair size r in (r,i).

  Definition pamr size (ri:positive*positive) := 
    let (r,i) := ri in fromPair_V2 size (i,r).

  Definition valid_index size i :=
    match size with
      | O => false
      | S n => log_lower i n 
    end.

  Definition valid_reg_ssa size r :=
    match size with
      | O => false
      | S n => log_greater r size && log_lower (fst (toPair (S n) r)) n
    end.

  Lemma from_valid_index_to_valid_reg_ssa : forall size i,
    valid_index size i = true -> 
    forall r, valid_reg_ssa size (pamr size (r,i)) = true.
  Proof.
    unfold valid_index, valid_reg_ssa, pamr; intros s i T1 r.
    destruct s; try congruence.
    rewrite fromPair_V2_prop.
    rewrite toPair_fromPair; auto.
    apply andb_true_intro; split; auto.
    apply log_lower_implies_log_greater; auto.
  Qed.
  
  Lemma from_valid_reg_ssa_to_valid_index2 : forall size ri r i,
    valid_reg_ssa size ri = true -> rmap size ri = (r,i) -> valid_index size i = true.
  Proof.
    unfold valid_index, valid_reg_ssa, rmap; intros s ri r i T1 T2.
    case_eq (toPair s ri); intros i' r' T; rewrite T in *; inversion T2; subst.
    destruct s; try congruence.
    replace i with (fst (toPair (S s) ri)).
    elim andb_prop with (1:=T1); auto.
    rewrite T; auto.
  Qed.

  Lemma from_valid_reg_ssa_to_valid_index : forall size ri,
      valid_reg_ssa size ri = true -> valid_index size (snd (rmap size ri)) = true.
  Proof.
    intros.
    eapply from_valid_reg_ssa_to_valid_index2 with (r:= fst (rmap size0 ri)); eauto.
    rewrite <- surjective_pairing. auto.
  Qed.
  
  Lemma BIJ1 : forall size r i,
    valid_index size i = true -> rmap size (pamr size (r,i)) = (r,i).
  Proof.
    unfold valid_index, rmap, pamr; intros s r i.
    destruct s; intros; try congruence.
    rewrite fromPair_V2_prop.
    rewrite (toPair_fromPair s); auto.
  Qed.

  Lemma BIJ2 : forall size ri,
    valid_reg_ssa size ri = true -> pamr size (rmap size ri) = ri.
  Proof.
    unfold valid_index, rmap, pamr; intros s ri.
    case_eq (toPair s ri); intros.
    rewrite <- H.
    rewrite fromPair_V2_prop.
    rewrite fromPair_toPair; auto.
    destruct s; unfold valid_reg_ssa in H0; auto.
    elim andb_prop with (1:=H0); auto.
  Qed.

  Lemma INJ' : forall size r1 i1 r2 i2, 
    valid_index size i1 = true ->
    valid_index size i2 = true ->
    pamr size (r1,i1) = pamr size (r2,i2) ->
    (r1,i1) = (r2,i2).
  Proof.
    intros s r1 i1 r2 i2 V1 V2 H.
    rewrite <- (BIJ1 s r1 i1); auto.
    rewrite <- (BIJ1 s r2 i2); auto.
    congruence.
  Qed.

  Lemma INJ : forall size r1 r2, 
    valid_reg_ssa size r1 = true ->
    valid_reg_ssa size r2 = true ->
    rmap size r1 = rmap size r2 ->
    r1 = r2.
  Proof.
    intros s r1 r2 V1 V2 H.
    rewrite <- (BIJ2 s r1); auto.
    rewrite <- (BIJ2 s r2); auto.
    congruence.
  Qed.

End Bij.
