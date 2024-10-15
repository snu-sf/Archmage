(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris                                  *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Assertions on memory states, in the style of separation logic *)

(** This library defines a number of useful logical assertions about
  CompCert memory states, such as "block [b] at offset [ofs] contains
  value [v]".  Assertions can be grouped using a separating conjunction
  operator in the style of separation logic.

  Currently, this library is used only in module [Stackingproof]
  to reason about the shapes of stack frames generated during the
  [Stacking] pass.

  This is not a full-fledged separation logic because there is no
  program logic (Hoare triples) to speak of.  Also, there is no general
  frame rule; instead, a weak form of the frame rule is provided
  by the lemmas that help us reason about the logical assertions. *)

Require Import Setoid Program.Basics.
Require Import Coqlib Decidableplus.
Require Import AST Integers Values Memory Events Globalenvs.

(** * Assertions about memory *)

(** An assertion is composed of:
- a predicate over memory states (of type [mem -> Prop])
- a set of (block, offset) memory locations that represents the memory footprint of the assertion
- a proof that the predicate is invariant by changes of memory outside of the footprint
- a proof that the footprint contains only valid memory blocks.

This presentation (where the footprint is part of the assertion) makes
it possible to define separating conjunction without explicitly
defining a separation algebra over CompCert memory states (i.e. the
notion of splitting a memory state into two disjoint halves).  *)

Record massert : Type := {
  m_pred : mem -> Prop;
  m_footprint: block -> Z -> Prop;
  m_invar: forall m m', m_pred m -> Mem.unchanged_on m_footprint m m' -> m_pred m';
  m_valid: forall m b ofs, m_pred m -> m_footprint b ofs -> Mem.valid_block m b
}.

Notation "m |= p" := (m_pred p m) (at level 74, no associativity) : sep_scope.

(** Implication and logical equivalence between memory predicates *)

Definition massert_imp (P Q: massert) : Prop :=
  (forall m, m_pred P m -> m_pred Q m) /\ (forall b ofs, m_footprint Q b ofs -> m_footprint P b ofs).
Definition massert_eqv (P Q: massert) : Prop :=
  massert_imp P Q /\ massert_imp Q P.

Remark massert_imp_refl: forall p, massert_imp p p.
Proof.
  unfold massert_imp; auto.
Qed.

Remark massert_imp_trans: forall p q r, massert_imp p q -> massert_imp q r -> massert_imp p r.
Proof.
  unfold massert_imp; intros. des. split; eauto.
Qed.

Remark massert_eqv_refl: forall p, massert_eqv p p.
Proof.
  unfold massert_eqv, massert_imp; intros. tauto.
Qed.

Remark massert_eqv_sym: forall p q, massert_eqv p q -> massert_eqv q p.
Proof.
  unfold massert_eqv, massert_imp; intros. tauto.
Qed.

Remark massert_eqv_trans: forall p q r, massert_eqv p q -> massert_eqv q r -> massert_eqv p r.
Proof.
  unfold massert_eqv, massert_imp; intros. des. esplits; eauto.
Qed.

(** Record [massert_eqv] and [massert_imp] as relations so that they can be used by rewriting tactics. *)
Add Relation massert massert_imp
  reflexivity proved by massert_imp_refl
  transitivity proved by massert_imp_trans
as massert_imp_prel.

Add Relation massert massert_eqv
  reflexivity proved by massert_eqv_refl
  symmetry proved by massert_eqv_sym
  transitivity proved by massert_eqv_trans
as massert_eqv_prel.

Add Morphism m_pred
  with signature massert_imp ==> eq ==> impl
  as m_pred_morph_1.
Proof.
  intros P Q [A B]. auto.
Qed.

Add Morphism m_pred
  with signature massert_eqv ==> eq ==> iff
  as m_pred_morph_2.
Proof.
  intros P Q [[A B] [C D]]. split; auto.
Qed.

Global Hint Resolve massert_imp_refl massert_eqv_refl : core.

(** * Separating conjunction *)

Definition disjoint_footprint (P Q: massert) : Prop :=
  forall b ofs, m_footprint P b ofs -> m_footprint Q b ofs -> False.

Program Definition sepconj (P Q: massert) : massert := {|
  m_pred := fun m => m_pred P m /\ m_pred Q m /\ disjoint_footprint P Q;
  m_footprint := fun b ofs => m_footprint P b ofs \/ m_footprint Q b ofs
|}.
Next Obligation.
  repeat split; auto.
  apply (m_invar P) with m; auto. eapply Mem.unchanged_on_implies; eauto. simpl; auto.
  apply (m_invar Q) with m; auto. eapply Mem.unchanged_on_implies; eauto. simpl; auto.
Qed.
Next Obligation.
  destruct H0; [eapply (m_valid P) | eapply (m_valid Q)]; eauto.
Qed.

Add Morphism sepconj
  with signature massert_imp ==> massert_imp ==> massert_imp
  as sepconj_morph_1.
Proof.
  intros P1 P2 [A B] Q1 Q2 [C D].
  red; simpl; split; intros.
- intuition auto. red; intros. apply (H2 b ofs); auto.
- intuition auto.
Qed.

Add Morphism sepconj
  with signature massert_eqv ==> massert_eqv ==> massert_eqv
  as sepconj_morph_2.
Proof.
  intros. destruct H, H0. split; apply sepconj_morph_1; auto.
Qed.

Infix "**" := sepconj (at level 60, right associativity) : sep_scope.

Local Open Scope sep_scope.

Lemma sep_imp:
  forall P P' Q Q' m,
  m |= P ** Q -> massert_imp P P' -> massert_imp Q Q' -> m |= P' ** Q'.
Proof.
  intros. rewrite <- H0, <- H1; auto.
Qed.

Lemma sep_comm_1:
  forall P Q,  massert_imp (P ** Q) (Q ** P).
Proof.
  unfold massert_imp; simpl; split; intros.
- intuition auto. red; intros; eapply H2; eauto.
- intuition auto.
Qed.

Lemma sep_comm:
  forall P Q, massert_eqv (P ** Q) (Q ** P).
Proof.
  intros; split; apply sep_comm_1.
Qed.

Lemma sep_assoc_1:
  forall P Q R, massert_imp ((P ** Q) ** R) (P ** (Q ** R)).
Proof.
  intros. unfold massert_imp, sepconj, disjoint_footprint; simpl.
  esplits; ii.
  { des. esplits; eauto. ii. des; eauto. }
  { des; eauto. }
Qed.

Lemma sep_assoc_2:
  forall P Q R, massert_imp (P ** (Q ** R)) ((P ** Q) ** R).
Proof.
  intros. unfold massert_imp, sepconj, disjoint_footprint; simpl.
  esplits; eauto; ii.
  { des. esplits; eauto. ii. des; eauto. }
  { des; eauto. }
Qed.

Lemma sep_assoc:
  forall P Q R, massert_eqv ((P ** Q) ** R) (P ** (Q ** R)).
Proof.
  intros; split. apply sep_assoc_1. apply sep_assoc_2.
Qed.

Lemma sep_swap:
  forall P Q R, massert_eqv (P ** Q ** R) (Q ** P ** R).
Proof.
  intros. rewrite <- sep_assoc. rewrite (sep_comm P). rewrite sep_assoc. reflexivity.
Qed.

Definition sep_swap12 := sep_swap.

Lemma sep_swap23:
  forall P Q R S, massert_eqv (P ** Q ** R ** S) (P ** R ** Q ** S).
Proof.
  intros. rewrite (sep_swap Q). reflexivity.
Qed.

Lemma sep_swap34:
  forall P Q R S T, massert_eqv (P ** Q ** R ** S ** T) (P ** Q ** S ** R ** T).
Proof.
  intros. rewrite (sep_swap R). reflexivity.
Qed.

Lemma sep_swap45:
  forall P Q R S T U, massert_eqv (P ** Q ** R ** S ** T ** U) (P ** Q ** R ** T ** S ** U).
Proof.
  intros. rewrite (sep_swap S). reflexivity.
Qed.

Definition sep_swap2 := sep_swap.

Lemma sep_swap3:
  forall P Q R S, massert_eqv (P ** Q ** R ** S) (R ** Q ** P ** S).
Proof.
  intros. rewrite sep_swap. rewrite (sep_swap P). rewrite sep_swap. reflexivity.
Qed.

Lemma sep_swap4:
  forall P Q R S T, massert_eqv (P ** Q ** R ** S ** T) (S ** Q ** R ** P ** T).
Proof.
  intros. rewrite sep_swap. rewrite (sep_swap3 P). rewrite sep_swap. reflexivity.
Qed.

Lemma sep_swap5:
  forall P Q R S T U, massert_eqv (P ** Q ** R ** S ** T ** U) (T ** Q ** R ** S ** P ** U).
Proof.
  intros. rewrite sep_swap. rewrite (sep_swap4 P). rewrite sep_swap. reflexivity.
Qed.

Lemma sep_drop:
  forall P Q m, m |= P ** Q -> m |= Q.
Proof.
  simpl; intros. tauto.
Qed.

Lemma sep_drop2:
  forall P Q R m, m |= P ** Q ** R -> m |= P ** R.
Proof.
  intros. rewrite sep_swap in H. eapply sep_drop; eauto.
Qed.

Lemma sep_proj1:
  forall Q P m, m |= P ** Q -> m |= P.
Proof.
  intros. destruct H; auto.
Qed.

Lemma sep_proj2:
  forall P Q m, m |= P ** Q -> m |= Q.
Proof sep_drop.

Definition sep_pick1 := sep_proj1.

Lemma sep_pick2:
  forall P Q R m, m |= P ** Q ** R -> m |= Q.
Proof.
  intros. eapply sep_proj1; eapply sep_proj2; eauto.
Qed.

Lemma sep_pick3:
  forall P Q R S m, m |= P ** Q ** R ** S -> m |= R.
Proof.
  intros. eapply sep_pick2; eapply sep_proj2; eauto.
Qed.

Lemma sep_pick4:
  forall P Q R S T m, m |= P ** Q ** R ** S ** T -> m |= S.
Proof.
  intros. eapply sep_pick3; eapply sep_proj2; eauto.
Qed.

Lemma sep_pick5:
  forall P Q R S T U m, m |= P ** Q ** R ** S ** T ** U -> m |= T.
Proof.
  intros. eapply sep_pick4; eapply sep_proj2; eauto.
Qed.

Lemma sep_preserved:
  forall m m' P Q,
  m |= P ** Q ->
  (m |= P -> m' |= P) ->
  (m |= Q -> m' |= Q) ->
  m' |= P ** Q.
Proof.
  simpl; intros. intuition auto.
Qed.

(** * Basic memory assertions. *)

(** Pure logical assertion *)

Program Definition pure (P: Prop) : massert := {|
  m_pred := fun m => P;
  m_footprint := fun b ofs => False
|}.
Next Obligation.
  tauto.
Qed.

Lemma sep_pure:
  forall P Q m, m |= pure P ** Q <-> P /\ m |= Q.
Proof.
  simpl; intros. intuition auto. red; simpl; tauto.
Qed.

(** A range of bytes, with full permissions and unspecified contents. *)

Program Definition range (b: block) (lo hi: Z) : massert := {|
  m_pred := fun m =>
       0 <= lo /\ hi <= Ptrofs.modulus
    /\ (forall i k p, lo <= i < hi -> Mem.perm m b i k p);
  m_footprint := fun b' ofs' => b' = b /\ lo <= ofs' < hi
|}.
Next Obligation.
  split; auto. split; auto. intros. eapply Mem.perm_unchanged_on; eauto. simpl; auto.
Qed.
Next Obligation.
  apply Mem.perm_valid_block with ofs Cur Freeable; auto.
Qed.

Lemma alloc_rule:
  forall m lo hi b m' P,
  Mem.alloc m lo hi = (m', b) ->
  0 <= lo -> hi <= Ptrofs.modulus ->
  m |= P ->
  m' |= range b lo hi ** P.
Proof.
  intros; simpl. split; [|split].
- split; auto. split; auto. intros.
  apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.perm_alloc_2; eauto.
- apply (m_invar P) with m; auto. eapply Mem.alloc_unchanged_on; eauto.
- red; simpl. intros. destruct H3; subst b0.
  eelim Mem.fresh_block_alloc; eauto. eapply (m_valid P); eauto.
Qed.

Lemma range_split:
  forall b lo hi P mid m,
  lo <= mid <= hi ->
  m |= range b lo hi ** P ->
  m |= range b lo mid ** range b mid hi ** P.
Proof.
  intros. rewrite <- sep_assoc. eapply sep_imp; eauto.
  split; simpl; intros.
- intuition auto.
+ lia.
+ apply H5; lia.
+ lia.
+ apply H5; lia.
+ red; simpl; intros; lia.
- intuition lia.
Qed.

Lemma range_drop_left:
  forall b lo hi P mid m,
  lo <= mid <= hi ->
  m |= range b lo hi ** P ->
  m |= range b mid hi ** P.
Proof.
  intros. apply sep_drop with (range b lo mid). apply range_split; auto.
Qed.

Lemma range_drop_right:
  forall b lo hi P mid m,
  lo <= mid <= hi ->
  m |= range b lo hi ** P ->
  m |= range b lo mid ** P.
Proof.
  intros. apply sep_drop2 with (range b mid hi). apply range_split; auto.
Qed.

Lemma range_split_2:
  forall b lo hi P mid al m,
  lo <= align mid al <= hi ->
  al > 0 ->
  m |= range b lo hi ** P ->
  m |= range b lo mid ** range b (align mid al) hi ** P.
Proof.
  intros. rewrite <- sep_assoc. eapply sep_imp; eauto.
  assert (mid <= align mid al) by (apply align_le; auto).
  split; simpl; intros.
- intuition auto.
+ lia.
+ apply H7; lia.
+ lia.
+ apply H7; lia.
+ red; simpl; intros; lia.
- intuition lia.
Qed.

Lemma range_preserved:
  forall m m' b lo hi,
  m |= range b lo hi ->
  (forall i k p, lo <= i < hi -> Mem.perm m b i k p -> Mem.perm m' b i k p) ->
  m' |= range b lo hi.
Proof.
  intros. destruct H as (A & B & C). simpl; intuition auto.
Qed.

(** A memory area that contains a value sastifying a given predicate *)

Program Definition contains (chunk: memory_chunk) (b: block) (ofs: Z) (spec: val -> Prop) : massert := {|
  m_pred := fun m =>
       0 <= ofs <= Ptrofs.max_unsigned
    /\ Mem.valid_access m chunk b ofs Freeable
    /\ Mem.change_check chunk (Mem.getN (size_chunk_nat chunk) ofs (Maps.PMap.get b (Mem.mem_contents m))) = false
    /\ exists v, Mem.load chunk m b ofs = Some v /\ spec v;
  m_footprint := fun b' ofs' => b' = b /\ ofs <= ofs' < ofs + size_chunk chunk
|}.
Next Obligation.
  Local Transparent Mem.loadbytes.
  rename H3 into v. split;[|split];[| | split].
- auto.
- destruct H1; split; auto. red; intros; eapply Mem.perm_unchanged_on; eauto. simpl; auto.
- exploit Mem.load_valid_access; eauto. i.
  exploit (Mem.loadbytes_unchanged_on_1 _ m m' b ofs (size_chunk chunk) H0); eauto with mem.
  i. unfold Mem.loadbytes in H7. des_ifs.
  2:{ exfalso. inv H3. clarify. }
  unfold size_chunk_nat in *. rewrite H7. auto.
- exists v. split; auto. rewrite <- H5. eapply Mem.load_unchanged_on_check_2; eauto.
+ ii. unfold Mem.loadbytes in H3. des_ifs.
+ eapply Mem.load_valid_access in H5. eauto with mem.
+ ii. ss.
Qed.
Next Obligation.
  eauto with mem.
Qed.

Lemma contains_no_overflow:
  forall spec m chunk b ofs,
  m |= contains chunk b ofs spec ->
  0 <= ofs <= Ptrofs.max_unsigned.
Proof.
  intros. simpl in H. tauto.
Qed.

Lemma load_rule:
  forall spec m chunk b ofs,
  m |= contains chunk b ofs spec ->
  exists v, Mem.load chunk m b ofs = Some v /\ spec v.
Proof.
  intros. destruct H as (D & E & F & v & G & H).
  exists v; auto.
Qed.

Lemma loadv_rule:
  forall spec m chunk b ofs,
  m |= contains chunk b ofs spec ->
  exists v, Mem.loadv chunk m (Vptr b (Ptrofs.repr ofs)) = Some v /\ spec v.
Proof.
  intros. exploit load_rule; eauto. intros (v & A & B). exists v; split; auto.
  unfold Mem.loadv.
  simpl. rewrite Ptrofs.unsigned_repr; auto. eapply contains_no_overflow; eauto.
Qed.

(* move to memory.v *)
Lemma store_unchange_bytes
    chunk m b ofs v m'
    (STORE : Mem.store chunk m b ofs v = Some m'):
  <<ENC: Mem.change_check chunk (Mem.getN (size_chunk_nat chunk) ofs (Maps.PMap.get b (Mem.mem_contents m'))) = false>>.
Proof.
  Local Transparent Mem.store. unfold Mem.store in STORE. des_ifs. ss. rewrite Maps.PMap.gss.
  erewrite <- (encode_val_length chunk v). erewrite Mem.getN_setN_same. eapply Mem.encode_val_change_check_false.
Qed.

Lemma store_rule:
  forall chunk m b ofs v (spec1 spec: val -> Prop) P,
  m |= contains chunk b ofs spec1 ** P ->
  spec (Val.load_result chunk v) ->
  exists m',
  Mem.store chunk m b ofs v = Some m' /\ m' |= contains chunk b ofs spec ** P.
Proof.
  intros. destruct H as (A & B & C). destruct A as (D & E & F & v0 & G & H').
  assert (H: Mem.valid_access m chunk b ofs Writable) by eauto with mem.
  destruct (Mem.valid_access_store _ _ _ _ v H) as [m' STORE].
  exists m'; split; auto. simpl. intuition auto.
- eapply Mem.store_valid_access_1; eauto.
- eapply store_unchange_bytes in STORE. des. eauto.
- exists (Val.load_result chunk v); split; auto. eapply Mem.load_store_same; eauto.
- apply (m_invar P) with m; auto.
  eapply Mem.store_unchanged_on; eauto.
  intros; red; intros. apply (C b i); simpl; auto.
Qed.

Lemma storev_rule:
  forall chunk m b ofs v (spec1 spec: val -> Prop) P,
  m |= contains chunk b ofs spec1 ** P ->
  spec (Val.load_result chunk v) ->
  exists m',
  Mem.storev chunk m (Vptr b (Ptrofs.repr ofs)) v = Some m' /\ m' |= contains chunk b ofs spec ** P.
Proof.
  intros. exploit store_rule; eauto. intros (m' & A & B). exists m'; split; auto.
  simpl. rewrite Ptrofs.unsigned_repr; auto. eapply contains_no_overflow. eapply sep_pick1; eauto.
Qed.

(* undefined area *)
Program Definition undef_area (b: block) (lo hi: Z) : massert := {|
  m_pred := fun m =>
       0 <= lo /\ hi <= Ptrofs.max_unsigned
    /\ (exists bytes, Mem.loadbytes m b lo (hi - lo) = Some bytes /\ bytes_all_undef bytes = true);
  m_footprint := fun b' ofs' => b' = b /\ lo <= ofs' < hi
|}.
Next Obligation.
  split; auto. split; auto. rename H2 into bytes.
  exploit Mem.loadbytes_unchanged_on; eauto. ss; lia.
Qed.
Next Obligation.
  Local Transparent Mem.loadbytes. unfold Mem.loadbytes in *. des_ifs.
  specialize (r lo). eapply Mem.perm_valid_block. eapply r. lia.
Qed.

(* move to memory.v *)

Lemma undef_all_bytes_sublist
  bytes bytes0 bytes1
  (UNDEF: bytes_all_undef bytes = true)
  (APP: bytes = bytes0 ++ bytes1):
  <<UNDEF: bytes_all_undef bytes0 = true /\ bytes_all_undef bytes1 = true>>.
Proof.
  ginduction bytes; ss; ii.
  { destruct bytes0; ss. destruct bytes1; ss. }
  destruct bytes0; ss.
  - destruct bytes1; ss. clarify.
  - clarify. eapply andb_prop in UNDEF. des. exploit IHbytes; eauto. i. des.
    rewrite H, H0, UNDEF. ss.
Qed.

Lemma undef_area_split
  b lo hi P mid m
  (INRANGE: lo <= mid <= hi)
  (UNDEF: m |= undef_area b lo hi ** P) :
  <<UNDEFS: m |= undef_area b lo mid ** undef_area b mid hi ** P>>.
Proof.
  r. rewrite <- sep_assoc. eapply sep_imp; eauto.
  split; ss; i.
- intuition auto.
+ lia.
+ des. replace (hi - lo) with ((mid - lo) + (hi - mid)) in H8 by lia.
  exploit Mem.loadbytes_split; try eapply H8; try lia. i. des. esplits; eauto.
  exploit undef_all_bytes_sublist; try eapply H13; eauto. i. des; eauto.
+ lia.
+ des. replace (hi - lo) with ((mid - lo) + (hi - mid)) in H8 by lia.
  exploit Mem.loadbytes_split; try eapply H8; try lia. i. des.
  replace (lo + (mid - lo)) with mid in H12 by lia. esplits; eauto.
  exploit undef_all_bytes_sublist; try eapply H13; eauto. i. des; eauto.
+ red; simpl; intros; lia.
- intuition lia.
Qed.

Lemma undef_area_drop_left
  b lo hi P mid m
  (INRANGE: lo <= mid <= hi)
  (UNDEF: m |= undef_area b lo hi ** P):
  <<UNDEF: m |= undef_area b mid hi ** P>>.
Proof.
  i. apply sep_drop with (undef_area b lo mid). apply undef_area_split; auto.
Qed.

Lemma undef_area_drop_right
  b lo hi P mid m
  (INRANGE: lo <= mid <= hi)
  (UNDEF: m |= undef_area b lo hi ** P):
  <<UNDEF: m |= undef_area b lo mid ** P>>.
Proof.
  i. apply sep_drop2 with (undef_area b mid hi). apply undef_area_split; auto.
Qed.

(* move to memory.v *)
Lemma loadbytes_divide
  m b lo hi mid bytes bytes1 bytes2
  (RANGE: lo <= mid <= hi)
  (LB1: Mem.loadbytes m b lo (hi - lo) = Some bytes)
  (LB2: Mem.loadbytes m b lo (mid - lo) = Some bytes1)
  (LB3: Mem.loadbytes m b mid (hi - mid) = Some bytes2):
  <<BYTES: bytes = bytes1 ++ bytes2>>.
Proof.
  unfold Mem.loadbytes in *. des_ifs.
  replace (hi - lo) with ((mid - lo) + (hi - mid)) by lia. rewrite Z2Nat.inj_add; try lia.
  rewrite Mem.getN_concat. rewrite Z2Nat.id; try lia. replace (lo + (mid - lo)) with mid by lia. ss.
Qed.

Lemma undef_all_bytes_sublist2
  m b ofs sz bytes bytes' lo hi
  (LB1: Mem.loadbytes m b ofs sz = Some bytes)
  (BYTES: bytes_all_undef bytes = true)
  (LB2: Mem.loadbytes m b lo (hi - lo) = Some bytes')
  (IN1: ofs <= lo <= ofs + sz)
  (IN2: ofs <= hi <= ofs + sz):
  <<BYTES: bytes_all_undef bytes' = true>>.
Proof.
  destruct (Z_le_gt_dec lo hi); cycle 1.
  { rewrite Mem.loadbytes_empty in LB2; try lia. clarify. }
  assert (Mem.range_perm m b ofs (ofs + sz) Cur Readable).
  { eapply Mem.loadbytes_range_perm; eauto. }
  assert (Mem.range_perm m b lo (ofs + sz) Cur Readable).
  { r. i. eapply H. lia. }
  assert (Mem.range_perm m b ofs lo Cur Readable).
  { r. i. eapply H. lia. }
  replace (ofs + sz) with (lo + (ofs + sz - lo)) in H0 by lia.
  replace lo with (ofs + (lo - ofs)) in H1 by lia.
  replace sz with (ofs + sz - ofs) in LB1 by lia.
  exploit Mem.range_perm_loadbytes; try eapply H0. i. des.
  exploit Mem.range_perm_loadbytes; try eapply H1. i. des.
  exploit loadbytes_divide. 2:{ eapply LB1. } 2:{ eapply H3. } 2:{ eapply H2. } lia. i.
  exploit undef_all_bytes_sublist; try eapply H4; eauto. i. des.
  clear H H1 H3 H4 H5. replace (lo + (ofs + sz - lo)) with (ofs + sz) in H0 by lia.
  assert (Mem.range_perm m b hi (ofs + sz) Cur Readable).
  { ii. eapply H0. lia. }
  assert (Mem.range_perm m b lo hi Cur Readable).
  { ii. eapply H0. lia. }
  replace (ofs + sz) with (hi + (ofs + sz - hi)) in H by lia.
  replace hi with (lo + (hi - lo)) in H1 by lia. 
  exploit Mem.range_perm_loadbytes; try eapply H. i. des.
  exploit Mem.range_perm_loadbytes; try eapply H1. i. des.
  exploit loadbytes_divide. 3:{ eapply H4. } 3:{ eapply H3. } 2:{ eapply H2. } lia. i.
  exploit undef_all_bytes_sublist; try eapply H4; eauto. i. des. clarify.
Qed.
  
Lemma undef_area_split_2
  b lo hi P mid al m
  (INRANGE: lo <= align mid al <= hi)
  (MID: lo <= mid)
  (LEN: al > 0)
  (UNDEF: m |= undef_area b lo hi ** P) :
  <<UNDEFS: m |= undef_area b lo mid ** undef_area b (align mid al) hi ** P>>.
Proof.
  r. rewrite <- sep_assoc. eapply sep_imp; eauto.
  assert (mid <= align mid al) by (apply align_le; auto).
  split; simpl; intros.
- intuition auto.
+ lia.
+ des. replace (hi - lo) with ((mid - lo) + (hi - mid)) in H5 by lia.
  exploit Mem.loadbytes_split; try eapply H5; try lia.
  i. des. esplits; eauto.
  exploit undef_all_bytes_sublist; try eapply H8; eauto. i. des; eauto.
+ lia.
+ des.
  assert (Mem.range_perm m0 b lo (lo + (hi - lo)) Cur Readable).
  { eapply Mem.loadbytes_range_perm; eauto. }
  assert (Mem.range_perm m0 b (align mid al) ((align mid al) + (hi - (align mid al))) Cur Readable).
  { r in H6. r. ii. eapply H6. lia. }
  exploit Mem.range_perm_loadbytes; try eapply H7. i. des. esplits; eauto.
  exploit undef_all_bytes_sublist2. eapply H5. eauto. eapply H8. lia. lia. i. eauto.
+ red; simpl; intros; lia.
- intuition lia.
Qed.

Program Definition Tmassert : massert := {|
  m_pred := fun m => True;
  m_footprint := fun b ofs => False
|}.
Next Obligation.
  clarify.
Qed.

Lemma range_contains:
  forall chunk b ofs P m (ENC: Mem.change_check chunk (Mem.getN (size_chunk_nat chunk) ofs (Maps.PMap.get b (Mem.mem_contents m))) = false),
  m |= range b ofs (ofs + size_chunk chunk) ** P ->
  (align_chunk chunk | ofs) ->
  m |= contains chunk b ofs (fun v => True) ** P.
Proof.
  intros. destruct H as (A & B & C). destruct A as (D & E & F).
  split; [|split].
- assert (Mem.valid_access m chunk b ofs Freeable).
  { split; auto. red; auto. }
  split. generalize (size_chunk_pos chunk). unfold Ptrofs.max_unsigned. lia.
  split. auto.
  split.
+ auto.
+ destruct (Mem.valid_access_load m chunk b ofs) as [v LOAD].
  eauto with mem.
  exists v; auto.
- auto.
- auto.
Qed.

Lemma contains_imp:
  forall (spec1 spec2: val -> Prop) chunk b ofs,
  (forall v, spec1 v -> spec2 v) ->
  massert_imp (contains chunk b ofs spec1) (contains chunk b ofs spec2).
Proof.
  intros; split; simpl; intros.
- intuition auto. destruct H5 as (v & A & B). exists v; auto.
- auto.
Qed.

(** A memory area that contains a given value *)

Definition hasvalue (chunk: memory_chunk) (b: block) (ofs: Z) (v: val) : massert :=
  contains chunk b ofs (fun v' => v' = v).

Lemma store_rule':
  forall chunk m b ofs v (spec1: val -> Prop) P,
  m |= contains chunk b ofs spec1 ** P ->
  exists m',
  Mem.store chunk m b ofs v = Some m' /\ m' |= hasvalue chunk b ofs (Val.load_result chunk v) ** P.
Proof.
  intros. eapply store_rule; eauto.
Qed.

Lemma storev_rule':
  forall chunk m b ofs v (spec1: val -> Prop) P,
  m |= contains chunk b ofs spec1 ** P ->
  exists m',
  Mem.storev chunk m (Vptr b (Ptrofs.repr ofs)) v = Some m' /\ m' |= hasvalue chunk b ofs (Val.load_result chunk v) ** P.
Proof.
  intros. eapply storev_rule; eauto.
Qed.

(** Non-separating conjunction *)

Program Definition mconj (P Q: massert) : massert := {|
  m_pred := fun m => m_pred P m /\ m_pred Q m;
  m_footprint := fun b ofs => m_footprint P b ofs \/ m_footprint Q b ofs
|}.
Next Obligation.
  split.
  apply (m_invar P) with m; auto. eapply Mem.unchanged_on_implies; eauto. simpl; auto.
  apply (m_invar Q) with m; auto. eapply Mem.unchanged_on_implies; eauto. simpl; auto.
Qed.
Next Obligation.
  destruct H0; [eapply (m_valid P) | eapply (m_valid Q)]; eauto.
Qed.

Lemma mconj_intro:
  forall P Q R m,
  m |= P ** R -> m |= Q ** R -> m |= mconj P Q ** R.
Proof.
  intros. destruct H as (A & B & C). destruct H0 as (D & E & F).
  split; [|split].
- simpl; auto.
- auto.
- red; simpl; intros. destruct H; [eelim C | eelim F]; eauto.
Qed.

Lemma mconj_proj1:
  forall P Q R m, m |= mconj P Q ** R -> m |= P ** R.
Proof.
  intros. destruct H as (A & B & C); simpl in A.
  simpl. intuition auto.
  red; intros; eapply C; eauto; simpl; auto.
Qed.

Lemma mconj_proj2:
  forall P Q R m, m |= mconj P Q ** R -> m |= Q ** R.
Proof.
  intros. destruct H as (A & B & C); simpl in A.
  simpl. intuition auto.
  red; intros; eapply C; eauto; simpl; auto.
Qed.

Lemma frame_mconj:
  forall P P' Q R m m',
  m |= mconj P Q ** R ->
  m' |= P' ** R ->
  m' |= Q ->
  m' |= mconj P' Q ** R.
Proof.
  intros. destruct H as (A & B & C); simpl in A.
  destruct H0 as (D & E & F).
  simpl. intuition auto.
  red; simpl; intros. destruct H2. eapply F; eauto. eapply C; simpl; eauto.
Qed.

Add Morphism mconj
  with signature massert_imp ==> massert_imp ==> massert_imp
  as mconj_morph_1.
Proof.
  intros P1 P2 [A B] Q1 Q2 [C D].
  red; simpl; intuition auto.
Qed.

Add Morphism mconj
  with signature massert_eqv ==> massert_eqv ==> massert_eqv
  as mconj_morph_2.
Proof.
  intros. destruct H, H0. split; apply mconj_morph_1; auto.
Qed.

Lemma range_contains':
  forall chunk b ofs P Q m,
  m |= range b ofs (ofs + size_chunk chunk) ** P ->
  m |= (undef_area b ofs (ofs + size_chunk chunk)) ** Q ->
  (align_chunk chunk | ofs) ->
  m |= contains chunk b ofs (fun v => True) ** P.
Proof.
  intros. destruct H as (A & B & C). rename H0 into A'. destruct A as (D & E & F).
  split; [|split].
- assert (Mem.valid_access m chunk b ofs Freeable).
  { split; auto. red; auto. }
  split. generalize (size_chunk_pos chunk). unfold Ptrofs.max_unsigned. lia.
  split. auto.
  split.
+ inv A'. inv H0. des. replace (ofs + (size_chunk chunk) - ofs) with (size_chunk chunk) in H0 by lia.
  unfold Mem.loadbytes in H0. des_ifs.
  eapply Mem.bytes_all_undef_not_change; eauto. destruct chunk; ss.
  (* unfold Mem.encoded_bytes, size_chunk_nat. rewrite H5. eapply orb_true_r. *)
+ destruct (Mem.valid_access_load m chunk b ofs) as [v LOAD].
  eauto with mem.
  exists v; auto.
- auto.
- unfold disjoint_footprint in *; ii. eapply C; eauto.
Qed.

Lemma undef_contains:
  forall chunk b ofs P Q m,
  m |= range b ofs (ofs + size_chunk chunk) ** P ->
  m |= (undef_area b ofs (ofs + size_chunk chunk)) ** Q ->
  (align_chunk chunk | ofs) ->
  m |= contains chunk b ofs (fun v => True) ** Q.
Proof.
  intros. destruct H as (A & B & C). rename H0 into A'. destruct A as (D & E & F).
  split; [|split].
- assert (Mem.valid_access m chunk b ofs Freeable).
  { split; auto. red; auto. }
  split. generalize (size_chunk_pos chunk). unfold Ptrofs.max_unsigned. lia.
  split. auto.
  split.
+ inv A'. inv H0. des. replace (ofs + (size_chunk chunk) - ofs) with (size_chunk chunk) in H0 by lia.
  unfold Mem.loadbytes in H0. des_ifs.
  eapply Mem.bytes_all_undef_not_change; eauto. destruct chunk; ss.
  (* unfold Mem.encoded_bytes, size_chunk_nat. rewrite H5. eapply orb_true_r. *)
+ destruct (Mem.valid_access_load m chunk b ofs) as [v LOAD].
  eauto with mem.
  exists v; auto.
- inv A'. des. auto.
- inv A'. des. unfold disjoint_footprint in *; ii. eapply H2; eauto.
Qed.

(** The image of a memory injection *)

Program Definition minjection (j: meminj) (m0: mem) : massert := {|
  m_pred := fun m => Mem.inject j m0 m;
  m_footprint := fun b ofs => exists b0 delta, j b0 = Some(b, delta) /\ Mem.perm m0 b0 (ofs - delta) Max Nonempty
|}.
Next Obligation.
  set (img := fun b' ofs => exists b delta, j b = Some(b', delta) /\ Mem.perm m0 b (ofs - delta) Max Nonempty) in *.
  assert (IMG: forall b1 b2 delta ofs k p,
           j b1 = Some (b2, delta) -> Mem.perm m0 b1 ofs k p -> img b2 (ofs + delta)).
  { intros. red. exists b1, delta; split; auto.
    replace (ofs + delta - delta) with ofs by lia.
    eauto with mem. }
  destruct H. constructor.
- destruct mi_inj. constructor; intros.
+ eapply Mem.perm_unchanged_on; eauto.
+ eauto.
+ rewrite (Mem.unchanged_on_contents _ _ _ H0); eauto.
- assumption.
- intros. eapply Mem.valid_block_unchanged_on; eauto.
- assumption.
- assumption.
- intros. destruct (Mem.perm_dec m0 b1 ofs Max Nonempty); auto.
  eapply mi_perm_inv; eauto.
  eapply Mem.perm_unchanged_on_2; eauto.
- inv H0. i. eapply unchanged_concrete; eauto.
- eauto.
Qed.
Next Obligation.
  eapply Mem.valid_block_inject_2; eauto.
Qed.

Lemma loadv_parallel_rule:
  forall j m1 m2 chunk addr1 v1 addr2,
  m2 |= minjection j m1 ->
  Mem.loadv chunk m1 addr1 = Some v1 ->
  Val.inject j addr1 addr2 ->
  exists v2, Mem.loadv chunk m2 addr2 = Some v2 /\ Val.inject j v1 v2.
Proof.
  intros. simpl in H. eapply Mem.loadv_inject; eauto.
Qed.

Lemma storev_parallel_rule:
  forall j m1 m2 P chunk addr1 v1 m1' addr2 v2,
  m2 |= minjection j m1 ** P ->
  Mem.storev chunk m1 addr1 v1 = Some m1' ->
  Val.inject j addr1 addr2 ->
  Val.inject j v1 v2 ->
  exists m2', Mem.storev chunk m2 addr2 v2 = Some m2' /\ m2' |= minjection j m1' ** P.
Proof.
  intros. destruct H as (A & B & C). simpl in A.
  exploit Mem.storev_mapped_inject; eauto. intros (m2' & STORE & INJ).
  inv H1; simpl in STORE; try discriminate.
  { esplits; eauto.
    unfold Mem.storev in H0. des_ifs.
    exploit Mem.denormalize_inject; try eapply Heq1; eauto.
    i. des. clarify. inv VINJ.
    rename b0 into b1. rename b into b2. rename z into ofs2. rename z0 into ofs1.
    assert (VALID: Mem.valid_access m1 chunk b1 ofs1 Writable)
      by eauto with mem.
    eapply Mem.denormalize_in_range in Heq1, DENOTGT.
    assert (OFS1: ofs1 = Ptrofs.unsigned (Ptrofs.repr ofs1)).
    { rewrite Ptrofs.unsigned_repr; eauto. unfold Ptrofs.max_unsigned. des; lia. }
    exploit Mem.mi_representable; try eapply A; eauto.
    { left. eapply Mem.store_valid_access_3 in H0.
      eapply (Mem.valid_access_perm _ _ _ _ Cur) in H0.
      eapply Mem.perm_cur_max. rewrite OFS1 in H0.
      eapply Mem.perm_implies; eauto. eapply perm_any_N. }
    i.
    assert (ofs2 = ofs1 + delta).
    { rewrite Ptrofs.add_unsigned in H6.
      do 2 rewrite Ptrofs.unsigned_repr in H6; unfold Ptrofs.max_unsigned in *; try ( by (des; lia)).
      assert (Ptrofs.unsigned (Ptrofs.repr ofs2) = Ptrofs.unsigned (Ptrofs.repr (ofs1 + delta))).
      { rewrite H6. eauto. }
      do 2 rewrite Ptrofs.unsigned_repr in H1; unfold Ptrofs.max_unsigned in *; try ( by (des; lia)). }
    split; [|split].
    - exact INJ.
    - apply (m_invar P) with m2; auto.
      eapply Mem.store_unchanged_on; eauto.
      intros; red; intros. eelim C; eauto. simpl.
      exists b1, delta; split; auto. destruct VALID as [V1 V2].
      apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
      apply V1. lia.
    - red; simpl; intros. destruct H3 as (b0 & delta0 & U & V).
      eelim C; eauto. simpl. exists b0, delta0; eauto with mem. }
  assert (VALID: Mem.valid_access m1 chunk b1 (Ptrofs.unsigned ofs1) Writable)
    by eauto with mem.
  assert (EQ: Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta).
  { eapply Mem.address_inject'; eauto with mem. }
  exists m2'; split; auto.
  split; [|split].
- exact INJ.
- apply (m_invar P) with m2; auto.
  eapply Mem.store_unchanged_on; eauto.
  intros; red; intros. eelim C; eauto. simpl.
  exists b1, delta; split; auto. destruct VALID as [V1 V2].
  apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
  apply V1. omega.
- red; simpl; intros. destruct H1 as (b0 & delta0 & U & V).
  eelim C; eauto. simpl. exists b0, delta0; eauto with mem.
Qed.

Lemma alloc_undef_rule
  m1 lo hi m1' b1
  (LO: 0 <= lo) (HI: hi <= Ptrofs.max_unsigned)
  (ALLOC: Mem.alloc m1 lo hi = (m1', b1)):
  <<UNDEF: m1' |= undef_area b1 lo hi>>.
Proof.
  repeat split; eauto.
  assert (Mem.range_perm m1' b1 lo hi Cur Readable).
  { ii. exploit Mem.perm_alloc_2; eauto. instantiate (1:=Cur). i.
    eapply Mem.perm_implies; eauto. eapply perm_F_any. }
  unfold Mem.loadbytes. replace (lo + (hi - lo)) with hi by lia. des_ifs_safe.
  esplits; eauto. Local Transparent Mem.alloc. injection ALLOC. i; subst. ss.
  rewrite Maps.PMap.gss; eauto. remember (Z.to_nat (hi - lo)) as n. clear.
  ginduction n; ss; ii. rewrite IHn. rewrite Maps.ZMap.gi. ss.
Qed.

Lemma alloc_parallel_rule:
  forall m1 sz1 m1' b1 m2 sz2 m2' b2 P j lo hi delta,
  m2 |= minjection j m1 ** P ->
  Mem.alloc m1 0 sz1 = (m1', b1) ->
  Mem.alloc m2 0 sz2 = (m2', b2) ->
  (8 | delta) ->
  lo = delta ->
  hi = delta + Z.max 0 sz1 ->
  0 <= sz2 <= Ptrofs.max_unsigned ->
  0 <= delta -> hi <= sz2 ->
  exists j',
     m2' |= range b2 0 lo ** range b2 hi sz2 ** minjection j' m1' ** P
  /\ inject_incr j j'
  /\ j' b1 = Some(b2, delta)
  /\ (forall b, b <> b1 -> j' b = j b) /\ m2' |= undef_area b2 0 lo ** undef_area b2 hi sz2 ** minjection j' m1' ** P.
Proof.
  intros until delta; intros SEP ALLOC1 ALLOC2 ALIGN LO HI RANGE1 RANGE2 RANGE3.
  assert (RANGE4: lo <= hi) by extlia.
  assert (FRESH1: ~Mem.valid_block m1 b1) by (eapply Mem.fresh_block_alloc; eauto).
  assert (FRESH2: ~Mem.valid_block m2 b2) by (eapply Mem.fresh_block_alloc; eauto).
  destruct SEP as (INJ & SP & DISJ). simpl in INJ.
  exploit Mem.alloc_left_mapped_inject.
- eapply Mem.alloc_right_inject; eauto.
- eexact ALLOC1.
- instantiate (1 := b2). eauto with mem.
- instantiate (1 := delta). extlia.
- intros. assert (0 <= ofs < sz2) by (eapply Mem.perm_alloc_3; eauto). lia.
- intros. apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.perm_alloc_2; eauto. extlia.
- red; intros. apply Z.divide_trans with 8; auto.
  exists (8 / align_chunk chunk). destruct chunk; reflexivity.
- intros. elim FRESH2. eapply Mem.valid_block_inject_2; eauto.
- intros (j' & INJ' & J1 & J2 & J3).
  exists j'; split; auto; [|split; auto]; [|split; auto]; [|split; auto]; cycle 1.
{ rewrite <- ! sep_assoc.
  assert (PERM: Mem.range_perm m2' b2 0 sz2 Cur Readable).
  { eapply (Mem.range_perm_implies _ _ _ _ _ Freeable); [|eapply perm_F_any].
    ii. eapply Mem.perm_alloc_2; eauto. }
  split; [|split]. 
  + simpl. intuition auto; try (unfold Ptrofs.max_unsigned in *; lia).
    * assert (Mem.range_perm m2' b2 0 lo Cur Readable).
      { r in PERM. ii. eapply PERM. lia. }
      replace lo with (0 + lo) in H1 by lia. replace (lo - 0) with lo by lia.
      exploit Mem.range_perm_loadbytes; eauto. i. des. esplits; eauto.
      replace sz2 with (0 + sz2) in PERM by lia.
      exploit Mem.range_perm_loadbytes; try eapply PERM. i. des.
      assert (bytes_all_undef bytes0 = true).
      { unfold bytes_all_undef. rewrite forallb_forall. i.
        exploit Mem.loadbytes_alloc_same; try eapply ALLOC2; eauto.
        i. subst. ss. }
      replace lo with (lo - 0) in H2 by lia.
      eapply undef_all_bytes_sublist2; eauto; try lia.
    * assert (Mem.range_perm m2' b2 hi sz2 Cur Readable).
      { r in PERM. ii. eapply PERM. lia. }
      replace sz2 with (hi + (sz2 - hi)) in H1 by lia. exploit Mem.range_perm_loadbytes; try eapply H1. i. des.
      replace sz2 with (0 + sz2) in PERM by lia. exploit Mem.range_perm_loadbytes; try eapply PERM. i. des.
      esplits; eauto.
      assert (bytes_all_undef bytes0 = true).
      { unfold bytes_all_undef. rewrite forallb_forall. i.
        exploit Mem.loadbytes_alloc_same; try eapply ALLOC2; eauto.
        i. subst. ss. }
      eapply undef_all_bytes_sublist2; eauto; try lia.
    * red; simpl; intros. destruct H1, H2. lia.
    * red; simpl; intros.
      assert (b = b2) by tauto. subst b.
      assert (0 <= ofs < lo \/ hi <= ofs < sz2) by tauto. clear H1.
      destruct H2 as (b0 & delta0 & D & E).
      eapply Mem.perm_alloc_inv in E; eauto.
      destruct (eq_block b0 b1).
      subst b0. rewrite J2 in D. inversion D; clear D; subst delta0. extlia.
      rewrite J3 in D by auto. elim FRESH2. eapply Mem.valid_block_inject_2; eauto.
  + apply (m_invar P) with m2; auto. eapply Mem.alloc_unchanged_on; eauto.
  + red; simpl; intros.
    assert (VALID: Mem.valid_block m2 b) by (eapply (m_valid P); eauto).
    destruct H as [A | (b0 & delta0 & A & B)].
    * assert (b = b2) by tauto. subst b. contradiction.
    * eelim DISJ; eauto. simpl.
      eapply Mem.perm_alloc_inv in B; eauto.
      destruct (eq_block b0 b1).
      subst b0. rewrite J2 in A. inversion A; clear A; subst b delta0. contradiction.
      rewrite J3 in A by auto. exists b0, delta0; auto.
}
  rewrite <- ! sep_assoc.
  split; [|split].
+ simpl. intuition auto; try (unfold Ptrofs.max_unsigned in *; lia).
* apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.perm_alloc_2; eauto. lia.
* apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.perm_alloc_2; eauto. lia.
* red; simpl; intros. destruct H1, H2. lia.
* red; simpl; intros.
  assert (b = b2) by tauto. subst b.
  assert (0 <= ofs < lo \/ hi <= ofs < sz2) by tauto. clear H1.
  destruct H2 as (b0 & delta0 & D & E).
  eapply Mem.perm_alloc_inv in E; eauto.
  destruct (eq_block b0 b1).
  subst b0. rewrite J2 in D. inversion D; clear D; subst delta0. extlia.
  rewrite J3 in D by auto. elim FRESH2. eapply Mem.valid_block_inject_2; eauto.
+ apply (m_invar P) with m2; auto. eapply Mem.alloc_unchanged_on; eauto.
+ red; simpl; intros.
  assert (VALID: Mem.valid_block m2 b) by (eapply (m_valid P); eauto).
  destruct H as [A | (b0 & delta0 & A & B)].
* assert (b = b2) by tauto. subst b. contradiction.
* eelim DISJ; eauto. simpl.
  eapply Mem.perm_alloc_inv in B; eauto.
  destruct (eq_block b0 b1).
  subst b0. rewrite J2 in A. inversion A; clear A; subst b delta0. contradiction.
  rewrite J3 in A by auto. exists b0, delta0; auto.
Qed.

Lemma free_parallel_rule:
  forall j m1 b1 sz1 m1' m2 b2 sz2 lo hi delta P,
  m2 |= range b2 0 lo ** range b2 hi sz2 ** minjection j m1 ** P ->
  Mem.free m1 b1 0 sz1 = Some m1' ->
  j b1 = Some (b2, delta) ->
  lo = delta -> hi = delta + Z.max 0 sz1 ->
  exists m2',
     Mem.free m2 b2 0 sz2 = Some m2'
  /\ m2' |= minjection j m1' ** P.
Proof.
  intros. rewrite <- ! sep_assoc in H.
  destruct H as (A & B & C).
  destruct A as (D & E & F).
  destruct D as (J & K & L).
  destruct J as (_ & _ & J). destruct K as (_ & _ & K).
  simpl in E.
  assert (PERM: Mem.range_perm m2 b2 0 sz2 Cur Freeable).
  { red; intros.
    destruct (zlt ofs lo). apply J; lia.
    destruct (zle hi ofs). apply K; lia.
    replace ofs with ((ofs - delta) + delta) by lia.
    eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. extlia.
  }
  destruct (Mem.range_perm_free _ _ _ _ PERM) as [m2' FREE].
  exists m2'; split; auto. split; [|split].
- simpl. eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
  intros. apply (F b2 (ofs + delta0)).
+ simpl.
  destruct (zlt (ofs + delta0) lo). intuition auto.
  destruct (zle hi (ofs + delta0)). intuition auto.
  destruct (eq_block b0 b1).
* subst b0. rewrite H1 in H; inversion H; clear H; subst delta0.
  eelim (Mem.perm_free_2 m1); eauto. extlia.
* exploit Mem.mi_no_overlap; eauto.
  apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
  eapply Mem.perm_free_3; eauto.
  apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
  eapply (Mem.free_range_perm m1); eauto.
  instantiate (1 := ofs + delta0 - delta). extlia.
  intros [X|X]. congruence. lia.
+ simpl. exists b0, delta0; split; auto.
  replace (ofs + delta0 - delta0) with ofs by lia.
  apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
  eapply Mem.perm_free_3; eauto.
- apply (m_invar P) with m2; auto.
  eapply Mem.free_unchanged_on; eauto.
  intros; red; intros. eelim C; eauto. simpl.
  destruct (zlt i lo). intuition auto.
  destruct (zle hi i). intuition auto.
  right; exists b1, delta; split; auto.
  apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.free_range_perm; eauto. extlia.
- red; simpl; intros. eelim C; eauto.
  simpl. right. destruct H as (b0 & delta0 & U & V).
  exists b0, delta0; split; auto.
  eapply Mem.perm_free_3; eauto.
Qed.

(** Preservation of a global environment by a memory injection *)

Inductive globalenv_preserved {F V: Type} (ge: Genv.t F V) (j: meminj) (bound: block) : Prop :=
  | globalenv_preserved_intro
      (DOMAIN: forall b, Plt b bound -> j b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, j b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> Plt b bound)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> Plt b bound)
      (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> Plt b bound).

Program Definition globalenv_inject {F V: Type} (ge: Genv.t F V) (j: meminj) : massert := {|
  m_pred := fun m => exists bound, Ple bound (Mem.nextblock m) /\ globalenv_preserved ge j bound;
  m_footprint := fun b ofs => False
|}.
Next Obligation.
  rename H into bound. exists bound; split; auto. eapply Ple_trans; eauto. eapply Mem.unchanged_on_nextblock; eauto.
Qed.
Next Obligation.
  tauto.
Qed.

Lemma globalenv_inject_preserves_globals:
  forall (F V: Type) (ge: Genv.t F V) j m,
  m |= globalenv_inject ge j ->
  meminj_preserves_globals ge j.
Proof.
  intros. destruct H as (bound & A & B). destruct B.
  split; [|split]; intros.
- eauto.
- eauto.
- symmetry; eauto.
Qed.

Lemma globalenv_inject_incr:
  forall j m0 (F V: Type) (ge: Genv.t F V) m j' P,
  inject_incr j j' ->
  inject_separated j j' m0 m ->
  m |= globalenv_inject ge j ** P ->
  m |= globalenv_inject ge j' ** P.
Proof.
  intros. destruct H1 as (A & B & C). destruct A as (bound & D & E).
  split; [|split]; auto.
  exists bound; split; auto.
  inv E; constructor; intros.
- eauto.
- destruct (j b1) as [[b0 delta0]|] eqn:JB1.
+ erewrite H in H1 by eauto. inv H1. eauto.
+ exploit H0; eauto. intros (X & Y). elim Y. apply Pos.lt_le_trans with bound; auto.
- eauto.
- eauto.
- eauto.
Qed.

Lemma external_call_parallel_rule:
  forall (F V: Type) ef (ge: Genv.t F V) vargs1 m1 t vres1 m1' m2 j P vargs2 (DETERM: determ_properties ef),
  external_call ef ge vargs1 m1 t vres1 m1' ->
  m2 |= minjection j m1 ** globalenv_inject ge j ** P ->
  Val.inject_list j vargs1 vargs2 ->
  exists j' vres2 m2',
     external_call ef ge vargs2 m2 t vres2 m2'
  /\ Val.inject j' vres1 vres2
  /\ m2' |= minjection j' m1' ** globalenv_inject ge j' ** P
  /\ inject_incr j j'
  /\ inject_separated j j' m1 m2.
Proof.
  intros until vargs2; intros DETERM CALL SEP ARGS.
  destruct SEP as (A & B & C). simpl in A.
  exploit external_call_mem_inject; eauto.
  eapply globalenv_inject_preserves_globals. eapply sep_pick1; eauto.
  intros (j' & vres2 & m2' & CALL' & RES & INJ' & UNCH1 & UNCH2 & INCR & ISEP).
  assert (MAXPERMS: forall b ofs p,
            Mem.valid_block m1 b -> Mem.perm m1' b ofs Max p -> Mem.perm m1 b ofs Max p).
  { intros. eapply external_call_max_perm; eauto. }
  exists j', vres2, m2'; intuition auto.
  split; [|split].
- exact INJ'.
- apply (m_invar _ m2).
+ apply globalenv_inject_incr with j m1; auto.
+ eapply Mem.unchanged_on_implies; eauto.
  intros; red; intros; red; intros.
  eelim C; eauto. simpl. exists b0, delta; auto.
- red; intros. destruct H as (b0 & delta & J' & E).
  destruct (j b0) as [[b' delta'] | ] eqn:J.
+ erewrite INCR in J' by eauto. inv J'.
  eelim C; eauto. simpl. exists b0, delta; split; auto. apply MAXPERMS; auto.
  eapply Mem.valid_block_inject_1; eauto.
+ exploit ISEP; eauto. intros (X & Y). elim Y. eapply m_valid; eauto.
Qed.

Lemma alloc_parallel_rule_2:
  forall (F V: Type) (ge: Genv.t F V) m1 sz1 m1' b1 m2 sz2 m2' b2 P j lo hi delta,
  m2 |= minjection j m1 ** globalenv_inject ge j ** P ->
  Mem.alloc m1 0 sz1 = (m1', b1) ->
  Mem.alloc m2 0 sz2 = (m2', b2) ->
  (8 | delta) ->
  lo = delta ->
  hi = delta + Z.max 0 sz1 ->
  0 <= sz2 <= Ptrofs.max_unsigned ->
  0 <= delta -> hi <= sz2 ->
  exists j',
     m2' |= range b2 0 lo ** range b2 hi sz2 ** minjection j' m1' ** globalenv_inject ge j' ** P
  /\ inject_incr j j'
  /\ j' b1 = Some(b2, delta) /\ m2' |= undef_area b2 0 lo ** undef_area b2 hi sz2 ** minjection j' m1' ** globalenv_inject ge j' ** P.
Proof.
  intros.
  set (j1 := fun b => if eq_block b b1 then Some(b2, delta) else j b).
  assert (X: inject_incr j j1).
  { unfold j1; red; intros. destruct (eq_block b b1); auto.
    subst b. eelim Mem.fresh_block_alloc. eexact H0.
    eapply Mem.valid_block_inject_1. eauto. apply sep_proj1 in H. eexact H. }
  assert (Y: inject_separated j j1 m1 m2).
  { unfold j1; red; intros. destruct (eq_block b0 b1).
  - inversion H9; clear H9; subst b3 delta0 b0. split; eapply Mem.fresh_block_alloc; eauto.
  - congruence. }
  rewrite sep_swap in H. eapply globalenv_inject_incr with (j' := j1) in H; eauto. rewrite sep_swap in H.
  clear X Y.
  exploit alloc_parallel_rule; eauto.
  intros (j' & A & B & C & D & E).
  exists j'; split; auto; [|split;auto]; [|split;auto]; cycle 1.
  { rewrite sep_swap4 in E. rewrite sep_swap4. apply globalenv_inject_incr with j1 m1; auto.
    - red; unfold j1; intros. destruct (eq_block b b1). congruence. rewrite D; auto.
    - red; unfold j1; intros. destruct (eq_block b0 b1). congruence. rewrite D in H9 by auto. congruence. }
  rewrite sep_swap4 in A. rewrite sep_swap4. apply globalenv_inject_incr with j1 m1; auto.
- red; unfold j1; intros. destruct (eq_block b b1). congruence. rewrite D; auto.
- red; unfold j1; intros. destruct (eq_block b0 b1). congruence. rewrite D in H9 by auto. congruence.
Qed.

Lemma external_call_parallel_rule_backward:
  forall (F V: Type) ef (ge: Genv.t F V) vargs1 m1 t vres2 m2' m2 j P vargs2,
  is_external_ef ef ->
  external_call ef ge vargs2 m2 t vres2 m2' ->
  m2 |= minjection j m1 ** globalenv_inject ge j ** P ->
  Val.inject_list j vargs1 vargs2 ->
  (exists t' vres m2, external_call ef ge vargs1 m1 t' vres m2) ->
  (exists j' vres1 m1',
    external_call ef ge vargs1 m1 t vres1 m1'
  /\ Val.inject j' vres1 vres2
  /\ m2' |= minjection j' m1' ** globalenv_inject ge j' ** P
  /\ inject_incr j j'
  /\ inject_separated j j' m1 m2)
  \/ (forall t' vres1 m1', ~ external_call ef ge vargs1 m1 t' vres1 m1')
  \/ (~ trace_intact t /\
       (exists t' vres1 m1',
          external_call ef ge vargs1 m1 t' vres1 m1' /\
          (exists tl, t' = Eapp (trace_cut_pterm t) tl))).
Proof.
  intros until vargs2; intros EXT CALL SEP ARGS SAFESRC.
  destruct SEP as (A & B & C). simpl in A.
  exploit external_call_mem_inject_backward; eauto.
  eapply globalenv_inject_preserves_globals. eapply sep_pick1; eauto.
  intros [(j' & vres1 & m1' & CALL' & RES & INJ' & UNCH1 & UNCH2 & INCR & ISEP) |
          [UBSRC | (INTACT & t' & vres1 & m1' & CALL' & tl & CUT)]].
{ left.
  assert (MAXPERMS: forall b ofs p,
            Mem.valid_block m1 b -> Mem.perm m1' b ofs Max p -> Mem.perm m1 b ofs Max p).
  { intros. eapply external_call_max_perm; eauto. }
  exists j', vres1, m1'; intuition auto.
  split; [|split]; auto.
- apply m_invar with (m0 := m2).
+ apply globalenv_inject_incr with j m1; auto.
+ eapply Mem.unchanged_on_implies; eauto.
  intros; red; intros; red; intros.
  eelim C; eauto. simpl. exists b0, delta; auto.
- red; intros. destruct H as (b0 & delta & J' & E).
  destruct (j b0) as [[b' delta'] | ] eqn:J.
* erewrite INCR in J' by eauto. inv J'.
  eelim C; eauto. simpl. exists b0, delta; split; auto. apply MAXPERMS; auto.
  eapply Mem.valid_block_inject_1; eauto.
* exploit ISEP; eauto. intros (X & Y). elim Y. eapply m_valid; eauto. }
{ des. exploit UBSRC; eauto. }
{ right. right. esplits; eauto. }
Qed.

Lemma external_call_parallel_rule_backward_progress:
  forall (F V: Type) ef (ge: Genv.t F V) vargs1 m1 t vres1 m1' m2 j P vargs2,
  is_external_ef ef ->
  external_call ef ge vargs1 m1 t vres1 m1' ->
  m2 |= minjection j m1 ** globalenv_inject ge j ** P ->
  Val.inject_list j vargs1 vargs2 ->
  exists t' vres2 m2',
    external_call ef ge vargs2 m2 t' vres2 m2'.
Proof.
  intros until vargs2; intros EXT CALL SEP ARGS.
  destruct SEP as (A & B). simpl in A.
  exploit external_call_mem_inject_backward_progress; eauto.
  eapply globalenv_inject_preserves_globals. eapply sep_pick1; eauto.
  eapply B.
Qed.

Lemma capture_parallel_rule_backward
    j m1 m2 b1 b2 addr delta m2' P
    (CAPTURE: Mem.capture m2 b2 (addr - delta) m2')
    (SEP: m2 |= minjection j m1 ** P)
    (INJ: j b1 = Some (b2, delta)) :
  exists m1', Mem.capture m1 b1 addr m1' /\ m2' |= minjection j m1' ** P.
Proof.
  destruct SEP as (A & B). simpl in A. des.
  exploit Mem.capture_inject_backward; eauto. i. des. esplits; eauto.
  econs; ss.
  split.
- apply (m_invar P) with m2; auto. eapply Mem.capture_unchanged_on; eauto.
- red; simpl; intros. destruct H as (b0 & delta0 & U & V).
  eelim B0; eauto. simpl. exists b0, delta0; eauto with mem.
  esplits; eauto. rewrite Genv.capture_same_perm; eauto.
Qed.

